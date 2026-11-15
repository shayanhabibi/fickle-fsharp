// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.CodeAnalysis

open System
open System.Collections.Concurrent
open System.IO
open System.Threading

open Internal.Utilities.Collections
open Internal.Utilities.Library
open Internal.Utilities.Library.Extras

open FSharp.Compiler
open FSharp.Compiler.AbstractIL
open FSharp.Compiler.AbstractIL.IL
open FSharp.Compiler.AbstractIL.ILBinaryReader
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.CheckDeclarations
open FSharp.Compiler.CompilerConfig
open FSharp.Compiler.CompilerDiagnostics
open FSharp.Compiler.CompilerGlobalState
open FSharp.Compiler.CompilerImports
open FSharp.Compiler.CompilerOptions
open FSharp.Compiler.DependencyManager
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.NameResolution
open FSharp.Compiler.ParseAndCheckInputs
open FSharp.Compiler.ScriptClosure
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.TcGlobals
open FSharp.Compiler.Text
open FSharp.Compiler.Text.Range
open FSharp.Compiler.Tokenization
open FSharp.Compiler.TypedTree
open FSharp.Compiler.TypedTreeBasics
open FSharp.Compiler.TypedTreeOps
open FSharp.Compiler.BuildGraph
open FSharp.Compiler.GraphChecking

//-------------------------------------------------------------------------
// FSharpProjectChecker
//-------------------------------------------------------------------------

type internal TcResult = PartialResult
type internal TcErrors = FSharpDiagnostic[]

/// The result of checking one file over the dependency graph, kept for reuse while
/// neither the file nor anything it depends on changes.
type internal GraphCheckEntry =
    {
        parseResults: FSharpParseFileResults
        qualifiedName: string
        fileIndex: int
        /// Identifies the finisher: a new one gets a new generation.
        generation: int
        /// The files this one depends on, with the generations of the finishers it was checked against.
        dependencyGenerations: (string * int)[]
        /// Adds the file's signature to the state its dependents are checked in. Kept from an earlier check while later
        /// checks of the file give the same signature, so the dependents' results stay valid.
        finisher: Finisher<NodeToTypeCheck, TcState, PartialResult>
        /// The implementation to report, from the latest check of the file.
        implFile: CheckedImplFile option
        signature: Lazy<string option>
        tcErrors: TcErrors
    }

/// How a file's result was obtained in a check over the dependency graph.
type internal GraphCheckOutcome =
    /// The file is unchanged, and none of the files it depends on, now or in the earlier check, was replaced.
    | Reused of GraphCheckEntry
    /// The file changed but its signature did not, and none of the files it depends on was replaced. The earlier
    /// finisher stays, so the file's dependents can be reused; the new implementation is reported.
    | Kept of GraphCheckEntry * CheckedImplFile
    /// The file was checked, and its dependents see the new result.
    | Replaced of Finisher<NodeToTypeCheck, TcState, PartialResult> * dependencyGenerations: (string * int)[]

type internal CompilerState =
    {
        tcConfig: TcConfig
        tcGlobals: TcGlobals
        tcImports: TcImports
        tcInitialState: TcState
        projectOptions: FSharpProjectOptions
        parseCache: ConcurrentDictionary<string * int, FSharpParseFileResults>
        checkCache: ConcurrentDictionary<string, (TcResult * TcErrors) * (TcState * ModuleNamesDict)>
        graphCheckCache: ConcurrentDictionary<string, GraphCheckEntry>
    }

type internal CacheMsg<'T> =
    | Get of AsyncReplyChannel<'T>
    | Reset

type internal Cache<'T>(init: (unit -> unit) -> Async<'T>) =
    let agent =
        MailboxProcessor<CacheMsg<'T>>.Start(fun agent ->
            let rec loop cached =
                async {
                    match! agent.Receive() with
                    | Get channel ->
                        match cached with
                        | Some cached ->
                            channel.Reply(cached)
                            return! Some cached |> loop
                        | None ->
                            let reset () = agent.Post Reset
                            let! cached = init reset
                            channel.Reply cached
                            return! Some cached |> loop
                    | Reset -> return! loop None
                }

            loop None)

    member _.Get() = agent.PostAndAsyncReply(Get)
    member _.Reset() = agent.Post Reset

[<AutoOpen>]
module internal ParseAndCheck =

    let userOpName = "Unknown"
    let suggestNamesForErrors = true
    let captureIdentifiersWhenParsing = false

    let measureTime (f: unit -> 'a) =
        let sw = Diagnostics.Stopwatch.StartNew()
        let res = f ()
        sw.Stop()
        res, sw.ElapsedMilliseconds

    let measureTimeAsync (f: unit -> Async<'a>) =
        async {
            let sw = Diagnostics.Stopwatch.StartNew()
            let! res = f ()
            sw.Stop()
            return res, sw.ElapsedMilliseconds
        }

    // Cache to store current compiler state.
    // In the case of type provider invalidation,
    // compiler state needs to be reset to recognize TP changes.
    let initializeCompilerStateWith (projectReferences: IProjectReference list) projectOptions (reset: unit -> unit) =
        async {
            let tcConfig =
                let tcConfigB =
                    TcConfigBuilder.CreateNew(
                        SimulatedMSBuildReferenceResolver.getResolver (),
                        defaultFSharpBinariesDir = FSharpCheckerResultsSettings.defaultFSharpBinariesDir,
                        reduceMemoryUsage = ReduceMemoryFlag.Yes,
                        implicitIncludeDir = !!Path.GetDirectoryName(projectOptions.ProjectFileName),
                        isInteractive = false,
                        isInvalidationSupported = true,
                        defaultCopyFSharpCore = CopyFSharpCoreFlag.No,
                        tryGetMetadataSnapshot = (fun _ -> None),
                        sdkDirOverride = None,
                        rangeForErrors = range0
                    )
                // Before the -r: options are applied: each one takes the project reference of its path
                tcConfigB.projectReferences <- projectReferences
                let sourceFiles = projectOptions.SourceFiles |> Array.toList
                let argv = projectOptions.OtherOptions |> Array.toList
                let _sourceFiles = ApplyCommandLineArgs(tcConfigB, sourceFiles, argv)
                TcConfig.Create(tcConfigB, validate = false)

            let tcConfigP = TcConfigProvider.Constant(tcConfig)

            let dependencyProvider = new DependencyProvider()
            let! tcGlobals, tcImports = TcImports.BuildTcImports(tcConfigP, dependencyProvider)

#if !NO_TYPEPROVIDERS
            // Handle type provider invalidation by resetting compiler state
            tcImports.GetCcusExcludingBase()
            |> Seq.iter (fun ccu -> ccu.Deref.InvalidateEvent.Add(fun _ -> reset ()))
#else
            ignore reset
#endif

            // The name the build gives the assembly (<AssemblyName>, by -o:): InternalsVisibleTo reads it, and references resolve by it
            let assemblyName =
                match tcConfig.outputFile with
                | Some(output: string) -> !!Path.GetFileNameWithoutExtension(output)
                | None -> !!Path.GetFileNameWithoutExtension(projectOptions.ProjectFileName)

            let tcInitial, openDecls0 =
                GetInitialTcEnv(assemblyName, rangeStartup, tcConfig, tcImports, tcGlobals)

            let tcInitialState =
                GetInitialTcState(rangeStartup, assemblyName, tcConfig, tcGlobals, tcImports, tcInitial, openDecls0)

            // parse cache, keyed on file name and source hash
            let parseCache =
                ConcurrentDictionary<string * int, FSharpParseFileResults>(HashIdentity.Structural)
            // type check cache, keyed on file name
            let checkCache =
                ConcurrentDictionary<string, (TcResult * TcErrors) * (TcState * ModuleNamesDict)>(HashIdentity.Structural)
            // graph type check cache, keyed on file name
            let graphCheckCache =
                ConcurrentDictionary<string, GraphCheckEntry>(HashIdentity.Structural)

            return
                {
                    tcConfig = tcConfig
                    tcGlobals = tcGlobals
                    tcImports = tcImports
                    tcInitialState = tcInitialState
                    projectOptions = projectOptions
                    parseCache = parseCache
                    checkCache = checkCache
                    graphCheckCache = graphCheckCache
                }
        }

    let initializeCompilerState projectOptions reset =
        initializeCompilerStateWith [] projectOptions reset

    let MakeProjectResults
        (
            projectFileName: string,
            parseResults: FSharpParseFileResults[],
            tcState: TcState,
            errors: FSharpDiagnostic[],
            topAttrsOpt: TopAttribs option,
            tcImplFilesOpt: CheckedImplFile list option,
            compilerState
        ) =
        let assemblyRef = mkSimpleAssemblyRef "stdin"
        let access = tcState.TcEnvFromImpls.AccessRights
        let symbolUses = Choice2Of2(async { return seq { } })

        let dependencyFiles =
            parseResults |> Seq.map (fun x -> x.DependencyFiles) |> Array.concat

        let getAssemblyData () = None

        let details =
            (compilerState.tcGlobals,
             compilerState.tcImports,
             tcState.Ccu,
             tcState.CcuSig,
             symbolUses,
             topAttrsOpt,
             getAssemblyData,
             assemblyRef,
             access,
             tcImplFilesOpt,
             dependencyFiles,
             Some compilerState.projectOptions)

        let keepAssemblyContents = true
        FSharpCheckProjectResults(projectFileName, Some compilerState.tcConfig, keepAssemblyContents, errors, Some details)

    let ClearStaleCache (fileName: string, parsingOptions: FSharpParsingOptions, compilerState) =
        let fileIndex = parsingOptions.SourceFiles |> Array.findIndex ((=) fileName)
        let filesAbove = parsingOptions.SourceFiles |> Array.take fileIndex
        // backup all cached typecheck entries above file
        let cachedAbove =
            filesAbove
            |> Array.choose (fun key ->
                match compilerState.checkCache.TryGetValue(key) with
                | true, value -> Some(key, value)
                | false, _ -> None)
        // remove all parse cache entries with the same file name
        let staleParseKeys =
            compilerState.parseCache.Keys
            |> Seq.filter (fun (n, _) -> n = fileName)
            |> Seq.toArray

        staleParseKeys
        |> Array.iter (fun key -> compilerState.parseCache.TryRemove(key) |> ignore)

        compilerState.checkCache.Clear() // clear all typecheck cache
        // restore all cached typecheck entries above file
        cachedAbove
        |> Array.iter (fun (key, value) -> compilerState.checkCache.TryAdd(key, value) |> ignore)

    let ParseFile (fileName: string, sourceHash: int, source: Lazy<string>, parsingOptions: FSharpParsingOptions, compilerState, ct) =
        let parseCacheKey = fileName, sourceHash

        compilerState.parseCache.GetOrAdd(
            parseCacheKey,
            fun _ ->
                ClearStaleCache(fileName, parsingOptions, compilerState)
                let sourceText = SourceText.ofString source.Value
                let flatErrors = compilerState.tcConfig.flatErrors

                let parseErrors, parseTreeOpt, anyErrors =
                    ParseAndCheckFile.parseFile (
                        sourceText,
                        fileName,
                        parsingOptions,
                        userOpName,
                        suggestNamesForErrors,
                        flatErrors,
                        captureIdentifiersWhenParsing,
                        ct
                    )

                let dependencyFiles = [||] // interactions have no dependencies
                FSharpParseFileResults(parseErrors, parseTreeOpt, anyErrors, dependencyFiles)
        )

    /// Counts the compiler-generated names of a file from zero again, before checking it, so a file checked again in
    /// this process, as in watch mode, gets the names a fresh compilation gives instead of continuing from its last check.
    let ResetGeneratedNames (input: ParsedInput, compilerState) =
        compilerState.tcGlobals.CompilerGlobalState
        |> Option.iter (fun state -> state.ResetCompilerGeneratedNamesOfFile input.QualifiedName.Range.FileIndex)

    let TypeCheckOneInputEntry
        (parseResults: FSharpParseFileResults, tcSink: TcResultsSink, tcState: TcState, moduleNamesDict: ModuleNamesDict, compilerState)
        =
        let input = parseResults.ParseTree
        let diagnosticsOptions = compilerState.tcConfig.diagnosticsOptions

        let capturingLogger =
            CompilationDiagnosticLogger("TypeCheckFile", diagnosticsOptions)

        let diagnosticsLogger =
            GetDiagnosticsLoggerFilteringByScopedNowarn(diagnosticsOptions, capturingLogger)

        use _scope = new CompilationGlobalsScope(diagnosticsLogger, BuildPhase.TypeCheck)

        let checkForErrors () =
            parseResults.ParseHadErrors || diagnosticsLogger.ErrorCount > 0

        let prefixPathOpt = None

        let input, moduleNamesDict =
            input |> DeduplicateParsedInputModuleName moduleNamesDict

        ResetGeneratedNames(input, compilerState)

        let tcResult, tcState =
            CheckOneInput(
                checkForErrors,
                compilerState.tcConfig,
                compilerState.tcImports,
                compilerState.tcGlobals,
                prefixPathOpt,
                tcSink,
                tcState,
                input
            )
            |> Cancellable.runWithoutCancellation

        let fileName = parseResults.FileName
        let flatErrors = compilerState.tcConfig.flatErrors
        let parseDiagnostics = capturingLogger.GetDiagnostics()

        let tcErrors =
            DiagnosticHelpers.CreateDiagnostics(
                diagnosticsOptions,
                false,
                fileName,
                parseDiagnostics,
                suggestNamesForErrors,
                flatErrors,
                None
            )

        (tcResult, tcErrors), (tcState, moduleNamesDict)

    let CheckFile
        (projectFileName: string, parseResults: FSharpParseFileResults, tcState: TcState, moduleNamesDict: ModuleNamesDict, compilerState)
        =
        let sink = TcResultsSinkImpl(compilerState.tcGlobals)
        let tcSink = TcResultsSink.WithSink sink

        let (tcResult, tcErrors), (tcState, moduleNamesDict) =
            TypeCheckOneInputEntry(parseResults, tcSink, tcState, moduleNamesDict, compilerState)

        let fileName = parseResults.FileName
        compilerState.checkCache.[fileName] <- ((tcResult, tcErrors), (tcState, moduleNamesDict))

        let loadClosure = None
        let keepAssemblyContents = true

        let tcEnvAtEnd, _topAttrs, implFile, ccuSigForFile, ownSigForFile = tcResult
        let errors = Array.append parseResults.Diagnostics tcErrors

        let scope =
            TypeCheckInfo(
                compilerState.tcConfig,
                compilerState.tcGlobals,
                ccuSigForFile,
                ownSigForFile,
                tcState.Ccu,
                compilerState.tcImports,
                tcEnvAtEnd.AccessRights,
                projectFileName,
                fileName,
                Some compilerState.projectOptions,
                sink.GetResolutions(),
                sink.GetSymbolUses(),
                tcEnvAtEnd.NameEnv,
                loadClosure,
                implFile,
                sink.GetOpenDeclarations()
            )

        FSharpCheckFileResults(fileName, errors, Some scope, parseResults.DependencyFiles, None, keepAssemblyContents)

    /// The last generation given to a graph check finisher; 0 is never given.
    let lastGraphCheckGeneration = ref 0

    /// Whether a changed file whose signature is the same keeps its dependents' results (FCS_SIGNATURE_CUTOFF=0 turns it off).
    let signatureCutoff =
        Environment.GetEnvironmentVariable "FCS_SIGNATURE_CUTOFF" <> "0"

    let ReportCheckedFile (tcState: TcState, tcResult: TcResult, compilerState, subscriber) =
        let _, _, implFile, _, _ = tcResult

        match subscriber, implFile with
        | Some subscriber, Some implFile ->
            let cenv =
                SymbolEnv(compilerState.tcGlobals, tcState.Ccu, Some tcState.CcuSig, compilerState.tcImports)

            FSharpImplementationFileContents(cenv, implFile) |> subscriber
        | _ -> ()

    /// Type checks the files in parallel where the file dependency graph allows. A file checked by an earlier call is
    /// reused while neither it nor anything it depends on has changed, so after an edit only the edited file and its
    /// dependents are checked again. Fills the check cache with the same per-file entries a sequential check would
    /// leave. The subscriber gets the files in project order, each as soon as it and all files before it are checked,
    /// because Fable expects every earlier file to be known, not only the file's dependencies.
    let TypeCheckInputsInParallel (parseResults: FSharpParseFileResults[], tcState: TcState, compilerState, subscriber) =
        let tcConfig = compilerState.tcConfig
        let diagnosticsOptions = tcConfig.diagnosticsOptions

        let inputsAndModuleNames, _ =
            (Map.empty, parseResults)
            ||> Array.mapFold (fun moduleNamesDict parseRes ->
                let input, moduleNamesDict =
                    parseRes.ParseTree |> DeduplicateParsedInputModuleName moduleNamesDict

                (input, moduleNamesDict), moduleNamesDict)

        let inputs, moduleNamesDicts = Array.unzip inputsAndModuleNames
        let fileNames = parseResults |> Array.map (fun parseRes -> parseRes.FileName)

        let sourceFiles =
            inputs
            |> Array.mapi (fun idx input ->
                {
                    Idx = idx
                    FileName = input.FileName
                    ParsedInput = input
                })

        let filePairs = FilePairMap(sourceFiles)
        let graph, _trie = DependencyResolution.mkGraph filePairs sourceFiles

        let dependencies =
            Array.init inputs.Length (fun idx -> graph[idx] |> Array.filter ((<>) idx) |> Array.map (fun dep -> fileNames[dep]))

        // Each file's outcome is decided when the graph reaches it, after the files it depends on: dependencies always
        // come earlier in the project. Entities are compared by identity, so a file's earlier result stays valid only
        // while the finishers of everything it depends on are the ones it was checked with, also across checks of
        // part of the project.
        let outcomes = Array.zeroCreate<GraphCheckOutcome> inputs.Length
        let generations = Array.zeroCreate<int> inputs.Length
        let fileIndexes = Collections.Generic.Dictionary<string, int>()
        fileNames |> Array.iteri (fun idx fileName -> fileIndexes[fileName] <- idx)

        // A file this check reaches later is not settled yet, and gets 0, which no finisher has.
        let currentGeneration fileName =
            match fileIndexes.TryGetValue fileName with
            | true, idx -> generations[idx]
            | _ ->
                match compilerState.graphCheckCache.TryGetValue fileName with
                | true, entry -> entry.generation
                | _ -> -1

        let capturingLoggers =
            parseResults
            |> Array.map (fun _ -> CompilationDiagnosticLogger("TypeCheckFile", diagnosticsOptions))

        let loggers =
            capturingLoggers
            |> Array.map (fun logger -> GetDiagnosticsLoggerFilteringByScopedNowarn(diagnosticsOptions, logger))

        let checkFile idx tcState =
            let settle outcome generation =
                outcomes[idx] <- outcome
                generations[idx] <- generation

            let earlier =
                match compilerState.graphCheckCache.TryGetValue fileNames[idx] with
                | true, entry when
                    entry.qualifiedName = inputs[idx].QualifiedName.Text
                    && entry.fileIndex = idx
                    && entry.dependencyGenerations
                       |> Array.forall (fun (dep, generation) -> currentGeneration dep = generation)
                    && dependencies[idx]
                       |> Array.forall (fun dep -> entry.dependencyGenerations |> Array.exists (fst >> (=) dep))
                    ->
                    Some entry
                | _ -> None

            match earlier with
            | Some entry when obj.ReferenceEquals(entry.parseResults, parseResults[idx]) ->
                settle (Reused entry) entry.generation
                entry.finisher
            | _ ->
                let parseRes = parseResults[idx]
                let logger = loggers[idx]
                use _scope = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)

                let checkForErrors () =
                    parseRes.ParseHadErrors || logger.ErrorCount > 0

                let prefixPathOpt = None
                ResetGeneratedNames(inputs[idx], compilerState)

                let finisher =
                    CheckOneInputWithCallback
                        (NodeToTypeCheck.PhysicalFile idx)
                        (checkForErrors,
                         tcConfig,
                         compilerState.tcImports,
                         compilerState.tcGlobals,
                         prefixPathOpt,
                         TcResultsSink.NoSink,
                         tcState,
                         inputs[idx],
                         false)
                    |> Cancellable.runWithoutCancellation

                let kept =
                    match earlier with
                    | Some entry when signatureCutoff ->
                        // The graph applies a finisher once for every file that depends on it, so applying it once more to
                        // read the signature changes nothing. Its diagnostics are already in the file's logger.
                        let (Finisher(finisher = finish)) = finisher

                        let partialResult, _ =
                            use _ = new CompilationGlobalsScope(DiscardErrorsLogger, BuildPhase.TypeCheck)
                            finish tcState

                        match partialResult with
                        | _, topAttrs, Some implFile, _, _ ->
                            let signature = SignatureFingerprint.compute implFile.Signature topAttrs

                            if signature.IsSome && signature = entry.signature.Force() then
                                Some(entry, implFile)
                            else
                                None
                        | _ -> None
                    | _ -> None

                match kept with
                | Some(entry, implFile) ->
                    settle (Kept(entry, implFile)) entry.generation
                    entry.finisher
                | None ->
                    let dependencyGenerations =
                        dependencies[idx] |> Array.map (fun dep -> dep, currentGeneration dep)

                    settle (Replaced(finisher, dependencyGenerations)) (Interlocked.Increment &lastGraphCheckGeneration.contents)
                    finisher

        // The implementation to report for a file: a kept or reused file's finisher gives an earlier one.
        let withLatestImplFile idx ((tcEnv, topAttrs, implFile, ccuSig, ownSig): TcResult) : TcResult =
            let implFile =
                match outcomes[idx] with
                | Reused entry -> entry.implFile
                | Kept(_, implFile) -> Some implFile
                | Replaced _ -> implFile

            tcEnv, topAttrs, implFile, ccuSig, ownSig

        let checkedFiles = Array.zeroCreate<(TcResult * TcState) option> parseResults.Length
        let nextToReport = ref 0

        let onChecked idx tcResult tcState =
            lock checkedFiles (fun () ->
                checkedFiles[idx] <- Some(withLatestImplFile idx tcResult, tcState)

                while nextToReport.Value < checkedFiles.Length
                      && checkedFiles[nextToReport.Value].IsSome do
                    let tcResult, tcState = checkedFiles[nextToReport.Value].Value
                    ReportCheckedFile(tcState, tcResult, compilerState, subscriber)
                    nextToReport.Value <- nextToReport.Value + 1)

        let fileResults =
            use _ = UseBuildPhase BuildPhase.TypeCheck

            CheckMultipleInputsUsingGraphModeWithStates(
                compilerState.tcImports,
                compilerState.tcGlobals,
                None,
                tcState,
                inputs,
                graph,
                filePairs,
                checkFile,
                onChecked,
                (fun idx -> loggers[idx]),
                CancellationToken.None
            )

        let flatErrors = tcConfig.flatErrors

        let results =
            fileResults
            |> Array.mapi (fun idx (tcResult, tcState) ->
                let fileName = fileNames[idx]
                let tcResult = withLatestImplFile idx tcResult

                let newErrors () =
                    let diagnostics = capturingLoggers[idx].GetDiagnostics()

                    DiagnosticHelpers.CreateDiagnostics(
                        diagnosticsOptions,
                        false,
                        fileName,
                        diagnostics,
                        suggestNamesForErrors,
                        flatErrors,
                        None
                    )

                let entry =
                    match outcomes[idx] with
                    | Reused entry -> entry
                    | Kept(entry, implFile) ->
                        // The kept finisher was checked against the earlier dependencies, which include the current ones.
                        { entry with
                            parseResults = parseResults[idx]
                            implFile = Some implFile
                            tcErrors = newErrors ()
                        }
                    | Replaced(finisher, dependencyGenerations) ->
                        let _, topAttrs, implFile, _, _ = tcResult

                        {
                            parseResults = parseResults[idx]
                            qualifiedName = inputs[idx].QualifiedName.Text
                            fileIndex = idx
                            generation = generations[idx]
                            dependencyGenerations = dependencyGenerations
                            finisher = finisher
                            implFile = implFile
                            signature =
                                lazy
                                    (implFile
                                     |> Option.bind (fun implFile -> SignatureFingerprint.compute implFile.Signature topAttrs))
                            tcErrors = newErrors ()
                        }

                compilerState.graphCheckCache[fileName] <- entry
                compilerState.checkCache[fileName] <- ((tcResult, entry.tcErrors), (tcState, moduleNamesDicts[idx]))
                tcResult, entry.tcErrors)

        if not (isNull (Environment.GetEnvironmentVariable "FCS_GRAPH_LOG")) then
            let count f =
                outcomes |> Array.filter f |> Array.length

            eprintfn
                "Graph check: %d reused, %d kept, %d replaced"
                (count (function
                    | Reused _ -> true
                    | _ -> false))
                (count (function
                    | Kept _ -> true
                    | _ -> false))
                (count (function
                    | Replaced _ -> true
                    | _ -> false))

        let lastState = fileResults |> Array.last |> snd
        results, (lastState, Array.last moduleNamesDicts)

    let TypeCheckClosedInputSet (parseResults: FSharpParseFileResults[], tcState, compilerState, subscriber) =
        let cachedTypeCheck (tcState, moduleNamesDict) (parseRes: FSharpParseFileResults) =
            let checkCacheKey = parseRes.FileName

            let typeCheckOneInput _fileName =
                TypeCheckOneInputEntry(parseRes, TcResultsSink.NoSink, tcState, moduleNamesDict, compilerState)

            let (result, errors), (tcState, moduleNamesDict) =
                compilerState.checkCache.GetOrAdd(checkCacheKey, typeCheckOneInput)

            ReportCheckedFile(tcState, result, compilerState, subscriber)
            (result, errors), (tcState, moduleNamesDict)

        // Several files go through the dependency graph in parallel, reusing unaffected results from earlier checks.
        let checkInParallel =
            parseResults.Length > 1
            && compilerState.tcConfig.typeCheckingConfig.Mode = TypeCheckingMode.Graph
            && not compilerState.tcConfig.compilingFSharpCore

        let results, (tcState, moduleNamesDict) =
            if checkInParallel then
                TypeCheckInputsInParallel(parseResults, tcState, compilerState, subscriber)
            else
                ((tcState, Map.empty), parseResults) ||> Array.mapFold cachedTypeCheck

        let tcResults, tcErrors = Array.unzip results

        let (tcEnvAtEndOfLastFile, topAttrs, implFiles, _ccuSigsForFiles), tcState =
            CheckMultipleInputsFinish(tcResults |> Array.toList, tcState)

        let tcState, declaredImpls, ccuContents =
            CheckClosedInputSetFinish(implFiles, tcState)

        tcState.Ccu.Deref.Contents <- ccuContents
        tcState, topAttrs, declaredImpls, tcEnvAtEndOfLastFile, moduleNamesDict, tcErrors

    /// Errors grouped by file, sorted by line, column
    let ErrorsByFile (fileNames: string[], errorList: FSharpDiagnostic[] list) =
        let errorMap =
            errorList |> Array.concat |> Array.groupBy (fun x -> x.FileName) |> Map.ofArray

        let errors = fileNames |> Array.choose errorMap.TryFind
        errors |> Array.iter (Array.sortInPlaceBy (fun x -> x.StartLine, x.StartColumn))
        errors |> Array.concat

[<Sealed>]
type FSharpProjectChecker internal (compilerStateCache) =

    static member Create(projectOptions: FSharpProjectOptions) =
        Cache(initializeCompilerState projectOptions) |> FSharpProjectChecker

    /// Parses and checks the whole project, good for compilers (Fable etc.)
    /// Does not retain name resolutions and symbol uses which are quite memory hungry (so no intellisense etc.).
    /// Already parsed files will be cached so subsequent compilations will be faster.
    member _.ParseAndCheckProject
        (
            projectFileName: string,
            fileNames: string[],
            sourceReader: string -> int * Lazy<string>,
            ?lastFile: string,
            ?subscriber: FSharpImplementationFileContents -> unit
        ) =
        async {
            let! ct = Async.CancellationToken
            let! compilerState = compilerStateCache.Get()
            // parse files
            let parsingOptions =
                FSharpParsingOptions.FromTcConfig(compilerState.tcConfig, fileNames, false)

            let parseResults =
                let fileNames =
                    match lastFile with
                    | None -> fileNames
                    | Some fileName ->
                        let fileIndex = fileNames |> Array.findIndex ((=) fileName)
                        fileNames |> Array.take (fileIndex + 1)

                let parseFile fileName =
                    let sourceHash, source = sourceReader fileName
                    ParseFile(fileName, sourceHash, source, parsingOptions, compilerState, ct)

                // Don't parallelize if we have cached files, as it would create issues with invalidation
                if compilerState.parseCache.Count = 0 then
                    fileNames |> Array.Parallel.map parseFile
                else
                    fileNames |> Array.map parseFile

            // type check files
            let (tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, _moduleNamesDict, tcErrors) =
                TypeCheckClosedInputSet(parseResults, compilerState.tcInitialState, compilerState, subscriber)

            // make project results
            let parseErrors = parseResults |> Array.collect (fun p -> p.Diagnostics)
            let typedErrors = tcErrors |> Array.concat
            let errors = ErrorsByFile(fileNames, [ parseErrors; typedErrors ])

            let projectResults =
                MakeProjectResults(projectFileName, parseResults, tcState, errors, Some topAttrs, Some tcImplFiles, compilerState)

            return projectResults
        }

    /// Parses and checks file in project, will compile and cache all the files up to this one
    /// (if not already done before), or fetch them from cache. Returns partial project results,
    /// up to and including the file requested. Returns parse and typecheck results containing
    /// name resolutions and symbol uses for the file requested only, so intellisense etc. works.
    member _.ParseAndCheckFileInProject
        (projectFileName: string, fileNames: string[], sourceReader: string -> int * Lazy<string>, fileName: string)
        =
        async {
            let! ct = Async.CancellationToken
            let! compilerState = compilerStateCache.Get()

            // get files before file
            let fileIndex = fileNames |> Array.findIndex ((=) fileName)
            let fileNamesBeforeFile = fileNames |> Array.take fileIndex

            // parse files before file
            let parsingOptions =
                FSharpParsingOptions.FromTcConfig(compilerState.tcConfig, fileNames, false)

            let parseFile fileName =
                let sourceHash, source = sourceReader fileName
                ParseFile(fileName, sourceHash, source, parsingOptions, compilerState, ct)

            let parseResults = fileNamesBeforeFile |> Array.map parseFile

            // type check files before file
            let tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, moduleNamesDict, tcErrors =
                TypeCheckClosedInputSet(parseResults, compilerState.tcInitialState, compilerState, None)

            // parse and type check file
            let parseFileResults = parseFile fileName

            let checkFileResults =
                CheckFile(projectFileName, parseFileResults, tcState, moduleNamesDict, compilerState)

            let (tcResult, _tcErrors), (tcState, _moduleNamesDict) =
                compilerState.checkCache.[fileName]

            let _tcEnvAtEndFile, topAttrsFile, implFile, _ccuSigForFile, _ownSigForFile =
                tcResult

            // collect errors
            let parseErrorsBefore = parseResults |> Array.collect (fun p -> p.Diagnostics)
            let typedErrorsBefore = tcErrors |> Array.concat
            let newErrors = checkFileResults.Diagnostics

            let errors =
                ErrorsByFile(fileNames, [ parseErrorsBefore; typedErrorsBefore; newErrors ])

            // make partial project results
            let parseResults = Array.append parseResults [| parseFileResults |]
            let tcImplFiles = List.append tcImplFiles (Option.toList implFile)
            let topAttrs = CombineTopAttrs topAttrsFile topAttrs

            let projectResults =
                MakeProjectResults(projectFileName, parseResults, tcState, errors, Some topAttrs, Some tcImplFiles, compilerState)

            return (parseFileResults, checkFileResults, projectResults)
        }
