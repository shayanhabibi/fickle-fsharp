// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.Declarations

open System
open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Threading

open Internal.Utilities.Collections
open Internal.Utilities.Library

open FSharp.Compiler
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.CheckDeclarations
open FSharp.Compiler.CheckExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.CompilerDiagnostics
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.NameResolution
open FSharp.Compiler.ParseAndCheckInputs
open FSharp.Compiler.SourceCodeServices
open FSharp.Compiler.Syntax
open FSharp.Compiler.TcGlobals
open FSharp.Compiler.Text
open FSharp.Compiler.Text.Range
open FSharp.Compiler.TypedTree
open FSharp.Compiler.TypedTreeOps

type DeclarationKind =
    | Value
    | Type
    | Exception
    | Module
    | Open
    | ModuleAbbrev
    | Attribute
    | Do
    | RecGroup
    | Augmentation

type DeclarationKey =
    { ModulePath: string list
      Name: string
      Kind: DeclarationKind
      /// The number of earlier declarations of the file with the same module path, name and kind
      Ordinal: int }

/// A top-level declaration of an implementation file.
[<Sealed>]
type ParsedDeclaration internal (key: DeclarationKey, decl: SynModuleDecl, scopem: range, text: string) =
    member _.Key = key
    member _.Range = decl.Range
    /// A hash of the declaration's source text. Unequal hashes mean the text changed; equal ones do not prove
    /// it is the same, so compare Text for that.
    member _.SyntaxHash = hash text
    /// The declaration's source text, from the start of its range to its end. Compare Text, not SyntaxHash, to
    /// decide a declaration is unchanged.
    member _.Text = text
    member internal _.Syntax = decl
    /// The range the declaration's definitions are in scope for, as TcModuleOrNamespaceElementsNonMutRec gives it.
    member internal _.ScopeRange = scopem

/// A project's options, references and initial checking state.
[<Sealed>]
type ProjectContext internal (state: CompilerState) =
    member internal _.State = state

/// What a file adds to the state later files are checked in.
[<Sealed>]
type FileSignature internal (fileName: string, apply: TcState -> TcState, moduleNamesDict: ModuleNamesDict) =
    member internal _.FileName = fileName
    member internal _.Apply tcState = apply tcState
    /// The module-name dictionary DeduplicateParsedInputModuleName gave for this file: every earlier file's entries
    /// and its own. BeginFile merges these over the earlier files.
    member internal _.ModuleNamesDict = moduleNamesDict

/// The environment a declaration is checked in.
[<Sealed>]
type DeclEnv internal (env: TcEnv) =
    member internal _.Env = env

/// An implementation file set up for checking its declarations one at a time.
[<Sealed>]
type FileStart
    internal
    (
        ctx: ProjectContext,
        parse: FSharpParseFileResults,
        file: ParsedImplFileInput,
        moduleNamesDict: ModuleNamesDict,
        tcState: TcState,
        rootSigOpt: ModuleOrNamespaceType option,
        scope: ImplFileDeclarationScope,
        scopeContents: ModuleOrNamespaceType,
        sink: TcResultsSinkImpl,
        leftovers: TcFileState -> unit,
        diagnostics: FSharpDiagnostic[],
        errorCount: int
    ) =
    let sync = obj ()
    let mutable lastFinish: ResizeArray<unit -> unit> | null = null

    member internal _.Context = ctx
    member internal _.Parse = parse
    member internal _.File = file
    member internal _.ModuleNamesDict = moduleNamesDict
    member internal _.TcState = tcState
    member internal _.RootSigOpt = rootSigOpt
    member internal _.Scope = scope
    /// What the scope's accumulator held before the declarations: FinishFile merges their deltas onto it.
    member internal _.ScopeContents = scopeContents
    member internal _.Sink = sink
    member internal _.Leftovers = leftovers
    /// What setting up the file reported.
    member internal _.Diagnostics = diagnostics
    member internal _.ErrorCount = errorCount
    /// Held while finishing the file.
    member internal _.Sync = sync

    /// Undoes what the latest finish changed in the declarations' typed trees, once.
    member internal _.UndoLastFinish() =
        lock sync (fun () ->
            match lastFinish with
            | null -> ()
            | log ->
                lastFinish <- null
                MutationLog.Undo log)

    member internal _.SetLastFinish(log: ResizeArray<unit -> unit>) = lastFinish <- log

type internal CheckedDeclaration = ModuleOrNamespaceContents list * (unit -> unit) list * (AttributeTargets * Attrib) list

[<Sealed>]
type DeclarationResult
    internal
    (
        key: DeclarationKey,
        fingerprint: string,
        diagnostics: FSharpDiagnostic[],
        errorCount: int,
        leavesFreeTypars: bool,
        envAfter: DeclEnv,
        envAtEnd: TcEnv,
        checkedDecl: CheckedDeclaration,
        delta: ModuleOrNamespaceType,
        deltaCombines: bool,
        sink: TcResultsSinkImpl,
        leftovers: TcFileState -> unit
    ) =
    member _.Key = key
    /// The fingerprint as the check left the declaration. Finishing the file can still change it, by defaults or by
    /// later declarations solving its inference variables: FileResult.Fingerprints has the final one.
    member _.Fingerprint = fingerprint
    member _.Diagnostics = diagnostics
    member _.LeavesFreeTypars = leavesFreeTypars
    member _.EnvAfter = envAfter
    member internal _.ErrorCount = errorCount
    /// The environment at the end of the enclosing scope if this is its last declaration.
    member internal _.EnvAtEnd = envAtEnd
    member internal _.Checked = checkedDecl
    /// What the declaration publishes into the module or namespace it is in.
    member internal _.Delta: ModuleOrNamespaceType = delta
    /// Whether the delta is combined into the file's contents, as a namespace fragment's is, rather than added.
    member internal _.DeltaCombines = deltaCombines
    member internal _.Sink = sink
    member internal _.Leftovers = leftovers

    /// Whether the two results contribute the same Val and Entity objects, by reference and in the same order.
    /// For tests.
    member _.IsSameDelta(other: DeclarationResult) =
        let same (mine: seq<'T>) (theirs: seq<'T>) =
            Seq.length mine = Seq.length theirs && Seq.forall2 (fun a b -> obj.ReferenceEquals(a, b)) mine theirs

        same delta.AllValsAndMembers other.Delta.AllValsAndMembers
        && same delta.AllEntities other.Delta.AllEntities

[<Sealed>]
type FileResult
    internal
    (
        diagnostics: FSharpDiagnostic[],
        fingerprints: IReadOnlyDictionary<DeclarationKey, string>,
        signature: FileSignature,
        checkResults: FSharpCheckFileResults
    ) =
    member _.Diagnostics = diagnostics
    /// Each declaration's fingerprint after the file's inference scope is closed.
    member _.Fingerprints = fingerprints
    member _.Signature = signature
    member _.CheckResults = checkResults

module internal DeclarationCheck =

    /// The source each parse was made from, for hashing a declaration's text.
    let sources = ConditionalWeakTable<FSharpParseFileResults, ISourceText>()

    let textOfRange (source: ISourceText) (m: range) =
        let sb = Text.StringBuilder()
        let lastLine = min (m.EndLine - 1) (source.GetLineCount() - 1)

        for line in m.StartLine - 1 .. lastLine do
            let text = source.GetLineString line
            let first = if line = m.StartLine - 1 then min m.StartColumn text.Length else 0
            let last = if line = m.EndLine - 1 then min m.EndColumn text.Length else text.Length
            sb.Append(text, first, max 0 (last - first)).Append('\n') |> ignore

        sb.ToString()

    let longIdentText (ids: Ident list) =
        ids |> List.map (fun id -> id.idText) |> String.concat "."

    let rec patNames (pat: SynPat) =
        match pat with
        | SynPat.Named(ident = SynIdent(id, _)) -> [ id.idText ]
        | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) -> [ (List.last ids).idText ]
        | SynPat.Typed(pat = pat)
        | SynPat.Paren(pat = pat)
        | SynPat.Attrib(pat = pat)
        | SynPat.As(rhsPat = pat) -> patNames pat
        | SynPat.Tuple(elementPats = pats) -> List.collect patNames pats
        | SynPat.Wild _ -> [ "_" ]
        | _ -> []

    let typeDefnName (SynTypeDefn(typeInfo = info)) = longIdentText info.LongIdent

    let isAugmentation (SynTypeDefn(typeRepr = repr)) =
        match repr with
        | SynTypeDefnRepr.ObjectModel(kind = SynTypeDefnKind.Augmentation _) -> true
        | _ -> false

    let nameAndKind (decl: SynModuleDecl) =
        match decl with
        | SynModuleDecl.Let(isRecursive = isRec; bindings = binds) ->
            let names = binds |> List.collect (fun (SynBinding(headPat = pat)) -> patNames pat)
            String.Join(",", names), (if isRec then RecGroup else Value)
        | SynModuleDecl.Types([ typeDefn ], _) ->
            typeDefnName typeDefn, (if isAugmentation typeDefn then Augmentation else Type)
        | SynModuleDecl.Types(typeDefns, _) ->
            (match typeDefns with
             | typeDefn :: _ -> typeDefnName typeDefn
             | [] -> ""),
            RecGroup
        | SynModuleDecl.Exception(SynExceptionDefn(SynExceptionDefnRepr(caseName = SynUnionCase(ident = SynIdent(id, _))), _, _, _), _) ->
            id.idText, Exception
        | SynModuleDecl.NestedModule(moduleInfo = info; isRecursive = isRec) ->
            longIdentText info.LongIdent, (if isRec then RecGroup else Module)
        | SynModuleDecl.Open(target, _) ->
            (match target with
             | SynOpenDeclTarget.ModuleOrNamespace(SynLongIdent(id = ids), _) -> longIdentText ids
             | SynOpenDeclTarget.Type(SynType.LongIdent(SynLongIdent(id = ids)), _) -> "type " + longIdentText ids
             | SynOpenDeclTarget.Type _ -> "type"),
            Open
        | SynModuleDecl.ModuleAbbrev(ident = id) -> id.idText, ModuleAbbrev
        | SynModuleDecl.Attributes(attrs, _) ->
            attrs
            |> List.collect (fun list -> list.Attributes)
            |> List.map (fun attr -> longIdentText attr.TypeName.LongIdent)
            |> String.concat ",",
            Attribute
        | SynModuleDecl.Expr _ -> "", Do
        | SynModuleDecl.HashDirective(ParsedHashDirective(ident = ident), _) -> "#" + ident, Do
        | SynModuleDecl.NamespaceFragment(SynModuleOrNamespace(longId = ids; isRecursive = isRec)) ->
            longIdentText ids, (if isRec then RecGroup else Module)

    /// Whether the declarations of the file are those of its only fragment; otherwise they are the fragments,
    /// and recursive ones are one declaration.
    let splitsFragment (file: ParsedImplFileInput) =
        match file.Contents with
        | [ SynModuleOrNamespace(isRecursive = false) ] -> true
        | _ -> false

    let newLoggers (state: CompilerState) =
        let diagnosticsOptions = state.tcConfig.diagnosticsOptions
        let capturing = CompilationDiagnosticLogger("TypeCheckFile", diagnosticsOptions)
        capturing, GetDiagnosticsLoggerFilteringByScopedNowarn(diagnosticsOptions, capturing)

    let diagnosticsOf (state: CompilerState) fileName (capturing: CompilationDiagnosticLogger) =
        DiagnosticHelpers.CreateDiagnostics(
            state.tcConfig.diagnosticsOptions,
            false,
            fileName,
            capturing.GetDiagnostics(),
            suggestNamesForErrors,
            state.tcConfig.flatErrors,
            None
        )

    let stateBefore (state: CompilerState) (before: FileSignature list) =
        let tcState = (state.tcInitialState, before) ||> List.fold (fun tcState signature -> signature.Apply tcState)

        let moduleNamesDict =
            (Map.empty, before)
            ||> List.fold (fun (acc: ModuleNamesDict) signature ->
                (acc, signature.ModuleNamesDict)
                ||> Map.fold (fun acc qualifiedName files ->
                    let known = acc |> Map.tryFind qualifiedName |> Option.defaultValue Map.empty
                    acc |> Map.add qualifiedName (Map.foldBack Map.add files known)))

        tcState, moduleNamesDict

    let conditionalDefines (state: CompilerState) =
        if state.tcConfig.noConditionalErasure then
            None
        else
            Some state.tcConfig.conditionalDefines

    /// What a declaration adds to the module type it is published into, as the values and entities that are new.
    let contribution (before: ModuleOrNamespaceType) (after: ModuleOrNamespaceType) =
        let oldVals = HashSet<Val>(before.AllValsAndMembers, HashIdentity.Reference)
        let oldEntities = HashSet<Entity>(before.AllEntities, HashIdentity.Reference)
        let vals = after.AllValsAndMembers |> Seq.filter (oldVals.Contains >> not) |> List.ofSeq
        let entities = after.AllEntities |> Seq.filter (oldEntities.Contains >> not) |> List.ofSeq
        Construct.NewModuleOrNamespaceType after.ModuleOrNamespaceKind entities vals

    /// Whether a declaration publishes into the file's contents by combining: a fragment in a namespace does, at its
    /// end, and only reads accumulators of its own before that. A fragment with no namespace (namespace global, or the
    /// module of a file) publishes into the file's accumulator directly, as declarations in a module do.
    let combinesIntoFile (decl: SynModuleDecl) =
        match decl with
        | SynModuleDecl.NamespaceFragment(SynModuleOrNamespace(longId = longId; kind = kind)) ->
            // The enclosing namespace path, as EnterNamespaceFragment computes it
            let path = if kind.IsModule then List.truncate (max 0 (longId.Length - 1)) longId else longId
            not path.IsEmpty
        | _ -> false

    /// Merges the declarations' deltas in order onto what the scope held before them, as publishing them did: a
    /// namespace fragment combines its namespaces with the file's, and anything else adds its values and entities.
    let mergeDeltas (scopeContents: ModuleOrNamespaceType) (deltas: (ModuleOrNamespaceType * bool) list) =
        (scopeContents, deltas)
        ||> List.fold (fun acc (delta, combines) ->
            if combines then
                CombineCcuContentFragments [ acc; delta ]
            else
                let acc = (acc, delta.AllEntities) ||> Seq.fold (fun acc entity -> acc.AddEntity entity)
                (acc, delta.AllValsAndMembers) ||> Seq.fold (fun acc v -> acc.AddVal v))

    /// What checking left in cenv that CheckImplFileTail reads, to replay into the finish's own cenv.
    let leftoversOf (cenv: TcFileState) : TcFileState -> unit =
        let css = cenv.css
        let preDefaults = css.PostInferenceChecksPreDefaults.ToArray()
        let final = css.PostInferenceChecksFinal.ToArray()
        // Oldest first for each type variable, so adding them again keeps their order
        let extraCxs = css.ExtraCxs.Fold (fun stamp cx acc -> (stamp, cx) :: acc) []
        let unionsWithDeferredAttributes = css.UnionsWithDeferredAttributes
        let deferredUnionNullnessChecks = css.DeferredUnionNullnessChecks
        let createsGeneratedProvidedTypes = cenv.createsGeneratedProvidedTypes
        let namedDebugPoints = Array.ofSeq cenv.namedDebugPointsForInlinedCode

        fun into ->
            into.css.PostInferenceChecksPreDefaults.AddRange preDefaults
            into.css.PostInferenceChecksFinal.AddRange final

            for stamp, cx in extraCxs do
                into.css.ExtraCxs.Add(stamp, cx)

            into.css.UnionsWithDeferredAttributes <- Set.union into.css.UnionsWithDeferredAttributes unionsWithDeferredAttributes
            into.css.DeferredUnionNullnessChecks <- deferredUnionNullnessChecks @ into.css.DeferredUnionNullnessChecks

            if createsGeneratedProvidedTypes then
                into.createsGeneratedProvidedTypes <- true

            for KeyValue(key, m) in namedDebugPoints do
                into.namedDebugPointsForInlinedCode[key] <- m

    /// A checker state of its own (solver, caches, sink), with a new initial environment and accumulator for the file.
    let newCheckerState (state: CompilerState) (tcState: TcState) rootSigOpt file (sink: TcResultsSinkImpl) =
        CreateImplFileCheckState(
            state.tcGlobals,
            state.tcImports.GetImportMap(),
            tcState.Ccu,
            conditionalDefines state,
            TcResultsSink.WithSink sink,
            state.tcConfig.internalTestSpanStackReferring,
            tcState.TcEnvFromImpls,
            rootSigOpt,
            file,
            state.tcConfig.diagnosticsOptions
        )

    /// The results of several sinks as one sink's, in order.
    let mergeSinks (g: TcGlobals) (sinks: TcResultsSinkImpl list) =
        let all (pick: TcResolutions -> ResizeArray<'T>) =
            ResizeArray(sinks |> Seq.collect (fun sink -> pick (sink.GetResolutions())))

        let resolutions =
            TcResolutions(
                all (fun r -> r.CapturedEnvs),
                all (fun r -> r.CapturedExpressionTypings),
                all (fun r -> r.CapturedNameResolutions),
                all (fun r -> r.CapturedMethodGroupResolutions),
                all (fun r -> r.CapturedRelatedSymbolUses)
            )

        let formatSpecifierLocations =
            sinks |> Seq.collect (fun sink -> sink.GetFormatSpecifierLocations()) |> Array.ofSeq

        let symbolUses =
            TcSymbolUses(g, resolutions.CapturedNameResolutions, resolutions.CapturedRelatedSymbolUses, formatSpecifierLocations)

        let openDeclarations =
            sinks
            |> Seq.collect (fun sink -> sink.GetOpenDeclarations())
            |> Seq.distinctBy (fun x -> x.Range, x.AppliedScope, x.IsOwnNamespace)
            |> Array.ofSeq

        resolutions, symbolUses, openDeclarations

    /// The bindings of inline values in a declaration's typed tree, in order.
    let rec inlineBodies (contents: ModuleOrNamespaceContents) =
        let ofBinding (TBind(v, body, _)) = if v.ShouldInline then [ v, body ] else []

        match contents with
        | TMDefs defs -> List.collect inlineBodies defs
        | TMDefLet(binding, _) -> ofBinding binding
        | TMDefRec(bindings = bindings) ->
            bindings
            |> List.collect (function
                | ModuleOrNamespaceBinding.Binding binding -> ofBinding binding
                | ModuleOrNamespaceBinding.Module(_, def) -> inlineBodies def)
        | TMDefOpens _
        | TMDefDo _ -> []

    let fingerprintOf (contribution: ModuleOrNamespaceType) ((contents, _, _): CheckedDeclaration) =
        match SignatureFingerprint.computeDeclaration contribution (List.collect inlineBodies contents) with
        | Some fingerprint -> fingerprint
        // Not describable: never equal to another fingerprint, so it always counts as changed.
        | None -> "?" + Guid.NewGuid().ToString("N")

    let implFileSignature (state: CompilerState) fileName qualNameOfFile (implFileSig: ModuleOrNamespaceType) createsGeneratedProvidedTypes moduleNamesDict =
        let amap = state.tcImports.GetImportMap()

        let apply (tcState: TcState) =
            let hadSig = (tcState.TryFindRootSig qualNameOfFile).IsSome

            let _, tcState =
                AddCheckResultsToTcState
                    (state.tcGlobals, amap, hadSig, None, TcResultsSink.NoSink, tcState.TcEnvFromImpls, qualNameOfFile, implFileSig)
                    tcState

            AddCreatesGeneratedProvidedTypes createsGeneratedProvidedTypes tcState

        FileSignature(fileName, apply, moduleNamesDict)

[<AbstractClass; Sealed>]
type DeclarationChecker =

    static member CreateProject(options: FSharpProjectOptions) : Async<ProjectContext> =
        async {
            let! state = initializeCompilerState options ignore
            return ProjectContext state
        }

    static member Parse(ctx: ProjectContext, fileName: string, source: string) : FSharpParseFileResults =
        let state = ctx.State
        let parsingOptions = FSharpParsingOptions.FromTcConfig(state.tcConfig, state.projectOptions.SourceFiles, false)
        let sourceText = SourceText.ofString source

        let parseErrors, parseTree, anyErrors =
            ParseAndCheckFile.parseFile (
                sourceText,
                fileName,
                parsingOptions,
                userOpName,
                suggestNamesForErrors,
                state.tcConfig.flatErrors,
                captureIdentifiersWhenParsing,
                CancellationToken.None
            )

        let parse = FSharpParseFileResults(parseErrors, parseTree, anyErrors, [||])
        DeclarationCheck.sources.AddOrUpdate(parse, sourceText)
        parse

    static member Split(parse: FSharpParseFileResults) : ParsedDeclaration[] =
        match parse.ParseTree with
        | ParsedInput.SigFile _ -> invalidArg (nameof parse) "Only implementation files are checked one declaration at a time."
        | ParsedInput.ImplFile file ->
            let modulePath, endm, decls =
                if DeclarationCheck.splitsFragment file then
                    let (SynModuleOrNamespace(longId = longId; decls = decls; range = m)) = List.exactlyOne file.Contents
                    longId |> List.map (fun id -> id.idText), m.EndRange, decls
                else
                    [], file.QualifiedName.Range, [ for fragment in file.Contents -> SynModuleDecl.NamespaceFragment fragment ]

            let source =
                match DeclarationCheck.sources.TryGetValue parse with
                | true, source -> source
                | _ -> invalidArg (nameof parse) "Only a parse made by DeclarationChecker.Parse can be split: its declarations' text comes from the source it recorded."

            let seen = Dictionary<string list * string * DeclarationKind, int>(HashIdentity.Structural)

            decls
            |> List.mapi (fun i decl ->
                // As TcModuleOrNamespaceElementsNonMutRec: a declaration's scope runs from the next one to the end of
                // the enclosing module, namespace or file. This is the only place the end is computed.
                let scopem =
                    match List.tryItem (i + 1) decls with
                    | Some next -> unionRanges next.Range endm
                    | None -> unionRanges decl.Range endm

                let name, kind = DeclarationCheck.nameAndKind decl
                let ordinal = match seen.TryGetValue((modulePath, name, kind)) with | true, n -> n | _ -> 0
                seen[(modulePath, name, kind)] <- ordinal + 1

                let text = DeclarationCheck.textOfRange source decl.Range
                ParsedDeclaration({ ModulePath = modulePath; Name = name; Kind = kind; Ordinal = ordinal }, decl, scopem, text))
            |> Array.ofList

    static member CheckSignatureFile(ctx: ProjectContext, before: FileSignature list, parse: FSharpParseFileResults) : FileSignature =
        let state = ctx.State

        match parse.ParseTree with
        | ParsedInput.ImplFile _ -> invalidArg (nameof parse) "Expected a signature file."
        | ParsedInput.SigFile _ ->
            let tcState, moduleNamesDict = DeclarationCheck.stateBefore state before
            let input, moduleNamesDict = DeduplicateParsedInputModuleName moduleNamesDict parse.ParseTree

            match input with
            | ParsedInput.ImplFile _ -> invalidOp "unreachable"
            | ParsedInput.SigFile file ->
                let _, logger = DeclarationCheck.newLoggers state
                use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
                ResetGeneratedNames(input, state)
                let checkForErrors () = parse.ParseHadErrors || logger.ErrorCount > 0
                let amap = state.tcImports.GetImportMap()

                let _, sigFileType, createsGeneratedProvidedTypes =
                    CheckOneSigFile
                        (state.tcGlobals,
                         amap,
                         tcState.Ccu,
                         checkForErrors,
                         DeclarationCheck.conditionalDefines state,
                         TcResultsSink.NoSink,
                         state.tcConfig.internalTestSpanStackReferring,
                         state.tcConfig.diagnosticsOptions)
                        tcState.TcEnvFromSignatures
                        file
                    |> Cancellable.runWithoutCancellation

                let qualNameOfFile = file.QualifiedName
                let m = input.Range

                let apply =
                    AddSignatureFileToTcState (state.tcGlobals, amap, m, qualNameOfFile, sigFileType, createsGeneratedProvidedTypes)

                FileSignature(parse.FileName, apply, moduleNamesDict)

    static member BeginFile(ctx: ProjectContext, before: FileSignature list, parse: FSharpParseFileResults) : FileStart * DeclEnv =
        let state = ctx.State

        match parse.ParseTree with
        | ParsedInput.SigFile _ -> invalidArg (nameof parse) "Only implementation files are checked one declaration at a time."
        | ParsedInput.ImplFile _ ->
            let tcState, moduleNamesDict = DeclarationCheck.stateBefore state before
            let input, moduleNamesDict = DeduplicateParsedInputModuleName moduleNamesDict parse.ParseTree

            match input with
            | ParsedInput.SigFile _ -> invalidOp "unreachable"
            | ParsedInput.ImplFile file ->
                let capturing, logger = DeclarationCheck.newLoggers state
                use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
                use _ = FSharp.Compiler.Cancellable.UsingToken CancellationToken.None
                ResetGeneratedNames(input, state)

                let qualNameOfFile = file.QualifiedName
                let rootSigOpt = tcState.TryFindRootSig qualNameOfFile

                if tcState.HasRootImpl qualNameOfFile then
                    errorR (Error(FSComp.SR.buildImplementationAlreadyGiven (RichText.mkModule qualNameOfFile.Text), input.Range))

                let sink = TcResultsSinkImpl(state.tcGlobals)
                let cenv, envFile, _ = DeclarationCheck.newCheckerState state tcState rootSigOpt file sink
                let scope = EnterImplFileDeclarations cenv envFile file (DeclarationCheck.splitsFragment file)
                let diagnostics = DeclarationCheck.diagnosticsOf state parse.FileName capturing

                let start =
                    FileStart(
                        ctx,
                        parse,
                        file,
                        moduleNamesDict,
                        tcState,
                        rootSigOpt,
                        scope,
                        scope.Env.eModuleOrNamespaceTypeAccumulator.Value,
                        sink,
                        DeclarationCheck.leftoversOf cenv,
                        diagnostics,
                        logger.ErrorCount
                    )

                start, DeclEnv scope.Env

    /// Checks one declaration in the environment after an earlier one, or the first. Each call has its own checker
    /// state and accumulator, so calls may come in any order, again, or at the same time, and leave the file setup
    /// and other results as they were. It first undoes what the latest FinishFile on the same FileStart changed in
    /// the earlier declarations, so it sees them as their checks left them.
    static member CheckDeclaration(start: FileStart, envBefore: DeclEnv, decl: ParsedDeclaration, ct: CancellationToken) : DeclarationResult =
        start.UndoLastFinish()
        let state = start.Context.State
        let capturing, logger = DeclarationCheck.newLoggers state
        use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
        // Cancellable.run hands ct to the cancellable computation; code outside it calls CheckAndThrow, which reads
        // the ambient token, and nothing else sets that one.
        use _ = FSharp.Compiler.Cancellable.UsingToken ct
        let sink = TcResultsSinkImpl(state.tcGlobals)
        let cenv, _, _ = DeclarationCheck.newCheckerState state start.TcState start.RootSigOpt start.File sink
        let contentsBefore = envBefore.Env.eModuleOrNamespaceTypeAccumulator.Value

        // Combining builds new namespace entities, so only from an empty start is what such a fragment adds the
        // whole of what it leaves; it reads nothing else from the file's accumulator. Anything else starts from the
        // earlier declarations' contents, which its duplicate checks read.
        let deltaCombines = DeclarationCheck.combinesIntoFile decl.Syntax

        let contentsAtStart =
            if deltaCombines then
                Construct.NewEmptyModuleOrNamespaceType contentsBefore.ModuleOrNamespaceKind
            else
                contentsBefore

        let accumulator = ref contentsAtStart
        let env = { envBefore.Env with eModuleOrNamespaceTypeAccumulator = accumulator }

        let checkedDecl, envAfter, envAtEnd =
            let scope = start.Scope

            if not scope.ChecksDeclarations then
                ([], [], []), env, env
            else
                TcModuleOrNamespaceElementNonMutRec cenv scope.Parent scope.TypeNames decl.ScopeRange env decl.Syntax
                |> cenv.stackGuard.GuardCancellable
                |> Cancellable.run ct
                |> function
                    | ValueOrCancelled.Value result -> result
                    | ValueOrCancelled.Cancelled exn -> raise exn

        let delta = DeclarationCheck.contribution contentsAtStart accumulator.Value

        let leavesFreeTypars =
            not (Zset.isEmpty (GeneralizationHelpers.ComputeUngeneralizableTypars envAfter))

        DeclarationResult(
            decl.Key,
            DeclarationCheck.fingerprintOf delta checkedDecl,
            DeclarationCheck.diagnosticsOf state start.Parse.FileName capturing,
            logger.ErrorCount,
            leavesFreeTypars,
            DeclEnv envAfter,
            envAtEnd,
            checkedDecl,
            delta,
            deltaCombines,
            sink,
            DeclarationCheck.leftoversOf cenv
        )

    /// Builds the file from the declarations' results, in declaration order, closes its inference scope, and takes
    /// the declarations' final fingerprints.
    ///
    /// The file's accumulators, namespace entities and checker state are new each time. A 'module X.Y' file's module
    /// entity is not: it is the setup's, the parent of the declarations' values, shared by every finish on this
    /// FileStart. Each finish gives it a new type, so the last finish wins, and an earlier FileResult shows that
    /// finish's module contents.
    ///
    /// Closing the inference scope changes the declarations' typed trees in place: defaults and other solutions of
    /// their inference variables, trait solutions, closed augmentations. These are recorded and undone before the
    /// next finish or declaration check on this FileStart, so a finish over the same or other results gives what a
    /// full check would. Finishes on one FileStart are serialized, by its lock; a finish must not overlap a
    /// declaration check on the same FileStart.
    static member FinishFile(start: FileStart, results: DeclarationResult[]) : FileResult =
        lock start.Sync (fun () ->
            start.UndoLastFinish()
            let log = ResizeArray()
            let outer = MutationLog.Current
            MutationLog.Current <- log

            try
                DeclarationChecker.Finish(start, results)
            finally
                MutationLog.Current <- outer
                start.SetLastFinish log)

    static member private Finish(start: FileStart, results: DeclarationResult[]) : FileResult =
        let state = start.Context.State
        let parse = start.Parse
        let file = start.File
        let tcState = start.TcState
        let capturing, logger = DeclarationCheck.newLoggers state
        use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
        use _ = FSharp.Compiler.Cancellable.UsingToken CancellationToken.None
        let sink = TcResultsSinkImpl(state.tcGlobals)
        let cenv, envFile, moduleTyAcc = DeclarationCheck.newCheckerState state tcState start.RootSigOpt file sink
        start.Leftovers cenv

        for result in results do
            result.Leftovers cenv

        let scopeContents =
            DeclarationCheck.mergeDeltas start.ScopeContents [ for result in results -> result.Delta, result.DeltaCombines ]

        let envAtEnd =
            match Array.tryLast results with
            | Some last -> last.EnvAtEnd
            | None -> start.Scope.Env

        let fileContents =
            ExitImplFileDeclarations
                cenv
                envFile
                tcState.ImplicitOpenDeclarations
                start.Scope
                scopeContents
                [ for result in results -> result.Checked ]
                envAtEnd

        let earlierErrors = start.ErrorCount + (results |> Array.sumBy (fun result -> result.ErrorCount))
        let checkForErrors () = parse.ParseHadErrors || earlierErrors > 0 || logger.ErrorCount > 0

        let _topAttrs, implFile, tcEnvAtEnd, createsGeneratedProvidedTypes, ownSigForFile =
            CheckImplFileTail cenv checkForErrors tcState.TcEnvFromImpls start.RootSigOpt file moduleTyAcc fileContents

        let qualNameOfFile = file.QualifiedName

        let signature =
            DeclarationCheck.implFileSignature
                state
                parse.FileName
                qualNameOfFile
                implFile.Signature
                createsGeneratedProvidedTypes
                start.ModuleNamesDict

        let diagnostics =
            Array.concat
                [ yield parse.Diagnostics
                  yield start.Diagnostics
                  for result in results do
                      yield result.Diagnostics
                  yield DeclarationCheck.diagnosticsOf state parse.FileName capturing ]

        let fingerprints =
            Dictionary<DeclarationKey, string>(HashIdentity.Structural)

        for result in results do
            fingerprints[result.Key] <- DeclarationCheck.fingerprintOf result.Delta result.Checked

        let ccuSigForFile, _ =
            AddCheckResultsToTcState
                (state.tcGlobals,
                 state.tcImports.GetImportMap(),
                 start.RootSigOpt.IsSome,
                 None,
                 TcResultsSink.NoSink,
                 tcState.TcEnvFromImpls,
                 qualNameOfFile,
                 implFile.Signature)
                tcState

        let resolutions, symbolUses, openDeclarations =
            DeclarationCheck.mergeSinks
                state.tcGlobals
                [ yield start.Sink
                  for result in results do
                      yield result.Sink
                  yield sink ]

        let scope =
            TypeCheckInfo(
                state.tcConfig,
                state.tcGlobals,
                ccuSigForFile,
                ownSigForFile,
                tcState.Ccu,
                state.tcImports,
                tcEnvAtEnd.AccessRights,
                state.projectOptions.ProjectFileName,
                parse.FileName,
                Some state.projectOptions,
                resolutions,
                symbolUses,
                tcEnvAtEnd.NameEnv,
                None,
                Some implFile,
                openDeclarations
            )

        let checkResults =
            FSharpCheckFileResults(parse.FileName, diagnostics, Some scope, parse.DependencyFiles, None, true)

        FileResult(diagnostics, fingerprints, signature, checkResults)
