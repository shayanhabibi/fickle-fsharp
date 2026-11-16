// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.Benchmarks

open System
open System.Collections.Generic
open System.IO
open System.Runtime.CompilerServices
open System.Text
open System.Threading
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.CodeAnalysis.Declarations
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.EditorServices
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Compiler.Tokenization
open FSharp.Compiler.Xml
open BenchmarkDotNet.Attributes
open FSharp.Benchmarks.Common.Categories

[<AutoOpen>]
module private SymbolAndIwsamHelpers =

    let mkSdkProjectOptions (tempDir: string) (filePath: string) (outDllName: string) =
        let checker = FSharpChecker.Create(projectCacheSize = 200)
        let probePath = Path.Combine(tempDir, "ResolveSdkProbe.fsx")

        let probeOptions, probeDiags =
            checker.GetProjectOptionsFromScript(probePath, SourceText.ofString "let x = 1", assumeDotNetFramework = false, useSdkRefs = true)
            |> Async.RunSynchronously

        let probeErrors =
            probeDiags |> List.filter (fun (d: FSharpDiagnostic) -> d.Severity = FSharpDiagnosticSeverity.Error)

        if not probeErrors.IsEmpty then
            failwithf "Script SDK resolution had errors: %A" probeErrors

        let refs = probeOptions.OtherOptions |> Array.filter (fun o -> o.StartsWith("-r:", StringComparison.Ordinal))
        let outDll = Path.Combine(tempDir, outDllName)

        {
            ProjectFileName = Path.Combine(tempDir, Path.ChangeExtension(outDllName, ".fsproj"))
            ProjectId = None
            SourceFiles = [| filePath |]
            OtherOptions =
                [|
                    yield "--noframework"
                    yield "--target:library"
                    yield "--optimize-"
                    yield "--out:" + outDll
                    yield! refs
                |]
            ReferencedProjects = [||]
            IsIncompleteTypeCheckEnvironment = false
            UseScriptResolutionRules = false
            LoadTime = DateTime(2020, 1, 1)
            UnresolvedReferences = None
            OriginalLoadReferences = []
            Stamp = Some 0L
        }

    let mkSymbolAndInterfaceSource (variantLiteral: int) =
        let sb = StringBuilder()
        sb.AppendLine("module Bench.Symbols") |> ignore
        sb.AppendLine("") |> ignore
        sb.AppendLine("open System") |> ignore
        sb.AppendLine("open System.Collections.Generic") |> ignore
        sb.AppendLine("") |> ignore
        sb.AppendLine("type IntList = int list") |> ignore
        sb.AppendLine("type Pair<'a, 'b> = 'a * 'b") |> ignore
        sb.AppendLine("type Lookup<'v> = IReadOnlyDictionary<string, 'v>") |> ignore
        sb.AppendLine("") |> ignore
        sb.AppendLine("type RecordItem =") |> ignore
        sb.AppendLine("    { Id: int") |> ignore
        sb.AppendLine("      Name: string") |> ignore
        sb.AppendLine("      Tags: IntList }") |> ignore
        sb.AppendLine("") |> ignore

        for i in 0..59 do
            let lit = if i = 59 then variantLiteral else (i + 1)
            sb.AppendLine($"let computeSym%02d{i}") |> ignore
            sb.AppendLine("    (d: IDisposable)") |> ignore
            sb.AppendLine("    (xs: IEnumerable<int>)") |> ignore
            sb.AppendLine("    (ys: IReadOnlyList<string>)") |> ignore
            sb.AppendLine("    (cmp: IComparable<int>)") |> ignore
            sb.AppendLine("    (eq: IEquatable<string>)") |> ignore
            sb.AppendLine("    (fmt: IFormattable)") |> ignore
            sb.AppendLine("    (pair: Pair<int, string>)") |> ignore
            sb.AppendLine("    (xs2: IntList)") |> ignore
            sb.AppendLine("    (lookup: Lookup<int>)") |> ignore
            sb.AppendLine("    : IntList =") |> ignore
            sb.AppendLine("    let c = cmp.CompareTo(xs2.Head)") |> ignore
            sb.AppendLine("    let _s = fmt.ToString(null, null)") |> ignore
            sb.AppendLine("    let m = if eq.Equals(ys[0]) then lookup.Count else 0") |> ignore
            sb.AppendLine($"    [ c; m; (if isNull d then 0 else 1); (xs |> Seq.length); fst pair; %d{lit} ]") |> ignore
            sb.AppendLine("") |> ignore

        sb.ToString()

[<MemoryDiagnoser>]
[<BenchmarkCategory(ShortCategory)>]
type SymbolAndIwsamBenchmarks() =

    let tempDir = Path.Combine(Path.GetTempPath(), $"fcs-sym-iwsam-{Guid.NewGuid():N}")
    let filePath = Path.Combine(tempDir, "SymbolAndIwsam.fs")
    let mutable checker = Unchecked.defaultof<FSharpChecker>
    let mutable options = Unchecked.defaultof<FSharpProjectOptions>
    let mutable sourceTextA = Unchecked.defaultof<ISourceText>
    let mutable sourceTextB = Unchecked.defaultof<ISourceText>
    let mutable checkedEntities: IList<FSharpEntity> = [||]
    let mutable step = 0

    [<GlobalSetup>]
    member this.Setup() =
        Directory.CreateDirectory(tempDir) |> ignore
        let srcA = mkSymbolAndInterfaceSource 101
        let srcB = mkSymbolAndInterfaceSource 202
        sourceTextA <- SourceText.ofString srcA
        sourceTextB <- SourceText.ofString srcB
        File.WriteAllText(filePath, srcA)

        checker <- FSharpChecker.Create(projectCacheSize = 200, keepAssemblyContents = true)
        options <- mkSdkProjectOptions tempDir filePath "SymbolAndIwsam.dll"

        let _, answer = checker.ParseAndCheckFileInProject(filePath, 0, sourceTextA, options) |> Async.RunSynchronously

        match answer with
        | FSharpCheckFileAnswer.Aborted -> failwith "Setup check aborted"
        | FSharpCheckFileAnswer.Succeeded results ->
            let errors = results.Diagnostics |> Array.filter (fun d -> d.Severity = FSharpDiagnosticSeverity.Error)

            if errors.Length > 0 then
                failwithf "Setup check had errors: %A" errors

            checkedEntities <- results.PartialAssemblySignature.Entities

            let memberCount = checkedEntities |> Seq.sumBy (fun e -> e.MembersFunctionsAndValues.Count)

            if memberCount < 60 then
                failwithf "Expected at least 60 module functions, got %d" memberCount

            if this.InspectSymbolsRepeatedly() <= 0 then
                failwith "Expected positive symbol inspection checksum"

    [<Benchmark>]
    member _.InspectSymbolsRepeatedly() : int =
        let mutable acc = 0

        for entity in checkedEntities do
            for m in entity.MembersFunctionsAndValues do
                for _pass in 1..3 do
                    let groups = m.CurriedParameterGroups

                    for group in groups do
                        for p in group do
                            let ty = p.Type

                            if ty.IsAbbreviation then
                                acc <- acc + 1

                            if ty.HasTypeDefinition || ty.IsTupleType || ty.IsFunctionType || ty.IsAnonRecordType then
                                acc <- acc + ty.GenericArguments.Count

                    let retTy = m.ReturnParameter.Type

                    if retTy.IsAbbreviation then
                        acc <- acc + 1

                    if retTy.HasTypeDefinition then
                        acc <- acc + 2

        acc

    [<Benchmark>]
    member _.WarmCheckFileWithInterfaces() : int =
        step <- step + 1
        let srcText = if step &&& 1 = 0 then sourceTextA else sourceTextB
        let _, answer = checker.ParseAndCheckFileInProject(filePath, step, srcText, options) |> Async.RunSynchronously

        match answer with
        | FSharpCheckFileAnswer.Aborted -> failwith "Check aborted"
        | FSharpCheckFileAnswer.Succeeded results ->
            let errors = results.Diagnostics |> Array.filter (fun d -> d.Severity = FSharpDiagnosticSeverity.Error)

            if errors.Length > 0 then
                failwithf "Check had errors: %A" errors

            results.Diagnostics.Length

    [<GlobalCleanup>]
    member _.Cleanup() =
        try
            Directory.Delete(tempDir, true)
        with _ ->
            ()

[<AutoOpen>]
module private DeclarationCheckerBenchHelpers =

    let mkDeclarationsSource (bodyConst: int) (docLabel: string) (extraLinesAfterFirst: int) =
        let sb = StringBuilder()
        sb.AppendLine("module Bench.Declarations") |> ignore
        sb.AppendLine("") |> ignore

        for i in 0..59 do
            let doc = if i = 30 then docLabel else $"Step %02d{i}"
            sb.AppendLine($"/// {doc}") |> ignore

            if i = 30 then
                sb.AppendLine($"let compute%02d{i} (x: int) =") |> ignore
                sb.AppendLine($"    let items = [ x; x + 1; x + 2 ] |> List.map (fun v -> v * 2 + %d{bodyConst})") |> ignore
                sb.AppendLine("    items |> List.sum") |> ignore
            elif i >= 31 && i <= 35 then
                sb.AppendLine($"let compute%02d{i} (x: int) =") |> ignore
                sb.AppendLine("    let baseVal = compute30 x") |> ignore
                sb.AppendLine($"    let items = [ baseVal; x + %d{i}; x + %d{i + 1} ]") |> ignore
                sb.AppendLine("    items |> List.sum") |> ignore
            else
                sb.AppendLine($"let compute%02d{i} (x: int) =") |> ignore
                sb.AppendLine($"    let items = [ x; x + %d{i + 1}; x + %d{i + 2} ] |> List.map (fun v -> v * 2 + 1)") |> ignore
                sb.AppendLine("    items |> List.sum") |> ignore

            sb.AppendLine("") |> ignore

            if i = 0 then
                for _ in 1..extraLinesAfterFirst do
                    sb.AppendLine("") |> ignore

        sb.ToString()

    let checkAllDeclarations (ctx: ProjectContext) (parse: FSharpParseFileResults) =
        let start, env0 = DeclarationChecker.BeginFile(ctx, [], parse)
        let decls = DeclarationChecker.Split parse
        let results = Array.zeroCreate<DeclarationResult> decls.Length
        let envsBefore = Array.zeroCreate<DeclarationEnvironment> decls.Length
        let mutable env = env0

        for i in 0 .. decls.Length - 1 do
            envsBefore[i] <- env
            let r = DeclarationChecker.CheckDeclaration(start, env, decls[i], CancellationToken.None)
            results[i] <- r
            env <- DeclarationChecker.ExtendEnv(env, r)

        let fileRes = DeclarationChecker.FinishFile(start, results, parse)

        if not (Array.isEmpty fileRes.Diagnostics) then
            failwithf "Expected zero diagnostics in setup, got %A" fileRes.Diagnostics

        start, decls, envsBefore, results, fileRes

    let tryFindBindingDocInParse (parse: FSharpParseFileResults) (owner: FSharpDocOwner) : XmlDoc voption =
        if not (String.Equals(owner.FileName, parse.FileName, StringComparison.OrdinalIgnoreCase)) then
            ValueNone
        else
            let targetPath = owner.Path
            let mutable found = ValueNone

            let rec searchDecls (modulePrefix: string) (decls: SynModuleDecl list) =
                for decl in decls do
                    if found.IsNone then
                        match decl with
                        | SynModuleDecl.Let(bindings = bindings) ->
                            for SynBinding(xmlDoc = xmlDoc; headPat = pat) in bindings do
                                if found.IsNone then
                                    match pat with
                                    | SynPat.LongIdent(longDotId = SynLongIdent(id = ident :: _)) ->
                                        let candidatePath = "V:" + modulePrefix + "." + ident.idText

                                        if String.Equals(candidatePath, targetPath, StringComparison.Ordinal) then
                                            found <- ValueSome(xmlDoc.ToXmlDoc(false, None))
                                    | _ -> ()
                        | SynModuleDecl.NestedModule(moduleInfo = compInfo; decls = innerDecls) ->
                            let nested = compInfo.LongIdent |> List.map _.idText |> String.concat "."
                            let nextPrefix = if String.IsNullOrEmpty modulePrefix then nested else modulePrefix + "." + nested
                            searchDecls nextPrefix innerDecls
                        | _ -> ()

            match parse.ParseTree with
            | ParsedInput.ImplFile(ParsedImplFileInput(contents = modules)) ->
                for SynModuleOrNamespace(longId = lid; decls = decls) in modules do
                    let modPath = lid |> List.map _.idText |> String.concat "."
                    searchDecls modPath decls
            | _ -> ()

            found

    let docXmlTextOfTooltip (ToolTipText elements) (composeOpt: (FSharpDocSource -> FSharpXmlDoc) option) (sources: FSharpDocSource option list) =
        let mutable rest = sources
        let sb = StringBuilder()

        let next () =
            match rest with
            | head :: tail ->
                rest <- tail
                head
            | [] -> None

        for elem in elements do
            match elem with
            | ToolTipElement.Group items ->
                for item in items do
                    let xmlDoc =
                        match composeOpt, next () with
                        | Some compose, Some src -> compose src
                        | _ -> item.XmlDoc

                    match xmlDoc with
                    | FSharpXmlDoc.FromXmlText doc -> sb.Append(doc.GetXmlText()) |> ignore
                    | FSharpXmlDoc.FromXmlFile(_, xmlSig) -> sb.Append(xmlSig) |> ignore
                    | FSharpXmlDoc.None -> ()
            | _ -> ()

        sb.ToString()

[<MemoryDiagnoser>]
[<BenchmarkCategory(ShortCategory)>]
type DeclarationCheckerBenchmarks() =

    let tempDir = Path.Combine(Path.GetTempPath(), $"fcs-decl-bench-{Guid.NewGuid():N}")
    let filePath = Path.Combine(tempDir, "DeclarationsBench.fs")
    let wholeFilePath = Path.Combine(tempDir, "WholeFileBench.fs")
    let tooltipFilePath = Path.Combine(tempDir, "TooltipBench.fs")

    let mutable wholeChecker = Unchecked.defaultof<FSharpChecker>
    let mutable tooltipChecker = Unchecked.defaultof<FSharpChecker>
    let mutable wholeOptions = Unchecked.defaultof<FSharpProjectOptions>
    let mutable tooltipOptions = Unchecked.defaultof<FSharpProjectOptions>
    let mutable ctx = Unchecked.defaultof<ProjectContext>

    let mutable bodyEditA = ""
    let mutable bodyEditB = ""
    let mutable bodyTextA = Unchecked.defaultof<ISourceText>
    let mutable bodyTextB = Unchecked.defaultof<ISourceText>

    let mutable shiftedA = ""
    let mutable shiftedB = ""

    let mutable commentA = ""
    let mutable commentB = ""
    let mutable commentTextA = Unchecked.defaultof<ISourceText>
    let mutable commentTextB = Unchecked.defaultof<ISourceText>

    let mutable editIdx = 0
    let mutable basePrintEdit = ""

    let mutable bodyCutoffStart = Unchecked.defaultof<FSharp.Compiler.CodeAnalysis.Declarations.FileStart>
    let mutable bodyCutoffEnvsBefore = Array.empty<FSharp.Compiler.CodeAnalysis.Declarations.DeclarationEnvironment>
    let mutable bodyCutoffResults = Array.empty<FSharp.Compiler.CodeAnalysis.Declarations.DeclarationResult>

    let mutable bodyFullStart = Unchecked.defaultof<FSharp.Compiler.CodeAnalysis.Declarations.FileStart>
    let mutable bodyFullEnvsBefore = Array.empty<FSharp.Compiler.CodeAnalysis.Declarations.DeclarationEnvironment>
    let mutable bodyFullResults = Array.empty<FSharp.Compiler.CodeAnalysis.Declarations.DeclarationResult>

    let mutable shiftStart = Unchecked.defaultof<FSharp.Compiler.CodeAnalysis.Declarations.FileStart>
    let mutable shiftResults = Array.empty<FSharp.Compiler.CodeAnalysis.Declarations.DeclarationResult>

    let mutable commentBaseDecls = Array.empty<FSharp.Compiler.CodeAnalysis.Declarations.ParsedDeclaration>
    let mutable commentCheckResults = Unchecked.defaultof<FSharpCheckFileResults>

    let mutable hoverLine = 0
    let mutable hoverColEnd = 0
    let mutable hoverLineText = ""

    let mutable wholeStep = 0
    let mutable wholeDeclStep = 0
    let mutable cutoffStep = 0
    let mutable fullStep = 0
    let mutable shiftStep = 0
    let mutable commentWholeStep = 0
    let mutable commentPartsStep = 0

    [<GlobalSetup>]
    member _.Setup() =
        Directory.CreateDirectory(tempDir) |> ignore

        bodyEditA <- DeclarationCheckerBenchHelpers.mkDeclarationsSource 101 "Summary Alpha for compute30." 0
        bodyEditB <- DeclarationCheckerBenchHelpers.mkDeclarationsSource 202 "Summary Alpha for compute30." 0
        bodyTextA <- SourceText.ofString bodyEditA
        bodyTextB <- SourceText.ofString bodyEditB

        shiftedA <- DeclarationCheckerBenchHelpers.mkDeclarationsSource 101 "Summary Alpha for compute30." 2
        shiftedB <- DeclarationCheckerBenchHelpers.mkDeclarationsSource 101 "Summary Alpha for compute30." 4

        commentA <- DeclarationCheckerBenchHelpers.mkDeclarationsSource 101 "Summary Alpha for compute30." 0
        commentB <- DeclarationCheckerBenchHelpers.mkDeclarationsSource 101 "Summary Beta for compute30." 0
        commentTextA <- SourceText.ofString commentA
        commentTextB <- SourceText.ofString commentB

        File.WriteAllText(filePath, bodyEditA)
        File.WriteAllText(wholeFilePath, bodyEditA)
        File.WriteAllText(tooltipFilePath, commentA)

        // Find the `compute30` call inside `compute31` so tooltips resolve the documented `compute30` symbol.
        let lines = bodyEditA.Replace("\r\n", "\n").Split('\n')
        let callLineIdx = lines |> Array.findIndex (fun l -> l.Contains("compute30 x", StringComparison.Ordinal))
        hoverLine <- callLineIdx + 1
        hoverLineText <- lines[callLineIdx]
        hoverColEnd <- hoverLineText.IndexOf("compute30", StringComparison.Ordinal) + "compute30".Length

        wholeChecker <- FSharpChecker.Create(projectCacheSize = 200, keepAssemblyContents = true)
        tooltipChecker <- FSharpChecker.Create(projectCacheSize = 200, keepAssemblyContents = true)
        wholeOptions <- mkSdkProjectOptions tempDir wholeFilePath "WholeFileBench.dll"
        tooltipOptions <- mkSdkProjectOptions tempDir tooltipFilePath "TooltipBench.dll"
        let declOptions = mkSdkProjectOptions tempDir filePath "DeclarationsBench.dll"

        // Warm both FSharpChecker instances once so TcImports and project setup are excluded from warm ops.
        match wholeChecker.ParseAndCheckFileInProject(wholeFilePath, 0, bodyTextA, wholeOptions) |> Async.RunSynchronously with
        | _, FSharpCheckFileAnswer.Succeeded r when r.Diagnostics.Length = 0 -> ()
        | _, other -> failwithf "Warmup wholeChecker failed: %A" other

        match tooltipChecker.ParseAndCheckFileInProject(tooltipFilePath, 0, commentTextA, tooltipOptions) |> Async.RunSynchronously with
        | _, FSharpCheckFileAnswer.Succeeded r when r.Diagnostics.Length = 0 -> ()
        | _, other -> failwithf "Warmup tooltipChecker failed: %A" other

        ctx <-
            FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CreateProject(declOptions)
            |> Async.RunSynchronously

        let parseCutoff = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, bodyEditA)
        let s1, decls1, envs1, res1, _ = DeclarationCheckerBenchHelpers.checkAllDeclarations ctx parseCutoff

        if decls1.Length < 60 then
            failwithf "Expected at least 60 declarations, got %d" decls1.Length

        editIdx <- decls1 |> Array.findIndex (fun d -> d.Key.Name = "compute30")
        basePrintEdit <- res1[editIdx].Fingerprint
        bodyCutoffStart <- s1
        bodyCutoffEnvsBefore <- envs1
        bodyCutoffResults <- res1

        let parseFull = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, bodyEditA)
        let s2, _, envs2, res2, _ = DeclarationCheckerBenchHelpers.checkAllDeclarations ctx parseFull
        bodyFullStart <- s2
        bodyFullEnvsBefore <- envs2
        bodyFullResults <- res2

        let parseShift = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, bodyEditA)
        let s3, _, _, res3, _ = DeclarationCheckerBenchHelpers.checkAllDeclarations ctx parseShift
        shiftStart <- s3
        shiftResults <- res3

        let parseComment = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, commentA)
        let _, declsComment, _, _, commentFileRes = DeclarationCheckerBenchHelpers.checkAllDeclarations ctx parseComment
        commentBaseDecls <- declsComment
        commentCheckResults <- commentFileRes.CheckResults

        // Validate setup invariants: GetToolTipParts must recompose comments without re-typechecking.
        let parseCommentB = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, commentB)
        let declsCommentB = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Split parseCommentB

        if not (declsCommentB[editIdx].IsUnchangedFrom(commentBaseDecls[editIdx])) then
            failwith "Expected IsUnchangedFrom = true for comment-only edit"

        let tip, sources =
            commentCheckResults.GetToolTipParts(hoverLine, hoverColEnd, hoverLineText, [ "compute30" ], FSharpTokenTag.Identifier)

        let recomposed =
            DeclarationCheckerBenchHelpers.docXmlTextOfTooltip
                tip
                (Some(fun src -> src.Compose(DeclarationCheckerBenchHelpers.tryFindBindingDocInParse parseCommentB)))
                sources

        if not (recomposed.Contains("Summary Beta", StringComparison.Ordinal)) then
            failwithf "Expected GetToolTipParts to recompose updated comment 'Summary Beta', got: %s" recomposed

    [<Benchmark(Baseline = true)>]
    member _.BodyEdit_WholeFile_FSharpChecker() : int =
        wholeStep <- wholeStep + 1
        let srcText = if wholeStep &&& 1 = 1 then bodyTextB else bodyTextA
        let _, answer = wholeChecker.ParseAndCheckFileInProject(wholeFilePath, wholeStep, srcText, wholeOptions) |> Async.RunSynchronously

        match answer with
        | FSharpCheckFileAnswer.Aborted -> failwith "Whole-file check aborted"
        | FSharpCheckFileAnswer.Succeeded res ->
            if res.Diagnostics.Length > 0 then
                failwithf "Whole-file check had diagnostics: %A" res.Diagnostics

            res.Diagnostics.Length

    [<Benchmark>]
    member _.BodyEdit_WholeFile_DeclarationChecker() : int =
        // CheckFile validates types and signature without building TcResultsSink unless CheckResults is read.
        wholeDeclStep <- wholeDeclStep + 1
        let src = if wholeDeclStep &&& 1 = 1 then bodyEditB else bodyEditA
        let parse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, src)
        let fileRes = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CheckFile(ctx, [], parse)

        if fileRes.Diagnostics.Length > 0 then
            failwithf "CheckFile had diagnostics: %A" fileRes.Diagnostics

        fileRes.Signature.Fingerprint.Length

    [<Benchmark>]
    member _.BodyEdit_Incremental_Cutoff() : int =
        cutoffStep <- cutoffStep + 1
        let src = if cutoffStep &&& 1 = 1 then bodyEditB else bodyEditA
        let parse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, src)
        let decls = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Split parse

        let r =
            FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CheckDeclaration(
                bodyCutoffStart,
                bodyCutoffEnvsBefore[editIdx],
                decls[editIdx],
                CancellationToken.None
            )

        if r.Fingerprint <> basePrintEdit then
            failwith "Expected unchanged declaration signature fingerprint for body-only edit"

        bodyCutoffResults[editIdx] <- r
        let fileRes = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.FinishFile(bodyCutoffStart, bodyCutoffResults, parse)

        if fileRes.Diagnostics.Length > 0 then
            failwithf "FinishFile had diagnostics: %A" fileRes.Diagnostics

        fileRes.Reused

    [<Benchmark>]
    member _.BodyEdit_Incremental_WithCheckResults() : bool =
        fullStep <- fullStep + 1
        let src = if fullStep &&& 1 = 1 then bodyEditB else bodyEditA
        let parse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, src)
        let decls = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Split parse

        let r =
            FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CheckDeclaration(
                bodyFullStart,
                bodyFullEnvsBefore[editIdx],
                decls[editIdx],
                CancellationToken.None
            )

        if r.Fingerprint <> basePrintEdit then
            failwith "Expected unchanged declaration signature fingerprint for body-only edit"

        bodyFullResults[editIdx] <- r
        let fileRes = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.FinishFile(bodyFullStart, bodyFullResults, parse)
        let checkRes = fileRes.CheckResults

        if checkRes.Diagnostics.Length > 0 then
            failwithf "CheckResults had diagnostics: %A" checkRes.Diagnostics

        checkRes.HasFullTypeCheckInfo

    [<Benchmark>]
    member _.LineShift_Incremental_DeclarationChecker() : int =
        shiftStep <- shiftStep + 1
        let src = if shiftStep &&& 1 = 1 then shiftedA else shiftedB
        let parse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, src)
        let decls = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Split parse
        let mutable shiftedCount = 0

        for i in 0 .. decls.Length - 1 do
            if decls[i].Range.StartLine <> shiftResults[i].Declaration.Range.StartLine then
                match FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Shift(shiftResults[i], decls[i]) with
                | ValueSome shifted ->
                    shiftResults[i] <- shifted
                    shiftedCount <- shiftedCount + 1
                | ValueNone -> failwithf "Shift refused declaration %d (%s)" i decls[i].Key.Name

        if shiftedCount < 59 then
            failwithf "Expected at least 59 shifted declarations, got %d" shiftedCount

        let fileRes = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.FinishFile(shiftStart, shiftResults, parse)

        if fileRes.Diagnostics.Length > 0 then
            failwithf "FinishFile after Shift had diagnostics: %A" fileRes.Diagnostics

        fileRes.Reused

    [<Benchmark>]
    member _.CommentEdit_WholeFile_GetToolTip() : int =
        commentWholeStep <- commentWholeStep + 1
        let srcText = if commentWholeStep &&& 1 = 1 then commentTextB else commentTextA
        let _, answer = tooltipChecker.ParseAndCheckFileInProject(tooltipFilePath, commentWholeStep, srcText, tooltipOptions) |> Async.RunSynchronously

        match answer with
        | FSharpCheckFileAnswer.Aborted -> failwith "Whole-file tooltip check aborted"
        | FSharpCheckFileAnswer.Succeeded res ->
            let (ToolTipText elements) = res.GetToolTip(hoverLine, hoverColEnd, hoverLineText, [ "compute30" ], FSharpTokenTag.Identifier)
            elements.Length

    [<Benchmark>]
    member _.CommentEdit_NoRecheck_GetToolTipParts() : int =
        commentPartsStep <- commentPartsStep + 1
        let src = if commentPartsStep &&& 1 = 1 then commentB else commentA
        let parse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, src)
        let decls = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Split parse

        if not (decls[editIdx].IsUnchangedFrom(commentBaseDecls[editIdx])) then
            failwith "Comment-only edit unexpectedly changed declaration syntax"

        let tip, sources =
            commentCheckResults.GetToolTipParts(hoverLine, hoverColEnd, hoverLineText, [ "compute30" ], FSharpTokenTag.Identifier)

        let text =
            DeclarationCheckerBenchHelpers.docXmlTextOfTooltip
                tip
                (Some(fun docSrc -> docSrc.Compose(DeclarationCheckerBenchHelpers.tryFindBindingDocInParse parse)))
                sources

        text.Length

    [<GlobalCleanup>]
    member _.Cleanup() =
        try
            Directory.Delete(tempDir, true)
        with _ ->
            ()

/// Retained live-heap comparison for a 60-declaration checked file after ProjectContext/TcImports warmup.
///
/// Not a BDN benchmark: run from Program.fs with the `declaration-memory` argument.
module DeclarationMemoryProbe =

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let private keepClosedSignature (ctx: FSharp.Compiler.CodeAnalysis.Declarations.ProjectContext) filePath src =
        let parse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, src)
        let fileRes = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CheckFile(ctx, [], parse)
        fileRes.Signature

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let private keepIncrementalState (ctx: FSharp.Compiler.CodeAnalysis.Declarations.ProjectContext) filePath src =
        let parse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, filePath, src)
        let start, _, _, results, fileRes = DeclarationCheckerBenchHelpers.checkAllDeclarations ctx parse
        box (start, results, fileRes.Signature)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let private keepFullCheckResults (checker: FSharpChecker) filePath srcText options =
        let _, answer = checker.ParseAndCheckFileInProject(filePath, 1, srcText, options) |> Async.RunSynchronously

        match answer with
        | FSharpCheckFileAnswer.Succeeded res -> res
        | FSharpCheckFileAnswer.Aborted -> failwith "Probe check aborted"

    let private printRow (label: string) (before: int64) (after: int64) (allocated: int64) =
        printfn "| %-30s | %10.2f KB | %10.2f KB |" label (float (after - before) / 1024.0) (float allocated / 1024.0)

    let run () =
        let tempDir = Path.Combine(Path.GetTempPath(), $"fcs-decl-mem-{Guid.NewGuid():N}")
        Directory.CreateDirectory(tempDir) |> ignore

        try
            let warmPath = Path.Combine(tempDir, "Warmup.fs")
            let targetPath = Path.Combine(tempDir, "Target60.fs")
            let warmSrc = "module Bench.Warmup\nlet ready = 1\n"
            let targetSrc = DeclarationCheckerBenchHelpers.mkDeclarationsSource 101 "Summary Alpha for compute30." 0
            File.WriteAllText(warmPath, warmSrc)
            File.WriteAllText(targetPath, targetSrc)

            let baseOpts = mkSdkProjectOptions tempDir targetPath "MemProbe.dll"
            let multiOpts = { baseOpts with SourceFiles = [| warmPath; targetPath |] }

            printfn "Declaration retention probe (60-declaration file, post-warmup TcImports):"
            printfn "| %-30s | %13s | %13s |" "State Retained" "Retained" "Allocated"
            printfn "| %s | %13s | %13s |" (String('-', 30)) "------------:" "------------:"

            // 1. Closed-file FileSignature only (demoted project-graph file state).
            do
                let ctx =
                    FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CreateProject(baseOpts)
                    |> Async.RunSynchronously

                let warmParse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, targetPath, warmSrc)
                FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CheckFile(ctx, [], warmParse) |> ignore
                forceGC ()
                let before = GC.GetTotalMemory true
                let allocBefore = GC.GetTotalAllocatedBytes true
                let sigOnly = keepClosedSignature ctx targetPath targetSrc
                let allocated = GC.GetTotalAllocatedBytes true - allocBefore
                forceGC ()
                let after = GC.GetTotalMemory true
                printRow "ClosedFile_FileSignature" before after allocated
                GC.KeepAlive sigOnly
                GC.KeepAlive ctx

            // 2. Open-file incremental state (FileStart + DeclarationResult[] + FileSignature, no CheckResults).
            do
                let ctx =
                    FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CreateProject(baseOpts)
                    |> Async.RunSynchronously

                let warmParse = FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.Parse(ctx, targetPath, warmSrc)
                FSharp.Compiler.CodeAnalysis.Declarations.DeclarationChecker.CheckFile(ctx, [], warmParse) |> ignore
                forceGC ()
                let before = GC.GetTotalMemory true
                let allocBefore = GC.GetTotalAllocatedBytes true
                let incState = keepIncrementalState ctx targetPath targetSrc
                let allocated = GC.GetTotalAllocatedBytes true - allocBefore
                forceGC ()
                let after = GC.GetTotalMemory true
                printRow "OpenFile_IncrementalState" before after allocated
                GC.KeepAlive incState
                GC.KeepAlive ctx

            // 3. Standard FSharpChecker full FSharpCheckFileResults (warm IncrementalBuilder via Warmup.fs).
            do
                let checker = FSharpChecker.Create(projectCacheSize = 200, keepAssemblyContents = true)
                let warmText = SourceText.ofString warmSrc
                let targetText = SourceText.ofString targetSrc
                checker.ParseAndCheckFileInProject(warmPath, 0, warmText, multiOpts) |> Async.RunSynchronously |> ignore
                forceGC ()
                let before = GC.GetTotalMemory true
                let allocBefore = GC.GetTotalAllocatedBytes true
                let checkRes = keepFullCheckResults checker targetPath targetText multiOpts
                let allocated = GC.GetTotalAllocatedBytes true - allocBefore
                forceGC ()
                let after = GC.GetTotalMemory true
                printRow "FSharpChecker_CheckFileResults" before after allocated
                GC.KeepAlive checkRes
                GC.KeepAlive checker
        finally
            try
                Directory.Delete(tempDir, true)
            with _ ->
                ()
