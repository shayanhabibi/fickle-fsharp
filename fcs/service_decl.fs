// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.Declarations

open System
open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Threading

open Internal.Utilities.Collections
open Internal.Utilities.Library
open Internal.Utilities.Library.Extras

open FSharp.Compiler
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.CheckDeclarations
open FSharp.Compiler.CheckExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.CompilerDiagnostics
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.GraphChecking
open FSharp.Compiler.NameResolution
open FSharp.Compiler.ParseAndCheckInputs
open FSharp.Compiler.SourceCodeServices
open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTreeOps
open FSharp.Compiler.TcGlobals
open FSharp.Compiler.Text
open FSharp.Compiler.Text.Range
open FSharp.Compiler.TypedTree
open FSharp.Compiler.TypedTreeBasics
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
    { /// The file's module or namespace, then the nested modules the declaration is in
      ModulePath: string list
      Name: string
      Kind: DeclarationKind
      /// The number of earlier declarations of the file with the same module path, name and kind
      Ordinal: int }

/// A declaration of the project that a typed use resolves to: the declaration with Key in File. Key is None for what a
/// signature file declares, which is checked whole: a use of it depends on that file's text.
type DeclarationRef = { File: string; Key: DeclarationKey option }

/// The names a declaration defines and uses, from its syntax. A use can resolve to a definition through any of the
/// lists: Defines holds every kind of name, so a dependency on a name is a dependency on every declaration defining it.
type DeclarationContent =
    { /// Values, types, union cases, record fields, members, custom operation names and modules, including those
      /// inside a nested module or namespace fragment the declaration holds whole
      Defines: string[]
      /// Names resolved in the environment: unqualified identifiers, every segment of qualified ones, types, attributes
      /// (with and without the Attribute suffix) and opened modules. Locally bound names are included.
      Uses: string[]
      /// Names after a dot and members constructs call implicitly (computation expression builders, enumerators,
      /// indexers, trait calls): each may be a member or extension of any type
      MemberUses: string[]
      /// Record labels and union cases, including names after a dot, which can be record fields
      FieldOrCaseUses: string[]
      /// Something resolves to a name the syntax does not show, such as the `?` operator: the declaration depends on
      /// every earlier declaration
      HasUnresolvable: bool
      /// Every later declaration depends on this one: open, an [<AutoOpen>] module, a type or module abbreviation,
      /// a module-level do, an attribute declaration, a hash directive, or a custom operation whose name is unknown.
      /// #nowarn and #warnon are not declarations: lexing turns them into warning scopes by position, and FinishFile
      /// filters every declaration's diagnostics with the scopes of the parse it is given, so they need no dependency.
      AffectsAllLater: bool
      /// The names, as written, of the types the declaration augments (`type T with ...`; a group `type A with ... and
      /// B with ...` augments both), sorted; empty for anything else. Checking an intrinsic augmentation adds its
      /// members to T's entity, which T's result holds, so T's declaration and its augmentations re-check together,
      /// T first, whenever any of them re-checks: re-checking T gives a new entity, which only the augmentations
      /// checked after it extend.
      Augments: string[] }

/// A top-level declaration of an implementation file, or a declaration of a non-recursive nested module, or the
/// header of such a module (its attributes and name, which the module's declarations are checked inside).
[<Sealed>]
type ParsedDeclaration
    internal
    (
        key: DeclarationKey,
        decl: SynModuleDecl,
        range: range,
        scopem: range,
        text: string,
        headerInputs: string,
        within: DeclarationKey option,
        siblings: SynModuleDecl list,
        depth: int,
        isModuleHeader: bool
    ) =
    member _.Key = key
    /// The declaration's range; for a module header, from its start to the '=' after the module's name.
    member _.Range = range
    /// A hash of the declaration's source text. Unequal hashes mean the text changed; equal ones do not prove
    /// it is the same, so compare Text for that.
    member _.SyntaxHash = hash text
    /// The declaration's source text, from the start of its range to its end. Text alone does not decide a module
    /// header is unchanged: use IsUnchangedFrom, which also compares HeaderInputs.
    member _.Text = text
    /// For a module, what checking it reads beyond its text: whether a type of the same name is among the
    /// declarations around it (which gives the module the Module suffix), and for a module header the type names of
    /// its body (which its declarations, and the modules among them, are checked with). Empty for other declarations.
    member _.HeaderInputs = headerInputs
    /// The key of the module header this declaration is directly inside, if any. A re-checked header gives the module
    /// a new entity, the parent of its declarations' values, so every declaration under it must be checked again:
    /// an edge from the header to them with no fingerprint cutoff.
    member _.Within = within
    /// Whether checking this declaration reads the same syntax as checking the other: same Text and HeaderInputs.
    member x.IsUnchangedFrom(other: ParsedDeclaration) =
        String.Equals(text, other.Text, StringComparison.Ordinal) && String.Equals(headerInputs, other.HeaderInputs, StringComparison.Ordinal)
    /// The whole declaration; for a module header, the whole module.
    member internal _.Syntax = decl
    /// The range the declaration's definitions are in scope for, as TcModuleOrNamespaceElementsNonMutRec gives it.
    member internal _.ScopeRange = scopem
    /// How many nested modules the declaration is in, below the file's scope
    member internal _.Depth = depth
    member internal _.IsModuleHeader = isModuleHeader
    /// The declarations of the enclosing module or namespace, this one included: a module's suffix reads their types
    member internal _.Siblings = siblings

/// A scoped `before` was refused because the dependency snapshot it would be checked against is not current for the
/// file: FileDependencies has not been given this parse with the latest parse of every earlier file. Checking again
/// with current dependencies, or every earlier file, is accepted.
type StaleDependenciesException(message: string) =
    inherit ArgumentException(message, "before")

/// A check was refused because the process's #line directives of the file are not its parse's: a newer parse of
/// another text of the file replaced them. The check is right once they are its parse's again.
type SupersededLineDirectivesException(message: string) =
    inherit InvalidOperationException(message)

/// What FileDependencies computed from one parse of every file of the project.
[<NoEquality; NoComparison>]
type internal DependencySnapshot =
    { Parses: FSharpParseFileResults[]
      Dependencies: int[][]
      /// The module-name dictionary each file is deduplicated against: every earlier file's entries, as checking the
      /// whole project gives them
      ModuleNamesBefore: ModuleNamesDict[]
      /// The signature files whose implementation file has the same qualified name, both deduplicated: checking the
      /// implementation file gives it that signature, so a setup can stand the signature in for it
      MatchedSignatures: HashSet<string> }

/// What the checks of a project share that does not reach its parses, so a lazily built result can hold it: the
/// compiler state, a lock per file, and the test counter.
[<Sealed>]
type internal ProjectChecks(state: CompilerState) =
    let fileLocks = System.Collections.Concurrent.ConcurrentDictionary<string, obj>(StringComparer.OrdinalIgnoreCase)
    let mutable checkResultsBuilt = 0

    let fileIndexes =
        let indexes = Dictionary<string, int>(StringComparer.OrdinalIgnoreCase)
        state.projectOptions.SourceFiles |> Array.iteri (fun idx fileName -> indexes[fileName] <- idx)
        indexes

    member _.State = state

    /// The project file's index, or -1.
    member _.IndexOf(fileName: string) =
        match fileIndexes.TryGetValue fileName with
        | true, idx -> idx
        | _ -> -1

    /// Whether `fileName` is a project file that comes before `other`.
    member _.IsBefore(fileName: string, other: string) =
        match fileIndexes.TryGetValue fileName, fileIndexes.TryGetValue other with
        | (true, a), (true, b) -> a < b
        | _ -> false

    /// Held from resetting a file's compiler-generated-name counters through the check that generates its names:
    /// the counters are the project's, by file, so two checks of one file must not interleave there. Checks of
    /// different files do not wait for each other.
    member _.FileLock(fileName: string) = fileLocks.GetOrAdd(fileName, fun _ -> obj ())

    member _.CheckResultsBuilt = Volatile.Read &checkResultsBuilt

    member _.CountCheckResultsBuilt() =
        Interlocked.Increment &checkResultsBuilt |> ignore

/// A project's options, references and initial checking state.
[<Sealed>]
type ProjectContext internal (state: CompilerState) =
    let parseLocks = System.Collections.Concurrent.ConcurrentDictionary<string, obj>(StringComparer.OrdinalIgnoreCase)
    // Exactly as ErrorsByFile matches a diagnostic's file against the project's files
    let sourceFiles = HashSet<string>(state.projectOptions.SourceFiles, StringComparer.Ordinal)

    let fileIndexes =
        let indexes = Dictionary<string, int>(StringComparer.OrdinalIgnoreCase)
        state.projectOptions.SourceFiles |> Array.iteri (fun idx fileName -> indexes[fileName] <- idx)
        indexes

    let latestParses = System.Collections.Concurrent.ConcurrentDictionary<string, FSharpParseFileResults>(StringComparer.OrdinalIgnoreCase)
    let mutable dependencies: DependencySnapshot option = None
    let checks = ProjectChecks state
    member internal _.State = state
    member internal _.Checks = checks

    /// For tests: how many times CheckFile's results on this context built a name-resolution sink and check results.
    member _.CheckResultsBuilt = checks.CheckResultsBuilt

    /// Held while a file is parsed and its #nowarn scopes, which the parse records in the project's options, are
    /// copied: parses of one file serialize, parses of different files do not.
    member internal _.ParseLock(fileName: string) = parseLocks.GetOrAdd(fileName, fun _ -> obj ())
    member internal _.IsSourceFile(fileName: string) = sourceFiles.Contains fileName

    member internal _.IndexOf(fileName: string) =
        match fileIndexes.TryGetValue fileName with
        | true, idx -> Some idx
        | _ -> None

    member internal _.SourceFiles = state.projectOptions.SourceFiles

    /// The latest parse Parse made of each file, set while the file's parse lock is held.
    member internal _.SetLatestParse(parse: FSharpParseFileResults) = latestParses[parse.FileName] <- parse

    member internal _.LatestParse(fileName: string) =
        match latestParses.TryGetValue fileName with
        | true, parse -> Some parse
        | _ -> None

    /// What the latest FileDependencies computed. A reference, so reads and writes are atomic.
    member internal _.Dependencies
        with get () = dependencies
        and set (snapshot: DependencySnapshot option) = dependencies <- snapshot

/// What a file adds to the state later files are checked in.
[<Sealed>]
type FileSignature
    internal
    (
        fileName: string,
        apply: TcState -> TcState,
        moduleNamesDict: ModuleNamesDict,
        definitions: Map<Stamp, DeclarationRef>,
        fingerprint: string,
        moduleType: ModuleOrNamespaceType,
        asImplementation: (TcState -> TcState) option
    ) =
    /// What the files after this one see of it, as the file-level SignatureFingerprint describes it: for an
    /// implementation file with a signature file, the signature file's. Unequal for anything not describable.
    member _.Fingerprint = fingerprint
    member internal _.FileName = fileName
    member internal _.Apply tcState = apply tcState
    /// The module-name dictionary DeduplicateParsedInputModuleName gave for this file: every earlier file's entries
    /// and its own. BeginFile merges these over the earlier files.
    member internal _.ModuleNamesDict = moduleNamesDict
    /// The declaration defining each entity and value later files see of this file, by stamp
    member internal _.Definitions = definitions
    /// The module type the file adds to the checker state, for tests
    member internal _.ModuleType = moduleType
    /// For a signature file: what graph-mode checking's ArtificialImplFile node does, adding the signature's contents
    /// to the environment implementation files are checked in. A file set up from a signature file without the
    /// implementation file behind it sees the signature there, as in graph mode.
    member internal _.AsImplementation = asImplementation

type internal CheckedDeclaration = ModuleOrNamespaceContents list * (unit -> unit) list * (AttributeTargets * Attrib) list

/// Keeps every diagnostic as reported, before the warning options and #nowarn scopes filter it, and passes it on.
/// The #nowarn scopes come from lexing the file: FinishFile filters what was kept again with those of the parse it
/// is given.
type internal RawDiagnostics(next: DiagnosticsLogger) =
    inherit DiagnosticsLogger("RawDiagnostics")
    let raw = ResizeArray<PhasedDiagnostic>()

    override _.DiagnosticSink diagnostic =
        raw.Add diagnostic
        next.DiagnosticSink diagnostic

    override _.ErrorCount = next.ErrorCount
    override _.CheckForRealErrorsIgnoringWarnings = next.CheckForRealErrorsIgnoringWarnings
    member _.Diagnostics = raw.ToArray()

/// A non-recursive nested module whose declarations are checked one at a time.
[<NoEquality; NoComparison>]
type internal ModuleFrame =
    { /// None when setting up the module failed, which skips its declarations
      Entity: ModuleOrNamespace option
      /// The module declaration's scope in its parent, and its range
      ScopeRange: range
      Range: range
      /// The environment, parent and type names the module's header was checked in
      OuterEnv: TcEnv
      OuterParent: ParentRef
      OuterTypeNames: Set<string>
      /// What the module's declarations checked so far left, latest first
      Checked: CheckedDeclaration list }

/// The environment a declaration is checked in.
[<Sealed>]
type DeclEnv
    internal (env: TcEnv, parent: ParentRef, typeNames: Set<string>, frames: ModuleFrame list, definitions: Map<Stamp, DeclarationRef>) =
    member internal _.Env = env
    member internal _.Parent = parent
    member internal _.TypeNames = typeNames
    /// The nested modules the environment is inside, innermost first
    member internal _.Frames = frames
    /// The declaration defining each entity and value of the project the environment holds, by stamp: those of
    /// earlier files, and of every declaration the environment was built from, including earlier versions of them
    member internal _.Definitions = definitions

/// Where a result goes when the file is built from the results.
[<NoEquality; NoComparison>]
type internal Nesting =
    /// A declaration, in as many nested modules
    | InModules of depth: int
    /// The header of a nested module that is in as many nested modules
    | ModuleHeader of depth: int * frame: ModuleFrame

    member x.Depth =
        match x with
        | InModules depth
        | ModuleHeader(depth, _) -> depth

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
        rawDiagnostics: PhasedDiagnostic[]
    ) =
    let sync = obj ()
    let mutable lastFinish: ResizeArray<unit -> unit> | null = null

    member internal _.Context = ctx
    /// The parse the file was set up from.
    member _.Parse = parse
    member internal _.File = file
    member internal _.ModuleNamesDict = moduleNamesDict
    member internal _.TcState = tcState
    member internal _.RootSigOpt = rootSigOpt
    member internal _.Scope = scope
    /// What the scope's accumulator held before the declarations: FinishFile merges their deltas onto it.
    member internal _.ScopeContents = scopeContents
    member internal _.Sink = sink
    member internal _.Leftovers = leftovers
    /// What setting up the file reported, before filtering: FinishFile filters it with its parse's #nowarn scopes
    member internal _.RawDiagnostics = rawDiagnostics
    /// Held while finishing the file.
    member internal _.Sync = sync

    /// Undoes what the latest finish changed in the declarations' typed trees, once.
    member internal _.UndoLastFinish() =
        lock sync (fun () ->
            match lastFinish with
            | null -> ()
            | log ->
                // Cleared only after every action ran: they restore saved values, so after an exception part-way the
                // next call can run them all again.
                MutationLog.Undo log
                lastFinish <- null)

    member internal _.SetLastFinish(log: ResizeArray<unit -> unit>) = lastFinish <- log

[<Sealed>]
type DeclarationResult
    internal
    (
        start: FileStart,
        declaration: ParsedDeclaration,
        fingerprint: string,
        diagnostics: FSharpDiagnostic[],
        rawDiagnostics: PhasedDiagnostic[],
        leavesFreeTypars: bool,
        dependsOnLater: bool,
        slotsAtCheck: IReadOnlyDictionary<Val, SlotSig list * bool>,
        envAfter: DeclEnv,
        envAtEnd: TcEnv,
        checkedDecl: CheckedDeclaration,
        delta: ModuleOrNamespaceType,
        deltaCombines: bool,
        sink: TcResultsSinkImpl,
        leftovers: TcFileState -> unit,
        nesting: Nesting,
        typedUses: DeclarationRef[],
        references: (DeclarationRef * string list * string)[]
    ) =
    let mutable finishTypedUses: DeclarationRef[] = [||]

    member _.Key = declaration.Key
    /// The fingerprint as the check left the declaration. Finishing the file can still change it, by defaults or by
    /// later declarations solving its inference variables, and only then: FileResult.Fingerprints has the final one,
    /// which differs from this one only when DependsOnLaterDeclarations.
    member _.Fingerprint = fingerprint
    /// Provisional: the declaration's diagnostics filtered with the project's live options when it was checked,
    /// whose #nowarn scopes are those of whichever version of the file was parsed last. FileResult.Diagnostics is
    /// authoritative: FinishFile filters what the check reported with the scopes of the parse it is given, and
    /// renders it after closing the inference scope, so its types show what defaults solved.
    member _.Diagnostics = diagnostics

    /// Whether the environment after the declaration holds inference variables nothing has solved yet
    /// (ComputeUngeneralizableTypars of it holds one that is not rigid), as `let r = ref []` leaves. A later declaration's check can
    /// solve them in place, and nothing undoes that, so the result depends on every later declaration of its file:
    /// see DependsOnLaterDeclarations.
    member _.LeavesFreeTypars = leavesFreeTypars

    /// Whether later checks change this result in place, so that (ruling R12) it depends on every later declaration
    /// of its file: when one changes, is added or is removed, discard this result and re-check the declaration from
    /// its environment before it, and everything after it. That is when it LeavesFreeTypars, or when what it publishes
    /// or an inline body of it holds an inference variable nothing has solved: a member's can be solved by a later use
    /// of the member, and one only in an inline body by the finish's defaults (this over-approximates that case: no
    /// later declaration reaches such a variable, but the finish changes the fingerprint). Checks also mark the values
    /// they use referenced, which the unused-value warning (FS1182) reads; FinishFile recomputes those marks from the
    /// current results (ruling R15), so they need no dependency.
    member _.DependsOnLaterDeclarations = dependsOnLater

    member _.EnvAfter = envAfter

    /// The declarations of the project this declaration depends on through types, which its names may not show:
    /// those defining every entity, value and trait solution in its checked contents, in the types of what it binds
    /// and in what its checker reported resolving (so a tree damaged by error recovery is still covered), and then,
    /// for each type of the project among them, the types it is made of (fields, union cases, base type, interfaces,
    /// abbreviation, type parameter constraints), transitively. Assemblies the project references are left out: they
    /// do not change within a session. Taken at the check, and again at the latest FinishFile given this result, which
    /// can solve more; this is the union of both.
    member _.TypedUses =
        match finishTypedUses with
        | [||] -> typedUses
        | atFinish -> Array.append typedUses atFinish |> Array.distinct |> Array.sort

    member internal _.SetFinishTypedUses(uses: DeclarationRef[]) = finishTypedUses <- uses
    /// The module values of the project the check marked referenced: the declaration defining each, the path of the
    /// module it is in, and its name
    member internal _.References = references
    member internal _.Start = start
    member internal _.Declaration = declaration
    member internal _.Ref = { File = start.Parse.FileName; Key = Some declaration.Key }
    /// What the check reported, before filtering
    member internal _.RawDiagnostics = rawDiagnostics
    /// The environment at the end of the enclosing scope if this is its last declaration.
    member internal _.EnvAtEnd = envAtEnd
    member internal _.Checked = checkedDecl
    /// What the declaration publishes into the module or namespace it is in; for a module header, the module without
    /// contents, which FinishFile does not merge (it finishes the module from its declarations).
    member internal _.Delta: ModuleOrNamespaceType = delta
    /// Whether the delta is combined into the file's contents, as a namespace fragment's is, rather than added.
    member internal _.DeltaCombines = deltaCombines
    member internal _.Sink = sink
    member internal _.Leftovers = leftovers
    member internal _.Nesting = nesting
    /// See DeclarationCheck.slotsAtCheck
    member internal _.SlotsAtCheck = slotsAtCheck

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
        checkResults: Lazy<FSharpCheckFileResults>,
        phaseTicks: IReadOnlyDictionary<string, int64>
    ) =
    member _.Diagnostics = diagnostics
    /// Each declaration's fingerprint after the file's inference scope is closed.
    member _.Fingerprints = fingerprints
    member _.Signature = signature
    /// CheckFile's are built on first read, by checking the file again with a sink in the setup it was checked in.
    /// That build raises InvalidOperationException, then and on every later read, when the file's line directives
    /// are no longer those of the parse it checked: a newer parse of another text of the file replaced them.
    member _.CheckResults = checkResults.Value
    /// Stopwatch ticks of each part of the finish, in source order: refilter, leftovers, assemble, replay, tail,
    /// typedUses, signature, render, fingerprints, sinks. CheckFile's: setup, tail (the check), definitions,
    /// fingerprint, render.
    member _.PhaseTicks = phaseTicks

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

    /// Loggers filtering by these options, whose #nowarn scopes may be a parse's copy.
    let newLoggersWith (diagnosticsOptions: FSharpDiagnosticOptions) =
        let capturing = CompilationDiagnosticLogger("TypeCheckFile", diagnosticsOptions)
        capturing, RawDiagnostics(GetDiagnosticsLoggerFilteringByScopedNowarn(diagnosticsOptions, capturing))

    let newLoggers (state: CompilerState) = newLoggersWith state.tcConfig.diagnosticsOptions

    let diagnosticsWith (state: CompilerState) (diagnosticsOptions: FSharpDiagnosticOptions) fileName (capturing: CompilationDiagnosticLogger) =
        DiagnosticHelpers.CreateDiagnostics(
            diagnosticsOptions,
            false,
            fileName,
            capturing.GetDiagnostics(),
            suggestNamesForErrors,
            state.tcConfig.flatErrors,
            None
        )

    let diagnosticsOf (state: CompilerState) fileName (capturing: CompilationDiagnosticLogger) =
        diagnosticsWith state state.tcConfig.diagnosticsOptions fileName capturing

    /// The diagnostics in the project's source files, as a full check's ErrorsByFile keeps them (ruling R18). Rendering
    /// keeps a diagnostic by the file of its range as reported, then applies #line directives to it: one in generated
    /// code mapped to its source, such as pars.fs to pars.fsy, would otherwise be reported in that other file.
    let projectDiagnostics (ctx: ProjectContext) (diagnostics: FSharpDiagnostic[]) =
        diagnostics |> Array.filter (fun diagnostic -> ctx.IsSourceFile diagnostic.FileName)

    /// Diagnostics as reported, filtered by these options (a parse's copy, with its #nowarn scopes), not yet
    /// rendered: their text shows the types as they are when diagnosticsWith renders them.
    let refiltered diagnosticsOptions (raw: PhasedDiagnostic[]) =
        let capturing, logger = newLoggersWith diagnosticsOptions

        for diagnostic in raw do
            logger.DiagnosticSink diagnostic

        capturing

    /// Each parse's copy of the project's diagnostic options, holding the #nowarn scopes that parse recorded.
    let warnOptions = ConditionalWeakTable<FSharpParseFileResults, FSharpDiagnosticOptions>()

    let warnOptionsOf (parse: FSharpParseFileResults) =
        match warnOptions.TryGetValue parse with
        | true, options -> options
        | _ -> invalidArg (nameof parse) "Only a parse made by DeclarationChecker.Parse can be checked: its #nowarn scopes are the ones it recorded."

    /// The fully qualified names of the entities a file declares where another file can declare the same name (ruling
    /// R19), and the namespaces it puts them in: its top-level modules, and the modules, types, exceptions and module
    /// abbreviations it declares directly in a namespace. Adding a file to the checker state combines these with every
    /// earlier file's (CombineCcuContentFragments), which reports two modules or types of one name (FS0037, FS0248,
    /// FS0249), and a module with a namespace's name (FS0247), whether or not either file uses the other. Types of
    /// one name and different arity can coexist; they share an entry here, which only adds edges.
    let declaredNames (input: ParsedInput) =
        let entities = ResizeArray<string>()
        let namespaces = ResizeArray<string>()
        let pathOf (ids: LongIdent) = ids |> List.map _.idText

        let addNamespaces (path: string list) =
            for n in 1 .. path.Length do
                namespaces.Add(String.concat "." (List.truncate n path))

        let add (path: string list) (name: string) = entities.Add(String.concat "." (path @ [ name ]))

        // A module may compile as XModule: next to a type X, or under [<CompilationRepresentation(ModuleSuffix)>]
        let addModule (path: string list) (name: string) =
            add path name
            add path (name + "Module")

        let addTop (path: string list) (isModule: bool) (inNamespace: string list -> unit) =
            if isModule then
                addNamespaces (List.truncate (max 0 (path.Length - 1)) path)
                entities.Add(String.concat "." path)
                entities.Add(String.concat "." path + "Module")
            else
                addNamespaces path
                inNamespace path

        let lastName (ids: LongIdent) =
            match List.tryLast ids with
            | Some id -> id.idText
            | None -> ""

        match input with
        | ParsedInput.ImplFile file ->
            for SynModuleOrNamespace(longId = ids; kind = kind; decls = decls) in file.Contents do
                addTop (pathOf ids) kind.IsModule (fun path ->
                    for decl in decls do
                        match decl with
                        | SynModuleDecl.NestedModule(moduleInfo = moduleInfo) -> addModule path (longIdentText moduleInfo.LongIdent)
                        | SynModuleDecl.Types(typeDefns, _) ->
                            for SynTypeDefn(typeInfo = typeInfo) as typeDefn in typeDefns do
                                if not (isAugmentation typeDefn) then
                                    add path (lastName typeInfo.LongIdent)
                        | SynModuleDecl.Exception(SynExceptionDefn(SynExceptionDefnRepr(caseName = SynUnionCase(ident = SynIdent(id, _))), _, _, _), _) ->
                            add path id.idText
                            add path (id.idText + "Exception")
                        | SynModuleDecl.ModuleAbbrev(ident = id) -> add path id.idText
                        | _ -> ())
        | ParsedInput.SigFile file ->
            for SynModuleOrNamespaceSig(longId = ids; kind = kind; decls = decls) in file.Contents do
                addTop (pathOf ids) kind.IsModule (fun path ->
                    for decl in decls do
                        match decl with
                        | SynModuleSigDecl.NestedModule(moduleInfo = moduleInfo) -> addModule path (longIdentText moduleInfo.LongIdent)
                        | SynModuleSigDecl.Types(typeDefns, _) ->
                            for SynTypeDefnSig(typeInfo = typeInfo; typeRepr = repr) in typeDefns do
                                match repr with
                                | SynTypeDefnSigRepr.ObjectModel(kind = SynTypeDefnKind.Augmentation _) -> ()
                                | _ -> add path (lastName typeInfo.LongIdent)
                        | SynModuleSigDecl.Exception(SynExceptionSig(exnRepr = SynExceptionDefnRepr(caseName = SynUnionCase(ident = SynIdent(id, _)))), _) ->
                            add path id.idText
                            add path (id.idText + "Exception")
                        | SynModuleSigDecl.ModuleAbbrev(ident = id) -> add path id.idText
                        | _ -> ())

        entities, namespaces

    /// Raises unless `before` is a sound setup for the file: earlier files of the project in file order, either every
    /// one of them, or at least those the latest FileDependencies found the file depends on. That list is used only
    /// while it is current: it was computed from this parse of the file, and from the latest parse of each earlier
    /// file, whose contents decide what the file depends on.
    ///
    /// For a setup from part of the earlier files, gives the module-name dictionary the file is deduplicated against,
    /// as checking every earlier file gives it: the files in `before` alone would miss the names of the others.
    let checkBefore (ctx: ProjectContext) (before: FileSignature list) (parse: FSharpParseFileResults) : (ModuleNamesDict * HashSet<string>) option =
        match ctx.IndexOf parse.FileName with
        | None -> None
        | Some idx ->
            let mutable last = -1

            for signature in before do
                match ctx.IndexOf signature.FileName with
                | Some position when position > last && position < idx -> last <- position
                | _ ->
                    raise (
                        ArgumentException(
                            $"The files before %s{parse.FileName} must be earlier files of the project, in file order: %s{signature.FileName} is not.",
                            nameof before
                        )
                    )

            if before.Length = idx then
                None
            else
                let isCurrent (snapshot: DependencySnapshot) =
                    snapshot.Parses.Length > idx
                    && obj.ReferenceEquals(snapshot.Parses[idx], parse)
                    && Seq.forall
                        (fun earlier ->
                            match ctx.LatestParse snapshot.Parses[earlier].FileName with
                            | Some latest -> obj.ReferenceEquals(latest, snapshot.Parses[earlier])
                            | None -> false)
                        (seq { 0 .. idx - 1 })

                match ctx.Dependencies with
                | Some snapshot when isCurrent snapshot ->
                    let present = HashSet<string>(before |> Seq.map _.FileName, StringComparer.OrdinalIgnoreCase)

                    match snapshot.Dependencies[idx] |> Array.tryFind (fun dep -> not (present.Contains snapshot.Parses[dep].FileName)) with
                    | Some missing ->
                        raise (
                            ArgumentException(
                                $"%s{parse.FileName} depends on %s{snapshot.Parses[missing].FileName}, which the files before it miss.",
                                nameof before
                            )
                        )
                    | None -> Some(snapshot.ModuleNamesBefore[idx], snapshot.MatchedSignatures)
                | _ ->
                    raise (
                        StaleDependenciesException
                            $"The files before %s{parse.FileName} are not every earlier file, and FileDependencies has not been given this parse with the latest parse of every earlier file, so its dependencies are unknown."
                    )

    /// The file-level fingerprint of what later files see of a file.
    let signatureFingerprint (mty: ModuleOrNamespaceType) (topAttrs: TopAttribs) =
        match SignatureFingerprint.compute mty topAttrs with
        | Some fingerprint -> fingerprint
        | None -> "?" + Guid.NewGuid().ToString("N")

    /// An implementation file's: its signature file's when it has one, as CheckSignatureFile gives it.
    let implFingerprint (rootSigOpt: ModuleOrNamespaceType option) (implFileSig: ModuleOrNamespaceType) (topAttrs: TopAttribs) =
        match rootSigOpt with
        | Some sigFileType -> signatureFingerprint sigFileType EmptyTopAttrs
        | None -> signatureFingerprint implFileSig topAttrs

    /// The checker state after `before`, for checking `fileName`. A signature file in `before` whose implementation
    /// file comes before `fileName` but is not in `before` is also added to the implementation environment, as graph
    /// mode's ArtificialImplFile node adds it, at the implementation file's place in file order. So a file depending
    /// on a signature file need not wait for the implementation file's check, and it still sees what a check of every
    /// earlier file would. Only for the pairs `matched` holds (FileDependencies keeps the implementation file on the
    /// lists of the others); a signature file whose implementation comes later is not added either: such a check
    /// would not see it.
    let stateBefore (checks: ProjectChecks) (before: FileSignature list) (matched: HashSet<string> option) (fileName: string) =
        let state = checks.State

        let present =
            HashSet<string>(before |> Seq.map (fun signature -> signature.FileName), StringComparer.OrdinalIgnoreCase)

        let implementationOf (signatureFile: string) = signatureFile.Substring(0, signatureFile.Length - 1)

        let artificial =
            [ for signature in before do
                  match signature.AsImplementation, matched with
                  | Some asImplementation, Some matched when
                      matched.Contains signature.FileName
                      && not (present.Contains(implementationOf signature.FileName))
                      && checks.IsBefore(implementationOf signature.FileName, fileName)
                      ->
                      yield checks.IndexOf(implementationOf signature.FileName), asImplementation
                  | _ -> () ]

        // In file order, each step where its file is: the environments layer what they hold in the order a check of
        // every earlier file adds it (AutoOpen modules and extension members shadow by it)
        let steps =
            [ for signature in before -> checks.IndexOf signature.FileName, signature.Apply ] @ artificial
            |> List.sortBy fst

        let tcState = (state.tcInitialState, steps) ||> List.fold (fun tcState (_, step) -> step tcState)

        let moduleNamesDict =
            (Map.empty, before)
            ||> List.fold (fun (acc: ModuleNamesDict) signature ->
                (acc, signature.ModuleNamesDict)
                ||> Map.fold (fun acc qualifiedName files ->
                    let known = acc |> Map.tryFind qualifiedName |> Option.defaultValue Map.empty
                    acc |> Map.add qualifiedName (Map.foldBack Map.add files known)))

        tcState, moduleNamesDict

    /// The checker state after `before` and the implementation file to check in it, as BeginFile and CheckFile set
    /// them up.
    let implFileState (checks: ProjectChecks) (before: FileSignature list) (scoped: (ModuleNamesDict * HashSet<string>) option) (parse: FSharpParseFileResults) =
        let tcState, chainModuleNames = stateBefore checks before (Option.map snd scoped) parse.FileName
        let moduleNamesDict = scoped |> Option.map fst |> Option.defaultValue chainModuleNames
        let input, moduleNamesDict = DeduplicateParsedInputModuleName moduleNamesDict parse.ParseTree

        match input with
        | ParsedInput.SigFile _ -> invalidArg (nameof parse) "Expected an implementation file."
        | ParsedInput.ImplFile file -> tcState, moduleNamesDict, input, file

    /// What CheckOneInput does before checking an implementation file, reporting to the ambient logger: the file's
    /// signature, if any.
    let enterImplFile (state: CompilerState) (tcState: TcState) (input: ParsedInput) (file: ParsedImplFileInput) =
        ResetGeneratedNames(input, state)
        let qualNameOfFile = file.QualifiedName

        if tcState.HasRootImpl qualNameOfFile then
            errorR (Error(FSComp.SR.buildImplementationAlreadyGiven (RichText.mkModule qualNameOfFile.Text), input.Range))

        tcState.TryFindRootSig qualNameOfFile

    let conditionalDefines (state: CompilerState) =
        if state.tcConfig.noConditionalErasure then
            None
        else
            Some state.tcConfig.conditionalDefines

    /// The #line directives the process holds for a file: those of its latest parse anywhere in the process. Checking
    /// reads them, and so do the results it builds.
    let currentLineDirectives (fileName: string) =
        LineDirectives.ofFile (FileIndex.fileIndexOfFile fileName)

    /// The #line directives of each parse, read right after it, under the file's parse lock.
    let lineDirectives = ConditionalWeakTable<FSharpParseFileResults, (int * (int * int)) list>()

    let lineDirectivesOf (parse: FSharpParseFileResults) =
        match lineDirectives.TryGetValue parse with
        | true, directives -> directives
        | _ -> invalidArg (nameof parse) "Only a parse made by DeclarationChecker.Parse can be checked."

    /// Raises SupersededLineDirectivesException unless the process's #line directives of the file are still the parse's. A
    /// check reads them, and rendering a diagnostic applies them: a newer parse of another text of the file replaces
    /// them, and that parse's are wrong for this one.
    let refuseUnlessCurrentDirectives (parse: FSharpParseFileResults) =
        if currentLineDirectives parse.FileName <> lineDirectivesOf parse then
            raise (
                SupersededLineDirectivesException
                    $"%s{parse.FileName} cannot be checked: a newer parse of the file replaced the line directives of the text that was parsed."
            )

    /// CheckOneImplFile on an implementation file set up by implFileState and enterImplFile, recovering from an error as
    /// CheckOneInput does, under the ambient logger.
    let checkImplFile (state: CompilerState) (tcState: TcState) rootSigOpt file (parse: FSharpParseFileResults) (logger: DiagnosticsLogger) sink =
        let checkForErrors () = parse.ParseHadErrors || logger.ErrorCount > 0

        try
            CheckOneImplFile(
                state.tcGlobals,
                state.tcImports.GetImportMap(),
                tcState.Ccu,
                tcState.ImplicitOpenDeclarations,
                checkForErrors,
                conditionalDefines state,
                sink,
                state.tcConfig.internalTestSpanStackReferring,
                tcState.TcEnvFromImpls,
                rootSigOpt,
                file,
                state.tcConfig.diagnosticsOptions
            )
            |> Cancellable.runWithoutCancellation
            |> Some
        with RecoverableException exn ->
            errorRecovery exn range0
            None

    /// The check results of a file CheckFile checked without a sink: it is checked again, with one, in the same
    /// setup. Like CheckFile, the build refuses (refuseUnlessCurrentDirectives) before and after the check. Its
    /// diagnostics are those of the first check, already rendered; this check's are dropped.
    let buildCheckResults (checks: ProjectChecks) before moduleNamesBefore (parse: FSharpParseFileResults) diagnostics =
        let state = checks.State
        refuseUnlessCurrentDirectives parse
        let tcState, _, input, file = implFileState checks before moduleNamesBefore parse
        let _, logger = newLoggersWith (warnOptionsOf parse)
        use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
        use _ = FSharp.Compiler.Cancellable.UsingToken CancellationToken.None
        let sink = TcResultsSinkImpl(state.tcGlobals)
        checks.CountCheckResultsBuilt()

        let rootSigOpt, checkedFile =
            lock (checks.FileLock parse.FileName) (fun () ->
                let rootSigOpt = enterImplFile state tcState input file
                rootSigOpt, checkImplFile state tcState rootSigOpt file parse logger (TcResultsSink.WithSink sink))

        refuseUnlessCurrentDirectives parse

        let ccuSigForFile, ownSigForFile, tcEnvAtEnd, implFileOpt =
            match checkedFile with
            | Some(_, implFile, tcEnvAtEnd, _, ownSigForFile) ->
                let ccuSigForFile, _ =
                    AddCheckResultsToTcState
                        (state.tcGlobals,
                         state.tcImports.GetImportMap(),
                         rootSigOpt.IsSome,
                         None,
                         TcResultsSink.NoSink,
                         tcState.TcEnvFromImpls,
                         file.QualifiedName,
                         implFile.Signature)
                        tcState

                ccuSigForFile, ownSigForFile, tcEnvAtEnd, Some implFile
            | None ->
                tcState.CcuSig,
                Construct.NewEmptyModuleOrNamespaceType(ModuleOrNamespaceKind.Namespace true),
                tcState.TcEnvFromSignatures,
                None

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
                sink.GetResolutions(),
                sink.GetSymbolUses(),
                tcEnvAtEnd.NameEnv,
                None,
                implFileOpt,
                sink.GetOpenDeclarations()
            )

        FSharpCheckFileResults(parse.FileName, diagnostics, Some scope, parse.DependencyFiles, None, true)

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

    /// Merges a declaration's delta onto what its module or namespace held before it, as publishing it did: a
    /// namespace fragment combines its namespaces with the file's, and anything else adds its values and entities.
    let mergeDelta (acc: ModuleOrNamespaceType) (delta: ModuleOrNamespaceType) combines =
        if combines then
            CombineCcuContentFragments [ acc; delta ]
        else
            let acc = (acc, delta.AllEntities) ||> Seq.fold (fun acc entity -> acc.AddEntity entity)
            (acc, delta.AllValsAndMembers) ||> Seq.fold (fun acc v -> acc.AddVal v)

    /// A module or namespace being built from results at finish.
    [<NoEquality; NoComparison>]
    type Level =
        { /// None for the file's scope
          Frame: ModuleFrame option
          mutable Contents: ModuleOrNamespaceType
          Checked: ResizeArray<CheckedDeclaration>
          mutable EnvAtEnd: TcEnv }

    /// Builds the scope's contents, checked declarations and environment at its end from the results in order,
    /// finishing each nested module after its declarations, as checking the file whole does.
    let assemble (cenv: TcFileState) (scopeContents: ModuleOrNamespaceType) (scopeEnv: TcEnv) (results: DeclarationResult[]) =
        let root =
            { Frame = None
              Contents = scopeContents
              Checked = ResizeArray()
              EnvAtEnd = scopeEnv }

        let levels = Stack<Level>()
        levels.Push root

        let close () =
            let level = levels.Pop()
            let parent = levels.Peek()

            match level.Frame with
            | Some({ Entity = Some entity } as frame) ->
                let outerEnv = { frame.OuterEnv with eModuleOrNamespaceTypeAccumulator = ref parent.Contents }

                let checkedDecl, _, envAtEnd =
                    ExitNestedModuleDeclarations cenv frame.ScopeRange outerEnv frame.Range entity level.Contents (List.ofSeq level.Checked) level.EnvAtEnd

                parent.Contents <- outerEnv.eModuleOrNamespaceTypeAccumulator.Value
                parent.Checked.Add checkedDecl
                parent.EnvAtEnd <- envAtEnd
            | Some frame ->
                parent.Checked.Add(([], [], []))
                parent.EnvAtEnd <- frame.OuterEnv
            | None -> ()

        for result in results do
            while levels.Count - 1 > result.Nesting.Depth do
                close ()

            match result.Nesting with
            | ModuleHeader(_, frame) ->
                let kind =
                    match frame.Entity with
                    | Some entity -> entity.ModuleOrNamespaceType.ModuleOrNamespaceKind
                    | None -> ModuleOrNamespaceKind.ModuleOrType

                levels.Push
                    { Frame = Some frame
                      Contents = Construct.NewEmptyModuleOrNamespaceType kind
                      Checked = ResizeArray()
                      EnvAtEnd = frame.OuterEnv }
            | InModules _ ->
                let level = levels.Peek()
                level.Contents <- mergeDelta level.Contents result.Delta result.DeltaCombines
                level.Checked.Add result.Checked
                level.EnvAtEnd <- result.EnvAtEnd

        while levels.Count > 1 do
            close ()

        root.Contents, List.ofSeq root.Checked, root.EnvAtEnd

    /// The names of the types among declarations, as TypeNamesInNonMutRecDecls collects them for module suffixes.
    /// It also counts types whose type parameters fail that function's early measure check, so it can only hold more.
    let typeNamesIn (decls: SynModuleDecl list) =
        set
            [ for decl in decls do
                  match decl with
                  | SynModuleDecl.Types(typeDefns, _) ->
                      for SynTypeDefn(typeInfo = typeInfo; typeRepr = repr) in typeDefns do
                          match repr, List.tryLast typeInfo.LongIdent with
                          | SynTypeDefnRepr.ObjectModel(kind = SynTypeDefnKind.Augmentation _), _ -> ()
                          | _, Some id -> yield id.idText
                          | _, None -> ()
                  | _ -> () ]

    let isTypeAbbreviation (SynTypeDefn(typeRepr = repr)) =
        match repr with
        | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.TypeAbbrev _, _) -> true
        | _ -> false

    /// Whether every later declaration depends on this one. For a module or fragment checked whole, that holds when
    /// anything in it would, except an open, whose scope ends with the module.
    let rec affectsAllLater (decl: SynModuleDecl) =
        let inner (decl: SynModuleDecl) =
            match decl with
            | SynModuleDecl.Open _ -> false
            | _ -> affectsAllLater decl

        match decl with
        | SynModuleDecl.Open _
        | SynModuleDecl.ModuleAbbrev _
        | SynModuleDecl.Attributes _
        | SynModuleDecl.Expr _
        | SynModuleDecl.HashDirective _ -> true
        | SynModuleDecl.Types(typeDefns, _) -> List.exists isTypeAbbreviation typeDefns
        | SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(attributes = attributes); decls = decls) ->
            findSynAttribute "AutoOpen" attributes || List.exists inner decls
        | SynModuleDecl.NamespaceFragment(SynModuleOrNamespace(attribs = attributes; decls = decls)) ->
            findSynAttribute "AutoOpen" attributes || List.exists inner decls
        | SynModuleDecl.Let _
        | SynModuleDecl.Exception _ -> false

    /// The uses in the entries of a declaration's syntax.
    let usesOf (entries: FileContentEntry list) =
        let uses = HashSet<string>()
        let members = HashSet<string>()
        let fields = HashSet<string>()
        let mutable unresolvable = false

        let rec visit (entry: FileContentEntry) =
            match entry with
            | FileContentEntry.Name name
            | FileContentEntry.ModuleName name -> uses.Add name |> ignore
            | FileContentEntry.OpenStatement path -> uses.UnionWith path
            | FileContentEntry.MemberName name -> members.Add name |> ignore
            | FileContentEntry.FieldOrCaseName name -> fields.Add name |> ignore
            | FileContentEntry.Unresolvable -> unresolvable <- true
            | FileContentEntry.TopLevelNamespace(content = content)
            | FileContentEntry.NestedModule(nestedContent = content) -> List.iter visit content
            // Its segments are names already, except after a dot on an expression, where they are members
            | FileContentEntry.PrefixedIdentifier _ -> ()

        List.iter visit entries
        uses, members, fields, unresolvable

    let sorted (names: seq<string>) =
        names |> Seq.distinct |> Seq.toArray |> Array.sortWith (fun a b -> String.CompareOrdinal(a, b))

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

    /// The environment after leaving nested modules until the environment is in only `depth` of them, as the first
    /// declaration after a module is checked in. FinishFile finishes the modules again and reports what that finds,
    /// so what this reports is dropped. It gives each module its contents so far as its type, as FinishFile does.
    let exitModules (state: CompilerState) (start: FileStart) (envBefore: DeclEnv) depth =
        if envBefore.Frames.Length <= depth then
            envBefore
        else
            use _ = new CompilationGlobalsScope(DiscardErrorsLogger, BuildPhase.TypeCheck)
            let cenv, _, _ = newCheckerState state start.TcState start.RootSigOpt start.File (TcResultsSinkImpl state.tcGlobals)

            let rec exit (env: DeclEnv) =
                match env.Frames with
                | frame :: outer when env.Frames.Length > depth ->
                    let outerEnv =
                        { frame.OuterEnv with
                            eModuleOrNamespaceTypeAccumulator = ref frame.OuterEnv.eModuleOrNamespaceTypeAccumulator.Value }

                    let envAfter =
                        match frame.Entity with
                        | Some entity ->
                            let moduleContents = env.Env.eModuleOrNamespaceTypeAccumulator.Value
                            let _, envAfter, _ =
                                ExitNestedModuleDeclarations cenv frame.ScopeRange outerEnv frame.Range entity moduleContents (List.rev frame.Checked) env.Env

                            envAfter
                        | None -> outerEnv

                    exit (DeclEnv(envAfter, frame.OuterParent, frame.OuterTypeNames, outer, env.Definitions))
                | _ -> env

            exit envBefore

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

    /// The slots each member of a contribution implements, and whether it is implemented, as its check left them.
    ///
    /// Closing the inference scope completes them (FinalTypeDefinitionChecksAtEndOfInferenceScope): a slot the check
    /// recorded by name and declaring type only gets its parameters and return type, and those of a generated
    /// comparison member are taken from the interface's own metadata; a slot no member was matched to at the check is
    /// recorded; an abstract member with a default is marked implemented. The declarations after this one are checked
    /// before that, so they see these. A fingerprint taken at the finish describes these too: the finish computes the
    /// completed slots from the member (its name, type, flags, which the fingerprint describes), the interfaces and base
    /// type of its type (described with it) and the slots those declare, which come from referenced assemblies, earlier
    /// files (whose signatures are compared whole) or declarations whose own fingerprints describe them. An augmentation
    /// of the type later in the file can add members and interfaces, and it leads a segment with the type.
    let slotsAtCheck (contribution: ModuleOrNamespaceType) : IReadOnlyDictionary<Val, SlotSig list * bool> =
        let slots = Dictionary<Val, SlotSig list * bool>(HashIdentity.Reference)

        let rec visit (mty: ModuleOrNamespaceType) =
            for v in mty.AllValsAndMembers do
                match v.MemberInfo with
                | Some memberInfo -> slots[v] <- (memberInfo.ImplementedSlotSigs, memberInfo.IsImplemented)
                | None -> ()

            for entity in mty.AllEntities do
                if entity.IsModuleOrNamespace then
                    visit entity.ModuleOrNamespaceType

        visit contribution
        slots :> IReadOnlyDictionary<_, _>

    let fingerprintOf (contribution: ModuleOrNamespaceType) ((contents, _, _): CheckedDeclaration) (slots: IReadOnlyDictionary<Val, SlotSig list * bool>) =
        // Every member the fingerprint describes was captured; reading one that was not would describe the finish's slots
        let slotsOf (v: Val) (_: ValMemberInfo) =
            match slots.TryGetValue v with
            | true, atCheck -> Some atCheck
            | _ -> None

        match SignatureFingerprint.computeDeclaration contribution (List.collect inlineBodies contents) slotsOf with
        | Some fingerprint -> fingerprint
        // Not describable: never equal to another fingerprint, so it always counts as changed.
        | None -> "?" + Guid.NewGuid().ToString("N")

    /// Whether any of the type parameters can still be solved. A rigid one, such as the declared 'T of
    /// `type Box<'T>(v: 'T)` that the environment after the type keeps, cannot: unifying it with another type, or
    /// constraining it further, is an error, not a solution.
    let anySolvable (typars: Zset<Typar>) =
        typars |> Zset.exists (fun tp -> tp.Rigidity <> TyparRigidity.Rigid)

    /// Whether what a declaration publishes, or the body of one of its inline values, holds an inference variable
    /// nothing has solved. Such a variable is not always in the environment after it, as a value's is: a member's
    /// (`member _.M() = 1L + 1`) is solved in place by a later `let t: int64 = T().M()`, and one only in an inline body
    /// is solved by the finish's defaults, which the fingerprint describes.
    let leavesOpenTypes (contribution: ModuleOrNamespaceType) ((contents, _, _): CheckedDeclaration) =
        anySolvable (freeInModuleTy contribution).FreeTypars
        || contents
           |> List.collect inlineBodies
           |> List.exists (fun (_, body) -> anySolvable (freeInExpr CollectTyparsNoCaching body).FreeTyvars.FreeTypars)

    /// The stamps of every entity and value in a module type, including those inside its modules.
    let rec stampsOf (mty: ModuleOrNamespaceType) =
        seq {
            for entity in mty.AllEntities do
                yield entity.Stamp

                if entity.IsModuleOrNamespace then
                    yield! stampsOf entity.ModuleOrNamespaceType

            for v in mty.AllValsAndMembers do
                yield v.Stamp
        }

    /// The module values in a module type, including those inside its modules.
    let rec moduleValuesOf (mty: ModuleOrNamespaceType) =
        seq {
            for v in mty.AllValsAndMembers do
                if v.IsModuleBinding then
                    yield v

            for entity in mty.AllEntities do
                if entity.IsModuleOrNamespace then
                    yield! moduleValuesOf entity.ModuleOrNamespaceType
        }

    /// The compilation path and name of the module a module value is in: a declaration holding modules whole can hold
    /// values of the same name in several of them. The names are the same in every check of the declaration.
    let modulePathOf (v: Val) =
        match v.TryDeclaringEntity with
        | Parent entity ->
            let outer =
                match entity.CompilationPathOpt with
                | Some cpath -> cpath.MangledPath
                | None -> []

            outer @ [ entity.LogicalName ]
        | ParentNone -> []

    /// Marks referenced exactly the module values of the results that the results' checks referenced (ruling R15).
    /// A check marks the values it uses, and a later check can mark an earlier result's value, or a value of an earlier
    /// version of a declaration that the current result no longer holds: so every flag is cleared, then each recorded
    /// reference is found by its declaration's key, its module's path and its name in the current results. Both are
    /// recorded in the active mutation log, which the next finish or check undoes.
    ///
    /// The flag only means something for a module value a signature hides, which the unused-value warning (FS1182)
    /// reads: references from later files are not replayed, so after a finish a public value used only by later files
    /// reads as unreferenced, as FSharpMemberOrFunctionOrValue shows it. No diagnostic depends on that.
    let replayReferences (fileName: string) (results: DeclarationResult[]) =
        let byKey = Dictionary<DeclarationKey, DeclarationResult>(HashIdentity.Structural)

        for result in results do
            byKey[result.Key] <- result

        for result in results do
            for v in moduleValuesOf result.Delta do
                v.SetHasBeenReferencedTo false

        for result in results do
            for declaration, path, name in result.References do
                match declaration.Key with
                | Some key when String.Equals(declaration.File, fileName, StringComparison.OrdinalIgnoreCase) ->
                    match byKey.TryGetValue key with
                    | true, target ->
                        for v in moduleValuesOf target.Delta do
                            if v.LogicalName = name && modulePathOf v = path then
                                v.SetHasBeenReferencedTo true
                    | _ -> ()
                | _ -> ()

    /// Records the declaration as the definition of what its delta publishes.
    let addDefinitions (definitions: Map<Stamp, DeclarationRef>) (declaration: DeclarationRef) (delta: ModuleOrNamespaceType) =
        (definitions, stampsOf delta) ||> Seq.fold (fun acc stamp -> Map.add stamp declaration acc)

    let definitionsBefore (before: FileSignature list) =
        (Map.empty, before) ||> List.fold (fun acc signature -> Map.foldBack Map.add signature.Definitions acc)

    /// What a signature file declares: its declarations are not checked one at a time, so the file stands for them.
    let signatureDefinitions fileName (sigType: ModuleOrNamespaceType) =
        addDefinitions Map.empty { File = fileName; Key = None } sigType

    /// The definitions of a file's inferred signature, a copy of the file's contents with new stamps
    /// (copyModuleOrNamespaceType keeps every entity and value, in order): each copied entity and value is matched to
    /// the original at the same position. A copy of another shape would lose definitions, so it raises.
    let rec copiedDefinitions (own: Map<Stamp, DeclarationRef>) (contents: ModuleOrNamespaceType) (copy: ModuleOrNamespaceType) acc =
        let pairs (originals: seq<'T>) (copies: seq<'T>) (name: 'T -> string) =
            let originals, copies = Array.ofSeq originals, Array.ofSeq copies
            let names (items: 'T[]) = items |> Array.map name |> String.concat ", "

            if originals.Length <> copies.Length || Array.exists2 (fun o c -> name o <> name c) originals copies then
                invalidOp $"The inferred signature is not a copy of the file's contents: [%s{names originals}] against [%s{names copies}]."

            Array.zip originals copies

        let add acc (original: Stamp) (copied: Stamp) =
            match own.TryFind original with
            | Some declaration -> Map.add copied declaration acc
            | None -> acc

        let acc =
            (acc, pairs contents.AllEntities copy.AllEntities _.LogicalName)
            ||> Array.fold (fun acc (o, c) -> copiedDefinitions own o.ModuleOrNamespaceType c.ModuleOrNamespaceType (add acc o.Stamp c.Stamp))

        (acc, pairs contents.AllValsAndMembers copy.AllValsAndMembers _.LogicalName)
        ||> Array.fold (fun acc (o, c) -> add acc o.Stamp c.Stamp)

    /// The types a type is made of, which its equality, comparison and other inferred properties come from.
    let structureOf (tycon: Tycon) =
        [ for field in tycon.AllFieldsArray -> field.FormalType
          if tycon.IsUnionTycon then
              for case in tycon.UnionCasesArray do
                  for field in case.RecdFieldsArray -> field.FormalType
          yield! Option.toList tycon.TypeContents.tcaug_super
          yield! tycon.ImmediateInterfaceTypesOfFSharpTycon
          yield! Option.toList tycon.TypeAbbrev ]

    /// The declarations other than `self` that define what the declaration's checked contents, the types of what it
    /// publishes and what its sink resolved refer to, closed over the types each type of the project is made of.
    let typedUsesOf
        (definitions: Map<Stamp, DeclarationRef>)
        (self: DeclarationRef)
        (delta: ModuleOrNamespaceType)
        (contents: ModuleOrNamespaceContents list)
        (sink: TcResultsSinkImpl option)
        =
        let refs = HashSet<DeclarationRef>(HashIdentity.Structural)
        let seenTycons = HashSet<Stamp>()
        let madeOf = Stack<Tycon>()

        let addStamp stamp =
            match definitions.TryFind stamp with
            | Some declaration -> refs.Add declaration |> ignore; true
            | None -> false

        let addVal (v: Val) = addStamp v.Stamp |> ignore

        // Only a type of the project can change, so only those are opened up
        let addTycon (tycon: Tycon) =
            if seenTycons.Add tycon.Stamp && addStamp tycon.Stamp then
                madeOf.Push tycon

        let addTyvars (ftyvs: FreeTyvars) =
            Zset.iter addTycon ftyvs.FreeTycons
            Zset.iter addVal ftyvs.FreeTraitSolutions

        let addType ty = addTyvars (freeInType CollectAll ty)
        let addTcref (tcref: TyconRef) = if tcref.IsLocalRef then addTycon tcref.Deref
        let addVref (vref: ValRef) = if vref.IsLocalRef then addVal vref.Deref

        let addFreeVars (fvs: FreeVars) =
            Zset.iter addVal fvs.FreeLocals
            Zset.iter (fun (rfref: RecdFieldRef) -> addTcref rfref.TyconRef) fvs.FreeRecdFields
            Zset.iter (fun (ucref: UnionCaseRef) -> addTcref ucref.TyconRef) fvs.FreeUnionCases
            Zset.iter addTycon fvs.FreeLocalTyconReprs
            addTyvars fvs.FreeTyvars

        let addItem (item: Item) =
            match item with
            | Item.Value vref
            | Item.CustomBuilder(_, vref) ->
                addVref vref
                addType vref.Type
            | Item.UnionCase(info, _)
            | Item.UnionCaseField(info, _) -> addTcref info.TyconRef
            | Item.ActivePatternResult(apOverallTy = ty)
            | Item.DelegateCtor ty -> addType ty
            | Item.ActivePatternCase apref -> addVref apref.ActivePatternVal
            | Item.ExnCase tcref -> addTcref tcref
            | Item.RecdField info -> addTcref info.TyconRef
            | Item.Trait info -> addTyvars (accFreeInTrait CollectAll info emptyFreeTyvars)
            | Item.Types(_, tys) -> List.iter addType tys
            | Item.ModuleOrNamespaces modrefs -> List.iter addTcref modrefs
            | Item.Property(info = pinfos) ->
                for pinfo in pinfos do
                    addType pinfo.ApparentEnclosingType
                    Option.iter addVref pinfo.ArbitraryValRef
            | Item.MethodGroup(methods = minfos)
            | Item.CtorGroup(_, minfos) ->
                for minfo in minfos do
                    addType minfo.ApparentEnclosingType
                    Option.iter addVref minfo.ArbitraryValRef
            | Item.CustomOperation(_, _, Some minfo) ->
                addType minfo.ApparentEnclosingType
                Option.iter addVref minfo.ArbitraryValRef
            | Item.Event einfo ->
                addType einfo.ApparentEnclosingType
                Option.iter addVref einfo.ArbitraryValRef
            | Item.ILField finfo -> addType finfo.ApparentEnclosingType
            | Item.ImplicitOp(_, sln) -> sln.Value |> Option.iter (fun sln -> addTyvars (accFreeInTraitSln CollectAll sln emptyFreeTyvars))
            | _ -> ()

        for c in contents do
            addFreeVars (freeInModuleOrNamespace CollectAll c)

        // The types of what it publishes, and what its own types are made of
        let rec published (mty: ModuleOrNamespaceType) =
            for v in mty.AllValsAndMembers do
                addTyvars (freeInVal CollectAll v)

            for entity in mty.AllEntities do
                if entity.IsModuleOrNamespace then
                    published entity.ModuleOrNamespaceType
                elif seenTycons.Add entity.Stamp then
                    madeOf.Push entity

        published delta

        match sink with
        | Some sink ->
            let resolutions = sink.GetResolutions()

            for resolution in resolutions.CapturedNameResolutions do
                addItem resolution.Item

            for resolution in resolutions.CapturedMethodGroupResolutions do
                addItem resolution.Item

            for ty, _, _, _ in resolutions.CapturedExpressionTypings do
                addType ty
        | None -> ()

        while madeOf.Count > 0 do
            let tycon = madeOf.Pop()

            for ty in structureOf tycon do
                addType ty

            addTyvars (accFreeInTypars CollectAll tycon.Typars emptyFreeTyvars)

        refs.Remove self |> ignore
        refs |> Array.ofSeq |> Array.sort

    let implFileSignature
        (state: CompilerState)
        fileName
        qualNameOfFile
        (implFileSig: ModuleOrNamespaceType)
        createsGeneratedProvidedTypes
        moduleNamesDict
        definitions
        fingerprint
        =
        let amap = state.tcImports.GetImportMap()

        let apply (tcState: TcState) =
            let hadSig = (tcState.TryFindRootSig qualNameOfFile).IsSome

            let _, tcState =
                AddCheckResultsToTcState
                    (state.tcGlobals, amap, hadSig, None, TcResultsSink.NoSink, tcState.TcEnvFromImpls, qualNameOfFile, implFileSig)
                    tcState

            AddCreatesGeneratedProvidedTypes createsGeneratedProvidedTypes tcState

        FileSignature(fileName, apply, moduleNamesDict, definitions, fingerprint, implFileSig, None)

    /// What CheckOneInput's PartialResultOnError gives later files: the checker state as it was before the file.
    let failedFileSignature fileName moduleNamesDict =
        FileSignature(
            fileName,
            id,
            moduleNamesDict,
            Map.empty,
            "?" + Guid.NewGuid().ToString("N"),
            Construct.NewEmptyModuleOrNamespaceType(ModuleOrNamespaceKind.Namespace true),
            None
        )

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

        // Lexing records the file's #nowarn scopes in the project's diagnostic options, replacing the last parse's:
        // copy them while no other parse of this file can replace them. The latest parse of the file is recorded under
        // the same lock, so it is the one whose scopes were copied last. Its #line directives are read the same way: a
        // parse of the file on another context can still replace them in between.
        lock (ctx.ParseLock fileName) (fun () ->
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

            let options = parsingOptions.DiagnosticOptions
            let warnOptions = lock options (fun () -> { options with WarnScopeData = options.WarnScopeData })
            let parse = FSharpParseFileResults(parseErrors, parseTree, anyErrors, [||])
            DeclarationCheck.sources.AddOrUpdate(parse, sourceText)
            DeclarationCheck.warnOptions.AddOrUpdate(parse, warnOptions)
            DeclarationCheck.lineDirectives.AddOrUpdate(parse, DeclarationCheck.currentLineDirectives fileName)
            ctx.SetLatestParse parse
            parse)

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

            let declaration modulePath within siblings depth (decl: SynModuleDecl) (range: range) scopem headerInputs isModuleHeader =
                let name, kind = DeclarationCheck.nameAndKind decl
                let ordinal = match seen.TryGetValue((modulePath, name, kind)) with | true, n -> n | _ -> 0
                seen[(modulePath, name, kind)] <- ordinal + 1
                let text = DeclarationCheck.textOfRange source range
                let key = { ModulePath = modulePath; Name = name; Kind = kind; Ordinal = ordinal }
                ParsedDeclaration(key, decl, range, scopem, text, headerInputs, within, siblings, depth, isModuleHeader)

            let rec split modulePath within depth (endm: range) (decls: SynModuleDecl list) =
                let typeNames = DeclarationCheck.typeNamesIn decls

                // Whether the module gets the Module suffix for a type of its name among the declarations around it
                let suffixInput (moduleInfo: SynComponentInfo) =
                    let ownName = moduleInfo.LongIdent |> List.tryLast |> Option.map _.idText |> Option.defaultValue ""
                    $"suffix=%b{typeNames.Contains ownName}"

                let declaration modulePath within depth decl range scopem headerInputs isModuleHeader =
                    declaration modulePath within decls depth decl range scopem headerInputs isModuleHeader

                decls
                |> List.mapi (fun i decl ->
                    // As TcModuleOrNamespaceElementsNonMutRec: a declaration's scope runs from the next one to the end
                    // of the enclosing module, namespace or file. This is the only place the end is computed.
                    let scopem =
                        match List.tryItem (i + 1) decls with
                        | Some next -> unionRanges next.Range endm
                        | None -> unionRanges decl.Range endm

                    match decl with
                    // A module with a name, and not recursive: its header, then its declarations, as checking the
                    // module checks them, with its end as theirs
                    | SynModuleDecl.NestedModule(
                        moduleInfo = SynComponentInfo(synType = Some _) as moduleInfo
                        isRecursive = false
                        decls = moduleDecls
                        range = m
                        trivia = trivia) ->
                        let headerEnd =
                            match trivia.EqualsRange with
                            | Some equals -> equals.End
                            | None -> moduleInfo.Range.End

                        // What TcNestedModuleHeader and EnterNestedModuleDeclarations read besides the header's text
                        let headerInputs =
                            let bodyTypes =
                                DeclarationCheck.typeNamesIn moduleDecls |> Seq.sortWith (fun a b -> String.CompareOrdinal(a, b))

                            $"%s{suffixInput moduleInfo};types=%s{String.Join(',', bodyTypes)}"

                        let range = mkRange m.FileName m.Start headerEnd
                        let header = declaration modulePath within depth decl range scopem headerInputs true
                        let path = modulePath @ [ DeclarationCheck.longIdentText moduleInfo.LongIdent ]
                        header :: split path (Some header.Key) (depth + 1) m.EndRange moduleDecls
                    // A module checked whole (module rec, or without a name) reads its suffix the same way
                    | SynModuleDecl.NestedModule(moduleInfo = moduleInfo) ->
                        [ declaration modulePath within depth decl decl.Range scopem (suffixInput moduleInfo) false ]
                    | _ -> [ declaration modulePath within depth decl decl.Range scopem "" false ])
                |> List.concat

            split modulePath None 0 endm decls |> Array.ofList

    /// The names the declaration defines and uses. A module header has only its name and its attributes' uses.
    static member Content(decl: ParsedDeclaration) : DeclarationContent =
        let entries, (defines, unreadableName) =
            match decl.Syntax with
            | SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(attributes = attributes) as moduleInfo) when decl.IsModuleHeader ->
                FileContentMapping.visitSynAttributes attributes, ([ for id in moduleInfo.LongIdent -> id.idText ], false)
            | SynModuleDecl.NamespaceFragment(SynModuleOrNamespace(attribs = attributes; decls = decls)) ->
                FileContentMapping.visitSynAttributes attributes @ List.collect FileContentMapping.visitSynModuleDecl decls,
                TrieMapping.declarationNames decl.Syntax
            | syntax -> FileContentMapping.visitSynModuleDecl syntax, TrieMapping.declarationNames syntax

        let uses, members, fields, unresolvable = DeclarationCheck.usesOf entries

        let affectsAllLater =
            match decl.Syntax with
            | SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(attributes = attributes)) when decl.IsModuleHeader ->
                findSynAttribute "AutoOpen" attributes
            | syntax -> DeclarationCheck.affectsAllLater syntax

        let augments =
            match decl.Syntax with
            | SynModuleDecl.Types(typeDefns, _) ->
                typeDefns
                |> List.filter DeclarationCheck.isAugmentation
                |> List.map DeclarationCheck.typeDefnName
                |> DeclarationCheck.sorted
            | _ -> [||]

        { Defines = DeclarationCheck.sorted defines
          Uses = DeclarationCheck.sorted uses
          MemberUses = DeclarationCheck.sorted members
          FieldOrCaseUses = DeclarationCheck.sorted fields
          HasUnresolvable = unresolvable
          AffectsAllLater = affectsAllLater || unreadableName
          Augments = augments }

    static member CheckSignatureFile(ctx: ProjectContext, before: FileSignature list, parse: FSharpParseFileResults) : FileSignature =
        let state = ctx.State

        match parse.ParseTree with
        | ParsedInput.ImplFile _ -> invalidArg (nameof parse) "Expected a signature file."
        | ParsedInput.SigFile _ ->
            let moduleNamesBefore = DeclarationCheck.checkBefore ctx before parse
            let tcState, chainModuleNames = DeclarationCheck.stateBefore ctx.Checks before (Option.map snd moduleNamesBefore) parse.FileName
            let moduleNamesDict = moduleNamesBefore |> Option.map fst |> Option.defaultValue chainModuleNames
            let input, moduleNamesDict = DeduplicateParsedInputModuleName moduleNamesDict parse.ParseTree

            match input with
            | ParsedInput.ImplFile _ -> invalidOp "unreachable"
            | ParsedInput.SigFile file ->
                let _, logger = DeclarationCheck.newLoggers state
                use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
                let checkForErrors () = parse.ParseHadErrors || logger.ErrorCount > 0
                let amap = state.tcImports.GetImportMap()

                // The fingerprint reads the compiled names of the file's values, which are given on first read
                let sigFileType, createsGeneratedProvidedTypes, fingerprint =
                    lock (ctx.Checks.FileLock parse.FileName) (fun () ->
                        ResetGeneratedNames(input, state)

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

                        sigFileType, createsGeneratedProvidedTypes, DeclarationCheck.signatureFingerprint sigFileType EmptyTopAttrs)

                let qualNameOfFile = file.QualifiedName
                let m = input.Range

                let apply =
                    AddSignatureFileToTcState (state.tcGlobals, amap, m, qualNameOfFile, sigFileType, createsGeneratedProvidedTypes)

                // As AddSignatureResultToTcImplEnv, which graph mode runs for an ArtificialImplFile node
                let asImplementation (tcState: TcState) =
                    match tcState.TryFindRootSig qualNameOfFile with
                    | Some rootSig ->
                        AddCheckResultsToTcState
                            (state.tcGlobals, amap, true, None, TcResultsSink.NoSink, tcState.TcEnvFromImpls, qualNameOfFile, rootSig)
                            tcState
                        |> snd
                    | None -> tcState

                FileSignature(
                    parse.FileName,
                    apply,
                    moduleNamesDict,
                    DeclarationCheck.signatureDefinitions parse.FileName sigFileType,
                    fingerprint,
                    sigFileType,
                    Some asImplementation
                )

    /// For tests: each access path of the entities, values, fields and union cases in the signature's module type, as
    /// the fingerprint writes it and as sprintf "%A" gives it.
    static member AccessPathTexts(signature: FileSignature) : (string * string)[] =
        let paths = ResizeArray<CompilationPath>()

        let addAccess (TAccess compPaths) =
            for compPath in compPaths do
                paths.Add compPath

        let rec walk (mty: ModuleOrNamespaceType) =
            for v in mty.AllValsAndMembers do
                addAccess v.Accessibility

            for e in mty.AllEntities do
                addAccess e.Accessibility
                addAccess e.TypeReprAccessibility

                for f in e.AllFieldsArray do
                    addAccess f.Accessibility

                for uc in e.UnionCasesArray do
                    addAccess uc.Accessibility

                if e.IsModuleOrNamespace then
                    walk e.ModuleOrNamespaceType

        walk signature.ModuleType
        [| for path in paths -> SignatureFingerprint.accessPathText path, sprintf "%A" path.AccessPath |]

    static member BeginFile(ctx: ProjectContext, before: FileSignature list, parse: FSharpParseFileResults) : FileStart * DeclEnv =
        let state = ctx.State

        match parse.ParseTree with
        | ParsedInput.SigFile _ -> invalidArg (nameof parse) "Only implementation files are checked one declaration at a time."
        | ParsedInput.ImplFile _ ->
            let moduleNamesBefore = DeclarationCheck.checkBefore ctx before parse
            let tcState, moduleNamesDict, input, file = DeclarationCheck.implFileState ctx.Checks before moduleNamesBefore parse
            let _, logger = DeclarationCheck.newLoggers state
            use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
            use _ = FSharp.Compiler.Cancellable.UsingToken CancellationToken.None
            let sink = TcResultsSinkImpl(state.tcGlobals)

            let rootSigOpt, cenv, scope =
                lock (ctx.Checks.FileLock parse.FileName) (fun () ->
                    let rootSigOpt = DeclarationCheck.enterImplFile state tcState input file
                    let cenv, envFile, _ = DeclarationCheck.newCheckerState state tcState rootSigOpt file sink
                    rootSigOpt, cenv, EnterImplFileDeclarations cenv envFile file (DeclarationCheck.splitsFragment file))

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
                    logger.Diagnostics
                )

            start, DeclEnv(scope.Env, scope.Parent, scope.TypeNames, [], DeclarationCheck.definitionsBefore before)

    /// For each of the project's files, given in file order, the ascending indices of the earlier files checking it
    /// reads: the file dependency graph graph-mode checking builds, transitively closed. A file that depends on a
    /// signature file does not depend on its implementation file when their qualified names match: the setup adds the
    /// signature's contents to the implementation environment instead, as graph mode's ArtificialImplFile node does
    /// (see stateBefore). When they differ, it depends on the implementation file, as a check of every earlier file
    /// reads it.
    ///
    /// A file also depends on every earlier file that declares an entity of the same fully qualified name, or a
    /// namespace of a module's name (ruling R19, see DeclarationCheck.declaredNames): adding it to the checker state
    /// reports the clash, whether or not either file uses the other.
    ///
    /// `parses` must be one parse of each of the project's source files, in file order. BeginFile, CheckFile and
    /// CheckSignatureFile accept the signatures of these files as `before`, in place of every earlier file, for these
    /// parses, while each earlier one is still the latest parse of its file.
    static member FileDependencies(ctx: ProjectContext, parses: FSharpParseFileResults[]) : int[][] =
        let sourceFiles = ctx.SourceFiles

        if
            parses.Length <> sourceFiles.Length
            || Array.exists2 (fun (parse: FSharpParseFileResults) file -> not (String.Equals(parse.FileName, file, StringComparison.OrdinalIgnoreCase))) parses sourceFiles
        then
            raise (ArgumentException("Expected one parse of each of the project's source files, in file order.", nameof parses))

        let inputsAndModuleNames, _ =
            (Map.empty, parses)
            ||> Array.mapFold (fun moduleNamesDict parse ->
                let input, after = DeduplicateParsedInputModuleName moduleNamesDict parse.ParseTree
                (input, moduleNamesDict), after)

        let inputs, moduleNamesBefore = Array.unzip inputsAndModuleNames

        let files =
            inputs
            |> Array.mapi (fun idx input -> { Idx = idx; FileName = input.FileName; ParsedInput = input })

        let filePairs = FilePairMap files
        let graph, _ = DependencyResolution.mkGraph filePairs files

        // The checker gives an implementation file its signature by qualified name, FilePairMap pairs them by file name
        let matched = HashSet<string>(StringComparer.OrdinalIgnoreCase)

        for idx in 0 .. files.Length - 1 do
            if filePairs.IsSignature idx then
                let impl = filePairs.GetImplementationIndex idx

                if inputs[idx].QualifiedName.Text = inputs[impl].QualifiedName.Text then
                    matched.Add parses[idx].FileName |> ignore

        // By name, the files declaring an entity of that name, and those with a namespace of that name
        let entityFiles = Dictionary<string, ResizeArray<int>>(StringComparer.OrdinalIgnoreCase)
        let namespaceFiles = Dictionary<string, ResizeArray<int>>(StringComparer.OrdinalIgnoreCase)

        let filesOf (table: Dictionary<string, ResizeArray<int>>) name =
            match table.TryGetValue name with
            | true, files -> files :> seq<int>
            | _ -> Seq.empty

        let record (table: Dictionary<string, ResizeArray<int>>) idx name =
            match table.TryGetValue name with
            | true, files -> files.Add idx
            | _ -> table[name] <- ResizeArray [ idx ]

        let names = inputs |> Array.map DeclarationCheck.declaredNames

        names
        |> Array.iteri (fun idx (entities, namespaces) ->
            for name in entities do
                record entityFiles idx name

            for name in namespaces do
                record namespaceFiles idx name)

        let closed = Array.zeroCreate<int[]> files.Length

        for idx in 0 .. files.Length - 1 do
            let dependencies = HashSet<int>()
            let pending = Stack<int>(graph[idx])
            let entities, namespaces = names[idx]

            for name in entities do
                for other in Seq.append (filesOf entityFiles name) (filesOf namespaceFiles name) do
                    pending.Push other

            for name in namespaces do
                for other in filesOf entityFiles name do
                    pending.Push other

            while pending.Count > 0 do
                let dependency = pending.Pop()

                if dependency < idx && dependencies.Add dependency then
                    for transitive in closed[dependency] do
                        pending.Push transitive

                    // A pair whose names differ: the signature does not stand in for the implementation file
                    if filePairs.IsSignature dependency && not (matched.Contains parses[dependency].FileName) then
                        pending.Push(filePairs.GetImplementationIndex dependency)

            closed[idx] <- dependencies |> Seq.sort |> Array.ofSeq

        ctx.Dependencies <-
            Some
                { Parses = Array.copy parses
                  Dependencies = closed |> Array.map Array.copy
                  ModuleNamesBefore = moduleNamesBefore
                  MatchedSignatures = matched }

        closed

    /// Checks an implementation file whole, as a full check does, after the files before it: every earlier file, or
    /// those FileDependencies gives for this parse. It keeps no per-declaration state: the result has no
    /// fingerprints. It checks with no name-resolution sink, as a project check does; the result's check results are
    /// built when first read (FileResult.CheckResults).
    ///
    /// The diagnostics come from `parse`, filtered with its #nowarn scopes, as FinishFile's do.
    static member CheckFile(ctx: ProjectContext, before: FileSignature list, parse: FSharpParseFileResults) : FileResult =
        let state = ctx.State

        match parse.ParseTree with
        | ParsedInput.SigFile _ -> invalidArg (nameof parse) "Expected an implementation file."
        | ParsedInput.ImplFile _ ->
            let phaseTicks = Dictionary<string, int64>()
            let mutable phaseStart = System.Diagnostics.Stopwatch.GetTimestamp()

            let endPhase name =
                let now = System.Diagnostics.Stopwatch.GetTimestamp()
                phaseTicks[name] <- now - phaseStart
                phaseStart <- now

            let moduleNamesBefore = DeclarationCheck.checkBefore ctx before parse
            DeclarationCheck.refuseUnlessCurrentDirectives parse
            let options = DeclarationCheck.warnOptionsOf parse
            let tcState, moduleNamesDict, input, file = DeclarationCheck.implFileState ctx.Checks before moduleNamesBefore parse
            let capturing, logger = DeclarationCheck.newLoggersWith options
            use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
            use _ = FSharp.Compiler.Cancellable.UsingToken CancellationToken.None

            // The fingerprint reads the compiled names of the file's values, which are given on first read
            let signature =
                lock (ctx.Checks.FileLock parse.FileName) (fun () ->
                    let rootSigOpt = DeclarationCheck.enterImplFile state tcState input file
                    endPhase "setup"
                    let checkedFile = DeclarationCheck.checkImplFile state tcState rootSigOpt file parse logger TcResultsSink.NoSink
                    endPhase "tail"

                    match checkedFile with
                    | Some(topAttrs, implFile, _, createsGeneratedProvidedTypes, _) ->
                        // No declaration stands for what later files see of it, so the file does, as a signature file
                        let definitions =
                            match rootSigOpt with
                            | Some _ -> Map.empty
                            | None -> DeclarationCheck.signatureDefinitions parse.FileName implFile.Signature

                        endPhase "definitions"
                        let fingerprint = DeclarationCheck.implFingerprint rootSigOpt implFile.Signature topAttrs
                        endPhase "fingerprint"

                        DeclarationCheck.implFileSignature
                            state
                            parse.FileName
                            file.QualifiedName
                            implFile.Signature
                            createsGeneratedProvidedTypes
                            moduleNamesDict
                            definitions
                            fingerprint
                    | None -> DeclarationCheck.failedFileSignature parse.FileName moduleNamesDict)

            let diagnostics =
                Array.append parse.Diagnostics (DeclarationCheck.diagnosticsWith state options parse.FileName capturing)
                |> DeclarationCheck.projectDiagnostics ctx

            endPhase "render"
            // The check and the rendering read the directives: neither may have seen a newer parse's
            DeclarationCheck.refuseUnlessCurrentDirectives parse

            // Holds the setup's inputs, not the setup it built from them, so the check state is not kept alive, and not
            // the context, which reaches every parse of the project
            let checks = ctx.Checks

            let checkResults =
                Lazy<FSharpCheckFileResults>(
                    (fun () -> DeclarationCheck.buildCheckResults checks before moduleNamesBefore parse diagnostics),
                    LazyThreadSafetyMode.ExecutionAndPublication
                )

            FileResult(diagnostics, Dictionary<DeclarationKey, string>(HashIdentity.Structural), signature, checkResults, phaseTicks)

    /// Checks one declaration in the environment after an earlier one, or the first. Each call has its own checker
    /// state and accumulator, so calls may come in any order, again, or at the same time, without publishing into
    /// the file setup or another result's module contents. It first undoes what the latest FinishFile on the same
    /// FileStart changed in the earlier declarations, so it sees them as their checks left them.
    ///
    /// A check still changes earlier results in place, and nothing undoes that: it can solve the inference variables
    /// an earlier declaration left free (LeavesFreeTypars), and it marks the earlier values it uses as referenced
    /// (SetHasBeenReferenced). DependsOnLaterDeclarations says when that matters: such a result is re-checked when
    /// any later declaration of its file changes, is added or is removed.
    ///
    /// Check a declaration in the environment ExtendEnv assembles from the current results of the declarations before
    /// it: the EnvAfter of an earlier check holds those declarations as they were then.
    ///
    /// A nested module's header creates the module's entity, the parent of the values its declarations define, and
    /// those declarations are checked in the environment it leads to. So when a header is checked again, the module's
    /// declarations must be checked again after it. The first declaration after a module gives the module its
    /// contents so far as its type, as FinishFile does: the module's entity is shared, and the last of them wins.
    static member CheckDeclaration(start: FileStart, envBefore: DeclEnv, decl: ParsedDeclaration, ct: CancellationToken) : DeclarationResult =
        if decl.Depth > envBefore.Frames.Length then
            invalidArg (nameof envBefore) "The environment is outside the declaration's module: it is not the environment after the declaration before it."

        start.UndoLastFinish()
        let state = start.Context.State
        let capturing, logger = DeclarationCheck.newLoggers state
        use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
        // Cancellable.run hands ct to the cancellable computation; code outside it calls CheckAndThrow, which reads
        // the ambient token, and nothing else sets that one.
        use _ = FSharp.Compiler.Cancellable.UsingToken ct
        let sink = TcResultsSinkImpl(state.tcGlobals)
        let cenv, _, _ = DeclarationCheck.newCheckerState state start.TcState start.RootSigOpt start.File sink
        let referenced = ResizeArray<Val>()
        cenv.recordValueReference <- fun v -> if v.IsModuleBinding then referenced.Add v
        let envBefore = DeclarationCheck.exitModules state start envBefore decl.Depth
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

        // As checking the whole file: nothing in a scope or module whose setup failed is checked
        let checks =
            start.Scope.ChecksDeclarations
            && (match envBefore.Frames with
                | frame :: _ -> frame.Entity.IsSome
                | [] -> true)

        // Only a module reads them, for its suffix, and the whole check collects them once, in the environment where
        // the enclosing module's declarations start. Inside a nested module, that is what its header collected. At the
        // file's scope it is redone from the siblings' syntax (which HeaderInputs covers) in the scope's environment,
        // so a FileStart made before a sibling type was added still gives the suffix. A cenv of its own keeps the
        // attribute resolutions it reports out of this declaration's sink.
        let typeNames =
            match decl.Syntax with
            | SynModuleDecl.NestedModule _ when decl.Depth = 0 ->
                let scratch, _, _ = DeclarationCheck.newCheckerState state start.TcState start.RootSigOpt start.File (TcResultsSinkImpl state.tcGlobals)
                TypeNamesOfDeclarations scratch start.Scope.Env decl.Siblings
            | _ -> envBefore.TypeNames

        let checkedDecl, envAfter, envAtEnd, delta, nesting =
            if decl.IsModuleHeader then
                let entered =
                    if checks then
                        EnterNestedModuleDeclarations cenv envBefore.Parent typeNames env decl.Syntax
                    else
                        None

                let frame =
                    { Entity = entered |> Option.map (fun (entity, _, _, _) -> entity)
                      ScopeRange = decl.ScopeRange
                      Range = decl.Syntax.Range
                      OuterEnv = env
                      OuterParent = envBefore.Parent
                      OuterTypeNames = envBefore.TypeNames
                      Checked = [] }

                let envAfter =
                    match entered with
                    | Some(_, envForModule, parent, typeNames) ->
                        DeclEnv(envForModule, parent, typeNames, frame :: envBefore.Frames, envBefore.Definitions)
                    | None -> DeclEnv(env, envBefore.Parent, envBefore.TypeNames, frame :: envBefore.Frames, envBefore.Definitions)

                // What the header decides about the module (its name, kind, attributes, access), without the contents
                // the module's declarations give it, which FinishFile replaces
                let delta =
                    match frame.Entity with
                    | Some entity ->
                        let header =
                            { entity with
                                entity_modul_type = MaybeLazy.Strict(Construct.NewEmptyModuleOrNamespaceType entity.ModuleOrNamespaceType.ModuleOrNamespaceKind) }

                        Construct.NewModuleOrNamespaceType contentsBefore.ModuleOrNamespaceKind [ header ] []
                    | None -> Construct.NewEmptyModuleOrNamespaceType contentsBefore.ModuleOrNamespaceKind

                ([], [], []), envAfter, envAfter.Env, delta, ModuleHeader(decl.Depth, frame)
            else
                let checkedDecl, envAfter, envAtEnd =
                    if not checks then
                        ([], [], []), env, env
                    else
                        TcModuleOrNamespaceElementNonMutRec cenv envBefore.Parent typeNames decl.ScopeRange env decl.Syntax
                        |> cenv.stackGuard.GuardCancellable
                        |> Cancellable.run ct
                        |> function
                            | ValueOrCancelled.Value result -> result
                            | ValueOrCancelled.Cancelled exn -> raise exn

                let frames =
                    match envBefore.Frames with
                    | frame :: outer -> { frame with Checked = checkedDecl :: frame.Checked } :: outer
                    | [] -> []

                let delta = DeclarationCheck.contribution contentsAtStart accumulator.Value
                checkedDecl, DeclEnv(envAfter, envBefore.Parent, envBefore.TypeNames, frames, envBefore.Definitions), envAtEnd, delta, InModules decl.Depth

        let leavesFreeTypars =
            DeclarationCheck.anySolvable (GeneralizationHelpers.ComputeUngeneralizableTypars envAfter.Env)

        let self = { File = start.Parse.FileName; Key = Some decl.Key }
        let definitions = DeclarationCheck.addDefinitions envBefore.Definitions self delta
        let envAfter = DeclEnv(envAfter.Env, envAfter.Parent, envAfter.TypeNames, envAfter.Frames, definitions)
        let contents, _, _ = checkedDecl

        // By the declaration that defines each and the value's name, never the value: FinishFile finds the value in
        // whatever result of that declaration is current
        let references =
            referenced
            |> Seq.choose (fun v ->
                definitions.TryFind v.Stamp
                |> Option.map (fun declaration -> declaration, DeclarationCheck.modulePathOf v, v.LogicalName))
            |> Seq.distinct
            |> Array.ofSeq

        let slots = DeclarationCheck.slotsAtCheck delta

        DeclarationResult(
            start,
            decl,
            DeclarationCheck.fingerprintOf delta checkedDecl slots,
            DeclarationCheck.diagnosticsOf state start.Parse.FileName capturing,
            logger.Diagnostics,
            leavesFreeTypars,
            leavesFreeTypars || DeclarationCheck.leavesOpenTypes delta checkedDecl,
            slots,
            envAfter,
            envAtEnd,
            checkedDecl,
            delta,
            deltaCombines,
            sink,
            DeclarationCheck.leftoversOf cenv,
            nesting,
            DeclarationCheck.typedUsesOf definitions self delta contents (Some sink),
            references
        )

    /// The environment after the declaration of `result`, assembled from `envBefore` without checking it again: what
    /// it defined (its values and entities), what it opened, its module structure. For name resolution it equals the
    /// environment a fresh check of the declaration in envBefore would leave, with the definitions of this result.
    /// A stored EnvAfter holds the earlier declarations as they were when it was checked; a declaration's environment
    /// is instead built by folding ExtendEnv over the current results of the declarations before it, from the
    /// environment BeginFile gave. Like CheckDeclaration, it first undoes what the latest FinishFile on the same
    /// FileStart changed.
    static member ExtendEnv(envBefore: DeclEnv, result: DeclarationResult) : DeclEnv =
        let decl = result.Declaration

        if decl.Depth > envBefore.Frames.Length then
            invalidArg (nameof envBefore) "The environment is outside the declaration's module: it is not the environment after the declaration before it."

        let start = result.Start
        start.UndoLastFinish()
        let state = start.Context.State
        use _ = new CompilationGlobalsScope(DiscardErrorsLogger, BuildPhase.TypeCheck)
        use _ = FSharp.Compiler.Cancellable.UsingToken CancellationToken.None
        let envBefore = DeclarationCheck.exitModules state start envBefore decl.Depth
        // Its own checker state and sink: resolving an open or a module abbreviation again reports nothing
        let cenv, _, _ = DeclarationCheck.newCheckerState state start.TcState start.RootSigOpt start.File (TcResultsSinkImpl state.tcGlobals)
        let definitions = DeclarationCheck.addDefinitions envBefore.Definitions result.Ref result.Delta
        let contentsBefore = envBefore.Env.eModuleOrNamespaceTypeAccumulator.Value

        match result.Nesting with
        | ModuleHeader(_, frame) ->
            // As CheckDeclaration for a header: the module is published when it is left, not here
            let env = { envBefore.Env with eModuleOrNamespaceTypeAccumulator = ref contentsBefore }

            let frame =
                { frame with
                    OuterEnv = env
                    OuterParent = envBefore.Parent
                    OuterTypeNames = envBefore.TypeNames
                    Checked = [] }

            match frame.Entity with
            | Some entity ->
                // As TcNestedModuleHeader and EnterNestedModuleDeclarations, with the module the header's check made
                let envForModule, _ = MakeInnerEnv true env entity.Id entity.ModuleOrNamespaceType.ModuleOrNamespaceKind

                let moduleDecls =
                    match decl.Syntax with
                    | SynModuleDecl.NestedModule(decls = decls) -> decls
                    | _ -> []

                let typeNames = TypeNamesOfDeclarations cenv envForModule moduleDecls
                DeclEnv(envForModule, Parent(mkLocalModuleRef entity), typeNames, frame :: envBefore.Frames, definitions)
            | None -> DeclEnv(env, envBefore.Parent, envBefore.TypeNames, frame :: envBefore.Frames, definitions)
        | InModules _ ->
            let checks =
                start.Scope.ChecksDeclarations
                && (match envBefore.Frames with
                    | frame :: _ -> frame.Entity.IsSome
                    | [] -> true)

            // Replayed against what the module or namespace held before it, as its check saw it (a recursive
            // fragment reads that), then given what it publishes
            let env = { envBefore.Env with eModuleOrNamespaceTypeAccumulator = ref contentsBefore }

            let env =
                if checks then
                    ExtendEnvWithDeclaration cenv decl.ScopeRange env decl.Syntax result.Delta
                else
                    env

            let accumulator = ref (DeclarationCheck.mergeDelta contentsBefore result.Delta result.DeltaCombines)
            let env = { env with eModuleOrNamespaceTypeAccumulator = accumulator }

            let frames =
                match envBefore.Frames with
                | frame :: outer -> { frame with Checked = result.Checked :: frame.Checked } :: outer
                | [] -> []

            DeclEnv(env, envBefore.Parent, envBefore.TypeNames, frames, definitions)

    /// Builds the file from the declarations' results, in declaration order, closes its inference scope, and takes
    /// the declarations' final fingerprints.
    ///
    /// The file's accumulators, namespace entities and checker state are new each time. A 'module X.Y' file's module
    /// entity is not: it is the setup's, the parent of the declarations' values, shared by every finish on this
    /// FileStart. Each finish gives it a new type, so the last finish wins, and an earlier FileResult shows that
    /// finish's module contents. The same holds for a nested module's entity, which its header's result holds.
    ///
    /// Closing the inference scope changes the declarations' typed trees in place: defaults and other solutions of
    /// their inference variables, trait solutions, closed augmentations, the slots members implement (whose check-time
    /// form the fingerprints keep, see DeclarationCheck.slotsAtCheck). These are recorded and undone before the
    /// next finish or declaration check on this FileStart, so a finish over the same or other results gives what a
    /// full check would. Finishes on one FileStart are serialized, by its lock; a finish must not overlap a
    /// declaration check on the same FileStart.
    ///
    /// The diagnostics come from `parse`, which must be the parse of the file's current text (the FileStart's own
    /// parse only while the text is unchanged): its parse diagnostics, and its #nowarn scopes, which filter every
    /// declaration's diagnostics again and decide which errors stop the finish pass from reporting. A #nowarn is not
    /// a declaration, so adding or removing one changes no result: only this parse carries it.
    ///
    /// An error that escapes closing the inference scope is recovered from as a full check's CheckOneInput does:
    /// the file then adds nothing to later files' environments, and its check results have no implementation file.
    static member FinishFile(start: FileStart, results: DeclarationResult[], parse: FSharpParseFileResults) : FileResult =
        if not (String.Equals(parse.FileName, start.Parse.FileName, StringComparison.OrdinalIgnoreCase)) then
            invalidArg (nameof parse) "The parse is of another file than the FileStart's."

        lock start.Sync (fun () ->
            start.UndoLastFinish()
            let log = ResizeArray()
            let outer = MutationLog.Current
            MutationLog.Current <- log

            try
                DeclarationChecker.Finish(start, results, parse)
            finally
                MutationLog.Current <- outer
                start.SetLastFinish log)

    static member private Finish(start: FileStart, results: DeclarationResult[], parse: FSharpParseFileResults) : FileResult =
        let state = start.Context.State
        let file = start.File
        let tcState = start.TcState
        let phaseTicks = Dictionary<string, int64>()
        let mutable phaseStart = System.Diagnostics.Stopwatch.GetTimestamp()

        let endPhase name =
            let now = System.Diagnostics.Stopwatch.GetTimestamp()
            phaseTicks[name] <- now - phaseStart
            phaseStart <- now

        let options = DeclarationCheck.warnOptionsOf parse

        // With the parse's #nowarn scopes, which an added or removed #nowarn changes without changing any declaration.
        // Rendered after the tail, as a full check renders them, so their types show what the defaults solved.
        let earlierDiagnostics =
            [| yield DeclarationCheck.refiltered options start.RawDiagnostics
               for result in results do
                   yield DeclarationCheck.refiltered options result.RawDiagnostics |]

        let earlierErrors = earlierDiagnostics |> Array.sumBy (fun capturing -> capturing.ErrorCount)
        endPhase "refilter"

        let capturing, logger = DeclarationCheck.newLoggersWith options
        use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
        use _ = FSharp.Compiler.Cancellable.UsingToken CancellationToken.None
        let sink = TcResultsSinkImpl(state.tcGlobals)
        let cenv, envFile, moduleTyAcc = DeclarationCheck.newCheckerState state tcState start.RootSigOpt file sink
        start.Leftovers cenv

        for result in results do
            result.Leftovers cenv

        endPhase "leftovers"

        let scopeContents, compiledDefs, envAtEnd =
            DeclarationCheck.assemble cenv start.ScopeContents start.Scope.Env results

        endPhase "assemble"
        let checkForErrors () = parse.ParseHadErrors || earlierErrors > 0 || logger.ErrorCount > 0
        DeclarationCheck.replayReferences start.Parse.FileName results
        endPhase "replay"

        // Recovered from as CheckOneInput recovers in a full check, such as a default that fails where the tail does
        // not catch it (SolveInternalUnknowns): the file then adds nothing to the files after it.
        let tail =
            try
                let fileContents =
                    ExitImplFileDeclarations cenv envFile tcState.ImplicitOpenDeclarations start.Scope scopeContents compiledDefs envAtEnd

                Some(CheckImplFileTail cenv checkForErrors tcState.TcEnvFromImpls start.RootSigOpt file moduleTyAcc fileContents)
            with RecoverableException exn ->
                errorRecovery exn range0
                None

        endPhase "tail"
        let qualNameOfFile = file.QualifiedName

        // The finish can solve more of each declaration's types and traits; this is the last finish's view
        for result in results do
            let contents, _, _ = result.Checked
            result.SetFinishTypedUses(DeclarationCheck.typedUsesOf result.EnvAfter.Definitions result.Ref result.Delta contents None)

        endPhase "typedUses"

        let signature, ccuSigForFile, ownSigForFile, tcEnvAtEnd, implFileOpt =
            match tail with
            | Some(topAttrs, implFile, tcEnvAtEnd, createsGeneratedProvidedTypes, ownSigForFile) ->
                // Later files see a copy of the file's contents, or the signature file's declarations, which it maps already
                let definitions =
                    match start.RootSigOpt with
                    | Some _ -> Map.empty
                    | None ->
                        let own = (Map.empty, results) ||> Array.fold (fun acc result -> DeclarationCheck.addDefinitions acc result.Ref result.Delta)
                        DeclarationCheck.copiedDefinitions own moduleTyAcc.Value implFile.Signature Map.empty

                let signature =
                    DeclarationCheck.implFileSignature
                        state
                        parse.FileName
                        qualNameOfFile
                        implFile.Signature
                        createsGeneratedProvidedTypes
                        start.ModuleNamesDict
                        definitions
                        (DeclarationCheck.implFingerprint start.RootSigOpt implFile.Signature topAttrs)

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

                signature, ccuSigForFile, ownSigForFile, tcEnvAtEnd, Some implFile
            | None ->
                DeclarationCheck.failedFileSignature parse.FileName start.ModuleNamesDict,
                tcState.CcuSig,
                Construct.NewEmptyModuleOrNamespaceType(ModuleOrNamespaceKind.Namespace true),
                tcState.TcEnvFromSignatures,
                None

        endPhase "signature"

        // While the finish's solutions are in effect: the next finish or declaration check undoes them
        let diagnostics =
            Array.concat
                [ yield parse.Diagnostics
                  for earlier in earlierDiagnostics do
                      yield DeclarationCheck.diagnosticsWith state options parse.FileName earlier
                  yield DeclarationCheck.diagnosticsWith state options parse.FileName capturing ]
            |> DeclarationCheck.projectDiagnostics start.Context

        endPhase "render"

        let fingerprints =
            Dictionary<DeclarationKey, string>(HashIdentity.Structural)

        for result in results do
            fingerprints[result.Key] <- DeclarationCheck.fingerprintOf result.Delta result.Checked result.SlotsAtCheck

        endPhase "fingerprints"

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
                implFileOpt,
                openDeclarations
            )

        let checkResults =
            FSharpCheckFileResults(parse.FileName, diagnostics, Some scope, parse.DependencyFiles, None, true)

        endPhase "sinks"
        FileResult(diagnostics, fingerprints, signature, Lazy<_>.CreateFromValue checkResults, phaseTicks)
