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
      AffectsAllLater: bool }

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

/// A project's options, references and initial checking state.
[<Sealed>]
type ProjectContext internal (state: CompilerState) =
    let parseLocks = System.Collections.Concurrent.ConcurrentDictionary<string, obj>(StringComparer.OrdinalIgnoreCase)
    member internal _.State = state
    /// Held while a file is parsed and its #nowarn scopes, which the parse records in the project's options, are
    /// copied: parses of one file serialize, parses of different files do not.
    member internal _.ParseLock(fileName: string) = parseLocks.GetOrAdd(fileName, fun _ -> obj ())

/// What a file adds to the state later files are checked in.
[<Sealed>]
type FileSignature internal (fileName: string, apply: TcState -> TcState, moduleNamesDict: ModuleNamesDict) =
    member internal _.FileName = fileName
    member internal _.Apply tcState = apply tcState
    /// The module-name dictionary DeduplicateParsedInputModuleName gave for this file: every earlier file's entries
    /// and its own. BeginFile merges these over the earlier files.
    member internal _.ModuleNamesDict = moduleNamesDict

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
type DeclEnv internal (env: TcEnv, parent: ParentRef, typeNames: Set<string>, frames: ModuleFrame list) =
    member internal _.Env = env
    member internal _.Parent = parent
    member internal _.TypeNames = typeNames
    /// The nested modules the environment is inside, innermost first
    member internal _.Frames = frames

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
        key: DeclarationKey,
        fingerprint: string,
        diagnostics: FSharpDiagnostic[],
        rawDiagnostics: PhasedDiagnostic[],
        leavesFreeTypars: bool,
        envAfter: DeclEnv,
        envAtEnd: TcEnv,
        checkedDecl: CheckedDeclaration,
        delta: ModuleOrNamespaceType,
        deltaCombines: bool,
        sink: TcResultsSinkImpl,
        leftovers: TcFileState -> unit,
        nesting: Nesting
    ) =
    member _.Key = key
    /// The fingerprint as the check left the declaration. Finishing the file can still change it, by defaults or by
    /// later declarations solving its inference variables: FileResult.Fingerprints has the final one.
    member _.Fingerprint = fingerprint
    /// Provisional: the declaration's diagnostics filtered with the project's live options when it was checked,
    /// whose #nowarn scopes are those of whichever version of the file was parsed last. FileResult.Diagnostics is
    /// authoritative: FinishFile filters what the check reported with the scopes of the parse it is given.
    member _.Diagnostics = diagnostics
    member _.LeavesFreeTypars = leavesFreeTypars
    member _.EnvAfter = envAfter
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

    /// Diagnostics as reported, filtered by these options (a parse's copy, with its #nowarn scopes).
    let refiltered (state: CompilerState) diagnosticsOptions fileName (raw: PhasedDiagnostic[]) =
        let capturing, logger = newLoggersWith diagnosticsOptions

        for diagnostic in raw do
            logger.DiagnosticSink diagnostic

        diagnosticsWith state diagnosticsOptions fileName capturing

    /// Each parse's copy of the project's diagnostic options, holding the #nowarn scopes that parse recorded.
    let warnOptions = ConditionalWeakTable<FSharpParseFileResults, FSharpDiagnosticOptions>()

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

                    exit (DeclEnv(envAfter, frame.OuterParent, frame.OuterTypeNames, outer))
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

        // Lexing records the file's #nowarn scopes in the project's diagnostic options, replacing the last parse's:
        // copy them while no other parse of this file can replace them
        let (parseErrors, parseTree, anyErrors), warnOptions =
            lock (ctx.ParseLock fileName) (fun () ->
                let parsed =
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
                parsed, lock options (fun () -> { options with WarnScopeData = options.WarnScopeData }))

        let parse = FSharpParseFileResults(parseErrors, parseTree, anyErrors, [||])
        DeclarationCheck.sources.AddOrUpdate(parse, sourceText)
        DeclarationCheck.warnOptions.AddOrUpdate(parse, warnOptions)
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

        { Defines = DeclarationCheck.sorted defines
          Uses = DeclarationCheck.sorted uses
          MemberUses = DeclarationCheck.sorted members
          FieldOrCaseUses = DeclarationCheck.sorted fields
          HasUnresolvable = unresolvable
          AffectsAllLater = affectsAllLater || unreadableName }

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
                let _, logger = DeclarationCheck.newLoggers state
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

                start, DeclEnv(scope.Env, scope.Parent, scope.TypeNames, [])

    /// Checks one declaration in the environment after an earlier one, or the first. Each call has its own checker
    /// state and accumulator, so calls may come in any order, again, or at the same time, without publishing into
    /// the file setup or another result's module contents. It first undoes what the latest FinishFile on the same
    /// FileStart changed in the earlier declarations, so it sees them as their checks left them.
    ///
    /// A check still changes earlier results in place, and nothing undoes that: it can solve the inference variables
    /// an earlier declaration left free (LeavesFreeTypars), and it marks the earlier values it uses as referenced
    /// (SetHasBeenReferenced). The checker's guard (ruling R12, Task 13) re-checks a declaration that left free
    /// inference variables when any later declaration of its file changes or is removed.
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
                    | Some(_, envForModule, parent, typeNames) -> DeclEnv(envForModule, parent, typeNames, frame :: envBefore.Frames)
                    | None -> DeclEnv(env, envBefore.Parent, envBefore.TypeNames, frame :: envBefore.Frames)

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
                checkedDecl, DeclEnv(envAfter, envBefore.Parent, envBefore.TypeNames, frames), envAtEnd, delta, InModules decl.Depth

        let leavesFreeTypars =
            not (Zset.isEmpty (GeneralizationHelpers.ComputeUngeneralizableTypars envAfter.Env))

        DeclarationResult(
            decl.Key,
            DeclarationCheck.fingerprintOf delta checkedDecl,
            DeclarationCheck.diagnosticsOf state start.Parse.FileName capturing,
            logger.Diagnostics,
            leavesFreeTypars,
            envAfter,
            envAtEnd,
            checkedDecl,
            delta,
            deltaCombines,
            sink,
            DeclarationCheck.leftoversOf cenv,
            nesting
        )

    /// Builds the file from the declarations' results, in declaration order, closes its inference scope, and takes
    /// the declarations' final fingerprints.
    ///
    /// The file's accumulators, namespace entities and checker state are new each time. A 'module X.Y' file's module
    /// entity is not: it is the setup's, the parent of the declarations' values, shared by every finish on this
    /// FileStart. Each finish gives it a new type, so the last finish wins, and an earlier FileResult shows that
    /// finish's module contents. The same holds for a nested module's entity, which its header's result holds.
    ///
    /// Closing the inference scope changes the declarations' typed trees in place: defaults and other solutions of
    /// their inference variables, trait solutions, closed augmentations. These are recorded and undone before the
    /// next finish or declaration check on this FileStart, so a finish over the same or other results gives what a
    /// full check would. Finishes on one FileStart are serialized, by its lock; a finish must not overlap a
    /// declaration check on the same FileStart.
    ///
    /// The diagnostics come from `parse`, which must be the parse of the file's current text (the FileStart's own
    /// parse only while the text is unchanged): its parse diagnostics, and its #nowarn scopes, which filter every
    /// declaration's diagnostics again and decide which errors stop the finish pass from reporting. A #nowarn is not
    /// a declaration, so adding or removing one changes no result: only this parse carries it.
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

        let options =
            match DeclarationCheck.warnOptions.TryGetValue parse with
            | true, options -> options
            | _ -> invalidArg (nameof parse) "Only a parse made by DeclarationChecker.Parse can finish a file: its #nowarn scopes are the ones it recorded."

        // With the parse's #nowarn scopes, which an added or removed #nowarn changes without changing any declaration
        let earlierDiagnostics =
            Array.concat
                [ yield DeclarationCheck.refiltered state options parse.FileName start.RawDiagnostics
                  for result in results do
                      yield DeclarationCheck.refiltered state options parse.FileName result.RawDiagnostics ]

        let earlierErrors =
            earlierDiagnostics |> Array.sumBy (fun d -> if d.Severity = FSharpDiagnosticSeverity.Error then 1 else 0)

        let capturing, logger = DeclarationCheck.newLoggersWith options
        use _ = new CompilationGlobalsScope(logger, BuildPhase.TypeCheck)
        use _ = FSharp.Compiler.Cancellable.UsingToken CancellationToken.None
        let sink = TcResultsSinkImpl(state.tcGlobals)
        let cenv, envFile, moduleTyAcc = DeclarationCheck.newCheckerState state tcState start.RootSigOpt file sink
        start.Leftovers cenv

        for result in results do
            result.Leftovers cenv

        let scopeContents, compiledDefs, envAtEnd =
            DeclarationCheck.assemble cenv start.ScopeContents start.Scope.Env results

        let fileContents =
            ExitImplFileDeclarations cenv envFile tcState.ImplicitOpenDeclarations start.Scope scopeContents compiledDefs envAtEnd

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
                [ parse.Diagnostics
                  earlierDiagnostics
                  DeclarationCheck.diagnosticsWith state options parse.FileName capturing ]

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
