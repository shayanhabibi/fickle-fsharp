// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.CodeAnalysis.Declarations

open System
open System.Collections.Generic
open System.Threading
open FSharp.Compiler
open FSharp.Compiler.AbstractIL.ILBinaryReader
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.CheckDeclarations
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.CompilerConfig
open FSharp.Compiler.CompilerImports
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.EditorServices
open FSharp.Compiler.NameResolution
open FSharp.Compiler.ParseAndCheckInputs
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.TcGlobals
open FSharp.Compiler.Text
open FSharp.Compiler.TypedTree
open FSharp.Compiler.TypedTreeOps

[<RequireQualifiedAccess>]
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
    {
        /// The file's module or namespace, then the nested modules the declaration is in.
        ModulePath: string list
        Name: string
        Kind: DeclarationKind
        /// The number of earlier declarations of the file with the same module path, name and kind.
        Ordinal: int
    }

/// A declaration of the project that a typed use resolves to: the declaration with Key in File.
/// Key is None for what a signature file declares, which is checked whole: a use of it depends on that file's text.
type DeclarationRef =
    {
        File: string
        Key: DeclarationKey option
    }

/// The names a declaration defines and uses, from its syntax.
type DeclarationContent =
    {
        /// Values, types, union cases, record fields, members, custom operation names and modules.
        Defines: string[]
        /// Names resolved in the environment: unqualified identifiers, every segment of qualified ones, types, attributes, and opened modules.
        Uses: string[]
        /// Names after a dot and members constructs call implicitly.
        MemberUses: string[]
        /// Record labels and union cases, including names after a dot.
        FieldOrCaseUses: string[]
        /// Something resolves to a name the syntax does not show, such as the `?` operator.
        HasUnresolvable: bool
        /// Every later declaration depends on this one: open, an [&lt;AutoOpen&gt;] module, a module abbreviation,
        /// a module-level do, an attribute declaration, a hash directive, or a custom operation whose name is unknown.
        AffectsAllLater: bool
        /// The names, as written, of the types the declaration augments, sorted; empty for anything else.
        Augments: string[]
    }

/// A top-level declaration of an implementation file, or a declaration of a non-recursive nested module, or the
/// header of such a module.
[<Sealed>]
type ParsedDeclaration =
    internal new:
        key: DeclarationKey *
        decl: SynModuleDecl *
        range: range *
        scopem: range *
        text: string *
        headerInputs: string *
        within: DeclarationKey option *
        siblings: SynModuleDecl list *
        depth: int *
        isModuleHeader: bool *
        source: ISourceText -> ParsedDeclaration

    member Key: DeclarationKey
    /// The declaration's range; for a module header, from its start to the '=' after the module's name.
    member Range: range
    /// A hash of the declaration's source text. Unequal hashes mean the text changed; equal ones do not prove it is the same.
    member SyntaxHash: int
    /// The declaration's source text, from the start of its range to its end.
    member Text: string
    /// For a module or module header, what checking it reads beyond its text; empty for other declarations.
    member HeaderInputs: string
    /// The key of the module header this declaration is directly inside, if any.
    member Within: DeclarationKey option
    /// Whether checking this declaration reads the same syntax as checking the other: same Text and HeaderInputs.
    member IsUnchangedFrom: other: ParsedDeclaration -> bool
    member internal Syntax: SynModuleDecl
    member internal ScopeRange: range
    member internal Depth: int
    member internal IsModuleHeader: bool
    member internal Siblings: SynModuleDecl list
    member internal Source: ISourceText

/// A scoped `before` was refused because the dependency snapshot it would be checked against is not current for the file.
type StaleDependenciesException =
    inherit ArgumentException
    new: message: string -> StaleDependenciesException

/// A check was refused because the process's #line directives of the file are not its parse's.
type SupersededLineDirectivesException =
    inherit InvalidOperationException
    new: message: string -> SupersededLineDirectivesException

type internal CompilerState =
    {
        tcConfig: TcConfig
        tcGlobals: TcGlobals
        tcImports: TcImports
        tcInitialState: TcState
        projectOptions: FSharpProjectOptions
    }

[<AutoOpen>]
module internal CompilerStateInit =
    val userOpName: string
    val suggestNamesForErrors: bool
    val captureIdentifiersWhenParsing: bool
    val initializeCompilerStateWith:
        projectReferences: IProjectReference list -> projectOptions: FSharpProjectOptions -> reset: (unit -> unit) -> Async<CompilerState>
    val initializeCompilerState: projectOptions: FSharpProjectOptions -> reset: (unit -> unit) -> Async<CompilerState>
    val ResetGeneratedNames: input: ParsedInput * compilerState: CompilerState -> unit

[<NoEquality; NoComparison>]
type internal DependencySnapshot =
    {
        Parses: FSharpParseFileResults[]
        Dependencies: int[][]
        ModuleNamesBefore: ModuleNamesDict[]
        MatchedSignatures: HashSet<string>
    }

[<Sealed>]
type internal SetupNode =
    new: state: TcState -> SetupNode
    member State: TcState
    member After: key: obj * step: (TcState -> TcState) -> SetupNode

[<Sealed>]
type internal ProjectChecks =
    new: state: CompilerState -> ProjectChecks
    member State: CompilerState
    member SetupRoot: SetupNode
    member IndexOf: fileName: string -> int
    member IsBefore: fileName: string * other: string -> bool
    member FileLock: fileName: string -> obj
    member SetLatestParse: parse: FSharpParseFileResults -> unit
    member LatestParse: fileName: string -> FSharpParseFileResults option
    member CheckResultsBuilt: int
    member CountCheckResultsBuilt: unit -> unit

/// A project's options, references and initial checking state.
[<Sealed>]
type ProjectContext =
    internal new: state: CompilerState -> ProjectContext
    member internal State: CompilerState
    member internal Checks: ProjectChecks
    /// For tests: how many times CheckFile's results on this context built a name-resolution sink and check results.
    member CheckResultsBuilt: int
    /// Runs `f` holding the file's check lock, as a declaration check does. For tests.
    member HoldingCheckLock: fileName: string * f: (unit -> 'T) -> 'T
    /// For tests: when set, DeclarationChecker.Shift refuses every declaration of this context.
    member RefuseShifts: bool with get, set
    /// Runs with the reason each time DeclarationChecker.Shift refuses a declaration of this context whose text is the same at another line.
    member ShiftRefusedHook: (string -> unit) with get, set
    /// How many checks the finish ran for shifted results of any context in the process reported at a range outside their declaration.
    static member ShiftFinishMisses: int64
    member internal ParseLock: fileName: string -> obj
    member internal IsSourceFile: fileName: string -> bool
    member internal IndexOf: fileName: string -> int option
    member internal SourceFiles: string[]
    member internal SetLatestParse: parse: FSharpParseFileResults -> unit
    member internal LatestParse: fileName: string -> FSharpParseFileResults option
    member internal Dependencies: DependencySnapshot option with get, set

/// What a file adds to the state later files are checked in.
[<Sealed>]
type FileSignature =
    internal new:
        fileName: string *
        apply: (TcState -> TcState) *
        moduleNamesDict: ModuleNamesDict *
        definitions: Map<Stamp, DeclarationRef> *
        fingerprint: Lazy<string> *
        moduleType: ModuleOrNamespaceType *
        asImplementation: (TcState -> TcState) option *
        failed: bool *
        uses: (struct (Item * ItemOccurrence * range))[] *
        semanticClassification: SemanticClassificationItem[] -> FileSignature

    /// What the files after this one see of it, as the file-level SignatureFingerprint describes it.
    member Fingerprint: string
    /// Whether the fingerprint has been taken: comparing it otherwise takes it.
    member HasFingerprint: bool
    member internal FileName: string
    member internal Apply: tcState: TcState -> TcState
    member internal ModuleNamesDict: ModuleNamesDict
    member internal Definitions: Map<Stamp, DeclarationRef>
    member internal Uses: (struct (Item * ItemOccurrence * range))[]
    /// Semantic classification items captured during signature checking; empty for an implementation file's signature.
    member SemanticClassification: SemanticClassificationItem[]
    member internal ModuleType: ModuleOrNamespaceType
    /// For tests: every type variable or entity the signature's types use that it does not itself hold.
    member OutOfScope: unit -> string[]
    /// For tests: the names of the type parameters of the signature's values.
    member TyparNames: unit -> string[]
    member internal AsImplementation: (TcState -> TcState) option
    /// Whether the implementation file's check failed with an error it recovered from.
    member Failed: bool
    member internal ArtificialKey: obj

type internal CheckedDeclaration = ModuleOrNamespaceContents list * (unit -> unit) list * (AttributeTargets * Attrib) list

type internal RawDiagnostics =
    inherit DiagnosticsLogger
    new: next: DiagnosticsLogger -> RawDiagnostics
    member Diagnostics: PhasedDiagnostic[]

[<NoEquality; NoComparison>]
type internal ModuleFrame =
    {
        Entity: ModuleOrNamespace option
        ScopeRange: range
        Range: range
        OuterEnv: TcEnv
        OuterParent: ParentRef
        OuterTypeNames: Set<string>
        Checked: CheckedDeclaration list
    }

/// The environment a declaration is checked in.
[<Sealed>]
type DeclarationEnvironment =
    internal new:
        env: TcEnv *
        parent: ParentRef *
        typeNames: Set<string> *
        frames: ModuleFrame list *
        definitions: Map<Stamp, DeclarationRef> -> DeclarationEnvironment

    member internal Env: TcEnv
    member internal Parent: ParentRef
    member internal TypeNames: Set<string>
    member internal Frames: ModuleFrame list
    member internal Definitions: Map<Stamp, DeclarationRef>

[<NoEquality; NoComparison>]
type internal Nesting =
    | InModules of depth: int
    | ModuleHeader of depth: int * frame: ModuleFrame

    member Depth: int

[<Sealed>]
type internal FinishUndo =
    new: unit -> FinishUndo
    member Log: ResizeArray<unit -> unit> | null with get, set

[<Sealed>]
type internal Leftovers =
    new:
        preDefaults: (unit -> unit)[] *
        final: (unit -> unit)[] *
        extraCxs: (Stamp * (TraitConstraintInfo * range)) list *
        unionsWithDeferredAttributes: Set<Stamp> *
        deferredUnionNullnessChecks: (TType * range) list *
        createsGeneratedProvidedTypes: bool *
        namedDebugPoints: KeyValuePair<NamedDebugPointKey, range>[] *
        moved: struct (int * range * pos * int) voption -> Leftovers

    static member Of: cenv: TcFileState -> Leftovers
    member Apply: into: TcFileState -> unit
    member HasDeferredChecks: bool
    member Shifted: s: DeclarationShift.Shifter -> Leftovers

[<Sealed>]
type internal AugmentedTypes =
    new: unit -> AugmentedTypes
    member Add: target: Tycon * memberRef: ValRef -> unit
    member Iter: action: (Tycon -> ResizeArray<ValRef> -> unit) -> unit

/// An implementation file set up for checking its declarations one at a time.
[<Sealed>]
type FileStart =
    internal new:
        ctx: ProjectContext *
        parse: FSharpParseFileResults *
        file: ParsedImplFileInput *
        moduleNamesDict: ModuleNamesDict *
        tcState: TcState *
        rootSigOpt: ModuleOrNamespaceType option *
        scope: ImplFileDeclarationScope *
        scopeContents: ModuleOrNamespaceType *
        sink: TcResultsSinkImpl *
        leftovers: Leftovers *
        rawDiagnostics: PhasedDiagnostic[] -> FileStart

    member internal Context: ProjectContext
    member internal Augmented: AugmentedTypes
    /// The parse the file was set up from.
    member Parse: FSharpParseFileResults
    member internal File: ParsedImplFileInput
    member internal ModuleNamesDict: ModuleNamesDict
    member internal TcState: TcState
    member internal RootSigOpt: ModuleOrNamespaceType option
    member internal Scope: ImplFileDeclarationScope
    member internal ScopeContents: ModuleOrNamespaceType
    member internal Sink: TcResultsSinkImpl
    member internal Leftovers: Leftovers
    member internal RawDiagnostics: PhasedDiagnostic[]
    member internal Sync: obj
    member internal EnvAtStart: DeclarationEnvironment with get, set
    member internal UndoLastFinish: unit -> unit
    member internal SetLastFinish: log: ResizeArray<unit -> unit> -> unit
    member internal FinishUndo: FinishUndo
    member internal LastShares: obj | null with get, set

[<Sealed>]
type DeclarationResult =
    internal new:
        start: FileStart *
        declaration: ParsedDeclaration *
        fingerprint: string *
        atCheck: string voption *
        diagnostics: FSharpDiagnostic[] *
        rawDiagnostics: PhasedDiagnostic[] *
        leavesFreeTypars: bool *
        dependsOnLater: bool *
        openTypars: Typar[] *
        leavesUnsolved: bool *
        slotsAtCheck: IReadOnlyDictionary<Val, SlotSig list * bool> *
        envAfter: DeclarationEnvironment *
        envAtEnd: TcEnv *
        checkedDecl: CheckedDeclaration *
        delta: ModuleOrNamespaceType *
        deltaCombines: bool *
        sink: TcResultsSinkImpl *
        leftovers: Leftovers *
        nesting: Nesting *
        typedUses: DeclarationRef[] *
        heldDefinitions: (Stamp * DeclarationRef)[] *
        references: (DeclarationRef * string list * string)[] *
        shareKey: obj *
        capturedScope: range -> DeclarationResult

    member Key: DeclarationKey
    member internal ShareKey: obj
    /// The scope the check was given for the declaration, moved by each shift of the result.
    member CapturedScope: range
    member internal IsAdHoc: bool with get, set
    /// The fingerprint as the check left the declaration.
    member Fingerprint: string
    member internal AtCheck: string voption
    /// Provisional diagnostics filtered with the project's live options when checked.
    member Diagnostics: FSharpDiagnostic[]
    /// Whether the environment after the declaration holds inference variables nothing has solved yet.
    member LeavesFreeTypars: bool
    /// Whether later checks change this result in place, so it depends on every later declaration of its file.
    member DependsOnLaterDeclarations: bool
    /// Whether a later result holding what the declaration publishes must hold its latest check's.
    member DefinesEntities: bool
    member internal OpenTypars: Typar[]
    /// `OpenTypars`, each with where it comes from. For diagnosing why a result depends on later declarations.
    member DescribeOpenTypars: unit -> string[]
    member internal LeavesUnsolved: bool
    member EnvAfter: DeclarationEnvironment
    /// The declarations of the project this declaration depends on through types.
    member TypedUses: DeclarationRef[]
    member internal SetFinishTypedUses: uses: DeclarationRef[] -> unit
    member internal FinishTypedUses: DeclarationRef[]
    member internal ShiftedTo: DeclarationResult | null with get, set
    member internal CheckTypedUses: DeclarationRef[]
    member internal HeldDefinitions: (Stamp * DeclarationRef)[]
    member internal References: (DeclarationRef * string list * string)[]
    member internal Start: FileStart
    member internal Declaration: ParsedDeclaration
    member internal Ref: DeclarationRef
    member internal RawDiagnostics: PhasedDiagnostic[]
    member internal EnvAtEnd: TcEnv
    member internal Checked: CheckedDeclaration
    member internal Delta: ModuleOrNamespaceType
    member internal DeltaCombines: bool
    member internal Sink: TcResultsSinkImpl
    member internal Leftovers: Leftovers
    member internal Nesting: Nesting
    member internal SlotsAtCheck: IReadOnlyDictionary<Val, SlotSig list * bool>
    /// Whether the two results contribute the same Val and Entity objects, by reference and in the same order. For tests.
    member IsSameDelta: other: DeclarationResult -> bool

[<Sealed>]
type FileResult =
    internal new:
        diagnostics: FSharpDiagnostic[] *
        fingerprints: IReadOnlyDictionary<DeclarationKey, string> *
        signature: FileSignature *
        checkResults: Lazy<FSharpCheckFileResults> *
        phaseTicks: IReadOnlyDictionary<string, int64> *
        phaseAllocated: IReadOnlyDictionary<string, int64> *
        reused: int *
        topAttrs: TopAttribs *
        beforeRead: (unit -> unit) *
        buildAgain: (unit -> FSharpCheckFileResults) voption *
        classify: (range option -> SemanticClassificationItem[]) voption -> FileResult

    member Diagnostics: FSharpDiagnostic[]
    member internal TopAttrs: TopAttribs
    /// Each declaration's fingerprint after the file's inference scope is closed.
    member Fingerprints: IReadOnlyDictionary<DeclarationKey, string>
    member Signature: FileSignature
    /// Built on first read, holding the file's check lock.
    member CheckResults: FSharpCheckFileResults
    /// As CheckResults, for a reader that copies out what it needs without keeping CheckResults built again.
    member CheckResultsNotKept: FSharpCheckFileResults
    /// Semantic classifications for the checked file, filtered to `range` when given.
    member GetSemanticClassification: ?range: range -> SemanticClassificationItem[]
    member PhaseTicks: IReadOnlyDictionary<string, int64>
    member PhaseAllocated: IReadOnlyDictionary<string, int64>
    /// How many results' final fingerprint, finish TypedUses and rendered diagnostics came from the previous finish of the same FileStart.
    member Reused: int

/// A project's assembly as a referencing project sees it, built from the project's checked files without compiling.
[<Sealed>]
type ProjectAssembly =
    internal new: fingerprint: string * data: Lazy<ProjectAssemblyDataResult> -> ProjectAssembly
    member Fingerprint: string
    member internal Data: ProjectAssemblyDataResult
    member ReadsFileOnDisk: bool

[<NoEquality; NoComparison>]
type internal FinishShare =
    {
        Fingerprint: string
        Diagnostics: FSharpDiagnostic[]
        ErrorCount: int
        Line: int
    }

[<Sealed>]
type internal FinishShares =
    new:
        options: FSharpDiagnosticOptions *
        directives: (int * (int * int)) list *
        shares: Dictionary<obj, FinishShare> *
        keys: DeclarationKey[] *
        fingerprints: string[] *
        signature: FileSignature option *
        envs: (obj * DeclarationEnvironment)[] *
        exits: TcResultsSinkImpl[] -> FinishShares

    member Options: FSharpDiagnosticOptions
    member Directives: (int * (int * int)) list
    member Shares: Dictionary<obj, FinishShare>
    member Keys: DeclarationKey[]
    member Fingerprints: string[]
    member Signature: FileSignature option
    member Envs: (obj * DeclarationEnvironment)[]
    member Exits: TcResultsSinkImpl[]

type internal ScopesNow =
    new:
        setup: TcResultsSinkImpl *
        setupEnd: pos *
        rows: (TcResultsSinkImpl * range * range)[] *
        fileEnd: pos *
        current: (unit -> (range * range)[]) -> ScopesNow

    member Of: sink: TcResultsSinkImpl * m: range -> range
