// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

module internal FSharp.Compiler.CheckDeclarations

open System
open FSharp.Compiler.Diagnostics
open Internal.Utilities.Library
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.NameResolution
open FSharp.Compiler.Import
open FSharp.Compiler.Syntax
open FSharp.Compiler.TcGlobals
open FSharp.Compiler.Text
open FSharp.Compiler.TypedTree

val AddLocalRootModuleOrNamespace: TcGlobals -> ImportMap -> range -> TcEnv -> ModuleOrNamespaceType -> TcEnv

val CreateInitialTcEnv:
    TcGlobals * ImportMap * range * assemblyName: string * (CcuThunk * string list * string list) list ->
        OpenDeclaration list * TcEnv

val AddCcuToTcEnv:
    TcGlobals *
    ImportMap *
    range *
    TcEnv *
    assemblyName: string *
    ccu: CcuThunk *
    autoOpens: string list *
    internalsVisibleToAttributes: string list ->
        OpenDeclaration list * TcEnv

type TopAttribs =
    { mainMethodAttrs: Attribs
      netModuleAttrs: Attribs
      assemblyAttrs: Attribs }

type ConditionalDefines = string list

val EmptyTopAttrs: TopAttribs

val CombineTopAttrs: TopAttribs -> TopAttribs -> TopAttribs

val TcOpenModuleOrNamespaceDecl:
    TcResultsSink -> TcGlobals -> ImportMap -> range -> TcEnv -> LongIdent * range -> TcEnv * OpenDeclaration list

val AddLocalSubModule:
    g: TcGlobals -> amap: ImportMap -> m: range -> env: TcEnv -> moduleEntity: ModuleOrNamespace -> TcEnv

val CheckOneImplFile:
    TcGlobals *
    ImportMap *
    CcuThunk *
    OpenDeclaration list *
    (unit -> bool) *
    ConditionalDefines option *
    TcResultsSink *
    bool *
    TcEnv *
    ModuleOrNamespaceType option *
    ParsedImplFileInput *
    FSharpDiagnosticOptions ->
        Cancellable<TopAttribs * CheckedImplFile * TcEnv * bool * ModuleOrNamespaceType>

/// Checks one declaration of a module or namespace that is not part of a recursive group
val TcModuleOrNamespaceElementNonMutRec:
    cenv: TcFileState ->
    parent: ParentRef ->
    typeNames: Set<string> ->
    scopem: range ->
    env: TcEnv ->
    synDecl: SynModuleDecl ->
        Cancellable<(ModuleOrNamespaceContents list * (unit -> unit) list * (AttributeTargets * Attrib) list) * TcEnv * TcEnv>

val CreateImplFileCheckState:
    TcGlobals *
    ImportMap *
    CcuThunk *
    ConditionalDefines option *
    TcResultsSink *
    bool *
    TcEnv *
    ModuleOrNamespaceType option *
    ParsedImplFileInput *
    FSharpDiagnosticOptions ->
        TcFileState * TcEnv * ModuleOrNamespaceType ref

val CheckImplFileTail:
    cenv: TcFileState ->
    checkForErrors: (unit -> bool) ->
    env: TcEnv ->
    rootSigOpt: ModuleOrNamespaceType option ->
    synImplFile: ParsedImplFileInput ->
    moduleTyAcc: ModuleOrNamespaceType ref ->
    ModuleOrNamespaceContents * (AttributeTargets * Attrib) list * TcEnv ->
        TopAttribs * CheckedImplFile * TcEnv * bool * ModuleOrNamespaceType

[<Sealed; NoEquality; NoComparison>]
type ImplFileFragmentScope

[<NoEquality; NoComparison>]
type ImplFileDeclarationScope =
    { Parent: ParentRef
      Env: TcEnv
      TypeNames: Set<string>
      EndRange: range
      Fragment: ImplFileFragmentScope option }

val EnterImplFileDeclarations:
    cenv: TcFileState ->
    env: TcEnv ->
    synImplFile: ParsedImplFileInput ->
    splitFragment: bool ->
        ImplFileDeclarationScope option

val ExitImplFileDeclarations:
    cenv: TcFileState ->
    env: TcEnv ->
    openDecls0: OpenDeclaration list ->
    scope: ImplFileDeclarationScope option ->
    compiledDefs: (ModuleOrNamespaceContents list * (unit -> unit) list * (AttributeTargets * Attrib) list) list ->
    envAtEnd: TcEnv ->
        ModuleOrNamespaceContents * (AttributeTargets * Attrib) list * TcEnv

val CheckOneSigFile:
    TcGlobals *
    ImportMap *
    CcuThunk *
    (unit -> bool) *
    ConditionalDefines option *
    TcResultsSink *
    bool *
    FSharpDiagnosticOptions ->
        TcEnv ->
        ParsedSigFileInput ->
            Cancellable<TcEnv * ModuleOrNamespaceType * bool>

exception NotUpperCaseConstructor of range: range

exception NotUpperCaseConstructorWithoutRQA of range: range
