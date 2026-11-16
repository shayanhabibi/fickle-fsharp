// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

module internal FSharp.Compiler.CodeAnalysis.Declarations.DeclarationStep

open System.Collections.Generic
open System.Threading
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.CheckDeclarations
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.NameResolution
open FSharp.Compiler.Syntax
open FSharp.Compiler.TcGlobals
open FSharp.Compiler.TypedTree
open FSharp.Compiler.TypedTreeOps

val combinesIntoFile: decl: SynModuleDecl -> bool

val mergeDelta: acc: ModuleOrNamespaceType -> delta: ModuleOrNamespaceType -> combines: bool -> ModuleOrNamespaceType

val exitModulesInto:
    exits: TcResultsSinkImpl ->
    state: CompilerState ->
    start: FileStart ->
    envBefore: DeclarationEnvironment ->
    depth: int ->
        DeclarationEnvironment

val keepingModuleTypes: entities: Entity list -> replay: (unit -> 'T) -> 'T

val fingerprintOf:
    contribution: ModuleOrNamespaceType ->
    checkedDecl: CheckedDeclaration ->
    slots: IReadOnlyDictionary<Val, SlotSig list * bool> ->
        string

val finishedFingerprint: atCheck: string voption -> finished: string -> string

val applyDefaults:
    g: TcGlobals ->
    scratch: (unit -> TcFileState) ->
    defaults: ModuleOrNamespaceContents * Attribs ->
        env: TcEnv ->
            unit

val moduleValuesOf: mty: ModuleOrNamespaceType -> seq<Val>

val modulePathOf: v: Val -> string list

val typedUsesOf:
    definitions: Map<Stamp, DeclarationRef> ->
    self: DeclarationRef ->
    delta: ModuleOrNamespaceType ->
    contents: ModuleOrNamespaceContents list ->
    sink: TcResultsSinkImpl option ->
        DeclarationRef[] * (Stamp * DeclarationRef)[]

val mutable afterUndoHook: (string -> unit)

val checkDeclaration:
    start: FileStart ->
    envBefore: DeclarationEnvironment ->
    decl: ParsedDeclaration ->
    ct: CancellationToken ->
        DeclarationResult

val windowOpen: start: FileStart -> results: DeclarationResult[] -> ct: CancellationToken -> bool

val printsNow: start: FileStart -> results: DeclarationResult[] -> string[]

val shift: result: DeclarationResult -> decl: ParsedDeclaration -> DeclarationResult voption

val extendEnvLocked: envBefore: DeclarationEnvironment -> result: DeclarationResult -> DeclarationEnvironment

val extendEnv: envBefore: DeclarationEnvironment -> result: DeclarationResult -> DeclarationEnvironment

val extendEnvAdHoc: envBefore: DeclarationEnvironment -> result: DeclarationResult -> DeclarationEnvironment

val checkDeclarationAdHoc:
    start: FileStart ->
    envBefore: DeclarationEnvironment ->
    decl: ParsedDeclaration ->
    ct: CancellationToken ->
        DeclarationResult
