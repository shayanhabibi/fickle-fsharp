// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

module internal FSharp.Compiler.CodeAnalysis.Declarations.DeclarationProjectCheck

open System.Collections.Generic
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.CheckDeclarations
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.CompilerDiagnostics
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.NameResolution
open FSharp.Compiler.ParseAndCheckInputs
open FSharp.Compiler.Syntax
open FSharp.Compiler.TypedTree

val allocatedBytesForCurrentThread: unit -> int64

val newLoggersWith: diagnosticsOptions: FSharpDiagnosticOptions -> CompilationDiagnosticLogger * RawDiagnostics

val newLoggers: state: CompilerState -> CompilationDiagnosticLogger * RawDiagnostics

val diagnosticsWith:
    state: CompilerState ->
    diagnosticsOptions: FSharpDiagnosticOptions ->
    fileName: string ->
    capturing: CompilationDiagnosticLogger ->
        FSharpDiagnostic[]

val diagnosticsOf: state: CompilerState -> fileName: string -> capturing: CompilationDiagnosticLogger -> FSharpDiagnostic[]

val projectDiagnostics: ctx: ProjectContext -> diagnostics: FSharpDiagnostic[] -> FSharpDiagnostic[]

val refiltered: diagnosticsOptions: FSharpDiagnosticOptions -> raw: PhasedDiagnostic[] -> CompilationDiagnosticLogger

val implFingerprint: rootSigOpt: ModuleOrNamespaceType option -> implFileSig: ModuleOrNamespaceType -> topAttrs: TopAttribs -> string

val leavingSignatureRanges: checks: ProjectChecks -> parse: FSharpParseFileResults -> rootSigOpt: ModuleOrNamespaceType option -> check: (unit -> 'T) -> 'T

val compiledNamesOf: state: CompilerState -> resolutions: TcResolutions -> implFileOpt: CheckedImplFile option -> unit

val newCheckerState:
    state: CompilerState ->
    tcState: TcState ->
    rootSigOpt: ModuleOrNamespaceType option ->
    file: ParsedImplFileInput ->
    sink: TcResultsSinkImpl ->
        TcFileState * TcEnv * ModuleOrNamespaceType ref

val stampsOf: mty: ModuleOrNamespaceType -> seq<Stamp>

val addDefinitions: definitions: Map<Stamp, DeclarationRef> -> declaration: DeclarationRef -> delta: ModuleOrNamespaceType -> Map<Stamp, DeclarationRef>

val copiedDefinitions:
    own: Map<Stamp, DeclarationRef> ->
    contents: ModuleOrNamespaceType ->
    copy: ModuleOrNamespaceType ->
    acc: Map<Stamp, DeclarationRef> ->
        Map<Stamp, DeclarationRef>

val implFileSignature:
    state: CompilerState ->
    fileName: string ->
    qualNameOfFile: QualifiedNameOfFile ->
    implFileSig: ModuleOrNamespaceType ->
    createsGeneratedProvidedTypes: bool ->
    moduleNamesDict: ModuleNamesDict ->
    definitions: Map<Stamp, DeclarationRef> ->
    fingerprint: Lazy<string> ->
        FileSignature

val failedFileSignature: fileName: string -> moduleNamesDict: ModuleNamesDict -> FileSignature

val createProject: options: FSharpProjectOptions -> Async<ProjectContext>

val createProjectWithReferences: options: FSharpProjectOptions -> references: IReadOnlyDictionary<string, ProjectAssembly> -> Async<ProjectContext>

val failingProjectAssembly: message: string -> ProjectAssembly

val projectAssembly: ctx: ProjectContext -> files: FileResult list -> signatures: FileSignature list -> ProjectAssembly

val checkSignatureFile: ctx: ProjectContext -> before: FileSignature list -> parse: FSharpParseFileResults -> FileSignature

val accessPathTexts: signature: FileSignature -> (string * string)[]

val beginFile: ctx: ProjectContext -> before: FileSignature list -> parse: FSharpParseFileResults -> FileStart * DeclarationEnvironment

val checkFile: ctx: ProjectContext -> before: FileSignature list -> parse: FSharpParseFileResults -> fingerprint: bool option -> FileResult
