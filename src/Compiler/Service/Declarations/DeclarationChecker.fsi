// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.CodeAnalysis.Declarations

open System.Collections.Generic
open System.Threading
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Text

[<AbstractClass; Sealed>]
type DeclarationChecker =

    /// <summary>
    /// A text key for a symbol, equal for a definition, its copies in later files' signatures and in another project's
    /// in-memory assembly, and the objects an older check holds: the defining assembly, the kind, the path and name, and
    /// for a member the types of its arguments, which tell overloads apart. None for a local.
    /// </summary>
    static member SymbolKey: symbol: FSharpSymbol -> string option

    /// The range in a signature file of what `key` names, read from this check of it.
    static member SignatureLocation: ctx: ProjectContext * signature: FileSignature * key: string * conformed: bool * ct: CancellationToken -> range option

    /// What a signature file's check resolved: each range, whether it defines, and the symbol.
    static member SignatureUses: ctx: ProjectContext * signature: FileSignature -> (struct (range * bool * FSharpSymbol))[]

    /// The location of the definition of what `key` names in a file's check results.
    static member DefinitionLocation: check: FSharpCheckFileResults * key: string * ct: CancellationToken -> range option

    static member CreateProject: options: FSharpProjectOptions -> Async<ProjectContext>

    /// A project context in which each `-r:` whose path is a key of `references` is that project's in-memory assembly.
    static member CreateProject: options: FSharpProjectOptions * references: IReadOnlyDictionary<string, ProjectAssembly> -> Async<ProjectContext>

    static member FailingProjectAssembly: message: string -> ProjectAssembly

    static member ProjectAssembly: ctx: ProjectContext * files: FileResult list * signatures: FileSignature list -> ProjectAssembly

    static member Parse: ctx: ProjectContext * fileName: string * source: string -> FSharpParseFileResults

    static member CountDeclarations: parse: FSharpParseFileResults -> int

    static member Split: parse: FSharpParseFileResults -> ParsedDeclaration[]

    static member Content: decl: ParsedDeclaration -> DeclarationContent

    static member CheckSignatureFile: ctx: ProjectContext * before: FileSignature list * parse: FSharpParseFileResults -> FileSignature

    static member AccessPathTexts: signature: FileSignature -> (string * string)[]

    static member BeginFile: ctx: ProjectContext * before: FileSignature list * parse: FSharpParseFileResults -> FileStart * DeclarationEnvironment

    static member FileDependencies: ctx: ProjectContext * parses: FSharpParseFileResults[] -> int[][]

    static member CheckFile: ctx: ProjectContext * before: FileSignature list * parse: FSharpParseFileResults * ?fingerprint: bool -> FileResult

    static member AfterUndoHook: (string -> unit) with get, set

    static member CheckDeclaration: start: FileStart * envBefore: DeclarationEnvironment * decl: ParsedDeclaration * ct: CancellationToken -> DeclarationResult

    static member WindowOpen: start: FileStart * results: DeclarationResult[] * ct: CancellationToken -> bool

    static member PrintsNow: start: FileStart * results: DeclarationResult[] -> string[]

    static member Shift: result: DeclarationResult * decl: ParsedDeclaration -> DeclarationResult voption

    static member ExtendEnv: envBefore: DeclarationEnvironment * result: DeclarationResult -> DeclarationEnvironment

    static member ExtendEnvAdHoc: envBefore: DeclarationEnvironment * result: DeclarationResult -> DeclarationEnvironment

    static member CheckDeclarationAdHoc: start: FileStart * envBefore: DeclarationEnvironment * decl: ParsedDeclaration * ct: CancellationToken -> DeclarationResult

    static member AnsweringDeclarations: start: FileStart * results: DeclarationResult[] * parse: FSharpParseFileResults * line: int * column: int -> struct (int[] * int * bool)

    static member ViewResults: start: FileStart * results: DeclarationResult[] * parse: FSharpParseFileResults -> FSharpCheckFileResults

    static member FinishFile: start: FileStart * results: DeclarationResult[] * parse: FSharpParseFileResults -> FileResult
