// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

module internal FSharp.Compiler.CodeAnalysis.Declarations.DeclarationSyntax

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

val sourceOf: parse: FSharpParseFileResults -> ISourceText option

val warnOptionsOf: parse: FSharpParseFileResults -> FSharpDiagnosticOptions

val sameWarnOptions: a: FSharpDiagnosticOptions -> b: FSharpDiagnosticOptions -> bool

val lineDirectivesOf: parse: FSharpParseFileResults -> (int * (int * int)) list

val refuseUnlessCurrentDirectives: parse: FSharpParseFileResults -> unit

val fileEndOf: parse: FSharpParseFileResults -> pos

val splitsFragment: file: ParsedImplFileInput -> bool

val parse: ctx: ProjectContext -> fileName: string -> source: string -> FSharpParseFileResults

val countDeclarations: parse: FSharpParseFileResults -> int

val split: parse: FSharpParseFileResults -> ParsedDeclaration[]

val content: decl: ParsedDeclaration -> DeclarationContent

val fileDependencies: ctx: ProjectContext -> parses: FSharpParseFileResults[] -> int[][]
