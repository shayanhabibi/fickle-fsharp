// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

module internal FSharp.Compiler.CodeAnalysis.Declarations.DeclarationFinish

open FSharp.Compiler.CodeAnalysis

val answeringDeclarations:
    start: FileStart ->
    results: DeclarationResult[] ->
    parse: FSharpParseFileResults ->
    line: int ->
    column: int ->
        struct (int[] * int * bool)

val viewResults:
    start: FileStart ->
    results: DeclarationResult[] ->
    parse: FSharpParseFileResults ->
        FSharpCheckFileResults

val finishFile: start: FileStart -> results: DeclarationResult[] -> parse: FSharpParseFileResults -> FileResult
