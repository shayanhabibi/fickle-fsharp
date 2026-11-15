// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

module internal FSharp.Compiler.CodeAnalysis.Declarations.DeclarationSymbolKeys

open System.Threading
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Text

val symbolKey: symbol: FSharpSymbol -> string option

val signatureLocation: ctx: ProjectContext -> signature: FileSignature -> key: string -> conformed: bool -> ct: CancellationToken -> range option

val signatureUses: ctx: ProjectContext -> signature: FileSignature -> (struct (range * bool * FSharpSymbol))[]

val definitionLocation: check: FSharpCheckFileResults -> key: string -> ct: CancellationToken -> range option
