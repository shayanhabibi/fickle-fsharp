// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.CodeAnalysis

open FSharp.Compiler.Symbols

/// Whole-project and single-file checker with parse, type-check, and file-level signature cutoff caching.
[<Sealed>]
type FSharpProjectChecker =

    /// Creates a checker for the given project options.
    static member Create: projectOptions: FSharpProjectOptions -> FSharpProjectChecker

    /// Parses and checks the whole project, retaining cached file results and signatures across checks.
    member ParseAndCheckProject:
        projectFileName: string *
        fileNames: string[] *
        sourceReader: (string -> int * Lazy<string>) *
        ?lastFile: string *
        ?subscriber: (FSharpImplementationFileContents -> unit) ->
            Async<FSharpCheckProjectResults>

    /// Parses and checks a single file in the project, returning parse, check, and partial project results.
    member ParseAndCheckFileInProject:
        projectFileName: string * fileNames: string[] * sourceReader: (string -> int * Lazy<string>) * fileName: string ->
            Async<FSharpParseFileResults * FSharpCheckFileResults * FSharpCheckProjectResults>
