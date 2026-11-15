// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// What the files that depend on a file see of it: the types, values, members and attributes its signature declares,
/// without ranges or stamps, and with type parameters numbered by position. Equal fingerprints mean the dependents
/// would check the same against either signature. Anything it cannot describe exactly gives None, so the file
/// always counts as changed.
module internal FSharp.Compiler.SignatureFingerprint

open FSharp.Compiler.Syntax
open FSharp.Compiler.TypedTree
open FSharp.Compiler.CheckDeclarations

/// <summary>Formats an access path consistently with <c>sprintf "%A"</c>, without keeping short paths in a process-wide table.</summary>
val accessPathText: compPath: CompilationPath -> string

/// <summary>Computes a structural fingerprint for a module or namespace signature and top-level attributes, or <c>None</c> if not describable.</summary>
val compute: mty: ModuleOrNamespaceType -> topAttrs: TopAttribs -> string option

/// <summary>
/// What the code after a declaration sees of it: its contribution to the module or namespace it is in, and the
/// bodies of its inline values. Numbering starts again for each declaration, so a fingerprint depends neither on
/// other declarations nor on the order they were checked in. A member's implemented slots come from <c>slotsOf</c>:
/// closing the inference scope completes them.
/// </summary>
val computeDeclaration:
    contribution: ModuleOrNamespaceType ->
    inlineBodies: (Val * Expr) list ->
    slotsOf: (Val -> ValMemberInfo -> (SlotSig list * bool) option) ->
        string option
