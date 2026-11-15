// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Moving what a declaration's check left by a number of lines, for a declaration whose text is unchanged but which
/// starts on another line (DeclarationChecker.Shift).
module internal FSharp.Compiler.CodeAnalysis.Declarations.DeclarationShift

open FSharp.Compiler
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.NameResolution
open FSharp.Compiler.TcGlobals
open FSharp.Compiler.Text
open FSharp.Compiler.TypedTree

/// Counts a check the finish ran for a shifted result that reported at a range of the file outside the declaration.
val CountFinishMiss: unit -> unit

/// How many such checks have run in the process. For tests.
val FinishMisses: unit -> int64

/// The resolution with any active-pattern case's tags and named-argument parameter's ident at their current ranges.
val currentItems: r: CapturedNameResolution -> CapturedNameResolution

/// Moves every range of one declaration's syntax by `delta` lines.
[<Sealed>]
type Shifter =

    /// Creates a shifter tied to a check's ShareKey (`owner`).
    new: fileIndex: int * oldRange: range * scopeEnd: pos * delta: int * owner: obj -> Shifter

    /// A shifter for what a shifted result's deferred checks report at the finish.
    static member Create: fileIndex: int * oldRange: range * scopeEnd: pos * delta: int -> Shifter

    member Parameters: int * range * pos * int

    /// Drops what the shift built up, once its result is made.
    member Release: unit -> unit

    /// Restores everything it moved in place, latest first.
    member Undo: unit -> unit

    /// The first reason the shift cannot be made, if any.
    member Refused: string option

    /// The range `delta` lines lower, keeping its columns, height and flags.
    member Move: m: range -> range

    /// A range of the declaration's own syntax: moved, or the shift refused when it is elsewhere in the file.
    member Own: m: range -> range

    /// The scope of an environment or an open the declaration's check notified.
    member Scope: m: range -> range

    /// An attribute of an item the declaration made.
    member Attrib: attrib: Attrib -> Attrib

    /// An entity this declaration made, with what it holds.
    member EntityWith: e: Entity * withContents: bool -> unit

    member ModuleType: mty: ModuleOrNamespaceType -> unit

    member Contents: contents: ModuleOrNamespaceContents -> ModuleOrNamespaceContents

    /// A sink holding what `sink` holds, at the moved ranges.
    member Sink: g: TcGlobals * sink: TcResultsSinkImpl -> TcResultsSinkImpl

    member Diagnostic: d: PhasedDiagnostic -> PhasedDiagnostic

    member Exn: e: exn -> exn

/// Passes each diagnostic on with its ranges moved.
[<Sealed>]
type ShiftingLogger =
    inherit DiagnosticsLogger

    new: next: DiagnosticsLogger * shift: (PhasedDiagnostic -> PhasedDiagnostic) -> ShiftingLogger
