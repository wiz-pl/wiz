import Lean.Data.Json
import Wiz.Elab.Command
import Wiz.Actions

/-!
# Diagnostics: one conversion for editors and tools

The elaborator reports a message as a `Msg`: a `SourceInfo` (character offsets), a
`Severity`, the text, and (for common mistakes) a stable `code`. Two consumers print
those messages:

* the language server (`Wiz/LSP.lean`), as LSP `Diagnostic`s with zero-based
  `line`/`character` positions;
* `wiz check --json`, as the versioned document of `docs/schema/check-json-v1.json`
  with zero-based character offsets and one-based `line`/`col`.

Both go through this module, so a position or a quick-fix payload cannot mean one thing
in an editor and another on the command line. The offsets are **character offsets**
(indices into `String.toList`, i.e. Unicode scalar values), like `SourceInfo` and the
rest of the frontend; they are neither UTF-8 bytes nor UTF-16 code units.
-/

namespace Wiz

open Lean (Json)

/-- An LSP position (`line`/`character`, both zero-based) at a character offset. -/
def positionJson (text : String) (off : Nat) : Json :=
  let (line, col) := lineCol text off
  Json.mkObj [("line", line), ("character", col)]

/-- An LSP `Range` for a source span. A zero-width span is one character wide, as an
editor's diagnostic range cannot be empty. -/
def sourceRangeJson (text : String) (info : SourceInfo) : Json :=
  Json.mkObj [("start", positionJson text info.start),
              ("end", positionJson text (max info.stop (info.start + 1)))]

/-- A `wiz check --json` span: the file, the character offsets, and the one-based
`line`/`col` of `start`. The end is the source's own: a parse error can be zero-width
(`end == start`). -/
def sourceSpanJson (file text : String) (info : SourceInfo) : Json :=
  let (line, col) := lineCol text info.start
  Json.mkObj [("file", Json.str file), ("start", info.start),
              ("end", (max info.stop info.start : Nat)),
              ("line", (line + 1 : Nat)), ("col", (col + 1 : Nat))]

/-- A span for a text edit: like `sourceSpanJson`, but an insertion is allowed to be
empty (`end == start`). -/
def editSpanJson (file text : String) (start stop : Nat) : Json :=
  sourceSpanJson file text { start, stop }

/-- The severity names of the JSON document. -/
def severityName : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .info => "info"

/-- The numeric LSP severity (`1` error, `2` warning, `3` information). -/
def lspSeverity : Severity → Nat
  | .error => 1
  | .warning => 2
  | .info => 3

/-- The `data` object of an LSP diagnostic (and of a `wiz check --json` diagnostic):
what a quick fix needs, as `Actions.messageData` computes it. Shared so that the two
forms never disagree. -/
def diagnosticDataJson (fields : List (String × List String)) : Json :=
  Json.mkObj (fields.map fun (k, vs) =>
    (k, if k == "name" then Json.str (vs.headD "") else Json.arr (vs.map Json.str).toArray))

end Wiz
