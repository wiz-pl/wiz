import Wiz.Query
import Wiz.Actions
import Lean.Data.Json

/-!
# User-defined language-server extensions (11ae)

A file can teach the language server what to offer at the nodes of a syntax kind it
declares:

    syntax (name := double) "double" term:max : term
    def doubleAction (stx : Syntax) : String := …
    attribute [codeAction term.double] doubleAction

    def doubleHover (stx : Syntax) : String := …
    attribute [hover term.double] doubleHover

The registered function is a **pure Wiz function** `Syntax → String`, type-checked at the
attribute like a macro (`Elab/Command.lean`, `command.attrCodeAction`). For `hover` the
string is Markdown. For `codeAction` it is JSON — one object or an array of them:

    {"title": "Rewrite as addition", "text": "Nat.add x x", "kind": "refactor.rewrite"}

`title` is required; `text`, when present, replaces the node the server found (the
action's edit is exactly that node's range); `kind` defaults to `refactor.rewrite`.
Malformed JSON, or a function that does not return a string, is ignored: the server must
not fail because of an extension.

The host bridges the JSON: the Wiz side only builds a string, which keeps the signature
portable (the self-hosted toolchain can run the same functions; it does not yet parse the
attribute — see `wiz-notes/lsp-extensions.md`).

## Finding the node

The registered kind names a node of the *parsed* command under the cursor, not an entry
of the info tree: an extension should work in a file that does not elaborate (that is
where an action is most useful). `commandAt` walks the document with the state's parser
tables and returns the command whose range contains the offset; `find`/`findIn` pick the
innermost node of the kind there. `Syntax` is handed to the function encoded as the
runtime value macros get (`Elab.encodeSyntax`), so `Syntax.getArg`, `Syntax.reprint` and
friends work; the decoder is the same as for procedural macros.

## Running it

The function is erased and interpreted when the server first needs it in a document
(`compile`), then applied to the node (`runString`). The compiled code is cached on the
document (`LSP.Doc.extCode`) and dropped when the text changes, as the info tree is.
-/

namespace Wiz.Extensions

open Lean (Json)

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- A registered extension: the syntax kind and the Wiz function. -/
structure Handler where
  kind : Name
  fn : Name
  deriving Inhabited, Repr, BEq

/-- `attribute [codeAction k] f` registrations, latest first (`CommandState`). -/
def codeActionHandlers (s : CommandState R) : Array Handler :=
  s.extCodeActions.toArray.map fun (k, f) => { kind := k, fn := f }

/-- `attribute [hover k] f` registrations, latest first. -/
def hoverHandlers (s : CommandState R) : Array Handler :=
  s.extHovers.toArray.map fun (k, f) => { kind := k, fn := f }

/-! ## The parsed syntax at a position -/

/-- The command containing character offset `off`, parsed with the state's tables (the
ones the user's `syntax` commands made). A command that does not parse is skipped the
way the frontend recovers (to the next line at column 0), so an extension still works
below an incomplete command. -/
partial def commandAt (tables : ParserTables) (chars : Array Char) (pos off : Nat) : Option Syntax :=
  let pos := skipWs chars pos
  if pos ≥ chars.size then none else
  match parseCommand chars tables pos with
  | .ok (cmd, stop) =>
    if cmd.info.stop > cmd.info.start && cmd.info.start ≤ off && off ≤ cmd.info.stop then some cmd
    else if off < cmd.info.start || stop ≤ pos then none
    else commandAt tables chars stop off
  | .error _ =>
    let next := recoverPos chars pos
    if next ≤ pos then none else commandAt tables chars next off

/-- The range `[start, stop]` of an LSP request meets a node's range. -/
def overlap (r : SourceInfo) (start stop : Nat) : Bool :=
  r.stop > r.start && r.start ≤ stop && start ≤ r.stop

/-- The innermost node of kind `k` of `stx` whose range overlaps `[start, stop]`. -/
partial def findIn (k : Name) (start stop : Nat) : Syntax → Option Syntax
  | stx =>
    let pick (a b : Syntax) : Syntax := if b.info.stop - b.info.start < a.info.stop - a.info.start then b else a
    let inChild := stx.args.foldl (fun acc c =>
      match findIn k start stop c with
      | some n => some (match acc with | some m => pick m n | none => n)
      | none => acc) none
    match inChild with
    | some n => some n
    | none => if stx.isOfKind k && overlap stx.info start stop then some stx else none

/-- The innermost node of kind `k` of `stx` containing character offset `off`. -/
def find (k : Name) (off : Nat) (stx : Syntax) : Option Syntax :=
  findIn k off off stx

/-- The innermost node of kind `k` at `off` of a document, if any. -/
def nodeAt (s : CommandState R) (text : String) (off : Nat) (k : Name) : Option Syntax := do
  let cmd ← commandAt s.tables text.toList.toArray 0 off
  find k off cmd

/-- The innermost node of kind `k` overlapping `[start, stop]` of a document, if any. -/
def nodeIn (s : CommandState R) (text : String) (start stop : Nat) (k : Name) : Option Syntax := do
  let cmd ← commandAt s.tables text.toList.toArray 0 start
  findIn k start stop cmd

/-! ## Running an extension -/

/-- The erased code of an extension function (and what it reaches), for the interpreter. -/
def compile (s : CommandState R) (f : Name) : Except String Code :=
  (compileReachable s.globals s.builtins [f] (externImpls := false)).mapError
    fun e => s!"cannot compile the extension {f}: {e}"

/-- Run `f stx`, expecting a `String` (the one thing an extension may return). -/
def runString (code : Code) (f : Name) (stx : Syntax) : Except String String :=
  match (apply code (run code [] (.global f)) (Elab.encodeSyntax stx)).toString? with
  | some s => .ok s
  | none => .error s!"{f} did not return a String"

/-! ## Code actions from the extension's JSON -/

/-- One action an extension returned. -/
structure ExtAction where
  title : String
  kind : String := "refactor.rewrite"
  /-- the replacement for the node, if the action edits it -/
  text : Option String := none
  deriving Inhabited, Repr

/-- Read the JSON an extension returned: an object, or an array of objects. Anything
malformed, and any object without a nonempty `title`, is left out. -/
def parseActions (out : String) : Array ExtAction :=
  let one (j : Json) : Option ExtAction := do
    let title := match j.getObjVal? "title" with
      | .ok (.str s) => s
      | _ => ""
    if title.isEmpty then none
    let kind := match j.getObjVal? "kind" with
      | .ok (.str s) => if s.isEmpty then "refactor.rewrite" else s
      | _ => "refactor.rewrite"
    let text := match j.getObjVal? "text" with
      | .ok (.str s) => some s
      | _ => none
    pure { title, kind, text }
  match Json.parse out with
  | .ok (.arr xs) => (xs.filterMap one).extract 0 10
  | .ok j => (one j).toArray
  | .error _ => #[]

/-- An extension action as a code action whose edit replaces the node. -/
def ExtAction.toAction (a : ExtAction) (r : SourceInfo) : Actions.Action :=
  { title := a.title, kind := a.kind,
    edits := match a.text with
      | some t => #[{ start := r.start, stop := r.stop, text := t }]
      | none => #[] }

end Wiz.Extensions
