import Wiz.Query
import Wiz.Actions
import Wiz.Elab.Tactic
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

/-- A registered extension: the syntax kind and the Wiz function. `termAware` is set for
the `[codeActionTerm k]`/`[hoverTerm k]` forms (`Syntax → ExtInfo → String`); the plain
forms take just the syntax node (`Syntax → String`). -/
structure Handler where
  kind : Name
  fn : Name
  termAware : Bool := false
  deriving Inhabited, Repr, BEq

/-- `attribute [codeAction k] f` registrations, latest first (`CommandState`), then the
term-aware ones. -/
def codeActionHandlers (s : CommandState R) : Array Handler :=
  (s.extCodeActions.toArray.map fun (k, f) => { kind := k, fn := f }) ++
  (s.extCodeActionTerms.toArray.map fun (k, f) => { kind := k, fn := f, termAware := true })

/-- `attribute [hover k] f` registrations, latest first, then the term-aware ones. -/
def hoverHandlers (s : CommandState R) : Array Handler :=
  (s.extHovers.toArray.map fun (k, f) => { kind := k, fn := f }) ++
  (s.extHoverTerms.toArray.map fun (k, f) => { kind := k, fn := f, termAware := true })

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

/-! ## The info tree at a node (11ag)

A term-aware extension gets an `ExtInfo` (lib/Prelude.wiz) besides the parsed node: the
info-tree entry at it, if any. The expected type of a checked term, an identifier's
inferred type, and the tactic goals are reflected as the prelude's `Expr` (with the
same layout tactics use), and the type and goals are also rendered as text. No entry is
`kind == ""`: the hook still runs and can fall back. -/

/-- The info-tree entry at a parsed node. Prefer an entry with exactly the node's range
(an identifier's entry for an identifier node, a term's otherwise), else the innermost
entry containing the node's start. -/
def entryAt (s : CommandState R) (stx : Syntax) : Option (Info R) :=
  let r := stx.info
  let isIdent := stx.isOfKind "term.ident"
  let prefer (i : Info R) : Bool :=
    match i with
    | .ident .. => isIdent
    | .term .. => !isIdent
    | .tactic .. | .inst .. => true
    | _ => false
  let exact (p : Info R → Bool) : Option (Info R) :=
    s.infos.findSome? fun i =>
      let q := i.info
      if q.start == r.start && q.stop == r.stop && q.stop > q.start && p i then some i else none
  match exact prefer with
  | some i => some i
  | none => match exact fun _ => true with
    | some i => some i
    | none => Query.innermost s r.start prefer (endIn := true)

/-- The info-tree entry's kind, for `ExtInfo.kind`. -/
def infoKind : Info R → String
  | .term .. => "term"
  | .ident .. => "ident"
  | .tactic .. => "tactic"
  | .inst .. => "instance"
  | .decl .. => "declaration"
  | .matchCases .. => "match"
  | .syntaxRef .. => "syntax"
  | .expansion .. => "expansion"
  | .importMod .. => "import"
  | .unknownIdent .. => "unknown-identifier"
  | .warning .. => "warning"
  | .trace .. => "trace"
  | .fix .. => "fix"

/-- A term as the prelude's `Expr` value (`depth` variables in scope). -/
def reflectTerm (t : Term R) (depth : Nat) : RVal :=
  (Wiz.Elab.reflect t depth).run #[] |>.1

/-- An `Option Expr` value. -/
def encodeTerm? (t? : Option (Term R)) (depth : Nat) : RVal :=
  match t? with
  | some t => .obj 1 #[reflectTerm t depth]
  | none => .obj 0 #[]

/-- An `ExtGoal` value: its hypotheses (outermost first), its target, and its text. -/
def encodeGoal (s : CommandState R) (g : GoalView R) : RVal :=
  let hyps := (g.hyps.toList.mapIdx fun k (n, ty, _) =>
      .obj 0 #[Elab.encodeString n, reflectTerm ty k]).foldr
    (fun h acc => .obj 1 #[h, acc]) (.obj 0 #[])
  .obj 0 #[hyps, reflectTerm g.target g.hyps.size, Elab.encodeString (g.show (some s.globals))]

/-- The `ExtInfo` value for a node: the entry at it, its expected/inferred type, and the
tactic goals at the node (after the innermost tactic, as the infoview shows them). -/
def extInfo (s : CommandState R) (stx : Syntax) : RVal :=
  let off := stx.info.start
  let atNode := (Query.goalsAt s off).map (·.2.2) |>.getD #[]
  let (kind, ty?, depth, goals, tyText) :
      String × Option (Term R) × Nat × Array (GoalView R) × String :=
    match entryAt s stx with
    | some (.term _ g _) =>
      ("term", some g.target, g.hyps.size, atNode,
       g.target.pretty g.names (some s.globals))
    | some (.ident _ _ _ names ty) =>
      let ty := names.foldl (fun t n => t.instantiateAt 0 (.const n [])) ty
      ("ident", some ty, names.length, atNode, ty.pretty names (some s.globals))
    | some (.tactic _ _ _ after) =>
      ("tactic", none, 0, after, "")
    | some (.inst _ names ty _) =>
      let ty := names.foldl (fun t n => t.instantiateAt 0 (.const n [])) ty
      ("instance", some ty, names.length, atNode, ty.pretty names (some s.globals))
    | some i => (infoKind i, none, 0, atNode, "")
    | none => ("", none, 0, atNode, "")
  let goalVals := goals.toList.foldr (fun g acc => .obj 1 #[encodeGoal s g, acc]) (.obj 0 #[])
  let goalsText := "\n\n".intercalate (goals.toList.map fun g => g.show (some s.globals))
  .obj 0 #[Elab.encodeString kind, encodeTerm? ty? depth, goalVals,
    Elab.encodeString tyText, Elab.encodeString goalsText]

/-! ## Running an extension

Each call has a **step budget** (`Extensions.fuel`): the same erased interpreter as
`#eval`, but through `NativeRun.applyWith`, where every application and primitive costs
fuel. A runaway extension ends in an ordinary ignored failure instead of hanging the
server. -/

/-- The erased code of an extension function (and what it reaches), for the interpreter. -/
def compile (s : CommandState R) (f : Name) : Except String Code :=
  (compileReachable s.globals s.builtins [f] (externImpls := false)).mapError
    fun e => s!"cannot compile the extension {f}: {e}"

/-- The step budget of one extension call (a request may run several registrations; the
host subtracts what each used). It is generous for a string-building function and small
enough that a loop ends in milliseconds. -/
def fuel : Nat := 1000000

/-- Run `f` applied to `args`, expecting a `String` (the one thing an extension may
return). Returns the string and the number of steps used. -/
def runString (code : Code) (f : Name) (args : List RVal) (fuel : Nat) :
    Except String (String × Nat) :=
  match NativeRun.applyWith code (run code [] (.global f)) args fuel with
  | .ok (v, rest) => match v.toString? with
    | some s => .ok (s, fuel - rest)
    | none => .error s!"{f} did not return a String"
  | .error e => .error e

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
