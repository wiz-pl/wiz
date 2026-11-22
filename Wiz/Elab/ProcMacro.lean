import Wiz.Compiler.Run
import Wiz.Elab.Macro

/-!
# Procedural macros

A procedural macro is a Wiz function `f : Macro`, from the prelude:

    def MacroM (A : Type) : Type := TacticM A     -- requests: `fresh`, `fail`
    def Macro : Type := Syntax → MacroM Syntax

registered for a node kind with `attribute [macro k] f`. To expand a node of kind `k`
the elaborator **runs `f` in the interpreter**: it encodes the node as a runtime
`Syntax` value, applies `f` to it, answers its requests (fresh macro scopes) until it
returns, and decodes the result. That needs the host and the prelude to agree on data
layouts:

    SyntaxF:  missing | atom (val : String) | ident (val : String)
            | node (kind : String) (args : SyntaxF .false) | nil | cons (head) (tail)
    String := String.mk (data : List Char),   Char := Char.mk (val : Nat)
    List:     nil | cons (head) (tail),        Tac: see `Elab/Tactic.lean`

and a constructor value with tag `t` and fields `f₁ … fₙ` is the flat object
`⟨t f₁ … fₙ⟩` (see `Erase.lean`).

**Hygiene.** A quotation in a Wiz term marks each identifier it introduces as `x✝`
(a scope still to be chosen). When a macro's output comes back, `x✝` becomes `x✝n`
for this expansion's scope `n`, exactly as `macro_rules` templates are scoped.
-/

namespace Wiz.Elab

/-- A constructor value: a flat object. -/
def mkCon (tag : Nat) (fields : List RVal) : RVal := .obj tag fields.toArray

def encodeString (s : String) : RVal :=
  mkCon 0 [s.toList.foldr (fun c t => mkCon 1 [mkCon 0 [.nat c.toNat], t]) (mkCon 0 [])]

/-- (11w) The range of syntax the user wrote, as two hidden trailing fields of its
constructor value (`start`, `stop`). Wiz code never reads them (its `SyntaxF` has no such
fields), so they survive exactly as long as a macro or tactic hands back the very value
it was given (`exact $t` passes the user's `t` through), and are gone from anything it
builds. `relocate` reads them back. -/
def rangeFields (i : SourceInfo) : List RVal :=
  if i.stop == 0 || i.synthetic then [] else [.nat i.start, .nat i.stop]

/-- A host syntax tree as a runtime `Syntax` value. -/
partial def encodeSyntax : Syntax → RVal
  | .missing => mkCon 0 []
  | .atom i v => mkCon 1 ([encodeString v] ++ rangeFields i)
  | .ident i n => mkCon 2 ([encodeString n] ++ rangeFields i)
  | .node i k args =>
    mkCon 3 ([encodeString k, args.foldr (fun a t => mkCon 5 [encodeSyntax a, t]) (mkCon 4 [])] ++ rangeFields i)

/-- The `i`th field of a constructor value. -/
def _root_.Wiz.RVal.conField (v : RVal) (i : Nat) : RVal := v.field i

/-- **Exercise 6.3.** Decode a runtime `Syntax` value (see the layouts in the module
docstring; `RVal.tag?`, `RVal.conField` and `RVal.toString?` help). Every node gets
the source position `info` of the macro call, so errors in the expansion point there. -/
partial def decodeSyntax (info : SourceInfo) (v : RVal) : Option Syntax :=
  --<sol
  match v.tag? with
  | some 0 => some .missing
  | some 1 => return .atom info (← (v.conField 0).toString?)
  | some 2 => return .ident info (← (v.conField 0).toString?)
  | some 3 => return .node info (← (v.conField 0).toString?) (← list (v.conField 1) #[])
  | _ => none
where
  list (l : RVal) (acc : Array Syntax) : Option (Array Syntax) :=
    match l.tag? with
    | some 4 => some acc
    | some 5 => do list (l.conField 1) (acc.push (← decodeSyntax info (l.conField 0)))
    | _ => none
  --|ex
  --| sorry
  --sol>

/-- (11w) Give a decoded syntax tree the ranges its value carries (`rangeFields`): the
user's syntax that a macro or tactic passed through gets its own ranges back, and
everything else gets `fallback` (the call's range, synthetic). `s` is `decodeSyntax`'s
result for `v`, so the two have the same shape. -/
partial def relocate (fallback : SourceInfo) (v : RVal) (s : Syntax) : Syntax :=
  let info : SourceInfo := match v with
    | .obj t fs =>
      let k := if t == 3 then 2 else 1
      match (fs[k]? : Option RVal), (fs[k + 1]? : Option RVal) with
      | some (.nat a), some (.nat b) => { start := a, stop := b }
      | _, _ => fallback
    | _ => fallback
  match s with
  | .atom _ x => .atom info x
  | .ident _ n => .ident info n
  | .node _ k as => .node info k (go (v.conField 1) as.toList).toArray
  | s => s
where
  go (l : RVal) : List Syntax → List Syntax
    | [] => []
    | a :: as => relocate fallback (l.conField 0) a :: go (l.conField 1) as

/-- Decode a macro's or tactic's syntax, with the ranges of what it passed through. -/
def decodeLocated (info : SourceInfo) (v : RVal) : Option Syntax :=
  let fallback := { info with synthetic := true }
  (decodeSyntax fallback v).map (relocate fallback v)

/-- Give the identifiers a quotation introduced (`x✝`) the scope `scope`. -/
partial def scopeQuoted (scope : Nat) : Syntax → Syntax
  | .ident i n => if n.endsWith "✝" then .ident i s!"{n}{scope}" else .ident i n
  | .node i k as => .node i k (as.map (scopeQuoted scope))
  | s => s

/-- What a macro may ask about the environment (HD8): the view of an inductive type
(an `IndView` value) and the type of a declaration (a `Syntax` value), if they exist.
The command elaborator supplies them (`Elab/Reflect.lean`). -/
structure MacroEnv where
  inductive? : String → Option RVal := fun _ => none
  declType? : String → Option RVal := fun _ => none

/-- Answer a macro's requests until it returns. `v` is a `Tac` value; the result is the
syntax it returns (scoped with `scope`) and the next free scope, or an error; with it
come the messages the macro `trace`d, in order (also when it fails). A macro may ask for
fresh scopes (`fresh`), fail (`fail`), `trace`, and read the environment
(`getInductive`, `getType`). -/
partial def runMacroTac (code : Code) (env : MacroEnv) (what : String) (info : SourceInfo)
    (scope : Nat) (v : RVal) (next : Nat) (traces : Array String := #[]) :
    Array String × Except String (Syntax × Nat) :=
  let str (r : RVal) := (r.toString?).getD ""
  match v.tag? with
  | some 1 => -- result
    -- (11q, 11w) the macro's output: synthetic at the call's range, except what it passed through
    match decodeLocated info (v.conField 0) with
    | some out => (traces, pure (scopeQuoted scope out, next))
    | none => (traces, throw s!"{what} returned a malformed syntax tree")
  | some 2 => (traces, throw (((v.conField 0).toString?).getD "macro failed")) -- fail
  | some 3 => runMacroTac code env what info scope (v.conField 1) next (traces.push (str (v.conField 0))) -- trace
  | some 4 => runMacroTac code env what info scope (apply code (v.conField 0) (.nat next)) (next + 1) traces -- fresh
  | some 21 => -- getInductive
    let ans := (env.inductive? (str (v.conField 0))).map (mkCon 1 [·]) |>.getD (mkCon 0 [])
    runMacroTac code env what info scope (apply code (v.conField 1) ans) next traces
  | some 22 => -- getType
    let ans := (env.declType? (str (v.conField 0))).map (mkCon 1 [·]) |>.getD (mkCon 0 [])
    runMacroTac code env what info scope (apply code (v.conField 1) ans) next traces
  | some t => (traces, throw s!"{what} made a request ({t}) that only tactics can make")
  | none => match v with
    | .stuck m => (traces, throw s!"{what}: {m}")
    | _ => (traces, throw s!"{what} returned a malformed result")

/-- Run the macro `f` on `stx`: its traces, and the expansion and the next free scope.

`f stx : MacroM Syntax`, and `Macro.run` turns it into a `Tac` request chain ending in
`result stx'` (see `Elab/Tactic.lean`). -/
def runProcMacro (code : Code) (f : Name) (stx : Syntax) (scope : Nat) (env : MacroEnv := {}) :
    Array String × Except String (Syntax × Nat) :=
  let m := apply code (run code [] (.global f)) (encodeSyntax stx)
  runMacroTac code env s!"macro {f}" stx.info scope (apply code (run code [] (.global "Macro.run")) m) (scope + 1)

/-- Run the command macro `f : CommandMacro` on `stx`: the commands it expands to. -/
def runCommandMacro (code : Code) (f : Name) (stx : Syntax) (scope : Nat) (env : MacroEnv := {}) :
    Array String × Except String (Array Syntax × Nat) :=
  let m := apply code (run code [] (.global f)) (encodeSyntax stx)
  let (tr, r) := runMacroTac code env s!"macro {f}" stx.info scope
    (apply code (run code [] (.global "CommandMacro.run")) m) (scope + 1)
  (tr, r.map fun (out, next) => (out.args, next))

/-- Run the deriver `f : Deriver` for the type `T`: the commands it produces. -/
def runDeriver (code : Code) (f : Name) (T : Name) (info : SourceInfo) (scope : Nat) (env : MacroEnv := {}) :
    Array String × Except String (Array Syntax × Nat) :=
  let m := apply code (run code [] (.global f)) (encodeString T)
  let (tr, r) := runMacroTac code env s!"deriver {f}" info scope
    (apply code (run code [] (.global "CommandMacro.run")) m) (scope + 1)
  (tr, r.map fun (out, next) => (out.args, next))

/-! ## Located output of command macros

Runtime `Syntax` has no positions, so a command macro names a node of its input by its
**path**: the child indices from the macro's input node down to it. Its output may
contain three pseudo-commands that the command elaborator interprets (prelude:
`Syntax.errorAt`, `Syntax.infoAt`, `Syntax.sourceAt`):

    macro.error  [path, msg]    an error at the input node at `path`
    macro.info   [path, msg]    an info message there
    macro.source [path, text]   Wiz source: parsed as commands, positioned at that node

A path is a `null` node of atoms, each a decimal child index. -/

/-- The position of the node of `stx` at `path`: the deepest node on the way that has a
position (optional and empty nodes have none). -/
def pathInfo (stx : Syntax) (path : Syntax) : SourceInfo := Id.run do
  let mut cur := stx
  let mut info := stx.info
  for a in path.args do
    let i := match a with
      | .atom _ v => v.toNat?.getD 0
      | _ => 0
    cur := cur.getArg i
    if cur.info.stop > cur.info.start then info := cur.info
  info

/-- Give every node of `stx` the position `info`. -/
partial def setInfoAll (info : SourceInfo) : Syntax → Syntax
  | .missing => .missing
  | .atom _ v => .atom info v
  | .ident _ n => .ident info n
  | .node _ k as => .node info k (as.map (setInfoAll info))

/-! ### Positions inside generated source

A command macro can mark which parts of its generated source come from which node of its
input: the text between U+E000 *path* U+E001 and the matching U+E002 (marks nest; *path*
is decimal child indices separated by `.`) comes from the input node at *path*. Feral
marks every expression's value, the names of functions, parameters and `let`s, and the
function a call names (lib/Feral.wiz, `Fe.Out.at`). -/

/-- A marked part of generated source: its range in the text without marks, and the
path of the input node it comes from (a `null` node of decimal atoms, as `pathNode`). -/
structure MarkSpan where
  start : Nat
  stop : Nat
  path : Syntax
  deriving Inhabited

/-- The generated text without its marks, and the marked spans. -/
def stripMarks (text : String) : String × Array MarkSpan := Id.run do
  let mut out : Array Char := #[]
  let mut spans : Array MarkSpan := #[]
  let mut open_ : List (Nat × Syntax) := []
  let mut inPath := false
  let mut path : String := ""
  for c in text.toList do
    if inPath then
      if c == '' then
        inPath := false
        let atoms := (path.splitOn ".").filter (· ≠ "") |>.map (Syntax.atom {} ·)
        open_ := (out.size, Syntax.mkNull atoms.toArray) :: open_
      else path := path.push c
    else if c == '' then
      inPath := true
      path := ""
    else if c == '' then
      match open_ with
      | (a, p) :: rest =>
        spans := spans.push { start := a, stop := out.size, path := p }
        open_ := rest
      | [] => pure ()
    else out := out.push c
  (String.mk out.toList, spans)

/-- The innermost span containing `[a, b)`: the shortest; among equal ones, the one
closed first (the innermost mark). -/
def innermostSpan (spans : Array MarkSpan) (a b : Nat) : Option MarkSpan :=
  spans.foldl (fun acc sp =>
    if sp.start ≤ a && b ≤ sp.stop then
      match acc with
      | some q => if sp.stop - sp.start < q.stop - q.start then some sp else acc
      | none => some sp
    else acc) none

/-- Position syntax parsed from a macro's generated source (ranges in the text without
marks) in the user's file. Syntax whose range is exactly a marked span gets the range of
the input node the span comes from, so that its type shows there and errors about it are
reported there; syntax strictly inside a span gets that range too, but synthetic (nothing
is recorded for hovers: the span's own syntax is the precise one); the rest is the
macro's own (synthetic, at `item`), except the command itself, which is at `item`.
Without spans, every node is at `item` (`setInfoAll`). -/
partial def locateMarked (input : Syntax) (item : SourceInfo) (spans : Array MarkSpan) (stx : Syntax) : Syntax :=
  if spans.isEmpty then setInfoAll item stx else
  match stx with
  | .node _ k as => .node item k (as.map go)
  | s => go s
where
  infoFor (i : SourceInfo) : SourceInfo :=
    if i.stop == 0 then { item with synthetic := true } else
    match innermostSpan spans i.start i.stop with
    | some sp =>
      let u := pathInfo input sp.path
      if sp.start == i.start && sp.stop == i.stop then u else { u with synthetic := true }
    | none => { item with synthetic := true }
  go : Syntax → Syntax
    | .missing => .missing
    | .atom i v => .atom (infoFor i) v
    | .ident i n => .ident (infoFor i) n
    | .node i k as => .node (infoFor i) k (as.map go)

def atomText : Syntax → String
  | .atom _ v => v
  | _ => ""

end Wiz.Elab
