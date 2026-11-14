import Wiz
import Tests.Harness

/-!
# Kernel lint: every traversal handles every constructor, and every child of it

Two soundness bugs had the same shape: a traversal with a default case that silently
skipped a constructor (`Term.mapChildrenM` had no case for `natOp`: audit S1, a closed
proof of `False`). This group makes that a test failure. See `wiz-notes/kernel-lint.md`.

How it works.

* **The constructor lists are read from the source** (`Wiz/Core/Term.lean`, `Value.lean`,
  `Level.lean`, `selfhost/Kernel.wiz`): `parseInductive`. Nothing here lists them by hand.
* **Each constructor has a witness builder** in a table below (`termTable`, `valTable`, …):
  a function from "the children" to a value of that constructor. The tables are checked
  against the source: a constructor without a row, a row whose number of children differs
  from the fields in the source, or a field of a type the lint does not know, fails. So a
  new constructor, or a new field, fails the lint until its row is written.
* **The properties** put a *mark* (a variable, a level parameter) in one child at a time and
  require each traversal to find, rename or instantiate it. That catches a skipped child of
  a handled constructor, not only a missing case.
* `Kernel.wiz` is checked statically: its traversals are parsed, and each must have an arm
  for every constructor that has children, with every child used on the right-hand side
  (`wizFns`). The exceptions are listed with their reasons.
* The catch-all arms (`| _ =>`) of the Lean kernel's traversals are counted and pinned
  (`pinned`): a new one fails until it is reviewed (and the note's table updated).

**Adding a constructor** (`Term`, `Val`, `Head`, `Elim`, `Level`, or `Kernel.wiz`'s): add
its row to the table here; the failures that remain name the traversals that skip it.
-/

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Wiz

namespace Tests.Lint

abbrev R := ZeroOneMany

/-! ## Reading constructor lists from the source -/

structure Ctor where
  name : String
  /-- field name and type, as written; a binder group `(a b : T)` gives two fields -/
  fields : List (String × String)
  deriving Repr, Inhabited

def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!'

/-- Does `needle` occur in `hay`? -/
def hasSub (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The top-level pieces of `s` between separators `sep` (outside parentheses). -/
def splitTop (s : String) (sep : Char → Bool) : List String := Id.run do
  let mut depth : Nat := 0
  let mut cur : List Char := []
  let mut out : List String := []
  for c in s.toList do
    if c == '(' || c == '[' then depth := depth + 1
    if c == ')' || c == ']' then depth := depth - 1
    if depth == 0 && sep c then
      out := String.ofList cur.reverse :: out
      cur := []
    else cur := c :: cur
  out := String.ofList cur.reverse :: out
  return out.reverse.map trim |>.filter (· != "")

/-- `(a b : T) (c : U)` as `[(a, T), (b, T), (c, U)]`. -/
def parseFields (s : String) : Except String (List (String × String)) := do
  let s := (s.splitOn " --")[0]!
  let mut out := []
  for g in splitTop s Char.isWhitespace do
    unless g.startsWith "(" && g.endsWith ")" do throw s!"not a binder group: {g}"
    let inner := String.ofList (g.toList.drop 1).dropLast
    match inner.splitOn " : " with
    | names :: ty :: rest =>
      let ty := trim (" : ".intercalate (ty :: rest))
      for n in splitTop names Char.isWhitespace do out := out ++ [(n, ty)]
    | _ => throw s!"not a binder group: {g}"
  return out

/-- The constructors of `inductive name` in `src` (Lean or Wiz syntax: one `| ctor fields`
per constructor), in order. -/
def parseInductive (src name : String) : Except String (List Ctor) := do
  let header (l : String) : Bool :=
    let l := trim l
    let p := "inductive " ++ name
    l.startsWith p && !((l.toList.drop p.length).head?.any isIdChar)
  let lines := src.splitOn "\n"
  let rest := (lines.dropWhile (!header ·)).drop 1
  if rest.isEmpty then throw s!"no `inductive {name}` in the source"
  let stops := ["deriving", "inductive ", "end", "structure ", "def ", "abbrev ", "instance ",
    "mutual", "partial ", "namespace ", "/-!", "private ", "@["]
  let mut inDoc := false
  let mut acc : List (String × String) := []   -- name, text of the fields
  for l in rest do
    let t := trim l
    if inDoc then
      if hasSub t "-/" then inDoc := false
      continue
    if t.startsWith "/-" && !t.startsWith "/-!" then
      unless hasSub t "-/" do inDoc := true
      continue
    if t == "" || t.startsWith "--" then continue
    if t.startsWith "| " then
      let body := trim (t.drop 2).toString
      let n := String.ofList (body.toList.takeWhile isIdChar)
      acc := (n, (body.drop n.length).toString) :: acc
    else if stops.any (t.startsWith ·) then break
    else match acc with
      | (n, f) :: more => acc := (n, f ++ " " ++ t) :: more
      | [] => throw s!"inductive {name}: unexpected line: {t}"
  if acc.isEmpty then throw s!"inductive {name}: no constructors found"
  acc.reverse.mapM fun (n, f) => do
    match parseFields f with
    | .ok fs => pure { name := n, fields := fs }
    | .error e => throw s!"inductive {name}, constructor {n}: {e}"

def readCtors (file name : String) : IO (List Ctor) := do
  let src ← IO.FS.readFile file
  match parseInductive src name with
  | .ok cs => pure cs
  | .error e => throw (IO.userError s!"{file}: {e}")

/-- Collect failures, and report them together. -/
abbrev Failures := StateT (Array String) IO

def fail (msg : String) : Failures Unit := modify (·.push msg)
def expect (cond : Bool) (msg : String) : Failures Unit := unless cond do fail msg

def report (what : String) (x : Failures Unit) : IO Unit := do
  let ((), fs) ← x.run #[]
  unless fs.isEmpty do
    throw (IO.userError (s!"{what}: {fs.size} failure(s)\n  " ++ "\n  ".intercalate fs.toList))

/-- Compare a table of rows with the constructors in the source: every constructor has
exactly one row, in the same order, and the row's child counts are those of the fields.
`classify` gives the counts of a field type (`none`: a type the lint does not know). -/
def checkTable (what : String) (ctors : List Ctor) (rows : List (String × List Nat))
    (classify : String → Option (List Nat)) (kinds : List String) : Failures Unit := do
  for c in ctors do
    match rows.filter (·.1 == c.name) with
    | [] => fail s!"{what}.{c.name}: the constructor has no row in the lint's table (Tests/Lint.lean): add one, then fix the traversals the lint names"
    | [(_, counts)] =>
      let mut want := kinds.map fun _ => 0
      for (f, ty) in c.fields do
        match classify ty with
        | some ns => want := (want.zip ns).map fun (a, b) => a + b
        | none => fail s!"{what}.{c.name}: field `{f} : {ty}` has a type the lint does not know (Tests/Lint.lean, the `classify` function): say what its children are"
      unless want == counts do
        fail s!"{what}.{c.name}: the source has {want} children ({kinds}), the lint's row has {counts}: a field was added or removed; update the row"
    | _ => fail s!"{what}.{c.name}: more than one row in the lint's table"
  for (n, _) in rows do
    unless ctors.any (·.name == n) do fail s!"{what}.{n}: a row in the lint's table, but no such constructor in the source"
  if rows.length == ctors.length && rows.all (fun r => ctors.any (·.name == r.1))
      && rows.map (·.1) != ctors.map (·.name) then
    fail s!"{what}: the table's rows are not in the source's order"

/-! ## `Term` -/

/-- A witness builder for one constructor of `Term`: `depths` are the binder depths of its
term children in field order (a list or array field counts as two children, a `mu`/`nu`
hint as two), `levels` the number of its level children (a list: two; an option: one). -/
structure TermRow where
  name : String
  depths : List Nat
  levels : Nat
  build : (Nat → Term R) → (Nat → Level) → Term R

def termClassify : String → Option (List Nat)
  | "Term R" => some [1, 0]
  | "List (Term R)" | "Array (Term R)" => some [2, 0]
  | "Level" | "Option Level" => some [0, 1]
  | "List Level" | "BinderSorts" => some [0, 2]
  | "Option (Name × List Level × List (Term R))" => some [2, 2]
  | "Name" | "Nat" | "BinderInfo" | "R" | "List Name" => some [0, 0]
  | _ => none

/-- One row per constructor of `Term`, in the order of `Wiz/Core/Term.lean`. -/
def termTable : List TermRow := [
  ⟨"var", [], 0, fun _ _ => .var 0⟩,
  ⟨"const", [], 2, fun _ l => .const "c" [l 0, l 1]⟩,
  ⟨"sort", [], 1, fun _ l => .sort (l 0)⟩,
  ⟨"pi", [0, 0, 1], 2, fun c l => .pi "x" .default (c 0) (c 1) (c 2) ⟨l 0, l 1⟩⟩,
  ⟨"lam", [1], 0, fun c _ => .lam "x" (c 0)⟩,
  ⟨"app", [0, 0], 0, fun c _ => .app (c 0) (c 1)⟩,
  ⟨"letE", [0, 0, 0, 1], 0, fun c _ => .letE "x" (c 0) (c 1) (c 2) (c 3)⟩,
  ⟨"ann", [0, 0], 0, fun c _ => .ann (c 0) (c 1)⟩,
  ⟨"mvar", [], 0, fun _ _ => .mvar 0⟩,
  ⟨"sigma", [0, 0, 1], 2, fun c l => .sigma "x" (c 0) (c 1) (c 2) ⟨l 0, l 1⟩⟩,
  ⟨"pair", [0, 0], 0, fun c _ => .pair (c 0) (c 1)⟩,
  ⟨"fst", [0], 0, fun c _ => .fst (c 0)⟩,
  ⟨"snd", [0], 0, fun c _ => .snd (c 0)⟩,
  ⟨"split", [0, 0, 1, 2], 0, fun c _ => .split (c 0) (c 1) "z" (c 2) "x" "y" (c 3)⟩,
  ⟨"unit", [], 1, fun _ l => .unit (l 0)⟩,
  ⟨"tt", [], 0, fun _ _ => .tt⟩,
  ⟨"empty", [], 1, fun _ l => .empty (l 0)⟩,
  ⟨"absurd", [0, 0], 0, fun c _ => .absurd (c 0) (c 1)⟩,
  ⟨"letUnit", [0, 0], 0, fun c _ => .letUnit (c 0) (c 1)⟩,
  ⟨"eq", [0, 0, 0], 0, fun c _ => .eq (c 0) (c 1) (c 2)⟩,
  ⟨"eqTy", [0, 0], 0, fun c _ => .eqTy (c 0) (c 1)⟩,
  ⟨"refl", [0, 0], 0, fun c _ => .refl (c 0) (c 1)⟩,
  ⟨"reflTy", [0], 0, fun c _ => .reflTy (c 0)⟩,
  ⟨"cast", [0, 0, 0, 0], 0, fun c _ => .cast (c 0) (c 1) (c 2) (c 3)⟩,
  ⟨"transp", [0, 0, 0, 0, 0, 0], 0, fun c _ => .transp (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)⟩,
  ⟨"qty", [], 0, fun _ _ => .qty⟩,
  ⟨"qlit", [], 0, fun _ _ => .qlit .one⟩,
  ⟨"enum", [], 0, fun _ _ => .enum ["a", "b"]⟩,
  ⟨"tag", [], 0, fun _ _ => .tag ["a", "b"] 1⟩,
  ⟨"ecase", [1, 0, 0, 0], 0, fun c _ => .ecase "z" (c 0) (c 1) [c 2, c 3]⟩,
  ⟨"desc", [0], 1, fun c l => .desc (l 0) (c 0)⟩,
  ⟨"dret", [0], 0, fun c _ => .dret (c 0)⟩,
  ⟨"darg", [0, 0, 0], 0, fun c _ => .darg (c 0) (c 1) (c 2)⟩,
  ⟨"drec", [0, 0, 0], 0, fun c _ => .drec (c 0) (c 1) (c 2)⟩,
  ⟨"dhrec", [0, 0, 0, 0], 0, fun c _ => .dhrec (c 0) (c 1) (c 2) (c 3)⟩,
  ⟨"delim", [0, 0, 0, 0, 0, 0], 1, fun c l => .delim (l 0) (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)⟩,
  ⟨"mu", [0, 0, 0, 0, 0, 0], 3, fun c l => .mu (l 0) (c 0) (c 1) (c 2) (c 3) (some ("T", [l 1, l 2], [c 4, c 5]))⟩,
  ⟨"con", [0], 0, fun c _ => .con (c 0)⟩,
  ⟨"ind", [0, 0, 0, 0, 0, 0], 2, fun c l => .ind (l 0) (c 0) (c 1) (l 1) (c 2) (c 3) (c 4) (c 5)⟩,
  ⟨"nu", [0, 0, 0, 0, 0, 0], 3, fun c l => .nu (l 0) (c 0) (c 1) (c 2) (c 3) (some ("T", [l 1, l 2], [c 4, c 5]))⟩,
  ⟨"out", [0], 0, fun c _ => .out (c 0)⟩,
  ⟨"size", [], 0, fun _ _ => .size⟩,
  ⟨"szInf", [], 0, fun _ _ => .szInf⟩,
  ⟨"szSuc", [0], 0, fun c _ => .szSuc (c 0)⟩,
  ⟨"sizeLt", [0], 0, fun c _ => .sizeLt (c 0)⟩,
  ⟨"sfix", [0, 0, 0, 0, 0, 0, 0], 2, fun c l => .sfix (l 0) (c 0) (c 1) (l 1) (c 2) (c 3) (c 4) (c 5) (c 6)⟩,
  ⟨"scase", [0, 0, 0, 0, 0, 0, 0, 0], 2, fun c l => .scase (l 0) (c 0) (c 1) (c 2) (l 1) (c 3) (c 4) (c 5) (c 6) (c 7)⟩,
  ⟨"cocon", [0], 0, fun c _ => .cocon (c 0)⟩,
  ⟨"scofix", [0, 0, 0, 0, 0, 0, 0], 1, fun c l => .scofix (l 0) (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)⟩,
  ⟨"coit", [0, 0, 0, 0, 0, 0], 1, fun c l => .coit (l 0) (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)⟩,
  ⟨"natLit", [], 0, fun _ _ => .natLit 3⟩,
  ⟨"natOp", [0, 0], 0, fun c _ => .natOp "nat.add" #[c 0, c 1]⟩,
  ⟨"ulift", [0], 2, fun c l => .ulift (l 0) (l 1) (c 0)⟩,
  ⟨"up", [0], 0, fun c _ => .up (c 0)⟩,
  ⟨"down", [0], 0, fun c _ => .down (c 0)⟩,
  ⟨"prf", [0], 1, fun c l => .prf (l 0) (c 0)⟩
]

/-- The name of a term's constructor, from its derived `Repr` (`Wiz.Term.pi …`). -/
def termCtorName (t : Term R) : String :=
  let s := toString (repr t)
  let s := (s.splitOn "Wiz.Term.").getD 1 ""
  String.ofList (s.toList.takeWhile isIdChar)

/-- A closed leaf for the children that are not marked. -/
def plainT : Term R := .qty

/-- The witness of `row` with `mark` as its `j`-th term child. -/
def TermRow.withChild (row : TermRow) (j : Nat) (mark : Term R) (plain : Term R := plainT) : Term R :=
  row.build (fun i => if i == j then mark else plain) (fun _ => .zero)

def TermRow.withLevel (row : TermRow) (j : Nat) (mark : Level) : Term R :=
  row.build (fun _ => plainT) (fun i => if i == j then mark else .zero)

/-- The free variables of `t` under `depth` binders, as indices into the enclosing
environment (with repeats). (The kernel's copy of this went with its syntactic
regularity, conv-regularity §5; the lint keeps its own.) -/
partial def freeVarsAt (depth : Nat) (t : Term R) : StateM (Array Nat) Unit :=
  match t with
  | .var i => if i ≥ depth then modify (·.push (i - depth)) else pure ()
  | t => t.forChildren (fun _ => pure ()) (fun d c => freeVarsAt (depth + d) c)

def freeVars (t : Term R) : List Nat := ((freeVarsAt 0 t).run #[]).2.toList

/-- The index of the marked variable, as seen from outside the witness. -/
def M : Nat := 40

/-- The syntactic traversals, as a record, so that the lint can be run against a broken
one (`selfTest`). -/
structure TermOps where
  children : Term R → List (Nat × Term R)
  levels : Term R → List Level
  freeVars : Term R → List Nat
  hasVar : Nat → Term R → Bool
  lift : Nat → Nat → Term R → Term R
  instantiateAt : Term R → Nat → Term R → Term R
  strengthen? : Nat → Term R → Option (Term R)
  abstract : Term R → Term R → Term R
  instLevels : List Name → List Level → Term R → Term R
  levelParamsUsed : Term R → List Name

def kernelOps : TermOps where
  children t := ((t.forChildren (m := StateM (List (Nat × Term R))) (fun _ => pure ())
    (fun k c => modify (· ++ [(k, c)]))).run []).2
  levels t := ((t.forChildren (m := StateM (List Level)) (fun l => modify (· ++ [l]))
    (fun _ _ => pure ())).run []).2
  freeVars := freeVars
  hasVar := Term.hasVar
  lift k cut t := t.lift k cut
  instantiateAt t k s := t.instantiateAt k s
  strengthen? k t := t.strengthen? k
  abstract t target := t.abstract target
  instLevels := Term.instLevels
  levelParamsUsed := Term.levelParamsUsed

/-- Every syntactic traversal finds each child of each constructor, at its binder depth. -/
def checkTermOps (ops : TermOps) (rows : List TermRow) : Failures Unit := do
  for row in rows do
    let at' (what : String) (j : Nat) := s!"Term.{row.name}, child {j}: {what}"
    -- the generic traversal reports the children in field order, with their depths
    let w := row.build (fun i => .var (100 + i)) (fun i => .param s!"u{i}")
    let cs := ops.children w
    unless cs == (List.range row.depths.length).map (fun i => (row.depths[i]!, .var (100 + i))) do
      fail s!"Term.{row.name}: mapChildrenM/forChildren visit the children {cs.map fun (k, c) => (k, toString (repr c))}, expected {row.depths.length} of them at the depths {row.depths}"
    unless ops.levels w == (List.range row.levels).map (fun i => .param s!"u{i}") do
      fail s!"Term.{row.name}: mapChildrenM/forChildren visit the levels {ops.levels w}, expected {row.levels} of them"
    for j in [0:row.depths.length] do
      let d := row.depths[j]!
      -- the mark is the variable `M - d` of the enclosing context
      let w := row.withChild j (.var M)
      let x := M - d
      expect (ops.freeVars w == [x]) (at' s!"freeVarsAt gives {ops.freeVars w}, expected [{x}]" j)
      expect ((List.range (M + 5)).all fun i => ops.hasVar i w == (i == x)) (at' s!"hasVar does not find variable {x}, or finds another" j)
      expect (ops.lift 3 0 w == row.withChild j (.var (M + 3))) (at' "lift does not shift it" j)
      expect (ops.lift 3 (x + 1) w == w) (at' "lift shifts it below the cut" j)
      expect (ops.lift 3 x w == row.withChild j (.var (M + 3))) (at' "lift does not shift it at the cut" j)
      expect (ops.instantiateAt w x (.const "S" []) == row.withChild j (.const "S" []))
        (at' "instantiateAt does not substitute it" j)
      expect (ops.instantiateAt w (x + 1) (.const "S" []) == w) (at' "instantiateAt changes a lower variable" j)
      expect (ops.instantiateAt w (x - 1) (.const "S" []) == row.withChild j (.var (M - 1)))
        (at' "instantiateAt does not lower a higher variable" j)
      expect (ops.strengthen? x w == none) (at' "strengthen? does not see it" j)
      expect (ops.strengthen? (x - 1) w == some (row.withChild j (.var (M - 1)))) (at' "strengthen? does not lower it" j)
      expect (ops.abstract (row.withChild j (.const "S" [])) (.const "S" []) == row.withChild j (.var d))
        (at' s!"abstract does not replace the target by the variable {d}" j)
    for j in [0:row.levels] do
      let w := row.withLevel j (.param "u")
      expect (ops.levelParamsUsed w == ["u"]) s!"Term.{row.name}, level {j}: levelParamsUsed gives {ops.levelParamsUsed w}"
      expect (ops.instLevels ["u"] [.succ .zero] w == row.withLevel j (.succ .zero))
        s!"Term.{row.name}, level {j}: instLevels does not instantiate it"

/-! ### Evaluation and read-back keep every child

The witness is evaluated in an environment of `L` variables and read back. The marked
child is the variable with the highest level, and the term
read back must mention the variable (index 0). The other children are a lower variable:
every eliminator is stuck on it. -/

def L : Nat := 8
def semEnv : Env R := (List.range L).map fun i => Val.var (L - 1 - i)

/-- Globals for the witnesses: `natOp "nat.add"` needs its registration. -/
def semGlobals (erase : Bool) : Globals R :=
  let g : Globals R := { builtins := [("nat.add", "Nat.add")], quoteErasesProofs := erase }
  g.insert { name := "Nat.add", type := .qty, value := some (.lam "a" (.lam "b" (.var 0))) }

/-- The children that evaluation drops, with the reason. -/
def evalDrops : List (String × Nat × String) := [
  ("letE", 0, "a let's quantity is not part of its value"),
  ("letE", 1, "a let's type annotation is not part of its value"),
  ("letE", 2, "a let's value is reached through the body's variable (the witness body does not use it)"),
  ("ann", 1, "an annotation is not part of the value"),
  ("letUnit", 0, "η for Unit: the eliminator is its body (its scrutinee is evaluated by compiled code only)")]

/-- The children that read-back erases when `quoteErasesProofs` (the kernel's own
comparisons, `sameVal`): the proof positions the syntax marks (P2). -/
def eraseDrops : List (String × Nat × String) := [
  ("cast", 2, "the equation of a cast is a proof"),
  ("transp", 3, "transp's proof `p`"),
  ("transp", 5, "transp's equation `e`"),
  ("prf", 0, "a marked proof at level 0 is erased"),
  -- (P2) read-back erases every proof head, not only suspensions (a `refl` head where the
  -- term was evaluated and a suspension where it was read back are the same proof)
  ("refl", 0, "a refl is a proof"), ("refl", 1, "a refl is a proof"),
  ("reflTy", 0, "a reflTy is a proof"),
  ("transp", 0, "a transp is a proof"), ("transp", 1, "a transp is a proof"),
  ("transp", 2, "a transp is a proof"), ("transp", 4, "a transp is a proof")]

/-- The levels that evaluation drops (none today). -/
def evalLevelDrops : List (String × Nat × String) := [
  ("prf", 0, "a marker at a level that is not 0 is its term's value (it suspends nothing), and read-back writes no marker back")]

def checkTermEval (rows : List TermRow) : Failures Unit := do
  for row in rows do
    for j in [0:row.depths.length] do
      if evalDrops.any fun (n, i, _) => n == row.name && i == j then continue
      -- the mark is the outer variable 0 (level `L - 1`), the others the outer variable 3
      let w := row.build (fun i => .var (row.depths[i]! + (if i == j then 0 else 3))) (fun _ => .zero)
      for erase in [false, true] do
        let g := semGlobals erase
        let v := eval g semEnv w
        let mode := if erase then "erasing proofs" else "evaluating proofs"
        let dropped := erase && eraseDrops.any fun (n, i, _) => n == row.name && i == j
        let back := quote g L v
        expect ((freeVars back).contains 0 == !dropped)
          s!"Term.{row.name}, child {j}: quote ({mode}) of its value {if dropped then "keeps" else "loses"} the child: {repr back}"
    for j in [0:row.levels] do
      if evalLevelDrops.any fun (n, i, _) => n == row.name && i == j then continue
      let w := row.build (fun i => .var (row.depths[i]! + 3)) (fun i => if i == j then .param "u" else .zero)
      for erase in [false, true] do
        let g := semGlobals erase
        let back := quote g L (eval g semEnv w)
        expect (back.levelParamsUsed.contains "u")
          s!"Term.{row.name}, level {j}: quote of its value loses the level: {repr back}"

/-! ## `Val`, `Head`, `Elim` -/

/-- A witness builder for a constructor of `Val`, `Head` or `Elim` (as a value: a head is
wrapped in a neutral, an elimination is applied to a global). `vals` is the number of its
value children (an environment counts as one, a `mu`/`nu` hint as two), `closures` the
binder counts of its closure children, `levels` its level children. -/
structure ValRow where
  name : String
  vals : Nat
  closures : List Nat
  levels : Nat
  build : (Nat → Val R) → (Nat → Closure R) → (Nat → Level) → Val R

def valClassify : String → Option (List Nat)
  | "Val R" | "List (Val R)" => some [1, 0, 0]
  | "Closure R" => some [0, 1, 0]
  | "Level" | "Option Level" => some [0, 0, 1]
  | "List Level" | "BinderSorts" => some [0, 0, 2]
  | "Option (Name × List Level × List (Val R))" => some [2, 0, 2]
  -- a head and a spine have their own tables; a thunk is the value of what the other
  -- fields describe (an unfolding, a proof's value); an `ecase`'s branches and a
  -- suspended proof's term are closed by the environment next to them
  | "Head R" | "Array (Elim R)" | "Thunk (Val R)" | "List (Term R)" | "Term R" => some [0, 0, 0]
  | "Name" | "Nat" | "Lvl" | "BinderInfo" | "R" | "List Name" => some [0, 0, 0]
  | _ => none

def thunk (v : Val R) : Thunk (Val R) := Thunk.mk fun _ => v
def stuck : Val R := .neutral (.global "stuck" []) #[]

def valTable : List ValRow := [
  ⟨"neutral", 0, [], 0, fun _ _ _ => .neutral (.global "h" []) #[]⟩,
  ⟨"sort", 0, [], 1, fun _ _ l => .sort (l 0)⟩,
  ⟨"pi", 2, [1], 2, fun c k l => .pi "x" .default (c 0) (c 1) (k 0) ⟨l 0, l 1⟩⟩,
  ⟨"lam", 0, [1], 0, fun _ k _ => .lam "x" (k 0)⟩,
  ⟨"sigma", 2, [1], 2, fun c k l => .sigma "x" (c 0) (c 1) (k 0) ⟨l 0, l 1⟩⟩,
  ⟨"pair", 2, [], 0, fun c _ _ => .pair (c 0) (c 1)⟩,
  ⟨"unit", 0, [], 1, fun _ _ l => .unit (l 0)⟩,
  ⟨"tt", 0, [], 0, fun _ _ _ => .tt⟩,
  ⟨"empty", 0, [], 1, fun _ _ l => .empty (l 0)⟩,
  ⟨"qty", 0, [], 0, fun _ _ _ => .qty⟩,
  ⟨"qlit", 0, [], 0, fun _ _ _ => .qlit .one⟩,
  ⟨"enum", 0, [], 0, fun _ _ _ => .enum ["a"]⟩,
  ⟨"tag", 0, [], 0, fun _ _ _ => .tag ["a"] 0⟩,
  ⟨"desc", 1, [], 1, fun c _ l => .desc (l 0) (c 0)⟩,
  ⟨"dret", 1, [], 0, fun c _ _ => .dret (c 0)⟩,
  ⟨"darg", 3, [], 0, fun c _ _ => .darg (c 0) (c 1) (c 2)⟩,
  ⟨"drec", 3, [], 0, fun c _ _ => .drec (c 0) (c 1) (c 2)⟩,
  ⟨"dhrec", 4, [], 0, fun c _ _ => .dhrec (c 0) (c 1) (c 2) (c 3)⟩,
  ⟨"mu", 6, [], 3, fun c _ l => .mu (l 0) (c 0) (c 1) (c 2) (c 3) (some ("T", [l 1, l 2], [c 4, c 5]))⟩,
  ⟨"con", 1, [], 0, fun c _ _ => .con (c 0)⟩,
  ⟨"nu", 6, [], 3, fun c _ l => .nu (l 0) (c 0) (c 1) (c 2) (c 3) (some ("T", [l 1, l 2], [c 4, c 5]))⟩,
  ⟨"size", 0, [], 0, fun _ _ _ => .size⟩,
  ⟨"szInf", 0, [], 0, fun _ _ _ => .szInf⟩,
  ⟨"szSuc", 1, [], 0, fun c _ _ => .szSuc (c 0)⟩,
  ⟨"sizeLt", 1, [], 0, fun c _ _ => .sizeLt (c 0)⟩,
  ⟨"cocon", 1, [], 0, fun c _ _ => .cocon (c 0)⟩,
  ⟨"scofix", 7, [], 1, fun c _ l => .scofix (l 0) (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)⟩,
  ⟨"coit", 6, [], 1, fun c _ l => .coit (l 0) (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)⟩,
  ⟨"natLit", 0, [], 0, fun _ _ _ => .natLit 3⟩,
  ⟨"ulift", 1, [], 2, fun c _ l => .ulift (l 0) (l 1) (c 0)⟩,
  ⟨"up", 1, [], 0, fun c _ _ => .up (c 0)⟩,
  ⟨"unfold", 0, [], 2, fun _ _ l => .unfold "f" [l 0, l 1] #[] (thunk stuck)⟩,
  ⟨"lazyInd", 6, [], 2, fun c _ l => .lazyInd (l 0) (c 0) (c 1) (l 1) (c 2) (c 3) (c 4) (c 5) #[] (thunk stuck)⟩
]

def headTable : List ValRow := [
  ⟨"local", 0, [], 0, fun _ _ _ => .neutral (.local 0) #[]⟩,
  ⟨"global", 0, [], 2, fun _ _ l => .neutral (.global "g" [l 0, l 1]) #[]⟩,
  ⟨"mvar", 0, [], 0, fun _ _ _ => .neutral (.mvar 0) #[]⟩,
  ⟨"eq", 3, [], 0, fun c _ _ => .neutral (.eq (c 0) (c 1) (c 2)) #[]⟩,
  ⟨"eqTy", 2, [], 0, fun c _ _ => .neutral (.eqTy (c 0) (c 1)) #[]⟩,
  ⟨"cast", 4, [], 0, fun c _ _ => .neutral (.cast (c 0) (c 1) (c 2) (c 3)) #[]⟩,
  ⟨"refl", 2, [], 0, fun c _ _ => .neutral (.refl (c 0) (c 1)) #[]⟩,
  ⟨"reflTy", 1, [], 0, fun c _ _ => .neutral (.reflTy (c 0)) #[]⟩,
  ⟨"transp", 6, [], 0, fun c _ _ => .neutral (.transp (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)) #[]⟩,
  -- the suspended proof `var 0` in the environment `[c 0]`, whose value is `c 0`
  ⟨"prf", 1, [], 0, fun c _ _ => .neutral (.prf [c 0] (.var 0)) #[]⟩
]

/-- The eliminations, as builders of one spine entry. -/
structure ElimRow where
  name : String
  vals : Nat
  closures : List Nat
  levels : Nat
  build : (Nat → Val R) → (Nat → Closure R) → (Nat → Level) → Elim R

def elimTable : List ElimRow := [
  ⟨"app", 1, [], 0, fun c _ _ => .app (c 0)⟩,
  ⟨"fst", 0, [], 0, fun _ _ _ => .fst⟩,
  ⟨"snd", 0, [], 0, fun _ _ _ => .snd⟩,
  ⟨"split", 1, [1, 2], 0, fun c k _ => .split (c 0) "z" (k 0) "x" "y" (k 1)⟩,
  ⟨"absurd", 1, [], 0, fun c _ _ => .absurd (c 0)⟩,
  -- one branch, `var 0`, in the environment `[c 0]`
  ⟨"ecase", 1, [1], 0, fun c k _ => .ecase "z" (k 0) [c 0] [.var 0]⟩,
  ⟨"delim", 5, [], 1, fun c _ l => .delim (l 0) (c 0) (c 1) (c 2) (c 3) (c 4)⟩,
  ⟨"ind", 5, [], 2, fun c _ l => .ind (l 0) (c 0) (c 1) (l 1) (c 2) (c 3) (c 4)⟩,
  ⟨"sfix", 6, [], 2, fun c _ l => .sfix (l 0) (c 0) (c 1) (l 1) (c 2) (c 3) (c 4) (c 5)⟩,
  ⟨"scase", 7, [], 2, fun c _ l => .scase (l 0) (c 0) (c 1) (c 2) (l 1) (c 3) (c 4) (c 5) (c 6)⟩,
  ⟨"out", 0, [], 0, fun _ _ _ => .out⟩,
  ⟨"down", 0, [], 0, fun _ _ _ => .down⟩
]

def ElimRow.toValRow (r : ElimRow) (wrap : Elim R → Val R) : ValRow :=
  { name := r.name, vals := r.vals, closures := r.closures, levels := r.levels,
    build := fun c k l => wrap (r.build c k l) }

/-- The constructor names, written out: a `match` with no default, so that a new
constructor does not compile until it is named here (and then needs a row). -/
def valCtorName : Val R → String
  | .neutral .. => "neutral" | .sort _ => "sort" | .pi .. => "pi" | .lam .. => "lam"
  | .sigma .. => "sigma" | .pair .. => "pair" | .unit _ => "unit" | .tt => "tt"
  | .empty _ => "empty" | .qty => "qty" | .qlit _ => "qlit" | .enum _ => "enum"
  | .tag .. => "tag" | .desc .. => "desc" | .dret _ => "dret" | .darg .. => "darg"
  | .drec .. => "drec" | .dhrec .. => "dhrec" | .mu .. => "mu" | .con _ => "con"
  | .nu .. => "nu" | .size => "size" | .szInf => "szInf" | .szSuc _ => "szSuc"
  | .sizeLt _ => "sizeLt" | .cocon _ => "cocon" | .scofix .. => "scofix" | .coit .. => "coit"
  | .natLit _ => "natLit" | .ulift .. => "ulift" | .up _ => "up" | .unfold .. => "unfold"
  | .lazyInd .. => "lazyInd"

def headCtorName : Head R → String
  | .local _ => "local" | .global .. => "global" | .mvar _ => "mvar" | .eq .. => "eq"
  | .eqTy .. => "eqTy" | .cast .. => "cast" | .refl .. => "refl" | .reflTy _ => "reflTy"
  | .transp .. => "transp" | .prf .. => "prf"

def elimCtorName : Elim R → String
  | .app _ => "app" | .fst => "fst" | .snd => "snd" | .split .. => "split"
  | .absurd _ => "absurd" | .ecase .. => "ecase" | .delim .. => "delim" | .ind .. => "ind"
  | .sfix .. => "sfix" | .scase .. => "scase" | .out => "out" | .down => "down"

/-- The level of the marked variable in a value witness, and the level to quote at. -/
def VM : Nat := 6

def plainV : Val R := .tt
def plainK : Closure R := .mk [] (.var 0)
/-- A closure under `b` binders whose body is the entry of its environment. -/
def markK (b : Nat) (v : Val R) : Closure R := .mk [v] (.var b)

/-- Every child of every value constructor is read back by
`quote` in both modes; `eraseExempt` names the rows whose children are erased proofs. -/
def checkValRows (what : String) (rows : List ValRow) (eraseExempt : List String := []) :
    Failures Unit := do
  for row in rows do
    let plain := row.build (fun _ => plainV) (fun _ => plainK) (fun _ => .zero)
    let _ := plain
    let marked : List (String × Val R) :=
      (List.range row.vals).map (fun j => (s!"value child {j}",
        row.build (fun i => if i == j then Val.var VM else plainV) (fun _ => plainK) (fun _ => .zero))) ++
      (List.range row.closures.length).map (fun j => (s!"closure child {j}",
        row.build (fun _ => plainV) (fun i => if i == j then markK row.closures[j]! (Val.var VM) else plainK) (fun _ => .zero)))
    for (child, w) in marked do
      for erase in [false, true] do
        let g := semGlobals erase
        let back := quote g (VM + 1) w
        let dropped := erase && eraseExempt.contains row.name
        expect ((freeVars back).contains 0 == !dropped)
          s!"{what}.{row.name}, {child}: quote (quoteErasesProofs := {erase}) {if dropped then "keeps" else "loses"} the child: {repr back}"
    for j in [0:row.levels] do
      let w := row.build (fun _ => plainV) (fun _ => plainK) (fun i => if i == j then .param "u" else .zero)
      for erase in [false, true] do
        let back := quote (semGlobals erase) (VM + 1) w
        expect (back.levelParamsUsed.contains "u")
          s!"{what}.{row.name}, level {j}: quote (quoteErasesProofs := {erase}) loses the level: {repr back}"

/-! ## `Level` -/

structure LevelRow where
  name : String
  kids : Nat
  build : (Nat → Level) → Level

def levelTable : List LevelRow := [
  ⟨"zero", 0, fun _ => .zero⟩,
  ⟨"succ", 1, fun c => .succ (c 0)⟩,
  ⟨"max", 2, fun c => .max (c 0) (c 1)⟩,
  ⟨"imax", 2, fun c => .imax (c 0) (c 1)⟩,
  ⟨"param", 0, fun _ => .param "p"⟩,
  ⟨"mvar", 0, fun _ => .mvar 0⟩,
  ⟨"hole", 0, fun _ => .hole⟩
]

def levelCtorName : Level → String
  | .zero => "zero" | .succ _ => "succ" | .max .. => "max" | .imax .. => "imax"
  | .param _ => "param" | .mvar _ => "mvar" | .hole => "hole"

def checkLevels : Failures Unit := do
  for row in levelTable do
    for j in [0:row.kids] do
      let w (mark : Level) (plain : Level := .param "p") : Level := row.build fun i => if i == j then mark else plain
      let at' (what : String) := s!"Level.{row.name}, child {j}: {what}"
      expect ((w (.param "u")).params.contains "u") (at' "params misses it")
      let inst := (w (.param "u")).instParams ["u"] [.param "v"]
      expect (inst == w (.param "v")) (at' "instParams does not instantiate it")
      expect (w (.mvar 7)).hasMVar (at' "hasMVar misses it")
      expect ((w (.mvar 7)).instMVars (fun m => if m == 7 then some (.param "v") else none) == w (.param "v"))
        (at' "instMVars does not instantiate it")
      expect ((w (.param "u")).normalize != (w (.succ (.param "u"))).normalize) (at' "normalize ignores it")
      expect (!(w (.param "u")).equiv (w (.succ (.succ (.param "u"))))) (at' "equiv ignores it")
      expect ((w (Level.ofNat 5) (Level.ofNat 1)).toNat? != (w (Level.ofNat 7) (Level.ofNat 1)).toNat?
          && ((w (Level.ofNat 5) (Level.ofNat 1)).toNat?).isSome)
        (at' "toNat? ignores it")
      expect (toString (w (.param "u")) != toString (w (.param "v"))) (at' "format ignores it")

/-! ## Catch-all arms of the Lean kernel's traversals, pinned

The number of default arms (`| _ =>`, `| _, _ =>`, `| t =>`: a pattern of wildcards and
variables only) in each function below. A new one fails here until it is reviewed: is the
default the conservative answer for a constructor added later? `wiz-notes/kernel-lint.md`
has the table with the verdict of each. Zero means the function is a total match, which
the compiler then checks. -/

/-- The text of a top-level (or mutual, or `where`-local) definition: from its `def` line
to the next line that starts a declaration at the same or a lower indentation. -/
def leanFnBody (src fn : String) : Option (List String) := Id.run do
  let lines := src.splitOn "\n"
  let indent (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length
  let isDef (l : String) : Bool :=
    let t := trim l
    let t := (t.splitOn "def ").getD 1 ""
    !(trim l).startsWith "--" && hasSub l "def " && t.startsWith fn && !((t.toList.drop fn.length).head?.any fun c => isIdChar c || c == '.')
  match lines.dropWhile (!isDef ·) with
  | [] => return none
  | hd :: rest =>
    let ind := indent hd
    let starts := ["def ", "partial def ", "private ", "protected ", "@[", "theorem ", "instance ",
      "end", "mutual", "inductive ", "structure ", "abbrev ", "/--", "/-!", "namespace ", "where", "variable "]
    let body := rest.takeWhile fun l =>
      trim l == "" || indent l > ind || !(starts.any ((trim l).startsWith ·))
    return some (hd :: body)

/-- Is this line a default arm: `| p₁, …, pₙ =>` where every `pᵢ` is `_` or a variable? -/
def isCatchAll (line : String) : Bool :=
  let t := trim line
  if !t.startsWith "| " then false else
  match (t.drop 2).toString.splitOn "=>" with
  | pat :: _ :: _ =>
    let ps := splitTop pat (· == ',')
    !ps.isEmpty && ps.all fun p =>
      p == "_" || (p.toList.all isIdChar && (p.toList.head?.any Char.isLower) &&
        !["none", "true", "false", "nil", "zero"].contains p)
  | _ => false

def catchAlls (body : List String) : List String :=
  body.filter fun l => !(trim l).startsWith "--" && isCatchAll l

/-- file, function, the number of default arms, and why they are safe (the note has more). -/
def pinned : List (String × String × Nat × String) := [
  ("Wiz/Core/Term.lean", "mapChildrenM", 0, "the leaves by name (prf-conv): no default arm"),
  ("Wiz/Core/Term.lean", "lift", 1, "everything but `var` goes to mapChildrenM"),
  ("Wiz/Core/Term.lean", "abstract", 1, "as lift"),
  ("Wiz/Core/Term.lean", "strengthen?", 1, "as lift"),
  ("Wiz/Core/Term.lean", "instantiateAt", 1, "as lift"),
  ("Wiz/Core/Term.lean", "hasVar", 1, "as lift"),
  ("Wiz/Core/Term.lean", "instLevels", 0, ""),
  ("Wiz/Core/Term.lean", "levelParamsUsed", 0, ""),
  ("Wiz/Core/Eval.lean", "eval", 2, "`const`: no definition is a stuck global; `szSuc`: any size but ∞"),
  ("Wiz/Core/Eval.lean", "quote", 2, "the erased proof's `isAbsurd`; a lazyInd's spine holds only app/fst/snd/down (the lint checks that dynamically: 'glued spines')"),
  ("Wiz/Core/Eval.lean", "vElims", 0, ""),
  ("Wiz/Core/Level.lean", "instParams", 0, ""),
  ("Wiz/Core/Level.lean", "instMVars", 0, ""),
  ("Wiz/Core/Level.lean", "params", 0, ""),
  ("Wiz/Core/Level.lean", "hasMVar", 0, ""),
  ("Wiz/Core/Level.lean", "normalize", 0, ""),
  ("Wiz/Core/Level.lean", "toNat?", 1, "param, mvar: not closed"),
]

def checkPinned : Failures Unit := do
  for (file, fn, n, _) in pinned do
    let src ← IO.FS.readFile file
    match leanFnBody src fn with
    | none => fail s!"{file}: no definition `{fn}` (renamed? update `pinned` in Tests/Lint.lean)"
    | some body =>
      let cs := catchAlls body
      unless cs.length == n do
        fail s!"{file}, {fn}: {cs.length} default arm(s), the lint pins {n}. A default arm in a traversal hides a constructor added later: make the match explicit, or review it, update `pinned` and the table in wiz-notes/kernel-lint.md. Found: {cs.map trim}"

/-! ## `Kernel.wiz`, statically

The self-hosted kernel has no generic traversal: each function matches on every
constructor. For each function below, its arms are parsed and checked against the
constructors of its type (read from the same file):

* **total**: no default arm at all, or (`defaultOk`) the default is the conservative
  answer, so a constructor may be left to it;
* otherwise every constructor that has a child must have its own arm;
* in every arm, each child (a field whose type is in `childTys`) is bound to a variable
  that the right-hand side uses, unless `(constructor, field)` is in `exempt`.
-/

structure WizFn where
  fn : String
  /-- the inductive type whose constructors the arms are about -/
  ty : String
  /-- which of the arm's comma-separated patterns is of that type -/
  arg : Nat
  /-- the arms compare two values: the patterns at `arg` and `arg + 1` -/
  binary : Bool := false
  /-- a default arm is allowed, and a constructor with children may fall into it -/
  defaultOk : Bool := false
  /-- (binary) every constructor must have an arm that compares it with itself -/
  diagonal : Bool := false
  /-- a default arm is allowed for the constructors without children -/
  leafDefault : Bool := false
  childTys : List String := ["Tm", "Tms", "Val", "Env", "Spine", "Head"]
  /-- `(constructor, field)`: this child is not used, on purpose; the reason -/
  exempt : List (String × String × String) := []
  /-- a known violation, reported to the coordinator and not yet fixed (the function is
  being changed on another branch): the lint expects it to fail, and fails when it no
  longer does, so that this mark is removed with the fix -/
  pending : Option String := none

structure Arm where
  pats : List String
  rhs : String

/-- The arms of `def fn` in `Kernel.wiz`: the lines `  | pats => rhs` (two spaces), each
with the more indented lines that follow it. The definition ends at the next line that is
not indented. Comment lines (the exercise stubs among them) are skipped. -/
def wizArms (src fn : String) : Except String (List Arm) := do
  let lines := src.splitOn "\n"
  let isDef (l : String) : Bool :=
    let l := if l.startsWith "partial " then (l.drop 8).toString else l
    l.startsWith ("def " ++ fn) && !((l.toList.drop (4 + fn.length)).head?.any fun c => isIdChar c || c == '.')
  match lines.dropWhile (!isDef ·) with
  | [] => throw s!"no `def {fn}`"
  | _ :: rest =>
    let body := rest.takeWhile fun l => l == "" || l.startsWith " "
    let mut arms : List (String × String) := []
    for l in body do
      if (trim l).startsWith "--" then continue
      if l.startsWith "  | " then
        match (l.drop 4).toString.splitOn " =>" with
        | pat :: r => arms := (pat, " =>".intercalate r) :: arms
        | [] => pure ()
      else match arms with
        | (p, r) :: more => arms := (p, r ++ "\n" ++ l) :: more
        | [] => pure ()
    if arms.isEmpty then throw s!"`def {fn}` has no arms"
    return arms.reverse.map fun (p, r) => { pats := splitTop p (· == ','), rhs := r }

/-- `.ctor x y (nested …)` as `(ctor, [x, y, (nested …)])`; `none` for a default. -/
def ctorPat (p : String) : Option (String × List String) :=
  let p := if p.startsWith "(" && p.endsWith ")" then String.ofList (p.toList.drop 1).dropLast else p
  if p.startsWith "." then
    match splitTop (p.drop 1).toString Char.isWhitespace with
    | c :: fs => some (c, fs)
    | [] => none
  else none

/-- Does the identifier `x` occur in `s` (as a whole word)? -/
def usesWord (s x : String) : Bool := Id.run do
  let mut cur : List Char := []
  for c in s.toList ++ [' '] do
    if isIdChar c then cur := c :: cur
    else
      if String.ofList cur.reverse == x then return true
      cur := []
  return false

def checkWizFn (src : String) (f : WizFn) : Failures Unit := do
  let ctors ← match parseInductive src f.ty with
    | .ok cs => pure cs
    | .error e => fail s!"Kernel.wiz: {e}"; return
  let arms ← match wizArms src f.fn with
    | .ok as => pure as
    | .error e => fail s!"Kernel.wiz: {e} (renamed? update `wizFns` in Tests/Lint.lean)"; return
  let isChild (c : Ctor) (field : String × String) : Bool :=
    f.childTys.contains field.2 && !(f.exempt.any fun (n, x, _) => n == c.name && x == field.1)
  let mut seen : List String := []
  let mut hasDefault := false
  for arm in arms do
    let some p := arm.pats[f.arg]? | fail s!"Kernel.wiz, {f.fn}: an arm has fewer than {f.arg + 1} patterns: {arm.pats}"
    match ctorPat p with
    | none =>
      hasDefault := true
      unless f.defaultOk || f.leafDefault do
        fail s!"Kernel.wiz, {f.fn}: a default arm (`{", ".intercalate arm.pats} => …`): this function must match every constructor of {f.ty} by name (a constructor added later would fall into it)"
    | some (cn, fields) =>
      let some c := ctors.find? (·.name == cn) | fail s!"Kernel.wiz, {f.fn}: `.{cn}` is not a constructor of {f.ty}"
      seen := cn :: seen
      let sides := if f.binary then [fields, ((arm.pats[f.arg + 1]?.bind ctorPat).map (·.2)).getD []] else [fields]
      if f.binary && ((arm.pats[f.arg + 1]?.bind ctorPat).map (·.1)) != some cn then
        -- (a mixed arm, such as `.vszInf, _`: not a comparison of like with like)
        seen := seen.drop 1
        continue
      for fs in sides do
        unless fs.length == c.fields.length do
          fail s!"Kernel.wiz, {f.fn}, .{cn}: the pattern has {fs.length} fields, the constructor {c.fields.length}"
          continue
        for (field, pat) in c.fields.zip fs do
          if isChild c field && !pat.startsWith "(" then
            if pat == "_" then
              fail s!"Kernel.wiz, {f.fn}, .{cn}: the child `{field.1} : {field.2}` is ignored (`_`)"
            else unless usesWord arm.rhs pat do
              fail s!"Kernel.wiz, {f.fn}, .{cn}: the child `{field.1} : {field.2}` (bound to `{pat}`) is not used"
  if f.diagonal then
    for c in ctors do
      unless seen.contains c.name do
        fail s!"Kernel.wiz, {f.fn}: no arm compares the constructor `.{c.name}` of {f.ty} with itself"
  unless f.defaultOk && hasDefault do
    for c in ctors do
      let needsArm := !hasDefault || c.fields.any (isChild c)
      if needsArm && !seen.contains c.name then
        fail s!"Kernel.wiz, {f.fn}: no arm for the constructor `.{c.name}` of {f.ty}{if hasDefault then ", which has children: the default arm skips them" else ""}"

/-- Closed terms carried by a constant or an axiom: its value and type. They have no free
variables and their own level parameters. -/
def closedConst (why : String) : List (String × String × String) :=
  [("const", "value", why), ("const", "ty", why), ("axiomC", "ty", why),
   ("hconst", "value", why), ("hconst", "ty", why), ("haxiom", "ty", why)]

/-- The parts of proofs: conversion never compares two proofs (proof irrelevance). -/
def proofFields : List (String × String × String) :=
  let why := "a proof: all proofs of a proposition are convertible"
  [("hcast", "e", why), ("hrefl", "A", why), ("hrefl", "a", why), ("hreflTy", "X", why),
   ("htransp", "A", why), ("htransp", "a", why), ("htransp", "P", why), ("htransp", "p", why),
   ("htransp", "b", why), ("htransp", "e", why), ("hprf", "env", why), ("hprf", "t", why)]

def wizFns : List WizFn := [
  -- level substitution: every `Lvl`, `Tm`, `Tms` field
  { fn := "tmSubst", ty := "Tm", arg := 0, leafDefault := true, childTys := ["Tm", "Tms", "Lvl", "List Lvl"],
    exempt := closedConst "a constant's value and type are closed and have their own level parameters" },
  { fn := "tmsSubst", ty := "Tms", arg := 0 },
  { fn := "substLvl", ty := "Lvl", arg := 0, leafDefault := true, childTys := ["Lvl"] },
  { fn := "lvlNorm", ty := "Lvl", arg := 0, childTys := ["Lvl"] },
  { fn := "lvlParams", ty := "Lvl", arg := 0, leafDefault := true, childTys := ["Lvl"] },
  { fn := "lvlClosed", ty := "Lvl", arg := 0, childTys := ["Lvl"] },
  -- syntactic equality: the default is `false`, the conservative answer; in the arms
  -- that say `true`, every child must be compared, except proofs (all proofs are equal)
  { fn := "tmEq", ty := "Tm", arg := 0, binary := true, defaultOk := true, childTys := ["Tm", "Tms", "Lvl", "List Lvl"],
    exempt := closedConst "constants are compared by name (names are unique: CoreSpec §15)" ++ [
      ("coe", "e", "a cast's equation is a proof"),
      ("eqRefl", "A", "a proof"), ("eqRefl", "a", "a proof"), ("tyRefl", "X", "a proof"),
      ("subst", "A", "a proof"), ("subst", "a", "a proof"), ("subst", "P", "a proof"),
      ("subst", "p", "a proof"), ("subst", "b", "a proof"), ("subst", "e", "a proof")] },
  { fn := "tmsEq", ty := "Tms", arg := 0, binary := true, defaultOk := true },
  -- "might mention the variable": the default is `true`, the conservative answer
  { fn := "usesVar", ty := "Tm", arg := 1, defaultOk := true,
    exempt := closedConst "closed" },
  -- evaluation and read-back
  { fn := "eval", ty := "Tm", arg := 1,
    exempt := closedConst "a constant's type is not part of its value" ++ [
      ("letE", "ty", "a let's type is not part of its value"), ("letq", "ty", "as letE"),
      ("ann", "ty", "an annotation is not part of the value"),
      ("letUnit", "u", "η for Unit: the eliminator is its body (its scrutinee is evaluated by compiled code only)")] },
  { fn := "forceSp", ty := "Spine", arg := 1 },
  { fn := "fromAbsurd", ty := "Spine", arg := 0,
    exempt := [("sabsurd", "sp", "the eliminations from the last `absurd` on: what is below it is the erased proof")] },
  { fn := "quoteM", ty := "Val", arg := 1 },
  { fn := "quoteSpine", ty := "Spine", arg := 2 },
  { fn := "quoteHead", ty := "Head", arg := 1 },
  { fn := "quoteBranches", ty := "Tms", arg := 2 },
  -- conversion of neutrals: the default is `false`
  { fn := "convHead", ty := "Head", arg := 1, binary := true, defaultOk := true, diagonal := true,
    childTys := ["Tm", "Tms", "Val", "Env", "Spine", "Head", "Lvl", "List Lvl"],
    exempt := closedConst "constants are compared by name" ++ proofFields },
  { fn := "convSpineW", ty := "Spine", arg := 3, binary := true, defaultOk := true, diagonal := true },
  -- the structural fast path (`valSame`): its default is "don't know", but an arm that
  -- answers "the same" must have compared every child, levels included
  { fn := "headSame", ty := "Head", arg := 1, binary := true, defaultOk := true,
    childTys := ["Tm", "Tms", "Val", "Env", "Spine", "Head", "Lvl", "List Lvl"],
    exempt := closedConst "constants are compared by name" },
  { fn := "spineSame", ty := "Spine", arg := 1, binary := true, defaultOk := true },
  { fn := "valSame", ty := "Val", arg := 1, binary := true, defaultOk := true },
  -- (mandatory sorts) the sorts pass skips a term without holes: a hole missed here is
  -- one the pass does not fill (a kernel error, never unsoundness)
  { fn := "tmHasHole", ty := "Tm", arg := 0, childTys := ["Tm", "Tms", "Lvl"],
    exempt := closedConst "a constant's value and type are closed and were filled when it was declared" ++
      [("const", "levels", "a constant's levels are never holes")] },
  { fn := "lvlHasHole", ty := "Lvl", arg := 0, childTys := ["Lvl"] },
]

/-! ## The lint against a broken traversal

The properties above are only worth something if they fail on the bugs they are for.
`brokenOps` is the kernel's traversal with the S1 bug put back (no case for `natOp`). -/

def brokenChildren (t : Term R) : List (Nat × Term R) :=
  match t with
  | .natOp .. => []
  | t => kernelOps.children t

partial def brokenFreeVars (depth : Nat) (t : Term R) : List Nat :=
  match t with
  | .var i => if i ≥ depth then [i - depth] else []
  | t => (brokenChildren t).flatMap fun (k, c) => brokenFreeVars (depth + k) c

def brokenOps : TermOps := { kernelOps with children := brokenChildren, freeVars := brokenFreeVars 0 }

/-! ## Panics

Each ill-typed term below makes one eliminator of the evaluator panic. The checker never
evaluates a term it has not checked. The one exception this audit found, the display hint
of a `mu`/`nu` (`wiz-notes/kernel-lint.md`, H), is closed by `checkHint` (PR #83):
`hintCarrier X` carries the raw term `X` in a hint, and `addDecl` now rejects it with an
ordinary error before evaluating it. The panics themselves are reached by evaluating each
term directly (`--panic-probe MODE eval:SITE`). -/

def panicSites : List (String × Term R) := [
  ("vFst", .fst .tt),
  ("vSnd", .snd .tt),
  ("vDown", .down .tt),
  ("vAbsurd", .absurd .tt .tt),
  ("vApp", .app .tt .tt),
  ("vSplit", .split (.qlit .one) .tt "z" .tt "x" "y" .tt),
  ("vEcase", .ecase "z" .tt .tt []),
  ("vEcase-tag", .ecase "z" .tt (.tag [] 0) []),
  ("vDelim", .delim .zero .tt .tt .tt .tt .tt .tt),
  ("vInd", .ind .zero .tt .tt .zero .tt .tt .tt .tt),
  ("vSfix", .sfix .zero .tt .tt .zero .tt .tt .tt .tt .tt),
  ("vScase", .scase .zero .tt .tt .tt .zero .tt .tt .tt .tt .tt),
  ("vOut", .out .tt),
  ("vNatOp", .natOp "nat.add" #[.tt, .tt])
]

def hintCarrier (X : Term R) : Decl R :=
  { name := "carrier", value := none
    type := .pi "x" .default (.qlit .one)
      (.mu 0 (.unit 1) (.dret .tt) .tt .szInf (some ("hint", [], [X]))) (.unit 1) ⟨1, 1⟩ }

/-- `tests --panic-probe MODE SITE`: check `hintCarrier` of the site's term (`eval`: just
evaluate `fst ()` and print the constructor of the value; `eval:SITE`: evaluate the site's
term directly, force it and read it back), after `exitOnPanic` when MODE is `exit`. Prints
the verdict. -/
def panicProbe (mode site : String) : IO UInt32 := do
  Wiz.exitOnPanic (mode == "exit")
  if site == "eval" then
    IO.println (valCtorName (Wiz.eval (R := R) {} [] (.fst .tt)))
    return 0
  if site.startsWith "eval:" then
    let name := site.drop 5
    let some (_, X) := panicSites.find? (·.1 == name) | do IO.eprintln s!"no such site: {name}"; return 2
    let v := Wiz.whnf (Wiz.eval (R := R) {} [] X)
    let t := quote {} 0 v
    IO.println s!"{valCtorName v} {(reprStr t).length}"
    return 0
  let some (_, X) := panicSites.find? (·.1 == site) | do IO.eprintln s!"no such site: {site}"; return 2
  match addDecl {} (hintCarrier X) with
  | .ok _ => IO.println "accepted"
  | .error e => IO.println s!"rejected: {e}"
  return 0

/-! ## The group -/

def lintGroup : Group where
  name := "lint"
  parallel := true
  exercise := "kernel hygiene (wiz-notes/kernel-lint.md)"
  cases := [
    { name := "Term: every constructor in the source has a witness row, with the source's children", run := fun _ => do
        let ctors ← readCtors "Wiz/Core/Term.lean" "Term"
        report "Term table" do
          checkTable "Term" ctors (termTable.map fun r => (r.name, [r.depths.length, r.levels])) termClassify ["terms", "levels"]
          for r in termTable do
            let w := r.build (fun _ => plainT) (fun _ => .zero)
            expect (termCtorName w == r.name) s!"Term.{r.name}: the row builds a `{termCtorName w}`" },
    { name := "Term: mapChildrenM, forChildren, freeVarsAt, hasVar, lift, instantiateAt, strengthen?, abstract, instLevels, levelParamsUsed reach every child", run := fun _ =>
        report "Term traversals" (checkTermOps kernelOps termTable) },
    { name := "Term: eval and quote (both modes) keep every child and level", run := fun _ =>
        report "Term evaluation" (checkTermEval termTable) },
    { name := "the lint fails on the S1 bug (a traversal without a case for natOp)", run := fun _ => do
        let ((), fs) ← (checkTermOps brokenOps termTable).run #[]
        check (fs.any (hasSub · "Term.natOp")) "the lint accepts a traversal that skips natOp"
        check (fs.all (hasSub · "Term.natOp")) s!"the broken traversal fails elsewhere: {fs}" },
    { name := "Val, Head, Elim: every constructor in the source has a witness row", run := fun _ => do
        let vs ← readCtors "Wiz/Core/Value.lean" "Val"
        let hs ← readCtors "Wiz/Core/Value.lean" "Head"
        let es ← readCtors "Wiz/Core/Value.lean" "Elim"
        report "value tables" do
          let counts (r : ValRow) := (r.name, [r.vals, r.closures.length, r.levels])
          let kinds := ["values", "closures", "levels"]
          checkTable "Val" vs (valTable.map counts) valClassify kinds
          checkTable "Head" hs (headTable.map counts) valClassify kinds
          checkTable "Elim" es (elimTable.map fun r => (r.name, [r.vals, r.closures.length, r.levels])) valClassify kinds
          let plain (r : ValRow) := r.build (fun _ => plainV) (fun _ => plainK) (fun _ => .zero)
          for r in valTable do
            expect (valCtorName (plain r) == r.name) s!"Val.{r.name}: the row builds a `{valCtorName (plain r)}`"
          for r in headTable do
            match plain r with
            | .neutral h _ => expect (headCtorName h == r.name) s!"Head.{r.name}: the row builds a `{headCtorName h}`"
            | _ => fail s!"Head.{r.name}: the row does not build a neutral"
          for r in elimTable do
            let e := r.build (fun _ => plainV) (fun _ => plainK) (fun _ => .zero)
            expect (elimCtorName e == r.name) s!"Elim.{r.name}: the row builds a `{elimCtorName e}`" },
    { name := "Val, Head, Elim: quote (both modes) reads back every child and level", run := fun _ =>
        report "value traversals" do
          checkValRows "Val" valTable
          -- (a suspended proof is erased by `quoteErasesProofs`; its bound still counts)
          checkValRows "Head" headTable (eraseExempt := ["prf", "refl", "reflTy", "transp"])
          checkValRows "Elim" (elimTable.map (·.toValRow fun e => .neutral (.global "h" []) #[e]))
          -- the variable itself
          expect (quote (semGlobals false) 7 (Val.var 4 : Val R) == .var 2) "Head.local: quote is not the index" },
    { name := "glued spines: every elimination of an unfold or a lazyInd is counted and read back", run := fun _ =>
        report "glued spines" do
          checkValRows "Elim (on an unfold)" (elimTable.map (·.toValRow fun e => .unfold "f" [] #[e] (thunk stuck)))
          -- a lazyInd's spine is read back only for app/fst/snd/down (`quote`'s default
          -- arm drops the rest): so no eliminator may push anything else onto it. Apply
          -- each elimination to a lazyInd, as the evaluator does, and read the result back.
          let lz : Val R := .lazyInd .zero plainV plainV .zero plainV plainV plainV plainV #[] (thunk stuck)
          checkValRows "Elim (applied to a lazyInd)" (elimTable.map (·.toValRow fun e => vElims (semGlobals false) lz #[e])) },
    { name := "type equality: `T = T` never computes to False, for any value constructor", run := fun _ =>
        -- (`vEqType`'s last case answers `False` for two canonical types that no case
        -- above it matched: right only while every former it calls canonical has its own
        -- case. A former added to that list without one would make `T = T` false.)
        report "T = T" do
          let g := semGlobals false
          let one : Level := .succ .zero
          let mut types := 0
          for row in valTable ++ headTable do
            let w := row.build (fun _ => .unit one) (fun _ => .mk [] (.unit one)) (fun _ => one)
            if propSort? (whnf w) == some false then types := types + 1
            match whnf (vEqType g w w) with
            | .empty _ => fail s!"Val.{row.name}: `T = T` computes to False for T := {repr (quote g 0 w)}"
            | _ => pure ()
          -- the witnesses that are types above `Prop` (pi, sigma, sort, unit, empty, enum,
          -- desc, mu, nu, ulift, qty, size, sizeLt): if this drops, the witnesses no longer
          -- reach the cases under test
          expect (types ≥ 13) s!"only {types} witnesses are types above Prop: the property no longer tests the canonical formers" },
    { name := "Level: every constructor has a row; instParams, instMVars, params, hasMVar, normalize, equiv, toNat?, format reach every child", run := fun _ => do
        let ctors ← readCtors "Wiz/Core/Level.lean" "Level"
        report "Level" do
          checkTable "Level" ctors (levelTable.map fun r => (r.name, [r.kids]))
            (fun ty => if ty == "Level" then some [1] else if ty == "String" || ty == "Nat" then some [0] else none) ["levels"]
          for r in levelTable do
            let w := r.build fun _ => .zero
            expect (levelCtorName w == r.name) s!"Level.{r.name}: the row builds a `{levelCtorName w}`"
          checkLevels },
    { name := "Lean kernel: the default arms of the traversals are the pinned ones", run := fun _ =>
        report "pinned default arms" checkPinned },
    { name := "Kernel.wiz: tmSubst, tmEq, usesVar, the level bound, eval, quote and the neutral comparisons handle every constructor and child", run := fun _ => do
        let src ← IO.FS.readFile "selfhost/Kernel.wiz"
        report "Kernel.wiz traversals" do
          for f in wizFns do
            let ((), fs) ← (checkWizFn src f).run #[]
            match f.pending with
            | none => modify (· ++ fs)
            | some why =>
              expect (!fs.isEmpty) s!"Kernel.wiz, {f.fn}: marked pending ({why}) but the lint finds nothing: remove the mark" },
    { name := "a panic's value is a stuck unknown that the checker rejects, not Sort 0; with exitOnPanic the process ends", run := fun _ => do
        let self ← IO.appPath
        -- (`fst ()` in the evaluator: `vFst`'s panic)
        let go ← IO.Process.output { cmd := self.toString, args := #["--panic-probe", "continue", "eval"] }
        check (go.exitCode == 0 && trim go.stdout == "neutral")
          s!"after a panic the evaluator went on with a `{trim go.stdout}` (exit code {go.exitCode}), expected a stuck neutral"
        check (hasSub go.stderr "PANIC") s!"no panic message: {go.stderr}"
        let stop ← IO.Process.output { cmd := self.toString, args := #["--panic-probe", "exit", "eval"] }
        check (stop.exitCode == 1 && trim stop.stdout == "" && hasSub stop.stderr "PANIC")
          s!"with exitOnPanic: exit code {stop.exitCode}, output `{trim stop.stdout}`, expected 1 and none"
        -- the default value read back is not a type, nor a term of any type
        let t : Term R := quote {} 0 (default : Val R)
        check (t == .const kernelPanicName []) s!"the default value reads back as {repr t}"
        match addDecl {} { name := "x", type := t, value := none } with
        | .ok _ => throw (IO.userError "the checker accepts a panic's value as a type")
        | .error _ => pure ()
        match addDecl {} { name := "x", type := .sort 0, value := some t } with
        | .ok _ => throw (IO.userError "the checker accepts a panic's value as a proposition")
        | .error _ => pure () },
    { name := "a raw core term in a mu's hint is rejected by the checker before it is evaluated (finding H, checkHint)", run := fun _ => do
        let self ← IO.appPath
        -- the carrier itself is well typed (with a hint argument whose type can be inferred)
        match addDecl {} (hintCarrier (.ann .tt (.unit 0))) with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"the carrier is rejected: {e}")
        let mut bad : List String := []
        for (site, _) in panicSites do
          let out ← IO.Process.output { cmd := self.toString, args := #["--panic-probe", "exit", site] }
          unless out.exitCode == 0 && (trim out.stdout).startsWith "rejected:" && !hasSub out.stderr "PANIC" do
            bad := bad ++ [s!"{site}: exit code {out.exitCode}, output `{trim out.stdout}`, stderr `{(out.stderr.take 200).toString}`"]
        check bad.isEmpty s!"a raw term in a hint was not rejected with an ordinary error: {bad}" },
    { name := "every panic of the evaluator, reached from a raw core term, ends the process", run := fun _ => do
        let self ← IO.appPath
        let mut bad : List String := []
        for (site, _) in panicSites do
          let out ← IO.Process.output { cmd := self.toString, args := #["--panic-probe", "exit", s!"eval:{site}"] }
          unless out.exitCode == 1 && hasSub out.stderr "PANIC" && trim out.stdout == "" do
            bad := bad ++ [s!"{site}: exit code {out.exitCode}, output `{trim out.stdout}`, stderr `{(out.stderr.take 200).toString}`"]
        check bad.isEmpty s!"an evaluator panic did not end the process: {bad}" },
    { name := "the static lint fails on a default arm and on an ignored child", run := fun _ => do
        let src := "inductive T where\n  | leaf\n  | node (a b : T)\n  | wrap (t : T)\n" ++
          "def f : T → T\n  | .node a _ => .wrap a\n  | t => t\n" ++
          "def g : T → T\n  | .leaf => .leaf\n  | .node a b => .node (g a) (g b)\n  | .wrap t => .wrap (g t)\n"
        let run (fn : WizFn) : IO (Array String) := do
          let ((), fs) ← (checkWizFn src fn).run #[]
          pure fs
        let bad ← run { fn := "f", ty := "T", arg := 0, leafDefault := true, childTys := ["T"] }
        check (bad.any (hasSub · "no arm for the constructor `.wrap`")) s!"a constructor left to the default was accepted: {bad}"
        check (bad.any (hasSub · "`b : T` is ignored")) s!"an ignored child was accepted: {bad}"
        let strict ← run { fn := "f", ty := "T", arg := 0, childTys := ["T"] }
        check (strict.any (hasSub · "a default arm")) s!"a default arm was accepted: {strict}"
        let good ← run { fn := "g", ty := "T", arg := 0, childTys := ["T"] }
        check good.isEmpty s!"a total function was rejected: {good}" }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  lintGroup ::
  []

end Tests.Lint
