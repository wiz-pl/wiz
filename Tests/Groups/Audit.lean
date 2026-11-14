import Wiz
import Tests.Harness
import Tests.Elab

/-!
# Soundness audit, second pass: tests

* levels: `Level.normalize`, `equiv`, `le`, `isNeverZero`, `toNat?`, `instParams` against
  the meaning of a level (a number for every assignment of its parameters), exhaustively
  over small levels;
* templates: the kernel's closed description templates and the types of the eliminators'
  arguments are well typed (a wrong de Bruijn index in one is not re-checked by anything);
* arithmetic: the native operations of the kernel against the Prelude's definitions (the
  Prelude without its `builtin nat.*` lines), and compiled code (C, LLVM) and `#eval`
  against Lean's `Nat`; the word natives of `lib/Word.wiz` against their definitions;
* paradoxes: Hurkens, Girard, Berardi and Russell attempts, each rejected.

`lake test -- '=audit'` runs the small version; `.lake/build/bin/tests --audit-long` the
long one (larger grids, more widths, random values).
-/

set_option compiler.extract_closed false

open Wiz

namespace Tests.Audit

/-! ## Levels -/

/-- The meaning of a level: its value when `u`, `v` are `ρ.1`, `ρ.2`. -/
def lvlSem (ρ : Nat × Nat) : Level → Nat
  | .zero => 0
  | .succ l => lvlSem ρ l + 1
  | .max a b => Nat.max (lvlSem ρ a) (lvlSem ρ b)
  | .imax a b => if lvlSem ρ b == 0 then 0 else Nat.max (lvlSem ρ a) (lvlSem ρ b)
  | .param n => if n == "u" then ρ.1 else ρ.2
  | .mvar _ => 0
  -- (a hole is an opaque atom: it is never assigned, so any value will do)
  | .hole => 0

mutual
partial def atomSem (ρ : Nat × Nat) : Level.Atom → Nat
  | .const => 0
  | .param n => if n == "u" then ρ.1 else ρ.2
  | .mvar _ => 0
  | .hole => 0
  | .imax a b => if nfSem ρ b == 0 then 0 else Nat.max (nfSem ρ a) (nfSem ρ b)
/-- The meaning of a normal form: the maximum of `atom + offset`. -/
partial def nfSem (ρ : Nat × Nat) (n : Level.NF) : Nat :=
  n.foldl (fun m (a, k) => Nat.max m (atomSem ρ a + k)) 0
end

def grid (n : Nat) : List (Nat × Nat) := (List.range n).flatMap fun a => (List.range n).map fun b => (a, b)

def grow (ls : List Level) : List Level :=
  ls ++ ls.map .succ ++ (ls.flatMap fun a => ls.map fun b => Level.max a b) ++
    (ls.flatMap fun a => ls.map fun b => Level.imax a b)

/-- All levels of depth ≤ 1 (24) and ≤ 2 (1200) over `0`, `u`, `v`. -/
def levels1 : List Level := grow [.zero, .param "u", .param "v"]
def levels2 : List Level := grow levels1

def hasImax : Level → Bool
  | .succ l => hasImax l
  | .max a b => hasImax a || hasImax b
  | .imax _ _ => true
  | _ => false

def showL (l : Level) : String := toString l

/-- One level: its normal form, `isNeverZero` and `toNat?` mean what the level means. -/
def checkLevel (l : Level) : Except String Unit := do
  let nf := l.normalize
  for ρ in grid 4 do
    unless nfSem ρ nf == lvlSem ρ l do
      throw s!"normalize {showL l}: the normal form is {nfSem ρ nf} at {ρ}, the level is {lvlSem ρ l}"
  if l.isNeverZero then
    if let some ρ := (grid 4).find? fun ρ => lvlSem ρ l == 0 then
      throw s!"isNeverZero {showL l}, but it is 0 at {ρ}"
  for (a, b) in [(0, 0), (1, 0), (0, 2), (3, 1)] do
    let closed := l.instParams ["u", "v"] [Level.ofNat a, Level.ofNat b]
    unless closed.toNat? == some (lvlSem (a, b) l) do
      throw s!"toNat? of {showL l} at {(a, b)}: {closed.toNat?}, expected {lvlSem (a, b) l}"

/-- A pair: `equiv` and `le` hold only when they hold at every assignment (soundness).
Returns whether `equiv` said yes, and whether the two are equal on the grid. -/
def checkPair (a b : Level) : Except String (Bool × Bool) := do
  let g := grid 5
  let eq := Level.equiv a b
  let semEq := g.all fun ρ => lvlSem ρ a == lvlSem ρ b
  if eq && !semEq then throw s!"equiv {showL a} {showL b}, but they differ"
  if Level.le a b then
    if let some ρ := g.find? fun ρ => lvlSem ρ a > lvlSem ρ b then
      throw s!"le {showL a} {showL b}, but {lvlSem ρ a} > {lvlSem ρ b} at {ρ}"
  pure (eq, semEq)

/-- Substitution is simultaneous and commutes with the meaning. -/
def checkSubst (l a b : Level) : Except String Unit := do
  for ρ in grid 3 do
    let lhs := lvlSem ρ (l.instParams ["u", "v"] [a, b])
    let rhs := lvlSem (lvlSem ρ a, lvlSem ρ b) l
    unless lhs == rhs do throw s!"instParams {showL l} [u := {showL a}, v := {showL b}] at {ρ}: {lhs}, expected {rhs}"

/-- `stride`: every `stride`-th level of `levels2` on the right-hand side (1 = all pairs). -/
def levelPairs (stride : Nat) : IO Unit := do
  let ls := levels2.toArray
  let mut yes := 0
  let mut missedPlain := 0
  let mut missedImax := 0
  for a in ls do
    for j in [0:ls.size] do
      if j % stride != 0 then continue
      let b := ls[j]!
      match checkPair a b with
      | .error e => throw (IO.userError e)
      | .ok (eq, semEq) =>
        if eq then yes := yes + 1
        if semEq && !eq then
          if hasImax a || hasImax b then missedImax := missedImax + 1 else missedPlain := missedPlain + 1
  IO.println s!"    ({ls.size} × {(ls.size + stride - 1) / stride} pairs: {yes} equivalent; equal on the grid but not found: {missedPlain} without imax, {missedImax} with)"
  check (yes > 100) "too few equivalent pairs: the test is vacuous"
  -- complete without `imax` (the claim in `Level.lean`)
  check (missedPlain == 0) s!"{missedPlain} equal pairs without imax were not found equivalent"

/-! ## Templates -/

def errorsOf (s : CommandState ZeroOneMany) (input : String) : Array String :=
  (s.messages.filter (·.severity == .error)).map fun m => m.render input

def expectOk (what : String) (s : CommandState ZeroOneMany) (input : String) : IO Unit := do
  let errs := errorsOf s input
  unless errs.isEmpty do throw (IO.userError s!"{what}: unexpected errors:\n{"\n".intercalate errs.toList}")

def sortName (v : Nat) : String := if v == 0 then "Prop" else if v == 1 then "Type" else s!"Type {v - 1}"

/-- Replace every occurrence of the closed term `pat` (not under a binder that it would
see: it is closed) by `rep`. -/
partial def replaceTm (pat rep : Term ZeroOneMany) (t : Term ZeroOneMany) : Term ZeroOneMany :=
  if t == pat then rep else Id.run (t.mapChildrenM (fun l => pure l) fun _ c => pure (replaceTm pat rep c))

/-- The closed templates (`Templates.lean`) as definitions with the types they are meant to
have, written in the surface language (names, not indices) and checked by `addDecl`. -/
def closedTemplates (l v : Nat) : IO (Globals ZeroOneMany) := do
  let tyI := sortName (l + 1)
  let big (n : Nat) := sortName (n + 1)
  let lv : Level := Level.ofNat l
  let vv : Level := Level.ofNat v
  -- a template applies the earlier ones as terms (`(fun I D => …) I E X i`: a redex the
  -- kernel evaluates but could not infer a type for): here they are the constants
  let foldInterp (t : Term ZeroOneMany) : Term ZeroOneMany := replaceTm (Templates.interpTm lv) (.const "T.interp" []) t
  let fold (t : Term ZeroOneMany) : Term ZeroOneMany :=
    replaceTm (Templates.interpTm lv) (.const "T.interp" []) (replaceTm (Templates.allTm lv vv) (.const "T.all" []) t)
  let step (g : Globals ZeroOneMany) (tyName tySrc : String) (declName : Name) (tm : Term ZeroOneMany) :
      IO (Globals ZeroOneMany) := do
    let s := runFrontend (R := ZeroOneMany) tySrc { globals := g }
    expectOk tyName s tySrc
    -- checked erased: the templates project fields whose quantity is a variable (`xs.1` with
    -- `xs : (%q s : S) × …`), which `infer` allows only in an erased position. `interp` and
    -- `All` are types; for `hyps` and `map` this means the kernel does not account for the
    -- usage inside them (audit note, T-qty)
    let tm' := if declName == "T.interp" then tm else if declName == "T.all" then foldInterp tm else fold tm
    let ctx : Ctx ZeroOneMany := { globals := s.globals, erased := true }
    -- (P2) the templates are kernel-built raw terms: mark them as the elaborator would, as
    -- every declaration is marked before the kernel. First without the requirement (the
    -- pass checks nothing), then the real check of the marked term.
    let tyv := ctx.eval (.const tyName [])
    let ctx0 : Ctx ZeroOneMany := { ctx with globals := { s.globals with lazyProofs := false } }
    match Wiz.check ctx0 tm' tyv with
    | .error e => throw (IO.userError s!"{declName} (l = {l}, v = {v}) does not have the type {tySrc}: {e}")
    | .ok _ =>
      let tm'' := Mark.check ctx tm' tyv
      match Wiz.check ctx tm'' tyv with
      | .ok _ => pure (s.globals.insert { name := declName, type := .const tyName [], value := some tm'' })
      | .error e => throw (IO.userError s!"{declName} (l = {l}, v = {v}) does not have the type {tySrc}: {e}")
  let g ← step {} "InterpTy"
    s!"def InterpTy : {big (l + 1)} := (I : {tyI}) → Desc I → (I → {tyI}) → I → {tyI}"
    "T.interp" (Templates.interpTm lv)
  let g ← step g "AllTy"
    (s!"def AllTy : {big (Nat.max (l + 1) v)} := (I : {tyI}) → (D : Desc I) → (X : I → {tyI}) → " ++
     s!"(P : (i : I) → X i → {sortName v}) → (i : I) → T.interp I D X i → {sortName (Nat.max (l + 1) v)}")
    "T.all" (Templates.allTm lv vv)
  let g ← step g "HypsTy"
    (s!"def HypsTy : {big (Nat.max (l + 1) v)} := (I : {tyI}) → (D : Desc I) → (X : I → {tyI}) → " ++
     s!"(P : (i : I) → X i → {sortName v}) → (f : (i : I) → (x : X i) → P i x) → (i : I) → " ++
     "(xs : T.interp I D X i) → T.all I D X P i xs")
    "T.hyps" (Templates.hypsTm lv vv)
  step g "MapTy"
    (s!"def MapTy : {big (l + 1)} := (I : {tyI}) → (D : Desc I) → (X : I → {tyI}) → (Y : I → {tyI}) → " ++
     "(f : (i : I) → X i → Y i) → (i : I) → T.interp I D X i → T.interp I D Y i")
    "T.map" (Templates.mapTm lv)

/-- The types of the eliminators' arguments (`Conv.lean`): evaluated at variables, quoted,
and checked to be types. `concrete`: the description is `rec i₀ (ret i₀)` instead of a
variable (see `scaseMethodTy` below). -/
def argumentTypes (l v : Nat) (concrete : Bool) : IO Unit := do
  let g : Globals ZeroOneMany := {}
  let lv : Level := Level.ofNat l
  let vv : Level := Level.ofNat v
  let w : ZeroOneMany := .many
  let q := QPoly.const w
  let isType (what : String) (ctx : Ctx ZeroOneMany) (ty : VTy ZeroOneMany) : IO Unit :=
    match checkType ctx (quote g ctx.lvl ty) with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"{what} (l = {l}, v = {v}, concrete = {concrete}) is not a type: {e}")
  let c0 : Ctx ZeroOneMany := { globals := g }
  let c1 := c0.bind "I" q (.sort (.succ lv))
  let I : Val ZeroOneMany := Val.var 0
  let c1 := c1.bind "i₀" q I
  let dTm : Term ZeroOneMany := .drec (.qlit .many) (.var 0) (.dret (.var 0))
  let c2 := if concrete then c1.define "D" q (.desc lv I) (c1.eval dTm) else c1.bind "D" q (.desc lv I)
  let D : Val ZeroOneMany := if concrete then c1.eval dTm else Val.var 2
  -- Desc.elim
  let dm := delimMotiveTy lv vv I w
  isType "delimMotiveTy" c1 dm
  let cP := c1.bind "P" q dm
  let (ta, tb, tc, th) := delimMethodTys g lv vv I (Val.var 2) w
  isType "delim mret" cP ta
  isType "delim marg" cP tb
  isType "delim mrec" cP tc
  isType "delim mhrec" cP th
  -- ind, sfix, scase
  let m := indMotiveTy g lv vv I D w
  isType "indMotiveTy" c2 m
  let c3 := c2.bind "P" q m
  let P : Val ZeroOneMany := Val.var 3
  isType "indMethodTy" c3 (indMethodTy g lv vv I D P w)
  isType "sfixFunTy" c3 (sfixFunTy g lv vv I D P w)
  let c4 := c3.bind "s" q .size
  -- `(xs : ⟦D⟧ (μ^j D) i) → P i (con xs)` puts `con xs` where a `μ^∞ D i` is expected: that
  -- needs `⟦D⟧ (μ^j D) i ≤ ⟦D⟧ (μ^∞ D) i`, which subtyping finds only once `⟦D⟧` computes.
  -- With a variable for `D` the kernel's own checker rejects this type (recorded in the
  -- audit note, T-scase); it holds for every concrete description
  if concrete then isType "scaseMethodTy" c4 (scaseMethodTy g lv vv I D P (Val.var 4) (.qlit .many))
  else match checkType c4 (quote g c4.lvl (scaseMethodTy g lv vv I D P (Val.var 4) (.qlit .many))) with
    | .ok _ => throw (IO.userError "scaseMethodTy now checks with a variable description: update the audit note (T-scase)")
    | .error _ => pure ()
  -- coit, scofix
  let st := coitStateTy lv I w
  isType "coitStateTy" c2 st
  let c3' := c2.bind "S" q st
  isType "coitStepTy" c3' (coitStepTy g lv I D (Val.var 3) w)
  isType "scofixFunTy" c3' (scofixFunTy g lv I D (Val.var 3) w)

/-! ## Native arithmetic against the definitions -/

/-- A linear congruential generator. -/
def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

/-- `n` random numbers below `bound`. -/
def randoms (seed n bound : Nat) : List Nat := Id.run do
  let mut s := seed
  let mut out := []
  for _ in [0:n] do
    s := next s
    let hi := s
    s := next s
    out := ((hi * 18446744073709551616 + s) % bound) :: out
  return out

/-- The Prelude up to its arithmetic, without the `builtin nat.*` registrations of the
operations: numerals stay (`nat`, `nat.zero`, `nat.succ`), every operation is its
definition. -/
def definitionsOnly : IO String := do
  let p ← IO.FS.readFile "lib/Prelude.wiz"
  let lines := (p.splitOn "\n").takeWhile fun l => !l.startsWith "builtin nat.log2"
  let keep := lines.filter fun l =>
    !(l.startsWith "builtin nat." && !l.startsWith "builtin nat.zero" && !l.startsWith "builtin nat.succ")
  check (lines.length - keep.length == 14) s!"expected to remove 14 registrations, removed {lines.length - keep.length}"
  pure ("\n".intercalate keep ++ "\n")

structure Op where
  name : String
  key : String
  arity : Nat

def natOps : List Op :=
  [⟨"Nat.pred", "nat.pred", 1⟩, ⟨"Nat.log2", "nat.log2", 1⟩, ⟨"Nat.add", "nat.add", 2⟩, ⟨"Nat.sub", "nat.sub", 2⟩,
   ⟨"Nat.mul", "nat.mul", 2⟩, ⟨"Nat.div", "nat.div", 2⟩, ⟨"Nat.mod", "nat.mod", 2⟩, ⟨"Nat.pow", "nat.pow", 2⟩,
   ⟨"Nat.land", "nat.land", 2⟩, ⟨"Nat.lor", "nat.lor", 2⟩, ⟨"Nat.xor", "nat.xor", 2⟩,
   ⟨"Nat.shiftLeft", "nat.shiftLeft", 2⟩, ⟨"Nat.shiftRight", "nat.shiftRight", 2⟩,
   ⟨"Nat.beq", "nat.beq", 2⟩, ⟨"Nat.lt", "nat.blt", 2⟩]

/-- What the kernel computes natively (`natNative?`; comparisons as the kernel does them),
as a Wiz term. -/
def nativeResult (op : Op) (args : Array Nat) : String :=
  match natNative? op.key args, op.key, args with
  | some n, _, _ => toString n
  | none, "nat.beq", #[a, b] => if a == b then "Bool.true" else "Bool.false"
  | none, "nat.blt", #[a, b] => if a < b then "Bool.true" else "Bool.false"
  | _, _, _ => "?"

/-- The points an operation is tried at, small enough to run its definition in unary. -/
def smallPoints (op : Op) (long : Bool) : List (Array Nat) :=
  let pairs (as bs : List Nat) : List (Array Nat) := as.flatMap fun a => bs.map fun b => #[a, b]
  let r (seed n bound : Nat) := randoms seed n bound
  match op.key with
  | "nat.pred" | "nat.log2" => ((List.range 34) ++ (if long then r 1 40 600 else [])).map (#[·])
  | "nat.pow" => pairs (List.range 5) (List.range 5) ++ (if long then pairs [0, 1, 2, 3, 7, 10] [0, 1, 2, 3] else [])
  | "nat.div" | "nat.mod" =>
    pairs [0, 1, 2, 3, 7, 8, 9, 20, 21] [0, 1, 2, 3, 7, 10, 25] ++ (if long then pairs (r 2 14 150) (0 :: r 3 8 40) else [])
  | "nat.land" | "nat.lor" | "nat.xor" =>
    pairs [0, 1, 2, 3, 5, 6, 12, 15, 16] [0, 1, 2, 3, 5, 6, 12, 15, 16] ++ (if long then pairs (r 4 8 64) (r 5 8 64) else [])
  | "nat.shiftLeft" | "nat.shiftRight" =>
    pairs [0, 1, 3, 5, 16, 21] (List.range 5) ++ (if long then pairs (r 6 8 60) [0, 1, 2, 3, 5, 7] else [])
  | "nat.mul" => pairs [0, 1, 2, 3, 5, 8, 13] [0, 1, 2, 3, 5, 8, 13] ++ (if long then pairs (r 7 12 40) (r 8 12 40) else [])
  | "nat.beq" | "nat.blt" => pairs [0, 1, 2, 3, 7] [0, 1, 2, 3, 7] ++ (if long then pairs (r 9 12 50) (r 10 12 50) else [])
  | _ => pairs [0, 1, 2, 3, 5, 8, 13] [0, 1, 2, 3, 5, 8, 13] ++ (if long then pairs (r 11 20 300) (r 12 20 300) else [])

/-- `def tN : op a b = r := refl r` for every point, `r` the native result: checked with
the definitions only (`native := false`), each line is "the definition computes what the
native operation does"; with the Prelude, a control. -/
def definitionsAgree (native long : Bool) : IO Unit := do
  let defs ← definitionsOnly
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let loader : Name → Option String := fun m =>
    if m == "NatDefs" then some defs else if m == "Prelude" then some prelude else none
  let mut total := 0
  for op in natOps do
    let pts := smallPoints op long
    let mut src := if native then "import Prelude\n" else "import NatDefs\n"
    let mut i := 0
    for p in pts do
      let r := nativeResult op p
      let args := " ".intercalate (p.toList.map toString)
      src := src ++ s!"def t{i} : {op.name} {args} = {r} := refl {r}\n"
      i := i + 1
    let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
    let errs := errorsOf s src
    unless errs.isEmpty do
      let lines := (src.splitOn "\n").toArray
      let shown := errs.toList.take 5 |>.map fun e =>
        let ln := (e.splitOn ":")[0]!.toNat!
        s!"{lines[ln - 1]!}\n        {e}"
      throw (IO.userError s!"{op.name}: {errs.size} of {pts.length} points disagree with the native result:\n{"\n".intercalate shown}")
    total := total + pts.length
  IO.println s!"    ({total} points)"

/-! ### Compiled code and `#eval` against Lean's `Nat` -/

def pow2 (n : Nat) : Nat := 2 ^ n

def edgeValues (long : Bool) : List Nat :=
  let base := [0, 1, 2, 3, pow2 31, pow2 32 - 1, pow2 32, pow2 32 + 1, pow2 62, pow2 63 - 1, pow2 63, pow2 64 - 1, pow2 64,
    pow2 64 + 1, pow2 65]
  if long then base ++ [7, pow2 31 - 1, pow2 63 + 1, pow2 65 + 12345, pow2 127 + 5, 10 ^ 30, pow2 128 - 1, pow2 128] ++
    randoms 21 6 (pow2 32) ++ randoms 22 8 (pow2 64) ++ randoms 23 8 (pow2 130)
  else base

def shiftAmounts : List Nat := [0, 1, 31, 32, 33, 63, 64, 65, 100]
def powBases : List Nat := [0, 1, 2, 3, 10, pow2 32, pow2 64 + 1]
def powExps : List Nat := [0, 1, 2, 3, 5, 64]

def wizList (xs : List Nat) : String := xs.foldr (fun x acc => s!"(.cons {x} {acc})") ".nil"
/-- A list as compiled code and `#eval` print it. -/
def printedList (xs : List Nat) : String :=
  if xs.isEmpty then ".nil" else
  String.intercalate " (" (xs.map fun x => s!".cons {x}") ++ " .nil" ++ String.ofList (List.replicate (xs.length - 1) ')')

/-- The operands come from lists the program walks at run time, so nothing is folded
when it is compiled. -/
def arithProgram (long : Bool) : String :=
  "import Prelude\n" ++
  "def app2 : List Nat → List Nat → List Nat\n  | .nil, ys => ys\n  | .cons x xs, ys => .cons x (app2 xs ys)\n" ++
  "def row (f : Nat → Nat → Nat) (a : Nat) : List Nat → List Nat → List Nat\n  | .nil, rest => rest\n" ++
  "  | .cons b bs, rest => .cons (f a b) (row f a bs rest)\n" ++
  "def table (f : Nat → Nat → Nat) (bs : List Nat) : List Nat → List Nat → List Nat\n  | .nil, rest => rest\n" ++
  "  | .cons a as, rest => row f a bs (table f bs as rest)\n" ++
  "def map1 (f : Nat → Nat) : List Nat → List Nat → List Nat\n  | .nil, rest => rest\n" ++
  "  | .cons a as, rest => .cons (f a) (map1 f as rest)\n" ++
  "def b2n : Bool → Nat\n  | .true => 1\n  | .false => 0\n" ++
  s!"def es : List Nat := {wizList (edgeValues long)}\n" ++
  s!"def ks : List Nat := {wizList shiftAmounts}\n" ++
  s!"def pbs : List Nat := {wizList powBases}\n" ++
  s!"def pes : List Nat := {wizList powExps}\n" ++
  "def main : List Nat :=\n" ++
  "  table Nat.add es es (table Nat.sub es es (table Nat.mul es es (table Nat.div es es (table Nat.mod es es\n" ++
  "  (table Nat.land es es (table Nat.lor es es (table Nat.xor es es\n" ++
  "  (table (fun a b => b2n (Nat.beq a b)) es es (table (fun a b => b2n (Nat.lt a b)) es es\n" ++
  "  (table (fun a b => b2n (Nat.le a b)) es es (table Nat.max es es\n" ++
  "  (table Nat.shiftLeft ks es (table Nat.shiftRight ks es (table (fun a b => b2n (Nat.testBit a b)) ks es\n" ++
  "  (table Nat.pow pes pbs\n" ++
  "  (map1 Nat.succ es (map1 Nat.pred es (map1 Nat.log2 es .nil))))))))))))))))))\n"

/-- The same table with Lean's `Nat`. -/
def arithExpected (long : Bool) : List Nat :=
  let es := edgeValues long
  let table (f : Nat → Nat → Nat) (bs as : List Nat) : List Nat := as.flatMap fun a => bs.map fun b => f a b
  let b2n (b : Bool) : Nat := if b then 1 else 0
  table (· + ·) es es ++ table (· - ·) es es ++ table (· * ·) es es ++ table (· / ·) es es ++
  table (fun a b => if b == 0 then a else a % b) es es ++
  table (· &&& ·) es es ++ table (· ||| ·) es es ++ table (· ^^^ ·) es es ++
  table (fun a b => b2n (a == b)) es es ++ table (fun a b => b2n (a < b)) es es ++
  table (fun a b => b2n (a ≤ b)) es es ++ table Nat.max es es ++
  table (· <<< ·) shiftAmounts es ++ table (· >>> ·) shiftAmounts es ++
  table (fun a b => b2n (a.testBit b)) shiftAmounts es ++
  table (· ^ ·) powExps powBases ++
  es.map (· + 1) ++ es.map (· - 1) ++ es.map Nat.log2

/-- Where two printed lists first differ (a message), for a readable failure. -/
def firstDifference (expected got : String) : String :=
  let e := (expected.splitOn " ").toArray
  let g := (got.splitOn " ").toArray
  match (List.range (Nat.min e.size g.size)).find? fun i => e[i]! != g[i]! with
  | some i => s!"first difference at token {i} (entry {i / 2}): expected {e[i]!}, got {g[i]!}"
  | none => s!"lengths differ: expected {e.size} tokens, got {g.size}"

/-- Elaborate `src` with `lib/` and return the frontend state (no errors allowed). -/
def elabLib (src : String) : IO (CommandState ZeroOneMany) := do
  let loader ← Elab.preludeLoader
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
  expectOk "program" s src
  pure s

/-- `main` compiled and run. `none`: no toolchain. -/
def compiled (src : String) (llvm : Bool) : IO (Option String) := do
  let s ← elabLib src
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir llvm (timeout := some 300) with
  | .ok v => pure (some v)
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then IO.println "    (skipped: no toolchain)"; pure none
    else throw (IO.userError e)

/-- What `#eval main` prints. -/
def evaluated (src : String) : IO String := do
  let s ← elabLib (src ++ "#eval main\n")
  match s.messages.toList.filter (·.severity == .info) |>.getLast? with
  | some m => pure m.text
  | none => throw (IO.userError "#eval printed nothing")

def sameOutput (what expected got : String) : IO Unit :=
  unless expected == got do throw (IO.userError s!"{what}: {firstDifference expected got}")

def arithCompiled (long llvm : Bool) : IO Unit := do
  let expected := printedList (arithExpected long)
  if let some got ← compiled (arithProgram long) llvm then
    sameOutput "compiled code against Lean's Nat" expected got
    IO.println s!"    ({(arithExpected long).length} results)"

def arithEval (long : Bool) : IO Unit := do
  sameOutput "#eval against Lean's Nat" (printedList (arithExpected long)) (← evaluated (arithProgram long))

/-! ### Words -/

/-- Values of a word of width `w`, as numbers below `2^w` (the program applies `ofNat`). -/
def wordValues (w : Nat) (long : Bool) : List Nat :=
  let m := pow2 w
  let base := [0, 1, 2, m / 2 - 1, m / 2, m / 2 + 1, m - 2, m - 1].map (· % m)
  (base ++ (if long then randoms (30 + w) 5 m else randoms (30 + w) 1 m)).eraseDups

def wordWidths (long : Bool) : List Nat :=
  if long then [1, 2, 7, 8, 16, 31, 32, 33, 62, 63, 64, 65, 127, 128] else [8, 32, 63, 64]

/-- Every operation of `lib/Word.wiz` that has a native implementation, on all pairs of
the values, for a width given at run time. -/
def wordProgram (ws : List (Nat × List Nat)) : String :=
  "import Word\n" ++
  "def b2n : Bool → Nat\n  | .true => 1\n  | .false => 0\n" ++
  "def ks : List Nat := .cons 0 (.cons 1 (.cons 7 (.cons 31 (.cons 63 (.cons 64 (.cons 200 .nil))))))\n" ++
  "def vs : List Nat := .cons 1 (.cons 8 (.cons 33 (.cons 64 (.cons 100 .nil))))\n" ++
  "def uPair (ω w : Nat) (a b : UIntN w) (rest : List Nat) : List Nat :=\n" ++
  "  .cons (UIntN.add a b).toNat (.cons (UIntN.sub a b).toNat (.cons (UIntN.mul a b).toNat\n" ++
  "  (.cons (UIntN.div a b).toNat (.cons (UIntN.mod a b).toNat (.cons (b2n (UIntN.beq a b))\n" ++
  "  (.cons (b2n (UIntN.lt a b)) (.cons (b2n (UIntN.le a b)) (.cons (UIntN.land a b).toNat\n" ++
  "  (.cons (UIntN.lor a b).toNat (.cons (UIntN.xor a b).toNat rest))))))))))\n" ++
  "def iPair (ω w : Nat) (a b : IntN w) (rest : List Nat) : List Nat :=\n" ++
  "  .cons (IntN.add a b).toNat (.cons (IntN.sub a b).toNat (.cons (IntN.mul a b).toNat\n" ++
  "  (.cons (IntN.div a b).toNat (.cons (IntN.rem a b).toNat (.cons (b2n (IntN.beq a b))\n" ++
  "  (.cons (b2n (IntN.lt a b)) (.cons (b2n (IntN.le a b)) (.cons (IntN.land a b).toNat\n" ++
  "  (.cons (IntN.lor a b).toNat (.cons (IntN.xor a b).toNat rest))))))))))\n" ++
  "def uShift (ω w : Nat) (a : UIntN w) : List Nat → List Nat → List Nat\n  | .nil, rest => rest\n" ++
  "  | .cons k ks, rest => .cons (UIntN.shiftLeft a k).toNat (.cons (UIntN.shiftRight a k).toNat\n" ++
  "      (.cons (b2n (UIntN.testBit a k)) (uShift w a ks rest)))\n" ++
  "def iShift (ω w : Nat) (a : IntN w) : List Nat → List Nat → List Nat\n  | .nil, rest => rest\n" ++
  "  | .cons k ks, rest => .cons (IntN.shiftLeft a k).toNat (.cons (IntN.shiftRight a k).toNat (iShift w a ks rest))\n" ++
  "def uResize (ω w : Nat) (a : UIntN w) : List Nat → List Nat → List Nat\n  | .nil, rest => rest\n" ++
  "  | .cons v vs, rest => .cons (UIntN.resize v a).toNat (.cons (IntN.resize v a.toIntN).toNat (uResize w a vs rest))\n" ++
  "def uOne (ω w : Nat) (a : UIntN w) (rest : List Nat) : List Nat :=\n" ++
  "  .cons (UIntN.neg a).toNat (.cons (UIntN.not a).toNat (.cons (b2n (UIntN.msb a))\n" ++
  "  (.cons (IntN.neg a.toIntN).toNat (.cons (IntN.not a.toIntN).toNat (.cons (b2n (IntN.isNeg a.toIntN))\n" ++
  "  (.cons (IntN.natAbs a.toIntN) (.cons (IntN.ofNeg w a.toNat).toNat (.cons (a.toIntN.toUIntN).toNat\n" ++
  "  (uShift w a ks (iShift w a.toIntN ks (uResize w a vs rest)))))))))))\n" ++
  "def uRow (ω w : Nat) (a : Nat) : List Nat → List Nat → List Nat\n  | .nil, rest => rest\n" ++
  "  | .cons b bs, rest => uPair w (UIntN.ofNat w a) (UIntN.ofNat w b) (iPair w (IntN.ofNat w a) (IntN.ofNat w b) (uRow w a bs rest))\n" ++
  "def uAll (ω w : Nat) (bs : List Nat) : List Nat → List Nat → List Nat\n  | .nil, rest => rest\n" ++
  "  | .cons a as, rest => uOne w (UIntN.ofNat w a) (uRow w a bs (uAll w bs as rest))\n" ++
  String.join (ws.map fun (w, xs) => s!"def xs{w} : List Nat := {wizList xs}\n") ++
  "def main : List Nat :=\n  " ++
  String.join (ws.map fun (w, _) => s!"uAll {w} xs{w} xs{w} (") ++ ".nil" ++ String.ofList (List.replicate ws.length ')') ++ "\n"

/-- Compiled words (the natives) against `#eval` (the definitions). -/
def wordsAgree (long llvm : Bool) : IO Unit := do
  for w in wordWidths long do
    let src := wordProgram [(w, wordValues w long)]
    let expected ← evaluated src
    if let some got ← compiled src llvm then
      sameOutput s!"width {w}: compiled natives against the definitions (#eval)" expected got

/-! ## The two kernels against each other

A type-directed generator: closed types (so no index needs shifting) and terms of a given
type, mostly well typed. For each sample the two kernels are compared on the verdict (the
type, or `error`) *and on normal forms*: of the term, of an equation between two terms of
the type (`vEq`), of an equation between two types (`vEqType`), and of a cast along a
hypothetical proof (`vCast`: the Π and Σ templates, `ULift`, data). -/

open Tests.Elab (MTm)

inductive GTy where
  | enum (k : Nat)
  | unit
  | nat
  /-- the global `Nat` (a glued definition) -/
  | glob
  | pi (q : ZeroOneMany) (a b : GTy)
  | sigma (q : ZeroOneMany) (a b : GTy)
  /-- `ULift.{1} A` -/
  | lift (a : GTy)
  /-- `ULift.{1} (#i = #j : Enum k)`: a boxed proof (or an empty type) -/
  | liftEq (k i j : Nat)
  /-- `(x : Enum k) → case x [B₀, …]` and the Σ: dependent, by large elimination -/
  | depPi (k : Nat) (bs : List GTy)
  | depSigma (k : Nat) (bs : List GTy)
  /-- the type of a binder the generator does not use -/
  | other
  deriving BEq, Inhabited

namespace GTy

partial def toM : GTy → MTm
  | enum k => .enum k
  | unit => .unit 0
  | nat => MTm.natTy
  | glob => .const "Nat"
  | pi q a b => .sorted 1 1 (if q == .many then .pi a.toM b.toM else .piq q a.toM b.toM)
  | sigma q a b => .sorted 1 1 (if q == .many then .sigma a.toM b.toM else .sigmaq q a.toM b.toM)
  | lift a => .ulift 1 1 a.toM
  | liftEq k i j => .ulift 0 1 (.eq (.enum k) (.tag k i) (.tag k j))
  | depPi k bs => .sorted 1 1 (.pi (.enum k) (.ecase (.univ 0) (.var 0) (bs.map toM)))
  | depSigma k bs => .sorted 1 1 (.sigma (.enum k) (.ecase (.univ 0) (.var 0) (bs.map toM)))
  | other => .unit 0

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

partial def gen (s : Nat) (depth : Nat) : GTy × Nat :=
  let s := lcg s
  let q : ZeroOneMany := match s / 31 % 6 with | 0 => .zero | 1 => .one | _ => .many
  let pick := s / 65536 % (if depth == 0 then 5 else 12)
  match pick with
  | 0 => (enum (s / 7 % 3 + 1), s)
  | 1 => (unit, s)
  | 2 => (nat, s)
  | 3 => (glob, s)
  | 4 => let k := s / 7 % 2 + 1; let i := s / 11 % k; (liftEq k i (if s / 13 % 4 == 0 then s / 17 % k else i), s)
  | 5 | 6 => let (a, s) := gen s (depth - 1); let (b, s) := gen s (depth - 1); (pi q a b, s)
  | 7 | 8 => let (a, s) := gen s (depth - 1); let (b, s) := gen s (depth - 1); (sigma q a b, s)
  | 9 => let (a, s) := gen s (depth - 1); (lift a, s)
  | 10 =>
    let (a, s) := gen s (depth - 1); let (b, s) := gen s (depth - 1)
    (depPi 2 [a, b], s)
  | _ =>
    let (a, s) := gen s (depth - 1); let (b, s) := gen s (depth - 1)
    (depSigma 2 [a, b], s)

/-- A term of type `ty` in a context of variables of the types `ctx` (innermost first). -/
partial def term (s : Nat) (depth : Nat) (ctx : List GTy) (ty : GTy) : MTm × Nat :=
  let s := lcg s
  let T := ty.toM
  let vars := (List.range ctx.length).filter fun i => ctx[i]! == ty
  let d := depth - 1
  let natLit (n : Nat) : MTm := (List.range n).foldl (fun acc _ => MTm.natSucc acc) MTm.natZero
  let intro (s : Nat) : MTm × Nat := match ty with
    | enum k => (.tag k (s / 7 % k), s)
    | unit | other => (.star, s)
    | nat => (natLit (s / 7 % 3), s)
    | glob => (if s / 7 % 2 == 0 then .const "zero" else .const "one", s)
    | pi _ a b => let (body, s) := term s d (a :: ctx) b; (.lam body, s)
    | sigma _ a b => let (x, s) := term s d ctx a; let (y, s) := term s d ctx b; (.pair x y, s)
    | lift a => let (x, s) := term s d ctx a; (.up x, s)
    | liftEq _ i j =>
      -- (an empty type has no closed term: use a hypothesis of it if there is one)
      if i == j then (.up .star, s) else
      (match vars.head? with | some v => .var v | none => .up .star, s)
    | depPi k bs =>
      let motive := MTm.ecase (.univ 0) (.var 0) (bs.map toM)
      let (brs, s) := bs.foldl (fun (acc, s) b => let (t, s) := term s d (enum k :: ctx) b; (acc ++ [t], s)) ([], s)
      (.lam (.ecase motive (.var 0) brs), s)
    | depSigma k bs =>
      let i := s / 7 % k
      let (y, s) := term s d ctx bs[i]!
      (.pair (.tag k i) y, s)
  if depth == 0 then
    (match vars.head? with
     | some v => if s / 3 % 2 == 0 then (.var v, s) else intro s
     | none => intro s)
  else match s / 65536 % 14 with
    | 0 | 1 | 2 | 3 => intro s
    | 4 => (match vars[s / 7 % (vars.length + 1)]? with | some v => (.var v, s) | none => intro s)
    | 5 =>
      -- a β-redex, at a binder of any quantity
      let (a, s) := gen s 1
      let (arg, s) := term s d ctx a
      let (body, s) := term s d (a :: ctx) ty
      let q : ZeroOneMany := match s / 31 % 5 with | 0 => .zero | 1 => .one | _ => .many
      (.app (.ann (.lam body) (if q == .many then .pi a.toM T else .piq q a.toM T)) arg, s)
    | 6 =>
      -- a projection of a pair (with an erased or linear first component, sometimes)
      let (b, s) := gen s 1
      let (x, s) := term s d ctx ty
      let (y, s) := term s d ctx b
      let q : ZeroOneMany := match s / 31 % 5 with | 0 => .zero | 1 => .one | _ => .many
      (if s / 3 % 2 == 0 then .fst (.ann (.pair x y) (.sigma T b.toM))
       else .snd (.ann (.pair y x) (if q == .many then .sigma b.toM T else .sigmaq q b.toM T)), s)
    | 7 => let (x, s) := term s d ctx ty; (.cast T T (.reflTy T) x, s)
    | 8 => let (x, s) := term s d ctx ty; (.down (.ann (.up x) (.ulift 1 1 T)), s)
    | 9 =>
      let k := s / 7 % 2 + 1
      let (brs, s) := (List.range k).foldl (fun (acc, s) _ => let (t, s) := term s d ctx ty; (acc ++ [t], s)) ([], s)
      let (sc, s) := term s d ctx (enum k)
      (.ecase T sc brs, s)
    | 10 => let (x, s) := term s d ctx ty; let (b, s) := term s d (ty :: ctx) ty; (.letE T x b, s)
    | 11 =>
      -- induction on a number, with a constant motive
      let (n, s) := term s d ctx nat
      let (m, s) := term s d (other :: other :: other :: ctx) ty
      (.ind 0 (.unit 0) MTm.natD 1 (MTm.lams 2 T) (MTm.lams 3 m) .star n, s)
    | 12 => let (x, s) := term s d ctx ty; (.app (.app (.const "idP" [1]) T) x, s)
    | _ =>
      -- through an empty hypothesis
      (match (List.range ctx.length).find? fun i => match ctx[i]! with | liftEq _ a b => a != b | _ => false with
       | some v => (.exfalso T (.down (.var v)), s)
       | none => intro s)

end GTy

/-- A term with its quantity *variables* replaced by ω: `Kernel.wiz` has only literal
quantities, and its templates use ω where the Lean ones pass a field's quantity on. -/
partial def dropQty : Term ZeroOneMany → Term ZeroOneMany
  | .pi x bi q a b s => .pi x bi (keep q) (dropQty a) (dropQty b) s
  | .sigma x q a b s => .sigma x (keep q) (dropQty a) (dropQty b) s
  | t => Id.run (t.mapChildrenM (fun l => pure l) fun _ c => pure (dropQty c))
where
  keep : Term ZeroOneMany → Term ZeroOneMany
    | .qlit q => .qlit q
    | _ => .qlit .many

/-- The Lean kernel's normal form of a closed term, printed like the Wiz kernel prints. -/
def leanNormal (t : MTm) : String :=
  let g := Elab.leanGlobals ()
  -- (P2) the query is marked first, as the Wiz side marks it (`kernelsAgree`); a term the
  -- pre-P2 kernel rejects is left as it is, as in `Elab.leanVerdict`
  let tm := if !(infer (R := ZeroOneMany) { globals := { g with lazyProofs := false } } t.toTerm).toBool then
      t.toTerm else (Mark.infer (R := ZeroOneMany) { globals := g } t.toTerm).1
  match MTm.ofTerm (dropQty (quote g 0 (eval g [] tm))) with
  | some m => m.pretty 0
  | none => "?"

/-- What to ask both kernels: a verdict (`true`) or a normal form. -/
abbrev Query := Bool × MTm

/-- The queries of one sample. Normal forms are asked only of terms the Lean kernel
accepts (an ill-typed term may not evaluate). -/
def sampleQueries (seed : Nat) (depth : Nat) : List Query × Nat :=
  let (ty, s) := GTy.gen seed depth
  let (ty', s) := GTy.gen s depth
  let (t, s) := GTy.term s depth [] ty
  let (t2, s) := GTy.term s depth [] ty
  let T := ty.toM
  let T' := ty'.toM
  let typed := MTm.ann t T
  let typed2 := MTm.ann t2 T
  let ok (m : MTm) : Bool := Elab.leanVerdict m != "error"
  let castFn := MTm.ann (.lam (.cast T T' (.var 0) t)) (.piq .zero (.eqTy T T') T')
  -- a normal form keeps a global folded or not depending on what forced it (the Lean
  -- kernel's `vDown` unfolds a glued value, the Wiz kernel's keeps it; a stuck equation
  -- shows its type as written in one and in weak head normal form in the other): the same
  -- value, printed differently. So normal forms are compared on terms without globals
  let pure (m : MTm) : Bool := (m.toWiz.splitOn ".const ").length == 1
  let qs : List Query := [(true, typed), (true, typed2), (true, castFn)] ++
    (if pure T && pure T' then [(false, .eqTy T T')] else []) ++
    (if ok typed && pure typed then [(false, typed)] else []) ++
    (if ok typed && ok typed2 && pure typed then [(true, .ann (.refl T t) (.eq T t t2))] else []) ++
    (if ok typed && ok typed2 && pure typed && pure typed2 then [(false, .eq T t t2)] else []) ++
    (if ok castFn && pure castFn then [(false, castFn)] else [])
  (qs, s)

def kernelQueries (n : Nat) : List Query := Id.run do
  let mut out := []
  let mut seed := 2026
  for i in [0:n] do
    let (qs, s) := sampleQueries seed (1 + i % 3)
    out := out ++ qs
    seed := s
  return out

def leanAnswer (q : Query) : String := if q.1 then Elab.leanVerdict q.2 else leanNormal q.2

/-! ### Hurkens' paradox as a core term

`star` is the universe that the paradox needs to contain itself. With `Prop` for it, the
term is ill typed. The Wiz kernel used to accept an *out-of-scope variable* as a term
`Prop : Prop` (finding K6), and with that for `star` it accepted the whole paradox, a
closed term of type `False`: the control that this encoding is the paradox. -/

inductive NTm where
  | v (x : String)
  | star
  | fls
  | pi (x : String) (a b : NTm)
  | lam (x : String) (b : NTm)
  | app (f a : NTm)
  deriving Inhabited

partial def NTm.toM (star : Nat → MTm) (scope : List String) : NTm → MTm
  | .v x => .var ((scope.idxOf? x).getD 9999)
  | .star => star scope.length
  | .fls => .pfalse
  | .pi x a b => .pi (a.toM star scope) (b.toM star (x :: scope))
  | .lam x b => .lam (b.toM star (x :: scope))
  | .app f a => .app (f.toM star scope) (a.toM star scope)

def hurkens (star : Nat → MTm) : MTm :=
  let v := NTm.v
  let app2 (f a b : NTm) := NTm.app (.app f a) b
  let arr (a b : NTm) := NTm.pi "_" a b
  let pw (x : NTm) := NTm.app (v "Pw") x
  let lams (xs : List String) (b : NTm) := xs.foldr NTm.lam b
  let tauSigma (x : NTm) := NTm.app (v "tau") (.app (v "sigma") x)
  let defs : List (String × NTm × NTm) := [
    ("Pw", arr .star .star, .lam "X" (arr (v "X") .star)),
    ("U", .star, .pi "X" .star (arr (arr (pw (pw (v "X"))) (v "X")) (pw (pw (v "X"))))),
    ("tau", arr (pw (pw (v "U"))) (v "U"),
      lams ["t", "X", "f", "p"] (.app (v "t") (.lam "x" (.app (v "p") (.app (v "f") (app2 (v "x") (v "X") (v "f"))))))),
    ("sigma", arr (v "U") (pw (pw (v "U"))), .lam "s" (app2 (v "s") (v "U") (v "tau"))),
    ("Delta", pw (v "U"),
      .lam "y" (arr (.pi "p" (pw (v "U")) (arr (app2 (v "sigma") (v "y") (v "p")) (.app (v "p") (tauSigma (v "y"))))) .fls)),
    ("Omega", v "U",
      .app (v "tau") (.lam "p" (.pi "x" (v "U") (arr (app2 (v "sigma") (v "x") (v "p")) (.app (v "p") (v "x")))))),
    ("D", .star,
      .pi "p" (pw (v "U")) (arr (app2 (v "sigma") (v "Omega") (v "p")) (.app (v "p") (tauSigma (v "Omega"))))),
    ("lem1", .pi "p" (pw (v "U")) (arr (.pi "x" (v "U") (arr (app2 (v "sigma") (v "x") (v "p")) (.app (v "p") (v "x"))))
        (.app (v "p") (v "Omega"))),
      lams ["p", "H1"] (app2 (v "H1") (v "Omega") (.lam "x" (.app (v "H1") (tauSigma (v "x")))))),
    ("lem2", arr (v "D") .fls,
      app2 (v "lem1") (v "Delta") (lams ["x", "H2", "H3"]
        (.app (app2 (v "H3") (v "Delta") (v "H2")) (.lam "p" (.app (v "H3") (.lam "y" (.app (v "p") (tauSigma (v "y"))))))))),
    ("lem3", v "D", .lam "p" (.app (v "lem1") (.lam "y" (.app (v "p") (tauSigma (v "y"))))))]
  let rec go (scope : List String) : List (String × NTm × NTm) → MTm
    | [] => (NTm.app (v "lem2") (v "lem3")).toM star scope
    | (x, ty, val) :: rest => .letE (ty.toM star scope) (val.toM star scope) (go (x :: scope) rest)
  go [] defs

/-- Terms on which the kernels are known to differ or did differ (findings K1, K6), with
what each kernel must answer: `(query, Lean, Wiz)`. -/
def pinned : List (String × Query × String × String) :=
  let propPi (q : ZeroOneMany) : MTm := .sorted 0 0 (.piq q .ptrue .ptrue)
  -- (`ULift.{k,l} A`: `k` the content's sort, `l` the lifted one; `Sort n : Sort (n+1)`)
  [("Girard through ULift: Type lowered to Prop", (true, .ulift 2 0 (.univ 0)), "error", "error"),
   ("… Type 1 lowered to Type", (true, .ulift 3 1 (.univ 1)), "error", "error"),
   ("… a field of a small type over all small types", (true, .ann (.darg (.ulift 2 1 (.univ 0)) (.lam (.dret .star))) (.desc 0 (.unit 0))), "error", "error"),
   ("ULift raises", (true, .ulift 2 2 (.univ 0)), "U1", "U1"),
   ("K6: a variable out of scope", (true, .var 0), "error", "error"),
   ("K6: … under a binder", (true, .ann (.lam (.var 3)) (.pi (.unit 0) .prop)), "error", "error"),
   ("K6: Hurkens with an out-of-scope variable as Prop : Prop", (true, hurkens fun d => .var d), "error", "error"),
   ("Hurkens with Prop for the universe", (true, hurkens fun _ => .prop), "error", "error"),
   ("ULift against another former", (false, .eqTy (.ulift 1 1 (.enum 2)) MTm.natTy), "False", "False"),
   ("… is refuted", (true, .ann (.lam (.var 0)) (.pi (.eqTy (.ulift 1 1 (.enum 2)) (.unit 0)) .pfalse)),
     "(x0 : False) → False", "(x0 : False) → False"),
   -- K1: the Lean kernel ignores quantities at a Π that is a proposition; the Wiz kernel compares them
   ("K1 (subtyping): a proof with an erased argument where an unrestricted one is expected: both accept",
     (true, .ann (.lam (.var 0)) (.pi (propPi .zero) (propPi .many))),
     "(x0 : (x0 :0 True) → True) → (x1 : True) → True", "(x0 : (x0 :0 True) → True) → (x1 : True) → True"),
   -- K9: a linear variable that is never used (the Wiz kernel accepted it: `popUsage` on an empty usage list)
   ("K9: a linear variable must be used", (true, .ann (.lam (.univ 0)) (.piq .one (.univ 1) (.univ 1))), "error", "error"),
   ("K9: … under another binder", (true, .ann (.lam (.lam (.var 0))) (.piq .one (.univ 1) (.pi (.univ 1) (.univ 1)))), "error", "error"),
   -- (its sibling, found by kernel-lint: joining the branches of a case with a shorter usage list)
   ("K9: a linear variable used in one branch only", (true, .ann (.lam (.lam (.ecase (.enum 2) (.var 1) [.var 0, .tag 2 0])))
       (.pi (.enum 2) (.piq .one (.enum 2) (.enum 2)))), "error", "error"),
   ("K9: … in the other branch only", (true, .ann (.lam (.lam (.ecase (.enum 2) (.var 1) [.tag 2 0, .var 0])))
       (.pi (.enum 2) (.piq .one (.enum 2) (.enum 2)))), "error", "error")]

def templatePairs : List (String × Term ZeroOneMany) :=
  let L := Level.ofNat
  [("interpTm 0", Templates.interpTm (L 0)), ("interpTm 1", Templates.interpTm (L 1)),
   ("allTm 0 0", Templates.allTm (L 0) (L 0)), ("allTm 0 1", Templates.allTm (L 0) (L 1)),
   ("allTm 1 3", Templates.allTm (L 1) (L 3)),
   ("hypsTm 0 0", Templates.hypsTm (L 0) (L 0)), ("hypsTm 0 2", Templates.hypsTm (L 0) (L 2)),
   ("mapTm 0", Templates.mapTm (L 0)), ("mapTm 1", Templates.mapTm (L 1))]

/-- (21x) Drop the description fields' quantities and every `sigmaQ` to the `Σ` at ω, as
the Lean side's `dropQty` does before `MTm.ofTerm`: the audit compares the kernels modulo
quantities (the differential `MTm` can write a literal, and the templates at a method's
quantity variable print as `%q` in Kernel.wiz and as `Σ` at ω after `dropQty`). -/
def dropQSrc : String :=
  "mutual\n" ++
  "partial def dropQTm : Tm → Tm\n" ++
  "  | .var i => .var i\n" ++
  "  | .univ n => .univ n\n" ++
  "  | .prop => .prop\n" ++
  "  | .sortL l => .sortL l\n" ++
  "  | .pi q i j a b => .pi q i j (dropQTm a) (dropQTm b)\n" ++
  "  | .lam b => .lam (dropQTm b)\n" ++
  "  | .app f a => .app (dropQTm f) (dropQTm a)\n" ++
  "  | .letE ty v b => .letE (dropQTm ty) (dropQTm v) (dropQTm b)\n" ++
  "  | .ann t ty => .ann (dropQTm t) (dropQTm ty)\n" ++
  "  | .letq q ty v b => .letq q (dropQTm ty) (dropQTm v) (dropQTm b)\n" ++
  "  | .sigma q i j a b => .sigma q i j (dropQTm a) (dropQTm b)\n" ++
  "  | .sigmaQ _ i j a b => .sigma .qw i j (dropQTm a) (dropQTm b)\n" ++
  "  | .pair a b => .pair (dropQTm a) (dropQTm b)\n" ++
  "  | .fst p => .fst (dropQTm p)\n" ++
  "  | .snd p => .snd (dropQTm p)\n" ++
  "  | .unit n => .unit n\n" ++
  "  | .star => .star\n" ++
  "  | .empty n => .empty n\n" ++
  "  | .ptrue => .ptrue\n" ++
  "  | .pfalse => .pfalse\n" ++
  "  | .exfalso m t => .exfalso (dropQTm m) (dropQTm t)\n" ++
  "  | .letUnit u b => .letUnit (dropQTm u) (dropQTm b)\n" ++
  "  | .enum k => .enum k\n" ++
  "  | .tag k i => .tag k i\n" ++
  "  | .ecase m s bs => .ecase (dropQTm m) (dropQTm s) (dropQTms bs)\n" ++
  "  | .eq A a b => .eq (dropQTm A) (dropQTm a) (dropQTm b)\n" ++
  "  | .eqTy A B => .eqTy (dropQTm A) (dropQTm B)\n" ++
  "  | .eqRefl A a => .eqRefl (dropQTm A) (dropQTm a)\n" ++
  "  | .tyRefl X => .tyRefl (dropQTm X)\n" ++
  "  | .coe A B e t => .coe (dropQTm A) (dropQTm B) (dropQTm e) (dropQTm t)\n" ++
  "  | .subst A a P p b e => .subst (dropQTm A) (dropQTm a) (dropQTm P) (dropQTm p) (dropQTm b) (dropQTm e)\n" ++
  "  | .qty => .qty\n" ++
  "  | .qlit q => .qlit q\n" ++
  "  | .descr l I => .descr l (dropQTm I)\n" ++
  "  | .dret i => .dret (dropQTm i)\n" ++
  "  | .darg q S D => .darg (dropQTm q) (dropQTm S) (dropQTm D)\n" ++
  "  | .drec q j D => .drec (dropQTm q) (dropQTm j) (dropQTm D)\n" ++
  "  | .dhrec q H j D => .dhrec (dropQTm q) (dropQTm H) (dropQTm j) (dropQTm D)\n" ++
  "  | .delim v P a b c h D => .delim v (dropQTm P) (dropQTm a) (dropQTm b) (dropQTm c) (dropQTm h) (dropQTm D)\n" ++
  "  | .mu l I D i => .mu l (dropQTm I) (dropQTm D) (dropQTm i)\n" ++
  "  | .con x => .con (dropQTm x)\n" ++
  "  | .size => .size\n" ++
  "  | .szInf => .szInf\n" ++
  "  | .szSuc s => .szSuc (dropQTm s)\n" ++
  "  | .sizeLt s => .sizeLt (dropQTm s)\n" ++
  "  | .mus l I D i s => .mus l (dropQTm I) (dropQTm D) (dropQTm i) (dropQTm s)\n" ++
  "  | .sfix l I D v P f s i x => .sfix l (dropQTm I) (dropQTm D) v (dropQTm P) (dropQTm f) (dropQTm s) (dropQTm i) (dropQTm x)\n" ++
  "  | .scase l q I D v P m s i x => .scase l q (dropQTm I) (dropQTm D) v (dropQTm P) (dropQTm m) (dropQTm s) (dropQTm i) (dropQTm x)\n" ++
  "  | .nu l I D i s => .nu l (dropQTm I) (dropQTm D) (dropQTm i) (dropQTm s)\n" ++
  "  | .out x => .out (dropQTm x)\n" ++
  "  | .cocon x => .cocon (dropQTm x)\n" ++
  "  | .scofix l I D A f s i a => .scofix l (dropQTm I) (dropQTm D) (dropQTm A) (dropQTm f) (dropQTm s) (dropQTm i) (dropQTm a)\n" ++
  "  | .coit l I D S st i s => .coit l (dropQTm I) (dropQTm D) (dropQTm S) (dropQTm st) (dropQTm i) (dropQTm s)\n" ++
  "  | .ind l I D v P m i x => .ind l (dropQTm I) (dropQTm D) v (dropQTm P) (dropQTm m) (dropQTm i) (dropQTm x)\n" ++
  "  | .const n ps ls v ty => .const n ps ls v ty\n" ++
  "  | .axiomC n ty => .axiomC n ty\n" ++
  "  | .ulift k l A => .ulift k l (dropQTm A)\n" ++
  "  | .up a => .up (dropQTm a)\n" ++
  "  | .down t => .down (dropQTm t)\n" ++
  "  | .prf l t => .prf l (dropQTm t)\n" ++
  "partial def dropQTms : Tms → Tms\n" ++
  "  | .tnil => .tnil\n" ++
  "  | .tcons t r => .tcons (dropQTm t) (dropQTms r)\n" ++
  "end\n"

def kernelProgram (queries : List Query) : IO String := do
  let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
  -- (P2) every query gets its proof markers first, with `Kernel.wiz`'s own pass, as the
  -- Lean side marks with `Mark.infer` (`leanAnswer`); a term the pre-P2 kernel rejects is
  -- not marked (the pass checks nothing), so it answers `error` as before
  let verdict :=
    "def rawVerdict (t : Tm) : String := match infer empty t with\n  | .ok ty _ => show .nil 0 (quote 0 ty)\n  | .err _ => \"error\"\n" ++
    "def markedVerdict (t : Tm) : String := rawVerdict (MR.tm (markInfer (TCtx.relevant empty) t))\n" ++
    -- (mandatory sorts: the queries are `MTm` terms, whose `Π`/`Σ` sorts are holes until
    -- the sorts pass fills them; the kernel rejects a hole)
    "def verdict (t : Tm) : String := let u := sortsInfer t; match infer (TCtx.noMarkers empty) u with\n  | .err _ => \"error\"\n  | .ok _ _ => markedVerdict u\n" ++
    "def markedNormalize0 (t : Tm) : String := show .nil 0 (dropQTm (quote 0 (eval .nil (MR.tm (markInfer (TCtx.relevant empty) t)))))\n" ++
    "def markedNormalize (t : Tm) : String := markedNormalize0 (sortsInfer t)\n"
  let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
  -- one definition per query: a single list of every term is slow to elaborate
  let defs := String.join ((List.range queries.length).zip queries |>.map fun (i, (isVerdict, t)) =>
    s!"def q{i} (u : Unit) : String := {if isVerdict then "verdict" else "markedNormalize"} {t.toWiz}\n")
  let calls := (List.range queries.length).map fun i => s!"(q{i} ())"
  let tmpl := templatePairs.map fun (n, _) => s!"(show .nil 0 (dropQTm ({n})))"
  pure (kernel ++ "\n" ++ dropQSrc ++ verdict ++ printAll ++ defs ++
    s!"def main : IO Unit := printAll {Elab.wizList (calls ++ tmpl)}\n")

/-- Both kernels on the generated queries, the pinned ones and the templates. -/
def kernelsAgree (n : Nat) : IO Unit := do
  let gen := kernelQueries n
  let leanGen := gen.map leanAnswer
  let verdicts := (gen.zip leanGen).filter (·.1.1)
  let accepted := verdicts.filter (·.2 != "error")
  IO.println s!"    ({gen.length} queries: {verdicts.length} verdicts, {accepted.length} accepted; {gen.length - verdicts.length} normal forms)"
  check (accepted.length * 3 ≥ verdicts.length) "too few well-typed terms"
  for (name, q, lean, _) in pinned do
    unless leanAnswer q == lean do
      throw (IO.userError s!"{name}: the Lean kernel answers {leanAnswer q}, expected {lean}")
  let tmpl := templatePairs.map fun (_, t) => match MTm.ofTerm (dropQty t) with
    | some m => m.pretty 0
    | none => "?"
  let expected := leanGen ++ pinned.map (·.2.2.2) ++ tmpl
  let prog ← kernelProgram (gen ++ pinned.map (·.2.1))
  Elab.ioRun prog ("\n".intercalate expected ++ "\n")

/-- K10, a tracked gap: the self-hosted frontend drops the quantities written on binders,
so it accepts programs that the Lean frontend rejects. Pinned as a difference: the Lean
side must reject, the self-hosted side (today) accepts and prints unrestricted binders. -/
def k10Lean : List (String × String) :=
  [("def drop (1 x : Type) : Type 1 := Type", "quantity"),
   ("def twice (1 x : Type) (f : Type → Type → Type) : Type := f x x", "quantity")]
def k10Wiz : String :=
  "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef drop (1 x : Nat) : Nat := Nat.zero\n" ++
  "def twice (1 x : Nat) (f : Nat → Nat → Nat) : Nat := f x x\n"

def kernelGroup : Group where
  name := "audit-kernels"
  exercise := "soundness audit 2"
  cases := [
    { name := "the two kernels agree on generated typed terms, their normal forms, and the templates",
      run := fun _ => kernelsAgree 120 },
    -- (K10 was a gap until stage 21m: the self-hosted frontend now checks written quantities;
    -- the selfhost group's 21m cases test it in full)
    { name := "K10 (closed by 21m): both frontends reject a dropped and a duplicated linear variable",
      run := fun _ => do
        for (src, fragment) in k10Lean do Elab.fails src fragment
        if let some out ← Elab.selfhostOutput k10Wiz then
          let n := (out.splitOn "does not fit its quantity").length - 1
          unless n == 2 do throw (IO.userError s!"expected 2 quantity errors from the self-hosted checker, got {n}:\n{out}") }]

/-! ## Paradoxes

Each attempt is rejected at the first line that needs the inconsistency
(`/workspace/wiz-notes/soundness-audit-2.md`, §6, names the rule for each). The core-term
versions (Hurkens with an out-of-scope variable, `ULift` lowering a universe) are in
`pinned`.

The level mismatches are rendered as a type mismatch whose two universes are printed
(`mismatchReason` no longer repeats "universe level mismatch" when the types already show
it), so each entry pins the expected/inferred pair.
-/

def pw : String := "def Pw (X : Type) : Type := X → Prop\n"
def pwPoly : String :=
  "def Pw.{u} (X : Type u) : Type u := X → Prop\n" ++
  "def U.{u} : Type (u+1) := (X : Type u) → (Pw (Pw X) → X) → Pw (Pw X)\n" ++
  "def tau.{u} (t : Pw (Pw U.{u})) : U.{u} := fun X f p => t (fun x => p (f (x X f)))\n"
def orDefs : String :=
  "import Prelude\ndef Or (P Q : Prop) : Prop := (C : Prop) → (P → C) → (Q → C) → C\n" ++
  "def Not (P : Prop) : Prop := P → False\ndef EM : Prop := (P : Prop) → Or P (Not P)\n"
def codes : String :=
  "import Prelude\ndef Code : Type 1 := (I : Type) × ((D : Desc I) × I)\ndef El (c : Code) : Type := μ c.2.1 c.2.2\n"

/-- `(name, source, fragment of the one error, needs lib/)`. -/
def paradoxes : List (String × String × String × Bool) := [
  ("Hurkens: U : Type quantifying over Type", pw ++ "def U : Type := (X : Type) → (Pw (Pw X) → X) → Pw (Pw X)", "type mismatch\n  expected: Type\n  inferred: Type 1", false),
  ("Hurkens: honest universes, the self-application", pw ++ "def U : Type 1 := (X : Type) → (Pw (Pw X) → X) → Pw (Pw X)\ndef sigma (s : U) : Type 1 := s U", "type mismatch\n  expected: Type\n  inferred: Type 1", false),
  ("Hurkens: in Prop, the powerset of a proposition is not a proposition",
    "def Pw (X : Prop) : Type := X → Prop\ndef U : Prop := (X : Prop) → (Pw (Pw X) → X) → Pw (Pw X)", "type mismatch\n  expected: Prop\n  inferred: Type", false),
  ("Hurkens: level-polymorphic, σ at its own level", pwPoly ++ "def sigma.{u} (s : U.{u}) : Pw (Pw U.{u}) := s U.{u} tau.{u}", "type mismatch\n  expected: Type u\n  inferred: Type (u+1)", false),
  ("Hurkens: level-polymorphic, σ one level down: Ω does not come back",
    pwPoly ++ "def sigma.{u} (s : U.{u+1}) : Pw (Pw U.{u}) := s U.{u} tau.{u}\n" ++
    "def Delta.{u} : Pw U.{u+1} := fun y => ((p : Pw U.{u}) → sigma y p → p (tau (sigma y))) → False\n" ++
    "def Omega.{u} : U.{u} := tau (fun p => (x : U.{u+1}) → sigma x p → p x)", "universe level mismatch", false),
  ("Girard: Sort u : Sort u", "def a.{u} : Sort u := Sort u", "type mismatch\n  expected: Sort u\n  inferred: Type u", false),
  ("Girard: Type (u+1) : Type u", "def b.{u} : Sort (u+1) := Sort (u+1)", "type mismatch\n  expected: Type u\n  inferred: Type (u+1)", false),
  ("Girard: a Π into Type in Sort u", "def c.{u} (A : Sort u) : Sort u := A → Type", "type mismatch\n  expected: Sort u\n  inferred: Sort (imax u 2)", false),
  ("Girard: a Π from Type in Sort u", "def d.{u} (A : Sort u) : Sort u := Type → A", "type mismatch\n  expected: Sort u\n  inferred: Sort (imax 2 u)", false),
  ("Girard: Sort (max 1 u) is not Sort u", "def f.{u} (A : Sort (max 1 u)) : Sort u := A", "type mismatch\n  expected: Sort u\n  inferred: Sort (max 1 u)", false),
  ("Girard: Sort u is not Sort (max 1 u)", "def e.{u} (A : Sort u) : Sort (max 1 u) := A", "type mismatch\n  expected: Sort (max 1 u)\n  inferred: Sort u", false),
  ("Girard: imax u v is not v", "def g.{u, v} (A : Sort (imax u v)) : Sort v := A", "type mismatch\n  expected: Sort v\n  inferred: Sort (imax u v)", false),
  ("Girard: max is not imax", "def h.{u, v} (A : Sort (max u v)) : Sort (imax u v) := A", "type mismatch\n  expected: Sort (imax u v)\n  inferred: Sort (max u v)", false),
  ("Girard: imax is not max", "def h.{u, v} (A : Sort (imax u v)) : Sort (max u v) := A", "type mismatch\n  expected: Sort (max u v)\n  inferred: Sort (imax u v)", false),
  ("Girard: imax (imax u v) v is not imax v u", "def k.{u, v} (A : Sort (imax (imax u v) v)) : Sort (imax v u) := A", "type mismatch\n  expected: Sort (imax v u)\n  inferred: Sort (imax (imax u v) v)", false),
  ("Berardi: no conditional from a proof into data",
    orDefs ++ "def ite (em : EM) (P : Prop) (A : Type) (a b : A) : A := em P A (fun _ => a) (fun _ => b)", "type mismatch\n  expected: Prop\n  inferred: Type", true),
  ("Berardi: no Bool from a disjunction",
    orDefs ++ "def toBool (P Q : Prop) (h : Or P Q) : Bool := h Bool (fun _ => .true) (fun _ => .false)", "type mismatch\n  expected: Prop\n  inferred: Type", true),
  ("Berardi: no proposition that stores a proposition", "def Box : Prop := (P : Prop) × P", "type mismatch\n  expected: Prop\n  inferred: Type", false),
  ("Russell: a small type with a field over all small types",
    "import Prelude\ninductive V : Type where\n  | sup (X : Type) (f : X → V)", "can't lift", true),
  ("Russell: the same as a raw description",
    "import Prelude\ndef V : Type := μ (Desc.arg ω Type (fun X => Desc.hrec ω X (fun _ => ()) (Desc.ret ())) : Desc Unit) ()", "universe level mismatch", true),
  ("Russell: a negative occurrence", "import Prelude\ninductive Bad : Type where\n  | mk (f : Bad → Prop)", "may only occur", true),
  ("Russell: a positive, not strictly positive occurrence",
    "import Prelude\ninductive Bad : Type where\n  | mk (f : (Bad → Prop) → Prop)", "may only occur", true),
  ("Russell (Hur): an index of type Type → Type",
    "import Prelude\ninductive J : (Type → Type) → Type where\n  | mk (F : Type → Type) : J F", "index type must be in its universe", true),
  ("Russell: codes of small types as a field of a small type",
    codes ++ "inductive R : Type where\n  | mk (c : Code) (h : El c → False)", "can't lift", true)]

/-- Level identities that hold, for contrast: accepted. -/
def levelIdentities : String :=
  "def k1.{u} (A : Sort (imax u u)) : Sort u := A\n" ++
  "def ok1.{u} (A : Sort u) : Sort u := Unit → A\n" ++
  "def ok2.{u} (A : Sort u) : Sort (imax 1 u) := A\n" ++
  "def ok3.{u, v} (A : Sort (imax u (v+1))) : Sort (max u (v+1)) := A\n" ++
  "def ok4.{u, v} (A : Sort (imax (max u 1) v)) : Sort (imax 1 (imax u v)) := A\n" ++
  "def ok6.{u, v} (A : Sort (max (imax u v) v)) : Sort (imax u v) := A\n"

def paradoxCases : List Case :=
  (paradoxes.map fun (name, src, fragment, lib) =>
    { name := s!"paradox: {name}", run := fun _ => if lib then Elab.failsLib src fragment else Elab.fails src fragment }) ++
  [{ name := "paradox: the level identities that do hold are accepted", run := fun _ => Elab.ok levelIdentities },
   { name := "paradox: Berardi's conditional into Prop is accepted (it proves only proof irrelevance)", run := fun _ =>
       Elab.okLib (orDefs ++ "def iteP (em : EM) (P : Prop) (A : Prop) (a b : A) : A := em P A (fun _ => a) (fun _ => b)\n") },
   { name := "paradox: Hurkens as a core term with Prop for its universe is rejected (Lean kernel)", run := fun _ =>
       checkEq "error" (Elab.leanVerdict (hurkens fun _ => .prop)) },
   { name := "paradox: … and with an out-of-scope variable (it was Prop : Prop, and the term had type False)", run := fun _ => do
       checkEq "error" (Elab.leanVerdict (.var 0))
       checkEq "error" (Elab.leanVerdict (hurkens fun d => .var d)) }]

/-! ## The group -/

def cases (long : Bool) : List Case := [
  { name := "levels: normal forms, isNeverZero, toNat? mean what the level means (1200 levels)", run := fun _ => do
      for l in levels2 do
        match checkLevel l with
        | .ok _ => pure ()
        | .error e => throw (IO.userError e) },
  { name := "levels: equiv and le are sound, and complete without imax", run := fun _ =>
      levelPairs (if long then 1 else 16) },
  { name := "levels: instParams is a simultaneous substitution", run := fun _ => do
      let args := [Level.zero, .param "u", .param "v", .succ (.param "v"), .max (.param "u") (.param "v"),
        .imax (.param "v") (.param "u")]
      for l in (if long then levels2 else levels1) do
        for a in args do
          for b in args do
            match checkSubst l a b with
            | .ok _ => pure ()
            | .error e => throw (IO.userError e) },
  { name := "templates: interp, All, hyps, map have their types", run := fun _ => do
      for (l, v) in [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 3)] do
        let _ ← closedTemplates l v },
  { name := "templates: the types of the eliminators' arguments are types", run := fun _ => do
      for (l, v) in [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 3)] do
        argumentTypes l v false
        argumentTypes l v true },
  { name := "arithmetic: the definitions compute what the native operations do", run := fun _ =>
      definitionsAgree (native := false) long },
  { name := "arithmetic: the same points with the registrations (control)", run := fun _ =>
      definitionsAgree (native := true) long },
  { name := "arithmetic: #eval against Lean's Nat", run := fun _ => arithEval long },
  { name := "arithmetic: compiled (C) against Lean's Nat", run := fun _ => arithCompiled long false },
  { name := "arithmetic: compiled (LLVM) against Lean's Nat", run := fun _ => arithCompiled long true },
  { name := "words: the natives (C) against the definitions", run := fun _ => wordsAgree long false },
  { name := "words: the natives (LLVM) against the definitions", run := fun _ => wordsAgree long true },
  -- R5 (closed by the seal, #119): a word's constructor is private to lib/Word.wiz, so an
  -- out-of-range word can't be built with `.mk` outside it (before, the definitions and the
  -- compiled natives disagreed on such a word: `not` gave 0 and 211)
  { name := "words: R5, a word can't be built with .mk outside lib/Word.wiz (the seal)", run := fun _ =>
      Elab.failsLibs "import Word\ndef big (n : Nat) : UIntN 8 := .mk (n + 300)\n" "is private to module Word" }] ++
  paradoxCases

def group : Group where
  name := "audit"
  parallel := true
  exercise := "soundness audit 2"
  cases := cases false

/-- `tests --audit-hurkens`: what the Lean kernel says about Hurkens' paradox as a core
term, with `Prop` and with an out-of-scope variable for the universe. -/
def hurkensMain : IO UInt32 := do
  IO.println s!"var 0 in the empty context: {Elab.leanVerdict (.var 0)}"
  IO.println s!"Hurkens, universe := Prop: {Elab.leanVerdict (hurkens fun _ => .prop)}"
  IO.println s!"Hurkens, universe := an out-of-scope variable: {Elab.leanVerdict (hurkens fun d => .var d)}"
  pure 0

/-- `tests --audit-query I J …`: the queries with these indices, as terms, with the Lean
kernel's answer (and its error). -/
def queryMain (ixs : List String) : IO UInt32 := do
  let qs := (kernelQueries 120 ++ pinned.map (·.2.1)).toArray
  for ix in ixs do
    let some (isVerdict, t) := qs[ix.toNat!]? | IO.println s!"{ix}: no such query"
    IO.println s!"== {ix} ({if isVerdict then "verdict" else "normal form"})\n{t.pretty 0}\n-- Lean: {leanAnswer (isVerdict, t)}"
    if isVerdict then
      match infer (R := ZeroOneMany) { globals := Elab.leanGlobals () } t.toTerm with
      | .error e => IO.println s!"-- error: {e}"
      | .ok _ => pure ()
    else
      let g := Elab.leanGlobals ()
      IO.println (((toString (repr (quote g 0 (eval g [] t.toTerm)))).take 1500).toString)
  pure 0

/-- `tests --audit-long`: the same cases on the large grids, in this process. -/
def longMain : IO UInt32 := do
  let mut failed := 0
  for c in cases true do
    IO.println s!"  … {c.name}"
    (← IO.getStdout).flush
    try
      c.run ()
      IO.println "  ✓"
    catch e =>
      IO.println s!"  ✗ {e}"
      failed := failed + 1
  IO.println s!"{failed} failed"
  pure (if failed == 0 then 0 else 1)

builtin_initialize registerGroup group
builtin_initialize registerGroup kernelGroup

end Tests.Audit
