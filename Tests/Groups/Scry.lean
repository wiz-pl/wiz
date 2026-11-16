import Wiz
import Tests.Harness
import Tests.Elab

/-!
# scry's Datalog engine (S3, deep embedding)

The group `scry-datalog` checks `lib/Scry/Store.wiz`, `lib/Scry/Datalog.wiz` and
`lib/Scry/Eval.wiz` through `examples/scry-datalog-*.wiz`; the group `scry-egraph`
checks the S12 e-graph (`lib/Scry/Egraph.wiz`) through `examples/scry-egraph-*.wiz`.
The Datalog group's cases are:

* transitive closure and a provenance witness;
* same-generation;
* a lattice-valued relation (a product of a min and a max lattice);
* constant propagation with a conflict joining to `top`;
* stratified negation, and the same file's non-stratified program rejected;
* the pure list model of the relation store.

The engine is ordinary Wiz, so the same examples run under the interpreter (`#eval`) and
compiled (C and LLVM); the transitive-closure case runs both. The design is in
`wiz-notes/scry-datalog.md`.
-/

open Wiz

namespace Tests.Scry

/-- An example file's `main`, under the interpreter, with every library importable. -/
def interp (name expected : String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.okLibs (src ++ "\n#eval main") [expected]

/-- The same, compiled to C and to LLVM. -/
def compiled (name expected : String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.cRunLibs src expected
  Elab.cRunLibs src expected (llvm := true)

/-- `check` rejects a rule whose negated variable is not bound by a positive atom. -/
def rangeRestrictionCase : IO Unit := do
  let src := "import Scry.Eval\n" ++
    "def p : Scry.Program Nat := Scry.Program.mk (Scry.LatOps.mk 0 (fun a b => if Nat.lt a b then b else a) Nat.beq) [1, 1] [] [] " ++
    "[Scry.Rule.mk (Scry.Head.tuple 1 [Scry.Term.var 0]) [Scry.Atom.neg 0 [Scry.Term.var 0]]]\n" ++
    "#eval (match Scry.Program.check p with | .none => 1 | .some _ => 0)"
  Elab.okLibs src ["1"]

/-- `Program.check` returns one stratum per relation, and a negated dependency raises the
head's stratum by one. -/
def strataCase : IO Unit := do
  let src := "import Scry.Eval\n" ++
    "def ops : Scry.LatOps Nat := Scry.LatOps.mk 0 (fun a b => if Nat.lt a b then b else a) Nat.beq\n" ++
    "def p : Scry.Program Nat := Scry.Program.mk ops [1, 1, 1] [] [] " ++
    "[Scry.Rule.mk (Scry.Head.tuple 1 [Scry.Term.var 0]) [Scry.Atom.pos 0 [Scry.Term.var 0], Scry.Atom.neg 2 [Scry.Term.var 0]]]\n" ++
    "#eval (match Scry.Program.check p with | .none => 999 | .some st => List.foldr (fun x acc => x * 10 + acc) 0 st)"
  -- strata [0, 1, 0] read from the right by the fold: 010
  Elab.okLibs src ["10"]

def scryEgraphGroup : Group where
  name := "scry-egraph"
  exercise := "S12: lib/Scry/Egraph.wiz"
  cases := [
    { name := "congruence: a = b also equates f a = f b and g (f a) = g (f b)", run := fun _ =>
        interp "scry-egraph-congruence" "14111" },
    { name := "rebuild: a batch of unions canonicalises every class, child and level", run := fun _ =>
        interp "scry-egraph-rebuild" "14111" },
    { name := "extraction: unit cost takes x, a heavy leaf weight takes 0 + 1", run := fun _ =>
        interp "scry-egraph-extract" "11332" },
    { name := "extraction: the same under C and LLVM", run := fun _ =>
        compiled "scry-egraph-extract" "11332" },
    { name := "saturation: x + 0 → x, x * 1 → x and commutativity reach x", run := fun _ =>
        interp "scry-egraph-saturate" "3171" },
    { name := "fuel: a growing rewrite adds one layer per round and stops at the bound", run := fun _ =>
        interp "scry-egraph-fuel" "2851" },
    { name := "Datalog: derived equality facts feed one mergeFacts, then congruence", run := fun _ =>
        interp "scry-egraph-datalog" "4021" }
  ]

def scryGroup : Group where
  name := "scry-datalog"
  exercise := "S3: lib/Scry/Store.wiz, lib/Scry/Datalog.wiz, lib/Scry/Eval.wiz"
  cases := [
    { name := "transitive closure: the delta loop, and a witness for (1, 4) (interp)", run := fun _ =>
        interp "scry-datalog-tc" "600107" },
    { name := "transitive closure: the same under C and LLVM", run := fun _ =>
        compiled "scry-datalog-tc" "600107" },
    { name := "same-generation: two recursive rules", run := fun _ =>
        interp "scry-datalog-samegen" "9111000" },
    { name := "lattice: a product of min and max lattices, joined in place", run := fun _ =>
        interp "scry-datalog-lattice" "9973004" },
    { name := "constant propagation: copies, add1, and a conflict joins to top", run := fun _ =>
        interp "scry-datalog-constprop" "7089995" },
    { name := "stratified negation, and a non-stratified program rejected", run := fun _ =>
        interp "scry-datalog-negation" "101032" },
    { name := "the store model: dedup, sparse relation numbers, one value per lattice key", run := fun _ =>
        interp "scry-datalog-store" "123170" },
    { name := "range restriction: an unbound negated variable is rejected", run := fun _ =>
        rangeRestrictionCase },
    { name := "stratification: a negative dependency raises the head's stratum", run := fun _ =>
        strataCase }
  ]

builtin_initialize registerGroup scryGroup
builtin_initialize registerGroup scryEgraphGroup

end Tests.Scry
