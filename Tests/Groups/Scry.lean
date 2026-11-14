import Wiz
import Tests.Harness
import Tests.Elab

/-!
# scry's Datalog engine (S3, deep embedding)

The group `scry-datalog` checks `lib/Scry/Store.wiz`, `lib/Scry/Datalog.wiz` and
`lib/Scry/Eval.wiz` through `examples/scry-datalog-*.wiz`, and the follow-ups
`lib/Scry/Schema.wiz` (typed columns and range checks), `lib/Scry/Index.wiz` (native
kernels) and `lib/Scry/Fast.wiz` (the worklist engine, checked against the reference and
against `Scry.Cert`); the group `scry-egraph`
checks the S12 e-graph (`lib/Scry/Egraph.wiz`) through `examples/scry-egraph-*.wiz`.
The Datalog group's cases are:

* transitive closure and a provenance witness;
* same-generation;
* a lattice-valued relation (a product of a min and a max lattice);
* constant propagation with a conflict joining to `top`;
* stratified negation, and the same file's non-stratified program rejected;
* the pure list model of the relation store;
* a typed schema (u32/u64/interned-string/lattice columns) with range checks;
* the fast engine: differential agreement with the reference on every example, native
  kernel checks, a derivation checked by `Scry.Cert`, the compiled 10^5-fact scale set,
  and the stratification/range-restriction negatives.

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

/-- The example with extra `#eval` probes appended, expecting their printed values. -/
def probes (name : String) (extra : String) (expected : List String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.okLibs ("import Scry.Fast\n" ++ src ++ "\n" ++ extra) expected

/-- The same, compiled to C and to LLVM. -/
def compiled (name expected : String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.cRunLibs src expected
  Elab.cRunLibs src expected (llvm := true)

/-- `check` rejects a rule whose negated variable is not bound by a positive atom, and
the fast engine's `eval` rejects it too (both go through `Program.check`). -/
def rangeRestrictionCase : IO Unit := do
  let src := "import Scry.Fast\n" ++
    "def p : Scry.Program Nat := Scry.Program.mk (Scry.LatOps.mk 0 (fun a b => if Nat.lt a b then b else a) Nat.beq) [1, 1] [] [] " ++
    "[Scry.Rule.mk (Scry.Head.tuple 1 [Scry.Term.var 0]) [Scry.Atom.neg 0 [Scry.Term.var 0]]]\n" ++
    "#eval (match Scry.Program.check p with | .none => 1 | .some _ => 0)\n" ++
    "#eval (match Scry.Fast.eval p Scry.State.empty with | .none => 1 | .some _ => 0)"
  Elab.okLibs src ["1", "1"]

/-- The fast engine agrees with the reference on every program example (fact sets,
lattice values and provenance rule indices; `agree` returns 0). -/
def differentialCase : IO Unit := do
  let cases : List (String × String) := [
    ("scry-datalog-tc", "tc tcDb"),
    ("scry-datalog-samegen", "sg sgDb"),
    ("scry-datalog-lattice", "latProg latDb"),
    ("scry-datalog-constprop", "constProg constDb"),
    ("scry-datalog-negation", "good db")]
  for (name, args) in cases do
    let src ← IO.FS.readFile s!"examples/{name}.wiz"
    Elab.okLibs ("import Scry.Fast\n" ++ src ++ s!"\n#eval Scry.Fast.agree {args}\n") ["0"]

/-- The store kernels (dedup, indexes, lattice entries) behave like the list store's
`TupleRel`/`LatRel` on the same facts as `scry-datalog-store`. -/
def storeKernelsCase : IO Unit := do
  let src := "import Scry.Index\nimport Scry.Store\n" ++
    "def u (n : Nat) : U64 := U64.ofNat n\n" ++
    "def main : Nat :=\n" ++
    "  let r0 := (Scry.FRel.empty 2).insert [u 1, u 2] 0;\n" ++
    "  let r1 := r0.1.insert [u 1, u 2] 1;\n" ++
    "  let r2 := r1.1.insert [u 3, u 4] 2;\n" ++
    "  let t0 := Scry.TupleRel.insert Scry.TupleRel.empty [u 1, u 2];\n" ++
    "  let t1 := Scry.TupleRel.insert t0.1 [u 1, u 2];\n" ++
    "  let t2 := Scry.TupleRel.insert t1.1 [u 3, u 4];\n" ++
    "  let same := if Nat.beq r2.1.count (Scry.TupleRel.size t2.1) then 10 else 0;\n" ++
    "  let dedup := if r1.2 then 0 else 1;\n" ++
    "  let mem := if r2.1.mem [u 3, u 4] then (if r2.1.mem [u 9, u 9] then 0 else 1) else 0;\n" ++
    "  let l0 := (Scry.FLat.empty : Scry.FLat Nat);\n" ++
    "  let l1 := l0.setVal [u 9] 42 0;\n" ++
    "  let l2 := l1.setVal [u 9] 7 1;\n" ++
    "  let lat := match l2.find [u 9] with\n" ++
    "    | .some e => if Nat.beq e.val 7 then (if Nat.beq l2.count 1 then 100 else 0) else 0\n" ++
    "    | .none => 0;\n" ++
    "  let absent := match l2.find [u 10] with | .none => 1 | .some _ => 0;\n" ++
    "  same * 10000 + dedup * 1000 + mem * 100 + lat + absent\n" ++
    "#eval main"
  Elab.okLibs src ["101201"]

/-- A derivation expanded from the fast engine's provenance is checked by `Scry.Cert`
(`Scry.Fast.explainTuple` materialises the reference state and calls the same checker
as the reference engine). -/
def fastCertCase : IO Unit := do
  let src ← IO.FS.readFile "examples/scry-datalog-tc.wiz"
  let probe :=
    "\n#eval (match Scry.Fast.eval tc tcDb with" ++
    " | .none => 0" ++
    " | .some f => match Scry.Fast.explainTuple tc tcDb.db f 1 [u 1, u 4] with" ++
    "   | .none => 0" ++
    "   | .some d => if Scry.Derivation.check tc tcDb.db d then 1 else 0)\n"
  Elab.okLibs ("import Scry.FastCert\n" ++ src ++ probe) ["1"]

/-- The generated scale example (50k edges, 50k labels, a 400-edge chain) under the fast
engine, compiled to C. `main` is `paths * 10^6 + closure facts * 10 + (0, 400) hit`. -/
def scaleCase : IO Unit := do
  let src ← IO.FS.readFile "examples/scry-datalog-scale.wiz"
  Elab.cRunLibs src "50000802001"

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
  exercise := "S3: lib/Scry/{Store,Datalog,Eval,Schema,Index,Fast,FastCert}.wiz"
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
    { name := "typed columns: schema arity and u32/u64/string range checks", run := fun _ =>
        interp "scry-datalog-schema" "11111111111" },
    { name := "fast engine: the generated 10^5-fact set compiled (paths and closure)", run := fun _ =>
        scaleCase },
    { name := "fast engine: agreement with the reference on every example", run := fun _ =>
        differentialCase },
    { name := "fast engine: the native kernels dedup and join like the list store", run := fun _ =>
        storeKernelsCase },
    { name := "fast engine: a derivation is accepted by Scry.Cert's checker", run := fun _ =>
        fastCertCase },
    { name := "fast engine: rejects the non-stratified program and accepts the stratified one", run := fun _ =>
        probes "scry-datalog-negation"
          "#eval (match Scry.Fast.eval bad db with | .none => 1 | .some _ => 0)\n#eval (match Scry.Fast.eval good db with | .some _ => 1 | .none => 0)"
          ["1", "1"] },
    { name := "range restriction: an unbound negated variable is rejected", run := fun _ =>
        rangeRestrictionCase },
    { name := "stratification: a negative dependency raises the head's stratum", run := fun _ =>
        strataCase }
  ]

builtin_initialize registerGroup scryGroup
builtin_initialize registerGroup scryEgraphGroup

end Tests.Scry
