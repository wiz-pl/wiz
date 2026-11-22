import Wiz
import Tests.Harness
import Tests.Elab

/-!
# scry's Datalog engine (S3, deep embedding)

The group `scry-datalog` checks `scry/src/Scry/Store.wiz`, `scry/src/Scry/Datalog.wiz` and
`scry/src/Scry/Eval.wiz` through `examples/scry-datalog-*.wiz`; the group `scry-egraph`
checks the S12 e-graph (`scry/src/Scry/Egraph.wiz`) through `examples/scry-egraph-*.wiz`.
The Datalog group's cases are:

* transitive closure and a provenance witness;
* same-generation;
* a lattice-valued relation (a product of a min and a max lattice);
* constant propagation with a conflict joining to `top`;
* stratified negation, and the same file's non-stratified program rejected;
* the pure list model of the relation store;
* the monotonicity registration (a gapped rule is refused) and a round-budget stop
  that reports `Termination.rounds` instead of a silent short answer.

The engine is ordinary Wiz, so the same examples run under the interpreter (`#eval`) and
compiled (C and LLVM); the transitive-closure case runs both. The embedding and the
evaluator are described in the module docs of `scry/src/Scry/Datalog.wiz` and
`scry/src/Scry/Eval.wiz`.
-/

open Wiz

namespace Tests.Scry

/-- An example file's `main`, under the interpreter, with every library importable. -/
def interp (name expected : String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.okLibs (src ++ "\n#eval main") [expected]

/-- An example run through another import: the file's `import Scry.Egraph` line is
swapped for `mod`. `Scry.EgraphNative` is now the compatibility import of the one
engine, so the six differential examples keep the same source and digest through it;
the case pins that the compatibility name still brings the whole surface. -/
def interpAs (mod name expected : String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.okLibs ((src.replace "import Scry.Egraph" s!"import {mod}") ++ "\n#eval main") [expected]

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

/-- The monotonicity obligation (`Program.checkMono`/`MonoDecl`) and the budgeted
evaluator (`evalBudget`): a rule registered monotone whose head maps an undeclared
transfer is a gap and a checked run refuses it; a round budget returns the facts derived
so far plus `Termination.rounds limit ran`, never a silent short answer. -/
def monoCase : IO Unit := do
  let base := "import Scry.Eval\n" ++
    "def ops : Scry.LatOps Nat := Scry.LatOps.mk 0 (fun a b => if Nat.lt a b then b else a) Nat.beq\n" ++
    "def bump (x : Nat) : Nat := if Nat.lt x 5 then Nat.add x 1 else 5\n" ++
    "def grow : Scry.Rule Nat := Scry.Rule.mk (Scry.Head.lat 0 [Scry.Term.lit (U64.ofNat 0)] (Scry.LExpr.map 0 (Scry.LExpr.var 0))) [Scry.Atom.lat 0 [Scry.Term.lit (U64.ofNat 0)] 0]\n" ++
    "def prog : Scry.Program Nat := Scry.Program.mk ops [1] [0] [bump] [grow]\n" ++
    "def good : Scry.MonoDecl := Scry.MonoDecl.mk [.true] [.true]\n" ++
    "def bad : Scry.MonoDecl := Scry.MonoDecl.mk [.true] [.false]\n" ++
    "def valAt (st : Scry.State Nat) : Nat := match Scry.Db.findLat st.db 0 [U64.ofNat 0] with | .some v => v | .none => 0\n" ++
    "def db : Scry.State Nat := Scry.State.addLatFact Scry.State.empty ops 0 [U64.ofNat 0] 1\n";
  -- A complete registration has no gap; the bad one names the undeclared transfer.
  Elab.okLibs (base ++
    "#eval (match Scry.Program.obligationError prog good with | .none => 1 | .some _ => 0)") ["1"];
  Elab.okLibs (base ++
    "#eval (match Scry.Program.obligationError prog bad with | .some e => if String.contains e \"not declared monotone\" then 1 else 0 | .none => 0)") ["1"];
  -- The checked evaluator refuses the gapped registration ...
  Elab.okLibs (base ++
    "#eval (match Scry.evalBudget prog (.some bad) .none db with | .none => 1 | .some _ => 0)") ["1"];
  -- ... and a two-round budget stops after exactly two rounds, incomplete.
  Elab.okLibs (base ++
    "#eval (match Scry.evalBudget prog (.some good) (.some 2) db with | .none => 0 | .some o => match o.termination with | .rounds l r => if Nat.beq l 2 then (if Nat.beq r 2 then (if Scry.EvalOutcome.complete o then 0 else 1) else 2) else 3 | .fixpoint => 4)") ["1"];
  -- With enough rounds the fixpoint is reached, the value is 5, and the result is
  -- certified (complete + registered).
  Elab.okLibs (base ++
    "#eval (match Scry.evalBudget prog (.some good) (.some 10) db with | .none => 0 | .some o => match o.termination with | .fixpoint => match Scry.Db.findLat o.state.db 0 [U64.ofNat 0] with | .some v => if Nat.beq v 5 then (if Scry.EvalOutcome.certified o then 1 else 2) else 3 | .none => 4 | .rounds _ _ => 5)") ["1"];
  -- Without a declaration the run is allowed but its outcome says the obligation is
  -- not covered.
  Elab.okLibs (base ++
    "#eval (match Scry.evalBudget prog .none (.some 20) db with | .some o => if o.monoChecked then 0 else 1 | .none => 0)") ["1"];
  -- The bounded loop is faithful: an unbounded `eval` and `evalBudget` with generous
  -- rounds reach the same value.
  Elab.okLibs (base ++
    "#eval (match Scry.eval prog db with | .some a => match Scry.evalBudget prog (.some good) (.some 20) db with | .some o => if Nat.beq (valAt a) (valAt o.state) then 1 else 0 | .none => 0 | .none => 0)") ["1"];
  -- A map nested under a registered map is checked recursively: one undeclared inner
  -- transfer is still a gap.
  Elab.okLibs (base ++
    "#eval (if Scry.LExpr.monoOk (L := Nat) [.true, .false] (Scry.LExpr.map 0 (Scry.LExpr.map 1 (Scry.LExpr.var 0))) then 0 else 1)") ["1"];
  Elab.okLibs (base ++
    "#eval (if Scry.LExpr.monoOk (L := Nat) [.true, .true] (Scry.LExpr.map 0 (Scry.LExpr.map 1 (Scry.LExpr.var 0))) then 1 else 0)") ["1"]

def scryEgraphGroup : Group where
  name := "scry-egraph"
  exercise := "S12: scry/src/Scry/Egraph.wiz"
  parallel := true
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
        interp "scry-egraph-datalog" "4021" },
    { name := "native tables: all six examples give the reference digests", run := fun _ => do
        interpAs "Scry.EgraphNative" "scry-egraph-congruence" "14111"
        interpAs "Scry.EgraphNative" "scry-egraph-rebuild" "14111"
        interpAs "Scry.EgraphNative" "scry-egraph-extract" "11332"
        interpAs "Scry.EgraphNative" "scry-egraph-saturate" "3171"
        interpAs "Scry.EgraphNative" "scry-egraph-fuel" "2851"
        interpAs "Scry.EgraphNative" "scry-egraph-datalog" "4021" },
    { name := "Datalog: eqsort columns, an equality-assertion head, canonicalise between rounds", run := fun _ =>
        interp "scry-egraph-eqplan" "11111121" },
    { name := "canonicalise: merge eq facts, rewrite eqsort columns, idempotent", run := fun _ =>
        interp "scry-egraph-canon" "111012" },
    { name := "analysis: an interval per e-class, a guarded rewrite and a joined interval", run := fun _ =>
        interp "scry-egraph-analysis" "1131341" },
    { name := "the analysis example under C and LLVM", run := fun _ =>
        compiled "scry-egraph-analysis" "1131341" },
    { name := "join: eqsort terms, an interval per e-class and a guarded rewrite refine each other", run := fun _ =>
        interp "scry-egraph-join" "1131341" },
    { name := "explanation: a rewrite chain and a congruence chain from the union log", run := fun _ =>
        interp "scry-egraph-explain" "1000111" },
    { name := "limits: fixpoint, fuel, node cap and clock cap stop reasons", run := fun _ =>
        interp "scry-egraph-limits" "123415" },
    { name := "extraction: Option costs, a cycle with no finite term, a large weight", run := fun _ =>
        interp "scry-egraph-extract-opt" "111111" },
    { name := "Wil terms: constant folding and identities reach 5 and 10", run := fun _ =>
        interp "scry-egraph-wil-const" "13252025" },
    { name := "Wil terms: a copy-only function is a one-round no-op fixpoint", run := fun _ =>
        interp "scry-egraph-wil-noop" "1110200" },
    { name := "Wil terms: fuel 1 stops before the outer fold, fuel 5 reaches it", run := fun _ =>
        interp "scry-egraph-wil-fuel" "110113" },
    { name := "extract back to Wil: 2+3 -> 5, identities -> copies, b+c -> 10, with fuel", run := fun _ =>
        interp "scry-egraph-extract-wil" "24001111130111" },
    { name := "extract guard: a redefined operand blocks the second identity", run := fun _ =>
        interp "scry-egraph-extract-guard" "21101111" }
  ]

def scryGroup : Group where
  name := "scry-datalog"
  exercise := "S3: scry/src/Scry/Store.wiz, scry/src/Scry/Datalog.wiz, scry/src/Scry/Eval.wiz"
  parallel := true
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
        strataCase },
    { name := "monotonicity: a registered rule with an undeclared transfer is refused; a round budget reports truncation", run := fun _ =>
        monoCase }
  ]

builtin_initialize registerGroup scryGroup
builtin_initialize registerGroup scryEgraphGroup

end Tests.Scry
