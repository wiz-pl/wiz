import Wiz
import Tests.Harness
import Tests.Elab

/-!
# scry's derivation certificates (S8)

The group `scry-cert` checks `lib/Scry/Cert.wiz` through
`examples/scry-derivation.wiz`:

* a valid transitive-closure derivation is accepted, rendered and explained from the
  evaluator's provenance;
* a wrong premise, an out-of-range rule and a falsified EDB fact are rejected;
* a lattice-valued fact certified by a join of rule instances (the min lattice) is
  accepted, and a wrong join is rejected;
* the same example compiled to C and LLVM.

The checker, its shape and the soundness theorem are in `wiz-notes/scry-derivation.md`.
-/

open Wiz

namespace Tests.ScryCert

/-- An example file's `main`, under the interpreter, with every library importable. -/
def interp (name expected : String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.okLibs (src ++ "\n#eval main") [expected]

/-- The example with extra `#eval` probes appended, expecting their printed values. -/
def probes (name : String) (extra : String) (expected : List String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.okLibs (src ++ "\n" ++ extra) expected

/-- The same example compiled to C and to LLVM. -/
def compiled (name expected : String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  Elab.cRunLibs src expected
  Elab.cRunLibs src expected (llvm := true)

/-- Every info message of a source with every library importable. -/
def msgs (input : String) : IO (List String) := do
  let s := runFrontend (R := ZeroOneMany) input
    { trustedModule := Tests.libModule, loader := ← Elab.libLoader }
  pure (s.messages.toList.map (fun m => m.text))

def has (ms : List String) (frag : String) : Bool := ms.any fun m => (m.splitOn frag).length > 1

def scryCertGroup : Group where
  name := "scry-cert"
  exercise := "S8: lib/Scry/Cert.wiz"
  cases := [
    { name := "transitive closure: a valid derivation is accepted (and `main`)", run := fun _ =>
        interp "scry-derivation" "10001011" },
    { name := "transitive closure: check and the rendered certificate", run := fun _ =>
        probes "scry-derivation"
          "#eval Scry.Derivation.check dcProg tcEdb tcDeriv\n#eval Nat.lt 0 (String.length (Scry.Derivation.render (fun n => Nat.repr n) tcDeriv))"
          [".true", ".true"] },
    { name := "a wrong premise, an out-of-range rule, a falsified fact: rejected", run := fun _ =>
        probes "scry-derivation"
          "#eval Scry.Derivation.check dcProg tcEdb badPremise\n#eval Scry.Derivation.check dcProg tcEdb badRule\n#eval Scry.Derivation.check dcProg tcEdb badFact"
          [".false", ".false", ".false"] },
    { name := "a lattice join (min) certificate: accepted; a wrong join: rejected", run := fun _ =>
        probes "scry-derivation"
          "#eval Scry.Derivation.check latProg latEdb latDeriv\n#eval Scry.Derivation.check latProg latEdb latBadDeriv"
          [".true", ".false"] },
    { name := "provenance to certificate: explainTuple returns a checked witness", run := fun _ =>
        probes "scry-derivation" "#eval explained" ["1"] },
    { name := "negation: an absent atom is accepted; a present one is rejected", run := fun _ =>
        probes "scry-derivation"
          "#eval Scry.Derivation.check negProg negEdb negDeriv\n#eval Scry.Derivation.check negProg negEdb negBadDeriv\n#eval Scry.Derivation.check negLatProg negEdb negLatOkDeriv\n#eval Scry.Derivation.check negLatProg negEdb negLatBadDeriv"
          [".true", ".false", ".true", ".false"] },
    { name := "lattice provenance: explainLat rebuilds the join chain", run := fun _ =>
        probes "scry-derivation"
          "#eval chainOk\n#eval chainNodes"
          ["1", "7"] },
    { name := "stratification: Program.check's map freezes the lower strata", run := fun _ =>
        probes "scry-derivation"
          "#eval stratDigest\n#eval frozenOk\n#eval frozenMiss"
          ["10", ".true", ".false"] },
    { name := "absence certificates: accepted, rejected, and the add-the-tuple counterexample", run := fun _ =>
        probes "scry-derivation"
          "#eval absGoodOk\n#eval absBadOk\n#eval counterexample"
          ["1", "0", "1"] },
    { name := "a non-range-restricted program is rejected by Program.check", run := fun _ => do
        let src := "import Scry.Eval\n" ++
          "def p : Scry.Program Nat := Scry.Program.mk (Scry.LatOps.mk 0 (fun a b => if Nat.lt a b then b else a) Nat.beq) [1, 1] [] [] " ++
          "[Scry.Rule.mk (Scry.Head.tuple 1 [Scry.Term.var 0]) [Scry.Atom.neg 0 [Scry.Term.var 0]]]\n" ++
          "#eval (match Scry.Program.check p with | .none => 1 | .some _ => 0)"
        Elab.okLibs src ["1"] },
    { name := "the new soundness theorems trust only the existing natives", run := fun _ => do
        let ms ← msgs ("import Scry.Cert\n#print axioms Scry.check_sound_stratified\n" ++
          "#print axioms Scry.check_sound_negFree\n#print axioms Scry.absence_check_sound\n" ++
          "#print axioms Scry.edbInModel_dbIncl\n#print axioms Scry.absence_check_sound_checked\n")
        unless has ms "'Scry.check_sound_stratified' depends on axioms:" do
          throw (IO.userError s!"no axiom list for check_sound_stratified: {ms}")
        unless has ms "'Scry.absence_check_sound' depends on axioms:" do
          throw (IO.userError s!"no axiom list for absence_check_sound: {ms}")
        unless has ms "Scry.TupleRel.seal" && has ms "Scry.LatRel.seal" do
          throw (IO.userError s!"expected the store's seals only: {ms}")
        if has ms "native_refl" then
          throw (IO.userError s!"native_refl in the axiom list: {ms}") },
    { name := "the same certificate compiled to C and LLVM", run := fun _ =>
        compiled "scry-derivation" "10001011" }
  ]

builtin_initialize registerGroup scryCertGroup

end Tests.ScryCert
