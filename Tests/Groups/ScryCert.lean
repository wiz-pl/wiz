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
    { name := "the same certificate compiled to C and LLVM", run := fun _ =>
        compiled "scry-derivation" "10001011" }
  ]

builtin_initialize registerGroup scryCertGroup

end Tests.ScryCert
