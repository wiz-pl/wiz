import Wiz
import Tests.Harness

/-!
# Tests for scry's prover mode (`Scry.Prover`)

The design is `wiz-notes/scry-prover.md`. The group `scry-prover` checks the smallest
honest slice of "prove, don't just report":

* **a universal claim, proved.** `no Console.ReadLine result reaches Process.Start` in
  the sanitised C# twin `cwe78-process-safe.cs`. The proof is an invariant over
  `(point, register)` facts; `Scry.check` verifies it from the EDB without running the
  analysis and without calling `Scry.prove`.
* **the same claim refuted on the unsafe twin.** The prover's closure reaches the sink,
  and the checker's alert obligation refutes it with a provenance path.
* **memory is covered.** A store/load pair is proved when the load is sanitised and
  refuted (with `store`/`load` in the witness) when it is not. The closure obligation
  is checked for both `tainted` rows and `mtainted` locations.
* **vacuity fails loudly.** A claim about a function with no selected source or no sink
  gets `vacuous`, not `proved`.
* **the verdict is tagged.** `proved`, `refuted`, `refused`, `script-failed`, `vacuous`
  are distinct; the script's `none` is not the only failure signal.
* **a claim selects its sources.** A parameter flow does not make a claim about `src`
  fail; the same claim over every source is refuted.
* **wrong proofs rejected.** An invariant that omits the seed is refused by the closure
  obligation; the unsafe program's invariant checked against the safe program is not
  accepted.

The group reads the checked-in C# spills, so it needs no tree-sitter and no .NET, like
`scry-csharp`.
-/

open Wiz

namespace Tests.ScryProver

/-- Every `lib/*.wiz`, `lib/D/*.wiz` (as `D.X`) and `scry/src/Scry/*.wiz` (as `Scry.X`),
by module name: one loader for the suite (`Tests.scryLoader`). -/
def loader : IO (Name → Option String) := Tests.scryLoader

/-- Run `body` (after the imports) and return the `#eval` message texts. -/
def runProbe (imports body : String) : IO (List String) := do
  let src := imports ++ body ++ "\n"
  let loader ← loader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure (s.messages.toList.map (·.text))

def proverImports : String :=
  "import Scry.CsLower\nimport Scry.Rules\nimport Scry.Models\nimport Scry.RuleTaint\n" ++
  "import Scry.Bounds\nimport Scry.Interproc\nimport Scry.Prover\nimport Scry.ProverExamples\nimport Text\n"

/-- A fixture's C# text and its checked-in spill. -/
def fixture (name : String) : IO (String × String) := do
  let src ← IO.FS.readFile s!"scry/corpus/csharp/taint/{name}.cs"
  let spill ← IO.FS.readFile s!"scry/corpus/csharp/taint/{name}.cst"
  pure (src, spill)

/-- Definitions for one fixture under a name prefix: the lowered program, its analysis,
and the EDB of `Fixtures.Runner.Main`. -/
def fixtureBody (pfx name src spill : String) : String :=
  s!"def {pfx}Src : String := {wizStr src}\n" ++
  s!"def {pfx}Spill : String := {wizStr spill}\n" ++
  s!"def {pfx}Prog : Wil.Program := Scry.Cs.programOf {wizStr (name ++ ".cs")} {pfx}Src {pfx}Spill\n" ++
  s!"def {pfx}Pr : Scry.ProgramResult := Scry.analyze {pfx}Prog pack\n" ++
  s!"def {pfx}Edb : Scry.State Nat :=\n" ++
  s!"  match Scry.findResult {pfx}Pr \"Fixtures.Runner.Main\" with\n" ++
  "  | .some r => r.edb\n" ++
  "  | .none => Scry.State.empty\n"

/-- `body`'s `#eval` messages are exactly `expected`. -/
def evalTexts (body : String) (expected : List String) : IO Unit := do
  checkEq expected (← runProbe proverImports body)

def packText : IO String := IO.FS.readFile "scry/corpus/csharp/csharp.scry"

/-- The pack and the two fixtures, as a probe prefix. -/
def bothFixtures (pack sSrc sSpill uSrc uSpill : String) : String :=
  s!"def pack : Scry.RulePack := Scry.parseRulePack {wizStr pack}\n" ++
  fixtureBody "safe" "cwe78-process-safe" sSrc sSpill ++
  fixtureBody "unsafe" "cwe78-process-unsafe" uSrc uSpill

def group : Group where
  name := "scry-prover"
  exercise := "Scry prover mode: invariants, memory, vacuity and a tactic script"
  parallel := true
  cases := [
    { name := "the tiny examples: safe proves, unsafe is refuted with a path, wrong invariants are refused",
      run := fun _ => evalTexts
        ("#eval String.eq (Scry.Verdict.show Scry.proverSafeVerdict) \"proved\"\n" ++
         "#eval String.eq Scry.proverSafeInvariant \"{(0,0)}\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverUnsafeVerdict) \"alert rule fires at sink 2 argument 0\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverUnsafeVerdict) \"path src(0,0) -> flow(0,1,0) -> flow(1,2,1) -> sink(2,0,1)\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverEmptyVerdict) \"rule 0 derives tainted (0,0)\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverEmptyVerdict) \"refused\"\n" ++
         "#eval Scry.Verdict.isOk Scry.proverSafeVerdict\n" ++
         "#eval Scry.Verdict.isOk Scry.proverUnsafeVerdict\n" ++
         "#eval Scry.Verdict.isOk Scry.proverEmptyVerdict\n" ++
         "#eval Scry.Verdict.isOk Scry.proverCrossVerdict\n" ++
         "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram Scry.proverSafe (Scry.Claim.noFlow \"hand\" [(0,0)] []))\n" ++
         "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram Scry.proverSafe (Scry.Claim.noFlow \"hand-wrong\" [(1,1)] []))\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverUnsafeCoverVerdict) \"refuted\"\n")
        [".true", ".true", ".true", ".true", ".true", ".true", ".true", ".false", ".false", ".false", ".true", ".false", ".true"] },
    { name := "the script proves the safe twin; the unsafe twin is refuted at the alert obligation",
      run := fun _ => do
        let pack ← packText
        let (sSrc, sSpill) ← fixture "cwe78-process-safe"
        let (uSrc, uSpill) ← fixture "cwe78-process-unsafe"
        evalTexts
          (bothFixtures pack sSrc sSpill uSrc uSpill ++
           "def safeClaim : Scry.Verdict := Scry.prove Scry.ruleTaintProgram safeEdb\n" ++
           "#eval Scry.Verdict.isOk safeClaim\n" ++
           "#eval match safeClaim with\n" ++
           "  | .proved c => List.length c.invariant\n" ++
           "  | _ => 999\n" ++
           "def unsafeClaim : Scry.Verdict := Scry.prove Scry.ruleTaintProgram unsafeEdb\n" ++
           "#eval Scry.Verdict.isOk unsafeClaim\n" ++
           "#eval String.contains (Scry.Verdict.show unsafeClaim) \"alert rule fires at sink\"\n" ++
           "#eval String.eq Scry.defaultScript \"intro 1;intro 6;intro 7;close;split;\"\n")
          [".true", "1", ".false", ".true", ".true"] },
    { name := "wrong proof 1: an invariant that omits the seed is refused",
      run := fun _ => do
        let pack ← packText
        let (src, spill) ← fixture "cwe78-process-safe"
        evalTexts
          (s!"def pack : Scry.RulePack := Scry.parseRulePack {wizStr pack}\n" ++
           fixtureBody "safe" "cwe78-process-safe" src spill ++
           "def full : Scry.Verdict := Scry.prove Scry.ruleTaintProgram safeEdb\n" ++
           "def noSeeds (c : Scry.Claim) : Scry.Claim :=\n" ++
           "  { c with invariant := List.filter (fun p => Bool.not (List.any (fun r => Scry.pairEq p (Scry.rowPair r))\n" ++
           "      (Scry.rtRows safeEdb Scry.rtSrc))) c.invariant }\n" ++
           "#eval match full with\n" ++
           "  | .proved c => Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram safeEdb (noSeeds c))\n" ++
           "  | _ => .true\n" ++
           "#eval match full with\n" ++
           "  | .proved c => (match Scry.check Scry.ruleTaintProgram safeEdb (noSeeds c) with\n" ++
           "    | .refused r => String.contains r \"rule 0 derives tainted\"\n" ++
           "    | _ => (.false : Bool))\n" ++
           "  | _ => .false\n")
          [".false", ".true"] },
    { name := "wrong proof 2: the unsafe program's invariant is rejected on the safe program",
      run := fun _ => do
        let pack ← packText
        let (sSrc, sSpill) ← fixture "cwe78-process-safe"
        let (uSrc, uSpill) ← fixture "cwe78-process-unsafe"
        evalTexts
          (bothFixtures pack sSrc sSpill uSrc uSpill ++
           "def uInv : Scry.Inv :=\n" ++
           "  match Scry.searchWith Scry.ruleTaintProgram unsafeEdb\n" ++
           "    ([Scry.Tactic.intro Scry.rtSrc, Scry.Tactic.close] : List Scry.Tactic) with\n" ++
           "  | .some inv => inv\n" ++
           "  | .none => Scry.Inv.empty\n" ++
           "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram safeEdb\n" ++
           "  (Scry.Claim.noFlow \"wrong\" uInv.tainted uInv.locations))\n" ++
           "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram unsafeEdb\n" ++
           "  (Scry.Claim.noFlow \"wrong\" uInv.tainted uInv.locations))\n")
          [".false", ".false"] },
    { name := "memory is covered: the store/load witness names both edges; the safe load proves",
      run := fun _ => evalTexts
        ("#eval String.contains (Scry.Verdict.show Scry.proverMemoryUnsafeVerdict) \"refuted\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverMemoryUnsafeVerdict) \"store(7,1,0)\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverMemoryUnsafeVerdict) \"load(7,2,0)\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverMemoryUnsafeVerdict) \"sink(4,0,0)\"\n" ++
         "#eval Scry.Verdict.isOk Scry.proverMemorySafeVerdict\n" ++
         "#eval String.eq Scry.proverMemorySafeInvariant \"{(0,0)}\"\n" ++
         "#eval String.eq Scry.proverMemorySafeLocations \"{7}\"\n" ++
         "def noM : Scry.Verdict := Scry.check Scry.ruleTaintProgram Scry.proverMemorySafe\n" ++
         "  (Scry.Claim.noFlow \"no-m\" [(0,0)] [])\n" ++
         "#eval String.contains (Scry.Verdict.show noM) \"mtainted 7\"\n" ++
         "def noLoad : Scry.Verdict := Scry.check Scry.ruleTaintProgram Scry.proverMemoryUnsafe\n" ++
         "  (Scry.Claim.noFlow \"no-load\" [(0,0)] [7])\n" ++
         "#eval String.contains (Scry.Verdict.show noLoad) \"tainted (2,0)\"\n" ++
         "#eval Scry.Verdict.isOk noLoad\n")
        [".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".false"] },
    { name := "vacuity: a claim with no source or no sink is vacuous, not proved",
      run := fun _ => evalTexts
        ("#eval String.contains (Scry.Verdict.show Scry.proverVacuousVerdict) \"vacuous\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverVacuousVerdict) \"source set is empty\"\n" ++
         "#eval Scry.Verdict.isOk Scry.proverVacuousVerdict\n" ++
         "def srcOnly : Scry.State Nat :=\n" ++
         "  Scry.State.addTuple Scry.State.empty Scry.rtSrc [U64.ofNat 0, U64.ofNat 0]\n" ++
         "def noSink : Scry.Verdict := Scry.prove Scry.ruleTaintProgram srcOnly\n" ++
         "#eval String.contains (Scry.Verdict.show noSink) \"sink set is empty\"\n" ++
         "#eval Scry.Verdict.isOk noSink\n")
        [".true", ".true", ".false", ".true", ".false"] },
    { name := "a claim selects its sources; constantOrBound allows parameter flows",
      run := fun _ => evalTexts
        ("#eval String.contains (Scry.Verdict.show Scry.proverSelectAllVerdict) \"refuted\"\n" ++
         "#eval Scry.Verdict.isOk Scry.proverSelectSrcVerdict\n" ++
         "#eval Scry.Verdict.isOk Scry.proverConstantOrBoundVerdict\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverConstantOrBoundVerdict) \"constant or parameter-bound\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverConstantOrBoundUnsafeVerdict) \"refuted\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverConstantOrBoundUnsafeVerdict) \"src(0,0)\"\n")
        [".true", ".true", ".true", ".true", ".true", ".true"] },
    { name := "the verdict is tagged: a bad script is script-failed, not none",
      run := fun _ => evalTexts
        ("#eval String.contains (Scry.Verdict.show Scry.proverScriptFailVerdict) \"script-failed\"\n" ++
         "#eval Scry.Verdict.isOk Scry.proverScriptFailVerdict\n")
        [".true", ".false"] },
    { name := "the cut: a guarded write proves; an unordered, weak, unknown-capacity or unguarded write is refuted",
      run := fun _ => evalTexts
        ("#eval Scry.Verdict.isOk Scry.proverCutSafeVerdict\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutSafeVerdict) \"proved (every write is preceded by a check)\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutUnorderedVerdict) \"does not dominate\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutUnorderedVerdict) \"guard(0,3,32,1)\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutUnorderedVerdict) \"use(1,3,7,32,2,0)\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutWeakVerdict) \"allows register 3 up to 64\"\n" ++
         "#eval Scry.Verdict.isOk Scry.proverCutConstOkVerdict\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutConstBadVerdict) \"constant 64\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutUnknownCapVerdict) \"no statically known capacity\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutPhantomVerdict) \"no guard fact\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCutVacuousVerdict) \"write set is empty\"\n" ++
         "#eval Scry.Verdict.isOk Scry.proverCutUnorderedVerdict\n" ++
         "#eval String.eq (Scry.Property.show Scry.Property.cut) \"cut (every write is preceded by a check)\"\n" ++
         "#eval Nat.beq (List.length Scry.guardFnRows) 1\n" ++
         "#eval match Scry.guardFnRows with\n" ++
         "  | .cons r _ => Bool.and (Nat.beq (List.getD r 1 99) 0) (Nat.beq (List.getD r 2 99) 16)\n" ++
         "  | .nil => .false\n")
        [".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".false", ".true", ".true", ".true"] }
  ]

builtin_initialize registerGroup group

end Tests.ScryProver
