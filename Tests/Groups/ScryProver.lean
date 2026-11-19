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
  and the checker's alert obligation rejects it. The tool does not rubber-stamp.
* **wrong proofs rejected.** An invariant that omits the seed is rejected by the
  closure obligation; the unsafe program's invariant checked against the safe program is
  rejected; a function with a store is refused (the memory rules are outside the
  fragment) rather than accepted unsoundly.

The group reads the checked-in C# spills, so it needs no tree-sitter and no .NET, like
`scry-csharp`.
-/

open Wiz

namespace Tests.ScryProver

/-- Every `lib/*.wiz`, `lib/D/*.wiz` (as `D.X`) and `scry/src/Scry/*.wiz` (as `Scry.X`). -/
def loader : IO (Name → Option String) := do
  let mut m : List (Name × String) := []
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then
      m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then
          m := (e.fileName ++ "." ++ f.path.fileStem.getD "", ← IO.FS.readFile f.path) :: m
  for e in ← System.FilePath.readDir "scry/src/Scry" do
    if e.path.extension == some "wiz" then
      m := ("Scry." ++ e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
  pure fun n => m.lookup n

/-- A Wiz string literal for `s`. -/
def wizStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\t' => "\\t"
    | c => c.toString) "" ++ "\""

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
  "import Scry.Interproc\nimport Scry.Prover\nimport Scry.ProverExamples\nimport Text\n"

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
  exercise := "Scry prover mode: invariants, a checker, and a tactic script"
  parallel := true
  cases := [
    { name := "the tiny examples: safe proves, unsafe is refuted, empty and cross invariants are rejected",
      run := fun _ => evalTexts
        ("#eval String.eq (Scry.Verdict.show Scry.proverSafeVerdict) \"ok\"\n" ++
         "#eval String.eq Scry.proverSafeInvariant \"{(0,0)}\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverUnsafeVerdict) \"alert rule fires at sink 2 argument 0\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverEmptyVerdict) \"rule 0 derives tainted (0,0)\"\n" ++
         "#eval String.contains (Scry.Verdict.show Scry.proverCrossVerdict) \"alert rule fires\"\n" ++
         "#eval Scry.Verdict.isOk Scry.proverSafeVerdict\n" ++
         "#eval Scry.Verdict.isOk Scry.proverUnsafeVerdict\n" ++
         "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram Scry.proverSafe (Scry.Claim.mk \"hand\" [(0,0)]))\n" ++
         "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram Scry.proverSafe (Scry.Claim.mk \"hand-wrong\" [(1,1)]))\n" ++
         "#eval match Scry.prove Scry.ruleTaintProgram Scry.proverUnsafe with\n" ++
         "  | .some _ => .true\n" ++
         "  | .none => .false\n")
        [".true", ".true", ".true", ".true", ".true", ".true", ".false", ".true", ".false", ".false"] },
    { name := "the script proves the safe twin; the unsafe twin is refuted at the alert obligation",
      run := fun _ => do
        let pack ← packText
        let (sSrc, sSpill) ← fixture "cwe78-process-safe"
        let (uSrc, uSpill) ← fixture "cwe78-process-unsafe"
        evalTexts
          (bothFixtures pack sSrc sSpill uSrc uSpill ++
           "def safeClaim : Option Scry.Claim := Scry.prove Scry.ruleTaintProgram safeEdb\n" ++
           "#eval match safeClaim with\n" ++
           "  | .some c => Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram safeEdb c)\n" ++
           "  | .none => .false\n" ++
           "#eval match safeClaim with\n" ++
           "  | .some c => List.length c.invariant\n" ++
           "  | .none => 999\n" ++
           "def unsafeCover : Option Scry.Claim := Scry.proveWith Scry.ruleTaintProgram unsafeEdb\n" ++
           "  ([Scry.Tactic.intro Scry.rtSrc, Scry.Tactic.intro Scry.rtParam,\n" ++
           "    Scry.Tactic.intro Scry.rtRetSrc, Scry.Tactic.close] : List Scry.Tactic)\n" ++
           "#eval match unsafeCover with\n" ++
           "  | .some c => (match Scry.check Scry.ruleTaintProgram unsafeEdb c with\n" ++
           "    | .rejected r => String.contains r \"alert rule fires at sink\"\n" ++
           "    | .ok => .false)\n" ++
           "  | .none => .false\n" ++
           "#eval match Scry.prove Scry.ruleTaintProgram unsafeEdb with\n" ++
           "  | .some _ => .true\n" ++
           "  | .none => .false\n" ++
           "#eval String.eq Scry.defaultScript \"intro 1;intro 6;intro 7;close;split;\"\n")
          [".true", "1", ".true", ".false", ".true"] },
    { name := "wrong proof 1: an invariant that omits the seed is rejected",
      run := fun _ => do
        let pack ← packText
        let (src, spill) ← fixture "cwe78-process-safe"
        evalTexts
          (s!"def pack : Scry.RulePack := Scry.parseRulePack {wizStr pack}\n" ++
           fixtureBody "safe" "cwe78-process-safe" src spill ++
           "def full : Option Scry.Claim := Scry.prove Scry.ruleTaintProgram safeEdb\n" ++
           "def noSeeds (c : Scry.Claim) : Scry.Claim :=\n" ++
           "  { c with invariant := List.filter (fun p => Bool.not (List.any (fun r => Scry.pairEq p (Scry.rowPair r))\n" ++
           "      (Scry.rtRows safeEdb Scry.rtSrc))) c.invariant }\n" ++
           "#eval match full with\n" ++
           "  | .some c => Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram safeEdb (noSeeds c))\n" ++
           "  | .none => .true\n" ++
           "#eval match full with\n" ++
           "  | .some c => (match Scry.check Scry.ruleTaintProgram safeEdb (noSeeds c) with\n" ++
           "    | .rejected r => String.contains r \"rule 0 derives tainted\"\n" ++
           "    | .ok => .false)\n" ++
           "  | .none => .false\n")
          [".false", ".true"] },
    { name := "wrong proof 2: the unsafe program's invariant is rejected on the safe program",
      run := fun _ => do
        let pack ← packText
        let (sSrc, sSpill) ← fixture "cwe78-process-safe"
        let (uSrc, uSpill) ← fixture "cwe78-process-unsafe"
        evalTexts
          (bothFixtures pack sSrc sSpill uSrc uSpill ++
           "def uInv : List (Nat × Nat) :=\n" ++
           "  match Scry.proveWith Scry.ruleTaintProgram unsafeEdb\n" ++
           "    ([Scry.Tactic.intro Scry.rtSrc, Scry.Tactic.close] : List Scry.Tactic) with\n" ++
           "  | .some c => c.invariant\n" ++
           "  | .none => []\n" ++
           "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram safeEdb (Scry.Claim.mk \"wrong\" uInv))\n" ++
           "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram unsafeEdb (Scry.Claim.mk \"wrong\" uInv))\n")
          [".false", ".false"] },
    { name := "the fragment boundary: a function with a store is refused, not accepted",
      run := fun _ => do
        let pack ← packText
        let (src, spill) ← fixture "cwe78-process-safe"
        evalTexts
          (s!"def pack : Scry.RulePack := Scry.parseRulePack {wizStr pack}\n" ++
           fixtureBody "safe" "cwe78-process-safe" src spill ++
           "def stored : Scry.State Nat := Scry.State.addTuple safeEdb Scry.rtMStore\n" ++
           "  [U64.ofNat 0, U64.ofNat 1, U64.ofNat 2]\n" ++
           "#eval Scry.Verdict.isOk (Scry.check Scry.ruleTaintProgram stored (Scry.Claim.mk \"stored\" []))\n" ++
           "#eval match Scry.check Scry.ruleTaintProgram stored (Scry.Claim.mk \"stored\" []) with\n" ++
           "  | .rejected r => String.contains r \"memory rules are not covered\"\n" ++
           "  | .ok => .false\n")
          [".false", ".true"] }
  ]

builtin_initialize registerGroup group

end Tests.ScryProver
