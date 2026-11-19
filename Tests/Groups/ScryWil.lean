import Wiz
import Tests.Harness

/-!
# Tests for `Scry.Wil` (the IR and its concrete semantics)

The programs are hand-built in `lib/Scry/WilExamples.wiz`; each case evaluates a property
of `Wil.runFunction` with `#eval` (so no C toolchain is needed) and compares the `Nat`
it evaluates to with the expected list. The differential cases compare the IR's result
with a direct Wiz computation of the same function: when the C frontend lands, the same
shape of test adds a third computation (compiled C).
-/

open Wiz

namespace Tests.ScryWil

/-- Every `lib/*.wiz` and `lib/*/*.wiz` (as `D.X`), by module name. -/
def libLoader : IO (Name → Option String) := do
  let mut m : List (Name × String) := []
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then
      m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then
          m := (e.fileName ++ "." ++ f.path.fileStem.getD "", ← IO.FS.readFile f.path) :: m
  pure fun n => m.lookup n

/-- `body` elaborated against `imports`; the `#eval` messages, in order. -/
def runWiz (imports body : String) : IO (List String) := do
  let src := imports ++ body ++ "\n"
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure (s.messages.toList.map (·.text))

/-- What the sequential cases import: the IR, the corpus and `Text`. -/
def baseImports : String := "import Scry.Wil\nimport Scry.WilExamples\nimport Text\n"

/-- What the concurrency cases import: the concurrent corpus and the race analysis
(which pulls in `Scry.Analysis`), so the sequential cases pay nothing for them. -/
def concImports : String :=
  baseImports ++ "import Scry.ConcurrencyExamples\nimport Scry.Race\n"

/-- The `#eval`s of `body` are `expected`, in order (each a `Nat`). -/
def evalNats (body : String) (expected : List Nat) : IO Unit := do
  checkEq (expected.map toString) (← runWiz baseImports body)

/-- The `#eval`s of `body` are `expected`, in order (a `String` prints quoted). -/
def evalStrings (body : String) (expected : List String) : IO Unit := do
  checkEq expected (← runWiz baseImports body)

/-- `evalNats` for the concurrency cases (they import `Scry.Race` and the corpus). -/
def evalNatsConc (body : String) (expected : List Nat) : IO Unit := do
  checkEq (expected.map toString) (← runWiz concImports body)

/-- `evalStrings` for the concurrency cases. -/
def evalStringsConc (body : String) (expected : List String) : IO Unit := do
  checkEq expected (← runWiz concImports body)

/-- Shared definitions for the concurrency cases: the three drivers, the root value, and
the shape of the first race finding. -/
def concPrelude : String :=
  "def runRR (prog : Wil.Program) (fuel : Nat) : Wil.CRun :=\n" ++
  "  Wil.crunFunction prog fuel Wil.schedRoundRobin \"main\" []\n" ++
  "def runFirst (prog : Wil.Program) (fuel : Nat) : Wil.CRun :=\n" ++
  "  Wil.crunFunction prog fuel Wil.schedFirst \"main\" []\n" ++
  "def runScript (prog : Wil.Program) (fuel : Nat) : Wil.CRun :=\n" ++
  "  Wil.crunFunction prog fuel (Wil.schedScript\n" ++
  "    [0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0]) \"main\" []\n" ++
  "def cval (r : Wil.CRun) : Nat :=\n" ++
  "  match r.valueOf 0 with\n" ++
  "  | .some v => Wil.Val.bitsAt 32 v\n" ++
  "  | .none => 999\n" ++
  "def census (prog : Wil.Program) : Nat :=\n" ++
  "  match Scry.raceFindings prog with\n" ++
  "  | .cons f _ => match Bool.and (String.eq f.func \"inc\") (Bool.and (Nat.beq f.pointA 0) (Bool.and (Nat.beq f.pointB 3) (Nat.beq f.key 0))) with\n" ++
  "    | .true => 1\n" ++
  "    | .false => 0\n" ++
  "  | .nil => 0\n"

/-- The pinned round-robin trace of `Scry.raceUnsafe`: the root's first five steps, then the
first child joins the rotation as soon as it exists, so the two workers' loads both happen
before either store (that is the lost update), and the root finishes after both. -/
def raceTrace : String := "0,0,0,0,0,1,0,1,2,0,1,2,1,2,1,2,0,2,0,0,0"

/-- The pinned trace of the same program under `Wil.schedScript` with the script used by
`runScript`: the children start only after the root's join blocks, and the two workers then
alternate exactly. A different interleaving, with the same lost update. -/
def scriptTrace : String := "0,0,0,0,0,0,0,1,2,1,2,1,2,1,2,1,2,0,0,0,0"

def group : Group where
  name := "scry-wil"
  exercise := "Scry S2 (Wil)"
  parallel := true
  cases := [
    { name := "arithmetic: three-address add and multiply",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.arith 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [14] },
    { name := "branch: max of (10, 3)",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.maxOf 100 \"max\" [Scry.i32 10, Scry.i32 3] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [10] },
    { name := "branch (other arm): max of (3, 10)",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.maxOf 100 \"max\" [Scry.i32 3, Scry.i32 10] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [10] },
    { name := "direct calls: inc twice, 2 -> 4",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.incTwice 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [4] },
    { name := "recursive direct call: sumTo 10",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.sumTo 500 \"sum\" [Scry.i32 10] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [55] },
    { name := "a back edge that terminates: 5!",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.facLoop 1000 \"fac\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [120] },
    { name := "signed arithmetic: (-7) / 2 = -3",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.signedDiv 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [4294967293] },
    { name := "signed arithmetic: (-7) % 2 = -1",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.signedRem 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [4294967295] },
    { name := "unsigned arithmetic wraps at the width",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.wrapAdd 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [1] },
    { name := "memory: alloc, store, load",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.storeLoad 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [7] },
    { name := "memory: a pointer computed by gep",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.gepLoad 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [5] },
    { name := "memory: a load one past the end faults",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.oobLoad 100 \"main\" [] with\n  | .fault m => match String.eq m \"load: out of bounds at 0+4\" with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "memory: a load after free faults",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.danglingLoad 100 \"main\" [] with\n  | .fault m => match String.eq m \"load: freed block 0\" with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "an assume that is false faults",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.assumeFalse 100 \"main\" [] with\n  | .fault m => match String.eq m \"infeasible: assumption is false\" with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "an infinite loop runs out of fuel (and only fuel stops it)",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.spin 20 \"main\" [] with\n  | .outOfFuel => 1\n  | _ => 0" [1] },
    { name := "the step relation: an entry configuration has a successor",
      run := fun _ => evalNats
        "#eval match Wil.entry Scry.arith \"main\" [] with\n  | .ok c => match Wil.step c with\n    | .next _ => 1\n    | _ => 0\n  | .error _ => 0" [1] },
    { name := "differential: Wil arithmetic agrees with Wiz arithmetic",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.arith 100 \"main\" [] with\n  | .ok v => match Nat.beq (Wil.Val.bitsAt 32 v) (2 + 3 * 4) with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "differential: Wil's recursive sum agrees with a direct Wiz recursion",
      run := fun _ => evalNats
        "def sumRef : Nat → Nat\n  | .zero => 0\n  | .succ n => Nat.add (.succ n) (sumRef n)\n#eval match Wil.runFunction Scry.sumTo 500 \"sum\" [Scry.i32 10] with\n  | .ok v => match Nat.beq (Wil.Val.bitsAt 32 v) (sumRef 10) with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "differential: Wil's iterative factorial agrees with a Wiz recursion",
      run := fun _ => evalNats
        "def factRef : Nat → Nat\n  | .zero => 1\n  | .succ n => Nat.mul (.succ n) (factRef n)\n#eval match Wil.runFunction Scry.facLoop 1000 \"fac\" [] with\n  | .ok v => match Nat.beq (Wil.Val.bitsAt 32 v) (factRef 5) with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    -- ## Concurrency and the memory model (wiz-notes/scry-wil-concurrency.md)
    { name := "concurrency: the unsynchronised counter loses an update under round-robin",
      run := fun _ => evalStringsConc
        (concPrelude ++ "#eval cval (runRR Scry.raceUnsafe 200)\n#eval Wil.COut.show ((runRR Scry.raceUnsafe 200).out)\n")
        ["1", "\"all-done\""] },
    { name := "concurrency: the same program under the first-runnable schedule counts both",
      run := fun _ => evalNatsConc
        (concPrelude ++ "#eval cval (runFirst Scry.raceUnsafe 200)\n")
        [2] },
    { name := "concurrency: lock/unlock removes the lost update under both schedules",
      run := fun _ => evalNatsConc
        (concPrelude ++
         "#eval cval (runRR Scry.raceSafe 300)\n#eval cval (runFirst Scry.raceSafe 300)\n")
        [2, 2] },
    { name := "concurrency: atomic_add is one micro-step, so it cannot be split",
      run := fun _ => evalNatsConc
        (concPrelude ++ "#eval cval (runRR Scry.raceAtomic 200)\n")
        [2] },
    { name := "concurrency: a pinned interleaving has the exact expected trace",
      run := fun _ => evalStringsConc
        (concPrelude ++ "#eval Wil.showIds (runRR Scry.raceUnsafe 200).trace\n")
        [s!"\"{raceTrace}\""] },
    { name := "concurrency: a named script is a different interleaving with the same race",
      run := fun _ => evalStringsConc
        (concPrelude ++
         "#eval cval (runScript Scry.raceUnsafe 200)\n" ++
         "#eval Wil.showIds (runScript Scry.raceUnsafe 200).trace\n")
        ["1", s!"\"{scriptTrace}\""] },
    { name := "concurrency: every sequential case still runs on the concurrent machine",
      run := fun _ => evalNatsConc
        (concPrelude ++
         "#eval cval (Wil.crunFunction Scry.arith 100 Wil.schedFirst \"main\" [])\n" ++
         "#eval cval (Wil.crunFunction Scry.facLoop 1000 Wil.schedFirst \"fac\" [])\n" ++
         "#eval match (Wil.crunFunction Scry.danglingLoad 100 Wil.schedFirst \"main\" []).out with\n" ++
         "  | .fault _ m => match String.eq m \"load: freed block 0\" with\n    | .true => 1\n    | .false => 0\n" ++
         "  | _ => 0\n" ++
         "#eval match List.all (fun i => Nat.beq i 0)\n" ++
         "    (Wil.crunFunction Scry.facLoop 1000 Wil.schedFirst \"fac\" []).trace with\n" ++
         "  | .true => 1\n  | .false => 0\n")
        [14, 120, 1, 1] },
    { name := "concurrency: a thread-local block cannot be reached from a sibling",
      run := fun _ => evalNatsConc
        (concPrelude ++
         "#eval match (Wil.crunFunction Scry.localEscape 200 (Wil.schedScript []) \"main\" []).out with\n" ++
         "  | .fault tid m => match Bool.and (Nat.beq tid 2) (String.eq m \"cross-thread access to a block local to thread 1\") with\n" ++
         "    | .true => 1\n" ++
         "    | .false => 0\n" ++
         "  | _ => 0\n")
        [1] },
    { name := "race analysis: the unsynchronised increment is one finding",
      run := fun _ => evalNatsConc
        (concPrelude ++
         "#eval Scry.raceCount Scry.raceUnsafe\n" ++
         "#eval census Scry.raceUnsafe\n" ++
         "#eval Scry.raceCount Scry.raceSafe\n" ++
         "#eval Scry.raceCount Scry.raceAtomic\n")
        [1, 1, 0, 0] },
    { name := "race analysis: the finding names the function and both accesses",
      run := fun _ => evalStringsConc
        (concPrelude ++ "#eval Scry.raceReport Scry.raceUnsafe\n")
        ["\"data race in inc: load at point 0 and store at point 3 on register 0\""] },
    { name := "kernel-checked: a concurrent step of a sequential program is its sequential step",
      run := fun _ => evalNatsConc
        "#eval match Wil.cstep Scry.storeLoadCfg 0 with\n  | .next _ => 1\n  | .fault _ => 0\n" [1] }
  ]

builtin_initialize registerGroup group

end Tests.ScryWil
