import Wiz
import Tests.Harness

/-!
# Tests for the intraprocedural taint prototype (`Scry.Analysis`, `Scry.Taint`)

The corpus is in `lib/Scry/TaintExamples.wiz`; each case evaluates `Scry.findings` (or a
graph-layer query) with `#eval` and compares the `Nat` summary with the expected list.
No C toolchain is needed.

The cases cover:

* a real flow through copies and arithmetic, with its source -> sink path;
* a sanitiser kill (and the same program without the sanitiser in the spec, which is
  flagged: the kill is spec-driven);
* a no-flow program;
* a branch merge (one tainted arm, one clean arm);
* a loop fixpoint where the only path to the sink is around the back edge;
* the false-positive / false-negative pair, with the positive control;
* the spec parser and the sink argument index;
* CFG edge count, dominators, reaching definitions and PDG data edges;
* stratification of the taint Datalog program.
-/

open Wiz

namespace Tests.ScryTaint

/-- Every `lib/*.wiz` and `lib/D/*.wiz` (as `D.X`), by module name. -/
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

/-- `body` (which imports the libraries) has no errors, and its `#eval` messages are
`expected`, in order (each a `Nat`). -/
def evalNats (body : String) (expected : List Nat) : IO Unit := do
  let src := "import Scry.Analysis\nimport Scry.Taint\nimport Scry.TaintExamples\nimport Text\n" ++ body ++ "\n"
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (expected.map toString) (s.messages.toList.map (·.text))

/-- A helper prefix for every case: `pathCode` encodes a path's length, first and last
point, so a wrong path fails without printing a list. -/
def prelude : String :=
  "def headNat : List Nat → Nat\n" ++
  "  | .nil => 999\n" ++
  "  | .cons x _ => x\n" ++
  "def lastNat : List Nat → Nat\n" ++
  "  | .nil => 999\n" ++
  "  | .cons x .nil => x\n" ++
  "  | .cons _ xs => lastNat xs\n" ++
  "def pathCode (p : List Nat) : Nat :=\n" ++
  "  Nat.add (Nat.mul (List.length p) 1000000)\n" ++
  "    (Nat.add (Nat.mul (headNat p) 1000) (lastNat p))\n"

def group : Group where
  name := "scry-taint"
  exercise := "Scry S4 (intraprocedural dataflow and taint prototype)"
  cases := [
    { name := "real flow: getenv -> copy -> add -> system, with its path",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.findings Scry.taintDirect Scry.demoSpec with\n" ++
        "  | .cons f .nil => pathCode f.path\n  | _ => 0") [4000004] },
    { name := "sanitiser kill: the flow is not reported",
      run := fun _ => evalNats
        "#eval List.length (Scry.findings Scry.taintSanitised Scry.demoSpec)" [0] },
    { name := "the same program is flagged when the sanitiser is not in the spec",
      run := fun _ => evalNats
        "#eval List.length (Scry.findings Scry.taintSanitised (Scry.TaintSpec.mk [\"getenv\"] [] [(\"system\", 0)]))" [1] },
    { name := "no flow: a source and a sink with no data path",
      run := fun _ => evalNats
        "#eval List.length (Scry.findings Scry.taintClean Scry.demoSpec)" [0] },
    { name := "branch merge: the tainted arm reaches the sink",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.findings Scry.taintBranch Scry.demoSpec with\n" ++
        "  | .cons f .nil => pathCode f.path\n  | _ => 0") [3000008] },
    { name := "loop fixpoint: the only path to the sink goes around the back edge",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.findings Scry.taintLoop Scry.demoSpec with\n" ++
        "  | .cons f .nil => pathCode f.path\n  | _ => 0") [3005003] },
    { name := "false-positive/false-negative pair, with the positive control",
      run := fun _ => evalNats
        ("#eval Nat.add (Nat.mul (List.length (Scry.findings Scry.taintFp Scry.demoSpec)) 100)\n" ++
         "  (Nat.add (Nat.mul (List.length (Scry.findings Scry.taintFn Scry.demoSpec)) 10)\n" ++
         "           (List.length (Scry.findings Scry.taintDirect Scry.demoSpec)))") [1] },
    { name := "spec parser: the line format parses to the same spec",
      run := fun _ => evalNats
        ("#eval Nat.add (Nat.mul (List.length (Scry.findings Scry.taintDirect (Scry.parseTaintSpec Scry.demoSpecText))) 10)\n" ++
         "  (List.length (Scry.findings Scry.taintSanitised (Scry.parseTaintSpec Scry.demoSpecText)))") [10] },
    { name := "sink argument index: the wrong argument is not a sink",
      run := fun _ => evalNats
        "#eval List.length (Scry.findings Scry.taintDirect (Scry.TaintSpec.mk [\"getenv\"] [] [(\"system\", 1)]))" [0] },
    { name := "dominators: entry and branch point dominate the sink, the arm does not",
      run := fun _ => evalNats
        ("#eval match Scry.fnInfo Scry.branchFn with\n" ++
         "  | info =>\n" ++
         "    Nat.add (Nat.mul (if Scry.dominates info.g info.dom 0 8 then 1 else 0) 100)\n" ++
         "      (Nat.add (Nat.mul (if Scry.dominates info.g info.dom 4 8 then 1 else 0) 10)\n" ++
         "               (if Scry.dominates info.g info.dom 3 8 then 1 else 0))") [101] },
    { name := "reaching definitions: two definitions of x at the merge, PDG edges from both",
      run := fun _ => evalNats
        ("#eval match Scry.fnInfo Scry.branchFn with\n" ++
         "  | info =>\n" ++
         "    Nat.add (Nat.mul (List.length (Scry.cfgEdges info.g)) 1000)\n" ++
         "      (Nat.add (Nat.mul (List.length (Scry.rdForVar info.defs info.rd 8 3)) 10)\n" ++
         "        (Nat.add (if Scry.flowHas info 4 8 then 1 else 0)\n" ++
         "          (Nat.add (if Scry.flowHas info 6 8 then 2 else 0)\n" ++
         "                   (if Scry.flowHas info 0 8 then 4 else 0))))") [10023] },
    { name := "loop reaching definitions: the back-edge definition reaches the sink",
      run := fun _ => evalNats
        ("#eval match Scry.fnInfo Scry.loopFn with\n" ++
         "  | info =>\n" ++
         "    Nat.add (if Scry.memNat 6 (Scry.rdForVar info.defs info.rd 3 2) then 10 else 0)\n" ++
         "      (if Scry.flowHas info 6 3 then 1 else 0)") [11] },
    { name := "the taint Datalog program is stratified (tainted above the sanitiser EDB)",
      run := fun _ => evalNats
        ("#eval match Scry.Program.check Scry.taintProgram with\n" ++
         "  | .none => 999\n" ++
         "  | .some st => List.foldr (fun x acc => Nat.add (Nat.mul x 10) acc) 0 st") [20] },
    { name := "alert tuples are one per sink call and argument",
      run := fun _ => evalNats
        ("#eval match Scry.alertsInFunc Scry.branchFn Scry.demoSpec with\n" ++
         "  | .cons p .nil => Nat.add (Nat.mul p.1 10) p.2\n" ++
         "  | _ => 0") [80] }
  ]

builtin_initialize registerGroup group

end Tests.ScryTaint
