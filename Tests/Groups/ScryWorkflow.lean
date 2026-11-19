import Wiz
import Tests.Harness

/-!
# Workflow identity, triage and store tests (`Scry.Workflow`)

The pure layer: a deterministic finding id, the triage state machine, the JSON store and
the CWE tiers. The end-to-end command (scan/repro/verify) is `scry/tests/workflow.wiz`;
this group keeps the identity/state rules cheap and free of C or a compiler.
-/

open Wiz

namespace Tests.ScryWorkflow

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

def imports : String :=
  "import Scry.Workflow\nimport Json\nimport Text\n"

def runProbe (body : String) : IO (List String) := do
  let src := imports ++ body ++ "\n"
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure (s.messages.toList.map (·.text))

def evalNats (body : String) (expected : List Nat) : IO Unit := do
  checkEq (expected.map toString) (← runProbe body)

/-- The shared fixture: one taint finding with a source -> flow -> sink path. -/
def prelude : String :=
  "def mkFind (rule : String) : Scry.RuleFinding :=\n" ++
  "  Scry.RuleFinding.mk rule Scry.Severity.error \"m\" Scry.FindingKind.taint \"main\" 3 \"system\" 0\n" ++
  "    [Scry.PathNode.mk \"main\" 1 0 Scry.PathKind.source,\n" ++
  "     Scry.PathNode.mk \"main\" 2 0 Scry.PathKind.flow,\n" ++
  "     Scry.PathNode.mk \"main\" 3 0 Scry.PathKind.sink]\n" ++
  "def f : Scry.RuleFinding := mkFind \"command-injection\"\n"

def group : Group where
  name := "scry-workflow"
  exercise := "Scry workflow (finding identity, triage machine, JSON store, CWE tiers)"
  parallel := true
  cases := [
    { name := "identity: normalized path, rule and path shape, line hash",
      run := fun _ => evalNats (prelude ++
        "#eval if String.eq (Scry.wfId f \"src/a.c\") (Scry.wfId f \"./src/a.c\") then 1 else 0\n" ++
        "#eval if String.eq (Scry.wfId f \"src/a.c\") (Scry.wfId (mkFind \"format-string\") \"src/a.c\") then 0 else 1\n" ++
        "#eval if String.eq (Scry.wfLineHash f \"  system(cmd); \") (Scry.wfLineHash f \"system(cmd);\") then 1 else 0\n" ++
        "#eval if String.eq (Scry.wfLineHash f \"system(cmd);\") (Scry.wfLineHash f \"system(other);\") then 0 else 1\n" ++
        "#eval Nat.add (Nat.mul (List.length f.path) 100) (Nat.add (if String.eq (Scry.wfFirstFunc f.path) \"main\" then 10 else 0) (if String.eq (Scry.wfLastFunc f.path) \"main\" then 1 else 0))")
        [1, 1, 1, 1, 311] },
    { name := "triage: the state machine's edges and the history",
      run := fun _ => evalNats (prelude ++
        "#eval Nat.add (if Scry.wfAllowed .new .confirmed then 100 else 0) (Nat.add (if Scry.wfAllowed .new .fixed then 0 else 10) (if Scry.wfAllowed .confirmed .fixed then 1 else 0))\n" ++
        "#eval Nat.add (if Scry.wfAllowed .falsePositive .triaged then 10 else 0) (if Scry.wfAllowed .fixed .triaged then 1 else 0)\n" ++
        "def r0 : Scry.WfRecord := Scry.WfRecord.mk \"f_x\" \"k\" \"h\" .new [] \"src/a.c\" .none .false Json.mkNull \"art\" .none .none .none .none .none 1 1\n" ++
        "#eval match Scry.wfTriage r0 .confirmed \"tester\" \"seen\" 2 with\n" ++
        "  | .ok r => match Scry.wfTriage r .fixed \"tester\" \"patched\" 3 with\n" ++
        "    | .ok r2 => Nat.add (Nat.mul (List.length r2.history) 10) (if String.eq (Scry.WfState.show r2.state) \"fixed\" then 1 else 0)\n" ++
        "    | .error _ => 0\n" ++
        "  | .error _ => 0\n" ++
        "#eval match Scry.wfTriage r0 .fixed \"tester\" \"skip\" 2 with | .error _ => 1 | .ok _ => 0")
        [111, 11, 21, 1] },
    { name := "store: JSON round-trip and the schema check",
      run := fun _ => evalNats (prelude ++
        "def r0 : Scry.WfRecord := Scry.WfRecord.mk \"f_x\" \"k\" \"h\" .confirmed [] \"src/a.c\" .none .false Json.mkNull \"art\" (.some \"static.json\") .none .none .none .none 1 2\n" ++
        "def st : Scry.WfStore := Scry.wfUpsert Scry.wfEmptyStore r0\n" ++
        "#eval match Scry.wfStoreOfText (Scry.wfStoreText st) with\n" ++
        "  | .ok s => match Scry.wfFind s \"f_x\" with\n" ++
        "    | .some x => Nat.add (if String.eq (Scry.WfState.show x.state) \"confirmed\" then 10 else 0) (if String.eq (Scry.wfOptStrJson x.staticRel |> Json.render) \"\\\"static.json\\\"\" then 1 else 0)\n" ++
        "    | .none => 0\n" ++
        "  | .error _ => 0\n" ++
        "#eval match Scry.wfStoreOfText \"{\\\"schema\\\":\\\"other\\\",\\\"findings\\\":[]}\" with | .error _ => 1 | .ok _ => 0\n" ++
        "#eval Nat.add (Nat.mul (if String.eq (Scry.wfCweTier \"command-injection\") \"T1\" then 1 else 0) 100) (Nat.add (Nat.mul (if String.eq (Scry.wfCweTier \"use-after-free\") \"T2\" then 1 else 0) 10) (if String.eq (Scry.wfCweTier \"gets-overflow\") \"N/A\" then 1 else 0))")
        [11, 1, 111] },
    { name := "candidate: source/plan derivation, rank, verdict and JSON round-trip",
      run := fun _ => evalNats (
        "def src : Scry.WfSource := Scry.WfSource.mk \"getenv\" \"env\" \"SCRY_CMD\" \"main\" 7 3 0\n" ++
        "def plan := Scry.wfPlanFor \"f_abc\" \"command-injection\" \"main\" \"system\" 0 (.some src)\n" ++
        "#eval if String.eq plan.channel \"env\" then 1 else 0\n" ++
        "#eval if String.eq plan.envName \"SCRY_CMD\" then 1 else 0\n" ++
        "#eval if String.contains plan.inputText plan.marker then 1 else 0\n" ++
        "#eval if String.eq (Scry.wfCalleeOfLine \"  char *cmd = getenv(\\\"SCRY_CMD\\\");\") \"getenv\" then 1 else 0\n" ++
        "#eval if String.eq (Scry.wfChannelOfCallee \"System.Console.ReadLine\") \"stdin\" then 1 else 0\n" ++
        "def ok := Scry.wfRankInputOf .true 0 0 2 \"T1\" \"env\" \"SCRY_CMD\" .false\n" ++
        "def dup := Scry.wfRankInputOf .true 0 0 2 \"T1\" \"env\" \"SCRY_CMD\" .true\n" ++
        "#eval (Scry.wfRank ok).1\n" ++
        "#eval if String.eq (Scry.wfVerdict (Scry.wfRank ok).1) \"pursue\" then 1 else 0\n" ++
        "#eval if String.eq (Scry.wfVerdict (Scry.wfRank dup).1) \"reject\" then 1 else 0\n" ++
        "def cand : Scry.WfCandidate := Scry.WfCandidate.mk \"refined\" 95 \"pursue\" [\"why\"] (.some src) plan\n" ++
        "def rec0 : Scry.WfRecord := Scry.WfRecord.mk \"f_abc\" \"k\" \"h\" .new [] \"src/a.c\" .none .false Json.mkNull \"art\" .none .none .none (.some cand) (.some \"candidate.json\") 1 2\n" ++
        "#eval match Scry.wfStoreOfText (Scry.wfStoreText (Scry.wfUpsert Scry.wfEmptyStore rec0)) with\n" ++
        "  | .ok s => match Scry.wfFind s \"f_abc\" with\n" ++
        "    | .some r => match r.candidate with\n" ++
        "      | .some c => Nat.add (if String.eq c.verdict \"pursue\" then 10 else 0) (Nat.add (if Nat.beq c.rank 95 then 1 else 0) (if String.eq c.plan.envName \"SCRY_CMD\" then 100 else 0))\n" ++
        "      | .none => 0\n" ++
        "    | .none => 0\n" ++
        "  | .error _ => 0")
        [1, 1, 1, 1, 1, 95, 1, 1, 111] }
  ]

builtin_initialize registerGroup group

end Tests.ScryWorkflow
