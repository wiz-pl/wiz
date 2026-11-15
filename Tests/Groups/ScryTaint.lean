import Wiz
import Tests.Harness

/-!
# Tests for scry's taint analyses (`Scry.Analysis`, `Scry.Taint`, `Scry.RuleTaint`,
`Scry.Interproc`, `Scry.Sarif`, `Scry.Certify`)

The corpus is in `lib/Scry/TaintExamples.wiz` (the intraprocedural prototype) and
`lib/Scry/RuleExamples.wiz` (the rule pack and interprocedural engine); each case
evaluates a summary with `#eval` and compares it with the expected value. No C toolchain
is needed.

The cases cover:

* the intraprocedural prototype: a real flow with its path, a sanitiser kill (and the
  same program without the sanitiser), no flow, a branch merge, a loop fixpoint, the
  false-positive/false-negative pair, the spec parser, the sink argument index, CFG
  edges, dominators, reaching definitions, PDG edges and stratification;
* the `.scry` rule pack: four rules, per-argument sources/sinks, severities, kinds and
  function-name matching;
* interprocedural flow: argument -> parameter, return-value summaries, and a recursive
  parameter fixpoint, with the stitched source -> sink paths;
* per-argument sources and an in-place sanitiser;
* forbidden calls (`gets`, `strcpy`) and per-argument sinks (`fprintf`);
* no false positives on the safe fixtures, and indirect calls stay unknown;
* points-to and memory: same-slot store/load, a known no-alias pair, field sensitivity,
  a location tainted in one function and read in another (the memory summary), known and
  unknown indirect targets, the location lattice's kinds and `locOverlap`;
* certificates: a finding's derivation checks, reports its axioms and assumptions, and a
  tampered derivation is rejected;
* SARIF 2.1.0 shape, locations from an origin map, related locations, and the JSON
  round-trip through `Json.parse`.

The prototype cases import only the old modules (so they stay cheap); the rule-pack
cases import the whole taint stack.
-/

open Wiz

namespace Tests.ScryTaint

/-- Every `lib/*.wiz`, `lib/D/*.wiz` (as `D.X`) and `scry/src/Scry/*.wiz` (as
`Scry.X`), by module name. The C-lowering pipeline case serves both roots. -/
def libLoader : IO (Name → Option String) := do
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

def prototypeImports : String :=
  "import Scry.Analysis\nimport Scry.Taint\nimport Scry.TaintExamples\nimport Text\n"

/-- A Wiz string literal for `s` (the escapes the Wiz lexer reads). -/
def wizStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\t' => "\\t"
    | c => c.toString) "" ++ "\""

def ruleImports : String :=
  "import Scry.Analysis\n" ++
  "import Scry.Taint\n" ++
  "import Scry.TaintExamples\n" ++
  "import Scry.Rules\n" ++
  "import Scry.RuleTaint\n" ++
  "import Scry.Interproc\n" ++
  "import Scry.Sarif\n" ++
  "import Scry.Certify\n" ++
  "import Scry.RuleExamples\n" ++
  "import Json\n" ++
  "import Text\n"

/-- The rule pack plus S2's lowering, for the CLI's pipeline (without tree-sitter: the
case reads a checked-in `scry-cst` spill). -/
def pipelineImports : String :=
  ruleImports ++
  "import Scry.Lower\n" ++
  "import Scry.CstStore\n"


/-- Run `body` with `imports` prepended and return the `#eval` message texts. -/
def runProbe (imports body : String) : IO (List String) := do
  let src := imports ++ body ++ "\n"
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure (s.messages.toList.map (·.text))

/-- `body`'s `#eval` messages are `expected`, in order (each printed as a `Nat`). -/
def evalNats (body : String) (expected : List Nat) : IO Unit := do
  checkEq (expected.map toString) (← runProbe prototypeImports body)

/-- The same with the whole rule-pack stack importable. -/
def evalRuleNats (body : String) (expected : List Nat) : IO Unit := do
  checkEq (expected.map toString) (← runProbe ruleImports body)

/-- `body`'s `#eval` messages are exactly `expected` (e.g. quoted strings). -/
def evalRuleTexts (body : String) (expected : List String) : IO Unit := do
  checkEq expected (← runProbe ruleImports body)

/-- A helper prefix for the prototype cases: `pathCode` encodes a path's length, first
and last point, so a wrong path fails without printing a list. -/
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

/-- The rule-pack prelude: `pathCode3`/`kindsCode` encode a `PathNode` path, and the
helpers read group-ranked rules and JSON objects. -/
def rulePrelude : String := prelude ++
  "def firstFn : List Scry.PathNode → String\n" ++
  "  | .nil => \"\"\n" ++
  "  | .cons p _ => p.func\n" ++
  "def lastFn : List Scry.PathNode → String\n" ++
  "  | .nil => \"\"\n" ++
  "  | .cons p .nil => p.func\n" ++
  "  | .cons _ ps => lastFn ps\n" ++
  "def firstPt : List Scry.PathNode → Nat\n" ++
  "  | .nil => 999\n" ++
  "  | .cons p _ => p.point\n" ++
  "def lastPt : List Scry.PathNode → Nat\n" ++
  "  | .nil => 999\n" ++
  "  | .cons p .nil => p.point\n" ++
  "  | .cons _ ps => lastPt ps\n" ++
  "def kindCode (k : Scry.PathKind) : Nat :=\n" ++
  "  match k with\n" ++
  "  | .source => 1 | .param => 2 | .call => 3 | .returnSeed => 4\n" ++
  "  | .returnValue => 5 | .flow => 6 | .sink => 7 | .recursion => 8 | .assumed => 9\n" ++
  "  | .store => 10 | .load => 11 | .alloc => 12 | .free => 13\n" ++
  "def kindsCode : List Scry.PathNode → Nat\n" ++
  "  | .nil => 0\n" ++
  "  | .cons p ps => Nat.add (Nat.mul 10 (kindsCode ps)) (kindCode p.kind)\n" ++
  "def pathCode3 (p : List Scry.PathNode) : Nat :=\n" ++
  "  Nat.add (Nat.mul (List.length p) 1000000)\n" ++
  "    (Nat.add (Nat.mul (firstPt p) 1000) (lastPt p))\n" ++
  "def ruleSev : List Scry.PackRule → String → String\n" ++
  "  | .nil, _ => \"\"\n" ++
  "  | .cons r rest, id => if String.eq (Scry.PackRule.id r) id then Scry.Severity.show (Scry.PackRule.severity r) else ruleSev rest id\n" ++
  "def ruleKind : List Scry.PackRule → String → String\n" ++
  "  | .nil, _ => \"\"\n" ++
  "  | .cons r rest, id => if String.eq (Scry.PackRule.id r) id then Scry.FindingKind.show (Scry.PackRule.kind r) else ruleKind rest id\n" ++
  "def totalSinks : List Scry.TaintRule → Nat\n" ++
  "  | .nil => 0\n" ++
  "  | .cons r rest => Nat.add (List.length r.sinks) (totalSinks rest)\n" ++
  "def totalSources : List Scry.TaintRule → Nat\n" ++
  "  | .nil => 0\n" ++
  "  | .cons r rest => Nat.add (List.length r.sources) (totalSources rest)\n" ++
  "def headJ (d : Json) (l : List Json) : Json :=\n" ++
  "  match l with\n" ++
  "  | .cons x _ => x\n" ++
  "  | .nil => d\n" ++
  "def sarifRun (j : Json) : Json := headJ Json.mkNull (Json.getList j \"runs\")\n" ++
  "def sarifDriver (j : Json) : Json :=\n" ++
  "  match Json.get (sarifRun j) \"tool\" with\n" ++
  "  | .some t => (match Json.get t \"driver\" with | .some d => d | .none => Json.mkNull)\n" ++
  "  | .none => Json.mkNull\n" ++
  "def sarifResults (j : Json) : List Json := Json.getList (sarifRun j) \"results\"\n" ++
  "def firstResult (j : Json) : Json := headJ Json.mkNull (sarifResults j)\n" ++
  "def jStr (j : Json) (k : String) : String := Json.getStr j k\n" ++
  "def jLen (j : Json) (k : String) : Nat := List.length (Json.getList j k)\n" ++
  "def originMap : Scry.OriginMap :=\n" ++
  "  [ Scry.OriginEntry.mk \"main\" 0 (Scry.Origin.mk \"src/demo.c\" 10 5 10 20)\n" ++
  "  , Scry.OriginEntry.mk \"main\" 1 (Scry.Origin.mk \"src/demo.c\" 11 3 11 12)\n" ++
  "  , Scry.OriginEntry.mk \"callee\" 0 (Scry.Origin.mk \"src/demo.c\" 20 3 20 9) ]\n" ++
  "def emptyOrigins : Scry.OriginMap := []\n"

def group : Group where
  name := "scry-taint"
  exercise := "Scry S4 (intraprocedural dataflow, rule pack, interprocedural taint, SARIF, certificates)"
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
         "  | _ => 0") [80] },

    -- The rule pack and the interprocedural engine.
    { name := "rule pack: counts, severities, kinds and name globs",
      run := fun _ => do
        evalRuleNats (rulePrelude ++
          "#eval Nat.add (Nat.mul (List.length Scry.demoRules.rules) 10000) (Nat.add (Nat.mul (List.length (Scry.RulePack.taintRules Scry.demoRules)) 1000) (Nat.add (Nat.mul (List.length (Scry.RulePack.forbiddenRules Scry.demoRules)) 100) (Nat.add (Nat.mul (totalSinks (Scry.RulePack.taintRules Scry.demoRules)) 10) (totalSources (Scry.RulePack.taintRules Scry.demoRules)))))\n" ++
          "#eval if Scry.nameMatches \"mem*\" \"memcpy\" then 1 else 0\n" ++
          "#eval if Scry.nameMatches \"strcpy*\" \"astrcpy\" then 1 else 0\n" ++
          "#eval match Scry.Program.check Scry.ruleTaintProgram with | .none => 999 | .some st => List.length st") [42245, 1, 0, 14]
        evalRuleTexts (rulePrelude ++
          "#eval ruleSev Scry.demoRules.rules \"gets-overflow\"\n" ++
          "#eval ruleKind Scry.demoRules.rules \"gets-overflow\"")
          ["\"error\"", "\"forbidden\""]
        let text ← IO.FS.readFile "lib/Scry/rules/default.scry"
        let lit := (text.replace "\\" "\\\\").replace "\"" "\\\"" |>.replace "\n" "\\n"
        evalRuleNats (rulePrelude ++
          s!"#eval List.length (Scry.parseRulePack \"{lit}\").rules") [4] },
    { name := "interprocedural: argument taint crosses a direct call to the callee's sink",
      run := fun _ => do
        evalRuleNats (rulePrelude ++
          "#eval match Scry.programFindings (Scry.analyze Scry.interprocProgram Scry.demoRules) with | .cons f .nil => pathCode3 f.path | _ => 0\n" ++
          "#eval match Scry.programFindings (Scry.analyze Scry.interprocProgram Scry.demoRules) with | .cons f _ => Nat.add (Nat.mul (kindsCode f.path) 100) f.arg | .nil => 0") [4000000, 723100]
        evalRuleTexts (rulePrelude ++
          "#eval match Scry.programFindings (Scry.analyze Scry.interprocProgram Scry.demoRules) with | .cons f _ => f.rule | .nil => \"\"\n" ++
          "#eval match Scry.programFindings (Scry.analyze Scry.interprocProgram Scry.demoRules) with | .cons f _ => firstFn f.path | .nil => \"\"\n" ++
          "#eval match Scry.programFindings (Scry.analyze Scry.interprocProgram Scry.demoRules) with | .cons f _ => lastFn f.path | .nil => \"\"")
          ["\"command-injection\"", "\"main\"", "\"callee\""] },
    { name := "return-value summary: the callee's return reaches the caller's sink",
      run := fun _ => do
        evalRuleNats (rulePrelude ++
          "#eval match Scry.programFindings (Scry.analyze Scry.returnProgram Scry.demoRules) with | .cons f .nil => pathCode3 f.path | _ => 0\n" ++
          "#eval match Scry.programFindings (Scry.analyze Scry.returnProgram Scry.demoRules) with | .cons f _ => kindsCode f.path | .nil => 0") [4000001, 7451]
        evalRuleTexts (rulePrelude ++
          "#eval match Scry.programFindings (Scry.analyze Scry.returnProgram Scry.demoRules) with | .cons f _ => firstFn f.path | .nil => \"\"\n" ++
          "#eval match Scry.programFindings (Scry.analyze Scry.returnProgram Scry.demoRules) with | .cons f _ => lastFn f.path | .nil => \"\"")
          ["\"retCallee\"", "\"retMain\""] },
    { name := "recursion: the parameter fixpoint marks x (position 1) tainted",
      run := fun _ => do
        evalRuleNats (rulePrelude ++
          "def prR : Scry.ProgramResult := Scry.analyze Scry.recursionProgram Scry.demoRules\n" ++
          "#eval Nat.add (Nat.mul (List.length (Scry.summaryOf prR.summaries \"rec\").params) 10) (if Scry.memNat 1 (Scry.summaryOf prR.summaries \"rec\").params then 1 else 0)\n" ++
          "#eval match Scry.programFindings prR with | .cons f .nil => pathCode3 f.path | _ => 0\n" ++
          "#eval match Scry.programFindings prR with | .cons f _ => kindsCode f.path | .nil => 0") [11, 4000001, 7231]
        evalRuleTexts (rulePrelude ++
          "def prR : Scry.ProgramResult := Scry.analyze Scry.recursionProgram Scry.demoRules\n" ++
          "#eval match Scry.programFindings prR with | .cons f _ => firstFn f.path | .nil => \"\"\n" ++
          "#eval match Scry.programFindings prR with | .cons f _ => lastFn f.path | .nil => \"\"")
          ["\"main\"", "\"rec\""] },
    { name := "per-argument sources, in-place sanitisers, and per-argument sinks",
      run := fun _ => evalRuleNats
        ("#eval List.length (Scry.programFindings (Scry.analyze Scry.argSourceProgram Scry.demoRules))\n" ++
         "#eval Nat.add (Nat.mul (List.length (Scry.programFindings (Scry.analyze Scry.argSanProgram Scry.demoRules))) 10) (List.length (Scry.programFindings (Scry.analyze Scry.argSanProgram Scry.demoRulesNoSan)))\n" ++
         "#eval Nat.add (Nat.mul (List.length (Scry.programFindings (Scry.analyze Scry.fprintfProgram Scry.demoRules))) 10) (List.length (Scry.programFindings (Scry.analyze (Wil.program [Scry.safeFormatFn]) Scry.demoRules)))") [1, 1, 10] },
    { name := "safe fixtures: no false positives across the sanitiser and format cases",
      run := fun _ => evalRuleNats
        "#eval List.foldr (fun p acc => Nat.add (List.length (Scry.programFindings (Scry.analyze p Scry.demoRules))) acc) 0 Scry.safePrograms" [0] },
    { name := "forbidden rules: gets and strcpy are one-node findings with their rules",
      run := fun _ => do
        evalRuleNats (rulePrelude ++
          "#eval match Scry.programFindings (Scry.analyze Scry.getsProgram Scry.demoRules) with | .cons f .nil => Nat.add (Nat.mul (List.length f.path) 100) (if String.eq f.rule \"gets-overflow\" then 1 else 0) | _ => 0") [101]
        evalRuleTexts (rulePrelude ++
          "#eval match Scry.programFindings (Scry.analyze Scry.strcpyProgram Scry.demoRules) with | .cons f _ => f.rule | .nil => \"\"") ["\"strcpy-overflow\""] },
    { name := "indirect calls stay unknown: no flow and the graph records them",
      run := fun _ => evalRuleNats
        ("#eval Nat.add (Nat.mul (List.length (Scry.programFindings (Scry.analyze Scry.indirectProgram Scry.demoRules))) 10)\n" ++
         "  (List.length (Scry.analyze Scry.indirectProgram Scry.demoRules).graph.indirect)") [2] },
    { name := "memory: store then load is a flow (the prototype's documented false negative)",
      run := fun _ => evalRuleNats (rulePrelude ++
        "def memFindings : List Scry.RuleFinding :=\n" ++
        "  Scry.programFindings (Scry.analyze Scry.taintFn Scry.demoRules)\n" ++
        "def memPath : List Scry.PathNode :=\n" ++
        "  match memFindings with\n" ++
        "  | .cons f _ => f.path\n" ++
        "  | .nil => []\n" ++
        "#eval List.length memFindings\n" ++
        "#eval List.length memPath\n" ++
        "#eval kindsCode memPath\n" ++
        "#eval lastPt memPath") [1, 4, 8201, 4] },
    { name := "memory: a store into one object is not a flow from another (known no-alias)",
      run := fun _ => evalRuleNats
        ("#eval Nat.add (Nat.mul (List.length (Scry.programFindings (Scry.analyze Scry.taintDistinct Scry.demoRules))) 10)\n" ++
         "  (List.length (Scry.analyze Scry.taintDistinct Scry.demoRules).warnings)") [0] },
    { name := "memory: field sensitivity reaches cell 0 but not cell 1",
      run := fun _ => evalRuleNats (rulePrelude ++
        "def fieldFindings : List Scry.RuleFinding :=\n" ++
        "  Scry.programFindings (Scry.analyze Scry.taintFields Scry.demoRules)\n" ++
        "def fieldPath : List Scry.PathNode :=\n" ++
        "  match fieldFindings with\n" ++
        "  | .cons f _ => f.path\n" ++
        "  | .nil => []\n" ++
        "#eval List.length fieldFindings\n" ++
        "#eval lastPt fieldPath\n" ++
        "#eval firstPt fieldPath") [1, 8, 0] },
    { name := "memory: an indirect call through a known function pointer propagates",
      run := fun _ => evalRuleNats (rulePrelude ++
        "def prK : Scry.ProgramResult := Scry.analyze Scry.indirectKnownProgram Scry.demoRules\n" ++
        "def kf : List Scry.RuleFinding := Scry.programFindings prK\n" ++
        "#eval List.length kf\n" ++
        "#eval List.length prK.warnings\n" ++
        "#eval List.length prK.graph.indirect\n" ++
        "#eval match kf with\n" ++
        "  | .cons f _ => Nat.add (if String.eq f.func \"knownSink\" then 10 else 0)\n" ++
        "      (if String.eq (firstFn f.path) \"indirectKnown\" then 1 else 0)\n" ++
        "  | .nil => 0") [1, 0, 1, 11] },
    { name := "memory: unresolved indirect calls are unknown and warned",
      run := fun _ => evalRuleNats
        ("#eval Nat.add (Nat.mul (List.length (Scry.programFindings (Scry.analyze Scry.indirectProgram Scry.demoRules))) 10)\n" ++
         "  (List.length (Scry.analyze Scry.indirectProgram Scry.demoRules).warnings)") [2] },
    { name := "memory: a location tainted in one function is read in another",
      run := fun _ => evalRuleNats (rulePrelude ++
        "def prM : Scry.ProgramResult := Scry.analyze Scry.memAcrossProgram Scry.demoRules\n" ++
        "def mf : List Scry.RuleFinding := Scry.programFindings prM\n" ++
        "def mp : List Scry.PathNode := match mf with\n" ++
        "  | .cons f _ => f.path\n" ++
        "  | .nil => []\n" ++
        "#eval List.length mf\n" ++
        "#eval List.length prM.warnings\n" ++
        "#eval kindsCode mp\n" ++
        "#eval match mf with\n" ++
        "  | .cons f _ => Nat.add (if String.eq f.func \"memReader\" then 10 else 0)\n" ++
        "      (if String.eq (firstFn f.path) \"memWriter\" then 1 else 0)\n" ++
        "  | .nil => 0") [1, 0, 8201, 11] },
    { name := "points-to: location kinds of a field-sensitive object",
      run := fun _ => evalRuleTexts (rulePrelude ++
        "def ptF := Scry.pointsTo (Wil.program [Scry.fieldFn])\n" ++
        "#eval (Scry.locKindAt ptF 0) ++ \"/\" ++ (Scry.locKindAt ptF 1)\n" ++
        "#eval Nat.repr (Nat.add (Nat.mul (Scry.ptLocCount ptF) 10)\n" ++
        "  (Scry.ptVarCount ptF))") ["\"heap/field\"", "\"23\""] },
    { name := "points-to: overlap is exact for constant offsets and wildcard for anyOff",
      run := fun _ => evalRuleNats
        ("def h := Scry.Loc.heap \"f\" 1\n" ++
         "#eval Nat.add (if Scry.locEq (Scry.addOff h 0) h then 100 else 0)\n" ++
         "  (Nat.add (if Scry.locOverlap (Scry.Loc.field h 0) (Scry.Loc.field h 1) then 10 else 0)\n" ++
         "    (Nat.add (if Scry.locOverlap (Scry.Loc.field h 0) (Scry.Loc.anyOff h) then 1 else 0) 0))") [101] },
    { name := "certificates: the derivation checks, reports axioms, and a tampered one is rejected",
      run := fun _ => do
        evalRuleNats (rulePrelude ++
          "def prI : Scry.ProgramResult := Scry.analyze Scry.interprocProgram Scry.demoRules\n" ++
          "def prR : Scry.ProgramResult := Scry.analyze Scry.recursionProgram Scry.demoRules\n" ++
          "def prG : Scry.ProgramResult := Scry.analyze Scry.getsProgram Scry.demoRules\n" ++
          "#eval match Scry.certifyAll prI with | .cons c .nil => Nat.add (if c.verified then 100 else 0) (Nat.add (Nat.mul (List.length c.axioms) 10) (List.length c.assumptions)) | _ => 0\n" ++
          "#eval match Scry.certifyAll prR with | .cons c .nil => Nat.add (if c.verified then 100 else 0) (Nat.add (Nat.mul (List.length c.axioms) 10) (List.length c.assumptions)) | _ => 0\n" ++
          "#eval match Scry.certifyAll prG with | .cons c .nil => Nat.add (if c.verified then 100 else 0) (Nat.add (Nat.mul (List.length c.axioms) 10) (List.length c.assumptions)) | _ => 0") [131, 131, 110]
        evalRuleTexts (rulePrelude ++
          "def prI : Scry.ProgramResult := Scry.analyze Scry.interprocProgram Scry.demoRules\n" ++
          "#eval match Scry.certifyAll prI with | .cons c _ => (match Scry.findResult prI c.finding.func with | .some r => Scry.Derivation.check Scry.ruleTaintProgram r.edb.db { c.derivation with root := 999 } | .none => (.false : Bool)) | .nil => (.false : Bool)") [".false"] },
    { name := "SARIF: version, driver, rules, result, locations, related locations and round-trip",
      run := fun _ => do
        evalRuleNats (rulePrelude ++
          "def prI : Scry.ProgramResult := Scry.analyze Scry.interprocProgram Scry.demoRules\n" ++
          "def sar : Json := Scry.sarif \"scry\" originMap Scry.demoRules (Scry.programFindings prI)\n" ++
          "def sarNo : Json := Scry.sarif \"scry\" emptyOrigins Scry.demoRules (Scry.programFindings prI)\n" ++
          "#eval List.length (Json.getList sar \"runs\")\n" ++
          "#eval jLen (sarifDriver sar) \"rules\"\n" ++
          "#eval List.length (sarifResults sar)\n" ++
          "#eval jLen (firstResult sar) \"locations\"\n" ++
          "#eval jLen (firstResult sar) \"relatedLocations\"\n" ++
          "#eval Json.getNat (firstResult sar) \"ruleIndex\"\n" ++
          "#eval match Json.getList (firstResult sar) \"locations\" with | .cons loc _ => (match Json.get loc \"physicalLocation\" with | .some _ => 1 | .none => 0) | .nil => 9\n" ++
          "#eval match Json.getList (firstResult sarNo) \"locations\" with | .cons loc _ => (match Json.get loc \"physicalLocation\" with | .some _ => 1 | .none => 0) | .nil => 9\n" ++
          "#eval match Json.getList (firstResult sarNo) \"locations\" with | .cons loc _ => (match Json.get loc \"logicalLocations\" with | .some _ => 1 | .none => 0) | .nil => 9") [1, 4, 1, 1, 3, 0, 1, 0, 1]
        evalRuleTexts (rulePrelude ++
          "def prI : Scry.ProgramResult := Scry.analyze Scry.interprocProgram Scry.demoRules\n" ++
          "def sar : Json := Scry.sarif \"scry\" originMap Scry.demoRules (Scry.programFindings prI)\n" ++
          "#eval Json.getStr sar \"version\"\n" ++
          "#eval jStr (sarifDriver sar) \"name\"\n" ++
          "#eval jStr (firstResult sar) \"ruleId\"\n" ++
          "#eval jStr (firstResult sar) \"level\"\n" ++
          "#eval match Json.parse (Scry.renderSarif \"scry\" originMap Scry.demoRules (Scry.programFindings prI)) with | .ok j => Json.getStr j \"version\" | .error e => e")
          ["\"2.1.0\"", "\"scry\"", "\"scry/c/command-injection\"", "\"error\"", "\"2.1.0\""] },
    { name := "pipeline: C to Wil to rule pack, the CLI's path on a checked-in CST",
      run := fun _ => do
        let csrc ← IO.FS.readFile "scry/tests/fixtures/taint-unsafe.c"
        let cst ← IO.FS.readFile "scry/tests/fixtures/taint-unsafe.cst"
        let body :=
          s!"def source : String := {wizStr csrc}\n" ++
          s!"def spill : String := {wizStr cst}\n" ++
          "def cst : Option Scry.Cst := match Scry.CstStore.ofText spill with\n" ++
          "  | .ok s => .some (Scry.Cst.ofStore source s)\n" ++
          "  | .error _ => .none\n" ++
          "def tu : Option Scry.TU := match cst with\n" ++
          "  | .some c => .some (Scry.lowerTU \"taint-unsafe.c\" c)\n" ++
          "  | .none => .none\n" ++
          "#eval match tu with | .some t => List.length t.warnings | .none => 999\n" ++
          "#eval match tu with | .some t => List.length (Scry.programFindings (Scry.analyze (Wil.program t.funcs) Scry.demoRules)) | .none => 999\n" ++
          "#eval match tu with\n" ++
          "  | .none => 999\n" ++
          "  | .some t => match Scry.programFindings (Scry.analyze (Wil.program t.funcs) Scry.demoRules) with\n" ++
          "    | .cons f _ => if String.eq f.rule \"command-injection\" then 1 else 0\n" ++
          "    | .nil => 0\n"
        checkEq ["0", "1", "1"] (← runProbe pipelineImports body) }
  ]

builtin_initialize registerGroup group

end Tests.ScryTaint
