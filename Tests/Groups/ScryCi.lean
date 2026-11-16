import Wiz
import Tests.Harness

/-!
# Tests for the CI frontend and analyses (`Scry.Ci`, `Scry.CiYaml`)

The corpus is `lib/Scry/CiExamples.wiz`; every case evaluates `#eval`s with the frontend
evaluator and compares the `Nat` summaries. The cases cover:

* the YAML subset: block mappings/sequences, flow values, quotes and comments, block
  scalars, multi-document input, and an indentation error;
* GitHub extraction: the three `on:` forms, jobs/steps, env/with expressions;
* the three GitHub rules: script injection (and the env-indirection fix), unpinned
  actions (pinned/local/digest references are clean), and `pull_request_target` +
  checkout of the PR head;
* Azure extraction: stages → jobs → steps, variable groups, resources, `extends`;
* the three Azure rules: `System.AccessToken`/secret in a script (env indirection is
  clean), floating task versions, and parameter interpolation into a script or template
  path;
* the Datalog program's stratification and every finding's checked certificate, plus a
  certificate the checker must reject on an empty EDB;
* the graph/store: node, edge and relation counts, and a cross-platform model.
-/

open Wiz

namespace Tests.ScryCi

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
  let src := "import Scry.CiYaml\nimport Scry.Ci\nimport Scry.CiExamples\nimport Text\n" ++ body ++ "\n"
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (expected.map toString) (s.messages.toList.map (·.text))

/-- Helpers for the cases: booleans to 0/1, list sums, option defaults and a few
finding counters. -/
def prelude : String :=
  "def b2n (b : Bool) : Nat := if b then 1 else 0\n" ++
  "def sumN (xs : List Nat) : Nat := List.foldl (fun a b => Nat.add a b) 0 xs\n" ++
  "def optYaml (r : Except String Scry.Yaml) : Scry.Yaml := match r with\n" ++
  "  | .ok y => y\n  | .error _ => .scalar \"\" 0 0\n" ++
  "def optDocs (r : Except String (List Scry.Yaml)) : List Scry.Yaml := match r with\n" ++
  "  | .ok ys => ys\n  | .error _ => []\n" ++
  "def optModel (r : Except String Scry.CiModel) : Scry.CiModel := match r with\n" ++
  "  | .ok m => m\n  | .error _ => Scry.ciEmptyModel\n" ++
  "def yText (y : Scry.Yaml) (k : String) : String := match Scry.Yaml.lookup k y with\n" ++
  "  | .some v => Scry.Yaml.asText v\n  | .none => \"\"\n" ++
  "def stepCount (wf : Scry.CiWorkflow) : Nat :=\n" ++
  "  List.foldl (fun a j => Nat.add a (List.length j.steps)) 0 wf.jobs\n" ++
  "def lenF (r : Scry.CiReport) : Nat := List.length r.findings\n" ++
  "def ruleC (r : Scry.CiReport) (n : Nat) : Nat := List.length (Scry.ciFindingsOfRule r n)\n" ++
  "def certsOk (r : Scry.CiReport) : Nat :=\n" ++
  "  List.length (List.filter (fun f => match f.cert with\n" ++
  "    | .some _ => .true\n" ++
  "    | .none => .false) r.findings)\n" ++
  "def certSum (r : Scry.CiReport) : Nat :=\n" ++
  "  List.foldl (fun a f => Nat.add a (Scry.ciCertSize f)) 0 r.findings\n" ++
  "def kindC (g : Scry.CiGraph) (k : Scry.CiKind) : Nat :=\n" ++
  "  List.length (List.filter (fun n => Scry.CiKind.beq n.kind k) g.nodes)\n" ++
  "def ruleVec (r : Scry.CiReport) : Nat :=\n" ++
  "  Nat.add (Nat.mul (ruleC r 1) 100000)\n" ++
  "    (Nat.add (Nat.mul (ruleC r 2) 10000)\n" ++
  "      (Nat.add (Nat.mul (ruleC r 3) 1000)\n" ++
  "        (Nat.add (Nat.mul (ruleC r 4) 100)\n" ++
  "          (Nat.add (Nat.mul (ruleC r 5) 10) (ruleC r 6)))))\n" ++
  "def factC (g : Scry.CiGraph) (rel : Nat) : Nat :=\n" ++
  "  List.length (List.filter (fun f => Nat.beq f.rel rel) g.facts)\n" ++
  "def firstF (r : Scry.CiReport) : Scry.CiFinding := match r.findings with\n" ++
  "  | .cons f _ => f\n" ++
  "  | .nil => Scry.CiFinding.mk 0 0 0 0 0 \"\" \"\" \"\" .none\n" ++
  "def jb (s : String) (sub : String) : Nat := if String.contains s sub then 1 else 0\n" ++
  "def pathRule (r : Scry.CiReport) (p : String) (n : Nat) : Nat :=\n" ++
  "  List.length (List.filter (fun f =>\n" ++
  "    Bool.and (String.eq f.path p) (Nat.beq f.rule n)) r.findings)\n" ++
  "def vec (xs : List Nat) : Nat :=\n" ++
  "  List.foldl (fun a x => Nat.add (Nat.mul a 10) x) 0 xs\n" ++
  "def vec100 (xs : List Nat) : Nat :=\n" ++
  "  List.foldl (fun a x => Nat.add (Nat.mul a 100) x) 0 xs\n" ++
  "def bits (xs : List Nat) : Nat :=\n" ++
  "  List.foldl (fun a x => Nat.add (Nat.mul a 2) x) 0 xs\n"

def group : Group where
  name := "scry-ci"
  exercise := "Scry CI frontend (YAML subset, GitHub/Azure IR, CI Datalog rules)"
  cases := [
    { name := "YAML subset: block map, block sequence, flow map, comments, quotes",
      run := fun _ => evalNats (prelude ++
        "#eval b2n (String.eq (Scry.Yaml.render (optYaml (Scry.parseYaml\n" ++
        "  \"a: 1\\nb:\\n- x\\n- {c: d}\\n\")))\n" ++
        "  \"{a: \\\"1\\\", b: [\\\"x\\\", {c: \\\"d\\\"}]}\")\n" ++
        "#eval b2n (String.eq (Scry.Yaml.render (optYaml (Scry.parseYaml\n" ++
        "  \"a: \\\"x # y\\\" # comment\\nb: 'it''s'\\n\")))\n" ++
        "  \"{a: \\\"x # y\\\", b: \\\"it's\\\"}\")") [1, 1] },
    { name := "YAML subset: literal and folded block scalars, document count",
      run := fun _ => evalNats (prelude ++
        "#eval b2n (String.eq (yText (optYaml (Scry.parseYaml\n" ++
        "  \"run: |\\n  echo a\\n  echo b\\n\\n\")) \"run\") \"echo a\\necho b\\n\")\n" ++
        "#eval b2n (String.eq (yText (optYaml (Scry.parseYaml\n" ++
        "  \"run: >-\\n  echo a\\n  echo b\\n\")) \"run\") \"echo a echo b\")\n" ++
        "#eval List.length (optDocs (Scry.parseYamlDocs \"---\\na: 1\\n---\\nb: 2\\n\"))") [1, 1, 2] },
    { name := "YAML subset: an over-indented mapping entry is rejected",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.parseYaml \"a: 1\\n   b: 2\\n\" with\n" ++
        "  | .error _ => 1\n  | .ok _ => 0") [1] },
    { name := "GitHub: the three on: forms give 1, 2 and 2 triggers",
      run := fun _ => evalNats (prelude ++
        "#eval List.length (Scry.ciWorkflowFirst (optModel (Scry.ciParseModel \"w.yml\" Scry.ciGhOnScalar))).triggers\n" ++
        "#eval List.length (Scry.ciWorkflowFirst (optModel (Scry.ciParseModel \"w.yml\" Scry.ciGhOnSeq))).triggers\n" ++
        "#eval List.length (Scry.ciWorkflowFirst (optModel (Scry.ciParseModel \"w.yml\" Scry.ciGhOnMap))).triggers") [1, 2, 2] },
    { name := "GitHub: jobs, steps and their expressions are extracted",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.ciModelGhUnsafe.workflows with\n" ++
        "  | .cons wf _ => Nat.add (Nat.mul (List.length wf.jobs) 1000) (stepCount wf)\n" ++
        "  | .nil => 0") [1004] },
    { name := "GitHub: script injection on the unsafe file, none on the safe one",
      run := fun _ => evalNats (prelude ++
        "#eval vec [ruleC (Scry.ciAnalyze Scry.ciModelGhUnsafe) 1,\n" ++
        "  ruleC (Scry.ciAnalyze Scry.ciModelGhSafe) 1,\n" ++
        "  ruleC (Scry.ciAnalyze\n" ++
        "    (optModel (Scry.ciParseModel \".github/workflows/t.yml\" Scry.ciGhTrusted))) 1]") [100] },
    { name := "trust: event kinds and context classes are explicit facts",
      run := fun _ => evalNats (prelude ++
        "#eval Scry.ciEventKind \"push\"\n" ++
        "#eval Scry.ciEventKind \"pull_request\"\n" ++
        "#eval Scry.ciEventKind \"pull_request_target\"\n" ++
        "#eval Scry.ciEventKind \"workflow_run\"\n" ++
        "#eval Scry.ciEventKind \"issue_comment\"\n" ++
        "#eval Scry.ciEventKind \"workflow_dispatch\"\n" ++
        "#eval Scry.ciGhCtxTag \"github.event.pull_request.title\"\n" ++
        "#eval Scry.ciGhCtxTag \"github.ref\"\n" ++
        "#eval Scry.ciGhCtxTag \"github.event.pull_request.head.sha\"\n" ++
        "#eval Scry.ciGhCtxTag \"inputs.name\"\n" ++
        "#eval Scry.ciGhCtxTag \"github.event.head_commit.message\"") [0, 1, 2, 3, 4, 5, 0, 11, 10, 12, 6] },
    { name := "trust: a context is tainted only for the event kinds that carry it",
      run := fun _ => evalNats (prelude ++
        "#eval b2n (Scry.ciCtxTaint 0 1)\n" ++
        "#eval b2n (Scry.ciCtxTaint 0 0)\n" ++
        "#eval b2n (Scry.ciCtxTaint 2 4)\n" ++
        "#eval b2n (Scry.ciCtxTaint 2 2)\n" ++
        "#eval b2n (Scry.ciCtxTaint 11 1)\n" ++
        "#eval b2n (Scry.ciCtxTaint 8 1)\n" ++
        "#eval b2n (Scry.ciCtxTaint 12 5)") [1, 0, 1, 0, 0, 1, 1] },
    { name := "trust: script injection follows the event (PR title, issue title, ref, head_ref, inputs)",
      run := fun _ => evalNats (prelude ++
        "def r := Scry.ciAnalyze Scry.ciModelGhEvents\n" ++
        "#eval vec [pathRule r \"ev/push.yml\" 1,\n" ++
        "  pathRule r \"ev/pr.yml\" 1,\n" ++
        "  pathRule r \"ev/issue-target.yml\" 1,\n" ++
        "  pathRule r \"ev/issue-comment.yml\" 1,\n" ++
        "  pathRule r \"ev/ref.yml\" 1,\n" ++
        "  pathRule r \"ev/head-ref.yml\" 1]") [10101] },
    { name := "trust: attacker ref and fork capability are per workflow",
      run := fun _ => evalNats (prelude ++
        "#eval b2n (Scry.ciWorkflowAttackerRef (Scry.ciWorkflowFirst Scry.ciModelGhUnsafe))\n" ++
        "#eval b2n (Scry.ciWorkflowForkCap (Scry.ciWorkflowFirst Scry.ciModelGhUnsafe))\n" ++
        "#eval b2n (Scry.ciWorkflowAttackerRef\n" ++
        "  (Scry.ciWorkflowFirst (optModel (Scry.ciParseModel \".github/workflows/pr.yml\" Scry.ciGhPullRequest))))\n" ++
        "#eval b2n (Scry.ciWorkflowForkCap\n" ++
        "  (Scry.ciWorkflowFirst (optModel (Scry.ciParseModel \".github/workflows/pr.yml\" Scry.ciGhPullRequest))))\n" ++
        "#eval b2n (Scry.ciWorkflowAttackerRef (Scry.ciWorkflowFirst Scry.ciModelGhEventPush))\n" ++
        "#eval b2n (Scry.ciWorkflowForkCap (Scry.ciWorkflowFirst Scry.ciModelGhEventPush))") [1, 1, 1, 0, 0, 0] },
    { name := "trust: checkout target is head vs base, and the rule needs both fork facts",
      run := fun _ => evalNats (prelude ++
        "#eval vec [ruleC (Scry.ciAnalyze Scry.ciModelGhArtifactUnsafe) 3,\n" ++
        "  ruleC (Scry.ciAnalyze Scry.ciModelGhArtifactSafe) 3,\n" ++
        "  factC (Scry.ciLower Scry.ciModelGhArtifactUnsafe) 7,\n" ++
        "  factC (Scry.ciLower Scry.ciModelGhArtifactUnsafe) 18,\n" ++
        "  factC (Scry.ciLower Scry.ciModelGhArtifactSafe) 7,\n" ++
        "  factC (Scry.ciLower Scry.ciModelGhArtifactSafe) 18]") [101001] },
    { name := "GitHub: unpinned action references; SHA, local and digest are pinned",
      run := fun _ => evalNats (prelude ++
        "#eval vec [ruleC (Scry.ciAnalyze Scry.ciModelGhUnsafe) 2,\n" ++
        "  ruleC (Scry.ciAnalyze Scry.ciModelGhSafe) 2]\n" ++
        "#eval b2n (Scry.ciPinned \"actions/checkout@9c091f2e5f7f4b0f44f0d9a6c5c6e8a1b2c3d4e5\")\n" ++
        "#eval b2n (Scry.ciPinned \"./local-action\")\n" ++
        "#eval b2n (Scry.ciPinned \"docker://alpine@sha256:abc\")\n" ++
        "#eval b2n (Scry.ciPinned \"actions/checkout@v4\")\n" ++
        "#eval b2n (Scry.ciPinned \"docker://alpine:3.20\")") [30, 1, 1, 1, 0, 0] },
    { name := "GitHub: pull_request_target plus a PR-head checkout is the privileged case",
      run := fun _ => evalNats (prelude ++
        "#eval vec [ruleC (Scry.ciAnalyze Scry.ciModelGhUnsafe) 3,\n" ++
        "  ruleC (Scry.ciAnalyze\n" ++
        "    (optModel (Scry.ciParseModel \".github/workflows/pr.yml\" Scry.ciGhPullRequest))) 3]") [10] },
    { name := "Azure: stages, jobs, steps, variable groups and a secret are extracted",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.ciModelAzUnsafe.workflows with\n" ++
        "  | .cons wf _ =>\n" ++
        "    Nat.add (Nat.mul (List.length wf.vars) 1000)\n" ++
        "      (Nat.add (Nat.mul (List.length (List.filter (fun v => v.secret) wf.vars)) 100)\n" ++
        "        (Nat.add (Nat.mul (List.length wf.jobs) 10) (stepCount wf)))\n" ++
        "  | .nil => 0") [1115] },
    { name := "Azure: System.AccessToken in a script; env indirection is clean",
      run := fun _ => evalNats (prelude ++
        "#eval vec [ruleC (Scry.ciAnalyze Scry.ciModelAzUnsafe) 4,\n" ++
        "  ruleC (Scry.ciAnalyze Scry.ciModelAzSafe) 4]") [10] },
    { name := "Azure: floating task versions are unpinned, x.y.z is pinned",
      run := fun _ => evalNats (prelude ++
        "#eval vec [ruleC (Scry.ciAnalyze Scry.ciModelAzUnsafe) 5,\n" ++
        "  ruleC (Scry.ciAnalyze Scry.ciModelAzSafe) 5]\n" ++
        "#eval b2n (Scry.ciTaskVersionPinned \"1.2.3\")\n" ++
        "#eval b2n (Scry.ciTaskVersionPinned \"1.2\")\n" ++
        "#eval b2n (Scry.ciTaskVersionPinned \"1\")") [10, 1, 0, 0] },
    { name := "Azure: parameters in a script and in a template path are two findings",
      run := fun _ => evalNats (prelude ++
        "#eval vec [ruleC (Scry.ciAnalyze Scry.ciModelAzUnsafe) 6,\n" ++
        "  ruleC (Scry.ciAnalyze Scry.ciModelAzSafe) 6]") [20] },
    { name := "Azure: resources and extends appear as includes/resource nodes",
      run := fun _ => evalNats (prelude ++
        "def m := optModel (Scry.ciParseModel \"azure-pipelines.yml\" Scry.ciAzResourceFile)\n" ++
        "#eval match m.workflows with\n" ++
        "  | .cons wf _ =>\n" ++
        "    Nat.add (Nat.mul (List.length wf.includes) 100)\n" ++
        "      (Nat.add (Nat.mul (List.length wf.resources) 10)\n" ++
        "        (List.length (List.filter (fun r => String.eq r.kind \"container\") wf.resources)))\n" ++
        "  | .nil => 0") [121] },
    { name := "artifact: an untrusted producer and a privileged needs consumer is two flows",
      run := fun _ => evalNats (prelude ++
        "def r := Scry.ciAnalyze Scry.ciModelGhArtifacts\n" ++
        "#eval vec [pathRule r \"art/unsafe.yml\" 7,\n" ++
        "  pathRule r \"art/safe.yml\" 7,\n" ++
        "  pathRule r \"art/nodep.yml\" 7,\n" ++
        "  List.length r.findings]") [2003] },
    { name := "artifact: producer/consumer facts, needs closure and shared cache nodes",
      run := fun _ => evalNats (prelude ++
        "def g := Scry.ciLower Scry.ciModelGhArtifactUnsafe\n" ++
        "#eval vec [factC g 12, factC g 13, factC g 14, factC g 15, factC g 16,\n" ++
        "  factC g 17, kindC g .artifact,\n" ++
        "  certsOk (Scry.ciAnalyze Scry.ciModelGhArtifactUnsafe)]") [33611223] },
    { name := "secrets: an opaque group makes an undeclared reference a possible secret",
      run := fun _ => evalNats (prelude ++
        "def r := Scry.ciAnalyze Scry.ciModelAzGroupsOpaque\n" ++
        "#eval vec [pathRule r \"az/opaque.yml\" 4,\n" ++
        "  pathRule r \"az/predefined.yml\" 4,\n" ++
        "  List.length r.findings]") [101] },
    { name := "secrets: a known group list is exhaustive (members are secrets, others are not)",
      run := fun _ => evalNats (prelude ++
        "#eval vec [ruleC (Scry.ciAnalyze Scry.ciModelAzGroupKnown) 4,\n" ++
        "  ruleC (Scry.ciAnalyze Scry.ciModelAzGroupKnownMiss) 4]\n" ++
        "#eval Scry.ciSecretOrigin (Scry.CiSecrets.mk [] [] [] .true) \"System.AccessToken\"\n" ++
        "#eval Scry.ciSecretOrigin (Scry.CiSecrets.mk [] [] [] .true) \"DB_PASSWORD\"\n" ++
        "#eval Scry.ciSecretOrigin (Scry.CiSecrets.mk [] [\"DB_PASSWORD\"] [] .false) \"DB_PASSWORD\"\n" ++
        "#eval Scry.ciSecretOrigin (Scry.CiSecrets.mk [] [\"OTHER\"] [] .false) \"DB_PASSWORD\"\n" ++
        "#eval Scry.ciSecretOrigin (Scry.CiSecrets.mk [] [] [\"greeting\"] .true) \"greeting\"") [10, 1, 2, 1, 0, 0] },
    { name := "spans: a finding carries its line, column and path",
      run := fun _ => evalNats (prelude ++
        "def f := firstF (Scry.ciAnalyze Scry.ciModelGhUnsafe)\n" ++
        "#eval vec100 [b2n (String.eq f.path \".github/workflows/unsafe.yml\"), f.line, f.col]") [11208] },
    { name := "json: the findings document has rule, severity, message, path, span and derivation",
      run := fun _ => evalNats (prelude ++
        "def r := Scry.ciAnalyze Scry.ciModelGhUnsafe\n" ++
        "def js := Scry.ciRenderJson r\n" ++
        "def s := Scry.ciRenderSarif r\n" ++
        "#eval bits [jb js \"\\\"rule\\\":\\\"gh-script-injection\\\"\",\n" ++
        "  jb js \"\\\"severity\\\":\\\"error\\\"\",\n" ++
        "  jb js \"\\\"path\\\":\\\".github/workflows/unsafe.yml\\\"\",\n" ++
        "  jb js \"\\\"span\\\":{\\\"start\\\":{\\\"line\\\":12\",\n" ++
        "  jb js \"\\\"derivation\\\":{\\\"checked\\\":true\",\n" ++
        "  jb js \"\\\"certificates\\\":\\\"checked\\\"\",\n" ++
        "  jb s \"\\\"version\\\":\\\"2.1.0\\\"\",\n" ++
        "  jb s \"\\\"ruleId\\\":\\\"gh-script-injection\\\"\",\n" ++
        "  jb s \"\\\"runs\\\"\"]") [511] },
    { name := "Datalog: the positive program checks, with every relation in stratum 0",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.Program.check Scry.ciProgram with\n" ++
        "  | .none => 999\n" ++
        "  | .some strata => Nat.add 1 (sumN strata)") [1] },
    { name := "certificates: every finding carries a checked derivation",
      run := fun _ => evalNats (prelude ++
        "def rg := Scry.ciAnalyze Scry.ciModelGhUnsafe\n" ++
        "def ra := Scry.ciAnalyze Scry.ciModelAzUnsafe\n" ++
        "#eval vec [Nat.add (Nat.mul (lenF rg) 10) (certsOk rg),\n" ++
        "  Nat.add (Nat.mul (lenF ra) 10) (certsOk ra),\n" ++
        "  b2n (Nat.lt 0 (certSum rg))]") [55441] },
    { name := "certificates: a derivation does not check against an empty EDB",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.ciAnalyze Scry.ciModelGhUnsafe with\n" ++
        "  | r => match r.findings with\n" ++
        "    | .cons f _ => match f.cert with\n" ++
        "      | .some d => b2n (Scry.Derivation.check Scry.ciProgram Scry.Db.empty d)\n" ++
        "      | .none => 9\n" ++
        "    | .nil => 8") [0] },
    { name := "graph: node, edge, action and expression counts",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.ciAnalyze Scry.ciModelGhUnsafe with\n" ++
        "  | r =>\n" ++
        "    Nat.add (Nat.mul (List.length r.graph.nodes) 10000)\n" ++
        "      (Nat.add (Nat.mul (List.length r.graph.edges) 100)\n" ++
        "        (Nat.add (Nat.mul (kindC r.graph .action) 10) (kindC r.graph .expression)))") [161732] },
    { name := "cross-platform: the rule vector over both unsafe files",
      run := fun _ => evalNats (prelude ++
        "#eval ruleVec (Scry.ciAnalyze Scry.ciModelAll)") [131112] },
    { name := "no false positives: both safe files produce no findings",
      run := fun _ => evalNats (prelude ++
        "def r := Scry.ciAnalyze Scry.ciModelSafe\n" ++
        "#eval vec [lenF r, b2n (Scry.ciCheckCerts r)]") [1] },
    { name := "report rendering starts with the finding count",
      run := fun _ => evalNats (prelude ++
        "#eval b2n (String.startsWith (Scry.ciRenderReport (Scry.ciAnalyze Scry.ciModelGhUnsafe))\n" ++
        "  \"findings: 5\")") [1] }
  ]

builtin_initialize registerGroup group

end Tests.ScryCi
