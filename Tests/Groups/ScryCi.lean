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
  "          (Nat.add (Nat.mul (ruleC r 5) 10) (ruleC r 6)))))\n"

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
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelGhUnsafe) 1\n" ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelGhSafe) 1\n" ++
        "#eval ruleC (Scry.ciAnalyze\n" ++
        "  (optModel (Scry.ciParseModel \".github/workflows/t.yml\" Scry.ciGhTrusted))) 1") [1, 0, 0] },
    { name := "GitHub: untrusted contexts (event, head_ref, inputs) and trusted ones",
      run := fun _ => evalNats (prelude ++
        "#eval b2n (Scry.ciGhUntrusted \"github.event.pull_request.head.ref\")\n" ++
        "#eval b2n (Scry.ciGhUntrusted \"github.head_ref\")\n" ++
        "#eval b2n (Scry.ciGhUntrusted \"inputs.name\")\n" ++
        "#eval b2n (Scry.ciGhUntrusted \"github.sha\")\n" ++
        "#eval b2n (Scry.ciGhUntrusted \"env.FOO\")\n" ++
        "#eval b2n (Scry.ciGhUntrusted \"matrix.os\")\n" ++
        "#eval b2n (Scry.ciGhUntrusted \"secrets.TOKEN\")") [1, 1, 1, 0, 0, 0, 0] },
    { name := "GitHub: unpinned action references; SHA, local and digest are pinned",
      run := fun _ => evalNats (prelude ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelGhUnsafe) 2\n" ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelGhSafe) 2\n" ++
        "#eval b2n (Scry.ciPinned \"actions/checkout@9c091f2e5f7f4b0f44f0d9a6c5c6e8a1b2c3d4e5\")\n" ++
        "#eval b2n (Scry.ciPinned \"./local-action\")\n" ++
        "#eval b2n (Scry.ciPinned \"docker://alpine@sha256:abc\")\n" ++
        "#eval b2n (Scry.ciPinned \"actions/checkout@v4\")\n" ++
        "#eval b2n (Scry.ciPinned \"docker://alpine:3.20\")") [3, 0, 1, 1, 1, 0, 0] },
    { name := "GitHub: pull_request_target plus a PR-head checkout is the privileged case",
      run := fun _ => evalNats (prelude ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelGhUnsafe) 3\n" ++
        "#eval ruleC (Scry.ciAnalyze\n" ++
        "  (optModel (Scry.ciParseModel \".github/workflows/pr.yml\" Scry.ciGhPullRequest))) 3") [1, 0] },
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
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelAzUnsafe) 4\n" ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelAzSafe) 4") [1, 0] },
    { name := "Azure: floating task versions are unpinned, x.y.z is pinned",
      run := fun _ => evalNats (prelude ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelAzUnsafe) 5\n" ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelAzSafe) 5\n" ++
        "#eval b2n (Scry.ciTaskVersionPinned \"1.2.3\")\n" ++
        "#eval b2n (Scry.ciTaskVersionPinned \"1.2\")\n" ++
        "#eval b2n (Scry.ciTaskVersionPinned \"1\")") [1, 0, 1, 0, 0] },
    { name := "Azure: parameters in a script and in a template path are two findings",
      run := fun _ => evalNats (prelude ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelAzUnsafe) 6\n" ++
        "#eval ruleC (Scry.ciAnalyze Scry.ciModelAzSafe) 6") [2, 0] },
    { name := "Azure: resources and extends appear as includes/resource nodes",
      run := fun _ => evalNats (prelude ++
        "def m := optModel (Scry.ciParseModel \"azure-pipelines.yml\" Scry.ciAzResourceFile)\n" ++
        "#eval match m.workflows with\n" ++
        "  | .cons wf _ =>\n" ++
        "    Nat.add (Nat.mul (List.length wf.includes) 100)\n" ++
        "      (Nat.add (Nat.mul (List.length wf.resources) 10)\n" ++
        "        (List.length (List.filter (fun r => String.eq r.kind \"container\") wf.resources)))\n" ++
        "  | .nil => 0") [121] },
    { name := "Datalog: the positive program checks, with every relation in stratum 0",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.Program.check Scry.ciProgram with\n" ++
        "  | .none => 999\n" ++
        "  | .some strata => Nat.add 1 (sumN strata)") [1] },
    { name := "certificates: every finding carries a checked derivation",
      run := fun _ => evalNats (prelude ++
        "#eval match Scry.ciAnalyze Scry.ciModelGhUnsafe with\n" ++
        "  | r => Nat.add (Nat.mul (lenF r) 10) (certsOk r)\n" ++
        "#eval match Scry.ciAnalyze Scry.ciModelAzUnsafe with\n" ++
        "  | r => Nat.add (Nat.mul (lenF r) 10) (certsOk r)\n" ++
        "#eval b2n (Nat.lt 0 (match Scry.ciAnalyze Scry.ciModelGhUnsafe with\n" ++
        "  | r => certSum r))") [55, 44, 1] },
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
        "#eval lenF (Scry.ciAnalyze Scry.ciModelSafe)\n" ++
        "#eval b2n (Scry.ciCheckCerts (Scry.ciAnalyze Scry.ciModelSafe))") [0, 1] },
    { name := "report rendering starts with the finding count",
      run := fun _ => evalNats (prelude ++
        "#eval b2n (String.startsWith (Scry.ciRenderReport (Scry.ciAnalyze Scry.ciModelGhUnsafe))\n" ++
        "  \"findings: 5\")") [1] }
  ]

builtin_initialize registerGroup group

end Tests.ScryCi
