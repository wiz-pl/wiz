import Wiz
import Tests.Harness

/-!
# Analysis files, revision manifests, claims and widget payloads (`Scry.AnalysisFile`)

The pure half of "a scry run is an ordinary Wiz file" (`wiz-notes/scry-as-wiz.md`):

* `#ingest "dir" into "graph.quire"` is a command that expands to a checked
  `Scry.IngestSpec` declaration; the scanner that finds declarations and their line;
* `Scry.mergeFacts` (the frontend) and `Scry.viewOfFacts`, the small projection a claim
  reads;
* the **revision manifest**: tree/git revision round-trip and the fresh/stale verdict
  (including a kind change and a dirty git tree);
* the claim (`calls-recorded`), the diagnostics, the code action, and the
  `wiz.widget/1` bundle with the `scry.analysis/1` extension.

The Quire half (encoding, `openQ`/`getQ`/`putQ`, snapshots, the writer lock) is compiled
code and is tested by `drafts/scry-analysis/tests/effect-test.wiz`.
-/

open Wiz

namespace Tests.ScryAnalysis

/-- Every `lib/*.wiz`, `lib/*/*.wiz` and `scry/src/Scry/*.wiz` (as `Scry.X`): one loader
for the suite (`Tests.scryLoader`). -/
def loader : IO (Name → Option String) := Tests.scryLoader

def imports : String :=
  "import Scry.AnalysisFile\nimport Scry.Facts\nimport Web.Widget\nimport Json\nimport Text\n"

def runProbe (body : String) : IO (List String) := do
  let src := imports ++ body ++ "\n"
  let loader ← loader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure (s.messages.toList.map (·.text))

def evalTexts (body : String) (expected : List String) : IO Unit := do
  checkEq expected (← runProbe body)

/-- The fixture graph (the same stores as `drafts/scry-analysis/fixtures`), as Wiz
constructors, and the view/claim over it. -/
def fixtures : String :=
  "def nd (id : Nat) (kind field : String) (parent : Option Nat) (s e : Nat) : Scry.Node :=\n" ++
  "  Scry.Node.mk (Scry.nodeId id) kind field\n" ++
  "    (match parent with | .some p => .some (Scry.nodeId p) | .none => .none)\n" ++
  "    (Scry.Span.mk s e) .true .false .false\n" ++
  "def eg (id src dst : Nat) (label : String) : Scry.Edge :=\n" ++
  "  Scry.Edge.mk (Scry.edgeId id) (Scry.nodeId src) (Scry.nodeId dst) label\n" ++
  "def store (files : List Scry.SourceFile) (nodes : List Scry.Node) (edges : List Scry.Edge)\n" ++
  "    (rels : List Scry.Relation) : Scry.Facts :=\n" ++
  "  match Scry.finishFacts \"scry-facts\" 1 \"c\" files nodes edges rels with\n" ++
  "  | .ok f => f\n" ++
  "  | .error _ => Scry.emptyGraph\n" ++
  "def alpha : Scry.Facts := store\n" ++
  "  [Scry.SourceFile.mk 0 \"alpha.c\" 40]\n" ++
  "  [nd 0 \"translation_unit\" \"\" .none 0 40,\n" ++
  "   nd 1 \"function_definition\" \"\" (.some 0) 0 30,\n" ++
  "   nd 2 \"call_expression\" \"\" (.some 1) 5 15,\n" ++
  "   nd 3 \"identifier\" \"function\" (.some 2) 5 8]\n" ++
  "  [eg 0 0 1 \"child\", eg 1 1 2 \"child\", eg 2 2 3 \"function\"]\n" ++
  "  [Scry.Relation.mk (Scry.relId 0) \"call\" 2 [[2, 3]]]\n" ++
  "def beta : Scry.Facts := store\n" ++
  "  [Scry.SourceFile.mk 0 \"beta.c\" 24]\n" ++
  "  [nd 0 \"translation_unit\" \"\" .none 0 24,\n" ++
  "   nd 1 \"function_definition\" \"\" (.some 0) 0 18,\n" ++
  "   nd 2 \"call_expression\" \"\" (.some 1) 4 14]\n" ++
  "  [eg 0 0 1 \"child\", eg 1 1 2 \"child\"]\n" ++
  "  [Scry.Relation.mk (Scry.relId 0) \"call\" 2 []]\n" ++
  "def merged : Scry.Facts := match Scry.mergeFacts [alpha, beta] with\n" ++
  "  | .ok f => f | .error _ => Scry.emptyGraph\n" ++
  "def graphView : Scry.GraphView := Scry.viewOfFacts merged\n" ++
  "def claim : Scry.ClaimResult := Scry.claimCalls graphView\n" ++
  "def errStore : Scry.Facts := store\n" ++
  "  [Scry.SourceFile.mk 0 \"bad.c\" 8]\n" ++
  "  [Scry.Node.mk (Scry.nodeId 0) \"ERROR\" \"\" .none (Scry.Span.mk 0 4) .false .true .false]\n" ++
  "  [] []\n" ++
  "def rev : Scry.Revision := Scry.Revision.mk \"tree\" \"fnv1a64\" \"t_abc\" .false \"\"\n" ++
  "def mf : Scry.Manifest := Scry.Manifest.mk \"scry-graph-manifest/1\" \"fixtures\"\n" ++
  "  \"graph.quire\" 3 rev [] [] [] [] [] 9 5 8 graphView\n"

def group : Group where
  name := "scry-analysis"
  exercise := "Scry analysis files: #ingest, view, revision manifest, claim, widget payload"
  parallel := true
  cases := [
    { name := "#ingest parses and the scanner reports line and paths",
      run := fun _ => evalTexts
        ("#ingest \"fixtures\" into \"graph.quire\"\n" ++
         "def src : String := \"import X\\n\\n#ingest \\\"fixtures\\\" into \\\"build/graph.quire\\\"\\n\"\n" ++
         "#eval Nat.repr (List.length (Scry.ingestLines src))\n" ++
         "#eval match Scry.ingestLines src with\n" ++
         "  | .cons l _ => Nat.add l.line (Nat.add (String.length l.spec.root) (String.length l.spec.dest))\n" ++
         "  | .nil => 0")
        ["\"1\"", "28"] },
    { name := "merge/view/claim: files, unioned relations, file_of, the refuted claim",
      run := fun _ => evalTexts (fixtures ++
        "#eval Nat.repr (List.length merged.files)\n" ++
        "#eval Nat.repr (List.length merged.nodes)\n" ++
        "#eval Nat.repr (List.length (List.filter (fun r => String.eq r.name \"call\") merged.relations))\n" ++
        "#eval match Scry.findRelation merged.relations \"file_of\" with\n" ++
        "  | .some r => Nat.beq (List.length r.tuples) 7\n" ++
        "  | .none => Bool.false\n" ++
        "#eval Nat.repr (List.length graphView.calls)\n" ++
        "#eval Nat.repr (List.length graphView.callHeads)\n" ++
        "#eval String.eq claim.status \"refuted\"\n" ++
        "#eval Nat.repr (List.length claim.findings)\n" ++
        "#eval match claim.findings with\n" ++
        "  | .cons x _ => String.eq x.file \"beta.c\"\n" ++
        "  | .nil => Bool.false\n" ++
        "#eval match claim.findings with\n" ++
        "  | .cons x _ => Nat.beq x.node 7\n" ++
        "  | .nil => Bool.false\n" ++
        "#eval String.eq (Scry.claimNoErrors (Scry.viewOfFacts errStore)).status \"refuted\"\n" ++
        "#eval Nat.repr (List.length (Scry.claimNoErrors (Scry.viewOfFacts errStore)).findings)")
        ["\"2\"", "\"9\"", "\"1\"", ".true", "\"2\"", "\"1\"", ".true", "\"1\"",
         ".true", ".true", ".true", "\"1\""] },
    { name := "the revision manifest round-trips and the verdict is fresh/stale",
      run := fun _ => evalTexts (fixtures ++
        "#eval match Scry.manifestOfText (Scry.manifestText mf) with\n" ++
        "  | .ok m => Nat.beq m.gen 3\n" ++
        "  | .error _ => Bool.false\n" ++
        "#eval match Scry.manifestOfText (Scry.manifestText mf) with\n" ++
        "  | .ok m => String.eq m.revision.value \"t_abc\"\n" ++
        "  | .error _ => Bool.false\n" ++
        "#eval match Scry.revisionVerdict mf rev with | .fresh => 1 | _ => 0\n" ++
        "#eval match Scry.revisionVerdict mf (Scry.Revision.mk \"tree\" \"fnv1a64\" \"t_other\" .false \"\") with | .stale _ _ _ => 1 | _ => 0\n" ++
        "#eval match Scry.revisionVerdict mf (Scry.Revision.mk \"git\" \"git-sha1\" \"deadbeef\" .false \"\") with | .stale _ _ _ => 1 | _ => 0\n" ++
        "#eval match Scry.revisionVerdict mf (Scry.Revision.mk \"tree\" \"fnv1a64\" \"t_abc\" .true \"d\") with | .stale _ _ _ => 1 | _ => 0\n" ++
        "#eval Scry.renderRevision rev\n" ++
        "#eval String.contains (Scry.renderRevisionVerdict (Scry.RevisionVerdict.stale rev (Scry.Revision.mk \"tree\" \"fnv1a64\" \"t_other\" .false \"\") \"changed\")) \"t_other\"")
        [".true", ".true", "1", "1", "1", "1", "\"tree:fnv1a64:t_abc\"", ".true"] },
    { name := "diagnostics and the code action have the LSP shapes",
      run := fun _ => evalTexts
        ("def d : Scry.IngestDiagnostic := Scry.IngestDiagnostic.mk \"error\" \"bad store\" \"a.wiz\" 3 0 12\n" ++
         "#eval Scry.renderDiagnostic d\n" ++
         "#eval match Json.getPath (Scry.diagJson d) [\"severity\"] with\n" ++
         "  | .some v => match Json.asNat v with | .some n => Nat.repr n | .none => \"x\"\n" ++
         "  | .none => \"x\"\n" ++
         "#eval match Json.getPath (Scry.diagJson d) [\"range\", \"start\", \"line\"] with\n" ++
         "  | .some v => match Json.asNat v with | .some n => Nat.repr n | .none => \"x\"\n" ++
         "  | .none => \"x\"\n" ++
         "def ca : Json := Scry.ingestCodeActionJson \"file:///a.wiz\" \"fixtures\" \"graph.quire\" 10 40\n" ++
         "#eval Json.getStr ca \"kind\"\n" ++
         "#eval match Json.get ca \"command\" with\n" ++
         "  | .some c => Json.getStr c \"command\"\n" ++
         "  | .none => \"\"")
        ["\"error:a.wiz:3:0: bad store\"", "\"1\"", "\"2\"", "\"refactor.rewrite\"",
         "\"wiz.scry.ingest\""] },
    { name := "the widget payload is a wiz.widget/1 bundle with the scry extension",
      run := fun _ => evalTexts (fixtures ++
        "def disp : String := Scry.analysisDisplay claim graphView\n" ++
        "#eval String.startsWith disp \"WIZ_WIDGET:\"\n" ++
        "#eval match Widget.parseDisplay disp with\n" ++
        "  | .some j => Json.getStr j \"schema\"\n" ++
        "  | .none => \"none\"\n" ++
        "#eval match Widget.parseDisplay disp with\n" ++
        "  | .some j => match Json.get j \"scry\" with\n" ++
        "    | .some e => Json.getStr e \"schema\"\n" ++
        "    | .none => \"\"\n" ++
        "  | .none => \"\"\n" ++
        "#eval match Widget.parseDisplay disp with\n" ++
        "  | .some j => match Json.get j \"scry\" with\n" ++
        "    | .some e => match Json.get e \"claim\" with\n" ++
        "      | .some c => Json.getStr c \"status\"\n" ++
        "      | .none => \"\"\n" ++
        "    | .none => \"\"\n" ++
        "  | .none => \"\"\n" ++
        "#eval Nat.repr (List.length (Widget.widgetsOf disp))\n" ++
        "#eval match Widget.parseDisplay disp with\n" ++
        "  | .some j => String.contains (Json.getStr j \"html\") \"wiz-widget\"\n" ++
        "  | .none => Bool.false\n" ++
        "#eval match Widget.parseDisplay disp with\n" ++
        "  | .some j => match Json.get j \"scry\" with\n" ++
        "    | .some e => match Json.get e \"findings\" with\n" ++
        "      | .some fs => Nat.repr (List.length (Json.asList fs))\n" ++
        "      | .none => \"0\"\n" ++
        "    | .none => \"0\"\n" ++
        "  | .none => \"0\"")
        [".true", "\"wiz.widget/1\"", "\"scry.analysis/1\"", "\"refuted\"", "\"3\"",
         ".true", "\"1\""] }
  ]

builtin_initialize registerGroup group

end Tests.ScryAnalysis
