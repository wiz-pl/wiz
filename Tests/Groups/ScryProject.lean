import Tests.Elab

set_option compiler.extract_closed false

/-!
# scry-project: the project findings index on Quire and JSON

`Scry.ProjectIO` computes a project's findings a second time from scratch even when only
the report's JSON is wanted. `Scry.cacheFindings` (`scry/src/Scry/ProjectCache.wiz`,
backed by `lib/Scry/QuireFindings.wiz`) stores the findings **index** — one 32-byte Quire
record per finding, or the same rows as a JSON document — and reads it back on a warm
run. This case runs the real driver over `scry/corpus/project/taint` and asserts:

* both backends round-trip the same rows (the same finding ids, count and fingerprint);
* a warm run is a hit, and the severity index answers the same count as the report;
* a garbage Quire file is a clean `corrupt` miss (rewritten, never a panic), and a
  truncated one is too.

The case needs the project package (`scry/src`, `scry/gen`) and its native shim, so it is
built with `linkRunRoots`; the C compiler the driver runs is the test toolchain's own, so
a node with no `cc` on `PATH` still works.
-/

namespace Tests.Elab

/-- The driver program. `cc` is the test toolchain's C compiler (the driver runs
`cc -E` on each translation unit). -/
def scryProjectSource (cc : String) : String :=
  "import Scry.NativeLink\nimport Sys\nimport Text\nimport Json\n" ++
  "import Scry.Project\nimport Scry.ProjectIO\nimport Scry.ProjectTaint\n" ++
  "import Scry.ProjectCache\nimport Scry.QuireFindings\nimport Scry.TaintCmd\n\n" ++
  "def check (label : String) (ok : Bool) : EIO Unit :=\n" ++
  "  EIO.lift (match ok with\n" ++
  "    | .true => IO.println (label ++ \": ok\")\n" ++
  "    | .false => IO.bind (IO.println (label ++ \": FAILED\"))\n" ++
  "        (fun _ => Process.exit 1))\n\n" ++
  "def run : EIO Unit := do\n" ++
  s!"  let cc := \"{cc}\"\n" ++
  "  tmp ← FS.createTempDir;\n" ++
  "  built ← Scry.ProjectIO.buildProject \"scry/corpus/project/taint\" .none cc .true .false .false .nil Scry.CacheOpts.none;\n" ++
  "  pack ← Scry.loadTaintPack .none;\n" ++
  "  let rep := Scry.analyzeProject built.1 pack built.2;\n" ++
  "  let rows := Scry.rowsOfReport rep;\n" ++
  "  let id := Scry.ProjectIO.projectIndexId rep.project;\n" ++
  "  check (String.append \"index: \" (String.append (Nat.repr (List.length rows)) \" findings\"))\n" ++
  "    (Nat.lt 0 (List.length rows));\n" ++
  "  let json : Scry.CacheOpts := Scry.CacheOpts.mk .true tmp .json;\n" ++
  "  let quire : Scry.CacheOpts := Scry.CacheOpts.mk .true tmp .quire;\n" ++
  "  j1 ← Scry.cacheFindings json id rows;\n" ++
  "  check \"index: json cold\" (String.eq j1.reason \"cold\");\n" ++
  "  j2 ← Scry.cacheFindings json id rows;\n" ++
  "  check \"index: json hit\" (String.eq j2.reason \"hit\");\n" ++
  "  q1 ← Scry.cacheFindings quire id rows;\n" ++
  "  check \"index: quire cold\" (String.eq q1.reason \"cold\");\n" ++
  "  q2 ← Scry.cacheFindings quire id rows;\n" ++
  "  check \"index: quire hit\" (String.eq q2.reason \"hit\");\n" ++
  "  jl ← Scry.findingsLoad json id;\n" ++
  "  ql ← Scry.findingsLoad quire id;\n" ++
  "  let same := match jl, ql with\n" ++
  "    | .ok a, .ok b => Bool.and (Nat.beq (List.length a) (List.length b))\n" ++
  "        (UIntN.beq (Scry.fiPrint a) (Scry.fiPrint b))\n" ++
  "    | _, _ => .false;\n" ++
  "  check \"index: json and quire hold the same findings\" same;\n" ++
  "  let sev0 := List.length (List.filter (fun r => Nat.beq r.severity 0) rows);\n" ++
  "  qc ← Scry.findingsQuery quire id 0;\n" ++
  "  check \"index: quire severity query\"\n" ++
  "    (match qc with | .ok n => Nat.beq n sev0 | .error _ => .false);\n" ++
  "  jc ← Scry.findingsQuery json id 0;\n" ++
  "  check \"index: json severity query\"\n" ++
  "    (match jc with | .ok n => Nat.beq n sev0 | .error _ => .false);\n" ++
  "  let qpath := Scry.findingsCachePath quire id;\n" ++
  "  FS.writeFile qpath \"not a quire image\\n\";\n" ++
  "  q3 ← Scry.cacheFindings quire id rows;\n" ++
  "  check \"index: corrupt quire is a miss\" (String.eq q3.reason \"corrupt\");\n" ++
  "  q4 ← Scry.cacheFindings quire id rows;\n" ++
  "  check \"index: quire hit after repair\" (String.eq q4.reason \"hit\");\n" ++
  "  qb ← FS.readBytes qpath;\n" ++
  "  FS.writeBytes qpath (Bytes.slice qb 0 100);\n" ++
  "  q5 ← Scry.cacheFindings quire id rows;\n" ++
  "  check \"index: truncated quire is a miss\" (String.eq q5.reason \"corrupt\");\n" ++
  "  FS.removeAll tmp\n\n" ++
  "def main : IO Unit := EIO.toIO run\n"

def scryProjectExpected : String :=
  "index: 2 findings: ok\n" ++
  "index: json cold: ok\n" ++
  "index: json hit: ok\n" ++
  "index: quire cold: ok\n" ++
  "index: quire hit: ok\n" ++
  "index: json and quire hold the same findings: ok\n" ++
  "index: quire severity query: ok\n" ++
  "index: json severity query: ok\n" ++
  "index: corrupt quire is a miss: ok\n" ++
  "index: quire hit after repair: ok\n" ++
  "index: truncated quire is a miss: ok\n"

def scryProject : IO Unit := do
  let tc ← toolchain
  linkRunRoots ["scry/src", "scry/gen"] [("main.wiz", scryProjectSource tc.cc)]
    scryProjectExpected

def scryProjectGroup : Group where
  name := "scry-project"
  exercise := "scry: the project findings index on Quire and JSON"
  cases := [
    { name := "findings index: same rows from both backends, corrupt/truncated Quire is a miss",
      run := fun _ => scryProject }
  ]

builtin_initialize registerGroup scryProjectGroup

end Tests.Elab
