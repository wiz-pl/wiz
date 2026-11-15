import Tests.ElabFuzz

open Wiz

/-!
# The elaborator fuzzer's test group

`Tests/ElabFuzz.lean` holds the seeded generator, the properties and the minimiser; the
group runs a small fixed corpus (fast, inside a child process under `timeout` so that a
panic or a hang is a failing case rather than a stuck suite), the minimised regression
inputs under `Tests/data/elab-fuzz/regressions/`, and the generator's own should-reject
templates (so that the soundness oracle is not vacuous).

The long campaign is not a case.  From the package root, with the tests binary built:

```
heavy --mem 3G timeout 3600 .lake/build/bin/tests --elab-fuzz 2000 1 --depth 4 \
  --out /tmp/elab-fuzz/findings
```

That runs 2000 samples from seed 1 (bounds: the count, `--depth`, and the outer
`timeout`), prints `FAIL seed …` and the command-minimised input for every finding, and
writes `${out}/<kind>-<seed>.wiz` with the minimised source and `.txt` with the details.
Replay one sample (the full generated source and its findings) with

```
.lake/build/bin/tests --elab-fuzz-sample SEED
```

replay a saved (minimised or full) input, with its intended verdict, and minimise any
finding it still shows:

```
.lake/build/bin/tests --elab-fuzz-replay FILE [accept|reject|any]
```

and re-check a minimised file with `.lake/build/bin/wiz check FILE`.  The default
`--depth` is 3; 4 is the long mode's setting.  The fixed corpus is `corpus` below; it
runs as the first case, in a child under `timeout`, so a panic or hang fails the case.
-/

namespace Tests.ElabFuzz

/-- The fixed corpus: seeds whose generated programs exercise every declaration shape
(the choice is deterministic, so the list is a corpus). -/
def corpus : String :=
  "1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28," ++
  "29,30,31,32,33,34,35,36,37,38,39,40,64,96,128,192,256,384,512"

/-- Run the campaign in a child process, bounded by `secs`; returns its exit code and
output.  The child is this same binary, so it has the suite's toolchain flags. -/
def runChild (args : List String) (secs : Nat) : IO (UInt32 × String) := do
  let self ← IO.appPath
  let out ← IO.Process.output
    { cmd := "sh", args := #["-c",
        s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --elab-fuzz " ++
          " ".intercalate args, self.toString] }
  pure (out.exitCode, out.stdout ++ out.stderr)

/-- The last `n` lines of a campaign's output (a failure can be long: the minimised
input is printed). -/
def tailLines (s : String) (n : Nat) : String :=
  let ls := s.splitOn "\n"
  "\n".intercalate (ls.drop (ls.length - min n ls.length))

def numberAfter (s key : String) : Option Nat := Id.run do
  for l in s.splitOn "\n" do
    if l.startsWith key then
      let rest := (l.drop key.length).toString
      let digits := (rest.toList.takeWhile Char.isDigit)
      return String.toNat? (String.ofList digits)
  return none

/-- The fixed corpus: it finishes, no input panics or hangs, every finding (if any) is
reported with its seed and minimised input, and the corpus is not vacuous (it accepts
some programs and rejects others). -/
def corpusCase : IO Unit := do
  let (code, out) ← runChild ["--seeds", corpus, "--depth", "3"] 120
  if code == 124 then
    throw (IO.userError s!"the corpus did not finish within 120 s (a hang?); last output:\n{tailLines out 40}")
  unless code == 0 do
    throw (IO.userError s!"the corpus reported findings or crashed (exit {code});\n{tailLines out 60}")
  check (out.contains "campaign:") "the child did not run the campaign (stale binary?)"
  check (out.contains "0 finding(s)") s!"the campaign did not report zero findings:\n{tailLines out 20}"
  match numberAfter out "stats: accepted=" with
  | some a => check (a ≥ 10) s!"only {a} accepted samples: the corpus is close to vacuous"
  | none => throw (IO.userError s!"no stats line:\n{tailLines out 10}")

/-- `-- expect: accept|reject` (required) and `-- expect-error: FRAGMENT` (optional) in
a regression file's header comments. -/
structure Regression where
  path : System.FilePath
  expect : Expect
  errorFragment : Option String

def parseRegression (path : System.FilePath) (text : String) : IO Regression := do
  let mut expect : Option Expect := none
  let mut frag : Option String := none
  for l in text.splitOn "\n" do
    let t := l.trimAscii.toString
    if t.startsWith "-- expect:" then
      let v := (t.drop "-- expect:".length).trimAscii.toString
      expect := if v == "accept" then some .accept else if v == "reject" then some .reject else none
    else if t.startsWith "-- expect-error:" then
      frag := some ((t.drop "-- expect-error:".length).trimAscii.toString)
  match expect with
  | some e => pure { path, expect := e, errorFragment := frag }
  | none => throw (IO.userError s!"{path}: no `-- expect: accept|reject` header")

def checkDir (dir : System.FilePath) (label : String) : IO Unit := do
  unless ← dir.pathExists do
    throw (IO.userError s!"missing {label} directory {dir}")
  let entries ← dir.readDir
  let files := entries.toList.map (·.path) |>.mergeSort (fun a b => a.toString < b.toString)
  check (!files.isEmpty) s!"no {label} files in {dir}"
  for path in files do
    let text ← IO.FS.readFile path
    let r ← parseRegression path text
    let ck ← checkSample { seed := 0, source := text, expect := r.expect, what := path.toString }
    for f in ck.failures do
      throw (IO.userError s!"{path}: {f.render}")
    if let some frag := r.errorFragment then
      let errs := errorsOf (Wiz.runFrontend (R := ZeroOneMany) text)
      unless errs.any (fun m => (m.text.splitOn frag).length > 1) do
        throw (IO.userError (s!"{path}: no error mentions '{frag}':\n" ++
          "\n".intercalate (errs.toList.map (·.text))))

def regressionCase : IO Unit :=
  checkDir "Tests/data/elab-fuzz/regressions" "regression"

/-- Curated programs for the features the generator is aimed at (implicit arguments,
instance search, levels, patterns, recursive definitions, coinduction): the same
properties, on inputs whose intent is clear. -/
def curatedCase : IO Unit :=
  checkDir "Tests/data/elab-fuzz/corpus" "curated"

/-- The should-reject templates, generated: the oracle is not vacuous if they are all
rejected, and a rejection must carry a span (checked by `checkSample`). -/
def rejectCase : IO Unit := do
  for seed in [1:25] do
    let (decl, _) := G.eval seed (genReject [])
    let ck ← checkSample { seed, source := prelude ++ "\n" ++ decl ++ "\n", expect := .reject,
                           what := "reject template" }
    for f in ck.failures do
      throw (IO.userError s!"seed {seed}: {f.render}\n{decl}")

def group : Group where
  name := "elab-fuzz"
  exercise := "elaborator fuzzing"
  cases := [
    { name := "fixed corpus: no panic or hang, stable, spans, fmt round-trip",
      run := fun _ => corpusCase },
    { name := "regressions: minimised findings",
      run := fun _ => regressionCase },
    { name := "curated feature corpus",
      run := fun _ => curatedCase },
    { name := "should-reject templates are rejected",
      run := fun _ => rejectCase }
  ]

builtin_initialize registerGroup group

end Tests.ElabFuzz
