import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-!
The root package's examples are tests (`Package.tests "examples" "examples"` in
`grail.wiz`), and this group is what makes them a gate: each case runs `runTests` over a
name range of `examples/`, so every `examples/*.expected` is compared in CI, not only
read by a human running `grail test` in the checkout.

Three of the cases are ranges rather than one case so a failure names a readable block
(and so the shard can be split); they cover the same files the package-wide `grail test`
does, minus `examples/tour/` (group `tour` already compares those 14) and the nested
`examples/fate-index/sources/*` packages (left out by `Grail.testFiles`, as by
`grail test`). A new `examples/*.wiz` falls into one of the ranges without an edit
here; only a new *nested* directory or a new name class would need one.

`-- test: skip` in an example itself still applies: the benchmarks are skipped with a
reason and are reported as skipped, not passed. Each case lists the skips it expects, so
a new skip (or a benchmark that stops skipping) fails the gate: skipping is a decision,
not a way to hide a failure. A `-- test: run` example is compiled and its `main`'s output
compared, so its `.expected` is a real output oracle.

The first case guards that correspondence: an `.expected` whose content is not the shape
its marker produces (program output under a check marker, check messages under a run
marker, a missing file) fails there, with the file named, before the ranges compare it
against the wrong output. The check is cheap (it reads the files) and self-tests the
classifier it uses.
-/

/-- A line of a `check` test's output, `path:line:col: severity: text`
(`Grail.Elab.render` over `Msg.render`). -/
def isCheckMessage (line : String) : Bool :=
  match line.splitOn ":" with
  | path :: pos :: col :: sev :: _ =>
    !path.isEmpty && !pos.isEmpty && !col.isEmpty
      && pos.toList.all Char.isDigit && col.toList.all Char.isDigit
      && (sev.trimAscii.toString == "error" || sev.trimAscii.toString == "warning"
          || sev.trimAscii.toString == "info")
  | _ => false

/-- The first non-empty line of a text. -/
def firstNonEmpty (s : String) : Option String :=
  (s.splitOn "\n").find? fun l => l.trimAscii != ""

/-- Why an example's `.expected` does not match its `-- test:` kind (`none`: it does).

A `check` test is compared against the messages of checking the file, so a `.expected`
whose first line is not one of those messages cannot have come from checking it: the
file is a program whose output was meant to be compared, and its first line must be
`-- test: run`. (That is the bug this catches: `examples/array.expected` held a digest,
`1039243342`, under no marker, and was compared against the empty check output. The
`check` test passed only because both sides were empty.) A `run` test is compared
against what `main` prints, so check messages in its `.expected` mean the marker is
wrong. The path in a check message must be the example itself, or a copy-pasted golden
compares one file's messages against another's. -/
def expectedMismatch (file : String) (kind : Grail.TestKind) (expected : Option String) :
    Option String :=
  let expFile := ((System.FilePath.mk file).withExtension "expected").toString
  match kind with
  | .skip _ => none
  | .check =>
    match expected with
    | none => some s!"{file}: no {expFile} (a check test needs its output; `grail test --update` writes it)"
    | some e =>
      match firstNonEmpty e with
      | none => none
      | some l =>
        if !isCheckMessage l then
          some s!"{file}: its {expFile} holds program output, but it has no `-- test: run` \
            (a check test is compared against the check messages, here empty): {l}"
        else
          match l.splitOn ":" with
          | p :: _ => if p == file then none
            else some s!"{file}: its {expFile} holds messages for {p}, not for this file"
          | [] => none
  | .run =>
    match expected with
    | none => some s!"{file}: a run test needs {expFile} (`grail test --update` writes it)"
    | some e =>
      match firstNonEmpty e with
      | none => none
      | some l =>
        if isCheckMessage l then
          some s!"{file}: it says `-- test: run` but its {expFile} holds check messages, so the file is checked, not run: {l}"
        else none

/-- Every example whose `.expected` disagrees with its marker. -/
def markerFailures : IO (List String) := do
  let files ← Grail.testFiles "." "examples"
  let mut bad : Array String := #[]
  for f in files do
    match Grail.TestKind.ofSource (← IO.FS.readFile f) with
    | .error e => bad := bad.push s!"{f}: {e}"
    | .ok kind =>
      let expFile := (System.FilePath.mk f).withExtension "expected"
      let expected ← if ← expFile.pathExists then some <$> IO.FS.readFile expFile else pure none
      if let some m := expectedMismatch f kind expected then bad := bad.push m
  pure bad.toList

/-- The guard that every `.expected` is the shape its marker produces. It runs before the
ranges and names every disagreement, so a digest under a check marker (or check messages
under a run marker) fails the group instead of being compared against the wrong output. -/
def markerCase : Case :=
  { name := "example markers: every .expected matches its `-- test:` kind"
    run := fun _ => do
      -- the classifier's self-test: a real check message passes, the digest does not
      check (isCheckMessage "examples/x.wiz:1:2: error: boom") "the guard rejects a check message"
      check (!isCheckMessage "1039243342") "the guard reads a bare digest as a check message"
      check ((expectedMismatch "examples/x.wiz" .check (some "1039243342\n")).isSome)
        "the guard misses a digest under a check marker"
      check ((expectedMismatch "examples/x.wiz" .run (some "1039243342\n")).isNone)
        "the guard rejects a digest under a run marker"
      check ((expectedMismatch "examples/x.wiz" .run (some "examples/x.wiz:1:2: info: ok\n")).isSome)
        "the guard misses check messages under a run marker"
      check ((expectedMismatch "examples/x.wiz" .check (some "examples/x.wiz:1:2: info: ok\n")).isNone)
        "the guard rejects a real check output"
      let bad ← markerFailures
      unless bad.isEmpty do
        throw (IO.userError (s!"{bad.length} example marker(s) disagree with their .expected:\n  "
          ++ "\n  ".intercalate bad)) }

/-- The root examples (`examples/*.wiz`, not `examples/tour/`) and, for each, the
`grail test` result, compared against its `.expected`; `keep` picks one case's range and
`skips` is the exact set of `-- test: skip` files there (a new skip, or a benchmark that
stops skipping, fails the case). -/
def examplesCase (name : String) (keep : String → Bool) (skips : List String) : Case :=
  { name := name, run := fun _ => do
      let files ← Grail.testFiles "." "examples"
      let sel := files.toList.filter fun f => !f.startsWith "examples/tour/" && keep f
      check (!sel.isEmpty) "no examples in this range (the range in Tests/Groups/GrailExamples.lean is stale)"
      -- (the driver's elaboration cache, from `--cache`: the files share imports, so
      -- the first one pays for `Prelude`, the rest replay it)
      let tc ← toolchain
      let (res, _) ← runTests "." tc (filters := sel)
      checkEq sel.length res.size
      checkEq skips (res.filter (·.skipped) |>.toList.map (·.file))
      for t in res do
        if t.skipped then
          check (!t.message.isEmpty) s!"{t.file}: -- test: skip needs a reason"
        -- (`run` tests need the C toolchain; on a machine without it the case is
        -- skipped, as the tour's are)
        else if !t.ok && (t.message.splitOn "gmp.h").length > 1 then
          skip "no toolchain"; return
        else check t.ok s!"{t.file}: {t.message}" }

def examplesGroup : Group where
  name := "examples"
  exercise := "examples/ (grail test)"
  cases :=
    [ markerCase
    , examplesCase "examples/ before hdl: the stage demos, classes, std-like and FFI examples"
        (fun f => f < "examples/hdl") ["examples/closed-table-bench.wiz"]
    , examplesCase "examples/hdl*: the HDL examples, including the large netlist goldens"
        (fun f => f < "examples/import_c" && !(f < "examples/hdl"))
        ["examples/hdl-crc-link.wiz", "examples/hdl-sim-bench.wiz", "examples/hdl-verified-full.wiz",
         "examples/hdl-verified-native.wiz"]
    , examplesCase "examples/ from import_c: the library, Scry, Rune and Pervasive examples"
        (fun f => !(f < "examples/import_c"))
        ["examples/natives-bench.wiz", "examples/plot.wiz", "examples/scry-datalog-bench.wiz"] ]

builtin_initialize registerGroup examplesGroup

end Tests.Grail
