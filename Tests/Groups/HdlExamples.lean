import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-!
# `=hdl-examples`: the Hdl package's goldens (`cd hdl && grail test`)

`hdl/` is a package of its own (`separate-repos.md` §1.2): its manifest is
`hdl/grail.wiz`, with `Package.lib "hdl" "src"` and `Package.tests "examples" "examples"`,
so `cd hdl && grail test` compares every `hdl/examples/*.wiz` with its `.expected`. The
root `examples` group covers the root package only, so once the `hdl-*` examples moved out
of `examples/` nothing in CI ran these goldens: this group is their gate.

Each case runs `runTests "hdl"` over a name range of `hdl/examples/`, so every
`.expected` there is compared in CI, not only read by a human running `grail test` in the
package. The ranges are the same split the root `examples` group uses (one before the
middle of the list, one after), and a new `hdl/examples/*.wiz` falls into one of them
without an edit here; only a new *nested* directory would need one.

`-- test: skip` in an example still applies: four are skipped with a reason
(`hdl-crc-link`, `hdl-sim-bench`, `hdl-verified-full`, `hdl-verified-native`) and are
reported as skipped, not passed. Each case lists the skips it expects, so a new skip (or
one that stops skipping) fails the gate: skipping is a decision, not a way to hide a
failure. A `-- test: run` example (`hdl-spi`, `hdl-stream`) is compiled and its `main`'s
output compared, so its `.expected` is a real output oracle.

Two examples in that range need minutes, not seconds: `hdl-uart-temporal.wiz` (the
UART's temporal properties) and `hdl-verified.wiz` (kernel-checked at full width). The
second range therefore gives every test a 900 s limit, so their `.expected` files are
compared too. They are also elaborated by cases of their own in the same shard
(`hdl-uart-temporal` and `hdl-verified`, which check properties and axioms); that
duplication is deliberate, so no golden is left out of the comparison.

The golden set is asserted, not assumed: the guard below fails unless
`hdl/examples` holds 36 `*.wiz`, exactly 32 of them have a `.expected` (the other four
are `-- test: skip`) and each of those 32 is in the walk. A move or rename that drops
one of them fails here instead of silently shrinking the comparison.

The first case guards that correspondence: an `.expected` whose content is not the shape
its marker produces (program output under a check marker, check messages under a run
marker, a missing file, or a check-message path naming another file) fails there, with
the file named, before the ranges compare it against the wrong output.
-/

/-- A line of a `check` test's output, `path:line:col: severity: text`. -/
def hdlIsCheckMessage (line : String) : Bool :=
  match line.splitOn ":" with
  | path :: pos :: col :: sev :: _ =>
    !path.isEmpty && !pos.isEmpty && !col.isEmpty
      && pos.toList.all Char.isDigit && col.toList.all Char.isDigit
      && (sev.trimAscii.toString == "error" || sev.trimAscii.toString == "warning"
          || sev.trimAscii.toString == "info")
  | _ => false

/-- The first non-empty line of a text. -/
def hdlFirstNonEmpty (s : String) : Option String :=
  (s.splitOn "\n").find? fun l => l.trimAscii != ""

/-- Why an example's `.expected` does not match its `-- test:` kind (`none`: it does).
The path in a check message must be the example itself, or a copy-pasted golden compares
one file's messages against another's. -/
def hdlExpectedMismatch (file : String) (kind : Grail.TestKind)
    (expected : Option String) : Option String :=
  let expFile := ((System.FilePath.mk file).withExtension "expected").toString
  match kind with
  | .skip _ => none
  | .check =>
    match expected with
    | none => some s!"{file}: no {expFile} (a check test needs its output; `grail test --update` writes it)"
    | some e =>
      match hdlFirstNonEmpty e with
      | none => none
      | some l =>
        if !hdlIsCheckMessage l then
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
      match hdlFirstNonEmpty e with
      | none => none
      | some l =>
        if hdlIsCheckMessage l then
          some s!"{file}: it says `-- test: run` but its {expFile} holds check messages, so the file is checked, not run: {l}"
        else none

/-- Every `hdl/examples/*.wiz` whose `.expected` disagrees with its marker. -/
def hdlMarkerFailures : IO (List String) := do
  let files ← Grail.testFiles "hdl" "examples"
  let pkg : System.FilePath := "hdl"
  let mut bad : Array String := #[]
  for f in files do
    match Grail.TestKind.ofSource (← IO.FS.readFile (pkg / f)) with
    | .error e => bad := bad.push s!"{f}: {e}"
    | .ok kind =>
      let expFile := (pkg / f).withExtension "expected"
      let expected ← if ← expFile.pathExists then some <$> IO.FS.readFile expFile else pure none
      if let some m := hdlExpectedMismatch f kind expected then bad := bad.push m
  pure bad.toList

/-- The four `hdl/examples/*.wiz` that are `-- test: skip` (they have no `.expected`). -/
def hdlSkips : List String :=
  ["examples/hdl-crc-link.wiz", "examples/hdl-sim-bench.wiz",
   "examples/hdl-verified-full.wiz", "examples/hdl-verified-native.wiz"]

/-- The package's goldens: `hdl/examples/*.wiz` minus the four skips (32 today), each
compared against its `.expected`. -/
def hdlGoldens : IO (List String) := do
  let files ← Grail.testFiles "hdl" "examples"
  pure (files.toList.filter fun f => !hdlSkips.contains f)

/-- The marker guard: it runs before the ranges and names every disagreement. -/
def hdlMarkerCase : Case :=
  { name := "hdl example markers: every .expected matches its `-- test:` kind"
    run := fun _ => do
      -- the classifier's self-test: a real check message passes, a digest does not
      check (hdlIsCheckMessage "examples/x.wiz:1:2: error: boom") "the guard rejects a check message"
      check (!hdlIsCheckMessage "1039243342") "the guard reads a bare digest as a check message"
      check ((hdlExpectedMismatch "examples/x.wiz" .check (some "1039243342\n")).isSome)
        "the guard misses a digest under a check marker"
      check ((hdlExpectedMismatch "examples/x.wiz" .run (some "1039243342\n")).isNone)
        "the guard rejects a digest under a run marker"
      check ((hdlExpectedMismatch "examples/x.wiz" .run (some "examples/x.wiz:1:2: info: ok\n")).isSome)
        "the guard misses check messages under a run marker"
      check ((hdlExpectedMismatch "examples/x.wiz" .check (some "examples/x.wiz:1:2: info: ok\n")).isNone)
        "the guard rejects a real check output"
      -- the golden set is total: a move that drops one fails here, not silently
      let files ← Grail.testFiles "hdl" "examples"
      check (files.size == 36)
        s!"hdl/examples has {files.size} .wiz; expected 36 (32 goldens + 4 `-- test: skip`): update HdlExamples.lean"
      let goldens ← hdlGoldens
      check (goldens.length == 32)
        s!"{goldens.length} goldens; expected 32 (a `.expected` is compared for each): update HdlExamples.lean"
      let pkg : System.FilePath := "hdl"
      for f in files do
        let hasExpected ← ((pkg / f).withExtension "expected").pathExists
        check (hasExpected == !hdlSkips.contains f)
          s!"{f}: expected={hasExpected}, skip={hdlSkips.contains f} (a golden without .expected, or a skip with one)"
      let bad ← hdlMarkerFailures
      unless bad.isEmpty do
        throw (IO.userError (s!"{bad.length} example marker(s) disagree with their .expected:\n  "
          ++ "\n  ".intercalate bad)) }

/-- The `hdl/examples/*.wiz` in one range and, for each, the `grail test` result compared
against its `.expected`; `keep` picks the range, `skips` is the exact set of
`-- test: skip` files there, and `limitSecs` is the per-test limit (the UART temporal and
verified examples need more than the harness's 300 s default). -/
def hdlExamplesCase (name : String) (keep : String → Bool) (skips : List String)
    (limitSecs : Nat := 300) : Case :=
  { name := name, run := fun _ => do
      let files ← Grail.testFiles "hdl" "examples"
      let sel := files.toList.filter keep
      check (!sel.isEmpty) "no examples in this range (the range in Tests/Groups/HdlExamples.lean is stale)"
      -- (the driver's elaboration cache, from `--cache`: the files share imports, so the
      -- first one pays for Prelude/Hdl.Core, the rest replay it)
      let tc ← toolchain
      let (res, _) ← runTests "hdl" tc (testTimeoutMs := some (1000 * limitSecs)) (filters := sel)
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

def hdlExamplesGroup : Group where
  name := "hdl-examples"
  exercise := "hdl/examples/ (grail test in the hdl package)"
  shard := "hdl"
  cases :=
    [ hdlMarkerCase
    , hdlExamplesCase "hdl/examples/ up to mem: the arithmetic, bus, CDC, display and formal goldens"
        (fun f => f < "examples/hdl-operators.wiz")
        ["examples/hdl-crc-link.wiz"]
    , hdlExamplesCase "hdl/examples/ from operators: the memory, simulation, protocol and verified goldens"
        (fun f => !(f < "examples/hdl-operators.wiz"))
        ["examples/hdl-sim-bench.wiz", "examples/hdl-verified-full.wiz",
         "examples/hdl-verified-native.wiz"]
        900 ]

builtin_initialize registerGroup hdlExamplesGroup

end Tests.Grail
