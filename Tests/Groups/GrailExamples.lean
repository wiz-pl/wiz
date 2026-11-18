import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-!
The root package's examples are tests (`Package.tests "examples" "examples"` in
`grail.wiz`), and this group is what makes them a gate: each case runs `runTests` over a
name range of `examples/`, so every `examples/*.expected` is compared in CI, not only
read by a human running `grail test` in the checkout.

The cases are ranges rather than one case so a failure names a readable block (and so
the shard can be split); they cover the same files the package-wide `grail test` does,
minus `examples/tour/` (group `tour` already compares those 14) and the nested
`examples/grail-index/sources/*` packages (left out by `Grail.testFiles`, as by
`grail test`). A new `examples/*.wiz` falls into one of the ranges without an edit
here; only a new *nested* directory or a new name class would need one.

`-- test: skip` in an example itself still applies: the benchmarks are skipped with a
reason and are reported as skipped, not passed. Each case lists the skips it expects, so
a new skip (or a benchmark that stops skipping) fails the gate: skipping is a decision,
not a way to hide a failure. A `-- test: run` example is compiled and its `main`'s output
compared, so its `.expected` is a real output oracle.
-/

/-- The root examples (`examples/*.wiz`, not `examples/tour/`) and, for each, the
`grail test` result, compared against its `.expected`; `keep` picks one case's range and
`skips` is the exact set of `-- test: skip` files there (a new skip, or a benchmark that
stops skipping, fails the case). -/
def examplesCase (name : String) (keep : String → Bool) (skips : List String) : Case :=
  { name := name, run := fun _ => do
      let files ← Grail.testFiles "." "examples"
      let sel := files.toList.filter fun f => !f.startsWith "examples/tour/" && keep f
      check (!sel.isEmpty) "no examples in this range (the range in Tests/Groups/GrailExamples.lean is stale)"
      let tc ← toolchain
      let tc : Toolchain := { tc with cacheDir := some (← tc.cacheDir.getDM IO.FS.createTempDir) }
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
    [ examplesCase "examples/ before hdl: the stage demos, classes, std-like and FFI examples"
        (fun f => f < "examples/hdl") ["examples/closed-table-bench.wiz"]
    , examplesCase "examples/hdl*: the HDL examples, including the large netlist goldens"
        (fun f => f < "examples/import_c" && !(f < "examples/hdl"))
        ["examples/hdl-sim-bench.wiz", "examples/hdl-verified-full.wiz",
         "examples/hdl-verified-native.wiz"]
    , examplesCase "examples/ from import_c: the library, Scry, Rune and Pervasive examples"
        (fun f => !(f < "examples/import_c"))
        ["examples/natives-bench.wiz", "examples/plot.wiz", "examples/scry-datalog-bench.wiz"] ]

builtin_initialize registerGroup examplesGroup

end Tests.Grail
