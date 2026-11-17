import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# `=selfhost-parity`: the parity matrix's claim is checked, not asserted

`wiz-notes/selfhost-parity.md` used to be maintained by hand: its counts drifted and an
**S** row could cite no test at all.  The rows now live in `selfhost-parity.tsv`, and
`scripts/parity-matrix.py` checks that:

* every **S** row names a case that exists in a self-host group and (transitively)
  reaches `selfhostCompiler`/`selfhostChecker` in `Tests/Elab.lean` — a case that
  compiles `selfhost/*.wiz` with the Lean host does not count;
* every **P** row says what is missing;
* every **M** row names no positive case;
* every case in the six self-host groups maps to a row;
* rows with no case are listed in `scripts/parity-matrix-overrides.tsv` with a reason;
* the note's `## Counts` section equals the TSV's counts (when the notes tree is
  present; CI has no `wiz-notes/`, and the checker says so).

The group is in the `selfhost` shard, so a matrix edit that stops being provable fails
CI with the row id.
-/

def selfhostParityGroup : Group where
  name := "selfhost-parity"
  exercise := "the parity matrix is derived from the test sources and its S rows have self-hosted evidence"
  shard := "selfhost"
  cases := [
    { name := "every S row has a case that runs the self-hosted binary; every case maps to a row", run := fun _ => do
        let out ← IO.Process.output
          { cmd := "python3", args := #["scripts/parity-matrix.py", "--check"] }
        unless out.exitCode == 0 do
          throw (IO.userError s!"scripts/parity-matrix.py --check failed ({out.exitCode}):\n{out.stdout}\n{out.stderr}")
        -- the checker's summary is the evidence the run did something: a matrix with
        -- rows and cases, not an empty file
        unless (out.stdout.splitOn "rows:").length > 1 do
          throw (IO.userError s!"parity-matrix.py printed no row summary:\n{out.stdout}") }
  ]

builtin_initialize registerGroup selfhostParityGroup

end Tests.Elab
