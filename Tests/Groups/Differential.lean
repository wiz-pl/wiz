import Tests.Differential

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Differential

/-- Every case of the corpus against every pipeline, as separate test cases so a run
reports passes, skips and diffs individually.  The golden baseline is
`Tests/Differential/baseline.tsv`; regenerate it with `scripts/differential.sh --update`
after reviewing the change. -/
def differentialGroup : Group where
  name := "differential"
  exercise := "COMP-02 (pipeline differential)"
  shard := "differential"
  cases := (corpus.flatMap fun sp =>
    allPipelines.map fun p =>
      { name := s!"{sp.name} / {p.name}"
        run := fun _ => do
          let rows ← readBaseline
          let r := checkBaseline rows (← runCase sp p)
          match r.verdict with
          | .pass => pure ()
          | .skipped => skip r.note
          | .diff =>
            throw (IO.userError s!"{sp.name} / {p.name}: {r.note}\nobserved: {r.observed}\nexit: {r.exit}") })

builtin_initialize registerGroup differentialGroup

end Tests.Differential
