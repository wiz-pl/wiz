import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Distributed P0 (`wiz-notes/distributed-proofs.md` §11): the generic temporal/LTS
core, the finite checker with proved soundness, and two-phase-commit safety for all `N`.
The positive instance is the `N = 2` decision projection (`ok`, 45 reachable states);
the broken twin commits a participant without the coordinator and returns a concrete
path. -/
def distProofsGroup : Group where
  name := "dist-proofs"
  exercise := "Distributed P0 (2PC safety)"
  cases := [
    { name := "the library checks, and the safety and checker theorems are axiom-free", run := fun _ =>
        okLibs ("import Dist.TwoPhaseFinite\n" ++
          "#print axioms TwoPC.safety\n" ++
          "#print axioms TwoPC.safetyDuring\n" ++
          "#print axioms Checker.Model.check_ok_spec\n" ++
          "#print axioms Checker.Model.check_bad_spec\n" ++
          "#print axioms TwoPC.Small.twoPC2_checked\n")
          [
            "'TwoPC.safety' does not depend on any axioms",
            "'TwoPC.safetyDuring' does not depend on any axioms",
            "'Checker.Model.check_ok_spec' does not depend on any axioms",
            "'Checker.Model.check_bad_spec' does not depend on any axioms",
            "'TwoPC.Small.twoPC2_checked' does not depend on any axioms"
          ] },
    { name := "positive: the N=2 instance is ok, and the finite safety theorem applies", run := fun _ =>
        okLibs ("import Dist.TwoPhaseFinite\n" ++
          "#eval Checker.Report.show TwoPC.Small.show2 TwoPC.Small.check2\n" ++
          "#print axioms TwoPC.Small.check2_ok\n" ++
          "#print axioms TwoPC.Small.twoPC2_checked\n")
          [
            "\"ok: 45 visited states\"",
            "'TwoPC.Small.check2_ok' does not depend on any axioms",
            "'TwoPC.Small.twoPC2_checked' does not depend on any axioms"
          ] },
    { name := "counterexample: a participant commits before the coordinator, with a concrete path", run := fun _ =>
        okLibs ("import Dist.TwoPhaseFinite\n" ++
          "#eval Checker.Report.show TwoPC.Small.show2 TwoPC.Small.brokenCheck\n" ++
          "#print axioms TwoPC.Small.broken_violation\n")
          [
            "\"bad: c=prepared p0=committed p1=init -> c=prepared p0=prepared p1=init -> c=prepared p0=init p1=init -> c=init p0=init p1=init\"",
            "'TwoPC.Small.broken_violation' does not depend on any axioms"
          ] },
    { name := "bounded traces: `safetyDuring` is axiom-free, and a bounded search is unknown", run := fun _ =>
        okLibs ("import Dist.TwoPhaseFinite\n" ++
          "#print axioms TwoPC.safetyDuring\n" ++
          "#eval Checker.Report.show TwoPC.Small.show2 (TwoPC.Small.model2.check 1)\n")
          [
            "'TwoPC.safetyDuring' does not depend on any axioms",
            "\"unknown: 1 visited states\""
          ] },
    { name := "the checker's soundness theorems are axiom-free", run := fun _ =>
        okLibs ("import Dist.TwoPhaseFinite\n" ++
          "#print axioms Checker.Model.check_ok_spec\n" ++
          "#print axioms Checker.Model.check_bad_spec\n")
          [
            "'Checker.Model.check_ok_spec' does not depend on any axioms",
            "'Checker.Model.check_bad_spec' does not depend on any axioms"
          ] }
  ]

builtin_initialize registerGroup distProofsGroup

end Tests.Elab
