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
    { name := "P1: refinement, fairness, leader safety/liveness and the bridge are axiom-free", run := fun _ =>
        okLibs ("import Dist.Refine\n" ++
          "import Dist.Fairness\n" ++
          "import Dist.Leader\n" ++
          "import Dist.Bridge\n" ++
          "#print axioms Refines.safety\n" ++
          "#print axioms Refines.safetyInv\n" ++
          "#print axioms Refines.comp\n" ++
          "#print axioms Refines.liveness_fails\n" ++
          "#print axioms LTS.fairRank\n" ++
          "#print axioms Leader.safety\n" ++
          "#print axioms Leader.safety_unique\n" ++
          "#print axioms Elect2.live\n" ++
          "#print axioms Elect2.idleNoLeader\n" ++
          "#print axioms Elect2.idleNotFair\n" ++
          "#print axioms Bridge.SpecModel.safety\n")
          [
            "'Refines.safety' does not depend on any axioms",
            "'Refines.safetyInv' does not depend on any axioms",
            "'Refines.comp' does not depend on any axioms",
            "'Refines.liveness_fails' does not depend on any axioms",
            "'LTS.fairRank' does not depend on any axioms",
            "'Leader.safety' does not depend on any axioms",
            "'Leader.safety_unique' does not depend on any axioms",
            "'Elect2.live' does not depend on any axioms",
            "'Elect2.idleNoLeader' does not depend on any axioms",
            "'Elect2.idleNotFair' does not depend on any axioms",
            "'Bridge.SpecModel.safety' does not depend on any axioms"
          ] },
    { name := "P1: the fair advance chooses a leader", run := fun _ =>
        okLibs ("import Dist.Leader\n" ++
          "#eval Elect2.leaderB (Elect2.advance Elect2.init)\n" ++
          "#eval Elect2.leaderB Elect2.init\n")
          [".true", ".false"] },
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
