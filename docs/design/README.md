# Design documents

These documents describe designs that are implemented in the Wiz repository, and the
reasons for them: the problem each one solves, the rules as the code implements them,
the alternatives that were considered and rejected, what remains open, and where the
tests are. They complement the reference specification ([CoreSpec](../CoreSpec.md)) and
the [soundness ledger](../Status.md), which use the same issue names.

* [mandatory-sorts.md](mandatory-sorts.md): every `Π`/`Σ` carries its two components'
  sorts and every `ULift` its content's, checked by both kernels (U5, U5b, D2).
* [prf-marker.md](prf-marker.md): the proof marker `prf.{l} t`, which lets both kernels
  promise never to evaluate a proof (P2).
* [conv-regularity.md](conv-regularity.md): regularity at inert types (InReg_conv),
  decided by the conversion checker, with ground equality as the evaluator's fast path
  (D1, P1).
* [infoview-protocol.md](infoview-protocol.md): the server side of the infoview protocol
  (`wiz/interactiveGoals` and friends).
* [linear-case-design.md](linear-case-design.md): linear values in and across data:
  quantity-indexed `match`, linear fields.
