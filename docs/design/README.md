# Design documents

These documents describe designs that are implemented in the Wiz repository, and the
reasons for them: the problem each one solves, the rules as the code implements them,
the alternatives that were considered and rejected, what remains open, and where the
tests are. They complement the reference specification ([CoreSpec](../CoreSpec.md)) and
the [soundness ledger](../Status.md), which use the same issue names.

**Policy: match Lean's extensibility interfaces, not its feature count.** The target is
not a feature-for-feature copy of Lean 4. It is the four *interfaces* that let a library
extend the language without a kernel change: data-driven term elaborators, user-extensible
`deriving` handlers, hygienic macros, and `simp only`-style explicit lemma sets. The reason
is concrete: a hard-coded name switch (today `Unit`/`Empty`/`Qty`/`Size`, the
`Desc`/`μ`/`ν` table and the string-literal encoding) makes every new data primitive a
compiler change (`wiz-notes/audit-kernel.md` #6), so adding features faster than these
seams entrenches the switch. The registry shape that `wiz-notes/targets-ext.md` describes
for targets — one `Entry` record, a table resolved by the consumer,
`Wiz/Lint/Basic.lean:49` as the only registry-shaped ABI in the tree — is the same shape
the elaborator needs. No new mechanism is proposed here: this paragraph is the policy
sentence, and `wiz-notes/targets-ext.md` is the design input.

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
