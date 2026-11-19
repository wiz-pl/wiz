# STC constraint prototypes (2026-11-19)

Small, self-contained witnesses for the decisions in
`/workspace/wiz-notes/stc-constraints-2026-11-19.md`. They are not imported by
`STC.lean`; they are a build target only so the evidence is reproducible.

| file | proves | run |
|---|---|---|
| `Totality.lean` | a fuel-indexed, non-`mutual` dispatcher is total and has **no axioms** | `lake build STC.Prototype.Totality` (watch for `does not depend on any axioms`) |
| `Totality.wiz` | the same shape is accepted by the host | `wiz check … Totality.wiz` |
| `IndProp.wiz` | native inductive propositions (issue #252) work | `wiz check … IndProp.wiz` |
| `IndPropReject.wiz` | large elimination of a non-singleton inductive proposition is rejected | expected failure |
| `Church.wiz` | Church `∃`/`∨` eliminate into a constant `Prop` | `wiz check … Church.wiz` |
| `ChurchDep.wiz` | their dependent eliminator is **not** available | expected failure |

Use `--no-cache --cache-verify off` for the CLI checks (the shared cache is slow; see
`stc-m0-triage.md` §2.4).
