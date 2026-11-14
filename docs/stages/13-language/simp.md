# `simp` is library code

The `simp` of [stage 6h](../06-macros/simp.md) is a Wiz tactic like `rw` and `unfold`:
a function `Syntax → TacticM Unit`, registered with `attribute [tactic tactic.simp]`, in
`lib/Prelude.wiz`. Its algorithm — rule order, direction (`← h`), the fuel bound, the
messages — is Wiz code; the elaborator only gained one request, `Tac.rewriteAt`, which
matches a rule's `∀` telescope with fresh metavariables and builds the transport.

This is the language-scale point of the stage-13 work: a tactic of this size is a
library artifact, not a compiler feature. Writing it in Wiz hit no new syntax and no new
elaborator capability beyond the request; the parts that stayed host-side are the parts
that need the kernel's `Term` and the unifier (a reflected `Expr` has no metavariable),
not policy. It also keeps the self-hosted frontend's route open: once its `Tac`/`Expr`
layer reaches parity, the same source runs there (`wiz-notes/simp-design.md` §6.6,
P0–P5).

```
import Prelude
def ex (a b : Nat) (h : a = b) (P : Nat → Prop) (pb : P b) : P a := by
  simp [h]
  exact pb
```

S1 (this stage) is goal rewriting with an explicit rule list. `[simp]`/the default
`lib/SimpLemmas.wiz` set, conditional rules (dischargers), `simp at h` and `simp?` are
S2–S4 and need their own requests (`getSimpLemmas`, premise goals, `changeHyp`/
`addHyp`/`clearHyp`). There is no automatic closer: `simp` rewrites and the user writes
`rfl`/`exact`/`assumption`, and `simp only []` is the identity.
