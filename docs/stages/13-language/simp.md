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
layer reaches parity, the same source runs there, with only the host requests to
port.

```
import Prelude
def ex (a b : Nat) (h : a = b) (P : Nat → Prop) (pb : P b) : P a := by
  simp [h]
  exact pb
```

S1 is goal rewriting with an explicit rule list. S2 adds `attribute [simp]`, the
per-library default sets (`lib/Nat.wiz`, `lib/Int.wiz`, `lib/Logic.wiz`,
`lib/Data/ListLemmas.wiz`, with `lib/SimpLemmas.wiz` as the umbrella), `local` scoping and
the `Tac.getSimpLemmas` read; conditional rules (dischargers), `simp at h` and `simp?`
are S3–S4 and need their own requests (premise goals, `changeHyp`/`addHyp`/`clearHyp`).
There is no automatic closer: `simp` rewrites and the user writes
`rfl`/`exact`/`assumption`, and `simp only []` is the identity.

**P0 (landed).** `Tac.rewriteAt` is now depth-aware: it walks the goal type with the
context of each λ binder, matches the rule there, and transports the child equality
through the parent (under a λ the proof is pointwise function equality). Rewriting under
a `Π` *type former* is still not done (it needs the P1/P2 type-congruence path), and
dependent application arguments fail at the kernel rather than producing a wrong term.
The Wiz driver records the rules that fired (`rulesUsed`), and `simp?` traces
`Try this: simp only […]` plus `; rfl` when the residual goal is reflexive. The step
budget remains 100 rewrites per goal; the host matcher is one request per winning node,
and the Wiz loop restarts the pass on a rewrite as before.
