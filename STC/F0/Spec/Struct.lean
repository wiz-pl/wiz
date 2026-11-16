import STC.F0.Spec.Rule
/-!
# The two structural conversion rules: conversion typing and context conversion

`F0/Sorting.lean` recorded the `conv`/`cong` gap: F0's rules do not type the two ends of a
conversion at its own type, and they do not type the second endpoint of a `cong`
conclusion (the codomain `B'` of `Pi.cong` lives in `A' :: Γ`, which no rule reaches from
`B'`'s typing in `A :: Γ`). This file adds the two rules the design note names:

    Γ ⊢ v ≡ w ∶ C
    ────────────────   eqTyped      (and, by `Core.symm`, for `w`)
    Γ ⊢ v ∶ C

    Γ ⊢ A ≡ A' ∶ Sort i      (A :: Γ) ⊢ J
    ────────────────────────────────────────   ctxConv
    (A' :: Γ) ⊢ J

Both are **licensed only for closed signatures** (`Sig.Closed`), which is why the rule set
is parameterized by the signature: `Struct sg` has instances only when `Sig.Closed sg`.

* `eqTyped` is in fact sound for any signature: every rule that generates a conversion
  types its left endpoint (`refl` in its premise; `symm`/`trans`/`eqConv`/`redConv` from
  their premises; `irrel`, the `cong`s, η and `reflTy` in their premises, with `Core.conv`
  for the endpoint of `eqConv`). It is gated with `ctxConv` so that the two rules have one
  licensing condition. It is not the kernels' `InReg` (`Core.lean` rules that out): it
  types the ends of `≡`, it does not reduce `cast A A e t` to `t`.

* `ctxConv` is the renaming-for-conversion lemma. Its proof needs `Sig.Closed` exactly as
  the renaming lemma does: a context entry `A` must be renamed, and a global constant's
  declared type must be closed for that to be well typed. `J`'s variables are unchanged:
  the rule replaces a context entry's type, it does not rename anything.

The interface between the two: `ctxConv` needs `eqTyped` to type the new context entry
(`F0/Typing.lean`, `ctxConv_ty` and friends), and `eqTyped` needs nothing.

**What the two rules do not fix.** They close the `conv`/`cong` cases, but not the `trans`
case of the sorting lemma: `ctxConv`/`eqTyped` type conversions, they do not give them
canonical heads. See `F0/Sorting.lean` for the remaining obligation (`ConvJoin`) and for
the refutation of `TyUnique` (`F0/Typing.lean`) that these rules also make possible.
-/


namespace STC
namespace F0
namespace Spec

/-- The two structural conversion rules, as a rule set of its own so that the fragment
without them (`F0Base`) keeps exactly the rules the renaming and substitution lemmas were
proved for. -/
inductive Struct (sg : Sig) : Rules where
  /-- `eqTyped`: a conversion types its left endpoint at its own type. `Core.symm` gives
  the right endpoint (`Typing.eqTyped_right`). -/
  | eqTyped {hsg : Sig.Closed sg} {Γ : Ctx} {t u C : Tm} :
      Struct sg ⟨[Γ ⊢ t ≡ u ∶ C], Γ ⊢ t ∶ C⟩
  /-- `ctxConv`: a judgment about terms in `A :: Γ` is a judgment about the same terms in
  `A' :: Γ`, when `A ≡ A'` at a sort. The hypothesis records that `j` is a judgment in
  `A :: Γ`; `j`'s terms are unchanged (`Jdg.rectx`). -/
  | ctxConv {hsg : Sig.Closed sg} {Γ : Ctx} {A A' : Tm} {s : Srt} {j : Jdg}
      (h : j.ctx = A :: Γ) :
      Struct sg ⟨[Γ ⊢ A ≡ A' ∶ .sort s, j], j.rectx (A' :: Γ)⟩

end Spec
end F0
end STC
