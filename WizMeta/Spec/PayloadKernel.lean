import WizMeta.Spec.Rule

/-!
# Equations between constructors: variant Kernel

`con x =_{μ D i} con y` computes to an equation between the payloads. Three variants; a
system takes one. What each gives up:

| | stable under substitution | `cons x xs = cons y ys` at `List A` (a field at a type variable) | `succ m = succ n` |
|---|---|---|---|
| **Kernel** (both kernels) | **no** | `(x = y) × (cast … xs = ys)`, the Σ rule | `m = n` |
| **Stuck** | yes | **stuck**: no injectivity of constructors with a field at a neutral type | `m = n` |
| **Uniform** | yes | the Σ rule | the Σ rule: `(#1 = #1) × (cast … (m, _) = (n, _))`, an equation with a cast |

* *Kernel.* By the description: `ret` gives `True`; a tag field (`Enum k` or a lift of it)
  with two canonical tags continues at that constructor's description if they are equal
  and is the Σ rule if they differ; a recursive field gives the field's equation, paired
  with the rest unless the rest is `ret`; **any other field takes the Σ rule, also when
  its type is neutral**. A substitution can turn a neutral field type into `Enum k`, and
  then the other rule applies, with a result that is equivalent but not convertible. So a
  substitution instance of a well-typed term can be ill typed (E5b: `λ A a b h. h.1`, with
  `h` an equation of two one-field constructors at a field of type `A`, is accepted, and
  its instance at `A := Enum 2` is not; the regression is the case "E5b: …" of the group
  *meta* in `Tests/Meta.lean`, which pins all three variants). The premise "not a tag
  type" is negative (it has to hold of a weak-head normal form, including a neutral one),
  which is why this file takes the notion of weak-head normal type as a parameter.
* *Stuck.* The same, but the Σ rule only at a canonical field type; at a neutral one the
  equation is stuck. Every premise is positive, so the rules are stable. The price is in
  the table.
* *Uniform.* No shortcut. Stable, and no injectivity is lost, but every equation between
  constructors carries a cast of the remaining fields along the tags' equation. That cast
  is between convertible types; whether it goes away is exactly regularity. With
  regularity decided by conversion (`InReg.lean`; `docs/design/conv-regularity.md`) it does
  at inert types, so there the uniform rule is as usable as the shortcut (`succ m = succ
  n` gives `m = n` up to conversion of the *terms*, though the two *types* are still
  different propositions). At a polymorphic type the cast is at a neutral type, where no
  rule removes it: only the axiom `castRefl`. So the conv design makes **Uniform** work
  for inert data, and makes none of the three work fully at polymorphic types.
-/

namespace WizMeta.Spec

/-- A description that is visibly not `ret`. -/
def NonRet' : Tm → Prop
  | .darg .. | .drec .. | .dhrec .. => True
  | _ => False

/-- `whnfTy Γ S`: the type `S` is in weak-head normal form (canonical or neutral). -/
inductive PayloadKernel (whnfTy : Ctx → Tm → Prop) : Rules
  | eq {Γ : Ctx} {x I D i y r : Tm} {l : Lvl} : PayloadKernel whnfTy ⟨[Γ ⊢ .con x ∶ .mu l I D i, Γ ⊢ .con y ∶ .mu l I D i, .peq Γ l I (.muFamily l I D) i D x y r],
      Γ ⊢ .eq (.mu l I D i) (.con x) (.con y) ⟶ r ∶ .sort 0⟩
  | eqRedL {Γ : Ctx} {a a' I D i b : Tm} {l : Lvl} : PayloadKernel whnfTy ⟨[Γ ⊢ a ⟶ a' ∶ .mu l I D i, Γ ⊢ b ∶ .mu l I D i],
      Γ ⊢ .eq (.mu l I D i) a b ⟶ .eq (.mu l I D i) a' b ∶ .sort 0⟩
  | eqRedR {Γ : Ctx} {a I D i b b' : Tm} {l : Lvl} : PayloadKernel whnfTy ⟨[Γ ⊢ a ∶ .mu l I D i, Γ ⊢ b ⟶ b' ∶ .mu l I D i],
      Γ ⊢ .eq (.mu l I D i) a b ⟶ .eq (.mu l I D i) a b' ∶ .sort 0⟩
  | peqRet {Γ : Ctx} {D j I X i x y : Tm} {l : Lvl} : PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .dret j ∶ .desc l I], .peq Γ l I X i D x y .True'⟩
  /-- a tag field, the same canonical tag on both sides -/
  | peqTag {Γ : Ctx} {D q E I x y X i r : Tm} {l : Lvl} {k a : Nat} : PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .darg q (.enum k) E ∶ .desc l I, Γ ⊢ .fst x ≡ .tag k a ∶ .enum k,
        Γ ⊢ .fst y ≡ .tag k a ∶ .enum k, .peq Γ l I X i (.app E (.tag k a)) (.snd x) (.snd y) r],
      .peq Γ l I X i D x y r⟩
  | peqTagLifted {Γ : Ctx} {D q E I x y X i r : Tm} {u l : Lvl} {k a : Nat} : PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .darg q (.ulift u (.enum k)) E ∶ .desc l I, Γ ⊢ .down (.fst x) ≡ .tag k a ∶ .enum k,
        Γ ⊢ .down (.fst y) ≡ .tag k a ∶ .enum k, .peq Γ l I X i (.app E (.up (.tag k a))) (.snd x) (.snd y) r],
      .peq Γ l I X i D x y r⟩
  /-- two different canonical tags: the `Σ` rule (whose first component is `False`) -/
  | peqTagDiff {Γ : Ctx} {D q E I x y X i : Tm} {l : Lvl} {a b k : Nat} : a ≠ b →
      PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .darg q (.enum k) E ∶ .desc l I, Γ ⊢ .fst x ≡ .tag k a ∶ .enum k, Γ ⊢ .fst y ≡ .tag k b ∶ .enum k],
        .peq Γ l I X i D x y (.eq (.interp l I (.darg q (.enum k) E) X i) x y)⟩
  | peqTagLiftedDiff {Γ : Ctx} {D q E I x y X i : Tm} {u l : Lvl} {a b k : Nat} : a ≠ b →
      PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .darg q (.ulift u (.enum k)) E ∶ .desc l I, Γ ⊢ .down (.fst x) ≡ .tag k a ∶ .enum k,
          Γ ⊢ .down (.fst y) ≡ .tag k b ∶ .enum k],
        .peq Γ l I X i D x y (.eq (.interp l I (.darg q (.ulift u (.enum k)) E) X i) x y)⟩
  /-- a field at any weak-head normal type that is not a tag type, canonical or neutral:
  the `Σ` rule -/
  | peqField {Γ : Ctx} {S D q E I X i x y : Tm} {l : Lvl} : whnfTy Γ S → (∀ k, S ≠ .enum k) → (∀ u k, S ≠ .ulift u (.enum k)) →
      PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .darg q S E ∶ .desc l I], .peq Γ l I X i D x y (.eq (.interp l I (.darg q S E) X i) x y)⟩
  | peqRecLast {Γ : Ctx} {D q j j' I X i x y : Tm} {l : Lvl} : PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .drec q j (.dret j') ∶ .desc l I], .peq Γ l I X i D x y (.eq (.app X j) (.fst x) (.fst y))⟩
  | peqRec {Γ : Ctx} {E D q j I X i x y r : Tm} {l : Lvl} : NonRet' E →
      PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .drec q j E ∶ .desc l I, .peq Γ l I X i E (.snd x) (.snd y) r],
        .peq Γ l I X i D x y (.sigma .zero (some 0) (.eq (.app X j) (.fst x) (.fst y)) r.shift)⟩
  | peqHrecLast {Γ : Ctx} {D q H j j' I X i x y : Tm} {l : Lvl} : PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .dhrec q H j (.dret j') ∶ .desc l I],
      .peq Γ l I X i D x y (.eq (.hrecFieldTy l H j X) (.fst x) (.fst y))⟩
  | peqHrec {Γ : Ctx} {E D q H j I X i x y r : Tm} {l : Lvl} : NonRet' E →
      PayloadKernel whnfTy ⟨[Γ ⊢ D ≡ .dhrec q H j E ∶ .desc l I, .peq Γ l I X i E (.snd x) (.snd y) r],
        .peq Γ l I X i D x y (.sigma .zero (some 0) (.eq (.hrecFieldTy l H j X) (.fst x) (.fst y)) r.shift)⟩

end WizMeta.Spec
