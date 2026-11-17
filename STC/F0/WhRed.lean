import STC.F0.Substitution
/-!
# `WhRed` is empty at propositions

`WHN` (`Obligations.lean`) is stated only at a type `A` whose sort is not `prop`, the
side condition that lets the strategy leave proofs alone. Its justification is that
`WhRed` (`Spec/Fragments.lean`) --- a reduction of a *relevant* term --- has no instance
at a proposition:

    WhRed T Γ t u A = Derivable T (Γ ⊢ t ⟶ u ∶ A) ∧ ∃ s, Derivable T (Γ ⊢ A ∶ .sort s) ∧ s.NeverZero.

The second conjunct is what fails: `WhRed` carries a nonzero sort of `A`, while a
proposition is typed at `prop`. Making the two sorts equal is a **sorting lemma**
(`SortUniqueAt` below): every term has at most one sort. It is a consequence of
regularity plus uniqueness of types; `stc-plan.md` lists uniqueness of types as an M1
consequence, and M0 has no inversion/regularity lemma, so it is not derivable from the
rules as given here without that development. The theorem below therefore takes it as an
explicit hypothesis, which is exactly the missing statement; the reduction judgment in
`WhRed`'s first conjunct plays no role in the emptiness (there *are* reductions at
propositions, e.g. `Pi.beta` into a `Π` ending in `Prop`; they are just not `WhRed`).

`F0/Sorting.lean` reduces `SortUniqueAt` to two named M1 statements (`TyUnique`,
`ConvInjSort`) and proves the reduction, including the version of the theorem here that
takes those two instead of `SortUniqueAt` at the term. It also records which rule-level
cases block the two statements: the `trans` case of conversion needs the normalisation
(canonical-head) theorem (`ConvJoin`); the `conv`/`cong` rule gaps it once recorded are
now rules (`Spec/Struct.lean`: `eqTyped`, `ctxConv`). Read that file before attempting the
lemma.
-/


namespace STC
namespace F0
namespace Spec

/-- At most one sort for a term in a given context. The missing ingredient of
`WhRed.empty_at_prop`: a proposition has sort `prop` and cannot also have a nonzero
sort. -/
def SortUniqueAt (sg : Sig) (Γ : Ctx) (A : Tm) : Prop :=
  ∀ s s', Derivable (F0 sg) (Γ ⊢ A ∶ .sort s) →
    Derivable (F0 sg) (Γ ⊢ A ∶ .sort s') → s = s'

/-- The global form of `SortUniqueAt`. -/
def SortUnique (sg : Sig) : Prop := ∀ Γ A, SortUniqueAt sg Γ A

/-- A proposition has no other sort, given `SortUniqueAt` at the term. -/
theorem SortUniqueAt.sort_eq_prop {sg : Sig} {Γ : Ctx} {A : Tm}
    (h : SortUniqueAt sg Γ A) (hp : Derivable (F0 sg) (Γ ⊢ A ∶ .sort .prop)) {s : Srt}
    (hs : Derivable (F0 sg) (Γ ⊢ A ∶ .sort s)) : s = .prop :=
  h s .prop hs hp

/-- **`WhRed` is empty at propositions.** `WhRed` carries a nonzero sort of `A`; at a
proposition the sort is `prop`, and `SortUniqueAt` identifies the two, contradicting
`Srt.NeverZero`. This is the side condition that makes `WHN` stateable without reducing
proofs. -/
theorem WhRed.empty_at_prop {sg : Sig} {Γ : Ctx} {t u A : Tm}
    (hsort : SortUniqueAt sg Γ A) (h : WhRed (F0 sg) Γ t u A)
    (hp : Derivable (F0 sg) (Γ ⊢ A ∶ .sort .prop)) : False := by
  obtain ⟨s, hs, hnz⟩ := h.2
  exact hnz (hsort.sort_eq_prop hp hs)

/-- `WhRed` is empty at propositions, from the global sorting lemma. -/
theorem WhRed.empty_at_prop' {sg : Sig} (hsort : SortUnique sg) {Γ : Ctx} {t u A : Tm}
    (h : WhRed (F0 sg) Γ t u A) (hp : Derivable (F0 sg) (Γ ⊢ A ∶ .sort .prop)) : False :=
  WhRed.empty_at_prop (hsort Γ A) h hp

end Spec
end F0
end STC
