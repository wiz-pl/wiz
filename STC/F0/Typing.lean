import STC.F0.Sorting
/-!
# What the two structural conversion rules buy

`Spec/Struct.lean` adds `eqTyped` and `ctxConv` to F0. This file uses them.

## Endpoint typing

`eqTyped_left`/`eqTyped_right`: **every conversion types both of its endpoints at its own
type**. This is what `Sorting.lean` recorded as missing: only `Core.refl` typed an end.

## The `cong` conclusions

`Pi.cong`/`Sigma.cong` relate `B` and `B'` in `A :: Γ` and conclude a conversion between
`Π s A B` and `Π s' A' B'`; before `Struct`, nothing typed the *second* endpoint in
`A' :: Γ`. `pi_cong_typed`/`sigma_cong_typed` derive both endpoint typings of that
conclusion from the rule's own premises: `eqTyped` types `A'` and `B'`, and `ctxConv`
moves `B'`'s typing from `A :: Γ` to `A' :: Γ`.

## The proved laws and the remaining law obligation

The renaming and substitution lemmas are proved for `F0Base` (the fragment without
`Struct`), because `ctxConv` is not closed under renaming in the `RenOK` sense: a renaming
`ρ` from `A' :: Γ` to `Δ` induces a renaming `ρ ∘ succ` from `Γ`, and the two context
entries `A.ren ρ` and `A'.ren ρ` are only *convertible*, not equal — exactly the situation
`ctxConv` handles, so the closure statement needs contexts related by conversion, not a
renaming. The two closure properties are named here:

* `StructRenClosed sg`: `RenClosed (Struct sg) (F0 sg)`;
* `StructSubClosed sg`: `SubClosed (Struct sg) (F0 sg)`.

With them, `F0_rename_of`/`F0_subst_of` give the laws for `F0` itself.
-/


namespace STC
namespace F0
namespace Spec

/-! ## `eqTyped`: conversions type their endpoints -/

/-- A conversion types its **left** endpoint at its own type. -/
theorem eqTyped_left {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {t u C : Tm}
    (d : Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ C)) : Derivable (F0 sg) (Γ ⊢ t ∶ C) :=
  ofRule (struct_in_F0 (Struct.eqTyped (sg := sg) (hsg := hsg) (Γ := Γ) (t := t) (u := u)
    (C := C))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact d)

/-- A conversion types its **right** endpoint at its own type (`symm` + `eqTyped_left`). -/
theorem eqTyped_right {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {t u C : Tm}
    (d : Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ C)) : Derivable (F0 sg) (Γ ⊢ u ∶ C) :=
  eqTyped_left hsg (ofRule (core_in_F0 Core.symm) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact d))

/-- **Both endpoints of a conversion are typed at its type.** -/
theorem conv_typed {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {t u C : Tm}
    (d : Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ C)) :
    Derivable (F0 sg) (Γ ⊢ t ∶ C) ∧ Derivable (F0 sg) (Γ ⊢ u ∶ C) :=
  ⟨eqTyped_left hsg d, eqTyped_right hsg d⟩

/-- A conversion is well typed at both ends: the `Cong` rules of `Sorting.lean`'s
discussion can now be applied to a conversion obtained at an arbitrary type. -/
theorem conv_typed_left' {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {t u A B : Tm} {s : Srt}
    (d : Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A)) (h : Derivable (F0 sg) (Γ ⊢ A ≡ B ∶ .sort s)) :
    Derivable (F0 sg) (Γ ⊢ t ∶ B) :=
  ofRule (core_in_F0 (Core.conv (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨eqTyped_left hsg d, h⟩)

/-! ## `ctxConv`: context conversion -/

theorem ctxConv_wf {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A A' : Tm} {s : Srt}
    (hconv : Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s))
    (h : Derivable (F0 sg) (.wf (A :: Γ))) : Derivable (F0 sg) (.wf (A' :: Γ)) :=
  ofRule (struct_in_F0 (Struct.ctxConv (sg := sg) (hsg := hsg) (Γ := Γ) (A := A) (A' := A')
    (s := s) (j := .wf (A :: Γ)) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hconv, h⟩)

theorem ctxConv_ty {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A A' : Tm} {s : Srt}
    {t B : Tm} (hconv : Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s))
    (h : Derivable (F0 sg) ((A :: Γ) ⊢ t ∶ B)) : Derivable (F0 sg) ((A' :: Γ) ⊢ t ∶ B) :=
  ofRule (struct_in_F0 (Struct.ctxConv (sg := sg) (hsg := hsg) (Γ := Γ) (A := A) (A' := A')
    (s := s) (j := .ty (A :: Γ) t B) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hconv, h⟩)

theorem ctxConv_eq {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A A' : Tm} {s : Srt}
    {t u B : Tm} (hconv : Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s))
    (h : Derivable (F0 sg) ((A :: Γ) ⊢ t ≡ u ∶ B)) :
    Derivable (F0 sg) ((A' :: Γ) ⊢ t ≡ u ∶ B) :=
  ofRule (struct_in_F0 (Struct.ctxConv (sg := sg) (hsg := hsg) (Γ := Γ) (A := A) (A' := A')
    (s := s) (j := .eq (A :: Γ) t u B) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hconv, h⟩)

theorem ctxConv_red {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A A' : Tm} {s : Srt}
    {t u B : Tm} (hconv : Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s))
    (h : Derivable (F0 sg) ((A :: Γ) ⊢ t ⟶ u ∶ B)) :
    Derivable (F0 sg) ((A' :: Γ) ⊢ t ⟶ u ∶ B) :=
  ofRule (struct_in_F0 (Struct.ctxConv (sg := sg) (hsg := hsg) (Γ := Γ) (A := A) (A' := A')
    (s := s) (j := .red (A :: Γ) t u B) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hconv, h⟩)

/-! ## The second endpoint of a `cong` conclusion -/

/-- **F0 types both endpoints of `Pi.cong`'s conclusion.** From the rule's premises alone:
`eqTyped` types `B`, `A'`, `B'`, and `ctxConv` moves `B'`'s typing from `A :: Γ` to
`A' :: Γ`. Before `Struct`, the second conjunct was underivable. -/
theorem pi_cong_typed {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A A' B B' : Tm}
    {i j s s' : Srt} (hs : s.Equiv (.imax i j)) (hs' : s'.Equiv (.imax i j))
    (hA : Derivable (F0 sg) (Γ ⊢ A ∶ .sort i))
    (hAA : Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort i))
    (hB : Derivable (F0 sg) ((A :: Γ) ⊢ B ≡ B' ∶ .sort j)) :
    Derivable (F0 sg) (Γ ⊢ .pi s A B ∶ .sort s) ∧
      Derivable (F0 sg) (Γ ⊢ .pi s' A' B' ∶ .sort s) := by
  have hB₁ : Derivable (F0 sg) ((A :: Γ) ⊢ B ∶ .sort j) := eqTyped_left hsg hB
  have hB₂ : Derivable (F0 sg) ((A :: Γ) ⊢ B' ∶ .sort j) := eqTyped_right hsg hB
  have hA' : Derivable (F0 sg) (Γ ⊢ A' ∶ .sort i) := eqTyped_right hsg hAA
  have hB₂' : Derivable (F0 sg) ((A' :: Γ) ⊢ B' ∶ .sort j) := ctxConv_ty hsg hAA hB₂
  have hsEq : s' = s := hs'.trans hs.symm
  refine ⟨?_, ?_⟩
  · exact ofRule (pi_in_F0 (Pi.form (i := i) (j := j) (s := s) hs)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hA, hB₁⟩)
  · have h₂ : Derivable (F0 sg) (Γ ⊢ .pi s' A' B' ∶ .sort s') :=
      ofRule (pi_in_F0 (Pi.form (i := i) (j := j) (s := s') hs')) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hA', hB₂'⟩)
    simpa [hsEq] using h₂

/-- **F0 types both endpoints of `Sigma.cong`'s conclusion** (as `pi_cong_typed`, with
`max`). -/
theorem sigma_cong_typed {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A A' B B' : Tm}
    {i j s s' : Srt} (hs : s.Equiv (.max i j)) (hs' : s'.Equiv (.max i j))
    (hA : Derivable (F0 sg) (Γ ⊢ A ∶ .sort i))
    (hAA : Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort i))
    (hB : Derivable (F0 sg) ((A :: Γ) ⊢ B ≡ B' ∶ .sort j)) :
    Derivable (F0 sg) (Γ ⊢ .sigma s A B ∶ .sort s) ∧
      Derivable (F0 sg) (Γ ⊢ .sigma s' A' B' ∶ .sort s) := by
  have hB₁ : Derivable (F0 sg) ((A :: Γ) ⊢ B ∶ .sort j) := eqTyped_left hsg hB
  have hB₂ : Derivable (F0 sg) ((A :: Γ) ⊢ B' ∶ .sort j) := eqTyped_right hsg hB
  have hA' : Derivable (F0 sg) (Γ ⊢ A' ∶ .sort i) := eqTyped_right hsg hAA
  have hB₂' : Derivable (F0 sg) ((A' :: Γ) ⊢ B' ∶ .sort j) := ctxConv_ty hsg hAA hB₂
  have hsEq : s' = s := hs'.trans hs.symm
  refine ⟨?_, ?_⟩
  · exact ofRule (sigma_in_F0 (Sigma.form (i := i) (j := j) (s := s) hs)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hA, hB₁⟩)
  · have h₂ : Derivable (F0 sg) (Γ ⊢ .sigma s' A' B' ∶ .sort s') :=
      ofRule (sigma_in_F0 (Sigma.form (i := i) (j := j) (s := s') hs')) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hA', hB₂'⟩)
    simpa [hsEq] using h₂

/-! ## The law obligation for the two structural rules

`Renaming.lean` and `Substitution.lean` prove the laws for `F0Base`. The two rules of
`Struct` need a relation between contexts whose entries are *convertible*: a renaming
`ρ` from `A' :: Γ` to `Δ` induces `ρ ∘ succ` from `Γ`, and the target entries for the two
heads differ by `Δ ⊢ A'.shift.ren ρ ≡ A.shift.ren (ρ ∘ succ)`, which is the premise of
`ctxConv` applied under the binder, not an equality of types. Proving the closure is
therefore the "context conversion under renaming" lemma, and it is not a corollary of the
architecture below. -/

/-- **The renaming law for `Struct`, as an obligation**: every rule of `Struct sg`,
renamed, is derivable in `F0 sg` from its renamed premises. -/
def StructRenClosed (sg : Sig) : Prop := RenClosed (Struct sg) (F0 sg)

/-- **The substitution law for `Struct`, as an obligation**. -/
def StructSubClosed (sg : Sig) : Prop := SubClosed (Struct sg) (F0 sg)

/-- The renaming lemma for `F0` itself, from `StructRenClosed`: the fragment's closure is
proved (`F0Rules_renClosedIn`), the structural rules' is the hypothesis. -/
theorem F0_rename_of {sg : Sig} (hsg : Sig.Closed sg) (hstruct : StructRenClosed sg)
    {j : Jdg} (d : Derivable (F0 sg) j) : Renames (F0 sg) j :=
  rename_of_closed
    (RenClosed.union
      (F0Rules_renClosedIn (sg := sg) (var := .levelled) (R := F0 sg) hsg
        (fun _ x => Or.inl x) (fun _ x => core_in_F0 x))
      hstruct) d

/-- The substitution lemma for `F0` itself, from the two closure obligations. -/
theorem F0_subst_of {sg : Sig} (hsg : Sig.Closed sg) (hren : StructRenClosed sg)
    (hsub : StructSubClosed sg) {j : Jdg} (d : Derivable (F0 sg) j) : Substs (F0 sg) j :=
  subst_of_closed
    (SubClosed.union
      (F0Rules_subClosedIn (sg := sg) (var := .levelled) (R := F0 sg) hsg
        (fun _ d => F0_rename_of hsg hren d) (fun _ x => Or.inl x) (fun _ x => core_in_F0 x))
      hsub) d

end Spec
end F0
end STC
