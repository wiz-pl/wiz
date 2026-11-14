import STC.F0.Sorting
/-!
# The top-universe boundary of `TyUnique`

`Obligations.lean`'s `TyUnique` says two types of one term are convertible at one sort.
It is **refuted** here, for the empty signature, by the term `Sort u0`:

    [] ⊢ Sort u0 ∶ Sort u1        (twice, `Core.sort rfl`)

so `TyUnique` would give `∃ c, [] ⊢ Sort u1 ≡ Sort u1 ∶ Sort c`. But `HasSortU1` below —
"the typing's term, or an endpoint of an equation or reduction, is `Sort u1`" — is
preserved by no rule: `Core.sort` would need `Srt.succ? .u1 = some s`, `eqTyped` would
need a conversion of `Sort u1` (itself), and for the empty signature `delta` has no
declaration. `Sort u1` is a type but not a term (`Sort.lean`), so the witness conversion
of `TyUnique` cannot exist. The corrected statements are `TyUniqueTyped` and
`TopSortUnique` (`Obligations.lean`).

The induction is over all four judgments at once because the rules mix them: `eqTyped`
turns an equation into a typing, `symm` moves an endpoint, `redConv` a reduction into an
equation. `Tm.inst_eq_sort` is what the `Pi.beta` case needs: `b.inst a` is a sort only if
`b` is that sort or `b` is the innermost variable and `a` is.
-/


namespace STC
namespace F0

namespace Tm

/-- An instantiation is a sort only if the body is that sort, or the body is the
instantiated variable and the argument is that sort. (The `Pi.beta` case of
`HasSortU1`.) -/
theorem inst_eq_sort (b : Tm) : ∀ (a : Tm) (s : Srt), b.inst a = Tm.sort s →
    b = Tm.sort s ∨ (b = Tm.var 0 ∧ a = Tm.sort s) := by
  induction b with
  | var n =>
    intro a s h
    cases n with
    | zero => exact Or.inr ⟨rfl, by simpa [Tm.inst, Tm.sub, Tm.one] using h⟩
    | succ k => simp [Tm.inst, Tm.sub, Tm.one] at h
  | const c => intro a s h; simp [Tm.inst, Tm.sub] at h
  | sort s' => intro a s h; exact Or.inl (by simpa [Tm.inst, Tm.sub] using h)
  | pi s' A B ihA ihB => intro a s h; simp [Tm.inst, Tm.sub] at h
  | lam b ih => intro a s h; simp [Tm.inst, Tm.sub] at h
  | app f x ihf ihx => intro a s h; simp [Tm.inst, Tm.sub] at h
  | letE A v b ihA ihv ihb => intro a s h; simp [Tm.inst, Tm.sub] at h
  | letUnit u b ihu ihb => intro a s h; simp [Tm.inst, Tm.sub] at h
  | ann t A iht ihA => intro a s h; simp [Tm.inst, Tm.sub] at h
  | sigma s' A B ihA ihB => intro a s h; simp [Tm.inst, Tm.sub] at h
  | pair x y ihx ihy => intro a s h; simp [Tm.inst, Tm.sub] at h
  | fst p ih => intro a s h; simp [Tm.inst, Tm.sub] at h
  | snd p ih => intro a s h; simp [Tm.inst, Tm.sub] at h
  | unit s' => intro a s h; simp [Tm.inst, Tm.sub] at h
  | tt => intro a s h; simp [Tm.inst, Tm.sub] at h
  | empty s' => intro a s h; simp [Tm.inst, Tm.sub] at h
  | absurd M t ihM iht => intro a s h; simp [Tm.inst, Tm.sub] at h
  | enum n => intro a s h; simp [Tm.inst, Tm.sub] at h
  | tag n i => intro a s h; simp [Tm.inst, Tm.sub] at h
  | ecase M x bs ihM ihx ihbs => intro a s h; simp [Tm.inst, Tm.sub] at h
  | bnil => intro a s h; simp [Tm.inst, Tm.sub] at h
  | bcons x xs ihx ihxs => intro a s h; simp [Tm.inst, Tm.sub] at h
  | eq A x y ihA ihx ihy => intro a s h; simp [Tm.inst, Tm.sub] at h
  | eqTy A B ihA ihB => intro a s h; simp [Tm.inst, Tm.sub] at h
  | refl A x ihA ihx => intro a s h; simp [Tm.inst, Tm.sub] at h
  | reflTy A ihA => intro a s h; simp [Tm.inst, Tm.sub] at h
  | cast A B e t ihA ihB ihe iht => intro a s h; simp [Tm.inst, Tm.sub] at h
  | transp A x P p y e ihA ihx ihP ihp ihy ihe => intro a s h; simp [Tm.inst, Tm.sub] at h
  | ulift s' A ihA => intro a s h; simp [Tm.inst, Tm.sub] at h
  | up x ih => intro a s h; simp [Tm.inst, Tm.sub] at h
  | down t ih => intro a s h; simp [Tm.inst, Tm.sub] at h

end Tm

namespace Spec

/-- A judgment with `Sort u1` where a term would have to be typed: the typing's term, or
an endpoint of an equation or of a reduction. (`Sort u1` is a type but not a term, so no
rule may produce such a judgment.) -/
def HasSortU1 : Jdg → Prop
  | .wf _ => False
  | .ty _ t _ => t = Tm.sort .u1
  | .eq _ t u _ => t = Tm.sort .u1 ∨ u = Tm.sort .u1
  | .red _ t u _ => t = Tm.sort .u1 ∨ u = Tm.sort .u1

/-- **No derivation in `F0 []` has `Sort u1` at an endpoint.** One induction over the
four judgments: `eqTyped` maps a typing to an equation, `symm` moves the endpoint,
`redConv` a reduction into an equation, `ctxConv` keeps the judgment's terms, and every
other rule either has a non-`Sort` head or types the endpoint in a premise. For the empty
signature `delta` is vacuous (there is no declaration to look up). -/
theorem not_hasSortU1 {j : Jdg} (d : Derivable (F0 ([] : Sig)) j) : ¬ HasSortU1 j := by
  induction d with
  | intro r hr hp ih =>
    rcases hr with hbase | hstruct
    · rcases hbase with hrest | hulift
      · rcases hrest with hrest | heqty
        · rcases hrest with hrest | heq
          · rcases hrest with hrest | hglobal
            · rcases hrest with hrest | hlet
              · rcases hrest with hrest | henum
                · rcases hrest with hrest | hempty
                  · rcases hrest with hrest | hunit
                    · rcases hrest with hrest | hsigma
                      · rcases hrest with hcore | hpi
                        · cases hcore with
                          | wfNil => intro h; exact h
                          | wfCons => intro h; exact h
                          | var => intro h; cases h
                          | @sort Γ s s' hsucc =>
                            intro h; cases h; simp [Srt.succ?] at hsucc
                          | @conv Γ t A B s => intro h; exact ih (.ty Γ t A) (by simp) h
                          | @eqConv Γ t u A B s => intro h; exact ih (.eq Γ t u A) (by simp) h
                          | @redConv Γ t u A B s => intro h; exact ih (.red Γ t u A) (by simp) h
                          | @refl Γ t A =>
                            intro h; rcases h with h | h <;>
                              exact ih (.ty Γ t A) (by simp) h
                          | @symm Γ t u A =>
                            intro h; rcases h with h | h
                            · exact ih (.eq Γ t u A) (by simp) (Or.inr h)
                            · exact ih (.eq Γ t u A) (by simp) (Or.inl h)
                          | @trans Γ t u A w =>
                            intro h; rcases h with h | h
                            · exact ih (.eq Γ t u A) (by simp) (Or.inl h)
                            · exact ih (.eq Γ u w A) (by simp) (Or.inr h)
                          | @redEq Γ t u A => intro h; exact ih (.red Γ t u A) (by simp) h
                          | @irrel Γ A t u s hs =>
                            intro h; rcases h with h | h
                            · exact ih (.ty Γ t A) (by simp) h
                            · exact ih (.ty Γ u A) (by simp) h
                          | eqProp => intro h; rcases h with h | h <;> cases h
                          | eqType => intro h; rcases h with h | h <;> cases h
                          | eqTySort => intro h; rcases h with h | h <;> cases h
                          | eqTySortApart => intro h; rcases h with h | h <;> cases h
                          | @castSort Γ e t u w hEq =>
                            intro h; rcases h with h | h
                            · cases h
                            · exact ih (.ty Γ t (.sort u)) (by simp) h
                        · cases hpi with
                          | form => intro h; cases h
                          | lam => intro h; cases h
                          | app => intro h; cases h
                          | @beta Γ A B b a s i =>
                            intro h; rcases h with h | h
                            · cases h
                            · rcases Tm.inst_eq_sort b a .u1 h with hb | ⟨hb, ha⟩
                              · exact ih (.ty (A :: Γ) b B) (by simp) hb
                              · subst hb
                                exact ih (.ty Γ a A) (by simp) ha
                          | appRed => intro h; rcases h with h | h <;> cases h
                          | @eta Γ f A B g s i =>
                            intro h; rcases h with h | h
                            · exact ih (.ty Γ f (.pi s A B)) (by simp) h
                            · exact ih (.ty Γ g (.pi s A B)) (by simp) h
                          | cong => intro h; rcases h with h | h <;> cases h
                          | appCong => intro h; rcases h with h | h <;> cases h
                          | eq => intro h; rcases h with h | h <;> cases h
                          | eqTyApart => intro h; rcases h with h | h <;> cases h
                          | cast => intro h; rcases h with h | h <;> cases h
                      · cases hsigma with
                        | form => intro h; cases h
                        | pair => intro h; cases h
                        | fst => intro h; cases h
                        | snd => intro h; cases h
                        | @fstBeta Γ A B a b s =>
                          intro h; rcases h with h | h
                          · cases h
                          · exact ih (.ty Γ a A) (by simp) h
                        | @sndBeta Γ A B a b s =>
                          intro h; rcases h with h | h
                          · cases h
                          · exact ih (.ty Γ b (B.inst a)) (by simp) h
                        | fstRed => intro h; rcases h with h | h <;> cases h
                        | sndRed => intro h; rcases h with h | h <;> cases h
                        | @eta Γ p A B p' s =>
                          intro h; rcases h with h | h
                          · exact ih (.ty Γ p (.sigma s A B)) (by simp) h
                          · exact ih (.ty Γ p' (.sigma s A B)) (by simp) h
                        | cong => intro h; rcases h with h | h <;> cases h
                        | fstCong => intro h; rcases h with h | h <;> cases h
                        | sndCong => intro h; rcases h with h | h <;> cases h
                        | eq => intro h; rcases h with h | h <;> cases h
                        | eqProof => intro h; rcases h with h | h <;> cases h
                        | eqTyApart => intro h; rcases h with h | h <;> cases h
                        | cast => intro h; rcases h with h | h <;> cases h
                    · cases hunit with
                      | form => intro h; cases h
                      | tt => intro h; cases h
                      | @eta Γ t u s =>
                        intro h; rcases h with h | h
                        · exact ih (.ty Γ t (.unit s)) (by simp) h
                        · exact ih (.ty Γ u (.unit s)) (by simp) h
                      | cong => intro h; rcases h with h | h <;> cases h
                      | eq => intro h; rcases h with h | h <;> cases h
                      | eqTy => intro h; rcases h with h | h <;> cases h
                      | eqTyApart => intro h; rcases h with h | h <;> cases h
                      | cast => intro h; rcases h with h | h <;> cases h
                  · cases hempty with
                    | form => intro h; cases h
                    | absurd => intro h; cases h
                    | cong => intro h; rcases h with h | h <;> cases h
                    | absurdCong => intro h; rcases h with h | h <;> cases h
                    | eq => intro h; rcases h with h | h <;> cases h
                    | eqTy => intro h; rcases h with h | h <;> cases h
                    | eqTyApart => intro h; rcases h with h | h <;> cases h
                    | @cast Γ e t u w h1 h2 =>
                      intro h; rcases h with h | h
                      · cases h
                      · exact ih (.ty Γ t (.empty u)) (by simp) h
                · cases henum with
                  | form => intro h; cases h
                  | tag => intro h; cases h
                  | ecase => intro h; cases h
                  | @iota Γ b M k n i bl hlen hget =>
                    intro h; rcases h with h | h
                    · cases h
                    · have hmem : (Γ ⊢ b ∶ M.inst (.tag n i)) ∈ branchPrems Γ M n bl :=
                        List.mem_map.mpr ⟨(b, i), List.mk_mem_zipIdx_iff_getElem?.mpr hget, rfl⟩
                      exact ih (.ty Γ b (M.inst (.tag n i)))
                        (List.mem_append_right _ hmem) h
                  | ecaseRed => intro h; rcases h with h | h <;> cases h
                  | ecaseCong => intro h; rcases h with h | h <;> cases h
                  | eqSame => intro h; rcases h with h | h <;> cases h
                  | eqDiff => intro h; rcases h with h | h <;> cases h
                  | eqRedL => intro h; rcases h with h | h <;> cases h
                  | eqRedR => intro h; rcases h with h | h <;> cases h
                  | eqTySame => intro h; rcases h with h | h <;> cases h
                  | eqTyDiff => intro h; rcases h with h | h <;> cases h
                  | @cast Γ e t n =>
                    intro h; rcases h with h | h
                    · cases h
                    · exact ih (.ty Γ t (.enum n)) (by simp) h
              · cases hlet with
                | letE => intro h; cases h
                | @zeta Γ A v B b s =>
                  intro h; rcases h with h | h
                  · cases h
                  · exact ih (.ty Γ (b.inst v) B) (by simp) h
                | letUnit => intro h; cases h
                | @letUnitRed Γ u B b s =>
                  intro h; rcases h with h | h
                  · cases h
                  · exact ih (.ty Γ b B) (by simp) h
                | ann => intro h; cases h
                | @annRed Γ A t s =>
                  intro h; rcases h with h | h
                  · cases h
                  · exact ih (.ty Γ t A) (by simp) h
            · cases hglobal with
              | const => intro h; cases h
              | delta =>
                intro h
                simp [Sig.find?] at *
          · cases heq with
            | eq => intro h; cases h
            | refl => intro h; cases h
            | reflTy => intro h; cases h
            | transp => intro h; cases h
            | cast => intro h; cases h
            | eqCong => intro h; rcases h with h | h <;> cases h
            | eqTyCong => intro h; rcases h with h | h <;> cases h
            | castCong => intro h; rcases h with h | h <;> cases h
            | eqRed => intro h; rcases h with h | h <;> cases h
            | eqTyRedL => intro h; rcases h with h | h <;> cases h
            | eqTyRedR => intro h; rcases h with h | h <;> cases h
            | castRedL => intro h; rcases h with h | h <;> cases h
            | castRedR => intro h; rcases h with h | h <;> cases h
            | eqAtProp => intro h; rcases h with h | h <;> cases h
            | eqTyProps => intro h; rcases h with h | h <;> cases h
            | eqTyFormers => intro h; rcases h with h | h <;> cases h
        · change EqTyLevelled r at heqty
          cases heqty with
          | form => intro h; cases h
          | pi => intro h; rcases h with h | h <;> cases h
          | sigma => intro h; rcases h with h | h <;> cases h
      · cases hulift with
        | form => intro h; cases h
        | up => intro h; cases h
        | down => intro h; cases h
        | @beta Γ A a l =>
          intro h; rcases h with h | h
          · cases h
          · exact ih (.ty Γ a A) (by simp) h
        | downRed => intro h; rcases h with h | h <;> cases h
        | @eta Γ t A t' l =>
          intro h; rcases h with h | h
          · exact ih (.ty Γ t (.ulift l A)) (by simp) h
          · exact ih (.ty Γ t' (.ulift l A)) (by simp) h
        | cong => intro h; rcases h with h | h <;> cases h
        | downCong => intro h; rcases h with h | h <;> cases h
        | eqProp => intro h; rcases h with h | h <;> cases h
        | eq => intro h; rcases h with h | h <;> cases h
        | eqTy => intro h; rcases h with h | h <;> cases h
        | eqTyApart => intro h; rcases h with h | h <;> cases h
        | cast => intro h; rcases h with h | h <;> cases h
    · cases hstruct with
      | @eqTyped hsg₀ Γ t u C => intro h; exact ih (.eq Γ t u C) (by simp) (Or.inl h)
      | @ctxConv hsg₀ Γ₀ A₀ A₀' s₀ j₀ hctx =>
        cases j₀ with
        | wf Γ' => intro h; exact h
        | ty Γ' t' A' => intro h; exact ih (.ty Γ' t' A') (by simp) h
        | eq Γ' t' u' A' => intro h; exact ih (.eq Γ' t' u' A') (by simp) h
        | red Γ' t' u' A' => intro h; exact ih (.red Γ' t' u' A') (by simp) h

/-- `Sort u1` is not a term: no typing of it is derivable, even in the extended F0. -/
theorem no_typing_sort_u1 {Γ : Ctx} {A : Tm}
    (d : Derivable (F0 ([] : Sig)) (Γ ⊢ Tm.sort .u1 ∶ A)) : False :=
  not_hasSortU1 d rfl

/-- No reduction in `F0 []` starts at `Sort u1`. -/
theorem no_red_sort_u1_left {Γ : Ctx} {u A : Tm}
    (d : Derivable (F0 ([] : Sig)) (Γ ⊢ Tm.sort .u1 ⟶ u ∶ A)) : False :=
  not_hasSortU1 d (Or.inl rfl)

/-- No reduction in `F0 []` ends at `Sort u1`. -/
theorem no_red_sort_u1_right {Γ : Ctx} {t A : Tm}
    (d : Derivable (F0 ([] : Sig)) (Γ ⊢ t ⟶ Tm.sort .u1 ∶ A)) : False :=
  not_hasSortU1 d (Or.inr rfl)

/-- No equation in `F0 []` has `Sort u1` on the left. -/
theorem no_eq_sort_u1_left {Γ : Ctx} {u A : Tm}
    (d : Derivable (F0 ([] : Sig)) (Γ ⊢ Tm.sort .u1 ≡ u ∶ A)) : False :=
  not_hasSortU1 d (Or.inl rfl)

/-- No equation in `F0 []` has `Sort u1` on the right. -/
theorem no_eq_sort_u1_right {Γ : Ctx} {t A : Tm}
    (d : Derivable (F0 ([] : Sig)) (Γ ⊢ t ≡ Tm.sort .u1 ∶ A)) : False :=
  not_hasSortU1 d (Or.inr rfl)

/-- **`TyUnique` as stated in `Obligations.lean` is refuted** by the empty signature: the
term `Sort u0` has type `Sort u1` (twice), so the assertion of a common conversion sort
would produce an equation with `Sort u1` at both ends, which `not_hasSortU1` forbids. -/
theorem tyUnique_false : ¬ TyUnique ([] : Sig) := by
  intro h
  have hwf : Derivable (F0 ([] : Sig)) (.wf ([] : Ctx)) :=
    ofRule (core_in_F0 Core.wfNil) (by simp)
  have hty : Derivable (F0 ([] : Sig)) (([] : Ctx) ⊢ Tm.sort .u0 ∶ Tm.sort .u1) :=
    ofRule (core_in_F0 (Core.sort (s := .u0) (s' := .u1) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hwf)
  obtain ⟨c, hc⟩ := h ([] : Ctx) (.sort .u0) (.sort .u1) (.sort .u1) hty hty
  exact no_eq_sort_u1_left hc

end Spec
end F0
end STC
