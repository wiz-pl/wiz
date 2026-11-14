import STC.F2.Laws
/-!
# F2: context validity (and the unconditional `[a/0]` companions)

`F0Base_ctx` (`F0/Substitution.lean`) proves context validity for `F0Base` by induction
over the last rule. The same induction works for any system `R` containing `F0Base`, and
the phase and F2 rules preserve the context trivially (their conclusions are at the same
context as a premise; only `Core.wfNil`/`wfCons` build a context). This file records that
as `CtxClosed`, instantiates it for `F1` and `F2`, and drops the `⊢ Γ` hypotheses from
`F1_subst*`/`F2_subst*`.

* `F1_ctx`: every judgment derivable in `F1` has a well-formed context (the F1 obligation
  F1/Phase.lean left open);
* `F2_ctx`: the same for F2, including `Ext 0`, strict `Glue` and `●`;
* `F1_subst'`, `F2_subst'`, `F2_subst_eq'`, `F2_subst_red'`: the concrete companions
  without the explicit `⊢ Γ` hypothesis.

The F0Base component is the proof of `F0Base_ctx` read in an arbitrary supersystem: each
rule's conclusion shares a premise's context, except `wfCons` (which uses `wfExt` on the
actual premises) and `wfNil`.
-/


namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-- Every rule of `S`, given the derivations of its premises and the well-formedness of
their contexts, has a well-formed conclusion context. -/
def CtxClosed (S R : Rules) : Prop :=
  ∀ r, S r → (∀ p, p ∈ r.prems → Derivable R p) →
    (∀ p, p ∈ r.prems → Derivable R (.wf (Jdg.ctx p))) →
    Derivable R (.wf (Jdg.ctx r.concl))

theorem CtxClosed.union {S S' R : Rules} (h : CtxClosed S R) (h' : CtxClosed S' R) :
    CtxClosed (S ∪ S') R :=
  fun r hr hp ih => hr.elim (fun hs => h r hs hp ih) (fun hs => h' r hs hp ih)

theorem ctx_of_closed {R : Rules} (h : CtxClosed R R) {j : Jdg}
    (d : Derivable R j) : Derivable R (.wf (Jdg.ctx j)) := by
  induction d with
  | intro r hr hp ih => exact h r hr hp ih

/-- `F0Base`'s rules, read in any system `R` that contains them. -/
theorem F0Base_ctxClosed {sg : Sig} {R : Rules}
    (h : ∀ r, F0Base sg r → R r) (hc : ∀ r, Core r → R r) :
    CtxClosed (F0Base sg) R := by
  intro r hr hp ih
  rcases hr with hrest | hulift
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
                      | wfNil => dsimp only [Jdg.ctx]; exact ofRule (h _ (core_in_F0Rules Core.wfNil)) (by simp)
                      | @wfCons Γ A sc =>
                        dsimp only [Jdg.ctx]
                        exact wfExt (s := sc) hc
                          (hp (.wf Γ) (by simp)) (hp (.ty Γ A (.sort sc)) (by simp))
                      | @var Γ A i h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                      | @sort Γ sc sc' h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                      | @conv Γ t A B sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ t A) (by simp)
                      | @eqConv Γ t u A B sc =>
                        dsimp only [Jdg.ctx]; exact ih (.eq Γ t u A) (by simp)
                      | @redConv Γ t u A B sc =>
                        dsimp only [Jdg.ctx]; exact ih (.red Γ t u A) (by simp)
                      | @refl Γ t A => dsimp only [Jdg.ctx]; exact ih (.ty Γ t A) (by simp)
                      | @symm Γ t u A => dsimp only [Jdg.ctx]; exact ih (.eq Γ t u A) (by simp)
                      | @trans Γ t u A w =>
                        dsimp only [Jdg.ctx]; exact ih (.eq Γ t u A) (by simp)
                      | @redEq Γ t u A => dsimp only [Jdg.ctx]; exact ih (.red Γ t u A) (by simp)
                      | @irrel Γ A t u sc h =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
                      | @eqProp Γ a b sc h =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.sort sc)) (by simp)
                      | @eqType Γ a b sc h =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.sort sc)) (by simp)
                      | @eqTySort Γ u w h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                      | @eqTySortApart Γ u w h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                      | @castSort Γ e t u w h =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.sort u)) (by simp)
                    · cases hpi with
                      | @form Γ A B i j sc h =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort i)) (by simp)
                      | @lam Γ A B b sc i =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi sc A B) (.sort sc)) (by simp)
                      | @app Γ f A B a sc =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ f (.pi sc A B)) (by simp)
                      | @beta Γ A B b a sc i =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi sc A B) (.sort sc)) (by simp)
                      | @appRed Γ f f' A B a sc =>
                        dsimp only [Jdg.ctx]; exact ih (.red Γ f f' (.pi sc A B)) (by simp)
                      | @eta Γ f A B g sc i =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ f (.pi sc A B)) (by simp)
                      | @cong Γ A A' B B' i j sc sc' h h' =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort i)) (by simp)
                      | @appCong Γ f f' A B a a' sc =>
                        dsimp only [Jdg.ctx]; exact ih (.eq Γ f f' (.pi sc A B)) (by simp)
                      | @eq Γ A B f g sc h =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi sc A B) (.sort sc)) (by simp)
                      | @eqTyApart Γ A₁ B₁ A₂ B₂ s₁ s₂ h1 h2 =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi s₁ A₁ B₁) (.sort s₁)) (by simp)
                      | @cast Γ A₁ B₁ A₂ B₂ e t s₁ s₂ i j h1 h2 =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi s₁ A₁ B₁) (.sort s₁)) (by simp)
                  · cases hsigma with
                    | @form Γ A B i j sc h =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort i)) (by simp)
                    | @pair Γ A B a b sc =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                    | @fst Γ p A B sc =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ p (.sigma sc A B)) (by simp)
                    | @snd Γ p A B sc =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ p (.sigma sc A B)) (by simp)
                    | @fstBeta Γ A B a b sc =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                    | @sndBeta Γ A B a b sc =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                    | @fstRed Γ p p' A B sc =>
                      dsimp only [Jdg.ctx]; exact ih (.red Γ p p' (.sigma sc A B)) (by simp)
                    | @sndRed Γ p p' A B sc =>
                      dsimp only [Jdg.ctx]; exact ih (.red Γ p p' (.sigma sc A B)) (by simp)
                    | @eta Γ p A B p' sc =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ p (.sigma sc A B)) (by simp)
                    | @cong Γ A A' B B' i j sc sc' h h' =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort i)) (by simp)
                    | @fstCong Γ p p' A B sc =>
                      dsimp only [Jdg.ctx]; exact ih (.eq Γ p p' (.sigma sc A B)) (by simp)
                    | @sndCong Γ p p' A B sc =>
                      dsimp only [Jdg.ctx]; exact ih (.eq Γ p p' (.sigma sc A B)) (by simp)
                    | @eq Γ A B a b sc i h1 h2 =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                    | @eqProof Γ A B a b sc i h1 h2 =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                    | @eqTyApart Γ A₁ B₁ A₂ B₂ s₁ s₂ h1 h2 =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma s₁ A₁ B₁) (.sort s₁)) (by simp)
                    | @cast Γ A₁ B₁ A₂ B₂ e t s₁ s₂ i j h1 h2 =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma s₁ A₁ B₁) (.sort s₁)) (by simp)
                · cases hunit with
                  | @form Γ sc => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @tt Γ sc => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @eta Γ t u sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.unit sc)) (by simp)
                  | @cong Γ sc sc' h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @eq Γ a b sc h => dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.unit sc)) (by simp)
                  | @eqTy Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @eqTyApart Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @cast Γ e t u w h1 h2 =>
                    dsimp only [Jdg.ctx]; exact ih (.ty Γ e (.eqTy (.unit u) (.unit w))) (by simp)
              · cases hempty with
                | @form Γ sc => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @absurd Γ M t k sc =>
                  dsimp only [Jdg.ctx]; exact ih (.ty Γ M (.sort k)) (by simp)
                | @cong Γ sc sc' h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @absurdCong Γ M M' t t' k sc =>
                  dsimp only [Jdg.ctx]; exact ih (.eq Γ M M' (.sort k)) (by simp)
                | @eq Γ a b sc h => dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.empty sc)) (by simp)
                | @eqTy Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @eqTyApart Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @cast Γ e t u w h1 h2 =>
                  dsimp only [Jdg.ctx]; exact ih (.ty Γ e (.eqTy (.empty u) (.empty w))) (by simp)
            · cases henum with
              | @form Γ n => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
              | @tag Γ i n h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
              | @ecase Γ sc M k n bl h =>
                dsimp only [Jdg.ctx]
                exact ih (.ty Γ sc (.enum n)) (List.mem_append_left _ (by simp))
              | @iota Γ b M k n i bl h1 h2 =>
                dsimp only [Jdg.ctx]
                exact hp (.wf Γ) (List.mem_append_left _ (by simp))
              | @ecaseRed Γ sc sc' M k n bl h =>
                dsimp only [Jdg.ctx]
                exact ih (.red Γ sc sc' (.enum n)) (List.mem_append_left _ (by simp))
              | @ecaseCong Γ sc sc' M M' k n bl bl' h h' =>
                dsimp only [Jdg.ctx]
                exact ih (.eq Γ sc sc' (.enum n)) (List.mem_append_left _ (by simp))
              | @eqSame Γ i n h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
              | @eqDiff Γ i n j h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
              | @eqRedL Γ a a' b n =>
                dsimp only [Jdg.ctx]; exact ih (.red Γ a a' (.enum n)) (by simp)
              | @eqRedR Γ a b b' n =>
                dsimp only [Jdg.ctx]; exact ih (.red Γ b b' (.enum n)) (by simp)
              | @eqTySame Γ n => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
              | @eqTyDiff Γ n m h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
              | @cast Γ e t n =>
                dsimp only [Jdg.ctx]; exact ih (.ty Γ e (.eqTy (.enum n) (.enum n))) (by simp)
          · cases hlet with
            | @letE Γ A v B b sc =>
              dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
            | @zeta Γ A v B b sc =>
              dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
            | @letUnit Γ u B b sc =>
              dsimp only [Jdg.ctx]; exact ih (.ty Γ u (.unit sc)) (by simp)
            | @letUnitRed Γ u B b sc =>
              dsimp only [Jdg.ctx]; exact ih (.ty Γ u (.unit sc)) (by simp)
            | @ann Γ A t sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
            | @annRed Γ A t sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        · cases hglobal with
          | @const Γ c d h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
          | @delta Γ v c d h1 h2 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
      · cases heq with
        | @eq Γ A a b sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @refl Γ A a sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @reflTy Γ A sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @transp Γ A a b P p e sc =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @cast Γ A B e t sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @eqCong Γ A A' a a' b b' sc =>
          dsimp only [Jdg.ctx]; exact ih (.eq Γ A A' (.sort sc)) (by simp)
        | @eqTyCong Γ A A' B B' sc sc' =>
          dsimp only [Jdg.ctx]; exact ih (.eq Γ A A' (.sort sc)) (by simp)
        | @castCong Γ A A' B B' e e' t t' sc =>
          dsimp only [Jdg.ctx]; exact ih (.eq Γ A A' (.sort sc)) (by simp)
        | @eqRed Γ A A' a b sc =>
          dsimp only [Jdg.ctx]; exact ih (.red Γ A A' (.sort sc)) (by simp)
        | @eqTyRedL Γ A A' B sc sc' =>
          dsimp only [Jdg.ctx]; exact ih (.red Γ A A' (.sort sc)) (by simp)
        | @eqTyRedR Γ A B B' sc sc' =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @castRedL Γ A A' B e t sc =>
          dsimp only [Jdg.ctx]; exact ih (.red Γ A A' (.sort sc)) (by simp)
        | @castRedR Γ A B B' e t sc =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @eqAtProp Γ A a b sc h =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @eqTyProps Γ A B sc sc' h h' =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @eqTyFormers Γ A B sc sc' f f' h1 h2 h3 h4 h5 =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
    · change EqTyLevelled r at heqty
      cases heqty with
      | @form Γ A B sc =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
      | @pi Γ A₁ A₂ B₁ B₂ i j s₁ s₂ h1 h2 h3 h4 =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ A₁ (.sort i)) (by simp)
      | @sigma Γ A₁ A₂ B₁ B₂ i j s₁ s₂ h1 h2 h3 h4 =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ A₁ (.sort i)) (by simp)
  · cases hulift with
    | @form Γ A k l h => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort k)) (by simp)
    | @up Γ A a l => dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift l A) (.sort l)) (by simp)
    | @down Γ t A l => dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.ulift l A)) (by simp)
    | @beta Γ A a l => dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift l A) (.sort l)) (by simp)
    | @downRed Γ t t' A l => dsimp only [Jdg.ctx]; exact ih (.red Γ t t' (.ulift l A)) (by simp)
    | @eta Γ t A t' l =>
      dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.ulift l A)) (by simp)
    | @cong Γ A A' l k l' h =>
      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift l A) (.sort l)) (by simp)
    | @downCong Γ t t' A l => dsimp only [Jdg.ctx]; exact ih (.eq Γ t t' (.ulift l A)) (by simp)
    | @eqProp Γ A a b k l h1 h2 =>
      dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort k)) (by simp)
    | @eq Γ A a b k l h1 h2 =>
      dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort k)) (by simp)
    | @eqTy Γ A B u w k k' h1 h2 h3 =>
      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift u A) (.sort u)) (by simp)
    | @eqTyApart Γ A B u w h1 h2 h3 =>
      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift u A) (.sort u)) (by simp)
    | @cast Γ A B e t u w k h1 h2 =>
      dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift u A) (.sort u)) (by simp)


/-! ## The phase and F2 rule sets -/

theorem phase_ctxClosed {R : Rules} (_h : ∀ r, STC.F1.Phase r → R r) :
    CtxClosed STC.F1.Phase R := by
  intro r hr hp ih
  cases hr with
  | @form Γ φ => exact ih (.wf Γ) (by simp)
  | @intro Γ e φ ψ hle => exact ih (.ty Γ e (ph φ)) (by simp)
  | @botRed Γ => exact ih (.wf Γ) (by simp)
  | @topRed Γ => exact ih (.wf Γ) (by simp)
  | @andRed Γ φ ψ => exact ih (.wf Γ) (by simp)

theorem ext0_ctxClosed {sg : Sig} (_h : ∀ r, Ext0 r → F2 sg r) :
    CtxClosed Ext0 (F2 sg) := by
  intro r hr hp ih
  cases hr with
  | @form Γ A a φ s => exact ih (.ty Γ A (.sort s)) (by simp)
  | @intro Γ A a t φ s => exact ih (.ty Γ (Ext A φ a) (.sort s)) (by simp)
  | @elim Γ A a x φ s => exact ih (.ty Γ (Ext A φ a) (.sort s)) (by simp)
  | @beta Γ A a t φ s => exact ih (.ty Γ (Ext A φ a) (.sort s)) (by simp)
  | @eta Γ A a x φ s => exact ih (.ty Γ (Ext A φ a) (.sort s)) (by simp)

theorem glue_ctxClosed {sg : Sig} (_h : ∀ r, Glue r → F2 sg r) :
    CtxClosed Glue (F2 sg) := by
  intro r hr hp ih
  cases hr with
  | @form Γ A T f φ s s' hs => exact ih (.ty Γ A (.sort s)) (by simp)
  | @intro Γ A T f t a φ s s' hs =>
    exact ih (.ty Γ (GlueTy φ A T f) (.sort s)) (by simp)
  | @elim Γ A T f x φ s s' hs =>
    exact ih (.ty Γ (GlueTy φ A T f) (.sort s)) (by simp)
  | @beta Γ A T f t a φ s s' hs =>
    exact ih (.ty Γ (GlueTy φ A T f) (.sort s)) (by simp)

theorem closed_ctxClosed {sg : Sig} (_h : ∀ r, Closed r → F2 sg r) :
    CtxClosed Closed (F2 sg) := by
  intro r hr hp ih
  cases hr with
  | @form Γ A φ s => exact ih (.ty Γ A (.sort s)) (by simp)
  | @intro Γ A a φ s => exact ih (.ty Γ (ClosedTy φ A) (.sort s)) (by simp)
  | @star Γ A φ s => exact ih (.ty Γ (ClosedTy φ A) (.sort s)) (by simp)
  | @elim Γ A B mEta mStar x φ sA sB => exact ih (.ty Γ A (.sort sA)) (by simp)
  | @betaIn Γ A B mEta mStar a φ sA sB => exact ih (.ty Γ A (.sort sA)) (by simp)
  | @betaStar Γ A B mEta mStar φ sA sB => exact ih (.ty Γ A (.sort sA)) (by simp)

/-! ## Context validity for F1 and F2 -/

theorem F1_ctx {sg : Sig} {j : Jdg}
    (d : Derivable (_root_.STC.F1.F1 sg) j) :
    Derivable (_root_.STC.F1.F1 sg) (.wf (Jdg.ctx j)) :=
  ctx_of_closed
    (CtxClosed.union
      (F0Base_ctxClosed (R := _root_.STC.F1.F1 sg) (fun _ x => Or.inl x)
        (fun _ x => Or.inl (core_in_F0Rules x)))
      (phase_ctxClosed (fun _ x => Or.inr x))) d

theorem F2_ctx {sg : Sig} {j : Jdg}
    (d : Derivable (F2 sg) j) : Derivable (F2 sg) (.wf (Jdg.ctx j)) :=
  ctx_of_closed
    (CtxClosed.union
      (CtxClosed.union
        (CtxClosed.union
          (CtxClosed.union
            (F0Base_ctxClosed (R := F2 sg) (fun _ x => f1_in_F2 (Or.inl x))
              (fun _ x => core_in_F2 x))
            (phase_ctxClosed (fun _ x => f1_in_F2 (Or.inr x))))
          (ext0_ctxClosed (fun _ x => ext0_in_F2 x)))
        (glue_ctxClosed (fun _ x => glue_in_F2 x)))
      (closed_ctxClosed (fun _ x => closed_in_F2 x))) d

/-- F1's typing companion without the explicit `⊢ Γ`. -/
theorem F1_subst' {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t B a : Tm}
    (ht : Derivable (_root_.STC.F1.F1 sg) ((A :: Γ) ⊢ t ∶ B))
    (ha : Derivable (_root_.STC.F1.F1 sg) (Γ ⊢ a ∶ A)) :
    Derivable (_root_.STC.F1.F1 sg) (Γ ⊢ t.inst a ∶ B.inst a) :=
  _root_.STC.F1.F1_subst hsg (F1_ctx ha) ht ha

/-- F2's typing companion without the explicit `⊢ Γ`. -/
theorem F2_subst' {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t B a : Tm}
    (ht : Derivable (F2 sg) ((A :: Γ) ⊢ t ∶ B))
    (ha : Derivable (F2 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F2 sg) (Γ ⊢ t.inst a ∶ B.inst a) :=
  F2_subst hsg (F2_ctx ha) ht ha

/-- F2's conversion companion without the explicit `⊢ Γ`. -/
theorem F2_subst_eq' {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t u B a : Tm}
    (ht : Derivable (F2 sg) ((A :: Γ) ⊢ t ≡ u ∶ B))
    (ha : Derivable (F2 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F2 sg) (Γ ⊢ t.inst a ≡ u.inst a ∶ B.inst a) :=
  F2_subst_eq hsg (F2_ctx ha) ht ha

/-- F2's reduction companion without the explicit `⊢ Γ`. -/
theorem F2_subst_red' {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t u B a : Tm}
    (ht : Derivable (F2 sg) ((A :: Γ) ⊢ t ⟶ u ∶ B))
    (ha : Derivable (F2 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F2 sg) (Γ ⊢ t.inst a ⟶ u.inst a ∶ B.inst a) :=
  F2_subst_red hsg (F2_ctx ha) ht ha

end F2
end STC
