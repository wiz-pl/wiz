import STC.F0.Typing
import STC.F0.Substitution
/-!
# Context validity for `F0`

`F0Base_ctx` (`F0/Substitution.lean`) proves that every derivable judgment of the fragment
has a well-formed context, from the rules and without an inversion principle: the proof
follows the last rule of the derivation. This file extends the statement to **`F0`**, the
specification's system — `F0Base` plus the two structural conversion rules `eqTyped` and
`ctxConv` (`Spec/Struct.lean`). That closes item 5 of `agents/stc-rules.md`, "context
validity for the extended `F0`", which `sortUniqueAt_of_typed` still took as a hypothesis
(`⊢ Γ`).

The two new cases are the reason the statement is cheap:

* `eqTyped` concludes a typing `Γ ⊢ t ∶ C` from a conversion in the same context `Γ`, so
  the context is the one its premise's induction hypothesis already gives;
* `ctxConv` concludes `(A' :: Γ) ⊢ J` from `(A :: Γ) ⊢ J` and `Γ ⊢ A ≡ A' ∶ Sort s`; the
  induction hypothesis gives `⊢ (A :: Γ)` and `ctxConv_wf` (`F0/Typing.lean`) converts
  the entry, giving `⊢ (A' :: Γ)`.

Everything else is the fragment's case tree (`F0Base_ctx_rule` below, the same induction
`F0Base_ctx` runs, lifted from `F0Base` to `F0`).

## What this buys

* `F0_ctx`: `Γ ⊢ J → ⊢ Γ` for every judgment, including conversions and reductions;
* `F0_wf_tail`: `⊢ A :: Γ → ⊢ Γ` (the only `wf` inversion the rules have);
* `sortUniqueAt_of_typing`: the corrected sorting reduction
  (`F0/Sorting.lean`, `sortUniqueAt_of_typed`) with the well-formedness of `Γ` derived
  from the typing instead of assumed;
* `WhRed.empty_at_prop_of_typing`: the same for the emptiness of `WhRed` at propositions.

It does **not** prove `StructRenClosed`/`StructSubClosed`: context validity is about the
contexts a derivation already carries, while those need contexts related by *conversion
under a renaming* (see `F0/Typing.lean`; the relation redesign is analysed in
`agents/stc-m1.md`).
-/


namespace STC
namespace F0
namespace Spec

/-- Context validity for one `F0Base` rule, read in `F0`: the premises are derivable in
`F0` and have well-formed contexts. This is `F0Base_ctx`'s case tree with the system
parameter changed from `F0Base` to `F0`. -/
theorem F0Base_ctx_rule {sg : Sig} {r : Rule} (hr : F0Base sg r)
    (hp : ∀ p, p ∈ r.prems → Derivable (F0 sg) p)
    (ih : ∀ p, p ∈ r.prems → Derivable (F0 sg) (.wf (Jdg.ctx p))) :
    Derivable (F0 sg) (.wf (Jdg.ctx r.concl)) := by
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
                      | wfNil => dsimp only [Jdg.ctx]; exact ofRule (core_in_F0 Core.wfNil) (by simp)
                      | @wfCons Γ A sc =>
                        dsimp only [Jdg.ctx]
                        exact wfExt (s := sc) (fun _ x => core_in_F0 x)
                          (hp (.wf Γ) (by simp)) (hp (.ty Γ A (.sort sc)) (by simp))
                      | @var Γ A i h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                      | @sort Γ sc sc' h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
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
                      | @eqTySort Γ u w h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                      | @eqTySortApart Γ u w h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
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
                  | @form Γ sc => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                  | @tt Γ sc => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                  | @eta Γ t u sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.unit sc)) (by simp)
                  | @cong Γ sc sc' h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                  | @eq Γ a b sc h => dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.unit sc)) (by simp)
                  | @eqTy Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                  | @eqTyApart Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                  | @cast Γ e t u w h1 h2 =>
                    dsimp only [Jdg.ctx]; exact ih (.ty Γ e (.eqTy (.unit u) (.unit w))) (by simp)
              · cases hempty with
                | @form Γ sc => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                | @absurd Γ M t k sc =>
                  dsimp only [Jdg.ctx]; exact ih (.ty Γ M (.sort k)) (by simp)
                | @cong Γ sc sc' h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                | @absurdCong Γ M M' t t' k sc =>
                  dsimp only [Jdg.ctx]; exact ih (.eq Γ M M' (.sort k)) (by simp)
                | @eq Γ a b sc h => dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.empty sc)) (by simp)
                | @eqTy Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                | @eqTyApart Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
                | @cast Γ e t u w h1 h2 =>
                  dsimp only [Jdg.ctx]; exact ih (.ty Γ e (.eqTy (.empty u) (.empty w))) (by simp)
            · cases henum with
              | @form Γ n => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
              | @tag Γ i n h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
              | @ecase Γ sc M k n bl h =>
                dsimp only [Jdg.ctx]
                exact ih (.ty Γ sc (.enum n)) (List.mem_append_left _ (by simp))
              | @iota Γ b M k n i bl h1 h2 =>
                dsimp only [Jdg.ctx]
                exact ih (.wf Γ) (List.mem_append_left _ (by simp))
              | @ecaseRed Γ sc sc' M k n bl h =>
                dsimp only [Jdg.ctx]
                exact ih (.red Γ sc sc' (.enum n)) (List.mem_append_left _ (by simp))
              | @ecaseCong Γ sc sc' M M' k n bl bl' h h' =>
                dsimp only [Jdg.ctx]
                exact ih (.eq Γ sc sc' (.enum n)) (List.mem_append_left _ (by simp))
              | @eqSame Γ i n h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
              | @eqDiff Γ i n j h1 h2 h3 => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
              | @eqRedL Γ a a' b n =>
                dsimp only [Jdg.ctx]; exact ih (.red Γ a a' (.enum n)) (by simp)
              | @eqRedR Γ a b b' n =>
                dsimp only [Jdg.ctx]; exact ih (.red Γ b b' (.enum n)) (by simp)
              | @eqTySame Γ n => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
              | @eqTyDiff Γ n m h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
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
          | @const Γ c d h => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
          | @delta Γ v c d h1 h2 => dsimp only [Jdg.ctx]; exact ih (.wf Γ) (by simp)
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

/-- **Context validity for `F0`**: every derivable judgment of the specification's system
has a well-formed context. The `F0Base` cases are `F0Base_ctx_rule`; the two `Struct`
cases are `eqTyped` (same context as its premise) and `ctxConv` (`ctxConv_wf`). -/
theorem F0_ctx {sg : Sig} {j : Jdg} (d : Derivable (F0 sg) j) :
    Derivable (F0 sg) (.wf (Jdg.ctx j)) := by
  induction d with
  | intro r hr hp ih =>
    rcases hr with hbase | hstruct
    · exact F0Base_ctx_rule hbase hp ih
    · cases hstruct with
      | @eqTyped hsg₀ Γ t u C =>
        dsimp only [Jdg.ctx]
        exact ih (.eq Γ t u C) (by simp)
      | @ctxConv hsg₀ Γ A A' s j h =>
        rw [Jdg.ctx_rectx]
        exact ctxConv_wf hsg₀ (hp (.eq Γ A A' (.sort s)) (by simp)) (h ▸ ih j (by simp))

/-- **Dropping the head entry**: `⊢ A :: Γ` implies `⊢ Γ`. The only rules that conclude a
`wf` judgment are `wfNil`, `wfCons` and `ctxConv`; `wfNil` cannot conclude a cons. -/
theorem F0_wf_tail {sg : Sig} {Γ : Ctx} {A : Tm}
    (h : Derivable (F0 sg) (.wf (A :: Γ))) : Derivable (F0 sg) (.wf Γ) := by
  have aux : ∀ j, Derivable (F0 sg) j → ∀ (Δ : Ctx) (B : Tm),
      j = .wf (B :: Δ) → Derivable (F0 sg) (.wf Δ) := by
    intro j dj
    induction dj with
    | intro r hr hp ih =>
      intro Δ B heq
      rcases hr with hbase | hstruct
      · rcases hbase with hrest | hulift
        · rcases hrest with hrest | heqty
          · rcases hrest with hrest | heqset
            · rcases hrest with hrest | hglobal
              · rcases hrest with hrest | hlet
                · rcases hrest with hrest | henum
                  · rcases hrest with hrest | hempty
                    · rcases hrest with hrest | hunit
                      · rcases hrest with hrest | hsigma
                        · rcases hrest with hcore | hpi
                          · cases hcore with
                            | wfNil => cases heq
                            | wfCons => cases heq; exact hp (.wf Δ) (by simp)
                            | var => cases heq
                            | sort => cases heq
                            | conv => cases heq
                            | eqConv => cases heq
                            | redConv => cases heq
                            | refl => cases heq
                            | symm => cases heq
                            | trans => cases heq
                            | redEq => cases heq
                            | irrel => cases heq
                            | eqProp => cases heq
                            | eqType => cases heq
                            | eqTySort => cases heq
                            | eqTySortApart => cases heq
                            | castSort => cases heq
                          · cases hpi <;> cases heq
                        · cases hsigma <;> cases heq
                      · cases hunit <;> cases heq
                    · cases hempty <;> cases heq
                  · cases henum <;> cases heq
                · cases hlet <;> cases heq
              · cases hglobal <;> cases heq
            · cases heqset <;> cases heq
          · change EqTyLevelled r at heqty
            cases heqty <;> cases heq
        · cases hulift <;> cases heq
      · cases hstruct with
        | eqTyped => cases heq
        | @ctxConv hsg₀ Γ₀ A₀ A₀' s₀ j₀ hj =>
          cases j₀ with
          | wf Γ' =>
            cases heq
            exact ih (.wf Γ') (by simp) Δ A₀ (by cases hj; rfl)
          | ty => cases heq
          | eq => cases heq
          | red => cases heq
  exact aux _ h Γ A rfl

/-- Context validity read at a typing: the context of `Γ ⊢ t ∶ A` is well formed. -/
theorem F0_ctx_ty {sg : Sig} {Γ : Ctx} {t A : Tm}
    (h : Derivable (F0 sg) (Γ ⊢ t ∶ A)) : Derivable (F0 sg) (.wf Γ) :=
  F0_ctx h

/-! ## The corrected sorting reduction without a `⊢ Γ` hypothesis

`sortUniqueAt_of_typed` (`F0/Sorting.lean`) takes `⊢ Γ`; with `F0_ctx` it follows from any
typing in `Γ`, which is how the statement is used: the two sorts of a term are read off
two typings of it. -/

/-- **`SortUniqueAt` from the corrected pair, at a typing**: `TyUniqueTyped`, `ConvInjSort`
and `TopSortUnique` give the sorting lemma at the type of any derivable typing, the
well-formedness of the context coming from context validity. -/
theorem sortUniqueAt_of_typing {sg : Sig} (hty : TyUniqueTyped sg) (hsi : ConvInjSort sg)
    (htop : TopSortUnique sg) {Γ : Ctx} {t A : Tm}
    (ht : Derivable (F0 sg) (Γ ⊢ t ∶ A)) : SortUniqueAt sg Γ A :=
  sortUniqueAt_of_typed hty hsi htop (F0_ctx ht) A

/-- **`WhRed` is empty at propositions** from the corrected pair, with no `⊢ Γ` hypothesis:
the context comes from the reduction's own typing (`F0_ctx`). -/
theorem WhRed.empty_at_prop_of_typing {sg : Sig} (hty : TyUniqueTyped sg)
    (hsi : ConvInjSort sg) (htop : TopSortUnique sg) {Γ : Ctx} {t u A : Tm}
    (h : WhRed (F0 sg) Γ t u A) (hp : Derivable (F0 sg) (Γ ⊢ A ∶ .sort .prop)) : False :=
  WhRed.empty_at_prop (sortUniqueAt_of_typed hty hsi htop (F0_ctx h.1) A) h hp

end Spec
end F0
end STC
