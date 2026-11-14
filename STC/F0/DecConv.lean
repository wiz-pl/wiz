import STC.F0.ConvJoin
import STC.F0.Context
/-!
# The algorithmic conversion `DecConv`: the canonical-head relation and its sort case

`F0/ConvJoin.lean` refuted the reduction-based canonical-head statement (`ConvJoin`):
proof irrelevance and η are conversions, not reductions, so two convertible `λ`-proofs of a
proposition need have no common reduct. The obligation is therefore the *algorithmic*
conversion `DecConv` (`F0/Obligations.lean`): the whnf-interleaved checker that decides
irrelevance and η by construction.

This file takes the canonical-head half of that obligation and makes it a checked object.
It has three parts: the reduction API, the canonical-head relation `CanonConv`, and the
exact remaining gaps.

## 1. `RedStar`: the closure lemmas the statements were missing

`RedStar` (`F0/Obligations.lean`) is the reflexive–transitive closure of a *typed*
reduction step. This file adds its algebra (`redStar_refl`, `redStar_step`,
`redStar_trans`), the soundness direction of joinability —

    redStar_conv:  Γ ⊢ t ∶ A  →  RedStar Γ A t u  →  Γ ⊢ t ≡ u ∶ A
    conv_of_join:  RedStar t v  →  RedStar u v  →  t and u are convertible

— and `redStar_sort_eq`: a `RedStar` chain between two sorts is constant. `conv_of_join`
is the valid half of `ConvJoin`; the refutation (`convJoin_false`) says the converse
fails, which is why the canonical-head relation below cannot be reduction-only.

## 2. `CanonConv`: the canonical-head conversion relation

`CanonConv sg Γ t u A` is the relation a sound check-and-convert algorithm produces:

* `refl`, `symm`, `redL`/`redR` (compare the reducts of the two sides);
* one constructor per well-behaved *generative* conversion rule: the type-former
  congruences (`piCong`, `sigmaCong`, `unitCong`, `emptyCong`, `uliftCong`,
  `eqCong`, `eqTyCong`), the term congruences (`appCong`, `fstCong`, `sndCong`,
  `absurdCong`, `castCong`, `downCong`, `ecaseCong`), and the η rules (`piEta`,
  `sigmaEta`, `unitEta`, `uliftEta`);
* the type- and context-changing rules `eqConv` and `ctxConv` (a checker is called at a
  fixed type and context, so these are *inputs* to the comparison, not recursive
  comparisons);
* `irrel` at a proposition, restricted to endpoints that are not sorts: proof
  irrelevance applies to *proofs*, and a sort is never one. (The guard is what makes the
  sort case of the algorithm a tag comparison; see `canonConv_sort_left`.)

The relation deliberately has **no `trans`** — that is the algorithmic content: a checker
recurses on the two sides instead of guessing the intermediate. Every other F0 conversion
rule is a constructor (the type- and context-changing `eqConv`/`ctxConv` as inputs, the rest
as recursive comparisons), so completeness of `CanonConv` (`CanonConvComplete`) is exactly
**trans-elimination**, the normalisation theorem behind `DecConv`. `CanonConv` is a subset
of `≡` (`canonConv_sound`), and it decides sorts exactly: **a term the algorithm relates to `Sort u` reduces to `Sort u`**

    canonConv_sort_left:   CanonConv Γ (sort u) t A  →  RedStar Γ A t (sort u)
    canonConv_sort_right:  CanonConv Γ t (sort v) A  →  RedStar Γ A t (sort v)
    canonConv_sort_inj:    CanonConv Γ (sort u) (sort v) A  →  u = v

This is the sharp form of the obligation `ConvInjSort`'s phrase "`A ≡ Sort i → A = Sort i`":
syntactic equality is false (`ann (sort i) X ≡ sort i` by `annRed`), but the canonical head
of the other side is the sort. `sort_inj` is **unconditional**, so the algorithm's sort
case is proved; the only remaining step to `ConvInjSort` is completeness of the algorithm
(`CanonConvComplete`), i.e. that every conversion has such a derivation. That is the
normalisation/trans-elimination theorem — the same M1 theorem `DecConv` names — and it is
stated exactly at the end of this file, together with the two reductions it closes
(`convInjSort_of_canonConvComplete`, `sortUniqueAt_of_canonConvComplete`).

The `irrel` guard is lossless once the remaining typing lemma holds: `SortNotProof sg`
(no sort is a proof of a proposition) makes every `irrel` endpoint non-sort
(`notSort_of_sortNotProof`), so `irrel` passes the guard (`canonConv_irrel_of_sortNotProof`).
That lemma is the second exact gap, and it is the `irrel` case of `sortUniqueAt_of_typed`.
-/


namespace STC
namespace F0
namespace Spec

/-! ## `RedStar`: reflexive–transitive closure of typed reduction -/

/-- The empty `RedStar` chain. -/
theorem redStar_refl {sg : Sig} {Γ : Ctx} {A t : Tm} : RedStar sg Γ A t t :=
  Or.inl rfl

/-- Extend a `RedStar` chain on the left by one typed reduction step. -/
theorem redStar_step {sg : Sig} {Γ : Ctx} {A t u v : Tm}
    (h : Derivable (F0 sg) (Γ ⊢ t ⟶ u ∶ A)) (h' : RedStar sg Γ A u v) :
    RedStar sg Γ A t v := by
  rcases h' with rfl | h'
  · exact Or.inr (Relation.TransGen.single h)
  · exact Or.inr (Relation.TransGen.trans (Relation.TransGen.single h) h')

/-- Concatenate two `RedStar` chains. -/
theorem redStar_trans {sg : Sig} {Γ : Ctx} {A t u v : Tm}
    (h1 : RedStar sg Γ A t u) (h2 : RedStar sg Γ A u v) : RedStar sg Γ A t v := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (Relation.TransGen.trans h1 h2)

/-- A `RedStar` chain whose start is a sort is constant (`redStar_of_sort`, restated for
the alphabet of this file). -/
theorem redStar_sort_eq {sg : Sig} {Γ : Ctx} {A : Tm} {u v : Srt}
    (h : RedStar sg Γ A (.sort u) (.sort v)) : u = v := by
  have h' := redStar_of_sort h
  injection h' with h'
  exact h'.symm

/-- A `RedStar` chain moves along a conversion of its type: each step is recast by
`Core.redConv`. -/
theorem redStar_redConv {sg : Sig} {Γ : Ctx} {A B : Tm} {s : Srt} {t u : Tm}
    (hc : Derivable (F0 sg) (Γ ⊢ A ≡ B ∶ .sort s)) (h : RedStar sg Γ A t u) :
    RedStar sg Γ B t u := by
  rcases h with rfl | h
  · exact redStar_refl
  · induction h with
    | single step =>
      exact Or.inr (Relation.TransGen.single (ofRule (core_in_F0 Core.redConv) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨step, hc⟩)))
    | tail _ step ih =>
      exact redStar_trans ih (Or.inr (Relation.TransGen.single
        (ofRule (core_in_F0 Core.redConv) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨step, hc⟩))))

/-- A `RedStar` chain moves along a context conversion: each step is recast by
`Struct.ctxConv` (`Typing.ctxConv_red`). -/
theorem redStar_ctxConv {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A A' : Tm} {s : Srt}
    {C t u : Tm} (hc : Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s))
    (h : RedStar sg (A :: Γ) C t u) : RedStar sg (A' :: Γ) C t u := by
  rcases h with rfl | h
  · exact redStar_refl
  · induction h with
    | single step => exact Or.inr (Relation.TransGen.single (ctxConv_red hsg hc step))
    | tail _ step ih =>
      exact redStar_trans ih (Or.inr (Relation.TransGen.single (ctxConv_red hsg hc step)))

/-- **A `RedStar` chain is a conversion**, given the typing of its start: every step is a
conversion (`Core.redEq`), and the empty chain is `Core.refl`. (The typing hypothesis is
only used by the empty chain: a step types its own endpoints.) -/
theorem redStar_conv {sg : Sig} {Γ : Ctx} {A t u : Tm}
    (ht : Derivable (F0 sg) (Γ ⊢ t ∶ A)) (h : RedStar sg Γ A t u) :
    Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A) := by
  rcases h with rfl | h
  · exact ofRule (core_in_F0 Core.refl) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact ht)
  · induction h with
    | single step =>
      exact ofRule (core_in_F0 Core.redEq) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
        exact step)
    | tail _ step ih =>
      exact ofRule (core_in_F0 Core.trans) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨ih, ofRule (core_in_F0 Core.redEq) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
          exact step)⟩)

/-- **The sound half of joinability**: two terms with a common `RedStar` reduct are
convertible. The converse is false (`ConvJoin.lean`, `convJoin_false`): `irrel` and η
relate terms that have no common reduct. -/
theorem conv_of_join {sg : Sig} {Γ : Ctx} {A t u v : Tm}
    (ht : Derivable (F0 sg) (Γ ⊢ t ∶ A)) (hu : Derivable (F0 sg) (Γ ⊢ u ∶ A))
    (h1 : RedStar sg Γ A t v) (h2 : RedStar sg Γ A u v) :
    Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A) :=
  ofRule (core_in_F0 Core.trans) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨redStar_conv ht h1, ofRule (core_in_F0 Core.symm) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact redStar_conv hu h2)⟩)

/-! ## The canonical-head conversion relation -/

/-- `t` is not a syntactic sort. The algorithmic guard on proof irrelevance and on the η
rules: a sort is not a proof, and comparing two sorts is a tag comparison, not η or
irrelevance. -/
def NotSort (t : Tm) : Prop := ∀ s, t ≠ .sort s

/-- **`CanonConv sg Γ t u A`**: the canonical-head (trans-free) conversion relation a
check-and-convert algorithm produces. Every constructor is a sound conversion rule or a
composition of one with the recursive calls; `trans` is absent, which is the point. -/
inductive CanonConv (sg : Sig) : Ctx → Tm → Tm → Tm → Prop where
  /-- the endpoints are the same typed term -/
  | refl {Γ : Ctx} {t A : Tm} : Derivable (F0 sg) (Γ ⊢ t ∶ A) → CanonConv sg Γ t t A
  /-- the comparison is symmetric -/
  | symm {Γ : Ctx} {t u A : Tm} : CanonConv sg Γ u t A → CanonConv sg Γ t u A
  /-- reduce the left side and continue -/
  | redL {Γ : Ctx} {t t' u A : Tm} : Derivable (F0 sg) (Γ ⊢ t ⟶ t' ∶ A) →
      CanonConv sg Γ t' u A → CanonConv sg Γ t u A
  /-- reduce the right side and continue -/
  | redR {Γ : Ctx} {t u u' A : Tm} : Derivable (F0 sg) (Γ ⊢ u ⟶ u' ∶ A) →
      CanonConv sg Γ t u' A → CanonConv sg Γ t u A
  /-- proof irrelevance at a proposition, for endpoints that are not sorts -/
  | irrel {Γ : Ctx} {A t u : Tm} {s : Srt} : s.IsZero →
      Derivable (F0 sg) (Γ ⊢ A ∶ .sort s) →
      Derivable (F0 sg) (Γ ⊢ t ∶ A) → Derivable (F0 sg) (Γ ⊢ u ∶ A) →
      NotSort t → NotSort u → CanonConv sg Γ t u A
  /-- `Pi.cong` -/
  | piCong {Γ : Ctx} {A A' B B' : Tm} {i j s s' : Srt} :
      s.Equiv (.imax i j) → s'.Equiv (.imax i j) →
      Derivable (F0 sg) (Γ ⊢ A ∶ .sort i) →
      Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort i) →
      Derivable (F0 sg) ((A :: Γ) ⊢ B ≡ B' ∶ .sort j) →
      CanonConv sg Γ (.pi s A B) (.pi s' A' B') (.sort s)
  /-- `Sigma.cong` -/
  | sigmaCong {Γ : Ctx} {A A' B B' : Tm} {i j s s' : Srt} :
      s.Equiv (.max i j) → s'.Equiv (.max i j) →
      Derivable (F0 sg) (Γ ⊢ A ∶ .sort i) →
      Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort i) →
      Derivable (F0 sg) ((A :: Γ) ⊢ B ≡ B' ∶ .sort j) →
      CanonConv sg Γ (.sigma s A B) (.sigma s' A' B') (.sort s)
  /-- `Unit.cong`: the tag is the sort -/
  | unitCong {Γ : Ctx} {s s' : Srt} : s.Equiv s' →
      Derivable (F0 sg) (.wf Γ) → CanonConv sg Γ (.unit s) (.unit s') (.sort s)
  /-- `Empty.cong`: the tag is the sort -/
  | emptyCong {Γ : Ctx} {s s' : Srt} : s.Equiv s' →
      Derivable (F0 sg) (.wf Γ) → CanonConv sg Γ (.empty s) (.empty s') (.sort s)
  /-- `ULift.cong` -/
  | uliftCong {Γ : Ctx} {A A' : Tm} {l k l' : Srt} : l.Equiv l' →
      Derivable (F0 sg) (Γ ⊢ .ulift l A ∶ .sort l) →
      Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort k) →
      CanonConv sg Γ (.ulift l A) (.ulift l' A') (.sort l)
  /-- `Eq.eqCong` -/
  | eqCong {Γ : Ctx} {A A' a a' b b' : Tm} {s : Srt} :
      Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s) →
      Derivable (F0 sg) (Γ ⊢ a ≡ a' ∶ A) →
      Derivable (F0 sg) (Γ ⊢ b ≡ b' ∶ A) →
      CanonConv sg Γ (.eq A a b) (.eq A' a' b') (.sort .prop)
  /-- `Eq.eqTyCong` -/
  | eqTyCong {Γ : Ctx} {A A' B B' : Tm} {s s' : Srt} :
      Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s) →
      Derivable (F0 sg) (Γ ⊢ B ≡ B' ∶ .sort s') →
      CanonConv sg Γ (.eqTy A B) (.eqTy A' B') (.sort .prop)
  /-- `Eq.castCong`: the proofs `e`, `e'` are not compared -/
  | castCong {Γ : Ctx} {A A' B B' e e' t t' : Tm} {s : Srt} :
      Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s) →
      Derivable (F0 sg) (Γ ⊢ B ≡ B' ∶ .sort s) →
      Derivable (F0 sg) (Γ ⊢ e ∶ .eqTy A B) →
      Derivable (F0 sg) (Γ ⊢ e' ∶ .eqTy A' B') →
      Derivable (F0 sg) (Γ ⊢ t ≡ t' ∶ A) →
      CanonConv sg Γ (.cast A B e t) (.cast A' B' e' t') B
  /-- `Pi.appCong` -/
  | appCong {Γ : Ctx} {f f' A B a a' : Tm} {s : Srt} :
      Derivable (F0 sg) (Γ ⊢ f ≡ f' ∶ .pi s A B) →
      Derivable (F0 sg) (Γ ⊢ a ≡ a' ∶ A) →
      CanonConv sg Γ (.app f a) (.app f' a') (B.inst a)
  /-- `Sigma.fstCong` -/
  | fstCong {Γ : Ctx} {p p' A B : Tm} {s : Srt} :
      Derivable (F0 sg) (Γ ⊢ p ≡ p' ∶ .sigma s A B) →
      CanonConv sg Γ (.fst p) (.fst p') A
  /-- `Sigma.sndCong` -/
  | sndCong {Γ : Ctx} {p p' A B : Tm} {s : Srt} :
      Derivable (F0 sg) (Γ ⊢ p ≡ p' ∶ .sigma s A B) →
      CanonConv sg Γ (.snd p) (.snd p') (B.inst (.fst p))
  /-- `Empty.absurdCong` -/
  | absurdCong {Γ : Ctx} {M M' t t' : Tm} {k s : Srt} :
      Derivable (F0 sg) (Γ ⊢ M ≡ M' ∶ .sort k) →
      Derivable (F0 sg) (Γ ⊢ t ≡ t' ∶ .empty s) →
      CanonConv sg Γ (.absurd M t) (.absurd M' t') M
  /-- `ULift.downCong` -/
  | downCong {Γ : Ctx} {t t' A : Tm} {l : Srt} :
      Derivable (F0 sg) (Γ ⊢ t ≡ t' ∶ .ulift l A) →
      CanonConv sg Γ (.down t) (.down t') A
  /-- `Enum.ecaseCong`: the scrutinee, the motive and the branches are compared; the
  branch conversions come in as a derived premise list (`branchEqPrems`) -/
  | ecaseCong {Γ : Ctx} {s s' M M' : Tm} {k : Srt} {n : Nat} {bl bl' : List Tm}
      (hlen : bl.length = n) (hlen' : bl'.length = n)
      (hss : CanonConv sg Γ s s' (.enum n))
      (hMM : CanonConv sg (.enum n :: Γ) M M' (.sort k))
      (hb : ∀ j, j ∈ branchEqPrems Γ M n bl bl' → Derivable (F0 sg) j) :
      CanonConv sg Γ (.ecase M s (.branches bl)) (.ecase M' s' (.branches bl')) (M.inst s)
  /-- `Core.eqConv`: a conversion at `A` is a conversion at any `B` with `A ≡ B` at a
  sort. The checker is type-directed; this constructor lets the relation follow the type.
  (`Core.redConv`, the reduction analogue, is absorbed by `redL`/`redR`.) -/
  | eqConv {Γ : Ctx} {t u A B : Tm} {s : Srt} :
      CanonConv sg Γ t u A → Derivable (F0 sg) (Γ ⊢ A ≡ B ∶ .sort s) →
      CanonConv sg Γ t u B
  /-- `Struct.ctxConv`: a conversion in `A :: Γ` is a conversion in `A' :: Γ` when the
  entries convert. (The context conversion is an input to the checker, not one of the two
  compared terms.) -/
  | ctxConv {hsg : Sig.Closed sg} {Γ : Ctx} {A A' : Tm} {s : Srt} {t u C : Tm} :
      Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s) →
      CanonConv sg (A :: Γ) t u C → CanonConv sg (A' :: Γ) t u C
  /-- `Pi.eta`, for non-sort endpoints -/
  | piEta {Γ : Ctx} {f g A B : Tm} {s i : Srt} :
      Derivable (F0 sg) (Γ ⊢ f ∶ .pi s A B) → Derivable (F0 sg) (Γ ⊢ g ∶ .pi s A B) →
      Derivable (F0 sg) (Γ ⊢ A ∶ .sort i) →
      Derivable (F0 sg) ((A :: Γ) ⊢ .app f.shift (.var 0) ≡ .app g.shift (.var 0) ∶ B) →
      NotSort f → NotSort g → CanonConv sg Γ f g (.pi s A B)
  /-- `Sigma.eta`, for non-sort endpoints -/
  | sigmaEta {Γ : Ctx} {p q A B : Tm} {s : Srt} :
      Derivable (F0 sg) (Γ ⊢ p ∶ .sigma s A B) → Derivable (F0 sg) (Γ ⊢ q ∶ .sigma s A B) →
      Derivable (F0 sg) (Γ ⊢ .fst p ≡ .fst q ∶ A) →
      Derivable (F0 sg) (Γ ⊢ .snd p ≡ .snd q ∶ B.inst (.fst p)) →
      NotSort p → NotSort q → CanonConv sg Γ p q (.sigma s A B)
  /-- `Unit.eta`: all terms of a `Unit` are convertible, for non-sort endpoints -/
  | unitEta {Γ : Ctx} {t u : Tm} {s : Srt} :
      Derivable (F0 sg) (Γ ⊢ t ∶ .unit s) → Derivable (F0 sg) (Γ ⊢ u ∶ .unit s) →
      NotSort t → NotSort u → CanonConv sg Γ t u (.unit s)
  /-- `ULift.eta`, for non-sort endpoints -/
  | uliftEta {Γ : Ctx} {t u : Tm} {A : Tm} {l : Srt} :
      Derivable (F0 sg) (Γ ⊢ t ∶ .ulift l A) → Derivable (F0 sg) (Γ ⊢ u ∶ .ulift l A) →
      Derivable (F0 sg) (Γ ⊢ .down t ≡ .down u ∶ A) →
      NotSort t → NotSort u → CanonConv sg Γ t u (.ulift l A)

/-! ### Soundness: every algorithmic derivation is a conversion -/

/-- **The algorithm is sound**: every `CanonConv` derivation is a conversion of F0. Each
constructor is the corresponding rule (or `Core.redEq` plus `Core.trans` for the reduction
interleaving). -/
theorem canonConv_sound {sg : Sig} : ∀ {Γ : Ctx} {t u A : Tm},
    CanonConv sg Γ t u A → Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A) := by
  intro Γ t u A h
  induction h with
  | refl ht =>
    exact ofRule (core_in_F0 Core.refl) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact ht)
  | symm _ ih =>
    exact ofRule (core_in_F0 Core.symm) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact ih)
  | redL h _ ih =>
    exact ofRule (core_in_F0 Core.trans) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨ofRule (core_in_F0 Core.redEq) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
        exact h), ih⟩)
  | redR h _ ih =>
    exact ofRule (core_in_F0 Core.trans) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨ih, ofRule (core_in_F0 Core.symm) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
        exact ofRule (core_in_F0 Core.redEq) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
          exact h))⟩)
  | irrel hs hA ht hu _ _ =>
    exact ofRule (core_in_F0 (Core.irrel (s := _) hs)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hA, ht, hu⟩)
  | piCong hs hs' hA hAA hBB =>
    exact ofRule (pi_in_F0 (Pi.cong (i := _) (j := _) (s := _) (s' := _) hs hs')) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hA, hAA, hBB⟩)
  | sigmaCong hs hs' hA hAA hBB =>
    exact ofRule (sigma_in_F0 (Sigma.cong (i := _) (j := _) (s := _) (s' := _) hs hs')) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hA, hAA, hBB⟩)
  | unitCong hs hΓ =>
    exact ofRule (unit_in_F0 (Unit.cong (s := _) (s' := _) hs)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ)
  | emptyCong hs hΓ =>
    exact ofRule (empty_in_F0 (Empty.cong (s := _) (s' := _) hs)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ)
  | uliftCong hs hA hAA =>
    exact ofRule (ulift_in_F0 (ULift.cong (var := .levelled) (l := _) (k := _) (l' := _) hs)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hA, hAA⟩)
  | eqCong hAA haa hbb =>
    exact ofRule (eq_in_F0 (Eq.eqCong (s := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hAA, haa, hbb⟩)
  | eqTyCong hAA hBB =>
    exact ofRule (eq_in_F0 (Eq.eqTyCong (s := _) (s' := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hAA, hBB⟩)
  | castCong hAA hBB he he' htt =>
    exact ofRule (eq_in_F0 (Eq.castCong (s := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hAA, hBB, he, he', htt⟩)
  | appCong hff haa =>
    exact ofRule (pi_in_F0 (Pi.appCong (s := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hff, haa⟩)
  | fstCong hpp =>
    exact ofRule (sigma_in_F0 (Sigma.fstCong (s := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hpp)
  | sndCong hpp =>
    exact ofRule (sigma_in_F0 (Sigma.sndCong (s := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hpp)
  | absurdCong hMM htt =>
    exact ofRule (empty_in_F0 (Empty.absurdCong (k := _) (s := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hMM, htt⟩)
  | downCong htt =>
    exact ofRule (ulift_in_F0 (ULift.downCong (var := .levelled) (l := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact htt)
  | ecaseCong hlen hlen' hss hMM hb ihss ihMM =>
    exact ofRule (enum_in_F0 (Enum.ecaseCong (k := _) (n := _) hlen hlen')) (by
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact ihss
        · exact ihMM
      · exact hb p hp)
  | eqConv _ hc ih =>
    exact ofRule (core_in_F0 Core.eqConv) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨ih, hc⟩)
  | @ctxConv hsg _ _ _ _ _ _ _ hc h ih =>
    exact ctxConv_eq hsg hc ih
  | piEta hf hg hA heta _ _ =>
    exact ofRule (pi_in_F0 (Pi.eta (s := _) (i := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hf, hg, hA, heta⟩)
  | sigmaEta hp hq hfst hsnd _ _ =>
    exact ofRule (sigma_in_F0 (Sigma.eta (s := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hp, hq, hfst, hsnd⟩)
  | unitEta ht hu _ _ =>
    exact ofRule (unit_in_F0 (Unit.eta (s := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨ht, hu⟩)
  | uliftEta ht hu hd _ _ =>
    exact ofRule (ulift_in_F0 (ULift.eta (var := .levelled) (l := _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨ht, hu, hd⟩)

/-! ### The sort case: a sort is related only to terms that reduce to it -/

/-- **The canonical-head theorem for sorts.** If the algorithm relates a term to `Sort a`,
the term reduces (`RedStar`) to `Sort a`; and symmetrically. This is the sharp form of
`ConvInjSort`'s "`A ≡ Sort i → A = Sort i`": syntactic equality is false (`annRed` turns
`ann (Sort i) X` into `Sort i`), but the canonical head of the other side is the sort.

Every constructor is either a reduction step (whose start cannot be a sort:
`red_not_sort`), a head former (which cannot be a sort), or a rule guarded by `NotSort`. -/
theorem canonConv_sort_star {sg : Sig} : ∀ {Γ : Ctx} {t u A : Tm},
    CanonConv sg Γ t u A →
    (∀ a, t = .sort a → RedStar sg Γ A u (.sort a)) ∧
    (∀ b, u = .sort b → RedStar sg Γ A t (.sort b)) := by
  intro Γ t u A h
  induction h with
  | refl ht =>
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · subst ha; exact redStar_refl
    · subst hb; exact redStar_refl
  | symm _ ih =>
    exact ⟨fun a ha => ih.2 a ha, fun b hb => ih.1 b hb⟩
  | redL hstep _ ih =>
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · subst ha
      exact (red_not_sort (.red _ _ _ _) hstep _ _ _ _ a rfl rfl).elim
    · exact redStar_step hstep (ih.2 b hb)
  | redR hstep _ ih =>
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · exact redStar_step hstep (ih.1 a ha)
    · subst hb
      exact (red_not_sort (.red _ _ _ _) hstep _ _ _ _ b rfl rfl).elim
  | irrel _ _ _ _ hnt hnu =>
    exact ⟨fun a ha => absurd ha (hnt a), fun b hb => absurd hb (hnu b)⟩
  | piCong _ _ _ _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | sigmaCong _ _ _ _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | unitCong _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | emptyCong _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | uliftCong _ _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | eqCong _ _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | eqTyCong _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | castCong _ _ _ _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | appCong _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | fstCong _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | sndCong _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | absurdCong _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | downCong _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | ecaseCong _ _ _ _ _ =>
    constructor
    · intro a ha; cases ha
    · intro b hb; cases hb
  | eqConv _ hc ih =>
    exact ⟨fun a ha => redStar_redConv hc (ih.1 a ha),
      fun b hb => redStar_redConv hc (ih.2 b hb)⟩
  | @ctxConv hsg _ _ _ _ _ _ _ hc h ih =>
    exact ⟨fun a ha => redStar_ctxConv hsg hc (ih.1 a ha),
      fun b hb => redStar_ctxConv hsg hc (ih.2 b hb)⟩
  | piEta _ _ _ _ hnt hnu =>
    exact ⟨fun a ha => absurd ha (hnt a), fun b hb => absurd hb (hnu b)⟩
  | sigmaEta _ _ _ _ hnt hnu =>
    exact ⟨fun a ha => absurd ha (hnt a), fun b hb => absurd hb (hnu b)⟩
  | unitEta _ _ hnt hnu =>
    exact ⟨fun a ha => absurd ha (hnt a), fun b hb => absurd hb (hnu b)⟩
  | uliftEta _ _ _ hnt hnu =>
    exact ⟨fun a ha => absurd ha (hnt a), fun b hb => absurd hb (hnu b)⟩

/-- **A sort's canonical head is itself**: if the algorithm relates `Sort a` to `t`, then
`t` reduces to `Sort a`. -/
theorem canonConv_sort_left {sg : Sig} {Γ : Ctx} {t A : Tm} {a : Srt}
    (h : CanonConv sg Γ (.sort a) t A) : RedStar sg Γ A t (.sort a) :=
  (canonConv_sort_star h).1 a rfl

/-- **A sort's canonical head is itself**, from the right. -/
theorem canonConv_sort_right {sg : Sig} {Γ : Ctx} {t A : Tm} {b : Srt}
    (h : CanonConv sg Γ t (.sort b) A) : RedStar sg Γ A t (.sort b) :=
  (canonConv_sort_star h).2 b rfl

/-- **The algorithm's sort case is injective**: it relates two sorts only when they are
the same sort. This is `ConvInjSort` read off the algorithm, with no completeness
hypothesis: the algorithm's sort branch is a tag comparison, and this is its soundness. -/
theorem canonConv_sort_inj {sg : Sig} {Γ : Ctx} {A : Tm} {u v : Srt}
    (h : CanonConv sg Γ (.sort u) (.sort v) A) : u = v :=
  redStar_sort_eq (canonConv_sort_right h)

/-! ### The `RedStar` half: joinability in the algorithm -/

/-- The reflexive constructor of the algorithm, at a typing. -/
theorem canonConv_refl {sg : Sig} {Γ : Ctx} {t A : Tm}
    (ht : Derivable (F0 sg) (Γ ⊢ t ∶ A)) : CanonConv sg Γ t t A :=
  CanonConv.refl ht

/-- A `RedStar` chain on the **left** can be absorbed into an algorithmic derivation: this
is the reduction-interleaving constructor `redL` iterated. -/
theorem canonConv_of_redStar_left {sg : Sig} {Γ : Ctx} {A t v u : Tm}
    (h : RedStar sg Γ A t v) (hv : CanonConv sg Γ v u A) : CanonConv sg Γ t u A := by
  rcases h with rfl | h
  · exact hv
  · induction h generalizing u with
    | single step => exact CanonConv.redL step hv
    | tail _ step ih => exact ih (CanonConv.redL step hv)

/-- A `RedStar` chain on the **right** can be absorbed into an algorithmic derivation. -/
theorem canonConv_of_redStar_right {sg : Sig} {Γ : Ctx} {A t u v : Tm}
    (h : RedStar sg Γ A u v) (hv : CanonConv sg Γ t v A) : CanonConv sg Γ t u A := by
  rcases h with rfl | h
  · exact hv
  · induction h generalizing t with
    | single step => exact CanonConv.redR step hv
    | tail _ step ih => exact ih (CanonConv.redR step hv)

/-- **The reduction half of the canonical-head obligation**: two terms that reduce to a
common typed term are algorithmically convertible. (The converse is where `irrel` and η
live, and where `CanonConv`'s non-reduction constructors are used.) -/
theorem canonConv_of_join {sg : Sig} {Γ : Ctx} {A t u v : Tm}
    (h1 : RedStar sg Γ A t v) (h2 : RedStar sg Γ A u v)
    (hv : Derivable (F0 sg) (Γ ⊢ v ∶ A)) : CanonConv sg Γ t u A :=
  canonConv_of_redStar_left h1 (canonConv_of_redStar_right h2 (canonConv_refl hv))

/-! ### The exact remaining gaps

`CanonConvComplete` is completeness of the algorithm: every conversion has a trans-free,
canonical-head derivation. It is the normalisation/trans-elimination theorem that
`DecConv` (`F0/Obligations.lean`) names, and the one part of this file that is not proved.

The second gap is the typing lemma behind the `irrel` guard: `SortNotProof` (`no sort is a
proof of a proposition`). Given it, the guard on `irrel` is lossless
(`canonConv_irrel_of_sortNotProof`), so the guard costs nothing in a complete algorithm. -/

/-- **`CanonConvComplete sg`**: every conversion has an algorithmic (canonical-head)
derivation. This is the remaining obligation: trans-elimination for `≡` (equivalently,
the normalisation theorem behind `DecConv`). -/
def CanonConvComplete (sg : Sig) : Prop :=
  ∀ Γ t u A, Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A) → CanonConv sg Γ t u A

/-- **`SortNotProof sg`**: no sort is a proof of a proposition. This is the typing lemma
the `irrel` case needs (`Core.irrel` needs a *proof* at a proposition; the rules cannot type
a sort there), and it is the `irrel` gap of `sortUniqueAt_of_typed`. -/
def SortNotProof (sg : Sig) : Prop :=
  ∀ Γ (s : Srt) (A : Tm), Derivable (F0 sg) (Γ ⊢ .sort s ∶ A) →
    Derivable (F0 sg) (Γ ⊢ A ∶ .sort .prop) → False

/-- Under `SortNotProof`, a typed term of a proposition is not a syntactic sort: the
`irrel` guard `NotSort` loses no instance. -/
theorem notSort_of_sortNotProof {sg : Sig} (hsp : SortNotProof sg) {Γ : Ctx} {t A : Tm}
    (ht : Derivable (F0 sg) (Γ ⊢ t ∶ A)) (hA : Derivable (F0 sg) (Γ ⊢ A ∶ .sort .prop)) :
    NotSort t :=
  fun s he => hsp Γ s A (he ▸ ht) hA

/-- **The `irrel` constructor without the syntactic guard**, under `SortNotProof`: proof
irrelevance at a proposition applies to any two proofs. -/
theorem canonConv_irrel_of_sortNotProof {sg : Sig} (hsp : SortNotProof sg)
    {Γ : Ctx} {A t u : Tm} {s : Srt} (hs : s.IsZero)
    (hA : Derivable (F0 sg) (Γ ⊢ A ∶ .sort s))
    (ht : Derivable (F0 sg) (Γ ⊢ t ∶ A)) (hu : Derivable (F0 sg) (Γ ⊢ u ∶ A)) :
    CanonConv sg Γ t u A :=
  CanonConv.irrel hs hA ht hu (notSort_of_sortNotProof hsp ht (hs ▸ hA))
    (notSort_of_sortNotProof hsp hu (hs ▸ hA))

/-- **The canonical head of a conversion to a sort** (from completeness): if `t` is
convertible to `Sort u`, then `t` reduces to `Sort u`. This is the algorithmic form of
"`A ≡ Sort i → A = Sort i`": the *canonical* head of `A` is the sort, which is what the
`trans` case of a sorting proof needs (`conv_target_unique_of_injSort`). -/
theorem redStar_of_conv_sort {sg : Sig} (hc : CanonConvComplete sg)
    {Γ : Ctx} {t A : Tm} {u : Srt}
    (h : Derivable (F0 sg) (Γ ⊢ t ≡ .sort u ∶ A)) : RedStar sg Γ A t (.sort u) :=
  canonConv_sort_right (hc Γ t (.sort u) A h)

/-- The symmetric form of `redStar_of_conv_sort`. -/
theorem redStar_of_sort_conv {sg : Sig} (hc : CanonConvComplete sg)
    {Γ : Ctx} {t A : Tm} {u : Srt}
    (h : Derivable (F0 sg) (Γ ⊢ .sort u ≡ t ∶ A)) : RedStar sg Γ A t (.sort u) :=
  canonConv_sort_left (hc Γ (.sort u) t A h)

/-- **`ConvInjSort` from algorithmic completeness**: two convertible sorts are equal. This
is the reduction of `ConvInjSort` (`F0/Obligations.lean`) to the one remaining theorem. -/
theorem convInjSort_of_canonConvComplete {sg : Sig} (hc : CanonConvComplete sg) :
    ConvInjSort sg :=
  fun Γ u v C d => canonConv_sort_inj (hc Γ (.sort u) (.sort v) C d)

/-- **The corrected sorting lemma at a typing, from algorithmic completeness**: composing
`convInjSort_of_canonConvComplete` with `sortUniqueAt_of_typing` (`F0/Context.lean`). -/
theorem sortUniqueAt_of_canonConvComplete {sg : Sig} (hc : CanonConvComplete sg)
    (hty : TyUniqueTyped sg) (htop : TopSortUnique sg) {Γ : Ctx} {t A : Tm}
    (ht : Derivable (F0 sg) (Γ ⊢ t ∶ A)) : SortUniqueAt sg Γ A :=
  sortUniqueAt_of_typing hty (convInjSort_of_canonConvComplete hc) htop ht

/-- **`WhRed` is empty at propositions**, from algorithmic completeness and the corrected
uniqueness pair: the composition of `convInjSort_of_canonConvComplete` with
`WhRed.empty_at_prop_of_typing` (`F0/Context.lean`). -/
theorem WhRed.empty_at_prop_canon {sg : Sig} (hc : CanonConvComplete sg)
    (hty : TyUniqueTyped sg) (htop : TopSortUnique sg) {Γ : Ctx} {t u A : Tm}
    (h : WhRed (F0 sg) Γ t u A) (hp : Derivable (F0 sg) (Γ ⊢ A ∶ .sort .prop)) : False :=
  WhRed.empty_at_prop_of_typing hty (convInjSort_of_canonConvComplete hc) htop h hp

/-- **`DecConvCanon`**: the refined form of `DecConv` (`F0/Obligations.lean`): conversion
is decided by the canonical-head algorithm. Its content is `CanonConvComplete` together
with the checked relation `CanonConv` (sound, `canonConv_sound`, and sort-reflecting,
`canonConv_sort_inj`). -/
def DecConvCanon (sg : Sig) : Prop := CanonConvComplete sg

/-- **The refined obligation implies the original one**: from a complete canonical-head
algorithm whose comparison is decidable, build the fuel-indexed `ConvChecker` of
`DecConv` (`F0/Obligations.lean`). The `if` is the checker: it returns `true` exactly on
`CanonConv`, which is sound by `canonConv_sound` and complete by `CanonConvComplete`. -/
theorem decConv_of_canonConvComplete {sg : Sig} (hc : CanonConvComplete sg)
    (hdec : ∀ (Γ : Ctx) (t u A : Tm), Decidable (CanonConv sg Γ t u A)) :
    DecConv sg := by
  classical
  refine ⟨fun _ Γ t u A => if CanonConv sg Γ t u A then .ok true else .ok false,
    ?_, ?_, ?_⟩
  · intro n Γ t u A h
    by_cases hcan : CanonConv sg Γ t u A
    · exact canonConv_sound hcan
    · simp [hcan] at h
  · intro n Γ t u A h
    by_cases hcan : CanonConv sg Γ t u A
    · simp [hcan] at h
    · intro hconv
      exact hcan (hc Γ t u A hconv)
  · intro Γ t u A hconv
    exact ⟨0, by simp [hc Γ t u A hconv]⟩

end Spec
end F0
end STC
