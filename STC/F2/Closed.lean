import STC.F2.Glue
/-!
# F2: the closed modality `●_φ A` (stage 22e, R3)

`●_φ A` is a primitive closed modality (`shared-cofib-layer.md` §7b): introduction forms
`η● a` (`closedIn φ a`) and `⋆●` (`closedStar φ A`, available when the context entails
`φ`), with `η● a ≡ ⋆●` under `φ`, and an eliminator with two methods.

This file gives the **non-dependent** eliminator `closedElim φ A B mEta mStar x`:

    mη : A → B,    m⋆ : [φ] → B,    x : ●_φ A
    ────────────────────────────────────────── elim
    closedElim φ A B mη m⋆ x ∶ B

with the computation rules on the two introductions (`mη a` and `m⋆ prf`). The
dependent eliminator of §7b (a motive `P : ●A → Sort`) and its coherence premise (the
two methods agree under `φ`) are the natural next refinement; the non-dependent version
has the same phase behaviour and keeps the renaming/substitution lemmas small.

The restriction (phase) rule is

    (Γ, z:[φ]) ⊢ η● a ≡ ⋆● ∶ ●_φ A

which is the `conv (Γ, φ) …` collapse of §6/§7b. It is the third of F1's deferred term
formers.
-/


namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-- The closed-modality type `●_φ A`. -/
abbrev ClosedTy (φ : F1.Cof) (A : Tm) : Tm := .closedTy φ A

/-- F2's closed-modality rules. -/
inductive Closed : Rules
  | form {Γ : Ctx} {A : Tm} {φ : F1.Cof} {s : Srt} :
      Closed ⟨[Γ ⊢ A ∶ .sort s], Γ ⊢ ClosedTy φ A ∶ .sort s⟩
  | intro {Γ : Ctx} {A a : Tm} {φ : F1.Cof} {s : Srt} :
      Closed ⟨[Γ ⊢ ClosedTy φ A ∶ .sort s, Γ ⊢ a ∶ A],
        Γ ⊢ .closedIn φ a ∶ ClosedTy φ A⟩
  /-- `⋆●`, given a proof of the phase. -/
  | star {Γ : Ctx} {A : Tm} {φ : F1.Cof} {s : Srt} :
      Closed ⟨[Γ ⊢ ClosedTy φ A ∶ .sort s, Γ ⊢ prf φ ∶ ph φ],
        Γ ⊢ .closedStar φ A ∶ ClosedTy φ A⟩
  | elim {Γ : Ctx} {A B mEta mStar x : Tm} {φ : F1.Cof} {sA sB : Srt} :
      Closed ⟨[Γ ⊢ A ∶ .sort sA, Γ ⊢ B ∶ .sort sB,
          Γ ⊢ mEta ∶ .pi (.imax sA sB) A B.shift,
          Γ ⊢ mStar ∶ .pi sB (ph φ) B.shift,
          Γ ⊢ x ∶ ClosedTy φ A],
        Γ ⊢ .closedElim φ A B mEta mStar x ∶ B⟩
  | betaIn {Γ : Ctx} {A B mEta mStar a : Tm} {φ : F1.Cof} {sA sB : Srt} :
      Closed ⟨[Γ ⊢ A ∶ .sort sA, Γ ⊢ B ∶ .sort sB,
          Γ ⊢ mEta ∶ .pi (.imax sA sB) A B.shift, Γ ⊢ a ∶ A],
        Γ ⊢ .closedElim φ A B mEta mStar (.closedIn φ a) ⟶ .app mEta a ∶ B⟩
  | betaStar {Γ : Ctx} {A B mEta mStar : Tm} {φ : F1.Cof} {sA sB : Srt} :
      Closed ⟨[Γ ⊢ A ∶ .sort sA, Γ ⊢ B ∶ .sort sB,
          Γ ⊢ mStar ∶ .pi sB (ph φ) B.shift, Γ ⊢ prf φ ∶ ph φ],
        Γ ⊢ .closedElim φ A B mEta mStar (.closedStar φ A) ⟶ .app mStar (prf φ) ∶ B⟩
end F2
end STC

/-!
## The restriction rule (deferred)

Under `φ` the two introductions are equal,

    (Γ, z:[φ]) ⊢ η● a ≡ ⋆● ∶ ●_φ A.

As with `GlueRestr`, it is kept out of `Closed`/`F2` in this slice because its conclusion
lives under the proof binder `z : [φ]`, which needs the restricted-context renaming
lemma (the `StructRenClosed` shape) rather than F0/F1's `Renames`. The rule is stated as
`ClosedRestr.collapse` so the gap is explicit.
-/

namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-- The closed-modality restriction rule, kept out of `F2` until the restricted-context
renaming lemma exists. -/
inductive ClosedRestr : Rules
  | collapse {Γ : Ctx} {A a : Tm} {φ : F1.Cof} {s : Srt} :
      ClosedRestr ⟨[.wf Γ, Γ ⊢ A ∶ .sort s, Γ ⊢ a ∶ A],
        (ph φ :: Γ) ⊢ (Tm.closedIn φ a).shift ≡ (Tm.closedStar φ A).shift
          ∶ (ClosedTy φ A).shift⟩

end F2
end STC
