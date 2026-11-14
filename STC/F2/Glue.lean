import STC.F2.Ext0
/-!
# F2: strict `Glue` (stage 22d)

`Glue φ A T f` (`shared-cofib-layer.md` §1, §6, R4) is the strict glue type with
`T : (z : [φ]) → Sort s` and `f : (z : [φ]) → T z → A`. It is `T prf` under `φ`; the
`eqv` field of the shared layer is `none` (STC's `f` is an isomorphism, and the design
does not require an `Equiv`; R4). `glue t a` is the element with underlying `a : A` and
`T`-part `t`, agreeing on the face; `unglue φ f x` is its underlying `A` element.

The rules:

    Γ ⊢ A ∶ Sort s    Γ ⊢ T ∶ ○_φ (Sort s)    Γ ⊢ f ∶ (z:[φ]) → T z → A
    ───────────────────────────────────────────────────────────────────── form
    Γ ⊢ Glue φ A T f ∶ Sort s

    Γ ⊢ Glue φ A T f ∶ Sort s    Γ ⊢ t ∶ (z:[φ]) → T z    Γ ⊢ a ∶ A
    (Γ, z:[φ]) ⊢ f z (t z) ≡ a
    ─────────────────────────────────────────────────────── intro
    Γ ⊢ glue φ t a ∶ Glue φ A T f

    Γ ⊢ Glue φ A T f ∶ Sort s    Γ ⊢ A ∶ Sort s    Γ ⊢ f ∶ (z:[φ]) → T z → A
    Γ ⊢ x ∶ Glue φ A T f
    ──────────────────────────────────────────────────── elim
    Γ ⊢ unglue φ f x ∶ A

    Γ ⊢ ...    Γ ⊢ t ∶ (z:[φ]) → T z    Γ ⊢ a ∶ A    (Γ, z:[φ]) ⊢ f z (t z) ≡ a
    ──────────────────────────────────────────────────────────────────────────── β
    Γ ⊢ unglue φ f (glue φ t a) ⟶ a ∶ A

and the two **restriction (phase) rules**, stated under `z : [φ]`:

    (Γ, z:[φ]) ⊢ Glue φ A T f ≡ T z ∶ Sort s          (Glue is T on the face)
    (Γ, z:[φ]) ⊢ glue φ t a ≡ t z ∶ T z              (glue is its T-part on the face)

`fTy` is the type `(z:[φ]) → T z → A`; `tTy` is `(z:[φ]) → T z`. `Srt.succ?` gives the
sort of `Sort s` (`s = u1` has none, so Glue at the top universe is not formable this
way: `T z : Sort u1` would be a type, not a term).

Unconditional Glue η (R4) is not part of this slice; the β and the two restriction
rules are what the F2 metatheory uses.
-/


namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-- The `T`-part type `(z : [φ]) → T z`. -/
def tTy (φ : F1.Cof) (T : Tm) : Tm :=
  .pi .prop (ph φ) (.app T.shift (.var 0))

/-- The map type `(z : [φ]) → T z → A`. -/
def fTy (s : Srt) (φ : F1.Cof) (A T : Tm) : Tm :=
  .pi .prop (ph φ) (.pi s (.app T.shift (.var 0)) (Tm.shiftN 2 A))

/-- The strict glue type `Glue φ A T f`. -/
abbrev GlueTy (φ : F1.Cof) (A T f : Tm) : Tm := .glueTy φ A T f

/-- F2's strict-`Glue` rules. -/
inductive Glue : Rules
  | form {Γ : Ctx} {A T f : Tm} {φ : F1.Cof} {s s' : Srt} (hs : s.succ? = some s') :
      Glue ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ T ∶ circ s' φ (.sort s), Γ ⊢ f ∶ fTy s φ A T],
        Γ ⊢ GlueTy φ A T f ∶ .sort s⟩
  | intro {Γ : Ctx} {A T f t a : Tm} {φ : F1.Cof} {s s' : Srt}
      (hs : s.succ? = some s') :
      Glue ⟨[Γ ⊢ GlueTy φ A T f ∶ .sort s, Γ ⊢ t ∶ tTy φ T, Γ ⊢ a ∶ A,
          (ph φ :: Γ) ⊢ .app (.app f.shift (.var 0)) (.app t.shift (.var 0)) ≡ a.shift
            ∶ A.shift],
        Γ ⊢ .glue φ t a ∶ GlueTy φ A T f⟩
  | elim {Γ : Ctx} {A T f x : Tm} {φ : F1.Cof} {s s' : Srt}
      (hs : s.succ? = some s') :
      Glue ⟨[Γ ⊢ GlueTy φ A T f ∶ .sort s, Γ ⊢ A ∶ .sort s,
          Γ ⊢ f ∶ fTy s φ A T, Γ ⊢ x ∶ GlueTy φ A T f],
        Γ ⊢ .unglue φ f x ∶ A⟩
  | beta {Γ : Ctx} {A T f t a : Tm} {φ : F1.Cof} {s s' : Srt}
      (hs : s.succ? = some s') :
      Glue ⟨[Γ ⊢ GlueTy φ A T f ∶ .sort s, Γ ⊢ A ∶ .sort s,
          Γ ⊢ f ∶ fTy s φ A T, Γ ⊢ t ∶ tTy φ T, Γ ⊢ a ∶ A,
          (ph φ :: Γ) ⊢ .app (.app f.shift (.var 0)) (.app t.shift (.var 0)) ≡ a.shift
            ∶ A.shift],
        Γ ⊢ .unglue φ f (.glue φ t a) ⟶ a ∶ A⟩
end F2
end STC

/-!
## The two restriction rules (deferred)

The design's strict-Glue collapse rules

    (Γ, z:[φ]) ⊢ Glue φ A T f ≡ T z ∶ Sort s
    (Γ, z:[φ]) ⊢ glue φ t a ≡ t z ∶ T z

are the phase rules proper. They are **not** in `Glue` (and hence not in `F2`) in this
slice: their conclusion lives in the context `z : [φ] :: Γ`, while F0/F1's renaming
lemma `Renames R j` is stated for the context of `j` itself, so proving the rule's
closure would need a relation between a renaming of `Γ` and a renaming of `φ :: Γ` (the
same restricted-context design as the open `StructRenClosed`). They are stated below as
a separate rule set, `GlueRestr`, so the obligation is explicit rather than hidden.
-/

namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-- The strict-Glue restriction rules, kept out of `F2` until the restricted-context
renaming lemma exists. -/
inductive GlueRestr : Rules
  /-- Under `φ`, `Glue φ A T f` is `T z`. -/
  | tyRed {Γ : Ctx} {A T f : Tm} {φ : F1.Cof} {s s' : Srt}
      (hs : s.succ? = some s') :
      GlueRestr ⟨[.wf Γ, Γ ⊢ A ∶ .sort s, Γ ⊢ T ∶ circ s' φ (.sort s),
          Γ ⊢ f ∶ fTy s φ A T],
        (ph φ :: Γ) ⊢ (GlueTy φ A T f).shift ≡ .app T.shift (prf φ) ∶ .sort s⟩
  /-- Under `φ`, `glue φ t a` is `t z`. -/
  | glueRed {Γ : Ctx} {A T f t a : Tm} {φ : F1.Cof} {s s' : Srt}
      (hs : s.succ? = some s') :
      GlueRestr ⟨[Γ ⊢ GlueTy φ A T f ∶ .sort s, Γ ⊢ t ∶ tTy φ T, Γ ⊢ a ∶ A,
          (ph φ :: Γ) ⊢ .app (.app f.shift (.var 0)) (.app t.shift (.var 0)) ≡ a.shift
            ∶ A.shift],
        (ph φ :: Γ) ⊢ (Tm.glue φ t a).shift ≡ .app t.shift (prf φ)
          ∶ .app T.shift (prf φ)⟩

end F2
end STC
