import STC.F1.Phase
/-!
# F2: the extension type `Ext 0` (stage 22c)

`Ext 0 A φ a` is the extension type `{A ∣ φ ↦ a}` of `shared-cofib-layer.md` §1/§6:
`A` is a type, `a : [φ] → A` its boundary. It is the first of the three F1 *term*
formers deferred by `F1/Phase.lean` (`Ext 0`, strict `Glue`, `●`).

The rules are the `n = 0` instance of §6 (no interval, so `A`, `φ`, `a` are not under
dimension binders):

    Γ ⊢ A ∶ Sort s    Γ ⊢ a ∶ ○_φ A
    ──────────────────────────────── form
    Γ ⊢ Ext 0 A φ a ∶ Sort s

    Γ ⊢ Ext 0 A φ a ∶ Sort s    Γ ⊢ t ∶ A    (Γ, z:[φ]) ⊢ a z ≡ t
    ──────────────────────────────────────────────────────────── intro
    Γ ⊢ in A φ a t ∶ Ext 0 A φ a

    Γ ⊢ Ext 0 A φ a ∶ Sort s    Γ ⊢ x ∶ Ext 0 A φ a
    ───────────────────────────────────────────────── elim
    Γ ⊢ out x ∶ A

with the computation `out (in t) ⟶ t` and the extensionality `in (out x) ≡ x`. `○_φ A`
is F1's open modality `circ` (`(z : [φ]) → A`). The boundary `a z ≡ t` is the `n = 0`
instance of §6's `conv (Γ, φ) A t (a prf)`; the variable `z : [φ]` is what makes the
premise a restriction to the phase.

The boundary premise is a judgment under the proof binder `z : [φ]`; it is the only
place where renaming/substitution need a binder here, and it uses F1's phase formation
rule to extend the target context.
-/


namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-- The boundary type `○_φ A = (z : [φ]) → A` (F1's open modality). -/
abbrev circ := F1.circ
/-- The phase proposition `[φ]`. -/
abbrev ph := F1.ph
/-- The canonical phase proof constant. -/
abbrev prf := F1.prf

/-- The extension type `Ext 0 A φ a`. -/
abbrev Ext (A : Tm) (φ : F1.Cof) (a : Tm) : Tm := .ext A φ a

/-- F2's `Ext 0` rules. -/
inductive Ext0 : Rules
  | form {Γ : Ctx} {A a : Tm} {φ : F1.Cof} {s : Srt} :
      Ext0 ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ a ∶ circ s φ A], Γ ⊢ Ext A φ a ∶ .sort s⟩
  | intro {Γ : Ctx} {A a t : Tm} {φ : F1.Cof} {s : Srt} :
      Ext0 ⟨[Γ ⊢ Ext A φ a ∶ .sort s, Γ ⊢ t ∶ A,
          (ph φ :: Γ) ⊢ .app a.shift (prf φ) ≡ t.shift ∶ A.shift],
        Γ ⊢ .extIn A φ a t ∶ Ext A φ a⟩
  | elim {Γ : Ctx} {A a x : Tm} {φ : F1.Cof} {s : Srt} :
      Ext0 ⟨[Γ ⊢ Ext A φ a ∶ .sort s, Γ ⊢ x ∶ Ext A φ a], Γ ⊢ .extOut x ∶ A⟩
  | beta {Γ : Ctx} {A a t : Tm} {φ : F1.Cof} {s : Srt} :
      Ext0 ⟨[Γ ⊢ Ext A φ a ∶ .sort s, Γ ⊢ t ∶ A],
        Γ ⊢ .extOut (.extIn A φ a t) ⟶ t ∶ A⟩
  | eta {Γ : Ctx} {A a x : Tm} {φ : F1.Cof} {s : Srt} :
      Ext0 ⟨[Γ ⊢ Ext A φ a ∶ .sort s, Γ ⊢ x ∶ Ext A φ a],
        Γ ⊢ .extIn A φ a (.extOut x) ≡ x ∶ Ext A φ a⟩

end F2
end STC
