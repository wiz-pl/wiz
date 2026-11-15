import STC.F0.Reducts
/-!
# Judgments, and rules as data

The architecture is `WizMeta/Spec/Rule.lean`'s, reduced to the four judgments F0 needs
(`/workspace/wiz-notes/stc-m0-spec.md` §2):

    ⊢ Γ                    the context is well formed
    Γ ⊢ t ∶ A              typing (types are terms: `Γ ⊢ A ∶ Sort s`)
    Γ ⊢ t ≡ u ∶ A          conversion
    Γ ⊢ t ⟶ u ∶ A          one step of weak-head reduction

`inert`, `inertD` and `peq` vanish with T1/T2: F0 has no regularity and no descriptions.

A **rule** is a list of premises and a conclusion; each former's file defines the set of
its rule instances (a non-recursive inductive predicate on `Rule`, one constructor per
rule, side conditions as hypotheses); a **system** is a union of such sets; `Derivable R j`
is the one inductive definition.

Reduction is a judgment of its own so that the rule a checker implements by a contraction
is told apart from one it implements in conversion (η, irrelevance). Every reduction is a
conversion (`Core.redEq`). **Proofs are never reduced**: at a proposition conversion holds
by irrelevance and needs no reduction (see `WhRed` in `Spec/Fragments.lean`).
-/


namespace STC
namespace F0

inductive Jdg where
  | wf (Γ : Ctx)
  | ty (Γ : Ctx) (t A : Tm)
  | eq (Γ : Ctx) (t u A : Tm)
  | red (Γ : Ctx) (t u A : Tm)

/-- The context of a judgment. -/
def Jdg.ctx : Jdg → Ctx
  | .wf Γ | .ty Γ .. | .eq Γ .. | .red Γ .. => Γ

/-- Replace the context of a judgment, keeping its terms and its kind. This is the
operation `ctxConv` (`Spec/Struct.lean`) acts with: a judgment about terms in `A :: Γ` is
also a judgment about the same terms in `A' :: Γ`. -/
def Jdg.rectx (Δ : Ctx) : Jdg → Jdg
  | .wf _ => .wf Δ
  | .ty _ t A => .ty Δ t A
  | .eq _ t u A => .eq Δ t u A
  | .red _ t u A => .red Δ t u A

structure Rule where
  prems : List Jdg
  concl : Jdg

/-- A set of rule instances. -/
abbrev Rules := Rule → Prop

instance : Union Rules := ⟨fun R S r => R r ∨ S r⟩

inductive Derivable (R : Rules) : Jdg → Prop where
  | intro (r : Rule) (h : R r) (hp : ∀ p, p ∈ r.prems → Derivable R p) : Derivable R r.concl

theorem Derivable.mono {R S : Rules} (h : ∀ r, R r → S r) {j : Jdg} (d : Derivable R j) :
    Derivable S j := by
  induction d with
  | intro r hr _ ih => exact .intro r (h r hr) ih

theorem Derivable.union_left {R S : Rules} {j : Jdg} (d : Derivable R j) : Derivable (R ∪ S) j :=
  d.mono fun _ h => Or.inl h

theorem Derivable.union_right {R S : Rules} {j : Jdg} (d : Derivable S j) : Derivable (R ∪ S) j :=
  d.mono fun _ h => Or.inr h

namespace Spec

/-- The two rule sets for an equation between two `Π` (`Σ`, `ULift`) types
(`EqTyCross.lean`, `EqTyLevelled.lean`). Rules outside those files that depend on the
choice take it as a parameter (`ULift`). -/
inductive EqTyVariant where
  | cross | levelled
  deriving Repr, DecidableEq

scoped notation:40 Γ " ⊢ " t " ∶ " A => Jdg.ty Γ t A
scoped notation:40 Γ " ⊢ " t " ≡ " u " ∶ " A => Jdg.eq Γ t u A
scoped notation:40 Γ " ⊢ " t " ⟶ " u " ∶ " A => Jdg.red Γ t u A

end Spec
end F0
end STC
