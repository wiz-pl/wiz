import STC.F0.Spec.Rule
/-!
# Enumerations

`Enum n : Sort 1`, tags, and `ecase` with a motive over the scrutinee. No η. An
enumeration is its size: labels are metadata and absent from the spec. There is no
`scase`: F0 has no sizes, hence no quantity-less sized case (§4 change 3).
-/


namespace STC
namespace F0
namespace Spec

/-- Each branch at the motive instantiated with its tag. -/
def branchPrems (Γ : Ctx) (M : Tm) (n : Nat) (bl : List Tm) : List Jdg :=
  bl.zipIdx.map fun (b, k) => Γ ⊢ b ∶ M.inst (.tag n k)

def branchEqPrems (Γ : Ctx) (M : Tm) (n : Nat) (bl bl' : List Tm) : List Jdg :=
  (bl.zip bl').zipIdx.map fun ((b, b'), k) => Γ ⊢ b ≡ b' ∶ M.inst (.tag n k)

inductive Enum : Rules
  | form {Γ : Ctx} {n : Nat} : Enum ⟨[.wf Γ], Γ ⊢ .enum n ∶ .sort .u0⟩
  | tag {Γ : Ctx} {i n : Nat} : i < n → Enum ⟨[.wf Γ], Γ ⊢ .tag n i ∶ .enum n⟩
  | ecase {Γ : Ctx} {s M : Tm} {k : Srt} {n : Nat} {bl : List Tm} : bl.length = n →
      Enum ⟨[Γ ⊢ s ∶ .enum n, (.enum n :: Γ) ⊢ M ∶ .sort k] ++ branchPrems Γ M n bl,
        Γ ⊢ .ecase M s (.branches bl) ∶ M.inst s⟩
  | iota {Γ : Ctx} {b M : Tm} {k : Srt} {n i : Nat} {bl : List Tm} :
      bl.length = n → bl[i]? = some b →
      Enum ⟨[.wf Γ, (.enum n :: Γ) ⊢ M ∶ .sort k] ++ branchPrems Γ M n bl,
        Γ ⊢ .ecase M (.tag n i) (.branches bl) ⟶ b ∶ M.inst (.tag n i)⟩
  | ecaseRed {Γ : Ctx} {s s' M : Tm} {k : Srt} {n : Nat} {bl : List Tm} : bl.length = n →
      Enum ⟨[Γ ⊢ s ⟶ s' ∶ .enum n, (.enum n :: Γ) ⊢ M ∶ .sort k] ++ branchPrems Γ M n bl,
        Γ ⊢ .ecase M s (.branches bl) ⟶ .ecase M s' (.branches bl) ∶ M.inst s⟩
  | ecaseCong {Γ : Ctx} {s s' M M' : Tm} {k : Srt} {n : Nat} {bl bl' : List Tm} :
      bl.length = n → bl'.length = n →
      Enum ⟨[Γ ⊢ s ≡ s' ∶ .enum n, (.enum n :: Γ) ⊢ M ≡ M' ∶ .sort k]
        ++ branchEqPrems Γ M n bl bl',
        Γ ⊢ .ecase M s (.branches bl) ≡ .ecase M' s' (.branches bl') ∶ M.inst s⟩
  /-- an equation between two tags is decided; between anything else it is stuck -/
  | eqSame {Γ : Ctx} {i n : Nat} : i < n →
      Enum ⟨[.wf Γ], Γ ⊢ .eq (.enum n) (.tag n i) (.tag n i) ⟶ .True' ∶ .sort .prop⟩
  | eqDiff {Γ : Ctx} {i n j : Nat} : i < n → j < n → i ≠ j →
      Enum ⟨[.wf Γ], Γ ⊢ .eq (.enum n) (.tag n i) (.tag n j) ⟶ .False' ∶ .sort .prop⟩
  | eqRedL {Γ : Ctx} {a a' b : Tm} {n : Nat} :
      Enum ⟨[Γ ⊢ a ⟶ a' ∶ .enum n, Γ ⊢ b ∶ .enum n],
        Γ ⊢ .eq (.enum n) a b ⟶ .eq (.enum n) a' b ∶ .sort .prop⟩
  | eqRedR {Γ : Ctx} {a b b' : Tm} {n : Nat} :
      Enum ⟨[Γ ⊢ a ∶ .enum n, Γ ⊢ b ⟶ b' ∶ .enum n],
        Γ ⊢ .eq (.enum n) a b ⟶ .eq (.enum n) a b' ∶ .sort .prop⟩
  | eqTySame {Γ : Ctx} {n : Nat} :
      Enum ⟨[.wf Γ], Γ ⊢ .eqTy (.enum n) (.enum n) ⟶ .True' ∶ .sort .prop⟩
  | eqTyDiff {Γ : Ctx} {n m : Nat} : n ≠ m →
      Enum ⟨[.wf Γ], Γ ⊢ .eqTy (.enum n) (.enum m) ⟶ .False' ∶ .sort .prop⟩
  /-- the identity cast at an enumeration -/
  | cast {Γ : Ctx} {e t : Tm} {n : Nat} :
      Enum ⟨[Γ ⊢ e ∶ .eqTy (.enum n) (.enum n), Γ ⊢ t ∶ .enum n],
        Γ ⊢ .cast (.enum n) (.enum n) e t ⟶ t ∶ .enum n⟩

end Spec
end F0
end STC
