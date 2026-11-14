import STC.F0.Spec.Rule
/-!
# Global constants

A signature is a list of closed declarations. A constant is used with no level arguments
(F0's globals are closed; level polymorphism is E2, later). A definition unfolds (δ).
There is no recursion: a declaration is checked in the signature before it
(`Fragments.lean`, `SigWF`).
-/


namespace STC
namespace F0
namespace Spec

inductive Global (sg : Sig) : Rules
  | const {Γ : Ctx} {c : String} {d : Decl} : sg.find? c = some d →
      Global sg ⟨[.wf Γ], Γ ⊢ .const c ∶ d.type⟩
  | delta {Γ : Ctx} {v : Tm} {c : String} {d : Decl} : sg.find? c = some d → d.value = some v →
      Global sg ⟨[.wf Γ], Γ ⊢ .const c ⟶ v ∶ d.type⟩

end Spec
end F0
end STC
