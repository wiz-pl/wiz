import WizMeta.Spec.Rule

/-!
# Equations between constructors: variant Uniform

`con x =_{μ D i} con y` computes to an equation between the payloads. Three variants; a
system takes one. What each gives up:

| | stable under substitution | `cons x xs = cons y ys` at `List A` (a field at a type variable) | `succ m = succ n` |
|---|---|---|---|
| **Kernel** (both kernels) | **no** | `(x = y) × (cast … xs = ys)`, the Σ rule | `m = n` |
| **Stuck** | yes | **stuck**: no injectivity of constructors with a field at a neutral type | `m = n` |
| **Uniform** | yes | the Σ rule | the Σ rule: `(#1 = #1) × (cast … (m, _) = (n, _))`, an equation with a cast |

* *Kernel.* By the description: `ret` gives `True`; a tag field (`Enum k` or a lift of it)
  with two canonical tags continues at that constructor's description if they are equal
  and is the Σ rule if they differ; a recursive field gives the field's equation, paired
  with the rest unless the rest is `ret`; **any other field takes the Σ rule, also when
  its type is neutral**. A substitution can turn a neutral field type into `Enum k`, and
  then the other rule applies, with a result that is equivalent but not convertible. So a
  substitution instance of a well-typed term can be ill typed (E5b: `λ A a b h. h.1`, with
  `h` an equation of two one-field constructors at a field of type `A`, is accepted, and
  its instance at `A := Enum 2` is not; the regression is the case "E5b: …" of the group
  *meta* in `Tests/Meta.lean`, which pins all three variants). The premise "not a tag
  type" is negative (it has to hold of a weak-head normal form, including a neutral one),
  which is why this file takes the notion of weak-head normal type as a parameter.
* *Stuck.* The same, but the Σ rule only at a canonical field type; at a neutral one the
  equation is stuck. Every premise is positive, so the rules are stable. The price is in
  the table.
* *Uniform.* No shortcut. Stable, and no injectivity is lost, but every equation between
  constructors carries a cast of the remaining fields along the tags' equation. That cast
  is between convertible types; whether it goes away is exactly regularity. With
  regularity decided by conversion (`InReg.lean`; `docs/design/conv-regularity.md`) it does
  at inert types, so there the uniform rule is as usable as the shortcut (`succ m = succ
  n` gives `m = n` up to conversion of the *terms*, though the two *types* are still
  different propositions). At a polymorphic type the cast is at a neutral type, where no
  rule removes it: only the axiom `castRefl`. So the conv design makes **Uniform** work
  for inert data, and makes none of the three work fully at polymorphic types.
-/

namespace WizMeta.Spec

inductive PayloadUniform : Rules
  | eq {Γ : Ctx} {x I D i y : Tm} {l : Lvl} : PayloadUniform ⟨[Γ ⊢ .con x ∶ .mu l I D i, Γ ⊢ .con y ∶ .mu l I D i],
      Γ ⊢ .eq (.mu l I D i) (.con x) (.con y) ⟶ .eq (.interp l I D (.muFamily l I D) i) x y ∶ .sort 0⟩
  | eqRedL {Γ : Ctx} {a a' I D i b : Tm} {l : Lvl} : PayloadUniform ⟨[Γ ⊢ a ⟶ a' ∶ .mu l I D i, Γ ⊢ b ∶ .mu l I D i],
      Γ ⊢ .eq (.mu l I D i) a b ⟶ .eq (.mu l I D i) a' b ∶ .sort 0⟩
  | eqRedR {Γ : Ctx} {a I D i b b' : Tm} {l : Lvl} : PayloadUniform ⟨[Γ ⊢ a ∶ .mu l I D i, Γ ⊢ b ⟶ b' ∶ .mu l I D i],
      Γ ⊢ .eq (.mu l I D i) a b ⟶ .eq (.mu l I D i) a b' ∶ .sort 0⟩

end WizMeta.Spec
