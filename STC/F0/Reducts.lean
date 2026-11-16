import STC.F0.Syntax
/-!
# The right-hand sides of the computation rules

Each computation rule of observational equality builds a term with binders. They are
written once here and used by the rules (`STC/F0/Spec/`) and, later, by the checker, so
that the two cannot drift apart in an index.

This is the subset of `WizMeta/Reducts.lean` that F0 needs: no descriptions, `μ` or
payload equations. Sort arguments are the closed `Srt`; `prop` replaces `Sort 0`.

All arguments are terms over the context `Γ` of the redex, except a codomain `B`, which is
over `Γ, x`.
-/


namespace STC
namespace F0
namespace Tm

def True' : Tm := .unit .prop
def False' : Tm := .empty .prop

/-- `(0 _ : a → b) × (b → a)`: what an equation between two propositions means. -/
def iff (a b : Tm) : Tm :=
  .sigma .prop (.pi .prop a b.shift) (.pi .prop b.shift (a.shiftN 2))

/-- `B` moved under `n` more variables below its own (its variable stays `var 0`). -/
def under (n : Nat) (B : Tm) : Tm := B.ren (upRen (· + n))

/-- funext: `f =_{(x : A) → B} g  ⟶  (0 x : A) → f x =_{B} g x`. -/
def eqPi (A B f g : Tm) : Tm :=
  .pi .prop A (.eq B (.app f.shift (.var 0)) (.app g.shift (.var 0)))

/-- The proof that `B a.1 ≡ B b.1`, from `e : a.1 = b.1` (`e` is `var 0`; the result is over
`Γ, e`): `transp A a.1 (λy _. B a.1 ≡ B y) (reflTy (B a.1)) b.1 e`. -/
def eqSigmaTransport (A B a b : Tm) : Tm :=
  let a1 : Tm := .fst a
  let b1 : Tm := .fst b
  let Ba := B.inst a1
  let P : Tm := .lam (.lam (.eqTy (Ba.shiftN 2) ((B.under 2).inst (.var 1))))
  .transp A.shift a1.shift P.shift (.reflTy Ba.shift) b1.shift (.var 0)

/-- `a =_{(x : A) × B} b  ⟶  (0 e : a.1 =_A b.1) × (cast (B a.1) (B b.1) ê a.2 =_{B b.1} b.2)`. -/
def eqSigma (A B a b : Tm) : Tm :=
  let Ba := B.inst (.fst a)
  let Bb := B.inst (.fst b)
  .sigma .prop (.eq A (.fst a) (.fst b))
    (.eq Bb.shift (.cast Ba.shift Bb.shift (eqSigmaTransport A B a b) (Tm.snd a).shift) (Tm.snd b).shift)

/-- `eqSigma` when `A` is a proposition: the proof that `B a.1 ≡ B b.1` is
`reflTy (B a.1)` (`a.1 ≡ b.1` by proof irrelevance), not `transp` along the proposition
`A`, which the kernels do not form. -/
def eqSigmaProof (A B a b : Tm) : Tm :=
  let Ba := B.inst (.fst a)
  let Bb := B.inst (.fst b)
  .sigma .prop (.eq A (.fst a) (.fst b))
    (.eq Bb.shift (.cast Ba.shift Bb.shift (.reflTy Ba.shift) (Tm.snd a).shift) (Tm.snd b).shift)

/-- `((x : A₁) → B₁) ≡ ((x : A₂) → B₂)  ⟶  (0 e : A₂ ≡ A₁) × ((0 x : A₂) → B₁ (cast A₂ A₁ e x) ≡ B₂ x)`:
the domain equation is backwards, as in CCobs. -/
def eqTyPi (A₁ B₁ A₂ B₂ : Tm) : Tm :=
  let c : Tm := .cast (A₂.shiftN 2) (A₁.shiftN 2) (.var 1) (.var 0)
  .sigma .prop (.eqTy A₂ A₁)
    (.pi .prop A₂.shift (.eqTy ((B₁.under 2).inst c) (B₂.under 1)))

/-- `((x : A₁) × B₁) ≡ ((x : A₂) × B₂)  ⟶  (0 e : A₁ ≡ A₂) × ((0 x : A₁) → B₁ x ≡ B₂ (cast A₁ A₂ e x))`. -/
def eqTySigma (A₁ B₁ A₂ B₂ : Tm) : Tm :=
  let c : Tm := .cast (A₁.shiftN 2) (A₂.shiftN 2) (.var 1) (.var 0)
  .sigma .prop (.eqTy A₁ A₂)
    (.pi .prop A₁.shift (.eqTy (B₁.under 1) ((B₂.under 2).inst c)))

/-- `cast ((x : A₁) → B₁) ((x : A₂) → B₂) e t  ⟶  λx. cast (B₁ x̂) (B₂ x) (e.2 x) (t x̂)`,
`x̂ = cast A₂ A₁ e.1 x`. -/
def castPi (A₁ B₁ A₂ B₂ e t : Tm) : Tm :=
  let x' : Tm := .cast A₂.shift A₁.shift (.fst e.shift) (.var 0)
  .lam (.cast ((B₁.under 1).inst x') B₂ (.app (.snd e.shift) (.var 0)) (.app t.shift x'))

/-- `cast ((x : A₁) × B₁) ((x : A₂) × B₂) e t  ⟶  (c₁, cast (B₁ t.1) (B₂ c₁) (e.2 t.1) t.2)`,
`c₁ = cast A₁ A₂ e.1 t.1`. -/
def castSigma (A₁ B₁ A₂ B₂ e t : Tm) : Tm :=
  let t1 : Tm := .fst t
  let c1 : Tm := .cast A₁ A₂ (.fst e) t1
  .pair c1 (.cast (B₁.inst t1) (B₂.inst c1) (.app (.snd e) t1) (.snd t))

/-- The canonical type formers: two different ones are never equal. -/
inductive Former where
  | pi | sigma | sort | unit | empty | enum | ulift
  deriving BEq, DecidableEq, Repr

def former? : Tm → Option Former
  | .pi .. => some .pi
  | .sigma .. => some .sigma
  | .sort _ => some .sort
  | .unit _ => some .unit
  | .empty _ => some .empty
  | .enum _ => some .enum
  | .ulift .. => some .ulift
  | _ => none

/-- The type of `transp`'s motive for `A : Sort s`:
`(0 b : A) → (0 _ : a =_A b) → Prop`. The inner `Π` is in `Sort (imax 0 1) = Sort 1`, the
outer one in `Sort (imax s 1)`. -/
def transpMotiveTy (s : Srt) (A a : Tm) : Tm :=
  .pi (.imax s .u0) A (.pi .u0 (.eq A.shift a.shift (.var 0)) (.sort .prop))

end Tm
end F0
end STC
