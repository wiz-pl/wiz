import STC.F0.Renaming
/-!
# The M0 obligations, as `Prop`s

M0 asks F0 to **state** what its metatheory will prove (see `STC.lean`'s module doc), not to prove it yet. This file is that list:

* `SoundF0 sg`: a checker exists that is sound, complete and total for F0 typing;
* `Con sg`: a well-formed, axiom-free signature has no closed term of type `Empty prop`;
* `WHN sg`: a deterministic, typed weak-head strategy reaches a whnf at every relevant
  type (a proposition is excluded: `WhRed` is empty there);
* `DecConv sg`: conversion is decided by a sound and complete whnf-interleaved algorithm;
* `DecTC sg`: typing is decided by a sound and complete bidirectional algorithm.

Every obligation below carries two signature hypotheses, and neither is decoration:

* `SigWF F0 sg` (`Spec/Fragments.lean`): declarations have fresh names, every declared type
  is a sort *in the signature before it*, and every value is typed at its declared type.
  Without it, `Global.const` (`Spec/Global.lean`) types a constant at `d.type` for any `d`
  with `sg.find? c = some d`, whatever `d.type` is, and `Global.delta` unfolds any value.
  That makes the old unrestricted `Con` **false**, not merely unproved:
  `F0/Regression.lean` refutes it with
  `badSig = [{ name := "bad", type := Empty prop, value := some tt }]`
  (`conUnrestricted_false`). The writer/checker obligations quantify over the same
  non-signatures, where `Global.const`/`delta` expose declarations the kernel would reject,
  so they carry the hypothesis too. `SigWF` is not a syntactic filter: it would fail for
  `badSig` only by forcing the inconsistency `Con []` denies
  (`badSig_sigWF_gives_empty`, `badSig_not_sigWF_of_con`).
* `Sig.Closed sg` (`Syntax.lean`): every declaration is closed under substitution. This is
  the licence `Struct.eqTyped`/`ctxConv` carry (`Spec/Struct.lean`). **Without it
  `Struct sg` has no instances**, so `F0 sg` admits exactly the `F0Base sg` derivations and
  an obligation named `F0` would silently be about the fragment without the structural
  conversion rules; the two lemmas `F0_rename_of`/`F0_subst_of` (`F0/Typing.lean`) already
  take it.

`F0/Regression.lean` also proves that the hypotheses are jointly inhabited, with a
non-empty signature (`sigWF_closed_axiomFree_inhabited`), so the obligations are not
vacuous.

The checker shape is `WizMeta/Checker.lean`'s: fuel-indexed, substitution-based, `M` a
result or a fuel/error. The functions themselves are M1 work; nothing here is proved.

The last section adds the statements the sorting lemma (`SortUniqueAt`, `F0/WhRed.lean`)
reduces to: uniqueness of types up to conversion (`TyUnique`) and injectivity of the type
formers at conversion (`ConvInjPi`, `ConvInjSigma`, `ConvInjEq`, `ConvInjEqTy`,
`ConvInjEnum`, `ConvInjSort`). `F0/Sorting.lean` proves the reduction and records which
rule-level cases block the statements themselves.
-/


namespace STC
namespace F0
namespace Spec

inductive Err where
  /-- the fuel ran out: not a verdict -/
  | fuel
  /-- the term is rejected -/
  | fail (msg : String)
  deriving Repr, Inhabited

instance : ToString Err := ⟨fun | .fuel => "out of fuel" | .fail m => m⟩

abbrev M := Except Err

/-- A fuel-indexed checker: `some true` accepts, `some false` rejects, `none`/fuel is not
a verdict. This is the shape the M1 checker will have: no environments, no quotation. -/
abbrev Checker := Nat → Ctx → Tm → Tm → M Bool

/-- `check` never accepts an ill-typed term. -/
def Sound (check : Checker) (sg : Sig) : Prop :=
  ∀ n Γ t A, check n Γ t A = .ok true → Derivable (F0 sg) (Γ ⊢ t ∶ A)

/-- `check` accepts every well-typed term at some fuel. -/
def Complete (check : Checker) (sg : Sig) : Prop :=
  ∀ Γ t A, Derivable (F0 sg) (Γ ⊢ t ∶ A) → ∃ n, check n Γ t A = .ok true

/-- `check` rejects every ill-typed term at some fuel (it does not run out of fuel). -/
def Total (check : Checker) (sg : Sig) : Prop :=
  ∀ Γ t A, ¬ Derivable (F0 sg) (Γ ⊢ t ∶ A) → ∃ n, check n Γ t A = .ok false

/-- **`Sound(F0)`**: there is a sound, complete and total checker for F0. The proof is M1/M2
(the M1 checker plus the logical relation for completeness); M0 states it.

`SigWF F0 sg` keeps the claim to signatures the kernel could accept (without it
`Global.const`/`delta` expose a declaration whose type is not a sort or whose value is not
at its type); `Sig.Closed sg` is the licence `Struct`'s rules carry, so this is about `F0`
and not silently about `F0Base` (module doc, `F0/Regression.lean`). -/
def SoundF0 (sg : Sig) : Prop :=
  SigWF F0 sg → Sig.Closed sg →
    ∃ check : Checker, Sound check sg ∧ Complete check sg ∧ Total check sg

/-- **`Con(F0)`**: for a well-formed, closed, axiom-free signature there is no closed proof
of `Empty prop`. The route is PT23's set model of codes plus the Σ/Unit/Enum/ULift cases of
the model memo; no mechanised model in M0. `castRefl` is not a rule, so consistency is
relative to a signature that does not declare it.

**The `SigWF` hypothesis is load-bearing.** The unrestricted statement is false, and not
merely unproved: `Global.const` types `const c` at `d.type` for any declaration `d` found by
`sg.find? c`, and nothing checks that `d.type` is a sort or that `d.value` is at it. The
signature `badSig = [{ name := "bad", type := Empty prop, value := some tt }]` is
`AxiomFree` and proves `[] ⊢ const "bad" ∶ Empty prop` (`F0/Regression.lean`,
`badSig_derives_empty`), refuting the old form (`conUnrestricted_false`).

`SigWF` excludes `badSig` for the right reason: its `defn` constructor checks a value at the
declared type in the signature **before** the declaration, so `SigWF F0 badSig` would give
`[] ⊢ tt ∶ Empty prop` in `F0 []` (`badSig_sigWF_gives_empty`) — the very judgment `Con []`
forbids (`badSig_not_sigWF_of_con`). The hypothesis therefore fails only when the fragment
is already inconsistent; it does not hide the malformed declaration.

`Sig.Closed sg` is there because `F0` includes `Struct`'s two rules and those are licensed
by it: with no `Sig.Closed` proof `Struct sg` is empty, so the statement would be about
`F0Base sg`. -/
def Con (sg : Sig) : Prop :=
  SigWF F0 sg → Sig.Closed sg → AxiomFree sg →
    ∀ t : Tm, ¬ Derivable (F0 sg) (([] : Ctx) ⊢ t ∶ .empty .prop)

/-- A weak-head normal form: well typed, and no further reduction step. -/
def Whnf (sg : Sig) (Γ : Ctx) (t A : Tm) : Prop :=
  Derivable (F0 sg) (Γ ⊢ t ∶ A) ∧ ¬ ∃ u, Derivable (F0 sg) (Γ ⊢ t ⟶ u ∶ A)

/-- The reflexive-transitive closure of one-step reduction at a fixed type. -/
def RedStar (sg : Sig) (Γ : Ctx) (A t u : Tm) : Prop :=
  t = u ∨ Relation.TransGen (fun x y => Derivable (F0 sg) (Γ ⊢ x ⟶ y ∶ A)) t u

/-- A typed, fuel-indexed weak-head strategy: `whnf fuel Γ A t` tries to reduce `t` (a
term of type `A`) to a whnf. -/
abbrev WhnfStrategy := Nat → Ctx → Tm → Tm → Option Tm

/-- **`WHN`**: a deterministic weak-head strategy reaches a whnf at every term of a type
that is not a proposition. At a proposition no proof is reduced (`WhRed` is empty there),
so the hypothesis `s.NeverZero` is essential. The emptiness of `WhRed` at a proposition
needs the sorting lemma `SortUniqueAt` (`F0/WhRed.lean`); see the note there.

The signature hypotheses are those of the module doc: `SigWF` (the strategy is about
signatures the kernel could accept) and `Sig.Closed` (the licence of `Struct`, which is part
of `F0`). -/
def WHN (sg : Sig) : Prop :=
  SigWF F0 sg → Sig.Closed sg →
    ∃ whnf : WhnfStrategy,
      (∀ n Γ A t u, whnf n Γ A t = some u → RedStar sg Γ A t u ∧ Whnf sg Γ u A) ∧
      (∀ Γ A t s, Derivable (F0 sg) (Γ ⊢ t ∶ A) → Derivable (F0 sg) (Γ ⊢ A ∶ .sort s) →
        s.NeverZero → ∃ n u, whnf n Γ A t = some u)

/-- A conversion checker: `conv fuel Γ t u A` decides `Γ ⊢ t ≡ u ∶ A`. -/
abbrev ConvChecker := Nat → Ctx → Tm → Tm → Tm → M Bool

/-- **`DecConv`**: conversion is decided by a typed, whnf-interleaved algorithm (proof
irrelevance at `Prop` first; η at Π/Σ/Unit/ULift; tags; neutral spines), sound and
complete. The signature hypotheses are those of the module doc: `SigWF` and `Sig.Closed`. -/
def DecConv (sg : Sig) : Prop :=
  SigWF F0 sg → Sig.Closed sg →
    ∃ conv : ConvChecker,
      (∀ n Γ t u A, conv n Γ t u A = .ok true → Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A)) ∧
      (∀ n Γ t u A, conv n Γ t u A = .ok false → ¬ Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A)) ∧
      (∀ Γ t u A, Derivable (F0 sg) (Γ ⊢ t ≡ u ∶ A) → ∃ n, conv n Γ t u A = .ok true)

/-! ## The sorting lemma's supporting statements

`SortUniqueAt` (`F0/WhRed.lean`) says a term has at most one sort. Its proof is
"regularity plus uniqueness of types plus injectivity of the formers" (`stc-plan.md`,
M1). The two statements below are that obligation, split at the joint the rules make
visible; `F0/Sorting.lean` derives `SortUniqueAt` from them, and proves the parts of them
that F0's rules do give. They are *statements to prove in M1*: the declarative rules have
no inversion principle for `≡` and no normal-form theorem. Two of the rule-level gaps the
first version of this note recorded are now rules (`Spec/Struct.lean`: `eqTyped`,
`ctxConv`), so `Sorting.lean`'s `conv`/`cong` blockers are discharged; the `trans` case is
not (it needs `ConvJoin`, `Sorting.lean`), and `TyUnique` as stated is false at the top
universe (`F0/TopSort.lean`, `tyUnique_false`), so this file states the corrected
`TyUniqueTyped` and `TopSortUnique` next to it. -/

/-- **`TyUnique`**: two types of one term are convertible at one sort. This is
"uniqueness of types up to conversion"; its proof is where the injectivity lemmas
(`ConvInjPi`, …) are used, at the `conv` case, and those lemmas in turn are where `trans`
and `irrel` block (`F0/Sorting.lean`, "the gap").

**This statement is false at the top universe** (`F0/TopSort.lean`, `tyUnique_false`):
the term `Sort u0` has type `Sort u1` twice (`Core.sort rfl`), so it would give a
conversion `Sort u1 ≡ Sort u1 ∶ Sort c`, but `Sort u1` is a type and not a term
(`Srt.succ? .u1 = none`), so no typing or equation may mention it at an endpoint. It is
kept as the conditional form of the obligation: `TyUnique` implies `TyUniqueTyped`, and
the stated obligations are `TyUniqueTyped` + `TopSortUnique` below. The reduction in
`F0/Sorting.lean` is `sortUniqueAt_of_typed`. -/
def TyUnique (sg : Sig) : Prop :=
  ∀ Γ t A B, Derivable (F0 sg) (Γ ⊢ t ∶ A) → Derivable (F0 sg) (Γ ⊢ t ∶ B) →
    ∃ s, Derivable (F0 sg) (Γ ⊢ A ≡ B ∶ .sort s)

/-- **`ConvInjSort`**: two convertible sorts are the same sort. This is what the `irrel`
case of `SortUniqueAt` needs: proof irrelevance must not identify a sort with anything. -/
def ConvInjSort (sg : Sig) : Prop :=
  ∀ Γ u v C, Derivable (F0 sg) (Γ ⊢ .sort u ≡ .sort v ∶ C) → u = v

/-- **Injectivity of `Π`** at conversion: a convertible pair of `Π` types has convertible
domains and codomains (the codomains under the binder). Together with the `Σ`, `Eq`,
`EqTy` and `Enum` versions this is `stc-plan.md`'s "injectivity of Π, Σ, Eq/EqTy, Enum";
it is what the `conv` case of `TyUnique` needs at an application. -/
def ConvInjPi (sg : Sig) : Prop :=
  ∀ Γ s₁ A₁ B₁ s₂ A₂ B₂ C, Derivable (F0 sg) (Γ ⊢ .pi s₁ A₁ B₁ ≡ .pi s₂ A₂ B₂ ∶ C) →
    (∃ i, Derivable (F0 sg) (Γ ⊢ A₁ ≡ A₂ ∶ .sort i)) ∧
    (∃ j, Derivable (F0 sg) ((A₁ :: Γ) ⊢ B₁ ≡ B₂ ∶ .sort j))

/-- **Injectivity of `Σ`** at conversion. -/
def ConvInjSigma (sg : Sig) : Prop :=
  ∀ Γ s₁ A₁ B₁ s₂ A₂ B₂ C,
    Derivable (F0 sg) (Γ ⊢ .sigma s₁ A₁ B₁ ≡ .sigma s₂ A₂ B₂ ∶ C) →
    (∃ i, Derivable (F0 sg) (Γ ⊢ A₁ ≡ A₂ ∶ .sort i)) ∧
    (∃ j, Derivable (F0 sg) ((A₁ :: Γ) ⊢ B₁ ≡ B₂ ∶ .sort j))

/-- **Injectivity of `Eq`** at conversion: the index type and the two endpoints agree. -/
def ConvInjEq (sg : Sig) : Prop :=
  ∀ Γ A a b A' a' b' C, Derivable (F0 sg) (Γ ⊢ .eq A a b ≡ .eq A' a' b' ∶ C) →
    (∃ s, Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s)) ∧
    Derivable (F0 sg) (Γ ⊢ a ≡ a' ∶ A) ∧ Derivable (F0 sg) (Γ ⊢ b ≡ b' ∶ A)

/-- **Injectivity of `EqTy`** at conversion. -/
def ConvInjEqTy (sg : Sig) : Prop :=
  ∀ Γ A B A' B' C, Derivable (F0 sg) (Γ ⊢ .eqTy A B ≡ .eqTy A' B' ∶ C) →
    (∃ s, Derivable (F0 sg) (Γ ⊢ A ≡ A' ∶ .sort s)) ∧
    (∃ s', Derivable (F0 sg) (Γ ⊢ B ≡ B' ∶ .sort s'))

/-- **Injectivity of `Enum`** at conversion: the sizes agree (an enumeration is its size). -/
def ConvInjEnum (sg : Sig) : Prop :=
  ∀ Γ n m C, Derivable (F0 sg) (Γ ⊢ .enum n ≡ .enum m ∶ C) → n = m

/-! ### The corrected uniqueness statements (the obligations)

`TyUnique` above is false at `Sort u1` (`F0/TopSort.lean`, `tyUnique_false`), so the
obligation is stated on *typed* types and well-formed contexts: a type is an inhabitant of
a sort, and the boundary case where the term is a top sort has no such common sort. The
second statement, `TopSortUnique`, is the branch of `SortUniqueAt` that the corrected
`TyUnique` cannot see: a term of sort `u1` has no other sort. `F0/Sorting.lean` proves
`SortUniqueAt` from the pair plus `ConvInjSort` (`sortUniqueAt_of_typed`), for a
well-formed context. -/

/-- **`TyUniqueTyped`** (the stated obligation): two *typed* types of one term are
convertible at one sort, in a well-formed context. Excludes `A = B = Sort u1`, which is
where `TyUnique` fails. -/
def TyUniqueTyped (sg : Sig) : Prop :=
  ∀ Γ, Derivable (F0 sg) (.wf Γ) → ∀ t A B,
    (∃ s, Derivable (F0 sg) (Γ ⊢ A ∶ .sort s)) →
    (∃ s, Derivable (F0 sg) (Γ ⊢ B ∶ .sort s)) →
    Derivable (F0 sg) (Γ ⊢ t ∶ A) → Derivable (F0 sg) (Γ ⊢ t ∶ B) →
    ∃ s, Derivable (F0 sg) (Γ ⊢ A ≡ B ∶ .sort s)

/-- **`TopSortUnique`** (the stated obligation): no term of sort `u1` has another sort,
in a well-formed context. This is the `u1` branch of `SortUniqueAt`; `TyUniqueTyped`
cannot see it because `Sort u1` is not a term with a sort. -/
def TopSortUnique (sg : Sig) : Prop :=
  ∀ Γ, Derivable (F0 sg) (.wf Γ) → ∀ A s,
    Derivable (F0 sg) (Γ ⊢ A ∶ .sort .u1) → Derivable (F0 sg) (Γ ⊢ A ∶ .sort s) → s = .u1

/-- `TyUnique` is the unconditional form of `TyUniqueTyped` (this direction is immediate;
the converse fails at the top universe). -/
theorem tyUniqueTyped_of_tyUnique {sg : Sig} (h : TyUnique sg) : TyUniqueTyped sg :=
  fun _ _ _ _ _ _ _ => h _ _ _ _

/-- A bidirectional typing checker: `tc fuel Γ t A` decides `Γ ⊢ t ⇐ A`. -/
abbrev TCChecker := Nat → Ctx → Tm → Tm → M Bool

/-- **`DecTC`**: bidirectional typing is sound and complete, hence decidable. The signature
hypotheses are those of the module doc: `SigWF` and `Sig.Closed`. -/
def DecTC (sg : Sig) : Prop :=
  SigWF F0 sg → Sig.Closed sg →
    ∃ tc : TCChecker,
      (∀ n Γ t A, tc n Γ t A = .ok true → Derivable (F0 sg) (Γ ⊢ t ∶ A)) ∧
      (∀ n Γ t A, tc n Γ t A = .ok false → ¬ Derivable (F0 sg) (Γ ⊢ t ∶ A)) ∧
      (∀ Γ t A, Derivable (F0 sg) (Γ ⊢ t ∶ A) → ∃ n, tc n Γ t A = .ok true)

end Spec
end F0
end STC
