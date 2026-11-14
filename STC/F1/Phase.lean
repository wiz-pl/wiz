import STC.F1.Cof
import STC.F0.Substitution
/-!
# F1: the phase layer — `[φ]` as a proposition, and its rules

F1 (`/workspace/wiz-notes/stc-plan.md` M4b, requirements R1–R3 in
`/workspace/wiz-notes/shared-cofib-layer.md`) is F0 plus

* abstract **phase atoms** and cofibrations over them (`F1/Cof.lean`);
* the proposition `[φ] : Prop` for a cofibration `φ`;
* the open modality `○_φ A := (z : [φ]) → A` (`circ s φ A` below), which is F0's `Π`.

This file is the **specification** half: the phase propositions are opaque constants
(`ph φ`), as the design requires ("named phases never unfold", R1), and the phase rules
are a rule set on top of `F0Base`. The rules are:

* `form`: `[φ] : Prop` (a proposition, not a type in a higher sort);
* `intro`: `φ ⊢ ψ` (the sound and complete decision procedure of `Cof.lean`) and any
  proof of `[φ]` give a proof of `[ψ]`. The proof term is the constant `prf ψ`: the
  evidence of `[φ]` is proof-irrelevant, so the rule may discard it, exactly as STC
  discards phase proofs at run time (R6);
* the three computations that connect the abstract proposition to F0's formers:
  `[⊥] ⟶ Empty prop`, `[⊤] ⟶ Unit prop`, `[φ ∧ ψ] ⟶ (z : [φ]) × [ψ]`.

There is deliberately **no rule for `∨`**: a proof of a disjunction is obtained from a
proof of either disjunct via `intro` (`φ ⊢ φ ∨ ψ`), and elimination is `intro` again
(`φ ∨ ψ ⊢ χ` once both disjuncts entail `χ`). This keeps the primitive rule set small and
shows the cofibration calculus carrying the propositional reasoning.

## What is proved

* `phase_renClosed` / `phase_subClosed`: every phase rule is stable under renaming and
  substitution (the constants are closed; the `intro` premise is the only subderivation);
* **`F1_rename`, `F1_weakening`, `F1_subst`, `F1_subst_eq`, `F1_subst_red`**: the
  renaming and substitution laws for the full F1 fragment `F0Base ∪ Phase`. These are
  the first laws beyond F0, and they are unconditional (no `Struct`-style context hole:
  the phase rules do not move a context entry);
* the derived rules: `⊤` is inhabited, `⊥` eliminates, `∧` introduces/eliminates, and
  `∨` is introduced through `intro`;
* **`circ_form`** (`○_φ` preserves the sort), `circ_intro`/`circ_elim` (the modality's
  `Π`-rules), and **`circ_restrict`**: if `φ ⊢ ψ` then `○_ψ A` gives `○_φ A`. That is
  the phase-restriction lemma the F1 metatheory needs, stated and proved for the first
  time here.

## What remains

* The F1 *term* formers `Ext 0`, strict `Glue` and `●` (R3/R4) are not in this slice;
  they need new term constructors (or the shared layer's `ext`/`glueTy` in `Tm`).
* `F1` here is `F0Base ∪ Phase`, i.e. without F0's two `Struct` rules
  (`eqTyped`, `ctxConv`): their renaming/substitution closure is still the open
  `StructRenClosed`/`StructSubClosed` of `F0/Typing.lean`. The phase rules themselves are
  `Struct`-free, so folding F1 into `F0 ∪ Phase` changes nothing in this file.
* Horn entailments between atoms (`¶_g ≤ ¶_f`, R1) extend `Cof.le` with a finite set of
  implications; the phase rules use `le` only through `le_iff`, so they are unaffected.
-/


namespace STC
namespace F1

open F0
open F0.Spec
open scoped F0.Spec

/-- A printable name for a cofibration, used to key the opaque phase constants.
`Cof.code` need not be injective for the development: equal cofibrations give equal
names by `rfl`, which is all the rules use. -/
def Cof.code : Cof → String
  | .bot => "bot"
  | .top => "top"
  | .atom i => "a" ++ toString i
  | .and a b => "(" ++ Cof.code a ++ "&" ++ Cof.code b ++ ")"
  | .or a b => "(" ++ Cof.code a ++ "|" ++ Cof.code b ++ ")"

/-- The proposition `[φ]`, an opaque constant (R1: named phases never unfold). -/
def ph (φ : Cof) : Tm := .const ("ph." ++ φ.code)

/-- The canonical proof constant of `[ψ]`. The `intro` rule produces it, discarding the
proof of `[φ]`: phase evidence is proof-irrelevant. -/
def prf (ψ : Cof) : Tm := .const ("prf." ++ ψ.code)

/-- The open modality `○_φ A := (0 z : [φ]) → A`, at the sort `s` of `A`: the `Π`'s sort
is `imax prop s = s`, so `○` preserves the universe (`circ_form`). -/
def circ (s : Srt) (φ : Cof) (A : Tm) : Tm := .pi s (ph φ) A.shift

/-! ## The phase rule set -/

/-- F1's phase rules: formation, entailment introduction, and the three computations. -/
inductive Phase : Rules
  | form {Γ : Ctx} {φ : Cof} : Phase ⟨[.wf Γ], Γ ⊢ ph φ ∶ .sort .prop⟩
  /-- `φ ⊢ ψ` and a proof of `[φ]` give a proof of `[ψ]`. -/
  | intro {Γ : Ctx} {e : Tm} {φ ψ : Cof} (h : φ.le ψ = true) :
      Phase ⟨[Γ ⊢ e ∶ ph φ], Γ ⊢ prf ψ ∶ ph ψ⟩
  | botRed {Γ : Ctx} : Phase ⟨[.wf Γ], Γ ⊢ ph .bot ⟶ Tm.False' ∶ .sort .prop⟩
  | topRed {Γ : Ctx} : Phase ⟨[.wf Γ], Γ ⊢ ph .top ⟶ Tm.True' ∶ .sort .prop⟩
  | andRed {Γ : Ctx} {φ ψ : Cof} :
      Phase ⟨[.wf Γ], Γ ⊢ ph (.and φ ψ) ⟶ .sigma .prop (ph φ) (ph ψ) ∶ .sort .prop⟩

/-- **F1** (this slice): the F0 fragment without the two structural conversion rules,
plus the phase layer. -/
abbrev F1 (sg : Sig) : Rules := F0Base sg ∪ Phase

/-! ## Renaming and substitution for the phase rules -/

/-- Every phase rule is stable under renaming: its terms are constants or the renamed
premise, and its only context is the premise's. -/
theorem phase_renClosed {sg : Sig} : RenClosed Phase (F1 sg) := by
  intro r hr ih
  cases hr with
  | form =>
    rename_i Γ φ
    intro ρ Δ hρ hΔ
    exact Derivable.intro (R := F1 sg) ⟨[Jdg.wf Δ], Jdg.ty Δ (ph φ) (Tm.sort .prop)⟩
      (Or.inr (Phase.form (Γ := Δ) (φ := φ))) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact hΔ)
  | intro h =>
    rename_i Γ e φ ψ
    intro ρ Δ hρ hΔ
    exact Derivable.intro (R := F1 sg)
      ⟨[Jdg.ty Δ (e.ren ρ) (ph φ)], Jdg.ty Δ (prf ψ) (ph ψ)⟩
      (Or.inr (Phase.intro (Γ := Δ) (e := e.ren ρ) (φ := φ) (ψ := ψ) h)) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact ih (Jdg.ty Γ e (ph φ)) (by simp) ρ Δ hρ hΔ)
  | botRed =>
    rename_i Γ
    intro ρ Δ hρ hΔ
    exact Derivable.intro (R := F1 sg)
      ⟨[Jdg.wf Δ], Jdg.red Δ (ph .bot) Tm.False' (Tm.sort .prop)⟩
      (Or.inr (Phase.botRed (Γ := Δ))) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact hΔ)
  | topRed =>
    rename_i Γ
    intro ρ Δ hρ hΔ
    exact Derivable.intro (R := F1 sg)
      ⟨[Jdg.wf Δ], Jdg.red Δ (ph .top) Tm.True' (Tm.sort .prop)⟩
      (Or.inr (Phase.topRed (Γ := Δ))) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact hΔ)
  | andRed =>
    rename_i Γ φ ψ
    intro ρ Δ hρ hΔ
    exact Derivable.intro (R := F1 sg)
      ⟨[Jdg.wf Δ], Jdg.red Δ (ph (.and φ ψ)) (.sigma .prop (ph φ) (ph ψ)) (Tm.sort .prop)⟩
      (Or.inr (Phase.andRed (Γ := Δ) (φ := φ) (ψ := ψ))) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact hΔ)

/-- Every phase rule is stable under substitution (the constants are closed). -/
theorem phase_subClosed {sg : Sig} : SubClosed Phase (F1 sg) := by
  intro r hr ih
  cases hr with
  | form =>
    rename_i Γ φ
    intro σ Δ hσ hΔ
    exact Derivable.intro (R := F1 sg) ⟨[Jdg.wf Δ], Jdg.ty Δ (ph φ) (Tm.sort .prop)⟩
      (Or.inr (Phase.form (Γ := Δ) (φ := φ))) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact hΔ)
  | intro h =>
    rename_i Γ e φ ψ
    intro σ Δ hσ hΔ
    exact Derivable.intro (R := F1 sg)
      ⟨[Jdg.ty Δ (e.sub σ) (ph φ)], Jdg.ty Δ (prf ψ) (ph ψ)⟩
      (Or.inr (Phase.intro (Γ := Δ) (e := e.sub σ) (φ := φ) (ψ := ψ) h)) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact ih (Jdg.ty Γ e (ph φ)) (by simp) σ Δ hσ hΔ)
  | botRed =>
    rename_i Γ
    intro σ Δ hσ hΔ
    exact Derivable.intro (R := F1 sg)
      ⟨[Jdg.wf Δ], Jdg.red Δ (ph .bot) Tm.False' (Tm.sort .prop)⟩
      (Or.inr (Phase.botRed (Γ := Δ))) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact hΔ)
  | topRed =>
    rename_i Γ
    intro σ Δ hσ hΔ
    exact Derivable.intro (R := F1 sg)
      ⟨[Jdg.wf Δ], Jdg.red Δ (ph .top) Tm.True' (Tm.sort .prop)⟩
      (Or.inr (Phase.topRed (Γ := Δ))) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact hΔ)
  | andRed =>
    rename_i Γ φ ψ
    intro σ Δ hσ hΔ
    exact Derivable.intro (R := F1 sg)
      ⟨[Jdg.wf Δ], Jdg.red Δ (ph (.and φ ψ)) (.sigma .prop (ph φ) (ph ψ)) (Tm.sort .prop)⟩
      (Or.inr (Phase.andRed (Γ := Δ) (φ := φ) (ψ := ψ))) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact hΔ)

/-- **The renaming lemma for F1**: `F0Base`'s laws plus the phase rules. -/
theorem F1_rename {sg : Sig} (hsg : Sig.Closed sg) {j : Jdg}
    (d : Derivable (F1 sg) j) : Renames (F1 sg) j :=
  rename_of_closed
    (RenClosed.union
      (F0Rules_renClosedIn (sg := sg) (var := .levelled) (R := F1 sg) hsg
        (fun _ x => Or.inl x) (fun _ x => Or.inl (core_in_F0Rules x)))
      phase_renClosed) d

/-- **The substitution lemma for F1**. -/
theorem F1_substs {sg : Sig} (hsg : Sig.Closed sg) {j : Jdg}
    (d : Derivable (F1 sg) j) : Substs (F1 sg) j :=
  subst_of_closed
    (SubClosed.union
      (F0Rules_subClosedIn (sg := sg) (var := .levelled) (R := F1 sg) hsg
        (fun _ d => F1_rename hsg d) (fun _ x => Or.inl x)
        (fun _ x => Or.inl (core_in_F0Rules x)))
      phase_subClosed) d

/-- Weakening for F1: a judged term stays derivable after a well-typed entry is added at
the head of the context. (The phase layer is what makes this the first unconditional
weakening for a system with F0's phase propositions; `F0`'s own law is still conditional
on `StructRenClosed`.) -/
theorem F1_weakening {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {t A B : Tm} {s : Srt}
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (ht : Derivable (F1 sg) (Γ ⊢ t ∶ A))
    (hB : Derivable (F1 sg) (Γ ⊢ B ∶ .sort s)) :
    Derivable (F1 sg) ((B :: Γ) ⊢ t.shift ∶ A.shift) :=
  F1_rename hsg ht Nat.succ (B :: Γ) (RenOK.succ Γ B)
    (ofRule (Or.inl (core_in_F0Rules (Core.wfCons (s := s)))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hΓ, hB⟩))

/-- F1's typing companion at `[a/0]`. As for `F0Base_subst`, the well-formedness of `Γ`
is an explicit hypothesis: F1 context validity (`Γ ⊢ J → ⊢ Γ`) is not proved in this
slice. -/
theorem F1_subst {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t B a : Tm}
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (ht : Derivable (F1 sg) ((A :: Γ) ⊢ t ∶ B))
    (ha : Derivable (F1 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F1 sg) (Γ ⊢ t.inst a ∶ B.inst a) := by
  have hsub : SubOK (F1 sg) (Tm.one a) (A :: Γ) Γ := by
    intro i C hC
    cases i with
    | zero =>
      rw [Ctx.lookup_zero] at hC; cases hC
      simp only [Tm.shift, Tm.one, Tm.sub_ren]
      rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
      exact ha
    | succ i =>
      rw [Ctx.lookup_succ] at hC
      cases hΓi : Ctx.lookup Γ i with
      | none => rw [hΓi] at hC; cases hC
      | some D =>
        rw [hΓi] at hC; cases hC
        simp only [Tm.shift, Tm.one, Tm.sub_ren]
        rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
        exact ofRule (Or.inl (core_in_F0Rules (Core.var hΓi))) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
          exact hΓ)
  have := F1_substs hsg ht (Tm.one a) Γ hsub hΓ
  simpa [Jdg.sub, Tm.inst] using this

/-- F1's conversion companion at `[a/0]`. -/
theorem F1_subst_eq {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t u B a : Tm}
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (ht : Derivable (F1 sg) ((A :: Γ) ⊢ t ≡ u ∶ B))
    (ha : Derivable (F1 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F1 sg) (Γ ⊢ t.inst a ≡ u.inst a ∶ B.inst a) := by
  have hsub : SubOK (F1 sg) (Tm.one a) (A :: Γ) Γ := by
    intro i C hC
    cases i with
    | zero =>
      rw [Ctx.lookup_zero] at hC; cases hC
      simp only [Tm.shift, Tm.one, Tm.sub_ren]
      rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
      exact ha
    | succ i =>
      rw [Ctx.lookup_succ] at hC
      cases hΓi : Ctx.lookup Γ i with
      | none => rw [hΓi] at hC; cases hC
      | some D =>
        rw [hΓi] at hC; cases hC
        simp only [Tm.shift, Tm.one, Tm.sub_ren]
        rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
        exact ofRule (Or.inl (core_in_F0Rules (Core.var hΓi))) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
          exact hΓ)
  have := F1_substs hsg ht (Tm.one a) Γ hsub hΓ
  simpa [Jdg.sub, Tm.inst] using this

/-- F1's reduction companion at `[a/0]`. -/
theorem F1_subst_red {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t u B a : Tm}
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (ht : Derivable (F1 sg) ((A :: Γ) ⊢ t ⟶ u ∶ B))
    (ha : Derivable (F1 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F1 sg) (Γ ⊢ t.inst a ⟶ u.inst a ∶ B.inst a) := by
  have hsub : SubOK (F1 sg) (Tm.one a) (A :: Γ) Γ := by
    intro i C hC
    cases i with
    | zero =>
      rw [Ctx.lookup_zero] at hC; cases hC
      simp only [Tm.shift, Tm.one, Tm.sub_ren]
      rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
      exact ha
    | succ i =>
      rw [Ctx.lookup_succ] at hC
      cases hΓi : Ctx.lookup Γ i with
      | none => rw [hΓi] at hC; cases hC
      | some D =>
        rw [hΓi] at hC; cases hC
        simp only [Tm.shift, Tm.one, Tm.sub_ren]
        rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
        exact ofRule (Or.inl (core_in_F0Rules (Core.var hΓi))) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
          exact hΓ)
  have := F1_substs hsg ht (Tm.one a) Γ hsub hΓ
  simpa [Jdg.sub, Tm.inst] using this


/-! ### Closed formers under renaming and substitution

The phase constants and F0's closed formers are fixed by both operations. These are the
`rfl` facts `simp` needs to read off the reducts of the phase rules. -/

@[simp] theorem tm_ren_const (c : String) (ρ : Nat → Nat) : (Tm.const c).ren ρ = Tm.const c := rfl
@[simp] theorem tm_ren_sort (s : Srt) (ρ : Nat → Nat) : (Tm.sort s).ren ρ = Tm.sort s := rfl
@[simp] theorem tm_ren_unit (s : Srt) (ρ : Nat → Nat) : (Tm.unit s).ren ρ = Tm.unit s := rfl
@[simp] theorem tm_ren_empty (s : Srt) (ρ : Nat → Nat) : (Tm.empty s).ren ρ = Tm.empty s := rfl
@[simp] theorem tm_shift_const (c : String) : (Tm.const c).shift = Tm.const c := rfl
@[simp] theorem tm_shift_sort (s : Srt) : (Tm.sort s).shift = Tm.sort s := rfl
@[simp] theorem tm_shift_unit (s : Srt) : (Tm.unit s).shift = Tm.unit s := rfl
@[simp] theorem tm_shift_empty (s : Srt) : (Tm.empty s).shift = Tm.empty s := rfl
@[simp] theorem tm_sub_const (c : String) (σ : Nat → Tm) : (Tm.const c).sub σ = Tm.const c := rfl
@[simp] theorem tm_sub_sort (s : Srt) (σ : Nat → Tm) : (Tm.sort s).sub σ = Tm.sort s := rfl
@[simp] theorem tm_sub_unit (s : Srt) (σ : Nat → Tm) : (Tm.unit s).sub σ = Tm.unit s := rfl
@[simp] theorem tm_sub_empty (s : Srt) (σ : Nat → Tm) : (Tm.empty s).sub σ = Tm.empty s := rfl

/-! ## Membership in F1, and the generic conversion steps -/

theorem core_in_F1 {sg : Sig} {r : Rule} (h : Core r) : F1 sg r :=
  Or.inl (core_in_F0Rules h)

theorem pi_in_F1 {sg : Sig} {r : Rule} (h : Pi r) : F1 sg r :=
  Or.inl (pi_in_F0Rules h)

theorem sigma_in_F1 {sg : Sig} {r : Rule} (h : Sigma r) : F1 sg r :=
  Or.inl (sigma_in_F0Rules h)

theorem unit_in_F1 {sg : Sig} {r : Rule} (h : Unit r) : F1 sg r :=
  Or.inl (unit_in_F0Rules h)

theorem empty_in_F1 {sg : Sig} {r : Rule} (h : Empty r) : F1 sg r :=
  Or.inl (empty_in_F0Rules h)

theorem eq_in_F1 {sg : Sig} {r : Rule} (h : Eq r) : F1 sg r :=
  Or.inl (eq_in_F0Rules h)

theorem eqTy_in_F1 {sg : Sig} {r : Rule} (h : EqTyLevelled r) : F1 sg r :=
  Or.inl (eqTy_in_F0Rules h)

theorem ulift_in_F1 {sg : Sig} {r : Rule} (h : ULift .levelled r) : F1 sg r :=
  Or.inl (ulift_in_F0Rules h)

theorem phase_in_F1 {sg : Sig} {r : Rule} (h : Phase r) : F1 sg r :=
  Or.inr h

theorem F1_eq_symm {sg : Sig} {Γ : Ctx} {t u A : Tm}
    (h : Derivable (F1 sg) (Γ ⊢ t ≡ u ∶ A)) : Derivable (F1 sg) (Γ ⊢ u ≡ t ∶ A) :=
  ofRule (core_in_F1 (Core.symm (Γ := Γ) (t := t) (u := u) (A := A))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact h)

theorem F1_eq_trans {sg : Sig} {Γ : Ctx} {t u w A : Tm}
    (h1 : Derivable (F1 sg) (Γ ⊢ t ≡ u ∶ A))
    (h2 : Derivable (F1 sg) (Γ ⊢ u ≡ w ∶ A)) :
    Derivable (F1 sg) (Γ ⊢ t ≡ w ∶ A) :=
  ofRule (core_in_F1 (Core.trans (Γ := Γ) (t := t) (u := u) (w := w) (A := A))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h1, h2⟩)

theorem F1_eq_redEq {sg : Sig} {Γ : Ctx} {t u A : Tm}
    (h : Derivable (F1 sg) (Γ ⊢ t ⟶ u ∶ A)) : Derivable (F1 sg) (Γ ⊢ t ≡ u ∶ A) :=
  ofRule (core_in_F1 (Core.redEq (Γ := Γ) (t := t) (u := u) (A := A))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact h)

/-- `Core.conv`: retype a term along a conversion of its type. -/
theorem F1_conv {sg : Sig} {Γ : Ctx} {t A B : Tm} {s : Srt}
    (ht : Derivable (F1 sg) (Γ ⊢ t ∶ A))
    (h : Derivable (F1 sg) (Γ ⊢ A ≡ B ∶ .sort s)) :
    Derivable (F1 sg) (Γ ⊢ t ∶ B) :=
  ofRule (core_in_F1 (Core.conv (Γ := Γ) (t := t) (A := A) (B := B) (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨ht, h⟩)

/-- `⊢ [φ] ∶ Prop` for any cofibration. -/
theorem phase_form {sg : Sig} {Γ : Ctx} (hΓ : Derivable (F1 sg) (.wf Γ)) (φ : Cof) :
    Derivable (F1 sg) (Γ ⊢ ph φ ∶ .sort .prop) :=
  ofRule (phase_in_F1 (Phase.form (Γ := Γ) (φ := φ))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact hΓ)

/-- `⊤` is inhabited: `[⊤]` computes to `Unit prop`. -/
theorem phase_top_intro {sg : Sig} {Γ : Ctx} (hΓ : Derivable (F1 sg) (.wf Γ)) :
    Derivable (F1 sg) (Γ ⊢ .tt ∶ ph .top) := by
  have hred : Derivable (F1 sg) (Γ ⊢ ph .top ⟶ Tm.True' ∶ .sort .prop) :=
    ofRule (phase_in_F1 (Phase.topRed (Γ := Γ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ)
  have heq : Derivable (F1 sg) (Γ ⊢ Tm.True' ≡ ph .top ∶ .sort .prop) :=
    F1_eq_symm (F1_eq_redEq hred)
  have htt : Derivable (F1 sg) (Γ ⊢ .tt ∶ Tm.True') :=
    ofRule (unit_in_F1 (Unit.tt (s := .prop))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ)
  exact F1_conv htt heq

/-- The entailment rule, as a theorem: `φ ⊢ ψ` and a proof of `[φ]` give a proof of `[ψ]`. -/
theorem phase_intro {sg : Sig} {Γ : Ctx} {φ ψ : Cof} {e : Tm}
    (h : φ.le ψ = true) (he : Derivable (F1 sg) (Γ ⊢ e ∶ ph φ)) :
    Derivable (F1 sg) (Γ ⊢ prf ψ ∶ ph ψ) :=
  ofRule (phase_in_F1 (Phase.intro (Γ := Γ) (e := e) (φ := φ) (ψ := ψ) h)) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact he)

/-- `[⊥]` eliminates: it computes to `Empty prop`, so `absurd` applies. -/
theorem phase_bot_elim {sg : Sig} {Γ : Ctx} {A e : Tm} {k : Srt}
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (hA : Derivable (F1 sg) (Γ ⊢ A ∶ .sort k))
    (he : Derivable (F1 sg) (Γ ⊢ e ∶ ph .bot)) :
    Derivable (F1 sg) (Γ ⊢ .absurd A e ∶ A) := by
  have hred : Derivable (F1 sg) (Γ ⊢ ph .bot ⟶ Tm.False' ∶ .sort .prop) :=
    ofRule (phase_in_F1 (Phase.botRed (Γ := Γ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ)
  have heq : Derivable (F1 sg) (Γ ⊢ ph .bot ≡ Tm.False' ∶ .sort .prop) :=
    F1_eq_redEq hred
  have he' : Derivable (F1 sg) (Γ ⊢ e ∶ Tm.False') := F1_conv he heq
  exact ofRule (empty_in_F1 (Empty.absurd (M := A) (s := .prop) (k := k))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hA, he'⟩)

/-- `[φ ∧ ψ]` introduction: `[φ ∧ ψ]` computes to `[φ] × [ψ]`. -/
theorem phase_and_intro {sg : Sig} {Γ : Ctx} {φ ψ : Cof} {e f : Tm}
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (he : Derivable (F1 sg) (Γ ⊢ e ∶ ph φ))
    (hf : Derivable (F1 sg) (Γ ⊢ f ∶ ph ψ)) :
    Derivable (F1 sg) (Γ ⊢ .pair e f ∶ ph (.and φ ψ)) := by
  have hph := phase_form hΓ φ
  have hΓ' : Derivable (F1 sg) (.wf (ph φ :: Γ)) :=
    wfExt (fun _ x => core_in_F1 x) hΓ hph
  have hsig : Derivable (F1 sg) (Γ ⊢ .sigma .prop (ph φ) (ph ψ) ∶ .sort .prop) :=
    ofRule (sigma_in_F1 (Sigma.form (i := .prop) (j := .prop) (s := .prop) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hph, phase_form hΓ' ψ⟩)
  have hred : Derivable (F1 sg)
      (Γ ⊢ ph (.and φ ψ) ⟶ .sigma .prop (ph φ) (ph ψ) ∶ .sort .prop) :=
    ofRule (phase_in_F1 (Phase.andRed (Γ := Γ) (φ := φ) (ψ := ψ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ)
  have heq : Derivable (F1 sg)
      (Γ ⊢ .sigma .prop (ph φ) (ph ψ) ≡ ph (.and φ ψ) ∶ .sort .prop) :=
    F1_eq_symm (F1_eq_redEq hred)
  have hpair : Derivable (F1 sg) (Γ ⊢ .pair e f ∶ .sigma .prop (ph φ) (ph ψ)) :=
    ofRule (sigma_in_F1 (Sigma.pair (s := .prop) (A := ph φ) (B := ph ψ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hsig, he, hf⟩)
  exact F1_conv hpair heq

/-- `[φ ∧ ψ]` first projection. -/
theorem phase_and_fst {sg : Sig} {Γ : Ctx} {φ ψ : Cof} {p : Tm}
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (hp : Derivable (F1 sg) (Γ ⊢ p ∶ ph (.and φ ψ))) :
    Derivable (F1 sg) (Γ ⊢ .fst p ∶ ph φ) := by
  have hred : Derivable (F1 sg)
      (Γ ⊢ ph (.and φ ψ) ⟶ .sigma .prop (ph φ) (ph ψ) ∶ .sort .prop) :=
    ofRule (phase_in_F1 (Phase.andRed (Γ := Γ) (φ := φ) (ψ := ψ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ)
  have heq : Derivable (F1 sg)
      (Γ ⊢ ph (.and φ ψ) ≡ .sigma .prop (ph φ) (ph ψ) ∶ .sort .prop) :=
    F1_eq_redEq hred
  have hp' : Derivable (F1 sg) (Γ ⊢ p ∶ .sigma .prop (ph φ) (ph ψ)) := F1_conv hp heq
  exact ofRule (sigma_in_F1 (STC.F0.Spec.Sigma.fst (s := .prop) (A := ph φ) (B := ph ψ))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact hp')

/-- `[φ ∧ ψ]` second projection. -/
theorem phase_and_snd {sg : Sig} {Γ : Ctx} {φ ψ : Cof} {p : Tm}
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (hp : Derivable (F1 sg) (Γ ⊢ p ∶ ph (.and φ ψ))) :
    Derivable (F1 sg) (Γ ⊢ .snd p ∶ ph ψ) := by
  have hred : Derivable (F1 sg)
      (Γ ⊢ ph (.and φ ψ) ⟶ .sigma .prop (ph φ) (ph ψ) ∶ .sort .prop) :=
    ofRule (phase_in_F1 (Phase.andRed (Γ := Γ) (φ := φ) (ψ := ψ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ)
  have heq : Derivable (F1 sg)
      (Γ ⊢ ph (.and φ ψ) ≡ .sigma .prop (ph φ) (ph ψ) ∶ .sort .prop) :=
    F1_eq_redEq hred
  have hp' : Derivable (F1 sg) (Γ ⊢ p ∶ .sigma .prop (ph φ) (ph ψ)) := F1_conv hp heq
  have hs := ofRule (sigma_in_F1 (STC.F0.Spec.Sigma.snd (s := .prop) (A := ph φ) (B := ph ψ))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact hp')
  simpa [Tm.inst, ph] using hs

/-- `[φ]` gives `[φ ∨ ψ]`, by the entailment rule. -/
theorem phase_or_inl {sg : Sig} {Γ : Ctx} {φ ψ : Cof} {e : Tm}
    (he : Derivable (F1 sg) (Γ ⊢ e ∶ ph φ)) :
    Derivable (F1 sg) (Γ ⊢ prf (.or φ ψ) ∶ ph (.or φ ψ)) :=
  ofRule (phase_in_F1 (Phase.intro (Γ := Γ) (e := e) (φ := φ) (ψ := .or φ ψ)
    (Cof.le_or_left φ ψ))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact he)

/-- `[ψ]` gives `[φ ∨ ψ]`. -/
theorem phase_or_inr {sg : Sig} {Γ : Ctx} {φ ψ : Cof} {e : Tm}
    (he : Derivable (F1 sg) (Γ ⊢ e ∶ ph ψ)) :
    Derivable (F1 sg) (Γ ⊢ prf (.or φ ψ) ∶ ph (.or φ ψ)) :=
  ofRule (phase_in_F1 (Phase.intro (Γ := Γ) (e := e) (φ := ψ) (ψ := .or φ ψ)
    (Cof.le_or_right φ ψ))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact he)

/-! ## The open modality `○_φ A = (z : [φ]) → A` -/

/-- `imax prop s = s`: `○` preserves the sort of its argument. -/
theorem imax_prop_left (s : Srt) : Srt.imax .prop s = s := by
  cases s <;> rfl

/-- `(A.shift).inst e = A` for any `e`: shifting a term by one and instantiating the
outermost variable does nothing. The de Bruijn fact `open_elim` needs. -/
@[simp] theorem Tm_shift_inst (A e : Tm) : (A.shift).inst e = A := by
  simp only [Tm.inst, Tm.shift, Tm.sub_ren]
  rw [show (Tm.one e) ∘ (· + 1) = Tm.var from rfl, Tm.sub_var]

/-- Shifting `○_φ A` once more: the codomain is shifted twice (the `Π`'s sort and the
domain are closed under `shift`, the codomain is not). -/
theorem circ_shift (s : Srt) (φ : Cof) (A : Tm) :
    (circ s φ A).shift = .pi s (ph φ) A.shift.shift := by
  simp only [circ, ph, Tm.shift, Tm.ren, Tm.ren_ren]
  rfl

/-- Formation: `○_φ A` is a type in `A`'s sort. -/
theorem circ_form {sg : Sig} {Γ : Ctx} {A : Tm} {s : Srt} (hsg : Sig.Closed sg)
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (hA : Derivable (F1 sg) (Γ ⊢ A ∶ .sort s)) (φ : Cof) :
    Derivable (F1 sg) (Γ ⊢ circ s φ A ∶ .sort s) := by
  have hph := phase_form hΓ φ
  have hAs : Derivable (F1 sg) ((ph φ :: Γ) ⊢ A.shift ∶ .sort s) :=
    F1_weakening hsg hΓ hA hph
  exact ofRule (pi_in_F1 (Pi.form (i := .prop) (j := s) (s := s) (by simp [Srt.Equiv, imax_prop_left]))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hph, hAs⟩)

/-- Introduction: a term of `A` gives a term of `○_φ A` (the constant function). -/
theorem circ_intro {sg : Sig} {Γ : Ctx} {A a : Tm} {s : Srt} (hsg : Sig.Closed sg)
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (hA : Derivable (F1 sg) (Γ ⊢ A ∶ .sort s))
    (ha : Derivable (F1 sg) (Γ ⊢ a ∶ A)) (φ : Cof) :
    Derivable (F1 sg) (Γ ⊢ .lam a.shift ∶ circ s φ A) := by
  have hPi := circ_form hsg hΓ hA φ
  have hph := phase_form hΓ φ
  have hbody : Derivable (F1 sg) ((ph φ :: Γ) ⊢ a.shift ∶ A.shift) :=
    F1_weakening hsg hΓ ha hph
  exact ofRule (pi_in_F1 (Pi.lam (s := s) (i := .prop) (A := ph φ) (B := A.shift)
    (b := a.shift))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hPi, hph, hbody⟩)

/-- Elimination: apply a term of `○_φ A` to a proof of `[φ]`. -/
theorem circ_elim {sg : Sig} {Γ : Ctx} {A f e : Tm} {s : Srt} {φ : Cof}
    (hf : Derivable (F1 sg) (Γ ⊢ f ∶ circ s φ A))
    (he : Derivable (F1 sg) (Γ ⊢ e ∶ ph φ)) :
    Derivable (F1 sg) (Γ ⊢ .app f e ∶ A) := by
  have happ := ofRule (pi_in_F1 (Pi.app (s := s) (A := ph φ) (B := A.shift) (a := e)))
    (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hf, he⟩)
  simpa using happ

/-- **Restriction of the open modality**: if `φ ⊢ ψ`, then `○_ψ A` gives `○_φ A`.
This is the F1 lemma that lets a derivation under a weaker phase be moved to a stronger
one — the first piece of the "conversion is stable under restriction" metatheory. -/
theorem circ_restrict {sg : Sig} {Γ : Ctx} {A f : Tm} {s : Srt} (hsg : Sig.Closed sg)
    (hΓ : Derivable (F1 sg) (.wf Γ))
    (hA : Derivable (F1 sg) (Γ ⊢ A ∶ .sort s)) {φ ψ : Cof} (h : φ.le ψ = true)
    (hf : Derivable (F1 sg) (Γ ⊢ f ∶ circ s ψ A)) :
    Derivable (F1 sg) (Γ ⊢ .lam (.app f.shift (prf ψ)) ∶ circ s φ A) := by
  have hphφ := phase_form hΓ φ
  have hΓ' : Derivable (F1 sg) (.wf (ph φ :: Γ)) :=
    wfExt (fun _ x => core_in_F1 x) hΓ hphφ
  have hvar : Derivable (F1 sg) ((ph φ :: Γ) ⊢ .var 0 ∶ ph φ) :=
    ofRule (core_in_F1 (Core.var (Γ := ph φ :: Γ) (A := ph φ) (i := 0)
      (by simp [Ctx.lookup_zero, ph]))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΓ')
  have hprf : Derivable (F1 sg) ((ph φ :: Γ) ⊢ prf ψ ∶ ph ψ) :=
    ofRule (phase_in_F1 (Phase.intro (Γ := ph φ :: Γ) (e := .var 0) (φ := φ) (ψ := ψ) h))
      (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
        exact hvar)
  have hfw := F1_weakening hsg hΓ hf hphφ
  rw [circ_shift] at hfw
  have happ : Derivable (F1 sg) ((ph φ :: Γ) ⊢ .app f.shift (prf ψ) ∶ A.shift) := by
    have h := ofRule (pi_in_F1 (Pi.app (s := s) (A := ph ψ) (B := (A.shift).shift)
      (a := prf ψ))) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hfw, hprf⟩)
    simpa using h
  have hPi := circ_form hsg hΓ hA φ
  exact ofRule (pi_in_F1 (Pi.lam (s := s) (i := .prop) (A := ph φ) (B := A.shift)
    (b := .app f.shift (prf ψ)))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hPi, hphφ, happ⟩)

end F1
end STC
