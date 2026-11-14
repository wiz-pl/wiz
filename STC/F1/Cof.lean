/-!
# F1: cofibrations over abstract phase atoms

The F1 layer of the STC track (`/workspace/wiz-notes/stc-plan.md` M4b, and the STC
requirements R1/R2 in `/workspace/wiz-notes/shared-cofib-layer.md`) starts with a
**cofibration**: a proposition built from abstract phase atoms, `⊥`, `⊤`, `∧` and `∨`.
This file is its propositional core, independent of terms:

* `Cof`: the formulas (a small inductive type, so the syntax is ordinary data);
* `Cof.eval`: the intended semantics, a valuation `Nat → Bool` of the atoms;
* `Cof.le`: a **decidable** entailment, by enumerating the valuations of the atoms that
  occur in the two formulas (`allVals`);
* `Cof.le_iff`: soundness and completeness of `Cof.le` for the valuation semantics — the
  theorem that makes the procedure usable in rules (`F1/Phase.lean` licences its
  entailment rule with `le`);
* the lattice laws (`le_refl`, `le_trans`, `and`/`or` introduction and elimination,
  distributivity, `⊥`/`⊤`), all proved from `le_iff`;
* independence sanity cases: distinct atoms do not entail each other, `⊥` entails
  everything, nothing entails `⊥` except `⊥`, and excluded middle is not even formable:
  `Cof` has no negation.

The cofibration is *abstract*: an atom has no equations, so entailment is exactly the
propositional consequence of the valuation semantics. That is the "distributive lattice"
half of the design's `CofCtx`; the Horn-clause extension (`phase ¶_g ≤ ¶_f`, R1) is noted
in the F1 implementation note as the next step.

The decision procedure is deliberately the simple one (brute force over the atoms that
occur). It is exponential in the number of atoms, but its correctness is exactly
`le_iff`, and the STC cofibrations are tiny. A normal-form check can replace `le` later
without changing any theorem in `F1/Phase.lean`, which only uses `le` through its
soundness (`le_iff.mp`).
-/


namespace STC
namespace F1

/-- A cofibration over abstract phase atoms: `⊥`, `⊤`, an atom, conjunction, disjunction.
There is no negation and no interval/dimension equation: F1's phases are *named* atoms
(R1), so no atom is ever refuted. -/
inductive Cof where
  | bot
  | top
  | atom (i : Nat)
  | and (a b : Cof)
  | or (a b : Cof)
  deriving Repr, Inhabited, BEq, DecidableEq

namespace Cof

/-- The semantics: a valuation of the atoms. A named phase is never forced, so the
valuation is arbitrary and the atoms are independent. -/
def eval (v : Nat → Bool) : Cof → Bool
  | .bot => false
  | .top => true
  | .atom i => v i
  | .and a b => eval v a && eval v b
  | .or a b => eval v a || eval v b

/-- The atoms occurring in a formula (with repetitions). -/
def atoms : Cof → List Nat
  | .bot => []
  | .top => []
  | .atom i => [i]
  | .and a b => atoms a ++ atoms b
  | .or a b => atoms a ++ atoms b

/-- Override a valuation at one atom. (Lean core has no `Function.update`.) -/
def upd (v : Nat → Bool) (a : Nat) (b : Bool) : Nat → Bool :=
  fun n => if n = a then b else v n

@[simp] theorem upd_same (v : Nat → Bool) (a : Nat) (b : Bool) : upd v a b a = b := by
  simp [upd]

theorem upd_ne (v : Nat → Bool) (a : Nat) (b : Bool) {n : Nat} (h : n ≠ a) :
    upd v a b n = v n := by
  simp [upd, h]

/-- All valuations of a finite list of atoms. The entries are total functions
`Nat → Bool`; only their values on the listed atoms are relevant, which is what
`allVals_agree` records. -/
def allVals : List Nat → List (Nat → Bool)
  | [] => [fun _ => false]
  | a :: as => (allVals as).flatMap fun w => [upd w a true, upd w a false]

/-- Every valuation agrees with some enumerated valuation on the listed atoms. (The list
may contain repetitions; the induction still works, because the head override is to the
value of the given valuation at that atom.) -/
theorem allVals_agree : ∀ (as : List Nat) (v : Nat → Bool),
    ∃ w ∈ allVals as, ∀ a ∈ as, w a = v a := by
  intro as
  induction as with
  | nil =>
    intro v
    exact ⟨fun _ => false, by simp [allVals], by simp⟩
  | cons a as ih =>
    intro v
    obtain ⟨w, hw, hag⟩ := ih v
    refine ⟨upd w a (v a), ?_, ?_⟩
    · rw [allVals, List.mem_flatMap]
      refine ⟨w, hw, ?_⟩
      cases v a <;> simp
    · intro b hb
      by_cases hba : b = a
      · subst hba
        simp [upd]
      · have hb' : b ∈ as := by simpa [hba] using hb
        rw [upd_ne w a (v a) hba]
        exact hag b hb'

/-- The value of a formula depends only on the atoms it contains. -/
theorem eval_ext (φ : Cof) {v w : Nat → Bool} (h : ∀ a ∈ φ.atoms, w a = v a) :
    eval w φ = eval v φ := by
  induction φ with
  | bot => rfl
  | top => rfl
  | atom i => simpa [eval, atoms] using h i (by simp [atoms])
  | and a b iha ihb =>
    have ha := iha (fun x hx => h x (List.mem_append_left _ hx))
    have hb := ihb (fun x hx => h x (List.mem_append_right _ hx))
    simp only [eval] at ha hb ⊢
    rw [ha, hb]
  | or a b iha ihb =>
    have ha := iha (fun x hx => h x (List.mem_append_left _ hx))
    have hb := ihb (fun x hx => h x (List.mem_append_right _ hx))
    simp only [eval] at ha hb ⊢
    rw [ha, hb]

/-- Decidable entailment: every enumerated valuation satisfying `φ` satisfies `ψ`. -/
def le (φ ψ : Cof) : Bool :=
  (allVals (φ.atoms ++ ψ.atoms)).all (fun v => !eval v φ || eval v ψ)

/-- **`Cof.le` is sound and complete** for the valuation semantics. This is the only
property of the decision procedure the phase layer uses. -/
theorem le_iff {φ ψ : Cof} : le φ ψ = true ↔ ∀ v : Nat → Bool, eval v φ = true → eval v ψ = true := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, hag⟩ := allVals_agree (φ.atoms ++ ψ.atoms) v
    have h1 : eval w φ = eval v φ :=
      eval_ext φ (fun a ha => hag a (List.mem_append_left _ ha))
    have h2 : eval w ψ = eval v ψ :=
      eval_ext ψ (fun a ha => hag a (List.mem_append_right _ ha))
    have hw' : (!eval w φ || eval w ψ) = true := List.all_eq_true.mp h w hw
    rw [h1, h2, hv] at hw'
    simpa using hw'
  · intro h
    apply List.all_eq_true.mpr
    intro w _hw
    by_cases hwφ : eval w φ = true
    · have := h w hwφ
      simp [hwφ, this]
    · simp [hwφ]

/-! ## The lattice laws -/

theorem le_refl (φ : Cof) : le φ φ = true :=
  le_iff.mpr fun _ h => h

theorem le_trans {φ ψ χ : Cof} (h1 : le φ ψ = true) (h2 : le ψ χ = true) : le φ χ = true :=
  le_iff.mpr fun v hv => le_iff.mp h2 v (le_iff.mp h1 v hv)

theorem le_top (φ : Cof) : le φ .top = true :=
  le_iff.mpr fun _ _ => rfl

theorem bot_le (φ : Cof) : le .bot φ = true :=
  le_iff.mpr fun _ h => by simp [eval] at h

theorem le_and_left (a b : Cof) : le (.and a b) a = true :=
  le_iff.mpr fun v h => by
    have h' : eval v a = true ∧ eval v b = true := by simpa [eval] using h
    exact h'.1

theorem le_and_right (a b : Cof) : le (.and a b) b = true :=
  le_iff.mpr fun v h => by
    have h' : eval v a = true ∧ eval v b = true := by simpa [eval] using h
    exact h'.2

theorem le_and_intro {φ a b : Cof} (ha : le φ a = true) (hb : le φ b = true) :
    le φ (.and a b) = true :=
  le_iff.mpr fun v hv => by
    have h1 := le_iff.mp ha v hv
    have h2 := le_iff.mp hb v hv
    simp [eval, h1, h2]

theorem le_or_left (a b : Cof) : le a (.or a b) = true :=
  le_iff.mpr fun v h => by simp [eval, h]

theorem le_or_right (a b : Cof) : le b (.or a b) = true :=
  le_iff.mpr fun v h => by simp [eval, h]

theorem le_or_elim {φ a b : Cof} (ha : le a φ = true) (hb : le b φ = true) :
    le (.or a b) φ = true :=
  le_iff.mpr fun v hv => by
    have h1 := le_iff.mp ha v
    have h2 := le_iff.mp hb v
    simp only [eval, Bool.or_eq_true] at hv
    rcases hv with hva | hvb
    · exact h1 hva
    · exact h2 hvb

theorem and_comm (a b : Cof) : le (.and a b) (.and b a) = true :=
  le_and_intro (le_and_right a b) (le_and_left a b)

theorem or_comm (a b : Cof) : le (.or a b) (.or b a) = true :=
  le_or_elim (le_or_right b a) (le_or_left b a)

theorem and_idem (a : Cof) : le (.and a a) a = true := le_and_left a a
theorem and_idem' (a : Cof) : le a (.and a a) = true :=
  le_and_intro (le_refl a) (le_refl a)
theorem or_idem (a : Cof) : le (.or a a) a = true :=
  le_or_elim (le_refl a) (le_refl a)
theorem or_idem' (a : Cof) : le a (.or a a) = true := le_or_left a a

/-- Distributivity, both directions. -/
theorem and_or_distrib (a b c : Cof) :
    le (.and a (.or b c)) (.or (.and a b) (.and a c)) = true :=
  le_iff.mpr fun v h => by
    simp only [eval, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    rcases h with ⟨ha, hb | hc⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hc⟩

theorem and_or_distrib' (a b c : Cof) :
    le (.or (.and a b) (.and a c)) (.and a (.or b c)) = true :=
  le_iff.mpr fun v h => by
    simp only [eval, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    rcases h with ⟨ha, hb⟩ | ⟨ha, hc⟩
    · exact ⟨ha, Or.inl hb⟩
    · exact ⟨ha, Or.inr hc⟩

theorem or_and_distrib (a b c : Cof) :
    le (.or a (.and b c)) (.and (.or a b) (.or a c)) = true :=
  le_iff.mpr fun v h => by
    simp only [eval, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    rcases h with ha | ⟨hb, hc⟩
    · exact ⟨Or.inl ha, Or.inl ha⟩
    · exact ⟨Or.inr hb, Or.inr hc⟩

theorem or_and_distrib' (a b c : Cof) :
    le (.and (.or a b) (.or a c)) (.or a (.and b c)) = true :=
  le_iff.mpr fun v h => by
    simp only [eval, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    rcases h with ⟨ha | hb, ha' | hc⟩
    · exact Or.inl ha
    · exact Or.inl ha
    · exact Or.inl ha'
    · exact Or.inr ⟨hb, hc⟩

/-- Absorption. -/
theorem and_absorb (a b : Cof) : le (.and a (.or a b)) a = true := le_and_left a _
theorem or_absorb (a b : Cof) : le a (.or a (.and a b)) = true := le_or_left a _

/-! ## Independence sanity cases -/

/-- Distinct atoms are independent: no atom entails another. -/
theorem atom_le_atom_iff (i j : Nat) : le (.atom i) (.atom j) = true ↔ i = j := by
  constructor
  · intro h
    by_cases hij : i = j
    · exact hij
    · exfalso
      have hsem := le_iff.mp h (fun k => decide (k = i)) (by simp [eval])
      simp only [eval] at hsem
      exact hij ((of_decide_eq_true hsem).symm)
  · intro h
    subst h
    exact le_refl _

/-- An atom does not entail `⊥`. -/
theorem atom_le_bot (i : Nat) : le (.atom i) .bot = false := by
  have h : ¬ (le (.atom i) .bot = true) := by
    intro h
    have := le_iff.mp h (fun _ => true) (by simp [eval])
    simp [eval] at this
  simpa using h

/-- A conjunction of two distinct atoms is not `⊥`, and does not entail a third atom. -/
theorem and_atom_le_atom (i j k : Nat) (hk : k ≠ i) (hk' : k ≠ j) :
    le (.and (.atom i) (.atom j)) (.atom k) = false := by
  have h : ¬ (le (.and (.atom i) (.atom j)) (.atom k) = true) := by
    intro h
    have hsem := le_iff.mp h (fun n => decide (n = i) || decide (n = j)) (by
      simp [eval])
    simp only [eval] at hsem
    have : decide (k = i) || decide (k = j) = true := hsem
    rcases (Bool.or_eq_true _ _).mp this with h1 | h2
    · exact hk (of_decide_eq_true h1)
    · exact hk' (of_decide_eq_true h2)
  simpa using h

/-- A disjunction of two distinct atoms is not a tautology: the all-false valuation
refutes it. This is where the calculus stops (there is no negation). -/
theorem or_atom_not_top (i j : Nat) : le .top (.or (.atom i) (.atom j)) = false := by
  have h : ¬ (le .top (.or (.atom i) (.atom j)) = true) := by
    intro h
    have := le_iff.mp h (fun _ => false) (by simp [eval])
    simp [eval] at this
  simpa using h

end Cof

end F1
end STC
