import STC.F0.Sort
/-!
# F0 terms

The F0 syntax of `/workspace/wiz-notes/stc-m0-spec.md` §2: the rules of T0 plus `ULift`,
with closed three sorts, and nothing of T1/T2.

Departures from `WizMeta/Syntax.lean`, all deliberate:

* no quantities: binders are plain (all `ω`), so `pi`/`sigma` carry only their sort;
* no level parameters on constants: globals are closed;
* no `Qty`, `Desc`, `μ`, `ν`, sizes, `scase`, `split`, numerals or natives;
* `letUnit u b` is added (the kernel's `Term.letUnit`, emitted by the elaborator);
* `Π`/`Σ` sorts are mandatory (no `Option`);
* de Bruijn indices; a binder's body lives under one more variable.
-/


namespace STC
namespace F0

inductive Tm where
  | var (i : Nat)
  /-- a closed global constant; no level arguments (E2 is later) -/
  | const (c : String)
  | sort (s : Srt)
  /-- `(x : A) → B` in `Sort s` (`s = imax i j`) -/
  | pi (s : Srt) (A B : Tm)
  | lam (b : Tm)
  | app (f a : Tm)
  /-- `let x : A := v; b` -/
  | letE (A v b : Tm)
  /-- `let () := u; b`: a unit binder that is erased (the kernel's `Term.letUnit`) -/
  | letUnit (u b : Tm)
  | ann (t A : Tm)
  /-- `(x : A) × B` in `Sort s` (`s = max i j`) -/
  | sigma (s : Srt) (A B : Tm)
  | pair (a b : Tm)
  | fst (p : Tm)
  | snd (p : Tm)
  | unit (s : Srt)
  | tt
  | empty (s : Srt)
  /-- `absurd M t`: eliminate a proof of `Empty`, into the type `M` -/
  | absurd (M t : Tm)
  /-- an enumeration of `n` tags (labels are metadata in Wiz and absent here) -/
  | enum (n : Nat)
  | tag (n i : Nat)
  /-- `ecase M s bs`: `s` is the scrutinee, `M` the motive under one binder, `bs` a
  `bnil`/`bcons` list (as in `Kernel.wiz`, so that `Tm` is a plain inductive type) -/
  | ecase (M s bs : Tm)
  | bnil
  | bcons (b bs : Tm)
  | eq (A a b : Tm)
  | eqTy (A B : Tm)
  | refl (A a : Tm)
  | reflTy (A : Tm)
  | cast (A B e t : Tm)
  | transp (A a P p b e : Tm)
  | ulift (s : Srt) (A : Tm)
  | up (a : Tm)
  | down (t : Tm)
  deriving Repr, Inhabited, BEq

namespace Tm

def branches : List Tm → Tm
  | [] => bnil
  | b :: bs => bcons b (branches bs)

/-- The `k`-th branch of a branch list. -/
def branch? : Tm → Nat → Option Tm
  | bcons b _, 0 => some b
  | bcons _ bs, k + 1 => branch? bs k
  | _, _ => none

/-- The branches as a list, if the term is a well-formed branch list. -/
def branchList? : Tm → Option (List Tm)
  | bnil => some []
  | bcons b bs => (branchList? bs).map (b :: ·)
  | _ => none

/-! ## Renaming and substitution -/

def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def ren (ρ : Nat → Nat) : Tm → Tm
  | var i => var (ρ i)
  | const c => const c
  | sort s => sort s
  | pi s A B => pi s (ren ρ A) (ren (upRen ρ) B)
  | lam b => lam (ren (upRen ρ) b)
  | app f a => app (ren ρ f) (ren ρ a)
  | letE A v b => letE (ren ρ A) (ren ρ v) (ren (upRen ρ) b)
  | letUnit u b => letUnit (ren ρ u) (ren ρ b)
  | ann t A => ann (ren ρ t) (ren ρ A)
  | sigma s A B => sigma s (ren ρ A) (ren (upRen ρ) B)
  | pair a b => pair (ren ρ a) (ren ρ b)
  | fst p => fst (ren ρ p)
  | snd p => snd (ren ρ p)
  | unit s => unit s
  | tt => tt
  | empty s => empty s
  | absurd M t => absurd (ren ρ M) (ren ρ t)
  | enum n => enum n
  | tag n i => tag n i
  | ecase M s bs => ecase (ren (upRen ρ) M) (ren ρ s) (ren ρ bs)
  | bnil => bnil
  | bcons b bs => bcons (ren ρ b) (ren ρ bs)
  | eq A a b => eq (ren ρ A) (ren ρ a) (ren ρ b)
  | eqTy A B => eqTy (ren ρ A) (ren ρ B)
  | refl A a => refl (ren ρ A) (ren ρ a)
  | reflTy A => reflTy (ren ρ A)
  | cast A B e t => cast (ren ρ A) (ren ρ B) (ren ρ e) (ren ρ t)
  | transp A a P p b e => transp (ren ρ A) (ren ρ a) (ren ρ P) (ren ρ p) (ren ρ b) (ren ρ e)
  | ulift s A => ulift s (ren ρ A)
  | up a => up (ren ρ a)
  | down t => down (ren ρ t)

/-- Weakening by one variable. -/
def shift (t : Tm) : Tm := ren (· + 1) t
/-- Weakening by `n` variables. -/
def shiftN (n : Nat) (t : Tm) : Tm := ren (· + n) t

def upSub (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | n + 1 => shift (σ n)

def sub (σ : Nat → Tm) : Tm → Tm
  | var i => σ i
  | const c => const c
  | sort s => sort s
  | pi s A B => pi s (sub σ A) (sub (upSub σ) B)
  | lam b => lam (sub (upSub σ) b)
  | app f a => app (sub σ f) (sub σ a)
  | letE A v b => letE (sub σ A) (sub σ v) (sub (upSub σ) b)
  | letUnit u b => letUnit (sub σ u) (sub σ b)
  | ann t A => ann (sub σ t) (sub σ A)
  | sigma s A B => sigma s (sub σ A) (sub (upSub σ) B)
  | pair a b => pair (sub σ a) (sub σ b)
  | fst p => fst (sub σ p)
  | snd p => snd (sub σ p)
  | unit s => unit s
  | tt => tt
  | empty s => empty s
  | absurd M t => absurd (sub σ M) (sub σ t)
  | enum n => enum n
  | tag n i => tag n i
  | ecase M s bs => ecase (sub (upSub σ) M) (sub σ s) (sub σ bs)
  | bnil => bnil
  | bcons b bs => bcons (sub σ b) (sub σ bs)
  | eq A a b => eq (sub σ A) (sub σ a) (sub σ b)
  | eqTy A B => eqTy (sub σ A) (sub σ B)
  | refl A a => refl (sub σ A) (sub σ a)
  | reflTy A => reflTy (sub σ A)
  | cast A B e t => cast (sub σ A) (sub σ B) (sub σ e) (sub σ t)
  | transp A a P p b e => transp (sub σ A) (sub σ a) (sub σ P) (sub σ p) (sub σ b) (sub σ e)
  | ulift s A => ulift s (sub σ A)
  | up a => up (sub σ a)
  | down t => down (sub σ t)

/-- The substitution `[a/0]`. -/
def one (a : Tm) : Nat → Tm
  | 0 => a
  | n + 1 => var n

/-- `b[a/x]` for the innermost variable of `b`. -/
def inst (b a : Tm) : Tm := sub (one a) b

end Tm

/-- A context: the types of the variables, innermost first. The type at position `i` lives
in the context of the entries after it, so the type of `var i` is `Γ[i]` weakened by
`i + 1`. -/
abbrev Ctx := List Tm

def Ctx.lookup (Γ : Ctx) (i : Nat) : Option Tm := (Γ[i]?).map (Tm.shiftN (i + 1))

/-- A global declaration: a closed type and a value (`none` for an axiom). There are no
level parameters (unlike `WizMeta.Decl`): globals are closed in F0. -/
structure Decl where
  name : String
  type : Tm
  value : Option Tm
  deriving Repr, Inhabited

/-- A signature, most recent declaration first. -/
abbrev Sig := List Decl

def Sig.find? (sg : Sig) (c : String) : Option Decl := List.find? (·.name == c) sg

namespace Spec

/-- Every declaration is closed: substituting any terms leaves its type (and value) alone.
Needed by the renaming lemma and by the two structural conversion rules (`Spec/Struct.lean`);
not implied by `SigWF` without "typed in the empty context implies closed", which is not
proved. -/
def Sig.Closed (sg : Sig) : Prop :=
  ∀ d, d ∈ sg → ∀ σ : Nat → Tm, d.type.sub σ = d.type ∧
    ∀ v, d.value = some v → v.sub σ = v

end Spec

end F0
end STC
