import STC.F0.Obligations
/-!
# Prototype: a fuel-indexed, non-`mutual` kernel core

`selfhost/Kernel.wiz` writes `eval`, `quote`, `conv` and `infer` as `mutual` blocks
(`Kernel.wiz:1047`, `:2581`, `:2972`), which the self-hosted kernel records as opaque
axioms (`docs/stages/17-selfhost-elaboration.md` §17d, `docs/trust-ledger.md`
"`partial` and `mutual`"). The extracted kernel cannot be an axiom.

This file is the smallest witness that the standard fix — **one function, fuel as its
first argument, the three "passes" as constructors of a command type** — is a total
Lean definition with no axioms at all. The same shape is accepted by the self-hosted
kernel (`STC/Prototype/Totality.wiz`, checked with `wiz check`).

The point is not the evaluator (it is a three-constructor toy); it is that

* every recursive call is `run n …` with `n` the predecessor of the current fuel, so the
  recursion is structural on `Nat`, not on the term: no well-founded relation, no
  `partial`, no `mutual`;
* the dispatcher is total by construction (`run_total`), and `#print axioms run` is
  empty; and
* `run` **is** the M2 NbE program: `eval`, `quote`, `conv` (and `infer`) are the cases of
  `Cmd`, so proving them equal to M1's checker at a common fuel is a statement about one
  function, not a simulation between separately terminating definitions.

Two Lean-specific details, both avoidable in Wiz and recorded so a port does not acquire
them by accident:

* a multi-scrutinee `match run n f, run n a with` makes the compiler produce a proof
  depending on `propext`; the nested matches below keep `run` axiom-free;
* a wildcard `_` in a `match` on the *mutual* `Val`/`Env` block also introduces `propext`
  (the equation compiler's inaccessible pattern). Every constructor is written out.
-/

namespace STC
namespace Prototype

/-- The toy syntax: variables, one universe, λ and application. Enough for the shape. -/
inductive Tm where
  | var (i : Nat)
  | sort (n : Nat)
  | lam (b : Tm)
  | app (f a : Tm)

mutual
  /-- Values: closures hold environments, so `Val` and `Env` are one mutual block (types
  may be mutual; the *functions* below are not). -/
  inductive Val where
    | sort (n : Nat)
    | clos (env : Env) (b : Tm)
    | neu (i : Nat) (args : List Val)
  inductive Env where
    | nil
    | cons (v : Val) (e : Env)
end

/-- The passes of a kernel are cases of one command type: this is what replaces the
`mutual` block. `infer`/`check` would be two more constructors. -/
inductive Cmd where
  | eval (env : Env) (t : Tm)
  | quote (l : Nat) (v : Val)
  | conv (l : Nat) (a b : Val)

/-- Results carry no fuel: running out of fuel is a verdict (`fuel`), not a term. This is
the `Except Err`/`M Bool` shape of `Spec/Obligations.lean`'s `Checker`. -/
inductive Res where
  | val (v : Val)
  | tm (t : Tm)
  | bool (b : Bool)
  | fuel

def tmEq : Tm → Tm → Bool
  | .var i, .var j => i == j
  | .sort m, .sort n => m == n
  | .lam b, .lam b' => tmEq b b'
  | .app f a, .app f' a' => tmEq f f' && tmEq a a'
  | .var _, .sort _ => false
  | .var _, .lam _ => false
  | .var _, .app _ _ => false
  | .sort _, .var _ => false
  | .sort _, .lam _ => false
  | .sort _, .app _ _ => false
  | .lam _, .var _ => false
  | .lam _, .sort _ => false
  | .lam _, .app _ _ => false
  | .app _ _, .var _ => false
  | .app _ _, .sort _ => false
  | .app _ _, .lam _ => false

def lookup : Env → Nat → Option Val
  | .nil, _ => none
  | .cons v _, 0 => some v
  | .cons _ e, n + 1 => lookup e n

/-- A closure's environment and body, if the value is one. Written as a separate function
because a nested constructor pattern such as `.val (.clos cenv b)` in `run`'s `match`
would make Lean's equation compiler add a `propext` dependency. -/
def asClos : Val → Option (Env × Tm)
  | .clos e b => some (e, b)
  | .sort _ => none
  | .neu _ _ => none

/-- The single total dispatcher. Every call is on `n`, never on `n + 1`; the term is only
destructed, never recursed into by the termination checker's measure. -/
def run : Nat → Cmd → Res
  | 0, .eval _ _ => .fuel
  | 0, .quote _ _ => .fuel
  | 0, .conv _ _ _ => .fuel
  | n + 1, .eval env t => match t with
    | .var i => match lookup env i with
      | some v => .val v
      | none => .val (.neu i [])
    | .sort k => .val (.sort k)
    | .lam b => .val (.clos env b)
    | .app f a => match run n (.eval env f) with
      | .val vf => match asClos vf with
        | some (cenv, b) => match run n (.eval env a) with
          | .val av => run n (.eval (.cons av cenv) b)
          | .tm _ => .fuel
          | .bool _ => .fuel
          | .fuel => .fuel
        | none => match run n (.eval env a) with
          | .val av => .val (.neu 0 [vf, av])
          | .tm _ => .fuel
          | .bool _ => .fuel
          | .fuel => .fuel
      | .tm _ => .fuel
      | .bool _ => .fuel
      | .fuel => .fuel
  | n + 1, .quote l v => match v with
    | .sort k => .tm (.sort k)
    | .neu i _ => .tm (.var i)
    | .clos env b => match run n (.eval (.cons (.neu l []) env) b) with
      | .val v' => run n (.quote (l + 1) v')
      | .tm _ => .fuel
      | .bool _ => .fuel
      | .fuel => .fuel
  | n + 1, .conv l a b => match run n (.quote l a) with
    | .tm ta => match run n (.quote l b) with
      | .tm tb => .bool (tmEq ta tb)
      | .val _ => .fuel
      | .bool _ => .fuel
      | .fuel => .fuel
    | .val _ => .fuel
    | .bool _ => .fuel
    | .fuel => .fuel

/-- `run` is total: for every fuel and command there is a result. This is trivial — that
is the point of fuel: the function cannot fail to return. -/
theorem run_total (n : Nat) (c : Cmd) : ∃ r, run n c = r := ⟨_, rfl⟩

/-- The dispatcher computes: with enough fuel, `(λx. x) y` evaluates to the value of the
body under the extended environment. -/
example : run 4 (.eval .nil (.app (.lam (.var 0)) (.sort 0)))
    = .val (.sort 0) := rfl

/-- The command type is not an obstacle to the proof: `eval` at a closure is the body
under the captured environment. -/
example : run 2 (.eval .nil (.lam (.sort 0))) = .val (.clos .nil (.sort 0)) := rfl

-- The axiom audit that matters: the extracted program has no axioms. (In particular it
-- does not depend on `propext`.)
#print axioms run

end Prototype
end STC
