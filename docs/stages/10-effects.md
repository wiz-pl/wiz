# Stage 10: effects

## 10a: effects as a library, commutation as proofs

```
import Eff
def prog : Eff (Row.cons (State Nat) (Row.cons (Exn String) (Row.cons Console Row.nil))) Nat := do
  n ← get;
  println "starting";
  put (n + 1);
  Monad.pure n
def main : IO Unit := do
  r ← runConsole (runExn (runState prog 4))
  …
```

* `lib/Eff.wiz`: an `Effect` is a type of operations with an answer type for each, a
  `Row` lists effects, and `Eff r A` is a free monad over the row's operations (its
  continuations are infinitary fields). `Member e r` (two instances, found by
  resolution) injects an effect's operations into a row; `send` performs one.
* Handlers peel the first effect off a row: `runState`, `runReader`, `runExn`, and
  `runConsole` into `IO` at the bottom.
* **Lowering to a monad**: a `Handler e m` for every effect of a row gives
  `interpret : Eff r A → m A`. **Commutation is a proof obligation**:
  `Commute e₁ e₂ m` asks for a proof (kernel-checked, with the OTT equality) that
  swapping two operations doesn't change the result in `m`; `reorder` needs it. Two
  readers commute (the proof is `rfl`); the kernel rejects the same claim for state.
* This needed more of the elaborator: dependent matching now carries induction
  hypotheses through nested patterns; unification got lazy delta (unfold the later
  definition one step), first-order approximation against variables, projections of
  holes, and non-linear spines; description fields may live in smaller universes;
  `Type` takes a universe argument only right of the enclosing position; types get
  their trailing instance arguments.

## 10b: fusion

Effectful code can be written against classes (`MonadState S m`, `MonadReader E m`,
`MonadConsole m`) and run two ways: as a tree of operations (`Eff r`, whose instances
`send` operations to handlers, so resumptions are general), or **fused**, directly in
a monad (`StateT S IO`, `ReaderT E IO`, `IO`), where every operation is a plain call
and no tree is built. In a 200,000-step state loop the fused version is about 4.5×
faster.

```
def prog {m : Type → Type} [Monad m] [MonadState Nat m] [MonadConsole m] : m Nat := …
runConsole (runState (prog : Eff (Row.cons (State Nat) (Row.cons Console Row.nil)) Nat) 0)   -- tree
(prog : StateT Nat IO Nat) 0                                                                 -- fused
```

## 10c: one-shot effects

```
structure Coin where
  value : Nat
def prog {R : Type} (1 c : Coin) : Eff1 1 (Row.cons (State Nat) Row.nil) R Coin :=
  Eff1.bind (do1 n ← get1; put1 (n + 1)) (fun u => Eff1.pure c)
def spent : Nat := Coin.spend (Eff1.run1 (evalState1 (prog (Coin.mk 5)) 10))
```

* `Eff`'s continuations are ω fields, so a computation can't keep a linear resource (a
  channel endpoint, a token) in one (plan CS4–6). `Eff1 q r R A` is the same
  computations over the same rows, effects and `Member`, Church-encoded over an answer
  type `R`: `(1 ret : (%q a : A) → R) → (h : (o : Union r) → (1 k : RetU r o → R) → R) → R`.
  The handler gets each continuation **at quantity 1**: it resumes exactly once
  (one-shot, as in OCaml 5), and in exchange a continuation may capture linear values.
  The result is used `q` times: `ω` for ordinary results, `1` for a computation that
  hands back a linear value. `Eff1.bind` goes from any `q` to any `p`.
* `send1`, `get1`, `put1`, `println1`; `Eff1.handle` (a one-shot handler of the first
  effect), `runState1`, `evalState1` (any result quantity), `runConsole1` into `IO`
  (whose bind takes its continuation at 1, 9e), `Eff1.run`, `Eff1.run1`. `Monad` and
  `Monad1` instances at `q = ω`, so `do`/`do1` work. `Eff.toEff1` runs every multi-shot
  program under one-shot handlers.
* A handler that resumes twice (backtracking) or never (an exception) is rejected by
  the kernel ("`k` declared with quantity 1 but used ω / 0"); those need `Eff`. With
  linear resources, an aborting effect needs an explicit cancel path (plan gap 8).
* Church-encoded, not a tree: a linear field can't be matched back out of data yet
  (plan L2). Answers of operations stay unrestricted, and an operation can't carry a
  linear value (its payload is ω data).
