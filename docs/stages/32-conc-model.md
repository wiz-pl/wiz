# Stage 32: concurrency as a model

Stage 25 runs real threads. This stage runs none: `lib/Conc.wiz` describes a concurrent
program as a value of an effect type, and a pure, deterministic scheduler runs it one
step at a time. That makes concurrency something a test can enumerate and a proof can
talk about. The scheduler is the reference semantics the concurrency plan wants for
deadlock freedom and concurrent separation logic (plan stage D3, decision CP8); this
stage is the executable part, with a model checker on top. Tests: group `conc-model`.

## 32a: the `Conc` effect and a pure scheduler

A program `Conc V A` forks threads, yields, and talks through MVars that hold values of
type `V`; its result is an `A`. The operations are those of Haskell's `Control.Concurrent`:

| operation | meaning |
|---|---|
| `Conc.fork m` | start `m : Conc V Unit` as a new thread; its id |
| `Conc.yield` | let another thread run |
| `Conc.newMVar` | a new, empty MVar |
| `Conc.take m` | wait until `m` is full, empty it: its value |
| `Conc.put m v` | wait until `m` is empty, fill it with `v` |
| `Conc.read m`, `Conc.newMVarWith v` | `take` then `put` back; `newMVar` then `put` |

`Conc V A` is `Eff1 ω (Conc.Eff V :: []) (Conc.Thread V) A`: a computation of the
one-shot effects of stage 10, so it has `do` notation, and `Monad1.bind1` sequences a
continuation that holds a linear value.

A scheduler state has the threads, each stopped at its next operation, a round-robin
queue of their ids and the MVars. One step lists the threads that can move (a `take` on
a full MVar, a `put` on an empty one, anything else always), picks one, performs its
operation and puts it at the back of the queue. `Conc.run d fuel script main` picks by a
*script*: the `i`-th step takes the `script[i]`-th ready thread, counting in queue order
from `0`. When the script runs out, the choice is `0`, so `Conc.runRR` (the empty script)
is round-robin. A run ends when main returns (the other threads are killed, as in
Haskell), when no thread can move (a deadlock), or after `fuel` steps.

```wiz
import Conc

def worker (c : Conc.MVar) : Conc Nat Unit := do
  v ← Conc.take c;
  Conc.put c (Nat.succ v)

def counter : Conc Nat Nat := do
  c ← Conc.newMVarWith 0;
  d1 ← Conc.newMVar;
  d2 ← Conc.newMVar;
  Conc.fork (do worker c; Conc.put d1 0);
  Conc.fork (do worker c; Conc.put d2 0);
  Conc.take d1;
  Conc.take d2;
  Conc.take c

#eval Conc.Res.show Nat.repr (Conc.runRR 0 100 counter)
```

The result has the outcome, the MVars, the script that was followed and a trace, one
event per step (`1: take m0 = 0` is thread 1 taking `0` from MVar 0). A script replays
a run exactly: `Conc.run 0 100 r.script counter` is the run `r` again.

**One-shot continuations make the threads linear.** `Eff1`'s handlers get each
continuation at quantity 1, so a suspended thread (`Conc.Thr`) is a linear value. A
thread can keep a linear resource across a `yield`, and the scheduler can't run a thread
twice or lose one. Dropping a suspended thread is a quantity error:

```wiz no-check
-- rejected: k is declared with quantity 1 but not used
def dropK {V : Type} (1 k : Conc.Thread V) : Unit := ()
```

That leaves the threads that are still suspended when a run stops early. Each
continuation takes a `Conc.Wake`; a wake-up with `killed = true` runs the rest of the
thread at once, answering every operation with a default (`d`, the first argument of
`Conc.run`), and returns `Conc.Thr.stop`. `Conc.Thr V b` is indexed by whether it was
killed: a `Thr V true` can only be `stop`. `Conc.Thr.stopped` takes one apart with the
index generalised (`h : b = true`); in every other branch `h` is `false = true`, which is
`False`, and the branch casts its continuation to `Unit` along it. No recursion, so no
termination argument: programs are total, and killing one runs it to its end. The pool
of suspended threads is indexed by its size, because a linear value has no structural
recursion (the recursors bind their fields at ω); `Conc.Pool.killAll` and
`Conc.Pool.extract` recurse on the size, with the same generalised-index trick for the
impossible `cons` at size 0.

## 32b: stateless model checking

`Conc.check cfg main good` runs every interleaving of `main` and tests each run with
`good`. A program can't be copied mid-run (its threads are linear), so the checker
re-runs it from the start for each script. That is *stateless* model checking, as in
CHESS and Haskell's dejafu. Each run records how many threads were ready at each step;
the scripts that branch off it change one choice made by default after the script's
end. Starting from the empty script, every script is reached exactly once, depth first.
`Conc.Cfg.mk d fuel runs` bounds the steps of one run and the number of runs. The report
is either `ok n complete` (`complete` when the space was exhausted and no run hit the
step bound) or the first failing run, with its script and trace.

A lost update: each worker reads the counter and writes back one more, in two separate
steps. Round-robin happens to return 2 here (the second worker yields first, which keeps
the two apart), so a round-robin test passes. The checker finds the interleaving where
both read 0, on its fifth run:

```wiz
import Conc

def incr (c : Conc.MVar) : Conc Nat Unit := do
  v ← Conc.read c;
  Conc.take c;
  Conc.put c (Nat.succ v)

def pause : Nat → Conc Nat Unit
  | .zero => Conc.ret ()
  | .succ n => Conc.andThen Conc.yield (pause n)

def lostUpdate : Conc Nat Nat := do
  c ← Conc.newMVarWith 0;
  d1 ← Conc.newMVar;
  d2 ← Conc.newMVar;
  Conc.fork (do incr c; Conc.put d1 0);
  Conc.fork (do pause 4; incr c; Conc.put d2 0);
  Conc.take d1;
  Conc.take d2;
  Conc.take c

#eval Conc.Outcome.show Nat.repr (Conc.runRR 0 100 lostUpdate).outcome    -- "done 2"
#eval Conc.Report.show Nat.repr
  (Conc.check (Conc.Cfg.mk 0 100 1000) lostUpdate (Conc.returns (fun v => Nat.beq v 2)))
  -- "failed on run 5: done 1", then the script [0, 0, 0, 0, 0, 1, 1, 1, 1, 0, …] and the trace
```

A deadlock: two threads take two locks (MVars holding `0`) in opposite orders. Again
round-robin finishes, and `Conc.findDeadlock` finds the cycle on its 19th run: main holds
`m0` and waits for `m1`, thread 1 holds `m1` and waits for `m0`.

```wiz
import Conc

def pause : Nat → Conc Nat Unit
  | .zero => Conc.ret ()
  | .succ n => Conc.andThen Conc.yield (pause n)

def lockOrder : Conc Nat Nat := do
  a ← Conc.newMVarWith 0;
  b ← Conc.newMVarWith 0;
  d ← Conc.newMVar;
  Conc.fork (do pause 3; x ← Conc.take b; y ← Conc.take a; Conc.put a y; Conc.put b x; Conc.put d 0);
  x ← Conc.take a;
  y ← Conc.take b;
  Conc.put b y;
  Conc.put a x;
  Conc.take d

#eval Conc.Outcome.show Nat.repr (Conc.runRR 0 100 lockOrder).outcome     -- "done 0"
#eval Conc.Report.show Nat.repr (Conc.findDeadlock (Conc.Cfg.mk 0 100 1000) lockOrder)
  -- "failed on run 19: deadlock (blocked: 0, 1)", script [0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1]
```

The correct counter of 32a (each worker takes the counter and puts back one more, so
the MVar is the lock) passes both tests over all 39 of its interleavings:
`ok: 39 runs, every interleaving`.

The search has no partial-order reduction, so the number of runs grows exponentially
with the steps; it is meant for small programs (tens of steps), which is where
concurrency bugs are explained.

## 32c: proofs about round-robin

The policy is a pure function on the queue, `Conc.pick ready q c` (remove the `c`-th
ready thread, keep the others in order), and the scheduler calls it at every step. Two
properties are proved, by structural recursion and with no axiom:

* `Conc.pick_ready`: whatever the script, the picked thread is ready (the scheduler
  never runs a blocked thread).
* `Conc.pick_rr_progress`, **fairness**: if `u` is ready and in the queue `q`, a
  round-robin step picks some thread (so a ready thread rules out a false deadlock), and
  it is `u`, or `u`'s position in the next queue (`Conc.pos`, the number of threads
  ahead of it) is strictly smaller than in `q`, whatever is added at the back (the
  picked thread, a child it forked, or nothing when it finished). So while `u` stays
  ready it runs within `Conc.pos u q + 1` steps: no ready thread waits longer than the
  number of threads ahead of it.

```wiz
import Conc

def fair (q : List Nat) (h : 4 ∈ q) : Conc.RRStep 4 q (Conc.pick (fun t => Nat.beq t 4) q 0) :=
  Conc.pick_rr_progress (fun t => Nat.beq t 4) 4 rfl q h
```

The proofs case on `ready x` by generalising it (`Conc.pickCons` takes it as an
argument), so each case reduces without rewriting. "While `u` stays ready" is the usual
weak-fairness assumption. A thread blocked on an MVar that another thread keeps
refilling and emptying can still starve; that is a property of the program, and the
model checker is the tool for it.

What is not here yet: an IO handler that runs a `Conc` program on stage 25's threads
(the plan's `Conc.runIO`, with a differential test against the pure scheduler), and the
use of this scheduler as the semantics of a concurrent separation logic (plan S-b).
