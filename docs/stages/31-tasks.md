# Stage 31: tasks and structured scopes

Parallelism on the threads of stage 25, in two libraries: pure tasks (`lib/Task.wiz`),
whose results are deterministic, and structured scopes for `IO` (`lib/Scope.wiz`), in
which every task is joined before the scope ends. Plan stages T1 and T3 of
`concurrency-plan-2026-11-17.md` (decisions CP1–CP8); T2 (IO tasks with cancellation)
is not done yet. Tests: group `task`.

## 31a: pure tasks

```wiz
import Task

def sumTo : Nat → Nat
  | .zero => 0
  | .succ n => .succ n + sumTo n

def two : Nat × Nat := Task.both (fun _ => sumTo 100) (fun _ => sumTo 200)
def sums : List Nat := Task.parMap sumTo [10, 20, 30]
def fast : Nat := Task.race (fun _ => sumTo 100) (fun _ => 5050) rfl

#eval two    -- (5050, 20100)
#eval sums   -- .cons 55 (.cons 210 (.cons 465 .nil))
```

| | |
|---|---|
| `Task.spawn : (Unit → A) → Task A` | start computing `f ()` |
| `Task.get : Task A → A` | its value (wait for it) |
| `Task.both : (Unit → A) → (Unit → B) → A × B` | both values, the second on another thread |
| `Task.par : List (Unit → A) → List A` | every value, in parallel, in order |
| `Task.parMap : (A → B) → List A → List B` | `List.map`, one task per element |
| `Task.race : (f g : Unit → A) → (0 h : f () = g ()) → A` | whichever finishes first |

**The model is sequential** (decision CP6). `Task A` is a structure holding an `A`, with
a private constructor and field, so outside the module a task is made only by
`Task.spawn` and read only by `Task.get`. `Task.spawn f` is `f ()` in the box. The kernel,
every proof and the interpreters (`#eval`, `#run`) use these definitions, so a program
with tasks means what it means without them. The laws hold by `rfl` or structural
induction, with no axiom: `Task.get_spawn`, `Task.both_eq`, `Task.race_eq_left`/`_right`,
`Task.par_eq` (`par fs = List.map (fun f => f ()) fs`) and `Task.parMap_eq`
(`parMap = List.map`).

**`race` is deterministic.** Its erased argument `h : f () = g ()` says the two sides
agree, so the result doesn't depend on which one wins: two algorithms for one value, and
the faster one answers. The loser runs on to its end in the background, because a pure
computation can't be cancelled.

**Compiled code** runs four natives by `implemented_by` (stage 22b): `wiz_task_spawn`,
`wiz_task_get`, `wiz_task_both` and `wiz_task_race`, in `runtime/rt_con.inc`. They are
trusted. `#print axioms` lists `native Task.spawn := Task.spawnNative` and the others for
anything that uses them, and the `task` group compares the compiled output with the
model's.

* A task is waiting to start, running, or done. Whoever moves it from waiting to running
  runs it: its own thread, or the first `Task.get` that needs it before any thread has
  started it (**work-first**). So `get` never waits for work nobody is doing, and nested
  tasks (a task that spawns and waits for others) can't deadlock.
* **At most one task thread per online CPU** runs at a time. A task spawned beyond that
  gets no thread and runs at the `get` that needs it. A thread has the stack of other
  spawned threads (256 MB, `WIZ_THREAD_STACK_MB`).
* A task's function is marked shared before it crosses to its thread, and its value
  before it is published (the transfer rule of 25a). The task object is a foreign object
  whose record is shared by the object and the thread. The program waits for every task
  thread before its leak check, as it does for other threads.
* `both` runs `f ()` on the calling thread while `g ()` is a task. `par` builds every task
  before it waits for the first (the list of tasks is the data dependency, so the
  optimiser can't sink a spawn past a `get`). `both` and `race` are natives of their own
  for the same reason: the inliner substitutes a `let` used once, and that would move a
  `spawn` to its `get`.
* **Without threads** (`WIZ_NO_THREADS`, the Wasm pages' runtime, stage 25 R2) the first
  `Task.spawn`, `Task.both` or `Task.race` stops the program with exit code 3 and
  `wiz: Task.spawn: threads are not available in this build (WIZ_NO_THREADS)`, through
  the same `wiz_no_threads` as `Chan.fork`. It doesn't fall back to the model.

Not yet: a thread pool (each task with a thread gets a new one, up to the CPU limit), a
command-line flag for the thread count (CP7; today it is the CPU count) and the `-j1`
vs `-jN` differential that would need it, and the self-hosted backend's runtime
(`selfhost/rt.c` has no threads).

## 31b: structured scopes

```wiz
import Scope

def sum3 : IO Nat :=
  Scope.with (fun ρ s =>
    Scope.spawn s (IO.pure 1) (fun s ja =>
    Scope.spawn s (IO.pure 2) (fun s jb =>
    IO.bind (Scope.close s) (fun d =>
    IO.bind (Join.get ja) (fun a =>
    IO.bind (Join.get jb) (fun b => IO.pure (a + b, d)))))))

def sum3Model : sum3 = IO.pure 3 := rfl
```

```wiz no-check
Scope.with  : (1 body : (0 ρ : Region) → (1 s : Scope ρ) → IO (A × Done ρ)) → IO A
Scope.spawn : (1 s : Scope ρ) → IO A → (1 k : (1 s : Scope ρ) → (j : Join ρ A) → IO B) → IO B
Scope.close : (1 s : Scope ρ) → IO (Done ρ)
Join.get    : Join ρ A → IO A
Scope.both  : IO A → IO B → IO (A × B)
Scope.all   : List (IO A) → IO (List A)
```

`Scope.with` opens a scope, `Scope.spawn` starts an action in it, and `Scope.close`
waits for all of them. The API is in continuation-passing style, like the channels of
25c (decision CS3): `spawn` passes the scope on to its continuation with the new task's
handle. The types promise two things.

1. **Every task is joined.** The scope is used at quantity 1, which is exact: it can't
   be dropped or copied. The body must return a `Done ρ`, which only `Scope.close` makes
   (a private constructor). By the time `Scope.with` returns, every task spawned in the
   scope has finished. An action is an unrestricted value, so it can't capture the scope,
   and nothing is spawned into a scope from outside its body.
2. **No handle escapes.** The region `ρ` is the body's own variable, bound at quantity 0
   (the `runST` trick, as with the borrows of `lib/Region.wiz`). A handle `Join ρ A`
   mentions it, and `Scope.with`'s result type is chosen outside, so a handle can't be the
   result: "a variable escapes the scope of the hole being solved". (A function that calls
   `Join.get` can still leave through an `MVar`. After the scope it reads a value that is
   already there.)

The rejections are tested (group `task`): returning a handle, dropping the scope, closing
it twice, capturing it in a task's action, returning another scope's `Done`, and building
a `Scope`, a `Done` or a task by hand.

**Model and compiled code.** The model runs each action at once, in spawn order, so the
kernel computes a scoped program (`sum3Model` above is `rfl`). Compiled code runs
`Scope.spawnThreads` by `implemented_by`: each action runs on a new thread (started by
`Chan.fork` on a protocol that is `done` at once), its result goes into an `MVar`, the
scope keeps a wait for it, and `close` runs the waits. The two differ only in when the
actions' effects happen. Actions that print or share state need an `MVar` or a `Lock` to
order them; the scope guarantees only the join. Without threads, the first `spawn` stops
at `Chan.fork`'s message.

Not yet (T2): cancellation (a scope that cancels its other tasks when one fails, and
`race` for `IO`), and errors (`IO` has no exceptions to propagate yet). Programs that use
scopes are outside the deadlock-freedom claim of 25c: a task may wait on an `MVar`.
