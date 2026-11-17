# Stage 25: concurrency

Real threads in compiled code, and two peer APIs on top of them (decision CS1):
session-typed linear channels (`lib/Session.wiz`), whose deadlock freedom is argued but
not mechanised for the IO API (25c), and MVars and locks (`lib/MVar.wiz`), which are more
flexible and give weaker guarantees.
Plan and survey: `concurrency-seplogic-plan.md` (stages C0, C2–C3, C8 there); runtime
design: `concurrency.md`. Tests: group `conc`.

## 25a: a thread-safe runtime

`runtime/` (C and LLVM backends) can run Wiz code on several threads at once. Wiz has
no user-visible mutation, so only the runtime's own state needs care: reference counts,
in-place updates of unique objects, memoised thunks and lazy cells, hoisted constants,
and a few globals. The scheme is Lean 4's:

| count | meaning | changed by |
|---|---|---|
| `rc > 0` | owned by one thread | plain arithmetic |
| `rc < 0` | shared between threads; the count is `-rc` | atomic add/sub |
| `rc == 0` | immortal (a hoisted constant) | nothing |

**The transfer rule.** A value crosses to another thread only through the runtime: a
forked thread's closure (`Chan.fork`), a message (`Chan.send`), an MVar's contents
(`MVar.put`). Before it does, `wiz_mark_mt` walks everything reachable from it and
negates the counts (it stops at objects already shared or immortal). So a shared object
points only to shared or immortal objects, and single-threaded code pays only for a sign
test per `inc`/`dec`. The rest follows from that invariant:

* **In-place updates** (Perceus reuse, `Bytes`/`Array`/`StrMap` updates, drop
  specialisation) need `rc == 1`, which a shared object never has: it is copied instead.
* **Thunks.** A shared `memo` thunk is forced under one recursive lock, and its value is
  marked shared before other threads can see it. Pure code never blocks, so the lock can't
  deadlock (it only serialises forcing shared thunks). A shared **lazy cell** (codata) is
  not overwritten with its payload: other observers recompute the same value.
* **Hoisted constants** are built, made immortal, and published with a compare-and-swap;
  a thread that loses the race uses the winner's (its own copy stays unused).
* **Globals.** The live-object count is per thread (each thread adds its balance when it
  ends); the program waits for every thread before its leak check, so leak checking works
  as before. The leak-tracking table (`WIZ_LEAKS`) has a mutex; static result buffers are
  per thread.

A spawned thread has a 256 MB stack (`WIZ_THREAD_STACK_MB`). The interpreters (`#eval`,
`#run`) don't run threads. Checked with ThreadSanitizer (`--cflags -fsanitize=thread`) on
the `conc` programs; the cost for single-threaded programs is queued for measurement
(`perf-queue.md`). Not yet: `selfhost/rt.c` (the self-hosted backend's runtime, under
Boehm it needs `GC_THREADS`), shared lazy cells that keep their payload (a CAS to a
blackhole), and `rc == -1` counting as unique.

An `extern` bound to a runtime native (a C name starting `wiz_`) now takes and returns any
Wiz value as it is (an opaque type's, a closure, a Σ pair), so the natives below are
typed precisely in Wiz.

## 25b: session types

```wiz no-check
import Session
def sumProto : Proto := .send Nat (fun n => sendMany ack n)   -- n, then n numbers, then the sum back
```

`Proto` is a protocol from one end's point of view: `.send A k` (send an `A`, continue with
`k a`), `.recv A k`, `.done`. The continuation is a **function of the value**, so protocols
are dependent (Toninho, Caires & Pfenning 2011): how many numbers follow depends on the
length just sent. `Proto.dual` swaps sends and receives. Choice is a dependent protocol
too (`Proto.choose p q := .send Bool …`).

The pure semantics: `Proc R p` is a process following `p` with result `R` (sending is a Σ,
receiving a Π), and `link p a b : A × B` runs a process against one following the dual.
`link` is total, by structural recursion on `p` (cut elimination as a program: one
channel can't get stuck). `#eval (link sumProto (client 100) server).1` gives `5050`.

## 25c: linear channels, and the deadlock-freedom argument

`Chan p` is one end of a channel whose remaining protocol is `p`, an opaque type (an
axiom: no constructor, nothing makes one at ω). The API is in continuation-passing style
(decision CS3): each operation passes the endpoint, at its next step, to a linear
continuation.

```
Chan.fork  : (p : Proto) → (1 child : (1 c : Chan (Proto.dual p)) → IO Unit) → (1 parent : (1 c : Chan p) → IO B) → IO B
Chan.send  : (1 c : Chan (.send A k)) → (a : A) → (1 next : (1 c' : Chan (k a)) → IO B) → IO B
Chan.recv  : (1 c : Chan (.recv A k)) → (1 next : (a : A) → (1 c' : Chan (k a)) → IO B) → IO B
Chan.close : (1 c : Chan .done) → (1 next : IO B) → IO B
Chan.cancel : (1 c : Chan (Proto.sendC A k)) → (1 next : IO B) → IO B
```

Quantity 1 is exact in Wiz (no weakening), so an endpoint is used **exactly once**: it
can't be copied (two threads on one end), dropped (a peer waiting for ever), closed twice,
or kept after its protocol moved on; a closure that captured one is linear itself. The
types check every step: the wrong message type or closing early is a type error.
`fork` creates a channel and runs `child` on a new thread with the dual end; since both
functions are linear they may capture other endpoints, which is how an endpoint moves to
another thread. Natives (`wiz_chan_*`, 25a): two queues per channel; `send` never blocks,
`recv` waits; a channel is freed when both ends are closed.

**Cancellation** (decision CS13) is part of the protocol: `Proto.sendC A k` sends a
`Msg A`, either `.val a` (continue with `k a`) or `.cancel` (the channel is done), and
`Chan.cancel` sends `.cancel` and closes. A process can't abandon a channel on an error
path (it can't drop the endpoint), so a protocol that may fail says where.

**The deadlock-freedom claim** (decision CS2). A program whose threads communicate only
through this API — no `MVar` or `Lock` (25d), no other blocking primitive (reading a
pipe another thread writes), no `partial` definition and no other non-terminating
code — should not deadlock: every thread finishes or makes progress. That is a claim
about the API, argued below; it is not a theorem about the API in this repository. The
argument is the one for Wadler's GV (Wadler 2012; Lindley & Morris 2015; as a
separation-logic proof, Jacobs, Balzer & Krebbers 2022, and LinearActris, POPL 2024):

1. **The channel graph is a forest.** Threads are nodes, channels edges. `fork` adds a new
   node joined by one new edge to its parent; endpoints the child captured move with it,
   which re-attaches edges from the parent to the child and keeps a forest. Nothing else
   creates or moves endpoints: an endpoint isn't a message (`send` takes the message at
   ω, so a linear endpoint can't be sent) and can't be stored in an MVar or any data
   (fields are ω). So the topology is a **tree topology** (each channel connects exactly
   two threads, and there are no cycles).
2. **Endpoints are linear**: nobody waits on a channel whose other end was dropped, and
   both ends follow dual protocols, so when one end receives the other eventually sends.
3. **Every process is total.** In a forest, some thread that is blocked waits on a peer
   that is not blocked on it; following those edges ends at a thread that can step.

This is a meta-theorem about the API, argued from the literature; it is not proved in
Wiz, and **no theorem in this repository states it**. It does not cover programs that use
MVars, locks or `partial`, it says nothing about the runtime's own correctness (the
natives are trusted, `#print axioms` lists them), and it is about deadlock, not fairness
or timing. For one channel, `link` is total by structural recursion (its own theorem, not
a deadlock theorem).

**What is mechanised, and what it assumes.** `lib/SessionDeadlock.wiz` (stage 35) proves
the following for the **finite fragment** of a **pure, synchronous** model of threads and
channels — not for the IO API above:

* `Deadlock.progress (C) : Typed C → Closed C → Acyclic C → Final C ∨ HasStep C` — a
  typed, closed, acyclic configuration is final or can step.
* `Deadlock.stepAcyclic : Step C D → Acyclic C → Acyclic D` — every step keeps
  acyclicity.
* `Deadlock.reachableProgress (n) (t) (r : Steps (init n t) D) : Typed D → Closed D →
  Final D ∨ HasStep D` — along a run from `init`, a configuration that is typed and
  closed is final or steps.
* `Deadlock.linkProgress` — the two-`Proc` configuration of `link p a b` is typed, closed
  and acyclic, so it is final or steps. Only this connection uses an axiom (`castRefl`).

The hypotheses are part of the statement, and the gaps are not hidden in it:

* preservation of `Typed` and `Closed` under steps is **not** proved, so
  `reachableProgress` carries them as hypotheses; the only concrete instance in the
  module is the two-thread `linkCfg`;
* `Acyclic` is a ranking definition, and its equivalence to "the channel graph is a
  forest" is argued, not proved;
* the model is synchronous, while `runtime/` channels buffer sends;
* adequacy to `Chan.forkD`/`sendD`/`recvD`/`closeD` (or to the `Conc` scheduler, stage 32)
  is **not** proved;
* recursive protocols, delegation, MVars, locks and `partial` are outside it, as are
  fairness, timing and the runtime's own correctness.

So no Wiz program is proved deadlock-free by stage 35. The library is not on master at
the time of writing: it was developed on the unmerged stage-35 branch, and
`Tests/Groups/VerifDeadlock.lean` there pins each statement above (a type ascription, not
just an empty `#print axioms`).

**Pure model vs threads.** `Proc.run p proc c` runs a pure process over a real endpoint,
and `Proc.runLinked p a b : IO (A × B)` is `IO.pure (link p a b)` for the kernel, `#eval`
and `#run`, but `implemented_by` threads in compiled code (the peer in a new thread, its
result back through an MVar). A compiled program printing it is a differential test of the
natives against the pure semantics (`conc` group). A model of the whole `Chan` API (a
deterministic scheduler) needs one-shot linear continuations (plan C5, `LEff`).

**Sequencing and current workarounds.** Linear steps sequence with `do1` or `IO.bind`
(both take the action and the continuation at quantity 1, [9e](09-ffi.md)); plain `do`
uses `Monad.bind`, whose continuation is ω, so it can't capture an endpoint. The
protocol's continuation `k` is inferred from the endpoint's type, also through a defined
protocol (`Chan.send c a next` with `c : Chan (Proto.dual Q)`): `Proto`'s field
`k : A → Proto` is stored lifted, as `fun h => k (down h)`, and the unifier takes
`?k (down h)` as a pattern (plan gap 7). `match` uses its branches at ω, so pass endpoints
into a branch as arguments (`| .val x => fun c => …`) instead of capturing them. `Proto.dual`
is an involution only propositionally; `Eq.cast` at quantity 1 (9e) can move an endpoint
along a proof. Direct style (`send : (1 c) → A → IO (Chan (k a))`) waits for linear Σ
fields (plan L3).

## 25d: MVars and locks

```
import MVar
MVar.new : IO (MVar A)        MVar.take : MVar A → IO A        MVar.put : MVar A → A → IO Unit
MVar.borrow : (m : MVar A) → (1 k : (a : A) → (1 h : MVar.Hole m) → IO B) → IO B
MVar.fill : (m : MVar A) → (1 h : MVar.Hole m) → A → (1 next : IO B) → IO B
Lock.acquire : (l : Lock) → (1 k : (1 g : Lock.Guard l) → IO B) → IO B
Lock.release : (l : Lock) → (1 g : Lock.Guard l) → (1 next : IO B) → IO B
```

A peer API for what channels don't fit: many threads sharing a cell, a lock around
output. MVars and locks are ordinary (ω) values, shared freely.

| API | guarantees | not guaranteed |
|---|---|---|
| `Chan` (25c) | protocol fidelity, every endpoint closed exactly once, no data races, **deadlock freedom argued, not mechanised** (tree topologies, total code, no MVars/locks) | fairness |
| `MVar.take`/`put` | no data races (values are immutable and marked shared) | deadlock freedom; that a taken value is put back |
| `MVar.borrow`/`fill` | the borrower refills the cell exactly once on every path (`Hole m` is linear and unforgeable) | deadlock freedom (another thread may `put` meanwhile, or wait on a cell this one holds) |
| `Lock` | every acquisition released exactly once, from any thread (`Guard l` is linear and unforgeable; a lock is a binary semaphore, not a pthread mutex) | deadlock freedom (lock order is up to the program) |

`MVar.modify m f` (borrow, then fill with `f a`) updates a cell atomically with respect to
other borrowers. Deadlock-free locks (lock levels, or Jacobs & Balzer's POPL 2023 linear
locks) are future work (plan C8).

## 25e: what's next

Pure parallelism (`Task.spawn`, plan C1) on the same runtime, with a `-j1` vs `-jN`
differential test; structured scopes (C4); a concurrency effect with a pure scheduler
(C5, needs one-shot continuations); recursive protocols over ν with sizes; delegation
(sending endpoints) with protocol-level linear payloads; the remaining steps of the
mechanised proof (preservation of `Typed`/`Closed` and adequacy to the IO API: stage 35,
C7); `selfhost/rt.c` threads.
