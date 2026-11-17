# Stage 35: deadlock freedom for a synchronous model

Stage 25c claims that a program using only session-typed channels can't deadlock:
endpoints are linear (quantity 1, which is exact in Wiz), and every `fork` adds one
channel between a new thread and its parent, so the channels form a forest. There, the
claim is a meta-theorem from the literature. This stage mechanises a **narrower**
statement in Wiz: for the finite fragment of a **pure, synchronous** model of threads and
channels, a typed, closed and acyclic configuration is final or can step
(`Deadlock.progress`), and a step preserves acyclicity (`Deadlock.stepAcyclic`). It does
**not** prove the 25c claim about the IO API: `Typed` and `Closed` are hypotheses, not
proved invariants, the model is synchronous while `runtime/` channels buffer, and
adequacy to the API is open (35d). The approach is Jacobs, Balzer and
Krebbers's (*Connectivity graphs: a method for proving deadlock freedom based on
separation logic*, POPL 2022), the core of LinearActris: progress follows from linearity
and an acyclic connectivity graph. It is item D4 of the concurrency plan, with the finite
fragment first. Library: `lib/SessionDeadlock.wiz` (`import SessionDeadlock`; every name
starts with `Deadlock.`). Tests: `lake test -- '=verif-deadlock'`.

**Status.** The library, its tests and this page are not on master at the time of
writing; they come from the unmerged stage-35 branch. Until they land, 25c's API claim
has no mechanised proof in the repository.
The theorems are ordinary definitions checked by the kernel. `#print axioms` is empty for
`Deadlock.progress`, `Deadlock.stepAcyclic` and `Deadlock.reachableProgress`. Only the
`link` connection (35c) uses an axiom: the Prelude's `castRefl`.
`Tests/Groups/VerifDeadlock.lean` pins the *statement* of each named theorem with a type
ascription, so a weakened statement fails even when the axiom print stays clean.

## 35a: the configuration model

A thread is a session-typed process over the endpoints it holds. A context `Ctx` lists
the endpoints: a channel name (`Nat`) and that end's remaining protocol (`Proto`, from
lib/Session.wiz). `Th n Γ` is a process over `Γ` that takes at most `n` actions. Each
action is one constructor of `Act`:

| action | typed by | continues as |
|---|---|---|
| `ret` | the context is empty | (the thread is finished) |
| `fork p m child parent` | any `p : Proto`, a mask `m` | the child holds `c : dual p` and the endpoints `m` selects; the parent holds `c : p` and the rest |
| `act pre post c p h x` at `.send A k` | `x` is a value `a : A` and a continuation | the endpoint at `k a` |
| the same at `.recv A k` | `x` is a continuation for every `a : A` | the endpoint at `k a` |
| the same at `.done` | `x` is a continuation | the endpoint closed and removed |

This is `Proc` (25b) over several channels at once. `ret` needs an empty context, so a
thread can't drop an endpoint, as in the linear API. The fuel `n` makes a thread finite
(the finite fragment). A fork's new channel name is a parameter of both continuations,
because the step chooses it.

A configuration `Cfg` is a list of threads read by index (a multiset). The channels are
the names the threads hold. `Step C D` is the reduction relation:

* **fork**: thread `i` is replaced by the parent's continuation, and the child is added at
  the end. The new channel's name is `Cfg.fresh C`, one more than every name in use.
* **send/receive**: thread `i` is at a `send A k` on `c1`, thread `j ≠ i` at a
  `recv B g` on `c2 = c1`. The sender goes on with its continuation, and the receiver goes
  on with the value cast along a proof of `A = B`. The exchange is synchronous, like
  `link`.
* **close**: two threads at `done` on the two ends of one channel both drop it.

The judgments on a configuration:

* `Typed C`: two different threads holding ends `(c, p)` and `(c, q)` of one channel
  have `DualR p q`. `DualR` is duality up to an equation between payload types: a send
  meets a receive with `A = B` and continuations dual at the cast value, and `done` meets
  `done`. Every other pair is `False`.
* `Closed C`: every channel a thread holds is also held by another thread. No endpoint
  dangles.
* `Acyclic C`: the connectivity graph is a forest. Its vertices are the threads, and its
  edges are the channels between the two threads that hold their ends. The definition is
  a ranking: functions `rk` (a rank per thread) and `par` (which thread holds a channel's
  parent end) such that
  1. every channel held by two different threads joins `par c` to the other thread, whose
     rank is higher (`Orient`);
  2. every thread is the child end of at most one channel (`OneUp`);
  3. no thread holds one name twice, so there are no self-loops (`NoLoops`).

  A finite graph has such a ranking exactly when it is a forest. Root every tree, let
  `rk` be the depth and `par` the parent. In the other direction, a cycle would need some
  thread that is the child end of two of the cycle's channels, or ranks that strictly
  decrease all the way round. The equivalence is argued here, not proved in Wiz.
* `Final C`: every thread has finished (no fuel left, or at `ret`).

## 35b: progress, and acyclicity preserved

**`Deadlock.progress (C) : Typed C → Closed C → Acyclic C → Final C ∨ HasStep C`.**

Every thread is finished, forking (which can always step), or ready on one endpoint
(`Thread.classify`). A finished thread holds nothing (`ret` needs an empty context). The
proof follows a ready thread's waiting chain over the ranking, by two inductions:

* `up` works by induction on the rank. Say thread `u` holds some endpoint and is ready on
  channel `c`. If `u` is `c`'s child end, the parent has a lower rank and also holds an
  endpoint, so `up` applies to it.
* `down` works by induction on the distance to the largest rank. If `u` is `c`'s parent
  end, the child `y` has a higher rank. Either something steps, or `y` is ready on its
  parent channel. By `OneUp` that channel is `c`, so `u` and `y` are ready on the two ends
  of `c`.

When two threads are ready on the two ends of one channel, `Typed` gives `DualR`, so
their actions meet: a send meets a receive, or `done` meets `done`. The configuration
steps (`pairAct`). A thread can't wait on itself (`NoLoops`), and the chain can't go
round, because the ranks would have to keep falling (`up`) or keep rising up to a bound
(`down`).

**`Deadlock.stepAcyclic : Step C D → Acyclic C → Acyclic D`**, by cases on the step:

* **send/receive** keeps every thread's channel names, so the same ranking works.
* **close** removes one name from each of two threads. The conditions only get weaker
  when names disappear (`Shrinks`, `shrinkGood`).
* **fork** builds a new ranking. Old ranks become `2·rk + 1`, and channels the child takes
  over from the forking thread `i` get the child as their parent end. Then there are two
  cases (`FCase`):
  * **A**: the child takes none of `i`'s parent channel. It goes below `i`, with rank
    `2·rk i + 2`, and the new channel's parent end is `i`.
  * **B**: the child takes `i`'s parent channel `c0`. It goes between `c0`'s parent and
    `i`, with rank `2·rk i`, and the new channel's parent end is the child.

  The new name is fresh, and `NoLoops` keeps the child's and the parent's names disjoint,
  so no channel gets a third holder. The proof is a case analysis over which of the two
  threads holding a channel is old, the forking thread or the child (`orientF`,
  `oneUpF`, `noLoopsF`).

Runs (`Steps`, the reflexive-transitive closure): a program starts as one thread holding
nothing (`Deadlock.init`), which is acyclic. So `Deadlock.reachableAcyclic` says every
configuration a program reaches is acyclic, and `Deadlock.reachableProgress` says such a
configuration is final or steps, given `Typed` and `Closed` (35d).

## 35c: the connection to `link`

`Proc.thread` turns a `Proc R p` (25b) into a thread on a single endpoint. It needs
`Bounded n p`, a bound on the protocol's depth, because a thread's fuel is a number while
a dependent protocol's branches can differ in length. `linkCfg n p bd a b` is the
configuration that `link p a b` runs: `a` and `b` on the two ends of channel 0.

`Deadlock.linkProgress` proves that this configuration is typed, closed and acyclic, so
by `progress` it is final or can step. This is a second proof that the model's two
processes on one channel can't get stuck. `link`'s totality is the first, and it is a
statement about the function, not about deadlock; this one goes through the general
theorem instead of `link`'s structural recursion.

`linkTyped` needs `DualR p (Proto.dual p)` (`DualR.dual`). At a payload type that is a
variable `A`, the receive step's `cast` along `A = A` does not compute, so the lemma
uses `castRefl` (CoreSpec §8.4a). It is the only axiom in the module.

```
import SessionDeadlock

def P : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))
def client : Proc Nat P := (3, fun r => r)
def server : Proc Unit (Proto.dual P) := fun n => (n + n, ())
def bd : Deadlock.Bounded 2 P := fun _ _ => True.intro
def ok := Deadlock.linkProgress 2 P bd client server
```

## 35d: what is not proved

The module proves progress and preserves acyclicity for the finite fragment. It does
**not** prove deadlock freedom for a Wiz program: the following are open, roughly in
order. (25c keeps the API claim as an argument until they are done.)

1. **Preservation of `Typed` and `Closed`** (subject reduction). With those two,
   `reachableProgress` loses its hypotheses: a program started from `Deadlock.init` would
   be final or step at every reachable configuration *in the model*. The parts:
   * send/receive: `DualR` of the continuations is the second component of the
     witness;
   * close: two ends removed;
   * fork: the new channel is `DualR p (Proto.dual p)`, which needs `castRefl`, and the
     masks keep every other channel's two holders.

   This is the same `Holds`/`isAtSet` bookkeeping as 35b, plus endpoint protocols. The
   `Closed` part also needs "exactly two holders" (linearity), which `Closed` does not
   state yet.
2. **Recursive protocols** (plan 25e): a bounded loop whose bodies are `Bounded` fits
   35a–35c as it is, if the protocol type is available. True recursion (ν, sizes) needs
   threads that are not fuel-bounded (a coinductive `Th`, or sized types). The progress
   proof does not use the fuel; the definitions do.
3. **Delegation** (plan 25e): an action that sends an endpoint, which moves an edge of
   the graph from one thread to another. Acyclicity is then preserved because the sent
   endpoint leaves the sender (linearity), the case JBK22 treat. The model has no such
   action yet.
4. **Asynchrony**: the model is synchronous like `link`, but `runtime/` channels buffer
   sends. An asynchronous model adds a buffer per channel and makes "ready" mean "a
   receive with an empty buffer".
5. **Adequacy**: relating `Step` to the IO API (`Chan.forkD`/`sendD`/`recvD`/`closeD`)
   or to the stage-32 `Conc` scheduler (`lib/Conc.wiz`), so that the theorem is about Wiz
   programs and not only about the model.
6. **The forest definition**: a Wiz proof that `Acyclic` (the ranking) is equivalent to
   "no cycle" in the graph-theoretic sense. Here it is argued (35a).
7. **MVars, locks and `partial`** stay outside the claim, as in 25c. D5 (lock levels) is
   the next step there.

So the honest summary is: progress and acyclicity for a finite, synchronous model, with
`Typed` and `Closed` assumed; not deadlock freedom for the API, and not yet for reachable
configurations.
