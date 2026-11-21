# Hot-reload P0 prototype (coding-only lane)

Status: **prototype, not built or run in this lane**. This directory is the P0
interpreter + transaction + cache from `/workspace/wiz-notes/hot-reload.md` (§12
"P0 — interpreter only, single-threaded"). It is a separate Lean library
(`HotReload`) and a non-default executable (`hotreload`); nothing under `Wiz/`,
`lib/`, `Main.lean` or the default `lake build` targets imports it. The default
path is therefore unchanged.

The lane's rule was: no `heavy`, no `lake`, no `wiz`, no `nix`, no build or test.
Everything below is **code-complete by inspection, unverified**. The "roadblocks"
section is the queue-slot list: what a build/measurement has to check.

## What is modelled

| file | what it is |
|---|---|
| `Basic.lean` | `Ty`, `Tm`, `Val`, the slot/generation records, the revision (content hash) and the versioned internal name, the runtime state, `Observable`/`Pinned` |
| `Check.lean` | the toy checker, the structural `Value A` predicate, the read-free witness rule, staging/commit/abort, the topological order and the per-generation check cache |
| `Interp.lean` | the interpreter: `read` as a slot lookup, memoised thunks, closures over a generation (no stale closures), `snapshot`, `readNow`, `withPinned`, `version`/`revision`, the `#check` line |
| `Tests.lean` | the P0 acceptance cases as pure `Bool`s; **not run**, no `#eval` |
| `Main.lean` | the `hotreload` command; disabled unless `--allow-reload` is passed |
| `../drafts/hot-reload/Reload.wiz` | the proposed Wiz surface (not parsed yet; not part of any check) |

The model is deliberately tiny: a first-order `Ty`, a de Bruijn `Tm`, and a
generation table. It is a *shape* witness for the design, not a Wiz interpreter.

## Design points encoded

* **A reload never rebinds a name.** A slot has a stable `surface` name
  (`x`), a stable slot id, and an `internal` body name `x@<bodyRevision>`. A
  *different* body has a different body revision, hence a different internal name;
  re-staging the same body keeps its old name, which is the old meaning, not a
  rebinding. `Gen.names` is the history/audit list. A body's memo `revision` is
  separate: it mixes the body revision with the callees' revisions and is
  recomputed to a fixed point on commit (generation-keyed on a `self`-read
  cycle).
* **`read` is opaque and generation-relative.** `read p o` is a table load in
  generation `p`; a closure stores the generation id it was built in, so a
  function read at `p` calls its reloadable callees at `p` even after a swap.
  `readAt` is the explicit-`Pinned` form used by pure code; `read` alone is the
  hidden `self` of a slot body.
* **Snapshot consistency.** A `Pinned` is a generation id. `snapshot` names the
  current generation; `install` appends a new one and never mutates an old one.
  A reader holding an old `Pinned` reads the old table forever.
* **Atomic multi-slot transaction.** `commit` checks every staged body and
  witness, topologically orders the staged items, then builds the new generation
  and publishes it in one functional step. Any error returns `Except.error` and
  the runtime is unchanged (all-or-nothing).
* **Fixed shape.** Staging an unknown slot, or removing one, is an error; the
  slot set and slot types are fixed for a generation.
* **`Value A`.** The structural predicate rejects `Pinned`, `Subscription`,
  `Region`, `World`, `Uniq`, `Chan`, `Mut`, `IO`, `IO1`, and anything containing
  them; `Observable A` is a value iff `A` is. A linear slot is refused before the
  body is checked.
* **Witness rule.** A slot body is checked at `A` with the hidden `self :
  Pinned`; the witness is checked at `A` with `self` too, but must be
  **read-free** (`no read`, `no readAt`, no `snapshot`). This is stricter than
  the note's "a checked witness of its type" because a witness that can `read`
  can be circular (`g : Unit → False := fun u => read self g u`, witness
  `read self g`). See the roadblock below.
* **Cache.** Two keys are kept apart, as §6.3/§8.5 require:
  * the **check key** `(slot type, body, helper environment, witness, kernel
    version)` is generation-independent and caches the kernel verdict;
  * the **revision** mixes the check key with the revisions of the slots the body
    reads, so a runtime memo / `native_refl` key is not reused after a callee
    changes.

  An unchanged body re-staged after a swap is a cache hit; `Tests.lean` records
  that as a `Bool`.

## What is *not* here (deliberately)

* No real `reloadable` parser/elaborator command, no `Observable`/`Pinned`
  axioms, no kernel integration. Those need a build and a `Wiz/` change; this
  lane is code-only.
* No P2 interpreter/compiled agreement and no `dlopen`. §7.5 is explicitly out of
  scope.
* No threads, atomics, GC/arena, subscriptions, packages, selfhost, Loom/scry
  runtime integration.
* No performance claim. The note's §6.5 budgets are targets, not measurements.

## Roadblocks: what needs a build or a measurement

Each item is a decision this lane cannot make statically. "Build should check"
is the minimal queue-slot work; "measure" is a benchmark or a real run.

1. **D1 — is a trusted `read` primitive acceptable?** The surface needs
   `Pinned`, `read`, `snapshot` as axioms (or a first-order `Gen` argument). The
   prototype uses a Lean model, so it does not settle it.
   *Build should check:* `#print axioms` of a real `Reload.wiz` program lists
   exactly the intended primitives; a sealed build refuses `install`; the trust
   ledger gets a row. This is shared with `effects-handlers.md`.
2. **D3/C7 — generation vs revision naming.** The prototype keeps both:
   `version : Pinned → Observable → Nat` (the slot's generation-local counter)
   and `revision : Pinned → Observable → String` (the content hash). The note
   says the scry contract needs one decision before it is written; this lane
   implements both and does not choose.
   *Build should check:* the chosen name appears in `#check`, `#print axioms`,
   the ledger and scry's `(generation, revision)` finding tuple with no alias.
3. **Witness circularity.** The note's witness rule ("a checked witness of its
   type") is unsound if the witness may call `read`: a slot `g : Unit → False`
   with body `fun u => read self g u` and witness `read self g` type-checks.
   The prototype forbids a witness that mentions `read`/`readAt`/`snapshot`; the
   real elaborator must decide whether that is a syntactic restriction on the
   witness term, a separate total fragment, or a kernel rule. This is not a
   build-only issue, but the kernel's actual `checkPartial`/`addPartialDecl`
   behaviour must be inspected and a regression test written.
   *Build should check:* `partial (default := w)` below `reloadable` cannot be
   circular through `read`; a test proves the rejection.
4. **Cache integration.** The real `Wiz/Cache.lean` key is the chained module
   hash plus salt/toolchain/binary; the prototype's `fnv1a` and its
   `(type, body, helpers, witness, kernel)` key are a model. The per-slot cache
   must be layered on `Cache.Key` without losing the binary/salt domain
   separation.
   *Build should check:* a warm swap of an unchanged body is a hit; a change to
   a non-reloadable helper that a slot mentions invalidates that slot only; a
   collision cannot select another input's verdict (strong key).
5. **Elaborator surface.** `reloadable def x : A := e` must allocate a stable
   slot id, elaborate `xBody : Pinned → A`, check the witness, add
   `x : Observable A` once, and record the body/version in the command state.
   The prototype's `Stage` is the data shape, not the elaboration.
   *Build should check:* `#check x` prints `Observable A` plus the slot/generation
   line (C11: use a `Msg`, not a private info tree); a second `x` is the
   "no rebinding" error; a missing witness is an error.
6. **`Value A` in the real quantity system.** The prototype's `Ty.isValue` is a
   whitelist. The real check must see field quantities through structures and
   inductives, and must name the real formers (`Uniq`, `Pts`, `Mut`, `MutOpt`,
   `Chan`, `IO`, `IO1`; `Lent` is a Feral lowering name, not a user type).
   *Build should check:* the §5.5 rejected/accepted examples, including a
   structure with a `1`-quantity field and `Observable (IO Nat)`.
7. **Interpreter vs the kernel evaluator.** `#eval` is the kernel evaluator and
   cannot run externs; P0's interpreter is a new runtime component. The model's
   fuel/`forcing`/memo protocol is not the real one.
   *Build should check:* a divergent slot diverges in the reader, not in
   `install`; a data slot that reads itself fails (blackhole) rather than
   deadlocks; a function slot's self-read is fine (the thunk is already forced).
8. **Atomicity and the single-writer cell.** The prototype's `commit` is
   functional (failure leaves the old runtime untouched), which models
   single-threaded atomicity; it says nothing about `wiz_current`, acquire/
   release, or a concurrent reader.
   *Build/measure:* P1's TSan test (note test 4) is the real evidence.
9. **Normal-code cost.** The claim "zero for normal code" is not testable here.
   *Measure:* compile a non-reloadable benchmark before/after and diff `#ir`/C;
   the reloadable indirect-call overhead on a hot loop.
10. **Budget §6.5.** `swap < 100 ms`, generation build `< 1 ms`, publish
    `< 1 µs` are targets. *Measure:* 1/10/100 slots, 10/100/1000-line bodies.
11. **Compiled path / `native_refl`.** Out of P0, but the design says
    `native_refl`/`native_decide` must refuse a term that mentions
    `Observable`/`read` (C3). *Build should check:* such a term is rejected, not
    silently evaluated by AOT code.

## How to build/run in a queue slot (do not run in this lane)

```
lake build HotReload           # typecheck the model and the unrun tests
lake build hotreload
.lake/build/bin/hotreload --allow-reload
lake build                     # default target must be unchanged
```

`lake build HotReload` is not a default target; see `lakefile.lean`. The test
list in `Tests.lean` is a `List (String × Bool)` with no `#eval`; the executable
prints it only with `--allow-reload`.
