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
  cycle). The no-rebinding rule is the note's first principle; its evidence is
  `wiz-notes/import-shadowing.md` and `soundness-probes/is-import-shadowing`.
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

  The cache is consulted **before** the checker: a hit is a prior successful
  verdict for the same body/type/mentioned-helpers/witness/kernel, so the type
  checker and the witness check are skipped (the `Value` check and the revision
  refresh still run). An unchanged body re-staged after a swap is a hit;
  `Tests.lean` records that as a `Bool`.

## Model boundaries (trusted in the prototype, must be checked in a build)

* `Runtime.initial` accepts any slot list, including a non-`Value` slot or an
  ill-typed body; `Tests.lean` uses that to exercise the *stage* rejection. A real
  initial generation must run the same `Value`/body/witness checks as a swap.
* Non-reloadable helper bodies are trusted by the model (`Helper.body`); it has
  their type but never checks the body. The real elaborator checks every helper,
  and a changed helper is a new name (§6.3).
* `bodyRevisionOf`/`helperHashFor` use the model's FNV-1a, not SHA-256. The cache
  integration must use `Wiz/Cache.Key`'s strong key and must keep the binary/salt/
  toolchain domains.
* `commit`'s atomicity is functional-state atomicity in one thread. It is not
  evidence about a concurrent reader, acquire/release, or a real `wiz_current`.
* The model's `Observable` has a public constructor; `read` checks the toy `Ty`
  against the slot to catch forgery. The real `Observable` has a private
  constructor and the type parameter is checked by the elaborator.

## What is *not* here (deliberately)

* No real `reloadable` parser/elaborator command, no `Observable`/`Pinned`
  axioms, no kernel integration. Those need a build and a `Wiz/` change; this
  lane is code-only.
* No P2 interpreter/compiled agreement and no `dlopen`. §7.5 is explicitly out of
  scope.
* No threads, atomics, GC/arena, subscriptions, packages, selfhost, Loom/scry
  runtime integration.
* No performance claim. The note's §6.5 budgets are targets, not measurements.

## Note §10 coverage

| note test | here |
|---|---|
| 1 failed swap keeps the old generation | `testFailedSwap` |
| 2 multi-slot atomicity | `testAtomicTransaction` |
| 3 pinned reader sees one generation | `testSnapshotConsistency` |
| 4 concurrent readers / TSan | not P0; P1 |
| 5 swap during a running task | not P0; P1 |
| 6 no stale closure | `testNoStaleClosure` |
| 7 unpinned `read` is ill-typed | `testUnpinnedRead`, `testReadAtNeedsPinned`, `testReadAtPinned` (type-level only; no proof model) |
| 8 parametric theorem survives | not modelled: the prototype has no proofs; roadblock 5/6 |
| 9 linear slot type refused | `testLinearSlot` |
| 10 pure code cannot snapshot | `testSnapshotPure` |
| 11 interpreter/compiled agreement | P2, out of scope |
| 12 normal code unchanged | `testNormalCode` (interpreter only; no IR/C diff) |
| 13 swap scales with the body | not measured; roadblock 10 |
| 14 old generations collected | not P0; P1 GC |
| 15 retained generation reported | `testRetentionCount` is the P0 history count, not GC/reporting |
| 16–18 packages/auth | P3, out of scope |

## Roadblocks: what needs a build or a measurement

Each item is a decision this lane cannot make statically. "Build should check"
is the minimal queue-slot work; "measure" is a benchmark or a real run.

1. **D1 — is a trusted `read` primitive acceptable?** The surface needs
   `Pinned`, `read`, `snapshot` as axioms (or a first-order `Gen` argument). The
   prototype uses a Lean model, so it does not settle it.
   *Build should check:* `#print axioms` of a real `Reload.wiz` program lists
   exactly the intended primitives; a sealed build refuses `install`; the trust
   ledger gets a row. This is shared with `effects-handlers.md`, and these are
   exactly the probes the note names for C2/D1.
2. **D3/C7 — generation vs revision naming.** The prototype keeps both:
   `version : Pinned → Observable → Nat` (the slot's generation-local counter)
   and `revision : Pinned → Observable → String` (the content hash). The note
   says the scry contract needs one decision before it is written; this lane
   implements both and does not choose.
   *Build should check:* the chosen name appears in `#check`, `#print axioms`,
   the ledger and scry's `(generation, revision)` finding tuple with no alias.
3. **Witness circularity.** The note's witness rule ("a checked witness of its
   type") is only obviously sound if the witness cannot call `read`. A witness of
   a slot type `A` is a term of `A`; `read p h` is a term of `h`'s type, and it is
   opaque to the kernel. `Wiz/Core/Check.lean`'s `addPartialDecl` checks the
   witness in the *old* globals and inserts the declaration afterwards, so plain
   `partial` excludes a direct self-reference. A `reloadable` declaration is
   different: the body must see its own slot (`read self g`), so the slot name is
   in scope before the witness is checked on a reload (and possibly on the first
   declaration, depending on the order §6.1 chooses). That is the route to
   `False` if `A` can be a function into `Prop` (the note's `Unit → False`
   example). The prototype forbids a witness that
   mentions `read`/`readAt`/`snapshot`. The real elaborator must decide whether
   that is a syntactic restriction on the witness term, a separate total
   fragment, or a kernel rule; the kernel's actual `checkPartial`/`addPartialDecl`
   behaviour must be inspected and a regression test written. This is not a
   build-only issue, but the acceptance test needs a build.
   *Build should check:* `partial (default := w)` below `reloadable` cannot use
   `read` to reach an opaque proof; a test proves the rejection.
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
   line (C11: use a `Msg`, not a private info tree; the note's probes are the
   `Tests/LSP.lean` constructor-table test and the hover test); a second `x` is
   the "no rebinding" error; a missing witness is an error.
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
    silently evaluated by AOT code. The note's probes are a `native_refl` on
    `read p x` that is rejected, a `#ir f` that is byte-identical for a function
    with no observable, and the compiled-vs-interpreter differential on a swap
    schedule (test 11).

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
