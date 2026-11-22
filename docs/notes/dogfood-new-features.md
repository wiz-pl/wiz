# Dogfooding the new features: where Wiz and the libraries should adopt them

Read-only audit, 2026-11-14, of `master` at `aeaa34ef`. No library edits, no build. Evidence
is static (reads and greps) plus measurements taken separately during development; those are
informal (not from a controlled benchmark run) and marked so at each claim. Where this note says
"est.", nothing has been measured yet; the last section lists the measurements wanted.

Legend: **now** = on master at the audit commit. **after stack** = implemented on a branch, PR or
stack that is not on master yet; the workstream starts only after that merges.

**Reading this note later.** It is a snapshot. Every `file:line` reference below is a line of
the audit commit `aeaa34ef`, not of today's `master`; the code has moved since (for example
`preludeText` and `Scope.lookup` in `selfhost/Frontend.wiz`), so look a definition up by the
name given beside the reference. Checked against `master` at `d23473da` (2026-11-16), these
items have landed since the audit:

| item in this note | on `master` now |
|---|---|
| `calc` + `Trans` (inventory; top 10 #1, W1) | **landed** (13s, `257c1b33`; `term.calc` in `Wiz/Parser/Builtin.lean`). `Trans` instances in `lib/Logic.wiz`, `IntOrder` and `Rat`; proofs use `calc` in `lib/Nat.wiz`, `Ring` and `IntRing`, not yet in `BitVecShift`, `BitBlast` or `Rat`. |
| `include_str` | **landed**, in the self-hosted parser too (`term.includeStr`). `preludeText` is still an inline string in `selfhost/Frontend.wiz` (W7's extraction is open). |
| `wiz fmt` | **landed** (11aa, `Wiz/Format.lean`, `b818b94a`). |
| `wiz lint` | not on `master` (no `Wiz/Lint.lean`, no `lint` command). |
| `--split N` (top 10 #6) | **landed** in `wiz build` (`666b4437`); `scripts/fixpoint.sh` does not pass it yet. |
| `ResultQ`/`ResultH` (W4) | **landed** in `lib/Region.wiz` (`60cd8ec9`); `lib/HeapBorrow.wiz` and `lib/Optic.wiz` do not use `ResultH` yet. |
| `PMap`/`PSet` | **landed** (`lib/Data/PMap.wiz`). |
| scry stack (`lib/Scry/*`, `scry/`) | **landed**; `Store`/`Egraph` are still the list models (top 10 #10, W6 open). |
| Grail region cache (top 10 #8, W2) | **landed**: `tc.regionCache` in `Grail/Elab.lean`, `--region-cache` in `Grail/Cli.lean` (`d5841ca4`). |
| Nix package with a warmed read-only cache (top 10 #7) | **landed**: `flake.nix` warms `share/wiz/cache` and both wrappers pass `--cache-ro` (`f480155a`). |
| duplicated Text helpers in `Json`/`Feral` (top 10 #3) | **done** (`ef67c6cf`: `Json` and `Feral` use `lib/Text.wiz`, `Json.divMod` is native `Nat.div`/`Nat.mod`, and `Fe.splitGo`/`Fe.wordsOf` accumulate in reverse). |
| `do` blocks in the I/O library (top 10 #4) | partly: 10 lines of `lib/Sys.wiz` still call `IO.bind`/`EIO.bind` (31 binds at the audit). |

The other candidates (equality lemmas at `Sort u`, `BEq` in the Prelude, the HDL helpers and
`HTrie` hash, the selfhost lookups) were still open at `d23473da`.

## 0. Feature inventory: what is on master, what is not

| feature | status | where it lives / what is missing |
|---|---|---|
| `--cache-ro` (read-only cache layers) | **now** | `Wiz/Toolchain.lean:29-31,104-111`; grail passes it to jobs (`Grail/Elab.lean:67`); `docs/building.md:258`. CI never passes it; the Nix package ships no store cache. |
| `--region-cache`, `--region-stats` | **landed in both**: `Toolchain.regionCache`/`regionStats`, `toFlags`, and one `region-stats:` line per grail job (`Grail/Elab.lean`, `Grail/Graph.lean`). | `Main.lean:190-194,551-553,872`; `Grail/Elab.lean:15,87-110`; `Wiz/Cache.lean:810-827`. |
| `--split N` for `wiz build` | **after stack** | now [15k](../stages/15-performance.md). CI's shard `"split"` is a different feature (`.github/test-shards.json`). |
| Grail one-job (`build F` = check+IR+C) | **now** | `Grail/Graph.lean:51-56,132-143`; informal measurement: one job avoids repeating the IR pipeline. |
| tower / Nix packaging | **now** | `tower/`, `flake.nix:83-109`. No warmed cache; `source nix` and `toolchain link` are in `docs/building.md`. |
| `calc` + `Trans` | **after stack** | now [13s](../stages/13-language.md). No `term.calc` in `Wiz/Parser` or `Wiz/Elab` today; the workaround is `Eq.via` (`lib/Nat.wiz:57`) and nested `Eq.trans`. |
| `include_str` | **after stack** | now [include-str.md](../stages/13-language/include-str.md); at the audit, selfhost parity was not implemented. |
| `wiz fmt` | **after stack** | now [11aa](../stages/11-tooling.md); at the audit, no `Wiz/Format.lean`. |
| `wiz lint` | **after stack** | designed, not on `master` (no `Wiz/Lint.lean`). |
| `wiz repl`, `wiz test-driver` | **now** | `Main.lean` (`replCmd`: `:type`, `:load`, `--prelude`; `testDriverCmd`); docs/stages/11-tooling.md, 11ac. The single-file `wiz test FILE` is still a proposal. |
| `ResultQ`/`ResultH`, q-variable fields | **after stack** | now in [libraries.md](../libraries.md) (`ResultQ`, `ResultH`). `Result1`/`Result`/`Monad Result` are **now** (`lib/Region.wiz:106`, `lib/Data/Result.wiz:34-44`). |
| `PMap`/`PSet` | **after stack** | `lib/Data/PMap.wiz`, now in [libraries.md](../libraries.md) ("Persistent data structures"). Not merged at the audit commit. |
| `U64Map`, `StrMap`, `Intern`, `U32Array`/`U64Array`, `WordMap` | **now** | `lib/WordMap.wiz`, `lib/WordArray.wiz`, `lib/Intern.wiz`, `lib/Std.wiz`. |
| `Optic`/`OpticDerive`, `Functor`, `Eff`/`Handle`, `Region`/`Result1` | **now** | `lib/Optic.wiz`, `lib/OpticDerive.wiz`, `lib/Functor.wiz`, `lib/Eff.wiz`, `lib/Handle.wiz`, `lib/Region.wiz`. |
| `sat_decide_native` | **not a PR** | an axiom whose statement mentions the certificate costs as much as the check itself: no gain, more trust. Do not adopt. (It has since been added anyway as [28e](../stages/28-solvers.md), behind `--trust-native`.) |
| scry typed columns / e-graph | **after stack** | `lib/Scry/*` and the `scry/` package only exist on that stack. |
| Hdl named ports / bundles / reset / enable | **now** | `hdl/src/Hdl/Core.wiz:148,1749-1785,2534-2660`; structured wires (`Wire t := NetM (HwTy.Ids t)`, `Core.wiz:931`). |
| Hdl multi-clock / CDC | **after stack** | design and prototype only at the audit; now `Multi`, `Clocking.domains` and `hdl/src/Hdl/Cdc.wiz` ([libraries.md](../libraries.md), H14 P2). |

`--trust-native` appears only in examples and tests (`hdl/examples/hdl-verified-*.wiz`,
`Tests/Native.lean`), with a trust note at each use; no library file uses `native_refl`
(9 non-comment uses, all in examples). No `sorry` in `lib/` or `selfhost/`. The 22 `axiom`s in
`lib/` are the documented natives and `Region`'s lifetime primitives (`lib/Region.wiz:33-48`,
`lib/Std.wiz`, `lib/IO.wiz`, `lib/MVar.wiz`, `lib/Ref.wiz`).

## 1. Top 10 candidates

Scored as (impact × confidence) / effort, each 1–5; impact is the expected size of the win on
the stated goal (build/eval time, RSS, proof readability, lines removed). Ties are ordered by
impact. "Big rocks" (high impact, high effort, low score) are listed after the table; they are
the workstreams' main prizes and should not be read as rejected.

| # | candidate | where | effort | expected win (one line) | score |
|---|---|---|---|---|---|
| 1 | `calc` for the chained proofs (**after stack**) | `lib/BitVecShift.wiz:29-45,409-436`; `lib/BitBlast.wiz:525-533,680-740`; `lib/IntRing.wiz:96-110`; `lib/Rat.wiz:207-237`; `lib/Nat.wiz:50-57`; `lib/Ring.wiz`; `lib/Vec.wiz`; `lib/HProp.wiz:108-113,312` | 2 | −15–25% of the lines in the densest proof files (BitVecShift/BitBlast/IntRing/Rat; `lib/` has 331 `Eq.trans`, 197 `congrArg`, 11 `Eq.via`), and a failure names the failing step; e.g. `Bits.low_shift` (19 lines) → ~8 | 10.0 |
| 2 | Equality lemmas at `Sort u`/`Type u` (**now**) | `lib/Logic.wiz:197-232`, duplicate `congrArg` at `lib/Nat.wiz:43-48`; downstream copy `wiz-cats/src/Cats/Eq.wiz:1-12` (G1 in `wiz-cats/FINDINGS.md`) | 1 | deletes a 29-line workaround module and the every-lemma-is-`Type`-only papercut; categories and any `Type u` proof get the standard lemmas | 10.0 |
| 3 | Delete the duplicated Text utilities (**now**) | `lib/Json.wiz:57-88` (`divMod`, `natChars`, `charsEq`, `revOnto`, despite `import Text` at `:2`); `lib/Feral.wiz:137-175,160-168,1016-1024` (`leq`, `seq`, `lpre`, `map`, `any`, `splitGo`, `wordsOf`) | 1 | −~90 lines, one copy of list/string helpers; `Json.divMod` becomes the native `Nat.div`/`Nat.mod`, and the two O(n²) one-char-at-a-time accumulates in Feral become linear | 10.0 |
| 4 | `do` blocks in the I/O library (**now**) | `lib/Sys.wiz` (31 `IO.bind`/`EIO.bind`, e.g. `:205-236`), `lib/IO.wiz:189-194`, `lib/Handle.wiz` | 1 | −~40 lines of `bind (fun x => …)`; `Monad IO`/`Monad1 IO` already exist (`lib/IO.wiz:52-59`), so this is semantics-preserving | 10.0 |
| 5 | Modernize the HDL examples and drop the local list helpers (**now**) | `hdl/examples/hdl-gaps.wiz:145-154`, `hdl/examples/hdl-mem.wiz:65-72`, `hdl/examples/hdl-sim.wiz:62`, `hdl/examples/hdl-compose.wiz:67,115-116`; `hdl/src/Hdl/Core.wiz:63-70` (`Hdl.map`/`Hdl.rev`), `:81` (`Hdl.natsEq`), `:948` (`Hdl.wEq`) | 1 | a `Circuit.RstEn`/`HwTy.rstEn` alias next to `withResetEnable` (`Core.wiz:1771`) removes the 3-line `prod (named "rst") (prod (named "en") …)` from 5 files; `BEq` for `List Nat`/triples removes 3 hand-written equalities (~40 lines) | 10.0 |
| 6 | `wiz build --split 4/8` in the fixpoint and CI selfhost builds (**after stack**) | `scripts/fixpoint.sh:26`; the CI selfhost compile step (`grail selfhost`/`wiz build` in `Grail/Selfhost.lean`) | 1 | the stage-1 selfhost compile is faster at `--split 8` (informal), but the built binary is slower, so the net fixpoint gain is smaller | 9.0 |
| 7 | Ship the Nix package with a warmed read-only cache (**after stack**) | `flake.nix:88-103` (installPhase), plus `--cache-ro $out/share/wiz/cache` in the wrappers | 1 | clean-`HOME` `grail build` of a one-target package 3.2 → 0.9 s, 437 store entries hit (informal) | 8.0 |
| 8 | Give Grail jobs the region cache (**now feature, plumbing ours**) | `Wiz/Toolchain.lean:28-31,104-111`; `Grail/Elab.lean:66-69` (`elaborate`); `Grail/Cli.lean:96-118` (the job process) | 2 | ~1.0 s of a 3.3 s warm `wiz check` of `hdl/examples/hdl-compose.wiz` is `.wizc` decode (12 modules, 15.5 MB text vs 5.5 MB regions; informal), so est. 15–25% off warm grail builds plus lower RSS | 6.0 |
| 9 | Thread the hash through `HTrie`, cheapen `NatList.hash` (**now**) | `hdl/src/Hdl/Core.wiz:761-766` (hash), `:785-810` (find/insert: 20 × `Nat.testBit h d`, each a division by `2^d`) | 1 | one shift per level instead of 20 `div`+`pow` per emitted node; est. 5–15% off `Circuit.netlist` on big designs (measure `hdl/examples/hdl-temporal.wiz`) | 6.0 |
| 10 | Native store and array-backed e-graph for scry (**after stack**) | `lib/Scry/Store.wiz:30-95` (`memRow`/`insert` linear), `lib/Scry/Egraph.wiz:177-250` (`List.append g.parent [id]` per node, linear `find`); `scry/src/Scry/CstStore.wiz` (already `U32Array`/`U64Array`) | 4 | the Wiz-side copy into the model is ~85% of parse wall time (0.53–0.91 MB/s vs the shim's 3.3–6.5; informal); store/e-graph go from O(n²) to near-linear | 5.0 (6.25 if the native store lands as designed) |

**Big rocks, not in the scored top 10** (high impact, high effort, confidence still medium):

* **CAF caching of closed top-level definitions** — **done on master** (`3ef38ad8`, stage 15i,
  PR #207; verified 2026-11-19 in `docs/notes/caf-closed-constants-2026-11-19.md`): the OLED demo's
  value simulation rebuilt `RomT` tables every cycle and spent ~60% of its time in malloc/RC
  (profiled informally before the feature); `IR.cafs` now caches closed definitions. The local
  reproduction is 204.9M → ~1.9k mallocs for 100k lookups. No work left here.
* **Selfhost `StrMap` keys**: `selfhost/Frontend.wiz:43-49` (`Scope.lookup`) converts the Wiz `String` to a native key
  with `Str.ofString` on every global lookup, and `selfhost/Backend.wiz:445,2465` does the same per
  `arity`/inlining lookup; intern once (`lib/Intern.wiz`) and key a `U64Map`, or hash the chars
  directly. Impact 3, confidence 2, effort 3 → 2.0. Measure `=selfhost`/selfcheck.
* **`ResultH`/`Result1` plumbing**: `lib/Region.wiz`, `lib/Optic.wiz:75-138`, `lib/HeapBorrow.wiz:30-45`
  all thread `Result (B × V)` by hand (35 `.ok`/`.err` matches in `Region` and `Optic` alone). After
  `ResultQ` merges, `ResultH 1 B V` is definitionally `Result1 B V`, so the pair plumbing can go.
  Impact 3, confidence 3, effort 2 → 4.5.

## 2. Workstreams (one PR each)

Each is one branch/PR, ordered so the ones that need no dependency come first.

### W1. Proof readability: `calc` and `Trans` (**after stack**)

Goal: replace the nested `Eq.trans`/`let eN`/`Eq.via` chains with `calc` steps; keep every proof
term kernel-checked and unchanged in statement.

* `lib/BitVecShift.wiz:29-45` (3 intermediate `let`s + a 3-deep `Eq.trans`), `:409-436` (5 named
  steps + `Eq.trans step1 (Eq.trans …)`), `:88-97`.
* `lib/BitBlast.wiz:525-533` (`@Eq.trans Nat …` with explicit endpoints), `:680-740` (Bool chains).
* `lib/IntRing.wiz:96-110` (transports whose equations are `nat_ring!` steps).
* `lib/Rat.wiz:208-237` (`Q.trans` is 4 nested `Eq.via`s, `Q.add_congr`, `Q.mul_congr`).
* `lib/Nat.wiz:50-57`, `lib/Ring.wiz:91-200`, `lib/Vec.wiz`, `lib/HProp.wiz:108-113,312`,
  `lib/HoareExamples.wiz:125`, `hdl/src/Hdl/Bits.wiz:180`, `hdl/src/Hdl/Temporal.wiz:164,302`.
* `wiz-reals/src/Reals/QSeq.wiz:11,31-35` (same style, downstream).

Also add the missing instances: `HEquiv` (`lib/HoareTactics.wiz:47`) so separation-logic chains
can be `calc`; the calc branch already adds `=`, `≤`, `<` for Nat/Int/Rat and `≈`.

Expected: −300–500 lines across those files, better error positions; no timing change expected
(check time may improve slightly). Verify: the `calc` group (`lake test -- '=calc'`) and the library shard in CI, plus a line count;
no perf claim.

### W2. Build and cache dogfooding (**mixed**)

Goal: make warm builds and the fixpoint use what the toolchain already has.

* `Wiz/Toolchain.lean`: add `regionCache : Bool` (and optionally `regionStats`) to `Toolchain`;
  `toFlags` gains `--region-cache`/`--region-stats`.
* `Grail/Elab.lean:66-69` (`elaborate`): build a `RegionStore` like `Main.lean:223-227` (the command state is
  already `ZeroOneMany`) and pass it to `Cache.elaborateCached`; `Grail/Cli.lean` parses the flags;
  the job process owns it (elaboration happens in the job, not in the scheduler); the job report
  can carry the `--region-stats` counters back to the scheduler.
* `scripts/fixpoint.sh:26`: `--split 4` (or 8) once `wiz build --split` merges; `.github` selfhost
  build likewise.
* `flake.nix`: warm a minimal package + Std cache during the build and add
  `--cache-ro $out/share/wiz/cache` to both wrappers (after the nix-cache branch).

Expected: warm grail builds −15–25% (region decode 1.0 s of 3.3 s on hdl-compose), fixpoint stage 1
−40%, clean-install first build −2 s. The Nix wrapper passes `--cache-ro` itself once the store
cache ships. Measure with a controlled benchmark run (commands in §5).

Risk: `--region-cache` is experimental and versioned by `regionFormat` (`Wiz/Cache.lean:627`); the
store is per job process (regions hold pointers and live for the process's lifetime), and stats
from several jobs must be summed by the scheduler.

### W3. Numeric and data-structure fast paths (**now**)

* `hdl/src/Hdl/Core.wiz:761-766`: hash with `Nat.land` (or at least fold without a division per
  element); `:775-810`: carry the hash halved down the trie and test the low bit, instead of
  `Nat.testBit h d` at every level. Check that `HTrie.depth = 20` is still the right trade.
* `lib/Ring.wiz:56-70,81-107`: `Ring.Key.merge` should merge two sorted lists in one pass instead of
  `insert`-ing each element, and `NatPoly.add` should merge rather than `addMono` per element; use
  `Nat.lt`/`Nat.beq` instead of `Nat.cmp`+`Ordering.andThen` (the 9 uses of `Nat.cmp` are in
  `Ring`, besides its definition), which builds and matches an `Ordering` where `Nat.lt`/`Nat.beq`
  is one Bool test. `nat_ring!`/`int_ring!` run at check time while `lib/Rat.wiz` and
  `lib/IntRing.wiz` are elaborated, so this is checking time, not runtime.
* `lib/Json.wiz`: use `Nat.div`/`Nat.mod` (native) instead of `Json.divMod`; use `Nat.repr` for
  `natChars` (see W7).
* Adopt the native containers where the model is the bottleneck: `lib/Intern.wiz:43-56` (`intern`
  appends to the list → O(n²) for n strings in the kernel/interpreter), `lib/WordMap.wiz:73-78`
  (fine; `ofList` folds native inserts), `U32Array`/`U64Array` in scry (W6).
* After `PMap` merges: use it where a *pure* map is needed and the list model is O(n) per op
  (`lib/Scry/Store.wiz` assoc lists), not to replace native `U64Map` in compiled hot paths:
  at 100k operations pmap is ~0.31 s vs umap ~0.03 s (informal).

Expected: checking time for ring-heavy files (est. 5–15% on `lib/Rat.wiz`/`lib/IntRing.wiz`),
netlist build 5–15% (`Circuit.netlist` on `hdl/examples/hdl-temporal.wiz`), fewer allocations.
Confidence: HTrie/ring high that the work is safe, medium on the size; measure first.

### W4. Result / Region / IO plumbing (**now + after stack**)

* `lib/Region.wiz:133-215`: several places do `match r with | .mk v => …` inside an `.ok`/`.err`
  match; `Uniq.end r (fun v => .ok (b, v))` already exists (`:126`) and removes the nesting.
  Keep the linear quantities exactly as they are.
* After `ResultQ` merges: `lib/Region.wiz` `Result1 B H` and `lib/Data/Result.wiz` `Result A` gain the
  quantity-polymorphic aliases; `lib/HeapBorrow.wiz:30-85` and `lib/Optic.wiz:75-138` replace
  `Result (B × V)` with `ResultH 1 B V` so specs name the handle instead of a pair. Expect the
  `.1`/`.2` plumbing in specs to disappear (~40–60 lines); no runtime change (definitional).
* `lib/Sys.wiz:205-236` and friends: `do` blocks (top 10 #4).
* `lib/Eff.wiz`/`lib/Handle.wiz` have no users outside `lib/EffHeap.wiz` and `examples/effects.wiz`;
  do not retrofit them, but new effectful code should start there (the `Row`/`Member`/`Handler`
  design is already the library's answer; `lib/Eff.wiz:166-205`).

Expected: −80–120 lines, clearer specs; `=regions`, `=effects`, `=seplogic` must stay green.

### W5. HDL modernization and CDC (**now + after stack**)

* Now: add `HwTy.rstEn`/`Circuit.RstEn` beside `Circuit.withResetEnable` (`hdl/src/Hdl/Core.wiz:1771`)
  and use it in `hdl/examples/hdl-gaps.wiz:145-154`, `hdl-mem.wiz:65-72`, `hdl-sim.wiz:62`,
  `hdl-compose.wiz:67,115-116`.
* Now: remove `Hdl.map`/`Hdl.rev`/`Hdl.reverse` (`Core.wiz:63-70`) in favour of `List.map`/
  `List.reverse` (in scope through `Deriving` → `Text`; add `import Text` if that ever stops
  being true), and make `Hdl.natsEq`/`Hdl.wEq` (`:81,948`) `BEq.beq` once the `List`/`Prod`
  instances are derived (W7).
  Caveat: the `Hdl.` prefix was chosen so importers keep the general names; with `private`
  (wishful `private-decls`) the reason disappears.
* After CDC merges (it has since, see the table at the top): a second register domain per composed top, CDC cells
  (`sync2`, `asyncFifo`) and domain annotations on wires; the prototype `hdl/examples/hdl-cdc.wiz`
  already emits two clocks but cannot clock a register, and crossing domains is silently
  accepted. Port `wiz-rv/src/Rv/{Core,Pipe,Board}.wiz` (already `deriving Bundle`) and check the
  `Clocking`/`Prim` kind checks (`hdl/src/Hdl/Prim.wiz:97-175`).
* `hdl/src/Hdl/Sim.wiz` is already the fast path (`Array`-based `simFast`, `:362-385`); document in
  examples that value simulation of a big circuit should use `Circuit.simFast`, not `Circuit.run`
  (CAF issue in the big-rocks list).

Expected: ~40 lines and clearer reset/enable ports now; CDC unblocks multi-clock designs.

### W6. Scry native columns and e-graph (**after stack**)

* `lib/Scry/Store.wiz:30-95`: keep the list model for the kernel, add native implementations for
  `TupleRel.insert`/`mem` and `LatRel.set`/`find` backed by `U64Map`/`U64Array` under
  `implemented_by` (the pattern of `lib/WordMap.wiz`/`lib/Intern.wiz`); a tuple is a `List U64`,
  so key it by a hash and compare the row (or intern to a `U32Array` of columns).
* `lib/Scry/Egraph.wiz:177-250`: `parent`/`rank` are appended per node and searched linearly;
  use `U32Array` for parent/rank and the same native-backend pattern, keeping the list model and
  its lemmas for the kernel. `rebuild`/`compress` (`:241-286`) currently copy lists per pass.
* `lib/Scry/Eval.wiz`: the delta loop over list stores; the store interface is the seam.
* `scry/src/Scry/CstStore.wiz` is already struct-of-arrays (`U32Array`/`U64Array`); the remaining
  cost is the Wiz-side copy (`Scry.Native.toCstStore`), which the native store work addresses.

Expected: parse 5–6× (to the shim's 3.3–6.5 MB/s) and e-graph saturation from O(n²) to near-linear;
biggest single performance win in the stack, highest effort. Measure with `scry parse --stats` and
the e-graph benchmarks.

### W7. Library and toolchain hygiene (**now + after stack**)

* Move `class BEq` (and `Inhabited`/`Repr` if cheap) from `lib/Deriving.wiz:33-70` into
  `lib/Prelude.wiz`, leaving the derivers in `Deriving`; then `Int.beq`, `Hdl.natsEq`
  and `Chars.eq` are one-liners, `String`/`Char` get `BEq` instances, and `Int`/`Sat.Lit`/`Hdl`
  types can `deriving BEq`.
  Today `Text` cannot use `BEq` because `Deriving` imports `Text` (the cycle is the only reason
  `Chars.eq` is hand-written).
* Remove the duplicated Text helpers and the quadratic accumulates (top 10 #3): `lib/Json.wiz`
  and `lib/Feral.wiz` (the `Fe.splitGo`/`Fe.wordsOf` char-by-char append is O(n²) in the word
  length; use a reversed accumulator and one reverse, as `Chars.splitGo` does at `lib/Text.wiz:158-166`).
* After `wiz fmt` merges: run it on `lib/Feral.wiz`, `selfhost/{Kernel,Frontend,Backend}.wiz`,
  `lib/BitBlast.wiz`, `hdl/src/Hdl/Core.wiz` (236/165/164/121/113 lines over 110 columns today) and
  keep a `--check` gate for new files.
* After `wiz lint` merges: `wiz lint lib/Prelude.wiz` reports 26 warnings including 2 real binder
  shadows in `Eq.subst`/`Eq.substBack` (found by the linter's prototype); fix those 2 and run lint over `lib/`
  in CI (the import-shadowing bug is a frontend error already, so lint's shadow rule is the one
  that pays).
* After `include_str` merges: extract `preludeText` (`selfhost/Frontend.wiz:4650` at the audit, a 6.7 kB
  single-line string that duplicates `lib/Prelude.wiz` and already differs definitionally, e.g.
  the embedded `Nat.sub` recurses on its second argument) to `selfhost/prelude.wiz` and embed it.
  This is the biggest single readability/maintenance win in `selfhost` and removes a silent
  divergence risk between the two preludes.

Expected: −150–200 lines, one definition of `BEq`/list helpers, formatter- and lint-clean files,
and a selfhost prelude that cannot drift.

### W8. Selfhost performance and parity (**now**)

* `selfhost/Frontend.wiz:43-49`: `Scope.lookup` walks the local-binder list linearly and converts
  every global name with `Str.ofString`; keep a `StrMap` on the `String` (it already is one) but
  avoid the conversion by keeping `Str` in the scope, or intern names and key a `U64Map`.
* `selfhost/Kernel.wiz:572-576` (`lookup`): walks the de Bruijn environment per variable; a
  random-access structure (the `Hdl.RList` pattern, `hdl/src/Hdl/Core.wiz:1230-1260`, or a trie)
  would make it O(log n). This is the stage-2 hot path; measure before changing (array copies on
  `bind` can lose).
* `selfhost/Backend.wiz:435-450,2465`: `StrMap` lookups per codegen application; the same intern
  treatment as above.
* `selfhost/Frontend.wiz`: 19 `List.length` calls inside matching loops (`:474,590,795,921,1099,
  :1828,3560-3603`); hoist the ones in recursive loops (e.g. `np` is recomputed per constructor).
* `selfhost/Backend.wiz:2349-2350,2869-2870`: the final program is a left-nested `List.append` of
  ~10 chunks; fine today (O(k·n), k≈10), but a single accumulator would make the intent clear.
* Parity: the known gaps are tracked with the selfhost work ([21-bootstrap.md](../stages/21-bootstrap.md)); the prelude duplication above is the
  one most likely to hide a difference.

Expected: a few percent of selfcheck and stage-1 (est.; measure `=selfhost` and the fixpoint),
plus fewer duplicated utilities. Do not change `selfhost/*.wiz` while a test reads them
(AGENTS.md).

## 3. Findings by area

| area | elegance | performance | correctness/debt |
|---|---|---|---|
| `lib/Prelude` | `Eq.cast`/`subst` are fine; `List.append`/`length` are structural and used everywhere | `String.append` copies its left side (`Prelude.wiz:136`; cost model at `lib/Text.wiz:9-20`), so `a ++ b` in a loop is quadratic; `Nat.testBit` (`:270`) divides by `2^i` per call | `Nat.beq`/`Nat.lt` are the only comparisons registered as builtins; `Nat.cmp` (`lib/Nat.wiz:167`) builds an `Ordering` and is used by `Ring.Key.cmp` |
| `Nat` | 24 `Eq.trans`/26 `congrArg`; `Eq.via` (`:57`) exists only because `calc` is missing | `Nat.pow`/`Nat.div` are builtins, so they cost nothing at run time; only symbolic statements keep the calls (proof-time conversion) | order is the Boolean `Nat.le = true` encoding (`:32-36`), which makes many proofs `rfl` but makes `omega`-style automation harder (Nat arithmetic automation is an open request) |
| `Word` / `BitVec` / `BitBlast` | BitBlast has the densest chains (`:525-533,680-740`); `Bits.low_shift` is the clearest calc example | all word ops have natives (`lib/Word.wiz:502-618`); `Bits.bit` uses native `Nat.isOdd`/`Nat.div` (`:140-143`), `Bits.low` is structural (proof only) | `Bits.bit` vs `Bits.odd`/`half` duality is documented and bridged; no sorry/axiom |
| `Logic` | `Eq.symm`/`trans`/`congrArg` are `Type`-only (`:197-206`) while `Nat.congrArg` is universe-polymorphic (`lib/Nat.wiz:43`): two copies, one too small | none | `transp` itself is universe-polymorphic, so the fix is local; `Iff`/`propext` are theorem-level (no axiom) |
| `Order` | 31 lines of class/notation; fine | none | `Equiv` exists for `Rat`'s `≈`; adding `Trans` instances (calc branch) is the only work |
| `Int*` | `IntRing` 64 `Eq.trans`/50 `congrArg`, many with explicit `@Eq.trans Int …` (`:96-110`); `Int.beq` is hand-written (`lib/Int.wiz:84-88`) | ring reflection normalises polynomials with sorted-list inserts (`lib/Ring.wiz:81-123`), quadratic in the monomial count; small goals only | `Int`'s pair representation is sound and well documented; `Int.beq`/`Int.lt` are candidates for `deriving BEq`/instances |
| `Rat` | `Q.trans`/`Q.add_congr`/`Q.mul_congr` are 4-deep `Eq.via` chains (`:208-237`), the best calc target after BitVecShift | `q_ring!`/`int_ring!` run at check time; the Ring fast paths (W3) help | `≈` is a setoid over unreduced fractions; `Q.ofEq`/`Q.refl` are fine |
| `Vec` | 13 `Eq.trans`, 16 `congrArg`; induction lemmas (`Vec.get_set`, `Vec.map_map`) | `Vec.length` counts the list (`:77`), used in proofs; `Vec.fromList`/`toList` are the runtime representation | indices are erased, so runtime is a list; the missing Nat div/mod lemmas block the `BitVec.toVec`/`ofVec` round-trips (an open request) |
| `Hdl/*` | bundles/`deriving Bundle`/`Hw.label` are adopted in `hdl/examples/hdl-compose.wiz` and wiz-rv; `Hdl.map`/`natsEq` are leftovers | `HTrie` uses 20 `Nat.testBit` per lookup (`Core.wiz:785-810`); `simFast` is already array-based (`Sim.wiz:362-385`); netlists are `List Nat` (kernel-friendly) | CDC absent (after stack); async reset not supported (an open request); the state is one register per leaf, documented |
| `Hoare*` / `HProp` / seplogic | `Heap.trans` (`HProp.wiz:112`) and `:312` use explicit `@Eq.trans`; `HEquiv` has no `Trans` instance | `Heap` is a function `Nat → Option V`, so a state is symbolic; the tactics do list scans over `starL`, which is the design | `HProp`'s heap is a total function (no partiality), and `Result.Holds`/`Triple` line up; no axioms |
| `Region`/`Result`/`Eff`/`IO` | `Region.wiz:133-215` nests `match` on the handle inside the result match; `Sys.wiz` uses 31 explicit binds | region scopes are `[inline]` and unboxed (`Region.wiz:73-76`); `Eff` interprets a tree (no native path), unused outside `EffHeap` | `Region` has 6 documented lifetime axioms; `Result1` and `Outlives` are the only unsafe surface; `IO1`/`Monad1` are the linear I/O story |
| `Grail` | one-job is in (`Graph.lean:51-56`); `addCheck` and `addCheckImports` (`:102-124`) read and parse the same imports twice | region cache not used (main gap); `-j` default `min(cores,4)` (`Cli.lean:107`) is deliberate: 8 jobs only bought 1.27× (informal) | scheduler is serial for keys but measured at 1.3 s for a 59-node no-op build (informal), not a bottleneck |
| `tower` | 613-line CLI with a few `List.length (String.splitOn …)` idioms (`Cli.wiz:373,490,580`); fine | file sizes are tiny (settings/toolchain files); `git ls-remote` dominates installs | the port follows the Lean reference definition by definition; `tower/tests/pure.wiz` covers settings parsing, while `update`/`install` need git/nix and have no unit tests |
| `selfhost` | embedded prelude (`preludeText`, `Frontend.wiz:4650` at the audit) duplicates `lib/Prelude.wiz`; Feral-style helpers are duplicated in `Backend`/`Frontend` | `Scope.lookup`/`Env.lookup` linear; `Str.ofString` per map op; 19 `List.length` in Frontend loops; non-tail `List.map` over big declaration lists (stack depth is fine at these sizes) | parity gaps tracked with the selfhost work; the embedded prelude is the drift risk (W7) |
| `scry` | the stack's modules are documented and tested; `Store`/`Egraph` are deliberately pure list models | store/e-graph are O(n²); the native columns are already used in CstStore; the Wiz-side copy is 85% of parse time | native store/egraph work is in progress; no axioms beyond the documented natives |
| `wiz-rv`/`wiz-reals`/`wiz-cats` | wiz-rv already derives `Bundle` everywhere (43-field `CoreSt`, `src/Rv/Core.wiz:61-105`) and has no `.1/.2` chains; wiz-reals has 4 `Eq.trans` (`QSeq.wiz:31-35`); wiz-cats carries `Cats/Eq.wiz` because of G1 | wiz-rv's emulator/sim uses `Hdl.Sim`; no list hot spots found; the pinned toolchain (`wiz-toolchain: … master-50cd3e7`) predates the newest lib | wiz-cats `FINDINGS.md` G1–G8 are the best source of library papercuts (G1 fixed by W1/W7; G2 proof-usage, G3 implicit quantities, G4 transp-computed equations remain language-level) |

## 4. Rejected candidates (so they are not re-tried)

* **Map/trie LRAT clause database** (`lib/Sat.wiz:222`): measured *slower* in the kernel (8-bit
  chain 18 s list vs 72 s for a 24-bit trie), and the bottleneck is the evaluator's per-step cost,
  not the list scan. Do not do it without a faster evaluator.
* **Raise grail's `-j` default**: 4 → 8 jobs buys 1.27× on a cold `std` build and raises memory;
  the default stays.
* **`sat_decide_native`**: an axiom whose statement mentions the certificate costs as much as the
  check. Not worth the trust (since added as [28e](../stages/28-solvers.md), opt-in).
* **Blanket `Array` conversion of the kernel context**: `Env`/`TCtx` are cons lists
  (`selfhost/Kernel.wiz:195-199,2002-2052`); `bind` would copy an array on every extension and the
  selfhost kernel is parity-tested, not proved. Use a persistent random-access structure (or
  measure an array first) before touching it.
* **`PMap` as a replacement for native maps**: at 100k operations pmap ~0.31 s vs U64Map ~0.03 s
  and list ~367 s (informal); PMap is the pure/kernel model, not the fast
  compiled map.
* **`native_refl` in the libraries**: only examples use it, with a trust note; keep it that way.

## 5. Measurements wanted

1. **calc**: no timing expectation; record line counts of the four proof files and check time of
   `wiz check` on them before/after (must be neutral).
2. **Grail region cache**: base vs branch, warm `grail build std` and `grail build` of
   `hdl/examples/hdl-compose.wiz`'s package (or `wiz check --region-cache` on hdl-compose), 2–3
   interleaved rounds, wall + peak RSS; plus `--region-stats` hits/misses.
3. **`--split`**: `scripts/fixpoint.sh` stage 1/2 wall on base vs `--split 4/8`, and the built
   binary's run time (the known regression on `compiler-self.wiz`, informal).
4. **Nix store cache**: clean-`HOME` `grail build` of a one-target package, installPhase wall,
   store hits.
5. **HTrie/ring**: `Circuit.netlist` on `hdl/examples/hdl-temporal.wiz` (wall/RSS), and `wiz check` of
   `lib/Rat.wiz`/`lib/IntRing.wiz` for the ring fast paths.
6. **scry**: `scry parse --stats` corpus and the e-graph bench.
7. **selfhost**: `lake test -- '=selfhost'` and selfcheck wall/RSS after the Scope/intern changes.
8. **Logic universes**: none (compile-time only); check that `wiz-cats` can delete `Cats/Eq.wiz`
   and still check.

## 6. Constraints followed

Read-only: no library code was edited, no tests were run, no timing was measured, and no PR was
opened. The only artefact is this note (plus its committed copy under `docs/notes/`). Features not
on master are marked **after stack**; the two toolchain features reused here (`--cache-ro`,
`--region-cache`) are on master, and `--split`/the store cache are explicitly after-stack.
