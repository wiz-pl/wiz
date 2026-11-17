# Taking `.#reference` off the `build` job's critical path

**Status: patch handed over, `ci.yml` not edited here.** Two open PRs own
`.github/workflows/ci.yml`:

* **#452** (`agent/supply-chain`) rewrites the `build` job's Cachix steps (trusted
  cache on master, a separate PR cache) and pins every action SHA;
* **#444** (`integration/e`) adds `check-shards --self-test` to the same job.

Editing `ci.yml` on this branch would conflict with both. Apply instead:

* `0001-ci-reference-off-the-build-critical-path.patch` — against `origin/master`
  (`d7756a37`); applies cleanly with `git apply`.
* `0001-ci-reference-off-the-build-critical-path.on-supply-chain.patch` — the same
  change rebased onto #452's `ci.yml` (both push steps lose `.#reference`).
* `0002-docs-reference-off-the-build-critical-path.patch` — the matching
  `docs/building.md` paragraph. Optional and also touched by #452; drop it if it
  conflicts.

```sh
git apply ci-patches/0001-ci-reference-off-the-build-critical-path.patch
git apply ci-patches/0002-docs-reference-off-the-build-critical-path.patch
```

Nothing in the patches changes gate ordering: the trusted-base step stays exactly
between `nix build` and the Cachix push, and `test` still `needs: build`.

## Measurements (before)

Per-step durations from the PR head runs of #386, #448 and #453, plus the #448 merge
run on master, whose `build` job finished while this was written (`gh run view <id>
--json jobs`). The #386 and #453 merge commits' own CI runs were cancelled 2–9 s in by
the next push (`concurrency`), so the PR head runs are the useful sample there; they are
the same `ci.yml` and runner pool.

| run | PR | build wall | `nix build` (wiz+tests+reference) | trusted-base gate | Cachix push | `check-shards` | fastest shard | slowest shard |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| 44023151097 | #386 | **74.7 min** (4480 s) | 55.2 min (3313 s) | 12.0 min (717 s) | 30 s | 2 s | 2.0 min (117 s) | 74.7 min (4479 s) |
| 44029538719 | #448 | **43.2 min** (2594 s) | 33.4 min (2001 s) | 6.9 min (411 s) | 18 s | 2 s | 2.4 min (143 s) | 86.0 min (5159 s) |
| 44039814067 | #453 | **14.5 min** (872 s) | 0.1 min (7 s) ¹ | 11.2 min (671 s) | 19 s | 3 s | 2.0 min (121 s) | 67.1 min (4025 s) |
| 44052840401 | #448 merge (master) | **80.4 min** (4823 s) | 60.7 min (3641 s) | 11.4 min (681 s) | 19 s | 3 s | shards were still running | — |

¹ #453 only touched `scry/` and `docs/`, so `wiz`/`tests`/`reference` were Cachix hits;
the run still took 14.5 min, almost entirely the trusted-base gate.

The rest of the `build` job is small: checkout 2 s, `setup` 23 s, cache key 1 s,
`check-shards` 3 s, shard matrix 3 s, runtime 1 s, grail index 13 s, package 17 s,
reproducibility 58–111 s, docs examples 1–303 s (303 s on the #448 master run, where its
cache missed) — about **3–8 min** together.

### The reference manual's share, measured cold

The CI step is one `nix build` invocation, so GitHub reports a single duration. Measured
on this machine against the same source (`d7756a37`), split at the two commands the job
runs:

| command | wall | output |
|---|---:|---:|
| `nix build .#wiz .#tests` | 628 s (10.5 min) | 405 + 183 MB |
| `nix build .#reference` | **894 s (14.9 min)** | 66 MB (64.8 MiB NAR) |

`.#reference` alone is longer than the whole compiler + driver build, and 59 % of the
two commands together. The `docs` job's equivalent `wiz doc --lib` pipeline is
667–757 s on CI (runs 44022466727 and 43953131171), so ~11–15 min is the right CI
figure. Its output is the ~64 MiB the push carries.

## The change

The `build` job stops running `nix build .#reference` and stops pushing it. Only the
`docs` job reads `.#reference` (`cp "$ref/index.md" doc-site/docs/reference.md`), only
on a push, and `docs` is not a required check. No shard, and the trusted-base gate,
reads it.

The `docs` job already builds `.#reference` itself when the store path is missing
(`nix build .#reference --no-link --print-out-paths`); after this change that is the
normal path on master, and it runs **concurrently with the test shards** instead of
delaying all of them.

`.#reference` is a separate derivation that depends on `.#wiz`; removing it does not
change `.#wiz` or `.#tests`, so their store paths (and the shards' substitutions) are
byte-identical.

## Determinism: the artefact, not the error order

Error order is not part of the contract for the Lean build. Parallel module builds may
report diagnostics in whatever order their tasks finish; this change adds **no ordering
machinery** and never sorts or re-orders diagnostics.

What must be deterministic is the artefact, and the `build` job keeps its existing
artefact check unchanged in the same place before the shards:

* `scripts/check-repro.sh --json` (the `Reproducibility (two absolute paths)` step) builds
  each corpus program twice under different `PWD`/`HOME`/`TMPDIR`/umask/locale/
  `SOURCE_DATE_EPOCH`/thread count, then compares the bytes and records `sha256` digests;
  diagnostics are deliberately not compared (`scripts/check-repro.sh`, header).
* `scripts/check-repro.sh --compiler` does the same for two full compiler builds, one with
  `LEAN_NUM_THREADS=1` and one with `LEAN_NUM_THREADS=8`, and compares the binaries and
  `.olean` files byte for byte. Thread count is a varied input, not an ordering
  requirement.

CI must not use `--fail-fast` for the build: it changes the **set** of reported errors,
not just their order, so a run would hide failures other than the first. The only
`fail-fast` in the workflow is the test matrix's `fail-fast: false`, which stays; nothing
in this patch touches error reporting.

## What each shard waits for

* **Before:** `changes` → `build` (`nix build` all three outputs → trusted-base gate →
  Cachix push → …) → `test (shard)`.
* **After:** `changes` → `build` (`nix build .#wiz .#tests` → the same trusted-base gate
  → Cachix push of the two paths the shards use → …) → `test (shard)`.

Shards still substitute the exact commit's `.#wiz` and `.#tests` from Cachix, as before.
`.#reference` is no longer in the cache from `build`; the `docs` job builds it from the
cached `.#wiz` on master pushes (and a docs-only push still works the same way).

## Why it is the largest safe win

The reference manual is generated from the whole standard library. Measured cold it is
**894 s locally** (and the `docs` job's same `wiz doc --lib` pipeline is 667–757 s on a
CI runner), for a 66 MB output — so building it in `build` adds roughly **11–15 min to
every run whose `wiz` is rebuilt** (any `lib/` or compiler change, the common case), and
uploads its output to Cachix on every master push, for an output no shard uses.

Estimated after (subtracting the local 894 s from the `nix build` step; the gate, push
and other steps are unchanged):

| run | build wall before | after (est.) |
|---|---:|---:|
| 44023151097 (#386) | 74.7 min | **59.8 min** |
| 44029538719 (#448) | 43.2 min | **28.3 min** |
| 44039814067 (#453, all cached) | 14.5 min | 14.5 min (reference was a cache hit) |
| 44052840401 (#448 merge, master) | **80.4 min** | **65.5 min** |

These are **not** from a triggered run: this branch is not pushed, so the after column is
the local `nix build` decomposition plus the measured step overheads above, not a new
Actions run.

Removing it is strictly subtractive: no new runner, no new cache, no change to the
gate, and the same store paths for the two outputs the shards substitute.

## Rejected

* **Split `wiz` from `tests`.** The shards genuinely need both at once: the test step
  installs `wiz`, `grail` and `tests` side by side and puts `wiz/bin` on `PATH`
  (`Tests/Grail.lean` looks for the binaries beside the driver). Two build jobs would
  duplicate the expensive `wiz` build (or serialise behind it), not shorten it.
* **A separate/larger runner.** The remaining wall time is a cold Lean build of the
  compiler and its prewarmed library cache; a bigger runner would help, but it costs a
  self-hosted machine (docs/ci-runner.md) and is not needed for this win.
* **`--keep-going` / fewer outputs.** `--keep-going` is allowed (it widens the set of
  reported errors; only `--fail-fast`, which narrows it, is out of bounds in CI), but it
  does not shorten the critical path. `.#wiz` and `.#tests` are both read by the shards,
  so neither can be dropped. `--no-link` is already used.
* **Moving the reproducibility/package/doc checks to a parallel job.** Worth ~2–4 min,
  but it changes what "build passed" means for branch protection; left as a follow-up.
