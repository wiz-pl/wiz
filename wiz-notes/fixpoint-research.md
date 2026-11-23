# Bootstrap fixpoint and chain: cost, coverage and stability (2026-11-23)

Status: research, read-only. Worktree `research-fixpoint`, branch
`agent/research-fixpoint`, base local `integration/train12` `f489cc876`. No product or CI
code changed; no build, test or `nix build` was run. Evidence is static reading of the
tree plus the public GitHub Actions API/logs; one section also uses another lane's
uncommitted scratch log (`ci-seed-measure`, attributed where used).

Scope: the three-stage C fixpoint (`scripts/fixpoint.sh`, `fixpoint.yml`, the weekly job
in `ci.yml`), the Nix `wizc` chain (`bootstrap-chain.yml`, `scripts/chain-step-check.sh`,
`nix/bootstrap-chain.nix`) and the Lake seed producer/consumer (`flake.nix`
`withLakeCache`, `scripts/lake-cache.sh`, `ci.yml` `lean`/`lake_seed`).

## 0. Top three findings

1. **The weekly fixpoint is broken at start, not merely skipped.** The only scheduled
   `CI` run in the public API (`43844215169`, 2026-11-16) ran the `fixpoint` job for 42 s
   and died at `scripts/fixpoint.sh: line 58: WIZ_GC_CFLAGS: needs the toolchain
   environment (nix develop)`. The workflow's default shell is
   `nix develop --command bash -eo pipefail {0}` (`ci.yml:87`), and `nix develop
   --command` does not export the `shellHook`'s `WIZ_*` variables — the tree itself says
   so at `ci.yml:618-621` and compensates for `WIZ_LLC` only. The nightly `fixpoint.yml`
   uses the same shell and the same `scripts/fixpoint.sh` invocation (`fixpoint.yml:46,
   108-115`), so it will fail the same way the moment `WIZ_RUNNER_HEAVY` is set, unless
   the self-hosted runner exports `WIZ_*` outside the shellHook (nothing in
   `docs/ci-runner.md` does). All 7 nightly runs so far are a clean skip because the
   variable is unset (`gh variable list` has only `CACHIX_PR_NAME`).
2. **The only fixpoint check that runs on a schedule is the chain's Nix check, and it
   costs 75–93 min per new master commit, not 30 min per mode.** Measured on
   `ubuntu-latest`: self + cross took
   **92.6 min** at `f045e5ea` (2026-11-22), **75.1 min** at `7776f41a` (2026-11-21),
   35.7 min at `18160a94` (2026-11-19), and **57 s** on 2026-11-20 when the commit had
   not moved and every derivation was in the store. Per mode the cost is three `wizc`
   runs at ~7.5 min each plus two static-musl `cc` runs at ~11.5 min each; the static
   `cc` is single-core, so a slow runner scales the wall directly. The docs' model
   ("three self-compiles plus three static cc runs, about twenty minutes", 
   `docs/bootstrap-chain.md:463-465`) is wrong on both the count and the time.
3. **The Lake seed's producer/pure byte equality — the trust foundation of the PR cache —
   is not measured, and the code still says it is.** `docs/building.md:1007-1012` and the
   CHANGELOG were corrected to "expectation, not a measured fact"; but
   `scripts/lake-cache.sh:12-13` still says "byte-identical ... (measured)" and
   `ci.yml:821` still says "byte-identical to the pure build's (the same compile)". The seed-measurement
   lane's scratch run has timings only: pure `nix build .#wiz .#tests` 1258 s, producer
   `withLakeCache empty-lake` 978 s, and **no `cmp` result** — its script printed the
   `lake` output first, so it looked for `...-lake/bin/wiz`, which does not exist. The
   follow-up `cmp-only.sh` was written but no output or `prod-bins/` was saved.

## 1. What is measured today

### 1.1 The three-stage C fixpoint

Two workflows, neither currently producing a fixpoint number:

| site | trigger | command | timeout / memory | last state |
|---|---|---|---|---|
| `ci.yml:1828-1856` `fixpoint` | `schedule` Mondays 02:23 (`ci.yml:36`), or dispatch with `fixpoint=true` | `scripts/fixpoint.sh .lake/fixpoint 2>&1 \| tee fixpoint.log` (`:1851`) | 180 min, no memory preflight | 1 scheduled run (`43844215169`), 42 s, **failed** at `WIZ_GC_CFLAGS`; not in `CI result` |
| `fixpoint.yml` `fixpoint` | nightly 03:41 (`fixpoint.yml:21-22`), or dispatch | `scripts/fixpoint.sh ${args[@]} .lake/fixpoint` (`:112-115`), default 3 stages, `--rc` optional (default off) | 240 min, `WIZ_FIXPOINT_MEM_GIB=7`, `MemAvailable` preflight (`:92-101`) | 7 schedule runs 11-16…11-22; `preflight` success, **`fixpoint` skipped** every time (no `WIZ_RUNNER_HEAVY`) |

What the script checks (`scripts/fixpoint.sh`):

* `:176-177` `lake build wiz Tests.Elab`, then `lake lean scripts/GenSelfhost.lean`
  assembles `compiler.wiz`, `self.wiz` in `OUTDIR`;
* `:181-191` stage 1 is `.lake/build/bin/wiz` compiling `compiler.wiz`, then the
  stage-1 compiler printing `self1.c`;
* `:193-213` each later stage: copy `self{k-1}.c` to `cc/wizc.c` (fixed basename),
  `cc -O2 -w -I selfhost $WIZ_GC_CFLAGS ... -o stage{k}`, then `stage{k}` prints
  `self{k}.c`;
* `:221-243` the verdict is `cmp self1.c self{k}.c` for every k; `:248-257` prints the
  stage executables but **does not include them in the verdict**;
* `--stages 2` is allowed (`:17,50-51`) and is the old "one coincident round" check.

The only current numbers are the 2026-11-16 two-stage measurement in
`docs/bootstrap-chain.md:580-607`: Lean host 199–204 s, stage-1 self-compile 40–45 s,
`cc` 150–175 s, stage-2 self-compile **825–834 s**, peak **6.3 GiB**, 6/6 artifacts
byte-identical under two environments. A three-stage run adds another ~150–175 s `cc`
and ~825–834 s self-compile, so ~38–40 min of fixpoint work plus the Lean build. No
three-stage number exists from CI. The docs' "6 GiB" at `docs/building.md:1394-1397` is
stale against the 7 GiB declaration in `fixpoint.yml:53` and the 6.3 GiB peak.

Cache: `fixpoint.yml` restores `.lake` only (`:102-107`); the weekly `ci.yml` job restores
`.lake` **and** `~/.cache/wiz` (`:1842-1849`). The latter is the Wiz elaboration cache,
which is unauthenticated (the shared note `cache-trust-boundary.md` §1); the weekly stage 1 is
therefore not necessarily a cold, trusted host build, while the nightly heavy job's
`.lake`-only cache is less exposed. Both jobs key the cache on
`hashFiles('lean-toolchain','lake-manifest.json')` plus
`hashFiles('lakefile.lean','**/*.lean','selfhost/*.wiz','lib/*.wiz')`.

### 1.2 The `wizc` chain

`bootstrap-chain.yml` has two jobs:

* **`release`** (`:54-121`), on `workflow_run` of `CI` on a master push, including a
  failed CI run (`conclusion != 'cancelled' && != 'skipped'`, `:58-63`):
  `nix build .#wizc-release .#wizc .#wizc-seed -L --no-link` (`:78`), then
  `scripts/check-wizc-release.sh --tarball "$rel/wizc-$sys.tar.gz" --seed "$seed"`
  (`:104-106`), then `cachix push` of the three paths (`:115-116`), artifact
  `wizc-release-SHA` for 14 days (`:117-121`). Timeout 90 min.
* **`chain`** (`:123-199`), nightly 05:17 and dispatch, never on `workflow_run`:
  `scripts/chain-step-check.sh --out .scratch/self` (self mode, `:141-146`), then with
  `--pred <previous-night commit> --pred-tarball prev/wizc-$SYS.tar.gz` (cross mode,
  `:191-199`); keeps `wizc-nightly` for 90 days and pushes the FOD
  `wizc-$SYS-$COMMIT.tar.gz` plus the `.scratch/self/*` and `.scratch/cross/*` links to
  Cachix (`:200-219`). Timeout 180 min.

`scripts/chain-step-check.sh` builds path A (`seed`, `lean-release`) and path B
(`pred`, `step`, `c1`, `stage1`, `release-b`) and compares (`:94-115`): in self mode
`pred wizc = A wizc`, `c1 = seed.c`, `c2 = seed.c`, `stage1 wizc = A wizc`,
`B wizc = A wizc`, `B tarball = A tarball`; in cross mode `c1` and `stage1 wizc` are
`info` only, `c2`/`wizc`/tarball must match. `nix/bootstrap-chain.nix` defines the
pieces: `seed` (`:65-91`), `stage` (`:34-57`), `fixpoint` (`:95-105`), `step` (`:113-124`),
`fromLean` (`:124`), `release` (`:131-153`), `fetchToolchain` (`:160-178`).

Measured Actions durations (public API, job start/completed):

| run | date | commit | job | duration | note |
|---|---|---|---:|---:|---|
| `45026891171` | 11-22 | `f045e5ea` | chain self+cross | **92.6 min** | self: c1 7m31, stage1 19m01, fixpoint 18m55; cross: c1 7m32, stage1 19m12, fixpoint 19m12; PASS |
| `44908915530` | 11-21 | `7776f41a` | chain self+cross | 75.1 min | PASS |
| `44543486335` | 11-19 | `18160a94` | chain self+cross | 35.7 min | PASS |
| `44749181628` | 11-20 | `18160a94` | chain self+cross | **57 s** | same commit as the previous night; all store hits |
| `44930396001` | 11-21 | `f32370e2` | release | 22.1 min | seed 6m49, `wizc-fixpoint` 14m38, gate 19 s |
| `44943590980` | 11-21 | `f045e5ea` | release | 47 s | substitution |
| `44505789830` | 11-19 | `18160a94` | release | 25.4 min | built |
| `44380549200` | 11-18 | `4ad29792` | release | 14.7 min | built |

The per-mode structure in `45026891171`: `c1` is one static-`wizc` run (7m31), each
`stage1`/`fixpoint` derivation is one static `cc` plus one `wizc` run (~19 min). That is
**three `wizc` runs and two static `cc` runs per mode**, not "three self-compiles plus
three static cc runs"; the release's own `wizc-fixpoint` is a third `cc`, but that is the
`release` job, not the chain link.

### 1.3 The Lake seed (producer/pure byte equality)

The flake has three relevant functions:

* `emptyLake` (`flake.nix:59-64`) — an empty `.lake/build` plus a `toolchain` stamp;
* `withLakeCache pkgs lakeCache` (`:74`, `:1254-1257`) — the same packages built from a
  prebuilt `.lake`; `cachedUnwrapped` (`:142-185`) copies the seed's `.lake`, runs
  `lake build wiz grail tests`, installs `bin/` in `out` and the next seed in `lake`;
* `lake-seed = (packagesWith pkgs (emptyLake pkgs)).unwrapped.lake` (`:1235`).

The trust direction (`scripts/lake-cache.sh:4-24`, `ci.yml:816-833`): a master push's
`lake_seed` job builds `.#lake-seed` from `empty-lake` (a cold compile inside the Nix
sandbox) and publishes it to the trusted Cachix; a PR restores its own untrusted
subset cache first, otherwise names its base commit's `.#lake-seed` and substitutes it
(`scripts/lake-cache.sh:109-138`), then builds `withLakeCache <seed>`. The producer's
`out/bin` is claimed to be byte-identical to the pure `.#unwrapped/bin`; that is what
would make the seed a trustworthy substitute for the compile.

What is actually run:

* `lake_seed` (`ci.yml:834-879`): `nix build .#lake-seed --no-link --print-out-paths`
  and `cachix push`, with a substitutability check; **no `cmp`**.
* `lean` (`ci.yml:509-545`): pure `nix build .#wiz .#tests` on a push; on a PR,
  `scripts/lake-cache.sh choose` / `build` / `save`.
* No CI job compares the producer's `bin/` with the pure build. `docs/building.md` says
  so; `scripts/lake-cache.sh:12-13` still says "(measured)" and `ci.yml:821` still
  asserts the equality.

The seed-measurement lane's scratch run (not my measurement; its uncommitted
scratch log) has:

```
PURE_SECONDS=1258       # nix build .#wiz .#tests, 6-core node, 21 min
PRODUCER_SECONDS=978    # withLakeCache empty-lake, 16.3 min
PRODUCER_OUT=/nix/store/...-wiz-unwrapped-lake-cache-0.1.0-lake   # actually the `lake` output
PRODUCER_LAKE=/nix/store/...-wiz-unwrapped-lake-cache-0.1.0       # actually the `out` output
```

`nix build --print-out-paths` printed the `-lake` output first (the script assumed the
`out` output was first), so step (3) looked for `$prod/bin/wiz` in the `lake` output and stopped
with `No such file or directory`. `cmp-only.sh` (written 10:11) uses the correct
`prod=...0.1.0` path, but its `prod-bins/` is empty and no `cmp-*.err` or log was saved.
**The equality is still unmeasured.** The lane also dropped the warm-build step
(`scripts/lake-cache.sh save` then `build <seed> wiz tests`), so there is no
`WARM_SECONDS` either; the earlier `ci-iteration` measurement that had that step timed
out in its first cold build at 341/629 modules (`ci-iteration.md:53-131`).

Cold/warm baseline for the compiler build itself: `ci-profile.md`'s 13-run table has
three cold `build` jobs at **44.1 / 49.1 / 49.6 min** and the other ten at **2.3–22.1
min** (Cachix substitution). The local 2026-11-17 `lake build wiz tests grail` was
**1680 s cold** on a loaded 32-core host and **12 s** with the Lake artifact cache warm
(`docs/building.md:574-586`); the fixpoint's `lake build wiz Tests.Elab` is the same
variable, so a cold `.lake` can add ~15–30 min to a fixpoint run and a restored `.lake`
makes its wall number ambiguous. The `lake_seed` producer is a second cold compile on
every master push (local 16.3 min; no CI number yet).

### 1.4 Adjacent checks that are not the chain

* `scripts/repro-fixpoint.sh`: two copies of the checkout under different PWD/TMPDIR/
  HOME/locale/umask/epoch/parallelism, `--stages 2` by default; not wired into any
  workflow. The 2026-11-16 run was 6/6 byte-identical (`docs/bootstrap-chain.md:580-607`).
* `repro.yml`: `scripts/check-repro.sh --compiler` nightly on the heavy runner; skipped
  for the same missing `WIZ_RUNNER_HEAVY`.
* `.#release-bin`'s `doCheck` rebuilds the binary release tarball twice and compares
  (`wiz-notes/nix-artifacts.md:74-87`); that is the user-facing release, not
  `wizc-release` and not a chain link.
* `scripts/check-wizc-release.sh`: the packed `wizc` on a frozen fixture with a one-byte
  control, plus the `scripts/wizc-seed.json` pin (`:1-26`); run by the `release` job,
  not by the `chain` job.

### 1.5 One-table summary

| what | runs today? | measured number | where |
|---|---|---|---|
| three-stage `scripts/fixpoint.sh` | no (weekly broken; nightly skipped) | 2-stage 6/6 reproducible; 3-stage ~38–40 min model | `docs/bootstrap-chain.md:580-607` |
| chain self+cross | yes, nightly | 35.7–92.6 min on a new commit; 57 s on a repeat | Actions runs above |
| `wizc-release` build | yes, per master CI | 14.7–25.4 min; 47 s substitution | Actions runs above |
| pure compiler build | yes, per master CI | cold 44.1–49.6 min (3/13); warm 2.3–22.1 min (10/13) | `ci-profile.md` |
| Lake seed producer | yes, per master push with `code` | no CI number; local 16.3 min | `ci.yml:834-879`; scratch |
| producer/pure `cmp` | **no** | none | — |
| seed warm PR build | **no** | none | — |
| `repro-fixpoint.sh` | no (manual) | 6/6 on 11-16 | `docs/bootstrap-chain.md:580-607` |

## 2. Failure modes

### 2.1 Prelude unification and roadmap risk R1

There are two preludes: `lib/Prelude.wiz` (1,574 lines, what the host compiles) and the
selfhost's embedded copy `preludeText` in `selfhost/Frontend.wiz:10151` (352 decoded
lines). `scripts/check-prelude-drift.py` measures the divergence (coverage, origin,
staleness; 8 reviewed gaps, 15 embedded-only names). Workstream A1
(`roadmap-2026-11-18.md:12-46`) would make the selfhost load the real prelude, either by
reading `lib/Prelude.wiz` from source or by *generating* the embedded copy with a
checked-in hash. Roadmap risk R1 (`roadmap/program-next.md:209`) is that
`--prelude-from-roots` / `agent/sh-backend-prelude` never lands, so the divergence stays;
`wiz-notes/extensibility.md:397,449` records the same dependency.

What this does to the fixpoint/chain:

* **The seed pin moves.** `self.wiz` is the concatenation of `compilerFiles`
  (`Wiz/Selfhost.lean:149-153`), which includes `selfhost/Frontend.wiz`; any edit to
  `preludeText` changes `self.wiz`, hence `seed.c`/`C*`, the release tarball and
  `scripts/wizc-seed.json`'s first entry. That is a reviewed pin update, not a
  regression, but it is the largest single source of seed churn on the roadmap.
* **The chain's "one input, one file" assumption is at risk.** `nix/bootstrap-chain.nix`
  builds `seed` from `selfhostSrc`, which `flake.nix:1218-1222` defines as only
  `selfhost/`; `step` copies `selfWiz` to `run/input.wiz` and runs `wizc` with **no
  `-I`** (`:111-124`). If A1 changes the selfhost to *read* `lib/Prelude.wiz` (and its
  imports) instead of embedding the text, `self.wiz` alone is not a complete input:
  `run/input.wiz` will not resolve the import, and `bootstrapChain` must ship `lib/` and
  pass `-I`, and `wizc-seed.json` must pin the prelude files too. If A1 *generates* the
  embedded copy (the safer variant), the chain remains single-input and only the hash
  moves.
* **The fixpoint verdict should still hold** if the prelude is expressible in the
  selfhost's language; the risk is that A1 lands a `lib/Prelude.wiz` feature the
  selfhost cannot compile, so the self-compile fails until parity. That is a real
  regression signal, not a false alarm; run `scripts/fixpoint.sh` plus chain self mode
  on the A1 branch before merging.

### 2.2 Cache trust

Covered:

* PR writes cannot reach the trusted Cachix: a PR gets no `CACHIX_AUTH_TOKEN`
  (`ci.yml:452-455`), and `CACHIX_PR_AUTH_TOKEN` has Read, not Write, on
  `badlydrawnwizards` (`docs/ci-runner.md:295-308`).
* The trusted Lake seed is a store path named by the **base commit's** flake, not an
  Actions tarball; `lake-cache.sh trusted` reads the path from the cache with
  `nix path-info --store` + `nix copy --from`, never builds it (`:109-138`).
* `withLakeCache` refuses a seed whose `toolchain` stamp is not the current
  `lean-toolchain` (`flake.nix:145-149`), and `lake-cache.sh build` falls back to
  `empty-lake` on a stamp mismatch (`:170-175`).
* `fetchToolchain` is an FOD; Nix checks its sha256 whichever source answers
  (`nix/bootstrap-chain.nix:160-178`).

Not covered:

* **One builder, no attestation.** `docs/bootstrap-chain.md:459-465` says a release is
  published "only when both agree"; no local builder exists (P5 open), no attestation is
  produced, and `bootstrap-chain.yml` has no second builder. The nightly chain is a
  single-builder self-consistency check, not Wheeler DDC.
* **The predecessor artifact is unauthenticated.** The `chain` job picks the newest
  unexpired `wizc-nightly` artifact from master (`bootstrap-chain.yml:165-190`), computes
  its hash from the file (`scripts/chain-step-check.sh:81-84`) and registers it under the
  FOD name. There is no expected hash and no signature; a replaced/poisoned artifact
  passes if it still compiles `self.wiz` to the same `C*` (the quine hole). The GitHub
  release `toolchain-COMMIT` that `fetchToolchain` names does not exist; only 14/90-day
  Actions artifacts and unpinned Cachix paths do.
* **No `cachix pin`.** `docs/bootstrap-chain.md:533-535` requires every release FOD to be
  pinned in Cachix; neither `bootstrap-chain.yml`'s push (`:115-116`, `:213-219`) nor any
  other workflow runs `cachix pin`. Retention is therefore best-effort GC, not the
  documented "kept forever".
* **The `release` job publishes on a failed CI run.** `:58-63` accepts
  `conclusion == failure`; a red master commit still pushes `wizc-release`, `wizc` and
  `wizc-seed` to the trusted cache. The pin gate in the release job prevents a *stale
  seed pin* release, but not a release from a commit whose `selfhost/Tables.wiz` is
  stale (the selfhost byte-compare test lives in `Tests/Groups/SelfHost.lean:4633-4639`
  and the release job does not run it).
* **The seed pin is not checked by the chain job.** `scripts/wizc-seed.json` is checked
  by `check-wizc-release.sh` in `release`, not by `chain-step-check.sh`; a nightly
  `wizc-nightly` can be built from a `self.wiz` that does not match the pin and still be
  pushed to Cachix.
* **The seed equality itself.** The whole PR-cache trust argument rests on
  `producer out/bin == pure unwrapped/bin`, which is an expectation, not a measurement
  (§1.3). Until the `cmp` lands, a PR's seeded build is a different derivation that is
  *believed* to be the same compile.
* **The weekly fixpoint's elaboration cache.** `~/.cache/wiz` is restored from an
  Actions cache and is not authenticated (the shared note `cache-trust-boundary.md`); the
  nightly heavy job does not restore it. A stale/forged entry in the weekly job's stage 1
  is a low-probability but uncontrolled input.

### 2.3 Toolchain drift

* `flake.lock` pins nixpkgs; `lean-toolchain` pins Lean; `flake.nix:104-109` asserts the
  nixpkgs Lean version and the GMP version/source hash. That is the strong guard.
* The Lake seed's `toolchain` stamp is only the **text** of `lean-toolchain`
  (`flake.nix:145-149`, `lake-cache.sh:170-175`). A `flake.lock` update that changes
  nixpkgs' Lean build without changing the version string is caught by the seed's
  different derivation path (the base commit's `.#lake-seed`) and the CI subset key
  (`flake.lock` + `lean-toolchain`, `scripts/ci.py:803-806`), not by the stamp. Do not rely on
  the stamp alone.
* The chain release's bytes are a function of the source **and nixpkgs' C compiler**
  (`pkgsStatic.stdenv.cc`), but `MANIFEST` records only `version`, `system`, `mode`,
  `wizc-sha256` and `fixpoint-c-sha256` (`nix/bootstrap-chain.nix:141-148`). A
  `nix flake update` changes the tarball hash while both self and cross modes still
  pass, because both sides use the new cc. There is no pinned expected tarball hash and
  no attestation, so a cc/nixpkgs drift is invisible unless someone records the lock
  rev next to the hash.
* `wizc-seed.json` pins `self.wiz`, `selfhost/Tables.wiz`, `selfhost/rt.c`,
  `Wiz/Selfhost.lean` and `Wiz/Version.lean`. A change to any of them moves the seed;
  `Wiz/Version.lean` in particular changes the assembled `self.wiz` via
  `toolchainId` (`Wiz/Selfhost.lean:155-159`). That is expected, but it means "the seed
  did not move" is a statement about a narrow set of files, not about the whole tree.
* `selfhost/Tables.wiz` is generated out of band (`scripts/GenSelfhostTables.lean`) and
  consumed as checked-in bytes (`nix/bootstrap-chain.nix:65-91`). A grammar change that
  forgets to regenerate it is caught by the selfhost shard, not by the chain; the
  release job runs even on a failed CI, so a stale table can be published.

### 2.4 aarch64

* `flake.nix:22` evaluates `aarch64-linux`, and `releaseInterp` has an aarch64 branch
  (`:901-904`) for the user-facing release. The **chain** is x86_64-only in practice:
  `bootstrap-chain.yml` runs `ubuntu-latest` (`:64`, `:126`), `wizc-release` names
  `wizc-${system}.tar.gz` (`nix/bootstrap-chain.nix:131-153`), and `fetchToolchain`
  defaults to `pkgs.stdenv.hostPlatform.system` (`:160`). No aarch64 `wizc`/seed is
  built or published.
* Cachix holds x86_64 builds only (`docs/ci-runner.md:320-326`); an aarch64 consumer
  would build the whole chain cold, including `pkgsStatic.boehmgc`, which is not in the
  binary cache even on x86_64 (`docs/bootstrap-chain.md:172-178`).
* The proposed pin format `wizc-toolchain.json` has one `system` and one `hash`
  (`docs/bootstrap-chain.md:324-338`), so it cannot express both architectures; a
  commit that wants aarch64 needs a second pin file or a per-system map, neither of
  which exists.
* The fixpoint's C comparison is architecture-independent in principle (`cmp self1.c`
  is text), but the stage executables and the 6.3 GiB peak are not measured on aarch64;
  `pkgsStatic` and the RC runtime may behave differently. Do not add aarch64 to the
  monthly plan until a release/cache exists; the first question is a one-off "does
  aarch64 print the same `seed.c` as x86_64", not a chain job.

### 2.5 Timeouts and the "3 h" risks

| job | timeout | measured | headroom | risk |
|---|---:|---:|---:|---|
| `ci.yml` weekly fixpoint | 180 min | never completed; model ~40–70 min | — | broken at start; a contended node at 4–7x slowdown could hit 180 |
| `fixpoint.yml` nightly | 240 min | skipped; model ~40–70 min | — | 7 GiB is the binding constraint (6.3 GiB peak); a 6x slowdown hits 240 |
| `bootstrap-chain.yml` chain | 180 min | 92.6 min worst in sample | 87 min (1.9x) | single-core static cc; at 2x slower the job is ~150–185 min depending on how much of the setup/cache also scales, so the 180 min is only ~1.9x headroom |
| `bootstrap-chain.yml` release | 90 min | 25.4 min worst | 64 min (3.5x) | a cold Lean host + seed + fixpoint could approach 90 |
| seed measurement (manual) | 3 h (job 5115) | killed at 3 h, 341/629 modules | — | the real 3 h casualty: a contended node with 99% `/tmp`, not a CI job |

The 3 h issue is not the fixpoint's 240 min; it is the **measurement** run on a
contended node. `ci-iteration.md:96-109` records the Slurm node (6 cores, 11 GiB free on
`/tmp`, ~1.9 modules/min vs CI's 13–14 modules/min (44–49 min for 629), so the 3 h
number is a node problem, not a fixpoint cost. Do not resize the fixpoint job from it.
The chain's 180 min is the only timeout that is close to a plausible bad run; add a
per-mode timeout before lowering the job timeout.

## 3. Minimal measurement plan

Run **monthly**, on a quiet machine (`perf-run --batch` or the same `ubuntu-latest` class
as CI), not nightly and not on a contended Slurm node. One run per month is enough: the
seed only moves on `selfhost/`, `Wiz/Selfhost.lean`, `Wiz/Version.lean` or a prelude
change, and the chain's self/cross is already nightly.

| # | what | exact command | gate? | cost |
|---|---|---|---|---|
| M1 | three-stage C fixpoint | source the machine's toolchain env (the `wiz-env.sh` local runs use) or enter `nix develop` and export `WIZ_CFLAGS`/`WIZ_LDFLAGS`/`WIZ_LLC`/`WIZ_GC_CFLAGS`/`WIZ_GC_LDFLAGS`, then `scripts/fixpoint.sh --stages 3 --keep .lake/fixpoint` | **yes**: exit 0 and `FIXPOINT`; record `timings.tsv`, `md5`, `self*.c` sizes | ~40–70 min, 7 GiB |
| M2 | chain self, then cross if a previous artifact survives | `scripts/chain-step-check.sh --commit <tip> --out .scratch/chain-self`; then `--pred <prev> --pred-tarball <file>` | **yes**: `chain-step-check: PASS`; record the tarball sha and per-step times | ~46 min/mode |
| M3 | seed producer/pure equality + warm build | `nix build .#unwrapped` (pure); `nix build --impure --expr '(f.lib."x86_64-linux".withLakeCache f.lib."x86_64-linux"."empty-lake").unwrapped'`; `cmp` each `out/bin/{wiz,grail,tests}`; then `scripts/lake-cache.sh save <producer.lake> <seed>` and `scripts/lake-cache.sh build <seed> wiz tests unwrapped.lake` | **yes**: the `cmp`; record `PURE_SECONDS`/`PRODUCER_SECONDS`/`WARM_SECONDS`, do **not** gate the times | ~40–60 min warm store |
| M4 | seed pin and Tables freshness | `nix build .#wizc-seed --no-link`; `scripts/check-wizc-release.sh --tarball <tarball> --seed <seed>`; `lake build genSelfhostTables` + `git diff --exit-code selfhost/Tables.wiz` (in a scratch copy) | **review**, not red: a changed pin/table is a deliberate update; a missing gate is a finding | minutes |
| M5 | drift record | `nix flake metadata --json` (nixpkgs narHash), `cat lean-toolchain`, `nix --version`, `cc --version`, `stat -c %s` of `self.wiz`/`self.c`, tarball sha | no gate; attach to M1–M3 | seconds |

Quarterly, not monthly:

* `scripts/repro-fixpoint.sh --stages 3 --keep` (two builds, 7 GiB, not in CI): the only
  check that the fixpoint is reproducible across environments; the 2026-11-16 run was
  2-stage/6-of-6.
* `scripts/check-wizc-release.sh --self-test`, `scripts/check-toolchain-pin.py
  --self-test`; no build needed.

### What to gate

* M1's exit 0 (the C fixpoint) — the one claim the three-stage job exists for.
* M2's `chain-step-check: PASS` (self, or self+cross when the artifact exists).
* M3's `cmp` equality — the seed's trust foundation.
* A changed M4 pin/table is a **reviewed change**, not a red job; a mismatch between the
  pin and the seed is a finding, not a test failure to route around.

### What to ignore

* Absolute wall times from any non-`perf-run` machine. The 341/629 (3 h) number is a
  contended node; the 1258/978 s seed numbers are one 6-core node and are not a PR
  benefit. Do not quote a producer/pure ratio as a speedup.
* `--stages 2` as a "fixpoint" (one coincident round); it is the old check.
* Cross-mode `c1` differences (info by design) and the word "DDC" for self/cross
  (convergence, not Wheeler DDC).
* A single chain run with a Cachix miss; classify cache hit/miss first.
* The historical `release` failures on commits whose flake had no `wizc-release`
  attribute (`44360902612`, `44355887264`, 26/22 s) — a rollout artifact, not a current
  instability.
* aarch64 until a release/cache/pin format exists.
* The `~/.cache/wiz` hit/miss as a correctness signal; use a fresh cache for M1 if the
  number is meant to be a cold host build.

## 4. Recommendation for the fixpoint job's cost and stability

1. **Fix the `WIZ_*` export before any further measurement.** Today both fixpoint
   workflows either skip (nightly) or die in 42 s (weekly). The smallest safe change is
   to `export` the five variables in `flake.nix`'s `shellHook` (`:1298-1303`), or to set
   them explicitly in the fixpoint run step, or to teach `scripts/fixpoint.sh` to derive
   `cc`/GMP/LLC paths the way `ci.yml:618-621` derives `WIZ_LLC`. Do not claim a
   fixpoint time until this is fixed; a "skip" is not a pass.
2. **Make the deep fixpoint monthly, not weekly.** Keep the nightly heavy
   `fixpoint.yml` as opt-in on `WIZ_RUNNER_HEAVY`; move the `ci.yml` weekly job to
   monthly (or `selfhost/`-only). The chain already runs a daily RC self/cross; the
   three-stage collector fixpoint is a monthly deep check, and a weekly job nobody gates
   on only adds runner minutes and a false sense of coverage.
3. **Keep 7 GiB, and add the memory preflight to the weekly job too.** Stage 2 peaked at
   6.3 GiB (`docs/bootstrap-chain.md:603-607`); `docs/building.md`'s 6 GiB is stale.
   The nightly job checks `MemAvailable`; the weekly `ci.yml` job does not. On
   `ubuntu-latest` (16 GB) this is usually fine, but a 7 GiB cgroup or a shared runner is
   not.
4. **Keep the timeouts, but add a per-mode timeout in the chain.** 240 min for the
   fixpoint and 180 min for the chain are generous against the measured 40–93 min; the
   risk is one hung mode consuming both. A `timeout 70m` around each
   `scripts/chain-step-check.sh` call (or a `timeout` inside it) preserves the cross
   mode. Do not lower the job timeout from the 3 h seed-measurement number; that was a
   contended node.
5. **Take the Actions cache and the unauthenticated elaboration cache out of the
   fixpoint's trust path, or at least record them.** Prefer the Nix-built
   `packages.wiz`/`grail` (the chain's host) over a restored `.lake`, or run M1 with a
   fresh `~/.cache/wiz` and a cold `.lake` and record the hit/miss. The current weekly
   job's `~/.cache/wiz` is an unauthenticated input; the nightly job's `.lake`-only
   cache is better but still makes "cold" ambiguous.
6. **Make the chain a real pin or stop calling it one.** If the chain is meant to be
   pinned by `wizc-toolchain.json`, add `cachix pin` for every pushed FOD/release and
   publish the `toolchain-COMMIT` release with the two-builder attestation (P5/P7). If
   that is not this quarter, document it as a nightly self-consistency check and do not
   rely on the 14/90-day artifacts for reproducibility. In either case, run
   `check-wizc-release.sh` (the seed pin) in the `chain` job too, not only in `release`.
7. **Measure the seed equality once, then decide.** Fix the path-order bug (read each
   output with `nix eval --raw`/`nix path-info` by attribute, not `sed -n 1p`), run the
   `cmp` and the warm build, and only then change the "(measured)" comments or the docs.
   The seed's benefit is a PR-latency claim; the equality is a trust claim. Do not
   conflate them. If the `cmp` fails, the seed must not be used for PRs at all until the
   difference is understood.
8. **Do not add aarch64 or a prelude-unification experiment to the monthly job yet.**
   aarch64 has no release, cache or pin; A1 should be tested on its own branch with M1 +
   M2 self mode (and the chain's input set extended if it reads `lib/Prelude.wiz`).

## 5. Evidence and honesty ledger

* **Read (static):** `docs/bootstrap-chain.md`, `docs/building.md` ("Continuous
  integration", "Build time and memory", the fixpoint section),
  `docs/ci-runner.md` ("aarch64", trust direction), `.github/workflows/fixpoint.yml`,
  `.github/workflows/bootstrap-chain.yml`, `.github/workflows/ci.yml` (the `lean`,
  `lake_seed`, `fixpoint` and `result` jobs), `flake.nix` (`pureUnwrapped`,
  `cachedUnwrapped`, `release-unwrapped`, `bootstrapChain`, `withLakeCache`),
  `nix/bootstrap-chain.nix`, `scripts/fixpoint.sh`, `scripts/chain-step-check.sh`,
  `scripts/chain-step.nix`, `scripts/check-wizc-release.sh`, `scripts/lake-cache.sh`,
  `scripts/repro-fixpoint.sh`, `scripts/wizc-seed.json`, `scripts/ci.py`,
  `Wiz/Selfhost.lean`, `selfhost/Frontend.wiz`; notes:
  `ci-iteration.md`, `ci-profile.md`, `bootstrap-fixity.md`, `bootstrap-chain-root.md`,
  `cache-trust-boundary.md`, `cache-invariants.md`, `release-determinism.md`,
  `roadmap-2026-11-18.md`, `roadmap/program-next.md`, `extensibility.md`,
  `wiz-notes/nix-artifacts.md`.
* **Actions data (public API):** `gh run list`, `gh run view --json jobs`, `gh run view
  --log` for `43844215169`, `45019946693`, `45026891171`, `44908915530`,
  `44543486335`, `44749181628`, `44930396001`, `44943590980`, `44505789830`,
  `44380549200`, `44360902612`, `44355887264`; `gh variable list`.
  The 11-16 `CI` schedule failure is line
  `scripts/fixpoint.sh: line 58: WIZ_GC_CFLAGS: needs the toolchain environment (nix
  develop)`; `ci.yml:618` explains why.
* **Not run by me:** any `nix build`, `lake build`, `scripts/fixpoint.sh`,
  `scripts/chain-step-check.sh`, `scripts/repro-fixpoint.sh`, `tests`, or `grail`.
  No local store paths from the seed-measurement lane exist on this machine, so I could
  not run its `cmp-only.sh`.
* **Not measured by me:** the seed equality, the warm PR build, the aarch64 `C*` and
  peak, the chain on a self-hosted runner. The 1258/978 s numbers are the other lane's
  scratch log, not a controlled measurement, and the producer/pure ratio is not a PR
  speedup.
* **Unverified:** whether `nix develop --command` exports `WIZ_*` on the self-hosted
  runner image (docs/ci-runner.md does not export them; the weekly log proves the
  GitHub-hosted path does not). That the 2026-11-23 02:23 `ci.yml` schedule did not run
  is observed in the API, but the cause (schedule delay vs disabled trigger) was not
  investigated.
* **No product/CI code was changed by this lane.** The branch carries only this note;
  the shared copy is in the shared notes directory.
