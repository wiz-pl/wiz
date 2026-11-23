# A self-hosted CI runner

CI runs on GitHub's `ubuntu-latest` runners. The heavy test shards (those with
`"heavy": true` in `.github/test-shards.json`: `selfhost-1` … `selfhost-4`, `hdl` and
`semantics`) can run on a machine of our own instead. Nothing changes until the
repository variable `WIZ_RUNNER_HEAVY` is set; unsetting it switches back.

This repository is **public**: anyone can open a pull request, and a workflow run on a
self-hosted runner executes that pull request's code on the machine. So:

* CI never sends a pull request **from a fork** to the self-hosted runner: the test job's
  `runs-on` (`.github/workflows/ci.yml`) picks `WIZ_RUNNER_HEAVY` only for pushes,
  merge-queue runs, manual runs and pull requests whose branch is in this repository
  (`github.event.pull_request.head.repo.full_name == github.repository`); a fork's pull
  request runs those shards on `ubuntu-latest`. Only collaborators can push branches here.
* The runner is **ephemeral**: it takes one job and is then thrown away, with a fresh
  container or VM for the next job, so one job can't leave anything behind for the next
  (a planted binary in `/tmp`, a poisoned cache, a credential).
* Repository settings (Settings → Actions → General): set "Require approval for all
  outside collaborators", so a fork pull request's workflows wait until a maintainer
  approves them, and keep the default `GITHUB_TOKEN` permissions read-only (the workflow
  asks for `contents: read`).
* The image and the host hold no secret of the repository's (the host has only the
  token it registers runners with, outside the containers), and the machine is on a
  network where it can reach nothing private (a guest VLAN, or a VM with only outbound
  internet). A job sees the Cachix auth token while it runs, as on GitHub's runners;
  that is why only this repository's code may run there.

## The CI job graph

`.github/workflows/ci.yml` is split by the repository subsets in
`.github/repo-subsets.json` (`scripts/repo-subsets.py`). The `changes` job publishes a
`subset_<name>` boolean per subset; `CI result` requires a job exactly when that job's
`if:` fires, so a skipped job and an unneeded job are the same thing.

| job | subset | runs when |
|---|---|---|
| `changes` | all (path filters) | every run but the weekly schedule |
| `docs style` | docs (static checks) | every run |
| `name collisions (reachable)` | docs/lean (static) | every run |
| `prelude drift` | docs/wizlib (static) | every run |
| `docs examples` | docs | a docs-only pull request |
| `source tarball` | release artifacts | `code` |
| `attestation verifier` | scripts/attest | every run |
| `lean` | lean (the Nix build of `wiz`/`tests`) | `code`; it emits the shard matrix and the store paths every shard substitutes |
| `lake seed` | lean (the trusted cold seed) | a push to master with `code` |
| `trust ledger` | wizlib (it walks `lib/`) | `code` |
| `STC metatheory` | `STC.lean`, `STC/` | `stc` or `code` |
| `tests` | tests (the shard matrix) | `shards` is not empty |
| `wasm modules` | web (the Wasm page modules) | `web` |
| `web` | web (browser-free tests) | `web` |
| `docs` | docs (the published site) | a push |
| `deploy docs to Pages` | docs | a push |
| `packages` | packages (`scry/`, `hdl/`, `tower/`) | `subset_packages` |
| `runtime` | runtime (`runtime/`, `c/`) | `subset_runtime` |
| `CI result` | all | every run but the weekly schedule |
| `bootstrap fixpoint` | none (schedule/dispatch) | the schedule or the `fixpoint` input |

A path that matches several subsets sets all of them. A path no subset claims
(`scripts/`, `flake.*`, `selfhost/`, ...) or any `.github/` edit sets every subset, so
an input the table does not classify still runs every job. The `lean` job runs for any
`code` change rather than the `lean` subset alone: the shard matrix is a job output, and
a non-empty `shards` list cannot be expanded without it. The build is warm on a
`wizlib`/`packages` change (the sources and the seed are unchanged, so Cachix
substitutes or Lake recompiles nothing).

## The shard budget

A test job is killed at **120 minutes** (`timeout-minutes` in the `tests` job). A killed
job has a partial log, and `scripts/ci.py balance` cannot see it (it reads only
successful jobs' walls), so a shard that grows into the timeout hides the regression that
made it slow. The plan therefore has a hard headroom guard: **no job's predicted wall may
exceed 75 minutes** (`SHARD_BUDGET_S` in `scripts/ci.py`; the 45 minutes left are the
job's setup before the `tests` step and the model's error). `JOB_TIMEOUT_S` in
`scripts/ci.py` mirrors the workflow's timeout and must be changed with it.

* `scripts/ci.py plan` (the `lean` job) prints the longest predicted job with its
  margins to the budget and to the 120-minute timeout, and exits 1 when a job is over.
* `scripts/ci.py check-shards` applies the same budget check, so the `lean` job fails
  before the matrix starts rather than sending a shard that would time out.
* The prediction is a per-part simulation from `.github/test-timings.json`
  (`scripts/ci.py simulated_wall`): each group after the previous one, with a barrier
  between groups; a group that opted in to `--jobs N` runs its cases through the
  driver's in-order pool (case *i* starts when case *i-N* is collected, so slot *i % N*),
  and the other groups are summed. Every shared program the part builds is added once,
  unscaled. It is deliberately conservative: the case times are medians from older runs,
  and a cold cache or a code change can move a case. `scripts/ci.py plan --json` prints
  the model's calibration against the 8-part and 12-part library runs (within 3.5 %).

When a shard is over the budget, split it (`"split": N`) or refresh the baseline from
green runs; do not raise the job timeout. A timeout is a cancelled job whose partial log
cannot tell which case hung, and `balance` then leaves it out of the reported tail.

## What the runner needs

* Linux, x86_64 or aarch64 (see "aarch64" below). 4 or more cores, 16 GB of memory
  (the selfhost shards peak at about 4.5 GB per job; one job runs at a time per runner),
  60 GB of disk (the Nix store: `wiz` is ~1.8 GB with its closure; the test driver's
  output is ~165 MB but its closure includes `wiz`, so ~2.0 GB; plus cache.nixos.org's
  dev shell, the Wiz caches under `~/.cache/wiz`, `.grail` and `/tmp/wiz-selfhost-*`).
  There is no `.lake` build any more. The opt-in nightly fixpoint
  (`.github/workflows/fixpoint.yml`) needs **7 GiB free** (the fixpoint's declaration:
  stage 2's self-compile has peaked at 6.3 GiB); it checks `MemAvailable` before the run
  and fails clearly on a smaller
  runner. The nightly benchmarks (`.github/workflows/bench.yml`) need **6 GiB free**,
  and pin the measurement to `WIZ_BENCH_CPUSET` when that variable is set (otherwise
  to all but two CPUs). The nightly compiler reproducibility check
  (`.github/workflows/repro.yml`, two `lake build wiz grail` runs under two absolute
  roots) needs **5 GiB free** and checks `MemAvailable` the same way.
* **Nix** (multi-user), with flakes, and the Cachix cache as a substituter. The workflow
  does not install Nix on a self-hosted runner (`.github/actions/setup`: only on GitHub's
  runners); `cachix-action` adds the cache per job, but configuring it system-wide means
  the image already has the dev shell's packages.
* The GitHub Actions runner (`actions/runner`), registered with the label
  `wiz-heavy` (any label; it is what `WIZ_RUNNER_HEAVY` names) and `--ephemeral`.
* `git`, `curl`, `tar`, `bash`, `python3` (the workflow's own scripts; the dev shell has
  the rest).

## Setup

The steps below build a container image with Nix and the runner, and a loop on the host
that starts a fresh container for every job. (A VM per job, e.g. with a cloud-init image
and the same `run-one.sh`, is stronger isolation; the container is the minimum.)

### 1. The host

Any Linux with Podman (or Docker). On Debian/Ubuntu:

```sh
sudo apt-get install -y podman
```

### 2. The image

`Containerfile` (pick the runner's architecture: `x64` or `arm64`). The base image digest,
the Nix version and the runner version are pinned; take the digests and checksums from
the image and release pages and update them together:

```dockerfile
FROM ubuntu:24.04@sha256:73b999393d07f2bf65a40373778a44dc9a6d54ad7718d29247d8ff9413c4d6a8
ARG RUNNER_VERSION=2.321.0
ARG RUNNER_ARCH=x64
RUN apt-get update && apt-get install -y curl git xz-utils ca-certificates python3 sudo \
    libicu74 && rm -rf /var/lib/apt/lists/*
RUN useradd -m runner && echo 'runner ALL=(ALL) NOPASSWD: ALL' > /etc/sudoers.d/runner
# Nix, single-user inside the container (the container is the isolation boundary).
# The versioned installer is the one nixos.org/nix/install serves for 2.35.6; its
# sha256 pins the script (it verifies the Nix tarball it downloads).
RUN mkdir -m 0755 /nix && chown runner /nix
USER runner
RUN curl -sSfL -o /tmp/nix-install.sh https://releases.nixos.org/nix/nix-2.35.6/install \
    && echo '6f7bf206efb54cd4941fb274930dbc74fdfc16fcb06757ef261c8d7d69cfd60e  /tmp/nix-install.sh' | sha256sum -c - \
    && sh /tmp/nix-install.sh --no-daemon
RUN mkdir -p ~/.config/nix && printf '%s\n' \
    'experimental-features = nix-command flakes' \
    'substituters = https://cache.nixos.org https://badlydrawnwizards.cachix.org' \
    'trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI=' \
    > ~/.config/nix/nix.conf
ENV PATH=/home/runner/.nix-profile/bin:$PATH
WORKDIR /home/runner/actions-runner
RUN case "$RUNNER_ARCH" in \
      x64) sum=ba46ba7ce3a4d7236b16fbe44419fb453bc08f866b24f04d549ec89f1722a29e ;; \
      arm64) sum=62cc5735d63057d8d07441507c3d6974e90c1854bdb33e9c8b26c0da086336e1 ;; \
      *) echo "RUNNER_ARCH must be x64 or arm64"; exit 1 ;; \
    esac \
    && curl -sSfL -o r.tgz https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-${RUNNER_ARCH}-${RUNNER_VERSION}.tar.gz \
    && echo "$sum  r.tgz" | sha256sum -c - \
    && tar xzf r.tgz && rm r.tgz
# pre-fetch the dev shell's packages so each job starts warm (optional; re-run to refresh)
RUN nix develop github:wiz-pl/wiz --command true || true
COPY --chown=runner run-one.sh /home/runner/run-one.sh
ENTRYPOINT ["/home/runner/run-one.sh"]
```

`run-one.sh` (registers, runs exactly one job, exits):

```sh
#!/bin/bash
set -euo pipefail
cd ~/actions-runner
./config.sh --unattended --ephemeral --replace \
  --url https://github.com/wiz-pl/wiz \
  --token "$RUNNER_TOKEN" \
  --name "wiz-heavy-$(hostname)" \
  --labels wiz-heavy \
  --work _work
exec ./run.sh
```

```sh
chmod +x run-one.sh
podman build -t wiz-runner --build-arg RUNNER_ARCH=x64 .   # or arm64
```

### 3. A registration token per job

A registration token lasts one hour and is used once per registration; the loop on the host
asks for a new one for each container. It needs a GitHub token of a repository admin
(a fine-grained token with "Administration: read and write" on this repository only),
kept on the host, never in the image:

```sh
gh api -X POST repos/wiz-pl/wiz/actions/runners/registration-token --jq .token
```

### 4. The loop on the host

`/usr/local/bin/wiz-runner-loop`:

```sh
#!/bin/bash
# one fresh container per job; the container is removed when its job ends
export GH_TOKEN=$(cat /etc/wiz-runner/admin-token)   # chmod 600, owned by the service user
while true; do
  tok=$(gh api -X POST repos/wiz-pl/wiz/actions/runners/registration-token --jq .token) \
    || { sleep 60; continue; }
  podman run --rm --memory 20g --cpus "$(nproc)" -e RUNNER_TOKEN="$tok" wiz-runner || sleep 10
done
```

and a systemd unit `/etc/systemd/system/wiz-runner.service`:

```ini
[Unit]
Description=Wiz CI runner (ephemeral, one container per job)
After=network-online.target
[Service]
User=wizrunner
ExecStart=/usr/local/bin/wiz-runner-loop
Restart=always
[Install]
WantedBy=multi-user.target
```

```sh
sudo systemctl enable --now wiz-runner
gh api repos/wiz-pl/wiz/actions/runners --jq '.runners[] | [.name, .status, (.labels | map(.name) | join(","))]'
```

### 5. Switch CI to it

```sh
gh variable set WIZ_RUNNER_HEAVY -R wiz-pl/wiz -b wiz-heavy
```

The next run's heavy shards queue for `wiz-heavy`. While the machine is off they wait in
the queue (up to 24 hours, then fail), so switch back before switching it off for long:

```sh
gh variable delete WIZ_RUNNER_HEAVY -R wiz-pl/wiz
```

A label names one or more machines: run the loop on several hosts (or several loops on a
big one, with smaller `--cpus`/`--memory`) to take several heavy shards at once.

## Caches

Each job starts with an empty container. The Nix store comes from the image and from
Cachix: the `lean` job's `nix build .#wiz .#tests` store paths are published and the
shards substitute them. The Wiz build caches (`~/.cache/wiz`, `.grail`,
`/tmp/wiz-selfhost-*`) and the per-subset workspace caches below still come from the
GitHub Actions cache, as on GitHub's runners, but the **trusted** elaboration layer is
not one of them: every shard also reads the packaged `$wiz/share/wiz/cache` (a Nix
derivation, substituted with the `wiz` store path) through `--cache-ro`, and a pull
request's writable `~/.cache/wiz` key is PR-scoped, so master's entry is never offered to
it. A pull request saves its own PR-scoped `lean` subset cache (`.subset-cache/lean`, a
`withLakeCache` `.lake` output); it is untrusted and PR-scoped, and the shards still have
no `.lake` build or `.lake` cache.

### Subset caches

The Actions caches are keyed per repository subset, not by the whole tree, so a run
that fails in one subset leaves the successful subsets' caches for the next run of the
same pull request. `scripts/ci.py subset-key NAME [--with NAME] [--scope S]
[--suffix S]` prints one `key=` and one `prefix=`:

```text
key:    subset-v1-<name>[-<name>...]-<os>-<arch>-<toolchain12>[-<scope>]-<sha12>[-<sha12>...][-<suffix>]
prefix: subset-v1-<name>[-<name>...]-<os>-<arch>-<toolchain12>[-<scope>]-
```

`<sha12>` is the first 12 hex of the subset's `sha256` in `.github/repo-subsets.json`;
`<toolchain12>` hashes `flake.lock` and `lean-toolchain`; `<os>`/`<arch>` are the
runner's OS and architecture. The prefix stops before the subset hashes, so a later run
restores its own subset's previous entry and recompiles what changed.

| job | cache path | key |
|---|---|---|
| `lean` | `.subset-cache/lean` | `subset-v1-lean-<os>-<arch>-<toolchain12>-<lean12>` |
| `lean` | `.lake/docs-examples` | `subset-v1-lean-<os>-<arch>-<toolchain12>-docs-examples-<lean12>` |
| `docs examples` | `.lake/docs-examples` | `subset-v1-docs-<os>-<arch>-<toolchain12>-examples-<docs12>` |
| `docs` | `.wiz-doc-cache/ro` | `subset-v1-docs-<os>-<arch>-<toolchain12>-site-<docs12>` |
| `packages` | `scry/.grail` | `subset-v1-packages-<os>-<arch>-<toolchain12>-<compiler-key>-<packages12>` |
| `tests` | `~/.cache/wiz`, `.grail`, `/tmp/wiz-selfhost-*` | `subset-v1-tests-wizlib-<os>-<arch>-<toolchain12>-[pr-<N>-]<shard>-<compiler-key>-<selfhost/lib hash>-<tests12>-<wizlib12>-<wiz tree hash>` |
| `trust ledger` | `.lake/trust-cache` | `subset-v1-wizlib-<os>-<arch>-<toolchain12>-[pr-<N>-]<driver sha>-<wizlib12>` |

`web`, `wasm` and `runtime` own no Actions cache: the modules are Nix store paths in
the PR Cachix cache (content-addressed and reused path by path), the web job's product
is a check result, and the runtime script builds into a temporary directory.

A job restores with `actions/cache/restore` (`key` plus `restore-keys` = the prefix) and
saves with `actions/cache/save` under the same key. The save step has no `always()`:
only a successful build (or check, or test) reaches it, so a failed subset writes
nothing. A failed `docs` or `web` job does not touch the `lean` key (the lean seed is
saved right after its Nix build), and the `tests` shards save their own keys (each shard
is a separate key). The trusted Lake seed is **not** an Actions entry: `lake_seed`
publishes the `.#lake-seed` store path to Cachix, and a PR names its base commit's
output and substitutes it (`scripts/lake-cache.sh trusted`). A PR writes only the subset
keys above; its own `.lake` seed entry is untrusted and PR-scoped.

### Which cache is trusted

The invariant: **only master publishes trusted paths; PR caches are per-run and
untrusted.**

* A push to `master` publishes the `lean` job's store paths (and the `wasm` job's page
  modules) to `CACHIX_NAME` (`badlydrawnwizards`) with the `CACHIX_AUTH_TOKEN` secret.
  The tag/release path only reads that cache (it has no Cachix push). That cache's key
  is the only Cachix key in the image's `nix.conf` and in the docs/tower instructions
  (`cachix use badlydrawnwizards`).
* A pull request publishes only to the PR cache `wiz-pl` (repository variable
  `CACHIX_PR_NAME`), with the token in the secret `CACHIX_PR_AUTH_TOKEN`. A PR's test
  shards, trust-ledger, web, wasm, lean and packages jobs add that cache as an extra
  substituter for that job only, so its key is trusted in that job and nowhere else;
  master and the docs job never add it as a substituter.
* If `CACHIX_PR_AUTH_TOKEN` is unset, or the PR is from a fork, the PR pushes nothing:
  the step prints "the store paths are not published" and continues, and the shards
  build the paths. Nothing falls back to `CACHIX_AUTH_TOKEN`.
* A merge-queue run is neither master nor a pull request: it gets no trusted token,
  publishes nothing, and its shards build.
* The PR cache's entries are content-addressed and its signatures are not trusted by
  anything but that run. A compromised PR can fill a cache its own runs read; it cannot
  change what master, the docs deploy or tower substitute.

`wiz-pl` must **not** be added to `trusted-public-keys` anywhere: no `nix.conf`, no
image, no docs/tower instruction. The shards' `cachix-action` adds its key per job, and
that is the only place it belongs. Two independent properties keep a PR away from the
trusted cache: a PR's push steps get no `CACHIX_AUTH_TOKEN` (the setup action's
`cachix-token` is for substitution only, `skipPush: true`, and never writes), and
`CACHIX_PR_AUTH_TOKEN` has **Read** (not Write) on `badlydrawnwizards`, so even a
mistake in the workflow cannot push to the trusted cache with it.

The settings are: repository variable `CACHIX_PR_NAME` = `wiz-pl` (the separate Cachix
cache, which the token has Write on), and repository secret `CACHIX_PR_AUTH_TOKEN` = a
Cachix token with Write on `wiz-pl` and Read on `badlydrawnwizards`.

## aarch64

* Cachix holds x86_64 builds only (the `lean` job runs on GitHub's x86_64 runner). A
  heavy shard on an aarch64 runner has a different store path for the same sources, so
  `nix build .#wiz .#tests` builds it there the first time and nothing publishes it:
  aarch64 jobs are slower until the cache holds an aarch64 build (publishing one needs a
  `lean` job on that architecture, or a manual `cachix push` from an aarch64 machine).
  The dev shell's packages still come from cache.nixos.org, which builds aarch64-linux,
  and the image's pre-fetch step matters more.
* The Wiz build-cache key carries the architecture through its compiler hash and
  `wiz-Linux-ARM64-…` name, so an ARM job never restores x86_64 programs.
* The release tarball (`release.yml`, `wiz-x86_64-linux.tar.gz`) and its bundled C
  toolchain are x86_64 only, and `tower`'s release source picks the tarball by `uname -m`:
  the release workflow stays on GitHub's runner, and tests that install a real release
  (none in the heavy shards today) would need an aarch64 tarball first.
* The LLVM backend's C-struct calling convention follows the x86-64 SysV ABI
  (docs/stages/09-ffi.md): its FFI cases are in the `backends` shard, which is not
  heavy and stays on x86_64. Don't mark a shard with `llvm` or `ffi` cases heavy for an
  aarch64 runner.
* Lean (elan) and the dev shell (GMP, Boehm GC, LLVM, cc) exist for aarch64-linux
  (`flake.nix` lists it).

## Checking it

After `gh variable set`, open (or update) a pull request from a branch of this
repository: the `test (selfhost-1)` … jobs show `wiz-heavy-…` as their runner in the
job's "Set up job" step. A fork's pull request shows `GitHub Actions …` for the same jobs.
