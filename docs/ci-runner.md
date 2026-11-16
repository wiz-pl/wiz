# A self-hosted CI runner

CI runs on GitHub's `ubuntu-latest` runners. The heavy test shards (those with
`"heavy": true` in `.github/test-shards.json`: `selfhost-1` … `selfhost-6` and
`grail-selfhost`) can run on a machine of our own instead. Nothing changes until the
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

## What the runner needs

* Linux, x86_64 or aarch64 (see "aarch64" below). 4 or more cores, 16 GB of memory
  (the selfhost shards peak at about 4.5 GB per job; one job runs at a time per runner),
  60 GB of disk (the Nix store: `wiz` is ~1.8 GB with its closure; the test driver's
  output is ~165 MB but its closure includes `wiz`, so ~2.0 GB; plus cache.nixos.org's
  dev shell, the Wiz caches under `~/.cache/wiz`, `.grail` and `/tmp/wiz-selfhost-*`).
  There is no `.lake` build any more. The opt-in nightly fixpoint
  (`.github/workflows/fixpoint.yml`) runs in reference-counting mode and needs **4 GiB
  free** (its largest step is `cc -O2` of a stage's C, 2.7 GiB when last measured; the
  RC self-compile peaked at 1.3 GiB); a run with the `gc` box ticked uses the Boehm
  collector and needs **7 GiB free** (stage 2's self-compile has peaked at 6.3 GiB). It
  checks `MemAvailable` before the run and fails clearly on a smaller runner. The nightly benchmarks (`.github/workflows/bench.yml`) need **6 GiB free**,
  and pin the measurement to `WIZ_BENCH_CPUSET` when that variable is set (otherwise
  to all but two CPUs).
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

`Containerfile` (pick the runner's architecture: `x64` or `arm64`; the version is the
latest from https://github.com/actions/runner/releases):

```dockerfile
FROM ubuntu:24.04
ARG RUNNER_VERSION=2.321.0
ARG RUNNER_ARCH=x64
RUN apt-get update && apt-get install -y curl git xz-utils ca-certificates python3 sudo \
    libicu74 && rm -rf /var/lib/apt/lists/*
RUN useradd -m runner && echo 'runner ALL=(ALL) NOPASSWD: ALL' > /etc/sudoers.d/runner
# Nix, single-user inside the container (the container is the isolation boundary)
RUN mkdir -m 0755 /nix && chown runner /nix
USER runner
RUN curl -L https://nixos.org/nix/install | sh -s -- --no-daemon
RUN mkdir -p ~/.config/nix && printf '%s\n' \
    'experimental-features = nix-command flakes' \
    'substituters = https://cache.nixos.org https://badlydrawnwizards.cachix.org' \
    'trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI=' \
    > ~/.config/nix/nix.conf
ENV PATH=/home/runner/.nix-profile/bin:$PATH
WORKDIR /home/runner/actions-runner
RUN curl -L -o r.tgz https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-${RUNNER_ARCH}-${RUNNER_VERSION}.tar.gz \
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
Cachix: the `build` job's `nix build .#wiz .#tests` store paths are published with an
explicit `nix shell nixpkgs#cachix -c cachix push badlydrawnwizards …` (the
`CACHIX_AUTH_TOKEN` secret is in that step's environment only; a fork's job never gets
it), and the shards substitute them. The Wiz build caches (`~/.cache/wiz`, `.grail`,
`/tmp/wiz-selfhost-*`) still come from the GitHub Actions cache, as on GitHub's runners.
There is no `.lake` build or `.lake` cache to restore.

## aarch64

* Cachix holds x86_64 builds only (the `build` job runs on GitHub's x86_64 runner). A
  heavy shard on an aarch64 runner has a different store path for the same sources, so
  `nix build .#wiz .#tests` builds it there the first time and nothing publishes it:
  aarch64 jobs are slower until the cache holds an aarch64 build (publishing one needs a
  build job on that architecture, or a manual `cachix push` from an aarch64 machine).
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
