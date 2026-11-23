# Deferred release variants: aarch64 and `share/wiz/cc`

This lane adds the two release variants that `agent/nix-derivations` left out: the
bundled C toolchain as its own output (`release-cc`) and a tarball variant that ships
it at `share/wiz/cc` (`release-bin-cc`), and it makes every release attribute build for
aarch64 as well as x86_64. It is code-only: **no heavy build was run in this lane**, and
the queue is reserved for train11. The default `release-bin` tarball is unchanged: its
bytes and its source subset do not include the compiler bundle.

Base: `integration/train12` `f489cc876`; branch `agent/release-variants`.

## Attributes

| attribute | what it is | source subset (`passthru.subset`) |
|---|---|---|
| `release-cc` | the portable C toolchain: clang, `ld.lld`, `cadical`, compiler-rt and clang headers, the glibc 2.27 / Linux 4.15 sysroot, static GMP 6.3.0 and Boehm GC 8.2.8, licences and `VERSIONS`. A normal store path; not stripped or patched by the leaf. | `scripts/bundle-cc.sh`, `scripts/bundle-cc.sources`, the pinned official Lean 4.35 toolchain tarball (clang, `ld.lld`, `cadical`, `lib/clang`, licences), and the pinned downloads (the host architecture's `libc6`/`libc6-dev`/`linux-libc-dev` debs, GMP 6.3.0, Boehm GC 8.2.8) |
| `release-bin` | the default tarball: `wiz`, `grail`, `tower`, `lib/`, editors, licences and the infoview. No `share/wiz/cc`; `wiz build` uses the host `cc`/GMP. | unchanged from `wiz-notes/nix-artifacts.md` |
| `release-bin-cc` | the same leaf **plus** `release-cc` copied to `share/wiz/cc`; output is `wiz-<arch>-linux-cc.tar.gz`. Requested explicitly so the default tarball keeps its identity and bytes. | `release-bin`'s subset + `release-cc` |
| `release-unwrapped`, `release-tower` | the statically linked release binaries, now built from the host platform's static GMP/libuv/OpenSSL and the host `cc` | unchanged |

`release-static-libs` is still the internal collection of `libgmp.a`, `libuv.a`,
`libssl.a` and `libcrypto.a`; it takes the archives from `pkgs` for the host platform,
so it has no x86_64-specific path.

## The portability contract

* `release-bin` and `release-bin-cc` are the **only** leaf steps that set the ELF
  interpreter, remove RUNPATH, strip and scrub store paths. Do not move that step into
  `release-cc` or any intermediate derivation.
* `release-cc` is a separate, normal store path. It is copied into the leaf tarball by
  `scripts/release-tarball.sh` (`CCDIR`), after the leaf has patched its own binaries.
  The compiler bundle itself already has the conventional interpreter and no
  `/nix/store` references; its `checkPhase` proves both, and the tarball's
  `test-release-portability.sh` scan proves no member names the store.
* The sysroot is link-time only: programs built with `share/wiz/cc` link the host's
  glibc dynamically. The 2.27 floor and the Ubuntu 18.04 provenance are the existing
  documented policy (`scripts/bundle-cc.sources`); this lane does not change the floor.
* The release promise is unchanged: `wiz-<arch>-linux.tar.gz` remains the published
  tarball shape. `release-bin-cc` is the explicit opt-in variant; a published aarch64
  tarball still needs a native aarch64 build and release decision.

## aarch64 changes

Everything is derived from `pkgs.stdenv.hostPlatform`; there are no per-host flags.

* `releaseInterp` is `/lib/ld-linux-aarch64.so.1` on aarch64 and
  `/lib64/ld-linux-x86-64.so.2` on x86_64. The Nix-build loader used only for
  `release-cc`'s throwaway build copies comes from the same `releaseLoader` name.
* `releaseArch` is `parsed.cpu.name` (`aarch64`/`x86_64`). `scripts/release-tarball.sh`
  accepts `WIZ_RELEASE_ARCH`; the USTAR name is no longer taken from `uname -m`, which
  reports the builder's kernel when an aarch64 build runs under emulation.
* `scripts/bundle-cc.sh` takes `WIZ_BUNDLE_ARCH` (also defaulting to `uname -m`) and
  selects one architecture's debs from `scripts/bundle-cc.sources`: `_amd64.deb` from
  archive.ubuntu.com or `_arm64.deb` from ports.ubuntu.com. The arm64 bionic debs are
  pinned in the same list:
  `libc6_2.27-3ubuntu1.6_arm64.deb`
  (`0b4348723ff763cb5d256283a362fb1f4db0658df9331c19b29c63a94cbb00dc`),
  `libc6-dev_2.27-3ubuntu1.6_arm64.deb`
  (`69586108d590bdd350d115c1b4a58763d930b9776bd554fd14462ffbbd305d19`) and
  `linux-libc-dev_4.15.0-213.224_arm64.deb`
  (`9e350db851f6cf12ae14d6a611ec2102e7d03004e9ea143c67e541fe7cf11f47`).
* GMP and the GC use `--host=aarch64-linux-gnu` and the sysroot's
  `aarch64-linux-gnu` lib directory. GMP's `--enable-fat` is x86-64 only and is dropped
  on aarch64 (a core-tuned build would not run on another aarch64 machine).
* The clang/`ld.lld`/`cadical`/`lib/clang` prefix is the official Lean 4.35 release
  tarball, fetched as a fixed-output input per architecture and pinned in `flake.nix`:
  `lean-4.35.0-linux.tar.zst`
  (`sha256-colZekRUMkbJInuMrlAXZ+CVzhf21Ei5X8So3Jcmj20=`) and
  `lean-4.35.0-linux_aarch64.tar.zst`
  (`sha256-yPD4o5IOg5cYsTQ+Z4H9gKPpsQJPvNcHjrMPVOgGsCg=`). nixpkgs' `lean4` builds Lean
  from source and does not install clang, so this is the same upstream toolchain the
  release job's elan install uses.
* The static archives come from the host's `pkgs`; `releaseCC` adds `-no-pie` and the
  static libstdc++/libgcc/atomic archives in the same order on both architectures.
* Nix may download a fixed-output input once, but the build sandbox never fetches:
  `release-cc` turns `scripts/bundle-cc.sources` into one `fetchurl` per file and sets
  `WIZ_BUNDLE_OFFLINE=1`. The build only hashes and copies those store paths into the
  script's downloads directory.

The self-test inside `bundle-cc.sh` executes the target binaries. A Nix sandbox has no
`/lib64/ld-linux-x86-64.so.2` (or `/lib/ld-linux-aarch64.so.1`), so `release-cc` builds
disposable copies of clang/`ld.lld`/`cadical` pointed at `${pkgs.glibc}`, uses
`WIZ_BUNDLE_SKIP_TEST=1`, and restores the official, portable binaries before the
output is checked. The release gate is still the tarball test below, run on a real
host.

## How to validate (later, on the heavy queue)

x86_64:

```sh
nix build .#release-cc --no-link --print-out-paths
nix build .#release-bin --no-link --print-out-paths        # default: no share/wiz/cc
nix build .#release-bin-cc --no-link --print-out-paths     # has share/wiz/cc
cc=$(nix build .#release-cc --no-link --print-out-paths)
"$cc/bin/cc" --version
"$cc/bin/cadical" --version
```

aarch64 (native builder or remote builder; do not cross-build the runnable tests):

```sh
nix build --system aarch64-linux .#release-cc .#release-bin .#release-bin-cc \
  --no-link --print-out-paths
```

The `release-bin-cc` `doCheck` already rebuilds the archive twice in different
environments, compares them byte for byte, runs
`scripts/test-release-portability.sh ... --glibc ${pkgs.glibc}` (no member names
`/nix/store`, glibc-only NEEDED, conventional interpreter, clean-environment run), and
checks that the archive has `wiz-<arch>-linux/share/wiz/cc/bin/cc`.

Outside Nix, against a downloaded/extracted or built tarball:

```sh
sh scripts/test-release-portability.sh wiz-x86_64-linux-cc.tar.gz
sh scripts/test-release-install.sh wiz-x86_64-linux-cc.tar.gz v0.1.0
# the install test builds with share/wiz/cc and checks cadical's LRAT output
sh scripts/test-release-portability.sh wiz-aarch64-linux-cc.tar.gz   # on aarch64
```

`nix flake check --no-build` is an evaluation check only; it does not prove the bundle
runs. The builds above are the first real gate (`release-cc`, then
`release-bin-cc`, on each architecture), followed by the tarball tests.

## What is still to build

1. `.#release-cc` on x86_64 and aarch64 (GMP/GC + sysroot; the long part).
2. `.#release-bin` on both (default leaf, unchanged).
3. `.#release-bin-cc` on both (leaf + `share/wiz/cc`; runs the reproducibility and
   portability checks).
4. Push the resulting store paths to `badlydrawnwizards` only after the checks pass;
   aarch64 needs an aarch64 builder and the push token.
