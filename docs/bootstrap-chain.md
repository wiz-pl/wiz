# The self-hosted toolchain chain

Status: **design, not active.** Nothing here runs in CI, no commit pins a toolchain, and
no release or attestation has been published. The chain starts when its root is
declared (see "The start condition"). Until then the pieces exist to be built and
measured locally: `scripts/repro-fixpoint.sh`, `scripts/check-toolchain-pin.py` and the
Nix prototype in `nix/bootstrap-chain.nix` (`packages.wizc`, `packages.wizc-release`,
`legacyPackages.SYSTEM.bootstrapChain`).

## The goal

Once Wiz is fully self-hosted, every commit's `flake.nix` names the toolchain that
builds it by **commit and content hash**. The toolchain is fetched from GitHub Releases
or from any other source, as long as the bytes have that hash. The chain of builds is
reproducible, so it can be *shortcut* from any source (fetch the pinned hash), and it
can be *verified* by rebuilding: attested builds assert, for each link, which inputs
produced which output hash.

Requirements this design meets, each in its own section below:

1. The release artifact is self-contained: a static executable (decided below, with
   evidence).
2. The chain is rooted at a commit that the Lean host builds (Lean from nixpkgs, built
   from source), with precise criteria for declaring the root; the Lean path stays
   buildable at the root for diverse double compiling.
3. The release is the fixpoint stage, so its hash depends only on the source and
   nixpkgs, not on which predecessor built it. Building it from two predecessors and
   getting one hash is a DDC check.
4. Attestations bind the source's narHash, the nixpkgs lock and the input toolchain's
   hash to the output's hash. The git commit is metadata only (git hashes are SHA-1).
5. Reproducibility across machines is shown before any attestation counts.
6. At least two independent builders agree before a link is published, and every
   release is mirrored to the Cachix cache `badlydrawnwizards`.
7. A lint rejects any pin that is not commit plus hash; a periodic audit rebuilds the
   links since the last checkpoint.
8. Every release that any commit pins is retained indefinitely, on GitHub and in Cachix.
   Snapshot pruning never applies to chain releases (see "Retention").

## Terms

| term | meaning |
|---|---|
| `self.wiz` | the toolchain's source as one program: `selfhost/*.wiz` assembled (imports stripped, files concatenated in `compilerFiles` order, with `wizVersion` and `toolchainId`) |
| `wizc` | the self-hosted compiler as an executable: run in a directory holding `input.wiz`, it prints C (`--rc` picks reference counting) |
| `T(B)` | the C that executable `B` prints for `self.wiz` |
| `CC(c)` | the executable built from C text `c` with the pinned recipe (nixpkgs' static cc, `-O2 -w`, `selfhost/rt.c`) |
| `C*` | the **fixpoint C**: `T(CC(C*)) = C*` |
| release | `CC(C*)`, checked to print `C*`, packed reproducibly with a manifest |
| link | one commit's release, built from its predecessor's release |
| root | the first link, built from the Lean host instead of a predecessor |

`T` depends only on what `B` computes, not on how `B` was built: two correct compilers
of the same source print the same `C*`. That is why the chain can change predecessors
without changing its outputs.

## The release is the fixpoint stage

A link built from a predecessor `P` (any correct compiler for the new source's
language, e.g. the previous release):

```
c1 = T(P)          P compiles the new source         (P's code generator)
s1 = CC(c1)        the new compiler, built by P
c2 = T(s1)         = C*: the new compiler's own output
s2 = CC(c2)        the release candidate
c3 = T(s2)         must equal c2: the fixpoint check
release = s2
```

`s2` is a function of `C*` and the cc recipe, and `C*` is a function of the source.
So the release's bytes do not depend on `P`: building the same commit from the Lean
host and from the previous release must give one sha256. That equality is the chain's
diverse double compiling (DDC) check, and it is run at the root (see below).

From the Lean host the first two steps collapse: the Lean-built compiler is already
the new compiler, so its output (`seed.c`, fixpoint.sh's `self1.c`) is `C*` when the
fixpoint holds (it does today: `self1.c = self2.c = self3.c`), and one more
self-compile checks it.

The Nix prototype implements both: `bootstrapChain.fromLean` (seed, then the fixpoint
check) and `bootstrapChain.step { pred }` (three self-compiles from a predecessor).

**Equal C must give equal executables.** cc records the source file's base name in
the symbol table (an `STT_FILE` entry), so `cc self1.c` and `cc self2.c` give
different bytes from identical C. Every stage compiles a copy named `wizc.c`;
`scripts/fixpoint.sh` now does the same and prints the stage executables' sha256 (with
`--stages 3`, stage2 against stage3).

## The artifact: a static executable

Fixed-output derivations (FODs) cannot refer to the store, and a release is consumed
through an FOD (`fetchurl` with a hash). Two shapes were considered:

| | static executable | FOD tarball + wrapper derivation |
|---|---|---|
| what is released | `wizc`, linked statically with musl (`pkgsStatic`), no interpreter, no RUNPATH | a dynamic `wizc` with its interpreter and RUNPATH stripped or set to placeholders |
| consuming it | unpack; it runs | unpack, then `patchelf --set-interpreter --set-rpath` against the consumer's nixpkgs (or a wrapper) |
| hash depends on | the bytes built | the bytes *before* patching; the patched result differs per consumer nixpkgs |
| runs outside Nix | yes, on any x86_64 Linux kernel | only after patching, or with the right glibc on the host |
| risk | musl differs from glibc (allocation speed, stack size of threads) | the patching step is part of the trusted path, and a missed store path in the binary is a silent dependency |

**Decision: static.** The self-hosted compiler needs only libc (reference-counted
mode) or libc and Boehm GC (collector mode). `pkgsStatic.stdenv.cc` is in the NixOS
binary cache at the pinned nixpkgs; `pkgsStatic.boehmgc` (collector mode only) is not,
and is built from source. The evidence is in
"Measurements": the release derivation fails unless the executable contains no
`/nix/store` string, `disallowedReferences` forbids musl's store path, and the C that
the static executable prints equals the C the glibc build prints.

**Against a relocated Nix build.** A third shape has been proposed for tower's
toolchain tarballs: a `wiz-release` flake output that copies the Nix build, sets an
`$ORIGIN`-relative RUNPATH with patchelf and bundles the non-glibc shared libraries
(GMP, the collector) beside it, using the host's glibc. Compared with the static `wizc`:

| | relocated Nix build (`wiz-release`, proposed) | static musl `wizc` (`wizc-release`) |
|---|---|---|
| host requirement | glibc at least the pinned nixpkgs' glibc (2.44 at `02c087f3`); the current tarball's floor is 2.27 (its bundled sysroot) | any x86_64 Linux kernel; no libc on the host |
| bytes | patched after the build: the published bytes are not the store output, so the patching is part of the recipe the attestation must cover | the store output itself, packed |
| interpreter | the host's `/lib64/ld-linux-x86-64.so.2` | none |
| what it ships | the whole toolchain (`wiz`, `grail`, `lib/`, the C toolchain) | the chain's compiler only |
| fits the chain | possible, but a nixpkgs bump raises the glibc floor, and the floor is part of what a link means | yes: the bytes do not depend on the host |

They answer different questions. `wiz-release` is how a *user's toolchain* could be
published from the Nix build; `wizc-release` is the *chain's* link, which must run on
any builder and stay byte-identical. A later full toolchain could be built *from* the
chain's `wizc` and relocated like `wiz-release`; the chain itself stays static.

**Mode: reference counting (`--rc`).** The release is built and checked in RC mode:
no collector to link, a self-compile peaks near 1.7 GB and takes about four minutes
(the collector's peaks at 5.7 GB and takes about fourteen), and a leak is a hard error
at exit. `rc = false` in `nix/bootstrap-chain.nix` gives the collector's chain.

The tarball (`packages.wizc-release`) is `wizc-SYSTEM/bin/wizc` and
`wizc-SYSTEM/MANIFEST`, packed with the flags of `scripts/release-tarball.sh` (sorted,
owner 0:0, mtime 0, `gzip -n`). The manifest records only facts about the bytes
(format, version, system, mode, the sha256 of `wizc` and of `C*`), so the tarball stays
a function of the source and nixpkgs; the commit and the inputs are bound by the
attestation.

## The root

The **root** is the first commit whose release has no predecessor: it is built from
the Lean host (`packages.wiz`, whose Lean comes from nixpkgs and is built from source
there, not from an elan binary). Every later link is built from its predecessor's
release.

A commit `R` may be declared the root when all of these hold at `R`:

1. **Fixpoint.** `scripts/fixpoint.sh --stages 3` passes in both modes (`--rc` and the
   collector): `self1.c = self2.c = self3.c`.
2. **Executable fixpoint.** With the pinned recipe (the static Nix build), `CC(C*)`
   reproduces `C*`, and stage 2's and stage 3's executables are byte-identical.
3. **Parity bar.** The self-hosted compiler meets the parity bar the project uses for
   "self-hosted" (`selfhost` test group green; the parity matrix's blocking rows
   closed). The chain needs the compiler to compile its own source, which (1) shows;
   (3) is what makes the chain's output a toolchain worth pinning.
4. **Lean-free assembly.** `self.wiz` is assembled without Lean (prerequisite P2,
   below), so a later link needs nothing but its predecessor, cc and libc.
5. **Reproducible.** The root's release builds to the same sha256 on two machines
   (GitHub Actions and a local builder), under the variations of
   `scripts/repro-fixpoint.sh` and the Nix sandbox.
6. **DDC at the root.** The root's release is also built from a second, independent
   path, and the hashes agree: the Lean host path, and the same `C*` compiled by a
   second C compiler (clang) whose output compiler prints `C*` again (DDC-1, as the
   bootstrap-seed prototype did). Once `R+1` exists, building `R+1` from `R`'s release
   and from the Lean host (while Lean is still in the tree) must give one hash.
7. **Lean stays buildable at the root.** `nix build .#wiz` (the Lean host) keeps
   building at `R` for as long as anyone wants to re-derive the root; the root's
   attestation names it as the input toolchain.

The root is declared by a commit that adds the chain's first pin file and a line to
this document naming `R`, the release's sha256 and the two builders' run links.

## The start condition

Nothing is switched on until the root exists. Concretely, until the commit described
above is merged:

* no workflow runs on push or pull request for the chain (any workflow added for it is
  `workflow_dispatch` only and says it is inactive);
* no `toolchain-*` GitHub release, no attestation and no Cachix pin is published;
* `wizc-toolchain.json` does not exist in the repository, and `flake.nix` does not read
  one.

This keeps CI cost at zero until the chain has something to anchor to.

## The flake interface

### How a commit pins its toolchain

One file at the repository root, `wizc-toolchain.json`:

```json
{
  "format": 1,
  "commit": "<40-hex commit of the predecessor>",
  "hash": "sha256-<SRI hash of wizc-x86_64-linux.tar.gz>",
  "system": "x86_64-linux",
  "urls": ["https://mirror.example/wizc/<commit>/wizc-x86_64-linux.tar.gz"]
}
```

`flake.nix` reads it with `builtins.fromJSON` and passes it to
`bootstrapChain.fetchToolchain`, whose result is the `pred` of `bootstrapChain.step`.
The commit is a label (it names the default URL and the store name); the hash is the
identity. The root's `flake.nix` has no pin and builds `fromLean`.

### Fetching from any source

`fetchToolchain { commit, hash, urls }` is a `fetchurl` FOD named
`wizc-SYSTEM-COMMIT.tar.gz` with `urls ++ [GitHub release URL]`. An FOD's store path
depends only on its name and hash, so any of these satisfies it with no network:

* a substituter that has the path: the Cachix cache `badlydrawnwizards` (every release
  is pushed there), or any other binary cache;
* a local copy added with `nix store add-file` (named `wizc-SYSTEM-COMMIT.tar.gz`), or
  `nix-store --add-fixed sha256`;
* any URL in `urls`, then the GitHub release `toolchain-COMMIT`.

Nix checks the hash whichever source answers, so a mirror can withhold the file but
cannot change it.

### The shortcut path and the full-verification path

* **Shortcut** (every build): fetch the pinned predecessor by hash, run `step` (three
  self-compiles, minutes in RC mode). This trusts the predecessor's hash, which the
  attestations vouch for.
* **Full verification** (the audit, or anyone who wants it): start from the root, built
  from the Lean host at `R`; for each later commit in the pin history, build `step`
  from the previous link's *locally built* release and compare its sha256 with the
  next pin. A mismatch is the first link that does not reproduce.
* **Checkpointed verification**: start from a checkpoint (a link whose rebuild has been
  confirmed by the audit) instead of the root.

## Attestations

An attestation is an in-toto Statement v1 with an SLSA Provenance v1 predicate, signed
with Sigstore through GitHub artifact attestations (`actions/attest-build-provenance`,
keyless, logged in Rekor) for the GitHub builder, and with `cosign attest-blob` (or the
same predicate signed by a maintainer key) for a local builder.

```json
{
  "_type": "https://in-toto.io/Statement/v1",
  "subject": [{ "name": "wizc-x86_64-linux.tar.gz", "digest": { "sha256": "<release>" } }],
  "predicateType": "https://slsa.dev/provenance/v1",
  "predicate": {
    "buildDefinition": {
      "buildType": "https://github.com/wiz-pl/wiz/blob/master/docs/bootstrap-chain.md#attestations",
      "externalParameters": {
        "flake": "github:wiz-pl/wiz/<commit>",
        "attribute": "packages.x86_64-linux.wizc-release",
        "mode": "rc"
      },
      "resolvedDependencies": [
        { "name": "source", "digest": { "sha256": "<narHash of the flake source>" },
          "annotations": { "gitCommit": "<commit>" } },
        { "name": "nixpkgs", "uri": "github:NixOS/nixpkgs/<rev>",
          "digest": { "sha256": "<narHash from flake.lock>" } },
        { "name": "predecessor", "digest": { "sha256": "<predecessor release>" },
          "annotations": { "gitCommit": "<predecessor commit>" } }
      ]
    },
    "runDetails": {
      "builder": { "id": "<GitHub workflow ref, or local:<builder name>>" },
      "metadata": { "invocationId": "<run URL>" }
    }
  }
}
```

For the root, `predecessor` is replaced by `{ "name": "lean-host", "digest": { "sha256":
"<narHash of packages.wiz's output>" } }`.

**What binds.** The source's narHash (SHA-256 over the NAR of the flake source, from
`self.narHash`), the nixpkgs narHash from `flake.lock`, and the predecessor's release
sha256 determine the subject's sha256. The git commit is an annotation: it says where
to find the source, not what the source is, because git object names are SHA-1.

**Verification policy.** A link `(commit, sha256)` is accepted when:

1. at least two attestations name it as subject with identical `resolvedDependencies`
   digests;
2. they come from two different builders: one GitHub Actions identity (certificate
   issuer `https://token.actions.githubusercontent.com`, subject the `wiz-pl/wiz`
   release workflow on a protected ref) and one local builder key listed in the
   repository;
3. the source digest equals the narHash of the commit's tree as Nix computes it
   (`nix flake metadata github:wiz-pl/wiz/<commit> --json`), and the nixpkgs digest
   equals that commit's `flake.lock`;
4. the predecessor digest equals the hash in the commit's `wizc-toolchain.json`, and
   that predecessor is itself accepted (or is a checkpoint);
5. each attestation is in the Rekor log (GitHub's verifier checks this:
   `gh attestation verify wizc-x86_64-linux.tar.gz --repo wiz-pl/wiz`).

A disagreement between builders blocks the release and is a reproducibility bug.

## Reproducibility

Attestations count only once two builds on different machines are known to agree.
Three layers check it:

1. **`scripts/repro-fixpoint.sh`** (local, now): runs `scripts/fixpoint.sh --keep` in
   two copies of the checkout that differ in directory (and path length), `TMPDIR`,
   `HOME`, locale, time zone, umask, `SOURCE_DATE_EPOCH`, the collector's marker
   threads and Lean's thread count, the CPUs it may use, and unrelated environment
   variables, then compares the generated sources, `self*.c` and every executable byte
   for byte. For the first difference it prints the first differing byte or line, the
   ELF sections and symbols that differ, and which varied value occurs in the file.
   `--compare A B` compares any two artifact directories (a kept `.lake/fixpoint`
   against another machine's, or against a Nix output).
2. **The Nix sandbox** varies the user (`nixbld`), `HOME` (`/homeless-shelter`), the
   build directory and `NIX_BUILD_CORES`, and removes ambient inputs. `nix build
   --rebuild` repeats a derivation and fails when the output differs.
3. **Two machines**: GitHub Actions and a local builder build `wizc-release` from the
   same commit; the sha256 must agree (requirement 6).

The measurements so far are under "Measurements".

## Builders and mirrors

* **Builders.** GitHub Actions (`ubuntu-latest`, Nix from the installer, nothing from
  Cachix for the chain's own derivations: `--option substitute false` for
  `wizc*`) and at least one local builder (a maintainer's machine, its key in the
  repository). Both build `packages.wizc-release` at the commit and attest it.
* **Publication.** Only when both agree: the GitHub release `toolchain-COMMIT` holds the
  tarball, its `.sha256` and the attestations; the FOD path is pushed to Cachix
  (`badlydrawnwizards`), so `fetchToolchain` substitutes it with GitHub down. A third
  mirror is any URL added to `urls`.
* **Cost.** One link is three RC self-compiles plus three static cc runs, about
  twenty minutes and 2 GB on one core. It runs only for commits that change
  `selfhost/` (other commits re-pin the same toolchain; see "Pins").

## Pins

`scripts/check-toolchain-pin.py` rejects any pin that is not a full commit plus a
content hash:

* `wizc-toolchain.json`: `commit` must be 40 hex digits, `hash` an SRI sha256, `urls`
  https only, no unknown keys;
* `wiz-toolchain` (tower's project pin): the spec must be `REF@<40 hex>` followed by
  ` sha256-…=`. Channels (`nightly`), branches, tags, short shas, paths and free text
  are rejected. `--commit-only` accepts `REF@<40 hex>` without the hash, which is all
  tower reads today.

It caught the case that motivated it: a `wiz-toolchain` holding a local-merge
description (`branch+branch@master-50cd3e7 (local merge, see README)`), which tower
parsed as a ref. Its self-test (`--self-test`) has that case. Once the chain is active,
CI runs it on `wizc-toolchain.json` and on every `wiz-toolchain` in the repository.

**Which commit to pin.** A commit pins the newest release whose source it can be built
from: normally the previous link. A commit that does not change `selfhost/` keeps the
same pin and the same `C*`, so its release has the same hash as its parent's and
nothing is rebuilt (the FOD is already in the store or in Cachix).

## Relation to tower and grail

* **tower** pins a whole toolchain (`wiz`, `grail`, the standard library) by
  `REF@COMMIT` and checks the tarball against a `.sha256` downloaded next to it. That
  is a commit pin with a hash from the same server. The proposed extension: the hash
  in the pin itself (`master@<sha> sha256-…=`), checked by tower; the lint accepts that
  form now. When the chain is active, a tower toolchain's `bin/wizc` *is* a chain
  release, so tower can verify it with the same attestations.
* **grail** records the toolchain that resolved a lock (`(toolchain VERSION REVISION)`)
  and lets an index entry require a toolchain version. Neither is a build input. When
  the chain is active, the lock's toolchain line can carry the release hash, so a
  package lock pins its compiler by content too.
* **The Lean host** stays as the root's builder and as a DDC witness. It is not part
  of any later link.

## Threat model

| threat | covered by | not covered |
|---|---|---|
| a mirror or CDN serves different bytes | the hash in the pin; Nix checks it | a mirror withholding the file (use another source) |
| a compromised GitHub release or CI runner publishes a bad release | two builders must agree; the local builder is independent of GitHub | both builders compromised the same way |
| a malicious predecessor injects code (trusting trust) | the release does not depend on the predecessor: DDC at the root (Lean host vs chain, gcc vs clang) and on audit | a backdoor in the source itself, in nixpkgs' cc or libc, or in the Lean host shared by both paths |
| git SHA-1 collision substitutes a source tree | the attestation binds the source's NAR sha256, not the commit | |
| nixpkgs changes under a pin | the nixpkgs narHash in `flake.lock` and in the attestation | a compromised nixpkgs at the pinned rev (shared by all builders) |
| nondeterminism makes honest builders disagree | repro-fixpoint.sh, Nix `--rebuild`, two machines before publishing | nondeterminism that both machines share (same CPU model); add a third builder of another kind |
| bitrot: an old link no longer rebuilds (nixpkgs fetch dies, a source vanishes) | the periodic audit; Cachix holds the sources' FODs | upstream tarballs gone from every cache |
| rollback: an old release served for a new commit | the pin names the exact hash; attestations name the commit | |
| a stolen local builder key | Rekor logs every attestation; the key list is in the repository and revocable | attestations made before revocation |

## Retention

**Requirement: a release that any commit pins is kept forever.** The tower snapshots
(`snapshot-<sha>`, docs/stages/26-tower.md, 26g) keep only the newest 20 plus tagged
ones, and a bisect has already failed because a pinned commit's snapshot had been
pruned. The chain cannot work that way: a pruned release makes every later link
unverifiable by the shortcut path, and every commit that pins it unbuildable without a
rebuild from the root or a checkpoint. So:

* chain releases are separate GitHub releases (`toolchain-COMMIT`), never matched by
  the snapshot pruner (`scripts/release-snapshots.sh` selects only `snapshot-*`
  releases; P7 adds a test that keeps it that way), and each is protected by a tag
  `toolchain-COMMIT` that is never deleted. (For tower pins the existing escape is a
  `keep/NAME` tag at the commit, which the pruner honours; a chain pin must not depend
  on someone remembering to push one.)
* every release's FOD store path is pushed to Cachix (`badlydrawnwizards`) and pinned
  there (`cachix pin`, without `--keep-revisions` limits), so Cachix's garbage
  collection does not drop it;
* the set of releases that must exist is the set of hashes in `wizc-toolchain.json`
  across master's history; the audit checks each one is fetchable from both GitHub and
  Cachix (a `nix store prefetch-file`/`nix path-info --store` probe, no download needed
  for Cachix);
* a mirror that only adds copies (any URL in `urls`) is welcome; none is required.

Retention is cheap: one tarball per commit that changes `selfhost/` (a static RC
executable, a few MB compressed).

## The periodic audit

A scheduled job (once the chain is active; weekly is enough) rebuilds every link since
the last checkpoint from the checkpoint's locally built release, compares each sha256
with the pin of the next commit, and on success moves the checkpoint (a tag
`chain-checkpoint`, pointing at the last verified link). Every eighth audit also
rebuilds the root from the Lean host. A failure opens an issue naming the first link
that did not reproduce and what differed (`scripts/repro-fixpoint.sh --compare`).

**A missing release.** When the retention check finds a pinned release absent from a
source (pruned, deleted, or the cache lost it), the audit rebuilds it from source: it
takes the nearest verified predecessor (the checkpoint, or the root from the Lean host),
runs `step` for each link up to the missing one, and compares the rebuilt tarball's
sha256 with the pin. Equal: the rebuilt file is the release (the hash proves it), so the
audit re-uploads it to every source that lost it and records the restoration in the
issue. Different: the link is unverifiable, which is a chain failure, not a retention
one; the issue says so and nothing is re-uploaded. A missing release is never replaced
by bytes that do not match the pin.

## Prerequisites before the root

| # | what | state |
|---|---|---|
| P1 | fixpoint in both modes, three stages | holds today (scheduled `fixpoint.yml`, GC; the bootstrap-seed prototype for RC) |
| P2 | Lean-free assembly of `self.wiz`: today `Wiz/Selfhost.lean` strips imports, concatenates the files and computes `toolchainId` with Lean's string hash | open: move it into the self-hosted driver (or a POSIX script) with a sha256-based id |
| P3 | cross-directory and cross-machine reproducibility | see "Measurements" |
| P4 | the parity bar | open (the parity matrix's blocking rows) |
| P5 | a local builder with a key, and a dispatch-only workflow that builds and attests | open |
| P6 | tower reads a hash in `wiz-toolchain` | open |
| P7 | retention: `toolchain-*` releases excluded from pruning, Cachix pins, the audit's fetchability check | open |

## Measurements

Run on x86_64 Linux (NixOS, gcc 16.2.0, nixpkgs `02c087f3`), 2026-11-16.

### Reproducibility of the fixpoint (collector mode), across two builds

`heavy --mem 6G bash scripts/repro-fixpoint.sh --stages 2 --keep`, two copies of
master `d23473da` plus this branch's `scripts/`:

| | build A | build B |
|---|---|---|
| directory | `…/repro/a/wiz` | `…/repro/b-a-longer-directory-name/src/wiz` |
| `TMPDIR`, `HOME` | `tmp-a`, `home-a` | `tmp-b-longer/x`, `home-b-longer` |
| locale, time zone, umask | `C`, `UTC`, 022 | `C.UTF-8`, `Asia/Kathmandu`, 077 |
| `SOURCE_DATE_EPOCH` | unset | 1234567890 |
| parallelism | `GC_MARKERS=1`, `LEAN_NUM_THREADS=1`, `-j1`, all allowed CPUs | collector and Lean defaults, `-j8`, `taskset -c 0,1` |
| environment | `env -i` plus the toolchain | the same plus `USER`/`LOGNAME` changed and an unrelated variable |

| artifact | sha256 (both builds) | result |
|---|---|---|
| `compiler.wiz` | `4a1ff239…3fe1` | same |
| `self.wiz` | `9aacf779…7dad` | same |
| `compiler` (stage 1, built by the Lean `wiz`) | `6bdebfac…e0a7` | same |
| `self1.c` | `88e12067…d8d7` (8,299,762 B) | same |
| `stage2` (cc of `self1.c`) | `5707cfcf…2d86` | same |
| `self2.c` | `88e12067…d8d7` (= `self1.c`) | same |

**6 of 6 byte-identical**, and each build reached the fixpoint (`self1.c = self2.c`).
Per build: Lean `wiz build` of the compiler 199–204 s (2.6 GB), stage 1's self-compile
40–45 s (0.7 GB), cc 150–175 s (2.6 GB), stage 2's self-compile 825–834 s with a
**peak of 6.3 GB**. Declare **7G** for a fixpoint job, not 6G (the scripts' comments
and `fixpoint.yml` still say 6).

Caveats: both builds ran on one machine as one user (the Nix sandbox build below
varies the user), and build B's Lake step replayed modules from the shared Lake cache
that build A had filled, so the Lean host was not built twice: the comparison covers
everything from the generated sources on. `scripts/check-repro.sh --compiler` is the
check for the Lean host's own reproducibility.

**Nondeterminism found and fixed:** cc writes the source's base name into the
executable's symbol table, so stage executables compiled from `self1.c` and `self2.c`
differed although the C was identical. `scripts/fixpoint.sh` and the Nix stages now
compile a copy named `wizc.c`. **Found and not fixed:** an executable built in the
dev environment carries that environment's RUNPATH (the cc wrapper adds the Nix
profile's library directories), so a dev-shell build and a sandbox build of the same C
differ; the chain uses only the Nix build, and the static release has no RUNPATH.
