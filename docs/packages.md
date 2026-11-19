# Packages, the registry and tower

A Wiz **package** is a directory with a `grail.wiz`, written in Wiz against
`lib/Grail.wiz`. `grail` evaluates the file, reads the result as an S-expression and
builds a graph of jobs (`docs/stages/23-grail.md`, 23d). This page is the path through
the package system: making a package, consuming dependencies, the lock, publishing to an
index, and the toolchain manager that picks which `wiz` and `grail` run. The reference
for the vocabulary is the [Grail module](https://wiz-pl.github.io/wiz/docs/Grail.html); the
design record is [stage 23](stages/23-grail.md) and [stage 26](stages/26-tower.md).

## Creating a package

`grail new NAME` writes the smallest package that builds, runs and tests: a `grail.wiz`,
`src/Main.wiz`, a golden test with its `.expected` file, a `README.md` and a `.gitignore`
for `.grail/` (`docs/stages/23-grail.md`, 23o). An existing non-empty directory is
refused, and the name must start with a letter.

A manifest is ordinary Wiz:

```wiz
import Grail
def package : Package :=
  Package.new "shapes"
    |> Package.lib "shapes" "src"          -- check every module under src/
    |> Package.exe "shapes" "src/Main.wiz" -- compile `main`
    |> Package.tests "golden" "tests"      -- run the *.wiz golden tests under tests/
```

`Package.lib`, `check`, `exe`, `tests`, `selfhost` and `command` add targets;
`Command.new` and its builders describe an external build step
(`lib/Grail.wiz`; `docs/stages/23-grail.md`, 23d and 23i). `Package.set` sets a
`key value` pair.

Machine-specific settings do not belong in the committed manifest: they go in an
uncommitted `grail.local.wiz`, whose `settings : Settings` is merged with the manifest's
(`Grail/Config.lean`; `Grail/Cli.lean`'s usage text; `docs/building.md` tells the story
of the local settings file). A `grail.wiz` and its `grail.local.wiz` are evaluated, not
parsed by a bespoke format, so a build file can use any Wiz function it imports.
(`lib/Grail.wiz`'s module comment still calls this `local`; the name the driver reads is
`settings`.)

`grail build` builds every target (or the ones named); `grail run TARGET` builds and
runs one; `grail test` runs the golden tests; `grail targets` lists them; `grail config`
prints the toolchain (`docs/stages/23-grail.md`, 23d, 23f and 23j). Builds are keyed:
a job whose key directory exists does not run, so a second build runs nothing and an
edit reruns the checks of the files that import what changed (23d, 23g).

## Choosing the toolchain: tower

`tower` is to Wiz what elan is to Lean: it installs toolchains, keeps a `wiz` and a
`grail` shim on `PATH`, and decides which toolchain a directory uses
(`docs/stages/26-tower.md`). A project names its toolchain in a **`wiz-toolchain`** file
at its root (one line: a channel such as `nightly`, a release tag, `master@<sha>`, a
linked name, or a path). `wiz-toolchain.local` next to it is a personal override that is
not committed. Resolution order, first match: an override set with `tower override set`,
then `wiz-toolchain.local`, then `wiz-toolchain`, then the default
(`docs/stages/26-tower.md`). It is a separate file rather than a field of `grail.wiz` so
that tower never has to evaluate a build file to know which toolchain to use (same
source).

The channel a release builds from, the snapshot layout, and the shims are described in
[stage 26](stages/26-tower.md); the toolchain is also what a `grail.wiz` can *require*:
`Package.toolchain ">=0.1 <0.3"` records the range a release was tested with, and the
resolver filters versions whose range excludes the running toolchain
(`docs/stages/23-grail.md`, 23m).

## Consuming dependencies

There are two kinds of dependency, and they stay separate on purpose:

* `Package.dep NAME URL REV` names a **source**: a git URL and a revision.
  `grail update` pins it to a commit and the lock records the commit and a content hash
  (`docs/stages/23-grail.md`, 23h and 23m).
* `Package.require NAME REQ` names a **registry package** and a version range, which
  the index resolves (23m).

```wiz
def package : Package := Package.new "greet"
  |> Package.version "1.2.0"                 -- this release's version
  |> Package.toolchain ">=0.1 <0.3"          -- the Wiz it was tested with
  |> Package.require "std" "^0.1"
  |> Package.require "text" "~1.0.3"
  |> Package.lib "greet" "src"
```

The index is a git repository of text files, `index/NAME.sexpr`, with no server, API or
token: a directory, a `file://` URL, or an `https://` git URL all work. It is chosen by
`--index URL` or `Package.set "index" "URL"` (`grail.local.wiz` wins, as for toolchain
settings). A URL index is cloned once into the cache; `grail update` fetches and resets
it, and `--offline` reads the cached clone (`docs/stages/23-grail.md`, 23m).

The resolver is flat and greedy: one version per name, the highest version satisfying
every requirement, adding that version's index `deps` until the selection is stable;
there is no backtracking, and a conflict names both requesters (23m). A requirement is
an exact version, `^`, `~`, `>=`/`<`, or `*`; prereleases only match a requirement that
names one (23m).

## The lock

`grail update` writes **`grail.lock`**, which is committed. Version 3 records the schema
version, the resolving toolchain, the index URL and commit, the git dependencies, the
registry packages with their archive hash, size, tree hash and command digest, and any
machine-local override (`docs/stages/23-grail.md`, "The lock (v3) and the commands").
Builds, tests, `run`, `lsp` and `doc` read the lock only; with the archives cached they
need neither the index nor the network (23m). A missing lock with `require`/`dep` lines
says `no grail.lock: run grail update`.

The two CI-safe commands are checks, not resolutions:

* `grail update --locked` verifies that every requirement is pinned and satisfied, and
  reads neither the index nor the network; a new upstream release cannot make CI fail.
* `grail fetch --locked --offline` materialises the lock without a network. With
  `grail vendor` the archives can live in the repository, and
  `grail fetch --locked --offline --vendor vendor` is the hermetic prelude
  (`docs/stages/23-grail.md`, 23m and 23n).

`grail vendor [DIR]` copies the lock's registry archives into `DIR` as
`<sha256>.tar.gz` plus an `index.sexpr`, and never rewrites the lock: its `source` stays
the published URL (23n). `grail cache path|list|verify` inspects the shared store
(`<cache>/grail/downloads/<sha256>` and `<cache>/grail/packages/<sha256>`); a corrupt
archive is re-downloaded and every unpacked tree is checked against the lock (23m, 23n).

An override, for local co-development, is `Package.override NAME PATH` in
`grail.local.wiz`: the build takes `NAME` from `PATH` and prints `using override NAME
from PATH`, the lock records it, and `--locked` refuses a lock that records one because
it is machine-local (23m).

## Publishing

Publishing is a **reviewed pull request to the index repository**, not an upload to a
service. The author tags a release and uploads a deterministic archive; `grail publish
ARCHIVE --source URL` reads the manifest, checks the name, version, toolchain and
requirement syntax, checks the archive layout (one `NAME-VERSION/` directory containing
`grail.wiz`), hashes the archive, and prints the `(version …)` entry to paste into
`index/NAME.sexpr` (`docs/stages/23-grail.md`, "Publishing"; `Grail/Registry.lean`). It
does not merge anything: the review (URL resolves, hash matches the release, deps match
the manifest, name untaken) is the gate.

The archive must be reproducible:

```sh
git archive --format=tar --prefix=greet-1.2.0/ COMMIT | gzip -n > greet-1.2.0.tar.gz
```

`gzip -n` drops the filename and timestamp, so the bytes are a function of the commit
(`docs/stages/23-grail.md`, 23m). Names are global and lowercase, and
`name@version` is immutable: a corrected release gets a new version (23m).

An index may also publish a signed snapshot (`index/snapshot.sexpr` plus a detached
`ssh-keygen -Y sign -n grail-index` signature); `grail update --require-signature
--allowed-signers FILE` verifies it, and the lock then records the key, fingerprint,
sequence and digest (23m). **Signature verification is opt-in**: `--require-signature`
defaults to false in the command-line options (`Grail/Cli.lean`), and an index without a
snapshot is read as before. The `allowed_signers` file is a trust root from outside the
index; the copy inside a checkout proves nothing (23m).

**What the registry gives, and what it does not.** It gives naming and integrity: a
version's bytes cannot change without failing every lock's SHA-256 check, and the lock
pins name, version, source and hash. It is not a safety boundary: `grail fetch`
downloads files, and `grail build` evaluates the package's `grail.wiz` (a Wiz program),
compiles its C and runs its commands, with no sandbox. Git `dep` entries keep a 64-bit
content hash (accident detection, not cryptographic); registry entries are the strong
path (`docs/stages/23-grail.md`, "Trust: fetch is not build", and its "What is verified"
list).

The public `wiz-pl/grail-index` is **not in this tree**: stage 23m lists the real index,
its CI naming rules and the first packages as deferred, and describes the intended
layout (`index/NAME.sexpr`, deterministic archives, `index.wiz`) in
[index-repository.md](stages/23-grail/index-repository.md). What is implemented and
tested here is the reader, the resolver, the lock, the publisher's mechanical step, the
vendor/cache store, and the index checker (`grail index check`), not a hosted registry.

## Where the code is

| what | file |
|---|---|
| the build-file vocabulary (`Package`, `Target`, `Command`, `Settings`) | `lib/Grail.wiz` |
| the driver, flags and `grail publish` | `Grail/Cli.lean`, `Grail/Main.lean` |
| the index, resolver, lock, archives and signing | `Grail/Registry.lean` |
| the package graph and job keys | `Grail/Build.lean`, `Grail/Graph.lean`, `Grail/Deps.lean` |
| the toolchain manager | `tower/` (`docs/stages/26-tower.md`) |
| the design record | `docs/stages/23-grail.md`, `docs/stages/26-tower.md` |

## The whole path, in a test

`Tests/Groups/GrailE2E.lean` (`=grail-e2e`) runs this page's path in one temporary
directory: `grail new` writes the packages, a local git repository is the `Package.dep`
source, and a directory index holds the entry `grail publish` printed for an archive
under the same directory. The first package locks, builds and vendors that archive; a
second package then runs `grail update --locked`, `grail fetch --locked --offline` and
`grail build --offline` after the index and the cache have been removed, so the vendor
directory is the only source of the archive. The same test shows that a changed
requirement makes `--locked` (and a build) refuse the stale lock until `grail update`,
that a changed git revision is still governed by the locked commit, and that a missing
vendored archive is an `--offline` error.

The test needs no network. Its one write outside the scenario's directory is the system
temporary directory: `grail publish` unpacks the archive there to compute its tree hash
(`unpackTreeHash`), as do the test helpers that build the tarball.
