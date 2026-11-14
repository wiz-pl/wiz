# The `grail-index` repository

The registry (23m, [../23-grail.md](../23-grail.md)) splits package distribution into a
manifest, a static index and a lock. This section describes the index repository itself:
its layout, how entries are generated, how they are checked, and what its trust story is
(and is not). The runnable example is `examples/grail-index/`; the schema is unchanged for
clients unless an entry opts into the new module fields.

## Layout

```
grail-index/
  index.wiz                    the index's own manifest (Wiz code)
  registry.sexpr               name, format, updated (plain S-expression metadata)
  index/NAME.sexpr             the static index: one file per package
  entries/NAME.sexpr.in        templates the generator fills in
  sources/NAME-VERSION/        unpacked sources; the generator's input
  packages/NAME-VERSION.tar.gz deterministic release archives
  make.sh                      the generator (archives, hashes, index files)
  index.sexpr                  the single-file form (every package in one document)
```

`grail update` reads only `index/*.sexpr` (or `index.sexpr`, or a git URL's checkout).
It never evaluates `index.wiz`: that file is for authors and for `grail index check`, so
reading an index stays "parse text", not "run code". `registry.sexpr` is metadata; the
resolver does not need it, but a mirror or a dashboard can read it without Wiz.

### `index.wiz`

```wiz
import Grail

def index : Index :=
  Index.new "wiz-pl/grail-index"
    |> Index.withFormat 1
    |> Index.package "base"
    |> Index.package "text"
    |> Index.package "hello"
```

`grail index check` evaluates `Index.render index` and checks that its name and format
agree with `registry.sexpr`, that every listed package has an `index/NAME.sexpr`, and that
every `index/NAME.sexpr` is listed. `Index.new` defaults to format 1; `Index.withFormat` and
`Index.package` are the combinators (`lib/Grail.wiz`).

## The entry schema

The entry is one S-expression file per package; the field table is in 23m. The static
index side adds two optional fields for module checking:

```lisp
(index
  (package "alpha"
    (summary "…") (repo "…")
    (version "1.2.0"
      (source "packages/alpha-1.2.0.tar.gz")
      (sha256 "…")
      (toolchain ">=0.1.0 <0.3.0")
      (modules "Alpha" "Alpha.Ctrl")
      (prefix "Alpha")
      (deps (dep "base" "^0.1")))))
```

* `(modules M…)`: the module names this release provides. `grail publish` computes them
  from the archive and the package's `lib` roots (`src/Greet/Hello.wiz` → `Greet.Hello`).
* `(prefix P)`: a dotted prefix the package reserves for future modules. It conflicts
  with any *other* package's module or prefix below it.
* Both are optional and unknown to an older grail, which ignores them (R3). An entry with
  neither is accepted exactly as before; only entries that opt in are checked.

`(size BYTES)` (the endless-data cap, R19) is **not** in this schema yet; the checker
therefore trusts the local tar and `--fetch`'s `curl` with no maximum. That is a known gap
(see "What is missing").

## Generation rules

1. **Sources before archives.** `sources/NAME-VERSION/` holds the release (its `grail.wiz`
   and `lib` roots). The archive is made from it and never edited afterwards.
2. **Archives are deterministic.** The example uses
   `tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner … | gzip -n`. A real
   index built from git tags uses `scripts/grail-archive.sh`, which is
   `git archive --prefix=NAME-VERSION/ COMMIT | gzip -n`; both make the SHA-256 a function
   of the source commit, so anyone can re-derive it (R18's check, done in the index's CI
   when the tag is available).
3. **Entries are generated, then reviewed.** `make.sh` renders `entries/NAME.sexpr.in`
   into `index/NAME.sexpr`, replacing `@SHA:NAME-VERSION@` with the archive's hash, and
   concatenates the package nodes into the single-file `index.sexpr`. To publish, add
   `sources/NAME-VERSION/` and a template, run `make.sh`, and open a pull request.
   `grail publish ARCHIVE --source URL` prints the `(version …)` node from the package's
   manifest and archive, including `(modules …)`.
4. **`index.wiz` lists exactly the packages on disk.** `registry.sexpr` repeats the index
   name and format for non-Wiz readers.
5. **`name@version` is immutable.** Edit neither a published `(version …)` nor its
   archive; publish a new version. A bad release is `(yanked VERSION "why")`, which stops
   new resolutions while old locks keep working (fetch never reads the index).
6. **`source` may be relative.** A relative source resolves against the index root, which
   makes a checkout, a mirror and an air-gapped copy self-contained. A hosted index uses
   absolute `https://` release URLs; the schema accepts both.

The example's `make.sh` is deliberately small and shell-only: `tar`, `gzip` and
`sha256sum`, no network and no clock.

## Consuming an index

`grail update` and `grail index resolve/show` accept:

| spec | read as |
|---|---|
| a directory | `SPEC/index/*.sexpr` (or `SPEC/*.sexpr`); uncommitted edits are visible |
| a file | one document holding several packages (`index.sexpr`) |
| a git URL or bare repository path | cloned into the cache, read at the tip or at `URL#COMMIT` |

`--index`, `Package.set "index"` and `grail.local.wiz` choose it; the lock records the URL
and commit. `--offline` reads the cached clone and refuses when there is none. A URL index
must fast-forward from the lock's commit unless `--allow-rewind` (R22). The tests exercise
the directory, the single-file and the `file://` git forms against the example.

## Checking an index

```sh
scripts/grail-index-check.sh examples/grail-index
# or
grail index check examples/grail-index
```

The check **makes no network requests by default**. It validates:

* package and dependency names (`[a-z][a-z0-9-]{0,63}`, or the scoped `@org/name` the
  reader already accepts), and duplicate package entries (the reader refuses those);
* every version parses and appears once; every `toolchain` and every `deps` requirement
  parses as a form of semver (the same parser the resolver uses);
* every `sha256` is 64 lowercase hex digits;
* every **local** archive (`packages/…`, a relative path or `file://`): it exists, its
  SHA-256 is recomputed and must equal the entry, and its layout is the fixed
  `NAME-VERSION/` with a `grail.wiz`;
* module names are dotted identifiers, and no two *different* packages claim overlapping
  module prefixes (the rule below);
* `index.wiz` agrees with `registry.sexpr` and with the files on disk (format 1).

Remote `https://` archives are counted (`N remote not verified`) and not touched. With
`--fetch`, the checker clones a URL index and downloads remote archives into a temporary
directory, verifies their hash and layout, and deletes them.

Exit status is 1 when any error is found; warnings (for example a dependency that another
index provides, i.e. an overlay) do not fail. CI runs the script on
`examples/grail-index` in the build job, so the example cannot rot; the `=grail-index`
test group covers the failure modes.

The resolver has the same module rule: `Resolve.resolve` refuses a selection in which two
packages overlap, naming both packages, both versions and the clashing names. That is the
runtime half of R32; the checker is the audit half, which can report a conflict before
anyone resolves the pair.

### The module-prefix rule

Wiz has one global module namespace (23b, "one name, one declaration"): a package's
modules are `Ddr3.Ctrl`, not `ddr3::Ctrl`. Two packages with valid, distinct registry
names can therefore collide at `import`. Because a package may grow a new module in a
later release, the check is on **dotted prefixes**, not only exact names: `Ddr3` and
`Ddr3.Ctrl` overlap (either is a prefix of the other at a dot), while `Ddr3` and `Ddr3x`
do not. It is conservative on purpose: an entry that lists only exact modules still
conflicts with a package that reserves their common prefix. The escape hatch is to not
select both; scopes (`@org/name`) prevent name squatting, not module collisions.

## Hosting

The index needs a git host, not a service. Any of these work, with no client change:

* a public repository (`https://github.com/wiz-pl/grail-index` is the intended one);
* an organisation's private clone (the same URL, with the org's credentials);
* a static HTTP mirror of the checkout served over HTTPS (the client clones it; the
  Cargo-sparse-style "one file per package over HTTP" is not implemented, R-§2.3);
* a directory or `file://` URL for a review, a test, or an air-gapped install;
* `index.sexpr` alone, for a small mirror that does not want a git repository.

Availability is the host's; there is no API, token, database or upload endpoint. A mirror
is just a copy of the tree plus the archives, and `grail index check MIRROR` verifies it
offline. Archive URLs are immutable by contract, so a mirror may serve them from anywhere
the client can reach.

## Signing and transparency

Today the trust story is: **SHA-256 for bytes, git for history, HTTPS for transport,
review for names.** A lock pins name, version, source and hash, so a changed archive is
detected; a force-pushed index is refused when a lock records an older commit. None of
that is a signature: a first-time user has no baseline, and the index's own history is
only an audit log if someone can see it. The index is **not signed**, and there is **no
transparency log**. Do not describe a hash as authorship.

Three stages would close the gaps; the first is cheap and none require a new server.

**Stage 1 — signed index tags.** Tag index states (`index-2026-11-14`), sign with an SSH
or GPG key (`git tag -s`), and add `grail update --require-signature`, which runs
`git verify-tag`/`git verify-commit` and records `(index URL COMMIT TAG)` in the lock.
Precedent: Debian's `InRelease` is exactly a signature over the index's own metadata.
What is missing: an `allowed_signers`/keyring policy, the flag and the lock field, and a
release process for the key. It gives authorship for a tag, not freshness.

**Stage 2 — a signed snapshot.** `index/snapshot.sexpr` lists every `name@version` with
its SHA-256 and size, plus `(seq N)` and `(updated T)`, and `snapshot.sexpr.minisig` (or
an SSH signature) signs it. Clients verify one signature, then read entries; a monotone
`seq` and an `updated` timestamp give rollback and freeze protection, and the snapshot's
hash chain covers mix-and-match. This is TUF's targets+timestamp collapsed into two
files, keeping the "static text" property. What is missing: the file format, a signature
checker in Lean, the client policy for "too old" and `(seq)` rollback, and key rotation.
Until it exists, `grail update` cannot tell a stale mirror from a fresh one.

**Stage 3 — provenance and a transparency log.** PEP 740-style attestations (Sigstore,
in-toto `Statement`, a `predicateType` for a Wiz release) attached to a publish PR, and an
append-only log of index states. Sigsum or Rekor would provide inclusion proofs; a
"`grail index log`" over the git history is the poor man's version. What is missing: a
log operator, a client that verifies an inclusion proof, a gossip/monitor story (a log
without clients checking it is a database), and an attestation predicate for Wiz. The
repository's existing attestation vocabulary (`wiz-build-manifest/v1`) is the natural
place to attach it, rather than inventing a second one.

What TUF calls out, mapped to this design:

| TUF attack | covered today? | cheapest closure |
|---|---|---|
| arbitrary installation / wrong software | yes — the lock pins name+version+source+hash | — |
| extraneous dependencies | yes — the lock holds the closure and `checkLocked` refuses an incomplete graph | — |
| rollback (an older index served) | partially — the fast-forward check needs a lock's commit | Stage 1 tag + Stage 2 `(seq)` |
| freeze (a stale index served forever) | **no** | Stage 2 `(updated)` and a client warning after N days |
| mix-and-match (metadata from different epochs) | partially — one commit hashes one tree | Stage 2 snapshot hash |
| endless data | **no** | `(size BYTES)` in the entry and `curl --max-filesize` (R19) |
| key compromise | n/a — no keys | multi-signature root when signing arrives |

## What is missing

* Signed tags and a signature recorded in the lock (`--require-signature`).
* The signed snapshot, its `(seq)`/`(updated)` policy, and key rotation.
* A transparency log (Sigsum/Rekor) and a client that verifies inclusion; this is
  explicitly not implemented.
* `(size BYTES)` and a download cap.
* A tree hash of the unpacked package (lock v3, R20), so a hand-edited file in
  `.grail/packages/NAME` is detected.
* Automatic publish: the review is still the gate. A bot that rebuilds the archive from
  the tag and compares the hash would make rule 2 load-bearing rather than decorative.
* A real hosted `wiz-pl/grail-index` with its first packages; the example here is the
  template, not the deployment.
* The `@org/name` layout is read, but scopes are not enforced in names or manifests.

## Tests

The `=grail-index` group (seven cases) checks the example offline, the CLI's offline
default and its error exit, breaks an archive hash, a requirement and the manifest,
proves a module-prefix conflict both in the checker and in the resolver, resolves the
example as a directory, a single file and a `file://` git URL, and checks that `grail
publish` records module names. The `=grail-deps` group keeps the registry correctness
cases (caret bounds, retraction, `--locked` without re-resolution, rollback, index pins,
archive verification).
