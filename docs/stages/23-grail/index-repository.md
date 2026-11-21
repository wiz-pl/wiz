# The `fate-index` repository

The registry (23m, [../23-grail.md](../23-grail.md)) splits package distribution into a
manifest, a static index and a lock. This section describes the index repository itself:
its layout, how entries are generated, how they are checked, and what its trust story is
(and is not). The runnable example is `examples/fate-index/`; the schema is unchanged for
clients unless an entry opts into the new module fields.

## Layout

```
fate-index/
  index.wiz                    the index's own manifest (Wiz code)
  registry.sexpr               name, format, updated (plain S-expression metadata)
  index/NAME.sexpr             the static index: one file per package
  index/snapshot.sexpr         the signed state (all name@version + SHA-256 + size)
  index/snapshot.sexpr.sig     its detached SSH signature
  entries/NAME.sexpr.in        templates the generator fills in
  sources/NAME-VERSION/        unpacked sources; the generator's input
  packages/NAME-VERSION.tar.gz deterministic release archives
  make.sh                      the generator (archives, hashes, index files)
  index.sexpr                  the single-file form (every package in one document)
```

The snapshot and its signature are **additive**: an index without them is read exactly
as before, and an older grail ignores them. `grail update` requires them with
`--require-signature`, or when the project's lock already pinned a signature; CI and the
install docs pass the flag, and `--allow-unsigned` is the explicit, documented escape for
a registry that has no signed snapshot.

`grail update` reads only the package files `index/NAME.sexpr` (or `index.sexpr`, or a
git URL's checkout); `index/snapshot.sexpr` is the signed state, not a package.
It never evaluates `index.wiz`: that file is for authors and for `grail index check`, so
reading an index stays "parse text", not "run code". `registry.sexpr` is metadata; the
resolver does not need it, but a mirror or a dashboard can read it without Wiz.

### `index.wiz`

```wiz
import Grail

def index : Index :=
  Index.new "wiz-pl/fate-index"
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
      (size 1042)
      (tree "…")
      (commands "…")
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
* `(size BYTES)`, `(tree SHA256)` and `(commands SHA256)` are the integrity fields: the
  archive's length (R19), the hash of its unpacked file tree (R20) and a digest of the
  package's declared `Package.command` set (R36). `grail publish` computes all three and
  records them in the lock (v3); older entries have none, which is accepted. A tree hash
  is checked after every unpack and a hand-edited `.grail/packages/NAME` is refused.
  The checker validates the shape of the hashes and `--fetch`'s download still has no
  maximum (the size is recorded for the lock, not used as a cap yet).

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
   manifest and archive, including `(modules …)`, `(size …)`, `(tree …)` and
   `(commands …)`.
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
| a directory | `SPEC/index/NAME.sexpr` (or `SPEC/*.sexpr`); uncommitted edits are visible |
| a file | one document holding several packages (`index.sexpr`) |
| a git URL or bare repository path | cloned into the cache, read at the tip or at `URL#COMMIT` |

`--index`, `Package.set "index"` and `grail.local.wiz` choose it; the lock records the URL
and commit. `--offline` reads the cached clone and refuses when there is none. A URL index
must fast-forward from the lock's commit unless `--allow-rewind` (R22). The tests exercise
the directory, the single-file and the `file://` git forms against the example.

## Checking an index

```sh
scripts/grail-index-check.sh examples/fate-index
# or
grail index check examples/fate-index
```

The check **makes no network requests by default**. It validates:

* package and dependency names (`[a-z][a-z0-9-]{0,63}`, or the scoped `@org/name` the
  reader already accepts), and duplicate package entries (the reader refuses those);
* every version parses and appears once; every `toolchain` and every `deps` requirement
  parses as a form of semver (the same parser the resolver uses);
* every `sha256` is 64 lowercase hex digits (and, when present, so are `tree` and
  `commands`);
* every **local** archive (`packages/…`, a relative path or `file://`): it exists, its
  SHA-256 is recomputed and must equal the entry, and its layout is the fixed
  `NAME-VERSION/` with a `grail.wiz`;
* module names are dotted identifiers, and no two *different* packages claim overlapping
  module prefixes (the rule below);
* `index.wiz` agrees with `registry.sexpr` and with the files on disk (format 1);
* a signed snapshot, when there is one, verifies and covers exactly the entries and
  archive hashes (`--require-signature` makes a missing or invalid one an error;
  `--allowed-signers FILE` supplies the trust root).

Remote `https://` archives are counted (`N remote not verified`) and not touched. With
`--fetch`, the checker clones a URL index and downloads remote archives into a temporary
directory, verifies their hash and layout, and deletes them.

Exit status is 1 when any error is found; warnings (for example a dependency that another
index provides, i.e. an overlay) do not fail. CI runs the script on
`examples/fate-index` in the build job, so the example cannot rot; the `=grail-index`
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

## Signed snapshots (Stage 1)

One signature over the index's own state closes the first-use gap without a server. The
state is a single document, `index/snapshot.sexpr`:

```lisp
(snapshot
  (name "wiz-pl/fate-index")
  (seq 42)
  (updated "2026-11-15T00:00:00Z")
  (key "SHA256:…")
  (expires "2027-11-15T00:00:00Z")
  (package "base" "0.1.0" "90fab0…" (size 1234))
  (package "hello" "1.0.0" "6c8ecf…" (size 345))
  …)
```

* `(seq N)` is monotone: a newer index state has a larger number. `(updated T)` says
  when it was made; `(key FP)` names the signing key's SHA-256 fingerprint, and
  `(expires T)` bounds how long that key is accepted. `(size BYTES)` is the archive's
  length when the generator could see it (a remote `https://` source omits it).
* `index/snapshot.sexpr.sig` is a detached SSH signature over the exact bytes:
  `ssh-keygen -Y sign -n grail-index -f KEY index/snapshot.sexpr`. Any OpenSSH key type
  works; the namespace is `grail-index`.
* `grail index snapshot INDEX --seq N --updated T --key FP --expires T` writes the
  document (sorted, deterministic) from the entries; the maintainer signs it. The
  sequence defaults to the previous snapshot's plus one.
* The trust root is a `allowed_signers` file passed with `--allowed-signers FILE`. It is
  **not** read from inside the index: whoever can rewrite the snapshot can rewrite a
  file next to it. On first use the file comes from the review/URL policy; afterwards
  `grail.lock` pins the key.

`grail update --require-signature --allowed-signers FILE` verifies the signature with
`ssh-keygen -Y verify` (offline, from the local checkout) and then checks that every
entry and every archive hash is exactly what the signed document lists. It records what
it accepted:

```lisp
(lock
  (index "https://github.com/wiz-pl/fate-index" "<commit>")
  (index-signature (kind snapshot) (identity "release-key")
    (key "ssh-ed25519 AAAA…") (fingerprint "SHA256:…") (expires "2027-11-15T00:00:00Z")
    (seq 42) (updated "2026-11-15T00:00:00Z") (sha256 "<snapshot digest>"))
  …)
```

The lock stores the public key, so later updates verify **without** the network and
without `--allowed-signers`, and refuse (even when the flag is omitted):

* a different fingerprint or key (a silent key change; re-lock deliberately);
* a lower `(seq)` — a rollback — unless `--allow-rewind`;
* the same `(seq)` with different bytes — a rewrite of a published state (never
  accepted);
* an expired key, or an entry/archive hash that disagrees with the snapshot.

`grail index verify INDEX [--locked] [--allowed-signers FILE]` is the offline verifier:
it prints the signer, fingerprint, sequence, expiry and snapshot digest; `--locked` also
requires the snapshot to match `grail.lock` (the key, sequence and digest), which detects a
mirror serving an older or altered index. `grail index check --require-signature` audits
a repository the same way and refuses an unsigned or expired one. A deliberate key
change means removing the lock's `(index-signature …)` (or deleting `grail.lock`) and
updating once with the new `--allowed-signers`; nothing rotates silently.

What this gives: **authorship of an index state** (not of an archive), rollback
protection from `(seq)`, a mix-and-match check from the snapshot digest and entry hashes,
and a definite end date for a key from `(expires)`. What it does not give: a transparency
log or gossip (a mirror can still hide a newer state; `(updated)` is informational), key
rotation beyond re-locking, a "too old" client warning, or a download cap. The signed
`(size)` is recorded and checked against local archives, but `--fetch`'s `curl` still has
no maximum (R19). Signed git tags from the earlier plan are an alternative form that this
implementation does not use.

## Hosting

The index needs a git host, not a service. Any of these work, with no client change:

* a public repository (`https://github.com/wiz-pl/fate-index` is the intended one);
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

The trust story is: **SHA-256 for bytes, a signed snapshot for the index state, git for
history, HTTPS for transport, review for names.** A lock pins name, version, source and
hash, so a changed archive is detected; a force-pushed index is refused when a lock
records an older commit; and a signed snapshot (above) gives a first-time user a baseline
and a sequence number to compare. The index is **not transparent**: there is no log, no
gossip and no monitor. Do not describe a hash as authorship.

Three stages close the gaps; the first is implemented (the snapshot form), and none
require a new server.

**Stage 1 — signed index state. Implemented as a signed snapshot.**
`index/snapshot.sexpr` carries every `name@version`, its SHA-256 and size, the signing
key's fingerprint and expiry, and a monotone `(seq N)`; `index/snapshot.sexpr.sig` is a
detached SSH signature. `grail update --require-signature --allowed-signers FILE`
verifies it offline, and `grail.lock` records the key, fingerprint, sequence and digest
(`index-signature`) so later updates re-verify without the flag. `grail index verify` is
the standalone offline checker. Precedent: Debian's `InRelease` is exactly a signature
over the index's own metadata. The signed-tag form from the original staging
(`git tag -s index-YYYY-MM-DD` plus `git verify-tag`) is **not** implemented; the
snapshot variant covers every entry with one signature and adds `(seq)`.

Remaining in this stage: a release process for the key, and a client policy for a key
rotation that does not require re-locking.

**Stage 2 — freshness and rotation.** A "too old" warning from `(updated)`, rotation
(multi-signature root or a signed key list), and the signed-tag alternative. The client
today sees `(seq)` (rollback) and `(expires)` (an expired key), but a mirror serving an
old snapshot is indistinguishable from a fresh one unless the lock records a newer
sequence.

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
| rollback (an older index served) | yes — the signed snapshot's `(seq)` against the lock (and git's fast-forward check) | — |
| freeze (a stale index served forever) | partially — `(updated)` and `(expires)` are recorded and checked, but there is no "too old" warning | Stage 2 |
| mix-and-match (metadata from different epochs) | yes — one signature covers the snapshot digest, and every entry/archive hash is checked against it | — |
| endless data | partially — `(size BYTES)` is recorded and checked against local archives, but no download cap | `curl --max-filesize` (R19) |
| key compromise | partially — the lock pins one key and rejects a silent change; rotation requires re-locking | multi-signature root (Stage 2) |

## What is missing

* Signed git tags (the snapshot form is implemented; the tag form is not) and a release
  process for the signing key.
* Key rotation without re-locking, and a "too old" freshness warning from `(updated)`.
* A transparency log (Sigsum/Rekor) and a client that verifies inclusion; this is
  explicitly not implemented.
* A download cap: `(size BYTES)` is recorded and checked for shape and against local
  archives, but `curl` still has no maximum (an endless-data attack is not prevented,
  only made visible).
* A SHA-256 tree hash for git dependencies (registry packages have one in lock v3, R20:
  the unpacked tree is checked after every unpack, so a hand-edited file in
  `.grail/packages/NAME` is refused).
* Automatic publish: the review is still the gate. A bot that rebuilds the archive from
  the tag and compares the hash would make rule 2 load-bearing rather than decorative.
* A real hosted `wiz-pl/fate-index` with its first packages; the example here is the
  template, not the deployment.
* The `@org/name` layout is read, but scopes are not enforced in names or manifests.

## Tests

The `=grail-index` group (ten cases) checks the example offline, the CLI's offline
default and its error exit, breaks an archive hash, a requirement and the manifest,
proves a module-prefix conflict both in the checker and in the resolver, resolves the
example as a directory, a single file and a `file://` git URL, and checks that `grail
publish` records module names. Three cases sign a temporary index with a throwaway
Ed25519 key: the lock records the fingerprint/sequence, verification works offline from
the pinned key, and a tampered entry, an unsigned or re-signed-but-wrong snapshot, an
expired key, a lower sequence and a same-sequence rewrite are all refused. The
`=grail-deps` group keeps the registry correctness cases (caret bounds, retraction,
`--locked` without re-resolution, rollback, index pins, archive verification) and adds
four lock v3 cases: a deterministic round-trip, v1/v2 parsing and refusal of a newer
format, an old lock upgraded by `update`, and a `grail.local.wiz` override that
`--locked` refuses.
