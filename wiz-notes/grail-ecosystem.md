# Grail's package ecosystem: the model, the weakest link, and the lock audit

**Status.** Review lane `grail-ecosystem`, 2026-11-23. Worktree
`/workspace/wt/grail-ecosystem`, branch `agent/grail-ecosystem` off
`integration/train12` (`3fa0eec95`). Code is on the branch; the note is in the
worktree's `wiz-notes/`. Every `file:line` was read in this tree; section 6 says what
was run and what is reasoned from code. No timing claim is made.

## 0. Verdict

The registry design is sound: a static index of text files, a signed snapshot of the
index state (SSH detached, `(seq)`/`(expires)`/key pin), content-addressed archives, a
shared unpacked store, vendoring, and a v3 lock that pins name/version/source/archive
SHA-256 plus an optional tree hash and command digest. The archive hash is checked
before every unpack and on every use; the signed snapshot covers every security-relevant
field of an entry (via the entry digest); the lock is the only thing a build reads.

**The weakest link is that the lock itself is not signed and its `pkg` entries are
never compared with the signed entries they claim to come from.** When the index is
signed (a required or previously pinned signature), `grail update` checks the resolver's
selection against the snapshot (`snap.checkResolved`, `Registry.lean:715`); after that,
every command trusts the lock's text. A hand-edited `pkg` line -- a different
archive SHA-256 and tree hash, with the bytes supplied by a committed `vendor/`
directory -- has exactly the shape every local check promises, so `update --locked`,
`fetch --locked`, `build --locked` and (before this branch) `index verify --locked` all
accept it. The signature then authenticates an index state that has nothing to do with
the bytes the build installs.

**Fix (implemented).** `Grail.Registry.checkLockEntries` compares every `pkg` entry of
`grail.lock` with the signed snapshot: the version must be listed, and the archive
SHA-256, tree hash and size (when the snapshot records one) must match.
`checkLockSnapshot` reads the lock, and `grail index verify --locked` calls it, which is
the one place the verified snapshot and the committed lock are available offline. A new
`=grail-index` case tampers with the lock's SHA-256 and tree hash and requires exit 1;
it fails on the pre-fix tree and passes with the check.

**Next two items.** (1) Make the lock self-contained: record the signed entries (or at
least each pkg's signed entry digest) in lock v4, so `fetch --locked` can refuse a
tampered lock without an index checkout; today the audit is a separate command, and the
CI command the docs recommend (`update --locked --require-signature`) cannot see the
tamper. (2) Make the tree hash load-bearing after the first unpack: today the
`.grail-pkg` stamp short-circuits `ensurePkg` before any tree hash, so a hand-edited
package tree is not detected on a later build even though three documents say it is;
decide between re-hashing on `--locked` builds and correcting the claim.

---

## 1. The model as it is

### 1.1 Three layers, one writer each

| layer | file | writer | read at |
|---|---|---|---|
| manifest | `grail.wiz` in the package | the author | `grail update`, and every build (targets, lib roots) |
| index | `index/NAME.sexpr` in a git repository | the publisher, by reviewed PR | `grail update`/`index` only |
| lock | `grail.lock` in the consumer | `grail update` | every `build`/`test`/`run`/`lsp`/`doc`/`fetch` |

`Package.require NAME REQ` names a registry package and a semver range; `Package.dep
NAME URL REV` names a git source and a revision. The resolver is flat and greedy: one
version per name (Wiz has one global module namespace), highest version satisfying every
requirement, 64 rounds, no backtracking (`Grail/Index.lean:504`). A version whose
`toolchain` range excludes the running toolchain is filtered out; that is a compatibility
signal, not a trust boundary (`docs/stages/23-grail.md`, 23m).

### 1.2 What `grail.lock` v3 records

`Grail/Deps.lean:39-75` and `:82-111`:

* `(version 3)`, `(toolchain VERSION [REVISION])`, `(index URL COMMIT)`;
* `(index-signature (kind snapshot) (identity …) (key …) (fingerprint …) (expires …)
  (seq N) (updated …) (sha256 …))` -- what was verified at update time;
* `(pkg NAME VERSION SOURCE SHA256 [(size N)] [(tree SHA256)] [(commands SHA256)]
  (deps "NAME REQ" …))` -- one line per package, sorted, flat dependencies;
* `(override NAME PATH TREE)` -- a machine-local `grail.local.wiz` override;
* `(dep NAME URL REV COMMIT CONTENT)` -- a git dependency (v1's 64-bit content hash).

A lock without `(version …)` is read as v1 (git deps only) or v2 (index/pkg entries) by
inspection; a newer format is refused (`Deps.lean:139-144`). `--locked` is a check, not
a resolution: it reads the lock and never touches the index (`Cli.lean:514-534`).

### 1.3 What a fetch and a build verify

`Grail/Registry.lean`:

* **Archive bytes.** `<cache>/grail/downloads/<sha256>` is re-hashed on every use; a
  corrupt or wrongly named file is removed and fetched again (`:383-431`). A `vendor/`
  archive is looked up by hash, not by URL, and its SHA-256 is checked before use
  (`:175-189`, `:395-413`). The download is `curl -fsSL` with a connect timeout, and an
  empty/truncated file is an error (`:193-223`).
* **Extraction.** `tar -t` and `tar -tv` are listed first; absolute or `..` member
  names, escaping or absolute symlink/hardlink targets, devices and fifos refuse the
  whole archive before `tar -x` runs (`:246-364`). `--strip-components=1` is treated
  as a layout rule, not a sanitiser.
* **The tree.** After unpacking into a temporary directory, when the lock has `(tree
  SHA256)`, the sorted `path NUL sha256(content) LF` construction is checked before the
  `.grail-pkg` stamp is written and the tree renamed into the shared store
  (`:85-92`, `:458-490`). The same construction is used by `grail publish`
  (`unpackTreeHash`, `:368-377`), so the index entry's tree and the lock's tree are the
  same function of the archive.
* **The lock's shape.** `checkLocked` (`:742-811`) checks that every manifest
  requirement is pinned and satisfied, the transitive closure is complete, hashes are
  64 lowercase hex digits, the signature entry has the shape a lock promises
  (`Signature.checkFields`), and `--locked` refuses a recorded override. `--locked` reads
  no index, so it checks the signature *entry's shape*, not the signature.
* **The shared store.** `<cache>/grail/packages/<sha256>` is one unpacked tree per
  archive hash; `.grail/packages/NAME` is a symlink to it (or a copy). A second project
  or a second package name with the same bytes reuses the unpack.

### 1.4 What the signature covers

`Grail/Signature.lean`:

* `index/snapshot.sexpr` lists every `name@version` with SHA-256, size, tree, commit,
  entry digest and yank reason, plus `(name)`, `(seq)`, `(updated)`, `(key)` and
  `(expires)`; `index/snapshot.sexpr.sig` is `ssh-keygen -Y sign -n grail-index`.
* The **entry digest** is SHA-256 over the canonical `(version …)` node
  (`Index.entryDigest`, `Index.lean:262-287`), so one signature covers source, archive
  hash, size, tree, command digest, commit, toolchain range, module claims, prefixes and
  dependency edges.
* `covers` requires the snapshot and index to describe exactly the same entries: same
  archive hash, tree, commit, entry digest and yank state; an older snapshot without a
  digest still verifies a minimal entry but refuses one that carries tree/commit/modules/
  deps (`Signature.lean:162-193`).
* `verifySnapshot` uses `ssh-keygen -Y verify` with an `allowed_signers` file from
  outside the index, or the key a lock pinned; it refuses a lower `(seq)`, a same-seq
  rewrite, a changed key/fingerprint, and an expired key (`:372-479`). `(seq)` gives
  rollback protection; the index's git history is separately required to fast-forward
  (`loadIndex.checkRewind`, `Registry.lean:634-644`, `--allow-rewind` to accept a
  rewrite).

### 1.5 The Fate index

`examples/fate-index/` is the template: `index.wiz` (the index's own manifest),
`registry.sexpr`, `index/NAME.sexpr`, deterministic `packages/NAME-VERSION.tar.gz`,
`entries/NAME.sexpr.in`, `make.sh`, and an optional `index/snapshot.sexpr` + `.sig`.
`scripts/grail-index-check.sh examples/fate-index` runs offline in CI
(`.github/workflows/ci.yml:468`) and checks names, versions, requirements, local archive
hashes and layouts, `index.wiz` consistency, module-prefix conflicts, and a signed
snapshot when required. `grail publish` prints the `(version …)` entry from a manifest
and archive (including modules, size, tree, command digest and commit); publishing is a
reviewed PR. What is deployed is still the example: there is no hosted
`wiz-pl/fate-index` with real packages (`docs/stages/23-grail/index-repository.md`,
"What is missing").

## 2. The weakest link: the lock is not bound to the signed state

### 2.1 The gap

`grail update` verifies the selected versions against the signed snapshot before writing
the lock (`Registry.lean:714-715`, `Snapshot.checkResolved`). After that:

* every build reads the lock's `pkg` entries and verifies archives against *those*
  values (`ensurePkg`, `fetch`, `lockedRoots`);
* `checkLocked` verifies shapes and requirement satisfaction, not provenance;
* `--locked` reads no index by design (R10);
* `Signature.checkFields` is shape-only, so a lock's `(index-signature …)` can be a
  genuine-looking pin while the `pkg` lines beneath it name different bytes;
* `grail index verify --locked` verified the *index* against the lock's pinned key,
  sequence and digest -- and then printed the signer. It never looked at
  `lock.pkgs`, so it accepted a lock whose entries the signed snapshot did not name.

The signature authenticates a state of the index. The lock is a copy of a *decision*
made from that state, in an unsigned file. Nothing checked the copy.

### 2.2 What a third party can do with that

The realistic actor is not the package author (their bytes are pinned) but anyone who can
change a consumer's `grail.lock` and `vendor/` in one commit -- a contributor, a bot, a
compromised branch -- or a user who edits a lock to "fix" a build. Concretely:

1. take a project whose signed `update` produced `(pkg greet 1.2.0 SOURCE A (tree TA))`;
2. build a different archive that claims the same `greet 1.2.0` layout, hash it as `X`
   and compute its tree `TX`;
3. commit `vendor/X.tar.gz` and a `vendor/index.sexpr` naming it;
4. replace `A` with `X` and `TA` with `TX` in `grail.lock` (or drop `(tree …)`, which a
   v2-shaped lock may do);
5. `grail fetch --locked --offline --vendor vendor && grail build --locked` installs and
   builds the attacker's bytes. `update --locked --require-signature` exits 0 (it is a
   local shape check). Before this branch, `grail index verify --locked` exited 0 too.

The signed snapshot still says `greet 1.2.0` is `A`. Nothing in the consumer's checks
asks it.

### 2.3 Evidence

Pre-fix tree (`integration/train12`, `3fa0eec95`):

* `Grail/Cli.lean:268-285`: the `index verify` branch loads the index with the lock's
  pinned signature and prints `signed by …`; there is no read of `grail.lock` beyond
  `lockSignature` (`Registry.lean:815-819`), which returns only the signature node.
* `Grail/Registry.lean:742-811`: `checkLocked` has no comparison with a `Snapshot`;
  `grep -n checkResolved Grail/*.lean` finds exactly one call, `Registry.lean:715`, in
  `resolveLock` (update).
* `Grail/Signature.lean:544-557`: `checkResolved` exists and is the right comparison,
  but is unreachable from any lock audit.
* `Grail/Registry.lean:458-462`: a warm `.grail-pkg` stamp short-circuits `ensurePkg`
  before the tree hash, so even the tree in the lock is not re-derived on a later build
  (section 4.1).

The deliberate-failure test (section 3.2) is the executable form of this evidence.

## 3. The fix

### 3.1 Code

`Grail/Registry.lean` (new, after `checkLocked`, this branch `:824-850`):

* `checkLockEntries (lock : Lock) (snap : Snapshot)` -- for every `pkg`, require
  `snap.find? name version`; compare `sha256`; compare `tree` when the snapshot records
  one; compare `size` when both record one. A version the snapshot does not list is
  refused.
* `checkLockSnapshot (dir) (snap)` -- read `dir/grail.lock`, parse it, and call the
  above.

`Grail/Cli.lean` (this branch `:282-289`): in `grail index verify`, when `--locked` was
given, after the index has been verified against the lock's pinned signature, call
`checkLockSnapshot` with the verified snapshot. The command now prints the signer only
after the lock audit passes.

Why here, and not `checkLocked`: `checkLocked` runs on every build and must not read the
index (R10), and it does not have the snapshot. `index verify --locked` verifies the
index offline from the lock's pinned key and is documented as the cryptographic check;
it is the only offline place both objects are available. This is a check, not a new
lock format; it closes the audit gap without changing what a build reads.

### 3.2 The deliberate-failure test

`Tests/Groups/GrailIndex.lean`, new case "a lock's registry entries are checked against
the signed snapshot" (skips without `ssh-keygen`, like the other signed cases):

1. a one-package signed index (`signedEntryIndex`, which carries tree, commit and entry
   digest) and a consumer that requires `greet ^1`; `grail update --require-signature
   --allowed-signers …` and `grail index verify INDEX --locked` (exit 0: the honest
   lock);
2. build a **second** `greet 1.2.0` archive from different sources (`hello := 666`),
   hash it as `X`, unpack it for its tree `TX`, and write `vendor/X.tar.gz` +
   `vendor/index.sexpr`;
3. replace the lock's archive SHA-256 with `X` and its tree with `TX`:
   `update --locked --require-signature` still exits 0 (documenting the local-only
   limit), `fetch --locked --offline --vendor vendor` exits 0, and the unpacked
   `src/Greet/Hello.wiz` is the attacker's `666` -- the exploit runs end to end;
4. `index verify --locked` must exit 1 (on the pre-fix tree it prints `signed by …` and
   exits 0, which is where the case fails);
5. replace only the lock's tree hash with 64 `6`s: exit 1; restore the lock: exit 0.

The red run below shows the tampered archive line (`greet 1.2.0 … fetched`) and the
`expected 1 / got 0` at step 4; the green run shows `[40/40] ✓`.

### 3.3 Docs

`docs/stages/23-grail.md` (23m), `docs/stages/23-grail/index-repository.md`,
`docs/building.md` and `docs/install.md` now say that `index verify --locked` also
compares the lock's `pkg` entries with the signed snapshot, and the "what is verified"
list no longer claims a warm package tree is re-hashed on every build (section 4.1).

## 4. Other findings, in order of importance

### 4.1 A warm tree is trusted; the docs say it is checked (next item)

`ensurePkg` returns immediately when `.grail-pkg` equals the archive hash
(`Registry.lean:462`), so the `(tree …)` check at `:480-486` runs only on the unpack
that creates the shared-store entry. `lockedRoots` calls `ensurePkg` and then reads
`grail.wiz`; it does not re-hash the tree (`:1091-1100`). `grail cache verify` checks
that the stamp names the directory, not that the tree matches it (`:933-958`). So after
the first fetch, editing `.grail/packages/NAME/...` (or the shared store itself) is
invisible to `fetch --locked`, `build --locked` and `cache verify`; only removing the
stamp (in the project and in the shared store) forces a re-unpack and the tree check.

Three documents claim otherwise: `docs/stages/23-grail.md` "What is verified" (before
this branch: "a hand-edited file in `.grail/packages/NAME` is refused"),
the shared design note `registry-provenance.md:420,595` ("on every build (`ensurePkg`,
`lockedRoots`)") and the shared `roadmap/packages-next.md:164` ("and on every build").
The shared `sota-registry-supply-chain.md:52` states the actual behaviour ("tree checked at
unpack only"). This is an accident-detection gap, not a third-party attack: an archive
cannot edit the store, and the archive hash pins the bytes that created it. The decision
needed is cost: re-hashing every dependency tree on every build is measurable on a large
dependency set; the alternatives are `--locked`-only re-hashing (CI gets it, a warm local
build does not), or trusting the stamp and correcting the docs. I corrected the user
docs to the current behaviour; the shared design notes still need the same edit or a
code change.

### 4.2 Module claims are trusted, and a package can shadow another package's modules

`(modules …)`/`(prefix …)` are what the resolver's conflict check compares
(`Index.lean:230-238`, `:490-499`), but nothing compares them with what the archive
actually contains. `grail publish` derives the list from the archive; a hand-written
entry can under-declare it. `Ctx.roots` is `[std, dir] ++ libRoots ++ tc.searchPath`
(`Build.lean:40`) and `lockedRoots` appends each `pkg`'s roots in lock order (sorted by
name, `Registry.lean:1091-1100`). If `evil` (sorts first) ships
`src/Crypto/Aes.wiz` while declaring only `Evil`, and the consumer also selects `crypto`,
`import Crypto.Aes` silently resolves to `evil`'s file; `index check` and the resolver
see no conflict. Closing this needs either a trusted module list in the lock (v4) checked
against the unpacked archive, or deriving the modules at `index check --fetch` without
executing the package's `grail.wiz` (which the checker deliberately does not do). Not
fixed: the correct fix is a design choice, and executing untrusted manifests in the
checker is the wrong default.

### 4.3 A relative `source` enters the entry digest as an absolute path

`readIndexDir` resolves a relative `source` against the index root before the entry is
used (`Registry.lean:503-537`). `Sign.ofIndex` is called with those resolved entries
(`Cli.lean:308,323`) and computes `entry := Index.entryDigest v`; `versionNode` renders
`source`. So a snapshot generated at `/home/maint/fate-index` binds
`/home/maint/fate-index/packages/greet-1.0.0.tar.gz`, and a client that reads the same
index from `~/.cache/wiz/grail/index` (or any other checkout) computes a different entry
digest and `covers` refuses a validly signed index. The example index
(`examples/fate-index`) uses exactly this relative layout; it is unsigned today, so the
bug is latent. A hosted index with absolute `https://` sources is unaffected, which is
what the docs recommend. This fails closed (availability, not a security hole), but it
means "a mirror is a byte-copy" is false for a signed index with relative sources. The
clean fix is to keep the written source for the digest and a separate resolved source for
fetching (a small `IxVersion` field); not done here. Found by reading; not run.

### 4.4 Known and documented, not fixed

* **Git dependencies** still use a 64-bit, non-cryptographic `contentHash`
  (`Deps.lean:210-214`); the docs say so plainly. Registry entries are the strong path.
* **`(commands …)`** is recorded in the index/lock and covered by the entry digest, but
  no build or audit recomputes it from the fetched package. It is "visible in a lock
  diff", not enforced.
* **`(size …)`** is checked against local archives by `index check` and the signed
  snapshot, but `fetch`/`curl` has no maximum, so an endless-data source is a disk-fill
  DoS, not detected.
* **The release `commit`** is bound by the signed entry but not copied into the lock
  (v3 has no field); a consumer cannot check the source claim offline. Design says lock
  v4.
* **First use** of an index is TOFU: `--allowed-signers` comes from outside, or
  `--allow-unsigned` accepts an unsigned index. CI/install docs pass
  `--require-signature`; the tool default is off.
* **`index verify --locked`** does not check that the lock's `indexCommit` is an
  ancestor of the index now read (it passes `previous = ""`); the snapshot digest, key
  and sequence are checked, and `update` does the ancestry check.
* **A signed snapshot's `(updated)`** is recorded, never aged; a mirror can serve a
  stale state until `(expires)`.

## 5. Next two items

1. **Make the lock a complete cryptographic statement (lock v4).** Record the signed
   entries in the lock -- at minimum each `pkg`'s signed `entry` digest and `commit`,
   ideally the verified snapshot entry lines -- so `fetch --locked`/`build --locked`
   can refuse a hand-edited `pkg` offline. Then the audit becomes structural instead of
   a separate command, and `update --locked --require-signature` (the CI recipe in
   `docs/install.md`) can no longer pass a tampered lock. Acceptance: the section 3.2
   test passes without `index verify` (the tampered `fetch --locked` exits 1), and a
   v3 lock still parses.
2. **Make the tree hash load-bearing after the first unpack, or stop claiming it.** If
   the answer is "re-hash", do it in `lockedRoots` when `p.tree` is present (and in
   `fetch --locked`), measure the cost on a multi-package lock, and offer an explicit
   escape; if the answer is "trust the stamp", correct `registry-provenance.md:420,595`
   and `roadmap/packages-next.md:164` and say so in 23m. Acceptance: a deliberate-failure
   test that appends a byte to `.grail/packages/NAME/...` and rebuilds either exits 1
   naming the tree, or the docs no longer claim it is refused (a documentation test is
   weaker; prefer the code).

The module-claim gap (4.2) is the next security item after these two; the relative-source
digest (4.3) is a small portability fix that should ride with the next index work.

## 6. Honesty ledger

**Read completely in this tree:** `Grail/Config.lean`, `Grail/Registry.lean`,
`Grail/Index.lean`, `Grail/IndexCheck.lean`, `Grail/Signature.lean`, `Grail/Deps.lean`,
`Grail/New.lean`, `Grail/Build.lean`, `grail.wiz`,
`docs/stages/23-grail.md`, `docs/stages/23-grail/index-repository.md`,
`docs/building.md` (registry section), `docs/install.md` (packages section),
`examples/fate-index/`, `Tests/fixtures/fate-index/`,
`Tests/Groups/GrailIndex.lean`, `Tests/Groups/GrailDeps.lean` (registry cases),
`Tests/Groups/GrailE2E.lean`, and the shared notes `wiz-notes/grail-registry.md`,
`wiz-notes/grail-index-signing.md`, `wiz-notes/registry-provenance.md`,
`wiz-notes/sota-registry-supply-chain.md`, `wiz-notes/roadmap/packages-next.md`.

**Run:**

* red build (test present, `Grail/Registry.lean` and `Grail/Cli.lean` reverted to
  `integration/train12`):
  `heavy --rsync --timeout 3600 -- lake build wiz grail tests` -> rc 0, 629 jobs.
* red test: `heavy --rsync --timeout 3600 -- lake test -- '=grail-index'` -> rc 1,
  `12 passed, 1 failed`; `[13/13]   ✗ a lock's registry entries are checked against the
  signed snapshot` with `expected 1 / got 0`, after the tampered lock's vendored archive
  was fetched (the log line `greet 1.2.0 8788… fetched`). The earlier signed cases
  passed in the same run, so the failure is the new assertion, not the signing setup.
  An intermediate version of the case failed at setup instead (the second archive's
  directory did not exist, so `tarballOf` failed); that was a test bug, fixed, and the
  red run was repeated on the final case. Only the repeated run is counted.
* green build/test (fix restored): `heavy --rsync --timeout 3600 -- lake test --
  '=grail-index' '=grail-deps'` -> rc 0, `40 passed, 0 failed` (`grail-index` 13,
  `grail-deps` 27); `[40/40]   ✓ a lock's registry entries are checked against the
  signed snapshot`, and the case's `fetch --locked --offline` of the tampered lock
  succeeded before the audit refused it (the exploit still works locally; the audit is
  what notices).
* neighbours: `heavy --rsync --timeout 3600 -- lake test -- '=grail-e2e' '=grail-vendor'`
  -> rc 0, `7 passed, 0 failed` (`grail-e2e` 1, `grail-vendor` 6; the latter includes
  "a wrong tree hash is refused before it enters the store").
* an earlier `heavy --sshfs --timeout 1800 -- lake test -- '=grail-index'` was killed at
  its inner limit while re-linking `tests` over sshfs (`STEP … CANCELLED … DUE TO TIME
  LIMIT`); it produced no test result and left a truncated local `tests`, which the next
  `--rsync` build replaced. It is reported, not counted. `--rsync` (local disk) is the
  right transport for a test run that has to link.
* no timing claim: the elapsed figures in those logs are build/test wall time on shared
  nodes, not measurements.

**Not run:** CI (the coordinator's train), the full test suite, a real hosted index,
`ssh-keygen` on a machine without it (the new case skips, as the other signed cases do),
and any performance measurement.

**Operational:** the worktree was created from `integration/train12` as instructed; the
branch `agent/grail-ecosystem` is committed and pushed (no PR, and nothing pushed to
`integration/*`); the tree was left clean apart from the ignored
`grail.local.wiz`/`.lake`/`.scratch`.
