# A witnessed transparency log for cache generations

A cache layer's generation index (`manifest.sexpr`) can be signed with an offline key
([cache-signing.md](cache-signing.md)). That makes one index authentic, but it does not stop
a writer who holds the key from showing two different signed indexes to two clients (a
**split view**), and it does not stop a mirror from replaying an older signed index (a
**rollback**). A pinned `--min-generation` catches the rollback for one client; a log with a
witness is the durable shape.

This note describes the **P4** piece: an append-only, signed log of cache generations, an
RFC 6962 inclusion proof for any entry, a `prev` hash chain, and an offline **monitor** that
compares a layer's log with a local witness file. It is a local file format and a local
witness, not a public log. Section "Sigsum and Rekor" maps the pieces onto the two public
designs Wiz does not operate; section "Limits" says exactly what this does and does not buy.

The code is `Wiz/Cache/Transparency.lean` (namespace `Wiz.Cache`), the CLI is in `Main.lean`
(`wiz cache log …`, `wiz cache monitor`), and the tests are in `Tests/Grail.lean`, group
`toolchain`.

## Layout

```
<cache>/manifest.sexpr              the current generation index (P1)
<cache>/manifest.sexpr.sig          its detached SSHSIG (P3)
<cache>/log/entries/00000000.sexpr      one logged generation, exact bytes
<cache>/log/entries/00000000.sexpr.sig  SSHSIG over those bytes
<cache>/log/checkpoint.sexpr            signed tree head over all entries
<cache>/log/checkpoint.sexpr.sig        SSHSIG over the checkpoint

<witness>                           the last checkpoint a monitor accepted (not in the cache)
```

One file per entry makes appends atomic (`writeAtomic`: temporary name, then rename) and
keeps the log append-only by construction: an existing entry is never rewritten. The
zero-padded eight-digit index makes directory order equal log order. The checkpoint is a
small signed object, so a witness stores one digest pair instead of the whole log.

## The entry

```
(log-entry
  (format 1)
  (index 41)
  (prev "sha256-hex-of-entry-40-bytes" | "")
  (generation 17)
  (root "the generation index's Merkle root")
  (manifest "sha256 of manifest.sexpr bytes")
  (manifest-sig "sha256 of manifest.sexpr.sig bytes")
  (valid-until 1767225600)
  (timestamp 1764690000))
```

* `index` is the position in the log; `readLogFiles` rejects a file whose own index is not
  its position (a gap, a deleted middle entry, or a rename).
* `prev` is the SHA-256 of the previous entry's **exact bytes** (`""` for entry 0). This is
  a hash chain: rewriting any entry breaks every later `prev`, even if the attacker can
  sign the rewritten entry.
* `generation`, `root`, `manifest`, `manifest-sig` bind the entry to the signed generation
  index it logs. `append` records the digest of the bytes as they are on disk, so a later
  change to the index or its signature is visible without trusting the index's own root.
* `generation` must be strictly larger than the previous entry's. This is the local
  monotonicity check; `prev` is the fork check.
* `timestamp` is the appender's Unix time. It is **not** a trusted timestamp: the log has no
  trusted clock, and a signer can choose it. The order comes from the chain and the index,
  not from the timestamp.
* Every entry is signed in the SSHSIG namespace `wiz-cache-transparency`. The signature
  covers the exact entry bytes, so a signature cannot be moved to another index.

`append` refuses to run when:

* the generation index is missing, not self-consistent, or unsigned;
* `--signers` was given and the index signature does not verify under that allowlist;
* the index generation is not newer than the last logged generation;
* the index `prev` is not the last logged index root (a re-sealed index that descends from
  a different history is a fork or a rollback, even if its generation is higher).

The last two checks are the `prev`/rollback checks. Together with the entry chain they mean
a log is extended, never replaced.

## The checkpoint

```
(checkpoint
  (format 1)
  (size 42)
  (root "RFC 6962 root over the 42 entry leaves")
  (head "SHA-256 of entry 41's bytes")
  (generation 17)
  (timestamp 1764690000))
```

`root` is the Merkle root over the entry leaf hashes (same `0x00` leaf / `0x01` node
separation as the cache manifests; the leaf domain is `wiz-log-entry-v1`). `head` is the
last entry's byte hash, so a witness can check that an older head is still a prefix without
a Merkle consistency proof. `generation` is the latest cache generation the log names.
`checkpoint.sexpr` and its SSHSIG are rewritten on each append (the checkpoint is not
append-only; the entries are).

## Inclusion proofs

```
wiz cache log prove --cache DIR --index N --out proof.sexpr
```

writes an RFC 6962 audit path:

```
(inclusion-proof
  (format 1)
  (index 41) (size 42)
  (leaf "hex of the entry's leaf hash")
  (path ((left "hex") (right "hex") …)))
```

`verify` (or `wiz cache log verify --proof proof.sexpr`) recomputes the root from the leaf
and the siblings and compares it with the signed checkpoint's `root`. It also checks the
proof's size against the checkpoint and the leaf against the entry's bytes. A proof for a
leaf that is not in the checkpoint, a wrong side, a changed digest, or a wrong index is
rejected. The proof is small: `O(log n)` digests.

## Verification and the offline monitor

```
wiz cache log verify --cache DIR --signers allowed_signers [--key-id ID] [--proof FILE]
wiz cache monitor    --cache DIR --signers allowed_signers --witness FILE [--key-id ID]
```

`log verify` is entirely offline. It checks, in order:

1. entry files are contiguous and each `index` matches its position;
2. the `prev` chain and strictly increasing generations;
3. every entry signature under the `allowed_signers` policy (same key ids/fingerprints as
   cache signing);
4. `checkpoint.sexpr` equals the checkpoint computed from the entries, and its signature
   verifies;
5. when the layer has `manifest.sexpr`: its generation is the logged generation (a lower
   one is a rollback; a higher one means the index was resealed and the log has not been
   appended yet), and its bytes, signature bytes and root match the last entry;
6. with `--proof`: the inclusion proof is valid against the checkpoint.

Exit status is 0 only when the log is consistent **and current**. A log that is behind a
newer signed index is a failure (`cache log verify` says to run `cache log append`;
`--allow-behind` accepts an intentionally not-yet-logged layer). A malformed or missing
entry, checkpoint, signature or index is a failure, never a silent skip.

`monitor` runs the same checks and then compares the checkpoint with a **witness file**:

```
(witness (format 1) (size 42) (root "…") (head "…") (generation 17) (updated 1764690000))
```

* no witness → `new`: write it, exit 0;
* log extends the witness (`size ≥`, witnessed head is the prefix's head and root) → `ok`:
  advance the witness, exit 0;
* log is shorter or names a lower generation → `rollback`, exit 1, witness untouched;
* the witnessed head/root is not a prefix of the log → `fork`, exit 1, witness untouched;
* any verification error → `tamper`, exit 1, witness untouched;
* the index is newer than the log → `behind`, exit 1 (run `append`).

The witness is ordinary local state and is deliberately **not** signed: a signature on it
would only move the key problem, not solve it. Keep it outside the cache directory and,
for a meaningful split-view check, on a different machine from the cache server. One
witness belongs to one layer; `monitor` refuses to guess when several layers are named.
A cron/systemd timer running `wiz cache monitor` and alerting on a non-zero exit is the
whole "monitor" deployment. There is no daemon and no network.

Typical release workflow:

```
wiz cache manifest --cache DIR --valid-days 30
wiz cache sign     --cache DIR --key /offline/release.key --key-id wiz-release-1
wiz cache log append --cache DIR --key /offline/release.key --key-id wiz-release-1 \
  --signers allowed_signers
# clients, from another machine:
wiz cache log verify --cache DIR --signers allowed_signers --proof proof.sexpr
wiz cache monitor    --cache DIR --signers allowed_signers --witness ~/.local/state/wiz/DIR.witness
```

`append` needs the signing key for the entry and checkpoint signatures. If the release key
must stay offline, sign the index on the offline host, copy `manifest.sexpr` and
`manifest.sexpr.sig` to the log host, then run `append` with a key that is allowed to sign
log entries (the two signatures need not be the same key; the allowlist decides both). The
log never reads a private key into the cache.

## Counts

The commands print what they checked, so a monitor log line is a small report:

* `cache log append`: `entry I, N entries, generation G, root R`;
* `cache log verify`: `N entries, generation G, root R: signatures valid (KEY)` or the
  list of errors, plus `behind` when the index is newer;
* `cache monitor`: status, `N entries`, `generation G`, `root R`, and `(witness updated)`.

The `toolchain` test group has three transparency cases (append/inclusion/tamper,
prev-chain/witness rollback, forked history). The group as a whole is 18 cases after this
change (15 before, plus the three here); the transparency cases take roughly 10 s each on
the shared machine.

## Sigsum and Rekor

This is the same shape as the public systems, with the log and the witnesses kept local.
The mapping is deliberately one-way: the file format is Wiz's, but the fields and
verification steps have public analogues, so a future move to a public log is a transport
change, not a redesign.

| Wiz (this change) | Sigsum | Rekor |
|---|---|---|
| signed generation index (`manifest.sexpr` + `.sig`) | a **signed checksum** submission (`sigsum-submit`): the submitter signs the checksum | an artifact/signature entry (`hashedrekord`, DSSE, …) in a log entry |
| log entry (`log/entries/N.sexpr` + `.sig`) | the log's leaf for that submission | the log entry body + its `logIndex` and `integratedTime` |
| entry leaf hash (`0x00` domain `wiz-log-entry-v1`) | RFC 6962 leaf hash of the submitted checksum | RFC 6962 leaf hash of the entry body |
| `prev` chain + `index` | the log's leaf order and Merkle tree | the log's `logIndex` / tree |
| signed checkpoint (size, root, head, generation) | the signed **tree head** | the signed **checkpoint** / signed entry timestamp (SET) |
| `allowed_signers` for the log key | the log's public key in the policy | Rekor's public key / trust root |
| inclusion proof (`log prove`) | `sigsum-verify` inclusion proof | `rekor-cli verify --inclusion` |
| witness file + `cache monitor` | a **witness** cosigning the tree head, and a monitor with a saved head | a monitor/checkpoint with `rekor-cli` or a transparency monitor |
| `--witness FILE`, offline, local | a witness key and a witness state, usually a separate operator | a monitor's persisted checkpoint |

What does not map: Sigsum's **cosigning witnesses** produce a quorum of signatures over
the tree head; here the witness is one local file with no signature and no quorum. Rekor's
`integratedTime` is a log-asserted time; the Wiz entry `timestamp` is only the appender's
clock. A real public deployment would replace the local checkpoint with a cosigned tree
head and the witness file with an independent monitor, and would publish the log's public
key.

## Limits

Call this **tamper-evident against a mirror that cannot rewrite the witness**, not
"tamper-proof" and not "transparency" without qualification.

* **One local witness is a local file.** An attacker who can write the cache and the
  witness can rewrite both. The monitor is useful when the witness lives on another machine
  or in a different account, and when the cache is a read-only mirror.
* **No public log and no quorum.** A writer can still show two different logs to two
  monitors (split view) unless the monitors compare witnesses out of band. The log detects
  this only after the fact, at a monitor that has seen both heads.
* **A compromised log key signs a false entry.** Signatures authenticate the logger, not
  the truth of the build; a valid log entry can name a wrong generation. The witness
  confines a compromise to entries after the last witnessed head, nothing more.
* **No trusted time.** `timestamp` and `valid-until` are inputs. An expired index is
  rejected by the existing verifier, and a witness pins order, but neither proves when an
  entry was made.
* **The log is not required for a local build.** A cache without `log/` works exactly as
  before; `cache verify` and `cache log verify` are separate checks. A plain `wiz check`
  does not consult the log, so it does not pay its cost.
* **Deletion is detectable only if a witness exists.** With no witness, deleting the log
  or the whole cache is indistinguishable from a fresh cache.
* **`ssh-keygen` is required** for signing and for signature verification, as for cache
  signing. The cache format and the log format do not depend on it.
* **No consistency proof.** The monitor checks that the witnessed head is a prefix by
  hashing the prefix (it has the whole log). A remote monitor that keeps only a head would
  need an RFC 6962 consistency proof, which this change does not implement.

## Tests

The `toolchain` group, cases 8–10:

* **append, inclusion proof, tamper**: append two signed generations; `log verify` names
  both; `log prove` and `log verify --proof` accept each entry; a changed proof leaf, a
  changed entry byte, and a deleted `manifest.sexpr.sig` are rejected; a generation that is
  already logged cannot be appended twice.
* **prev chain, witness rollback**: a pure `checkChain` test rejects a rewritten `prev`;
  the first `monitor` is `new`, the second advances the witness; restoring the first
  generation's index, signature and a consistent size-1 checkpoint makes `monitor` report
  `rollback` and leave the witness at size 2.
* **forked history**: two entries are rewritten with the same indices and generations,
  re-signed, and the checkpoint is recomputed; the log verifies on its own but `monitor`
  reports `fork`, because the witnessed head is not a prefix of the rewritten history.

Keys are ephemeral Ed25519 keys under the test's temporary directory; none is stored in the
repository. The witness and proof files are under temporary directories too.
