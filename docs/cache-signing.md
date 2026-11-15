# Signing cache manifests

A Wiz cache layer can carry a detached signature over its **generation index**
(`manifest.sexpr`). The signature makes the index authentic to a key holder: a mirror or
another process cannot rewrite the manifest (or the entries it lists) without detection.
It does not prove that the cached result is semantically right, that the signer is honest,
or that another client saw the same generation; those need independent builders and a
witnessed log. The design context is in `wiz-notes/trustix-inspirations.md`; the stage
description is `docs/stages/11-tooling.md`, section 11c.

## What is signed

```
<cache>/manifest.sexpr       the layer's generation index (bytes unchanged by signing)
<cache>/manifest.sexpr.sig   detached SSHSIG over those exact bytes
```

The signature covers the complete generation index: `generation`, `prev`, `valid-until`,
every module record, and `root`. It therefore also covers every per-module manifest digest
named by the index. A signed record cannot be edited, reordered or replaced without
breaking the signature, and `valid-until` cannot be extended.

Signing is additive. `manifest.sexpr` keeps its bytes, and the per-module manifests,
`.wizc`, `.wizr` and `.wizs` files are untouched. Existing SHA-256 checks and the region
checksum work exactly as before; an unsigned layer is byte-identical to a cache written by
an older `wiz`.

## Detached signature format

The sidecar is OpenSSH's **SSHSIG** format, written by `ssh-keygen -Y sign`:

* ASCII armor: `-----BEGIN SSH SIGNATURE-----` … `-----END SSH SIGNATURE-----`;
* namespace: `wiz-cache-manifest`;
* hash algorithm: the OpenSSH default (SHA-512 of the payload);
* payload: the exact bytes of `manifest.sexpr` (no canonicalization, no re-encoding).

The SSHSIG does not carry the signer's identity. Verification therefore needs a policy
file that maps a **key id** (a human label, or the key's `SHA256:` fingerprint) to the
public key. That file is an OpenSSH `allowed_signers` file:

```
# key id, then the public key (as in ssh-keygen -Y sign's own allowlist)
wiz-release-1 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAA... release 1
SHA256:8Zf...  ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAA... release 2
```

A `SHA256:` principal is checked against the actual fingerprint of its line's key, so a
mis-copied fingerprint fails instead of silently accepting the key.

## Signing

```
wiz cache manifest --cache DIR --valid-days 30
wiz cache sign --cache DIR --key /secure/offline/id_ed25519 --key-id wiz-release-1
```

`wiz cache sign` runs `ssh-keygen -Y sign` over each layer's `manifest.sexpr` and writes
`manifest.sexpr.sig`. `--valid-days N` first reseals the index (a new `generation`, with
`valid-until` set) and then signs it. Without `--valid-days`, the existing index is signed
as it stands; the command refuses an index whose root is not self-consistent.

Key handling:

* use an **offline** Ed25519 key, or a key held in a KMS/HSM and exposed through an agent;
  the cache itself never reads a private key and never writes one into a layer;
* do not commit private keys, signing-helper sockets or passphrases to the repository;
* keep the key out of the same trust domain as the cache server and the CI push token — a
  cache server that can sign is indistinguishable from the legitimate writer;
* a release key can sign many generations. `--key-id` is a policy label, not a secret.

`wiz cache sign` prints the generation, root, key id and fingerprint. If `--key-id` is
omitted the fingerprint is used, which can be pasted directly into `allowed_signers`.

## Verifying

```
wiz cache verify --cache DIR --signers trusted_keys \
  --require-signature --key-id wiz-release-1 --min-generation 12
```

`--signers FILE` is the `allowed_signers` allowlist. Any listed key is accepted by default;
`--key-id ID` requires that principal. `--require-signature` fails closed when a layer has
no signature, when the signature does not verify, when it is expired, or when no
`--signers` file was given. `--allow-unsigned` explicitly accepts a missing signature (it
is a deliberate downgrade, and cannot be combined with `--require-signature`). Without
either flag, verification reports the signature state but does not fail on a missing one,
which keeps an ordinary write cache usable.

`--min-generation N` rejects a generation index older than `N`. A signature alone cannot
detect a rollback: an old signed index is still a valid signature. Pin the expected head
(the generation, or the root, in release metadata) and pass it here. A generation index
whose `valid-until` has passed is rejected even if its signature verifies.

The rest of `wiz cache verify` is unchanged: it also compares every manifested entry with
its bytes, counts unmanifested files under `--strict`, and never writes a read-only layer.

## Rotation

1. Generate or activate the new offline key; publish its public key in the policy file as
   a new line (a new key id, or its `SHA256:` fingerprint).
2. Reseal and sign a new generation with the new key:
   `wiz cache manifest ...; wiz cache sign --key NEW --key-id wiz-release-2`.
3. Ship the new key's line together with the new generation. Clients accept either key
   while both lines are present.
4. After clients have a pinned generation from the new key, remove the old key's line and
   publish the policy file. Older signatures made by the old key no longer verify.
   `--min-generation` makes a rollback to an old generation fail even before that.

The `prev` field chains each sealed index to the previous index's root. It is a local hash
chain for audit and for comparing generations; without a pinned head it is not by itself a
rollback defence.

## Revocation

Remove the key's line from `allowed_signers` (or replace the policy file with one that
omits it) and publish that file. Verification then rejects signatures made by that key.
Because this format has no trusted time or append-only log, revocation is not retroactive
and not globally ordered:

* a signature made by the revoked key **before** removal still verifies as long as a
  client has the old policy file;
* a mirror can serve the old policy file together with an old signed generation;
* short `valid-until` values and a pinned `--min-generation` bound that window.

The durable fix is a witnessed append-only log (a later stage): a record signed by the
replacement key says "old key revoked from generation G", and clients that have seen it
reject old-key claims at or after that point. Until then, treat the cache signature as
tamper evidence against a mirror that cannot rewrite the policy, not as a revocation
service.

## Limits

* A valid signature by a compromised signer is accepted. The signature covers the output,
  not the source-to-output relation.
* A signed subset can omit entries; `strict`/`--require-signature` make omissions visible
  only for entries the manifest claims.
* Two clients can be shown different signed generations (split view) without a log or
  witnesses.
* The same Unix user can rewrite the cache, the signature and the policy file; signing is
  not a defence against local malware.
* `ssh-keygen` must be installed for signing and for signature verification. The cache
  format itself does not depend on it, and unsigned caches continue to work.

## Tests

The `toolchain` test group signs an ephemeral cache with a freshly generated Ed25519 key
and covers: a valid signature, key-id and fingerprint allowlists, a wrong key, a tampered
generation index, an expired index, a missing signature under `--require-signature`,
explicit `--allow-unsigned`, and a generation rollback rejected by `--min-generation`.
The keys are created under the test's temporary directory; none is stored in the
repository.
