# Cache trust domains and the signed generation index

Status: implementation note for `agent/cache-signed-index`, from
`integration/train12` @ `f489cc876` (2026-11-23). The containment baseline is
`bd6a330df`; the companion spec is `wiz-notes/cache-invariants.md` and the threat
survey is `wiz-notes/cache-trust-boundary.md`. No heavy build was run for this lane:
the verification record at the end is static-only.

---

## 1. What is bound, and to what

A cache key commits to the **inputs**; it says nothing about the bytes a layer returns.
The layer's files already form a chain of self-signed digests:

```
key → manifest entry (size, sha256) → .wizc / .wizr bytes
     manifest (root)                → its entries
generation index (root)             → every manifest file + sha256
```

Every link was already checked except the top one. This change adds the top link and,
crucially, makes the run **use** it:

* `manifest.sexpr.sig` is a detached OpenSSH `SSHSIG` over the exact bytes of the
  generation index, namespace `wiz-cache-index` (`ssh-keygen -Y sign`).
* A `--cache-ro` layer is a **signed** domain only when that signature verifies against
  an OpenSSH `allowed_signers` file given by `--cache-signers` (optionally pinned to a
  principal with `--cache-key-id`). The allowlist must live **outside the layer it
  judges**; a layer that ships its own trust root is refused (`cache-signers-in-layer`).
* For a signed layer, `ManifestStore.load` accepts a module manifest only when its file
  name is recorded in the **verified** index and `sha256(manifest bytes)` is the
  recorded digest. The per-module manifest then binds each `.wizc`/`.wizr` exactly as
  before. One signature covers the whole layer transitively.
* The index root is checked for self-consistency (`root == rootOf`) before the
  signature; expiry and an optional `--cache-min-generation` are checked too.
* `sealLayer` now writes a real chain: `generation := old.generation + 1` and
  `prev := old.root` when the old index is self-consistent. It still refuses to rewrite
  a signed layer.

The signature authenticates the **publisher of the layer**, not the claim that an effect
is the elaboration of the key's source. A malicious signer can still sign a forged effect
for any module it lists; that is the remaining soundness gap (§6).

## 2. Trust domains

A layer is admitted under a domain derived from the authentication decision, never from a
field the layer supplies about itself:

| domain | who | writable |
| --- | --- | --- |
| `local` | the one write cache (`--cache`), the user's own process domain; no signature | yes |
| `signed:<key-id>[<SHA256:…>]` | a `--cache-ro` layer whose index verified under an allowlisted principal | no |
| `unsigned:<path>` | a `--cache-ro` layer with **no** signature, explicitly accepted by `--cache-ro-unsigned` | no |

A layer that carries a signature is always judged by it and is **never** downgraded to
`unsigned`: `--cache-ro-unsigned` does not rescue an invalid, orphaned, untrusted,
expired or rolled-back signature. With both flags, a layer that carries a signature is
judged by the policy, while a layer that carries none is accepted under the unsigned
opt-in (the two are different layers, not a fallback for one another). A refused layer
has no domain; it contributes nothing.

## 3. Policy: what a foreign layer may serve

A **signed** `--cache-ro` layer may serve:

* only module manifests recorded in its verified index, with a matching SHA-256;
* only the `.wizc`/`.wizr` files those manifests list, with matching size/SHA-256 (and a
  region must also pass its `.wizs` checksum and `fits` tags);
* text entries, module regions, and the index's expiry — nothing else.

A **signed** layer may **not** serve an unlisted manifest (`cache-manifest-unlisted`), a
manifest whose recorded digest differs (`cache-manifest-digest`, which also poisons the
module key), a file from another layer, or a module for which its index has no record.

An **unsigned** `--cache-ro-unsigned` layer may serve what its manifests list, as
unauthenticated data. It is a distinct, lower domain; it is not promoted to `local`, and
its effects are never copied into the write cache's manifests (only write-cache hits are
recorded there, as before).

The **write cache** is `local`; it may serve its own manifested entries. It is the only
writable layer. A signed layer is read-only even if it is passed as `--cache`: every write
path (`Store.put`, `markSeen`, the `bin/` memos, root pointers, `ManifestStore.writeManifest`,
region write/repair, `sealLayer`, `pruneCache`) refuses it
(`cache-signed-layer-write`). Passing a signed
layer as `--cache` is still a misuse — it is read as `local`, not verified — but it does
not mutate the layer.

Layer order is unchanged: write cache, then each `--cache-ro` in order. A missing module
in one layer falls through to the next. A module whose signed manifest failed its digest
is poisoned, so a later layer cannot hide the tampering.

## 4. New refusal codes

| code | when |
| --- | --- |
| `cache-foreign-refused` | an unsigned `--cache-ro` layer without `--cache-ro-unsigned` |
| `cache-index-signature-orphan` | `manifest.sexpr.sig` without a readable index |
| `cache-index-tampered` | the index root does not cover its metadata/records |
| `cache-index-expired` | the index's `valid-until` has passed |
| `cache-index-rollback` | the index generation is below `--cache-min-generation` |
| `cache-index-signature-unverified` | an index signature with no `--cache-signers` |
| `cache-index-signature-invalid` | `ssh-keygen -Y verify` refused it, or no listed key verified |
| `cache-signers-in-layer` | the allowlist path resolves inside the layer |
| `cache-manifest-unlisted` | a manifest is not recorded in the signed index |
| `cache-manifest-digest` | a manifest's bytes differ from its signed-index record |
| `cache-signed-layer-write` | any write, re-seal or prune of a signed layer |

`wiz cache verify --signers FILE` verifies the index and each manifest's index record;
a layer that carries a signature the scan cannot check now fails the scan rather than
silently passing it, and a read-only layer without any signature fails when a signer
policy is given. `--min-generation N` and `--key-id ID` apply the same policy to the scan.

## 5. Tests

The new cases in `Tests/Groups/GrailToolchain.lean` (static, not yet run on this lane):

1. **signed index / tampering** — a cold layer is sealed and signed; the index verifies;
   a run with the policy serves entries, and a run without an allowlist is fail-closed
   (also with `--cache-ro-unsigned`: a signature is never downgraded); a minimum-generation
   pin rejects the index as a rollback. A flipped index byte is refused; a flipped module
   manifest under the intact signature is refused and counted while an intact module still
   serves; a re-seal chains `generation + 1` and `prev = old root`; the layer is unchanged
   by `pruneCache`, `writeManifest`, `Store.put` and `markSeen`.
2. **foreign trust domain** — layer B signed by key B verifies under its own policy and
   is refused under layer A's policy; a manifest transplanted from B into A is refused by
   A's signed-index digest; an `allowed_signers` file placed inside the layer is refused
   with `cache-signers-in-layer`.
3. **`--cache-ro-unsigned` is never writable** — an unsigned layer with regions is served
   through its manifests and regions; a run with a new command still writes nothing; the
   domain is named `unsigned:<path>`; without the opt-in the same layer is refused as
   `cache-foreign-refused`.
4. **policy flags** — `--cache-signers`, `--cache-key-id`, `--cache-min-generation`
   round-trip through `toFlags`/`parseFlags`, are settable in a build file, and stay out
   of `Toolchain.id`.

The existing `=cache-invariants` cases (T3, T7, T10) remain valid: their unsigned
`--cache-ro` opt-in and `sealLayer … valid-until` calls are unchanged in meaning; the
return type of `sealLayer` grew a "wrote" flag, and their call ignores the result.

## 6. Remaining gaps

1. **Source→effect authenticity is absent.** A signature names a publisher. A malicious
   publisher can sign `theorem bad : False` for its own module, or for a stdlib module it
   lists. Only a kernel re-check of replayed declarations (`Effect.apply` currently uses
   the unchecked `Globals.insert`) or a trusted build attestation closes this. Do not
   describe a signed layer as sound.
2. **Visibility scope.** The index signature authenticates every module record in the
   layer, including stdlib modules. A consumer must trust a signer for *every* module it
   lists, not just the signer's package. Per-module publisher policies are future work.
3. **Rollback.** `generation`/`prev` are now written monotonically by `sealLayer`, but no
   reader follows `prev` and the index itself can be replaced by an older, validly signed
   one. `--cache-min-generation` is a coarse optional pin; a pinned `(generation, root)`
   in `grail.lock` or package metadata would be the real fix.
4. **Key rotation/revocation.** `allowed_signers` is the whole policy: adding a line
   rotates, removing one revokes, and `valid-until` bounds the window. There is no
   transparency log or global ordering, so revocation is not retroactive.
5. **Trust-root location.** The allowlist is refused if it resolves inside the layer,
   but the code does not verify who owns it. It must be installed by the toolchain or
   pinned by the consumer; a world-writable allowlist is a compromised policy.
6. **`--cache-verify off` bypasses this layer.** It has no manifest store, reads `.wizc`
   by fast name in any layer, and serves no regions. It is explicit and documented; it is
   not the default, and a signed index cannot gate it.
7. **Per-layer opt-in.** `--cache-ro-unsigned` and `--cache-signers` are global to the
   process: with several read layers, one policy admits or refuses all of them. The
   `agent/library-reds` per-layer design would be least privilege; this lane does not
   change that interface.
8. **Publish freshness.** Normal runs do not rebuild `manifest.sexpr` (O(cache)). A
   signed layer must be produced explicitly with `wiz cache manifest --cache DIR` then
   `wiz cache sign --cache-ro DIR --key …`; a manifest written after signing is
   unlisted and therefore refused until the layer is re-sealed and re-signed. Re-sealing
   refuses while the signature exists: update a signed layer by building a fresh
   directory, or remove `manifest.sexpr.sig` first (an explicit unfreeze).
9. **Runtime dependency.** Verification shells out to `ssh-keygen`. If it is missing or
   the allowlist is unreadable, the layer is refused (fail closed), never served
   unauthenticated.
10. **Mid-run rewrites.** The index decision is memoized per process and each manifest's
    digest is checked when it is loaded; the region reader re-stats before and after the
    map. A layer that changes under a running process is a miss or a refusal, not a
    wrong effect, but a layer that is mutable for longer is outside the signed model.

## 7. Verification record (static only)

On `agent/cache-signed-index` from `integration/train12` @ `f489cc876`:

* `git diff --check`: clean.
* `scripts/check-docs-style.py`: clean (89 files); `scripts/check-doc-links.py`:
  clean (92 files, 429 links).
* `scripts/check-names.py`: clean (33 pre-existing unbaselined declarations, unchanged
  from the base).
* `scripts/repo-subsets.py --write`: `.github/repo-subsets.json` refreshed for the
  changed docs/lean/tests subsets; `--check` current.
* `scripts/check-shards.py`: not run to completion (it needs
  `.lake/build/bin/tests`). No shard configuration or group registration changed: the
  four cases are additions to the existing `=toolchain` group.
* `lake build`, `lake build wiz tests`, and the new test cases were **not** run: the
  heavy queue is reserved for train11-green. Run `lake build wiz tests`, then the
  `=toolchain` group (the four cases above), and
  `scripts/ci.py check-shards` with the built driver before merging.
