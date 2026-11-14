# Build attestation with a signed statement and a TPM 2.0 quote

A Wiz build produces a small, canonical **build manifest**, wraps it in an **in-toto
Statement v1**, signs that statement as a **DSSE envelope** with an offline Ed25519 key,
and binds the statement digest to a **TPM 2.0 quote**:

```
statement_digest = SHA-256(canonical DSSE payload)
quote_extraData  = SHA-256("wiz-quote-v1" || nonce || statement_digest)
```

The manifest is **challenge-free**, so the same inputs produce the same manifest and two
builders can compare digests.  Freshness lives in the quote's `extraData`, not in the
hashed manifest.  The TPM quote proves *this TPM, in this boot state, signed this
statement digest together with this verifier nonce*; the DSSE signature proves *the
holder of the offline key signed the statement*.  Neither proves that the builder was
honest or that the artifact is reproducible; see [trust model](#trust-model).

The tools are standalone Python 3 (standard library only) plus OpenSSH's `ssh-keygen`
for the signature.  They make no network call unless you explicitly pass `--sigstore*`.

* `scripts/attest/wiz-attest keygen` generates an offline Ed25519 key and prints its
  `SHA256:` fingerprint;
* `scripts/attest/wiz-attest sign` signs an existing manifest (and `ak-info` prints the
  AK's TPM Name and DER SPKI digest for a policy);
* `scripts/attest/wiz-attest SOURCE|--artifact ...` builds and signs, then asks the TPM
  for a quote;
* `scripts/attest/wiz-verify` verifies the DSSE payloadType, the signature over the PAE,
  the key-fingerprint allowlist, the statement/artifact/manifest binding, the nonce in
  `extraData`, a PCR policy and (via `tpm2_checkquote`) the quote signature.  With
  `--snp-report`/`--snp-policy` it also verifies AMD SEV-SNP evidence: the report fields,
  `REPORT_DATA = H("wiz-snp-v1" || nonce || statement_digest)`, the measurement, policy
  bits, TCB floor, the VCEK/VLEK -> ASK -> ARK chain against pinned AMD KDS roots, and the
  report signature (via `openssl`).

The TPM quote is E1: it proves *this TPM, in this boot state, signed this statement digest
with this nonce*.  The SEV-SNP report is E2: it proves *a guest with this launch measurement
and policy ran on an AMD platform, and its `REPORT_DATA` bound this statement digest and
nonce*.  The two are independent evidence; the verifier checks either or both.  Neither
proves that the build was honest, reproducible or run in a particular cloud location.

## Requirements

* `ssh-keygen` (OpenSSH >= 8.8) for key generation, `-Y sign` and `-Y verify`.  No
  Python cryptography package is needed.
* `tpm2-tools` (`tpm2_createprimary`, `tpm2_create`, `tpm2_load`, `tpm2_quote`,
  `tpm2_checkquote`, `tpm2_flushcontext`) on `PATH`, or a directory passed with
  `--tpm2-bin`.
* A TPM 2.0 with SHA-256 PCRs (`/dev/tpmrm0`).  On many systems the device node is
  root-only; pass `--sudo` to the producer (it runs the TPM commands through `sudo -n`).
  The producer uses only transient objects: it creates no persistent handle, writes no
  NV index and discards the AK private blob after the quote.
* For `wiz-attest SOURCE`, a built `wiz` (`--wiz`) and its C toolchain flags, exactly as
  for `wiz build`.  `--artifact` works without `wiz` when `--wiz-version` is given.
* Optional: `cosign` for the opt-in `--sigstore`/`--sigstore-upload` path.  Nothing uses
  `cosign`, the network or Rekor unless you ask for it.
* For SEV-SNP evidence, `openssl` (X.509 chain validation and ECDSA-P384/SHA-384 report
  signature).  It is on `PATH` on normal systems; pass `--openssl` or set
  `WIZ_ATTEST_OPENSSL` otherwise.  No network is used: the AMD KDS root certificates are
  embedded under `scripts/attest/amd-roots/`.

The verifier itself needs no TPM.  Without `tpm2_checkquote` (or with `--skip-crypto`)
it reports a **partial** result: the statement, signature, artifact, `extraData` and
PCR-policy checks run, but the quote signature and PCR digest were not checked.

## Signing keys (offline Ed25519)

Generate a key once, on the release machine, and keep the private half offline:

```sh
scripts/attest/wiz-attest keygen --key ~/.config/wiz/attest-signing-key
# fingerprint: SHA256:...
```

`keygen` uses `ssh-keygen -t ed25519 -N ""`, creates the private key with mode `0600`,
prints only the public fingerprint, and never copies the private key.  Use a passphrase
or a hardware-backed SSH key when appropriate; the automated `sign` path expects a key
`ssh-keygen` can use without an interactive prompt.

An envelope is canonical JSON (sorted keys, no whitespace, no trailing newline):

```json
{
  "payload": "<base64 canonical in-toto Statement>",
  "payloadType": "application/vnd.in-toto+json",
  "signatures": [{"keyid": "SHA256:...", "sig": "<base64 SSHSIG over PAE>"}]
}
```

The signature is over the DSSE PAE (`DSSEv1 <len(type)> <type> <len(payload)> <payload>`),
not over the payload alone.  `keyid` is the signing key's `SHA256:` fingerprint; the
verifier treats it as an unauthenticated hint and requires it to equal the fingerprint of
the key that actually verifies.  A detached `manifest.intoto.json.sig` (raw SSHSIG over
the PAE) is written next to the envelope.  With the same key and inputs the envelope is
byte-for-byte deterministic.

The statement is the signed root:

```json
{"_type": "https://in-toto.io/Statement/v1",
 "subject": [{"name": "prog", "digest": {"sha256": "..."}}],
 "predicateType": "https://wiz-lang.dev/attestation/build-manifest/v1",
 "predicate": {
   "schema": "wiz-build-manifest/v1",
   "buildType": "https://wiz-lang.dev/buildtypes/wiz-build/v1",
   "externalParameters": {"entry": "examples/io.wiz", "target": "x86_64-linux-gnu"},
   "resolvedDependencies": [{"uri": "wiz:source", "digest": {"sha256": "..."}}],
   "byproducts": [],
   "manifest": { ... the whole canonical manifest ... },
   "manifest_sha256": "..."
 }}
```

Two optional fields chain and expire a statement: `prev` (the previous statement digest,
64 hex; verify with `--expect-prev`) and `valid_until` (RFC 3339 UTC; an expired statement
fails).  They are *inside* the signed statement, so they cannot be changed without
breaking the signature.  The manifest itself still has no timestamp.  Use
`--valid-until` for releases; a statement without one verifies forever unless a policy or
log limits it.

### Offline key versus keyless

The **offline key** path (default) has a stable, publishable fingerprint and works with no
network.  Its trust is key custody: publish the public key/fingerprint over an
independent channel and pin it with `--key-fingerprint` or a file in `--public-key`.
Rotation is a new key plus a new pinned fingerprint; revocation is removing/refusing the
old fingerprint.  SSH keys have no CRL, so a signed `revoked_keys` list or a policy
update must carry the revocation (this version does not fetch one).

**Keyless** Sigstore/Fulcio/Rekor is an optional second signature, not a replacement:
`--sigstore` tells `cosign sign-blob` to write a local bundle (no upload), and
`--sigstore-upload` opts into a Rekor upload (network).  Use it as an independent CI
identity signer for release artifacts; do not put a long-lived release key in a workflow
that runs repository code.  The offline DSSE signature and the cosign bundle are checked
separately.

### What signing proves and does not

A valid signature proves the statement bytes (and therefore the manifest root, subjects
and predicate) were signed by the key whose fingerprint is allowlisted.  Combined with
the quote, it proves the statement digest and nonce were in this TPM's `extraData` in
this boot state.  It does **not** prove:

* that the build ran, that the source was honest, or that the artifact came from it
  (reproducibility and independent rebuilds are the missing check);
* that the key holder is authorised beyond your fingerprint/identity policy;
* that the AK is a genuine TPM (no EK certificate or `ActivateCredential` yet);
* anything about a confidential VM or a TEE.  There is no SEV-SNP/TDX/CCA evidence here,
  and none is claimed.

## Build, sign and quote

From a checkout, build `examples/io.wiz`, sign the statement, and bind it to PCRs 0, 1,
4, 7, 11, 12 and 14.  The nonce must come from the verifier (or KBS); it is not stored in
the manifest:

```sh
NONCE=$(python3 -c 'import secrets; print(secrets.token_hex(32))')
scripts/attest/wiz-attest examples/io.wiz \
  --out build-attest \
  --wiz .lake/build/bin/wiz \
  --wiz-flag=-I --wiz-flag=lib \
  --tree-root lib --tree-root runtime \
  --pcr-list sha256:0,1,4,7,11,12,14 \
  --sign-key ~/.config/wiz/attest-signing-key \
  --valid-until 2027-02-01T00:00:00Z \
  --nonce "$NONCE"
```

The output directory then contains:

```
manifest.json                  canonical, challenge-free build manifest
manifest.intoto.json           DSSE envelope with the signed in-toto Statement
manifest.intoto.json.sig       detached SSHSIG over the DSSE PAE
quote.msg                      TPMS_ATTEST quote message (signed by the AK)
quote.sig                      quote signature
quote.pcr                      PCR values, `-F values` format (32 bytes per PCR)
quote.nonce                    the nonce; check it against your own if you did not pass one
ak.pub                         AK public key (TPM2B_PUBLIC), not a PEM file
```

The quote's `extraData` is `H("wiz-quote-v1" || nonce || statement_digest)`.  If
`--nonce` is omitted the producer generates a random one and records it in
`quote.nonce`; that is only local freshness, not proof that the quote is fresh to *you*.

`--tree-root` names the compiler inputs whose digest goes into the manifest.  When it is
omitted, the producer uses `lib` and `runtime` if they exist in the current directory.
Use `--wiz-flag=--cc --wiz-flag=/path/to/clang` (and the other toolchain flags) for a
checkout build that needs them.  `--output-name` names the executable.  A quote requires
`--sign-key`: an unsigned quote would not bind a statement, so the producer fails with a
usage error instead of emitting one.

To produce only the manifest and statement (no TPM, useful for CI and reproducibility):

```sh
scripts/attest/wiz-attest --artifact build/prog --artifact build/prog.c \
  --out build --no-quote \
  --wiz-version 0.1.0-dev --target x86_64-linux-gnu \
  --source-entry examples/io.wiz \
  --sign-key ~/.config/wiz/attest-signing-key \
  --valid-until 2027-02-01T00:00:00Z
```

To sign an existing manifest separately (or re-sign before quoting again):

```sh
scripts/attest/wiz-attest sign \
  --manifest build-attest/manifest.json \
  --key ~/.config/wiz/attest-signing-key \
  --prev "$PREVIOUS_STATEMENT_SHA256" \
  --valid-until 2027-02-01T00:00:00Z
```

`sign` does not read or change `quote.msg`; if you add `--prev`/`--valid-until` after a
quote exists, that quote binds the *old* statement digest and must be regenerated with
the producer.  Artifact paths are recorded relative to `--out`.  If an artifact lives
elsewhere, it is recorded by basename and `wiz-verify --artifacts-dir DIR` says where to
find it.

## Verify

Write the expected PCR policy once per builder image.  A policy is a JSON object mapping
PCR indices to the SHA-256 values you expect.  Pin the AK by its **DER SPKI digest** and
**TPM Name**, not by hashing the `ak.pub` file:

```sh
scripts/attest/wiz-attest ak-info --ak build-attest/ak.pub --json
# {"name": "000b...", "spki_sha256": "...", "file_sha256": "...", ...}
```

```json
{
  "schema": "wiz-pcr-policy/v1",
  "bank": "sha256",
  "pcr": {
    "7": "4cc91dca1c10a94cd078eabae6af184b095ee55f9a95d4329c66366bf954dab5",
    "11": "d45f8048465e62ee101b708c802e2664b1810eb629958ca57f8671a65a733f93"
  },
  "ak_spki_sha256": "… SHA-256 of DER SubjectPublicKeyInfo …",
  "ak_name": "000b… TPM Name (nameAlg || H(publicArea)) …",
  "valid_until": "2027-02-01T00:00:00Z"
}
```

`ak_name` is compared with the quote's `qualifiedSigner`, so it binds the policy to the
key the TPM actually used.  `ak_spki_sha256` is the stable encoding OpenSSL/cosign tooling
uses.  `ak_sha256` (SHA-256 of the `ak.pub` TPM2B_PUBLIC file bytes) is still accepted for
older policies but is **deprecated**: it is not a canonical key encoding and the old docs
mistakenly showed a PEM hash.  `wiz-attest ak-info` prints all three.  PCR 7 is the
Secure Boot policy and PCR 11 the measured UKI in the example; use the values of *your*
builder, read with `tpm2_pcrread sha256:7,11`, and rotate the policy when the image
changes.  An expired policy fails.

Then, with the verifier's own nonce and an explicit trust root:

```sh
scripts/attest/wiz-verify \
  --manifest build-attest/manifest.json \
  --policy policy.json \
  --nonce "$NONCE" \
  --public-key release-signing-key.pub \
  --key-fingerprint SHA256:... \
  --ak-spki-sha256 "$AK_SPKI" \
  --ak-name "$AK_NAME" \
  --artifacts-dir build-attest \
  --json
```

`--nonce` checks the `extraData` formula and freshness; `--require-nonce` makes a missing
verifier nonce an error.  `--public-key` (repeatable) or `--allowed-signers` supplies the
trusted key(s), and `--key-fingerprint` (repeatable) is the allowlist the verifying key
must match.  `--require-signature` makes an unsigned manifest an error.  An unsigned
bundle is accepted only with the explicit `--allow-unsigned`, which records a warning;
the default is to **fail closed**.  `--expect-digest` pins the manifest,
`--expect-statement-digest` pins the statement, and `--expect-prev` pins a `prev` chain.
`--detached-signature` verifies the sidecar `.sig` in addition to the envelope.  If
`ak.pub` is not next to the manifest, pass `--ak`; the same applies to `--quote`,
`--signature` and `--pcr`.

A **verified** result needs all of: a canonical manifest, matching artifact bytes, a DSSE
payloadType of `application/vnd.in-toto+json`, a valid SSHSIG over the PAE under an
allowlisted key, a statement that still matches the manifest/artifacts, quote `extraData`
equal to `H("wiz-quote-v1" || nonce || statement_digest)`, the quote's PCR selection equal
to the manifest's, PCR values matching the policy, a pinned AK, and a successful
`tpm2_checkquote`.  Anything less is **partial** (exit 3), and any mismatch is
**failed** (exit 1).

## AMD SEV-SNP evidence (E2)

SEV-SNP adds platform evidence that survives a compromised guest kernel: the AMD Secure
Processor signs a 1184-byte `ATTESTATION_REPORT` containing the guest policy, launch
measurement, `REPORT_DATA`, TCB and chip ID.  The verifier treats the report and its
certificate chain as **evidence** and recomputes the result.  It never reads a guest's
`"verified": true` field: a guest `attestation.json` is not an input.

The report binds the signed statement exactly as the TPM quote does:

```
REPORT_DATA = SHA-256("wiz-snp-v1" || nonce || statement_digest) || 0^32
```

`statement_digest` is SHA-256 of the canonical DSSE payload (or of the deterministic
statement when the bundle is explicitly unsigned).  The 64-byte field carries the 32-byte
digest followed by 32 zero bytes; a bare manifest hash or a different nonce fails.

### Evidence files

Take these from inside the guest, before it is trusted:

* `snp/report.bin` -- the raw report from `snpguest report`; it may have the ABI
  certificate table appended;
* `snp/certs/` -- `vcek.pem`, `ask.pem`, `ark.pem` (or a PEM bundle, or an ABI table
  passed as `--snp-certs`);
* `snp/policy.json` -- the expected launch measurement, TCB floor and policy bits.

A policy is `wiz-snp-policy/v1`:

```json
{
  "schema": "wiz-snp-policy/v1",
  "measurement": "abab… 48 bytes of launch digest hex …",
  "product": "Milan",
  "signing_key": "VCEK",
  "vmpl": 0,
  "tcb": {
    "boot_loader": 3,
    "tee": 0,
    "snp": 8,
    "microcode": 115,
    "spl": 0
  },
  "policy": {"migration_agent": false, "smt": true},
  "valid_until": "2027-02-01T00:00:00Z"
}
```

The fields are optional except `schema`; a missing `measurement` or `tcb` makes the result
**partial**, not verified.  `debug` is rejected outright: a debuggable guest is never
accepted.  `product` is one of `Milan`, `Genoa` or `Turin`.  `signing_key` is `VCEK`,
`VLEK` or `either`; choose `VLEK` explicitly to accept a CSP-managed VLEK (it moves trust
from the chip to the CSP's seed plus TCB).  `tcb` values are per-component floors; the
component bytes are boot loader, TEE, SNP, microcode and SPL.  `policy` pins the guest
policy bits (`smt`, `migration_agent`, `single_socket`, `cxl`, `mem_aes_256_xts`,
`rapl_dis`, `ciphertext_hiding_dram`, `page_swap_disable`).  `chip_id` (64 bytes hex) and
`author_key_digest` (48 bytes hex) are optional pins; leave `chip_id` unset unless your
privacy model allows recording it.

### Running against a real SEV-SNP guest

The verifier needs no SNP device.  In the guest (root, with `snpguest` installed):

```sh
# Bind the report to the verifier's nonce and the signed statement digest.
python3 - "$NONCE" "$STATEMENT_DIGEST" > snp/request.bin <<'PY'
import hashlib, sys
nonce = bytes.fromhex(sys.argv[1])
digest = bytes.fromhex(sys.argv[2])
sys.stdout.buffer.write(hashlib.sha256(b"wiz-snp-v1" + nonce + digest).digest()
                        + bytes(32))
PY

snpguest report snp/report.bin snp/request.bin   # /dev/sev-guest
snpguest certificates pem snp/certs               # VCEK/VLEK + ASK + ARK
sha256sum snp/report.bin snp/certs/*
```

Copy `snp/` and the build bundle off the guest, then run the verifier on a trusted
machine:

```sh
scripts/attest/wiz-verify \
  --manifest build-attest/manifest.json \
  --policy policy.json \
  --nonce "$NONCE" \
  --public-key release-signing-key.pub \
  --key-fingerprint SHA256:... \
  --artifacts-dir build-attest \
  --snp-report snp/report.bin \
  --snp-certs snp/certs \
  --snp-policy snp/policy.json \
  --require-snp \
  --json
```

Use `--snp-measurement` to pin the 48-byte launch digest and `--snp-product` to require a
product family without writing a policy file.  `--require-snp` makes missing E2 evidence
an error.  On a machine with no `/dev/sev-guest` (or for an E1-only release), pass
`--allow-machine-only` **explicitly**: the result is then `partial` (exit 3), never
`verified`, and invalid evidence is still a failure.  Without `--snp-*`, `--require-snp`
or `--allow-machine-only`, the verifier stays E1-only and does not add an SNP check.

What a verified E2 result establishes:

* the report's version, signature algorithm, policy reserved bit and signer info are
  well-formed;
* `REPORT_DATA` equals `H("wiz-snp-v1" || nonce || statement_digest) || 0^32`;
* `MEASUREMENT` equals the pinned launch digest;
* `REPORTED_TCB` and `COMMITTED_TCB` meet every pinned component floor;
* debug is off and the pinned policy bits, VMPL and signing-key type match;
* the leaf (VCEK or VLEK) chains to an embedded AMD KDS ARK through its ASK/VLEK CA, the
  evidence ARK (if present) matches a pinned root, every certificate is valid at the
  verifier's clock (`--now` overrides it for tests), and the ECDSA-P384/SHA-384 signature
  over the first 0x2A0 bytes verifies under the leaf.

What it does **not** establish: that the image is honest or contains the pinned `wiz`, that
the build ran (the measurement covers the initial launch image, not files installed
afterwards), the cloud location, freshness after the nonce is consumed, or key release.
The report has no trustworthy timestamp; `valid_until` is checked against the verifier's
clock, and freshness is the nonce.

`REPORT_DATA` is **caller-supplied**: a compromised guest can ask the AMD secure processor
for a report with any 64-byte value, including the expected statement digest.  The report
therefore proves the launch image, policy and TCB, and that this platform signed this
value; it does not prove that the process inside the guest computed the statement
honestly.  Closing that gap needs the report (or a key-release receipt bound to it) to be
verified *before* a secret/key is released, a measured small signer, and ideally an
in-guest signature over the same data.  A nonce only prevents replay of an old report; it
does not make the requesting process trustworthy.

`$STATEMENT_DIGEST` is the SHA-256 of the canonical DSSE payload (the
`statement_sha256` in `wiz-verify --json`), and `$NONCE` is the verifier's nonce.  Both
must be chosen before the guest requests the report.  The existing E1 TPM checks still run
in `wiz-verify`; a combined bundle (vTPM quote plus SNP report, as on Azure DCasv5/ECasv5)
is the intended release shape.  A bare SNP report without the E1 bundle can be checked
with `snp.verify_report` from `scripts/attest/snp.py`; `wiz-verify` still expects the E1
quote and PCR policy files.

### Pinned AMD roots

`scripts/attest/amd-roots/` holds the AMD KDS ARKs and their ASK/VLEK-CA intermediates for
Milan, Genoa and Turin, with SHA-256 fingerprints in `amd-roots/README.md` and in
`AMD_ARK_SHA256` (`scripts/attest/snp.py`).  `snp.py` refuses to load a root whose digest
does not match the pinned value, and the verifier never trusts an ARK supplied in the
evidence.  `--ark FILE` overrides the roots for a private deployment or a test; it is not
needed for AMD hardware.  Nothing is fetched from the network.

### Exit codes and output

| exit | meaning |
|---|---|
| 0 | verified: every check ran and passed |
| 1 | verification failed (schema, signature, digest, binding, PCR, report or chain mismatch) |
| 2 | usage error |
| 3 | incomplete: a required tool is missing, `--skip-crypto` was used, the signature/nonce/AK pin was not supplied, or `--allow-machine-only` produced an E1-only result |

`--json` prints one object with `schema`, `status` (`verified`, `partial`, `failed`),
`ok`, `exit_code`, `manifest_sha256`, `statement_sha256`, `signed`, `signature_keyid`, a
`checks` array (`pass`, `fail` or `skip` with a detail), `errors`, `warnings`, the parsed
quote fields, and a `snp` object (report fields, certificate chain and the pinned product)
when E2 evidence was checked.  Human-readable output is one line per check.  The
producer's `--json` prints the manifest, statement, envelope, keyid and (with a quote) the
AK Name and SPKI digest.

### CI job

The `attestation verifier` job in `.github/workflows/ci.yml` runs
`python3 -m unittest discover -s scripts/attest/tests -v` on every pull request.  It needs
no TPM, no SNP device, no Wiz build and no network; the signing tests generate a throwaway
Ed25519 key with `ssh-keygen` in a temporary directory, and the SEV-SNP tests generate a
throwaway P-384 root/ASK/leaf chain with `openssl` and sign a synthetic report.  No private
key is committed and no AMD key is used.  The real-TPM and two-build reproducibility tests
stay opt-in (`WIZ_ATTEST_TPM=1`, `WIZ_ATTEST_REPRO=1`) and are not part of the default job.
A pull request that changes only `scripts/attest/*` is self-tested by this job:
`scripts/ci.py` treats it like a docs change, so the Lean build and test shards are
skipped.

## Manifest format

The manifest is `wiz-build-manifest/v1`:

```json
{
  "artifacts": [
    {"path": "prog", "sha256": "c950a5f8…", "size": 45288},
    {"path": "prog.c", "sha256": "d8598d2b…", "size": 186729}
  ],
  "builder": {"kind": "tpm2-quote"},
  "pcr": {"bank": "sha256", "indices": [0, 1, 4, 7, 11, 12, 14]},
  "schema": "wiz-build-manifest/v1",
  "source": {
    "entry": "examples/io.wiz",
    "sha256": "78b4e978…",
    "tree_roots": ["lib", "runtime"],
    "tree_sha256": "233c6aa7…"
  },
  "target": "x86_64-linux-gnu",
  "wiz": {
    "binary_sha256": "7d89c302…",
    "commit": "e3bd36ff…",
    "version": "0.1.0-dev"
  }
}
```

* `artifacts` are sorted by path; paths are relative, use `/`, and must not contain `.`
  or `..` components.  Sizes and SHA-256 digests are checked against the files.
* `source.tree_sha256` is SHA-256 over the sorted lines
  `"<sha256>  <root>/<relative-path>\n"` for every regular file under `tree_roots`.
  This is a simple deterministic Merkle substitute, not a standard transparency format.
  With `--artifact`, pass `--source-entry` and, if that file is not in the current
  directory, `--source-sha256`; the producer does not invent a source digest.
* `wiz` records the toolchain version, and the commit and binary hash when known.
* `target` is the target triple of the produced binary.
* `pcr` names the bank and exactly the PCR indices the quote selects.
* `builder.kind` is `tpm2-quote`.  SEV-SNP evidence is a separate report bound to the
  statement digest, not a manifest field; the manifest stays a stable, challenge-free
  description of the inputs and outputs whether or not E2 evidence accompanies it.
* There is no `challenge`, nonce, timestamp, hostname or absolute path.  Freshness is
  `quote.extraData = H("wiz-quote-v1" || nonce || statement_digest)`; expiry and the
  previous root, when used, are optional fields of the signed statement predicate, not
  the manifest.

The file is **canonical JSON**: keys sorted recursively, no insignificant whitespace, no
trailing newline, UTF-8.  The signed object is the canonical in-toto Statement whose
`predicate.manifest` is exactly these bytes; the quote binds the SHA-256 of the canonical
statement payload.  The verifier rejects a manifest that is not in canonical form,
duplicate keys, unknown fields and non-finite numbers.  There are no timestamps,
hostnames, cache paths or absolute build directories in the manifest, so the same inputs
produce the same manifest; `wiz-attest` writes that form directly.

## Trust model

A successful verification says:

* the artifact bytes match the signed statement's `subject` and the manifest;
* the statement (and its embedded manifest root) was signed by the key whose
  `SHA256:` fingerprint is in your allowlist, over the exact DSSE PAE;
* the statement digest and your nonce are what the TPM put in `extraData`, via
  `H("wiz-quote-v1" || nonce || statement_digest)`;
* the quote signature verifies under the `ak.pub` you supplied, its `qualifiedSigner`
  Name matches the pinned `ak_name`, and its PCR digest covers the supplied values (via
  `tpm2_checkquote`);
* the quoted PCRs match your policy, the policy has not expired, and the manifest names
  the source tree, toolchain and target that the builder claims.

When E2 evidence verifies, it additionally says:

* the AMD Secure Processor signed this report for a guest with the pinned launch
  `MEASUREMENT`, guest policy, VMPL and TCB floors;
* the report bound the same statement digest and verifier nonce as the TPM quote (or the
  only binding, if no quote is present);
* the VCEK/VLEK chain reaches an embedded AMD KDS ARK and the report signature verifies
  under that leaf, so the report was produced by an AMD platform rather than by software
  in the guest.

It does **not** say:

* that the builder ran an honest build, or that the artifacts came from that source.
  That is the job of reproducibility and independent rebuilders; a statement is a claim
  until someone rebuilds and compares.
* that the AK or signing key is genuine.  A pinned AK still does not prove that the key
  lives in a TPM, because there is no EK certificate or `ActivateCredential` yet.  If the
  AK is unpinned, an attacker can substitute AK + quote + manifest (`ak_spki_sha256` /
  `ak_name` close that hole); if the signing key is not pinned, a substitute statement
  also passes.  Always pass `--public-key`/`--allowed-signers` and `--key-fingerprint`.
* that the signing key was kept offline, or that the signer is authorised beyond the
  fingerprint policy.  Custody is an operational control, not a property of the signature.
* that the source or its dependencies are trustworthy, or that a cache was not poisoned.
  The producer hashes the source tree and artifacts, not cache provenance.
* anything about a confidential VM unless you passed `--snp-report`/`--snp-policy`.
  E1 alone has no SEV-SNP, TDX or CCA evidence and claims none.  With E2, the report
  proves the launch measurement, policy and TCB on an AMD platform, but not that the
  image is honest, that the build ran, or that the guest is in the location the operator
  claims.
* that the boot image is patched or current: a PCR policy pins an image, including its
  bugs.  PCR 7 and PCR 11 change on firmware, Secure Boot dbx and UKI updates, so a
  policy is versioned with the image and must be re-enrolled after an update.

The TPM on a laptop or desktop is often firmware (for example Microsoft Pluton, as in
the measured experiment), not a discrete tamper-resistant chip.  The device protects
the quote against software on the running machine, subject to the vendor's fTPM
implementation.

### Key rotation and revocation

* **Rotation:** generate a new offline key, publish its fingerprint over an independent
  channel, add `--key-fingerprint NEW` (and keep the old fingerprint only while old
  releases are still being verified), and re-sign new statements.  The quote is
  independent: keep the old AK policy for old bundles, or re-quote with the new image.
  A `prev` chain makes the transition explicit.
* **Revocation:** SSH keys have no CRL.  Remove the fingerprint from the allowlist and,
  for already-published bundles, maintain a signed `revoked_keys` list or a policy
  update; an old bundle still verifies cryptographically until the verifier refuses that
  fingerprint.  The same applies to `ak_name`/`ak_spki_sha256`: publish the replacement
  and reject the old Name.  This version does not fetch a revocation list automatically.
* **Policy expiry:** `valid_until` in the statement (and optionally in the policy) makes
  an old bundle fail after a date.  It is signed, so it cannot be extended without the
  key.

## Limitations and open gaps

* **Signed statement, not a build proof.** The DSSE signature proves key possession over
  the statement; it does not prove the build ran.  Reproducibility and independent
  rebuilds remain the missing check.
* **AK provisioning (deferred).** The AK is created fresh for every quote and discarded;
  there is no persistent AK, no EK certificate check and no `TPM2_ActivateCredential`.
  Pinning is trust-on-first-use unless `ak_name`/`ak_spki_sha256` are published out of
  band.  A release path needs a provisioned AK with a published certificate, EK
  endorsement and rotation.  This is deliberately deferred, not solved here.
* **PCR policy (deferred).** The policy is a static list of values.  There is no
  `TPM2_PolicyAuthorize`/signed-policy update path, no PCR event-log replay and no TCB
  version floor beyond the optional `valid_until`.  A firmware or UKI update invalidates
  it until re-enrolment.
* **Freshness store.** The verifier checks the nonce formula but keeps no used-nonce set
  and enforces no TTL; the relying party/KBS must issue an unpredictable, single-use
  nonce with a short lifetime and remember it.  `quote.nonce` is a convenience for local
  checks, not evidence that the verifier chose the nonce.
* **Transparency.** There is a DSSE envelope and an opt-in cosign/Rekor bundle, but no
  append-only build log, no inclusion proof and no anti-equivocation by default.  A
  local quote plus a signed statement can be shown only to the parties who receive them;
  two verifiers can still be shown different bundles.  Logging one claim per build to
  Rekor/Sigsum and verifying inclusion offline is future work.
* **Cache generation root (deferred).** The manifest records the source tree and
  artifacts, not which elaboration or grail cache supplied declarations, and there is no
  signed cache-generation root.  A shared writable cache can still change what is
  elaborated.  The TPM measures the booted OS image (PCR 7/11), not the `wiz` process or
  its shell.
* **Reproducibility.** The manifest makes a reproducible claim checkable, but this
  tooling does not rebuild the artifact.  Same-machine, same-toolchain builds are
  bit-identical for the measured example, including a warm cache; the release tarball is
  not yet deterministic, and a second independent builder is the missing check.
* **Toolchain allowlists.** The verifier checks that the manifest has a well-formed
  `wiz` section; it does not compare it to an allowlist of compiler hashes.  Add that
  check when release manifests are published.
* **SNP launch digest scope.** `MEASUREMENT` covers the initial launched image (VMSA and
  launched pages), not the running filesystem.  On many clouds it does not cover the
  kernel, initrd or cmdline; a stock image that installs `wiz` after launch attests the
  boot firmware, not the compiler.  Measure a purpose-built image, or add a vTPM quote
  with measured boot/IMA inside the guest.
* **SNP time and freshness.** A report has no trustworthy timestamp.  The verifier checks
  certificate and policy validity against its own clock, and the nonce is the only
  freshness mechanism; there is no used-nonce set or TTL here, and no key-release receipt
  bound to the report.  A relying party or KBS must issue a single-use nonce and refuse a
  replay.
* **SNP TCB and roots are manual.** The TCB floors and `valid_until` in `snp-policy.json`
  are maintained by hand; there is no KDS refresh, no revocation feed and no automatic
  VCEK fetch.  The verifier does not check the VCEK certificate's embedded TCB extension
  against the report beyond the chain and the report TCB floor.  Updating a root means
  replacing a file and its pinned fingerprint.
* **SNP does not close E1 gaps.** The report does not prove the builder was honest, that
  the artifact came from the measured image, reproducible builds, cache provenance or the
  signing-key custody.  Combining `MEASUREMENT` with a published launch digest is
  necessary but not sufficient for a release claim.
* **Scope.** E1 is a TPM 2.0 quote plus an offline-signed statement for one physical
  builder.  E2 adds an AMD SEV-SNP launch report verified outside the guest.  Neither
  covers TDX, ARM CCA, AWS Nitro Enclaves or key release, and no cloud/guest run is
  claimed by the local test suite (its fixtures are synthetic).

## Further reading

The design rationale and the measured experiment are in the project's research notes:
reproducible generated C and a TPM quote on the lab machine, the prior-art review of
attestation/supply-chain mechanisms, and the wider argument for attested builds.  The
concrete commands and trust gaps above are the parts a user needs; the notes are for
maintainers.
