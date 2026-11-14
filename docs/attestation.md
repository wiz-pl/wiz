# Build attestation with a TPM 2.0 quote

A Wiz build can produce a small **build manifest** and a **TPM 2.0 quote** that binds
the manifest to the state of the machine that built the artifact.  A verifier checks the
manifest, every artifact byte, an expected PCR policy and, with `tpm2-tools` installed,
the quote signature.  This is a machine attestation, not a claim about a confidential VM:
it uses the TPM that is already in the builder, and it makes no SEV-SNP or TDX claim.

The tools are standalone Python 3 (standard library only):

* `scripts/attest/wiz-attest` builds a program (or takes `--artifact`), writes the
  manifest, and asks the TPM for a quote;
* `scripts/attest/wiz-verify` verifies a manifest, its artifacts, a PCR policy and the
  quote.  It invokes `tpm2_checkquote` for TPM cryptography; it does not reimplement it.

The manifest is the build statement.  The quote's `extraData` is
`sha256(canonical_manifest)`, so a valid quote is evidence that *this TPM, in this boot
state, signed this manifest digest*.  It is not by itself evidence that the builder was
honest or that the artifact is reproducible; see [trust model](#trust-model).

## Requirements

* `tpm2-tools` (`tpm2_createprimary`, `tpm2_create`, `tpm2_load`, `tpm2_quote`,
  `tpm2_checkquote`, `tpm2_flushcontext`) on `PATH`, or a directory passed with
  `--tpm2-bin`.
* A TPM 2.0 with SHA-256 PCRs (`/dev/tpmrm0`).  On many systems the device node is
  root-only; pass `--sudo` to the producer (it runs the TPM commands through `sudo -n`).
  The producer uses only transient objects: it creates no persistent handle, writes no
  NV index and discards the AK private blob after the quote.
* For `wiz-attest SOURCE`, a built `wiz` (`--wiz`) and its C toolchain flags, exactly as
  for `wiz build`.  `--artifact` works without `wiz` when `--wiz-version` is given.

The verifier itself needs no TPM.  Without `tpm2_checkquote` (or with `--skip-crypto`)
it reports a **partial** result: the manifest, artifact, `extraData` and PCR-policy
checks run, but the signature and PCR digest were not checked.

## Build and quote

From a checkout, build `examples/io.wiz` and bind the manifest to PCRs 0, 1, 4, 7, 11,
12 and 14:

```sh
CHALLENGE=$(python3 -c 'import secrets; print(secrets.token_hex(32))')
scripts/attest/wiz-attest examples/io.wiz \
  --out build-attest \
  --wiz .lake/build/bin/wiz \
  --wiz-flag=-I --wiz-flag=lib \
  --tree-root lib --tree-root runtime \
  --pcr-list sha256:0,1,4,7,11,12,14 \
  --challenge "$CHALLENGE"
```

The output directory then contains:

```
manifest.json   canonical build manifest (its sha256 is the quote's extraData)
quote.msg       TPMS_ATTEST quote message (signed by the AK)
quote.sig       quote signature
quote.pcr       PCR values, `-F values` format (32 bytes per selected PCR)
ak.pub          AK public key (TPM2B_PUBLIC) used for the quote
```

`--tree-root` names the compiler inputs whose digest goes into the manifest.  When it is
omitted, the producer uses `lib` and `runtime` if they exist in the current directory.
Use `--wiz-flag=--cc --wiz-flag=/path/to/clang` (and the other toolchain flags) for a
checkout build that needs them.  `--output-name` names the executable.

To produce only the manifest (no TPM, useful for CI and for checking reproducibility):

```sh
scripts/attest/wiz-attest --artifact build/prog --artifact build/prog.c \
  --out build --no-quote \
  --wiz-version 0.1.0-dev --target x86_64-linux-gnu \
  --source-entry examples/io.wiz
```

Artifact paths are recorded relative to `--out`.  If an artifact lives elsewhere, it is
recorded by basename and `wiz-verify --artifacts-dir DIR` says where to find it.

## Verify

Write the expected PCR policy once per builder image.  A policy is a JSON object mapping
PCR indices to the SHA-256 values you expect; `ak_sha256` is optional and pins the AK
public key file:

```json
{
  "schema": "wiz-pcr-policy/v1",
  "bank": "sha256",
  "pcr": {
    "7": "4cc91dca1c10a94cd078eabae6af184b095ee55f9a95d4329c66366bf954dab5",
    "11": "d45f8048465e62ee101b708c802e2664b1810eb629958ca57f8671a65a733f93"
  },
  "ak_sha256": "b50081ec55eac4433bb75d1594d0fbe412e3189e5b5a542473398a83e61e3b90"
}
```

PCR 7 is the Secure Boot policy and PCR 11 the measured UKI in the example; use the
values of *your* builder, read with `tpm2_pcrread sha256:7,11`, and rotate the policy
when the image changes.  Then:

```sh
scripts/attest/wiz-verify \
  --manifest build-attest/manifest.json \
  --policy policy.json \
  --challenge "$CHALLENGE" \
  --artifacts-dir build-attest \
  --json
```

`--challenge` checks that the manifest carries the fresh challenge you issued;
`--require-challenge` makes a missing challenge an error.  `--expect-digest` pins the
whole manifest; `--ak-sha256` pins the AK when the policy does not.  If `ak.pub` is not
next to the manifest, pass `--ak`; the same applies to `--quote`, `--signature` and
`--pcr`.

A **verified** result needs all of: a canonical manifest, matching artifact bytes, quote
`extraData` equal to the manifest digest, the quote's PCR selection equal to the
manifest's, PCR values matching the policy, a pinned AK, a challenge, and a successful
`tpm2_checkquote`.  Anything less is **partial** (exit 3), and any mismatch is
**failed** (exit 1).

### Exit codes and output

| exit | meaning |
|---|---|
| 0 | verified: every check ran and passed |
| 1 | verification failed (schema, digest, binding or PCR mismatch) |
| 2 | usage error |
| 3 | incomplete: a required tool is missing, `--skip-crypto` was used, or the AK/challenge is not pinned |

`--json` prints one object with `schema`, `status` (`verified`, `partial`, `failed`),
`ok`, `exit_code`, `manifest_sha256`, a `checks` array (`pass`, `fail` or `skip` with a
detail), `errors`, `warnings` and the parsed quote fields.  Human-readable output is one
line per check.  The producer's `--json` prints the manifest path and digest.

## Manifest format

The manifest is `wiz-build-manifest/v1`:

```json
{
  "artifacts": [
    {"path": "prog", "sha256": "c950a5f8…", "size": 45288},
    {"path": "prog.c", "sha256": "d8598d2b…", "size": 186729}
  ],
  "builder": {"kind": "tpm2-quote"},
  "challenge": "bc055b35…",
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
* `challenge` is optional; when present it is the verifier's fresh challenge.

The file is **canonical JSON**: keys sorted recursively, no insignificant whitespace, no
trailing newline, UTF-8.  The digest bound by the quote is `sha256` of exactly those
bytes.  The verifier rejects a manifest that is not in canonical form, duplicate keys,
unknown fields and non-finite numbers.  There are no timestamps, hostnames, cache paths
or absolute build directories in the manifest, so the same inputs produce the same
manifest; `wiz-attest` writes that form directly.

## Trust model

A successful verification says:

* the artifact bytes match the manifest;
* the manifest digest is what the TPM put in `extraData`;
* the quote signature verifies under the `ak.pub` you supplied, and its PCR digest
  covers the supplied values (via `tpm2_checkquote`);
* the quoted PCRs match your policy, and (with `--challenge`) the manifest is fresh;
* the manifest names the source tree, toolchain and target that the builder claims.

It does **not** say:

* that the builder ran an honest build, or that the artifacts came from that source.
  That is the job of reproducibility and independent rebuilders; a manifest is a claim
  until someone rebuilds and compares.
* that the AK is genuine.  `ak.pub` is generated per run; without an out-of-band pin
  (`--ak-sha256` or `policy.ak_sha256`) an attacker can substitute a different AK,
  quote and manifest together.  Even pinned, this implementation does not validate an
  EK certificate or a TPM vendor endorsement chain.
* that the source or its dependencies are trustworthy, or that a cache was not poisoned.
  The producer hashes the source tree and artifacts, not cache provenance.
* anything about a confidential VM, memory encryption or a cloud TEE.  There is no
  SEV-SNP or TDX evidence here, and none is claimed.
* that the boot image is patched or current: a PCR policy pins an image, including its
  bugs.  PCR 7 and PCR 11 change on firmware, Secure Boot dbx and UKI updates, so a
  policy is versioned with the image and must be re-enrolled after an update.

The TPM on a laptop or desktop is often firmware (for example Microsoft Pluton, as in
the measured experiment), not a discrete tamper-resistant chip.  The device protects
the quote against software on the running machine, subject to the vendor's fTPM
implementation.

## Limitations and open gaps

* **AK provisioning.** The AK is created fresh for every quote and discarded; there is
  no persistent AK, no EK certificate check and no TPM endorsement.  Pinning is
  trust-on-first-use unless the digest is published out of band.  A real release should
  provision an AK once, publish its public key and certificate, and rotate it with the
  image.  The quote's `qualifiedSigner` name is parsed and reported but not matched to a
  pinned name; the AK file pin is the identity check.
* **PCR policy.** The policy is a static list of values.  There is no
  `TPM2_PolicyAuthorize`/signed-policy update path, no event-log replay and no TCB
  version floor.  A firmware or UKI update invalidates it until it is re-enrolled.
* **Transparency.** The quote is a local statement.  There is no transparency log, no
  in-toto/DSSE envelope, no signature over the manifest by a key sealed to the PCR
  policy, and no revocation or anti-equivocation service.  Two quotes for the same
  manifest cannot be distinguished from a replay without the challenge.
* **Reproducibility.** The manifest makes a reproducible claim checkable, but this
  tooling does not rebuild the artifact.  Same-machine, same-toolchain builds are
  bit-identical for the measured example, including a warm cache; the release tarball
  is not yet deterministic, and a second independent builder is the missing check.
* **Cache and environment.** The manifest records the source tree and artifacts, not
  which elaboration or grail cache supplied declarations.  The TPM measures the booted
  OS image (PCR 7/11), not the `wiz` process or its shell.
* **Toolchain allowlists.** The verifier checks that the manifest has a well-formed
  `wiz` section; it does not compare it to an allowlist of compiler hashes.  Add that
  check when release manifests are published.
* **Scope.** E1 is a TPM 2.0 quote for one physical builder.  It says nothing about
  cloud builders, SEV-SNP, TDX, ARM CCA or AWS Nitro.

## Further reading

The design rationale and the measured experiment are in the project's research notes:
reproducible generated C and a TPM quote on the lab machine, and the wider argument for
attested builds.  The concrete commands and trust gaps above are the parts a user needs;
the notes are for maintainers.
