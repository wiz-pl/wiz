# Pinned AMD SEV-SNP trust anchors

These are the AMD Key Distribution Service (KDS) roots and their signing
intermediates for the SEV-SNP product families the verifier understands.  The
**ARK** file is the trust anchor; the **ASK** (`ask.pem`) and **VLEK** CA
(`vlek-ca.pem`) files are intermediates used when the guest's certificate table
does not carry them.  The verifier never trusts a certificate supplied inside
the evidence as a root: it validates the supplied leaf against one of these
ARKs.  A report that supplies its own ARK must match one of these
fingerprints, or `wiz-verify` fails.

| product | file | SHA-256 (DER) |
|---|---|---|
| Milan | `Milan/ark.pem` | `69d063b45344d26a2e94e1f4210de49ef555308287d4c174445c95639a540bcd` |
| Genoa | `Genoa/ark.pem` | `4c6598d19c18719c5dfd4a7d335f674e5bfe1d8f800cea2cf270c10d103db2f1` |
| Turin | `Turin/ark.pem` | `1f084161a44bb6d93778a904877d4819cafa5d05ef4193b2ded9dd9c73dd3f6a` |

Intermediates:

| product | file | SHA-256 (DER) |
|---|---|---|
| Milan | `Milan/ask.pem` | `67d303bd3905fd38db8b20e0793699870e7fa612eaad5dec358293fd8c0bac1b` |
| Milan | `Milan/vlek-ca.pem` | `c5e081f59b7efab1fe2f8b505e159704e72f29cab7ef7cf628a05a42439082f5` |
| Genoa | `Genoa/ask.pem` | `5464738c1546aed5f2cecf1dc98c5c960a92e8913238a61711bc90ec6e828521` |
| Genoa | `Genoa/vlek-ca.pem` | `197e610743a917d6b9bb982a5a9226ccc0a15b611be0619e626aca9151457372` |
| Turin | `Turin/ask.pem` | `5b77ef5fe7a7a004fd9032668fba9d0fda22f88c4442069a479636a6ae3b3185` |
| Turin | `Turin/vlek-ca.pem` | `104e10a8bd060a3c20a434261a57d0588fd65a88915b4f65b08bdecaf8df1a3c` |

## Provenance

Fetched on 2026-11-14 over HTTPS from the AMD KDS:

```
https://kdsintf.amd.com/vcek/v1/Milan/cert_chain
https://kdsintf.amd.com/vcek/v1/Genoa/cert_chain
https://kdsintf.amd.com/vcek/v1/Turin/cert_chain
https://kdsintf.amd.com/vlek/v1/Milan/cert_chain
https://kdsintf.amd.com/vlek/v1/Genoa/cert_chain
https://kdsintf.amd.com/vlek/v1/Turin/cert_chain
```

`vcek/v1/<product>/cert_chain` contains the ASK and the ARK; the VCEK itself is
per-chip and is supplied by the guest (or fetched from KDS for the reported
chip ID and TCB).  `vlek/v1/<product>/cert_chain` contains the VLEK CA and the
same ARK.

The verifier does **not** fetch anything at run time.  To rotate a root, replace
the file and update both the table above and `AMD_ARK_SHA256` in
`scripts/attest/snp.py`; `snp.py` refuses to load a root whose digest does not
match the pinned value.
