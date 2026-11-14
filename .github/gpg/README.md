# GPG signing keys

Put **public** keys trusted for GPG-signed commits and tags here, one ASCII-armored
file per key, named `<owner>.asc`. `scripts/check-signatures.py` imports every
`*.asc`, `*.gpg` and `*.pub` file in this directory, and the signatures CI job
also imports GitHub's web-flow key from `https://github.com/web-flow.gpg`.

Export a public key with:

```sh
gpg --armor --export <fingerprint> > .github/gpg/<owner>.asc
```

Do not export a secret key here (`gpg --export-secret-keys`); the checker
rejects a file containing `PRIVATE KEY`. See `docs/signing.md`.
