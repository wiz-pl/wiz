# Commit and tag signing

Wiz uses signatures as a provenance boundary, not as a statement that a human
wrote every line. A commit or annotated tag may carry an SSH or GPG signature;
the protected branch accepts a commit that is signed, or one that a signed merge
commit covers. That is what lets pull requests from automation worktrees land
without giving those worktrees a human signing key.

The repository never contains a private key. Only public trust material lives in
the checkout:

| Path | Contents |
| --- | --- |
| `.github/allowed_signers` | SSH public keys trusted for `git` signatures, in `ssh-keygen` allowed-signers format |
| `.github/gpg/*.asc` | ASCII-armored **public** GPG keys trusted for commit/tag signatures |
| `.github/workflows/signatures.yml` | The CI check (self-test plus policy) |
| `scripts/check-signatures.py` | The checker, also usable locally |
| `scripts/test-check-signatures.py` | Throwaway-key self-test, no network and no personal key |

GitHub's own web-flow key is fetched by CI from
`https://github.com/web-flow.gpg`; it is not copied into the repository.

## What a signature proves

A valid signature proves that the holder of the private key signed this exact
commit or tag object at some time. For a merge commit, the signature covers the
tree and the parent object IDs, so it is a commitment to everything the merge
brings in. GitHub additionally requires the signing key to be on the account and
the commit author email to be verified before it shows a "Verified" badge.

A signature does **not** prove review, authorship, or that a binary was built
from the commit. A bot must not sign with a human's key: that would be a false
attestation. A bot that needs a signature gets its own key and identity.

## SSH signing (recommended)

SSH signing works with `ssh-keygen` and an OpenSSH-compatible agent, so an
existing SSH agent, or a password manager, can hold the private key. Git needs a
public key in its configuration and the private key only when it signs.

### Create a dedicated key

Do this once, for signing only; do not reuse an authentication key.

```sh
umask 077
ssh-keygen -t ed25519 -a 100 -C "wiz signing $(date +%F)" \
  -f "$HOME/.ssh/wiz-signing"
```

Keep the private half in a password manager (an attachment in an encrypted
database, injected into an SSH agent, when the database is unlocked) or, as a
fallback, as a passphrase-protected file in `~/.ssh`. In either case the public
half (`~/.ssh/wiz-signing.pub`) is what goes into Git configuration, GitHub, and
`.github/allowed_signers`.

For the password-manager route, the private key can be created in a tmpfs path
and attached without ever being written to persistent disk:

```sh
umask 077
ssh-keygen -t ed25519 -a 100 -C "wiz signing $(date +%F)" \
  -f /dev/shm/wiz-signing
# attach /dev/shm/wiz-signing to the password-manager entry, copy the .pub,
# then: shred -u /dev/shm/wiz-signing
```

Do not forward an SSH agent; the process that holds the signing key must stay
local. Locking the password-manager database removes the key from the agent, and
the next `git commit` then fails closed rather than silently committing
unsigned.

### Configure Git

With the key loaded in the agent, use the public key literally so no key file is
needed at signing time:

```sh
git config --global gpg.format ssh
git config --global user.signingkey "key::$(cat "$HOME/.ssh/wiz-signing.pub")"
git config --global commit.gpgsign true
git config --global tag.gpgSign true
```

If the key is a passphrase-protected file instead, point at the private key:

```sh
git config --global user.signingkey "$HOME/.ssh/wiz-signing"
```

Write an allowed-signers file for local verification. The email is the principal
Git reports for a good signature; `namespaces="git"` keeps the key from being
accepted for other SSH signature namespaces.

```sh
mkdir -p "$HOME/.config/git"
printf '%s namespaces="git" %s\n' \
  "$(git config user.email)" \
  "$(cat "$HOME/.ssh/wiz-signing.pub")" \
  > "$HOME/.config/git/allowed_signers"
git config --global gpg.ssh.allowedSignersFile "$HOME/.config/git/allowed_signers"
```

Use the same public key line in `.github/allowed_signers` so CI trusts it. Public
keys are not secrets; private keys, database files, and passphrases must never be
committed.

With Home Manager, the same settings can be declared instead of run by hand;
`signing.allowedSigners` writes `~/.config/git/allowed_signers` and wires it up:

```nix
programs.git = {
  enable = true;
  signing = {
    format = "ssh";
    key = "key::ssh-ed25519 AAAA... you@example.com";
    signByDefault = true;
    allowedSigners = ''
      you@example.com namespaces="git" ssh-ed25519 AAAA... you@example.com
    '';
  };
};
```

Keep the private key out of the Nix store and out of the dotfiles repository.

### Test it

Use a throwaway repository first, or the empty commit shown here:

```sh
git commit --allow-empty -S -m "test: signed commit"
git log --show-signature -1
git verify-commit HEAD
git tag -s v-test -m "test signed tag"
git tag -v v-test
```

`git log --show-signature` uses `gpg.format` from the configuration, so it must
be `ssh` for SSH signatures. `git verify-commit` and `git tag -v` detect the
signature type themselves and report `Good "git" signature` on success.

### Upload the public key to GitHub

Add the public key under **Settings → SSH and GPG keys → New SSH key**, with key
type **Signing Key**. If the `gh` CLI is used, its token needs the
`admin:ssh_signing_key` scope first:

```sh
gh auth refresh -h github.com -s admin:ssh_signing_key
gh ssh-key add "$HOME/.ssh/wiz-signing.pub" --type signing \
  --title "wiz signing $(date +%F)"
```

The commit email must be a verified GitHub email. Uploading the key as a signing
key does not change `git push` authentication.

## GPG (alternative)

GPG remains supported for contributors who already use it or need expiry and
revocation metadata. The private key then lives in `~/.gnupg`, or in a temporary
`GNUPGHOME` for a one-off signature; password managers cannot serve GPG keys to
`gpg-agent`.

```sh
gpg --quick-generate-key "Your Name <you@example.com>" ed25519 sign 0
fpr=$(gpg --list-secret-keys --with-colons |
  awk -F: '/^fpr:/{print $10; exit}')
git config --global gpg.format openpgp
git config --global user.signingkey "$fpr"
git config --global commit.gpgsign true
git config --global tag.gpgSign true
git commit --allow-empty -S -m "test: gpg-signed commit"
git log --show-signature -1
```

Export the **public** key into the repository (the checker imports every
`.github/gpg/*.asc`, `*.gpg` and `*.pub`):

```sh
gpg --armor --export "$fpr" > .github/gpg/you.asc
```

The default `gpg-agent` passphrase cache is bounded (`default-cache-ttl` 600 s,
`max-cache-ttl` 7200 s). Keep those bounds if the key is used interactively; do
not put the passphrase in shell history or an environment variable.

## The CI policy

`.github/workflows/signatures.yml` runs on a push to `master`, a tag push, a
pull request, and manually. It first runs the throwaway-key self-test, imports
GitHub's web-flow key, then checks the relevant range:

* **Push to `master`**: `BEFORE..AFTER`.
  Every commit must have a trusted signature, except a commit reachable from a
  signed merge commit in the same range. A direct push of unsigned commits fails;
  a normal pull-request merge passes because GitHub's signed merge commit covers
  the commits it brings in.
* **Tag `v*`**: the tag must be annotated (a lightweight tag cannot be signed) and
  its signature must verify. Release tags therefore need `git tag -s`.
* **Pull request**: the commits under the test merge run in `--warn` mode. A pull
  request is not a protected branch, and its commits are covered when the signed
  merge lands. Warnings identify unsigned commits early without blocking the
  current workflow.

The signing job is a normal check named `signed commits`. To make it a gate,
mark it required in the `master` branch protection rules (or ruleset). The check
does not enable itself: repository settings are not stored in the checkout.

Do **not** enable GitHub's own "Require signed commits" rule instead. It checks
every commit individually, so it rejects an unsigned automation commit even when
a signed merge covers it. Use this workflow's boundary policy, or give every
automation writer a dedicated bot key before switching.

The range rule is implemented by `scripts/check-signatures.py`; the self-test
shows both sides of each case. A signed merge commit is cryptographically a
commitment to its tree and history, which is why covering its ancestors is sound:

```sh
python3 scripts/test-check-signatures.py
python3 scripts/check-signatures.py --range origin/master..HEAD
python3 scripts/check-signatures.py --rev HEAD --warn
python3 scripts/check-signatures.py --tag v0.1.0
```

For a local check of GitHub's merge commits, download the public web-flow key
once and pass it explicitly:

```sh
curl -sSfL https://github.com/web-flow.gpg -o /tmp/web-flow.gpg
python3 scripts/check-signatures.py --gpg-key /tmp/web-flow.gpg --rev HEAD
```

The checker verifies with a temporary `GNUPGHOME` and null global/system Git
configuration, so a developer's trust settings cannot change the verdict. It
refuses to use a trust file that contains `PRIVATE KEY` material.

## Automation worktrees and the fallback

Automation worktrees do not hold a human signing key. Disable signing there with
a conditional Git include, so a missing signing key does not turn every commit
into an error:

```gitconfig
# ~/.config/git/unsigned
[commit]
	gpgsign = false
[tag]
	gpgSign = false
```

```gitconfig
# ~/.config/git/config
[includeIf "gitdir:/path/to/checkout/.git/worktrees/"]
	path = ~/.config/git/unsigned
[includeIf "gitdir:/path/to/checkout/.git"]
	path = ~/.config/git/unsigned
```

A linked worktree's real Git directory is
`<main-checkout>/.git/worktrees/<name>`, so match that path as well as the main
checkout. Verify before relying on it:

```sh
git -C /path/to/worktree config --get commit.gpgsign   # false
```

Automation commits then stay unsigned. They enter a protected branch through a
signed merge commit: a maintainer merges with `git merge -S`, or GitHub creates
and signs the merge commit when the pull request is merged with a merge commit.
The CI check treats that merge as the signature over the whole change. This is
the fallback that keeps the policy honest: no bot borrows a human key merely to
make a badge green.

If a bot genuinely needs its own signature (for example, release automation that
must produce signed tags), give it a dedicated key:

* a separate key and, preferably, a separate bot account or GitHub App;
* the private key in an environment-protected CI secret, never in a workflow
  file, an artifact, a log, or this repository;
* a workflow restricted to the release ref, and a rotation schedule;
* the public key in `.github/allowed_signers` or `.github/gpg/`, like any other.

Artifact provenance (`actions/attest-build-provenance` and similar) is a better
fit than a commit signature for "this binary came from this workflow".

## Rotation and compromise

Routine rotation keeps old and new keys valid at the same time:

1. Generate the new key and add its public half to `.github/allowed_signers`
   (or `.github/gpg/`).
2. Bound the old line with `valid-before="YYYYMMDD"` in `allowed_signers`; GPG
   keys carry their own expiry.
3. Start signing with the new key, add it to GitHub, and keep the old key on the
   account while old commits should still show Verified.
4. After the overlap, remove the old key from GitHub and from the trust files.

SSH signatures have no revocation certificate. If a key is compromised, remove
it from GitHub and from `.github/allowed_signers`, rotate, and state the
fingerprint and the date after which it must not be trusted. Old signatures
remain mathematically valid; the honest statement is about the compromise date,
not about rewriting history.

## Operational caveats

* `git verify-commit` checks that the key is trusted for some principal in
  `allowed_signers`; it does not require that principal to equal the commit's
  author or committer. The checker has the same property. GitHub performs the
  identity check for its badge (account key plus verified author email). If a
  repository needs local identity binding, add an explicit author/principal
  comparison; do not assume `git verify-commit` does it.
* SSH signatures have no built-in expiry or revocation. Use `valid-before` /
  `valid-after` in `allowed_signers` and rotate; removing a key from GitHub only
  changes how old commits are displayed.
* CI fetches `https://github.com/web-flow.gpg` on every run. A network failure or
  an unexpected GitHub key rotation fails the job; pin a reviewed copy in
  `.github/gpg/` if a self-contained check is required.
* The policy assumes merge commits. A squash or rebase merge may produce a
  different commit graph; verify that the resulting commit is signed and that
  the required merge method is still `--merge` before relying on the cover rule.
* A locked password manager or stopped signing process makes signing fail
  closed. That is preferable to an unsigned commit, but it also means unattended
  scripts must not be configured to sign with an interactive key.
* The pull-request job executes `scripts/check-signatures.py` and its self-test
  from the pull request's tree. It has read-only repository permissions and no
  secrets; keep it that way. Do not add a write token or a private key to this
  workflow.
* The checker trusts `.github/allowed_signers` as written. A malicious change to
  that file is a change to the trust policy and must be reviewed like code; the
  self-test and the private-key guard are not a substitute for review.
* `git log --show-signature` uses `gpg.format`; a globally configured
  `openpgp` value will not display SSH signatures. `git verify-commit` and the
  checker detect the format per object.
