# Making a release

How a `vX.Y.Z` release is made. What a release promises is in
[stability.md](stability.md), and what changed is in [CHANGELOG.md](../CHANGELOG.md).
The release workflow is `.github/workflows/release.yml`.

## Before tagging

Each item says what must be true and how to check it.

1. **The pull requests planned for the release are merged.** Every planned PR has
   either merged or been moved to the next release, and CHANGELOG.md says so.
2. **CI is green on the commit to tag.** Use a commit that the tag `nightly` points at
   (`git ls-remote https://github.com/wiz-pl/wiz refs/tags/nightly`). nightly.yml moves
   that tag only after the push run of `ci.yml` passed on the commit and its snapshot
   was published, so such a commit has passed CI. The weekly bootstrap fixpoint (the
   scheduled `ci.yml` run, or a dispatch with `fixpoint: true`) must be green on that
   commit, or on one with the same `selfhost/` tree.
3. **The exercise tree builds.** release.yml checks it only for `v*` tags, and a tag
   whose exercise tree fails publishes nothing. Check it first:
   `python3 scripts/mkexercises.py . /tmp/ex && (cd /tmp/ex && lake build wiz grail tests)`.
4. **Soundness status.** [Status.md](Status.md) describes the commit to tag, and every
   trust flag in the release (`--trust-*`) is listed in its trusted base. Check that
   no closed proof of `False` with default flags is known and unmerged. The audit groups
   pass in CI. Copy Status.md's open issues and conjectures into CHANGELOG.md under
   "Known limitations".
5. **Docs.** These exist and match the release: [install.md](install.md) (installing
   with tower, Nix or from source; the glibc floor; x86_64 Linux only),
   [tour.md](tour.md), [stability.md](stability.md), CHANGELOG.md, and the README's
   quick start.
6. **The snapshot of that commit passes the install smoke test.** Download its tarball
   (`snapshot-<sha>`, or the `wiz-x86_64-linux` artifact of its release.yml run) and run

   ```sh
   sh scripts/test-release-install.sh wiz-x86_64-linux.tar.gz vX.Y.Z
   ```

   This installs the tarball with `tower-init.sh` as the toolchain of a simulated tag,
   in a scratch directory. Nothing is pushed. It checks the tarball's contents (NOTICE,
   licences, the bundled C compiler and CaDiCaL, no z3), and that tower's default
   URLs, `tower-init.sh` and release.yml agree on `https://github.com/wiz-pl/wiz`. It
   then runs `stable`, a `wiz-toolchain` file, `wiz check/run/build` and a grail
   package. Also run the tests that CI does not run: `web/test.sh`, `infoview/test.sh`
   and the `nvim` group with a real Neovim.

## The tagging commit

On a branch off the commit to tag, open one PR that:

* sets the version to `X.Y.Z` in `Wiz/Version.lean`, `lakefile.lean`, `flake.nix`
  (`version = …`) and `tower/Tower/Cli.wiz` (`--version`);
* renames CHANGELOG.md's section `[X.Y.Z] - unreleased (draft)` to
  `[X.Y.Z] - YYYY-MM-DD` and leaves an empty `[Unreleased]` above it;
* puts the release's install line in the README (`tower default vX.Y.Z`).

Merge the PR. Then wait until CI is green on the merge commit and `nightly` has moved
to it. Tag that commit and push only the tag (a maintainer does this; CI does not push tags):

```sh
git tag -a vX.Y.Z -m "Wiz vX.Y.Z" <commit>
git push origin vX.Y.Z
```

The tag push runs release.yml. Its `exercises` job builds the exercise tree. Then
`tarball` builds and tests the tarball, runs the install smoke test with the tag's name,
and publishes the release `vX.Y.Z` with `wiz-x86_64-linux.tar.gz` and its `.sha256`.
The release notes are CHANGELOG.md's section `[X.Y.Z]` plus the install line; the step
fails if the section is missing. If the release already exists (a re-run), the step
fails rather than replace its assets. Delete a half-made draft release by hand before
re-running. The release is not a pre-release.
Snapshots are published with `--latest=false`, so the tag's release becomes "latest".
Snapshot pruning keeps every snapshot that a `v*` tag points at.

## After the tag

1. `sh scripts/test-release-install.sh --online wiz-x86_64-linux.tar.gz vX.Y.Z`, with the
   tarball downloaded from the release, checks the published URLs too.
2. On a clean machine (`docker run --rm -it ubuntu:24.04`):
   `curl -sSfL https://raw.githubusercontent.com/wiz-pl/wiz/vX.Y.Z/scripts/tower-init.sh | sh -s -- vX.Y.Z`.
   Then check that `wiz --version` prints `wiz X.Y.Z (<sha of the tag>)` and that
   `tower default stable` resolves to `vX.Y.Z`. Also run once with Nix:
   `nix run github:wiz-pl/wiz/vX.Y.Z#wiz -- --version`.
3. Open a PR that sets the version to the next `-dev` (`0.2.0-dev`) in the four places
   above.
