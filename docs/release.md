# Making a release

How a `vX.Y.Z` release is made. What a release promises is in
[stability.md](stability.md), and what changed is in [CHANGELOG.md](../CHANGELOG.md).
The release workflow is `.github/workflows/release.yml`. The concrete pass for 0.1 is
[release/v0.1-checklist.md](release/v0.1-checklist.md), with its notes in
[release/v0.1.md](release/v0.1.md).

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
   package. Also run the tests that CI does not run: the Chromium half of
   `web/test.sh` (leave `WIZ_WEB_NO_BROWSER` unset), `infoview/test.sh`
   and the `nvim` group with a real Neovim.
7. **The supply-chain artifacts match the tarballs.** Generate both SBOMs and the
   provenance from the snapshot (release.yml does this for a real run) and run the
   checks:

   ```sh
   python3 scripts/test_release_sbom.py -v
   python3 scripts/release-sbom.py --out dist --root . \
     --source-manifest dist/wiz-<version>-src.tar.gz.manifest.json \
     --binary-tarball dist/wiz-x86_64-linux.tar.gz \
     --channel snapshot --builder-id https://wiz-lang.org/builders/local \
     --invocation-id local-1 --json
   ```

   Every SBOM component hash must match the unpacked tarball, the provenance subject
   digests must match the source tarball, source manifest, source SBOM, binary tarball
   and binary SBOM, and two runs with the same arguments must be byte-identical. The
   provenance is SLSA-style, not a hosted SLSA level; `--sign-key` adds the E1 DSSE
   signature and is optional. Fill `release-manifest.json`'s `supplyChain` object from
   the generated files.

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
and publishes the release `vX.Y.Z` with `wiz-x86_64-linux.tar.gz`, its `.sha256` and
`.cdx.json`, the reproducible source tarball `wiz-<version>-src.tar.gz` with its
`.manifest.json`, `.sha256` and `.cdx.json`, `provenance.intoto.json`, and (when the
`WIZ_ATTEST_KEY` secret is set) the `.dsse` envelope and detached `.sig`
([building.md](building.md), "Reproducible source tarball" and "Release SBOM and
provenance"). The release notes are CHANGELOG.md's section `[X.Y.Z]` plus the install line; the step
fails if the section is missing. If the release already exists (a re-run), the step
fails rather than replace its assets. Delete a half-made draft release by hand before
re-running. The release is not a pre-release.
Snapshots are published with `--latest=false`, so the tag's release becomes "latest".
Snapshot pruning keeps every snapshot that a `v*` tag points at.

## After the tag

1. `sh scripts/test-release-install.sh --online wiz-x86_64-linux.tar.gz vX.Y.Z`, with the
   tarball downloaded from the release, checks the published URLs too.
2. The source tarball reproduces from the tag. Check out the tag and build it twice,
   then compare with each other and with the published asset:

   ```sh
   root=$(git rev-parse --show-toplevel)
   python3 "$root/scripts/source-tarball.py" --root "$root" --out /tmp/src-a --mode git
   (cd /tmp && python3 "$root/scripts/source-tarball.py" --root "$root" \
      --out /tmp/src-b --mode git)
   cmp /tmp/src-a/*.tar.gz /tmp/src-b/*.tar.gz
   cmp /tmp/src-a/*.cdx.json /tmp/src-b/*.cdx.json
   sha256sum /tmp/src-a/*.tar.gz
   ```

   The SHA-256 must equal the published `.sha256` file and the manifest's
   `tarball.sha256`; both manifests' `tree.sha256` must match; the source SBOM's digest
   must equal the manifest's `sbom.sha256` and its top component digest must equal the
   tarball's. A mismatch means the tag was not built from the source it claims (the
   epoch is the commit's, so it does not depend on the machine).

3. On a clean machine (`docker run --rm -it ubuntu:24.04`):
   `curl -sSfL -o tower-init.sh https://raw.githubusercontent.com/wiz-pl/wiz/vX.Y.Z/scripts/tower-init.sh`,
   check it against the release notes' `sha256sum`, then `sh tower-init.sh vX.Y.Z`.
   Then check that `wiz --version` prints `wiz X.Y.Z (<sha of the tag>)` and that
   `tower default stable` resolves to `vX.Y.Z`. Also run once with Nix:
   `nix run github:wiz-pl/wiz/vX.Y.Z#wiz -- --version`.

4. Verify the published supply-chain files: parse both `.cdx.json` files, check the
   subject digests in `provenance.intoto.json` against the downloaded assets, and if
   the release has a `.dsse`/`.sig`, verify it with the pinned E1 key fingerprint. The
   provenance claims the build inputs and outputs; it does not claim a hosted SLSA
   level.

5. Open a PR that sets the version to the next `-dev` (`0.2.0-dev`) in the four places
   above. If `scripts/tower-init.sh` changed since the last release, update the pinned
   hash in `docs/install.md` and `web/landing/index.html` in the same PR
   (`sha256sum scripts/tower-init.sh`): the install command there fails closed.
