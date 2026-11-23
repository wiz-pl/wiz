# Nix artifacts for the CI split

This is the handover note for the lane splitting `.github/workflows/ci.yml`. **No CI
workflow is edited here.** Every artifact below is a flake package, built with
`nix build .#<name>`, and each one is input-addressed by the sources it reads
(`passthru.subset` names that boundary). A successful subset from a failed pull-request
run can therefore be restored with `nix copy --from` while unchanged; a docs change does
not invalidate a Wasm module, and a change to one web module does not invalidate the
others.

## The exact steps

### `wasm modules` (`web_modules`)

```sh
nix build .#wiz-web .#wiz-playground .#wiz-playground-ui .#wiz-source-ui --no-link --max-jobs 1
```

Unchanged. Each path is published to Cachix as today. `.#web-bundle` is the union of the
three page-module outputs for consumers that want one path:

```sh
nix build .#web-bundle --no-link --print-out-paths
```

### `web`

Replace the three `WIZ_*_FROM` paths with the bundle (supported by `web/test.sh`):

```sh
bundle=$(nix build .#web-bundle --no-link --print-out-paths)
WIZ_WEB_BUNDLE="$bundle" \
WIZ=$wiz/bin/wiz WIZ_WEB_NO_BROWSER=1 sh web/test.sh
```

`web/test.sh` sets `WIZ_WEB_FROM`, `WIZ_PLAYGROUND_FROM` and `WIZ_PLAYGROUND_UI_FROM`
from `WIZ_WEB_BUNDLE` when they are unset, so the existing per-module variables still
work and the fork fallback needs no change. `WIZ_WEB_BUNDLE=1 sh web/modules-from-store.sh`
builds the bundle and writes the same three outputs (all the bundle path), for a job that
wants to keep that script.

### `docs` (`wiz doc --lib + site`)

The whole job's product is now one output; no `wiz doc`, `cp`, or `web/build-site.sh`
step is needed in the workflow:

```sh
site=$(nix build .#docs-site --no-link --print-out-paths)
```

`$site` is the tree the job assembled before (landing page, `/docs/`, `/guide/`,
`/bench/`, `/playground/`, `/licenses/`, `/notebooks/`), without `/source/`. The
elaboration cache and `.#reference` are inputs of the derivation, so the job no longer
restores or publishes the `wiz-doc-v1-*` cache; Cachix serves the whole output instead.

### `deploy docs to Pages`

Upload `$pages`, not the artifact the `docs` job assembled by hand:

```sh
pages=$(nix build .#pages --no-link --print-out-paths)
```

`$pages` is the exact `doc-site` tree — the `docs-site` output plus `/source/` (the
`scry` reader built with `grail build scry`, `web/source-bundle.sh`, and
`.#wiz-source-ui`). `actions/upload-pages-artifact` should take `path: $pages`. The
`wiz-docs` artifact, if the split still wants one for debugging, can be
`actions/upload-artifact` with `path: $pages`.

### `source tarball`

Unchanged: `nix build .#release-tarball` (alias `.#source-tarball`).

The **binary** release tarball is new:

```sh
nix build .#release-bin --no-link --print-out-paths
# $out/wiz-<arch>-linux.tar.gz and $out/wiz-<arch>-linux.tar.gz.sha256
```

Its `doCheck` runs `scripts/test-release-portability.sh` (only glibc, no `/nix/store`,
no RUNPATH) and rebuilds the archive twice in different environments and compares them.
`release.yml` can publish these files instead of running `lake build`,
`scripts/bundle-cc.sh` and `scripts/release-tarball.sh` itself. The Nix tarball has no
`share/wiz/cc`; `wiz build` uses the host `cc`/GMP. `release-bin-cc` (see
[release-variants.md](release-variants.md)) is the explicit variant that ships
`release-cc` at `share/wiz/cc`; it is a separate attribute, so the default tarball is
unchanged. `scripts/test-release-install.sh`'s bundled-compiler checks therefore apply
to `release-bin-cc` and to a release.yml tarball that still ships `cc-bundle`.

## Subset boundaries (for reuse across a failed run)

| output | `passthru.subset` |
|---|---|
| `wiz-wasm-fixtures` | `scripts/wasm-fixtures/` + `web/wasm-host.mjs` |
| `wiz-web-bundle` | `wiz-web` + `wiz-playground` + `wiz-playground-ui` (each its own fileset) |
| `wiz-docs-site` | `docs/` + `bench/` + `examples/` + `tools/` + `editors/` + `drafts/` + `scry/` + `README.md`/`ROADMAP.md`/`CHANGELOG.md`/`LICENSE` + `siteAssetFiles` (the site scripts, enumerated in `flake.nix`) + `wiz` + `reference` + `wiz-web-bundle` |
| `wiz-pages` | `wiz-docs-site` + `scry/` + `web/source-{bundle.sh,app.js,css,static.js}` + `web/framework/` + `wiz-source-ui` + `tree-sitter-c-sharp` |
| `wiz-release-bin` | `lib/` + `editors/` + `scripts/release-licenses` + `LICENSE` + `COPYING.RUNTIME` + `web/wasm-host.mjs`, composed with `release-unwrapped` + `release-tower` + `wiz-web` |
| `wiz-release-cc` | `scripts/bundle-cc.sh` + `scripts/bundle-cc.sources` + the pinned official Lean toolchain tarball (clang, `ld.lld`, `cadical`, `lib/clang`, licences) + the pinned downloads for the host architecture (libc6/libc6-dev/linux-libc-dev debs, GMP 6.3.0, Boehm GC 8.2.8) |
| `wiz-release-bin-cc` | `wiz-release-bin`'s subset + `release-cc` |
| `wiz-unwrapped-release` | `buildSrc`: `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `Main.lean`, `Wiz/`, `Grail/`, `WizMeta/`, `STC/`, `Tests/`, `runtime/`, `c/` (the release is a leaf; Lake reads the package definition) |

The release leaf is the only artifact allowed to depend on all of them. Its leaf step
(interpreter, RUNPATH, store-path scrub) is in `flake.nix`'s `release-bin` `buildPhase`
with the comment that it deliberately breaks Nix convention; do not hoist it.
