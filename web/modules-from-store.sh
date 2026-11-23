#!/bin/sh
# The three page-module derivations for this checkout, for the `web` and `docs` jobs.
#
# `web_modules` builds `.#wiz-web`, `.#wiz-playground` and `.#wiz-playground-ui` once per
# run and publishes them to Cachix; this step realises the same paths from there, so
# neither job runs Emscripten (the playground engine was ~10 min of a `web` run, with
# `wasm-opt`'s multi-GiB peak as the tail, and the `docs` job used to repeat the builds on
# every push).
#
# A miss is a bug in the workflow — the job that owns them did not run, or this
# checkout's derivations are not the ones it published — so it fails rather than quietly
# spending ten minutes rebuilding both here. The one legitimate miss is a pull request
# from a fork: it has no Cachix token, so nothing could be published for it, and that run
# builds them (loudly, as a warning) instead of failing.
#
# Writes `web=…`, `playground=…`, `ui=…` and (when the caller passes it) `source_ui=…`
# (store paths) to $GITHUB_OUTPUT. The source reader's module is optional because only
# the `docs` job renders `/source/`; when `WIZ_MODULES_SOURCE_UI` is set it is realised
# the same way (`nix build <path> --max-jobs 0` substitutes it, it does not rebuild).
set -eu
# One bundle for all three module sets (`nix build .#web-bundle`): the `web` job can set
# WIZ_WEB_BUNDLE=1 (or a store path) and export the same directory for each `--from`.
# The source reader's module: the `docs` job renders /source/ and used to take the
# producer's path as a string, which nothing demanded from Nix - so the path was absent
# on the runner and source-bundle.sh failed with "wiz-source-ui.mjs is missing".
if [ -n "${WIZ_MODULES_SOURCE_UI:-}" ]; then
  if ! source_ui=$(nix build "$WIZ_MODULES_SOURCE_UI" --no-link --print-out-paths --max-jobs 0 2>/dev/null); then
    if [ "${GITHUB_EVENT_NAME:-}" = pull_request ] && [ -z "${CACHIX_AUTH_TOKEN:-}" ]; then
      echo "::warning title=Cachix::a fork pull request has no token: building .#wiz-source-ui here"
      source_ui=$(nix build .#wiz-source-ui --no-link --print-out-paths -L)
    else
      echo "::error title=Cachix::.#wiz-source-ui is not in the cache: the wasm modules job must build and publish it"
      nix build "$WIZ_MODULES_SOURCE_UI" --no-link --print-out-paths --max-jobs 0
      exit 1
    fi
  fi
  [ -f "$source_ui/wiz-source-ui.mjs" ] || {
    echo "modules-from-store: $source_ui has no wiz-source-ui.mjs" >&2; exit 1; }
  [ -f "$source_ui/wiz-source-ui.wasm" ] || {
    echo "modules-from-store: $source_ui has no wiz-source-ui.wasm" >&2; exit 1; }
  echo "source_ui=$source_ui" >> "$GITHUB_OUTPUT"
  echo "wiz-source-ui: $source_ui"
fi

if [ -n "${WIZ_WEB_BUNDLE:-}" ]; then
  bundle=$WIZ_WEB_BUNDLE
  if [ ! -d "$bundle" ]; then
    bundle=$(nix build .#web-bundle --no-link --print-out-paths --max-jobs 1) || exit 1
  fi
  for f in wiz-infoview.mjs wiz-playground.mjs wiz-playground.wasm \
           wiz-playground-ui.mjs wiz-playground-ui.wasm; do
    [ -f "$bundle/$f" ] || { echo "modules-from-store: $bundle has no $f" >&2; exit 1; }
  done
  echo "web=$bundle" >> "$GITHUB_OUTPUT"
  echo "playground=$bundle" >> "$GITHUB_OUTPUT"
  echo "ui=$bundle" >> "$GITHUB_OUTPUT"
  echo "web-bundle: $bundle"
  du -sh "$bundle"
  exit 0
fi
ids=".#wiz-web .#wiz-playground .#wiz-playground-ui"
# The producer's paths, when the workflow passes them. On a pull request they are
# `withLakeCache` derivations (the seed is an input), so their store paths differ
# from the pure attrs above; recomputing those can never match what was pushed.
producer="${WIZ_MODULES_WEB:-} ${WIZ_MODULES_PLAYGROUND:-} ${WIZ_MODULES_UI:-}"
# (the source reader is a separate, optional call when the caller needs it)
if [ -n "${WIZ_MODULES_WEB:-}" ] && [ -n "${WIZ_MODULES_PLAYGROUND:-}" ] && [ -n "${WIZ_MODULES_UI:-}" ] \
   && paths=$(nix build $producer --no-link --print-out-paths --max-jobs 0 2>/dev/null); then
  :
elif paths=$(nix build $ids --no-link --print-out-paths --max-jobs 0 2>/dev/null); then
  :
elif [ "${GITHUB_EVENT_NAME:-}" = pull_request ] && [ -z "${CACHIX_AUTH_TOKEN:-}" ]; then
  echo "::warning title=Cachix::a fork pull request has no token: building .#wiz-web, .#wiz-playground and .#wiz-playground-ui in this job"
  paths=$(nix build $ids --no-link --print-out-paths -L)
else
  echo "::error title=Cachix::.#wiz-web/.#wiz-playground/.#wiz-playground-ui are not in the cache: the web_modules job must build and publish them"
  # again, without the discarded stderr: the error names what is missing and why
  nix build $ids --no-link --print-out-paths --max-jobs 0
  exit 1
fi
set -- $paths
web=$1 playground=$2 ui=$3
[ -f "$web/wiz-infoview.mjs" ] || {
  echo "modules-from-store: $web has no wiz-infoview.mjs" >&2; exit 1; }
[ -f "$playground/wiz-playground.mjs" ] || {
  echo "modules-from-store: $playground has no wiz-playground.mjs" >&2; exit 1; }
[ -f "$ui/wiz-playground-ui.mjs" ] || {
  echo "modules-from-store: $ui has no wiz-playground-ui.mjs" >&2; exit 1; }
[ -f "$ui/wiz-playground-ui.wasm" ] || {
  echo "modules-from-store: $ui has no wiz-playground-ui.wasm" >&2; exit 1; }
echo "web=$web" >> "$GITHUB_OUTPUT"
echo "playground=$playground" >> "$GITHUB_OUTPUT"
echo "ui=$ui" >> "$GITHUB_OUTPUT"
echo "wiz-web: $web"; echo "wiz-playground: $playground"; echo "wiz-playground-ui: $ui"
du -sh "$web" "$playground" "$ui"
