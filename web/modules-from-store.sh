#!/bin/sh
# The three page-module derivations for this checkout, for the `web` job.
#
# `wasm` builds `.#wiz-web`, `.#wiz-playground` and `.#wiz-playground-ui` once per
# run and publishes them to Cachix; this step realises the same paths from there, so the
# job runs no Emscripten (the playground engine was ~10 min of a `web` run, with
# `wasm-opt`'s multi-GiB peak as the tail). The `docs` job does not call this script: it
# takes the modules as inputs of `.#pages`, the derivation that is the published site.
#
# A miss is a bug in the workflow — the job that owns them did not run, or this
# checkout's derivations are not the ones it published — so it fails rather than quietly
# spending ten minutes rebuilding both here. The one legitimate miss is a pull request
# from a fork: it has no Cachix token, so nothing could be published for it, and that run
# builds them (loudly, as a warning) instead of failing.
#
# Writes `web=…`, `playground=…` and `ui=…` (store paths) to $GITHUB_OUTPUT.
set -eu
# One bundle for all three module sets (`nix build .#web-bundle`): a *local* run may set
# WIZ_WEB_BUNDLE=1 (or a store path) and export the same directory for each `--from`; the
# `web` job does not set it, so a CI run takes the three paths from the producer below.
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
if [ -n "${WIZ_MODULES_WEB:-}" ] && [ -n "${WIZ_MODULES_PLAYGROUND:-}" ] && [ -n "${WIZ_MODULES_UI:-}" ] \
   && paths=$(nix build $producer --no-link --print-out-paths --max-jobs 0 2>/dev/null); then
  :
elif paths=$(nix build $ids --no-link --print-out-paths --max-jobs 0 2>/dev/null); then
  :
elif [ "${GITHUB_EVENT_NAME:-}" = pull_request ] && [ -z "${CACHIX_AUTH_TOKEN:-}" ]; then
  echo "::warning title=Cachix::a fork pull request has no token: building .#wiz-web, .#wiz-playground and .#wiz-playground-ui in this job"
  paths=$(nix build $ids --no-link --print-out-paths -L)
else
  echo "::error title=Cachix::.#wiz-web/.#wiz-playground/.#wiz-playground-ui are not in the cache: the wasm job must build and publish them"
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
