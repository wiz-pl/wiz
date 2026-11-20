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
# Writes `web=…`, `playground=…` and `ui=…` (store paths) to $GITHUB_OUTPUT.
set -eu
ids=".#wiz-web .#wiz-playground .#wiz-playground-ui"
if paths=$(nix build $ids --no-link --print-out-paths --max-jobs 0 2>/dev/null); then
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
echo "web=$web" >> "$GITHUB_OUTPUT"
echo "playground=$playground" >> "$GITHUB_OUTPUT"
echo "ui=$ui" >> "$GITHUB_OUTPUT"
echo "wiz-web: $web"; echo "wiz-playground: $playground"; echo "wiz-playground-ui: $ui"
du -sh "$web" "$playground" "$ui"
