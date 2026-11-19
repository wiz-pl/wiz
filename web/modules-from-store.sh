#!/bin/sh
# The two page-module derivations for this checkout, for the `web` and `docs` jobs.
#
# `web_modules` builds `.#wiz-web` and `.#wiz-playground` once per run and publishes them
# to Cachix; this step realises the same two paths from there, so neither job runs
# Emscripten (the playground engine is ~10 min of a `web` run, with `wasm-opt -O2`'s
# 8–10 GiB peak as the tail, and the `docs` job used to run both builds again on every
# push).
#
# A miss is a bug in the workflow — the job that owns them did not run, or this
# checkout's derivations are not the ones it published — so it fails rather than quietly
# spending ten minutes rebuilding both here. The one legitimate miss is a pull request
# from a fork: it has no Cachix token, so nothing could be published for it, and that run
# builds them (loudly, as a warning) instead of failing.
#
# Writes `web=…` and `playground=…` (store paths) to $GITHUB_OUTPUT.
set -eu
ids=".#wiz-web .#wiz-playground"
if paths=$(nix build $ids --no-link --print-out-paths --max-jobs 0 2>/dev/null); then
  :
elif [ "${GITHUB_EVENT_NAME:-}" = pull_request ] && [ -z "${CACHIX_AUTH_TOKEN:-}" ]; then
  echo "::warning title=Cachix::a fork pull request has no token: building .#wiz-web and .#wiz-playground in this job"
  paths=$(nix build $ids --no-link --print-out-paths -L)
else
  echo "::error title=Cachix::.#wiz-web/.#wiz-playground are not in the cache: the web_modules job must build and publish them"
  # again, without the discarded stderr: the error names what is missing and why
  nix build $ids --no-link --print-out-paths --max-jobs 0
  exit 1
fi
set -- $paths
web=$1 playground=$2
[ -f "$web/wiz-infoview.mjs" ] || {
  echo "modules-from-store: $web has no wiz-infoview.mjs" >&2; exit 1; }
[ -f "$playground/wiz-playground.mjs" ] || {
  echo "modules-from-store: $playground has no wiz-playground.mjs" >&2; exit 1; }
echo "web=$web" >> "$GITHUB_OUTPUT"
echo "playground=$playground" >> "$GITHUB_OUTPUT"
echo "wiz-web: $web"; echo "wiz-playground: $playground"
du -sh "$web" "$playground"
