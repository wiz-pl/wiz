#!/usr/bin/env bash
# Build scry from a wiz checkout into ~/.cache/scry/bin/scry.
#
# Called only when resolve.sh found neither scry-path nor scry on PATH. The binary is
# cached by action.yml (keyed by the os, architecture, scry-version and a content hash
# of the scry sources), so the expensive `nix build .#wiz` + `grail build scry` runs
# once per revision instead of once per pull request.
set -euo pipefail

say() { printf 'scry: %s\n' "$*"; }
die() { printf 'scry: error: %s\n' "$*" >&2; exit 1; }

[ -n "${SCRY_BIN:-}" ] || die "SCRY_BIN is not set (resolve.sh must run first)"
[ -n "${SCRY_SOURCE_DIR:-}" ] || die "SCRY_SOURCE_DIR is not set"

if [ -x "$SCRY_BIN" ]; then
  say "using cached $SCRY_BIN"
  exit 0
fi

command -v nix >/dev/null 2>&1 \
  || die "building scry needs Nix (install nix, or pass a prebuilt scry-path)"

cd "$SCRY_SOURCE_DIR"
[ -f flake.nix ] || die "no flake.nix in $SCRY_SOURCE_DIR; pass a prebuilt scry-path"
[ -f scry/grail.wiz ] || die "no scry/grail.wiz in $SCRY_SOURCE_DIR"

# The dev shell writes the uncommitted grail.local.wiz (cc, llc, GMP, Boehm GC paths).
say "entering the dev shell to write grail.local.wiz"
nix develop --command bash -c 'true'

# Cachix substitutes this build on CI; a cold run compiles wiz and grail with Lean.
say "nix build .#wiz (grail)"
wiz=$(nix build --no-link --print-out-paths .#wiz)
grail="$wiz/bin/grail"
[ -x "$grail" ] || grail=$(command -v grail 2>/dev/null || true)
[ -n "$grail" ] && [ -x "$grail" ] || die "no grail in the nix build output"

cd "$SCRY_SOURCE_DIR/scry"
[ -f grail.local.wiz ] || cp ../grail.local.wiz . 2>/dev/null \
  || die "scry/grail.local.wiz is missing (the dev shell does not cover this tree)"
[ -f grail.wiz ] || die "no scry/grail.wiz"

say "grail build scry"
"$grail" build scry

[ -x .grail/bin/scry ] || die "grail build did not produce scry/.grail/bin/scry"
mkdir -p "$(dirname "$SCRY_BIN")"
cp .grail/bin/scry "$SCRY_BIN"
chmod +x "$SCRY_BIN"
say "built $SCRY_BIN"
