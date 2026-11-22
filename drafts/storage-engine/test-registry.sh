#!/bin/sh
# Check and run the persisted retention registry (format v2; compiled: the file natives
# are `wiz run` code).
#   drafts/storage-engine/test-registry.sh [PATH-TO-WIZ]
# The default binary is the worktree's own build (`.lake/build/bin/wiz`), so the runtime
# and lib/Sys.wiz used are the ones in this tree. If `cc` or GMP is not on the path, run
# this from the nix dev shell, or put the two flags in WIZ_RUN_FLAGS:
#   WIZ_RUN_FLAGS='--cflags "-I…/gmp/include" --ldflags "-L…/gmp/lib"' drafts/storage-engine/test-registry.sh
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
wiz=${1:-${WIZ:-$root/.lake/build/bin/wiz}}
run_flags=${WIZ_RUN_FLAGS:-}
cd "$root"
"$wiz" check lib/Scry/QuireRegistry.wiz
"$wiz" check lib/Scry/QuireDurable.wiz
"$wiz" check lib/Scry/QuireCompact.wiz
"$wiz" check -I drafts/storage-engine drafts/storage-engine/RegistryTest.wiz
# shellcheck disable=SC2086
"$wiz" run -I drafts/storage-engine $run_flags drafts/storage-engine/RegistryTest.wiz
