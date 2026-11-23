#!/bin/sh
# Check and run the slice-2 durable store (compiled: the file natives are `wiz run` code).
#   drafts/storage-engine/test-durable.sh [PATH-TO-WIZ]
# The default binary is the worktree's own build (`.lake/build/bin/wiz`), so the runtime
# and lib/Sys.wiz used are the ones in this tree. If `cc` or GMP is not on the path, run
# this from the nix dev shell, or put the two flags in WIZ_RUN_FLAGS:
#   WIZ_RUN_FLAGS='--cflags "-I…/gmp/include" --ldflags "-L…/gmp/lib"' drafts/storage-engine/test-durable.sh
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
wiz=${1:-${WIZ:-$root/.lake/build/bin/wiz}}
run_flags=${WIZ_RUN_FLAGS:-}
cd "$root"
"$wiz" check lib/Scry/QuireStorage.wiz
"$wiz" check lib/Scry/QuireDurable.wiz
"$wiz" check -I drafts/storage-engine -I drafts/optics drafts/storage-engine/DurableTest.wiz
# shellcheck disable=SC2086
"$wiz" run -I drafts/storage-engine -I drafts/optics $run_flags drafts/storage-engine/DurableTest.wiz
