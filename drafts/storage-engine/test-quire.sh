#!/bin/sh
# Check and run the page-backed store and its page cursor (compiled: the file and mmap
# natives are `wiz run` code).
#   drafts/storage-engine/test-quire.sh [PATH-TO-WIZ]
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
wiz=${1:-${WIZ:-$root/.lake/build/bin/wiz}}
run_flags=${WIZ_RUN_FLAGS:-}
cd "$root"
"$wiz" check lib/Scry/Quire.wiz
"$wiz" check lib/Scry/QuireCursor.wiz
"$wiz" check -I drafts/storage-engine drafts/storage-engine/QuireTest.wiz
# shellcheck disable=SC2086
"$wiz" run -I drafts/storage-engine $run_flags drafts/storage-engine/QuireTest.wiz
