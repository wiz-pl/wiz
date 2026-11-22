#!/bin/sh
# Check and run the Quire findings-store prototype (compiled: the file natives are
# `wiz run` code).
#   drafts/scry-quire/test.sh [PATH-TO-WIZ]
# The default is the worktree's own build (`.lake/build/bin/wiz`), so the runtime and
# lib/ are the ones in this tree (the system `wiz` predates `Fd.sync`/`Scry.Workflow`).
# If `cc` or GMP is not on the path, put the flags in WIZ_RUN_FLAGS, as for
# drafts/storage-engine/test-durable.sh.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
wiz=${1:-${WIZ:-$root/.lake/build/bin/wiz}}
run_flags=${WIZ_RUN_FLAGS:-}
cd "$root"
"$wiz" check -I drafts/storage-engine -I drafts/scry-quire drafts/scry-quire/FindingsQuire.wiz
"$wiz" check -I drafts/storage-engine -I drafts/scry-quire drafts/scry-quire/FindingsQuireTest.wiz
# shellcheck disable=SC2086
"$wiz" run -I drafts/storage-engine -I drafts/scry-quire $run_flags \
  drafts/scry-quire/FindingsQuireTest.wiz
