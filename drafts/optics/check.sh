#!/bin/sh
# Check the storage-engine drafts against the optics layer that now lives in
# lib/Optic.wiz. Pass a `wiz` binary built from this worktree (a `lib/` edit is
# shadowed by the installed library, so the shipped binary is not enough).
set -eu
wiz=${1:?"usage: check.sh /path/to/worktree/.lake/build/bin/wiz"}
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
cd "$root"
"$wiz" check -I drafts/optics drafts/optics/Tests.wiz
"$wiz" check -I drafts/optics drafts/optics/Limits.wiz
"$wiz" check -I drafts/storage-engine -I drafts/optics drafts/storage-engine/Storage.wiz
"$wiz" check -I drafts/storage-engine -I drafts/optics drafts/optics/EngineIndex.wiz
