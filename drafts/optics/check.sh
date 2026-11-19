#!/bin/sh
# Check the optics drafts. Pass a `wiz` binary as the first argument (the worktree's
# own build, e.g. ../train7/.lake/build/bin/wiz, enforces quantities most strictly).
set -eu
wiz=${1:-wiz}
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
cd "$root"
"$wiz" check -I drafts/optics drafts/optics/Profunctor.wiz
"$wiz" check -I drafts/optics drafts/optics/Traversal.wiz
"$wiz" check -I drafts/optics drafts/optics/Tests.wiz
"$wiz" check -I drafts/optics drafts/optics/Laws.wiz
"$wiz" check -I drafts/storage-engine -I drafts/optics drafts/storage-engine/Storage.wiz
"$wiz" check -I drafts/storage-engine -I drafts/optics drafts/optics/EngineIndex.wiz
