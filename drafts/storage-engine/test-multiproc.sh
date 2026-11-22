#!/bin/sh
# Check and run the multi-process store contract (compiled: the file and lock natives are
# `wiz run` code). The default binary is the worktree's own build, so the runtime and
# lib/Sys.wiz used are the ones in this tree. `wiz run` compiles C, so it needs GMP's
# include/link flags: source /workspace/wiz-env.sh (it sets WIZ_CFLAGS/WIZ_LDFLAGS and
# puts the toolchain on PATH) or pass them yourself.
#
# The run sets WIZ_MULTIPROC_KILL=1: it also SIGKILLs a child that holds the exclusive
# lock and checks that the kernel released it. That needs the `flock` utility, so the
# suite's fixed-output case leaves it off.
#
# It also crosses the merged branches on one file: `CompatSeed.wiz` writes a store with
# `Durable.wiz`, `CompatRead.wiz` maps it with `Mmap.wiz` and reads the nodes.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
wiz=${1:-${WIZ:-$root/.lake/build/bin/wiz}}
tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-multiproc.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
cd "$root"
for f in lib/Scry/Quire/Storage.wiz lib/Scry/Quire/Registry.wiz lib/Scry/Quire/Durable.wiz; do
  "$wiz" check "$f"
done
for f in Multiproc MultiprocTest CompatSeed CompatRead; do
  "$wiz" check -I drafts/storage-engine "drafts/storage-engine/$f.wiz"
done
if [ -n "${WIZ_CFLAGS:-}" ]; then
  set -- --cflags "$WIZ_CFLAGS" --ldflags "${WIZ_LDFLAGS:-}"
else
  set --
fi
WIZ_MULTIPROC_KILL=1 "$wiz" run -I drafts/storage-engine -I drafts/optics "$@" \
  drafts/storage-engine/MultiprocTest.wiz
WIZ_COMPAT_STORE="$tmp/compat.db" "$wiz" run -I drafts/storage-engine -I drafts/optics "$@" \
  drafts/storage-engine/CompatSeed.wiz
WIZ_COMPAT_STORE="$tmp/compat.db" "$wiz" run -I drafts/storage-engine -I drafts/optics "$@" \
  drafts/storage-engine/CompatRead.wiz
