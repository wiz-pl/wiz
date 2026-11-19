#!/bin/sh
# Check and run the multi-process store contract (compiled: the file and lock natives are
# `wiz run` code). The default binary is the worktree's own build, so the runtime and
# lib/Sys.wiz used are the ones in this tree. If `cc` or GMP is not on the path, run this
# from the nix dev shell, or put the two flags in WIZ_RUN_FLAGS:
#   WIZ_RUN_FLAGS='--cflags "-I…/gmp/include" --ldflags "-L…/gmp/lib"' drafts/storage-engine/test-multiproc.sh
#
# The run sets WIZ_MULTIPROC_KILL=1: it also SIGKILLs a child that holds the exclusive
# lock and checks that the kernel released it. That needs the `flock` utility, so the
# suite's fixed-output case leaves it off.
#
# It also crosses the two merged branches on one file: `CompatSeed.wiz` writes a store
# with `Durable.wiz`, `CompatRead.wiz` maps it with `Mmap.wiz` and reads the nodes.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
wiz=${1:-${WIZ:-$root/.lake/build/bin/wiz}}
run_flags=${WIZ_RUN_FLAGS:-}
tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-multiproc.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
cd "$root"
for f in Storage Durable Multiproc MultiprocTest CompatSeed CompatRead; do
  "$wiz" check -I drafts/storage-engine "drafts/storage-engine/$f.wiz"
done
# shellcheck disable=SC2086
WIZ_MULTIPROC_KILL=1 "$wiz" run -I drafts/storage-engine $run_flags \
  drafts/storage-engine/MultiprocTest.wiz
# shellcheck disable=SC2086
WIZ_COMPAT_STORE="$tmp/compat.db" "$wiz" run -I drafts/storage-engine $run_flags \
  drafts/storage-engine/CompatSeed.wiz
# shellcheck disable=SC2086
WIZ_COMPAT_STORE="$tmp/compat.db" "$wiz" run -I drafts/storage-engine $run_flags \
  drafts/storage-engine/CompatRead.wiz
