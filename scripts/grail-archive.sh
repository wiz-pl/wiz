#!/usr/bin/env bash
# The deterministic archive for a registry release (docs/stages/23-grail.md, 23m):
# one top directory NAME-VERSION/, every entry stamped with the commit's time, and
# `gzip -n` so neither the filename nor the timestamp is in the gzip header. The bytes
# are therefore a function of the commit, and the SHA-256 in the index can be re-derived.
#
#   usage (from the package's git checkout): scripts/grail-archive.sh NAME VERSION [COMMIT] [OUT]
#
# COMMIT defaults to HEAD and OUT to NAME-VERSION.tar.gz. A plain `git archive | gzip`
# is not enough: without -n the gzip header carries the current time.
set -euo pipefail
name=${1:?usage: grail-archive.sh NAME VERSION [COMMIT] [OUT]}
version=${2:?usage: grail-archive.sh NAME VERSION [COMMIT] [OUT]}
commit=${3:-HEAD}
out=${4:-"$name-$version.tar.gz"}
git archive --format=tar --prefix="$name-$version/" "$commit" | gzip -n > "$out"
sha256sum "$out"
