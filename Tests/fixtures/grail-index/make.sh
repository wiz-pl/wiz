#!/bin/sh
# Render the fixture index into OUT: the release archives and the index entries with
# their hashes. Nothing generated is committed; the `grail-deps` tests run this into a
# fresh temporary directory for each case (Tests/Grail.lean, `indexFixture`).
#
#   1. sources/NAME-VERSION/  -> OUT/packages/NAME-VERSION.tar.gz, deterministically
#   2. entries/NAME.sexpr.in  -> OUT/index/NAME.sexpr, each @SHA:NAME-VERSION@ filled in
#   3. registry.sexpr         -> OUT/registry.sexpr
#
# Deterministic: the same sources give the same bytes (sorted members, fixed mtime and
# owners, `gzip -n`, and modes normalised to 644/755, so a read-only copy such as the Nix
# store gives the same archive as a checkout), so the hashes are a function of the
# sources. Needs GNU tar.
#
#   usage: Tests/fixtures/grail-index/make.sh OUT
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=${1:?usage: make.sh OUT}
mkdir -p "$out/packages" "$out/index"
out=$(cd "$out" && pwd)
cd "$here"

for src in sources/*/; do
  rel=${src#sources/}
  rel=${rel%/}
  tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner --mode=u+w,go-w,a+rX \
    -C sources -cf - "$rel" | gzip -n > "$out/packages/$rel.tar.gz"
done

for tmpl in entries/*.sexpr.in; do
  base=${tmpl##*/}
  base=${base%.sexpr.in}
  text=$(cat "$tmpl")
  for src in sources/*/; do
    rel=${src#sources/}
    rel=${rel%/}
    sha=$(sha256sum "$out/packages/$rel.tar.gz" | cut -d' ' -f1)
    text=$(printf '%s\n' "$text" | sed "s|@SHA:$rel@|$sha|g")
  done
  case "$text" in
    *@SHA:*) echo "make.sh: $tmpl names a release with no sources/ directory" >&2; exit 1 ;;
  esac
  printf '%s\n' "$text" > "$out/index/$base.sexpr"
done

cp registry.sexpr "$out/registry.sexpr"
