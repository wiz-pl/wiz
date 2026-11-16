#!/bin/sh
# Generate the static index of this example repository (stage 23m).
#
#   1. sources/NAME-VERSION/ -> packages/NAME-VERSION.tar.gz, deterministically
#   2. entries/NAME.sexpr.in -> index/NAME.sexpr, with @SHA:NAME-VERSION@ filled in
#   3. index/*.sexpr -> index.sexpr, the single-file form grail also reads
#
# Run it after adding or changing a release, then commit the generated files. It touches
# no network and no clock: the archives use `--mtime=@0` and `gzip -n`, so the SHA-256 of
# a release is a function of its sources.
set -eu
cd "$(dirname "$0")"
mkdir -p packages index

for src in sources/*/; do
  rel=${src#sources/}
  rel=${rel%/}
  tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
    -C sources -cf - "$rel" | gzip -n > "packages/$rel.tar.gz"
done

for tmpl in entries/*.sexpr.in; do
  base=${tmpl##*/}
  base=${base%.sexpr.in}
  tmp=$(mktemp)
  cp "$tmpl" "$tmp"
  for src in sources/*/; do
    rel=${src#sources/}
    rel=${rel%/}
    sha=$(sha256sum "packages/$rel.tar.gz" | cut -d' ' -f1)
    sed -i.bak "s|@SHA:$rel@|$sha|g" "$tmp"
  done
  rm -f "$tmp.bak"
  mv "$tmp" "index/$base.sexpr"
done

tmp=$(mktemp)
printf '(index\n' > "$tmp"
for f in index/*.sexpr; do
  # index/snapshot.sexpr is the signed state, not a package: it is not part of the
  # single-file index (grail reads it separately when a signature is required)
  case "$f" in */snapshot.sexpr) continue ;; esac
  sed -e '1s/^(index//' -e '$s/)$//' "$f" >> "$tmp"
done
printf ')\n' >> "$tmp"
mv "$tmp" index.sexpr

echo "generated packages/, index/ and index.sexpr"
