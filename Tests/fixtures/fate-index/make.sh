#!/bin/sh
# Rebuild the fixture archives and their hashes. Deterministic: the same sources give
# the same bytes (fixed mtime, owners, sorted members, gzip -n), so this is safe to run.
set -eu
cd "$(dirname "$0")"
mkdir -p packages
for src in sources/*/; do
  name=${src#sources/}
  name=${name%/}
  tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
    -C sources -cf - "$name" | gzip -n > "packages/$name.tar.gz"
done

sha() { sha256sum "packages/$1-$2.tar.gz" | cut -d' ' -f1; }

sed -i "s/@STD_0_1_0_SHA@/$(sha std 0.1.0)/" index/std.sexpr
sed -i "s/@TEXT_1_0_0_SHA@/$(sha text 1.0.0)/" index/text.sexpr
sed -i "s/@TEXT_1_1_0_SHA@/$(sha text 1.1.0)/" index/text.sexpr
sed -i "s/@GREET_1_0_0_SHA@/$(sha greet 1.0.0)/" index/greet.sexpr
sed -i "s/@GREET_1_2_0_SHA@/$(sha greet 1.2.0)/" index/greet.sexpr
sed -i "s/@GREET_2_0_0_SHA@/$(sha greet 2.0.0)/" index/greet.sexpr
