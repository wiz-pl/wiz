#!/bin/sh
# A release tarball of the Wiz toolchain (stage 26d): what `tower` installs from GitHub
# Releases, and what you can untar by hand.
#
#   scripts/release-tarball.sh OUT.tar.gz [BINDIR] [REVISION] [CCDIR] [WEBDIR]
#
# BINDIR (default .lake/build/bin) holds the built wiz, grail and tower; the standard
# library, the nvim plugin and the docs come from this checkout. CCDIR is the C toolchain
# made by scripts/bundle-cc.sh (stage 26f; the release job passes it); WEBDIR the web
# infoview built by web/build.sh (11w: `wiz lsp` serves it). The tarball is one
# directory, wiz-ARCH-linux/:
#
#   bin/wiz, bin/grail       wrappers: the binary with -I share/wiz/lib (no other flags:
#                            `wiz build` uses share/wiz/cc when it is there, else `cc` and
#                            the system's GMP; tower rewrites them with your flags)
#   bin/tower                the toolchain manager
#   share/wiz/lib/           the standard library
#   share/wiz/.lake/build/bin/{wiz,grail}   the binaries (grail finds lib/ from there)
#   share/wiz/editors/       the editor plugins, when the checkout has them
#   share/wiz/cc/            the C compiler, glibc 2.27 sysroot, static GMP and GC (CCDIR)
#   share/wiz/web/           the web infoview: page, script, Wasm (WEBDIR)
#   share/wiz/REVISION       the commit
#   share/wiz/LICENSE, COPYING.RUNTIME, NOTICE   Wiz's licence, the runtime exception,
#                            and what third-party code is in the toolchain
#                            (scripts/release-licenses/NOTICE, beside this script)
#   share/wiz/LICENSES/      third-party licence texts: Lean's (lean --print-prefix, when
#                            there is a lean) and scripts/release-licenses/*-LICENSE
#   share/wiz/TOOLCHAIN      a marker: editors find the toolchain a library file belongs to
#
# The archive is reproducible: members are sorted, owned by 0:0, all dated
# SOURCE_DATE_EPOCH (default 0) and given the same modes, and gzip is told not to
# record a name or time. The same tree then gives the same bytes, wherever it was
# built. OUT.tar.gz.sha256 is written next to it.
set -eu
out=$1
bindir=${2:-.lake/build/bin}
rev=${3:-$(git rev-parse HEAD 2>/dev/null || echo unknown)}
ccdir=${4:-}
webdir=${5:-}
arch=$(uname -m)
name=wiz-$arch-linux
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
top=$work/$name
mkdir -p "$top/bin" "$top/share/wiz/.lake/build/bin"
for b in wiz grail; do
  cp "$bindir/$b" "$top/share/wiz/.lake/build/bin/$b"
done
[ -f "$bindir/tower" ] && cp "$bindir/tower" "$top/bin/tower"
cp -R lib "$top/share/wiz/lib"
[ -d editors ] && cp -R editors "$top/share/wiz/editors"
echo "$rev" > "$top/share/wiz/REVISION"
# (the licence files come from this script's directory: the release job runs the
# current scripts on an older commit too)
lic=$(cd "$(dirname "$0")" && pwd)/release-licenses
for f in LICENSE COPYING.RUNTIME; do [ -f "$f" ] && cp "$f" "$top/share/wiz/"; done
cp "$lic/NOTICE" "$top/share/wiz/NOTICE"
mkdir -p "$top/share/wiz/LICENSES"
cp "$lic/"*-LICENSE "$top/share/wiz/LICENSES/"
if lean=$(lean --print-prefix 2>/dev/null) && [ -f "$lean/LICENSE" ]; then
  cp "$lean/LICENSE" "$top/share/wiz/LICENSES/lean4-LICENSE"
  [ -f "$lean/LICENSES" ] && cp "$lean/LICENSES" "$top/share/wiz/LICENSES/lean4-third-party"
else
  echo "release-tarball: no lean on PATH: Lean's licence texts are not in the tarball" >&2
fi
[ -n "$ccdir" ] && cp -R "$ccdir" "$top/share/wiz/cc"
if [ -n "$webdir" ]; then
  mkdir -p "$top/share/wiz/web"
  # (11s) tagged.js is shared by the infoview and the documentation's pages (`wiz doc`,
  # which also copies scroll.*); a web dir from before 11s has none of them
  for f in infoview.html infoview.js wiz-infoview.mjs wiz-infoview.wasm; do cp "$webdir/$f" "$top/share/wiz/web/$f"; done
  for f in tagged.js scroll.js scroll-search.js scroll.css \
           lsp-client.js goals.js playground-lsp.js doc-live.js doc-live.css; do
    if [ -f "$webdir/$f" ]; then cp "$webdir/$f" "$top/share/wiz/web/$f"; fi
  done
fi
echo 'A Wiz toolchain: lib/ is its standard library, .lake/build/bin/ its binaries, ../../bin/ its commands (editors use this file to find them).' > "$top/share/wiz/TOOLCHAIN"
cat > "$top/bin/wiz" <<'EOF'
#!/bin/sh
d=$(cd "$(dirname "$0")/.." && pwd)
exec "$d/share/wiz/.lake/build/bin/wiz" -I "$d/share/wiz/lib" "$@"
EOF
cat > "$top/bin/grail" <<'EOF'
#!/bin/sh
d=$(cd "$(dirname "$0")/.." && pwd)
exec "$d/share/wiz/.lake/build/bin/grail" "$@"
EOF
chmod 755 "$top/bin/wiz" "$top/bin/grail"
case $out in /*) ;; *) out=$(pwd)/$out ;; esac
epoch=${SOURCE_DATE_EPOCH:-0}
tar --sort=name --mtime="@$epoch" --owner=0 --group=0 --numeric-owner \
    --mode='u+rwX,go+rX,go-w' -cf - -C "$work" "$name" | gzip -n > "$out"
(cd "$(dirname "$out")" && sha256sum "$(basename "$out")") > "$out.sha256"
echo "$out"
