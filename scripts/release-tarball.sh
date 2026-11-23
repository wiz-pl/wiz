#!/bin/sh
# A release tarball of the Wiz toolchain (stage 26d): what `tower` installs from GitHub
# Releases, and what you can untar by hand.
#
#   scripts/release-tarball.sh OUT.tar.gz [BINDIR] [REVISION] [CCDIR] [WEBDIR] [SRCDIR]
#
# BINDIR (default .lake/build/bin) holds the built wiz, grail and tower; the standard
# library, the nvim plugin and the docs come from the commit REVISION in SRCDIR, not
# from whatever happens to be in the working tree (so an untracked file cannot change a
# release). SRCDIR defaults to the current directory. CCDIR is the C toolchain
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
#   share/wiz/web/           the web infoview: page, script, Wasm (WEBDIR), and the Wasm
#                            backend's JS host (`wiz run --target wasm` finds it there)
#   share/wiz/REVISION       the commit
#   share/wiz/LICENSE, COPYING.RUNTIME, NOTICE   Wiz's licence, the runtime exception,
#                            and what third-party code is in the toolchain
#                            (scripts/release-licenses/NOTICE, beside this script)
#   share/wiz/LICENSES/      third-party licence texts: Lean's (lean --print-prefix, when
#                            there is a lean) and scripts/release-licenses/*-LICENSE
#   share/wiz/TOOLCHAIN      a marker: editors find the toolchain a library file belongs to
#
# The archive is reproducible: members are sorted, owned by 0:0, all dated the
# commit's time and given the same modes, and gzip is told not to record a name or
# time. The same commit and the same build outputs then give the same bytes, wherever
# they were built: the epoch is derived from REVISION, so an ambient SOURCE_DATE_EPOCH
# (or a re-run of an old commit months later) cannot change the archive. Pass
# RELEASE_SOURCE_DATE_EPOCH to override the epoch deliberately. OUT.tar.gz.sha256 is
# written next to it.
set -eu
out=$1
bindir=${2:-.lake/build/bin}
rev=${3:-$(git rev-parse HEAD 2>/dev/null || echo unknown)}
ccdir=${4:-}
webdir=${5:-}
srcdir=${6:-.}
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
# The inputs are the commit, not the working tree: `git ls-tree`/`git archive` cannot
# see an untracked file, a local edit or another branch's leftovers. SRCDIR is the
# checkout the commit lives in (the release job passes the workspace; the script may
# itself sit in a `.release-tools` sparse checkout).
gitc() { git -C "$srcdir" "$@"; }
have_git=no
if gitc rev-parse --git-dir >/dev/null 2>&1 &&
   gitc cat-file -e "$rev^{commit}" 2>/dev/null; then
  have_git=yes
fi
# `lib/` is the standard library alone: Scry is a package (`scry/`, separate-repos.md
# P0.1) and is not shipped in the toolchain tarball.
if [ "$have_git" = yes ] && gitc cat-file -e "$rev:lib" 2>/dev/null; then
  gitc archive --format=tar "$rev" -- lib | tar -xf - -C "$top/share/wiz"
else
  echo "release-tarball: warning: $rev is not a commit in $srcdir; copying the working tree" >&2
  cp -R "$srcdir/lib" "$top/share/wiz/lib"
fi
# (F12) the Wasm backend's JS host: `wiz run --target wasm` looks for it beside lib/
mkdir -p "$top/share/wiz/web"
if [ "$have_git" = yes ] && gitc cat-file -e "$rev:web/wasm-host.mjs" 2>/dev/null; then
  gitc show "$rev:web/wasm-host.mjs" > "$top/share/wiz/web/wasm-host.mjs"
elif [ -f "$srcdir/web/wasm-host.mjs" ]; then
  cp "$srcdir/web/wasm-host.mjs" "$top/share/wiz/web/wasm-host.mjs"
fi
if [ "$have_git" = yes ] && gitc cat-file -e "$rev:editors" 2>/dev/null; then
  gitc archive --format=tar "$rev" -- editors | tar -xf - -C "$top/share/wiz"
elif [ -d "$srcdir/editors" ]; then
  cp -R "$srcdir/editors" "$top/share/wiz/editors"
fi
echo "$rev" > "$top/share/wiz/REVISION"
# Licences come from REVISION too (the release job's `.release-tools` is checked out
# at the same commit); a non-git call falls back to this script's directory.
lic=$(cd "$(dirname "$0")" && pwd)/release-licenses
copy_rev() { # path-in-repo, destination
  if [ "$have_git" = yes ] && gitc cat-file -e "$rev:$1" 2>/dev/null; then
    gitc show "$rev:$1" > "$2"
  elif [ -f "$srcdir/$1" ]; then
    cp "$srcdir/$1" "$2"
  fi
}
mkdir -p "$top/share/wiz/LICENSES"
for f in LICENSE COPYING.RUNTIME; do copy_rev "$f" "$top/share/wiz/$f"; done
copy_rev scripts/release-licenses/NOTICE "$top/share/wiz/NOTICE"
if [ ! -f "$top/share/wiz/NOTICE" ] && [ -f "$lic/NOTICE" ]; then
  cp "$lic/NOTICE" "$top/share/wiz/NOTICE"
fi
if [ "$have_git" = yes ]; then
  for f in $(gitc ls-tree --name-only "$rev" -- scripts/release-licenses/ |
               sed 's|.*/||' | grep -- '-LICENSE$' || true); do
    gitc show "$rev:scripts/release-licenses/$f" > "$top/share/wiz/LICENSES/$f"
  done
else
  cp "$lic/"*-LICENSE "$top/share/wiz/LICENSES/"
fi
if lean=$(lean --print-prefix 2>/dev/null) && [ -f "$lean/LICENSE" ]; then
  cp "$lean/LICENSE" "$top/share/wiz/LICENSES/lean4-LICENSE"
  [ -f "$lean/LICENSES" ] && cp "$lean/LICENSES" "$top/share/wiz/LICENSES/lean4-third-party"
else
  echo "release-tarball: no lean on PATH: Lean's licence texts are not in the tarball" >&2
fi
[ -n "$ccdir" ] && cp -R "$ccdir" "$top/share/wiz/cc"
if [ -n "$webdir" ]; then
  mkdir -p "$top/share/wiz/web"
  # (11s) the documentation's scripts (`wiz doc` copies scroll.* and the runtimes); the
  # infoview and the live panel share the goals/hover runtimes (Wiz) and the mount
  # contract (framework/), and the standalone infoview has its own module.
  for f in infoview.html infoview.js wiz-infoview.mjs wiz-infoview.wasm \
           wiz-infoview-ui.mjs wiz-docs-ui.mjs wiz-doc-live-ui.mjs; do
    if [ -f "$webdir/$f" ]; then cp "$webdir/$f" "$top/share/wiz/web/$f"; fi
  done
  for f in scroll.js scroll-search.js scroll.css highlight.css lsp-client.js playground-lsp.js \
           widgets.js widgets.css hover.js squiggles.js completions.js overlays.css \
           doc-live.js doc-live.css; do
    if [ -f "$webdir/$f" ]; then cp "$webdir/$f" "$top/share/wiz/web/$f"; fi
  done
  mkdir -p "$top/share/wiz/web/framework"
  for f in mount.js driver.js runtime.js editor-text.js; do
    if [ -f "$webdir/framework/$f" ]; then cp "$webdir/framework/$f" "$top/share/wiz/web/framework/$f"; fi
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
# The epoch is a property of the commit (its author time is not used: `%ct` is the
# committer time, which a rebase/cherry-pick can change; for a tag it is the commit
# that was tagged). An ambient SOURCE_DATE_EPOCH is deliberately ignored so that the
# same commit always gives the same archive; RELEASE_SOURCE_DATE_EPOCH overrides it.
if [ -n "${RELEASE_SOURCE_DATE_EPOCH:-}" ]; then
  epoch=$RELEASE_SOURCE_DATE_EPOCH
elif [ "$have_git" = yes ]; then
  epoch=$(gitc log -1 --format=%ct "$rev")
else
  epoch=${SOURCE_DATE_EPOCH:-0}
fi
case $epoch in ''|*[!0-9]*) echo "release-tarball: epoch '$epoch' is not an integer" >&2; exit 2 ;; esac
tar --sort=name --mtime="@$epoch" --owner=0 --group=0 --numeric-owner \
    --mode='u+rwX,go+rX,go-w' -cf - -C "$work" "$name" | gzip -n > "$out"
(cd "$(dirname "$out")" && sha256sum "$(basename "$out")") > "$out.sha256"
echo "$out"
