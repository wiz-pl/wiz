#!/bin/sh
# The install smoke test of a release (docs/release.md, "Before tagging"): tower installs
# a release tarball as the toolchain of a tag, the way a user does with
# scripts/tower-init.sh, and the toolchain checks, runs and builds programs and a grail
# package with nothing but its own bundle. Nothing is pushed or published.
#
#   scripts/test-release-install.sh [--online] TARBALL [TAG] [REPO]
#
# TARBALL is a wiz-ARCH-linux.tar.gz (release.yml's dist/, or a snapshot's asset); TAG
# (default v0.1.0) is the tag it is installed as; REPO (default wiz-pl/wiz) the GitHub
# repository whose URLs the tarball, tower-init.sh and the release workflow must agree on.
#
# The tag is simulated in a scratch directory: a git repository with an annotated TAG,
# and beside it a release directory laid out as GitHub's (releases/download/TAG/…).
# tower's `git` and `releases` settings point at them; tower-init.sh runs with its `repo`
# pointing at them too. The test then checks:
#
#   * the URLs: tower's defaults and tower-init.sh name https://github.com/REPO, so a
#     user's `tower default TAG` downloads https://github.com/REPO/releases/download/TAG/
#     wiz-ARCH-linux.tar.gz, which is where release.yml's "Publish (a tag)" puts it;
#   * the tarball: NOTICE (with the copyright line), LICENSE, COPYING.RUNTIME, the
#     bundled C compiler and CaDiCaL (which gives an LRAT proof), and no z3;
#   * tower: `tower-init.sh TAG` installs it as the default, `--version` of the three
#     tools, `stable` resolves to TAG, a `wiz-toolchain` file selects it;
#   * the toolchain: wiz check/run/build (the bundled cc, GMP and GC) and a grail package
#     with a library and an executable.
#
# --online (after the tag is pushed and released): also fetch the real URLs: the
# tarball and .sha256 of the GitHub release TAG, and tower-init.sh at TAG.
set -eu
online=no
[ "${1:-}" = --online ] && { online=yes; shift; }
[ $# -ge 1 ] || { sed -n '2,30p' "$0"; exit 2; }
tarball=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
tag=${2:-v0.1.0}
repo=${3:-wiz-pl/wiz}
here=$(cd "$(dirname "$0")" && pwd)
arch=$(uname -m)
name=wiz-$arch-linux
gh_url=https://github.com/$repo
fail() { echo "test-release-install: FAIL: $*" >&2; exit 1; }
# a check that doesn't stop the run (the contents and the URLs): all of them are reported
bad() { echo "test-release-install: FAIL: $*" >&2; echo "$*" >> "$s/failures"; }
step() { echo "== $*"; }

s=$(mktemp -d)
trap 'rm -rf "$s"' EXIT
export HOME="$s/home" XDG_CACHE_HOME="$s/home/.cache"
mkdir -p "$HOME"
# (the toolchain's shims go first on PATH below; that `wiz build` needs no system cc or
# GMP is release.yml's container test)

step "the tarball's contents"
mkdir -p "$s/x"
tar -xzf "$tarball" -C "$s/x"
t=$s/x/$name
for f in bin/wiz bin/grail bin/tower share/wiz/.lake/build/bin/wiz share/wiz/.lake/build/bin/grail \
         share/wiz/lib share/wiz/REVISION share/wiz/TOOLCHAIN \
         share/wiz/LICENSE share/wiz/COPYING.RUNTIME share/wiz/NOTICE share/wiz/LICENSES \
         share/wiz/cc/bin/cc share/wiz/cc/bin/clang share/wiz/cc/bin/ld.lld share/wiz/cc/bin/cadical; do
  [ -e "$t/$f" ] || bad "no $f in the tarball"
done
grep -qF 'Copyright (C) 2026 Reuben Steenekamp' "$t/share/wiz/NOTICE" || bad "NOTICE: no copyright line"
grep -qF "$gh_url" "$t/share/wiz/NOTICE" || bad "NOTICE: the source is not at $gh_url"
if find "$t" -name 'z3*' | grep -q .; then bad "z3 is in the bundle (it should not be)"; fi
printf 'p cnf 1 2\n1 0\n-1 0\n' > "$s/t.cnf"
st=0; "$t/share/wiz/cc/bin/cadical" -q --lrat --no-binary "$s/t.cnf" "$s/t.lrat" >/dev/null || st=$?
[ "$st" = 20 ] && [ -s "$s/t.lrat" ] || bad "the bundled cadical gave no LRAT proof (exit $st)"
rev=$(cat "$t/share/wiz/REVISION")

step "the URLs agree on $gh_url"
"$t/bin/tower" --home "$s/fresh" settings > "$s/defaults"
grep -qx "git $gh_url" "$s/defaults" || bad "tower's default git is not $gh_url: $(grep '^git ' "$s/defaults")"
grep -qx "releases $gh_url/releases/download" "$s/defaults" || bad "tower's default releases: $(grep '^releases ' "$s/defaults")"
grep -qx "flake github:$repo" "$s/defaults" || bad "tower's default flake: $(grep '^flake ' "$s/defaults")"
grep -qx "repo=$gh_url" "$here/tower-init.sh" || bad "tower-init.sh: repo is not $gh_url"
# release.yml publishes dist/* (release-tarball.sh's name) to the release named the tag.
# In a checkout `here` is <root>/scripts; release.yml runs a sparse copy at
# <root>/.release-tools/scripts, so the workflow is one or two levels up.
workflow=
for d in "$here/.." "$here/../.."; do
  if [ -f "$d/.github/workflows/release.yml" ]; then
    workflow=$d/.github/workflows/release.yml
    break
  fi
done
[ -n "$workflow" ] || fail "release.yml not found from $here"
grep -q 'gh release create "${GITHUB_REF_NAME}" dist/\*' "$workflow" ||
  fail "release.yml: the tag's release is not named after the tag, with dist/*"
echo "a user's tower downloads $gh_url/releases/download/$tag/$name.tar.gz"

step "a simulated tag $tag (local repository and release directory)"
g=$s/wiz
git init -q "$g"
git -C "$g" -c user.name=t -c user.email=t@t commit -q --allow-empty -m "the release commit ($rev)"
git -C "$g" -c user.name=t -c user.email=t@t tag -a "$tag" -m "Wiz $tag"
git -C "$g" tag nightly # tower-init.sh's default channel looks for it; unused for a tag
mkdir -p "$g/releases/download/$tag"
cp "$tarball" "$g/releases/download/$tag/$name.tar.gz"
(cd "$g/releases/download/$tag" && sha256sum "$name.tar.gz" > "$name.tar.gz.sha256")

step "tower-init.sh $tag"
tower0="$t/bin/tower"
$tower0 set git "file://$g"
$tower0 set releases "file://$g/releases/download"
$tower0 set source release
sed "s|^repo=.*|repo=file://$g|" "$here/tower-init.sh" > "$s/tower-init.sh"
sh "$s/tower-init.sh" "$tag"
PATH=$HOME/.tower/bin:$PATH
export PATH

step "tower, wiz and grail from the toolchain $tag"
command -v tower wiz grail
tower --version
wiz --version | tee "$s/v"
grep -qF "($rev)" "$s/v" || bad "wiz --version does not name the tarball's commit $rev"
grail --version | tee "$s/v"
grep -qF "grail " "$s/v" || bad "grail --version"
tower show | tee "$s/show"
grep -qF "$tag" "$s/show" || fail "tower show: the default is not $tag"
tower default stable
tower show | tee "$s/show"
tower toolchain list | tee "$s/list"
grep -qF "$tag" "$s/list" || fail "stable did not resolve to $tag"

step "wiz check, run, build (the bundled C toolchain)"
mkdir -p "$s/hello/src"
cd "$s/hello"
echo "$tag" > wiz-toolchain
tower show | grep -qF "$tag" || fail "the wiz-toolchain file does not select $tag"
cat > Main.wiz <<'EOF'
import IO
def main : IO Unit := IO.println "hello from Wiz"
EOF
wiz check Main.wiz
[ "$(wiz run Main.wiz)" = "hello from Wiz" ] || fail "wiz run"
wiz build Main.wiz -o hello
[ "$(./hello)" = "hello from Wiz" ] || fail "wiz build"

step "a grail package (a library and an executable)"
cat > src/Greet.wiz <<'EOF'
import Prelude
def greeting : String := "hello from grail"
EOF
cat > App.wiz <<'EOF'
import IO
import Greet
def main : IO Unit := IO.println greeting
EOF
cat > grail.wiz <<'EOF'
import Grail
def package : Package := Package.new "hello"
  |> Package.lib "greet" "src"
  |> Package.exe "app" "App.wiz"
EOF
grail build
[ "$(grail run app)" = "hello from grail" ] || fail "grail run app"

if [ $online = yes ]; then
  step "online: the published $tag"
  u=$gh_url/releases/download/$tag/$name.tar.gz
  curl -sSfL -o "$s/pub.tar.gz" "$u" || fail "no $u"
  curl -sSfL -o "$s/pub.sha256" "$u.sha256" || fail "no $u.sha256"
  (cd "$s" && sed 's/ .*/  pub.tar.gz/' pub.sha256 | sha256sum -c --quiet -) || fail "$u: checksum mismatch"
  curl -sSfL -o "$s/init.sh" "https://raw.githubusercontent.com/$repo/$tag/scripts/tower-init.sh" || fail "no tower-init.sh at $tag"
  grep -qx "repo=$gh_url" "$s/init.sh" || fail "tower-init.sh at $tag: repo is not $gh_url"
fi
if [ -s "$s/failures" ]; then
  echo "test-release-install: the install works, but $(wc -l < "$s/failures") check(s) failed:" >&2
  sed 's/^/  /' "$s/failures" >&2
  exit 1
fi
echo "test-release-install: ok ($tag, $rev)"
