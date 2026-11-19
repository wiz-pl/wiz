#!/bin/sh
# Install tower and a default Wiz toolchain from a release tarball (stage 26d):
#
#   curl -sSfL -o tower-init.sh https://raw.githubusercontent.com/wiz-pl/wiz/master/scripts/tower-init.sh
#   echo '<sha256 of this file>  tower-init.sh' | sha256sum -c -
#   sh tower-init.sh [CHANNEL]
#
# The hash pins the installer: docs/install.md carries the current one, and a changed
# script fails the check until the docs are updated (fail closed). Release notes pin
# the same script at the tag (`.../vX.Y.Z/scripts/tower-init.sh`).
#
# CHANNEL is nightly (the default) or a release tag. tower goes to ~/.tower/bin with the
# shims; add that directory to PATH. Needs curl, tar and sha256sum (and git for nightly,
# as tower does). The tarball brings its own C compiler and GMP (26f): `wiz build` needs
# nothing else. docs/install.md has the details.
set -eu
channel=${1:-nightly}
arch=$(uname -m)
repo=https://github.com/wiz-pl/wiz
rel=$channel
# nightly: the snapshot the tag nightly points at (26g), which is complete when the tag
# moves; the release `nightly` itself is replaced in place and may be briefly missing
if [ "$channel" = nightly ] && command -v git >/dev/null 2>&1; then
  sha=$(git ls-remote "$repo" refs/tags/nightly | cut -f1)
  [ -z "$sha" ] || rel=snapshot-$sha
fi
url=$repo/releases/download/$rel/wiz-$arch-linux.tar.gz
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
echo "tower-init: downloading $url"
curl -sSfL -o "$tmp/wiz.tar.gz" "$url"
# The checksum is mandatory: a missing or mismatched one aborts before the tarball is
# unpacked or executed.
if ! curl -sSfL -o "$tmp/wiz.tar.gz.sha256" "$url.sha256"; then
  echo "tower-init: no checksum at $url.sha256; refusing to use the tarball" >&2
  exit 1
fi
(cd "$tmp" && sed 's/ .*/  wiz.tar.gz/' wiz.tar.gz.sha256 | sha256sum -c --quiet -) || {
  echo "tower-init: checksum mismatch for $url; refusing to use the tarball" >&2
  exit 1
}
tar -xzf "$tmp/wiz.tar.gz" -C "$tmp"
"$tmp/wiz-$arch-linux/bin/tower" self install
"$HOME/.tower/bin/tower" default "$channel"
echo "tower-init: done; add ~/.tower/bin to PATH (export PATH=\"\$HOME/.tower/bin:\$PATH\")"
