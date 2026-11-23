#!/bin/sh
# Does a release tarball run on a machine with only glibc?
#
#   scripts/test-release-portability.sh TARBALL [--glibc DIR] [--interp PATH]
#   scripts/test-release-portability.sh --dir DIR [--glibc DIR] [--interp PATH]
#
# TARBALL is `wiz-<arch>-linux.tar.gz` (what scripts/release-tarball.sh writes; its
# `.sha256` is checked when present). `--dir` tests an extracted tree instead.
#
# What is checked:
#
#   * no member contains `/nix/store` (the release-tarball scan's `--strict` rule);
#   * every ELF command (`bin/wiz`, `bin/grail`, `bin/tower`, and the unwrapped
#     `share/wiz/.lake/build/bin/*`) names only glibc libraries in NEEDED — no GMP,
#     libuv, OpenSSL, libstdc++ or libgcc — and has no RUNPATH/RPATH;
#   * its interpreter is the conventional one (`/lib64/ld-linux-x86-64.so.2`, or
#     `/lib/ld-linux-aarch64.so.1`), not a build path;
#   * the commands run under `env -i` with only a `PATH` and a writable `HOME`.
#
# `--glibc DIR` points at a glibc output (a Nix store path). The shipped binaries name
# the conventional interpreter, which a Nix build sandbox does not have; for that case
# the script copies each ELF to a scratch directory and points the *copy's* interpreter
# at `DIR/lib/ld-linux-*`, leaving the artifact untouched. That is the clean-room run:
# the loader is glibc and nothing else from the build environment is visible.
#
# Exit status: 0 pass, 1 a check failed, 2 usage/input error.
set -eu

usage() {
  sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'
  exit 2
}

tarball=
dir=
glibc=
interp=
while [ $# -gt 0 ]; do
  case $1 in
    --glibc) shift; glibc=${1:?--glibc needs a directory} ;;
    --interp) shift; interp=${1:?--interp needs a path} ;;
    --dir) shift; dir=${1:?--dir needs a directory} ;;
    -h|--help) usage ;;
    -*) echo "test-release-portability: unknown option $1" >&2; usage ;;
    *) tarball=$1 ;;
  esac
  shift
done
if [ -z "$tarball" ] && [ -z "$dir" ]; then usage; fi
if [ -n "$tarball" ] && [ -n "$dir" ]; then usage; fi

fail() {
  echo "test-release-portability: $*" >&2
  exit 1
}

work=$(mktemp -d "${TMPDIR:-/tmp}/wiz-release-portability.XXXXXX")
trap 'rm -rf "$work"' EXIT

if [ -n "$tarball" ]; then
  [ -f "$tarball" ] || { echo "test-release-portability: no $tarball" >&2; exit 2; }
  if [ -f "$tarball.sha256" ]; then
    want=$(cut -d' ' -f1 "$tarball.sha256")
    got=$(sha256sum "$tarball" | cut -d' ' -f1)
    [ "$want" = "$got" ] || fail "$tarball.sha256 does not name the tarball's digest"
  fi
  mkdir -p "$work/unpacked"
  tar -xzf "$tarball" -C "$work/unpacked"
  top=$(find "$work/unpacked" -mindepth 1 -maxdepth 1 -type d | head -1)
  [ -n "$top" ] || fail "the tarball has no top directory"
  root=$top
else
  root=$(cd "$dir" && pwd)
fi

name=$(basename "$root")
case $name in
  wiz-*-linux) ;;
  *) fail "$root is not a wiz-<arch>-linux tree" ;;
esac

# --- no store paths anywhere ---------------------------------------------------------
if grep -a -r -l '/nix/store' "$root" > "$work/store-hits" 2>/dev/null; then
  echo "test-release-portability: members name /nix/store:" >&2
  sed "s|^$root/||" "$work/store-hits" | head -20 >&2
  fail "a release must not carry build-store references"
fi
echo "ok: no member names /nix/store"

# --- the commands are there ----------------------------------------------------------
for f in bin/wiz bin/grail bin/tower share/wiz/.lake/build/bin/wiz \
         share/wiz/.lake/build/bin/grail share/wiz/web/wasm-host.mjs; do
  [ -e "$root/$f" ] || fail "missing $f"
done
[ -f "$root/share/wiz/lib/Prelude.wiz" ] || fail "missing share/wiz/lib/Prelude.wiz"
# bin/wiz and bin/grail are the tarball's shell wrappers; the ELF commands they exec
# are the ones the linkage checks apply to.
grep -q 'exec .*share/wiz/.lake/build/bin/wiz' "$root/bin/wiz" ||
  fail "bin/wiz is not the expected wrapper"
grep -q 'exec .*share/wiz/.lake/build/bin/grail' "$root/bin/grail" ||
  fail "bin/grail is not the expected wrapper"
echo "ok: the command, library and Wasm-host layout is present"

arch=x86_64
case $name in
  wiz-aarch64-linux) arch=aarch64 ;;
esac
case $arch in
  x86_64) expected_interp=/lib64/ld-linux-x86-64.so.2; loader=ld-linux-x86-64.so.2 ;;
  aarch64) expected_interp=/lib/ld-linux-aarch64.so.1; loader=ld-linux-aarch64.so.1 ;;
esac
[ -z "$interp" ] || expected_interp=$interp

allowed='libc.so.6 libm.so.6 libdl.so.2 libpthread.so.0 librt.so.1 ld-linux-x86-64.so.2 ld-linux-aarch64.so.1'

n=0
for f in bin/tower share/wiz/.lake/build/bin/wiz share/wiz/.lake/build/bin/grail; do
  file=$root/$f
  [ -f "$file" ] || continue
  if [ "$(head -c 4 "$file" | od -An -tx1 | tr -d ' \n')" != 7f454c46 ]; then
    fail "$f is not an ELF command"
  fi
  n=$((n + 1))
  # NEEDED must be glibc only: a static archive of GMP/libuv/OpenSSL/libstdc++ keeps
  # their code, but a shared one would name it here.
  readelf -d "$file" | sed -n 's/.*(NEEDED).*\[\(.*\)\]/\1/p' | while IFS= read -r lib; do
    case " $allowed " in
      *" $lib "*) ;;
      *) echo "test-release-portability: $f needs $lib (not glibc)" >&2; exit 1 ;;
    esac
  done || fail "$f links a non-glibc library"
  if readelf -d "$file" | grep -qE 'RUNPATH|RPATH'; then
    fail "$f has a RUNPATH/RPATH (it must find glibc the normal way)"
  fi
  got=$(readelf -l "$file" | sed -n 's/.*Requesting program interpreter: \(.*\)]/\1/p')
  [ "$got" = "$expected_interp" ] || \
    fail "$f interpreter is '$got', expected '$expected_interp'"
  glibc_max=$(readelf --version-info "$file" 2>/dev/null |
    grep -o 'GLIBC_[0-9.]*' | sort -Vu | tail -1)
  echo "ok: $f: glibc only ($glibc_max), interpreter $got, $(du -h "$file" | cut -f1)"
done
[ "$n" -ge 3 ] || fail "found only $n ELF commands"

# --- run them with only glibc --------------------------------------------------------
if [ -n "$glibc" ]; then
  [ -x "$glibc/lib/$loader" ] || fail "$glibc/lib/$loader is missing"
  run=$work/run
  mkdir -p "$run/home"
  for b in wiz grail tower; do
    cp "$root/share/wiz/.lake/build/bin/$b" "$run/$b" 2>/dev/null ||
      cp "$root/bin/$b" "$run/$b"
    chmod u+w "$run/$b"
    patchelf --set-interpreter "$glibc/lib/$loader" "$run/$b"
  done
  # The copy's interpreter is now glibc from the store. Nothing else is on the PATH
  # that the program could load a library from.
  env -i HOME=$run/home PATH=/usr/bin:/bin "$run/wiz" --version > "$run/wiz.version"
  env -i HOME=$run/home PATH=/usr/bin:/bin "$run/grail" --version > "$run/grail.version"
  env -i HOME=$run/home PATH=/usr/bin:/bin "$run/tower" --version > "$run/tower.version"
  cat > "$run/check.wiz" <<'EOF'
import Prelude

def main : Nat := 6 * 7
EOF
  env -i HOME=$run/home PATH=/usr/bin:/bin "$run/wiz" \
    -I "$root/share/wiz/lib" check "$run/check.wiz" > "$run/check.out" 2>&1 || {
      cat "$run/check.out" >&2
      fail "wiz check failed in the clean environment"
    }
  echo "ok: wiz, grail and tower ran with only $glibc (a clean environment)"
  echo "    $(cat "$run/wiz.version")"
  echo "    $(cat "$run/grail.version")"
  echo "    $(cat "$run/tower.version")"
else
  # The host has the conventional interpreter (a normal Linux, not a Nix sandbox).
  [ -x "$expected_interp" ] || {
    echo "test-release-portability: $expected_interp is absent; pass --glibc DIR" >&2
    exit 2
  }
  env -i HOME=$work PATH=/usr/bin:/bin "$root/bin/wiz" --version > "$work/wiz.version"
  env -i HOME=$work PATH=/usr/bin:/bin "$root/bin/grail" --version > "$work/grail.version"
  env -i HOME=$work PATH=/usr/bin:/bin "$root/bin/tower" --version > "$work/tower.version"
  echo "ok: the wrappers ran under env -i on this machine"
  cat "$work/wiz.version"
fi

echo "test-release-portability: ok ($(du -sh "$root" | cut -f1) extracted)"
