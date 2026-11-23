#!/bin/sh
# Does a release tarball run on a machine with only glibc?
#
#   scripts/test-release-portability.sh TARBALL [--glibc DIR] [--interp PATH] [--max-glibc VER]
#   scripts/test-release-portability.sh --dir DIR [--glibc DIR] [--interp PATH] [--max-glibc VER]
#
# TARBALL is `wiz-<arch>-linux.tar.gz` (what scripts/release-tarball.sh writes; its
# `.sha256` is checked when present). `--dir` tests an extracted tree instead.
#
# What is checked:
#
#   * no member contains `/nix/store` (the release-tarball scan's `--strict` rule);
#   * every ELF command (`bin/tower`, and the unwrapped
#     `share/wiz/.lake/build/bin/*`) names only glibc libraries in NEEDED, plus the
#     bundled `libstdc++.so.6`/`libgcc_s.so.1` when `lib/` carries them; a bundled
#     C++ runtime requires an `$ORIGIN`-relative RUNPATH, and a bare RUNPATH is a
#     failure;
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
max_glibc=
while [ $# -gt 0 ]; do
  case $1 in
    --glibc) shift; glibc=${1:?--glibc needs a directory} ;;
    --interp) shift; interp=${1:?--interp needs a path} ;;
    --max-glibc) shift; max_glibc=${1:?--max-glibc needs a version} ;;
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

bundled=no
if [ -f "$root/lib/libstdc++.so.6" ] || [ -f "$root/lib/libgcc_s.so.1" ]; then
  [ -f "$root/lib/libstdc++.so.6" ] && [ -f "$root/lib/libgcc_s.so.1" ] ||
    fail "lib/ must carry both libstdc++.so.6 and libgcc_s.so.1"
  bundled=yes
fi

n=0
for f in bin/tower share/wiz/.lake/build/bin/wiz share/wiz/.lake/build/bin/grail; do
  file=$root/$f
  [ -f "$file" ] || continue
  if [ "$(head -c 4 "$file" | od -An -tx1 | tr -d ' \n')" != 7f454c46 ]; then
    fail "$f is not an ELF command"
  fi
  n=$((n + 1))
  # NEEDED must be glibc only, or the bundled C++ runtime from lib/. A static
  # archive of GMP/libuv/OpenSSL/libstdc++ keeps their code; a shared one names it.
  needs_cxx=no
  needed=$(readelf -d "$file" | sed -n 's/.*(NEEDED).*\[\(.*\)\]/\1/p')
  for lib in $needed; do
    case $lib in
      libstdc++.so.6|libgcc_s.so.1)
        [ "$bundled" = yes ] || fail "$f needs $lib but lib/ does not provide it"
        needs_cxx=yes ;;
      *)
        case " $allowed " in
          *" $lib "*) ;;
          *) fail "$f needs $lib (not glibc)" ;;
        esac ;;
    esac
  done
  rp=$(readelf -d "$file" |
    sed -n 's/.*(RUNPATH).*\[\(.*\)\]/\1/p; s/.*(RPATH).*\[\(.*\)\]/\1/p')
  if [ -n "$rp" ]; then
    case $rp in
      *'$ORIGIN'*) ;;
      *) fail "$f has RUNPATH '$rp' (it must be \$ORIGIN-relative)" ;;
    esac
  fi
  if [ "$needs_cxx" = yes ] && [ -z "$rp" ]; then
    fail "$f needs the bundled C++ runtime but has no \$ORIGIN RUNPATH"
  fi
  got=$(readelf -l "$file" | sed -n 's/.*Requesting program interpreter: \(.*\)]/\1/p')
  [ "$got" = "$expected_interp" ] || \
    fail "$f interpreter is '$got', expected '$expected_interp'"
  glibc_max=$(readelf --version-info "$file" 2>/dev/null |
    grep -o 'GLIBC_[0-9.]*' | sort -Vu | tail -1)
  if [ -n "$max_glibc" ] && [ -n "$glibc_max" ]; then
    glibc_ver=${glibc_max#GLIBC_}
    highest=$(printf '%s\n%s\n' "$glibc_ver" "$max_glibc" | sort -V | tail -1)
    [ "$highest" = "$max_glibc" ] ||
      fail "$f requires $glibc_max, above --max-glibc $max_glibc"
  fi
  echo "ok: $f: $(printf '%s' "$needed" | tr '\n' ' '), interpreter $got, glibc $glibc_max, $(du -h "$file" | cut -f1)"
done
[ "$n" -ge 3 ] || fail "found only $n ELF commands"

# The bundled runtime must not raise the floor above the declared maximum either.
if [ "$bundled" = yes ] && [ -n "$max_glibc" ]; then
  for lib in "$root/lib/libstdc++.so.6" "$root/lib/libgcc_s.so.1"; do
    [ -f "$lib" ] || continue
    lib_max=$(readelf --version-info "$lib" 2>/dev/null |
      grep -o 'GLIBC_[0-9.]*' | sort -Vu | tail -1)
    [ -n "$lib_max" ] || continue
    lib_ver=${lib_max#GLIBC_}
    highest=$(printf '%s\n%s\n' "$lib_ver" "$max_glibc" | sort -V | tail -1)
    [ "$highest" = "$max_glibc" ] ||
      fail "$lib requires $lib_max, above --max-glibc $max_glibc"
  done
fi

# --- run them with only glibc --------------------------------------------------------
if [ -n "$glibc" ]; then
  [ -x "$glibc/lib/$loader" ] || fail "$glibc/lib/$loader is missing"
  run=$work/run
  mkdir -p "$run/home"
  # Run the whole extracted tree: the bundled C++ runtime is found through an
  # $ORIGIN RUNPATH, so copying a single binary would break the relative path.
  cp -a "$root" "$run/root"
  for f in share/wiz/.lake/build/bin/wiz share/wiz/.lake/build/bin/grail bin/tower; do
    [ -f "$run/root/$f" ] || continue
    patchelf --set-interpreter "$glibc/lib/$loader" "$run/root/$f"
  done
  # The copies' interpreter is now glibc from the store. Nothing else is on the PATH
  # that the program could load a library from; lib/ is reached by the RUNPATH. Run
  # the unwrapped commands directly: bin/wiz is a shell wrapper and needs dirname,
  # which a minimal clean room does not provide.
  env -i HOME=$run/home PATH=/usr/bin:/bin \
    "$run/root/share/wiz/.lake/build/bin/wiz" --version > "$run/wiz.version"
  env -i HOME=$run/home PATH=/usr/bin:/bin \
    "$run/root/share/wiz/.lake/build/bin/grail" --version > "$run/grail.version"
  env -i HOME=$run/home PATH=/usr/bin:/bin "$run/root/bin/tower" --version > "$run/tower.version"
  cat > "$run/check.wiz" <<'EOF'
import Prelude

def main : Nat := 6 * 7
EOF
  env -i HOME=$run/home PATH=/usr/bin:/bin \
    "$run/root/share/wiz/.lake/build/bin/wiz" \
    -I "$run/root/share/wiz/lib" check "$run/check.wiz" > "$run/check.out" 2>&1 || {
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
