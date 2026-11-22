#!/bin/sh
# The C toolchain a release tarball ships (stage 26f): `share/wiz/cc/` of the tarball, so
# that `wiz build`, `wiz run` and grail need no system compiler, GMP or Boehm GC.
#
#   scripts/bundle-cc.sh OUT [DOWNLOADS]
#
# OUT gets (and is replaced):
#
#   bin/cc            clang with the sysroot below: what `wiz` uses by default
#   bin/llc           the same clang on textual LLVM IR, with llc's arguments (`--llvm`)
#   bin/clang, bin/ld.lld, lib/*.so*   the compiler and linker, from the Lean toolchain
#                     (`lean --print-prefix`, or $LEAN_PREFIX): the same LLVM as Lean's
#   bin/cadical       (stage 28b) the SAT solver `sat_decide` asks for LRAT proofs, also
#                     the Lean toolchain's (Lean ships it for bv_decide; ~1 MB with libc++)
#   lib/clang/N/      compiler-rt (builtins, crtbegin/end) and clang's own headers
#   sysroot/          glibc 2.27 and Linux 4.15 headers and the libraries to link against
#                     (Ubuntu 18.04's libc6, libc6-dev, linux-libc-dev), with static
#                     GMP 6.3.0 and the Boehm GC 8.2.8 built here
#   LICENSES/         the licences of all of the above
#   VERSIONS          what went in
#
# Programs it builds link GMP and the GC statically and need only glibc >= 2.27 (libc,
# libm, libpthread) at run time. DOWNLOADS (default ~/.cache/wiz-bundle-cc) keeps the
# fetched files (the list, with mirrors and sha256s, is scripts/bundle-cc.sources).
# Runs outside Nix (the release job).
set -eu
out=$1
dl=${2:-${HOME:-/tmp}/.cache/wiz-bundle-cc}
lean=${LEAN_PREFIX:-$(lean --print-prefix)}
jobs=$(nproc 2>/dev/null || echo 2)
mkdir -p "$dl"
case $out in /*) ;; *) out=$(pwd)/$out ;; esac
case $dl in /*) ;; *) dl=$(pwd)/$dl ;; esac

# the downloads: scripts/bundle-cc.sources (FILE SHA256 URL…), each URL tried in turn
# with retries, every file checked against its sha256; an Ubuntu pool file is tried on
# several mirrors, and every file last on this repository's release `bundle-inputs`
here=$(cd "$(dirname "$0")" && pwd)
ubuntu_mirrors="http://archive.ubuntu.com/ubuntu/pool/main http://mirrors.kernel.org/ubuntu/pool/main http://mirror.math.princeton.edu/pub/ubuntu/pool/main http://ftp.halifax.rwth-aachen.de/ubuntu/pool/main"
inputs_release=${WIZ_BUNDLE_INPUTS:-https://github.com/wiz-pl/wiz/releases/download/bundle-inputs}
fetch() { # FILE SHA256 URL…
  f=$1 sum=$2; shift 2
  [ -f "$dl/$f" ] && echo "$sum  $dl/$f" | sha256sum -c --quiet - >/dev/null 2>&1 && return 0
  urls=
  for u in "$@"; do
    case $u in
      '$U'/*) for m in $ubuntu_mirrors; do urls="$urls $m${u#'$U'}"; done ;;
      *) urls="$urls $u" ;;
    esac
  done
  for u in $urls "$inputs_release/$f"; do
    rm -f "$dl/$f.part"
    if curl -sSfL --retry 3 --retry-delay 5 --retry-all-errors --connect-timeout 20 --max-time 900 \
         -o "$dl/$f.part" "$u" &&
       echo "$sum  $dl/$f.part" | sha256sum -c --quiet - >/dev/null 2>&1; then
      mv "$dl/$f.part" "$dl/$f"
      return 0
    fi
    echo "bundle-cc: $f: no good copy from $u" >&2
  done
  rm -f "$dl/$f.part"
  echo "bundle-cc: $f: every mirror failed" >&2
  return 1
}
grep -v '^#' "$here/bundle-cc.sources" | while read -r line; do
  [ -n "$line" ] || continue
  # shellcheck disable=SC2086
  fetch $line || exit 1
done

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
rm -rf "$out"
mkdir -p "$out/bin" "$out/lib" "$out/LICENSES"

# the compiler and linker, and the shared libraries they need (from Lean's lib/)
cp -L "$lean/bin/clang" "$lean/bin/ld.lld" "$lean/bin/cadical" "$out/bin/"
need() { readelf -d "$1" | sed -n 's/.*(NEEDED).*\[\(.*\)\]/\1/p'; }
# The Lean toolchain is prebuilt, and a build of it can name its builder's Nix store in
# a library's RUNPATH. Those libraries ship in the bundle, and the release promises no
# store path: strip the rpath, fall back to the build host's copy of the same runtime
# library, and refuse a path that survives both (it would be in the code, not the rpath).
copy_lib() { # soname
  src=$lean/lib/$1
  dst=$out/lib/$1
  [ -e "$dst" ] && return 0
  if ! grep -aq /nix/store "$src"; then
    cp -L "$src" "$dst"
    return 0
  fi
  tmp=$out/lib/.$1.tmp
  cp -L "$src" "$tmp"
  command -v patchelf >/dev/null 2>&1 && patchelf --remove-rpath "$tmp"
  if grep -aq /nix/store "$tmp"; then
    for d in /usr/lib/x86_64-linux-gnu /lib/x86_64-linux-gnu /usr/lib64 /usr/lib; do
      if [ -f "$d/$1" ] && ! grep -aq /nix/store "$d/$1"; then
        cp -L "$d/$1" "$tmp"
        break
      fi
    done
  fi
  if grep -aq /nix/store "$tmp"; then
    echo "bundle-cc: $1 still names /nix/store (patchelf and the host copy did not remove it)" >&2
    rm -f "$tmp"
    return 1
  fi
  mv "$tmp" "$dst"
  echo "bundle-cc: $1: removed the toolchain copy's /nix/store path" >&2
}
todo="$out/bin/clang $out/bin/ld.lld $out/bin/cadical"
while [ -n "$todo" ]; do
  next=
  for b in $todo; do
    for l in $(need "$b"); do
      if [ -e "$lean/lib/$l" ] && [ ! -e "$out/lib/$l" ]; then
        copy_lib "$l" || exit 1
        next="$next $out/lib/$l"
      fi
    done
  done
  todo=$next
done
# the gate: no shipped library may name the builder's store
for f in "$out"/lib/*.so*; do
  [ -f "$f" ] || continue
  if grep -aq /nix/store "$f"; then
    echo "bundle-cc: $f names /nix/store" >&2
    exit 1
  fi
done
ver=$(ls "$lean/lib/clang")
mkdir -p "$out/lib/clang/$ver/include"
cp -R "$lean/lib/clang/$ver/lib" "$out/lib/clang/$ver/"
cp "$lean/include/clang/"*.h "$out/lib/clang/$ver/include/"
cp "$lean/LICENSE" "$out/LICENSES/lean4-LICENSE"
# (a file in current Lean toolchains: the third-party licences, CaDiCaL's among them)
[ -e "$lean/LICENSES" ] && cp -R "$lean/LICENSES" "$out/LICENSES/lean4-LICENSES"

# the sysroot: glibc 2.27 and the kernel headers, only what compiling and linking need.
# 2.27 (Ubuntu 18.04, EOL 2023-05) is a link-time-only compatibility floor for the
# programs built here, not an execution environment (they link the host's glibc
# dynamically); 18.04 is the last distribution that requires it. See the dated note and
# TODO(2026-11-17, wiz-pl maintainers) in scripts/bundle-cc.sources before changing it.
sys=$out/sysroot
mkdir -p "$work/deb" "$sys"
for d in libc6_2.27-3ubuntu1.6_amd64.deb libc6-dev_2.27-3ubuntu1.6_amd64.deb linux-libc-dev_4.15.0-213.224_amd64.deb; do
  rm -rf "$work/deb"/*
  (cd "$work/deb" && ar x "$dl/$d" && tar -xf data.tar.* -C "$sys")
done
mkdir -p "$out/LICENSES/glibc" "$out/LICENSES/linux"
cp "$sys/usr/share/doc/libc6/copyright" "$out/LICENSES/glibc/copyright"
cp "$sys/usr/share/doc/linux-libc-dev/copyright" "$out/LICENSES/linux/copyright"
rm -rf "$sys/etc" "$sys/usr/share" "$sys/usr/bin" "$sys/usr/sbin" "$sys/sbin" "$sys/usr/lib/x86_64-linux-gnu/gconv" \
  "$sys/usr/lib/x86_64-linux-gnu/audit" "$sys/lib/x86_64-linux-gnu/security"
# static libc and friends are not used (programs link libc dynamically)
find "$sys/usr/lib/x86_64-linux-gnu" -name '*.a' ! -name '*_nonshared.a' -delete
# absolute symlinks (libdl.so -> /lib/x86_64-linux-gnu/libdl.so.2) point into the sysroot
find "$sys" -type l | while read -r l; do
  t=$(readlink "$l")
  case $t in /*) ln -sfn "$(realpath -m --relative-to="$(dirname "$l")" "$sys$t")" "$l" ;; esac
done

cat > "$out/bin/cc" <<'EOF'
#!/bin/sh
# Wiz's bundled C compiler (scripts/bundle-cc.sh): clang with glibc 2.27, GMP and the GC
d=$(cd "$(dirname "$0")/.." && pwd)
# a link also gets libm (as needed): `import_c "math.h"` calls it, and with glibc 2.27
# libpthread and libm are libraries of their own
link=yes
for a in "$@"; do
  case $a in -c|-E|-S|-r|-M|-MM) link= ;; esac
done
if [ -n "$link" ]; then
  exec "$d/bin/clang" --sysroot="$d/sysroot" -pthread -Wno-unused-command-line-argument "$@" \
    -Wl,--as-needed -lm -Wl,--no-as-needed
fi
exec "$d/bin/clang" --sysroot="$d/sysroot" -pthread -Wno-unused-command-line-argument "$@"
EOF
cat > "$out/bin/llc" <<'EOF'
#!/bin/sh
# `llc` for Wiz's LLVM backend: the bundled clang compiles the textual IR
# (it understands -O<n>, -filetype=obj|asm, -relocation-model=pic|static, -o FILE, FILE)
d=$(cd "$(dirname "$0")/.." && pwd)
opt=-O2 kind=-c pic=-fPIC o= in=
while [ $# -gt 0 ]; do
  case $1 in
    -O*) opt=$1 ;;
    -filetype=obj) kind=-c ;;
    -filetype=asm) kind=-S ;;
    -relocation-model=pic) pic=-fPIC ;;
    -relocation-model=static) pic=-fno-pic ;;
    -o) o=$2; shift ;;
    -*) echo "llc (wiz bundle): unsupported option $1" >&2; exit 2 ;;
    *) in=$1 ;;
  esac
  shift
done
exec "$d/bin/clang" -Wno-override-module $kind $opt $pic -x ir -o "${o:--}" "$in"
EOF
chmod 755 "$out/bin/cc" "$out/bin/llc"

# GMP and the Boehm GC, static and position-independent, into the sysroot.
# CC is `cc` by name, with $out/bin first on PATH: GMP records the compiler in the
# installed gmp.h (`__GMP_CC`), and an absolute $out/bin/cc there would make that
# header (and so the tarball) depend on the bundle's build directory.
cc=$out/bin/cc
PATH="$out/bin:$PATH"; export PATH
tar -xJf "$dl/gmp-6.3.0.tar.xz" -C "$work"
(cd "$work/gmp-6.3.0" &&
  # --enable-fat: code for every x86-64 CPU, picked at run time (a build tuned to this
  # machine's CPU would fail on older ones)
  ./configure -q --host=x86_64-pc-linux-gnu --enable-fat --enable-static --disable-shared --with-pic \
    --prefix="$sys/usr" CC=cc CFLAGS="-O2 -w" >/dev/null &&
  make -s -j"$jobs" >/dev/null && make -s install >/dev/null)
cp "$work/gmp-6.3.0/COPYING.LESSERv3" "$out/LICENSES/gmp-COPYING.LESSERv3"
cp "$work/gmp-6.3.0/COPYINGv3" "$out/LICENSES/gmp-COPYINGv3"
cp "$work/gmp-6.3.0/COPYINGv2" "$out/LICENSES/gmp-COPYINGv2"
tar -xzf "$dl/gc-8.2.8.tar.gz" -C "$work"
(cd "$work/gc-8.2.8" &&
  ./configure -q --host=x86_64-pc-linux-gnu --enable-static --disable-shared --with-pic --enable-threads=posix \
    --disable-docs --with-libatomic-ops=none --prefix="$sys/usr" CC=cc CFLAGS="-O2 -w" >/dev/null &&
  make -s -j"$jobs" >/dev/null && make -s install >/dev/null)
# its licence is the top of README.QUICK
cp "$work/gc-8.2.8/README.QUICK" "$out/LICENSES/bdwgc-README.QUICK"
rm -rf "$sys/usr/share" "$sys/usr/lib/pkgconfig"
find "$sys/usr/lib" -name '*.la' -delete

cat > "$out/VERSIONS" <<EOF
clang, ld.lld, compiler-rt: from $(basename "$lean") ($("$out/bin/clang" --version | head -1))
cadical: from $(basename "$lean") ($("$out/bin/cadical" --version))
glibc 2.27 (libc6, libc6-dev 2.27-3ubuntu1.6), Linux headers 4.15 (linux-libc-dev 4.15.0-213.224): Ubuntu 18.04, link-time only
GMP 6.3.0 (static, --enable-fat), Boehm GC 8.2.8 (static, threads)
EOF

# it works
cat > "$work/t.c" <<'EOF'
#include <gmp.h>
#include <gc.h>
#include <stdio.h>
int main(void) { mpz_t a; mpz_init_set_ui(a, 1); mpz_mul_2exp(a, a, 100); GC_INIT();
  char *p = GC_MALLOC(16); gmp_printf("%Zd %d\n", a, p != 0); return 0; }
EOF
"$cc" -O2 "$work/t.c" -o "$work/t" -lgmp -lgc
"$work/t"
# and the SAT solver gives LRAT proofs
printf 'p cnf 1 2\n1 0\n-1 0\n' > "$work/t.cnf"
st=0; "$out/bin/cadical" -q --lrat --no-binary "$work/t.cnf" "$work/t.lrat" >/dev/null || st=$?
[ "$st" = 20 ] && [ -s "$work/t.lrat" ] || { echo "bundle-cc: cadical gave no LRAT proof (exit $st)" >&2; exit 1; }
du -sh "$out"
