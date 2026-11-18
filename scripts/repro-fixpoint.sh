#!/usr/bin/env bash
# Is the bootstrap fixpoint reproducible? Build it twice under different conditions and
# compare every artifact byte for byte (docs/bootstrap-chain.md, "Reproducibility").
#
# Each build is scripts/fixpoint.sh --keep in its own copy of this checkout (the tracked
# files of the working tree, so uncommitted edits count). The two copies differ in:
#
#   directory      $BASE/a/wiz  vs  $BASE/b-a-longer-directory-name/src/wiz
#   TMPDIR, HOME   separate directories of different lengths
#   locale, TZ     LC_ALL=C, TZ=UTC  vs  LC_ALL=C.UTF-8, TZ=Asia/Kathmandu
#   umask          022  vs  077
#   SOURCE_DATE_EPOCH  unset  vs  1234567890
#   parallelism    GC_MARKERS=1 LEAN_NUM_THREADS=1 MAKEFLAGS=-j1  vs  the collector's and
#                  Lean's defaults, MAKEFLAGS=-j8, on two CPUs only (taskset, when the
#                  job may use at least two)
#   environment    both start from `env -i`; B also carries unrelated variables
#
# Not varied here: the user (needs root; a Nix sandbox build runs as nixbld and is the
# check for that, see --compare) and the machine (run this on two machines and use
# --compare on the kept outputs).
#
#   usage (from the repository root, with the toolchain environment of `nix develop` or
#   wiz-env.sh):
#     scripts/repro-fixpoint.sh [--stages N] [--base DIR] [--keep] [--rc]
#     scripts/repro-fixpoint.sh --compare DIR_A DIR_B
#
#   --stages N   fixpoint stages per build (default 2: the Lean-built stage 1, self1.c,
#                the stage-2 executable and self2.c); 3 adds stage3 and self3.c
#   --base DIR   where the two copies go (default: a new directory under $TMPDIR)
#   --keep       keep the copies (their .lake/fixpoint holds the artifacts)
#   --rc         pass --rc to fixpoint.sh (reference-counted stages)
#   --compare A B  only compare two artifact directories that already exist (e.g. a
#                kept .lake/fixpoint and a Nix build's output); files present in both
#                are compared, by name
#
# The fixpoint needs about 7 GiB (6.3 GiB peak) and the two builds run one after the other:
#   heavy --mem 7G timeout 6000 bash scripts/repro-fixpoint.sh
#
# Output: one line per artifact (sha256 of each side, SAME or DIFFERENT), and for the
# first differing artifact the first differing byte or line, the ELF sections that
# differ, and which of the varied values (paths, TMPDIR, HOME, user, epoch) occur in it.
# Exit 0 when everything compared is identical, 1 when something differs or a build
# failed, 2 on a usage error.
set -euo pipefail

usage() { awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"; }
die() { echo "repro-fixpoint: $*" >&2; exit 2; }

stages=2
base=
keep=0
rc=()
compare=()
while [ $# -gt 0 ]; do
  case "$1" in
    --stages) [ $# -ge 2 ] || die "--stages needs a number"; stages=$2; shift 2 ;;
    --base) [ $# -ge 2 ] || die "--base needs a directory"; base=$2; shift 2 ;;
    --keep) keep=1; shift ;;
    --rc) rc=(--rc); shift ;;
    --compare) [ $# -ge 3 ] || die "--compare needs two directories"; compare=("$2" "$3"); shift 3 ;;
    -h|--help) usage; exit 0 ;;
    *) die "unknown argument: $1 (try --help)" ;;
  esac
done
case "$stages" in ''|*[!0-9]*) die "--stages must be a whole number" ;; esac

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

# ---------------------------------------------------------------------------------
# Comparison

# The values that differ between the two builds, as NAME=VALUE lines, for the "why".
markers=()

explain() { # explain FILE_A FILE_B NAME
  local a=$1 b=$2 name=$3
  local -; set +e +o pipefail  # diagnostics only: a pipeline that finds nothing is fine
  echo
  echo "first difference: $name"
  if [ "$(head -c 4 "$a" | od -An -c | tr -d ' ')" = '177ELF' ]; then
    cmp "$a" "$b" | head -1 || true
    # Which sections differ (the section table itself may differ in sizes).
    local ta tb
    ta=$(mktemp -d); tb=$(mktemp -d)
    local secs
    secs=$(readelf -SW "$a" | sed -n 's/^ *\[ *[0-9]*\] \([^ ]\{1,\}\).*/\1/p' | grep -v '^NULL$' | sort -u)
    local diffsecs=()
    for s in $secs; do
      objcopy -O binary --only-section="$s" "$a" "$ta/x" 2>/dev/null || continue
      objcopy -O binary --only-section="$s" "$b" "$tb/x" 2>/dev/null || { diffsecs+=("$s(only in A)"); continue; }
      cmp -s "$ta/x" "$tb/x" || diffsecs+=("$s")
    done
    echo "  differing sections: ${diffsecs[*]:-(none: the headers or symbol table differ)}"
    if ! cmp -s <(readelf -sW "$a" 2>/dev/null) <(readelf -sW "$b" 2>/dev/null); then
      echo "  symbol tables differ; first lines:"
      diff <(readelf -sW "$a") <(readelf -sW "$b") | head -6 | sed 's/^/    /'
    fi
    if ! cmp -s <(readelf -dW "$a" 2>/dev/null) <(readelf -dW "$b" 2>/dev/null); then
      echo "  dynamic sections differ (RUNPATH/NEEDED):"
      diff <(readelf -dW "$a") <(readelf -dW "$b") | grep -E 'RUNPATH|RPATH|NEEDED' | head -4 | sed 's/^/    /'
    fi
    echo "  strings only in one side (first 8):"
    diff <(strings -a -n 6 "$a" | sort -u) <(strings -a -n 6 "$b" | sort -u) | grep '^[<>]' | head -8 | sed 's/^/    /'
    rm -rf "$ta" "$tb"
  else
    local line
    line=$(cmp "$a" "$b" 2>&1 | head -1 || true)
    echo "  $line"
    diff "$a" "$b" | head -8 | sed 's/^/    /' || true
  fi
  # Does a varied value occur in either side?
  local m k v hit
  for m in "${markers[@]}"; do
    k=${m%%=*}; v=${m#*=}
    [ -n "$v" ] || continue
    hit=
    grep -qaF -- "$v" "$a" && hit="A"
    grep -qaF -- "$v" "$b" && hit="${hit:+$hit,}B"
    [ -z "$hit" ] || echo "  contains $k ($v): $hit"
  done
}

compare_dirs() { # compare_dirs DIR_A DIR_B -> 0 identical, 1 differ
  local da=$1 db=$2 f name first= status=0 n=0
  printf '%-14s %-64s %-64s %s\n' artifact "sha256 (A)" "sha256 (B)" result
  # in chain order, so the first difference is the earliest one
  local chain=(compiler.wiz self.wiz compiler self1.c) k
  for k in $(seq 2 32); do chain+=("stage$k" "self$k.c"); done
  chain+=(wizc.c wizc)
  for f in "${chain[@]}"; do
    [ -f "$da/$f" ] && [ -f "$db/$f" ] || continue
    n=$((n + 1))
    local ha hb r
    ha=$(sha256sum "$da/$f" | cut -d' ' -f1)
    hb=$(sha256sum "$db/$f" | cut -d' ' -f1)
    if [ "$ha" = "$hb" ]; then r=SAME; else r=DIFFERENT; status=1; [ -n "$first" ] || first=$f; fi
    printf '%-14s %-64s %-64s %s\n' "$f" "$ha" "$hb" "$r"
  done
  [ "$n" -gt 0 ] || { echo "nothing to compare: no common artifact in $da and $db" >&2; return 1; }
  if [ -n "$first" ]; then
    explain "$da/$first" "$db/$first" "$first"
    echo
    echo "NOT REPRODUCIBLE: $n artifacts compared, some differ (the first is $first)."
  else
    echo
    echo "REPRODUCIBLE: $n artifacts compared, all identical."
  fi
  return "$status"
}

if [ ${#compare[@]} -eq 2 ]; then
  [ -d "${compare[0]}" ] && [ -d "${compare[1]}" ] || die "--compare: not directories: ${compare[*]}"
  compare_dirs "${compare[0]}" "${compare[1]}"
  exit $?
fi

# ---------------------------------------------------------------------------------
# Two builds

: "${WIZ_GC_CFLAGS?needs the toolchain environment (nix develop, or wiz-env.sh)}"
command -v lake >/dev/null || die "lake is not on PATH"
lake_cache=${LAKE_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/lake}
elan_home=${ELAN_HOME:-$HOME/.elan}

if [ -z "$base" ]; then
  base=$(mktemp -d "${TMPDIR:-/tmp}/wiz-repro-fixpoint.XXXXXX")
else
  mkdir -p "$base"; base=$(cd "$base" && pwd)
fi
[ "$keep" = 1 ] || trap 'chmod -R u+w "$base" 2>/dev/null; rm -rf "$base"' EXIT

ra=$base/a/wiz
rb=$base/b-a-longer-directory-name/src/wiz
for r in "$ra" "$rb"; do
  mkdir -p "$r"
  # the tracked files as they are in the working tree (deleted files are skipped)
  (cd "$root" && git ls-files -z | while IFS= read -r -d '' f; do [ -e "$f" ] && printf '%s\0' "$f"; done \
     | xargs -0 cp --parents -P -t "$r")
done
mkdir -p "$base/tmp-a" "$base/home-a" "$base/tmp-b-longer/x" "$base/home-b-longer"
cpu_b=()
if command -v taskset >/dev/null; then
  allowed=$(taskset -pc $$ 2>/dev/null | sed 's/.*: //')
  first2=$(python3 -c '
import sys
cpus=[]
for part in sys.argv[1].split(","):
    if "-" in part:
        a,b=part.split("-"); cpus+=range(int(a),int(b)+1)
    elif part: cpus.append(int(part))
print(",".join(map(str,cpus[:2])) if len(cpus)>=2 else "")' "$allowed")
  [ -z "$first2" ] || cpu_b=(taskset -c "$first2")
fi

markers=("root A=$ra" "root B=$rb" "TMPDIR A=$base/tmp-a" "TMPDIR B=$base/tmp-b-longer/x"
         "HOME A=$base/home-a" "HOME B=$base/home-b-longer" "user=$(id -un)" "epoch=1234567890")

common=(PATH="$PATH" LAKE_CACHE_DIR="$lake_cache" ELAN_HOME="$elan_home"
        WIZ_CFLAGS="${WIZ_CFLAGS:-}" WIZ_LDFLAGS="${WIZ_LDFLAGS:-}" WIZ_LLC="${WIZ_LLC:-}"
        WIZ_GC_CFLAGS="$WIZ_GC_CFLAGS" WIZ_GC_LDFLAGS="${WIZ_GC_LDFLAGS:-}")
# (NIX_* variables are the cc wrapper's inputs; keep them so both builds use one compiler setup)
while IFS='=' read -r k _; do
  case "$k" in NIX_CC*|NIX_CFLAGS_COMPILE*|NIX_LDFLAGS*|NIX_BINTOOLS*|NIX_HARDENING_ENABLE|NIX_ENFORCE*) common+=("$k=${!k}") ;; esac
done < <(env)

build() { # build LABEL ROOT -- ENV... -- PREFIX...
  local label=$1 r=$2; shift 2
  echo "== build $label in $r ($(date +%T))"
  local log=$base/build-$label.log
  if (cd "$r" && "$@" bash scripts/fixpoint.sh --keep --stages "$stages" "${rc[@]}" .lake/fixpoint) > "$log" 2>&1; then
    grep -E '^stage [0-9]|^total|FIXPOINT' "$log" | sed 's/^/   /'
  else
    echo "   build $label FAILED; the last lines of $log:"
    tail -15 "$log" | sed 's/^/   /'
    return 1
  fi
}

echo "repro-fixpoint: $stages stages, two builds under $base"
echo "   A: $ra  TMPDIR=$base/tmp-a  LC_ALL=C TZ=UTC umask 022  GC_MARKERS=1 LEAN_NUM_THREADS=1"
echo "   B: $rb  TMPDIR=$base/tmp-b-longer/x  LC_ALL=C.UTF-8 TZ=Asia/Kathmandu umask 077  SOURCE_DATE_EPOCH=1234567890  ${cpu_b[*]:-(no taskset)}"
fail=0
build A "$ra" sh -c 'umask 022; exec "$@"' sh env -i "${common[@]}" \
  HOME="$base/home-a" TMPDIR="$base/tmp-a" LC_ALL=C TZ=UTC \
  GC_MARKERS=1 LEAN_NUM_THREADS=1 MAKEFLAGS=-j1 || fail=1
build B "$rb" sh -c 'umask 077; exec "$@"' sh "${cpu_b[@]}" env -i "${common[@]}" \
  HOME="$base/home-b-longer" TMPDIR="$base/tmp-b-longer/x" LC_ALL=C.UTF-8 TZ=Asia/Kathmandu \
  SOURCE_DATE_EPOCH=1234567890 MAKEFLAGS=-j8 WIZ_REPRO_NOISE="an unrelated variable" \
  USER=nobody-in-particular LOGNAME=nobody-in-particular || fail=1

echo
compare_dirs "$ra/.lake/fixpoint" "$rb/.lake/fixpoint" || fail=1
[ "$keep" = 0 ] || echo "kept: $base"
exit "$fail"
