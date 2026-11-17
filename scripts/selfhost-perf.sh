#!/usr/bin/env bash
# Measure the self-hosted compiler on its own frontend: wall time and peak RSS of
# `check` and `build`, then a phase table (load, parse, elaborate, emit, write) and a
# function table from a `-finstrument-functions` build.
#
#   usage (from the repository root, in the dev shell):
#     heavy --mem 7G scripts/selfhost-perf.sh [--reps N] [--input FILE]
#                                            [--out DIR] [--no-build] [--no-profile]
#
#   --reps N        plain runs per command (default 3; medians are reported)
#   --input FILE    the file the self-hosted compiler reads (default: the checker's own
#                   sources, Lex+Parse+Kernel+CParse+CGlue+Frontend+Tables+Check, the
#                   `Selfhost.checkerSource` unit; `self.wiz` is the whole toolchain)
#   --out DIR       build and profile scratch (default .lake/selfhost-perf)
#   --no-build      reuse the two binaries already in DIR (compare a rebuilt tree only
#                   after deleting DIR, or a stale binary is measured)
#   --no-profile    plain wall/RSS only (no instrumentation build, no tables)
#
# It builds the Lean host (`lake build wiz Tests.Elab`), generates
# `$OUT/compiler.wiz` with `scripts/GenSelfhost.lean`, and builds it twice with
# `-O1`: `$OUT/selfhost` (measured) and `$OUT/selfhost-prof`
# (`-fno-inline -finstrument-functions`, only for shares and call counts; the
# instrumentation lives in scripts/selfhost-perf-prof.c and no checked-in Wiz source
# is modified).  The generated C of the plain build is kept as `$OUT/Frontend.c`:
# after a change, its bytes and md5 are the same "did the output move" check the
# fixpoint gives, and the profiled build's C must match it too.
#
# Output: one line per plain sample (so a noisy run is visible), the medians and peak
# RSS, then the phase and function tables.  The phase table scales the instrumented
# **inclusive** times of the driver's phase functions to the plain median, so the
# instrumentation's cost cancels; the function table is shares of exclusive time and
# exact call counts, not absolute seconds.
#
# Depends on: the dev-shell C toolchain (`cc`; if it is not on PATH the script takes
# `lake env`'s PATH), GNU `lake` + the checked-in Lean toolchain, python3, and Linux
# /proc for peak RSS.  `WIZ_CFLAGS`/`WIZ_LDFLAGS` come from the dev shell; without
# them the program still builds (no GMP include/lib flags) only if nothing needs them.
# It uses ~7 GiB peak for the -O1 build of the compiler, hence the `heavy --mem 7G`.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

reps=3
input=
out=$ROOT/.lake/selfhost-perf
build=1
profile=1
while [ $# -gt 0 ]; do
  case "$1" in
    --reps) [ $# -ge 2 ] || { echo "selfhost-perf: --reps needs a number" >&2; exit 2; }
            reps=$2; shift 2 ;;
    --reps=*) reps=${1#--reps=}; shift ;;
    --input) [ $# -ge 2 ] || { echo "selfhost-perf: --input needs a file" >&2; exit 2; }
             input=$2; shift 2 ;;
    --input=*) input=${1#--input=}; shift ;;
    --out) [ $# -ge 2 ] || { echo "selfhost-perf: --out needs a directory" >&2; exit 2; }
           out=$2; shift 2 ;;
    --out=*) out=${1#--out=}; shift ;;
    --no-build) build=0; shift ;;
    --no-profile) profile=0; shift ;;
    -h|--help) sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "selfhost-perf: unknown argument: $1 (try --help)" >&2; exit 2 ;;
  esac
done
case "$reps" in ''|*[!0-9]*) echo "selfhost-perf: --reps must be a whole number" >&2; exit 2 ;; esac
[ "$reps" -ge 1 ] || { echo "selfhost-perf: --reps must be at least 1" >&2; exit 2; }

# `cc` lives in the Lean toolchain's bin directory as a wrapper over the dev-shell
# GCC; `lake env` knows that PATH even when the caller did not source the dev shell.
if ! command -v cc >/dev/null 2>&1; then
  PATH=$(lake env printenv PATH 2>/dev/null | head -1):$PATH
  export PATH
fi
command -v cc >/dev/null 2>&1 || {
  echo "selfhost-perf: no cc on PATH (run this in the dev shell: nix develop)" >&2
  exit 2
}

mkdir -p "$out"
out=$(cd "$out" && pwd)

# The default input: the self-hosted checker's own sources (the frontend it is), as
# `Selfhost.checkerSource` concatenates them, so the compiler reads ~20k lines of its
# own Wiz.  `--input` overrides it.
if [ -z "$input" ]; then
  input=$out/selfhost-all.wiz
  python3 - "$input" selfhost/Lex.wiz selfhost/Parse.wiz selfhost/Kernel.wiz \
    selfhost/CParse.wiz selfhost/CGlue.wiz selfhost/Frontend.wiz selfhost/Tables.wiz \
    selfhost/Check.wiz <<'PY'
import sys
out, files = sys.argv[1], sys.argv[2:]
parts = ["import IO", "import Std"]
for f in files:
    parts.append("\n".join(l for l in open(f).read().split("\n") if not l.startswith("import")))
open(out, "w").write("\n".join(parts))
PY
fi
[ -f "$input" ] || { echo "selfhost-perf: no such input: $input" >&2; exit 2; }
cf=${WIZ_CFLAGS:-}
ld=${WIZ_LDFLAGS:-}

if [ "$build" = 1 ]; then
  echo "selfhost-perf: building the Lean host and the two -O1 self-hosted compilers"
  lake build wiz Tests.Elab
  OUT="$out" lake lean scripts/GenSelfhost.lean
  # `-O2` is on the generator's own command line; a later -O1 wins.
  ./.lake/build/bin/wiz build "$out/compiler.wiz" -o "$out/selfhost" \
    --cflags "$cf -O1" --ldflags "$ld"
  if [ "$profile" = 1 ]; then
    cc -O2 -c scripts/selfhost-perf-prof.c -o "$out/prof.o"
    ./.lake/build/bin/wiz build "$out/compiler.wiz" -o "$out/selfhost-prof" \
      --cflags "$cf -O1 -finstrument-functions -fno-pie" \
      --ldflags "$ld -no-pie $out/prof.o"
  fi
fi
[ -x "$out/selfhost" ] || { echo "selfhost-perf: no $out/selfhost (drop --no-build)" >&2; exit 2; }

args=(--binary "$out/selfhost" --input "$input" --reps "$reps" --out "$out")
if [ "$profile" = 1 ]; then
  [ -x "$out/selfhost-prof" ] || {
    echo "selfhost-perf: no $out/selfhost-prof (drop --no-build --no-profile)" >&2; exit 2; }
  args+=(--profile-binary "$out/selfhost-prof")
else
  args+=(--no-profile)
fi
python3 scripts/selfhost-perf.py "${args[@]}"
