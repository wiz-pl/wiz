#!/usr/bin/env bash
# The bootstrap fixpoint check.
#
# Stage 1 is the self-hosted compiler built by the Lean `wiz build`; it compiles the
# whole toolchain to C (self1.c). Each later stage compiles the previous stage's C with
# selfhost/rt.c and Boehm GC (to stage2, stage3, ...) and that program compiles the
# toolchain again (self2.c, self3.c, ...). Every stage's C must be byte-identical to
# stage 1's. Three stages are the default: stage 1 = stage 2 shows the C the Lean-built
# compiler emits is reproduced by the compiler that C builds; stage 2 = stage 3 shows
# that reproduction is a fixed point, not one coincident round.
#
#   usage (from the repository root, in `nix develop`):
#     scripts/fixpoint.sh [--rc] [--stages N] [--keep] [--compare-only] [OUTDIR]
#
#   --rc            compile with reference counting (the compiler's flag, stage 21k), so
#                   every stage is a reference-counted compiler that must free every object
#   --stages N      how many C stages to generate and compare (N >= 2; default 3)
#   --keep          keep the artifacts: self*.c, the stage binaries and run/
#   --compare-only  only compare self1.c ... selfN.c already in OUTDIR (with --keep),
#                   without building or compiling; useful to re-check kept artifacts
#   OUTDIR          default .lake/fixpoint
#
# It prints each step's wall time and peak RSS (the self-compile stages need about
# 6 GiB; they have peaked near 5.4 GiB), and each stage's C size and md5 with PASS/FAIL.
# A stage killed by the OOM killer or a memory cgroup (exit 137) fails with a hint.
# Slow: two or more compilations of the whole toolchain (CI runs it on a schedule).
set -euo pipefail

usage() { awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"; }
die() { echo "fixpoint: $*" >&2; exit 2; }

mode=()
stages=3
keep=0
compare_only=0
out=
while [ $# -gt 0 ]; do
  case "$1" in
    --rc) mode=(--rc); shift ;;
    --stages) [ $# -ge 2 ] || die "--stages needs a number"; stages=$2; shift 2 ;;
    --stages=*) stages=${1#--stages=}; shift ;;
    --keep) keep=1; shift ;;
    --compare-only) compare_only=1; shift ;;
    -h|--help) usage; exit 0 ;;
    --) shift; break ;;
    -*) die "unknown option: $1 (try --help)" ;;
    *) [ -z "$out" ] || die "unexpected argument: $1"; out=$1; shift ;;
  esac
done
case "$stages" in ''|*[!0-9]*) die "--stages must be a whole number" ;; esac
[ "$stages" -ge 2 ] || die "--stages must be at least 2 (a fixpoint compares two C files)"

out=${out:-.lake/fixpoint}
mkdir -p "$out"
out=$(cd "$out" && pwd)

if [ "$compare_only" = 0 ]; then
  : "${WIZ_GC_CFLAGS?needs the toolchain environment (nix develop)}"
  mkdir -p "$out/run"
fi

step() { echo "::group::$1" 2>/dev/null; echo "== $1 ($(date +%T))"; }
done_() { echo "::endgroup::"; }
md5_of() { md5sum "$1" | cut -d' ' -f1; }

timings=$out/timings.tsv
labels=()
walls=()
peaks=()
total_peak=0
if [ "$compare_only" = 0 ]; then
  : > "$timings"
  printf 'step\twall_s\tpeak_kib\n' >> "$timings"
fi

# A small sampler: run the command in DIR with its stdout in OUTFILE, and report the wall
# time and the peak resident set of the process tree (a self-compile is one process; `cc`
# and `lake` fan out). Python3 is part of the dev shell and of CI. /proc is Linux-only,
# as is the fixpoint's C toolchain.
measure=$out/.measure.py
if [ "$compare_only" = 0 ]; then
cat > "$measure" <<'PY'
import os, resource, subprocess, sys, time

def snapshot():
    procs = {}
    page = os.sysconf("SC_PAGE_SIZE")
    for name in os.listdir("/proc"):
        if not name.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % name, "rb") as f:
                data = f.read()
        except OSError:
            continue
        r = data.rfind(b")")
        if r < 0:
            continue
        parts = data[r + 2:].split()
        if len(parts) < 22:
            continue
        try:
            procs[int(name)] = (int(parts[1]), int(parts[21]) * (page // 1024))
        except ValueError:
            continue
    return procs

def tree_rss(procs, root):
    total = 0
    for pid, (ppid, rss) in procs.items():
        p = pid
        for _ in range(64):
            if p == root:
                total += rss
                break
            nxt = procs.get(p)
            if nxt is None or p <= 1:
                break
            p = nxt[0]
    return total

cwd, outfile, argv = sys.argv[1], sys.argv[2], sys.argv[3:]
start = time.monotonic()
try:
    with open(outfile, "wb") as out:
        p = subprocess.Popen(argv, cwd=cwd, stdout=out)
        peak = 0
        while p.poll() is None:
            peak = max(peak, tree_rss(snapshot(), p.pid))
            time.sleep(0.1)
        rc = p.returncode
except OSError as e:
    print("fixpoint: cannot run %r: %s" % (argv, e), file=sys.stderr)
    sys.exit(125)
wall = time.monotonic() - start
# ru_maxrss is a floor for short commands, which the sampling can miss.
peak = max(peak, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
print("%.3f %d" % (wall, peak))
sys.exit(128 - rc if rc < 0 else rc)
PY
fi

# run_step LABEL DIR OUTFILE COMMAND... -- run COMMAND in DIR, its stdout to OUTFILE,
# recording wall time and the tree's peak RSS.
run_step() {
  local label=$1 dir=$2 outfile=$3
  shift 3
  local metrics rc secs kb
  set +e
  metrics=$(python3 "$measure" "$dir" "$outfile" "$@")
  rc=$?
  set -e
  read -r secs kb <<< "$metrics" || { secs=0; kb=0; }
  secs=${secs:-0}; kb=${kb:-0}
  labels+=("$label"); walls+=("$secs"); peaks+=("$kb")
  [ "$kb" -le "$total_peak" ] 2>/dev/null || total_peak=$kb
  printf '   %-54s %8ss %8s MiB\n' "$label" "$secs" "$((kb / 1024))"
  printf '%s\t%s\t%s\n' "$label" "$secs" "$kb" >> "$timings"
  if [ "$rc" -ne 0 ]; then
    echo
    echo "FAILED: '$label' exited $rc after ${secs}s (peak $((kb / 1024)) MiB)." >&2
    if [ "$rc" -eq 137 ] || [ "$rc" -eq 9 ]; then
      echo "It was killed (SIGKILL), which is how the OOM killer and a memory cgroup end a run." >&2
      echo "The fixpoint needs about 6 GiB: the self-compiles peak near 5.4 GiB (stage 2 has reached 5.5 GiB)." >&2
      echo "Reserve it (e.g. 'heavy --mem 6G scripts/fixpoint.sh') and give the runner >= 6 GiB free." >&2
    fi
    echo "Artifacts are in $out (run/ and the files already produced)." >&2
    exit 1
  fi
}

if [ "$compare_only" = 0 ]; then
  t_start=$(date +%s)

  step "generate compiler.wiz and self.wiz"
  run_step "build the Lean wiz and the test driver" "$PWD" /dev/null lake build wiz Tests.Elab
  run_step "generate compiler.wiz and self.wiz" "$PWD" /dev/null env OUT="$out" lake lean scripts/GenSelfhost.lean
  cp "$out/self.wiz" "$out/run/input.wiz"
  done_

  step "stage 1: the Lean wiz build of the self-hosted compiler"
  # shellcheck disable=SC2086
  run_step "stage 1: the Lean wiz build of the compiler" "$PWD" /dev/null \
    .lake/build/bin/wiz build "$out/compiler.wiz" -o "$out/compiler" \
    --cflags "$WIZ_CFLAGS" --ldflags "$WIZ_LDFLAGS"
  done_

  step "stage 1 compiles the toolchain (self1.c)"
  run_step "stage 1 compiles the toolchain (self1.c)" "$out/run" "$out/self1.c" \
    "$out/compiler" "${mode[@]}"
  done_

  k=2
  while [ "$k" -le "$stages" ]; do
    prev=$((k - 1))
    step "stage $k: cc self$prev.c with selfhost/rt.c"
    # shellcheck disable=SC2086
    run_step "cc self$prev.c -> stage$k" "$PWD" /dev/null \
      cc -O2 -w -I"$PWD/selfhost" $WIZ_GC_CFLAGS "$out/self$prev.c" -o "$out/stage$k" $WIZ_GC_LDFLAGS
    done_

    step "stage $k compiles the toolchain (self$k.c)"
    run_step "stage $k compiles the toolchain (self$k.c)" "$out/run" "$out/self$k.c" \
      "$out/stage$k" "${mode[@]}"
    done_
    k=$((k + 1))
  done

  total_wall=$(( $(date +%s) - t_start ))
else
  total_wall=0
  [ "$stages" -ge 2 ] || die "--compare-only needs --stages >= 2"
fi

# Compare every stage with stage 1: equality is transitive, so this compares all of them.
echo
echo "stage C files (self1.c is the reference):"
fail=0
for k in $(seq 1 "$stages"); do
  f=$out/self$k.c
  if [ ! -f "$f" ]; then
    printf 'stage %d  %-16s  MISSING\n' "$k" "self$k.c"
    fail=1
    continue
  fi
  bytes=$(stat -c %s "$f")
  md5=$(md5_of "$f")
  if [ "$k" -eq 1 ]; then
    result="(reference)"
  elif cmp -s "$out/self1.c" "$f"; then
    result=PASS
  else
    result=FAIL
    fail=1
  fi
  printf 'stage %d  %-16s  %10d bytes  md5 %s  %s\n' "$k" "self$k.c" "$bytes" "$md5" "$result"
done

if [ "$compare_only" = 0 ]; then
  echo
  printf 'total   %8ss   peak %s MiB\n' "$total_wall" "$((total_peak / 1024))"
  echo "timings: $timings"
fi

if [ "$fail" -ne 0 ]; then
  echo
  echo "NO FIXPOINT: a stage's C differs from stage 1's."
  for k in $(seq 2 "$stages"); do
    f=$out/self$k.c
    [ -f "$f" ] || continue
    cmp -s "$out/self1.c" "$f" && continue
    echo "first difference, self1.c vs self$k.c:"
    diff "$out/self1.c" "$f" | head -20 || true
    break
  done
  echo "Artifacts are in $out (the C files are kept on failure)." >&2
  rm -f "$measure"
  exit 1
fi

first_bytes=$(stat -c %s "$out/self1.c")
first_md5=$(md5_of "$out/self1.c")
rm -f "$measure"

if [ "$compare_only" = 0 ] && [ "$keep" = 0 ]; then
  rm -rf "$out/run" "$out"/self*.c "$out"/stage* "$out/compiler" "$out/compiler.wiz" "$out/self.wiz"
  echo "artifacts removed (--keep keeps self*.c, the stage binaries and run/)"
elif [ "$keep" = 1 ]; then
  echo "artifacts kept in $out"
fi

if [ "$stages" -eq 2 ]; then
  echo "FIXPOINT (stage-1 C = stage-2 C, $first_bytes bytes, md5 $first_md5)"
else
  echo "FIXPOINT (stages 1-$stages agree: $first_bytes bytes, md5 $first_md5)"
fi
