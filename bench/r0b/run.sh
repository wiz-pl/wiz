#!/usr/bin/env bash
# R0(b) of the runtime convergence: what does masking object pointers with
# WIZ_OBJ(v) = v & ~0xE cost the Lean toolchain's generated programs?
#
# The converged core (stage R3) has to mask the selfhost runtime's offset bits in
# wiz_inc/wiz_dec/wiz_free/wiz_immortal/wiz_mark_mt. For Lean values the mask is a no-op
# (their pointers are the header), so the only question is time on the hot path. This
# builds each benchmark with the Lean `wiz` once per (target, variant), where a variant
# is a rewrite of the runtime text that `wiz build` hands to cc (patch-runtime.py, via a
# cc wrapper), and times every variant against `base` in interleaved A/B pairs.
#
#   usage (repository root, toolchain environment; one heavy job):
#     heavy --mem 4G timeout 5400 bash bench/r0b/run.sh [--reps N] [--out DIR] [--targets "c llvm"]
#
# Benchmarks:
#   stdlib-bench      bench/stdlib-bench.wiz, its 18 modes at their default sizes, through
#                     scripts/stdlib-bench.py --baseline-bin (paired ratios, checksums equal)
#   closed-table      examples/closed-table-bench.wiz 3000000 (CAF tables: inc/dec on
#                     immortal objects)
#   rc-churn          bench/r0b/rc-churn.wiz 400 (list/tree alloc, map, fold and free)
# Variants (patch-runtime.py): base; mask (the plan's 5 sites); mask-all (every header cast
#   in the runtime, an upper bound); check (mask, trapping on a set bit: run once, not
#   timed, to show that no Lean pointer has bits 1-3 set, without which the mask is wrong).
# Targets: c (runtime pasted into the program: inc/dec can inline) and llvm (runtime is a
#   separate object: inc/dec are calls).
#
# Output: DIR/summary.tsv (target, benchmark, variant, median paired ratio, min, max) and
# the JSON per run. Decision rule proposed in the plan (D-R3): accept the mask when every
# `mask` ratio's median is within 1.02 (noise) on both targets.
set -euo pipefail

reps=9
out=.lake/r0b
targets="c llvm"
while [ $# -gt 0 ]; do
  case "$1" in
    --reps) reps=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    --targets) targets=$2; shift 2 ;;
    -h|--help) awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"; exit 0 ;;
    *) echo "r0b: unknown argument $1" >&2; exit 2 ;;
  esac
done
: "${WIZ_CFLAGS?needs the toolchain environment (nix develop)}"
root=$(pwd)
here=$root/bench/r0b
mkdir -p "$out"; out=$(cd "$out" && pwd)
real_cc=$(command -v "${WIZ_CC:-cc}")
variants="base mask mask-all check"

echo "== lake build wiz ($(date +%T))"
lake build -j 2 wiz >/dev/null
wiz=$root/.lake/build/bin/wiz

# one cc wrapper per variant (distinct paths, so no build cache key is shared between
# variants): patch every .c argument that holds the runtime, log the site count, run cc
for v in $variants; do
  w=$out/cc-$v
  cat > "$w" <<EOF
#!/usr/bin/env bash
set -euo pipefail
for a in "\$@"; do
  case "\$a" in
    *.c) [ -f "\$a" ] && echo "\$a \$(python3 '$here/patch-runtime.py' '$v' "\$a")" >> '$out/patch-$v.log' ;;
  esac
done
exec '$real_cc' "\$@"
EOF
  chmod +x "$w"
done

benches=("stdlib-bench bench/stdlib-bench.wiz" "closed-table examples/closed-table-bench.wiz" "rc-churn bench/r0b/rc-churn.wiz")
for t in $targets; do
  for v in $variants; do
    : > "$out/patch-$v.log"
    for b in "${benches[@]}"; do
      set -- $b
      exe=$out/$t/$v/$1
      mkdir -p "$(dirname "$exe")"
      echo "== build $t/$v/$1 ($(date +%T))"
      before=$(wc -l < "$out/patch-$v.log")
      "$wiz" build "$2" -o "$exe" --target "$t" --cc "$out/cc-$v" --cache "$out/cache" \
        --cflags "${WIZ_CFLAGS:-}" --ldflags "${WIZ_LDFLAGS:-}" ${WIZ_LLC:+--llc "$WIZ_LLC"}
      # every non-base build must have patched the runtime once (C: the program; LLVM:
      # wiz_runtime.c), or its timing would be the base's
      patched=$(tail -n +"$((before + 1))" "$out/patch-$v.log" | awk '$2 > 0' | wc -l)
      if [ "$v" != base ] && [ "$patched" -lt 1 ]; then
        echo "r0b: $t/$v/$1: no runtime was patched (see $out/patch-$v.log)" >&2; exit 1
      fi
    done
  done
done

printf 'target\tbench\tvariant\tratio_median\tratio_min\tratio_max\n' > "$out/summary.tsv"
for t in $targets; do
  echo "== check: $t ($(date +%T))"
  # the trapping build, once per mode/program: a trap (SIGILL) fails the run
  python3 scripts/stdlib-bench.py --bin "$out/$t/check/stdlib-bench" --baseline-bin "$out/$t/base/stdlib-bench" \
    --reps 1 --warmup 0 --json "$out/$t-check-stdlib.json" --quiet
  python3 "$here/ab.py" --reps 1 --json "$out/$t-check-closed.json" closed-table "$out/$t/base/closed-table" "$out/$t/check/closed-table" 3000000
  python3 "$here/ab.py" --reps 1 --json "$out/$t-check-churn.json" rc-churn "$out/$t/base/rc-churn" "$out/$t/check/rc-churn" 400
  for v in mask mask-all; do
    echo "== time: $t $v vs base ($(date +%T))"
    j=$out/$t-$v-stdlib.json
    python3 scripts/stdlib-bench.py --bin "$out/$t/$v/stdlib-bench" --baseline-bin "$out/$t/base/stdlib-bench" \
      --reps "$reps" --json "$j" --quiet
    python3 - "$j" "$t" "$v" >> "$out/summary.tsv" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
for mode, r in d["ab"]["results"].items():
    print(f"{sys.argv[2]}\tstdlib:{mode}\t{sys.argv[3]}\t{r['median_ratio']:.4f}\t{r['min_ratio']:.4f}\t{r['max_ratio']:.4f}")
PY
    for p in "closed-table 3000000" "rc-churn 400"; do
      set -- $p
      j=$out/$t-$v-$1.json
      python3 "$here/ab.py" --reps "$reps" --json "$j" --tsv "$out/summary.tsv" --tag "$t" "$v" \
        "$1" "$out/$t/base/$1" "$out/$t/$v/$1" "$2"
    done
  done
done

echo
column -t -s $'\t' "$out/summary.tsv"
echo "results: $out/summary.tsv"
