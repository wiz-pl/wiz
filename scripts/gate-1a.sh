#!/usr/bin/env bash
# The PR gate for perf lead 1a (cheap-first Cast-Refl; wiz-notes/perf-plan-2026-11-17.md §3,
# wiz-notes/checker-regression-1a.md). Run from this worktree's root, inside `nix develop`, in two
# heavy jobs, one after the other (the fixpoint alone at 7G):
#
#   /workspace/wiz-tools/heavy --mem 8G timeout 5400 bash scripts/gate-1a.sh main
#   /workspace/wiz-tools/heavy --mem 7G timeout 3600 bash scripts/gate-1a.sh fixpoint
#
# main:     build wiz and the test driver (about 25 min; the 8G is the build); then the
#           pp-base probe (wiz-rv pre-merge Base.wiz, aa05ef8, --no-cache, ≤ 80 s, about 1.2 ×
#           the 62–65 s of aeaa34ef / 15e38a70; > 600 s at #324..master); then the groups
#           =conv, =hdl-uart-temporal, =effects, =selfhost.
# fixpoint: scripts/fixpoint.sh (Conv.lean's prop gate is mirrored in selfhost/Kernel.wiz).
# Results: one line per step in $OUT/gate.tsv (default .lake/gate-1a), each step's log beside it.
set -u
OUT=${OUT:-.lake/gate-1a}; mkdir -p "$OUT"; OUT=$(realpath "$OUT"); ROOT=$PWD
PP=${PP:-/workspace/wt/pipe-proofs-pre}   # wiz-rv, detached at aa05ef8
row() { printf '%s\t%s\t%s\n' "$(date -Is)" "$1" "$2" | tee -a "$OUT/gate.tsv"; }
step() { # step NAME CMD... : run, log, time, record rc
  local n=$1; shift
  /usr/bin/env time -f '%e s %M KB' -o "$OUT/$n.time" "$@" > "$OUT/$n.log" 2>&1
  local rc=$?
  row "$n" "rc=$rc $(tail -1 "$OUT/$n.time" 2>/dev/null)"
  return $rc
}
case "${1:-}" in
  main)
    row start "$(git rev-parse --short HEAD) main"
    step build lake build wiz tests || { row FAIL build; exit 1; }
    ( cd "$PP" && /usr/bin/env time -f '%e' -o "$OUT/pp-base.time" timeout 900 "$ROOT/.lake/build/bin/wiz" \
        --no-cache -I "$ROOT/lib" check -I src -I ../wiz-ddr3/src src/Rv/PipeProofs/Base.wiz > "$OUT/pp-base.log" 2>&1 )
    rc=$?; t=$(tail -1 "$OUT/pp-base.time" 2>/dev/null)
    ok=$(awk -v t="${t:-9999}" 'BEGIN { print (t + 0 <= 80) ? "PASS" : "FAIL" }')
    [ $rc = 0 ] || ok=FAIL
    row pp-base "rc=$rc ${t:-?} s (gate ≤ 80 s) $ok errors=$(grep -c error "$OUT/pp-base.log")"
    for g in conv hdl-uart-temporal effects selfhost; do
      step "tests-$g" .lake/build/bin/tests "=$g"
    done
    row done main ;;
  fixpoint)
    row start "$(git rev-parse --short HEAD) fixpoint"
    step fixpoint scripts/fixpoint.sh "$OUT/fixpoint"
    row done fixpoint ;;
  *) echo "usage: gate-1a.sh main|fixpoint (see the header for the heavy commands)" >&2; exit 2 ;;
esac
