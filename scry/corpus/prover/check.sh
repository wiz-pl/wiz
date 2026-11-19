#!/usr/bin/env bash
# Regression check for the prover corpus. Each proof prints `key<TAB>value` lines;
# this script asserts the tagged verdict and, for a refutation, that the message names
# the provenance path (a memory finding names its store and load). A refused
# certificate or a vacuous verdict is a result too: it must say which one it is.
set -u
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
OUT=$ROOT/scry/build/prover-proofs
mkdir -p "$OUT"
fail=0

expect() { # proof pattern
  local proof=$1 pattern=$2
  if ! grep -qE "$pattern" "$OUT/$proof.txt"; then
    echo "FAIL $proof: no /$pattern/"
    grep -E '^(PROPERTY|PROVE|ROWS|INV|LOCS|VERDICT|WITNESS|REFUSED|VACUOUS|SCRIPT|SRC|SINK|FLOW|MSTORE|MLOAD|MTAINTED|COVER|FUNCS)' "$OUT/$proof.txt" | sed 's/^/  /'
    fail=1
  else
    echo "ok   $proof  /$pattern/"
  fi
}

run() { # proof script
  local proof=$1
  PROVER=$PROVER "$ROOT/scry/corpus/prover/proofs/$proof.sh" > "$OUT/$proof.txt" 2>&1
}

run p1-process-safe && expect p1-process-safe '^VERDICT[[:space:]]+proved$' \
  && expect p1-process-safe '^ROWS[[:space:]]+1$'
# P1b reads a field and calls a service; there is no Console.ReadLine and no
# Process.Start, so the honest answer is vacuous, not proved.
run p1b-field-service && expect p1b-field-service '^VERDICT[[:space:]]+vacuous: .*source set is empty'
# P1c is the memory-free method in the same fixture: neither source nor sink.
run p1c-vacuous && expect p1c-vacuous '^VERDICT[[:space:]]+vacuous: .*source set is empty' \
  && expect p1c-vacuous '^SRC[[:space:]]+0$' \
  && expect p1c-vacuous '^SINK[[:space:]]+0$'
# P2: the SQL property over the untrusted sources. The field read is covered by the
# memory invariant; the command text is built from constants and parameter names.
run p2-sqlcommand && expect p2-sqlcommand '^VERDICT[[:space:]]+proved' \
  && expect p2-sqlcommand '^PROPERTY[[:space:]]+constant-or-parameter-bound'
# P3: the header is a source and the processor call is a sink, but the header does not
# reach the processor argument.
run p3-header-processor && expect p3-header-processor '^VERDICT[[:space:]]+proved$'
# P3b has no sink after lowering: vacuous, not a refused memory certificate.
run p3b-logpath && expect p3b-logpath '^VERDICT[[:space:]]+vacuous: .*sink set is empty'
# P6: the modern C# twin; the record's store and the later load are in the invariant,
# so the checker refutes it through memory.
run p6-modern-store && expect p6-modern-store '^VERDICT[[:space:]]+refuted:' \
  && expect p6-modern-store 'store\(2,23,25\)' \
  && expect p6-modern-store 'load\(2,31,35\)' \
  && expect p6-modern-store 'sink\(32,1,35\)'
run p4-process-unsafe && expect p4-process-unsafe '^VERDICT[[:space:]]+refuted:' \
  && expect p4-process-unsafe 'path .* -> sink\(10,1,9\)'
run p5-helper-safe && expect p5-helper-safe '^VERDICT[[:space:]]+proved$' \
  && expect p5-helper-safe '^ROWS[[:space:]]+3$'
run p5b-helper-unsafe && expect p5b-helper-unsafe '^VERDICT[[:space:]]+refuted:' \
  && expect p5b-helper-unsafe 'path .* -> sink\(8,0,7\)'
# The C fixtures' spills are checked in when available; regenerate one with scry-cst
# (SCRY_CST=/path/to/scry-cst) if it is missing.
ensure_spill() { # c-file
  local c=$1 tool=${SCRY_CST:-}
  [ -f "$c.cst" ] && return 0
  if [ -z "$tool" ]; then tool=$(command -v scry-cst || true); fi
  if [ -z "$tool" ]; then
    echo "FAIL $c: no spill and no scry-cst (set SCRY_CST=...)" >&2
    exit 2
  fi
  "$tool" "$c" > "$c.cst"
}
ensure_spill "$ROOT/scry/corpus/prover/c/memcpy-safe.c"
ensure_spill "$ROOT/scry/corpus/prover/c/memcpy-weak.c"
ensure_spill "$ROOT/scry/corpus/prover/c/memcpy-unguarded.c"
# P7: the cut. The memcpy length is guarded by n <= 16 and the destination has 32 cells.
run p7-memcpy-safe && expect p7-memcpy-safe '^VERDICT[[:space:]]+proved \(every write is preceded by a check\)$' \
  && expect p7-memcpy-safe '^GUARDS[[:space:]]+1$' \
  && expect p7-memcpy-safe '^WRITES[[:space:]]+1$'
# P8: the guard is before the copy but permits 64 into a 32-cell buffer; the witness
# names the guard and the use.
run p8-memcpy-weak && expect p8-memcpy-weak '^VERDICT[[:space:]]+refuted:' \
  && expect p8-memcpy-weak 'guard\(' \
  && expect p8-memcpy-weak 'use\(' \
  && expect p8-memcpy-weak 'allows register'
# P9: no guard at all; the witness names the use and says there is no guard.
run p9-memcpy-unguarded && expect p9-memcpy-unguarded '^VERDICT[[:space:]]+refuted:' \
  && expect p9-memcpy-unguarded 'has no guard on register' \
  && expect p9-memcpy-unguarded 'use\('

exit $fail
