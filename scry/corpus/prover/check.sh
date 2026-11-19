#!/usr/bin/env bash
# Regression check for the dogfood proofs. Each proof prints `key<TAB>value` lines;
# this script asserts the tagged verdict and, for a refutation, that the message names
# the provenance path (a memory finding names its store and load). A refusal or a
# vacuous verdict is a result too: it must say which one it is.
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
# P1b is memory-covered now, but it has no Console.ReadLine and no Process.Start, so
# the honest answer is "vacuous", not "proved".
run p1b-crux-api && expect p1b-crux-api '^VERDICT[[:space:]]+vacuous: .*source set is empty'
# P1c has neither a source nor a sink; the old rubber stamp is now a loud vacuity.
run p1c-crux-api-vacuous && expect p1c-crux-api-vacuous '^VERDICT[[:space:]]+vacuous: .*source set is empty' \
  && expect p1c-crux-api-vacuous '^SRC[[:space:]]+0$' \
  && expect p1c-crux-api-vacuous '^SINK[[:space:]]+0$'
# P2: the SQL property ("every argument is a constant or a parameter bind") over the
# untrusted sources. The method's reads (the connection string) are memory seeds now,
# but they do not reach the SQL text: the text is built from constants and parameter
# names, so the claim is proved.
run p2-sqlcommand && expect p2-sqlcommand '^VERDICT[[:space:]]+proved' \
  && expect p2-sqlcommand '^PROPERTY[[:space:]]+constant-or-parameter-bound'
run p3-header-processor && expect p3-header-processor '^VERDICT[[:space:]]+proved$' \
  && expect p3-header-processor '^ROWS[[:space:]]+10$'
# P3b has no sink after the frontend lowering: vacuous, not a memory refusal.
run p3b-logpath && expect p3b-logpath '^VERDICT[[:space:]]+vacuous: .*sink set is empty'
# P6: the modern C# twin the analysis already found; now the checker refutes it through
# the record's store and the later load.
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

exit $fail
