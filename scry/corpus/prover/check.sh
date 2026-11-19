#!/usr/bin/env bash
# Regression check for the dogfood proofs. Each proof prints `key<TAB>value` lines;
# this script asserts the verdict (and, for a refutation, that the message names the
# path). A refusal is a result too: the memory fragment is an explicit REASON.
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
    grep -E '^(PROVE|ROWS|INV|VERDICT|REASON|SRC|SINK|FLOW|MSTORE|COVER|FUNCS)' "$OUT/$proof.txt" | sed 's/^/  /'
    fail=1
  else
    echo "ok   $proof  /$pattern/"
  fi
}

run() { # proof script
  local proof=$1
  PROVER=$PROVER "$ROOT/scry/corpus/prover/proofs/$proof.sh" > "$OUT/$proof.txt" 2>&1
}

run p1-process-safe && expect p1-process-safe '^VERDICT[[:space:]]+ok$' \
  && expect p1-process-safe '^ROWS[[:space:]]+1$'
run p1b-crux-api && expect p1b-crux-api '^REASON[[:space:]]+rejected: .*mload.*memory rules are not covered'
run p2-sqlcommand && expect p2-sqlcommand '^REASON[[:space:]]+rejected: .*mload.*memory rules are not covered'
run p3-header-processor && expect p3-header-processor '^VERDICT[[:space:]]+ok$' \
  && expect p3-header-processor '^ROWS[[:space:]]+10$'
run p3b-logpath && expect p3b-logpath '^REASON[[:space:]]+rejected: .*mtainted.*memory rules are not covered'
run p4-process-unsafe && expect p4-process-unsafe '^VERDICT[[:space:]]+rejected:' \
  && expect p4-process-unsafe 'path tainted\([0-9]+,[0-9]+\) -> flow\([0-9]+,[0-9]+,[0-9]+\) -> sink\([0-9]+,[0-9]+,[0-9]+\)'
run p5-helper-safe && expect p5-helper-safe '^VERDICT[[:space:]]+ok$' \
  && expect p5-helper-safe '^ROWS[[:space:]]+3$'
run p5b-helper-unsafe && expect p5b-helper-unsafe '^VERDICT[[:space:]]+rejected:' \
  && expect p5b-helper-unsafe 'path tainted\([0-9]+,[0-9]+\) -> flow\([0-9]+,[0-9]+,[0-9]+\) -> sink\([0-9]+,[0-9]+,[0-9]+\)'

exit $fail
