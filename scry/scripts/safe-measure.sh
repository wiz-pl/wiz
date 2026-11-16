#!/usr/bin/env bash
# Measure the safe-code corpus with one scry binary.
#   SCRY_BIN=/path/to/scry scripts/safe-measure.sh [corpus-root]
# Prints TSV: case <TAB> findings <TAB> uaf <TAB> memory <TAB> boundary <TAB> rules
set -u
BIN=${SCRY_BIN:?set SCRY_BIN to the scry executable}
ROOT=${1:-$(CDPATH= cd -- "$(dirname -- "$0")/../bench/safe" && pwd)}
printf 'case\tfindings\tuaf_warn\tmemory_warn\tboundary\trules\n'
for f in "$ROOT"/*/*.c; do
  rel=${f#"$ROOT"/}
  json=$("$BIN" taint "$f" --json 2>/dev/null)
  printf '%s\t%s\n' "$rel" "$(printf '%s' "$json" | python3 -c '
import json,sys
d=json.load(sys.stdin)
f=d.get("findings") or []
m=d.get("memory") or []
b=d.get("boundary") or []
uaf=[x for x in m if x.get("rule")=="scry/memory/use-after-free"]
print(len(f), len(uaf), len(m), len(b), ",".join(x.get("rule","") for x in f) or "-", sep="\t")
')"
done
