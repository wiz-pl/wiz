#!/usr/bin/env bash
# P10: the `scry prove` subcommand. Each case prints `case=LABEL exit=N`, the report,
# and (for the JSON cases) one object; check.sh asserts the statuses and the tags.
#
# It reads the checked-in C# spills, so it needs no `scry-cst`, no tree-sitter and no
# .NET. The point is the command's contract: 0 proved, 1 rejected, 2 usage/IO,
# 3 vacuous, and `--json` carrying the same verdict without changing the status.
set -u
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVE=${SCRY_PROVE:-$ROOT/scry/build/scry-prove}
PACK="$ROOT/scry/corpus/csharp/csharp.scry"
SAFE="$ROOT/scry/corpus/csharp/taint/cwe78-process-safe.cs"
UNSAFE="$ROOT/scry/corpus/csharp/taint/cwe78-process-unsafe.cs"
VACUOUS="$ROOT/scry/corpus/prover/synthetic/RecordSeeder.cs"
cd "$ROOT"

case_run() { # label expected-rc args…
  local label=$1 expected=$2; shift 2
  local out rc
  out=$("$PROVE" "$@" 2>&1); rc=$?
  printf 'case=%s exit=%s expected=%s\n' "$label" "$rc" "$expected"
  printf '%s\n' "$out"
  if [ "$rc" != "$expected" ]; then printf 'BAD-EXIT %s (expected %s, got %s)\n' \
      "$label" "$expected" "$rc"; fi
}

# 0: the safe twin proves with the searched invariant `{(0,0)}`.
case_run proved 0 "$SAFE" --claim "noFlow Fixtures.Runner.Main" --pack "$PACK"
# 0: the JSON form prints the same verdict and status.
case_run proved-json 0 "$SAFE" --claim "noFlow Fixtures.Runner.Main" --json --pack "$PACK"
# 0: a hand-written certificate replaces the search; the same one row proves.
case_run hand-check 0 "$SAFE" --claim "noFlow Fixtures.Runner.Main rows=0:0" --pack "$PACK"
# 1: the unsafe twin is refuted, and the witness names the definition and the sink.
case_run refuted 1 "$UNSAFE" --claim "noFlow Fixtures.Runner.Main" --pack "$PACK"
case_run refuted-json 1 "$UNSAFE" --claim "noFlow Fixtures.Runner.Main" --json --pack "$PACK"
# 1: a wrong hand-written certificate is refused and names the missing seed fact.
case_run refused 1 "$SAFE" --claim "noFlow Fixtures.Runner.Main rows=1:1" --pack "$PACK"
# 1: an ill-formed script is scriptFailed, not a silent success.
case_run script-failed 1 "$SAFE" --claim "noFlow Fixtures.Runner.Main" \
  --script "apply 99" --pack "$PACK"
# 3: the memory-free method has no source and no sink: nothing was checked.
case_run vacuous 3 "$VACUOUS" --claim "noFlow Fixtures.Hosting.RecordSeeder.EnsureAsync" \
  --pack "$PACK"
# 2: a claim whose kind is not in the language is a usage error.
case_run usage 2 "$SAFE" --claim "bogus Fixtures.Runner.Main" --pack "$PACK"
