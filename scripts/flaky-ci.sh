#!/usr/bin/env bash
# CI glue for scripts/flaky.py. The ci.yml steps this expects (the file is owned by
# another pull request when this branch was written) are:
#
#   test shard, on a failed shard:
#     scripts/flaky-ci.sh shard SHARD logs/SHARD.log logs/SHARD-flaky.json
#   test shard, last (if: always()):
#     scripts/flaky-ci.sh verdict "${{ steps.tests.outcome }}" \
#                               "${{ steps.flaky.outcome }}" "${{ matrix.shard.name }}"
#   result job, last (if: always()):
#     scripts/flaky-ci.sh expiry
#
# `shard` reruns the failing cases with --from-log, writes the JSON report and a
# Markdown section for $GITHUB_STEP_SUMMARY, and exits 0 only when every failure is an
# active quarantine entry. A deterministic failure, an incomplete measurement, a source
# failure that now only skips, or a flaky case with no active entry exits non-zero.
#
# Cost: with the defaults (FLAKY_REPEATS=5) each failing case is run 5 times alone and a
# suspect 5 more times after a predecessor, so about 10 driver runs per failing case,
# capped by FLAKY_BUDGET seconds of wall time for the whole failed shard. It reuses the
# shard's Wiz cache (`FLAKY_CACHE`, default ~/.cache/wiz), so the reruns are incremental
# on both ubuntu-latest and the self-hosted runner; a cold cache pays elaboration again.
set -euo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
FLAKY="$ROOT/scripts/flaky.py"
DEFAULT_QUARANTINE="$ROOT/.github/flaky-quarantine.json"

DRIVER=${FLAKY_DRIVER:-$ROOT/.lake/build/bin/tests}
QUARANTINE=${FLAKY_QUARANTINE:-$DEFAULT_QUARANTINE}
CACHE=${FLAKY_CACHE-${HOME:+$HOME/.cache/wiz}}
BUDGET=${FLAKY_BUDGET:-600}
REPEATS=${FLAKY_REPEATS:-5}
TIMEOUT=${FLAKY_TIMEOUT:-600}
ORDER=${FLAKY_ORDER:-suspects}

emit() { # Markdown line(s) on stdout and in the step summary
  printf '%s\n' "$*"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    printf '%s\n' "$*" >> "$GITHUB_STEP_SUMMARY"
  fi
}

error() { # a GitHub annotation when running in Actions, a plain line otherwise
  if [ "${GITHUB_ACTIONS:-}" = true ]; then
    printf '::error title=%s::%s\n' "$1" "$2" >&2
  else
    printf 'error: %s\n' "$2" >&2
  fi
}

# Exit 0 only when every failing case in the report is an actively quarantined flake.
# A deterministic failure is never masked, whatever the quarantine says.
gate_report() { # REPORT
  python3 - "$1" <<'PY'
import json
import sys

path = sys.argv[1]
with open(path, encoding="utf-8") as f:
    report = json.load(f)
bad = []
for c in report.get("cases", []):
    cls = c.get("classification")
    state = (c.get("quarantine") or {}).get("state")
    label = f"{c['group']} #{c['index']} {c['name']}"
    if cls == "deterministic fail":
        bad.append(f"{label}: deterministic fail (a quarantine never masks this)")
    elif cls == "incomplete":
        bad.append(f"{label}: incomplete (the reruns did not measure it)")
    elif cls == "always skip" and c.get("source_failure"):
        bad.append(f"{label}: always skip after a failure (a skip is not a pass)")
    elif cls == "flaky" and state != "active":
        bad.append(f"{label}: flaky but quarantine is {state}")
    elif state == "expired":
        bad.append(f"{label}: quarantine expired {c['quarantine']['expires']}")
if not report.get("cases"):
    bad.append("the report has no cases (the log named no failing case)")
verdict = report.get("verdict") or {}
if verdict.get("code") != 0:
    bad.append(f"verdict is {verdict.get('kind')} (exit {verdict.get('code')})")
if bad:
    print("flaky gate: " + "; ".join(bad), file=sys.stderr)
    sys.exit(1)
PY
}

run_shard() { # SHARD LOG [REPORT]
  local shard=${1:?shard name}
  local log=${2:?test log}
  local report=${3:-}
  if [ ! -f "$log" ]; then
    error "Flaky CI" "no test log at $log, so the failed shard cannot be classified"
    return 1
  fi
  local dir
  dir=$(dirname "$log")
  report=${report:-$dir/$shard-flaky.json}
  local md="${report%.json}.md"
  local text="${report%.json}.txt"
  mkdir -p "$dir"

  local args=(
    python3 "$FLAKY"
    --driver "$DRIVER"
    --from-log "$log"
    --label "$shard"
    --budget "$BUDGET"
    --repeats "$REPEATS"
    --timeout "$TIMEOUT"
    --order-check "$ORDER"
    --report "$report"
    --summary-md "$md"
  )
  if [ -n "$QUARANTINE" ] && [ -f "$QUARANTINE" ]; then
    args+=(--quarantine "$QUARANTINE")
  else
    args+=(--no-quarantine)
  fi
  if [ -n "$CACHE" ]; then
    args+=(--driver-arg=--cache --driver-arg="$CACHE")
  fi

  local rc=0
  "${args[@]}" >"$text" 2>&1 || rc=$?
  if [ -f "$md" ]; then
    cat "$md"
    if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
      cat "$md" >> "$GITHUB_STEP_SUMMARY"
    fi
  fi

  local gate=0
  if [ -f "$report" ]; then
    gate_report "$report" || gate=$?
  else
    gate=1
  fi

  if [ "$rc" -eq 0 ] && [ "$gate" -eq 0 ]; then
    emit "✅ **Quarantined flake:** the shard failed, but every case is either an active quarantine entry (expiry above) or a clean pass. The job stays green."
    return 0
  fi

  local why
  case "$rc" in
    1) why="a deterministic failure, an incomplete measurement, a source failure that only skips, or an expired quarantine entry" ;;
    2) why="the classifier could not read its input" ;;
    3) why="a flaky case that is not quarantined (no active entry)" ;;
    4) why="the rerun budget ran out before every case was classified" ;;
    *) why="the classifier failed (exit $rc)" ;;
  esac
  emit "❌ **Not a quarantined flake:** $why. The shard stays red."
  if [ -f "$text" ]; then
    if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
      {
        echo
        echo "<details><summary>classifier output</summary>"
        echo
        echo '```'
        tail -40 "$text"
        echo '```'
        echo
        echo "</details>"
      } >> "$GITHUB_STEP_SUMMARY"
    fi
  fi
  return 1
}

run_expiry() {
  local out rc=0
  if [ -z "$QUARANTINE" ]; then
    printf 'flaky quarantine: no file (nothing is quarantined)\n'
    return 0
  fi
  out=$(python3 "$FLAKY" --check-quarantine "$QUARANTINE" 2>&1) || rc=$?
  printf '%s\n' "$out"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    {
      echo "### Flaky quarantine"
      echo
      echo '```'
      printf '%s\n' "$out"
      echo '```'
    } >> "$GITHUB_STEP_SUMMARY"
  fi
  if [ "$rc" -ne 0 ]; then
    error "Flaky quarantine" "the quarantine check failed: an entry is past its expiry (see the entry and owner above) or the file is malformed; fix the test or re-quarantine it with a new date"
    return 1
  fi
  return 0
}

run_verdict() { # TESTS_OUTCOME FLAKY_OUTCOME SHARD
  local tests=${1:?tests outcome}
  local flaky=${2:?flaky outcome}
  local shard=${3:-shard}
  if [ "$tests" = success ]; then
    emit "✅ **Test verdict:** $shard passed; no classification was needed."
    return 0
  fi
  if [ "$tests" = failure ] && [ "$flaky" = success ]; then
    emit "✅ **Test verdict:** $shard failed, and every failure was an active quarantine entry. The job is green."
    return 0
  fi
  error "CI tests" "shard $shard: tests=$tests, flaky classification=$flaky; a failed shard is green only when the classification clears every failure"
  emit "❌ **Test verdict:** $shard: tests=$tests, flaky classification=$flaky. The job stays red."
  return 1
}

self_test() {
  local tmp bad=0
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/flaky-ci-selftest.XXXXXX")
  trap 'rm -rf "${tmp:-}"' EXIT
  unset GITHUB_STEP_SUMMARY

  python3 - "$ROOT" "$tmp/tests" <<'PY'
import sys
sys.path.insert(0, sys.argv[1] + "/scripts")
import flaky
open(sys.argv[2], "w", encoding="utf-8").write(flaky.STUB_DRIVER)
PY
  chmod +x "$tmp/tests"
  DRIVER="$tmp/tests"
  CACHE="$tmp/cache" # exercises --driver-arg=--cache (the stub ignores it)
  BUDGET=60
  REPEATS=3
  TIMEOUT=30
  ORDER=off

  mklog() { # NAME CASE
    printf '\u2500\u2500 fixtures (fixtures)\n  \u2717 %s (0.001 s)\n      stub failure\n\n0 passed, 1 failed\n' "$2" > "$tmp/$1.log"
  }
  mkq() { # NAME CASE EXPIRES OWNER
    printf '{"version":1,"entries":[{"group":"fixtures","case":"%s","expires":"%s","reason":"test"%s}]}\n' \
      "$2" "$3" "${4:+,\"owner\":\"$4\"}" > "$tmp/$1.json"
  }
  expect() { # WANT NAME SHARD LOG QUARANTINE NEEDLE
    local want=$1 name=$2 shard=$3 log=$4 q=$5 needle=${6:-}
    QUARANTINE=$q
    local rc=0
    run_shard "$shard" "$log" "$tmp/report-$name.json" > "$tmp/$name.out" 2>&1 || rc=$?
    if [ "$rc" -ne "$want" ]; then
      echo "FAIL $name: exit $rc, wanted $want"
      sed -n '1,20p' "$tmp/$name.out"
      bad=$((bad + 1))
      return
    fi
    if [ -n "$needle" ] && ! grep -q "$needle" "$tmp/$name.out"; then
      echo "FAIL $name: output lacks $needle"
      sed -n '1,20p' "$tmp/$name.out"
      bad=$((bad + 1))
      return
    fi
    echo "ok   $name (exit $rc)"
  }

  mklog alternates alternates
  mkq active alternates 2099-12-01 "Fixture owner"
  printf '{"version":1,"entries":[]}\n' > "$tmp/empty.json"
  expect 0 "quarantined-flake" core "$tmp/alternates.log" "$tmp/active.json" "active until 2099-12-01"
  expect 1 "unquarantined-flake" core "$tmp/alternates.log" "$tmp/empty.json" "not quarantined"
  mklog fails "always fails"
  mkq activeFails "always fails" 2099-12-01 "Fixture owner"
  expect 1 "deterministic-fail" core "$tmp/fails.log" "$tmp/activeFails.json" "deterministic"
  mklog passes "always passes"
  mkq activePasses "always passes" 2099-12-01 ""
  expect 0 "unreproduced-quarantined" core "$tmp/passes.log" "$tmp/activePasses.json" "not reproduced"
  expect 1 "unreproduced-clean" core "$tmp/passes.log" "$tmp/empty.json" "not quarantined"
  mklog skips "always skips"
  mkq activeSkips "always skips" 2099-12-01 ""
  expect 1 "skip-not-pass" core "$tmp/skips.log" "$tmp/activeSkips.json" "always skip"
  mkq expired alternates 2000-01-01 "Fixture owner"
  expect 1 "expired-quarantine" core "$tmp/alternates.log" "$tmp/expired.json" "EXPIRED"

  # The budget is a hard cap: an exhausted rerun is never a green shard.
  local saved_budget=$BUDGET
  BUDGET=0.0001
  expect 1 "exhausted-budget" core "$tmp/alternates.log" "$tmp/active.json" "budget"
  BUDGET=$saved_budget

  # The verdict step decides the job: a failed shard is green only when `shard` cleared it.
  local vrc
  vrc=0; run_verdict success skipped core >/dev/null 2>&1 || vrc=$?
  [ "$vrc" -eq 0 ] && echo "ok   verdict: tests passed" || { echo "FAIL verdict: tests passed"; bad=$((bad + 1)); }
  vrc=0; run_verdict failure success core >/dev/null 2>&1 || vrc=$?
  [ "$vrc" -eq 0 ] && echo "ok   verdict: failure cleared by quarantine" || { echo "FAIL verdict: cleared"; bad=$((bad + 1)); }
  vrc=0; run_verdict failure failure core >/dev/null 2>&1 || vrc=$?
  [ "$vrc" -ne 0 ] && echo "ok   verdict: failure not cleared" || { echo "FAIL verdict: uncleared"; bad=$((bad + 1)); }
  vrc=0; run_verdict failure skipped core >/dev/null 2>&1 || vrc=$?
  [ "$vrc" -ne 0 ] && echo "ok   verdict: classification skipped" || { echo "FAIL verdict: skipped"; bad=$((bad + 1)); }

  # The report and the Markdown summary are written next to the log.
  python3 - "$tmp/report-quarantined-flake.json" <<'PY' || bad=$((bad + 1))
import json, sys
r = json.load(open(sys.argv[1]))
assert r["shard"] == "core", r["shard"]
c = r["cases"][0]
assert c["classification"] == "flaky", c
assert c["quarantine"]["state"] == "active", c
assert "| shard | case | class | seed(s) | quarantine |" in open(sys.argv[1].replace(".json", ".md")).read()
PY

  if [ "$bad" -eq 0 ]; then
    echo "flaky-ci self-test: ok"
    return 0
  fi
  echo "flaky-ci self-test: $bad failure(s)"
  return 1
}

usage() {
  cat <<EOF
usage: $0 shard SHARD LOG [REPORT]
       $0 expiry
       $0 verdict TESTS_OUTCOME FLAKY_OUTCOME [SHARD]
       $0 self-test

The classifier is scripts/flaky.py; see docs/building.md, "Flaky tests and the
quarantine". Environment: FLAKY_DRIVER, FLAKY_QUARANTINE, FLAKY_CACHE, FLAKY_BUDGET,
FLAKY_REPEATS, FLAKY_TIMEOUT, FLAKY_ORDER.
EOF
}

main() {
  local cmd=${1:-}
  case "$cmd" in
    shard)
      shift
      run_shard "$@"
      ;;
    expiry)
      run_expiry
      ;;
    verdict)
      shift
      run_verdict "$@"
      ;;
    self-test)
      self_test
      ;;
    *)
      usage >&2
      return 2
      ;;
  esac
}

main "$@"
