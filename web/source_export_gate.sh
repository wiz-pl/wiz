#!/bin/sh
# The negative case for the static source-reader export: `scry web`'s bundle must pass
# `web/source_static_test.mjs`, and three mutations of that bundle must each make the
# same test fail. Without this, a green acceptance test could be green because it checks
# nothing that a broken export breaks (web-docs-next M1.1, train12 triage task 15).
#
# The mutations are the three failure shapes the export can plausibly have:
#
#   1. a finding's span past the end of its file (the index and the file's own JSON, so
#      only the span bound catches it: the two agree with each other);
#   2. a finding dropped from `data/findings.json` (the count and the first paint lose it);
#   3. one byte of a scripted interaction's expected page in `ui-trace.json` (the patch
#      replay no longer reproduces the page it says it does).
#
#   usage: web/source_export_gate.sh BUNDLE_DIR
#
#   BUNDLE_DIR  a bundle `scry web` wrote (`scry web scry/tests/fixtures/report --out
#               build/web-bundle --assets web`, or `grail build web-bundle` in scry/)
#
# No Emscripten, no Wasm and no browser: the bundle's data and its patch trace are the
# contract, as in the acceptance test. `web/test.sh` runs this when it has a bundle
# (`WIZ_SOURCE_BUNDLE=DIR`, or a built `scry/.grail/bin/scry`), and scry.yml runs it on
# the export it makes.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
TEST=$ROOT/web/source_static_test.mjs
[ $# -ge 1 ] || {
  echo "usage: web/source_export_gate.sh BUNDLE_DIR" >&2
  exit 2
}
BUNDLE=$1
[ -d "$BUNDLE/data" ] || {
  echo "source export gate: $BUNDLE/data is missing (is it a \`scry web\` bundle?)" >&2
  exit 2
}
command -v node >/dev/null || { echo "source export gate: node is not on PATH" >&2; exit 2; }
command -v python3 >/dev/null || { echo "source export gate: python3 is not on PATH" >&2; exit 2; }
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# 0. The unmutated bundle passes, with the test's own verdict (so a crash there is not
#    mistaken for a pass).
cp -R "$BUNDLE" "$WORK/ok"
if out=$(node "$TEST" "$WORK/ok" 2>&1) &&
   printf '%s' "$out" | grep -qF 'source static: all checks passed'; then
  echo "ok (the export): the acceptance test passes"
else
  echo "FAIL (the export): the acceptance test must pass on the unmutated bundle"
  printf '%s\n' "$out"
  exit 1
fi

# 1. The taint.c finding's span past the end of its file (the finding the acceptance
#    test's answer schema exercises). Both the index and the per-file JSON get the same
#    bad span, so consistency checks cannot be what fails: the span bound must.
cp -R "$BUNDLE" "$WORK/span"
python3 - "$WORK/span/data" <<'PY'
import json, os, sys
data = sys.argv[1]
index = os.path.join(data, "findings.json")
j = json.load(open(index))
row = next((f for f in j["findings"] if f["path"].endswith("taint.c")), None)
if row is None:
    sys.exit("source export gate: no taint.c finding to mutate")
bad = {"start": 10 ** 9, "stop": 10 ** 9 + 1}
row["span"] = bad
json.dump(j, open(index, "w"))
per = os.path.join(data, "f", row["fileId"] + ".json")
k = json.load(open(per))
for r in k["findings"]:
    if r["id"] == row["id"]:
        r["span"] = bad
json.dump(k, open(per, "w"))
PY

# 2. The xss.c finding dropped from the index (its file keeps it): the manifest's count
#    and the file's own count disagree, and the first paint no longer lists it.
cp -R "$BUNDLE" "$WORK/drop"
python3 - "$WORK/drop/data/findings.json" <<'PY'
import json, sys
path = sys.argv[1]
j = json.load(open(path))
kept = [f for f in j["findings"] if not f["path"].endswith("xss.c")]
if len(kept) == len(j["findings"]):
    sys.exit("source export gate: no xss.c finding to drop")
j["findings"] = kept
json.dump(j, open(path, "w"))
PY

# 3. One byte of a scripted interaction's expected page: the replay must mismatch.
cp -R "$BUNDLE" "$WORK/trace"
python3 - "$WORK/trace/ui-trace.json" <<'PY'
import json, sys
path = sys.argv[1]
j = json.load(open(path))
step = j["steps"][0]
before = step["html"]
step["html"] = before.replace('data-finding="', 'data-findingX="', 1)
if step["html"] == before:
    sys.exit("source export gate: no byte to change in the first trace step")
json.dump(j, open(path, "w"))
PY

# Each mutation must fail, and fail with the test's own verdict: a crash or an unreadable
# bundle is not the red we want to prove.
failed=0
expect_fail() {  # DIR WHAT
  if out=$(node "$TEST" "$1" 2>&1); then
    echo "FAIL (mutation $2): the acceptance test still passed"
    printf '%s\n' "$out"
    failed=1
    return 0
  fi
  if printf '%s' "$out" | grep -Eq 'source static: [0-9]+ failure\(s\)'; then
    echo "ok (mutation $2): the acceptance test fails"
  else
    echo "FAIL (mutation $2): the test failed without its verdict (a crash, not a check)"
    printf '%s\n' "$out"
    failed=1
  fi
  return 0
}
expect_fail "$WORK/span" "the taint.c finding's span past the end of its file"
expect_fail "$WORK/drop" "the xss.c finding dropped from data/findings.json"
expect_fail "$WORK/trace" "one byte of a scripted page in ui-trace.json"
[ "$failed" = 0 ] || exit 1
echo "source export gate: all checks passed"
