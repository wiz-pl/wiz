#!/bin/sh
# The negative case for the C#'s static source-reader export: the bundle `scry cs
# --bundle` writes must pass `web/source_static_test.mjs`, and each mutation below must
# make that same test fail with its own verdict. Without this, a green acceptance test
# could be green because it checks nothing a broken C# export breaks.
#
# The mutations are the three failure shapes a front-end can plausibly produce, and each
# one is a shape the C export's gate (`web/source_export_gate.sh`) does not cover:
#
#   1. a finding's span past the end of its file (the index and the file's own JSON, so
#      only the span bound catches it: the two agree with each other);
#   2. a file missing from `data/f/` while the manifest still lists it (the reader cannot
#      mount that file, and the first paint lists a file with no source);
#   3. an `ast` fact whose span does not fit its file (the infotree would underline past
#      the end of the source; the C# export's own check, not the C export's).
#
#   usage: web/source_cs_gate.sh BUNDLE_DIR
#
#   BUNDLE_DIR  a bundle `scry cs tests/fixtures/report-cs --bundle DIR --assets web`
#               wrote (or `grail test tests/web-bundle-cs.wiz`'s build/web-bundle-cs)
#
# No Emscripten, no Wasm and no browser: the bundle's data and its patch trace are the
# contract, as in the acceptance test.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
TEST=$ROOT/web/source_static_test.mjs
[ $# -ge 1 ] || {
  echo "usage: web/source_cs_gate.sh BUNDLE_DIR" >&2
  exit 2
}
BUNDLE=$1
[ -d "$BUNDLE/data" ] || {
  echo "cs source export gate: $BUNDLE/data is missing (is it a \`scry cs --bundle\` bundle?)" >&2
  exit 2
}
command -v node >/dev/null || { echo "cs source export gate: node is not on PATH" >&2; exit 2; }
command -v python3 >/dev/null || { echo "cs source export gate: python3 is not on PATH" >&2; exit 2; }
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# 0. The unmutated bundle passes, with the test's own verdict.
cp -R "$BUNDLE" "$WORK/ok"
if out=$(node "$TEST" "$WORK/ok" 2>&1) &&
   printf '%s' "$out" | grep -qF 'source static: all checks passed'; then
  echo "ok (the C# export): the acceptance test passes"
else
  echo "FAIL (the C# export): the acceptance test must pass on the unmutated bundle"
  printf '%s\n' "$out"
  exit 1
fi

# 1. A finding's span past the end of its file (the first finding of the index, and the
#    same span in the file's own JSON, so consistency checks cannot be what fails).
cp -R "$BUNDLE" "$WORK/span"
python3 - "$WORK/span/data" <<'PY'
import json, os, sys
data = sys.argv[1]
index = os.path.join(data, "findings.json")
j = json.load(open(index))
if not j["findings"]:
    sys.exit("cs source export gate: no finding to mutate")
row = j["findings"][0]
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

# 2. A file missing from `data/f/` while the manifest and the file table list it.
cp -R "$BUNDLE" "$WORK/missing"
python3 - "$WORK/missing/data" <<'PY'
import json, os, sys
data = sys.argv[1]
files = json.load(open(os.path.join(data, "files.json")))["files"]
if not files:
    sys.exit("cs source export gate: no file to drop")
os.remove(os.path.join(data, "f", files[0]["id"] + ".json"))
PY

# 3. An `ast` fact whose span does not fit its file (one file's own JSON only).
cp -R "$BUNDLE" "$WORK/ast"
python3 - "$WORK/ast/data" <<'PY'
import json, os, sys
data = sys.argv[1]
files = json.load(open(os.path.join(data, "files.json")))["files"]
for f in files:
    per = os.path.join(data, "f", f["id"] + ".json")
    k = json.load(open(per))
    rows = [r for r in k.get("facts", []) if r.get("kind") == "ast"]
    if not rows:
        continue
    rows[-1]["span"] = {"start": 0, "stop": 10 ** 9}
    json.dump(k, open(per, "w"))
    print(f["path"])
    break
else:
    sys.exit("cs source export gate: no ast fact to mutate")
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
expect_fail "$WORK/span" "a finding's span past the end of its file"
expect_fail "$WORK/missing" "a file missing from data/f/"
expect_fail "$WORK/ast" "an ast fact's span outside its file"
[ "$failed" = 0 ] || exit 1
echo "cs source export gate: all checks passed"
