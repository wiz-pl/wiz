#!/usr/bin/env bash
# Run `scry project --taint` over the synthetic multi-TU project and the real C
# sources that are already on this machine. This is a measurement harness: it does not
# change the analysis. It records per-group counts, per-file findings, cache behaviour
# and wall time, and computes TP/FN/FP for the synthetic project from the checked-in
# ground truth (`bench/project-corpus.json`).
#
#   scry/scripts/project-corpus.sh
#   SCRY_LIMIT=600 scry/scripts/project-corpus.sh
#   SCRY_BIN=... SCRY_OUT=... scry/scripts/project-corpus.sh
#
# Wall time is informational on a shared machine; it is not a `perf-run` measurement.
set -u

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH= cd -- "$HERE/../.." && pwd)
SCry=$(CDPATH= cd -- "$HERE/.." && pwd)
BIN=${SCRY_BIN:-$SCry/.grail/bin/scry}
OUT=${SCRY_OUT:-$SCry/build/project-corpus}
LIMIT=${SCRY_LIMIT:-600}

if [ ! -x "$BIN" ]; then
  echo "project-corpus: no scry binary at $BIN (build it with grail build)" >&2
  exit 2
fi

mkdir -p "$OUT/compdb" "$OUT/json" "$OUT/sarif" "$OUT/log" "$OUT/cache"
RECORDS=$OUT/records.tsv
: > "$RECORDS"

python3 - "$REPO" "$OUT" "$SCry" <<'PY'
import glob, json, os, sys
repo, out, scry = sys.argv[1:]
ts = os.path.join(repo, "scry/native/tree-sitter/lib/src")
gc = glob.glob("/nix/store/*-boehm-gc-*-dev/include")
gcflags = ["-I" + gc[0]] if gc else []
groups = [
  ("synthetic", os.path.join(scry, "corpus/project/taint"),
   ["app.c", "io.c", "util.c"], ["-I."], 60, True),
  ("wiz-lang", repo,
   ["c/proc.c", "c/sockets.c", "lib/serial.c", "infoview/term.c",
    "selfhost/rt.c", "web/js.c"], ["-I.", "-Iselfhost", "-Iruntime"] + gcflags, 300, False),
  ("wiz-rv", "/workspace/wiz-rv",
   ["sw/ctest/ctest.c", "sw/doomgeneric_wizrv.c", "sw/iss/iss.c",
    "sw/iss/mustest.c", "sw/mus_synth.c", "sw/sound_wizrv.c", "sw/syscalls.c",
    "sw/tone/tone.c"], ["-I."], 600, False),
  ("tree-sitter", ts,
   ["alloc.c", "language.c", "lexer.c", "node.c", "parser.c", "query.c",
    "tree.c", "tree_cursor.c"], ["-I.", "-I../include"], 900, False),
  ("generated", "/workspace/wizard-test", ["build/old-wizard.c"], ["-Ibuild"], 120, False),
  ("generated", "/workspace/soyjack", ["droste.c"], ["."], 120, False),
]
rows = []
for name, root, files, flags, limit, synthetic in groups:
    present = [f for f in files if os.path.exists(os.path.join(root, f))]
    if not present:
        rows.append((name, root, "", "missing", str(limit)))
        continue
    label = name
    if name == "generated":
        label = "generated:" + os.path.basename(present[0])
    entries = []
    for f in present:
        entries.append({"directory": root, "file": f,
                        "arguments": ["cc"] + flags + ["-c", f, "-o", "/dev/null"]})
    compdb = os.path.join(out, "compdb", label.replace(":", "_").replace("/", "_") + ".json")
    with open(compdb, "w") as fh:
        json.dump(entries, fh, indent=1)
        fh.write("\n")
    rows.append((label, root, compdb, "run", str(limit)))
with open(os.path.join(out, "groups.tsv"), "w") as fh:
    for row in rows:
        fh.write("\t".join(row) + "\n")
PY

while IFS=$'\t' read -r group root compdb mode glimit; do
  json=$OUT/json/$group.json
  sarif=$OUT/sarif/$group.sarif
  log=$OUT/log/$group.err
  if [ "$mode" = missing ]; then
    printf '%s\t%s\t\tmissing\t0\n' "$group" "$root" >> "$RECORDS"
    continue
  fi
  start=$(date +%s%N)
  lim=${glimit:-$LIMIT}
  timeout "$lim" "$BIN" project "$root" --compdb "$compdb" --allow-errors \
      --skip-broken --taint --json --sarif "$sarif" --cache="$OUT/cache/$group" \
      --cache-stats > "$json" 2> "$log"
  st=$?
  end=$(date +%s%N)
  ms=$(( (end - start) / 1000000 ))
  printf '%s\t%s\t%s\t%s\t%s\n' "$group" "$root" "$json" "$st" "$ms" >> "$RECORDS"

done < "$OUT/groups.tsv"

# A second synthetic run with the same cache is the warm-cache measurement.
if [ -f "$OUT/compdb/synthetic.json" ]; then
  start=$(date +%s%N)
  timeout 60 "$BIN" project "$SCry/corpus/project/taint" \
      --compdb "$OUT/compdb/synthetic.json" --allow-errors --skip-broken --taint \
      --json --sarif "$OUT/sarif/synthetic-warm.sarif" \
      --cache="$OUT/cache/synthetic" --cache-stats \
      > "$OUT/json/synthetic-warm.json" 2> "$OUT/log/synthetic-warm.err"
  st=$?
  end=$(date +%s%N); ms=$(( (end - start) / 1000000 ))
  printf 'synthetic-warm\t%s\t%s\t%s\t%s\n' "$SCry/corpus/project/taint" \
    "$OUT/json/synthetic-warm.json" "$st" "$ms" >> "$RECORDS"
fi

python3 - "$REPO" "$SCry" "$OUT" "$LIMIT" <<'PY'
import json, os, sys
repo, scry, out, limit = sys.argv[1:]
rows = []
with open(os.path.join(out, "records.tsv")) as fh:
    for line in fh:
        p = line.rstrip("\n").split("\t")
        if len(p) == 5:
            rows.append(dict(group=p[0], root=p[1], json=p[2], status=p[3], ms=int(p[4])))

def load(p):
    try:
        with open(p) as fh:
            return json.load(fh)
    except Exception:
        return None

def finding_rows(d):
    xs = []
    for f in d.get("files", []):
        for x in f.get("findings", []):
            loc = x.get("location") or {}
            xs.append(dict(rule=x.get("rule"), file=f.get("file"),
                           function=x.get("function"),
                           line=loc.get("startLine"),
                           checked=x.get("derivation"), message=x.get("message")))
    return xs

groups = []
totals = dict(groups=0, units=0, functions=0, findings=0, checked=0,
              boundary=0, memory=0, ms=0, failed=0, missing=0,
              cache_hit=0, cache_miss=0, cache_write=0)
for row in rows:
    g = dict(group=row["group"], root=row["root"], status=row["status"],
             ms=row["ms"], counts={}, files=[], findings=[], cache={},
             callgraph={})
    if row["status"] == "missing":
        g["status"] = "missing"; totals["missing"] += 1
    elif row["status"] == "124":
        g["status"] = "timeout"
    elif row["status"] != "0":
        g["status"] = "error:" + row["status"]; totals["failed"] += 1
    else:
        d = load(row["json"])
        if d is None:
            g["status"] = "no-json"; totals["failed"] += 1
        else:
            g["status"] = "ok"
            g["counts"] = d.get("counts", {})
            g["units"] = d.get("units", 0)
            g["functions"] = d.get("functions", 0)
            g["cache"] = d.get("cache", {})
            g["callgraph"] = d.get("callgraph", {})
            g["files"] = [dict(file=f.get("file"), counts=f.get("counts"))
                          for f in d.get("files", [])]
            g["findings"] = finding_rows(d)
            if g["group"] != "synthetic-warm":
                totals["groups"] += 1
                totals["units"] += g["units"]
                totals["functions"] += g["functions"]
                totals["findings"] += g["counts"].get("findings", 0)
                totals["checked"] += g["counts"].get("checked", 0)
                totals["boundary"] += g["counts"].get("boundary", 0)
                totals["memory"] += g["counts"].get("memory", 0)
                totals["cache_hit"] += g["cache"].get("hit", 0)
                totals["cache_miss"] += g["cache"].get("miss", 0)
                totals["cache_write"] += g["cache"].get("write", 0)
    totals["ms"] += g["ms"]
    groups.append(g)

# Synthetic ground truth: TP/FN/FP at finding granularity.
truth_path = os.path.join(scry, "bench/project-corpus.truth.json")
truth = None
metrics = None
try:
    with open(truth_path) as fh:
        truth = json.load(fh)
except Exception:
    truth = None
if truth:
    for proj in truth.get("projects", []):
        grp = next((g for g in groups if g["group"] == proj["id"]), None)
        if grp is None or grp["status"] != "ok":
            continue
        actual = grp["findings"]
        expected = proj.get("findings", [])
        used = [False] * len(actual)
        tp = fn = 0
        for e in expected:
            hit = False
            for i, a in enumerate(actual):
                if used[i]:
                    continue
                if (a["rule"], a["file"], a["function"]) == (
                        e["rule"], e["file"], e["function"]):
                    used[i] = True; tp += 1; hit = True; break
            if not hit:
                fn += 1
        fp = len(actual) - tp
        safe = {s["file"] for s in proj.get("safe", [])}
        fp_safe = sum(1 for a in actual if a["file"] in safe and not any(
            (a["rule"], a["file"], a["function"]) == (e["rule"], e["file"], e["function"])
            for e in expected))
        precision = (100.0 * tp / (tp + fp)) if tp + fp else 100.0
        recall = (100.0 * tp / (tp + fn)) if tp + fn else 100.0
        metrics = dict(project=proj["id"], tp=tp, fn=fn, fp=fp,
                       fp_on_safe_file=fp_safe,
                       precision=round(precision, 2), recall=round(recall, 2),
                       expected=len(expected), actual=len(actual))
        grp_metrics = metrics

summary = dict(
    harness="scry/scripts/project-corpus.sh",
    note="wall time is informational on a shared machine; not a perf-run measurement",
    limit_seconds=int(limit),
    analysis="scry project --taint --json --sarif --allow-errors --cache --cache-stats",
    totals=totals, groups=groups, synthetic=locals().get("grp_metrics"))
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "summary.json"), "w") as fh:
    json.dump(summary, fh, indent=2)
    fh.write("\n")

lines = ["# scry multi-file project corpus", "",
         "Generated by `scry/scripts/project-corpus.sh`; `scry project --taint --json "
         "--sarif --allow-errors --cache --cache-stats`.",
         "Wall time is informational (shared machine, not a `perf-run` measurement).", "",
         "| group | status | units | functions | findings | checked | boundary | memory | cache hit/miss/write | ms |",
         "|---|---|---:|---:|---:|---:|---:|---:|---|---:|"]
for g in groups:
    c = g["counts"]
    ca = g["cache"]
    lines.append("| %s | %s | %s | %s | %s | %s | %s | %s | %s/%s/%s | %s |" % (
        g["group"], g["status"], g.get("units", ""), g.get("functions", ""),
        c.get("findings", ""), c.get("checked", ""), c.get("boundary", ""),
        c.get("memory", ""), ca.get("hit", ""), ca.get("miss", ""),
        ca.get("write", ""), g["ms"]))
t = totals
lines.append("| **total** | | %d | %d | %d | %d | %d | %d | %d/%d/%d | %d |" % (
    t["units"], t["functions"], t["findings"], t["checked"], t["boundary"],
    t["memory"], t["cache_hit"], t["cache_miss"], t["cache_write"], t["ms"]))
if metrics:
    lines += ["", "## Synthetic project precision/recall", "",
              "| TP | FN | FP | FP on a safe file | precision | recall | expected | actual |",
              "|---:|---:|---:|---:|---:|---:|---:|---:|",
              "| %d | %d | %d | %d | %.2f%% | %.2f%% | %d | %d |" % (
                  metrics["tp"], metrics["fn"], metrics["fp"],
                  metrics["fp_on_safe_file"], metrics["precision"],
                  metrics["recall"], metrics["expected"], metrics["actual"])]
lines += ["", "## Findings on real groups", ""]
for g in groups:
    if g["status"] != "ok" or g["group"].startswith("synthetic"):
        continue
    lines.append("### %s" % g["group"])
    if not g["findings"]:
        lines.append("(no findings)")
    for f in g["findings"][:30]:
        lines.append("- `%s:%s` **%s** `%s` (%s) - %s" % (
            f["file"], f["line"], f["rule"], f["function"], f["checked"], f["message"]))
    lines.append("")
lines += ["## Limits", "",
          "- The real groups have no independent ground truth; their findings are a "
          "manual spot-check, not a precision/recall claim.",
          "- The synthetic project is tiny; its 2/0/0 result is a regression check, not "
          "a statistical estimate.",
          "- Timings are wall clock on a shared machine and are not a `perf-run` "
          "measurement."]
with open(os.path.join(out, "summary.md"), "w") as fh:
    fh.write("\n".join(lines) + "\n")
print("wrote %s and %s" % (os.path.join(out, "summary.json"),
                          os.path.join(out, "summary.md")))
PY

python3 - "$OUT/summary.json" <<'PY'
import json, sys
s = json.load(open(sys.argv[1]))
t = s["totals"]
print("project-corpus: %d groups, %d findings (%d checked), %d boundary, %d memory, "
      "%d ms" % (t["groups"], t["findings"], t["checked"], t["boundary"],
                 t["memory"], t["ms"]))
if s.get("synthetic"):
    m = s["synthetic"]
    print("synthetic: TP=%d FN=%d FP=%d precision=%.2f%% recall=%.2f%%" % (
        m["tp"], m["fn"], m["fp"], m["precision"], m["recall"]))
PY
