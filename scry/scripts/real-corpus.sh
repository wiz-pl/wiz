#!/usr/bin/env bash
# Run scry over the real C sources that are already on this machine and write a
# reproducible, machine-readable summary plus one SARIF file per source.
#
# This is a measurement harness: it does not change the analysis.  It runs the same
# `scry taint` pipeline as the CLI (parse -> lower -> points-to -> taint -> certify)
# and records counts, wall time, parse errors, boundary warnings and memory warnings.
#
#   scry/scripts/real-corpus.sh                 # default corpus, build/real-corpus/
#   SCRY_LIMIT=300 scry/scripts/real-corpus.sh  # per-file timeout (seconds)
#   SCRY_STRESS=1 scry/scripts/real-corpus.sh   # also the 3.8 MB tree-sitter parser
#   SCRY_BIN=... SCRY_OUT=...                   # override binary / output directory
#
# The default corpus is the C that is actually checked in under this repository plus
# the two generated ``projects`` C files that exist in the standard workspace.  A
# missing external file is recorded as ``missing`` rather than failing the run, so the
# script also works on a bare checkout.  wiz-ddr3, wiz-crucible and wiz-reals have no
# tracked C sources on this machine (see scry/bench/real-corpus.md); they are listed
# here as explicit empty projects so the report does not silently omit them.
set -u

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH= cd -- "$HERE/../.." && pwd)
BIN=${SCRY_BIN:-$REPO/scry/.grail/bin/scry}
OUT=${SCRY_OUT:-$REPO/scry/build/real-corpus}
LIMIT=${SCRY_LIMIT:-300}

if [ ! -x "$BIN" ]; then
  echo "real-corpus: no scry binary at $BIN (build it with grail build)" >&2
  exit 2
fi

mkdir -p "$OUT/json" "$OUT/sarif" "$OUT/log"
RECORDS=$OUT/records.tsv
: > "$RECORDS"

# record PROJECT DISPLAY ABS_PATH REL_PATH
record() {
  project=$1; display=$2; abs=$3; rel=$4
  stem=$(printf '%s' "$project/$rel" | tr '/ ' '__')
  json=$OUT/json/$stem.json
  sarif=$OUT/sarif/$stem.sarif
  log=$OUT/log/$stem.err
  if [ ! -f "$abs" ]; then
    printf '%s\t%s\t%s\tmissing\t0\t0\t%s\t%s\t%s\n' \
      "$project" "$display" "$abs" "$json" "$sarif" "$log" >> "$RECORDS"
    return 0
  fi
  start=$(date +%s%N)
  timeout "$LIMIT" "$BIN" taint "$abs" --json --allow-errors \
      --sarif "$sarif" > "$json" 2> "$log"
  st=$?
  end=$(date +%s%N)
  ms=$(( (end - start) / 1000000 ))
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$project" "$display" "$abs" "$st" "$st" "$ms" "$json" "$sarif" "$log" >> "$RECORDS"
}

# --- wiz-lang: runtime, sockets, serial, infoview, self-hosted runtime ---
for f in c/proc.c c/sockets.c lib/serial.c infoview/term.c selfhost/rt.c web/js.c; do
  record wiz-lang "$f" "$REPO/$f" "$f"
done

# --- wiz-rv: the bare-metal RV32IM test programs and drivers ---
for f in sw/ctest/ctest.c sw/doomgeneric_wizrv.c sw/iss/iss.c sw/iss/mustest.c \
         sw/mus_synth.c sw/sound_wizrv.c sw/syscalls.c sw/tone/tone.c; do
  record wiz-rv "$f" "/workspace/wiz-rv/$f" "$f"
done

# --- vendored tree-sitter: a real, macro-heavy C library ---
for f in alloc.c language.c lexer.c node.c parser.c query.c tree.c tree_cursor.c; do
  record tree-sitter "$f" "$REPO/scry/native/tree-sitter/lib/src/$f" "$f"
done

# --- generated projects: the two C outputs that are present in /workspace ---
record generated old-wizard.c /workspace/wizard-test/build/old-wizard.c old-wizard.c
record generated droste.c /workspace/soyjack/droste.c droste.c

# --- explicitly empty projects: no tracked C on this machine ---
for p in wiz-ddr3 wiz-crucible wiz-reals; do
  : # listed in the checked-in report, no files to run
done

if [ "${SCRY_STRESS:-0}" = 1 ]; then
  record stress tree-sitter-c-parser.c \
    "$REPO/scry/native/tree-sitter-c/src/parser.c" tree-sitter-c-parser.c
fi

# --- the checked-in S0/S2 metric corpus (a separate, synthetic reference point) ---
BENCH=$OUT/bench.json
if timeout "$LIMIT" "$BIN" bench --no-timing --json - > "$BENCH" 2> "$OUT/log/bench.err"; then
  :
else
  echo "real-corpus: scry bench failed (see $OUT/log/bench.err)" >&2
  : > "$BENCH"
fi

python3 - "$RECORDS" "$BENCH" "$OUT" "$LIMIT" <<'PY'
import json, os, sys
from collections import OrderedDict

records_path, bench_path, out, limit = sys.argv[1:]
rows = []
with open(records_path) as f:
    for line in f:
        p = line.rstrip("\n").split("\t")
        if len(p) != 9:
            continue
        rows.append(dict(project=p[0], display=p[1], path=p[2], status=p[3],
                         exit=int(p[4]), ms=int(p[5]), json=p[6], sarif=p[7], log=p[8]))

def load(row):
    try:
        with open(row["json"]) as f:
            return json.load(f)
    except Exception:
        return None

projects = OrderedDict()
totals = dict(files=0, present=0, findings=0, checked=0, unchecked=0,
              boundary=0, memory=0, parse_errors=0, ms=0, timeouts=0, failures=0,
              missing=0)

for row in rows:
    proj = projects.setdefault(row["project"], dict(
        files=0, present=0, findings=0, checked=0, unchecked=0, boundary=0,
        memory=0, parse_errors=0, ms=0, timeouts=0, failures=0, missing=0,
        entries=[]))
    proj["files"] += 1
    totals["files"] += 1
    entry = dict(file=row["display"], status=row["status"], ms=row["ms"],
                 findings=0, checked=0, boundary=0, memory=0, parse_errors=0,
                 detail=[], memory_detail=[], boundary_detail=[])
    if row["status"] == "missing":
        proj["missing"] += 1; totals["missing"] += 1
        entry["status"] = "missing"
    else:
        proj["present"] += 1
        totals["present"] += 1
    if row["status"] == "missing":
        pass
    elif row["exit"] == 124:
        proj["timeouts"] += 1; totals["timeouts"] += 1
        entry["status"] = "timeout"
    elif row["exit"] != 0:
        proj["failures"] += 1; totals["failures"] += 1
        entry["status"] = "error:%d" % row["exit"]
    else:
        d = load(row)
        if d is None:
            proj["failures"] += 1; totals["failures"] += 1
            entry["status"] = "no-json"
        else:
            c = d.get("counts", {})
            entry["status"] = "ok"
            entry["findings"] = c.get("findings", 0)
            entry["checked"] = c.get("checked", 0)
            entry["boundary"] = c.get("boundary", 0)
            entry["memory"] = c.get("memory", 0)
            entry["parse_errors"] = d.get("parseErrors", 0)
            entry["detail"] = [
                dict(rule=x.get("rule"), severity=x.get("severity"),
                     function=x.get("function"), callee=x.get("callee"),
                     argument=x.get("argument"), derivation=x.get("derivation"),
                     line=(x.get("location") or {}).get("startLine"),
                     message=x.get("message"))
                for x in d.get("findings", [])]
            entry["memory_detail"] = [
                dict(rule=x.get("rule"), function=x.get("function"),
                     line=(x.get("location") or {}).get("startLine"),
                     message=x.get("message"))
                for x in d.get("memory", [])]
            entry["boundary_detail"] = [
                dict(function=x.get("function"),
                     line=(x.get("location") or {}).get("startLine"),
                     message=x.get("message"))
                for x in d.get("boundary", [])[:5]]
            for k in ("findings", "checked", "boundary", "memory", "parse_errors", "ms"):
                proj[k] += entry[k]; totals[k] += entry[k]
    proj["entries"].append(entry)

bench = None
try:
    with open(bench_path) as f:
        b = json.load(f)
    if b:
        bench = dict(cases=b.get("corpus", {}).get("cases"),
                     files=b.get("corpus", {}).get("files"),
                     bytes=b.get("corpus", {}).get("bytes"),
                     overall=b.get("overall"), macro=b.get("macro"),
                     path_validity=b.get("path_validity"),
                     certificate=b.get("certificate"))
except Exception:
    bench = None

summary = dict(
    harness="scry/scripts/real-corpus.sh",
    note="wall time is informational on a shared machine; not a perf-run measurement",
    limit_seconds=int(limit),
    analysis="scry taint --json --allow-errors --sarif (parse -> lower -> points-to -> taint -> certify)",
    totals=totals,
    projects=projects,
    bench=bench,
)

os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "summary.json"), "w") as f:
    json.dump(summary, f, indent=2, sort_keys=False)
    f.write("\n")

lines = []
lines.append("# scry real-C corpus: machine summary\n")
lines.append("Generated by `scry/scripts/real-corpus.sh`; `scry taint --json --allow-errors --sarif`.")
lines.append("Wall time is informational on the shared machine (not a `perf-run` measurement).\n")
lines.append("| project | files | present | findings | checked | boundary | memory | parse errors | timeouts | errors | ms |")
lines.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
for name, p in projects.items():
    lines.append("| %s | %d | %d | %d | %d | %d | %d | %d | %d | %d | %d |" % (
        name, p["files"], p["present"], p["findings"], p["checked"], p["boundary"],
        p["memory"], p["parse_errors"], p["timeouts"], p["failures"], p["ms"]))
t = totals
lines.append("| **total** | %d | %d | %d | %d | %d | %d | %d | %d | %d | %d |" % (
    t["files"], t["present"], t["findings"], t["checked"], t["boundary"],
    t["memory"], t["parse_errors"], t["timeouts"], t["failures"], t["ms"]))
lines.append("\n## Per file\n")
lines.append("| project | file | status | findings | boundary | memory | parse errors | ms |")
lines.append("|---|---|---|---:|---:|---:|---:|---:|")
for name, p in projects.items():
    for e in p["entries"]:
        lines.append("| %s | `%s` | %s | %d | %d | %d | %d | %d |" % (
            name, e["file"], e["status"], e["findings"], e["boundary"],
            e["memory"], e["parse_errors"], e["ms"]))
lines.append("\n## Findings (all, for the precision spot-check)\n")
any_f = False
for name, p in projects.items():
    for e in p["entries"]:
        for f in e["detail"]:
            any_f = True
            lines.append("- **%s/%s:%s** `%s` %s (%s, %s) - %s" % (
                name, e["file"], f.get("line"), f.get("rule"), f.get("function"),
                f.get("derivation"), "checked" if f.get("derivation") == "checked" else "unchecked",
                f.get("message")))
if not any_f:
    lines.append("(none)")
lines.append("\n## Memory warnings (first 5 per file)\n")
any_m = False
for name, p in projects.items():
    for e in p["entries"]:
        for m in e["memory_detail"][:5]:
            any_m = True
            lines.append("- **%s/%s:%s** `%s` %s - %s" % (
                name, e["file"], m.get("line"), m.get("rule"), m.get("function"), m.get("message")))
if not any_m:
    lines.append("(none)")
lines.append("\n## Boundary warnings (first 5 per file)\n")
any_b = False
for name, p in projects.items():
    for e in p["entries"]:
        for w in e["boundary_detail"][:5]:
            any_b = True
            lines.append("- **%s/%s:%s** %s - %s" % (
                name, e["file"], w.get("line"), w.get("function"), w.get("message")))
if not any_b:
    lines.append("(none)")
if bench:
    o = bench.get("overall") or {}
    lines.append("\n## `scry bench` (S0/S2 synthetic corpus, reference)\n")
    lines.append("- cases/files/bytes: %s / %s / %s" % (bench.get("cases"), bench.get("files"), bench.get("bytes")))
    lines.append("- TP/FN/TN/FP/unknown: %s / %s / %s / %s / %s" % (
        o.get("tp"), o.get("fn"), o.get("tn"), o.get("fp"), o.get("unknown")))
    lines.append("- TPR/FPR/Youden/precision/F1: %s / %s / %s / %s / %s" % (
        o.get("tpr"), o.get("fpr"), o.get("youden"), o.get("precision"), o.get("f1")))

with open(os.path.join(out, "summary.md"), "w") as f:
    f.write("\n".join(lines) + "\n")

print("wrote %s and %s" % (os.path.join(out, "summary.json"), os.path.join(out, "summary.md")))
PY

python3 - "$OUT/summary.json" <<'PY'
import json, sys
s = json.load(open(sys.argv[1]))
t = s["totals"]
print("real-corpus: %d files (%d present), %d findings (%d checked), %d boundary, "
      "%d memory, %d parse errors, %d timeouts, %d errors, %d ms" % (
      t["files"], t["present"], t["findings"], t["checked"], t["boundary"],
      t["memory"], t["parse_errors"], t["timeouts"], t["failures"], t["ms"]))
PY
