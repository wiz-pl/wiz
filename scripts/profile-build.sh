#!/usr/bin/env bash
# Profile a fixed build corpus and print its top costs, so two runs of the tree can be
# compared: per declaration (kind and name), per imported module, and the backend phases
# (IR, lowering, optimisation, code generation, object file, link).  The numbers come from
# `wiz build --profile-json`, one run per target with a fresh cache directory, so every
# target is a cold build (`--profile` itself is off by default and does not change the
# generated C; Tests/Groups/Profile.lean checks that).
#
#   scripts/profile-build.sh                     # top 20 of the corpus, on stdout
#   scripts/profile-build.sh --top 40
#   scripts/profile-build.sh --json /tmp/p.json  # also keep the merged JSON
#   scripts/profile-build.sh --baseline /tmp/p.json
#                                                # compare with an earlier run
#
# The corpus is fixed: a driver that imports a few `lib/` modules (Prelude, Text, Nat,
# ListLemmas, Json) and `examples/effects.wiz`.  A fresh cache per target means the
# declaration times are there (a warm build serves commands from the cache and reports
# them as hits, not as declarations).
#
# The table is **wall time on a shared machine**, not a benchmark: compare two runs from
# the same session (and the same machine) with --baseline; a single number is noise.
# Not attributed: process start-up, parsing, option handling, GC and I/O inside a phase.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

wiz=${WIZ:-$root/.lake/build/bin/wiz}
# the dev shell's toolchain (the `wiz` binary defaults to `cc` and `-lgmp`)
toolflags=()
[ -n "${WIZ_CC:-}" ] && toolflags+=(--cc "$WIZ_CC")
[ -n "${WIZ_CFLAGS:-}" ] && toolflags+=(--cflags "$WIZ_CFLAGS")
[ -n "${WIZ_LDFLAGS:-}" ] && toolflags+=(--ldflags "$WIZ_LDFLAGS")
top=20
json=${PROFILE_JSON:-$root/bench/.profile/profile-build.json}
baseline=
keep=0

usage() {
  cat <<'EOF'
usage: scripts/profile-build.sh [--top N] [--json FILE] [--baseline FILE] [--wiz PATH] [--keep]

  --top N         rows to print (default 20)
  --json FILE     merged output (default bench/.profile/profile-build.json)
  --baseline FILE compare with an earlier merged output
  --wiz PATH      the compiler (default .lake/build/bin/wiz, or $WIZ)
  --keep          keep the temporary build and cache directories
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --top) top=$2; shift 2 ;;
    --json) json=$2; shift 2 ;;
    --baseline) baseline=$2; shift 2 ;;
    --wiz) wiz=$2; shift 2 ;;
    --keep) keep=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "profile-build.sh: unknown argument $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [ ! -x "$wiz" ]; then
  echo "profile-build.sh: no compiler at $wiz (run 'lake build wiz' or pass --wiz)" >&2
  exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "profile-build.sh: python3 is needed to print the table" >&2
  exit 2
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-profile.XXXXXX")
cleanup() {
  if [ "$keep" = 1 ]; then echo "profile-build.sh: kept $tmp" >&2; else rm -rf "$tmp"; fi
}
trap cleanup EXIT

# The fixed corpus.  (`import Json` pulls Text; the imports are listed so the corpus does
# not change when one module's imports change.)
cat > "$tmp/corpus.wiz" <<'EOF'
import Prelude
import Text
import Nat
import ListLemmas
import Json
def main : Nat := 0
EOF

run() {
  local name=$1 src=$2 out=$3 cache=$4 jsonf=$5
  mkdir -p "$cache"
  if ! "$wiz" build "$src" -o "$out" "${toolflags[@]}" --cache "$cache" --profile-json "$jsonf" > "$tmp/$name.log" 2>&1; then
    echo "profile-build.sh: $name failed:" >&2
    sed 's/^/  /' "$tmp/$name.log" >&2
    exit 1
  fi
}

run corpus "$tmp/corpus.wiz" "$tmp/corpus" "$tmp/cache-corpus" "$tmp/corpus.json"
run example "$root/examples/effects.wiz" "$tmp/effects" "$tmp/cache-example" "$tmp/example.json"

mkdir -p "$(dirname "$json")"
python3 - "$tmp/corpus.json" "$tmp/example.json" "$json" "$top" "$baseline" "$root" <<'PY'
import json
import os
import platform
import subprocess
import sys
import time

corpus_path, example_path, out_path, top, baseline_path, root = sys.argv[1:7]
top = int(top)

def git(*args):
    try:
        return subprocess.run(["git", "-C", root, *args], capture_output=True,
                              text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""

def load(path, name):
    with open(path) as f:
        j = json.load(f)
    return name, j

targets = [load(corpus_path, "corpus"), load(example_path, "example")]

# One row per (kind, name), summed over the targets: the corpus is fixed, so the same
# declaration has the same key in a later run.
entries = {}
total = 0
target_info = {}
for name, j in targets:
    total += j["total_ns"]
    target_info[name] = {"total_ns": j["total_ns"], "cache": j["cache"],
                         "elaboration_ns": j["elaboration_ns"],
                         "modules": [m["name"] for m in j["modules"]]}
    def add(kind, label, ns, module="", status=""):
        key = (kind, label)
        old = entries.get(key, {"kind": kind, "name": label, "ns": 0,
                                "module": module, "status": status, "targets": 0})
        old["ns"] += ns
        old["targets"] += 1
        entries[key] = old
    for d in j["declarations"]:
        add("decl", d["name"], d["ns"], d["module"], d["status"])
    for m in j["modules"]:
        add("module", m["name"], m["ns"], "", m["status"])
    for key, val in j["backend"].items():
        add("phase", key.removesuffix("_ns"), val)

rows = sorted(entries.values(), key=lambda e: -e["ns"])

def ms(ns):
    return f"{ns / 1e6:.1f}"

def pct(ns):
    return 0.0 if total == 0 else 100.0 * ns / total

def show(row_list):
    print(f"{'%':>6}  {'ms':>9}  {'kind':<7} name")
    for e in row_list[:top]:
        where = "" if e["kind"] != "decl" or not e["module"] else f"  [{e['module']}]"
        label = e["name"] + where
        print(f"{pct(e['ns']):6.1f}  {ms(e['ns']):>9}  {e['kind']:<7} {label}")
    print()

print(f"wiz profile: {len(targets)} targets, total {ms(total)} ms "
      f"(wall time on a shared machine: compare with --baseline, not across machines)")
for name, _ in targets:
    c = target_info[name]["cache"]
    print(f"  {name:<8} {ms(target_info[name]['total_ns']):>9} ms, "
          f"{c['hits']} cache hits, {c['misses']} misses")
print()
show(rows)

if baseline_path:
    with open(baseline_path) as f:
        base = json.load(f)
    old = {(e["kind"], e["name"]): e["ns"] for e in base.get("entries", [])}
    old_total = base.get("total_ns", 0)
    print(f"against {baseline_path} (total {ms(old_total)} ms)")
    print(f"{'before':>9}  {'after':>9}  {'change':>8}  {'kind':<7} name")
    changed = []
    for e in rows:
        key = (e["kind"], e["name"])
        if key not in old:
            continue
        b = old[key]
        change = 0.0 if b == 0 else 100.0 * (e["ns"] - b) / b
        changed.append((change, e, b))
    for change, e, b in sorted(changed, key=lambda x: -abs(x[0]))[:top]:
        print(f"{ms(b):>9}  {ms(e['ns']):>9}  {change:+7.1f}%  {e['kind']:<7} {e['name']}")
    print()

out = {
    "schema": 1,
    "created": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "generator": "scripts/profile-build.sh",
    "commit": git("rev-parse", "HEAD"),
    "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
    "host": platform.node(),
    "note": "wall time on a shared machine; compare runs from the same session",
    "targets": {name: {"total_ns": j["total_ns"], "elaboration_ns": j["elaboration_ns"],
                       "cache": j["cache"], "declarations": len(j["declarations"]),
                       "modules": len(j["modules"])} for name, j in targets},
    "total_ns": total,
    "entries": rows,
}
os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
with open(out_path, "w") as f:
    json.dump(out, f, indent=2, sort_keys=True)
    f.write("\n")
print(f"wrote {out_path}")
PY
