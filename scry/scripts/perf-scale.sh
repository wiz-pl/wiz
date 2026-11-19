#!/usr/bin/env bash
# perf-scale.sh — the scale corpus as a phase table (`scry taint --progress`).
#
# One row per stage: the delta to that stage, and `VmHWM` sampled from
# /proc/<pid>/status at the moment the stage line arrived. A stage the run never reaches
# (a timeout) is simply absent; the TOTAL row still gives the wall and `ru_maxrss`, so a
# capped run is reported as such rather than guessed. stdout is drained to a temporary
# file (the JSON can be large) and stderr is read line by line.
#
#   scry/scripts/perf-scale.sh                     # the three canonical inputs
#   scry/scripts/perf-scale.sh -n 3                # report the median of three runs
#   scry/scripts/perf-scale.sh --timeout 60        # bound each run; exit 124 is reported
#   scry/scripts/perf-scale.sh --bench             # also `scry bench --no-timing`
#   scry/scripts/perf-scale.sh -b PATH FILE...     # another binary / other inputs
#
# Default inputs (all vendored, so the run is hermetic):
#   native/tree-sitter-c/src/parser.c          the 1.1 M-node generated grammar
#   native/tree-sitter/lib/src/parser.c        the 17 k-node runtime parser
#   native/tree-sitter/lib/src/query.c         the 34 k-node runtime query
# A missing input is reported as `missing` and the script continues, so a bare tree
# still runs.
#
# Dependencies: bash, python3 (os.fork/os.wait4; no `time`/`ps` needed) and a built
# `scry` (`cd scry && grail build scry`) with the vendored tree-sitter shim. The default
# rule pack is found at `../lib/Scry/rules/default.scry`; `--rules FILE` passes another
# one. The script writes only under a temporary directory.
#
# Timing policy: the numbers are informational unless the run is inside a `perf-run`
# window (AGENTS.md). Run it under `heavy` (which sizes the job from the templates) for
# a rough number on a shared machine; never quote that as a perf claim.
set -eu

runs=1
bin=${SCRY_BIN:-}
timeout=300
bench=0
rules=""
files=""

usage() {
  sed -n '2,29p' "$0" | sed 's/^# \{0,1\}//'
}

while [ $# -gt 0 ]; do
  case "$1" in
    -n) runs=$2; shift 2 ;;
    -b) bin=$2; shift 2 ;;
    -t|--timeout) timeout=$2; shift 2 ;;
    --bench) bench=1; shift ;;
    --rules) rules=$2; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    --) shift; break ;;
    -*) echo "perf-scale: unknown option $1" >&2; exit 2 ;;
    *) break ;;
  esac
done

case "$runs" in
  ''|*[!0-9]*|0) echo "perf-scale: -n needs a positive integer" >&2; exit 2 ;;
esac

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
pkg=$root/scry

if [ -z "$bin" ]; then
  bin=$pkg/.grail/bin/scry
fi
if [ ! -x "$bin" ]; then
  echo "perf-scale: no scry binary at $bin" >&2
  echo "  build it: (cd $pkg && $root/.lake/build/bin/grail build scry)" >&2
  exit 2
fi
case "$bin" in
  /*) ;;
  *) bin=$(CDPATH= cd -- "$(dirname -- "$bin")" && pwd)/$(basename -- "$bin") ;;
esac

if [ $# -gt 0 ]; then
  for f in "$@"; do files="$files $f"; done
else
  files="native/tree-sitter-c/src/parser.c"
  files="$files native/tree-sitter/lib/src/parser.c"
  files="$files native/tree-sitter/lib/src/query.c"
fi

cd "$pkg"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/perf-scale.XXXXXX")
trap 'rm -rf "$tmp"' EXIT INT TERM

printf '# scry %s\n' "$("$bin" --version 2>/dev/null | head -1)"
printf '# bin %s\n' "$bin"
printf '# runs %s  timeout %ss\n' "$runs" "$timeout"
printf 'file\tphase\twall_ms\tpeak_rss_kb\tnote\n'

# One run of one file. Writes the phase rows (`name delta peak`) to ROWS and the total
# (`wall rss exit`) to TOTAL. The parent samples VmHWM after every stderr line.
run_once() {
  local file=$1 rows=$2 total=$3
  python3 - "$bin" "$timeout" "$rules" "$rows" "$total" "$tmp/out" "$file" <<'PY'
import os, re, sys, time
bin, timeout, rules, rows_path, total_path, out_path, path = sys.argv[1:]
cmd = [bin, "taint", path, "--json", "--allow-errors", "--progress", "--timeout", timeout]
if rules:
    cmd += ["--rules", rules]
t0 = time.monotonic()
out = os.open(out_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
err_r, err_w = os.pipe()
pid = os.fork()
if pid == 0:
    try:
        devnull = os.open(os.devnull, os.O_RDONLY)
        os.dup2(devnull, 0); os.dup2(out, 1); os.dup2(err_w, 2)
        for fd in (err_r, err_w, out):
            os.close(fd)
        os.execv(cmd[0], cmd)
    except OSError:
        os._exit(127)
os.close(err_w)
os.close(out)
stage_re = re.compile(r"^scry: \[stage\] ([a-z-]+) elapsed=(\d+)ms(?: (.*))?$")
rows = []
peak = 0
with os.fdopen(err_r, "r", errors="replace") as err:
    for line in err:
        line = line.rstrip("\n")
        sys.stderr.write(line + "\n")
        try:
            with open("/proc/%d/status" % pid) as st:
                for l in st:
                    if l.startswith("VmHWM:"):
                        peak = int(l.split()[1])
                        break
        except OSError:
            pass
        m = stage_re.match(line)
        if m:
            # A per-function line is `summaries function ...`, whose first word after
            # `[stage]` is still `summaries`; skip it so only final stage lines count.
            if " function " in line:
                continue
            rows.append((m.group(1), int(m.group(2)), peak))
_, status, ru = os.wait4(pid, 0)
code = os.waitstatus_to_exitcode(status)
wall = int(round((time.monotonic() - t0) * 1000))
with open(rows_path, "w") as f:
    prev = 0
    for name, elapsed, peak in rows:
        delta = max(0, elapsed - prev)
        f.write("%s\t%d\t%d\n" % (name, delta, peak))
        prev = elapsed
with open(total_path, "w") as f:
    f.write("%d\t%d\t%d\n" % (wall, ru.ru_maxrss, code))
PY
}

median() {
  sort -n | awk '{ a[NR] = $1 } END { if (NR == 0) print ""; else print a[int((NR + 1) / 2)] }'
}

for f in $files; do
  if [ ! -f "$f" ]; then
    printf '%s\tmissing\t0\t0\t(absent)\n' "$f"
    continue
  fi
  i=0
  : > "$tmp/walls"
  while [ "$i" -lt "$runs" ]; do
    run_once "$f" "$tmp/run.$i.rows" "$tmp/run.$i.total"
    cut -f1 "$tmp/run.$i.total" >> "$tmp/walls"
    i=$((i + 1))
  done
  wall_med=$(median < "$tmp/walls")
  pick=0
  i=0
  while [ "$i" -lt "$runs" ]; do
    if [ "$(cut -f1 "$tmp/run.$i.total")" = "$wall_med" ]; then pick=$i; break; fi
    i=$((i + 1))
  done
  while IFS=$(printf '\t') read -r name delta peak; do
    if [ "$name" = "TOTAL" ]; then continue; fi
    printf '%s\t%s\t%s\t%s\n' "$f" "$name" "$delta" "$peak"
  done < "$tmp/run.$pick.rows"
  read -r wall rss code < "$tmp/run.$pick.total"
  printf '%s\tTOTAL\t%s\t%s\t(exit %s)\n' "$f" "$wall" "$rss" "$code"
done

if [ "$bench" -eq 1 ]; then
  printf '# bench (safe corpus)\n'
  "$bin" bench --no-timing 2>&1 | tail -1
fi
