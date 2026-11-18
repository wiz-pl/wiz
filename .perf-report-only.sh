set -eu
cd /workspace/wt/perf-page
export PATH="$PWD/.lake/build/bin:$PATH"
export TESTS_BIN="$PWD/.lake/build/bin/tests"
mkdir -p bench-out
python3 scripts/perf-report.py --out /tmp/opencode/perf-nocx.md --json /tmp/opencode/perf-nocx.json
