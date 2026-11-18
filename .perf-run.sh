set -eu
cd /workspace/wt/perf-page
export PATH="$PWD/.lake/build/bin:$PATH"
export TESTS_BIN="$PWD/.lake/build/bin/tests"
if [ -f /workspace/wiz-lang/grail.local.wiz ] && [ ! -f "$PWD/grail.local.wiz" ]; then cp /workspace/wiz-lang/grail.local.wiz "$PWD/grail.local.wiz"; fi
nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp
cd scry
cp ../grail.local.wiz . 2>/dev/null || true
grail build scry
cd ..
mkdir -p bench-out
python3 scripts/perf-report.py --out docs/perf.md --json bench-out/perf.json
