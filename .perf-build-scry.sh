set -eu
cd /workspace/wt/perf-page
export PATH="$PWD/.lake/build/bin:$PATH"
nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp
cd scry
cp ../grail.local.wiz . 2>/dev/null || true
grail build scry
ls -la .grail/bin/scry
