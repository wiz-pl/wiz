#!/bin/sh
# The COMP-02 multi-pipeline differential harness (Tests/Differential.lean).
#
#   scripts/differential.sh                     run the corpus, compare the baseline
#   scripts/differential.sh --report FILE       also write the Markdown report
#   scripts/differential.sh --case NAME ...     only these corpus cases
#   scripts/differential.sh --pipeline NAME ... only these pipelines
#   scripts/differential.sh --update            rewrite Tests/Differential/baseline.tsv
#
# The five pipelines are lean-c, lean-llvm, wiz-c-gc, wiz-c-rc and ir-interp.  A
# pipeline that cannot run here (no llc, no Boehm GC, no GMP, no C toolchain) is
# reported as skipped, not passed.  Build the driver first: `lake build wiz tests`.
# `--update` is deliberate: review the baseline diff, and run it on a machine with the
# full toolchain so that available pipelines are recorded as passes.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
bin=$root/.lake/build/bin/tests
if [ ! -x "$bin" ]; then
  echo "differential: no $bin: build it first with 'lake build wiz tests'" >&2
  exit 2
fi
cd "$root"
exec "$bin" --differential "$@"
