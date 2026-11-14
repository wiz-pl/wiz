#!/bin/sh
# The trust ledger (Tests/Native.lean, .github/trust-baseline.tsv): walks every
# declaration of lib/ (and the example that must stay axiom-free,
# examples/hdl-verified.wiz), runs `#print axioms`, and fails when a source of trust
# that is not in the checked-in baseline appears: an axiom, a `sorry`, a `native_refl`
# or SMT axiom, an `implemented_by`/`repr:` implementation, a `builtin` registration,
# or a `partial` definition.
#
#   scripts/trust-ledger.sh             check lib/ and the example
#   scripts/trust-ledger.sh --lib-only  check lib/ alone (what the `native` group runs)
#   scripts/trust-ledger.sh --print     print the ledger (module, declaration, item)
#   scripts/trust-ledger.sh --update    rewrite the baseline (review the diff first!)
#
# Build the driver first: `lake build wiz tests` (`lake build` alone does not build it).
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
bin=$root/.lake/build/bin/tests
if [ ! -x "$bin" ]; then
  echo "trust-ledger: no $bin: build it first with 'lake build wiz tests'" >&2
  exit 2
fi
cd "$root"
exec "$bin" --trust-ledger "$@"
