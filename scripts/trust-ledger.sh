#!/bin/sh
# The trust ledger (Tests/Native.lean, .github/trust-baseline.tsv): walks every
# declaration of lib/ (and the example that must stay axiom-free,
# examples/hdl-verified.wiz), runs `#print axioms`, and fails when a source of trust
# that is not in the checked-in ledger appears: an axiom, `unsafe`, a `sorry`, a
# `native_refl`/SMT axiom (Wiz's `native_decide`/`ofReduceBool`), an
# `implemented_by`/`repr:` implementation, an `extern`/FFI registration, a `builtin`
# registration, or a `partial` definition.
#
# A ledger row is `module<TAB>declaration<TAB>item<TAB>reason<TAB>owner<TAB>review`.
# A new source needs a reviewed row: `--update` refuses to add one without `--reason`.
# A row whose `review` date (YYYY-MM-DD) is before today fails as expired. A row from
# before the gate has reason `legacy: pre-gate baseline; not individually reviewed`
# and owner `unassigned`: it is accepted, reported, and still expires; `--strict-legacy`
# fails on it too.
#
#   scripts/trust-ledger.sh             check lib/ and the example
#   scripts/trust-ledger.sh --lib-only  check lib/ alone (what the `native` group runs)
#   scripts/trust-ledger.sh --print     print the sources (module, declaration, item)
#   scripts/trust-ledger.sh --update --reason "why" [--owner "who"] [--review DATE]
#                                       regenerate the ledger and add the new rows
#                                       (an explicit --review also renews migration rows)
#
# Scry is a package (`scry/`), not part of lib/ (separate-repos.md P0.1): its modules
# and rule packs moved to `scry/src/Scry/` and `scry/rules/`, and its rows left this
# ledger with them. Add a scry trust check when the package gets its own CI.
#
# `--cache DIR` is the elaboration cache the walk writes and `--cache-ro DIR` (repeatable)
# a read-only layer it searches, in the order given (the same flags as `wiz`). The walk
# elaborates every module of `lib/`, so a warm cache replays an unchanged module instead of
# elaborating it; entries are keyed by the module's exact text, its imports, the driver's
# bytes and the trust options, so a changed source cannot be served an old effect. A
# `--cache-ro`-only run writes nothing (CI restores the layer that way).
# `--no-cache` clears both.
#
# `--tree DIR --ledger FILE --today DATE` point at a fixture tree (Tests/trust-ledger/)
# and fix the date; they are for the gate's own tests (a fixture tree is never cached).
#
# Build the driver first: `lake build wiz tests` (`lake build` alone does not build it).
# `TESTS_BIN` overrides the driver path (the same variable Tests/trust-ledger/run.sh takes).
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
bin=${TESTS_BIN:-$root/.lake/build/bin/tests}
if [ ! -x "$bin" ]; then
  echo "trust-ledger: no $bin: build it first with 'lake build wiz tests'" >&2
  exit 2
fi
cd "$root"
exec "$bin" --trust-ledger "$@"
