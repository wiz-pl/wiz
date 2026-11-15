#!/bin/sh
# The trust gate's own tests: small .wiz trees and ledgers, checking the CLI's exit
# codes and messages. Run from anywhere; the driver is this worktree's
# .lake/build/bin/tests (or TESTS_BIN).
#
#   Tests/trust-ledger/run.sh
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
bin=${TESTS_BIN:-$root/.lake/build/bin/tests}
today=2026-11-15
if [ ! -x "$bin" ]; then
  echo "trust-ledger fixtures: no $bin: build it first with 'lake build wiz tests'" >&2
  exit 2
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
n=0
out=$tmp/out
err=$tmp/err
all=$tmp/all

fail () {
  echo "trust-ledger fixtures: $1" >&2
  echo "--- stdout ---" >&2
  cat "$out" 2>/dev/null >&2 || true
  echo "--- stderr ---" >&2
  cat "$err" 2>/dev/null >&2 || true
  exit 1
}

# `run EXPECTED_STATUS NAME ARGS...`: run the gate, keep stdout/stderr in $out/$err.
run () {
  want=$1
  name=$2
  shift 2
  n=$((n + 1))
  set +e
  ( cd "$root" && "$bin" --trust-ledger "$@" ) >"$out" 2>"$err"
  got=$?
  set -e
  cat "$out" "$err" >"$all"
  [ "$got" -eq "$want" ] || fail "$name: expected exit $want, got $got"
}

# Some line of stdout/stderr contains the literal fragment.
has () {
  grep -Fq -- "$1" "$all" || fail "$2: no message contains '$1'"
}

# --- the fixtures -----------------------------------------------------------------
# A clean tree: the axiom has a reviewed row; the legacy count is zero.
run 0 clean --check --tree "$root/Tests/trust-ledger/clean/tree" \
  --ledger "$root/Tests/trust-ledger/clean/ledger.tsv" --today "$today"
has "trust ledger: OK (1 sources" clean
has "0 legacy rows" clean

# A new axiom with no ledger row: the new-entry gate.
run 1 new --check --tree "$root/Tests/trust-ledger/new/tree" \
  --ledger "$root/Tests/trust-ledger/new/ledger.tsv" --today "$today"
has "new source of trust (1)" new
has "axiom bad" new

# A row that exists but has no reason: not a reviewed row.
run 1 unreasoned --check --tree "$root/Tests/trust-ledger/unreasoned/tree" \
  --ledger "$root/Tests/trust-ledger/unreasoned/ledger.tsv" --today "$today"
has "missing a reason" unreasoned

# A bare three-column row is not accepted: a new row needs reason, owner and date.
run 1 bare --check --tree "$root/Tests/trust-ledger/bare/tree" \
  --ledger "$root/Tests/trust-ledger/bare/ledger.tsv" --today "$today"
has "missing a reason, an owner and a review date" bare

# A row whose review date has passed.
run 1 expired --check --tree "$root/Tests/trust-ledger/expired/tree" \
  --ledger "$root/Tests/trust-ledger/expired/ledger.tsv" --today "$today"
has "expired on 2020-01-01" expired

# A renamed declaration: the new name is new, the old row is stale.
run 1 renamed --check --tree "$root/Tests/trust-ledger/renamed/tree" \
  --ledger "$root/Tests/trust-ledger/renamed/ledger.tsv" --today "$today"
has "renamed declaration (1)" renamed
has "renamedOld -> renamedNew" renamed

# A pre-gate row (migration reason/owner): accepted, reported; --strict-legacy refuses it.
run 0 legacy --check --tree "$root/Tests/trust-ledger/legacy/tree" \
  --ledger "$root/Tests/trust-ledger/legacy/ledger.tsv" --today "$today"
has "1 legacy rows" legacy
run 1 legacy-strict --check --strict-legacy --tree "$root/Tests/trust-ledger/legacy/tree" \
  --ledger "$root/Tests/trust-ledger/legacy/ledger.tsv" --today "$today"
has "legacy rows still have the pre-gate reason/owner" legacy-strict
run 1 legacy-expired --check --tree "$root/Tests/trust-ledger/legacy/tree" \
  --ledger "$root/Tests/trust-ledger/legacy/ledger.tsv" --today 2027-07-01
has "expired on 2027-06-30" legacy-expired

# An explicit --review renews a legacy row's deadline without a new reason.
renew=$tmp/renew.tsv
cp "$root/Tests/trust-ledger/legacy/ledger.tsv" "$renew"
run 0 renew --update --tree "$root/Tests/trust-ledger/legacy/tree" \
  --ledger "$renew" --review 2028-01-01 --today 2026-11-15
has "1 legacy renewed" renew
grep -Fq "2028-01-01" "$renew" || fail "renew: the review date was not updated"
run 0 renew-check --check --tree "$root/Tests/trust-ledger/legacy/tree" \
  --ledger "$renew" --today 2027-10-01
has "1 legacy rows" renew-check

# --- --update ----------------------------------------------------------------------
# A tree with a new axiom and an empty ledger: --update refuses without a reason.
ledger=$tmp/ledger.tsv
printf '# fixture ledger for --update\n' >"$ledger"
run 2 update-no-reason --update --tree "$root/Tests/trust-ledger/new/tree" \
  --ledger "$ledger" --today "$today"
has "refusing to add 1 new row(s) without a reason" update-no-reason

# With a reason (and owner/date), it writes a reviewed row that --check accepts.
run 0 update --update --reason "fixture: reviewed by the gate test" --owner "gate-fixture" \
  --review 2027-06-30 --tree "$root/Tests/trust-ledger/new/tree" --ledger "$ledger" --today "$today"
has "1 new, 0 removed, 0 legacy renewed" update
grep -Fq "fixture: reviewed by the gate test" "$ledger" || fail "update: the reason is not in the ledger"
grep -Fq "gate-fixture" "$ledger" || fail "update: the owner is not in the ledger"
grep -Fq "2027-06-30" "$ledger" || fail "update: the review date is not in the ledger"
run 0 update-check --check --tree "$root/Tests/trust-ledger/new/tree" \
  --ledger "$ledger" --today "$today"
has "0 legacy rows" update-check

echo "trust-ledger fixtures: OK ($n checks)"
