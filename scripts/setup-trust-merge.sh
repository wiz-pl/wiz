#!/bin/sh
# Install the local git merge driver for .github/trust-baseline.tsv.
#
# A git merge driver lives in the repository's local config, which is not cloned
# and cannot be set by CI: every clone runs this once. The `.gitattributes` entry
# (`merge=trust-ledger`) is committed; this names the command it refers to. The
# command is relative to the worktree root, so one installation serves every
# worktree of the clone.
#
#   scripts/setup-trust-merge.sh          install or refresh the driver
#   scripts/setup-trust-merge.sh --show   print the configured command
#   scripts/setup-trust-merge.sh --unset  remove it (plain text merge again)
#
# The driver is `scripts/trust-ledger-merge.sh %O %A %B`; its rule and its failure
# mode are in docs/trust-ledger.md. CI cannot enforce a local driver, so a merge
# is still followed by `scripts/trust-ledger.sh --check`.
set -eu

root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  echo "setup-trust-merge: not inside a git work tree" >&2
  exit 2
}
cd "$root"

case ${1:-} in
  "")
    [ -x "$root/scripts/trust-ledger-merge.sh" ] || {
      echo "setup-trust-merge: no executable scripts/trust-ledger-merge.sh" >&2
      exit 2
    }
    # Relative to the top of whichever worktree git merges in, so the shared
    # local config serves every worktree of this clone.
    driver='sh ./scripts/trust-ledger-merge.sh %O %A %B'
    git config --local merge.trust-ledger.driver "$driver"
    echo "setup-trust-merge: installed merge.trust-ledger.driver in $root"
    echo "  $driver"
    ;;
  --show)
    git config --local --get merge.trust-ledger.driver || {
      echo "setup-trust-merge: no merge.trust-ledger.driver (run $0)" >&2
      exit 1
    }
    ;;
  --unset)
    git config --local --unset-all merge.trust-ledger.driver 2>/dev/null || true
    echo "setup-trust-merge: removed merge.trust-ledger.driver"
    ;;
  -h|--help)
    sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'
    ;;
  *)
    echo "usage: $0 [--show|--unset]" >&2
    exit 2
    ;;
esac
