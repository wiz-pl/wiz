#!/bin/sh
# A fake `wiz` for scripts/check-docs-examples.py --self-test.
#
#   fake-wiz.sh check [--cache DIR] FILE
#   fake-wiz.sh run   [--cache DIR] FILE
#
# It accepts a block that starts with an import (the checker adds `import Prelude`),
# rejects one containing FAIL, and prints the expected output of the fixture's run
# block.  It is deliberately dumb; it tests the checker, not Wiz.
set -eu

if [ "${1:-}" = "--version" ]; then
  echo "fake-wiz 0"
  exit 0
fi

cmd=$1
shift
for file do :; done

body=$(cat "$file")
case "$body" in
  *FAIL*)
    echo "$file:1:1: error: fixture failure" >&2
    exit 1
    ;;
esac
case "$body" in
  import\ *|*"
import "*) ;;
  *)
    echo "$file:1:1: error: no import line (the checker should have added Prelude)" >&2
    exit 1
    ;;
esac

if [ "$cmd" = "run" ]; then
  echo "hello from fixture"
else
  echo "$file:1:1: info: ok"
fi
