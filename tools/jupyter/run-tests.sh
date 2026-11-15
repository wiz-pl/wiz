#!/bin/sh
# The test entry point for tools/jupyter: the protocol tests, the kernel self-test and
# the widget front end (Node fallback, plus a headless browser when one is installed).
#
#   sh tools/jupyter/run-tests.sh [--no-browser] [--browser PATH]
#
# Every part skips cleanly when its dependency is missing and prints the reason; a skip
# is not a failure.  The suite is opt-in: it is not part of `lake test` or CI.
set -u
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
TOOL=$ROOT/tools/jupyter
status=0

have_python=0
command -v python3 >/dev/null 2>&1 && have_python=1

if [ "$have_python" = 1 ] && python3 -c 'import zmq, jupyter_client' 2>/dev/null; then
  echo "== protocol tests (jupyter_client)"
  PYTHONPATH="$TOOL${PYTHONPATH:+:$PYTHONPATH}" \
    python3 -m unittest discover -s "$TOOL/tests" -v || status=1
else
  echo "skip: protocol tests (python3 with pyzmq and jupyter_client is not installed)"
fi

if [ "$have_python" = 1 ] && python3 -c 'import zmq' 2>/dev/null; then
  echo "== kernel self-test (pyzmq)"
  PYTHONPATH="$TOOL${PYTHONPATH:+:$PYTHONPATH}" \
    python3 -m wiz_kernel --self-test --backend auto || status=1
else
  echo "skip: kernel self-test (python3 with pyzmq is not installed)"
fi

if command -v node >/dev/null 2>&1; then
  echo "== widget front end (Node fallback; headless browser if installed)"
  node "$TOOL/static/widget_test.mjs" "$@" || status=1
else
  echo "skip: widget front end (node is not installed)"
fi

if [ "$status" = 0 ]; then
  echo "tools/jupyter: all runnable checks passed"
else
  echo "tools/jupyter: FAILURES" >&2
fi
exit $status
