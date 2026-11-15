#!/bin/sh
# The wiz.nvim tests (the `nvim` test group runs this from the repository root):
# headless Neovim, with the plugin from this checkout and the real `wiz lsp`.
#   WIZ  the wiz executable (default: this checkout's .lake/build/bin/wiz, else `wiz`)
#   GRAIL the grail executable (default: this checkout's .lake/build/bin/grail, else `grail`)
#   NVIM the nvim executable (default: `nvim`)
#
# The tests report themselves: run.lua prints a `N passed, M failed` summary and exits
# with `cquit! 1` when a test failed. Neovim can also exit nonzero *after* that summary
# for reasons of its own (a libuv handle or a job still alive while it tears down); such
# an exit is an nvim exit-status anomaly, not a test result, and reporting it as a test
# failure makes a flake look like a regression. This script keeps the two apart:
#
#   0  every test passed and nvim exited 0
#   1  a test failed (the `✗` case is named on a `harness:` line too)
#   2  the run cannot be trusted: nvim exited nonzero without a failed test, or died
#      before printing a summary. The message says which, and the end of nvim's raw
#      output (progress lines included) plus its log are printed.
#
# `run.sh --self-check` exercises those paths against fixture output; it needs neither
# nvim nor a build.
set -u

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../../.." && pwd)
self="$here/$(basename -- "$0")"

# The filtered rendering: progress lines end in \r and are overwritten by their result,
# so keep only the results. (The raw output is used for diagnostics.)
render() {
  tr '\r' '\n' <"$1" | grep -v '^  … ' | sed 's/-- INSERT --//g'
}
raw() {
  tr '\r' '\n' <"$1" | sed 's/-- INSERT --//g'
}

# `harness:`-prefixed lines can never be mistaken for (or filtered as) test output.
dump_raw() {
  printf 'harness: nvim output (last 40 lines, progress lines included):\n'
  raw "$1" | tail -n 40 | sed 's/^/harness: | /'
}

failing_cases() {
  # `.*` also catches a `✗` line that a stray message (e.g. a vim.notify warning)
  # was printed on top of.
  raw "$1" | sed -n 's/^.*  ✗ //p' | tr '\n' ';' | sed 's/;$//'
}

dump_log() {
  if [ -s "$1" ]; then
    printf 'harness: nvim log (NVIM_LOG_FILE):\n'
    tail -n 40 "$1" | sed 's/^/harness: | /'
    if grep -q 'uv_loop_close() hang?' "$1" 2>/dev/null; then
      printf 'harness: cause: nvim/libuv teardown could not close its event loop (a handle was still open); this is a Neovim exit-status anomaly, not a test failure\n'
    fi
  fi
}

main() {
  nvim=${NVIM:-nvim}
  if ! command -v "$nvim" >/dev/null 2>&1; then
    echo "skipped: no nvim on PATH"
    exit 0
  fi
  if [ -z "${WIZ:-}" ]; then
    if [ -x "$repo/.lake/build/bin/wiz" ]; then WIZ=$repo/.lake/build/bin/wiz; else WIZ=wiz; fi
  fi
  if [ -z "${GRAIL:-}" ]; then
    if [ -x "$repo/.lake/build/bin/grail" ]; then GRAIL=$repo/.lake/build/bin/grail; else GRAIL=grail; fi
  fi
  export WIZ GRAIL WIZ_LIB="${WIZ_LIB:-$repo/lib}"

  tmp="${TMPDIR:-/tmp}/wiz-nvim-tests.$$"
  if ! mkdir -p "$tmp"; then
    echo "harness: cannot create $tmp"
    exit 2
  fi
  trap 'rm -rf "$tmp"' EXIT
  out=$tmp/out
  log=$tmp/nvim.log

  # Run from editors/nvim (the tests use paths relative to it).
  cd "$here/.." || exit 2
  # A fresh log file: nvim logs a teardown that fails to close its loop here.
  # (Without this, nvim writes to $XDG_STATE_HOME/nvim/nvim.log or $HOME/nvim.log.)
  NVIM_LOG_FILE=$log "$nvim" --headless --clean -u tests/minimal_init.lua -l tests/run.lua >"$out" 2>&1
  status=$?

  render "$out"
  # The last line that ends in the tests' own summary (a stray message may share it).
  summary_line=$(raw "$out" | grep -E '[0-9][0-9]* passed, [0-9][0-9]* failed[[:space:]]*$' | tail -n 1)
  passed=
  failed=
  summary=
  if [ -n "$summary_line" ]; then
    passed=$(printf '%s\n' "$summary_line" | awk '{ for (i = 1; i <= NF; i++) if ($i == "passed,") { print $(i - 1); exit } }')
    failed=$(printf '%s\n' "$summary_line" | awk '{ for (i = 1; i <= NF; i++) if ($i == "failed") { print $(i - 1); exit } }')
    case $passed in '' | *[!0-9]*) ;; *)
      case $failed in '' | *[!0-9]*) ;; *)
        summary="$passed passed, $failed failed"
        ;;
      esac
      ;;
    esac
  fi

  if [ -n "$summary" ] && [ "$failed" -gt 0 ]; then
    printf 'harness: %s\n' "$summary"
    cases=$(failing_cases "$out")
    if [ -n "$cases" ]; then
      printf 'harness: failed case(s): %s\n' "$cases"
    fi
    if [ "$status" -ne 0 ]; then
      printf 'harness: nvim exited %s\n' "$status"
    fi
    exit 1
  fi

  if [ -z "$summary" ]; then
    printf 'harness: nvim exited %s before printing a summary\n' "$status"
    cases=$(failing_cases "$out")
    if [ -n "$cases" ]; then
      printf 'harness: failed case(s) before the summary: %s\n' "$cases"
    fi
    dump_raw "$out"
    dump_log "$log"
    exit 2
  fi

  if [ "$status" -ne 0 ]; then
    printf 'harness: nvim exited %s after %s passed, %s failed\n' "$status" "$passed" "$failed"
    printf 'harness: nvim exit-status anomaly, not a test failure (every test passed)\n'
    dump_raw "$out"
    dump_log "$log"
    exit 2
  fi

  exit 0
}

# --self-check: run this script against fixture output ("nvim") for each of the paths
# above, so the reporting is pinned without waiting for a real flake.
self_check() {
  tmp="${TMPDIR:-/tmp}/wiz-nvim-selfcheck.$$"
  if ! mkdir -p "$tmp"; then
    echo "self-check: cannot create $tmp"
    exit 2
  fi
  trap 'rm -rf "$tmp"' EXIT
  n=0
  bad=0

  # check NAME FIXTURE EXPECTED_STATUS EXPECTED_TEXT [UNEXPECTED_TEXT]
  check() {
    n=$((n + 1))
    fake=$tmp/nvim-$n
    cp "$2" "$fake" || exit 2
    chmod +x "$fake" || exit 2
    got=$(NVIM=$fake "$self" 2>&1)
    st=$?
    ok=1
    [ "$st" -eq "$3" ] || ok=0
    case $got in
      *"$4"*) ;;
      *) ok=0 ;;
    esac
    if [ -n "${5:-}" ]; then
      case $got in
        *"$5"*) ok=0 ;;
      esac
    fi
    if [ "$ok" -eq 1 ]; then
      printf 'self-check: ok %s\n' "$1"
    else
      bad=$((bad + 1))
      printf 'self-check: FAIL %s (exit %s, wanted %s and %s)\n' "$1" "$st" "$3" "$4"
      printf '%s\n' "$got" | sed 's/^/self-check: | /'
    fi
  }

  cat >"$tmp/pass" <<'EOF'
#!/bin/sh
printf '  … a case\r  ✓ a case\n24 passed, 0 failed\n'
exit 0
EOF

  cat >"$tmp/anomaly" <<'EOF'
#!/bin/sh
printf 'ERR 2026-01-01T00:00:00 loop_close:170: uv_loop_close() hang?\n' >> "$NVIM_LOG_FILE"
printf '  … a case\r  ✓ a case\n24 passed, 0 failed\n'
exit 1
EOF

  cat >"$tmp/failure" <<'EOF'
#!/bin/sh
printf '  ✓ a case\n  ✗ the broken case\n23 passed, 1 failed\n'
exit 1
EOF

  cat >"$tmp/failure-zero" <<'EOF'
#!/bin/sh
printf '  ✓ a case\n  ✗ the broken case\n23 passed, 1 failed\n'
exit 0
EOF

  cat >"$tmp/joined-failure" <<'EOF'
#!/bin/sh
printf 'wiz.nvim: a warning  ✗ a case printed over the warning\n23 passed, 1 failed\n'
exit 1
EOF

  cat >"$tmp/no-summary" <<'EOF'
#!/bin/sh
printf 'E5113: Lua chunk: boom\n'
exit 1
EOF

  cat >"$tmp/no-summary-zero" <<'EOF'
#!/bin/sh
printf 'nothing here\n'
exit 0
EOF

  cat >"$tmp/signal" <<'EOF'
#!/bin/sh
printf '  … a case\r'
kill -TERM $$
EOF

  check clean-pass "$tmp/pass" 0 '24 passed, 0 failed' 'harness:'
  check clean-summary-nonzero "$tmp/anomaly" 2 \
    'harness: nvim exited 1 after 24 passed, 0 failed'
  # the progress line is hidden from the filtered output but kept in the diagnostic
  check anomaly-keeps-progress "$tmp/anomaly" 2 'harness: |   … a case'
  check anomaly-prints-log "$tmp/anomaly" 2 'uv_loop_close() hang?'
  check anomaly-names-teardown "$tmp/anomaly" 2 \
    'harness: cause: nvim/libuv teardown could not close its event loop'
  check test-failure "$tmp/failure" 1 'harness: failed case(s): the broken case' \
    'harness: nvim exit-status anomaly'
  check test-failure-exit-zero "$tmp/failure-zero" 1 \
    'harness: failed case(s): the broken case' 'harness: nvim exit-status anomaly'
  check failure-after-message "$tmp/joined-failure" 1 \
    'harness: failed case(s): a case printed over the warning'
  check no-summary "$tmp/no-summary" 2 'harness: nvim exited 1 before printing a summary'
  check no-summary-zero "$tmp/no-summary-zero" 2 \
    'harness: nvim exited 0 before printing a summary'
  check killed "$tmp/signal" 2 'harness: nvim exited 143 before printing a summary'

  printf 'self-check: %d passed, %d failed\n' "$((n - bad))" "$bad"
  [ "$bad" -eq 0 ]
}

case "${1:-}" in
  --self-check) self_check ;;
  *) main "$@" ;;
esac
