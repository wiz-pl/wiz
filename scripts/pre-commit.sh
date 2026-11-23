#!/bin/sh
# The checks CI runs first, in one command, before a commit or a push.
#
#   scripts/pre-commit.sh --fast      docs style and links, the preludes' surface,
#                                     `wiz fmt` on changed files, the ledger fixtures,
#                                     the skip lint and `.github/` YAML
#   scripts/pre-commit.sh --full      the fast checks, then the trust ledger, the
#                                     reproducibility corpus and the formatter's tests
#   scripts/pre-commit.sh --staged    only the files in `git diff --cached` (the
#                                     pre-commit hook); combine with either tier
#   scripts/pre-commit.sh --self-test the tiers on a throwaway repository, and the hooks'
#                                     idempotence (exit 0 if the self-test passes)
#
# A check whose tool is missing (no `python3`, no PyYAML, no `wiz`, no test driver, no
# `cc`) is skipped, not failed, and says why: a contributor without a build still gets
# the checks that need nothing built. The last line is one summary line.
#
# Exit status: 0 clean (at least one check ran and none failed), 1 a real failure,
# 3 every check was skipped (so a hook can tell "nothing could run" from "all good").
# The hooks installed by scripts/install-hooks.sh treat 3 as success; a CI job can
# treat 3 as a missing toolchain.
#
# What it cannot check: the test suite (only the formatter group, in --full), generated
# C/LLVM beyond the reproducibility corpus, the docs site, the release workflows,
# sharding (`scripts/ci.py check-shards`), or behaviour on another OS/architecture. It
# is a fast local subset of CI, not a CI replacement.
set -u

root=
tier=fast
staged=0
selftest=0

usage() {
  sed -n '2,25p' "$0" | sed 's/^# \{0,1\}//'
}

while [ $# -gt 0 ]; do
  case $1 in
    --fast) tier=fast; shift ;;
    --full) tier=full; shift ;;
    --staged) staged=1; shift ;;
    --root) [ $# -ge 2 ] || { usage >&2; exit 2; }; root=$2; shift 2 ;;
    --root=*) root=${1#*=}; shift ;;
    --self-test) selftest=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "pre-commit: unknown argument $1" >&2; usage >&2; exit 2 ;;
  esac
done

# The checkout this script lives in, unless --root points at a fixture.
if [ -z "$root" ]; then
  root=$(cd "$(dirname "$0")/.." && pwd)
fi

# --- helpers -----------------------------------------------------------------------

now() { date +%s; }

total=0
passed=0
failed=0
skipped=0

pass_check() { # NAME
  total=$((total + 1)); passed=$((passed + 1))
  printf 'ok    %s\n' "$1"
}

skip_check() { # NAME REASON
  total=$((total + 1)); skipped=$((skipped + 1))
  printf 'skip  %s: %s\n' "$1" "$2"
}

fail_check() { # NAME LOG
  total=$((total + 1)); failed=$((failed + 1))
  printf 'FAIL  %s\n' "$1"
  sed 's/^/      /' "$2"
}

run_check() { # NAME COMMAND...
  _pc_name=$1
  shift
  _pc_log=$work/check.$((total + 1)).log
  if "$@" >"$_pc_log" 2>&1; then
    pass_check "$_pc_name"
  else
    fail_check "$_pc_name" "$_pc_log"
  fi
}

have() { command -v "$1" >/dev/null 2>&1; }

resolve_wiz() {
  if [ -n "${WIZ:-}" ]; then
    case $WIZ in
      */*) printf '%s' "$WIZ" ;;
      *) command -v "$WIZ" 2>/dev/null || printf '%s' "$WIZ" ;;
    esac
    return
  fi
  if [ -x "$root/.lake/build/bin/wiz" ]; then
    printf '%s' "$root/.lake/build/bin/wiz"
    return
  fi
  command -v wiz 2>/dev/null || true
}

resolve_tests() {
  if [ -n "${TESTS_BIN:-}" ]; then
    printf '%s' "$TESTS_BIN"
  elif [ -x "$root/.lake/build/bin/tests" ]; then
    printf '%s' "$root/.lake/build/bin/tests"
  fi
}

# The paths of the files this run is about: staged only, or everything on the branch
# plus the work tree (committed since the merge base with origin/master, unstaged,
# staged and untracked).
changed_files() {
  if ! git -C "$root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    return 0
  fi
  if [ "$staged" = 1 ]; then
    git -C "$root" diff --cached --name-only --diff-filter=ACMR 2>/dev/null
    return
  fi
  _pc_base=$(git -C "$root" merge-base HEAD origin/master 2>/dev/null || true)
  if [ -n "$_pc_base" ]; then
    git -C "$root" diff --name-only --diff-filter=ACMR "$_pc_base"...HEAD 2>/dev/null
  fi
  git -C "$root" diff --name-only --diff-filter=ACMR 2>/dev/null
  git -C "$root" diff --cached --name-only --diff-filter=ACMR 2>/dev/null
  git -C "$root" ls-files --others --exclude-standard 2>/dev/null
}

# --- the checks --------------------------------------------------------------------

check_docs_style() {
  python3 "$root/scripts/check-docs-style.py" --root "$root" --quiet
}

check_prelude_drift() {
  python3 "$root/scripts/check-prelude-drift.py" --root "$root" --quiet
}

check_doc_links() {
  python3 "$root/scripts/check-doc-links.py" --root "$root" --quiet
}

check_format() {
  _pc_bad=0
  while IFS= read -r _pc_file; do
    if ! "$wiz_bin" fmt --check "$root/$_pc_file"; then
      _pc_bad=$((_pc_bad + 1))
    fi
  done <"$work/wiz-files"
  [ "$_pc_bad" -eq 0 ]
}

check_yaml() {
  python3 - "$root" <<'PY'
import pathlib
import sys
import yaml

root = pathlib.Path(sys.argv[1])
files = sorted(p for p in (root / ".github").rglob("*")
               if p.suffix in (".yml", ".yaml") and p.is_file())
bad = 0
for path in files:
    try:
        list(yaml.safe_load_all(path.read_text(encoding="utf-8")))
    except Exception as exc:  # report the parser's own message
        print(f"{path.relative_to(root)}: {exc}")
        bad = 1
print(f"parsed {len(files)} YAML file(s) under .github/")
raise SystemExit(bad)
PY
}

check_trust_fixtures() {
  TESTS_BIN="$tests_bin" "$root/Tests/trust-ledger/run.sh"
}

check_host_unsafe() {
  python3 "$root/scripts/host-unsafe-ledger.py" --root "$root" --check &&
    "$root/Tests/host-unsafe-ledger/run.sh"
}

check_trust_ledger() {
  TESTS_BIN="$tests_bin" "$root/scripts/trust-ledger.sh" --check
}

check_repro() {
  WIZ="$wiz_bin" "$root/scripts/check-repro.sh"
}

pick_format_group() { # the group name; exit 1 if neither exists, 2 on a broken driver
  _pc_groups=$("$tests_bin" --list 2>"$work/list.err") || return 2
  printf '%s\n' "$_pc_groups" | grep -Fxq fmt && { printf '%s' fmt; return 0; }
  printf '%s\n' "$_pc_groups" | grep -Fxq format && { printf '%s' format; return 0; }
  return 1
}

# --- the self-test -----------------------------------------------------------------

# Run the tiers on a throwaway repository: a clean tree (exit 0), one docs-style
# violation (exit 1) and no tools at all (exit 3), then install the hooks twice and
# check they are idempotent and never overwrite a foreign hook without --force.
self_test() {
  if ! have python3; then
    echo "pre-commit self-test: skip (python3 not found)"
    return 3
  fi
  if ! have git; then
    echo "pre-commit self-test: skip (git not found)"
    return 3
  fi

  _st_tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-pre-commit-selftest.XXXXXX") || return 1
  trap 'rm -rf "$_st_tmp"' EXIT INT TERM
  _st_checks=0
  _st_bad=0
  _st_env=$(command -v env)

  _st_case() { # EXPECTED NAME COMMAND...
    _st_expected=$1
    _st_name=$2
    shift 2
    _st_checks=$((_st_checks + 1))
    if "$@" >"$_st_tmp/out" 2>&1; then
      _st_got=0
    else
      _st_got=$?
    fi
    if [ "$_st_got" -eq "$_st_expected" ]; then
      echo "ok   $_st_name (exit $_st_got)"
    else
      echo "FAIL $_st_name: expected exit $_st_expected, got $_st_got"
      sed 's/^/     /' "$_st_tmp/out"
      _st_bad=$((_st_bad + 1))
    fi
  }

  _st_repo=$_st_tmp/repo
  mkdir -p "$_st_repo/docs" "$_st_repo/.github/workflows"
  printf '# Fixture\n' >"$_st_repo/README.md"
  printf '# Fixture docs\n\nNothing to see.\n' >"$_st_repo/docs/index.md"
  printf 'name: fixture\non: [push]\n' >"$_st_repo/.github/workflows/ci.yml"
  printf 'def a := 1\n' >"$_st_repo/a.wiz"
  if [ -f "$root/.github/skip-allowlist.json" ]; then
    cp "$root/.github/skip-allowlist.json" "$_st_repo/.github/"
  else
    printf '{"groups": []}\n' >"$_st_repo/.github/skip-allowlist.json"
  fi
  ln -s "$root/scripts" "$_st_repo/scripts"
  ln -s "$root/Tests" "$_st_repo/Tests"
  git -C "$_st_repo" init -q

  _st_wiz=$_st_tmp/wiz-ok
  printf '#!/bin/sh\nexit 0\n' >"$_st_wiz"
  chmod +x "$_st_wiz"
  _st_missing=$_st_tmp/no-tests
  _st_script=$root/scripts/pre-commit.sh

  # A PATH with the shell tools and python3 but no wiz, cc or test driver, so the
  # built-tool checks skip identically on every machine (a machine's installed wiz
  # must not make this fixture run the real reproducibility corpus).
  _st_plain=$_st_tmp/plain-bin
  mkdir -p "$_st_plain"
  for _st_cmd in git dirname mktemp date rm sort cat sed grep uname python3; do
    _st_path=$(command -v "$_st_cmd" 2>/dev/null) && ln -s "$_st_path" "$_st_plain/$_st_cmd"
  done

  # fast: clean, then one real failure, then all skipped
  _st_case 0 "fast clean" \
    "$_st_env" -u WIZ -u TESTS_BIN PATH="$_st_plain" WIZ="$_st_wiz" TESTS_BIN="$_st_missing" \
    "$_st_script" --root "$_st_repo" --fast
  printf '\nSee `/workspace/elsewhere`.\n' >>"$_st_repo/docs/index.md"
  _st_case 1 "fast one failure" \
    "$_st_env" -u WIZ -u TESTS_BIN PATH="$_st_plain" WIZ="$_st_wiz" TESTS_BIN="$_st_missing" \
    "$_st_script" --root "$_st_repo" --fast
  printf '# Fixture docs\n\nNothing to see.\n' >"$_st_repo/docs/index.md"

  # the same two, plus --full (its built-tool checks skip here)
  _st_case 0 "full clean" \
    "$_st_env" -u WIZ -u TESTS_BIN PATH="$_st_plain" \
    "$_st_script" --root "$_st_repo" --full
  printf '\nSee `/workspace/elsewhere`.\n' >>"$_st_repo/docs/index.md"
  _st_case 1 "full one failure" \
    "$_st_env" -u WIZ -u TESTS_BIN PATH="$_st_plain" \
    "$_st_script" --root "$_st_repo" --full
  printf '# Fixture docs\n\nNothing to see.\n' >"$_st_repo/docs/index.md"

  # --staged sees the index, not the work tree
  git -C "$_st_repo" add a.wiz
  _st_case 0 "fast --staged" \
    "$_st_env" -u WIZ -u TESTS_BIN PATH="$_st_plain" WIZ="$_st_wiz" TESTS_BIN="$_st_missing" \
    "$_st_script" --root "$_st_repo" --fast --staged

  # no python3, wiz, cc or test driver on PATH: every check skips, exit 3
  _st_empty=$_st_tmp/empty-bin
  mkdir -p "$_st_empty"
  for _st_cmd in git dirname mktemp date rm sort cat sed grep uname; do
    _st_path=$(command -v "$_st_cmd" 2>/dev/null) && ln -s "$_st_path" "$_st_empty/$_st_cmd"
  done
  _st_case 3 "fast all skipped" \
    "$_st_env" -u WIZ -u TESTS_BIN PATH="$_st_empty" \
    "$_st_script" --root "$_st_repo" --fast
  _st_case 3 "full all skipped" \
    "$_st_env" -u WIZ -u TESTS_BIN PATH="$_st_empty" \
    "$_st_script" --root "$_st_repo" --full

  # the hooks: installed once, installed again byte-for-byte, and a foreign hook is
  # only replaced with --force
  _st_hooks=$_st_repo/.git/hooks
  _st_check() { # NAME COMMAND...
    _st_name=$1
    shift
    _st_checks=$((_st_checks + 1))
    if "$@" >"$_st_tmp/out" 2>&1; then
      echo "ok   $_st_name"
    else
      echo "FAIL $_st_name"
      sed 's/^/     /' "$_st_tmp/out"
      _st_bad=$((_st_bad + 1))
    fi
  }

  _st_install=$root/scripts/install-hooks.sh
  _st_check "hooks install" sh -c "cd '$_st_repo' && sh '$_st_install'"
  cp "$_st_hooks/pre-commit" "$_st_tmp/hook-pre-commit"
  cp "$_st_hooks/pre-push" "$_st_tmp/hook-pre-push"
  _st_check "hooks install is idempotent" sh -c "cd '$_st_repo' && sh '$_st_install'"
  _st_check "hooks are unchanged" \
    cmp "$_st_tmp/hook-pre-commit" "$_st_hooks/pre-commit"
  _st_check "pre-push is unchanged" \
    cmp "$_st_tmp/hook-pre-push" "$_st_hooks/pre-push"
  _st_check "pre-commit hook allows a skip-only run" \
    sh -c "cd '$_st_repo' && env PATH='$_st_empty' .git/hooks/pre-commit"

  printf '#!/bin/sh\n# someone else\x27s hook\nexit 0\n' >"$_st_hooks/pre-commit"
  _st_checks=$((_st_checks + 1))
  if sh -c "cd '$_st_repo' && sh '$_st_install'" >"$_st_tmp/out" 2>&1; then
    echo "FAIL foreign hook: install overwrote it without --force"
    _st_bad=$((_st_bad + 1))
  elif grep -Fxq "# someone else's hook" "$_st_hooks/pre-commit"; then
    echo "ok   foreign hook is kept without --force"
  else
    echo "FAIL foreign hook: its content changed"
    _st_bad=$((_st_bad + 1))
  fi
  _st_check "foreign hook is replaced with --force" \
    sh -c "cd '$_st_repo' && sh '$_st_install' --force"
  _st_check "forced hook matches the first install" \
    cmp "$_st_tmp/hook-pre-commit" "$_st_hooks/pre-commit"

  if [ "$_st_bad" -gt 0 ]; then
    echo "pre-commit self-test: FAIL ($_st_bad of $_st_checks checks failed)"
    return 1
  fi
  echo "pre-commit self-test: ok ($_st_checks checks)"
  return 0
}

# --- the run -----------------------------------------------------------------------

if [ "$selftest" = 1 ]; then
  self_test
  exit $?
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/wiz-pre-commit.XXXXXX") || {
  echo "pre-commit: cannot make a temp dir" >&2
  exit 1
}
trap 'rm -rf "$work"' EXIT INT TERM

start=$(now)
wiz_bin=$(resolve_wiz)
tests_bin=$(resolve_tests)

# `wiz fmt --check` landed after some installed toolchains: an older `wiz` on PATH is
# not a failure, it just cannot run this check. Probe once with an empty file.
wiz_fmt=0
if [ -n "$wiz_bin" ] && [ -x "$wiz_bin" ] &&
  "$wiz_bin" fmt --check /dev/null >/dev/null 2>&1; then
  wiz_fmt=1
fi

if [ "$staged" = 1 ]; then mode=staged; else mode=changed; fi

# The file-driven checks read this once.
changed_files >"$work/changed"
grep -E '\.wiz$' "$work/changed" >"$work/wiz-files" 2>/dev/null || : >"$work/wiz-files"

# docs style (no build: Python 3 standard library only)
if ! have python3; then
  skip_check "docs style" "python3 not found"
elif [ ! -f "$root/scripts/check-docs-style.py" ]; then
  skip_check "docs style" "scripts/check-docs-style.py is missing"
else
  run_check "docs style" check_docs_style
fi

# docs links and anchors (no build, no network: Python 3 standard library only)
if ! have python3; then
  skip_check "docs links" "python3 not found"
elif [ ! -f "$root/scripts/check-doc-links.py" ]; then
  skip_check "docs links" "scripts/check-doc-links.py is missing"
else
  run_check "docs links" check_doc_links
fi

# the self-hosted frontend's embedded prelude against lib/Prelude.wiz (no build:
# Python 3 standard library only; a checkout of the library and the frontend is needed)
if ! have python3; then
  skip_check "prelude drift" "python3 not found"
elif [ ! -f "$root/scripts/check-prelude-drift.py" ]; then
  skip_check "prelude drift" "scripts/check-prelude-drift.py is missing"
elif [ ! -f "$root/lib/Prelude.wiz" ] || [ ! -f "$root/selfhost/Frontend.wiz" ]; then
  skip_check "prelude drift" "not a full checkout (no lib/Prelude.wiz or selfhost/Frontend.wiz)"
else
  run_check "prelude drift" check_prelude_drift
fi

# wiz fmt --check, only the changed .wiz files (one file at a time)
if [ ! -s "$work/wiz-files" ]; then
  skip_check "wiz fmt" "no changed .wiz files"
elif [ -z "$wiz_bin" ] || [ ! -x "$wiz_bin" ]; then
  skip_check "wiz fmt" "wiz is not built (run 'lake build wiz' or set WIZ)"
elif [ "$wiz_fmt" = 0 ]; then
  skip_check "wiz fmt" "this wiz has no 'fmt --check' (build the checkout's wiz)"
else
  run_check "wiz fmt (changed files)" check_format
fi

# the trust ledger's fixture trees need only the test driver
if [ -z "$tests_bin" ] || [ ! -x "$tests_bin" ]; then
  skip_check "trust-ledger fixtures" "the test driver is not built (run 'lake build wiz tests')"
elif [ ! -x "$root/Tests/trust-ledger/run.sh" ]; then
  skip_check "trust-ledger fixtures" "Tests/trust-ledger/run.sh is missing"
else
  run_check "trust-ledger fixtures" check_trust_fixtures
fi

# the host-side unsafe ledger (the host Lean's `unsafe`/`implemented_by`/`extern`) and its
# fixtures: python3 only, no build
if ! have python3; then
  skip_check "host unsafe ledger" "python3 not found"
elif [ ! -f "$root/.github/host-unsafe.tsv" ] || [ ! -f "$root/scripts/host-unsafe-ledger.py" ]; then
  skip_check "host unsafe ledger" "no .github/host-unsafe.tsv in this tree"
else
  run_check "host unsafe ledger" check_host_unsafe
fi

# the skip lint's own rules (synthetic logs: no test run needed)
if ! have python3; then
  skip_check "skip lint self-test" "python3 not found"
elif [ ! -f "$root/scripts/ci.py" ]; then
  skip_check "skip lint self-test" "scripts/ci.py is missing"
else
  run_check "skip lint self-test" python3 "$root/scripts/ci.py" check-skips --self-test
fi

# check-repro's own rules, and its JSON reader, on synthetic input (no compiler needed)
if ! have python3; then
  skip_check "repro self-tests" "python3 not found"
elif [ ! -f "$root/scripts/check-repro.sh" ] || [ ! -f "$root/scripts/check-repro-report.py" ]; then
  skip_check "repro self-tests" "scripts/check-repro{,-report} is missing"
else
  run_check "repro self-tests" bash -c '"$1" --self-test && python3 "$2" --self-test' _ \
    "$root/scripts/check-repro.sh" "$root/scripts/check-repro-report.py"
fi

# every .github/*.yml parses (PyYAML is a dev tool, not a hard dependency)
if ! have python3; then
  skip_check "yaml (.github/)" "python3 not found"
elif ! python3 -c 'import yaml' >/dev/null 2>&1; then
  skip_check "yaml (.github/)" "the python3 yaml module (PyYAML) is not installed"
elif [ ! -d "$root/.github" ]; then
  skip_check "yaml (.github/)" ".github/ is missing"
else
  run_check "yaml (.github/)" check_yaml
fi

if [ "$tier" = full ]; then
  # the trusted base, as the build job runs it before any shard
  if [ -z "$tests_bin" ] || [ ! -x "$tests_bin" ]; then
    skip_check "trust ledger" "the test driver is not built (run 'lake build wiz tests')"
  elif [ ! -x "$root/scripts/trust-ledger.sh" ]; then
    skip_check "trust ledger" "scripts/trust-ledger.sh is missing"
  else
    run_check "trust ledger" check_trust_ledger
  fi

  # the reproducibility corpus: only when a compiler is built, and cc is available
  # (`check-repro.sh` builds the corpus programs)
  if [ -z "$wiz_bin" ] || [ ! -x "$wiz_bin" ]; then
    skip_check "reproducible builds" "the compiler is not built (run 'lake build wiz grail')"
  elif [ -z "${WIZ_CC:-}" ] && ! have cc; then
    skip_check "reproducible builds" "no C compiler (cc) on PATH"
  elif ! have sha256sum || ! have cmp; then
    skip_check "reproducible builds" "sha256sum or cmp is missing"
  elif [ ! -d "$root/Tests/ReproPaths" ]; then
    skip_check "reproducible builds" "Tests/ReproPaths is missing"
  else
    run_check "reproducible builds" check_repro
  fi

  # the formatter's test group (`fmt` when that branch has landed, else `format`)
  if [ -z "$tests_bin" ] || [ ! -x "$tests_bin" ]; then
    skip_check "formatter tests" "the test driver is not built (run 'lake build wiz tests')"
  else
    _pc_group=$(pick_format_group)
    _pc_rc=$?
    if [ "$_pc_rc" -eq 0 ]; then
      run_check "formatter tests (=$_pc_group)" "$tests_bin" "=$_pc_group"
    elif [ "$_pc_rc" -eq 1 ]; then
      skip_check "formatter tests" "the suite has no fmt/format group"
    else
      fail_check "formatter tests" "$work/list.err"
    fi
  fi
fi

elapsed=$(( $(now) - start ))
if [ "$failed" -gt 0 ]; then
  printf 'pre-commit: %s (%s): FAIL, %d ok, %d failed, %d skipped, %ds\n' \
    "$tier" "$mode" "$passed" "$failed" "$skipped" "$elapsed"
  exit 1
fi
if [ "$passed" -eq 0 ]; then
  printf 'pre-commit: %s (%s): SKIP, all %d checks skipped (no tool available), %ds\n' \
    "$tier" "$mode" "$skipped" "$elapsed"
  exit 3
fi
printf 'pre-commit: %s (%s): ok, %d passed, %d skipped, %ds\n' \
  "$tier" "$mode" "$passed" "$skipped" "$elapsed"
exit 0
