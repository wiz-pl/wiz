#!/usr/bin/env bash
# The devShell's WIZ_* toolchain environment, in one place.
#
# flake.nix's devShell shellHook exports the GMP, GC and LLVM paths and flags that
# `wiz build`, `grail` and the fixpoint's C stages use. `nix develop` runs that hook,
# but `nix develop --command` (CI's default shell) does not export its values: the
# scheduled fixpoint of 2026-11-16 died at `scripts/fixpoint.sh: line 58:
# WIZ_GC_CFLAGS: ...` before it compiled anything.
#
# This script resolves the same five variables once, for every consumer:
#
#   1. the current environment, when the four the fixpoint expands are non-empty;
#   2. `grail.local.wiz`, the file flake.nix's shellHook writes at the repository root;
#   3. `nix build .#wiz-env`, the flake output generated from the same `toolchain`
#      binding as the shellHook.
#
#   usage (from the repository root):
#     eval "$(scripts/wiz-env.sh)"   # export the variables in this shell
#     scripts/wiz-env.sh             # print the export lines instead
#     scripts/wiz-env.sh --check     # only check the current environment: exit 2 and
#                                    # name every absent variable (CI's guard)
#     scripts/wiz-env.sh --from FILE # read FILE (a grail.local.wiz); no nix fallback
#     scripts/wiz-env.sh --self-test # fixtures and the error paths; no build
#
# A missing variable is an error, not an empty flag: `cc` would otherwise compile
# without GMP's or GC's include paths and fail later with a C error that does not name
# the environment.
#
# Exit status: 0 ok, 1 the environment cannot be resolved, 2 a required variable is
# absent (or a usage error).
set -euo pipefail

# What scripts/fixpoint.sh expands. WIZ_LLC is exported when known (grail and the
# reproducibility check use it), but the fixpoint compiles C with `cc`, not LLVM.
required=(WIZ_CFLAGS WIZ_LDFLAGS WIZ_GC_CFLAGS WIZ_GC_LDFLAGS)
known=(WIZ_CFLAGS WIZ_LDFLAGS WIZ_LLC WIZ_GC_CFLAGS WIZ_GC_LDFLAGS)

me=wiz-env
die() { echo "$me: $*" >&2; exit 1; }
usage() { sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; }

# One name per line, always exit 0 (callers run under `set -e`).
missing_vars() {
  local v
  for v in "${required[@]}"; do
    [ -n "${!v:-}" ] || printf '%s\n' "$v"
  done
  return 0
}

missing_list() { missing_vars | tr '\n' ' ' | sed 's/ $//'; }

emit() {
  local v
  for v in "${known[@]}"; do
    [ -n "${!v:-}" ] || continue
    printf 'export %s=%q\n' "$v" "${!v}"
  done
}

check_env() {
  local missing
  missing=$(missing_list)
  if [ -n "$missing" ]; then
    echo "$me: the toolchain environment is incomplete; missing: $missing" >&2
    echo "$me: run in 'nix develop', or 'eval \"\$(scripts/wiz-env.sh)\"' to read the devShell's values" >&2
    exit 2
  fi
}

# read_file FILE: set the WIZ_* variables from a grail.local.wiz; return 1 (after
# naming the problem) when the file is incomplete or has an unknown setting.
read_file() {
  local file=$1 key val
  [ -f "$file" ] || { echo "$me: $file: not a file" >&2; return 1; }
  while IFS=$'\t' read -r key val; do
    case "$key" in
      cflags) WIZ_CFLAGS=$val ;;
      ldflags) WIZ_LDFLAGS=$val ;;
      llc) WIZ_LLC=$val ;;
      gc-cflags) WIZ_GC_CFLAGS=$val ;;
      gc-ldflags) WIZ_GC_LDFLAGS=$val ;;
      *) echo "$me: $file: unknown toolchain setting '$key'" >&2; return 1 ;;
    esac
  done < <(sed -n 's/.*Settings\.set "\([^"]*\)" "\([^"]*\)".*/\1\t\2/p' "$file")
  local missing
  missing=$(missing_list)
  if [ -n "$missing" ]; then
    echo "$me: $file does not define: $missing" >&2
    return 1
  fi
}

self_test() {
  local script out all_env
  script=$(cd "$(dirname "$0")" && pwd)/$(basename "$0")
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-env-test.XXXXXX") # global: the EXIT trap reads it
  trap 'rm -rf "$tmp"' EXIT
  all_env=(env -u WIZ_CFLAGS -u WIZ_LDFLAGS -u WIZ_LLC -u WIZ_GC_CFLAGS -u WIZ_GC_LDFLAGS)
  local failed=0

  ok() { printf 'ok   %s\n' "$1"; }
  bad() { printf 'FAIL %s\n' "$1" >&2; failed=1; }

  cat > "$tmp/complete.wiz" <<'EOF'
import Grail
def settings : Settings := Settings.empty
  |> Settings.set "cflags" "-I/fixture/gmp/include"
  |> Settings.set "ldflags" "-L/fixture/gmp/lib"
  |> Settings.set "llc" "/fixture/llvm/bin/llc"
  |> Settings.set "gc-cflags" "-I/fixture/gc/include"
  |> Settings.set "gc-ldflags" "-L/fixture/gc/lib -lgc -lpthread"
EOF
  if out=$("${all_env[@]}" "$script" --from "$tmp/complete.wiz" 2>&1); then
    if ( eval "$out"; [ "$WIZ_GC_CFLAGS" = "-I/fixture/gc/include" ] &&
         [ "$WIZ_GC_LDFLAGS" = "-L/fixture/gc/lib -lgc -lpthread" ] &&
         [ "$WIZ_LLC" = "/fixture/llvm/bin/llc" ] ); then
      ok "a complete grail.local.wiz round-trips"
    else
      bad "a complete grail.local.wiz round-trips"
    fi
  else
    bad "a complete grail.local.wiz round-trips (exit $?)"
  fi

  sed '/gc-cflags/d' "$tmp/complete.wiz" > "$tmp/no-gc-cflags.wiz"
  if out=$("${all_env[@]}" "$script" --from "$tmp/no-gc-cflags.wiz" 2>&1); then
    bad "a file without gc-cflags is rejected"
  elif printf '%s\n' "$out" | grep -q WIZ_GC_CFLAGS; then
    ok "a file without gc-cflags names WIZ_GC_CFLAGS"
  else
    bad "a file without gc-cflags names WIZ_GC_CFLAGS"
  fi

  if out=$("${all_env[@]}" WIZ_CFLAGS=-I/c WIZ_LDFLAGS=-L/c \
             WIZ_GC_CFLAGS=-I/gc WIZ_GC_LDFLAGS=-lgc "$script" --check 2>&1); then
    ok "--check accepts the four required variables"
  else
    bad "--check accepts the four required variables (exit $?)"
  fi

  if out=$("${all_env[@]}" WIZ_CFLAGS=-I/c WIZ_LDFLAGS=-L/c \
             WIZ_GC_LDFLAGS=-lgc "$script" --check 2>&1); then
    bad "--check rejects an absent WIZ_GC_CFLAGS"
  elif [ $? -eq 2 ] && printf '%s\n' "$out" | grep -q WIZ_GC_CFLAGS; then
    ok "--check rejects an absent WIZ_GC_CFLAGS and names it (exit 2)"
  else
    bad "--check rejects an absent WIZ_GC_CFLAGS and names it (exit 2)"
  fi

  if out=$("${all_env[@]}" WIZ_CFLAGS=-I/env WIZ_LDFLAGS=-L/env WIZ_LLC=/env/llc \
             WIZ_GC_CFLAGS=-I/env/gc WIZ_GC_LDFLAGS=-L/env/gc "$script" 2>&1); then
    if ( eval "$out"; [ "$WIZ_CFLAGS" = "-I/env" ] && [ "$WIZ_LLC" = "/env/llc" ] ); then
      ok "a complete environment is used unchanged"
    else
      bad "a complete environment is used unchanged"
    fi
  else
    bad "a complete environment is used unchanged (exit $?)"
  fi

  printf '%s\n' 'def settings : Settings := Settings.empty' > "$tmp/empty.wiz"
  if out=$("${all_env[@]}" "$script" --from "$tmp/empty.wiz" 2>&1); then
    bad "an empty file is rejected"
  elif printf '%s\n' "$out" | grep -q 'does not define'; then
    ok "an empty file is rejected"
  else
    bad "an empty file is rejected"
  fi

  if [ "$failed" -ne 0 ]; then
    echo "$me: --self-test: FAIL" >&2
    return 1
  fi
  echo "$me: --self-test: PASS (6 checks)"
}

case "${1:-}" in
  -h|--help) usage; exit 0 ;;
  --check) check_env; exit 0 ;;
  --self-test) [ $# -eq 1 ] || die "--self-test takes no arguments"; self_test; exit $? ;;
  --from)
    [ $# -eq 2 ] || die "--from needs one file"
    read_file "$2" || exit 1
    emit
    exit 0
    ;;
  '') ;;
  *) die "unknown option: $1 (try --help)" ;;
esac

# 1. The environment a dev shell or a caller already exported.
if [ -z "$(missing_list)" ]; then
  emit
  exit 0
fi

root=$(cd "$(dirname "$0")/.." && pwd)

# 2. The file the shellHook writes. It is a cache, not a source: a stale or partial
# file falls through to the flake output below, which is generated from flake.nix.
if [ -f "$root/grail.local.wiz" ]; then
  if read_file "$root/grail.local.wiz"; then
    emit
    exit 0
  fi
  echo "$me: $root/grail.local.wiz is incomplete; asking nix for .#wiz-env" >&2
fi

# 3. The flake output generated from the same `toolchain` binding as the shellHook.
command -v nix >/dev/null 2>&1 || \
  die "cannot resolve the toolchain environment: no WIZ_* variables, no $root/grail.local.wiz, and no nix on PATH"
err=$(mktemp "${TMPDIR:-/tmp}/wiz-env.XXXXXX")
trap 'rm -f "$err"' EXIT
if ! out=$(nix build --no-link --print-out-paths "$root#wiz-env" 2>"$err"); then
  echo "$me: 'nix build .#wiz-env' failed; this checkout must expose packages.wiz-env" >&2
  sed 's/^/  nix: /' "$err" >&2
  exit 1
fi
env_file=$(printf '%s\n' "$out" | head -n 1)
[ -f "$env_file" ] || die "nix build printed '$env_file', which is not a file"
# shellcheck disable=SC1090
. "$env_file"
missing=$(missing_list)
[ -z "$missing" ] || die "$env_file does not define: $missing"
emit
