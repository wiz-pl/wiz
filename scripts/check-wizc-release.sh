#!/usr/bin/env bash
# The packed wizc's behavioural gate (R1) and the seed pin (R2).
#
#   scripts/check-wizc-release.sh --tarball FILE [--seed DIR] [--out DIR]
#   scripts/check-wizc-release.sh --write-pin --seed DIR
#   scripts/check-wizc-release.sh --self-test
#
# `wizc` is the chain's release: a static executable that reads `input.wiz` in its
# working directory and prints C (docs/bootstrap-chain.md, "Terms"). Every chain check
# today compares C text, executable bytes or a tarball hash for the *one* input
# `self.wiz`; a compiler that quines `self.wiz` and miscompiles everything else passes
# them all. This gate is the second input:
#
#   1. the seed pin (R2): scripts/wizc-seed.json holds the sha256 of the assembled
#      `self.wiz`, the seed's `seed.c` (C*), and the checked-in chain inputs
#      (`selfhost/Tables.wiz`, `selfhost/rt.c`). A mismatch prints the file and both
#      hashes; a reviewed update is `--write-pin --seed DIR`.
#   2. the behaviour (R1): extract the packed tarball, run its `bin/wizc` on a frozen
#      program with a known stdout, compile the C it prints with that same runtime, run
#      it and compare every line. A one-byte change to the program must change the
#      output; if it does not, the fixture does not distinguish the programs and this
#      gate fails rather than passing on a comparison that cannot see anything.
#
# Exit codes: 0 pass, 1 the gate failed (a mismatch is printed), 2 usage, 3 skip (no
# tarball/seed input; not a pass). The release and chain jobs pass --tarball and
# --seed, so the skip path is only for a hand run.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
pin=$root/scripts/wizc-seed.json
fixture=$here/fixtures/wizc-release/accept.wiz
expected=$here/fixtures/wizc-release/accept.out
tarball=""
seed=""
out=""
cc=${CC:-cc}
mode="--rc"
write_pin=0
self_test=0
self_test_mode=all
extra_cc=()

usage() {
  sed -n '2,/^set -uo/p' "$0" | sed '$d; s/^# \{0,1\}//'
  cat <<'EOF'

Options:
  --tarball FILE  the packed release (wizc-SYSTEM.tar.gz, from `nix build .#wizc-release`)
  --seed DIR      the `.#wizc-seed` output (self.wiz, seed.c); required for the pin
  --out DIR       scratch directory (default: a temporary directory)
  --fixture FILE  the program (default: scripts/fixtures/wizc-release/accept.wiz)
  --expect FILE   its expected stdout (default: .../accept.out)
  --cc CMD        the C compiler (default: $CC or cc)
  --gc            the tarball was built in collector mode (adds the GC flags)
  --write-pin     rewrite scripts/wizc-seed.json from --seed (review the diff!)
  --self-test     exercise the gate on a fake tarball, a one-byte mutation and a
                  wrong pin (no compiler, no release needed)
  --self-test-behaviour  only the R1 checks (the fixture and the one-byte control)
  --self-test-pin        only the R2 check (a changed seed file names both hashes)
  -h, --help      this text
EOF
}

die() { echo "check-wizc-release: $*" >&2; exit 2; }
fail() { echo "check-wizc-release: FAIL: $*" >&2; return 1; }

# ---------------------------------------------------------------- the seed pin ---

# Print "path<TAB>source<TAB>sha256" for each pin entry.
pin_rows() {
  python3 - "$1" <<'PY'
import json, sys
with open(sys.argv[1]) as f:
    p = json.load(f)
if p.get("format") != "wizc-seed/1":
    print(f"{sys.argv[1]}: not a wizc-seed/1 file", file=sys.stderr)
    raise SystemExit(2)
for e in p["files"]:
    print(f'{e["path"]}\t{e["from"]}\t{e["sha256"]}')
PY
}

check_pin() {
  [ -f "$pin" ] || { fail "no seed pin at $pin"; return 1; }
  local rc=0 path from want f got rows
  rows=$(pin_rows "$pin") || return 1
  while IFS=$'\t' read -r path from want; do
    [ -n "$path" ] || continue
    case $from in
      seed) f=$seed/$path ;;
      checkout) f=$root/$path ;;
      *) fail "seed pin: $path has an unknown source '$from'"; rc=1; continue ;;
    esac
    if [ -z "$seed" ] && [ "$from" = seed ]; then
      echo "check-wizc-release: seed pin: $path needs --seed DIR (the .#wizc-seed output)" >&2
      rc=1
      continue
    fi
    if [ ! -f "$f" ]; then
      fail "seed pin: $path is missing (looked for $f)"
      rc=1
      continue
    fi
    got=$(sha256sum "$f" | cut -d' ' -f1)
    if [ "$got" != "$want" ]; then
      echo "check-wizc-release: FAIL: seed pin: $path" >&2
      echo "  pinned    $want" >&2
      echo "  actual    $got" >&2
      echo "  file      $f" >&2
      echo "  the chain's input or its fixpoint C changed: review it, then" >&2
      echo "  scripts/check-wizc-release.sh --write-pin --seed DIR" >&2
      rc=1
    else
      echo "ok      seed $path $got"
    fi
  done <<< "$rows"
  [ "$rc" -eq 0 ] || return 1
  echo "check-wizc-release: the seed pin matches ($(printf '%s\n' "$rows" | grep -c . ) files)"
}

write_pin() {
  [ -n "$seed" ] || die "--write-pin needs --seed DIR"
  local tmp f got sep=""
  tmp=$(mktemp "${TMPDIR:-/tmp}/wizc-seed.XXXXXX") || return 2
  {
    printf '{\n'
    printf '  "format": "wizc-seed/1",\n'
    printf '  "note": "The chain seed inputs, pinned by scripts/check-wizc-release.sh (R2). self.wiz is the assembled toolchain source; the rest are its checked-in inputs. seed.c is an output of the Lean host, not an input: the behavioural gate checks the packed wizc itself. Regenerate with --write-pin --seed DIR and review the diff.",\n'
    printf '  "files": [\n'
    for f in self.wiz; do
      [ -f "$seed/$f" ] || { rm -f "$tmp"; die "--seed is missing $f"; }
      got=$(sha256sum "$seed/$f" | cut -d' ' -f1)
      printf '%s    {"path": "%s", "from": "seed", "sha256": "%s"}' "$sep" "$f" "$got"
      sep=$',\n'
    done
    for f in selfhost/Tables.wiz selfhost/rt.c Wiz/Selfhost.lean Wiz/Version.lean; do
      [ -f "$root/$f" ] || { rm -f "$tmp"; die "missing $f"; }
      got=$(sha256sum "$root/$f" | cut -d' ' -f1)
      printf '%s    {"path": "%s", "from": "checkout", "sha256": "%s"}' "$sep" "$f" "$got"
      sep=$',\n'
    done
    printf '\n  ]\n}\n'
  } > "$tmp"
  mv "$tmp" "$pin"
  echo "check-wizc-release: wrote $pin"
  cat "$pin"
}

# ---------------------------------------------------------------- the behaviour ---

# Compile and run one program with the packed wizc; print its stdout.
run_program() { # SRC DIR -> stdout on stdout, diagnostics on stderr
  local src=$1 dir=$2
  mkdir -p "$dir"
  cp "$src" "$dir/input.wiz"
  ( cd "$dir" && "$wizc" "$mode" > out.c ) || {
    echo "check-wizc-release: wizc failed on $src" >&2
    sed -n '1,20p' "$dir/out.c" >&2 2>/dev/null || true
    return 1
  }
  "$cc" -O2 -w -I "$root/selfhost" ${extra_cc[@]+"${extra_cc[@]}"} "$dir/out.c" -o "$dir/prog" || {
    echo "check-wizc-release: the C compiler failed on the C wizc printed for $src" >&2
    return 1
  }
  ( cd "$dir" && ./prog )
}

# The first digit in a code line, changed: a one-byte edit that changes what a correct
# compiler prints. Comment lines are skipped (changing a comment changes no behaviour).
mutate_one_byte() { # SRC DST
  python3 - "$1" "$2" <<'PY'
import sys
lines = open(sys.argv[1], "rb").read().split(b"\n")
for i, line in enumerate(lines):
    if line.lstrip().startswith(b"--"):
        continue
    for j, c in enumerate(line):
        if 0x30 <= c <= 0x39:
            lines[i] = line[:j] + bytes([0x31 if c != 0x31 else 0x32]) + line[j + 1:]
            open(sys.argv[2], "wb").write(b"\n".join(lines))
            raise SystemExit(0)
raise SystemExit("the fixture has no digit in a code line to change")
PY
}

check_behaviour() {
  [ -n "$tarball" ] || die "no --tarball (a packed release is needed)"
  [ -f "$tarball" ] || die "no such tarball: $tarball"
  [ -f "$fixture" ] || die "no fixture: $fixture"
  [ -f "$expected" ] || die "no expected output: $expected"
  local dir=${out:-$(mktemp -d "${TMPDIR:-/tmp}/wizc-release.XXXXXX")}
  mkdir -p "$dir"
  tar -xzf "$tarball" -C "$dir" || { fail "cannot unpack $tarball"; return 1; }
  wizc=$(find "$dir" -type f -path '*/bin/wizc' | head -1)
  [ -n "$wizc" ] || { fail "the tarball has no */bin/wizc"; return 1; }
  chmod +x "$wizc" 2>/dev/null || true
  echo "== the packed wizc: $wizc"

  local got rc=0
  if ! got=$(run_program "$fixture" "$dir/good"); then
    fail "the packed wizc did not compile and run $fixture"; return 1
  fi
  printf '%s\n' "$got" > "$dir/good/out.txt"
  if ! diff -u "$expected" "$dir/good/out.txt"; then
    fail "the packed wizc's stdout is not the fixture's known answer"
    rc=1
  else
    echo "ok      behaviour: $(basename "$fixture") printed $(wc -l < "$expected") known lines"
  fi

  # The negative: one byte of the program changes, the expected answer does not, so a
  # gate that compares must fail. If it still passes, the comparison is blind.
  mutate_one_byte "$fixture" "$dir/mutated.wiz" || { fail "cannot mutate the fixture"; return 1; }
  if ! got=$(run_program "$dir/mutated.wiz" "$dir/mutated"); then
    echo "ok      negative: the one-byte variant does not compile (also a visible change)"
  else
    printf '%s\n' "$got" > "$dir/mutated/out.txt"
    if diff -q "$expected" "$dir/mutated/out.txt" >/dev/null 2>&1; then
      fail "the one-byte variant still prints the known answer: this fixture cannot see a miscompile"
      rc=1
    else
      echo "ok      negative: the one-byte variant prints a different answer (the gate can see it)"
    fi
  fi
  return "$rc"
}

# ---------------------------------------------------------------- the self-test ---

self_test() {
  local mode=${1:-all}
  local d rc=0
  d=$(mktemp -d "${TMPDIR:-/tmp}/wizc-release-test.XXXXXX") || return 2
  # shellcheck disable=SC2064
  trap "rm -rf '$d'" RETURN
  mkdir -p "$d/repo/selfhost" "$d/repo/scripts" "$d/seed" "$d/tar/wizc-test/bin" "$d/tar/wizc-blind/bin"
  : > "$d/repo/selfhost/rt.c"
  : > "$d/repo/selfhost/Tables.wiz"
  printf 'self.wiz bytes\n' > "$d/seed/self.wiz"
  printf 'seed.c bytes\n' > "$d/seed/seed.c"

  # a fake compiler that reads the three `def … : Nat := N` lines and prints them
  cat > "$d/tar/wizc-test/bin/wizc" <<'EOF'
#!/bin/sh
set --
for v in a b c; do
  n=$(sed -n "s/^def $v : Nat := //p" input.wiz)
  [ -n "$n" ] || { echo "no def $v" >&2; exit 1; }
  set -- "$@" "$n"
done
printf '#include <stdio.h>\nint main(void){puts("%s");puts("%s");puts("%s");return 0;}\n' "$1" "$2" "$3"
EOF
  # a compiler that ignores its input: the negative must catch it
  cat > "$d/tar/wizc-blind/bin/wizc" <<'EOF'
#!/bin/sh
printf '#include <stdio.h>\nint main(void){puts("5050");puts("60");puts("6");return 0;}\n'
EOF
  chmod +x "$d/tar/wizc-test/bin/wizc" "$d/tar/wizc-blind/bin/wizc"
  # a fake C compiler: the self-test needs no real one (CI has one for the real gate)
  cat > "$d/fakecc" <<'EOF'
#!/usr/bin/env python3
import re, sys
src, out = None, "prog"
a = sys.argv[1:]
for i, x in enumerate(a):
    if x == "-o" and i + 1 < len(a):
        out = a[i + 1]
    elif x.endswith(".c"):
        src = x
text = open(src).read()
with open(out, "w") as f:
    f.write("#!/bin/sh\n")
    for m in re.finditer(r'puts\("([^"]*)"\)', text):
        f.write('printf "%s\\n"\n' % m.group(1))
import os
os.chmod(out, 0o755)
EOF
  chmod +x "$d/fakecc"
  tar -czf "$d/tar/wizc-test.tar.gz" -C "$d/tar" wizc-test
  tar -czf "$d/tar/wizc-blind.tar.gz" -C "$d/tar" wizc-blind
  printf 'def a : Nat := 5050\ndef b : Nat := 60\ndef c : Nat := 6\ndef main : IO Unit := ()\n' > "$d/accept.wiz"
  printf '5050\n60\n6\n' > "$d/accept.out"

  # the pin for the fixture seed
  local p
  p=$d/pin.json
  {
    printf '{"format": "wizc-seed/1", "files": ['
    printf '{"path": "self.wiz", "from": "seed", "sha256": "%s"},' "$(sha256sum "$d/seed/self.wiz" | cut -d' ' -f1)"
    printf '{"path": "seed.c", "from": "seed", "sha256": "%s"},' "$(sha256sum "$d/seed/seed.c" | cut -d' ' -f1)"
    printf '{"path": "selfhost/Tables.wiz", "from": "checkout", "sha256": "%s"},' "$(sha256sum "$d/repo/selfhost/Tables.wiz" | cut -d' ' -f1)"
    printf '{"path": "selfhost/rt.c", "from": "checkout", "sha256": "%s"}]}\n' "$(sha256sum "$d/repo/selfhost/rt.c" | cut -d' ' -f1)"
  } > "$p"

  run() { # WANT NAME ARGS...
    local want=$1 name=$2 got=0
    shift 2
    out=$("$self" "$@" --pin-override "$p" --repo-override "$d/repo" 2>&1) || got=$?
    if [ "$got" -eq "$want" ]; then
      printf '  ok    %s (exit %d)\n' "$name" "$got"
    else
      printf '  FAIL  %s: wanted exit %d, got %d\n%s\n' "$name" "$want" "$got" "$out"
      rc=1
    fi
  }

  printf '\nself-test (fixtures under %s):\n' "$d"
  if [ "$mode" = all ] || [ "$mode" = behaviour ]; then
    run 0 "the gate passes the fake release and the pin" \
      --tarball "$d/tar/wizc-test.tar.gz" --seed "$d/seed" \
      --fixture "$d/accept.wiz" --expect "$d/accept.out" --cc "$d/fakecc"
    # a wrong expected answer fails the comparison (the check is not vacuous)
    printf '5150\n60\n6\n' > "$d/wrong.out"
    run 1 "a wrong expected answer fails the comparison" \
      --tarball "$d/tar/wizc-test.tar.gz" --seed "$d/seed" \
      --fixture "$d/accept.wiz" --expect "$d/wrong.out" --cc "$d/fakecc"
    # the blind compiler passes the mutated program too; the one-byte control must fail
    run 1 "a compiler that ignores its input is caught by the negative" \
      --tarball "$d/tar/wizc-blind.tar.gz" --seed "$d/seed" \
      --fixture "$d/accept.wiz" --expect "$d/accept.out" --cc "$d/fakecc"
  fi
  if [ "$mode" = all ] || [ "$mode" = pin ]; then
    # the seed pin: one byte of seed.c moved
    printf 'seed.C bytes\n' > "$d/seed/seed.c"
    run 1 "a changed seed.c fails, naming the file and both hashes" \
      --tarball "$d/tar/wizc-test.tar.gz" --seed "$d/seed" \
      --fixture "$d/accept.wiz" --expect "$d/accept.out" --cc "$d/fakecc"
  fi
  if [ "$rc" -eq 0 ]; then echo "self-test: ok"; else echo "self-test: FAILED" >&2; fi
  return "$rc"
}

# ---------------------------------------------------------------- the command line ---

self=$here/$(basename "$0")
# (the self-test runs this script recursively; these overrides keep the fixtures out
# of the checkout's own pin and runtime)
pin_override=""; repo_override=""
while [ $# -gt 0 ]; do
  case $1 in
    --tarball) tarball=$2; shift 2 ;;
    --seed) seed=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    --fixture) fixture=$2; shift 2 ;;
    --expect) expected=$2; shift 2 ;;
    --cc) cc=$2; shift 2 ;;
    --pin-override) pin=$2; shift 2 ;;
    --repo-override) root=$2; shift 2 ;;
    --gc) mode="--gc"; extra_cc+=(-lgc -lpthread); shift ;;
    --write-pin) write_pin=1; shift ;;
    --self-test) self_test=1; self_test_mode=all; shift ;;
    --self-test-behaviour) self_test=1; self_test_mode=behaviour; shift ;;
    --self-test-pin) self_test=1; self_test_mode=pin; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "check-wizc-release: unknown argument $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [ "$self_test" -eq 1 ]; then self_test "$self_test_mode"; exit $?; fi
if [ "$write_pin" -eq 1 ]; then write_pin; exit $?; fi
if [ -z "$tarball" ]; then
  echo "check-wizc-release: skip: no --tarball (a packed wizc is needed; this is not a pass)" >&2
  exit 3
fi
check_pin || exit 1
check_behaviour || exit 1
echo "check-wizc-release: PASS"
