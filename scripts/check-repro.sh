#!/usr/bin/env bash
# Do the same build under two absolute paths, with different PWD, HOME, TMPDIR, umask,
# locale, SOURCE_DATE_EPOCH, thread count (-j) and cache directories, and compare the
# bytes. The corpus is Tests/ReproPaths (a few small programs, a link_c shim, a --split
# build and a grail package); the compiler is built twice when --compiler is given.
#
#   scripts/check-repro.sh                 corpus only, using .lake/build/bin/wiz
#   scripts/check-repro.sh --json          the same, one JSON object on stdout
#   scripts/check-repro.sh --compiler      also build wiz and grail under /tmp/a and
#                                          /tmp/b and compare the binaries and .olean
#                                          files (slow: two full Lake builds)
#   scripts/check-repro.sh --compiler-a DIR --compiler-b DIR
#                                          compare two compiler builds that already exist
#
# Nothing is pushed or installed; the two roots are under $TMPDIR and are removed unless
# --keep is given. The script skips cleanly (exit 0, status "skip") when the compiler is
# not built: run `lake build wiz grail` first, or pass --wiz PATH.
#
# Compared per root: generated C and executables (single, --split, --llvm, -g), the
# .grail build tree and binaries, and the elaboration cache entries (file names and
# contents, not the bin/ memo, whose name is the executable's path). Windows and
# timestamps are not compared; this is about bytes in artifacts. Diagnostics are not
# compared: an error legitimately prints the path it was given.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

wiz=${WIZ:-$root/.lake/build/bin/wiz}
grail=${GRAIL:-$root/.lake/build/bin/grail}
corpus=${REPRO_CORPUS:-$root/Tests/ReproPaths}
json=0
keep=0
build_compiler=0
compiler_a=
compiler_b=
compiler_olean=0
verbose=0

usage() {
  sed -n '2,28p' "$0" | sed 's/^# \{0,1\}//'
  cat <<'EOF'

Options:
  --json                    print one JSON result object on stdout (logs stay on stderr)
  --compiler                build the compiler under two paths first
  --compiler-a DIR          an existing compiler build (with .lake/build/bin/wiz)
  --compiler-b DIR          the other existing compiler build
  --compiler-olean          also compare .olean files (Lean stores the absolute source
                            path in them, so they differ between two roots by design)
  --wiz PATH                the wiz used for the corpus (default $WIZ or .lake/build/bin/wiz)
  --grail PATH              the grail used for the corpus (default $GRAIL or .lake/build/bin/grail)
  --corpus DIR              the corpus (default Tests/ReproPaths)
  --keep                    keep the two roots and print their paths
  --verbose                 echo build commands
  -h, --help                this text
EOF
}

while [ $# -gt 0 ]; do
  case $1 in
    --json) json=1; shift ;;
    --compiler) build_compiler=1; shift ;;
    --compiler-a) [ $# -ge 2 ] || { usage; exit 2; }; compiler_a=$2; shift 2 ;;
    --compiler-a=*) compiler_a=${1#*=}; shift ;;
    --compiler-b) [ $# -ge 2 ] || { usage; exit 2; }; compiler_b=$2; shift 2 ;;
    --compiler-b=*) compiler_b=${1#*=}; shift ;;
    --compiler-olean) compiler_olean=1; shift ;;
    --wiz) [ $# -ge 2 ] || { usage; exit 2; }; wiz=$2; shift 2 ;;
    --wiz=*) wiz=${1#*=}; shift ;;
    --grail) [ $# -ge 2 ] || { usage; exit 2; }; grail=$2; shift 2 ;;
    --grail=*) grail=${1#*=}; shift ;;
    --corpus) [ $# -ge 2 ] || { usage; exit 2; }; corpus=$2; shift 2 ;;
    --corpus=*) corpus=${1#*=}; shift ;;
    --keep) keep=1; shift ;;
    --verbose) verbose=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "check-repro: unknown argument $1" >&2; usage >&2; exit 2 ;;
  esac
done

json_escape() {
  printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g; s/\t/\\t/g'
}

skip() {
  local reason=$1
  if [ "$json" = 1 ]; then
    printf '{"schema":"wiz-repro-paths/v1","ok":true,"status":"skip","reason":"%s"}\n' "$(json_escape "$reason")"
  else
    echo "check-repro: skip: $reason"
  fi
  exit 0
}

[ -x "$wiz" ] || skip "the compiler is not built ($wiz); run 'lake build wiz grail' or pass --wiz PATH"
[ -d "$corpus" ] || { echo "check-repro: no corpus at $corpus" >&2; exit 2; }
command -v sha256sum >/dev/null || { echo "check-repro: sha256sum is needed" >&2; exit 2; }
command -v cmp >/dev/null || { echo "check-repro: cmp is needed" >&2; exit 2; }
command -v python3 >/dev/null || { echo "check-repro: python3 is needed for --json" >&2; exit 2; }
[ -x "$grail" ] || echo "check-repro: no grail at $grail; the grail package check is skipped" >&2

start=$(date +%s)
work=$(mktemp -d "${TMPDIR:-/tmp}/wiz-repro-paths.XXXXXX") || { echo "check-repro: cannot make a temp dir" >&2; exit 2; }
if [ "$keep" = 1 ]; then
  echo "check-repro: roots $work/a and $work/b" >&2
else
  trap 'rm -rf "$work"' EXIT INT TERM
fi
checks=$work/checks.tsv
diffs=$work/diffs.tsv
: > "$checks"
: > "$diffs"

record() { # status label detail
  printf '%s\t%s\t%s\n' "$1" "$2" "${3//$'\t'/ }" >> "$checks"
}
report_diff() { # label path detail
  printf '%s\t%s\n' "$2" "$3" >> "$diffs"
  record diff "$1/$2" "$3"
}

# The toolchain flags: what the dev shell / Nix wrapper normally supplies.
tool_flags=()
[ -n "${WIZ_CC:-}" ] && tool_flags+=(--cc "$WIZ_CC")
[ -n "${WIZ_CFLAGS:-}" ] && tool_flags+=(--cflags "$WIZ_CFLAGS")
[ -n "${WIZ_LDFLAGS:-}" ] && tool_flags+=(--ldflags "$WIZ_LDFLAGS")
[ -n "${WIZ_LLC:-}" ] && tool_flags+=(--llc "$WIZ_LLC")
[ -n "${WIZ_LIBS:-}" ] && tool_flags+=(--libs "$WIZ_LIBS")

# The two roots differ in every environmental knob a build could read.
setup_root() { # dir A|B
  local R=$1 side=$2
  mkdir -p "$R/home" "$R/tmp" "$R/out" "$R/logs" "$R/src" "$R/cache"
  cp -R "$corpus/." "$R/src/" || return 1
  if [ "$side" = A ]; then
    printf '022\nC\nUTC\n1\n1\n1\n' > "$R/env"
  else
    printf '077\nC.UTF-8\nAsia/Tokyo\n1234567890\n42\n4\n' > "$R/env"
  fi
}

run_in() { # R dir cmd...
  local R=$1 dir=$2
  shift 2
  local mask locale tz epoch py hash jobs
  { read -r mask; read -r locale; read -r tz; read -r epoch; read -r py; read -r jobs; } < "$R/env"
  [ "$verbose" = 1 ] && printf '+ (cd %s; umask %s; LC_ALL=%s; %s)\n' "$dir" "$mask" "$locale" "$*" >&2
  (
    cd "$dir" || exit 1
    umask "$mask"
    export HOME="$R/home" TMPDIR="$R/tmp" LC_ALL="$locale" LANG="$locale" TZ="$tz"
    export SOURCE_DATE_EPOCH="$epoch" PYTHONHASHSEED="$py"
    "$@"
  )
}

build_wiz_side() { # R
  local R=$1 p
  for p in pure io text ffi; do
    run_in "$R" "$R/src" "$wiz" "${tool_flags[@]}" --cache "$R/cache" \
      build "$p.wiz" -o "../out/$p" >"$R/logs/$p.log" 2>&1
    local st=$?
    [ $st = 0 ] || { record error "wiz build $p ($(basename "$R"))" "exit $st: $(tail -n 3 "$R/logs/$p.log" | tr '\n' ' ')"; }
  done
  # --split: the parts are compiled by parallel tasks (thread scheduling must not matter)
  run_in "$R" "$R/src" "$wiz" "${tool_flags[@]}" --cache "$R/cache" \
    build pure.wiz -o ../out/pure-split --split 2 >"$R/logs/split.log" 2>&1
  [ $? = 0 ] || record error "wiz build --split ($(basename "$R"))" "$(tail -n 3 "$R/logs/split.log" | tr '\n' ' ')"
  # -g: debug info and __FILE__ are made relative by -ffile-prefix-map
  run_in "$R" "$R/src" "$wiz" "${tool_flags[@]}" --cache "$R/cache" \
    --cflags "${WIZ_CFLAGS:-} -g" build pure.wiz -o ../out/pure-debug >"$R/logs/debug.log" 2>&1
  [ $? = 0 ] || record error "wiz build -g ($(basename "$R"))" "$(tail -n 3 "$R/logs/debug.log" | tr '\n' ' ')"
  # --llvm, when the dev shell's llc is there
  if [ -n "${WIZ_LLC:-}" ] && [ -x "${WIZ_LLC}" ]; then
    run_in "$R" "$R/src" "$wiz" "${tool_flags[@]}" --cache "$R/cache" \
      build pure.wiz -o ../out/pure-llvm --llvm >"$R/logs/llvm.log" 2>&1
    [ $? = 0 ] || record error "wiz build --llvm ($(basename "$R"))" "$(tail -n 3 "$R/logs/llvm.log" | tr '\n' ' ')"
  else
    record skip "wiz build --llvm" "WIZ_LLC is not set or not executable"
  fi
}

build_grail_side() { # R
  local R=$1
  [ -x "$grail" ] || return 0
  local jobs
  jobs=$(sed -n '6p' "$R/env")
  run_in "$R" "$R/src" "$grail" "${tool_flags[@]}" --cache "$R/cache" -j "$jobs" build \
    >"$R/logs/grail.log" 2>&1
  [ $? = 0 ] || record error "grail build ($(basename "$R"), -j $jobs)" "$(tail -n 3 "$R/logs/grail.log" | tr '\n' ' ')"
}

# compare_tree LABEL A B [exclude-regex]: compare the regular files of two trees,
# by relative path and bytes. The exclude regex is matched against the relative path.
compare_tree() {
  local label=$1 a=$2 b=$3 exclude=${4:-}
  [ -d "$a" ] || { record skip "$label" "no $a"; return; }
  [ -d "$b" ] || { record skip "$label" "no $b"; return; }
  ( cd "$a" && find . -type f -printf '%P\n' | LC_ALL=C sort ) > "$work/a.list"
  ( cd "$b" && find . -type f -printf '%P\n' | LC_ALL=C sort ) > "$work/b.list"
  if [ -n "$exclude" ]; then
    grep -vE "$exclude" "$work/a.list" > "$work/a2.list" || true
    grep -vE "$exclude" "$work/b.list" > "$work/b2.list" || true
    mv "$work/a2.list" "$work/a.list"; mv "$work/b2.list" "$work/b.list"
  fi
  local bad=0
  if ! diff -q "$work/a.list" "$work/b.list" >/dev/null; then
    local only_a only_b
    only_a=$(comm -23 "$work/a.list" "$work/b.list" | head -n 5 | tr '\n' ' ')
    only_b=$(comm -13 "$work/a.list" "$work/b.list" | head -n 5 | tr '\n' ' ')
    report_diff "$label" "(tree)" "file lists differ; only A: ${only_a:-none}; only B: ${only_b:-none}"
    bad=1
  fi
  local rel n=0
  while IFS= read -r rel; do
    [ -f "$a/$rel" ] && [ -f "$b/$rel" ] || continue
    if ! cmp -s "$a/$rel" "$b/$rel"; then
      n=$((n + 1))
      if [ $n -le 20 ]; then
        report_diff "$label" "$rel" "$(sha256sum "$a/$rel" | cut -d' ' -f1) vs $(sha256sum "$b/$rel" | cut -d' ' -f1)"
      fi
    fi
  done < "$work/a.list"
  [ $n -gt 20 ] && record diff "$label" "$((n - 20)) more differing files not listed"
  [ $bad = 0 ] && [ $n = 0 ] && record ok "$label" "$(wc -l < "$work/a.list" | tr -d ' ') files"
}

compare_file() { # label A B
  local label=$1 a=$2 b=$3
  if [ ! -f "$a" ] || [ ! -f "$b" ]; then record skip "$label" "missing file"; return; fi
  if cmp -s "$a" "$b"; then record ok "$label" "$(sha256sum "$a" | cut -d' ' -f1)"; else
    record diff "$label" "$(sha256sum "$a" | cut -d' ' -f1) vs $(sha256sum "$b" | cut -d' ' -f1)"
  fi
}

# A manifest of relative path + sha256 for every file matching a find expression,
# sorted; two manifests are equal exactly when the trees have the same bytes.
manifest() { # dir find-args...
  local dir=$1
  shift
  ( cd "$dir" && find . -type f "$@" -printf '%P\n' | LC_ALL=C sort | while IFS= read -r f; do
      printf '%s  %s\n' "$(sha256sum "$f" | cut -d' ' -f1)" "$f"
    done )
}

compare_compilers() { # A B label
  local A=$1 B=$2 label=$3
  compare_file "$label/wiz" "$A/.lake/build/bin/wiz" "$B/.lake/build/bin/wiz"
  compare_file "$label/grail" "$A/.lake/build/bin/grail" "$B/.lake/build/bin/grail"
  if [ "$compiler_olean" = 1 ]; then
    manifest "$A" -path './.lake/build/lib/lean/*' -name '*.olean' > "$work/a.olean"
    manifest "$B" -path './.lake/build/lib/lean/*' -name '*.olean' > "$work/b.olean"
    if cmp -s "$work/a.olean" "$work/b.olean"; then
      record ok "$label/olean" "$(wc -l < "$work/a.olean" | tr -d ' ') files"
    else
      local rel
      rel=$(diff -u "$work/a.olean" "$work/b.olean" | sed -n 's/^-\([0-9a-f]*\)  \(.*\)$/\2/p' | head -n 3 | tr '\n' ' ')
      report_diff "$label/olean" "(manifest)" "differ: ${rel:-see manifests}"
    fi
  else
    record skip "$label/olean" "Lean stores the absolute source path; pass --compiler-olean to compare"
  fi
  manifest "$A" -path './.lake/build/ir/*' -name '*.c' > "$work/a.irc"
  manifest "$B" -path './.lake/build/ir/*' -name '*.c' > "$work/b.irc"
  if [ ! -s "$work/a.irc" ] || [ ! -s "$work/b.irc" ]; then
    record skip "$label/generated-c" "one build has no generated C (all artifacts came from the cache)"
  elif cmp -s "$work/a.irc" "$work/b.irc"; then
    record ok "$label/generated-c" "$(wc -l < "$work/a.irc" | tr -d ' ') files"
  else
    report_diff "$label/generated-c" "(manifest)" "generated C differs"
  fi
}

copy_compiler_tree() { # src dest
  ( cd "$1" && tar -cf - \
      --exclude='./.git' --exclude='./.lake' --exclude='./.lake-cache' --exclude='./.direnv' \
      --exclude='./grail.local.wiz' . ) | ( cd "$2" && tar -xf - )
}

build_two_compilers() {
  command -v lake >/dev/null || { record skip "compiler builds" "lake is not on PATH"; return 1; }
  local side dest jobs log home
  # HOME is the Lean toolchain: elan installs a toolchain per HOME, so changing it changes
  # the compiler's own inputs (and its RUNPATH). Keep it fixed; vary the source path,
  # TMPDIR, umask, locale, SOURCE_DATE_EPOCH, the Lake cache and LEAN_NUM_THREADS.
  home=${HOME:?check-repro: HOME must be set to build the compiler}
  for side in a b; do
    dest=$work/compiler-$side
    mkdir -p "$dest"
    copy_compiler_tree "$root" "$dest" || { record error "compiler copy ($side)" "tar failed"; return 1; }
    if [ "$side" = a ]; then jobs=1; else jobs=8; fi
    log=$work/compiler-$side.log
    [ "$verbose" = 1 ] && echo "+ (cd $dest; lake build wiz grail, LEAN_NUM_THREADS=$jobs)" >&2
    (
      cd "$dest" || exit 1
      umask 022
      export HOME="$home" TMPDIR="$work/tmp-$side" LC_ALL=C TZ=UTC SOURCE_DATE_EPOCH=1
      mkdir -p "$TMPDIR"
      export LAKE_CACHE_DIR="$dest/.lake-cache"
      export LEAN_NUM_THREADS="$jobs"
      lake build wiz grail
    ) >"$log" 2>&1
    if [ $? != 0 ]; then
      record error "build compiler $side" "$(tail -n 5 "$log" | tr '\n' ' ')"
      return 1
    fi
    record ok "build compiler $side" "$(tail -n 1 "$log")"
  done
  compare_compilers "$work/compiler-a" "$work/compiler-b" "compiler"
  return 0
}

setup_root "$work/a" A || { echo "check-repro: cannot set up root a" >&2; exit 2; }
setup_root "$work/b" B || { echo "check-repro: cannot set up root b" >&2; exit 2; }

build_wiz_side "$work/a"
build_wiz_side "$work/b"
build_grail_side "$work/a"
build_grail_side "$work/b"

compare_tree "wiz out" "$work/a/out" "$work/b/out"
if [ -x "$grail" ]; then
  compare_tree "grail .grail" "$work/a/src/.grail" "$work/b/src/.grail" '^log/'
else
  record skip "grail .grail" "grail is not built"
fi
# Cache entries: the keyed .wizc/.wizm/.wizr/.wizs files; bin/ is the executable's
# path+mtime memo and is deliberately not part of the comparison.
compare_tree "wiz cache" "$work/a/cache" "$work/b/cache" '^bin/'

if [ -n "$compiler_a" ] || [ -n "$compiler_b" ]; then
  if [ -n "$compiler_a" ] && [ -n "$compiler_b" ]; then
    compare_compilers "$compiler_a" "$compiler_b" "compiler"
  else
    record skip "compiler" "give both --compiler-a and --compiler-b"
  fi
elif [ "$build_compiler" = 1 ]; then
  build_two_compilers
else
  record skip "compiler" "pass --compiler to build it twice, or --compiler-a/--compiler-b"
fi

runtime=$(( $(date +%s) - start ))

# --- result -------------------------------------------------------------------------
fail=0
while IFS=$'\t' read -r st label detail; do
  case $st in
    diff|error) fail=1 ;;
  esac
  if [ "$json" = 0 ]; then
    case $st in
      ok) printf 'ok   %s: %s\n' "$label" "$detail" ;;
      diff) printf 'DIFF %s: %s\n' "$label" "$detail" ;;
      error) printf 'FAIL %s: %s\n' "$label" "$detail" ;;
      skip) printf 'skip %s: %s\n' "$label" "$detail" ;;
    esac
  fi
done < "$checks"

status=ok
[ $fail = 1 ] && status=fail

if [ "$json" = 0 ]; then
  echo
  echo "check-repro: $status in $runtime s"
  [ $fail = 1 ] && echo "differences are listed above; the roots are $work/a and $work/b (--keep keeps them)"
else
  python3 - "$status" "$runtime" "$checks" "$diffs" <<'PY'
import json, sys
status, runtime, checks_path, diffs_path = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
checks = []
with open(checks_path, encoding="utf-8") as f:
    for line in f:
        st, name, detail = line.rstrip("\n").split("\t", 2)
        checks.append({"name": name, "status": st, "detail": detail})
diffs = []
with open(diffs_path, encoding="utf-8") as f:
    for line in f:
        path, detail = line.rstrip("\n").split("\t", 1)
        diffs.append({"path": path, "detail": detail})
cchecks = [c for c in checks if c["name"].startswith("compiler") or c["name"].startswith("build compiler")]
if any(c["status"] in ("diff", "error") for c in cchecks):
    cstatus = "fail"
elif cchecks and all(c["status"] == "skip" for c in cchecks):
    cstatus = "skip"
elif cchecks:
    cstatus = "ok"
else:
    cstatus = "skip"
print(json.dumps({
    "schema": "wiz-repro-paths/v1",
    "ok": status == "ok",
    "status": status,
    "runtimeSeconds": runtime,
    "checks": checks,
    "diffs": diffs,
    "compiler": {"status": cstatus, "checks": cchecks},
}, separators=(",", ":"), ensure_ascii=False))
PY
fi

exit $fail
