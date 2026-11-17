#!/usr/bin/env bash
# The bootstrap fixpoint check.
#
# Stage 1 is the self-hosted compiler built by the Lean `wiz build`; it compiles the
# whole toolchain to C (self1.c). Each later stage compiles the previous stage's C with
# selfhost/rt.c and Boehm GC (to stage2, stage3, ...) and that program compiles the
# toolchain again (self2.c, self3.c, ...). Every stage's C must be byte-identical to
# stage 1's. Three stages are the default: stage 1 = stage 2 shows the C the Lean-built
# compiler emits is reproduced by the compiler that C builds; stage 2 = stage 3 shows
# that reproduction is a fixed point, not one coincident round.
#
# The check has five parts, all of which must hold:
#   * every stage's C is byte-identical (cmp), and every stage's C md5 equals stage 1's
#     (the md5 that is printed is checked, not decoration);
#   * every stage executable is byte-identical to stage 2's (compiled from a fixed
#     source name, with -frandom-seed, a fixed file-prefix map, SOURCE_DATE_EPOCH and
#     --build-id=none); if the raw binaries differ, their stripped copies are compared
#     and the differing ELF sections are named, and the verdict passes only if the
#     stripped copies agree;
#   * the checked-in parser tables (selfhost/Tables.wiz) equal the tables the Lean
#     grammar renders now (the generator writes to OUTDIR; the checked-in file is not
#     touched);
#   * the checked-in compiler input is the source of the run: OUTDIR/provenance records
#     the commit, source hash, mode, stage count, tables hash and every artifact hash.
#     --compare-only refuses a directory without it and refuses a directory produced by
#     another commit, source tree, mode or stage count.
#   * (with --rc) the same in reference-counting mode: --rc is a mode of the same check.
#
#   usage (from the repository root, in `nix develop`):
#     scripts/fixpoint.sh [--rc] [--stages N] [--keep] [--compare-only] [OUTDIR]
#
#   --rc            compile with reference counting (the compiler's flag, stage 21k), so
#                   every stage is a reference-counted compiler that must free every object
#   --stages N      how many C stages to generate and compare (N >= 2; default 3)
#   --keep          keep the artifacts: self*.c, the stage binaries and run/
#   --compare-only  only compare the artifacts already in OUTDIR, without building or
#                   compiling; requires the provenance file the run wrote and the
#                   artifacts it names (so use --keep); re-checks kept artifacts only
#   OUTDIR          default .lake/fixpoint
#
# It prints each step's wall time and peak RSS (the self-compile stages need about
# 6 GiB; they have peaked near 5.4 GiB), each stage's C size and md5 with PASS/FAIL, the
# stage executables' hashes, and the wall time of each added comparison. A stage killed
# by the OOM killer or a memory cgroup (exit 137) fails with a hint.
# Slow: two or more compilations of the whole toolchain (CI runs it on a schedule).
set -euo pipefail

usage() { awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"; }
die() { echo "fixpoint: $*" >&2; exit 2; }

mode=()
mode_name=gc
stages=3
keep=0
compare_only=0
out=
while [ $# -gt 0 ]; do
  case "$1" in
    --rc) mode=(--rc); mode_name=rc; shift ;;
    --stages) [ $# -ge 2 ] || die "--stages needs a number"; stages=$2; shift 2 ;;
    --stages=*) stages=${1#--stages=}; shift ;;
    --keep) keep=1; shift ;;
    --compare-only) compare_only=1; shift ;;
    -h|--help) usage; exit 0 ;;
    --) shift; break ;;
    -*) die "unknown option: $1 (try --help)" ;;
    *) [ -z "$out" ] || die "unexpected argument: $1"; out=$1; shift ;;
  esac
done
case "$stages" in ''|*[!0-9]*) die "--stages must be a whole number" ;; esac
[ "$stages" -ge 2 ] || die "--stages must be at least 2 (a fixpoint compares two C files)"

out=${out:-.lake/fixpoint}
mkdir -p "$out"
out=$(cd "$out" && pwd)

if [ "$compare_only" = 0 ]; then
  : "${WIZ_GC_CFLAGS?needs the toolchain environment (nix develop)}"
  mkdir -p "$out/run"
fi

step() { echo "::group::$1" 2>/dev/null; echo "== $1 ($(date +%T))"; }
done_() { echo "::endgroup::"; }
md5_of() { md5sum "$1" | cut -d' ' -f1; }
sha256_of() { sha256sum "$1" | cut -d' ' -f1; }
now_ms() { date +%s%N; }
since_ms() { echo "$(( ($(now_ms) - $1) / 1000000 ))"; }

# The provenance of a run. The C stages are determined by the toolchain sources, the
# generated inputs, the backend mode, the stage count and the C compiler/flags; a kept
# OUTDIR is only re-checkable when all of them are the ones it was produced with.
src_paths=(selfhost lib scripts/GenSelfhost.lean scripts/GenSelfhostTables.lean
           scripts/fixpoint.sh lakefile.lean lean-toolchain Main.lean Wiz WizMeta
           runtime c Tests/Elab.lean)
git_head=$(git rev-parse --verify HEAD 2>/dev/null || echo unknown)
if [ -n "$(git status --porcelain --untracked-files=no -- "${src_paths[@]}" 2>/dev/null)" ]; then
  dirty=yes
else
  dirty=no
fi
source_sha256() {
  {
    printf 'mode\t%s\n' "$mode_name"
    printf 'stages\t%s\n' "$stages"
    printf 'WIZ_CFLAGS\t%s\n' "${WIZ_CFLAGS:-}"
    printf 'WIZ_LDFLAGS\t%s\n' "${WIZ_LDFLAGS:-}"
    printf 'WIZ_GC_CFLAGS\t%s\n' "${WIZ_GC_CFLAGS:-}"
    printf 'WIZ_GC_LDFLAGS\t%s\n' "${WIZ_GC_LDFLAGS:-}"
    printf 'cc\t%s\n' "$(cc --version 2>/dev/null | head -1)"
    printf 'lean\t%s\n' "$(lean --version 2>/dev/null | head -1)"
    git ls-files -z -- "${src_paths[@]}" 2>/dev/null \
      | LC_ALL=C sort -z \
      | while IFS= read -r -d '' f; do
          printf '%s\t%s\n' "$f" "$(sha256_of "$f")"
        done
  } | sha256sum | cut -d' ' -f1
}
command -v cc >/dev/null || die "cc is not on PATH (run in the toolchain environment)"
command -v lean >/dev/null || die "lean is not on PATH (run in the toolchain environment)"
t_src=$(now_ms)
src_hash=$(source_sha256)
src_hash_ms=$(since_ms "$t_src")

prov_get() { awk -F'\t' -v k="$1" '$1 == k { print $2; exit }' "$out/provenance"; }
prov_stage() { awk -F'\t' -v k="$1" '$1 == k { print $2 "\t" $3; exit }' "$out/provenance"; }
require_provenance() {
  [ -f "$out/provenance" ] || die "no $out/provenance: this directory was not produced by a run that recorded its source (or --keep did not keep it); rebuild it, or use a fresh directory"
  local key want got
  for key in commit source_sha256 mode stages tables_sha256 tables_generated_sha256 compiler_wiz_sha256 self_wiz_sha256; do
    got=$(prov_get "$key")
    [ -n "$got" ] || die "$out/provenance has no '$key' entry"
  done
  if [ "$(prov_get commit)" != "$git_head" ]; then
    echo "note: OUTDIR was produced at commit $(prov_get commit), this checkout is $git_head;" >&2
    echo "      the input source hash still matches, so this is a change outside the fixpoint's inputs" >&2
  fi
  [ "$(prov_get mode)" = "$mode_name" ] || die "provenance mismatch: OUTDIR is from mode $(prov_get mode), this run is --$mode_name"
  [ "$(prov_get stages)" = "$stages" ] || die "provenance mismatch: OUTDIR has $(prov_get stages) stages, this run asks for $stages"
  [ "$(prov_get source_sha256)" = "$src_hash" ] || die "provenance mismatch: the sources, flags or compiler in this checkout differ from the run that produced OUTDIR (source hash $(prov_get source_sha256), now $src_hash)"
  [ "$(prov_get tables_sha256)" = "$(sha256_of selfhost/Tables.wiz)" ] \
    || die "provenance mismatch: selfhost/Tables.wiz differs from the one the run used"
  [ -f "$out/Tables.wiz" ] || die "provenance mismatch: $out/Tables.wiz (the tables the run generated) is missing"
  [ "$(prov_get tables_generated_sha256)" = "$(sha256_of "$out/Tables.wiz")" ] \
    || die "provenance mismatch: $out/Tables.wiz changed since the run"
  [ "$dirty" = "$(prov_get dirty)" ] || die "provenance mismatch: the working tree is now ${dirty} with respect to the run's inputs, but the run recorded $(prov_get dirty)"
  for f in compiler.wiz self.wiz; do
    [ -f "$out/$f" ] || die "provenance mismatch: $out/$f (a generated input) is missing"
  done
  [ "$(prov_get compiler_wiz_sha256)" = "$(sha256_of "$out/compiler.wiz")" ] \
    || die "provenance mismatch: $out/compiler.wiz changed since the run"
  [ "$(prov_get self_wiz_sha256)" = "$(sha256_of "$out/self.wiz")" ] \
    || die "provenance mismatch: $out/self.wiz changed since the run"
  local k f bytes md5
  for k in $(seq 1 "$stages"); do
    f=$out/self$k.c
    [ -f "$f" ] || die "$f is missing: the run kept it (--keep), and --compare-only checks the artifacts it recorded"
    bytes=$(stat -c %s "$f"); md5=$(md5_of "$f")
    [ "$(prov_stage "c$k")" = "$(printf '%s\t%s' "$bytes" "$md5")" ] \
      || die "provenance mismatch: $f is not the file the run produced (size/md5 differ)"
  done
  for k in $(seq 2 "$stages"); do
    f=$out/stage$k
    [ -f "$f" ] || die "$f is missing: the run kept it (--keep), and --compare-only checks the artifacts it recorded"
    [ "$(prov_stage "bin$k")" = "$(printf '%s\t%s' "$(stat -c %s "$f")" "$(sha256_of "$f")")" ] \
      || die "provenance mismatch: $f is not the executable the run produced (size/sha256 differ)"
  done
}

timings=$out/timings.tsv
labels=()
walls=()
peaks=()
total_peak=0
if [ "$compare_only" = 0 ]; then
  : > "$timings"
  printf 'step\twall_s\tpeak_kib\n' >> "$timings"
fi

# A small sampler: run the command in DIR with its stdout in OUTFILE, and report the wall
# time and the peak resident set of the process tree (a self-compile is one process; `cc`
# and `lake` fan out). Python3 is part of the dev shell and of CI. /proc is Linux-only,
# as is the fixpoint's C toolchain.
measure=$out/.measure.py
if [ "$compare_only" = 0 ]; then
cat > "$measure" <<'PY'
import os, resource, subprocess, sys, time

def snapshot():
    procs = {}
    page = os.sysconf("SC_PAGE_SIZE")
    for name in os.listdir("/proc"):
        if not name.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % name, "rb") as f:
                data = f.read()
        except OSError:
            continue
        r = data.rfind(b")")
        if r < 0:
            continue
        parts = data[r + 2:].split()
        if len(parts) < 22:
            continue
        try:
            procs[int(name)] = (int(parts[1]), int(parts[21]) * (page // 1024))
        except ValueError:
            continue
    return procs

def tree_rss(procs, root):
    total = 0
    for pid, (ppid, rss) in procs.items():
        p = pid
        for _ in range(64):
            if p == root:
                total += rss
                break
            nxt = procs.get(p)
            if nxt is None or p <= 1:
                break
            p = nxt[0]
    return total

cwd, outfile, argv = sys.argv[1], sys.argv[2], sys.argv[3:]
start = time.monotonic()
try:
    with open(outfile, "wb") as out:
        p = subprocess.Popen(argv, cwd=cwd, stdout=out)
        peak = 0
        while p.poll() is None:
            peak = max(peak, tree_rss(snapshot(), p.pid))
            time.sleep(0.1)
        rc = p.returncode
except OSError as e:
    print("fixpoint: cannot run %r: %s" % (argv, e), file=sys.stderr)
    sys.exit(125)
wall = time.monotonic() - start
# ru_maxrss is a floor for short commands, which the sampling can miss.
peak = max(peak, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
print("%.3f %d" % (wall, peak))
sys.exit(128 - rc if rc < 0 else rc)
PY
fi

# run_step LABEL DIR OUTFILE COMMAND... -- run COMMAND in DIR, its stdout to OUTFILE,
# recording wall time and the tree's peak RSS.
run_step() {
  local label=$1 dir=$2 outfile=$3
  shift 3
  local metrics rc secs kb
  set +e
  metrics=$(python3 "$measure" "$dir" "$outfile" "$@")
  rc=$?
  set -e
  read -r secs kb <<< "$metrics" || { secs=0; kb=0; }
  secs=${secs:-0}; kb=${kb:-0}
  labels+=("$label"); walls+=("$secs"); peaks+=("$kb")
  [ "$kb" -le "$total_peak" ] 2>/dev/null || total_peak=$kb
  printf '   %-54s %8ss %8s MiB\n' "$label" "$secs" "$((kb / 1024))"
  printf '%s\t%s\t%s\n' "$label" "$secs" "$kb" >> "$timings"
  if [ "$rc" -ne 0 ]; then
    echo
    echo "FAILED: '$label' exited $rc after ${secs}s (peak $((kb / 1024)) MiB)." >&2
    if [ "$rc" -eq 137 ] || [ "$rc" -eq 9 ]; then
      echo "It was killed (SIGKILL), which is how the OOM killer and a memory cgroup end a run." >&2
      echo "The fixpoint needs about 6 GiB: the self-compiles peak near 5.4 GiB (stage 2 has reached 5.5 GiB)." >&2
      echo "Reserve it (e.g. 'heavy --mem 6G scripts/fixpoint.sh') and give the runner >= 6 GiB free." >&2
    fi
    echo "Artifacts are in $out (run/ and the files already produced)." >&2
    exit 1
  fi
}

# The ELF sections that differ, for a binary comparison that needs to say why. It is
# diagnostics only and runs only when the comparison has already failed.
elf_sections_that_differ() { # elf_sections_that_differ A B
  local a=$1 b=$2 s tmpa tmpb out=()
  command -v readelf >/dev/null && command -v objcopy >/dev/null || return 0
  tmpa=$(mktemp -d) && tmpb=$(mktemp -d) || return 0
  while IFS= read -r s; do
    if [ "$s" = NULL ] || [ -z "$s" ]; then continue; fi
    objcopy -O binary --only-section="$s" "$a" "$tmpa/x" 2>/dev/null || continue
    if ! objcopy -O binary --only-section="$s" "$b" "$tmpb/x" 2>/dev/null; then
      out+=("$s(only in A)")
    elif ! cmp -s "$tmpa/x" "$tmpb/x"; then
      out+=("$s")
    fi
  done < <(readelf -SW "$a" | sed -n 's/^ *\[ *[0-9]*\] \([^ ]*\).*/\1/p')
  rm -rf "$tmpa" "$tmpb"
  [ ${#out[@]} -eq 0 ] || echo "differing ELF sections: ${out[*]}"
}

# Compile each source to an object and compare those, when even the stripped binaries
# differ. This separates a nondeterministic compiler (objects differ) from a
# nondeterministic link (objects equal, executables differ). Diagnostics only.
object_files_that_differ() { # object_files_that_differ FIRST LAST
  local first=$1 last=$2 k ok=1
  command -v cc >/dev/null || return 0
  mkdir -p "$out/diag"
  for k in $(seq "$first" "$last"); do
    prev=$((k - 1))
    cp "$out/self$prev.c" "$out/diag/wizc.c"
    if ! cc -O2 -w -I"$PWD/selfhost" $WIZ_GC_CFLAGS \
         -frandom-seed=wiz-fixpoint -ffile-prefix-map="$PWD"=. -fdebug-prefix-map="$PWD"=. \
         -c "$out/diag/wizc.c" -o "$out/diag/stage$k.o" 2>/dev/null; then
      echo "object comparison: could not compile self$prev.c"
      return 0
    fi
  done
  echo "object files (stage$first .. stage$last):"
  for k in $(seq $((first + 1)) "$last"); do
    if cmp -s "$out/diag/stage$((k - 1)).o" "$out/diag/stage$k.o"; then
      printf '  stage%d.o = stage%d.o\n' "$((k - 1))" "$k"
    else
      printf '  stage%d.o != stage%d.o (the C compiler is nondeterministic)\n' "$((k - 1))" "$k"
      ok=0
    fi
  done
  if [ "$ok" = 1 ]; then
    echo "  the objects agree, so the link is what differs (the linker or its inputs)"
    echo "  not compared: the runtime and GC libraries linked into both stages (they are inputs, not stage outputs)"
  fi
}

if [ "$compare_only" = 0 ]; then
  t_start=$(date +%s)

  step "generate compiler.wiz and self.wiz"
  run_step "build the Lean wiz and the test driver" "$PWD" /dev/null lake build wiz Tests.Elab
  run_step "generate compiler.wiz and self.wiz" "$PWD" /dev/null env OUT="$out" lake lean scripts/GenSelfhost.lean
  cp "$out/self.wiz" "$out/run/input.wiz"
  done_

  step "regenerate selfhost/Tables.wiz"
  # The generator writes to OUTDIR, never to the checked-in file (a test run may be
  # reading it). The selfhost group also checks this, but the fixpoint job runs no tests,
  # so the fixpoint must check its own input rather than trust it.
  t_tables=$(now_ms)
  run_step "regenerate the parser tables" "$PWD" /dev/null \
    env WIZ_TABLES_OUT="$out/Tables.wiz" lake lean scripts/GenSelfhostTables.lean
  tables_gen_ms=$(since_ms "$t_tables")
  tables_diff_ms=0
  t_tables_cmp=$(now_ms)
  if ! cmp -s "selfhost/Tables.wiz" "$out/Tables.wiz"; then
    echo "TABLES DIFFER: selfhost/Tables.wiz is stale; the generated tables are in $out/Tables.wiz" >&2
    diff "selfhost/Tables.wiz" "$out/Tables.wiz" | head -20 >&2 || true
    echo "Run 'lake build genSelfhostTables' and commit the result." >&2
    rm -f "$measure"
    exit 1
  fi
  tables_diff_ms=$(since_ms "$t_tables_cmp")
  t_tables_det=$(now_ms)
  run_step "regenerate the parser tables again (determinism)" "$PWD" /dev/null \
    env WIZ_TABLES_OUT="$out/Tables.2.wiz" lake lean scripts/GenSelfhostTables.lean
  if ! cmp -s "$out/Tables.wiz" "$out/Tables.2.wiz"; then
    echo "TABLES NOT DETERMINISTIC: two renders of the Lean grammar differ." >&2
    diff "$out/Tables.wiz" "$out/Tables.2.wiz" | head -20 >&2 || true
    rm -f "$out/Tables.2.wiz" "$measure"
    exit 1
  fi
  tables_det_ms=$(since_ms "$t_tables_det")
  rm -f "$out/Tables.2.wiz"
  done_

  step "stage 1: the Lean wiz build of the self-hosted compiler"
  # shellcheck disable=SC2086
  run_step "stage 1: the Lean wiz build of the compiler" "$PWD" /dev/null \
    .lake/build/bin/wiz build "$out/compiler.wiz" -o "$out/compiler" \
    --cflags "$WIZ_CFLAGS" --ldflags "$WIZ_LDFLAGS"
  done_

  step "stage 1 compiles the toolchain (self1.c)"
  run_step "stage 1 compiles the toolchain (self1.c)" "$out/run" "$out/self1.c" \
    "$out/compiler" "${mode[@]}"
  done_

  mkdir -p "$out/cc"
  k=2
  while [ "$k" -le "$stages" ]; do
    prev=$((k - 1))
    step "stage $k: cc self$prev.c with selfhost/rt.c"
    # cc records the source's base name in the executable's symbol table (an STT_FILE
    # entry), so every stage compiles a copy with one fixed name, cc/wizc.c: equal C
    # then gives equal executables. The other flags remove the build path, the random
    # seed and a content-addressed build id, the values that could make two builds of
    # the same C differ.
    cp "$out/self$prev.c" "$out/cc/wizc.c"
    # shellcheck disable=SC2086
    run_step "cc self$prev.c -> stage$k" "$PWD" /dev/null \
      env SOURCE_DATE_EPOCH=0 cc -O2 -w -I"$PWD/selfhost" $WIZ_GC_CFLAGS \
        -frandom-seed=wiz-fixpoint -ffile-prefix-map="$PWD"=. -fdebug-prefix-map="$PWD"=. \
        "$out/cc/wizc.c" -o "$out/stage$k" -Wl,--build-id=none $WIZ_GC_LDFLAGS
    done_

    step "stage $k compiles the toolchain (self$k.c)"
    run_step "stage $k compiles the toolchain (self$k.c)" "$out/run" "$out/self$k.c" \
      "$out/stage$k" "${mode[@]}"
    done_
    k=$((k + 1))
  done

  total_wall=$(( $(date +%s) - t_start ))
else
  total_wall=0
  [ "$stages" -ge 2 ] || die "--compare-only needs --stages >= 2"
  require_provenance
  tables_gen_ms=0
  tables_diff_ms=0
  tables_det_ms=0
fi

# Compare every stage with stage 1: equality is transitive, so this compares all of them.
echo
echo "stage C files (self1.c is the reference):"
t_cmp=$(now_ms)
fail=0
ref_md5=
for k in $(seq 1 "$stages"); do
  f=$out/self$k.c
  if [ ! -f "$f" ]; then
    printf 'stage %d  %-16s  MISSING\n' "$k" "self$k.c"
    fail=1
    continue
  fi
  bytes=$(stat -c %s "$f")
  md5=$(md5_of "$f")
  if [ "$k" -eq 1 ]; then
    ref_md5=$md5
    result="(reference)"
  elif cmp -s "$out/self1.c" "$f" && [ "$md5" = "$ref_md5" ]; then
    result=PASS
  else
    result=FAIL
    fail=1
  fi
  printf 'stage %d  %-16s  %10d bytes  md5 %s  %s\n' "$k" "self$k.c" "$bytes" "$md5" "$result"
done
c_cmp_ms=$(since_ms "$t_cmp")

# Compare the stage executables. stage 2 is the reference: stage 3 and later are cc of
# the same C with the same flags, so they should be byte-identical. If the raw bytes
# differ, compare stripped copies (the code and data, with the metadata removed) and
# report the sections that differ; the verdict passes only when the stripped copies
# agree. Not compared: stage 1's Lean-built `compiler` (a different toolchain, linked
# against Lean's runtime) and the runtime/GC libraries the stages link.
echo
echo "stage executables (stage2 is the reference):"
t_bin=$(now_ms)
bin_fail=0
bin_sha=()
for k in $(seq 2 "$stages"); do
  f=$out/stage$k
  if [ ! -f "$f" ]; then
    printf 'stage %d  %-16s  MISSING\n' "$k" "stage$k"
    bin_fail=1
    continue
  fi
  bin_sha[$k]=$(sha256_of "$f")
  if [ "$k" -eq 2 ]; then
    printf 'stage %d  %-16s  %10d bytes  sha256 %s  (reference)\n' \
      "$k" "stage$k" "$(stat -c %s "$f")" "${bin_sha[$k]}"
    continue
  fi
  if cmp -s "$out/stage2" "$f"; then
    printf 'stage %d  %-16s  %10d bytes  sha256 %s  PASS\n' \
      "$k" "stage$k" "$(stat -c %s "$f")" "${bin_sha[$k]}"
  else
    norm2=$out/.stage2.norm
    normk=$out/.stage$k.norm
    cp "$out/stage2" "$norm2"
    cp "$f" "$normk"
    if command -v strip >/dev/null && strip --strip-all "$norm2" "$normk" 2>/dev/null \
       && cmp -s "$norm2" "$normk"; then
      printf 'stage %d  %-16s  %10d bytes  sha256 %s  PASS (stripped; raw differs)\n' \
        "$k" "stage$k" "$(stat -c %s "$f")" "${bin_sha[$k]}"
      echo "  raw stage2 and stage$k differ; stripped copies are byte-identical."
      elf_sections_that_differ "$out/stage2" "$f" | sed 's/^/  /' || true
      rm -f "$norm2" "$normk"
    else
      printf 'stage %d  %-16s  %10d bytes  sha256 %s  FAIL\n' \
        "$k" "stage$k" "$(stat -c %s "$f")" "${bin_sha[$k]}"
      echo "  raw bytes: $(cmp "$out/stage2" "$f" 2>&1 | head -1)"
      elf_sections_that_differ "$out/stage2" "$f" | sed 's/^/  /' || true
      rm -f "$norm2" "$normk"
      if cmp -s "$out/self1.c" "$out/self$((k - 1)).c"; then
        object_files_that_differ 2 "$stages" | sed 's/^/  /' || true
      else
        echo "  the source C files differ (self1.c vs self$((k - 1)).c), so the executables"
        echo "  differ for that reason; object comparison would not separate a compiler"
        echo "  nondeterminism from that difference, so it is not compared."
      fi
      echo "  not compared: stage 1's Lean-built compiler (a different toolchain and runtime),"
      echo "  and the runtime/GC libraries linked into both executables (link inputs, not outputs)."
      bin_fail=1
    fi
  fi
done
[ "$bin_fail" -eq 0 ] || fail=1
bin_cmp_ms=$(since_ms "$t_bin")

if [ "$compare_only" = 0 ]; then
  echo
  printf 'total   %8ss   peak %s MiB\n' "$total_wall" "$((total_peak / 1024))"
  echo "timings: $timings"
  echo
  echo "comparison wall time (this run; not part of the stage timings above):"
  printf '   %-54s %8s s\n' "regenerate the parser tables" "$(awk -v n="$tables_gen_ms" 'BEGIN { printf "%.3f", n/1000 }')"
  printf '   %-54s %8s s\n' "diff the generated tables" "$(awk -v n="$tables_diff_ms" 'BEGIN { printf "%.3f", n/1000 }')"
  printf '   %-54s %8s s\n' "regenerate the tables a second time" "$(awk -v n="$tables_det_ms" 'BEGIN { printf "%.3f", n/1000 }')"
  printf '   %-54s %8s s\n' "compare the C files and their md5s" "$(awk -v n="$c_cmp_ms" 'BEGIN { printf "%.3f", n/1000 }')"
  printf '   %-54s %8s s\n' "compare the stage executables" "$(awk -v n="$bin_cmp_ms" 'BEGIN { printf "%.3f", n/1000 }')"
fi

if [ "$fail" -ne 0 ]; then
  echo
  echo "NO FIXPOINT: a stage's C or executable differs from stage 1's."
  for k in $(seq 2 "$stages"); do
    f=$out/self$k.c
    [ -f "$f" ] || continue
    cmp -s "$out/self1.c" "$f" && continue
    echo "first difference, self1.c vs self$k.c:"
    diff "$out/self1.c" "$f" | head -20 || true
    break
  done
  echo "Artifacts are in $out (the C files are kept on failure)." >&2
  rm -f "$measure"
  exit 1
fi

first_bytes=$(stat -c %s "$out/self1.c")
first_md5=$(md5_of "$out/self1.c")

# Record what this run was, for --compare-only. The file is written only after every
# comparison passed, so a directory with a provenance file is a green run's directory.
t_prov=$(now_ms)
{
  printf 'fixpoint-provenance\t1\n'
  printf 'commit\t%s\n' "$git_head"
  printf 'dirty\t%s\n' "$dirty"
  printf 'source_sha256\t%s\n' "$src_hash"
  printf 'mode\t%s\n' "$mode_name"
  printf 'stages\t%s\n' "$stages"
  printf 'tables_sha256\t%s\n' "$(sha256_of "selfhost/Tables.wiz")"
  printf 'tables_generated_sha256\t%s\n' "$(sha256_of "$out/Tables.wiz")"
  printf 'compiler_wiz_sha256\t%s\n' "$(sha256_of "$out/compiler.wiz")"
  printf 'self_wiz_sha256\t%s\n' "$(sha256_of "$out/self.wiz")"
  printf 'c1_md5\t%s\n' "$first_md5"
  for k in $(seq 1 "$stages"); do
    [ -f "$out/self$k.c" ] || continue
    printf 'c%d\t%s\t%s\n' "$k" "$(stat -c %s "$out/self$k.c")" "$(md5_of "$out/self$k.c")"
  done
  for k in $(seq 2 "$stages"); do
    [ -f "$out/stage$k" ] || continue
    printf 'bin%d\t%s\t%s\n' "$k" "$(stat -c %s "$out/stage$k")" "$(sha256_of "$out/stage$k")"
  done
} > "$out/provenance"
prov_ms=$(since_ms "$t_prov")
if [ "$compare_only" = 0 ]; then
  printf '   %-54s %8s s\n' "compute the provenance source hash" "$(awk -v n="$src_hash_ms" 'BEGIN { printf "%.3f", n/1000 }')"
  printf '   %-54s %8s s\n' "write the provenance" "$(awk -v n="$prov_ms" 'BEGIN { printf "%.3f", n/1000 }')"
  comparisons_ms=$((src_hash_ms + tables_diff_ms + tables_det_ms + c_cmp_ms + bin_cmp_ms + prov_ms))
  all_ms=$((total_wall * 1000 + comparisons_ms))
  printf '   %-54s %8s s\n' "total (stages + comparisons)" "$(awk -v n="$all_ms" 'BEGIN { printf "%.3f", n/1000 }')"
  echo "provenance: commit $git_head (dirty=$dirty), mode $mode_name, $stages stages, source $src_hash"
fi
rm -f "$measure"

if [ "$compare_only" = 0 ] && [ "$keep" = 0 ]; then
  rm -rf "$out/run" "$out/cc" "$out/diag" "$out"/self*.c "$out"/stage* "$out/compiler" "$out/compiler.wiz" "$out/self.wiz"
  echo "artifacts removed (--keep keeps self*.c, the stage binaries and run/; provenance and Tables.wiz are kept)"
elif [ "$keep" = 1 ]; then
  echo "artifacts kept in $out"
fi

if [ "$stages" -eq 2 ]; then
  echo "FIXPOINT (stage-1 C = stage-2 C, same md5: $first_bytes bytes, md5 $first_md5)"
else
  echo "FIXPOINT (stages 1-$stages agree in C and md5, stage 2-$stages agree in executables: $first_bytes bytes, md5 $first_md5)"
fi
