#!/usr/bin/env bash
# The reproducible-build gate: a Nix derivation must produce the same *content* when it
# is built again, not merely the same store path.
#
#   scripts/check-repro-build.sh [options] [INSTALLABLE]
#   scripts/check-repro-build.sh                 # .#wiz
#   scripts/check-repro-build.sh .#tests
#   scripts/check-repro-build.sh --self-test     # the positive and negative controls
#
# Why the hash and not the path: a store path is a hash of the derivation (its builder,
# inputs and environment), so the same derivation has the same path whether or not its
# build is reproducible. Comparing the path before and after a rebuild therefore always
# passes. The gate compares the NAR hash of the output (`nix hash path`): the bytes,
# modes and symlinks of the tree, which is what "reproducible" means here.
#
# Build 1 is `nix build` (on CI, the store path the `build` job published, substituted
# from Cachix). Build 2 is `nix build --rebuild`, which rebuilds the derivation and
# compares it with the existing output. The rebuild runs with a different
# `--option sandbox-build-dir DIR`, so `NIX_BUILD_TOP` inside the sandbox is different;
# Nix fails with "may not be deterministic" when the bytes differ, and leaves the
# differing tree at <out>.check. The gate hashes that too, so a failure names both
# hashes instead of only saying that they differ.
#
# Exit status: 0 every output's hash is identical, 1 a difference or a failed rebuild,
# 2 usage error (or nix is not installed). The self-test needs no build of Wiz: its
# controls are two tiny derivations in Tests/ReproDerivations/flake.nix, one
# reproducible and one that embeds a timestamp.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

attr=.#wiz
attr_set=0
dir_a=            # empty: use whatever built the store path (the store's default)
dir_b=/build-repro-gate
json=0
keep=0
self_test=0

usage() {
  awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"
  cat <<'EOF'

Options:
  --json                    print one JSON result object on stdout (logs go to stderr)
  --build-dir DIR           the second build's sandbox build dir, hence NIX_BUILD_TOP
                            (default /build-repro-gate); must be an absolute path
  --first-build-dir DIR     the first build's sandbox build dir (default: the store
                            default, /build; a substituted path keeps how it was built)
  --self-test               run the positive and negative controls (no Wiz build)
  --keep                    keep the logs and print their directory
  -h, --help                this text
EOF
}

die() { printf 'check-repro-build: %s\n' "$*" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case $1 in
    --json) json=1; shift ;;
    --build-dir) [ $# -ge 2 ] || die "--build-dir needs a value"; dir_b=$2; shift 2 ;;
    --build-dir=*) dir_b=${1#*=}; shift ;;
    --first-build-dir) [ $# -ge 2 ] || die "--first-build-dir needs a value"; dir_a=$2; shift 2 ;;
    --first-build-dir=*) dir_a=${1#*=}; shift ;;
    --self-test) self_test=1; shift ;;
    --keep) keep=1; shift ;;
    -h|--help) usage; exit 0 ;;
    -*) die "unknown option $1 (see --help)" ;;
    *)
      [ "$attr_set" = 0 ] || die "one installable at a time, not $attr and $1"
      attr=$1; attr_set=1; shift ;;
  esac
done

case $dir_b in
  /*) ;;
  *) die "--build-dir must be absolute (it is a path inside the sandbox): $dir_b" ;;
esac
if [ -n "$dir_a" ]; then
  case $dir_a in
    /*) ;;
    *) die "--first-build-dir must be absolute: $dir_a" ;;
  esac
fi

command -v nix >/dev/null 2>&1 || die "nix is not on PATH; this gate rebuilds a Nix derivation"

# One line per compared output: status, path, hash A, hash B, detail. Tabs and newlines
# in a detail (a log tail) would break the format, so they become spaces.
record() {
  printf '%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" \
    "$(printf '%s' "$5" | tr '\n\t' '  ' | cut -c1-2000)" >> "$records"
}

hash_of() { nix hash path "$1" 2>/dev/null; }

# drop_check PATH: remove a stale <out>.check before a rebuild. Nix writes the second
# build's output to <out>.check, a plain tree in the store rather than a
# database-registered store path (nix path-info prints it, nix-store -q says "not
# valid"). On a mismatch Nix keeps it, and the gate keeps it too: it is the second tree
# the failure names. A read-only store cannot remove a stale one; Nix replaces it.
drop_check() {
  local p=$1.check
  case $p in
    /nix/store/*.check) [ -e "$p" ] && rm -rf -- "$p" 2>/dev/null ;;
  esac
  return 0
}

# --- self-test -----------------------------------------------------------------------
# The gate without a failing test is a hope: the negative control must be rejected by the
# same code path that accepts the positive one. No Wiz build is needed.
self_test_run() {
  local fixture=$root/Tests/ReproDerivations tmp failed=0 st good bad good_json bad_json
  local bad_path_before bad_path_after good_err bad_err
  [ -f "$fixture/flake.nix" ] || { echo "self-test: no $fixture/flake.nix" >&2; return 2; }
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/check-repro-build-selftest.XXXXXX") || {
    echo "self-test: cannot make a temp dir" >&2; return 2; }
  # Build from a copy: Nix may want to write a lock file, and the checkout must stay clean.
  cp -R "$fixture" "$tmp/fixture"
  good="path:$tmp/fixture#reproducible"
  bad="path:$tmp/fixture#nonreproducible"
  good_json=$tmp/good.json
  bad_json=$tmp/bad.json
  good_err=$tmp/good.err
  bad_err=$tmp/bad.err

  "$here/check-repro-build.sh" --json "$good" > "$good_json" 2> "$good_err"
  st=$?
  if [ $st != 0 ]; then
    echo "FAIL the reproducible control was rejected (exit $st):" >&2
    tail -n 5 "$good_err" >&2
    failed=1
  fi

  bad_path_before=$(nix path-info "$bad" 2>/dev/null | head -n 1)
  "$here/check-repro-build.sh" --json "$bad" > "$bad_json" 2> "$bad_err"
  st=$?
  bad_path_after=$(nix path-info "$bad" 2>/dev/null | head -n 1)
  if [ $st = 1 ]; then
    :
  else
    echo "FAIL the non-reproducible control was accepted (exit $st)" >&2
    failed=1
  fi

  # The assertions: the positive control's two hashes agree; the negative control's
  # differ *at the same store path* (which is exactly why the path is not the invariant).
  python3 - "$good_json" "$bad_json" "$bad_path_before" <<'PY' || failed=1
import json, sys
good_path, bad_path, before = sys.argv[1], sys.argv[2], sys.argv[3]
bad = 0
def ok(name, cond, detail=""):
    global bad
    if not cond:
        bad = 1
    print(f"{'ok  ' if cond else 'FAIL'} {name}" + (f": {detail}" if detail and not cond else ""))
try:
    g = json.load(open(good_path, encoding="utf-8"))
except Exception as e:
    print(f"FAIL the positive control wrote no readable JSON: {e}")
    sys.exit(1)
ok("the positive control passes", g.get("ok") is True and g.get("status") == "ok",
   f"ok={g.get('ok')!r} status={g.get('status')!r}")
outs = g.get("outputs") or []
ok("the positive control compared an output", len(outs) == 1, f"{len(outs)} outputs")
if outs:
    ok("the positive control's two hashes are identical",
       outs[0].get("same") is True and outs[0].get("hashA") == outs[0].get("hashB")
       and bool(outs[0].get("hashA")),
       f"{outs[0].get('hashA')!r} vs {outs[0].get('hashB')!r}")
try:
    b = json.load(open(bad_path, encoding="utf-8"))
except Exception as e:
    print(f"FAIL the negative control wrote no readable JSON: {e}")
    sys.exit(1)
ok("the negative control fails for nondeterminism",
   b.get("ok") is False and b.get("status") == "diff"
   and b.get("reason") == "nondeterministic",
   f"ok={b.get('ok')!r} status={b.get('status')!r} reason={b.get('reason')!r}")
bouts = b.get("outputs") or []
ok("the negative control compared an output", len(bouts) == 1, f"{len(bouts)} outputs")
if bouts:
    ok("the negative control's two hashes differ",
       bouts[0].get("same") is False and bouts[0].get("hashA") != bouts[0].get("hashB")
       and bool(bouts[0].get("hashA")) and bool(bouts[0].get("hashB")),
       f"{bouts[0].get('hashA')!r} vs {bouts[0].get('hashB')!r}")
    ok("the negative control keeps the same store path",
       bouts[0].get("path") == before,
       f"{bouts[0].get('path')!r} vs {before!r}")
sys.exit(bad)
PY

  [ -n "${bad_path_after:-}" ] && [ "$bad_path_before" = "$bad_path_after" ] || {
    echo "FAIL the negative control's store path changed between builds; a path check" >&2
    echo "     would then have caught it and this test would not prove the hash comparison" >&2
    failed=1
  }

  if [ $keep = 0 ]; then rm -rf "$tmp"; else echo "self-test: kept $tmp" >&2; fi
  if [ $failed = 0 ]; then
    echo "self-test: ok (the reproducible control passes, the non-reproducible one is rejected)"
    return 0
  fi
  echo "self-test: failed" >&2
  return 1
}

if [ "$self_test" = 1 ]; then
  self_test_run
  exit $?
fi

# --- the gate ------------------------------------------------------------------------
start=$(date +%s)
work=$(mktemp -d "${TMPDIR:-/tmp}/check-repro-build.XXXXXX") || die "cannot make a temp dir"
if [ "$keep" = 1 ]; then
  echo "check-repro-build: logs in $work" >&2
else
  trap 'rm -rf "$work"' EXIT INT TERM
fi
records=$work/records.tsv
log_a=$work/build-a.log
log_b=$work/build-b.log
: > "$records"

first_args=()
[ -n "$dir_a" ] && first_args=(--option sandbox-build-dir "$dir_a")

# Nix refuses to check ("some outputs ... are not valid") a closure member it would have
# to build. Realise the derivation's build inputs first: on CI they are this commit's
# store paths from Cachix, including `unwrapped` (a build-time input of `wiz`, but not a
# runtime reference of it, so it is not in `wiz`'s substitution closure); locally a missing
# input is built here, once.
log_inputs=$work/inputs.log
drv=$(nix path-info --derivation "$attr" 2>/dev/null | head -n 1)
realised=1
if [ -n "$drv" ]; then
  mapfile -t inputs < <(nix-store -q --references "$drv" 2>/dev/null)
  if [ "${#inputs[@]}" -gt 0 ] && ! nix-store --realise "${inputs[@]}" > "$log_inputs" 2>&1; then
    record error "-" "" "" "the derivation's inputs could not be realised: $(tail -n 20 "$log_inputs")"
    status=error reason=build-failed
    realised=0
  fi
fi

# Build 1: the store's copy (on CI, the build job's Cachix path). A failure here is an
# error, not a reproducibility result: there is nothing to compare with.
if [ "$realised" = 0 ]; then
  : # already recorded above
elif ! nix build "$attr" --no-link -L "${first_args[@]}" 2>&1 | tee "$log_a" >&2; then
  record error "-" "" "" "build 1 failed: $(tail -n 20 "$log_a")"
  status=error reason=build-failed
else
  mapfile -t outs < <(nix path-info "$attr" 2>/dev/null | LC_ALL=C sort)
  if [ "${#outs[@]}" = 0 ]; then
    record error "-" "" "" "build 1 succeeded but reported no output path"
    status=error reason=build-failed
  else
    declare -A hash_a=()
    for p in "${outs[@]}"; do
      hash_a[$p]=$(hash_of "$p")
      drop_check "$p" # a stale scratch tree from an interrupted run
    done

    # Build 2: the same derivation, rebuilt under a different NIX_BUILD_TOP. Nix compares
    # the outputs itself and leaves a differing one at <out>.check.
    if nix build "$attr" --no-link --rebuild --keep-failed -L \
        --option sandbox-build-dir "$dir_b" 2>&1 | tee "$log_b" >&2; then
      status=ok reason=reproducible
      for p in "${outs[@]}"; do
        b=$(hash_of "$p")
        if [ "$b" = "${hash_a[$p]}" ] && [ -n "$b" ]; then
          record ok "$p" "${hash_a[$p]}" "$b" "rebuilt identically under NIX_BUILD_TOP $dir_b"
        else
          record diff "$p" "${hash_a[$p]}" "$b" "the rebuild succeeded but the hash differs"
        fi
      done
    else
      if grep -q 'may not be deterministic' "$log_b"; then
        reason=nondeterministic
      else
        reason=build-failed
      fi
      # The mismatch can be in any derivation of the closure, not only the requested
      # output: `--rebuild` checks all of them. Nix names each differing output and its
      # <out>.check in the log; hash that pair, so the failure names both hashes even when
      # the difference is in `unwrapped` (the Lean build). The top output's own check is
      # the same form.
      declare -A handled=()
      mapfile -t checks < <(grep -oE '/nix/store/[^"[:space:]]+\.check' "$log_b" | LC_ALL=C sort -u)
      for c in "${checks[@]}"; do
        base=${c%.check}
        handled[$base]=1
        a=$(hash_of "$base")
        b=$(hash_of "$c")
        if [ "$reason" = nondeterministic ]; then
          record diff "$base" "$a" "$b" \
            "a closure member differs; Nix left the second tree at $c (NIX_BUILD_TOP $dir_b)"
        else
          record error "$base" "$a" "$b" \
            "the rebuild failed for another reason: $(tail -n 20 "$log_b")"
        fi
      done
      for p in "${outs[@]}"; do
        [ "${handled[$p]:-0}" = 1 ] && continue
        record error "$p" "${hash_a[$p]}" "" \
          "the rebuild failed before it could compare: $(tail -n 20 "$log_b")"
      done
      if [ "$reason" = nondeterministic ]; then status="diff"; else status="error"; fi
    fi
  fi
fi

# The verdict: any non-ok record fails the gate. A diff is the interesting failure; an
# error (a builder that failed, an unbuildable installable) fails too, because the gate
# cannot claim reproducibility it did not observe.
verdict=ok
while IFS=$'\t' read -r rec_status rec_path rec_a rec_b rec_detail; do
  case $rec_status in
    ok) ;;
    diff|error) verdict=fail ;;
  esac
done < "$records"
[ "$status" = ok ] || verdict=fail

seconds=$(( $(date +%s) - start ))

if [ "$json" = 1 ]; then
  python3 - "$verdict" "$status" "$reason" "$seconds" "$attr" "$dir_a" "$dir_b" "$records" <<'PY'
import json, sys
verdict, status, reason, seconds, attr, dir_a, dir_b, records = sys.argv[1:9]
outputs = []
with open(records, encoding="utf-8") as f:
    for line in f:
        st, path, a, b, detail = line.rstrip("\n").split("\t", 4)
        outputs.append({"path": path, "hashA": a, "hashB": b,
                        "same": bool(a) and a == b, "status": st, "detail": detail})
print(json.dumps({
    "schema": "wiz-repro-build/v1",
    "ok": verdict == "ok",
    "status": status,
    "reason": reason,
    "attr": attr,
    "firstBuildDir": dir_a or None,
    "rebuildDir": dir_b,
    "runtimeSeconds": int(seconds),
    "outputs": outputs,
}, separators=(",", ":"), ensure_ascii=False))
PY
else
  echo "check-repro-build: $attr (first build dir: ${dir_a:-the store default}; rebuild dir: $dir_b)"
  while IFS=$'\t' read -r rec_status rec_path rec_a rec_b rec_detail; do
    case $rec_status in
      ok)
        printf 'ok    %s\n' "$rec_path"
        printf '      both builds: %s\n' "$rec_a"
        ;;
      diff)
        printf 'DIFF  %s\n' "$rec_path"
        printf '      build 1: %s\n' "$rec_a"
        printf '      build 2: %s\n' "$rec_b"
        ;;
      error)
        printf 'FAIL  %s: %s\n' "$rec_path" "$rec_detail"
        ;;
    esac
  done < "$records"
  if [ "$verdict" = ok ]; then
    echo "check-repro-build: ok in $seconds s (every output hash is identical)"
  else
    if [ "$reason" = nondeterministic ]; then
      echo "check-repro-build: FAILED in $seconds s: the same derivation built different bytes"
      echo "  the store path is identical in both builds: it hashes the derivation, not the output,"
      echo "  which is why the gate compares the output hash (nix hash path) and not the path"
    else
      echo "check-repro-build: FAILED in $seconds s: the rebuild did not complete (see above)"
    fi
    [ "$keep" = 0 ] && echo "  rerun with --keep to inspect the logs" >&2
  fi
fi

[ "$verdict" = ok ] && exit 0 || exit 1
