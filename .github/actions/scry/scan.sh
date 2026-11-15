#!/usr/bin/env bash
# Run scry over the C files a PR changes and merge their SARIF/JSON.
#
# The analysis itself is `scry taint FILE.c --diff BASE --sarif OUT --json`. scry taint
# analyses one translation unit at a time, so this script runs it per changed .c file
# and merge.py unions the SARIF results. `--diff` is what makes the report about this
# pull request: findings on unchanged lines stay in the SARIF with
# `baselineState: unchanged`, and their count is reported, never silently dropped.
#
# Exit status: 0 when the analysis ran (even with findings; the action's gate step
# applies fail-on-finding), 1 on a usage/analysis error, so a broken SARIF can never be
# uploaded by a later step.
set -euo pipefail

action_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
say() { printf 'scry: %s\n' "$*"; }
die() { printf 'scry: error: %s\n' "$*" >&2; exit 1; }

: "${SCRY_BIN:?SCRY_BIN is not set (resolve.sh must run first)}"
[ -x "$SCRY_BIN" ] || die "not executable: $SCRY_BIN"

workdir="${INPUT_WORKING_DIRECTORY:-.}"
[ -d "$workdir" ] || die "working-directory does not exist: $workdir"
repo_root=$(git -C "$workdir" rev-parse --show-toplevel 2>/dev/null) \
  || die "not a git checkout: $workdir"

# The SARIF path is relative to the repository root, like the paths input.
sarif="${INPUT_SARIF:-scry.sarif}"
case "$sarif" in
  /*) ;;
  *) sarif="$repo_root/$sarif" ;;
esac
mkdir -p "$(dirname "$sarif")"

# `paths` is a whitespace-separated list; the default is the whole repository.
paths="${INPUT_PATHS:-.}"
read -r -a path_args <<< "$paths"
[ "${#path_args[@]}" -gt 0 ] || path_args=(.)

# ---------------------------------------------------------------------------
# Diff base. `auto` means the pull request's base branch. A checkout with
# fetch-depth: 0 has origin/<base>; without it, fall back to the synthetic merge
# commit's first parent, which is the same diff. A push/manual run has no base
# branch, so `auto` degrades to the whole tree and says so.
# ---------------------------------------------------------------------------
base="${INPUT_DIFF:-auto}"
case "$base" in
  ""|auto)
    if [ -n "${GITHUB_BASE_REF:-}" ]; then
      base="origin/${GITHUB_BASE_REF}"
      if ! git -C "$repo_root" rev-parse -q --verify "${base}^{commit}" >/dev/null; then
        git -C "$repo_root" fetch --no-tags --depth=1 origin \
          "+refs/heads/${GITHUB_BASE_REF}:refs/remotes/${base}" 2>/dev/null || true
      fi
      if ! git -C "$repo_root" rev-parse -q --verify "${base}^{commit}" >/dev/null; then
        if [ "$(git -C "$repo_root" rev-list --parents -n 1 HEAD | wc -w)" -gt 2 ]; then
          base=HEAD^1
          say "origin/${GITHUB_BASE_REF} is not present; diffing the merge commit against HEAD^1"
        else
          printf '::warning::scry: no origin/%s and no merge commit; analysing the whole tree\n' \
            "$GITHUB_BASE_REF"
          base=all
        fi
      fi
    else
      base=all
    fi
    ;;
  all) ;;
  *) ;;
esac
if [ "$base" != all ]; then
  git -C "$repo_root" rev-parse -q --verify "${base}^{commit}" >/dev/null \
    || die "diff base is not a commit: $base"
fi

# ---------------------------------------------------------------------------
# Candidate files: changed .c files in diff mode, every tracked/untracked .c file
# otherwise. Headers are not analysed on their own (scry taint does not preprocess
# includes, so a header has no translation unit); a changed header alone is reported
# as "no C files", not as a clean result.
# ---------------------------------------------------------------------------
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
candidates="$tmp/candidates"
if [ "$base" = all ]; then
  git -C "$repo_root" ls-files -z --cached --others --exclude-standard -- \
    "${path_args[@]}" > "$candidates"
else
  git -C "$repo_root" diff --name-only --diff-filter=ACMR -z "$base" -- \
    "${path_args[@]}" > "$candidates"
fi

cd "$repo_root"
files=()
while IFS= read -r -d '' f; do
  case "$f" in
    *.c) [ -f "$f" ] && files+=("$f") ;;
  esac
done < "$candidates"

allow_errors="${INPUT_ALLOW_ERRORS:-false}"
extra_args="${INPUT_EXTRA_ARGS:-}"

if [ "${#files[@]}" -eq 0 ]; then
  python3 "$action_dir/merge.py" --out-sarif "$sarif" --out-counts "$tmp/counts.json" \
    --out-summary "$tmp/summary.md" --base "$base" --empty
  python3 "$action_dir/validate-sarif.py" "$sarif"
  say "no C files to analyse (paths: ${paths}; base: ${base})"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    cat "$tmp/summary.md" >> "$GITHUB_STEP_SUMMARY"
  fi
  cat "$tmp/summary.md"
  {
    echo "sarif=$sarif"
    echo "shown=0"
    echo "suppressed=0"
    echo "gate=0"
    echo "skip-upload=true"
  } >> "${GITHUB_OUTPUT:-/dev/null}"
  exit 0
fi

say "analysing ${#files[@]} file(s) against ${base}"
i=0
for f in "${files[@]}"; do
  out="$tmp/$i.sarif"
  args=(taint "$f")
  if [ "$base" != all ]; then
    args+=(--diff "$base")
  fi
  if [ -n "${SCRY_RULES:-}" ]; then
    args+=(--rules "$SCRY_RULES")
  fi
  if [ "$allow_errors" = true ]; then
    args+=(--allow-errors)
  fi
  if [ -n "$extra_args" ]; then
    read -r -a extra <<< "$extra_args"
    args+=("${extra[@]}")
  fi
  args+=(--sarif "$out" --json)

  if "$SCRY_BIN" "${args[@]}" > "$tmp/$i.json" 2> "$tmp/$i.err"; then
    :
  else
    status=$?
    printf 'scry: %s failed (exit %s)\n' "$f" "$status" >&2
    cat "$tmp/$i.err" >&2
    die "analysis failed on $f; no SARIF was uploaded"
  fi
  if [ -s "$tmp/$i.err" ]; then
    sed 's/^/  /' "$tmp/$i.err" >&2
  fi
  i=$((i + 1))
done

python3 "$action_dir/merge.py" --out-sarif "$sarif" --out-counts "$tmp/counts.json" \
  --out-summary "$tmp/summary.md" --base "$base"
python3 "$action_dir/validate-sarif.py" "$sarif"

read_counts=$(python3 - "$tmp/counts.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
print(d["findings"]["shown"], d["findings"]["suppressed"], d["gate"])
PY
)
read -r shown suppressed gate <<< "$read_counts"

say "$(python3 - "$tmp/counts.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
print(f'{d["findings"]["shown"]} finding(s) on changed lines, '
      f'{d["findings"]["suppressed"]} on unchanged lines, '
      f'{d["results"]} SARIF result(s) in {d["sarif"]}')
PY
)"

if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  cat "$tmp/summary.md" >> "$GITHUB_STEP_SUMMARY"
fi
cat "$tmp/summary.md"
{
  echo "sarif=$sarif"
  echo "shown=$shown"
  echo "suppressed=$suppressed"
  echo "gate=$gate"
  echo "skip-upload=false"
} >> "${GITHUB_OUTPUT:-/dev/null}"
