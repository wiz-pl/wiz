#!/usr/bin/env bash
# Reproduce scry/CSHARP.md §7's counts on a directory of C# sources.
#
#   scry/scripts/cs-coverage.sh DIR                 # construct frequencies
#   CS_COVER=… scry/scripts/cs-coverage.sh DIR      # + per-file parse/lower/taint
#   SCRY_RULES=… (default: scry/corpus/csharp/csharp.scry)
#
# `node_modules/`, `bin/` and `obj/` are excluded from every count (the same rules
# `Scry.CsCmd`'s walk applies, without the `.g.cs`/symlink rules).
#
# The first section is a regular-expression count of the constructs the frontend is
# audited on: it is a *lower bound* (a construct inside a comment or a string can match,
# a construct split across lines can be missed), so the table in CSHARP.md quotes the
# expression next to the number. The second section is the measurement proper: it spills
# each file with `scry-cst` and runs `cs-cover`, which prints one record per file
# (`FILE path functions warnings findings`), the warnings, and the taint findings.
# A file with `functions 0 warnings 0` is the silent skip §7 is about.
set -u

DIR=${1:?usage: cs-coverage.sh DIR}
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH= cd -- "$HERE/../.." && pwd)
EXCL=(-g '!**/node_modules/**' -g '!**/bin/**' -g '!**/obj/**' -g '*.cs')

count() { # name pattern
  local name=$1 pat=$2 o f
  o=$(rg --pcre2 -o "${EXCL[@]}" -e "$pat" "$DIR" 2>/dev/null | wc -l)
  f=$(rg --pcre2 -l "${EXCL[@]}" -e "$pat" "$DIR" 2>/dev/null | wc -l)
  printf '%-32s\t%8s\t%6s\n' "$name" "$o" "$f"
}

files=$(rg --files "${EXCL[@]}" "$DIR" 2>/dev/null | wc -l)
echo "# construct frequencies in $DIR"
echo "# .cs files: $files"
printf '%-32s\t%8s\t%6s\n' "construct" "occurrences" "files"
count "async"                  '\basync\b'
count "await"                  '\bawait\b'
count "record declaration"     '\brecord\s+(class|struct)?\s*[A-Za-z_]'
count "file-scoped namespace"  '(?m)^\s*namespace\s+[\w.]+\s*;'
count "using static"           '(?m)^\s*using\s+static\s'
count "switch expression"      '\bswitch\b(?!\s*\()'
count "is pattern"             '\bis\s+(?:not\s+)?(?:null|\{|[A-Za-z_])'
count "nullable annotation"    '[\w>\])]\?\s+(?:[A-Za-z_@]|[,)>\]])'
count "generic constraint"     '\bwhere\s+[A-Za-z_]\w*\s*:'
count "partial type"           '\bpartial\s+(class|struct|record|interface|enum)\b'
count "attribute list"         '(?m)^\s*\[[A-Z][\w.]*'
count "string interpolation"   '\$@?"'
count "LINQ query"             '\bfrom\s+[A-Za-z_]\w*\s+in\b'
count "LINQ method call"       '\.(Where|Select|SelectMany|OrderBy|OrderByDescending|First|FirstOrDefault|Any|All|ToList|ToArray|GroupBy|Sum|Count)\s*\('

CST=${SCRY_CST:-}
COVER=${CS_COVER:-}
if [ -z "$COVER" ]; then
  echo "# (no CS_COVER: skipping the parse/lower/taint measurement)"
  echo "#   build the probe in a scratch copy (it needs the native grammar):"
  echo "#     cd scry && wiz build tools/CsCover.wiz -I src -I ../lib -o build/cs-cover"
  exit 0
fi

RULES=${SCRY_RULES:-$REPO/scry/corpus/csharp/csharp.scry}
OUT=${CS_OUT:-$REPO/scry/build/cs-coverage}
mkdir -p "$OUT"
: > "$OUT/cover.tsv"

echo "# parse / lower / taint, one record per file"
"$COVER" "$DIR" "$RULES" > "$OUT/cover.tsv" 2> "$OUT/cover.err"
fail=$(grep -c '^PARSE' "$OUT/cover.tsv" || true)
data=$(grep -c '^FILE' "$OUT/cover.tsv" || true)
funcs=$(awk -F'\t' '$1=="FILE"{s+=$3}END{print s+0}' "$OUT/cover.tsv")
warns=$(awk -F'\t' '$1=="WARN"' "$OUT/cover.tsv" | wc -l)
finds=$(awk -F'\t' '$1=="FIND"' "$OUT/cover.tsv" | wc -l)
# A file with no function is only suspicious when it has an executable member: a
# declaration-only DTO/interface file (records, no `=>` or `{` body) genuinely has
# none. The distinction is the point — "functions 0" alone is not a silent skip.
zero=$(awk -F'\t' '$1=="FILE"&&$3==0&&$4==0 {print $2}' "$OUT/cover.tsv")
decl=0; silent=0; silent_list=""
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if rg -q '\)\s*(=>|\{)|^\s*\{|=\s*>' "$f" 2>/dev/null; then
    silent=$((silent + 1)); silent_list="$silent_list $f"
  else
    decl=$((decl + 1))
  fi
done <<< "$zero"
echo "# files: $files; parsed+lowered: $data; parse failures: $fail"
echo "# lowered functions: $funcs; warnings: $warns; findings: $finds"
echo "# files with 0 functions: $((decl + silent)) (declaration-only: $decl; with code: $silent)"
[ -n "$silent_list" ] && echo "# SILENT (no function, no warning, but has code):$silent_list"
echo "# warnings by message:"
awk -F'\t' '$1=="WARN"{sub(/^WARN\t[^\t]*\t/,""); print}' "$OUT/cover.tsv" \
  | sed -E -e 's/^unknown name .* not modelled/unknown name not modelled/' \
      -e 's/^call to [^:]+:/call to NAME:/' \
      -e 's/^(field|property) initialiser of .* not modelled/\1 initialiser not modelled/' \
      -e 's/^local function .* not modelled/local function NAME not modelled/' \
  | sort | uniq -c | sort -rn
echo "# records: $OUT/cover.tsv"
