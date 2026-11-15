#!/bin/sh
# Tests for scripts/trust-ledger-merge.sh, the git merge driver of
# .github/trust-baseline.tsv. Run from anywhere; no build and no network.
#
#   scripts/trust-ledger-merge_test.sh
#
# The last case builds a throwaway git repository, installs the driver with
# `scripts/setup-trust-merge.sh`, and runs a real `git merge`: that is what proves
# the committed `.gitattributes` entry and the local registration work together.
set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
driver=$root/scripts/trust-ledger-merge.sh
setup=$root/scripts/setup-trust-merge.sh
tmp=$(mktemp -d "${TMPDIR:-/tmp}/trust-ledger-merge-test.XXXXXX")
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
n=0

fail () {
  echo "trust-ledger-merge_test: $1" >&2
  echo "--- stdout ---" >&2
  cat "$tmp/out" 2>/dev/null >&2 || true
  echo "--- stderr ---" >&2
  cat "$tmp/err" 2>/dev/null >&2 || true
  exit 1
}

# `run WANT NAME BASE OURS THEIRS`: run the driver on three files.
run () {
  want=$1
  name=$2
  shift 2
  n=$((n + 1))
  set +e
  "$driver" "$@" >"$tmp/out" 2>"$tmp/err"
  got=$?
  set -e
  [ "$got" -eq "$want" ] ||
    fail "$name: expected exit $want, got $got: $(cat "$tmp/err" 2>/dev/null)"
}

# `same NAME EXPECTED ACTUAL`: the driver's result is exactly the expected file.
same () {
  [ "$#" -eq 3 ] || fail "same: internal error"
  if ! diff -u "$2" "$3" >"$tmp/diff"; then
    fail "$1: expected and actual differ: $(cat "$tmp/diff")"
  fi
}

has () { # NAME FILE FRAGMENT
  grep -Fq -- "$3" "$2" || fail "$1: no line contains '$3'"
}

row () { # module declaration item reason owner review
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$@"
}

legacy='legacy: pre-gate baseline; not individually reviewed'

write_hdr () {
  printf '%s\n' '# the ledger' '# second header line'
}

# --- disjoint rows: the union, header once, sorted --------------------------------
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
} >"$tmp/o"
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A b 'axiom b' "$legacy" unassigned 2027-05-14
} >"$tmp/a"
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$tmp/b"
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A b 'axiom b' "$legacy" unassigned 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$tmp/want"
run 0 disjoint "$tmp/o" "$tmp/a" "$tmp/b"
same disjoint "$tmp/want" "$tmp/a"
[ "$(grep -c '^# the ledger$' "$tmp/a")" -eq 1 ] || fail "disjoint: header duplicated"

# --- the same key with the same content appears once ------------------------------
{
  write_hdr
  row K k 'axiom k' 'reviewed: fixture' owner 2027-05-14
} >"$tmp/o"
cp "$tmp/o" "$tmp/a"
cp "$tmp/o" "$tmp/b"
cp "$tmp/o" "$tmp/want"
run 0 same-content "$tmp/o" "$tmp/a" "$tmp/b"
same same-content "$tmp/want" "$tmp/a"

# --- one reasoned row, one legacy row: the reasoned row wins ----------------------
{
  write_hdr
  row K k 'axiom k' "$legacy" unassigned 2027-05-14
} >"$tmp/o"
cp "$tmp/o" "$tmp/a"
{
  write_hdr
  row K k 'axiom k' 'reviewed: theirs' reviewer 2027-05-14
} >"$tmp/b"
cp "$tmp/b" "$tmp/want"
run 0 reasoned-theirs "$tmp/o" "$tmp/a" "$tmp/b"
same reasoned-theirs "$tmp/want" "$tmp/a"

# The same, with ours reasoned and theirs untouched.
{
  write_hdr
  row K k 'axiom k' "$legacy" unassigned 2027-05-14
} >"$tmp/o"
{
  write_hdr
  row K k 'axiom k' 'reviewed: ours' reviewer 2027-05-14
} >"$tmp/a"
cp "$tmp/o" "$tmp/b"
cp "$tmp/a" "$tmp/want"
run 0 reasoned-ours "$tmp/o" "$tmp/a" "$tmp/b"
same reasoned-ours "$tmp/want" "$tmp/a"

# No base row (add/add): the reasoned row still wins over the legacy one.
: >"$tmp/o"
{
  write_hdr
  row K k 'axiom k' "$legacy" unassigned 2027-05-14
} >"$tmp/a"
{
  write_hdr
  row K k 'axiom k' 'reviewed: add/add' reviewer 2027-05-14
} >"$tmp/b"
cp "$tmp/b" "$tmp/want"
run 0 reasoned-add-add "$tmp/o" "$tmp/a" "$tmp/b"
same reasoned-add-add "$tmp/want" "$tmp/a"

# --- two reasoned rows differ: refuse, name the key, leave ours alone -------------
{
  write_hdr
  row K k 'axiom k' "$legacy" unassigned 2027-05-14
} >"$tmp/o"
{
  write_hdr
  row K k 'axiom k' 'reviewed: ours' reviewer 2027-05-14
} >"$tmp/a"
{
  write_hdr
  row K k 'axiom k' 'reviewed: theirs' reviewer 2027-05-14
} >"$tmp/b"
cp "$tmp/a" "$tmp/a-orig"
run 1 two-reasoned "$tmp/o" "$tmp/a" "$tmp/b"
has two-reasoned "$tmp/err" 'K | k | axiom k'
has two-reasoned "$tmp/err" 'refusing to choose'
cmp -s "$tmp/a" "$tmp/a-orig" || fail "two-reasoned: ours was modified on failure"

# --- two legacy rows differ: refuse too -------------------------------------------
{
  write_hdr
  row K k 'axiom k' "$legacy" unassigned 2027-05-14
} >"$tmp/o"
{
  write_hdr
  row K k 'axiom k' 'legacy: ours' unassigned 2027-05-14
} >"$tmp/a"
{
  write_hdr
  row K k 'axiom k' 'legacy: theirs' unassigned 2027-05-14
} >"$tmp/b"
run 1 two-legacy "$tmp/o" "$tmp/a" "$tmp/b"
has two-legacy "$tmp/err" 'K | k | axiom k'

# --- comments and headers: kept once, base first, then the new ones ---------------
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
} >"$tmp/o"
{
  write_hdr
  printf '%s\n' '# ours note'
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A b 'axiom b' "$legacy" unassigned 2027-05-14
} >"$tmp/a"
{
  write_hdr
  printf '%s\n' '# theirs note' '# shared note'
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$tmp/b"
# Make both sides add the same comment: it must appear once.
printf '%s\n' '# shared note' >>"$tmp/a"
{
  write_hdr
  printf '%s\n' '# ours note' '# shared note' '# theirs note'
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A b 'axiom b' "$legacy" unassigned 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$tmp/want"
run 0 comments "$tmp/o" "$tmp/a" "$tmp/b"
same comments "$tmp/want" "$tmp/a"
[ "$(grep -c '^# shared note$' "$tmp/a")" -eq 1 ] || fail "comments: shared comment duplicated"
[ "$(grep -c '^# the ledger$' "$tmp/a")" -eq 1 ] || fail "comments: header duplicated"

# --- CRLF inputs are accepted and the result is LF -------------------------------
{
  printf '%s\r\n' '# the ledger' '# second header line'
  row A a 'axiom a' "$legacy" unassigned 2027-05-14 | tr -d '\n'
  printf '\r\n'
} >"$tmp/o"
{
  printf '%s\r\n' '# the ledger' '# second header line'
  row A a 'axiom a' "$legacy" unassigned 2027-05-14 | tr -d '\n'
  printf '\r\n'
  row A b 'axiom b' "$legacy" unassigned 2027-05-14 | tr -d '\n'
  printf '\r\n'
} >"$tmp/a"
{
  printf '%s\r\n' '# the ledger' '# second header line'
  row A a 'axiom a' "$legacy" unassigned 2027-05-14 | tr -d '\n'
  printf '\r\n'
  row A c 'axiom c' "$legacy" unassigned 2027-05-14 | tr -d '\n'
  printf '\r\n'
} >"$tmp/b"
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A b 'axiom b' "$legacy" unassigned 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$tmp/want-crlf"
run 0 crlf "$tmp/o" "$tmp/a" "$tmp/b"
same crlf "$tmp/want-crlf" "$tmp/a"
if grep -q "$(printf '\r')" "$tmp/a"; then
  fail "crlf: the result still contains a carriage return"
fi

# --- 100 pseudo-random rows: union, sorted, no duplicate keys --------------------
awk -v afile="$tmp/fuzz.a" -v bfile="$tmp/fuzz.b" -v ofile="$tmp/fuzz.o" \
  -v expfile="$tmp/fuzz.exp" '
BEGIN {
  print "# fuzz ledger" > ofile
  print "# 100 rows" > ofile
  print "# fuzz ledger" > afile
  print "# 100 rows" > afile
  print "# fuzz ledger" > bfile
  print "# 100 rows" > bfile
  legacy = "legacy: pre-gate baseline; not individually reviewed"
  reasoned = "reviewed by the fuzz fixture"
  review = "2027-05-14"
  for (j = 0; j < 100; j++) {
    i = (j * 37) % 100
    key = "M" (i % 7) "\td" i "\taxiom x" i
    r = i % 5
    if (r == 0) {
      a = key "\t" reasoned "\tfuzz\t" review
      b = a
      e = a
    } else if (r == 1) {
      a = key "\t" legacy "\tunassigned\t" review
      b = key "\t" reasoned "\tfuzz\t" review
      e = b
    } else if (r == 2) {
      a = key "\t" reasoned "\tfuzz\t" review
      e = a
    } else if (r == 3) {
      b = key "\t" reasoned "\tfuzz\t" review
      e = b
    } else {
      a = key "\t" legacy "\tunassigned\t" review
      e = a
    }
    if (a != "") print a > afile
    if (b != "") print b > bfile
    print e > expfile
  }
}'
{
  printf '%s\n' '# fuzz ledger' '# 100 rows'
  LC_ALL=C sort "$tmp/fuzz.exp"
} >"$tmp/fuzz.want"
run 0 fuzz "$tmp/fuzz.o" "$tmp/fuzz.a" "$tmp/fuzz.b"
same fuzz "$tmp/fuzz.want" "$tmp/fuzz.a"
[ "$(awk '!/^#/ && NF' "$tmp/fuzz.a" | wc -l)" -eq 100 ] ||
  fail "fuzz: expected 100 rows, got $(awk '!/^#/ && NF' "$tmp/fuzz.a" | wc -l)"
dups=$(awk -F'\t' '!/^#/ && NF { print $1 "\t" $2 "\t" $3 }' "$tmp/fuzz.a" |
  LC_ALL=C sort | uniq -d)
[ -z "$dups" ] || fail "fuzz: duplicate keys: $dups"

# --- a real git merge through .gitattributes and setup-trust-merge.sh ------------
repo=$tmp/repo
mkdir -p "$repo/.github" "$repo/scripts"
cp "$root/.gitattributes" "$repo/.gitattributes"
cp "$driver" "$repo/scripts/trust-ledger-merge.sh"
cp "$setup" "$repo/scripts/setup-trust-merge.sh"
chmod +x "$repo/scripts/trust-ledger-merge.sh" "$repo/scripts/setup-trust-merge.sh"
git -C "$repo" init -q -b main
git -C "$repo" config user.name 'merge fixture'
git -C "$repo" config user.email 'merge@example.invalid'
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$repo/.github/trust-baseline.tsv"
git -C "$repo" add -A
git -C "$repo" commit -qm base

git -C "$repo" checkout -qb ours
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A b 'axiom b' 'reviewed: ours' reviewer 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$repo/.github/trust-baseline.tsv"
git -C "$repo" commit -qam ours

git -C "$repo" checkout -q main
git -C "$repo" checkout -qb theirs
{
  write_hdr
  row A a 'axiom a' "$legacy" unassigned 2027-05-14
  row A bc 'axiom bc' 'reviewed: theirs' reviewer 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$repo/.github/trust-baseline.tsv"
git -C "$repo" commit -qam theirs

git -C "$repo" checkout -q ours
# The registration: committed .gitattributes names the driver, the setup script
# puts the command in this clone's local config.
attr=$(git -C "$repo" check-attr merge -- .github/trust-baseline.tsv)
case $attr in
  *'merge: trust-ledger') ;;
  *) fail "git: .gitattributes does not select trust-ledger: $attr" ;;
esac
(cd "$repo" && "$repo/scripts/setup-trust-merge.sh" >"$tmp/out" 2>"$tmp/err") ||
  fail "git: setup-trust-merge.sh failed"
configured=$(git -C "$repo" config --get merge.trust-ledger.driver)
case $configured in
  *trust-ledger-merge.sh*'%O %A %B'*) ;;
  *) fail "git: merge.trust-ledger.driver is '$configured'" ;;
esac

n=$((n + 1))
set +e
git -C "$repo" merge --no-edit theirs >"$tmp/out" 2>"$tmp/err"
got=$?
set -e
[ "$got" -eq 0 ] || fail "git: the merge through the driver failed: $(cat "$tmp/err")"
has git "$repo/.github/trust-baseline.tsv" 'axiom b'
has git "$repo/.github/trust-baseline.tsv" 'axiom bc'
if grep -q '^<<<<<<<\|^=======$\|^>>>>>>>' "$repo/.github/trust-baseline.tsv"; then
  fail "git: conflict markers in the merged ledger"
fi
if git -C "$repo" ls-files -u | grep -q .; then
  fail "git: the merge left an unmerged path"
fi

# The same registration refuses a real conflict: two reasoned rows for one key.
git -C "$repo" checkout -q -b conflict-a main
{
  write_hdr
  row A a 'axiom a' 'reviewed: conflict a' reviewer 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$repo/.github/trust-baseline.tsv"
git -C "$repo" commit -qam conflict-a
git -C "$repo" checkout -q -b conflict-b main
{
  write_hdr
  row A a 'axiom a' 'reviewed: conflict b' reviewer 2027-05-14
  row A c 'axiom c' "$legacy" unassigned 2027-05-14
} >"$repo/.github/trust-baseline.tsv"
git -C "$repo" commit -qam conflict-b
git -C "$repo" checkout -q conflict-a
n=$((n + 1))
set +e
git -C "$repo" merge --no-edit conflict-b >"$tmp/out" 2>"$tmp/err"
got=$?
set -e
[ "$got" -ne 0 ] || fail "git: an ambiguous ledger merge exited 0"
has git-conflict "$tmp/err" 'conflicting ledger rows'
has git-conflict "$tmp/err" 'A | a | axiom a'
git -C "$repo" status --porcelain | grep -q '^UU \.github/trust-baseline\.tsv$' ||
  fail "git: the conflict is not marked unmerged"
git -C "$repo" merge --abort

echo "trust-ledger-merge_test: OK ($n checks)"
