#!/bin/sh
# The host-side unsafe gate's own tests (scripts/host-unsafe-ledger.py): small Lean trees
# and ledgers, built here in a temporary directory, checking exit codes and messages,
# and that comments, strings and Wiz programs inside strings are not uses.
#
#   Tests/host-unsafe-ledger/run.sh
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
gate="python3 $root/scripts/host-unsafe-ledger.py"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
n=0

# `tree NAME`: a fresh tree $tmp/NAME with an empty Wiz/ (files are added by the case)
tree () { mkdir -p "$tmp/$1/Wiz" "$tmp/$1/.github"; : >"$tmp/$1/.github/host-unsafe.tsv"; }

# `expect STATUS NAME TEXT ARGS...`: run the gate on tree NAME; TEXT ('' for any) must be
# in its output
expect () {
  want=$1; name=$2; text=$3; shift 3
  n=$((n + 1))
  set +e
  $gate --root "$tmp/$name" "$@" >"$tmp/out" 2>&1
  got=$?
  set -e
  if [ "$got" != "$want" ] || { [ -n "$text" ] && ! grep -qF -- "$text" "$tmp/out"; }; then
    echo "host-unsafe-ledger fixtures: case $n ($name): want exit $want and '$text', got exit $got:" >&2
    cat "$tmp/out" >&2
    exit 1
  fi
}

row () { printf '%s\t%s\t%s\t%s\n' "$2" "$3" "$4" "$5" >>"$tmp/$1/.github/host-unsafe.tsv"; }

# 1. a listed use: clean
tree listed
cat >"$tmp/listed/Wiz/A.lean" <<'EOF'
private unsafe def getImpl (r : IO.Ref Nat) : Nat := unsafeBaseIO r.get
@[implemented_by getImpl] opaque get (r : IO.Ref Nat) : Nat
@[extern "c_f"] opaque f : IO Unit
EOF
row listed Wiz/A.lean getImpl unsafe,unsafeBaseIO "the cell is owned by one caller"
row listed Wiz/A.lean get implemented_by "opaque over getImpl"
row listed Wiz/A.lean f extern "IO only"
expect 0 listed "clean (3 uses, all listed)" --check

# 2. an unlisted use fails, and names the row to add
tree unlisted
cp "$tmp/listed/Wiz/A.lean" "$tmp/unlisted/Wiz/A.lean"
row unlisted Wiz/A.lean getImpl unsafe,unsafeBaseIO "owned by one caller"
row unlisted Wiz/A.lean get implemented_by "opaque over getImpl"
expect 1 unlisted "Wiz/A.lean	f	extern" --check

# 3. a row whose use is gone is stale
tree gone
cp "$tmp/listed/Wiz/A.lean" "$tmp/gone/Wiz/A.lean"
cp "$tmp/listed/.github/host-unsafe.tsv" "$tmp/gone/.github/host-unsafe.tsv"
row gone Wiz/A.lean old unsafe "was here once"
expect 1 gone "Wiz/A.lean old: no such use any more" --check

# 4. a use whose constructs changed is stale
tree changed
cp "$tmp/listed/Wiz/A.lean" "$tmp/changed/Wiz/A.lean"
row changed Wiz/A.lean getImpl unsafe "owned by one caller"
row changed Wiz/A.lean get implemented_by "opaque over getImpl"
row changed Wiz/A.lean f extern "IO only"
expect 1 changed "the row says unsafe, the code uses unsafe,unsafeBaseIO" --check

# 5. a row without an invariant fails
tree todo
cp "$tmp/listed/Wiz/A.lean" "$tmp/todo/Wiz/A.lean"
row todo Wiz/A.lean getImpl unsafe,unsafeBaseIO "TODO: the invariant"
row todo Wiz/A.lean get implemented_by "opaque over getImpl"
row todo Wiz/A.lean f extern "IO only"
expect 1 todo "without an invariant" --check

# 6. comments, doc comments, strings (plain, raw, interpolated with a nested string, a
# Wiz program) and char literals hold no use
tree quiet
cat >"$tmp/quiet/Wiz/B.lean" <<'EOF'
-- an unsafe def in a line comment
/-- a doc comment: `unsafeBaseIO`, `@[implemented_by g]`, /- nested unsafe -/ still -/
def words : List String := ["partial", "sealed", "unsafe"]
def wiz : String := "def f (n : Nat) : Nat := n\nattribute [implemented_by g] f\n"
def raw : String := r#"unsafe "quoted" @[extern "x"]"#
def msg (n : Nat) : String := s!"{String.join ["unsafe", toString n]} unsafeIO {"}"}"
def q : Char := '"'
def p : Char := '\''
def x' : Nat := 1
EOF
expect 0 quiet "clean (0 uses, all listed)" --check

# 7. a char literal or an interpolation does not hide a use that follows it; attributes
# on the line above and `attribute [...] f` commands are the declaration's
tree after
cat >"$tmp/after/Wiz/C.lean" <<'EOF'
def q : Char := '"'
def msg (n : Nat) : String := s!"{n} \" {"}"}"
@[never_extract]
@[implemented_by hImpl]
opaque h : Nat
def k : Nat := 0
attribute [implemented_by kImpl] k
unsafe def u : Nat := unsafeCast ()
EOF
expect 1 after "Wiz/C.lean	h	implemented_by" --check
expect 1 after "Wiz/C.lean	k	implemented_by" --check
expect 1 after "Wiz/C.lean	u	unsafe,unsafeCast" --check

# 8. --print lists the uses as rows
expect 0 listed "Wiz/A.lean	f	extern	TODO" --print

# 9. a malformed ledger is a usage error (exit 2)
tree bad
cp "$tmp/listed/Wiz/A.lean" "$tmp/bad/Wiz/A.lean"
printf 'Wiz/A.lean\tgetImpl\n' >"$tmp/bad/.github/host-unsafe.tsv"
expect 2 bad "want 4 tab-separated fields" --check

# 10. Tests/, Grail/ and root .lean files are scanned too
tree dirs
mkdir -p "$tmp/dirs/Tests/G" "$tmp/dirs/Grail"
echo 'unsafe def t : Nat := 0' >"$tmp/dirs/Tests/G/T.lean"
echo '@[extern "g"] opaque g : IO Unit' >"$tmp/dirs/Grail/E.lean"
echo 'def m : IO Unit := unsafeIO (pure ()) |> fun _ => pure ()' >"$tmp/dirs/Main.lean"
expect 1 dirs "Tests/G/T.lean	t	unsafe" --check
expect 1 dirs "Grail/E.lean	g	extern" --check
expect 1 dirs "Main.lean	m	unsafeIO" --check

# 11. the repository's own ledger is clean
n=$((n + 1))
$gate --check >"$tmp/out" 2>&1 || { echo "host-unsafe-ledger fixtures: the repository's ledger is not clean:" >&2; cat "$tmp/out" >&2; exit 1; }

echo "host-unsafe-ledger fixtures: $n cases passed"
