#!/bin/sh
# Audit the FFI part of the trust ledger: every `extern "SYM" name : …` in lib/ has two
# ledger rows (the `axiom name` for the C function, and the `builtin extern:SYM:…` for
# the marshalling).  This lists each one with its C symbol and whether both rows are
# reviewed, and (with --check) compiles a generated function-pointer assignment for each
# symbol against the real C prototype.
#
#   scripts/trust-ffi-audit.sh                 list every extern
#   scripts/trust-ffi-audit.sh --legacy        only the externs still `legacy:`
#   scripts/trust-ffi-audit.sh --check         signature check (needs cc; fails on drift)
#   scripts/trust-ffi-audit.sh --strict        with --check: also fail on legacy rows
#   scripts/trust-ffi-audit.sh Sys IO          restrict to those modules
#
# The signature check is generated, not eyeballed: for each ledger
# `builtin extern:SYM:params:result:…`, it writes
#
#   static <result> (*chk_N)(<params>) = SYM;
#
# with the C types the Wiz marshalling uses (n/u uint64_t, f double, s const char *,
# b int, p void *, w wiz_val, y a borrowed const void * + size_t) and compiles it with
# `cc -fsyntax-only` against runtime/wiz_rt.h and lib/serial.c.  A changed arity or type,
# or a symbol that no longer exists, is a compile error.  `cc` must find GMP: pass its
# include path in WIZ_CFLAGS, or let the script read `cflags` from grail.local.wiz.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
ledger=.github/trust-baseline.tsv
check=0
strict=0
only_legacy=0
modules=

usage () {
  sed -n '2,22p' "$0" | sed 's/^# \{0,1\}//'
}

for arg in "$@"; do
  case $arg in
    --check) check=1 ;;
    --strict) strict=1 ;;
    --legacy) only_legacy=1 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "trust-ffi-audit: unknown option: $arg" >&2; exit 2 ;;
    *) modules="$modules $arg" ;;
  esac
done

files=
if [ -n "$modules" ]; then
  for m in $modules; do
    f=lib/$m.wiz
    if [ ! -f "$f" ]; then
      echo "trust-ffi-audit: no $f" >&2
      exit 2
    fi
    files="$files $f"
  done
else
  files=$(ls lib/*.wiz)
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/trust-ffi.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

# module, line, declaration, C symbol, private?
: > "$tmp/externs"
for f in $files; do
  mod=$(basename "$f" .wiz)
  awk -v mod="$mod" '
    /^[ \t]*(private[ \t]+)?extern[ \t]+"/ {
      priv = ($0 ~ /^[ \t]*private[ \t]+extern[ \t]+"/) ? 1 : 0
      s = $0; sub(/^[^"]*"/, "", s); sym = s; sub(/".*/, "", sym)
      n = $0; sub(/^[^"]*"[^"]*"[ \t]+/, "", n); sub(/[ \t:].*/, "", n)
      print mod "\t" FNR "\t" n "\t" sym "\t" priv
    }
  ' "$f" >> "$tmp/externs"
done

# Join with the ledger: status, location, name, symbol, marshalling, axiom reason,
# builtin reason.
awk -F '\t' '
  FNR == NR {
    if ($1 == "module") next
    mod = $1; decl = $2; item = $3; reason = $4
    if (item == "axiom " decl) ax[mod SUBSEP decl] = reason
    if (index(item, "builtin extern:") == 1) {
      rest = substr(item, length("builtin extern:") + 1)
      p = index(rest, " := ")
      if (p) {
        left = substr(rest, 1, p - 1); decl2 = substr(rest, p + 4)
        split(left, a, ":")
        key = mod SUBSEP a[1] SUBSEP decl2
        bi[key] = reason; bp[key] = a[2]; br[key] = a[3]
      }
    }
    next
  }
  {
    mod = $1; line = $2; name = $3; sym = $4; priv = $5
    decl = name
    if (priv == 1) decl = "_private." mod "._0." name
    key = mod SUBSEP sym SUBSEP decl
    akey = mod SUBSEP decl
    ar = (akey in ax) ? ax[akey] : "<no axiom row>"
    brr = (key in bi) ? bi[key] : "<no builtin row>"
    st = "reviewed"
    if (ar ~ /^legacy:/ || brr ~ /^legacy:/ || ar == "<no axiom row>" || brr == "<no builtin row>") st = "legacy"
    codes = (key in bp) ? bp[key] "->" br[key] : "?"
    print st "\t" mod ":" line "\t" name "\t" sym "\t" codes "\t" ar "\t" brr
  }
' "$ledger" "$tmp/externs" > "$tmp/joined"

# The C definition (not the header prototype) for a symbol.
cdef () {
  grep -RInE "(WIZ_API[[:space:]]+)?[A-Za-z_][A-Za-z0-9_ *]*[ *]$1[[:space:]]*\(" \
    runtime/*.inc lib/*.c c/*.c 2>/dev/null | head -1 || true
}

bad=0
skipped=0
nall=0
nlegacy=0
while IFS='	' read -r status loc name sym codes ar br; do
  nall=$((nall + 1))
  if [ "$status" = legacy ]; then nlegacy=$((nlegacy + 1)); fi
  if [ "$only_legacy" = 1 ] && [ "$status" != legacy ]; then
    continue
  fi
  d=$(cdef "$sym")
  [ -n "$d" ] || d="<no C definition>"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$status" "$loc" "$name" "$sym" "$d" "$codes"
done < "$tmp/joined"

if [ "$check" = 0 ]; then
  if [ "$strict" = 1 ] && [ "$nlegacy" != 0 ]; then
    echo "trust-ffi-audit: $nlegacy of $nall externs are still legacy" >&2
    exit 1
  fi
  exit 0
fi

# A missing row cannot be signature-checked.
if awk -F '\t' '$5 == "?" || $6 == "<no axiom row>" || $7 == "<no builtin row>" { found = 1 } END { exit !found }' "$tmp/joined"; then
  echo "trust-ffi-audit: externs without both ledger rows:" >&2
  awk -F '\t' '$5 == "?" || $6 == "<no axiom row>" || $7 == "<no builtin row>" { print "  " $2 " " $3 " (" $4 ")" }' "$tmp/joined" >&2
  bad=1
fi

# A reviewed reason must name the C symbol (otherwise a bulk renewal could hide a
# declaration's contract).
if ! awk -F '\t' '
  $1 == "reviewed" && (index($6, $4) == 0 || index($7, $4) == 0) {
    print "  " $2 " " $3 ": reason does not name " $4
    bad = 1
  }
  END { exit bad }
' "$tmp/joined" >&2; then
  bad=1
fi

# Generate the C signature check.
awk -F '\t' '
  function ctype(c) {
    if (c == "n" || c == "u") return "uint64_t"
    if (c == "f") return "double"
    if (c == "s") return "const char *"
    if (c == "b") return "int"
    if (c == "p") return "void *"
    if (c == "w") return "wiz_val"
    if (c == "y") return "const void *, size_t"
    return ""
  }
  function params(s,   i, c, t, out) {
    out = ""
    for (i = 1; i <= length(s); i++) {
      c = substr(s, i, 1)
      if (c == "e") continue          # erased: no C argument
      t = ctype(c)
      if (t == "") return "?"
      out = out (out == "" ? "" : ", ") t
    }
    return out == "" ? "void" : out
  }
  $5 != "?" {
    split($5, c, "->")
    ps = params(c[1])
    if (ps == "?") { print "/* bad parameter code: " $4 " */"; bad = 1; next }
    if (c[2] == "v") rt = "void"
    else rt = ctype(c[2])
    if (rt == "") { print "/* bad result code: " $4 " */"; bad = 1; next }
    printf "static %s (*chk_%d)(%s) = %s;\n", rt, NR, ps, $4
  }
  END { exit bad }
' "$tmp/joined" > "$tmp/check.c" || bad=1

if [ "${TRUST_FFI_DEBUG:-0}" = 1 ]; then
  cp "$tmp/joined" /tmp/trust-ffi-joined.tsv
  cp "$tmp/check.c" /tmp/trust-ffi-check.c
fi

if [ "$bad" = 0 ]; then
  {
    printf '#define WIZ_API\n'
    printf '#include "runtime/wiz_rt.h"\n'
    printf '#include "lib/serial.c"\n'
    cat "$tmp/check.c"
  } > "$tmp/sig.c"

  if ! command -v cc >/dev/null 2>&1; then
    echo "trust-ffi-audit: no cc on PATH; cannot check signatures" >&2
    exit 2
  fi
  cflags=${WIZ_CFLAGS:-}
  if [ -z "$cflags" ] && [ -f grail.local.wiz ]; then
    cflags=$(sed -n 's/.*Settings.set "cflags" "\([^"]*\)".*/\1/p' grail.local.wiz | head -1)
  fi
  # shellcheck disable=SC2086
  if ! cc $cflags -I "$root" -fsyntax-only "$tmp/sig.c" 2>"$tmp/cc.err"; then
    if grep -q 'gmp.h' "$tmp/cc.err"; then
      echo "trust-ffi-audit: signature check skipped: cc cannot find gmp.h (set WIZ_CFLAGS)" >&2
      skipped=1
    else
      cat "$tmp/cc.err" >&2
      bad=1
    fi
  fi
fi

if [ "$bad" != 0 ]; then
  echo "trust-ffi-audit: signature check failed" >&2
  exit 1
fi
if [ "$strict" = 1 ] && [ "$nlegacy" != 0 ]; then
  echo "trust-ffi-audit: $nlegacy of $nall externs are still legacy" >&2
  exit 1
fi
if [ "$skipped" = 1 ]; then
  echo "trust-ffi-audit: $nall externs, $nlegacy legacy; signature check skipped"
else
  echo "trust-ffi-audit: $nall externs, $nlegacy legacy; signatures match the C prototypes"
fi
