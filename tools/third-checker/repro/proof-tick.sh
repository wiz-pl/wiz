#!/usr/bin/env bash
# Minimal reproducer: the host interpreter (`wiz check`) panics on a term that reaches
# the self-hosted kernel's proof suspender, because `wiz_proof_tick` is a native.
#
#   ./tools/third-checker/repro/proof-tick.sh
#   ... PANIC at Wiz.fireNative ... extern:wiz_proof_tick ... only in compiled code
#
# `wiz run` (the compiled driver) checks the same term; `corpus.dump` has the OK line.
set -euo pipefail
cd "$(dirname "$0")/../../.."
WIZ_BIN=${WIZ_BIN:-.lake/build/bin/wiz}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
python3 - "$tmp/probe.wiz" <<'PY'
import sys
src = open("selfhost/Kernel.wiz").read()
body = "\n".join(l for l in src.split("\n") if not l.startswith("import"))
probe = """
def vd (ty v : Tm) : String := match checkDecl ty (.some v) with
  | .ok _ _ => "OK"
  | .err m => String.append "ERR " m
-- transp Unit tt (fun _ _ => True) tt tt (refl Unit tt) : True
#eval vd .ptrue (.subst (.unit 0) .star (.lam (.lam .ptrue)) .star .star (.eqRefl (.unit 0) .star))
"""
open(sys.argv[1], "w").write("import IO\n" + body + probe)
PY
set +e
timeout 60 "$WIZ_BIN" check "$tmp/probe.wiz"
rc=$?
echo "exit=$rc (124 = timed out, 1 = the interpreter panic)"
exit 0
