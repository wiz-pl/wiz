#!/bin/sh
# Synthesise and simulate the Rune HDL library (`lib/Hdl/Uart.wiz`, `Spi.wiz`,
# `Ddr.wiz`) and the `examples/rune-*.wiz` designs, beyond the value simulation:
#
#   * emit Verilog from the Hdl emitter (`examples/rune-synth.wiz` through `wiz run`);
#   * compile every module with Icarus Verilog and replay the self-checking bench
#     (`Testbench.verilog`) for the designs that have one;
#   * synthesise the logic with yosys `synth_ice40` (cell/LUT/DFF/CARRY counts). The
#     DDR model's 64K x 128 memory (8 Mbit) is too big to map to iCE40 EBRs or gates, so
#     its initialisation is dropped (it is simulation-only) and it is reported before
#     the memory map: `proc; memory -nomap; opt; stat`, one `$mem_v2` cell.
#
# Usage:
#   nix shell nixpkgs#yosys nixpkgs#iverilog nixpkgs#gcc -c scripts/rune-synth.sh
#   WIZ=.lake/build/bin/wiz RUNE_SYNTH_DIR=/tmp/rune-synth scripts/rune-synth.sh
#
# The wiz binary must exist (`lake build wiz`). Its C toolchain flags are read from the
# uncommitted `grail.local.wiz` (as the test driver does); without it, set WIZ_CFLAGS,
# WIZ_LDFLAGS, WIZ_GC_CFLAGS and WIZ_GC_LDFLAGS. Exits 77 (skipped) when a tool is
# missing. Artifacts and logs are left in RUNE_SYNTH_DIR (a fresh temp directory by
# default).
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

missing=
for t in yosys iverilog vvp python3; do
  command -v "$t" >/dev/null 2>&1 || missing="$missing $t"
done
if [ -n "$missing" ]; then
  echo "rune-synth: missing:$missing" >&2
  echo "  run it as: nix shell nixpkgs#yosys nixpkgs#iverilog nixpkgs#gcc -c scripts/rune-synth.sh" >&2
  exit 77
fi

wiz=${WIZ:-$root/.lake/build/bin/wiz}
if [ ! -x "$wiz" ]; then
  echo "rune-synth: no wiz binary at $wiz (build it with: lake build wiz)" >&2
  exit 1
fi

out=${RUNE_SYNTH_DIR:-$(mktemp -d /tmp/rune-synth.XXXXXX)}
mkdir -p "$out"

# The wiz CLI takes its toolchain flags on the command line (grail.local.wiz is for the
# test driver); translate the machine's settings, or fall back to the environment.
set -- "$wiz"
if [ -f grail.local.wiz ]; then
  tab=$(printf '\t')
  while IFS="$tab" read -r key value; do
    [ -n "$key" ] && set -- "$@" "--$key" "$value"
  done <<EOF
$(python3 - grail.local.wiz <<'PY'
import re, sys
for line in open(sys.argv[1], encoding="utf-8"):
    m = re.search(r'Settings\.set\s+"([^"]+)"\s+"([^"]*)"', line)
    if m:
        print(m.group(1) + "\t" + m.group(2))
PY
)
EOF
else
  [ -n "${WIZ_CFLAGS:-}" ] && set -- "$@" --cflags "$WIZ_CFLAGS"
  [ -n "${WIZ_LDFLAGS:-}" ] && set -- "$@" --ldflags "$WIZ_LDFLAGS"
  [ -n "${WIZ_GC_CFLAGS:-}" ] && set -- "$@" --gc-cflags "$WIZ_GC_CFLAGS"
  [ -n "${WIZ_GC_LDFLAGS:-}" ] && set -- "$@" --gc-ldflags "$WIZ_GC_LDFLAGS"
fi

echo "rune-synth: artifacts in $out"
echo "  $("$wiz" --version 2>/dev/null | head -1)"
echo "  $(yosys -V | head -1)"
echo "  $(iverilog -V 2>&1 | head -1)"

if ! "$@" run examples/rune-synth.wiz >"$out/raw.txt" 2>"$out/wiz.err"; then
  echo "rune-synth: wiz run failed:" >&2
  cat "$out/wiz.err" >&2
  exit 1
fi

python3 - "$out" <<'PY'
import os, re, sys
out = sys.argv[1]
name = None
buf = []
count = 0
for line in open(os.path.join(out, "raw.txt"), encoding="utf-8"):
    stripped = line.rstrip("\n")
    m = re.fullmatch(r"//@@file (\S+)", stripped)
    if m:
        if name is not None:
            raise SystemExit(f"nested //@@file {m.group(1)} in {name}")
        name = m.group(1)
        buf = []
        continue
    m = re.fullmatch(r"//@@end (\S+)", stripped)
    if m:
        if name != m.group(1):
            raise SystemExit(f"//@@end {m.group(1)} does not close {name}")
        with open(os.path.join(out, name), "w", encoding="utf-8") as f:
            f.writelines(buf)
        count += 1
        name = None
        continue
    if name is not None:
        buf.append(line)
if name is not None:
    raise SystemExit(f"artifact {name} is not closed")
print(f"  wrote {count} artifacts")
PY

# The DDR model's memory initialisation is 65,536 lines of `mem[i] = 0`; yosys expands
# it to 8M flip-flops. It is simulation-only (a real controller has the DRAM), so drop
# it before the pre-map report.
python3 - "$out/ddr_model.v" "$out/ddr_model.synth.v" <<'PY'
import sys
src, dst = sys.argv[1], sys.argv[2]
lines = open(src, encoding="utf-8").read().splitlines(keepends=True)
out, i, dropped = [], 0, 0
while i < len(lines):
    if (lines[i].strip() == "initial begin" and i + 1 < len(lines)
            and lines[i + 1].strip().startswith("mem[")):
        i += 1
        while i < len(lines) and lines[i].strip() != "end":
            i += 1
        if i < len(lines):
            i += 1
        dropped += 1
        continue
    out.append(lines[i])
    i += 1
open(dst, "w", encoding="utf-8").writelines(out)
print(f"  ddr_model: dropped {dropped} memory initial block(s) for synthesis")
PY

failures=0
printf '\n%-16s %7s %7s %7s %7s %7s\n' module cells LUT4 DFF CARRY mem
for m in uart_baud uart_tx uart_rx uart_loopback spi_master spi_loop ddr_model; do
  # Icarus Verilog: every module compiles; the benches replay the value simulation.
  if (cd "$out" && iverilog -g2005 -o /dev/null "$m.v" >"$m.iv.log" 2>&1); then :; else
    echo "FAIL iverilog $m (see $out/$m.iv.log)" >&2
    cat "$out/$m.iv.log" >&2
    failures=$((failures + 1))
  fi
  if [ -f "$out/$m.tb.v" ]; then
    if (cd "$out" && iverilog -g2005 -o "$m.vvp" "$m.tb.v" "$m.v" >"$m.iv.log" 2>&1) \
       && (cd "$out" && vvp -n "$m.vvp" >"$m.sim.log" 2>&1) \
       && grep -q "^PASS $m:" "$out/$m.sim.log"; then
      : # the bench passed
    else
      echo "FAIL iverilog bench $m (see $out/$m.iv.log, $out/$m.sim.log)" >&2
      cat "$out/$m.sim.log" >&2 2>/dev/null || true
      failures=$((failures + 1))
    fi
  fi

  # yosys: synth_ice40 for the logic; the DDR model before the memory map.
  if [ "$m" = ddr_model ]; then
    script="read_verilog $m.synth.v; hierarchy -top $m; proc; memory -nomap; opt; tee -o $m.stat stat"
  else
    script="read_verilog $m.v; synth_ice40 -top $m; tee -o $m.stat stat"
  fi
  if (cd "$out" && yosys -q -p "$script" >"$m.yosys.log" 2>&1); then :; else
    echo "FAIL yosys $m (see $out/$m.yosys.log)" >&2
    tail -30 "$out/$m.yosys.log" >&2
    failures=$((failures + 1))
  fi

  set -- $(awk '
    $2 == "cells" && !seen++ { cells = $1 }
    $2 == "SB_LUT4" { lut = $1 }
    $2 ~ /^SB_DFF/ { dff += $1 }
    $2 == "$dff" || $2 == "$dffe" { dff += $1 }
    $2 == "SB_CARRY" { carry = $1 }
    $2 == "$mem_v2" { mem = $1 }
    END { printf "%d %d %d %d %d\n", cells, lut, dff, carry, mem }
  ' "$out/$m.stat" 2>/dev/null || echo "0 0 0 0 0")
  printf '%-16s %7s %7s %7s %7s %7s\n' "$m" "$1" "$2" "$3" "$4" "$5"

  if grep -qiE 'warning|error' "$out/$m.yosys.log"; then
    echo "  yosys warnings/errors:"
    grep -iE 'warning|error' "$out/$m.yosys.log" | sed 's/^/    /' | head -10
  fi
done

if [ "$failures" -ne 0 ]; then
  echo "rune-synth: $failures failure(s); logs in $out" >&2
  exit 1
fi
echo "rune-synth: all modules compile and synthesise; benches pass (logs in $out)"
