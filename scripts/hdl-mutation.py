#!/usr/bin/env python3
"""Mutation test for the HDL Verilog emitter (HW-01).

Each mutant injects one bug into a function of `lib/Hdl/Core.wiz` in a throw-away copy
of the library, then runs the same probe design through the emitter and checks that the
gate that is supposed to catch it does:

  expr   `Verilog.expr`: the `add` operator becomes `-`; the counter's test bench
         (`Testbench.verilog` replayed by Icarus) must print `FAIL counter:`.
  peel   `Net.peelEn`: a register's `en` is dropped; the enabled counter's test bench
         must print `FAIL enabled:`.
  domof  `Net.domOfNode`: a register is always reported in `clk`; the structural
         checker (`Netlist.domainErrors`, which `Circuit.netlist` includes) must report
         a crossing in a `clk2` netlist.

The probe design and the mutation list live here, not in `lib/`, and the library copy
means the worktree is never modified. Run it from a worktree with a built `wiz` binary:

    nix shell nixpkgs#iverilog nixpkgs#gcc -c python3 scripts/hdl-mutation.py
    python3 scripts/hdl-mutation.py --keep          # keep the temp tree
    python3 scripts/hdl-mutation.py --mutant expr   # one mutant

Without `iverilog`/`vvp`/`cc` it exits 77 (skipped), so a test group can map that to a
skip. Exit 1 means a mutant escaped (the gate did not catch it), 2 is a usage error.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "lib" / "Hdl" / "Core.wiz"
WIZ = ROOT / ".lake" / "build" / "bin" / "wiz"

# name -> (old text, new text, what must catch it)
MUTANTS = {
    "expr": (
        '  | .add => Verilog.bin cx "+" n.args',
        '  | .add => Verilog.bin cx "-" n.args',
        "testbench",
    ),
    "peel": (
        "    | .true => (Option.some e, a)",
        "    | .true => (Option.none, a)",
        "testbench",
    ),
    "domof": (
        "  | .reg r, _ => .cons (Net.DomCx.reg cx r).dom List.nil",
        '  | .reg r, _ => .cons "clk" List.nil',
        "checker",
    ),
}

PROBE = r'''import Hdl.Core
import Std
import IO

def Bit : HwTy := HwTy.bits 1
def B8 : HwTy := HwTy.bits 8

def counter : Circuit Bit B8 :=
  Circuit.mk B8 (BitVec.ofNat 8 250) (fun s u => Hw.pair (Hw.add s (Hw.lit 8 1)) s)

def enabled : Circuit (HwTy.prod (HwTy.named "en" HwTy.bit) Bit) B8 :=
  Circuit.withEnable counter

def bit (b : Nat) : HwTy.El Bit := BitVec.ofNat 1 b

def cIns : List (HwTy.El Bit) := Hdl.map (fun (_ : Nat) => bit 0) (Hdl.upto 8 0)

def eIns : List (HwTy.El (HwTy.prod (HwTy.named "en" HwTy.bit) Bit)) :=
  Hdl.map (fun (k : Nat) => (bit (Nat.mod k 2), bit 0)) (Hdl.upto 8 0)

def emit {ω i o : HwTy} (name : String) (c : Circuit i o) (xs : List (HwTy.El i)) : IO Unit := do
  let n := Circuit.netlist name c;
  IO.writeFile (name <+> ".v") (Verilog.emit n);
  IO.writeFile (name <+> ".tb.v") (Testbench.verilog n (name <+> ".vec") (List.length xs));
  IO.writeFile (name <+> ".vec") (Hdl.concat (Circuit.vectors n c xs))

def d2 : ClockDomain := ClockDomain.named "clk2"
def n2 : Netlist := Circuit.netlistIn d2 "twoclock" counter

def main : IO Unit := do
  emit "counter" counter cIns;
  emit "enabled" enabled eIns;
  IO.println ("domain_errors " <+> Hdl.show (List.length n2.errors))
'''


def toolchain_flags():
    """The `--cflags …` arguments from `grail.local.wiz`, as rune-synth.sh reads them."""
    flags = []
    g = ROOT / "grail.local.wiz"
    if g.exists():
        for line in g.read_text(encoding="utf-8").splitlines():
            m = re.search(r'Settings\.set\s+"([^"]+)"\s+"([^"]*)"', line)
            if m:
                flags += ["--" + m.group(1), m.group(2)]
    else:
        for key, flag in (
            ("WIZ_CFLAGS", "--cflags"),
            ("WIZ_LDFLAGS", "--ldflags"),
            ("WIZ_GC_CFLAGS", "--gc-cflags"),
            ("WIZ_GC_LDFLAGS", "--gc-ldflags"),
        ):
            if os.environ.get(key):
                flags += [flag, os.environ[key]]
    return flags


def need(tools):
    missing = [t for t in tools if shutil.which(t) is None]
    if missing:
        print(f"hdl-mutation: skip: missing {' '.join(missing)}", file=sys.stderr)
        sys.exit(77)


def prepare(tmp: Path):
    """A copy of `lib/` plus the built binary where it expects its toolchain library."""
    shutil.copytree(ROOT / "lib", tmp / "lib")
    bindir = tmp / ".lake" / "build" / "bin"
    bindir.mkdir(parents=True)
    try:
        os.link(WIZ, bindir / "wiz")
    except OSError:
        shutil.copy2(WIZ, bindir / "wiz")
    (tmp / "probe.wiz").write_text(PROBE, encoding="utf-8")
    return [str(bindir / "wiz")] + toolchain_flags() + ["run", "probe.wiz"]


def run(cmd, cwd, **kw):
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, **kw)


def replay(tmp: Path, name: str) -> str:
    """Compile and run one bench; return its output."""
    cc = run(["iverilog", "-g2005", "-o", name + ".vvp", name + ".tb.v", name + ".v"], tmp)
    if cc.returncode != 0:
        return "iverilog: " + cc.stdout + cc.stderr
    sim = run(["vvp", "-n", name + ".vvp"], tmp)
    return sim.stdout + sim.stderr


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep", action="store_true", help="keep the temporary tree")
    ap.add_argument("--mutant", action="append", choices=sorted(MUTANTS),
                    help="run only this mutant (repeatable)")
    args = ap.parse_args()

    need(["iverilog", "vvp", "cc"])
    if not WIZ.is_file():
        print(f"hdl-mutation: no wiz binary at {WIZ} (build it with: lake build wiz)", file=sys.stderr)
        return 2
    if not LIB.is_file():
        print(f"hdl-mutation: no emitter at {LIB}", file=sys.stderr)
        return 2
    source = LIB.read_text(encoding="utf-8")
    names = args.mutant or sorted(MUTANTS)
    tmp = Path(tempfile.mkdtemp(prefix="hdl-mutation."))
    try:
        cmd = prepare(tmp)
        base = run(cmd, tmp)
        if base.returncode != 0:
            print("hdl-mutation: the unmutated emitter does not run:\n" + base.stdout + base.stderr,
                  file=sys.stderr)
            return 1
        out = replay(tmp, "counter") + replay(tmp, "enabled")
        if "PASS counter:" not in out or "PASS enabled:" not in out or "domain_errors 0" not in base.stdout:
            print("hdl-mutation: baseline does not pass:\n" + out + base.stdout, file=sys.stderr)
            return 1
        print("baseline: benches PASS, domain_errors 0")

        failures = 0
        for name in names:
            old, new, gate = MUTANTS[name]
            n = source.count(old)
            if n != 1:
                print(f"mutant {name}: expected one occurrence of the mutation site, found {n}",
                      file=sys.stderr)
                return 2
            (tmp / "lib" / "Hdl" / "Core.wiz").write_text(source.replace(old, new, 1), encoding="utf-8")
            probe = run(cmd, tmp)
            if probe.returncode != 0:
                caught = f"elaboration failed (expected {gate}):\n{probe.stdout}{probe.stderr}"
                ok = False
            elif gate == "testbench":
                bench = replay(tmp, "counter" if name == "expr" else "enabled")
                caught = bench
                ok = "FAIL " + ("counter" if name == "expr" else "enabled") + ":" in bench
            else:
                m = re.search(r"domain_errors (\d+)", probe.stdout)
                caught = probe.stdout
                ok = m is not None and int(m.group(1)) > 0
            print(f"mutant {name}: {'caught by ' + gate if ok else 'ESCAPED'}")
            if not ok:
                failures += 1
                print(caught, file=sys.stderr)
            (tmp / "lib" / "Hdl" / "Core.wiz").write_text(source, encoding="utf-8")
        return 1 if failures else 0
    finally:
        if args.keep:
            print(f"kept {tmp}")
        else:
            shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
