#!/usr/bin/env python3
"""Write the seed corpus for the runtime's libFuzzer harnesses.

    scripts/gen-fuzz-seeds.py OUTDIR

The corpus has two parts:

* the existing compiled corpus (`runtime/corpus/*.c`) as raw seed bytes. The
  harness interprets its input as a bytecode, so a source file is a perfectly
  valid starting point: libFuzzer mutates the operation stream from there. The
  programs chosen for each target are the ones that exercise it (`values.c` for
  constructors and finalizers, `text.c` for the data structures, `numbers.c` for
  the words, `threads.c` next to `values.c` for finalizers).
* one short structured seed per operation, so every opcode is in the seed corpus
  even when a corpus program never reaches it.

The seeds are generated, not committed: `scripts/test-fuzz.sh` writes them under
its temporary build directory so a run never changes the worktree.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "runtime" / "corpus"

# target -> (corpus programs, highest opcode read by the harness)
TARGETS = {
    "values": (["values.c"], 19),
    "data": (["text.c", "values.c"], 60),
    "words": (["numbers.c"], 44),
    "finalizers": (["values.c", "threads.c"], 13),
}

# the per-step opcode layout, mirroring the harness loops
def op_seed(target: str, op: int) -> bytes:
    if target == "values":
        # a, op, then enough operands for any branch (tag, n, fields, ...)
        return bytes([0, op]) + bytes([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    if target == "data":
        # group (0..5), a, op (0..9), then operands for any branch
        return bytes([op // 10, 0, op % 10]) + bytes(
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
             0, 0, 0, 0, 0, 0, 0, 0])
    if target == "words":
        # group (0 Nat, 1 word), a, b, op, then operands
        return bytes([op // 22, 0, 0, op % 22]) + bytes(
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    # finalizers: a, op, operands
    return bytes([0, op]) + bytes([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: gen-fuzz-seeds.py OUTDIR", file=sys.stderr)
        return 2
    out = Path(argv[1])
    for target, (programs, last_op) in TARGETS.items():
        d = out / target
        d.mkdir(parents=True, exist_ok=True)
        for name in programs:
            src = CORPUS / name
            if src.is_file():
                (d / f"corpus-{src.stem}.seed").write_bytes(src.read_bytes()[:4096])
        for op in range(last_op):
            (d / f"op-{op:02d}.seed").write_bytes(op_seed(target, op) * 3)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
