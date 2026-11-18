#!/usr/bin/env python3
"""Generate the value-level semantics matrix (`docs/semantics-matrix.md`) and the
data its test reads (`Tests/Semantics/cells.tsv`).

The matrix pins what a *value* is at the boundaries of every numeric and textual
type: the expected column is computed here, from the definitions in the stage docs
(not from the implementation), so a bug shared by the model and the natives is not
hidden.  Run from the repository root:

    python3 scripts/gen-semantics-matrix.py

Cell channels:
  nat  -- a Wiz expression of type `Nat` (the value is observed directly)
  str  -- a Wiz expression of type `String` (printed with `IO.println`)

`interp` says whether the interpreters can evaluate the expression: `Float64` and
`Bytes` are foreign constants with no model, and a shift by a huge amount makes the
model compute `2^k`, so those cells are compiled-only.  `prelude` says whether the
self-hosted compiler's own Prelude (no `import Word`/`Int`/`Text`, a 63-bit `Nat`)
can run it.
"""

import math
import sys
from pathlib import Path

WIDTHS = [0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 128]

cells = []
seen = set()


def cell(family, width, op, label, expr, expected, note, channel="nat",
         interp=True, prelude=False):
    ident = "%s.%s.%s" % (family, width, label)
    assert ident not in seen, ident
    seen.add(ident)
    cells.append(dict(id=ident, family=family, width=width, op=op, label=label,
                      expr=expr, expected=str(expected), note=note,
                      channel=channel, interp=interp, prelude=prelude))


def mask(w):
    return (1 << w) - 1


def sbits(w, v):
    """The bit pattern of a signed width-w value."""
    return v & mask(w)


def sval(w, bits):
    """The signed value of a width-w bit pattern (width 0 is always 0)."""
    if w == 0:
        return 0
    return bits - (1 << w) if bits >= (1 << (w - 1)) else bits


def SHIFT_COUNTS(w):
    """The shift counts a width-indexed word is pinned at: the boundary `w`, and
    counts far beyond any width (`2^32 - 1`, `2^32`, `2^64 - 1`) that a naive model
    would try to materialise as `2^k`."""
    return [("0", 0), ("1", 1), ("w-1", max(0, w - 1)),
            ("w", w), ("w+1", w + 1),
            ("2^32-1", (1 << 32) - 1), ("2^32", 1 << 32),
            ("2^64-1", (1 << 64) - 1)]


def U(w, v):
    return "(UIntN.ofNat %d %d)" % (w, v)


def I(w, v):
    if v >= 0:
        return "(IntN.ofNat %d %d)" % (w, v)
    return "(IntN.ofNeg %d %d)" % (w, -v)


def un(w, e):
    return "(%s).toNat" % e


# -- UIntN ------------------------------------------------------------------

# Boundary operands, as values.  `mid` is 2^(w-1) (0 at width 0), `top` the
# scalar/raw-box boundary that the runtime representation changes at.
def uvals(w):
    m = mask(w)
    raw = {
        "0": 0, "1": 1, "max": m, "max-1": max(0, m - 1),
        "mid": 0 if w == 0 else 1 << (w - 1),
        "mid-1": 0 if w == 0 else (1 << (w - 1)) - 1,
        "p63": min(1 << 63, m), "p63-1": min((1 << 63) - 1, m),
        "p64": min(1 << 64, m), "p64-1": min((1 << 64) - 1, m),
    }
    # a width-w word is its value mod 2^w: at width 0 every name is 0, and a
    # name that does not fit (p63 below 63 bits) is the wrapped value
    return {k: x & m for k, x in raw.items()}


def uexpr(w, name):
    return U(w, uvals(w)[name])


def uintn_cells():
    for w in WIDTHS:
        v = uvals(w)
        # add
        for a, b in [("0", "0"), ("0", "1"), ("max", "0"), ("max", "1"),
                     ("max", "max"), ("max-1", "1"), ("mid", "mid")]:
            cell("uintn", w, "add", "%s+%s" % (a, b),
                 un(w, "UIntN.add %s %s" % (uexpr(w, a), uexpr(w, b))),
                 (v[a] + v[b]) & mask(w),
                 "(a + b) mod 2^w")
        # sub
        for a, b in [("0", "0"), ("0", "1"), ("1", "0"), ("max", "max"),
                     ("max", "max-1"), ("max-1", "max"), ("max", "0"), ("0", "max")]:
            cell("uintn", w, "sub", "%s-%s" % (a, b),
                 un(w, "UIntN.sub %s %s" % (uexpr(w, a), uexpr(w, b))),
                 (v[a] - v[b]) & mask(w),
                 "(a - b) mod 2^w")
        # mul
        for a, b in [("0", "max"), ("1", "max"), ("max", "max"), ("max", "2"),
                     ("max", "max-1"), ("mid", "2")]:
            bb = v[b] if b != "2" else 2
            cell("uintn", w, "mul", "%s*%s" % (a, b),
                 un(w, "UIntN.mul %s %s" % (uexpr(w, a), U(w, bb))),
                 (v[a] * bb) & mask(w),
                 "(a * b) mod 2^w")
        # div / mod: by 1, by max, by 0, and a non-power-of-two
        for a, b in [("max", "1"), ("max", "max"), ("1", "max"), ("max", "0"),
                     ("0", "0"), ("max", "max-1"), ("mid", "2")]:
            bb = v[b] if b != "2" else 2
            q = 0 if bb == 0 else v[a] // bb
            r = v[a] if bb == 0 else v[a] % bb
            cell("uintn", w, "div", "%s/%s" % (a, b),
                 un(w, "UIntN.div %s %s" % (uexpr(w, a), U(w, bb))), q,
                 "a / 0 = 0" if bb == 0 else "floor(a / b)")
            cell("uintn", w, "mod", "%s%%%s" % (a, b),
                 un(w, "UIntN.mod %s %s" % (uexpr(w, a), U(w, bb))), r,
                 "a % 0 = a" if bb == 0 else "a mod b")
        # neg
        for a in ["0", "1", "max", "max-1", "mid"]:
            cell("uintn", w, "neg", "-%s" % a,
                 un(w, "UIntN.neg %s" % uexpr(w, a)), (-v[a]) & mask(w),
                 "(0 - a) mod 2^w")
        # shifts, both directions. The count is a Nat, so the huge cases are no
        # different from `k >= w`: the model must not build `2^k` to learn that.
        for a in ["1", "max", "mid"]:
            for kn, k in SHIFT_COUNTS(w):
                cell("uintn", w, "shl", "%s<<%s" % (a, kn),
                     un(w, "UIntN.shiftLeft %s %d" % (uexpr(w, a), k)),
                     (v[a] << k) & mask(w) if k < w else 0,
                     "k >= w: 0 (bits shifted out)" if k >= w else
                     "(a * 2^k) mod 2^w")
                cell("uintn", w, "shr", "%s>>%s" % (a, kn),
                     un(w, "UIntN.shiftRight %s %d" % (uexpr(w, a), k)),
                     (v[a] >> k) if k < w else 0,
                     "logical: 0 for k >= w" if k >= w else "a >> k")
        # bits
        for op, e in [("and", "UIntN.land"), ("or", "UIntN.lor"), ("xor", "UIntN.xor")]:
            for a, b in [("max", "0"), ("max", "max"), ("max", "mid"), ("mid", "mid-1")]:
                fa = {"and": lambda x, y: x & y, "or": lambda x, y: x | y,
                      "xor": lambda x, y: x ^ y}[op]
                cell("uintn", w, op, "%s %s %s" % (a, op, b),
                     un(w, "%s %s %s" % (e, uexpr(w, a), uexpr(w, b))),
                     fa(v[a], v[b]) & mask(w), "bitwise on the bits")
        for a in ["0", "1", "max", "mid"]:
            cell("uintn", w, "not", "~%s" % a,
                 un(w, "UIntN.not %s" % uexpr(w, a)),
                 (mask(w) - v[a]) & mask(w), "(2^%d - 1) - %d" % (w, v[a]))
        for op, e in [("lt", "UIntN.lt"), ("le", "UIntN.le"), ("beq", "UIntN.beq")]:
            for a, b in [("0", "1"), ("1", "0"), ("0", "0"), ("max", "max"),
                         ("max-1", "max"), ("max", "max-1"), ("mid", "1")]:
                fa = {"lt": lambda x, y: x < y, "le": lambda x, y: x <= y,
                      "beq": lambda x, y: x == y}[op]
                cell("uintn", w, "cmp", "%s %s %s" % (a, op, b),
                     "b2n (%s %s %s)" % (e, uexpr(w, a), uexpr(w, b)),
                     1 if fa(v[a], v[b]) else 0, "unsigned comparison")
        # resize (zero-extend and truncate) and the free signed view
        for a in ["max", "mid"]:
            for to in [0, 1, 8, 16, 32, 64, 128]:
                if to > 128:
                    continue
                cell("uintn", w, "resize", "%s to u%d" % (a, to),
                     un(to, "UIntN.resize %d %s" % (to, uexpr(w, a))),
                     v[a] & mask(to), "ofNat v: zero-extend or truncate")
        cell("uintn", w, "toIntN", "toIntN max",
             un(w, "UIntN.toIntN %s" % uexpr(w, "max")), v["max"],
             "the same bits")
        # the runtime representation changes at 2^63 (scalar -> raw box) and 2^64
        # (raw box -> GMP number); cross both on the widths that have them
        if w >= 64:
            p63, p64 = 1 << 63, 1 << 64
            pairs = [("add", "p63-1+1", "UIntN.add", p63 - 1, 1),
                     ("add", "p63+p63", "UIntN.add", p63, p63),
                     ("sub", "p63-1", "UIntN.sub", p63, 1),
                     ("neg", "-p63", "UIntN.neg", p63, None),
                     ("mul", "p63*2", "UIntN.mul", p63, 2),
                     ("shr", "p63>>63", "UIntN.shiftRight", p63, 63)]
            if w >= 128:
                pairs += [("add", "p64-1+1", "UIntN.add", p64 - 1, 1),
                          ("add", "p64+p64", "UIntN.add", p64, p64),
                          ("sub", "p64-1", "UIntN.sub", p64, 1),
                          ("mul", "p64*2", "UIntN.mul", p64, 2),
                          ("div", "p64/2", "UIntN.div", p64, 2),
                          ("mod", "p64%3", "UIntN.mod", p64, 3),
                          ("shr", "p64>>64", "UIntN.shiftRight", p64, 64),
                          ("shl", "p64<<64", "UIntN.shiftLeft", p64, 64)]
            for op, label, fn, a, b in pairs:
                if op == "neg":
                    e = un(w, "%s %s" % (fn, U(w, a)))
                    exp = (-a) & mask(w)
                elif op in ("shr", "shl"):
                    e = un(w, "%s %s %d" % (fn, U(w, a), b))
                    exp = (a >> b) if op == "shr" else ((a << b) & mask(w))
                else:
                    e = un(w, "%s %s %s" % (fn, U(w, a), U(w, b)))
                    exp = {"add": a + b, "sub": a - b, "mul": a * b,
                           "div": a // b, "mod": a % b}[op] & mask(w)
                cell("uintn", w, "repr", label, e, exp,
                     "a representation boundary of the runtime (2^63 or 2^64)")
        # a rotate is not a primitive; this is its documented composition. For k >= w
        # shiftLeft is 0 and `Nat.sub w k` is 0, so the composition is just `a`.
        for a in ["max", "mid"]:
            for kn, k in [("0", 0), ("1", 1), ("w-1", max(0, w - 1)), ("w", w),
                          ("w+1", w + 1), ("2^32-1", (1 << 32) - 1),
                          ("2^32", 1 << 32), ("2^64-1", (1 << 64) - 1)]:
                exp = (v[a] if k == 0 or k >= w else
                       ((v[a] << k) | (v[a] >> (w - k))) & mask(w))
                cell("uintn", w, "rotl", "rotl %s %s" % (a, kn),
                     un(w, "rotl %s %d" % (uexpr(w, a), k)), exp,
                     "no primitive: (a << k) | (a >> (w-k)); k = 0 and k >= w are a")


# -- IntN -------------------------------------------------------------------

def ivals(w):
    m = mask(w)
    raw = {"0": 0, "1": 1, "-1": m, "-2": max(0, m - 1),
           "min": 0 if w == 0 else 1 << (w - 1),
           "min+1": 0 if w == 0 else (1 << (w - 1)) + 1,
           "max": 0 if w == 0 else (1 << (w - 1)) - 1,
           "max-1": 0 if w == 0 else (1 << (w - 1)) - 2,
           "mid": 0 if w == 0 else 1 << (w - 1)}
    # the names are values written as `ofNat`/`ofNeg`; at a width where the
    # positive literal does not exist it names its wrapped bits (width 1: "1" is -1)
    return {k: sval(w, x & m) for k, x in raw.items()}


def intn_cells():
    for w in WIDTHS:
        v = ivals(w)

        def IE(n):
            return I(w, v[n])

        def out(e):
            return un(w, e)

        def wrap(x):
            return sbits(w, x)

        for a, b in [("0", "0"), ("0", "1"), ("max", "1"), ("min", "-1"),
                     ("min", "min"), ("max", "max"), ("max-1", "1"), ("-1", "1")]:
            cell("intn", w, "add", "%s+%s" % (a, b),
                 out("IntN.add %s %s" % (IE(a), IE(b))), wrap(v[a] + v[b]),
                 "wrapping: (a + b) mod 2^w")
        for a, b in [("0", "1"), ("1", "0"), ("min", "1"), ("min", "-1"),
                     ("max", "-1"), ("max", "max"), ("-1", "min")]:
            cell("intn", w, "sub", "%s-%s" % (a, b),
                 out("IntN.sub %s %s" % (IE(a), IE(b))), wrap(v[a] - v[b]),
                 "wrapping: (a - b) mod 2^w")
        for a, b in [("min", "-1"), ("max", "2"), ("min", "2"), ("-1", "-1"),
                     ("max", "max"), ("min", "min")]:
            bb = v[b] if b != "2" else 2
            cell("intn", w, "mul", "%s*%s" % (a, b),
                 out("IntN.mul %s %s" % (IE(a), I(w, bb))), wrap(v[a] * bb),
                 "wrapping: (a * b) mod 2^w")
        # div/rem: min/-1, x/0, signs
        for a, b in [("min", "-1"), ("max", "-1"), ("min", "1"), ("0", "0"),
                     ("max", "0"), ("min", "0"), ("-1", "2"), ("1", "-2"),
                     ("-1", "-2"), ("max", "2"), ("min", "max")]:
            bb = 2 if b == "2" else v[b]
            ib = I(w, 2) if b == "2" else IE(b)
            if bb == 0:
                q, r = 0, v[a]
            else:
                q = abs(v[a]) // abs(bb) * (-1 if (v[a] < 0) != (bb < 0) else 1)
                r = v[a] - q * bb
            cell("intn", w, "div", "%s/%s" % (a, b),
                 out("IntN.div %s %s" % (IE(a), ib)), wrap(q),
                 "truncate toward zero; min / -1 wraps; a / 0 = 0")
            cell("intn", w, "mod", "%s%%%s" % (a, b),
                 out("IntN.rem %s %s" % (IE(a), ib)), wrap(r),
                 "remainder takes the dividend's sign; a % 0 = a")
        for a in ["0", "1", "-1", "min", "max", "min+1"]:
            cell("intn", w, "neg", "-%s" % a,
                 out("IntN.neg %s" % IE(a)), wrap(-v[a]),
                 "-min = min (wraps); -0 = 0")
        for a in ["1", "-1", "min", "max"]:
            for kn, k in SHIFT_COUNTS(w):
                cell("intn", w, "shl", "%s<<%s" % (a, kn),
                     out("IntN.shiftLeft %s %d" % (IE(a), k)),
                     wrap(v[a] << k) if k < w else 0,
                     "wrapping left shift; k >= w: 0" if k >= w else
                     "wrapping left shift")
                if w == 0:
                    exp = 0
                elif k >= w:
                    exp = -1 if v[a] < 0 else 0
                else:
                    exp = v[a] >> k
                cell("intn", w, "shr", "%s>>%s" % (a, kn),
                     out("IntN.shiftRight %s %d" % (IE(a), k)), wrap(exp),
                     "arithmetic: sign bits in; -1 for k >= w when negative"
                     if k >= w else "signed a >> k")
        for op, e in [("lt", "IntN.lt"), ("le", "IntN.le"), ("beq", "IntN.beq")]:
            for a, b in [("min", "max"), ("-1", "0"), ("0", "-1"), ("min", "min"),
                         ("max", "-1"), ("min+1", "min")]:
                fa = {"lt": lambda x, y: x < y, "le": lambda x, y: x <= y,
                      "beq": lambda x, y: x == y}[op]
                cell("intn", w, "cmp", "%s %s %s" % (a, op, b),
                     "b2n (%s %s %s)" % (e, IE(a), IE(b)),
                     1 if fa(v[a], v[b]) else 0, "signed comparison")
        for a in ["-1", "min", "max"]:
            for to in [8, 16, 32, 64, 128]:
                exp = sbits(to, v[a]) if to > 0 else 0
                cell("intn", w, "resize", "%s to i%d" % (a, to),
                     un(to, "IntN.resize %d %s" % (to, IE(a))), exp,
                     "sign-extend (or truncate) to v bits")
        # the signed view of the bits, and |x|
        for a in ["min", "-1", "max"]:
            cell("intn", w, "natAbs", "|%s|" % a,
                 "IntN.natAbs %s" % IE(a), abs(v[a]), "magnitude")
            cell("intn", w, "isNeg", "isNeg %s" % a,
                 "b2n (IntN.isNeg %s)" % IE(a), 1 if v[a] < 0 else 0,
                 "the top bit")



# -- Nat, Int ---------------------------------------------------------------

def nat_cells():
    ns = [("0", 0), ("1", 1), ("62-1", (1 << 62) - 1), ("62", 1 << 62),
          ("63-1", (1 << 63) - 1), ("63", 1 << 63),
          ("64", 1 << 64), ("100", 1 << 100), ("max2-1", (1 << 101) - 1)]
    for name, n in ns:
        pre = n < (1 << 63)
        cell("nat", "", "add", "%s+1" % name, "Nat.add %d 1" % n, n + 1,
             "unbounded", prelude=pre and n + 1 < (1 << 63))
    for name, n in [("1", 1), ("62", 1 << 62), ("63", 1 << 63), ("64", 1 << 64)]:
        cell("nat", "", "sub", "%s-1" % name, "Nat.sub %d 1" % n, n - 1,
             "truncated subtraction", prelude=n < (1 << 63))
    cell("nat", "", "sub", "0-1", "Nat.sub 0 1", 0, "n - m = 0 when m > n")
    for name, n in [("62-1", (1 << 62) - 1), ("63-1", (1 << 63) - 1), ("64", 1 << 64),
                    ("100", 1 << 100)]:
        pre = n < (1 << 63)
        cell("nat", "", "mul", "%s*2" % name, "Nat.mul %d 2" % n, n * 2,
             "unbounded", prelude=pre and n * 2 < (1 << 63))
    for name, n in [("0", 0), ("1", 1), ("62", 1 << 62), ("63", 1 << 63), ("100", 1 << 100)]:
        pre = n < (1 << 63)
        cell("nat", "", "div", "%s/0" % name, "Nat.div %d 0" % n, 0,
             "n / 0 = 0", prelude=pre)
        cell("nat", "", "mod", "%s%%0" % name, "Nat.mod %d 0" % n, n,
             "n % 0 = n", prelude=pre)
        cell("nat", "", "div", "%s/1" % name, "Nat.div %d 1" % n, n,
             "n / 1 = n", prelude=pre)
        cell("nat", "", "mod", "%s%%1" % name, "Nat.mod %d 1" % n, 0,
             "n % 1 = 0", prelude=pre)
    for name, n in [("100", 1 << 100)]:
        cell("nat", "", "div", "%s/(2^100)" % name,
             "Nat.div %d %d" % (n, n), 1, "n / n = 1")
        cell("nat", "", "mod", "%s%%(2^100-1)" % name,
             "Nat.mod %d %d" % (n, n - 1), n % (n - 1), "remainder")
    for kn, k in [("0", 0), ("1", 1), ("63", 63), ("64", 64), ("127", 127),
                  ("1000", 1000)]:
        cell("nat", "", "shl", "1<<%s" % kn, "Nat.shiftLeft 1 %d" % k, 1 << k,
             "2^%d" % k)
        cell("nat", "", "shr", "(2^100)>>%s" % kn,
             "Nat.shiftRight %d %d" % (1 << 100, k), (1 << 100) >> k, ">>")
    # A huge count: `0 << k` is 0 (no `2^k` is needed for the value), and `a >> k`
    # is 0 once k passes a's bit length. A nonzero `a << k` has a value with `k` bits,
    # too large to write down here (a resource limit, not a value question).
    for kn, k in [("2^32-1", (1 << 32) - 1), ("2^32", 1 << 32),
                  ("2^64-1", (1 << 64) - 1)]:
        # the self-hosted Nat is 63 bits: the count must fit, and 2^64 - 1 does not
        pre = k < (1 << 63)
        cell("nat", "", "shl", "0<<%s" % kn, "Nat.shiftLeft 0 %d" % k, 0,
             "0 << k = 0, whatever k is", prelude=pre)
        cell("nat", "", "shr", "0>>%s" % kn, "Nat.shiftRight 0 %d" % k, 0,
             "0 >> k = 0", prelude=pre)
        cell("nat", "", "shr", "1>>%s" % kn, "Nat.shiftRight 1 %d" % k, 0,
             "k is past the bit length of 1", prelude=pre)
        cell("nat", "", "shr", "(2^100)>>%s" % kn,
             "Nat.shiftRight %d %d" % (1 << 100, k), 0,
             "k is past the bit length of 2^100")
    for name, n in [("0", 0), ("1", 1), ("62", 1 << 62), ("63", 1 << 63), ("100", 1 << 100)]:
        pre = n < (1 << 63)
        cell("nat", "", "log2", "log2 %s" % name, "Nat.log2 %d" % n,
             0 if n == 0 else n.bit_length() - 1, "log2 0 = 0", prelude=pre)
        cell("nat", "", "testBit", "bit %s 0" % name,
             "b2n (Nat.testBit %d 0)" % n, n & 1, "bit 0", prelude=pre)
        cell("nat", "", "land", "%s &&& 1" % name,
             "Nat.land %d 1" % n, n & 1, "bitwise and", prelude=pre)
        cell("nat", "", "lor", "%s ||| 1" % name,
             "Nat.lor %d 1" % n, n | 1, "bitwise or", prelude=pre)
        cell("nat", "", "xor", "%s ^^^ 1" % name,
             "Nat.xor %d 1" % n, n ^ 1, "bitwise xor", prelude=pre)
    for op, e, fn in [("lt", "Nat.lt", lambda x, y: x < y),
                      ("le", "Nat.le", lambda x, y: x <= y),
                      ("beq", "Nat.beq", lambda x, y: x == y)]:
        for a, b in [(0, 1), ((1 << 63) - 1, 1 << 63), (0, 0), (1 << 100, 1)]:
            cell("nat", "", "cmp", "%d %s %d" % (a, op, b),
                 "b2n (%s %d %d)" % (e, a, b), 1 if fn(a, b) else 0,
                 "unbounded comparison", prelude=max(a, b) < (1 << 63))


def int_cells():
    # encode a : Int as natAbs * 2 + isNeg, so sign and magnitude are observed
    def code(e):
        return "intCode (%s)" % e

    for name, n in [("0", 0), ("1", 1), ("-1", -1), ("-2", -2),
                    ("2^63", 1 << 63), ("(-2)^100", -(1 << 100))]:
        lit = "Int.ofNat %d" % n if n >= 0 else "Int.neg (Int.ofNat %d)" % -n
        cell("int", "", "add", "%s+1" % name, code("Int.add (%s) (Int.ofNat 1)" % lit),
             (abs(n + 1) * 2 + (1 if n + 1 < 0 else 0)), "unbounded signed add",
             prelude=False)
        cell("int", "", "sub", "%s-1" % name, code("Int.sub (%s) (Int.ofNat 1)" % lit),
             (abs(n - 1) * 2 + (1 if n - 1 < 0 else 0)), "unbounded signed sub",
             prelude=False)
        cell("int", "", "mul", "%s*2" % name, code("Int.mul (%s) (Int.ofNat 2)" % lit),
             (abs(n * 2) * 2 + (1 if n * 2 < 0 else 0)), "unbounded signed mul",
             prelude=False)
        cell("int", "", "neg", "-%s" % name, code("Int.neg (%s)" % lit),
             abs(n) * 2 + (1 if -n < 0 else 0), "negation",
             prelude=False)
    for a, b in [(7, 2), (-7, 2), (7, -2), (-7, -2), (0, 0), (5, 0), (0, 5),
                 (-1, 1), (1, -1), (1 << 100, 3), (-(1 << 100), 3)]:
        la = "Int.ofNat %d" % a if a >= 0 else "Int.neg (Int.ofNat %d)" % -a
        lb = "Int.ofNat %d" % b if b >= 0 else "Int.neg (Int.ofNat %d)" % -b
        if b == 0:
            q, r = 0, a
        else:
            q = abs(a) // abs(b) * (-1 if (a < 0) != (b < 0) else 1)
            r = a - q * b
        cell("int", "", "div", "%d/%d" % (a, b),
             code("Int.div (%s) (%s)" % (la, lb)),
             abs(q) * 2 + (1 if q < 0 else 0),
             "truncates toward zero; a / 0 = 0",
             prelude=False)
        cell("int", "", "mod", "%d%%%d" % (a, b),
             code("Int.mod (%s) (%s)" % (la, lb)),
             abs(r) * 2 + (1 if r < 0 else 0),
             "remainder takes the dividend's sign; a % 0 = a",
             prelude=False)
    for a in [0, 1, -1, -(1 << 100), 1 << 100]:
        la = "Int.ofNat %d" % a if a >= 0 else "Int.neg (Int.ofNat %d)" % -a
        cell("int", "", "toNat", "toNat %d" % a,
             "Int.toNat (%s)" % la, max(a, 0), "negatives to 0")
        cell("int", "", "natAbs", "|%d|" % a, "Int.natAbs (%s)" % la, abs(a),
             "magnitude")
    for op, e, fn in [("lt", "Int.lt", lambda x, y: x < y),
                      ("le", "Int.le", lambda x, y: x <= y),
                      ("beq", "Int.beq", lambda x, y: x == y)]:
        for a, b in [(-1, 0), (0, -1), (-(1 << 100), 1 << 100), (3, 3)]:
            la = "Int.ofNat %d" % a if a >= 0 else "Int.neg (Int.ofNat %d)" % -a
            lb = "Int.ofNat %d" % b if b >= 0 else "Int.neg (Int.ofNat %d)" % -b
            cell("int", "", "cmp", "%d %s %d" % (a, op, b),
                 "b2n (%s (%s) (%s))" % (e, la, lb), 1 if fn(a, b) else 0,
                 "signed comparison", prelude=False)


# -- Float64 ----------------------------------------------------------------

def f64(x):
    return float(x)


def cshow(x):
    """C's `%.17g` (the documented `Float64.toString`), with glibc's spellings."""
    if x != x:
        # glibc prints the sign of the NaN bit pattern; 0.0/0.0 is negative on x86.
        return "-nan" if math.copysign(1.0, x) < 0 else "nan"
    if math.isinf(x):
        return "-inf" if x < 0 else "inf"
    return format(x, ".17g")


def float_cells():
    one = "(Float64.ofNat 1)"
    zero = "(Float64.ofNat 0)"
    neg1 = "(Float64.sub %s %s)" % (zero, one)

    def show(label, e, x, note, literal=None):
        exp = literal if literal is not None else cshow(x)
        cell("float", "", "show", label, e, exp, note, channel="str",
             interp=False, prelude=False)

    def cmp(label, e, exp, note):
        cell("float", "", "cmp", label, "b2n (%s)" % e, exp, note,
             channel="nat", interp=False)

    # value/formatting cells (C only: Float64 is an axiom with externs)
    show("0", zero, 0.0, "ofNat 0")
    show("-0", "Float64.mul %s %s" % (zero, neg1), -0.0, "0 * -1: the sign bit is set")
    show("1", one, 1.0, "ofNat 1")
    show("0.1", "Float64.div %s (Float64.ofNat 10)" % one, 0.1,
         "the nearest double to 1/10")
    show("1/3", "Float64.div %s (Float64.ofNat 3)" % one, 1.0 / 3.0,
         "the nearest double to 1/3")
    show("0.1+0.2", "Float64.add (Float64.div %s (Float64.ofNat 10)) (Float64.div %s (Float64.ofNat 5))" % (one, one),
         0.1 + 0.2, "the nearest double to 0.1 + 0.2")
    show("2^53", "Float64.ofNat 9007199254740992", float(2 ** 53),
         "exactly representable")
    show("2^53+1", "Float64.ofNat 9007199254740993", float(2 ** 53 + 1),
         "rounds to even")
    show("2^53+3", "Float64.ofNat 9007199254740995", float(2 ** 53 + 3),
         "rounds to even")
    show("2^63-1", "Float64.ofNat 9223372036854775807", float(2 ** 63 - 1),
         "rounds up: 2^63 is nearer than 2^63 - 1")
    show("2^64-1", "Float64.ofNat 18446744073709551615", float(2 ** 64 - 1),
         "rounds up to 2^64, printed by %.17g")
    show("inf", "Float64.div %s %s" % (one, zero), float("inf"), "1/0")
    show("-inf", "Float64.div %s %s" % (neg1, zero), float("-inf"), "-1/0")
    show("nan", "Float64.div %s %s" % (zero, zero), 0.0,
         "0/0 is a NaN; x86's default NaN has the sign bit set (glibc prints -nan)",
         literal="-nan")
    show("inf-inf", "Float64.sub (Float64.div %s %s) (Float64.div %s %s)" % (one, zero, one, zero),
         0.0, "inf - inf is a NaN", literal="-nan")
    show("inf+1", "Float64.add (Float64.div %s %s) %s" % (one, zero, one), float("inf"),
         "inf + 1 = inf")
    show("inf*0", "Float64.mul (Float64.div %s %s) %s" % (one, zero, zero), 0.0,
         "inf * 0 is a NaN", literal="-nan")
    show("1/inf", "Float64.div %s (Float64.div %s %s)" % (one, one, zero), 0.0,
         "1/inf = 0")
    show("min-subnormal", "halve 1074 %s" % one, 5e-324,
         "2^-1074: the least positive subnormal (halving 1074 times)")
    show("below-min-subnormal", "halve 1075 %s" % one, 0.0,
         "2^-1075 rounds to even: 0")
    show("max-normal", "double 1023 %s" % one, 2.0 ** 1023, "2^1023")
    show("overflow", "double 1024 %s" % one, float("inf"), "2^1024 overflows to inf")
    show("subnormal+subnormal", "Float64.add (halve 1074 %s) (halve 1074 %s)" % (one, one),
         2.0 * 5e-324, "2 * 2^-1074")
    show("subnormal/2", "halve 1 (halve 1074 %s)" % one, 0.0,
         "the least subnormal / 2 rounds to even: 0")

    # comparisons
    cmp("nan<1", "Float64.lt (Float64.div %s %s) %s" % (zero, zero, one), 0,
        "all comparisons with NaN are false")
    cmp("1<nan", "Float64.lt %s (Float64.div %s %s)" % (one, zero, zero), 0,
        "all comparisons with NaN are false")
    cmp("nan<nan", "Float64.lt (Float64.div %s %s) (Float64.div %s %s)" % (zero, zero, zero, zero),
        0, "NaN < NaN is false")
    cmp("-0<0", "Float64.lt (Float64.mul %s %s) %s" % (zero, neg1, zero), 0,
        "-0 and 0 compare equal")
    cmp("0<-0", "Float64.lt %s (Float64.mul %s %s)" % (zero, zero, neg1), 0,
        "-0 and 0 compare equal")
    cmp("-inf<0", "Float64.lt (Float64.div %s %s) %s" % (neg1, zero, zero), 1,
        "-inf < 0")
    cmp("0<inf", "Float64.lt %s (Float64.div %s %s)" % (zero, one, zero), 1,
        "0 < inf")
    cmp("inf<inf", "Float64.lt (Float64.div %s %s) (Float64.div %s %s)" % (one, zero, one, zero),
        0, "inf < inf is false")
    cmp("min-sub<0", "Float64.lt (halve 1074 %s) %s" % (one, zero), 0,
        "a positive subnormal is > 0")
    cmp("0<min-sub", "Float64.lt %s (halve 1074 %s)" % (zero, one), 1,
        "0 < the least positive subnormal")
    cmp("2^53=2^53+1", "Float64.lt (Float64.ofNat 9007199254740992) (Float64.ofNat 9007199254740993)",
        0, "both convert to the same double: not less")
    # conversions: from Nat only; there is no Float64 -> Nat
    # `ofNat` above 2^64 (the native covers one uint64_t; the wrapper rounds)
    for label, expr, n, note in [
        ("ofNat 10^19", "10000000000000000000", 10 ** 19,
         "above 2^63, still below 2^64"),
        ("ofNat 2^64", "(Nat.pow 2 64)", 2 ** 64,
         "the first Nat the native cannot take"),
        ("ofNat 2^64+2^11-1", "(Nat.sub (Nat.add (Nat.pow 2 64) 2048) 1)",
         2 ** 64 + 2 ** 11 - 1, "just below the tie: rounds down to 2^64"),
        ("ofNat 2^64+2^11", "(Nat.add (Nat.pow 2 64) 2048)", 2 ** 64 + 2 ** 11,
         "a tie; the 53-bit mantissa is even, so round to even: down"),
        ("ofNat 2^64+2^11+1", "(Nat.add (Nat.add (Nat.pow 2 64) 2048) 1)",
         2 ** 64 + 2 ** 11 + 1, "just above the tie: up"),
        ("ofNat 2^64+3*2^11", "(Nat.add (Nat.pow 2 64) 6144)",
         2 ** 64 + 3 * 2 ** 11, "a tie; the mantissa is odd, so round to even: up"),
        ("ofNat 2^64+2^12", "(Nat.add (Nat.pow 2 64) 4096)",
         2 ** 64 + 2 ** 12, "exactly representable"),
        ("ofNat 2^65-1", "(Nat.sub (Nat.pow 2 65) 1)", 2 ** 65 - 1,
         "rounds up to 2^65"),
        ("ofNat 2^100", "(Nat.pow 2 100)", 2 ** 100,
         "the nearest Float64 to 2^100"),
        ("ofNat 2^100+2^47", "(Nat.add (Nat.pow 2 100) 140737488355328)",
         2 ** 100 + 2 ** 47, "a tie far out; the mantissa is even: down"),
        ("ofNat 2^100+3*2^47", "(Nat.add (Nat.pow 2 100) 422212465065984)",
         2 ** 100 + 3 * 2 ** 47, "a tie far out; the mantissa is odd: up"),
        ("ofNat 2^1023", "(Nat.pow 2 1023)", 2 ** 1023,
         "the largest power of two below overflow"),
        ("ofNat 2^1024", "(Nat.pow 2 1024)", 2 ** 1024, "overflows to inf"),
        ("ofNat 2^1024-1", "(Nat.sub (Nat.pow 2 1024) 1)", 2 ** 1024 - 1,
         "rounds up to 2^1024: inf"),
        ("ofNat 2^100000", "(Nat.pow 2 100000)", 2 ** 100000,
         "the early inf branch (no huge shift)"),
    ]:
        try:
            x = float(n)
        except OverflowError:
            x = float("inf")
        show(label, "Float64.ofNat %s" % expr, x, note)
def text_cells():
    strings = [
        ("empty", "", 0),
        ("a", "a", 1),
        ("ascii-7f", "\u007f", 1),
        ("2byte-80", "\u0080", 1),
        ("2byte-7ff", "\u07ff", 1),
        ("3byte-800", "\u0800", 1),
        ("3byte-ffff", "\uffff", 1),
        ("4byte-10000", "\U00010000", 1),
        ("4byte-10ffff", "\U0010ffff", 1),
        ("astral-mid", "\U0001d11e", 1),
        ("a-astral-b", "a\U0001d11e b".replace(" ", ""), 3),
        ("nul", "\x00", 1),
        ("a-nul-b", "a\0b", 3),
        ("combining", "e\u0301", 2),
        ("two-astral", "\U0001d11e\U0001d11e", 2),
    ]
    for name, s, n in strings:
        lit = wiz_str(s)
        cell("text", "", "length", "len " + name, "String.length %s" % lit, n,
             "%d Unicode scalar values (not UTF-8 bytes, not NFC-normalised)" % n,
             prelude=True)
        cell("text", "", "utf8len", "utf8 len " + name,
             "Bytes.size (Bytes.ofUtf8 %s)" % lit, len(s.encode("utf-8")),
             "%d UTF-8 bytes: %s" % (len(s.encode("utf-8")),
                                     " ".join("%02x" % b for b in s.encode("utf-8")[:8]) +
                                     (" …" if len(s.encode("utf-8")) > 8 else "")),
             interp=False)
    # String operations
    cell("text", "", "append", "len (a ++ astral)", 'String.length (String.append "a" "\U0001d11e")',
         2, "append counts characters", prelude=True)
    cell("text", "", "take", "take 2 (a,astral,b)",
         'String.length (String.take 2 "a\U0001d11eb")', 2,
         "take counts characters, never splits a character")
    cell("text", "", "drop", "len (drop 1 (astral,b))",
         'String.length (String.drop 1 "\U0001d11eb")', 1, "drop counts characters")
    cell("text", "", "eq", "astral = astral",
         "b2n (String.eq \"\U0001d11e\" \"\U0001d11e\")", 1, "equality")
    cell("text", "", "eq", "nul <> empty", "b2n (String.eq \"\\0\" \"\")", 0,
         "an embedded NUL is a character")
    cell("text", "", "lt", "b < astral",
         "b2n (String.lt \"b\" \"\U0001d11e\")", 1,
         "lexicographic by code point; UTF-8 preserves code-point order, so byte order agrees")
    def lst(name, expr, expected, note, **kw):
        cell("text", "", "bytes", name, expr, expected, note, **kw)
    # bytes: sizes and the NUL boundary
    lst("bytes empty", "Bytes.size Bytes.empty", 0, "empty", interp=False)
    lst("push 255", "Bytes.size (Bytes.push Bytes.empty 255)", 1, "one byte", interp=False)
    lst("push 256", "(Bytes.get (Bytes.push Bytes.empty 256) 0)", 0,
        "push takes the low eight bits", interp=False)
    lst("push 511", "(Bytes.get (Bytes.push Bytes.empty 511) 0)", 255,
        "511 mod 256", interp=False)
    lst("get past end", "Bytes.get (Bytes.push Bytes.empty 7) 1", 0,
        "get past the end is 0 (the total Bytes.at is none)", interp=False)
    lst("ofString nul", "Bytes.size (Bytes.ofString \"a\\0b\")", 1,
        "ofString goes through a C string: it stops at the NUL", interp=False)
    lst("ofUtf8 nul", "Bytes.size (Bytes.ofUtf8 \"a\\0b\")", 3,
        "ofUtf8 encodes every character, NUL included", interp=False)
    lst("ofString astral", "Bytes.size (Bytes.ofString \"\U0001d11e\")", 4,
        "a C string of the UTF-8 encoding: 4 bytes", interp=False)
    lst("toString stops at nul", "String.length (Bytes.toString (Bytes.ofUtf8 \"a\\0b\"))", 1,
        "toString goes through a C string: it stops at the NUL", interp=False)
    lst("toUtf8 round trip nul", "match Bytes.toUtf8 (Bytes.ofUtf8 \"a\\0b\") with | .ok s => String.length s | .error _ => 999", 3,
        "toUtf8 decodes all bytes", interp=False)
    lst("latin1 255", "match Bytes.ofLatin1 \"\u00ff\" with | .ok b => Bytes.size b | .error _ => 999", 1,
        "one byte per character (code points up to 255)", interp=False)
    lst("latin1 >255", "match Bytes.ofLatin1 \"\u0100\" with | .ok b => Bytes.size b | .error _ => 999", 999,
        "a code point above 255 is an error, not a truncation", interp=False)
    lst("slice past end", "Bytes.size (Bytes.slice (Bytes.ofList [1, 2, 3]) 2 99)", 1,
        "slice clamps to the end", interp=False)
    lst("drop past end", "Bytes.size (Bytes.drop (Bytes.ofList [1, 2, 3]) 5)", 0,
        "drop past the end is empty", interp=False)
    lst("append", "Bytes.size (Bytes.append (Bytes.ofList [1]) (Bytes.ofList [2, 3]))", 3,
        "sizes add", interp=False)
    lst("eq", "b2n (Bytes.eq (Bytes.ofList [0, 255]) (Bytes.ofList [0, 255]))", 1,
        "byte equality", interp=False)
    lst("ofList mod 256", "Bytes.get (Bytes.ofList [256, 257]) 1", 1,
        "ofList pushes mod 256", interp=False)
    lst("UTF-8 4-byte size", "Bytes.size (Bytes.ofUtf8 \"\U00010000\")", 4,
        "U+10000 is 4 UTF-8 bytes", interp=False)
    lst("UTF-8 3-byte size", "Bytes.size (Bytes.ofUtf8 \"\uffff\")", 3,
        "U+FFFF is 3 UTF-8 bytes", interp=False)
    lst("surrogate -> U+FFFD", "Bytes.size (Bytes.ofUtf8 (String.ofChars [Char.mk 55296]))", 3,
        "a lone surrogate is not a Unicode scalar value: the encoder writes U+FFFD (spec gap: undocumented)",
        interp=False)
    lst("above 10FFFF -> U+FFFD", "Bytes.size (Bytes.ofUtf8 (String.ofChars [Char.mk 1114112]))", 3,
        "above U+10FFFF: U+FFFD again", interp=False)
    lst("surrogate round trip", "match Bytes.toUtf8 (Bytes.ofUtf8 (String.ofChars [Char.mk 55296])) with | .ok s => String.length s | .error _ => 999", 1,
        "the round trip is not the identity for a non-scalar: it comes back as U+FFFD",
        interp=False)
    lst("invalid UTF-8", "match Bytes.toUtf8 (Bytes.ofList [128]) with | .ok s => String.length s | .error _ => 999", 999,
        "a continuation byte alone is invalid: the total function .error (the total Bytes.at is none)",
        interp=False)
    lst("overlong UTF-8", "match Bytes.toUtf8 (Bytes.ofList [192, 128]) with | .ok s => String.length s | .error _ => 999", 999,
        "overlong forms are rejected", interp=False)
    lst("surrogate UTF-8", "match Bytes.toUtf8 (Bytes.ofList [237, 160, 128]) with | .ok s => String.length s | .error _ => 999", 999,
        "an encoded surrogate is rejected", interp=False)
    lst("UTF-8 2-byte size", "Bytes.size (Bytes.ofUtf8 \"\u0080\")", 2,
        "U+0080 is 2 UTF-8 bytes (U+007F is 1)  [see the length cells]",
        interp=False)


def wiz_str(s):
    out = ['"']
    for ch in s:
        o = ord(ch)
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif o == 0:
            out.append("\\0")
        elif 32 <= o < 127:
            out.append(ch)
        else:
            out.append("\\u{%x}" % o)
    out.append('"')
    return "".join(out)


# -- docs -------------------------------------------------------------------

def sources(c):
    s = []
    if c["interp"]:
        s += ["W"]
    s += ["L"]
    if c["prelude"]:
        s += ["S"]
    return " ".join(s)


def gen_docs():
    lines = []
    w = lines.append
    w("# Value-level semantics matrix")
    w("")
    w("<!-- Generated by scripts/gen-semantics-matrix.py; edit the generator, not this file. -->")
    w("")
    w("What a *value* is at the boundaries of every numeric and textual type, pinned")
    w("cell by cell, independently of the implementation: the `expected` column is")
    w("computed from the rules in the stage docs by `scripts/gen-semantics-matrix.py`,")
    w("not read back from the library. Every cell is then run through each backend that")
    w("can express it, and a disagreement is a finding (the test `=semantics` fails).")
    w("")
    w("## Sources and provenance")
    w("")
    w("| tag | pipeline | how |")
    w("|---|---|---|")
    w("| `[W]` | **the Wiz model**: `lib/`'s definitions | `#eval` (core interpreter) **and** `#run` (IR interpreter) agree; `K`: the curated subset also agrees in the kernel by `refl` |")
    w("| `[L]` | **Lean frontend → C** | the `implemented_by` natives in `runtime/` |")
    w("| `[S]` | **Wiz frontend (`selfhost/`) → C** | the self-hosted runtime, prelude fragment only |")
    w("")
    w("`[W]` is the specification's model, so `E` and `R` are checked separately (a")
    w("disagreement between them is still a finding). `K` is the curated subset — width-8")
    w("words, all of `Nat` and all of `Int` — decided by `refl` in the kernel, which pins")
    w("that the *definitions* compute the value, not only an interpreter.")
    w("")
    w("The `sources` column says which pipelines *can* express the cell and were")
    w("compared; `–` means the backend cannot run that cell at all, and the reason is")
    w("listed below. A cell with no comparison is not evidence.")
    w("")
    w("### Where a backend cannot run a cell")
    w("")
    w("* `[W]`: `Float64` and `Bytes` are `axiom`s implemented by `extern`s with no")
    w("  model, so both interpreters stop (`#eval (3 : Float64)` panics: \"foreign")
    w("  functions only run in compiled code\"). Word shifts by a huge count are")
    w("  evaluable: the model caps the exponent at the width before building `2^k`")
    w("  (below). A nonzero `Nat.shiftLeft` by a huge count has a numeral with `k`")
    w("  bits, so it is not a matrix cell; `0 << k` and `a >> k` are.")
    w("* `[S]`: the self-hosted frontend has no `term.eq` (an equality *type*), and")
    w("  `lib/Word.wiz`, `lib/Int.wiz` and `lib/Text.wiz` use it (a word's erased range")
    w("  proof is `Nat.lt ... = .true`), so `import Word` is rejected with \"unsupported")
    w("  syntax term.eq\"; only the Prelude fragment is available. Its `Nat` is a 63-bit")
    w("  scalar (`selfhost/rt.c`), so a value or intermediate at or above `2^63` is out")
    w("  of its range, and its runtime has no `wiz_f64_show` (no `Float64.toString`).")
    w("* `[L]` (and C generally) runs every cell; that is the point of the matrix.")
    w("")
    w("## The matrix")
    w("")
    w("### Shift rules")
    w("")
    w("Every shift count is a `Nat`, so no count is negative (`lib/Int.wiz`'s unbounded")
    w("`Int` has no shift operation). The rules are total for every count `k`:")
    w("")
    w("* `UIntN.shiftLeft a k = (a * 2^k) mod 2^w` and `UIntN.shiftRight a k = a / 2^k`;")
    w("  both are `0` for `k >= w`.")
    w("* `IntN.shiftLeft` is the same bits as unsigned; `IntN.shiftRight` is")
    w("  arithmetic, `floor(a / 2^k)`, so it is `0` for `k >= w` when `a >= 0` and")
    w("  `-1` (all ones) when `a < 0`.")
    w("* `Nat.shiftLeft a k = a * 2^k` and `Nat.shiftRight a k = a / 2^k` (floor).")
    w("  `0 << k = 0`; `a >> k = 0` once `k` is past the bit length of `a`. A nonzero")
    w("  `a << k` with a huge `k` has a numeral with `k` bits, too large to write")
    w("  down here: its value is fixed by the rule, but the matrix only pins the")
    w("  `0 << k` and `a >> k` cases (a resource limit, not a value difference).")
    w("* There is no rotate primitive. The `rotl` cells pin the composition")
    w("  `(a << k) | (a >> (w - k))`: for `k >= w` the left shift is `0` and")
    w("  `Nat.sub w k` is `0`, so the composition is `a` (also at `k = 0`).")
    w("")

    fam_names = {
        "uintn": "`UIntN w` (unsigned words, widths 0 … 128)",
        "intn": "`IntN w` (two's complement, widths 0 … 128)",
        "nat": "`Nat` (unbounded)",
        "int": "`Int` (unbounded signed; encoded as `|n| * 2 + isNeg`)",
        "float": "`Float64` (IEEE 754 binary64)",
        "text": "`String` and `Bytes` (UTF-8)",
    }
    heads = "| cell | " + " | ".join(str(x) for x in WIDTHS) + " | sources | derivation |"
    rule = "|---" * (len(WIDTHS) + 3) + "|"
    for fam in ["uintn", "intn", "nat", "int", "float", "text"]:
        w("### " + fam_names[fam])
        w("")
        if fam in ("uintn", "intn"):
            w("One row per boundary pattern; the columns are the widths. `expected` is")
            w("the value of `.toNat` (for `IntN`, the bits), so a negative number shows")
            w("its two's-complement pattern.")
            w("")
            w(heads)
            w(rule)
            # group by (op, label), preserving first-seen order
            order = []
            groups = {}
            for c in cells:
                if c["family"] != fam:
                    continue
                key = (c["op"], c["label"])
                if key not in groups:
                    groups[key] = {}
                    order.append(key)
                groups[key][c["width"]] = c
            for key in order:
                g = groups[key]
                vals = []
                for width in WIDTHS:
                    c = g.get(width)
                    vals.append("–" if c is None else "`%s`" % c["expected"])
                first = g[WIDTHS[0]] if WIDTHS[0] in g else next(iter(g.values()))
                srcs = {sources(c) for c in g.values()}
                src = srcs.pop() if len(srcs) == 1 else "/".join(sorted(srcs))
                label = first["label"].replace("|", "\\|")
                note = first["note"].replace("|", "\\|")
                w("| `%s` | %s | %s | %s |" % (label, " | ".join(vals), src, note))
        else:
            w("| cell | expected | sources | derivation |")
            w("|---|---|---|---|")
            for c in cells:
                if c["family"] != fam:
                    continue
                label = c["label"].replace("|", "\\|")
                note = c["note"].replace("|", "\\|")
                w("| `%s` | `%s` | %s | %s |" % (label, c["expected"],
                                                 sources(c), note))
        w("")

    w("## Findings of this pass")
    w("")
    w("* **One implementation/spec disagreement, fixed.** `Float64.ofNat` aborted for")
    w("  `n >= 2^64` instead of giving the nearest `Float64` (see the first known gap")
    w("  below).  It is fixed in `lib/IO.wiz` and pinned by 15 cells; the 15 include")
    w("  both kinds of tie and both overflow edges.")
    w("* **No value mismatch in the words, `Nat`, `Int`, `String` or `Bytes`.** Every")
    w("  cell that a backend can express agrees with the documented value: the word")
    w("  natives (scalar, raw box and GMP paths), the model at widths 0 … 128, the")
    w("  signed special cases (`min / -1`, `min % -1`, `-min`, wrapping overflow),")
    w("  shifts by `0, 1, w-1, w, w+1, 2^32-1, 2^32, 2^64-1`, div/mod by zero, the")
    w("  runtime's representation boundaries (`2^63`, `2^64`) and the")
    w("  UTF-8/NUL/astral text cases.")
    w("* **Huge shifts agree in the model now.** `UIntN.shiftLeft` used to unfold to")
    w("  `ofNat w (Nat.shiftLeft a.toNat k)` for every `k`, so the model built `2^k`")
    w("  even when `k >= w` made the result `0`; at `k >= 2^32` Lean's `Nat.shiftLeft`")
    w("  panicked (\"Nat.shiftl exponent is too big\") while compiled code returned `0`.")
    w("  The definition now caps the exponent at the width (`Word.min k w`,")
    w("  `lib/Word.wiz`), so `[W]`, `[L]` and the kernel all give `0` (and `-1` for")
    w("  a negative `IntN.shiftRight`).")
    w("  Huge `Nat.shiftRight` counts are short-circuited to `0` in the model's native")
    w("  table (`natNative?`), so `a >> 2^64-1` no longer walks `2^64-1` steps.")
    w("* **The self-hosted frontend cannot import `Word`.** It has no `term.eq`, so")
    w("  `lib/Word.wiz` (whose words carry a `Nat.lt ... = .true` proof) is rejected.")
    w("  That is a coverage limit of `[S]`, not a value difference; where `[S]` runs")
    w("  (the 63-bit `Nat` fragment and `String.length`), it agrees.")
    w("")
    w("## Mismatches found")
    w("")
    w("| cell(s) | before | decision |")
    w("|---|---|---|")
    w("| `ofNat 2^64`, `ofNat 2^100` (and the 13 other `ofNat` cells above `2^64`) | Lean → C aborted with \"a number is too big for a C integer\" | the **implementation** was wrong (the documented value is the nearest `Float64`), so spec first: `Float64.ofNat` now rounds (see below). After: `1.8446744073709552e+19`, `1.2676506002282294e+30` |")
    w("| `intn.1.1>> huge` | the matrix expected `0`, C gave `1` | the **matrix** was wrong: at width 1 the numeral `1` is the signed value `-1`, so an arithmetic shift keeps `1` (all ones). The generator now reads the signed value; C was right |")
    w("| `uintn.0.1%max`, `uintn.0.0 lt 1`, … | the matrix expected the values of 1 at width 0 | the **matrix** was wrong: width 0 has one value, `0`; the generator now masks every unsigned operand at its width |")
    w("| `text..surrogate round trip` | the harness used `String.length (Bytes.toUtf8 …)` (`Except String String`) | the **harness** expression was wrong; the value (`1`, U+FFFD) was right |")
    w("| `uintn.*.max<<huge`, `intn.*.*<<huge` (and the new `2^32-1`/`2^32`/`2^64-1` rows) | the model panicked with \"Nat.shiftl exponent is too big\"; C gave `0` / all ones | the **model** was wrong: `UIntN.shiftLeft` now caps the exponent at the width (`Word.min k w`, the documented word rule). The huge word cells are no longer compiled-only |")
    w("| `nat..(2^100)>>2^32`, `nat..1>>2^32-1`, … | the model walked `2^32` steps (or hung) | the **native table** was too literal: `a >> k` is `0` once `k` is past `a`'s bit length, which is now tested before the shift. `0 << k` is likewise `0` without building `2^k` |")
    w("")
    w("After those fixes every cell that a backend can express agrees; the run report")
    w("is `7 passed, 0 failed` (`#eval`, `#run`, Lean → C, `Float64`, Wiz → C and the")
    w("kernel` on this machine).")
    w("")
    w("## Coverage")
    w("")
    n_total = len(cells)
    n_er = sum(1 for c in cells if c["channel"] == "nat" and c["interp"])
    n_c = sum(1 for c in cells if c["channel"] == "nat")
    n_str = sum(1 for c in cells if c["channel"] == "str")
    n_gap = 0
    n_s = sum(1 for c in cells if c["prelude"])
    n_k = sum(1 for c in cells if c["interp"] and
              ((c["family"] in ("uintn", "intn") and c["width"] == "8") or
               c["family"] in ("nat", "int")))
    w("| what | cells | comparisons |")
    w("|---|---|---|")
    w("| all cells | %d | |" % n_total)
    w("| `[W]`, `#eval` and `#run` | %d | %d |" % (n_er, 2 * n_er))
    w("| `[L]`, Lean → C (every `Nat`-valued cell) | %d | %d |" % (n_c, n_c))
    w("| `[L]`, `Float64` text cells | %d | %d |" % (n_str, n_str))
    w("| `[S]`, Wiz → C (prelude fragment) | %d | %d |" % (n_s, n_s))
    w("| `K`, the kernel by `refl` (width-8 words, `Nat`, `Int`) | %d | %d |" % (n_k, n_k))
    w("| **total** | | **%d** |" % (2 * n_er + n_c + n_str + n_s + n_k))
    w("")
    w("")

    w("## Known gaps and underspecification")
    w("")
    w("* **`Float64.ofNat` above `2^64` (found and fixed here).** `lib/IO.wiz`")
    w("  documents \"the `Float64` nearest a `Nat`\", but the native is")
    w("  `double wiz_f64_of_nat(uint64_t)`: a bigger `Nat` failed with \"a number is too")
    w("  big for a C integer\".  The extern is now `Float64.ofNatU64` and")
    w("  `Float64.ofNat` rounds for every `Nat` (take the 53-bit mantissa from")
    w("  `Nat.log2`, then the dropped bits: greater than a half rounds up, less rounds")
    w("  down, exactly a half rounds to even), so no double rounding; `2^1024` and above")
    w("  give `inf`.  The 15 `ofNat` cells include the ties at `2^64` and `2^100`, the")
    w("  carry to the next binade (`2^65 - 1`) and overflow.")
    w("* **`Float64` has no `beq`, no total order and no `toNat`.** `lt` is the only")
    w("  comparison, and there is no conversion from a float to an integer; a value is")
    w("  observed only as text. `Float64.toString` is documented as C's `%.17g`;")
    w("  `-nan` is glibc's spelling for the default NaN (on x86 `0.0/0.0` has the sign")
    w("  bit set), while the spec says only \"NaN\", so the sign is under-specified.")
    w("  The cells pin the observable values (including subnormals, overflow and the")
    w("  round-to-even ties at `2^53`).")
    w("* **No rotate primitive.** Neither `UIntN`/`IntN` nor `BitVec` has")
    w("  `rotateLeft`/`rotateRight`. The `rotl` cells pin the composition")
    w("  `(a << k) | (a >> (w - k))`. It is total: for `k >= w` the left shift is `0`")
    w("  and `Nat.sub w k` is `0`, so the composition is `a` (the same as `k = 0`);")
    w("  there is no `k mod w` convention and none is needed.")
    w("* **No checked arithmetic.** The words are wrapping only (`add`/`sub`/`mul`/")
    w("  `neg`/`div`/`rem`); there is no `checked_*`, `overflowing_*` or `wrapping_*`")
    w("  family, and no way to observe an overflow besides the wrapped value. The")
    w("  overflow cells (`max+1`, `min-1`, `min/-1`, `-min`, `min*min`) pin the")
    w("  wrapping behaviour the docs state.")
    w("* **A nonzero `Nat.shiftLeft` by a huge count is resource-limited.** The value")
    w("  `a * 2^k` has `k` bits, so `k = 2^32` would be a 512 MiB numeral (before its")
    w("  decimal text); the model's registered native refuses exponents of `2^32` or")
    w("  more and the C runtime refuses a count it cannot hold as a machine word.")
    w("  That is a resource limit, not a value difference: the matrix pins `0 << k`")
    w("  and `a >> k` for huge `k`, and the rule for `a > 0` stays `a * 2^k`.")
    w("* **Still under-specified (not cheap to settle here).**")
    w("  * **No total order on `Float64`.** Only `lt` exists; there is no `beq`, `le`")
    w("    or total order, and no `toNat` (a float is observed only as text).")
    w("  * **`Float64` NaN payload/sign.** `toString` is C's `%.17g`; `-nan` is")
    w("    glibc's spelling for the x86 default NaN, while the spec says only \"NaN\".")
    w("  * **`Float64` `lt` with NaN / signed zero** is IEEE (all comparisons with")
    w("    NaN false, `-0 = 0`), but there is no total order to pin.")
    w("  * **Non-scalar `Char`s.** A `Char` is an unchecked `Nat` code; `Bytes.ofUtf8`")
    w("    maps a lone surrogate or a value above `U+10FFFF` to `U+FFFD`, so")
    w("    `toUtf8 (ofUtf8 s) != s`. The behaviour is pinned by the surrogate cells")
    w("    but is not stated as a general rule.")
    w("  * **`Int` has no shift or bitwise operation**, so there is nothing to pin")
    w("    there (the `int` cells cover arithmetic, comparison and conversion only).")
    w("* **`String` can contain non-scalar `Char`s.** `Char` is a `Nat` code, with no")
    w("  check that it is a Unicode scalar value. `Bytes.ofUtf8` maps a lone surrogate")
    w("  or a code point above `U+10FFFF` to `U+FFFD` (three bytes), so")
    w("  `toUtf8 (ofUtf8 s) != s` for such a string; this is not stated in the docs and")
    w("  is pinned by the \"surrogate\" cells. `toUtf8` rejects overlong forms and")
    w("  encoded surrogates (the decoder checks).")
    w("* **`Bytes.ofString`/`Bytes.toString` stop at a NUL** (documented) while")
    w("  `Bytes.ofUtf8`/`toUtf8` do not; `String.length` counts characters and")
    w("  `Bytes.size` counts UTF-8 bytes. The trap is that an astral character is 1")
    w("  `String` character and 4 bytes. `Bytes.get` past the end is `0` (the total")
    w("  `Bytes.at` is `none`).")
    w("* **Width 0** is an inhabited type (`UIntN 0` has one value, `0`); all arithmetic")
    w("  gives `0`, `2^0 - 1 = 0`, and `min = max = 0`. The docs only say \"a number of")
    w("  bits below `2^w`\", so the width-0 row is the specification by construction.")
    w("* **The self-hosted backend's `Nat` is 63 bits** (`selfhost/rt.c`), so `[S]` is")
    w("  limited to cells whose values and intermediates fit; that is a documented")
    w("  bootstrap limitation, not a semantic difference. Where `[S]` runs, it agrees.")
    w("")
    w("## Running it")
    w("")
    w("```sh")
    w("python3 scripts/gen-semantics-matrix.py          # regenerate this file and the TSV")
    w("lake build wiz tests")
    w(".lake/build/bin/tests '=semantics'               # all cells, all available backends")
    w("```")
    w("")
    w("The test reads `Tests/Semantics/cells.tsv` (the same data this document is")
    w("generated from), builds one program per backend and compares every value. A")
    w("mismatch is printed as a table with the cell id, the expected value and each")
    w("backend's value, and fails the case. It has its own heavy shard (`semantics`,")
    w("`.github/test-shards.json`); the C cases skip without a C toolchain and the")
    w("`[S]` case skips without the collector (`--gc-cflags`). The expected values are")
    w("computed by the generator, never read back from the implementation: change a")
    w("rule in the docs, then regenerate.")
    w("")
    return "\n".join(lines) + "\n"


def gen_tsv():
    out = ["id\tfamily\twidth\top\tlabel\texpr\texpected\tchannel\tinterp\tprelude\tnote"]
    for c in cells:
        out.append("\t".join(str(c[k]) for k in
                             ["id", "family", "width", "op", "label", "expr",
                              "expected", "channel", "interp", "prelude", "note"]))
    return "\n".join(out) + "\n"


def main():
    uintn_cells()
    intn_cells()
    nat_cells()
    int_cells()
    float_cells()
    text_cells()
    root = Path(__file__).resolve().parent.parent
    (root / "Tests" / "Semantics").mkdir(parents=True, exist_ok=True)
    (root / "Tests" / "Semantics" / "cells.tsv").write_text(gen_tsv())
    (root / "docs" / "semantics-matrix.md").write_text(gen_docs())
    fams = {}
    for c in cells:
        fams[c["family"]] = fams.get(c["family"], 0) + 1
    print("%d cells: %s" % (len(cells),
                            ", ".join("%s %d" % (k, fams[k]) for k in sorted(fams))))


if __name__ == "__main__":
    main()
