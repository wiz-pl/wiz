#!/usr/bin/env python3
"""Generate the case analyses of examples/hdl-uart-temporal.wiz.

The refinement of the iCEstick UART (transmitter, receiver) by its specification is one
lemma per reachable control state and input bit: the circuit's step on the image of the
specification's state is the image of the specification's step. Each case is a kernel
evaluation (`refl`) with the data as variables, plus, where the data path shifts, a
rewrite with a lemma about words. This script writes those cases (and their assembly
into one `Nat.All` table) between the `-- BEGIN GENERATED <name>` / `-- END GENERATED
<name>` markers of the example, in place.

    python3 scripts/gen-uart-temporal.py [examples/hdl-uart-temporal.wiz]

The clocks per bit are fixed at N = 4 (the example's parameterisation); for another N,
change N here and the constants 3 / 1 in Tx.spec / Rx.spec.

Where a case shifts the data path, the proof rewrites inside the *goal* with
`Eq.substProp` rather than building an equation at `TxT`/`RxTO` with `Eq.trans` and
`Eq.congrArg`. A word is a proof-carrying `UIntN`, so the type of an equation between
the nested products carries `transp`/cast spines for the erased range proofs; the table
proofs should not have to match those spines (they depend on how the word lemma's body
normalises). `Eq.substProp`'s motive is a family of propositions, so the rewrite stops at
propositional equality and depends only on the lemma's statement. In the shift cases the
first component (`bit0`) and the register (`shift9`) are rewritten one after the other,
each with the goal as the motive; the base of the second rewrite is the first rewrite's
result, not an equation at the product type.
"""
import re
import sys

N = 4            # clock cycles per bit
HALF = N // 2 - 1  # the receiver's start-bit sample


def b(x):
    return ".true" if x else ".false"


def nat_all(prop, items):
    """`Nat.All prop n` from the proofs of `prop 0`, …, `prop (n-1)`."""
    t = "True.intro"
    for it in items:
        t = f"And.intro ({t}) ({it})"
    return t


def tx_tuple(line, left, cnt, sh):
    """The transmitter's tuple `(line, (left, (cnt, sh)))`."""
    return f"({line}, ({left}, ({cnt}, {sh})))"


def tx_tail(left, cnt, sh):
    return f"({left}, ({cnt}, {sh}))"


# --------------------------------------------------------------------------------
# The transmitter: state (l, c), input start.

def tx_kind(l, c, st):
    """The transmitter's step from control state (l, c) with start bit st: the next
    control state and what happens to the data path."""
    idle = l == 0
    if idle and st:
        return 10, 0, "go"
    if (not idle) and c == N - 1:
        return l - 1, 0, "tick"
    return l, (0 if c == N - 1 else c + 1), "same"


def gen_tx():
    out = []
    for l in range(11):
        for c in range(N):
            for st in (True, False):
                l2, c2, kind = tx_kind(l, c, st)
                nm = f"{l}_{c}_{'t' if st else 'f'}"
                lhs = (f"Tx.G (BitVec.beq (BitVec.ofNat 4 {l}) (BitVec.ofNat 4 0)) (BitVec.beq (BitVec.ofNat 7 {c}) (BitVec.ofNat 7 3)) "
                       f"(Tx.embT (TxS.mk {l} {c} d)) (Bool.toBits {b(st)}) (byte e)")
                if kind == "same":
                    pf = f"refl (Tx.embT (TxS.mk {l2} {c2} d))"
                elif kind == "go":
                    # the frame enters the shift register: no `Eq` at `TxT`
                    m1 = tx_tuple("BitVec.ofNat 1 0", "BitVec.ofNat 4 10", "BitVec.ofNat 7 0",
                                  "@frame9 HwTy.El _ (byte e)")
                    mz = tx_tuple("BitVec.ofNat 1 0", "BitVec.ofNat 4 10", "BitVec.ofNat 7 0", "z")
                    pf = (f"Eq.substProp (fun (z : BitVec 9) => {lhs} = {mz}) "
                          f"(Uart.frame_byte e) (refl {m1})")
                else:
                    r = f"(Tx.reg d {l})"
                    tail9 = tx_tail(f"BitVec.ofNat 4 {l2}", "BitVec.ofNat 7 0",
                                    f"shift9 (reg9 {r})")
                    l1 = tx_tuple(f"Bool.toBits {r}.r0", f"BitVec.ofNat 4 {l2}",
                                  "BitVec.ofNat 7 0", f"shift9 (reg9 {r})")
                    # first `bit0`, then `shift9`; each rewrite is a `Prop`, the second
                    # starts from the first one's result
                    inner = (f"Eq.substProp (fun (z : BitVec 1) => (z, {tail9}) = {l1}) "
                             f"(Eq.symm (Uart.bit0_reg9 {r})) (refl {l1})")
                    pf = (f"Eq.substProp (fun (z : BitVec 9) => {lhs} = "
                          f"({f'Bool.toBits {r}.r0'}, {tx_tail(f'BitVec.ofNat 4 {l2}', 'BitVec.ofNat 7 0', 'z')})) "
                          f"(Uart.shift_reg9 {r})\n    ({inner})")
                out.append(f"def Tx.o_{nm} (d e : Bits8) : Tx.GOK (TxS.mk {l} {c} d) ({b(st)}, e) :=\n  {pf}")
                out.append(f"def Tx.v_{nm} (d e : Bits8) : Tx.inv (Tx.spec (TxS.mk {l} {c} d) ({b(st)}, e)).1 := And.intro rfl rfl")
                out.append(f"def Tx.c_{nm} (d e : Bits8) : Tx.Case (TxS.mk {l} {c} d) ({b(st)}, e) := And.intro (Tx.o_{nm} d e) (Tx.v_{nm} d e)")
        qs = []
        for c in range(N):
            out.append(f"def Tx.q_{l}_{c} : Tx.CaseLC {l} {c} := fun (d e : Bits8) => And.intro (Tx.c_{l}_{c}_t d e) (Tx.c_{l}_{c}_f d e)")
            qs.append(f"Tx.q_{l}_{c}")
        out.append(f"def Tx.cl_{l} : Tx.CaseL {l} := fun (c : Nat) (hc : Nat.lt c {N} = .true) =>\n"
                   f"  Nat.all_spec (Tx.CaseLC {l}) {N} ({nat_all('', qs)}) c hc")
    out.append(f"def Tx.cases : Nat.All Tx.CaseL 11 :=\n  {nat_all('', [f'Tx.cl_{l}' for l in range(11)])}")
    return "\n".join(out)


def gen_txframe():
    lst = [f"fun (x : Bool × Bits8) => rfl" for k in range(10 * N)]
    return f"def Tx.fsteps (d : Bits8) : Nat.All (Tx.FStep d) {10*N} :=\n  {nat_all('', lst)}"


def gen_txbits():
    lst = ["rfl" for m in range(10 * N)]
    return f"def Tx.lineBits (e : Bits8) : Nat.All (Tx.lineBit e) {10*N} :=\n  {nat_all('', lst)}"


def rx_bound(ph):
    return 128 if ph == 0 else (2 if ph == 10 else N)


def rx_kind(ph, c, r):
    """The receiver's step: next (ph, c) and whether the register shifts."""
    if ph == 0:
        return (0, 0 if c == 127 else c + 1, False) if r else (10, 0, False)
    if ph == 10:
        if c == HALF:
            return (0 if r else 9, 0, False)
        return (10, c + 1, False)
    if c == N - 1:
        if ph == 1:
            return (0, 0, False)
        return (ph - 1, 0, True)
    return (ph, c + 1, False)


def gen_rx():
    out = []
    for ph in range(1, 11):
        qs = []
        for c in range(rx_bound(ph)):
            for r in (True, False):
                ph2, c2, shift = rx_kind(ph, c, r)
                nm = f"{ph}_{c}_{'t' if r else 'f'}"
                valid = (ph == 1 and c == N - 1 and r)
                o = f"(Bool.toBits {b(valid)}, byte cs)"
                if not shift:
                    pf = f"refl (Rx.embT (RxS.mk {ph2} {c2} cs), {o})"
                else:
                    lhs = f"Rx.Gd (Rx.embT (RxS.mk {ph} {c} cs)) (Bool.toBits {b(r)})"
                    rxT = f"(BitVec.ofNat 4 {ph2}, (BitVec.ofNat 7 0, shift8 (byte cs) (Bool.toBits {b(r)})))"
                    m1 = f"({rxT}, {o})"
                    mz = f"((BitVec.ofNat 4 {ph2}, (BitVec.ofNat 7 0, z)), {o})"
                    # no `Eq` at `RxTO`: rewrite inside the goal (`Eq.substProp`)
                    pf = (f"Eq.substProp (fun (z : BitVec 8) => {lhs} = {mz}) "
                          f"(Uart.shift8_byte cs {b(r)}) (refl {m1})")
                out.append(f"def Rx.o_{nm} (cs : Bits8) : Rx.GOK (RxS.mk {ph} {c} cs) {b(r)} :=\n  {pf}")
                out.append(f"def Rx.v_{nm} (cs : Bits8) : Rx.inv (Rx.next (RxS.mk {ph} {c} cs) {b(r)}) := And.intro rfl rfl")
                out.append(f"def Rx.c_{nm} (cs : Bits8) : Rx.Case (RxS.mk {ph} {c} cs) {b(r)} := And.intro (Rx.o_{nm} cs) (Rx.v_{nm} cs)")
            out.append(f"def Rx.q_{ph}_{c} : Rx.CaseLC {ph} {c} := fun (cs : Bits8) => And.intro (Rx.c_{ph}_{c}_t cs) (Rx.c_{ph}_{c}_f cs)")
            qs.append(f"Rx.q_{ph}_{c}")
        out.append(f"def Rx.cl_{ph} : Rx.CaseL {ph} := fun (c : Nat) (hc : Nat.lt c {rx_bound(ph)} = .true) =>\n"
                   f"  Nat.all_spec (Rx.CaseLC {ph}) {rx_bound(ph)} ({nat_all('', qs)}) c hc")
    out.append(f"def Rx.cases : Nat.All Rx.CaseL 11 :=\n  {nat_all('', [f'Rx.cl_{p}' for p in range(11)])}")
    return "\n".join(out)


def gen_rxframe():
    st = []
    for k in range(39):
        if k < 38:
            st.append(f"fun (r : Bool) (h : Nat.lt {k} 38 = .true → r = Uart.frameBit e (Nat.div {k} 4)) => "
                      f"Eq.substProp (fun (z : Bool) => Rx.next (Rx.path c0 cs e {k}) z = Rx.path c0 cs e {k + 1}) (Eq.symm (h rfl)) rfl")
        else:
            st.append(f"fun (r : Bool) (h : Nat.lt {k} 38 = .true → r = Uart.frameBit e (Nat.div {k} 4)) => rfl")
    q = ["fun (r : Bool) => rfl" for k in range(38)]
    return (f"def Rx.psteps (c0 : Nat) (cs e : Bits8) : Nat.All (Rx.PStep c0 cs e) 39 :=\n  {nat_all('', st)}\n"
            f"def Rx.pquiet (c0 : Nat) (cs e : Bits8) : Nat.All (Rx.PQuiet c0 cs e) 38 :=\n  {nat_all('', q)}")


def gen_rxgg2():
    import itertools
    out = []
    def name(bits):
        return "Rx.gg_" + "".join("t" if x else "f" for x in bits)
    # leaves: all five Booleans given
    for bits in itertools.product((True, False), repeat=5):
        args = " ".join(b(x) for x in bits)
        out.append(f"def {name(bits)} (q : RxT) (rx : BitVec 1) : Rx.GEq q rx {args} := refl (Rx.G2 {args} q rx)")
    # nodes: split the next Boolean
    for n in range(4, -1, -1):
        for bits in itertools.product((True, False), repeat=n):
            args = " ".join(b(x) for x in bits)
            rest = " ".join(f"x{i}" for i in range(n + 2, 5 + 1))
            # P y := ∀ rest, GEq q rx args y rest
            pi = "".join(f"(x{i} : Bool) → " for i in range(n + 2, 5 + 1))
            P = f"(fun (y : Bool) => {pi}Rx.GEq q rx {args} y {rest})".replace("  ", " ")
            out.append(f"def {name(bits)} (q : RxT) (rx : BitVec 1) : (y : Bool) → {pi}Rx.GEq q rx {args} y {rest} :=".replace("  ", " ")
                       + f"\n  Bool.indP {P} ({name(bits + (True,))} q rx) ({name(bits + (False,))} q rx)")
    out.append("def Rx.GG2 (q : RxT) (rx : BitVec 1) (bi bs bp bh bt : Bool) : Rx.GEq q rx bi bs bp bh bt := Rx.gg_ q rx bi bs bp bh bt")
    return "\n".join(out)


def gen_rxidle():
    lst = ["rfl"] * 128
    return (f"def Rx.incs : Nat.All Rx.Inc 128 :=\n  {nat_all('', lst)}\n"
            f"def Rx.cntLts : Nat.All Rx.CntLt 128 :=\n  {nat_all('', lst)}")


GENS = {"tx": gen_tx, "rxgg2": gen_rxgg2, "rxidle": gen_rxidle, "rx": gen_rx, "rxframe": gen_rxframe, "txframe": gen_txframe, "txbits": gen_txbits}


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "examples/hdl-uart-temporal.wiz"
    src = open(path).read()
    for name, gen in GENS.items():
        pat = re.compile(r"(-- BEGIN GENERATED %s [^\n]*\n).*?(-- END GENERATED %s\n)" % (name, name), re.S)
        if not pat.search(src):
            continue
        body = gen()
        src = pat.sub(lambda m: m.group(1) + body + "\n" + m.group(2), src)
    open(path, "w").write(src)


if __name__ == "__main__":
    main()
