#!/usr/bin/env python3
"""The bounded kernel-level corpus for the third checker (tools/third-checker).

The terms below are written in the *self-hosted kernel's* internal term language
(`selfhost/Kernel.wiz`).  `emit()` writes a Wiz program: `selfhost/Kernel.wiz` with its
imports stripped, the serializer, and one `dumpLine` call per declaration.  Running

    wiz check dump.wiz

checks every declaration with the self-hosted kernel and prints one line per declaration:

    OK<TAB>name<TAB>type<TAB>value
    ERR<TAB>name<TAB>type<TAB>value

The same terms are serialized independently by `ser()` (used by the tests to check that
the Wiz serializer and this file agree).  The third checker never imports this module's
term constructors: it parses the text, and re-checks it.
"""

import sys

# --- quantities: 0, 1, w (omega) ---------------------------------------------------
Q0, Q1, QW = "0", "1", "w"


# --- levels ------------------------------------------------------------------------
def N(n):            return ("lnum", n)
def P(s):            return ("lparam", s)
def SUC(l):          return ("lsucc", l)
def MAX(a, b):       return ("lmax", a, b)
def IMAX(a, b):      return ("limax", a, b)
HOLE = ("lhole",)


# --- terms (constructor names and field order as in `selfhost/Kernel.wiz`) ---------
def V(i):            return ("var", i)
def U(n):            return ("univ", n)
PROP = ("prop",)
def SL(l):           return ("sortL", l)
def PI(q, i, j, a, b): return ("pi", q, i, j, a, b)
def LAM(b):          return ("lam", b)
def APP(f, a):       return ("app", f, a)
def LET(ty, v, b):   return ("letE", ty, v, b)
def ANN(t, ty):      return ("ann", t, ty)
def LETQ(q, ty, v, b): return ("letq", q, ty, v, b)
def SIG(q, i, j, a, b): return ("sigma", q, i, j, a, b)
def PAIR(a, b):      return ("pair", a, b)
def FST(p):          return ("fst", p)
def SND(p):          return ("snd", p)
def UNIT(n):         return ("unit", n)
STAR = ("star",)
def EMPTY(n):        return ("empty", n)
PTRUE = ("ptrue",)
PFALSE = ("pfalse",)
def EXFALSO(m, t):   return ("exfalso", m, t)
def ENUM(k):         return ("enum", k)
def TAG(k, i):       return ("tag", k, i)
def ECASE(m, s, bs): return ("ecase", m, s, tuple(bs))
def EQ(A, a, b):     return ("eq", A, a, b)
def EQTY(A, B):      return ("eqTy", A, B)
def REFL(A, a):      return ("eqRefl", A, a)
def REFLTY(A):       return ("tyRefl", A)
def CAST(A, B, e, t): return ("coe", A, B, e, t)
def TRANSP(A, a, Pm, p, b, e): return ("subst", A, a, Pm, p, b, e)
QTY = ("qty",)
def QLIT(q):         return ("qlit", q)
def SIGQ(q, i, j, a, b): return ("sigmaQ", q, i, j, a, b)
def DESCR(l, I):     return ("descr", l, I)
def DRET(i):         return ("dret", i)
def DARG(q, S, D):   return ("darg", q, S, D)
def DREC(q, j, D):   return ("drec", q, j, D)
def DHREC(q, H, j, D): return ("dhrec", q, H, j, D)
def MU(l, I, D, i):  return ("mu", l, I, D, i)
def CON(x):          return ("con", x)
def DELIM(v, P, a, b, c, h, D): return ("delim", v, P, a, b, c, h, D)
def IND(l, I, D, v, P, m, i, x): return ("ind", l, I, D, v, P, m, i, x)
SIZE = ("size",)
SZINF = ("szInf",)
def SZSUC(s):        return ("szSuc", s)
def SIZELT(s):       return ("sizeLt", s)
def ULIFT(k, l, A):  return ("ulift", k, l, A)
def UP(a):           return ("up", a)
def DOWN(t):         return ("down", t)
def PRF(l, t):       return ("prf", l, t)
def LETUNIT(u, b):   return ("letUnit", u, b)
def CONST(n, ps, ls, v, ty): return ("const", n, tuple(ps), tuple(ls), v, ty)


# --- a few reusable (closed) types and descriptions ---------------------------------
# `Nat` as an indexed family whose index is a selector tag: zero = ret, succ = a
# non-recursive head field (Unit) then a recursive field.  The description language has
# no sums, so the tag is an ordinary `arg` field, as the frontend's own encoding does.
NAT_D = DARG(QLIT(QW), ENUM(2),
             LAM(ECASE(DESCR(0, UNIT(0)), V(0),
                       [DRET(STAR), DREC(QLIT(QW), STAR, DRET(STAR))])))
NAT = MU(0, UNIT(0), NAT_D, STAR)
UNIT_DESC = DESCR(0, UNIT(0))


def nat_zero():
    return CON(PAIR(TAG(2, 0), PAIR(REFL(UNIT(0), STAR), STAR)))


def nat_succ(x):
    return CON(PAIR(TAG(2, 1), PAIR(x, PAIR(REFL(UNIT(0), STAR), STAR))))


# a list of `Unit`: nil = ret, cons = a Unit field then a recursive field
LIST_D = DARG(QLIT(QW), ENUM(2),
              LAM(ECASE(DESCR(0, UNIT(0)), V(0),
                        [DRET(STAR),
                         DARG(QLIT(QW), UNIT(0),
                              LAM(DREC(QLIT(QW), STAR, DRET(STAR))))])))
LIST = MU(0, UNIT(0), LIST_D, STAR)


def list_nil():
    return CON(PAIR(TAG(2, 0), PAIR(REFL(UNIT(0), STAR), STAR)))


def list_cons(x, xs):
    return CON(PAIR(TAG(2, 1), PAIR(x, PAIR(xs, PAIR(REFL(UNIT(0), STAR), STAR)))))


# --- the corpus --------------------------------------------------------------------
# (name, type, value, note).  The last five are negatives (an ill-typed proof, a wrong
# level, equality at Prop, and two quantity violations); the rest are positives.  They
# are kernel-level terms, not surface programs: the self-hosted *frontend* only
# elaborates a fragment without Eq/cast/transp/Σ (see README.md, "What is checked").
DECLS = [
    # Π, λ, application, β, let
    # (sorts: `U n` lives in Sort (n+2); a *variable* of type `U n` lives in Sort (n+1))
    ("id",
     PI(Q0, N(2), N(1), U(0), PI(Q1, N(1), N(1), V(0), V(1))),
     LAM(LAM(V(0))),
     "the polymorphic identity; A erased (0), x linear (1)"),
    ("const",
     PI(Q0, N(2), N(1), U(0), PI(QW, N(1), N(1), V(0), PI(QW, N(1), N(1), V(1), V(2)))),
     LAM(LAM(LAM(V(1)))),
     "K: two unrestricted arguments, the second unused"),
    ("K-type",
     PI(Q0, N(2), N(3), U(0), PI(Q0, N(3), N(2), U(1), U(0))),
     LAM(LAM(UNIT(0))),
     "a universe-polymorphic Π with imax(3,2)=3"),
    ("prop-impred",
     PI(Q0, N(2), N(1), U(0), PI(QW, N(1), N(1), PROP, PROP)),
     LAM(LAM(V(0))),
     "the impredicative Prop: (...) -> Prop"),
    ("apply2",
     PI(Q0, N(2), N(1), U(0),
        PI(QW, N(1), N(1), PI(QW, N(1), N(1), V(0), V(1)),
           PI(QW, N(1), N(1), V(1), V(2)))),
     LAM(LAM(LAM(APP(V(1), APP(V(1), V(0)))))),
     "f (f x), with f unrestricted"),
    ("beta",
     PI(Q0, N(2), N(1), U(0), PI(QW, N(1), N(1), V(0), V(1))),
     LAM(LAM(APP(ANN(LAM(V(0)), PI(QW, N(1), N(1), V(1), V(2))), V(0)))),
     "(fun y => y) x, ascribed so the application is inferable"),
    ("let",
     PI(Q0, N(2), N(1), U(0), PI(QW, N(1), N(1), V(0), V(1))),
     LAM(LAM(LET(V(1), V(0), V(0)))),
     "let x := x; x (transparent let)"),

    # Σ
    ("swap",
     PI(Q0, N(2), N(2), U(0),
        PI(Q0, N(2), N(1), U(0),
           PI(QW, N(1), N(1), SIG(QW, N(1), N(1), V(1), V(1)),
              SIG(QW, N(1), N(1), V(1), V(3))))),
     LAM(LAM(LAM(PAIR(SND(V(0)), FST(V(0)))))),
     "swap a pair (both projections use the unrestricted pair)"),
    ("fst",
     PI(Q0, N(2), N(1), U(0),
        PI(QW, N(1), N(1), SIG(QW, N(1), N(1), V(0), V(1)), V(1))),
     LAM(LAM(FST(V(0)))),
     "the first projection of a homogeneous pair"),
    ("pair-eta",
     PI(Q0, N(2), N(1), U(0),
        PI(QW, N(1), N(1), SIG(QW, N(1), N(1), V(0), V(1)),
           SIG(QW, N(1), N(1), V(1), V(2)))),
     LAM(LAM(PAIR(FST(V(0)), SND(V(0))))),
     "(p.1, p.2), with dependent snd substitution"),

    # Unit, Empty, enumerations
    ("trivial",
     PTRUE, STAR,
     "the unit type at Prop, inhabited by tt"),
    ("absurd",
     PI(Q0, N(2), N(1), U(0), PI(Q0, N(1), N(1), EMPTY(0), V(1))),
     LAM(LAM(EXFALSO(V(1), V(0)))),
     "ex falso: Empty_0 eliminates into any type"),
    ("not",
     PI(QW, N(1), N(1), ENUM(2), ENUM(2)),
     LAM(ECASE(ENUM(2), V(0), [TAG(2, 1), TAG(2, 0)])),
     "the two-tag negation by ecase"),
    ("ecase-unit",
     PI(QW, N(1), N(1), ENUM(2), UNIT(0)),
     LAM(ECASE(UNIT(0), V(0), [STAR, STAR])),
     "ecase with a constant motive"),

    # Eq, refl, cast, transp
    ("refl-unit",
     EQ(UNIT(0), STAR, STAR), REFL(UNIT(0), STAR),
     "refl at Unit_0"),
    ("refl-enum",
     EQ(ENUM(2), TAG(2, 0), TAG(2, 0)), REFL(ENUM(2), TAG(2, 0)),
     "refl at a finite type"),
    ("cast-unit",
     UNIT(0), CAST(UNIT(0), UNIT(0), REFLTY(UNIT(0)), STAR),
     "cast along a reflexive type equation at Unit"),
    ("cast-enum",
     ENUM(2), CAST(ENUM(2), ENUM(2), REFLTY(ENUM(2)), TAG(2, 1)),
     "cast at an enumeration is the identity"),
    ("transp-unit",
     PTRUE,
     TRANSP(UNIT(0), STAR, LAM(LAM(PTRUE)),
            STAR, STAR, REFL(UNIT(0), STAR)),
     "transport in the constant Prop-valued family (the J step)"),

    # ULift
    ("ulift-star",
     ULIFT(1, 2, UNIT(0)), UP(STAR),
     "ULift.{1,2} Unit_0, up tt"),
    ("ulift-down",
     UNIT(0), DOWN(ANN(UP(STAR), ULIFT(1, 2, UNIT(0)))),
     "down (up tt) computes to tt"),

    # Descriptions, μ, con
    ("desc-ret",
     DESCR(0, UNIT(0)), DRET(STAR),
     "the description ret () over Unit_0"),
    ("mu-ret",
     U(0), MU(0, UNIT(0), DRET(STAR), STAR),
     "mu of ret (): Sort 1"),
    ("con-ret",
     MU(0, UNIT(0), DRET(STAR), STAR),
     CON(PAIR(REFL(UNIT(0), STAR), STAR)),
     "con at ret: payload (() = (), tt)"),
    ("desc-arg",
     DESCR(0, UNIT(0)), DARG(QLIT(QW), UNIT(0), LAM(DRET(STAR))),
     "a description with a non-recursive field"),
    ("desc-rec",
     DESCR(0, UNIT(0)), DREC(QLIT(QW), STAR, DRET(STAR)),
     "a recursive field description"),
    ("mu-rec",
     U(0), MU(0, UNIT(0), DREC(QLIT(QW), STAR, DRET(STAR)), STAR),
     "mu of a recursive description"),
    ("desc-hrec",
     DESCR(0, UNIT(0)), DHREC(QLIT(QW), UNIT(0), LAM(STAR), DRET(STAR)),
     "an infinitary recursive field description"),

    # levels and impredicative propositions
    ("level-sort",
     SL(N(1)), UNIT(0),
     "Sort 1 contains Unit_0"),
    ("level-imax",
     SL(IMAX(N(0), N(1))), UNIT(0),
     "imax 0 1 normalises to 1"),
    ("pi-prop",
     PI(Q0, N(1), N(0), PROP, PI(QW, N(0), N(0), V(0), V(1))),
     PRF(N(0), LAM(LAM(V(0)))),
     "a Π into Prop, with the proof marker the kernel requires; (P : Prop) -> (w x : P) -> P"),

    # --- more inductive types: Nat and List of Unit ---------------------------------
    ("nat-type",
     U(0), NAT,
     "Nat as μ of a selector description (zero = ret, succ = a Unit field then rec)"),
    ("nat-zero",
     NAT, nat_zero(),
     "the zero constructor (payload: tag, index proof, unit)"),
    ("nat-succ",
     PI(QW, N(1), N(1), NAT, NAT),
     LAM(nat_succ(V(0))),
     "the successor constructor (a recursive field)"),
    ("nat-ind",
     PI(QW, N(1), N(1), NAT, ENUM(2)),
     LAM(IND(0, UNIT(0), NAT_D, 1,
             LAM(LAM(ENUM(2))),
             LAM(LAM(LAM(ECASE(ENUM(2), FST(V(1)),
                                [TAG(2, 0), TAG(2, 1)])))),
             STAR, V(0))),
     "induction on Nat: the motive is constant Enum 2, the method reads the selector"),

    ("list-type",
     U(0), LIST,
     "List Unit as μ of a selector description"),
    ("list-nil",
     LIST, list_nil(),
     "the nil constructor"),
    ("list-cons",
     PI(QW, N(1), N(1), UNIT(0), PI(QW, N(1), N(1), LIST, LIST)),
     LAM(LAM(list_cons(V(1), V(0)))),
     "the cons constructor: a non-recursive field then a recursive field"),

    # --- Desc.elim (`delim`) --------------------------------------------------------
    ("desc-elim",
     PI(QW, N(2), N(1), UNIT_DESC, ENUM(2)),
     LAM(DELIM(1, LAM(ENUM(2)), LAM(TAG(2, 0)),
               LAM(LAM(LAM(LAM(TAG(2, 1))))),
               LAM(LAM(LAM(LAM(TAG(2, 1))))),
               LAM(LAM(LAM(LAM(LAM(TAG(2, 1)))))),
               V(0))),
     "Desc.elim over Desc.0 Unit: ret and the three field constructors"),

    # --- cast and proof irrelevance -------------------------------------------------
    ("cast-prop",
     PTRUE, PRF(N(0), CAST(PTRUE, PTRUE, REFLTY(PTRUE), STAR)),
     "a cast between propositions is a proof: it stays stuck, accepted by irrelevance"),

    # --- level parameters -----------------------------------------------------------
    ("level-param-sort",
     SL(SUC(P("u"))), SL(P("u")),
     "Sort u : Sort (u+1), with a symbolic level parameter"),
    ("level-param-max",
     SL(SUC(MAX(P("u"), N(0)))), SL(P("u")),
     "max u 0 normalises to u"),
    ("level-param-id",
     PI(Q0, SUC(P("u")), P("u"), SL(P("u")),
        PI(Q1, P("u"), P("u"), V(0), V(1))),
     PRF(IMAX(SUC(P("u")), P("u")), LAM(LAM(V(0)))),
     "the polymorphic identity at a symbolic level; imax u u is u"),
    ("level-param-const",
     PI(Q0, N(2), N(1), U(0), PI(Q1, N(1), N(1), V(0), V(1))),
     CONST("poly-id", ("u",), (N(1),), LAM(LAM(V(0))),
           PI(Q0, SUC(P("u")), P("u"), SL(P("u")),
              PI(Q1, P("u"), P("u"), V(0), V(1)))),
     "a constant with a level parameter, instantiated at u := 1"),

    # --- negatives ---------------------------------------------------------------
    ("bad-proof",
     EQ(ENUM(2), TAG(2, 0), TAG(2, 1)), REFL(ENUM(2), TAG(2, 0)),
     "ill-typed proof: refl tag 0 proves tag 0 = tag 0, not tag 0 = tag 1"),
    ("bad-level",
     U(0), U(0),
     "wrong level: Type 0 : Type 0"),
    ("bad-eq-prop",
     EQ(PTRUE, STAR, STAR), REFL(PTRUE, STAR),
     "eq at a proposition (True): isNeverZero 0 is false"),
    ("linear-ok",
     PI(Q1, N(1), N(1), UNIT(0), UNIT(0)),
     LAM(V(0)),
     "positive control: a linear x used exactly once"),
    ("bad-linear-dup",
     PI(Q1, N(1), N(1), UNIT(0),
        PI(QW, N(1), N(1), PI(QW, N(1), N(1), UNIT(0), PI(QW, N(1), N(1), UNIT(0), UNIT(0))),
           UNIT(0))),
     LAM(LAM(APP(APP(V(0), V(1)), V(1)))),
     "quantity violation: a linear x used twice"),
    ("bad-linear-drop",
     PI(Q1, N(1), N(1), UNIT(0), UNIT(0)),
     LAM(STAR),
     "quantity violation: a linear x dropped"),
]


# --- emitting Wiz source -----------------------------------------------------------
def wiz_q(q):
    return {"0": ".qz", "1": ".qo", "w": ".qw"}[q]


def wiz_lvl(l):
    c = l[0]
    if c == "lnum": return f"(.lnum {l[1]})"
    if c == "lparam": return f'(.lparam "{l[1]}")'
    if c == "lsucc": return f"(.lsucc {wiz_lvl(l[1])})"
    if c == "lmax": return f"(.lmax {wiz_lvl(l[1])} {wiz_lvl(l[2])})"
    if c == "limax": return f"(.limax {wiz_lvl(l[1])} {wiz_lvl(l[2])})"
    if c == "lhole": return ".lhole"
    raise ValueError(l)


def wiz_tms(ts):
    out = ".tnil"
    for t in reversed(ts):
        out = f"(.tcons {wiz(t)} {out})"
    return out


def wiz(t):
    c = t[0]
    a = t[1:]
    simple = {"prop": ".prop", "star": ".star", "ptrue": ".ptrue", "pfalse": ".pfalse",
              "qty": ".qty", "size": ".size", "szInf": ".szInf"}
    if c in simple:
        assert not a
        return simple[c]
    if c == "var": return f"(.var {a[0]})"
    if c == "univ": return f"(.univ {a[0]})"
    if c == "sortL": return f"(.sortL {wiz_lvl(a[0])})"
    if c == "pi": return f"(.pi {wiz_q(a[0])} {wiz_lvl(a[1])} {wiz_lvl(a[2])} {wiz(a[3])} {wiz(a[4])})"
    if c == "lam": return f"(.lam {wiz(a[0])})"
    if c == "app": return f"(.app {wiz(a[0])} {wiz(a[1])})"
    if c == "letE": return f"(.letE {wiz(a[0])} {wiz(a[1])} {wiz(a[2])})"
    if c == "ann": return f"(.ann {wiz(a[0])} {wiz(a[1])})"
    if c == "letq": return f"(.letq {wiz_q(a[0])} {wiz(a[1])} {wiz(a[2])} {wiz(a[3])})"
    if c == "sigma": return f"(.sigma {wiz_q(a[0])} {wiz_lvl(a[1])} {wiz_lvl(a[2])} {wiz(a[3])} {wiz(a[4])})"
    if c == "pair": return f"(.pair {wiz(a[0])} {wiz(a[1])})"
    if c == "fst": return f"(.fst {wiz(a[0])})"
    if c == "snd": return f"(.snd {wiz(a[0])})"
    if c == "unit": return f"(.unit {a[0]})"
    if c == "empty": return f"(.empty {a[0]})"
    if c == "exfalso": return f"(.exfalso {wiz(a[0])} {wiz(a[1])})"
    if c == "letUnit": return f"(.letUnit {wiz(a[0])} {wiz(a[1])})"
    if c == "enum": return f"(.enum {a[0]})"
    if c == "tag": return f"(.tag {a[0]} {a[1]})"
    if c == "ecase": return f"(.ecase {wiz(a[0])} {wiz(a[1])} {wiz_tms(a[2])})"
    if c == "eq": return f"(.eq {wiz(a[0])} {wiz(a[1])} {wiz(a[2])})"
    if c == "eqTy": return f"(.eqTy {wiz(a[0])} {wiz(a[1])})"
    if c == "eqRefl": return f"(.eqRefl {wiz(a[0])} {wiz(a[1])})"
    if c == "tyRefl": return f"(.tyRefl {wiz(a[0])})"
    if c == "coe": return f"(.coe {wiz(a[0])} {wiz(a[1])} {wiz(a[2])} {wiz(a[3])})"
    if c == "subst": return f"(.subst {wiz(a[0])} {wiz(a[1])} {wiz(a[2])} {wiz(a[3])} {wiz(a[4])} {wiz(a[5])})"
    if c == "qlit": return f"(.qlit {wiz_q(a[0])})"
    if c == "sigmaQ": return f"(.sigmaQ {wiz(a[0])} {wiz_lvl(a[1])} {wiz_lvl(a[2])} {wiz(a[3])} {wiz(a[4])})"
    if c == "descr": return f"(.descr {a[0]} {wiz(a[1])})"
    if c == "dret": return f"(.dret {wiz(a[0])})"
    if c == "darg": return f"(.darg {wiz(a[0])} {wiz(a[1])} {wiz(a[2])})"
    if c == "drec": return f"(.drec {wiz(a[0])} {wiz(a[1])} {wiz(a[2])})"
    if c == "dhrec": return f"(.dhrec {wiz(a[0])} {wiz(a[1])} {wiz(a[2])} {wiz(a[3])})"
    if c == "delim": return f"(.delim {a[0]} " + " ".join(wiz(x) for x in a[1:]) + ")"
    if c == "mu": return f"(.mu {a[0]} {wiz(a[1])} {wiz(a[2])} {wiz(a[3])})"
    if c == "con": return f"(.con {wiz(a[0])})"
    if c == "ind":
        l, I, D, v, P, m, i, x = a
        return f"(.ind {l} {wiz(I)} {wiz(D)} {v} {wiz(P)} {wiz(m)} {wiz(i)} {wiz(x)})"
    if c == "szSuc": return f"(.szSuc {wiz(a[0])})"
    if c == "sizeLt": return f"(.sizeLt {wiz(a[0])})"
    if c == "mus": return f"(.mus {a[0]} {wiz(a[1])} {wiz(a[2])} {wiz(a[3])} {wiz(a[4])})"
    if c == "nu": return f"(.nu {a[0]} {wiz(a[1])} {wiz(a[2])} {wiz(a[3])} {wiz(a[4])})"
    if c == "out": return f"(.out {wiz(a[0])})"
    if c == "cocon": return f"(.cocon {wiz(a[0])})"
    if c == "ulift": return f"(.ulift {a[0]} {a[1]} {wiz(a[2])})"
    if c == "up": return f"(.up {wiz(a[0])})"
    if c == "down": return f"(.down {wiz(a[0])})"
    if c == "prf": return f"(.prf {wiz_lvl(a[0])} {wiz(a[1])})"
    if c == "const":
        return (f"(.const \"{a[0]}\" {wiz_strs(a[1])} {wiz_lvls(a[2])} "
                f"{wiz(a[3])} {wiz(a[4])})")
    raise ValueError(c)


def wiz_strs(xs):
    out = ".nil"
    for x in reversed(xs):
        out = f'(.cons "{x}" {out})'
    return out


def wiz_lvls(xs):
    out = ".nil"
    for x in reversed(xs):
        out = f"(.cons {wiz_lvl(x)} {out})"
    return out


def emit_each_source(limit=None):
    src = open("selfhost/Kernel.wiz").read()
    body = "\n".join(l for l in src.split("\n") if not l.startswith("import"))
    ser = open("tools/third-checker/serializer.wiz").read()
    decls = DECLS if limit is None else DECLS[:limit]
    evals = "\n".join(
        f'#eval dumpLine "{name}" ({wiz(ty)}) ({wiz(val)})'
        for name, ty, val, _ in decls)
    return "import IO\n" + body + "\n" + ser + "\n" + evals + "\n"


def emit_dump_source():
    src = open("selfhost/Kernel.wiz").read()
    body = "\n".join(l for l in src.split("\n") if not l.startswith("import"))
    ser = open("tools/third-checker/serializer.wiz").read()
    calls = "\n".join(
        f'  IO.println (String.append "#err {name} " (errMsg ({wiz(ty)}) ({wiz(val)})));\n'
        f'  IO.println (dumpLine "{name}" ({wiz(ty)}) ({wiz(val)}));'
        for name, ty, val, _ in DECLS)
    return ("import IO\n" + body + "\n" + ser + "\n" +
            "def errMsg (ty v : Tm) : String := match checkDecl ty (.some v) with\n" +
            "  | .err m => m\n  | .ok _ _ => \"\"\n" +

            "def main : IO Unit := do\n" + calls + "\n  IO.pure ()\n")


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ("--emit", "--emit-each", "--names"):
        print("usage: driver.py --emit|--emit-each [N]|--names", file=sys.stderr)
        return 2
    if sys.argv[1] == "--names":
        for name, _, _, note in DECLS:
            print(f"{name}\t{note}")
        return 0
    if sys.argv[1] == "--emit-each":
        limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
        sys.stdout.write(emit_each_source(limit))
        return 0
    sys.stdout.write(emit_dump_source())
    return 0


if __name__ == "__main__":
    sys.exit(main())


# --- the same serialization, in Python (the tests use it for a round-trip) ---------
def ser_lvl(l):
    c = l[0]
    if c == "lnum": return f"n{l[1]}"
    if c == "lparam": return f"p{l[1]}"
    if c == "lsucc": return f"(s {ser_lvl(l[1])})"
    if c == "lmax": return f"(max {ser_lvl(l[1])} {ser_lvl(l[2])})"
    if c == "limax": return f"(imax {ser_lvl(l[1])} {ser_lvl(l[2])})"
    if c == "lhole": return "hole"
    raise ValueError(l)


def ser(t):
    c = t[0]
    a = t[1:]
    simple = {"prop": "P", "star": "tt", "ptrue": "True", "pfalse": "False",
              "qty": "Qty", "size": "Size", "szInf": "inf"}
    if c in simple:
        return simple[c]
    if c == "var": return f"(v {a[0]})"
    if c == "univ": return f"(U {a[0]})"
    if c == "sortL": return f"(L {ser_lvl(a[0])})"
    if c == "pi": return f"(pi {a[0]} {ser_lvl(a[1])} {ser_lvl(a[2])} {ser(a[3])} {ser(a[4])})"
    if c == "lam": return f"(lam {ser(a[0])})"
    if c == "app": return f"(app {ser(a[0])} {ser(a[1])})"
    if c == "letE": return f"(letE {ser(a[0])} {ser(a[1])} {ser(a[2])})"
    if c == "ann": return f"(ann {ser(a[0])} {ser(a[1])})"
    if c == "letq": return f"(letq {a[0]} {ser(a[1])} {ser(a[2])} {ser(a[3])})"
    if c == "sigma": return f"(sigma {a[0]} {ser_lvl(a[1])} {ser_lvl(a[2])} {ser(a[3])} {ser(a[4])})"
    if c == "pair": return f"(pair {ser(a[0])} {ser(a[1])})"
    if c == "fst": return f"(fst {ser(a[0])})"
    if c == "snd": return f"(snd {ser(a[0])})"
    if c == "unit": return f"(unit {a[0]})"
    if c == "empty": return f"(empty {a[0]})"
    if c == "exfalso": return f"(exfalso {ser(a[0])} {ser(a[1])})"
    if c == "letUnit": return f"(letUnit {ser(a[0])} {ser(a[1])})"
    if c == "enum": return f"(enum {a[0]})"
    if c == "tag": return f"(tag {a[0]} {a[1]})"
    if c == "ecase":
        bs = " ".join(ser(x) for x in a[2])
        return f"(ecase {ser(a[0])} {ser(a[1])} (ts{(' ' + bs) if bs else ''}))"
    if c == "eq": return f"(eq {ser(a[0])} {ser(a[1])} {ser(a[2])})"
    if c == "eqTy": return f"(eqTy {ser(a[0])} {ser(a[1])})"
    if c == "eqRefl": return f"(refl {ser(a[0])} {ser(a[1])})"
    if c == "tyRefl": return f"(reflTy {ser(a[0])})"
    if c == "coe": return f"(cast {ser(a[0])} {ser(a[1])} {ser(a[2])} {ser(a[3])})"
    if c == "subst": return f"(transp {ser(a[0])} {ser(a[1])} {ser(a[2])} {ser(a[3])} {ser(a[4])} {ser(a[5])})"
    if c == "qlit": return f"(qlit {a[0]})"
    if c == "sigmaQ": return f"(sigmaQ {ser(a[0])} {ser_lvl(a[1])} {ser_lvl(a[2])} {ser(a[3])} {ser(a[4])})"
    if c == "descr": return f"(descr {a[0]} {ser(a[1])})"
    if c == "dret": return f"(dret {ser(a[0])})"
    if c == "darg": return f"(darg {ser(a[0])} {ser(a[1])} {ser(a[2])})"
    if c == "drec": return f"(drec {ser(a[0])} {ser(a[1])} {ser(a[2])})"
    if c == "dhrec": return f"(dhrec {ser(a[0])} {ser(a[1])} {ser(a[2])} {ser(a[3])})"
    if c == "delim": return f"(delim {a[0]} " + " ".join(ser(x) for x in a[1:]) + ")"
    if c == "mu": return f"(mu {a[0]} {ser(a[1])} {ser(a[2])} {ser(a[3])})"
    if c == "con": return f"(con {ser(a[0])})"
    if c == "ind":
        l, I, D, v, P, m, i, x = a
        return f"(ind {l} {ser(I)} {ser(D)} {v} {ser(P)} {ser(m)} {ser(i)} {ser(x)})"
    if c == "szSuc": return f"(suc {ser(a[0])})"
    if c == "sizeLt": return f"(lt {ser(a[0])})"
    if c == "mus": return f"(mus {a[0]} {ser(a[1])} {ser(a[2])} {ser(a[3])} {ser(a[4])})"
    if c == "nu": return f"(nu {a[0]} {ser(a[1])} {ser(a[2])} {ser(a[3])} {ser(a[4])})"
    if c == "out": return f"(out {ser(a[0])})"
    if c == "cocon": return f"(cocon {ser(a[0])})"
    if c == "ulift": return f"(ulift {a[0]} {a[1]} {ser(a[2])})"
    if c == "up": return f"(up {ser(a[0])})"
    if c == "down": return f"(down {ser(a[0])})"
    if c == "prf": return f"(prf {ser_lvl(a[0])} {ser(a[1])})"
    if c == "split": return f"(split {a[0]} {ser(a[1])} {ser(a[2])} {ser(a[3])})"
    if c == "const":
        ps = " ".join(a[1])
        ls = " ".join(ser_lvl(l) for l in a[2])
        return f"(const {a[0]} (ps{(' ' + ps) if ps else ''}) (ls{(' ' + ls) if ls else ''}) {ser(a[3])} {ser(a[4])})"
    raise ValueError(c)
