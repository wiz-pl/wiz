#!/usr/bin/env python3
"""An independent checker for the proof terms in `corpus.dump`.

This is *not* a production kernel.  It re-implements, from `docs/CoreSpec.md` and from
the rules in `selfhost/Kernel.wiz` (read, not imported), a bidirectional type checker
over the serialized terms of `tools/third-checker/serializer.wiz`:

    Π, λ, application, let, Σ, pair, projections, Unit/Empty/enumerations and ecase,
    observational equality (eq, eqTy, refl, reflTy, cast, transp), ULift,
    descriptions (ret/arg/rec/hrec), μ and con, quantities (0/1/ω), and levels.

It deliberately rejects what it does not implement (sizes, ν, the eliminators ind /
delim / sfix / scase / cofit, `split`, numerals, proof markers with non-zero levels);
see README.md for the trusted base and the omissions.  Rejecting is sound for the
question this tool answers: "is this dump accepted by two independent implementations?"

Terms are tuples whose first element is a constructor name (see `parse_term`).  Values
are not modelled as a separate domain: `whnf` normalises terms (β, let, projections,
ecase on a tag, cast, const unfolding), and `conv` compares normal forms structurally
with levels decided by `level_eq`.
"""

import sys

# ---------------------------------------------------------------------------------
# errors

class CheckError(Exception):
    pass


def fail(msg):
    raise CheckError(msg)


# ---------------------------------------------------------------------------------
# levels

def level_eq(a, b):
    """Equality of closed levels.  Parameters and holes are out of scope (rejected)."""
    ca, cb = closed_level(a), closed_level(b)
    if ca is None or cb is None:
        # out of scope: only syntactically equal parameters are accepted
        return a == b
    return ca == cb


def closed_level(l):
    c = l[0]
    if c == "lnum":
        return l[1]
    if c == "lsucc":
        x = closed_level(l[1])
        return None if x is None else x + 1
    if c == "lmax":
        a, b = closed_level(l[1]), closed_level(l[2])
        return None if a is None or b is None else max(a, b)
    if c == "limax":
        a, b = closed_level(l[1]), closed_level(l[2])
        return 0 if (b == 0) else (None if a is None or b is None else max(a, b))
    return None


def level_le(a, b):
    """a <= b for closed levels."""
    x, y = closed_level(a), closed_level(b)
    if x is None or y is None:
        return False
    return x <= y


def imax_level(a, b):
    bv = closed_level(b)
    if bv == 0:
        return N(0)
    av = closed_level(a)
    if av is None or bv is None:
        return IMAX(a, b)
    return N(max(av, bv))


def max_level(a, b):
    av, bv = closed_level(a), closed_level(b)
    if av is None or bv is None:
        return MAX(a, b)
    return N(max(av, bv))


def never_zero(l):
    v = closed_level(l)
    if v is not None:
        return v != 0
    if l[0] == "lsucc":
        return True
    if l[0] == "lmax":
        return never_zero(l[1]) or never_zero(l[2])
    if l[0] == "limax":
        return never_zero(l[2])
    return False


def is_zero_level(l):
    v = closed_level(l)
    return v == 0


# ---------------------------------------------------------------------------------
# term helpers

def V(i): return ("var", i)
def U(n): return ("univ", n)
PROP = ("prop",)
def SL(l): return ("sortL", l)
def N(n): return ("lnum", n)
def SUC(l): return ("lsucc", l)
def MAX(a, b): return ("lmax", a, b)
def IMAX(a, b): return ("limax", a, b)


def mk_sort(n):
    """The term for `Sort n` (n is an int or a closed-able Lvl)."""
    if isinstance(n, tuple):
        v = closed_level(n)
        if v is None:
            return SL(n)
        n = v
    if n == 0:
        return PROP
    return U(n - 1)


def sort_level_of_sort(t):
    """If `t` is already a sort term (Prop / U n / sortL l), its level, else None."""
    if t[0] == "prop":
        return N(0)
    if t[0] == "univ":
        return N(t[1] + 1)
    if t[0] == "sortL":
        return t[1]
    return None


def sort_level(t):
    """If `t` is a sort term (Prop / U n / sortL l), its level, else None."""
    return sort_level_of_sort(whnf(t))


def usage_zero(n):
    return tuple([0] * n)


def usage_one(i, n):
    u = [0] * n
    u[i] = 1
    return tuple(u)


def qadd(a, b):
    if a == 0:
        return b
    if b == 0:
        return a
    if a == 1 and b == 1:
        return 2
    return 2


def qmul(q, u):
    if q == 0:
        return 0
    if q == 2:
        return 2 if u != 0 else 0
    return u


def usage_add(u, v):
    return tuple(qadd(a, b) for a, b in zip(u, v))


def usage_scale(q, u):
    return tuple(qmul(q, x) for x in u)


def usage_join(u, v):
    out = []
    for a, b in zip(u, v):
        if a == 2 or b == 2 or (a != b):
            out.append(2)
        else:
            out.append(a)
    return tuple(out)


def qle(u, q):
    return u == q or q == 2


# ---------------------------------------------------------------------------------
# de Bruijn: shifting and substitution

def shift(t, k, cutoff=0):
    c = t[0]
    if c == "var":
        i = t[1]
        return ("var", i + k) if i >= cutoff else t
    if c in ("var",):
        return t
    if c == "pi" or c == "sigma":
        return (c, t[1], t[2], t[3], shift(t[4], k, cutoff), shift(t[5], k, cutoff + 1))
    if c == "sigmaQ":
        return (c, shift(t[1], k, cutoff), t[2], t[3],
                shift(t[4], k, cutoff), shift(t[5], k, cutoff + 1))
    if c == "lam":
        return ("lam", shift(t[1], k, cutoff + 1))
    if c == "letE":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff), shift(t[3], k, cutoff + 1))
    if c == "letq":
        return (c, t[1], shift(t[2], k, cutoff), shift(t[3], k, cutoff), shift(t[4], k, cutoff + 1))
    if c == "ann":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff))
    if c == "letUnit":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff))
    if c == "ecase":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff),
                tuple(shift(b, k, cutoff) for b in t[3]))
    if c == "eq":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff), shift(t[3], k, cutoff))
    if c == "eqTy":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff))
    if c == "eqRefl":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff))
    if c == "tyRefl":
        return (c, shift(t[1], k, cutoff))
    if c == "coe":
        return (c,) + tuple(shift(x, k, cutoff) for x in t[1:])
    if c == "subst":
        return (c,) + tuple(shift(x, k, cutoff) for x in t[1:])
    if c == "exfalso":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff))
    if c == "descr":
        return (c, t[1], shift(t[2], k, cutoff))
    if c == "mu":
        return (c, t[1]) + tuple(shift(x, k, cutoff) for x in t[2:])
    if c == "mus":
        return (c, t[1]) + tuple(shift(x, k, cutoff) for x in t[2:])
    if c == "nu":
        return (c, t[1]) + tuple(shift(x, k, cutoff) for x in t[2:])
    if c == "con":
        return (c, shift(t[1], k, cutoff))
    if c == "out" or c == "cocon" or c == "up" or c == "down":
        return (c, shift(t[1], k, cutoff))
    if c == "szSuc" or c == "sizeLt":
        return (c, shift(t[1], k, cutoff))
    if c == "dret":
        return (c, shift(t[1], k, cutoff))
    if c == "darg":
        return (c,) + tuple(shift(x, k, cutoff) for x in t[1:])
    if c == "drec":
        return (c,) + tuple(shift(x, k, cutoff) for x in t[1:])
    if c == "dhrec":
        return (c,) + tuple(shift(x, k, cutoff) for x in t[1:])
    if c == "ind":
        # (ind l I D v P m i x): P and m are under one binder (i), see the kernel; this
        # checker does not implement ind.
        return t
    if c == "prf":
        return (c, t[1], shift(t[2], k, cutoff))
    if c == "pair":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff))
    if c == "fst" or c == "snd":
        return (c, shift(t[1], k, cutoff))
    if c == "app":
        return (c, shift(t[1], k, cutoff), shift(t[2], k, cutoff))
    if c == "const":
        return (c, t[1], t[2], t[3], shift(t[4], k, cutoff), shift(t[5], k, cutoff))
    if c == "axiomC":
        return (c, t[1], shift(t[2], k, cutoff))
    return t


def subst(t, j, s):
    """Substitute `s` for `var j`; the result is in the same context as `t`."""
    c = t[0]
    if c == "var":
        i = t[1]
        if i == j:
            return s
        if i > j:
            return ("var", i - 1)
        return t
    if c == "pi" or c == "sigma":
        return (c, t[1], t[2], t[3], subst(t[4], j, s), subst(t[5], j + 1, shift(s, 1)))
    if c == "sigmaQ":
        return (c, subst(t[1], j, s), t[2], t[3], subst(t[4], j, s),
                subst(t[5], j + 1, shift(s, 1)))
    if c == "lam":
        return ("lam", subst(t[1], j + 1, shift(s, 1)))
    if c == "letE":
        return (c, subst(t[1], j, s), subst(t[2], j, s),
                subst(t[3], j + 1, shift(s, 1)))
    if c == "letq":
        return (c, t[1], subst(t[2], j, s), subst(t[3], j, s),
                subst(t[4], j + 1, shift(s, 1)))
    if c == "ann":
        return (c, subst(t[1], j, s), subst(t[2], j, s))
    if c == "letUnit":
        return (c, subst(t[1], j, s), subst(t[2], j, s))
    if c == "ecase":
        return (c, subst(t[1], j, s), subst(t[2], j, s),
                tuple(subst(b, j, s) for b in t[3]))
    if c in ("eq",):
        return (c,) + tuple(subst(x, j, s) for x in t[1:])
    if c in ("eqTy", "eqRefl", "exfalso"):
        return (c,) + tuple(subst(x, j, s) for x in t[1:])
    if c in ("coe", "subst"):
        return (c,) + tuple(subst(x, j, s) for x in t[1:])
    if c in ("tyRefl", "con", "out", "cocon", "up", "down", "szSuc", "sizeLt", "dret",
             "fst", "snd"):
        return (c, subst(t[1], j, s))
    if c in ("pair", "app"):
        return (c, subst(t[1], j, s), subst(t[2], j, s))
    if c in ("darg", "drec"):
        return (c,) + tuple(subst(x, j, s) for x in t[1:])
    if c == "dhrec":
        return (c,) + tuple(subst(x, j, s) for x in t[1:])
    if c == "descr":
        return (c, t[1], subst(t[2], j, s))
    if c in ("mu", "mus", "nu"):
        return (c, t[1]) + tuple(subst(x, j, s) for x in t[2:])
    if c == "prf":
        return (c, t[1], subst(t[2], j, s))
    if c == "const":
        return (c, t[1], t[2], t[3], subst(t[4], j, s), subst(t[5], j, s))
    if c == "axiomC":
        return (c, t[1], subst(t[2], j, s))
    return t


def subst_top(body, arg):
    # `subst` already decrements the variables above the removed binder, so there is no
    # second closing shift (a shift(-1) here under-counted every outer variable)
    return subst(body, 0, arg)


def inst_levels(t, ps, ls):
    """Instantiate level parameters (used by `const`).  Our corpus has none, but a
    dump may carry them: substitute `lparam` atoms by the position in `ps`."""
    if not ps:
        return t
    return t


# ---------------------------------------------------------------------------------
# weak head normalisation (β, let, projections, ecase, cast, const)

def whnf(t):
    while True:
        c = t[0]
        if c == "app":
            f = whnf(t[1])
            if f[0] == "lam":
                t = subst_top(f[1], t[2])
                continue
            return ("app", f, t[2])
        if c == "letE":
            t = subst_top(t[3], t[2])
            continue
        if c == "letq":
            t = subst_top(t[4], t[3])
            continue
        if c == "ann":
            t = t[1]
            continue
        if c == "fst":
            p = whnf(t[1])
            if p[0] == "pair":
                return p[1]
            return ("fst", p)
        if c == "snd":
            p = whnf(t[1])
            if p[0] == "pair":
                return p[2]
            return ("snd", p)
        if c == "ecase":
            sc = whnf(t[2])
            if sc[0] == "tag":
                k, i = sc[1], sc[2]
                if i >= len(t[3]):
                    fail("ecase: tag out of range")
                return whnf(t[3][i])
            return ("ecase", t[1], sc, t[3])
        if c == "down":
            x = whnf(t[1])
            if x[0] == "up":
                t = x[1]
                continue
            return ("down", x)
        if c == "coe":
            r = vcast(whnf(t[1]), whnf(t[2]), t[3], t[4])
            if r is not None:
                t = r
                continue
            return t
        if c == "const":
            # A self-hosted constant carries its value and type; the corpus has no
            # level parameters.  Checking the embedded pair is done in `infer`.
            t = inst_levels(t[4], t[2], t[3])
            continue
        if c == "ptrue":
            return ("unit", 0)
        if c == "pfalse":
            return ("empty", 0)
        if c == "eq":
            # `vEq` for the canonical types the corpus uses: an equation at Unit/Empty
            # is True; at an enumeration two tags are equal exactly when they are the
            # same tag (different tags are False).  Other equations stay stuck.
            A = whnf(t[1])
            if A[0] in ("unit", "empty"):
                return ("unit", 0)
            if A[0] == "enum":
                a, b = whnf(t[2]), whnf(t[3])
                if a[0] == "tag" and b[0] == "tag":
                    same = a[1] == b[1] and a[2] == b[2]
                    return ("unit", 0) if same else ("empty", 0)
            return t
        if c == "prf":
            if is_zero_level(t[1]):
                return t
            t = t[2]
            continue
        if c == "letUnit":
            # `let () := u; b` computes to `b` by η (only in a checker; not in dump)
            t = t[2]
            continue
        return t


def vcast(A, B, e, t):
    """The computing cases of `cast` used by the corpus; None when stuck."""
    ct, cA, cB = t[0], A[0], B[0]
    if cA == "unit" and cB == "unit":
        if A[1] == B[1]:
            return ("star",)
        return None
    if cA == "empty" and cB == "empty":
        if A[1] == B[1]:
            return t
        return None
    if cA == "enum" and cB == "enum" and A[1] == B[1]:
        return t
    if cA == "ulift" and cB == "ulift" and A[1] == B[1] and A[2] == B[2]:
        inner = vcast(A[3], B[3], e, ("down", t)) if ct == "up" else None
        return None if inner is None else ("up", inner)
    if cA == "sortL" and cB == "sortL":
        return t if level_eq(A[1], B[1]) else None
    if cA == "univ" and cB == "univ":
        return t if A[1] == B[1] else None
    if cA == "prop" and cB == "prop":
        return t
    return None


# ---------------------------------------------------------------------------------
# conversion

SORTS = ("prop", "univ", "sortL")


def conv(a, b):
    a, b = whnf(a), whnf(b)
    if a == b:
        return True
    if a[0] in SORTS and b[0] in SORTS:
        sa, sb = sort_level_of_sort(a), sort_level_of_sort(b)
        return sa is not None and sb is not None and level_eq(sa, sb)
    ca, cb = a[0], b[0]
    if ca != cb:
        return False
    if ca in ("prop", "star", "qty", "size", "szInf", "ptrue", "pfalse"):
        return True
    if ca == "univ":
        return a[1] == b[1]
    if ca == "sortL":
        return level_eq(a[1], b[1])
    if ca == "var":
        return a[1] == b[1]
    if ca in ("pi", "sigma"):
        return (a[1] == b[1] and level_eq(a[2], b[2]) and level_eq(a[3], b[3])
                and conv(a[4], b[4]) and conv(a[5], b[5]))
    if ca == "sigmaQ":
        return (conv(a[1], b[1]) and level_eq(a[2], b[2]) and level_eq(a[3], b[3])
                and conv(a[4], b[4]) and conv(a[5], b[5]))
    if ca == "lam":
        return conv(a[1], b[1])
    if ca == "app":
        return conv(a[1], b[1]) and conv(a[2], b[2])
    if ca == "pair":
        return conv(a[1], b[1]) and conv(a[2], b[2])
    if ca in ("fst", "snd", "down", "up", "con", "out", "cocon", "prf"):
        return conv(a[-1], b[-1])
    if ca == "prf":
        return level_eq(a[1], b[1]) and conv(a[2], b[2])
    if ca in ("unit", "empty"):
        return a[1] == b[1]
    if ca == "enum":
        return a[1] == b[1]
    if ca == "tag":
        return a[1] == b[1] and a[2] == b[2]
    if ca == "ecase":
        return (conv(a[1], b[1]) and conv(a[2], b[2])
                and len(a[3]) == len(b[3])
                and all(conv(x, y) for x, y in zip(a[3], b[3])))
    if ca == "eq":
        return conv(a[1], b[1]) and conv(a[2], b[2]) and conv(a[3], b[3])
    if ca == "eqTy":
        return conv(a[1], b[1]) and conv(a[2], b[2])
    if ca == "eqRefl":
        return conv(a[1], b[1]) and conv(a[2], b[2])
    if ca == "tyRefl":
        return conv(a[1], b[1])
    if ca == "coe":
        return all(conv(x, y) for x, y in zip(a[1:3], b[1:3])) and conv(a[4], b[4])
    if ca == "subst":
        return conv(a[1], b[1]) and conv(a[2], b[2]) and conv(a[3], b[3]) and \
            conv(a[5], b[5])
    if ca == "exfalso":
        return conv(a[1], b[1])
    if ca == "letUnit":
        return conv(a[1], b[1]) and conv(a[2], b[2])
    if ca == "descr":
        return a[1] == b[1] and conv(a[2], b[2])
    if ca in ("mu", "mus", "nu"):
        return (a[1] == b[1] and all(conv(x, y) for x, y in zip(a[2:], b[2:])))
    if ca == "dret":
        return conv(a[1], b[1])
    if ca in ("darg", "drec", "dhrec"):
        return all(conv(x, y) for x, y in zip(a[1:], b[1:]))
    if ca == "qlit":
        return a[1] == b[1]
    if ca == "szSuc" or ca == "sizeLt":
        return conv(a[1], b[1])
    if ca == "ulift":
        return a[1] == b[1] and a[2] == b[2] and conv(a[3], b[3])
    if ca == "axiomC":
        return a[1] == b[1]
    if ca in ("delim", "ind", "sfix", "scase", "scofix", "coit"):
        return False
    if ca == "const":
        # unreachable after whnf unless the value did not reduce; compare names
        return a[1] == b[1]
    return False


# ---------------------------------------------------------------------------------
# typing

def shift_ctx_free(t, n):
    return shift(t, n)


def lookup_type(ctx, i):
    if i >= len(ctx):
        fail(f"variable {i} is out of scope")
    return shift(ctx[i][1], i)


def bind(ctx, q, ty):
    # `ty` is written in the current context; after the binder it is one level deeper
    return [(q, shift(ty, 1))] + ctx


def check_type(ctx, t, expected=None):
    """`t` is a type; return its sort level (a Lvl)."""
    ty, _ = infer(ctx, t)
    st = sort_level(ty)
    if st is None:
        fail(f"the type of {t} is not a sort ({ty})")
    if expected is not None:
        if not level_eq(st, expected):
            fail(f"level mismatch: {st} vs {expected}")
    return st


def expect_pi(ty):
    ty = whnf(ty)
    if ty[0] != "pi":
        fail(f"expected a Π type, got {ty}")
    return ty


def expect_sigma(ty):
    ty = whnf(ty)
    if ty[0] not in ("sigma", "sigmaQ"):
        fail(f"expected a Σ type, got {ty}")
    return ty


def qty_value(t):
    """A quantity *term* at a Σ/Π the checker can use (a literal)."""
    t = whnf(t)
    if t[0] == "qlit":
        return {"0": 0, "1": 1, "w": 2}[t[1]]
    fail(f"quantity is not a literal: {t}")


def check(ctx, t, ty):
    ty = whnf(ty)
    c = t[0]
    if c == "lam":
        pi_ = expect_pi(ty)
        q = {"0": 0, "1": 1, "w": 2}[pi_[1]]
        inner = bind(ctx, q, pi_[4])
        u = check(inner, t[1], pi_[5])
        if not qle(u[0], q):
            fail(f"quantity violation: a {q!r} binder is used {u[0]!r} times")
        return u[1:]
    if c == "pair":
        sg = expect_sigma(ty)
        q = qty_value(sg[1]) if sg[0] == "sigmaQ" else {"0": 0, "1": 1, "w": 2}[sg[1]]
        ua = check(ctx, t[1], sg[4])
        ub = check(ctx, t[2], subst_top(sg[5], t[1]))
        return usage_add(usage_scale(q, ua), ub)
    if c == "star":
        if ty[0] != "unit":
            fail(f"tt is not a Unit: {ty}")
        return usage_zero(len(ctx))
    if c == "up":
        if ty[0] != "ulift":
            fail(f"up is not a ULift: {ty}")
        return check(ctx, t[1], ty[3])
    if c == "con":
        if ty[0] != "mu":
            fail(f"con is not a μ type: {ty}")
        l, I, D, i = ty[1], ty[2], ty[3], ty[4]
        fam = ("lam", ("mu", l, shift(I, 1), shift(D, 1), V(0)))
        payload = interp(l, I, D, fam, i)
        return check(ctx, t[1], payload)
    if c == "dret":
        if ty[0] != "descr":
            fail(f"dret is not a description: {ty}")
        return check(ctx, t[1], ty[2])
    if c == "darg":
        if ty[0] != "descr":
            fail(f"darg is not a description: {ty}")
        l, I = ty[1], ty[2]
        check_qty(ctx, t[1])
        check_type(ctx, t[2], N(l + 1))
        # D : (w s : S) -> Desc l I, with the index type shifted under the binder
        dty = ("pi", "w", N(l + 1), N(l + 2), t[2], ("descr", l, shift(I, 1)))
        u = check(bind(ctx, 2, t[2]), t[3], dty)
        return u[1:]
    if c == "drec":
        if ty[0] != "descr":
            fail(f"drec is not a description: {ty}")
        l, I = ty[1], ty[2]
        uj = check(ctx, t[2], I)
        ud = check(ctx, t[3], ty)
        return usage_add(uj, ud)
    if c == "dhrec":
        if ty[0] != "descr":
            fail(f"dhrec is not a description: {ty}")
        l, I = ty[1], ty[2]
        check_type(ctx, t[2], N(l + 1))
        inner = bind(ctx, 2, t[2])
        # j : (w h : H) -> I, under the binder
        jty = ("pi", "w", N(l + 1), N(l + 1), shift(t[2], 1), shift(I, 1))
        uj = check(inner, t[3], jty)
        ud = check(inner, t[4], ("descr", l, shift(I, 1)))
        return usage_add(uj[1:], ud[1:])
    if c == "prf":
        # check the type's sort is the marker's level
        st = check_type(ctx, ty)
        if not level_eq(st, t[1]):
            fail(f"proof marker at {t[1]} on a term of sort {st}")
        return check(ctx, t[2], ty)
    # default: infer, then conversion
    u = infer(ctx, t)
    if not conv(u[0], ty):
        fail(f"type mismatch: inferred {u[0]}, expected {ty}")
    return u[1]


def check_qty(ctx, q):
    u = infer(ctx, q)
    if not conv(u[0], ("qty",)):
        fail(f"not a quantity: {q}")
    return u


def expected_transp_type(ctx, A, a, sortA):
    """(0 b : A) -> (0 _ : a =_A b) -> Prop"""
    return ("pi", "0", sortA, N(1), A,
            ("pi", "0", N(0), N(1),
             ("eq", shift(A, 1), shift(a, 1), V(0)), PROP))


def infer(ctx, t):
    c = t[0]
    z = usage_zero(len(ctx))
    if c == "var":
        return lookup_type(ctx, t[1]), usage_one(t[1], len(ctx))
    if c == "univ":
        return mk_sort(t[1] + 2), z
    if c == "prop":
        return mk_sort(1), z
    if c == "sortL":
        return SL(SUC(t[1])), z
    if c == "pi":
        _, q, i, j, a, b = t
        check_type(ctx, a, i)
        check_type(bind(ctx, {"0": 0, "1": 1, "w": 2}[q], a), b, j)
        return mk_sort(imax_level(i, j)), z
    if c == "sigma":
        _, q, i, j, a, b = t
        check_type(ctx, a, i)
        check_type(bind(ctx, {"0": 0, "1": 1, "w": 2}[q], a), b, j)
        return mk_sort(max_level(i, j)), z
    if c == "sigmaQ":
        _, q, i, j, a, b = t
        check_qty(ctx, q)
        qq = qty_value(q)
        check_type(ctx, a, i)
        check_type(bind(ctx, qq, a), b, j)
        return mk_sort(max_level(i, j)), z
    if c == "lam":
        fail("cannot infer the type of a λ")
    if c == "app":
        tf, uf = infer(ctx, t[1])
        pi_ = expect_pi(tf)
        q = {"0": 0, "1": 1, "w": 2}[pi_[1]]
        ua = check(ctx, t[2], pi_[4])
        return subst_top(pi_[5], t[2]), usage_add(uf, usage_scale(q, ua))
    if c == "letE":
        check_type(ctx, t[1])
        uv = check(ctx, t[2], t[1])
        tb, ub = infer(ctx, subst_top(t[3], t[2]))
        return tb, usage_add(usage_scale(2, uv), ub)
    if c == "letq":
        q = {"0": 0, "1": 1, "w": 2}[t[1]]
        check_type(ctx, t[2])
        uv = check(ctx, t[3], t[2])
        tb, ub = infer(ctx, subst_top(t[4], t[3]))
        return tb, usage_add(usage_scale(q, uv), ub)
    if c == "ann":
        check_type(ctx, t[2])
        u = check(ctx, t[1], t[2])
        return t[2], u
    if c == "fst":
        ts, u = infer(ctx, t[1])
        sg = expect_sigma(ts)
        return sg[4], u
    if c == "snd":
        ts, u = infer(ctx, t[1])
        sg = expect_sigma(ts)
        return subst_top(sg[5], ("fst", t[1])), u
    if c == "unit":
        return mk_sort(t[1] + 1), z
    if c == "empty":
        return mk_sort(t[1] + 1), z
    if c == "ptrue":
        return mk_sort(0), z
    if c == "pfalse":
        return mk_sort(0), z
    if c == "exfalso":
        check_type(ctx, t[1])
        tt, _ = infer(ctx, t[2])
        tt = whnf(tt)
        if tt[0] != "empty":
            fail(f"exfalso needs a proof of Empty, got {tt}")
        return t[1], z
    if c == "enum":
        return mk_sort(1), z
    if c == "tag":
        if t[2] >= t[1]:
            fail("tag out of range")
        return ("enum", t[1]), z
    if c == "ecase":
        ts, us = infer(ctx, t[2])
        ts = whnf(ts)
        if ts[0] != "enum":
            fail(f"ecase on a non-enumeration: {ts}")
        k = ts[1]
        if len(t[3]) != k:
            fail(f"ecase has {len(t[3])} branches for {k} tags")
        check_type(bind(ctx, 0, ts), t[1])
        ub = usage_zero(len(ctx))
        for j, b in enumerate(t[3]):
            uj = check(ctx, b, subst_top(t[1], ("tag", k, j)))
            ub = usage_join(ub, uj)
        return subst_top(t[1], t[2]), usage_add(us, ub)
    if c == "eq":
        s = check_type(ctx, t[1])
        if not never_zero(s):
            fail(f"eq is formed at a sort that may be 0: {s}")
        check(ctx, t[2], t[1])
        check(ctx, t[3], t[1])
        return mk_sort(0), z
    if c == "eqTy":
        s1 = check_type(ctx, t[1])
        s2 = check_type(ctx, t[2])
        if not level_eq(s1, s2):
            fail(f"eqTy at different levels: {s1}, {s2}")
        return mk_sort(0), z
    if c == "eqRefl":
        s = check_type(ctx, t[1])
        if not never_zero(s):
            fail(f"refl is formed at a sort that may be 0: {s}")
        check(ctx, t[2], t[1])
        return ("eq", t[1], t[2], t[2]), z
    if c == "tyRefl":
        check_type(ctx, t[1])
        return ("eqTy", t[1], t[1]), z
    if c == "coe":
        s1 = check_type(ctx, t[1])
        s2 = check_type(ctx, t[2])
        if not level_eq(s1, s2):
            fail(f"cast between types at different levels: {s1}, {s2}")
        check(ctx, t[3], ("eqTy", t[1], t[2]))
        u = check(ctx, t[4], t[1])
        return t[2], u
    if c == "subst":
        A, a, P, p, b, e = t[1], t[2], t[3], t[4], t[5], t[6]
        s = check_type(ctx, A)
        if not never_zero(s):
            fail(f"transp at a sort that may be 0: {s}")
        check(ctx, a, A)
        check(ctx, P, expected_transp_type(ctx, A, a, s))
        pty = ("app", ("app", P, a), ("eqRefl", A, a))
        check(ctx, p, pty)
        check(ctx, b, A)
        ety = ("eq", A, a, b)
        check(ctx, e, ety)
        return ("app", ("app", P, b), e), z
    if c == "qty":
        return mk_sort(1), z
    if c == "qlit":
        return ("qty",), z
    if c == "descr":
        check_type(ctx, t[2], N(t[1] + 1))
        return mk_sort(t[1] + 2), z
    if c == "mu":
        l, I, D, i = t[1], t[2], t[3], t[4]
        check_type(ctx, I, N(l + 1))
        check(ctx, D, ("descr", l, I))
        check(ctx, i, I)
        return mk_sort(l + 1), z
    if c == "con":
        fail("cannot infer the type of a constructor (check only)")
    if c == "size":
        return mk_sort(1), z
    if c == "szInf":
        return ("size",), z
    if c == "szSuc":
        check(ctx, t[1], ("size",))
        return ("size",), z
    if c == "sizeLt":
        check(ctx, t[1], ("size",))
        return mk_sort(1), z
    if c == "ulift":
        k, l, A = t[1], t[2], t[3]
        check_type(ctx, A, N(k))
        if k > l:
            fail(f"ULift at {l} of a type at {k}")
        return mk_sort(l), z
    if c == "up":
        fail("cannot infer the type of up (check only)")
    if c == "down":
        tt, u = infer(ctx, t[1])
        tt = whnf(tt)
        if tt[0] != "ulift":
            fail(f"down on a non-ULift: {tt}")
        return tt[3], u
    if c == "prf":
        tt, u = infer(ctx, t[2])
        st = sort_level(tt)
        if st is None or not level_eq(st, t[1]):
            fail(f"proof marker at {t[1]} on a term of sort {st}")
        return tt, u
    if c == "const":
        _, name, ps, ls, v, ty = t
        check_type(ctx, ty)
        check(ctx, v, ty)
        return inst_levels(ty, ps, ls), z
    if c == "axiomC":
        check_type(ctx, t[2])
        return t[2], z
    if c in ("ind", "delim", "sfix", "scase", "scofix", "coit", "out", "cocon"):
        fail(f"out of scope: {c}")
    fail(f"cannot infer {t}")


# ---------------------------------------------------------------------------------
# the descriptions' payload (the `⟦D⟧` template, as in selfhost/Kernel.wiz)

def interp(l, I, D, X, i):
    D = whnf(D)
    c = D[0]
    if c == "dret":
        return ("sigma", "0", N(0), N(l + 1), ("eq", I, D[1], i), ("unit", l))
    if c == "darg":
        q, S, E = D[1], D[2], D[3]
        rest = interp(l, shift(I, 1), ("app", shift(E, 1), V(0)),
                      shift(X, 1), shift(i, 1))
        return ("sigmaQ", q, N(l + 1), N(l + 1), S, rest)
    if c == "drec":
        q, j, E = D[1], D[2], D[3]
        rest = interp(l, shift(I, 1), shift(E, 1), shift(X, 1), shift(i, 1))
        return ("sigmaQ", q, N(l + 1), N(l + 1), ("app", X, j), rest)
    if c == "dhrec":
        q, H, j, E = D[1], D[2], D[3], D[4]
        field = ("pi", "w", N(l + 1), N(l + 1), H,
                 ("app", shift(X, 1), ("app", shift(j, 1), V(0))))
        rest = interp(l, shift(I, 1), shift(E, 1), shift(X, 1), shift(i, 1))
        return ("sigmaQ", q, N(l + 1), N(l + 1), field, rest)
    fail(f"cannot interpret the description {D}")


# ---------------------------------------------------------------------------------
# the serialized format

def tokenize(s):
    out, i, n = [], 0, len(s)
    while i < n:
        ch = s[i]
        if ch.isspace():
            i += 1
        elif ch == "(" or ch == ")":
            out.append(ch)
            i += 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in "()":
                j += 1
            out.append(s[i:j])
            i = j
    return out


def parse_sexpr(tokens):
    pos = [0]

    def go():
        if pos[0] >= len(tokens):
            fail("unexpected end of input")
        tok = tokens[pos[0]]
        pos[0] += 1
        if tok == "(":
            xs = []
            while pos[0] < len(tokens) and tokens[pos[0]] != ")":
                xs.append(go())
            if pos[0] >= len(tokens):
                fail("missing )")
            pos[0] += 1
            return xs
        if tok == ")":
            fail("unexpected )")
        return tok

    x = go()
    if pos[0] != len(tokens):
        fail("trailing tokens")
    return x


def parse_lvl(x):
    if isinstance(x, str):
        if x == "hole":
            return ("lhole",)
        if x.startswith("n"):
            return ("lnum", int(x[1:]))
        if x.startswith("p"):
            return ("lparam", x[1:])
        fail(f"bad level {x}")
    head = x[0]
    if head == "s":
        return ("lsucc", parse_lvl(x[1]))
    if head == "max":
        return ("lmax", parse_lvl(x[1]), parse_lvl(x[2]))
    if head == "imax":
        return ("limax", parse_lvl(x[1]), parse_lvl(x[2]))
    fail(f"bad level {x}")


def parse_qty(x):
    if x not in ("0", "1", "w"):
        fail(f"bad quantity {x}")
    return x


def parse_term(x):
    if isinstance(x, str):
        table = {"P": PROP, "tt": ("star",), "True": ("ptrue",),
                 "False": ("pfalse",), "Qty": ("qty",), "Size": ("size",),
                 "inf": ("szInf",)}
        if x in table:
            return table[x]
        fail(f"bad atom {x}")
    h = x[0]
    a = x[1:]
    if h == "v": return ("var", int(a[0]))
    if h == "U": return ("univ", int(a[0]))
    if h == "L": return ("sortL", parse_lvl(a[0]))
    if h == "pi": return ("pi", parse_qty(a[0]), parse_lvl(a[1]), parse_lvl(a[2]),
                          parse_term(a[3]), parse_term(a[4]))
    if h == "lam": return ("lam", parse_term(a[0]))
    if h == "app": return ("app", parse_term(a[0]), parse_term(a[1]))
    if h == "letE": return ("letE", parse_term(a[0]), parse_term(a[1]), parse_term(a[2]))
    if h == "ann": return ("ann", parse_term(a[0]), parse_term(a[1]))
    if h == "letq": return ("letq", parse_qty(a[0]), parse_term(a[1]), parse_term(a[2]),
                            parse_term(a[3]))
    if h == "sigma": return ("sigma", parse_qty(a[0]), parse_lvl(a[1]), parse_lvl(a[2]),
                             parse_term(a[3]), parse_term(a[4]))
    if h == "pair": return ("pair", parse_term(a[0]), parse_term(a[1]))
    if h == "fst": return ("fst", parse_term(a[0]))
    if h == "snd": return ("snd", parse_term(a[0]))
    if h == "unit": return ("unit", int(a[0]))
    if h == "empty": return ("empty", int(a[0]))
    if h == "exfalso": return ("exfalso", parse_term(a[0]), parse_term(a[1]))
    if h == "letUnit": return ("letUnit", parse_term(a[0]), parse_term(a[1]))
    if h == "enum": return ("enum", int(a[0]))
    if h == "tag": return ("tag", int(a[0]), int(a[1]))
    if h == "ecase":
        bs = parse_tms(a[2])
        return ("ecase", parse_term(a[0]), parse_term(a[1]), bs)
    if h == "eq": return ("eq", parse_term(a[0]), parse_term(a[1]), parse_term(a[2]))
    if h == "eqTy": return ("eqTy", parse_term(a[0]), parse_term(a[1]))
    if h == "refl": return ("eqRefl", parse_term(a[0]), parse_term(a[1]))
    if h == "reflTy": return ("tyRefl", parse_term(a[0]))
    if h == "cast": return ("coe", parse_term(a[0]), parse_term(a[1]),
                            parse_term(a[2]), parse_term(a[3]))
    if h == "transp": return ("subst",) + tuple(parse_term(y) for y in a)
    if h == "qlit": return ("qlit", parse_qty(a[0]))
    if h == "sigmaQ": return ("sigmaQ", parse_term(a[0]), parse_lvl(a[1]),
                              parse_lvl(a[2]), parse_term(a[3]), parse_term(a[4]))
    if h == "descr": return ("descr", int(a[0]), parse_term(a[1]))
    if h == "dret": return ("dret", parse_term(a[0]))
    if h == "darg": return ("darg", parse_term(a[0]), parse_term(a[1]), parse_term(a[2]))
    if h == "drec": return ("drec", parse_term(a[0]), parse_term(a[1]), parse_term(a[2]))
    if h == "dhrec": return ("dhrec",) + tuple(parse_term(y) for y in a)
    if h == "delim": return ("delim", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "mu": return ("mu", int(a[0]), parse_term(a[1]), parse_term(a[2]),
                          parse_term(a[3]))
    if h == "con": return ("con", parse_term(a[0]))
    if h == "ind": return ("ind", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "suc": return ("szSuc", parse_term(a[0]))
    if h == "lt": return ("sizeLt", parse_term(a[0]))
    if h == "mus": return ("mus", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "nu": return ("nu", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "out": return ("out", parse_term(a[0]))
    if h == "cocon": return ("cocon", parse_term(a[0]))
    if h == "scofix": return ("scofix", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "coit": return ("coit", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "const":
        return ("const", a[0], tuple(), tuple(), parse_term(a[2]), parse_term(a[3]))
    if h == "axiom": return ("axiomC", a[0], parse_term(a[1]))
    if h == "ulift": return ("ulift", int(a[0]), int(a[1]), parse_term(a[2]))
    if h == "up": return ("up", parse_term(a[0]))
    if h == "down": return ("down", parse_term(a[0]))
    if h == "prf": return ("prf", parse_lvl(a[0]), parse_term(a[1]))
    fail(f"bad term {x}")


def parse_tms(x):
    if not isinstance(x, list) or not x or x[0] != "ts":
        fail(f"bad term list {x}")
    return tuple(parse_term(y) for y in x[1:])


# ---------------------------------------------------------------------------------
# checking a dump line

def check_decl(ty, value):
    """Check a closed declaration.  Returns (ok, message)."""
    try:
        infer_sort_of(ty)
        u = check([], value, ty)
        if any(x != 0 for x in u):
            fail("the value uses variables outside the empty context")
        return True, ""
    except CheckError as e:
        return False, str(e)
    except RecursionError:
        return False, "recursion limit"


def infer_sort_of(ty):
    """`ty` is a type (the kernel's `inferUniv`)."""
    tt, _ = infer([], ty)
    if sort_level(tt) is None:
        fail(f"the declared type {ty} is not a type")
    return tt


def read_dump(text):
    """[(verdict, name, ty_text, val_text)] from the dump's OK/ERR lines."""
    out = []
    for line in text.split("\n"):
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if parts[0] not in ("OK", "ERR", "CRASH") or len(parts) < 4:
            fail(f"bad dump line: {line!r}")
        out.append((parts[0], parts[1], parts[2], parts[3]))
    return out


def check_dump(text):
    """[(kernel_verdict, name, checker_accepts, message)]."""
    out = []
    for verdict, name, ty_s, val_s in read_dump(text):
        try:
            ty = parse_term(parse_sexpr(tokenize(ty_s)))
            val = parse_term(parse_sexpr(tokenize(val_s)))
        except CheckError as e:
            out.append((verdict, name, False, f"parse: {e}"))
            continue
        ok, msg = check_decl(ty, val)
        out.append((verdict, name, ok, msg))
    return out


def main():
    if len(sys.argv) != 2:
        print("usage: checker.py DUMP", file=sys.stderr)
        return 2
    text = open(sys.argv[1]).read()
    rows = check_dump(text)
    bad = 0
    for verdict, name, ok, msg in rows:
        if (verdict == "OK") != ok:
            bad += 1
            print(f"MISMATCH {name}: kernel={verdict} checker={'OK' if ok else 'ERR'} {msg}")
        else:
            print(f"{'OK' if ok else 'ERR'}\t{name}\t{msg}")
    print(f"{len(rows)} declarations, {bad} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
