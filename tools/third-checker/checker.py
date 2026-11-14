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
#
# The kernel (`Lvl` in selfhost/Kernel.wiz) compares levels by a normal form: a sorted
# list of atoms, each with a multiplicity, where an atom is a constant, a parameter, or
# an `imax` (the only non-distributive case).  `imax a b` is `max a b` when `b` is
# certainly non-zero, `0` when `b` is `0`, and an opaque atom otherwise.  Two levels
# that differ only in the *value* of an `imax` parameter are split on that parameter
# (`p = 0`, `p = p+1`), as `Level.equiv` does.  This is the rule the self-hosted kernel
# uses, so a parameter is not merely compared syntactically.

NF_ZERO = ((("const",), 0),)


def atom_eq(a, b):
    if a[0] != b[0]:
        return False
    if a[0] == "const":
        return True
    if a[0] == "param":
        return a[1] == b[1]
    return nf_eq(a[1], b[1]) and nf_eq(a[2], b[2])


def nf_eq(a, b):
    return a == b


def atom_show(a):
    if a[0] == "const":
        return "0"
    if a[0] == "param":
        return a[1]
    return f"imax({nf_show(a[1])}, {nf_show(a[2])})"


def nf_show(n):
    return " ".join(f"{atom_show(a)}+{k}" for a, k in n)


def atom_rank(a):
    return {"const": 0, "param": 1, "imax": 2}[a[0]]


def atom_lt(a, b):
    if a[0] == "param" and b[0] == "param":
        return a[1] < b[1]
    if a[0] == "imax" and b[0] == "imax":
        return atom_show(a) < atom_show(b)
    return atom_rank(a) < atom_rank(b)


def nf_insert(x, k, n):
    out = list(n)
    for i, (a, m) in enumerate(out):
        if atom_eq(a, x):
            out[i] = (a, max(k, m))
            return tuple(out)
        if atom_lt(x, a):
            out.insert(i, (x, k))
            return tuple(out)
    out.append((x, k))
    return tuple(out)


def nf_merge(a, b):
    out = b
    for x, k in a:
        out = nf_insert(x, k, out)
    return out


def nf_shift(n):
    return tuple((a, k + 1) for a, k in n)


def nf_others(n):
    return tuple((a, k) for a, k in n if a[0] != "const")


def nf_max_k(n):
    return max((k for _, k in n), default=0)


def nf_const(n):
    for a, k in n:
        if a[0] == "const":
            return k
    return None


def nf_cleanup(n):
    c = nf_const(n)
    if c is None:
        return n
    others = nf_others(n)
    if not others:
        return n
    if c <= nf_max_k(others):
        return others
    return n


def nf_nonzero(n):
    return any(k > 0 for _, k in n)


def lvl_norm(l):
    c = l[0]
    if c == "lnum":
        return ((("const",), l[1]),)
    if c == "lparam":
        return ((("param", l[1]), 0),)
    if c == "lhole":
        return ((("param", " _"), 0),)
    if c == "lsucc":
        return nf_cleanup(nf_shift(lvl_norm(l[1])))
    if c == "lmax":
        return nf_cleanup(nf_merge(lvl_norm(l[1]), lvl_norm(l[2])))
    if c == "limax":
        na, nb = lvl_norm(l[1]), lvl_norm(l[2])
        if nf_nonzero(nb):
            return nf_cleanup(nf_merge(na, nb))
        if nf_eq(nb, NF_ZERO):
            return NF_ZERO
        return ((("imax", na, nb), 0),)
    fail(f"bad level {l}")


def lvl_params(l):
    c = l[0]
    if c == "lparam":
        return [l[1]]
    if c in ("lsucc",):
        return lvl_params(l[1])
    if c in ("lmax", "limax"):
        return lvl_params(l[1]) + lvl_params(l[2])
    return []


def imax_param(l):
    c = l[0]
    if c == "lsucc":
        return imax_param(l[1])
    if c == "lmax":
        return imax_param(l[1]) or imax_param(l[2])
    if c == "limax":
        return (imax_param(l[1]) or imax_param(l[2]) or
                (None if never_zero(l[2]) else next(iter(lvl_params(l[2])), None)))
    return None


def lookup_lvl(ps, ls, name):
    for p, l in zip(ps, ls):
        if p == name:
            return l
    return ("lparam", name)


def subst_lvl(ps, ls, l):
    c = l[0]
    if c == "lparam":
        return lookup_lvl(ps, ls, l[1])
    if c == "lsucc":
        return ("lsucc", subst_lvl(ps, ls, l[1]))
    if c == "lmax":
        return ("lmax", subst_lvl(ps, ls, l[1]), subst_lvl(ps, ls, l[2]))
    if c == "limax":
        return ("limax", subst_lvl(ps, ls, l[1]), subst_lvl(ps, ls, l[2]))
    return l


def level_eq_f(depth, a, b):
    if nf_eq(lvl_norm(a), lvl_norm(b)):
        return True
    if depth == 0:
        return False
    p = imax_param(a) or imax_param(b)
    if p is None:
        return False
    z = subst_lvl([p], [N(0)], a), subst_lvl([p], [N(0)], b)
    sp = (subst_lvl([p], [SUC(("lparam", p))], a),
          subst_lvl([p], [SUC(("lparam", p))], b))
    return level_eq_f(depth - 1, *z) and level_eq_f(depth - 1, *sp)


def level_eq(a, b):
    """Equality of levels with parameters, as `Level.equiv` (the kernel's rule)."""
    return level_eq_f(8, a, b)


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
    """a <= b."""
    return level_eq(MAX(a, b), b)


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
    return nf_nonzero(lvl_norm(l))


def is_zero_level(l):
    v = closed_level(l)
    if v is not None:
        return v == 0
    return level_eq(l, N(0))


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
    if c == "delim":
        # (delim v P mret marg mrec mhrec D): no binder at the node (the method types
        # carry their own)
        return ("delim", t[1]) + tuple(shift(x, k, cutoff) for x in t[2:])
    if c == "ind":
        # (ind l I D v P m i x): no binder at the node
        return ("ind", t[1]) + tuple(shift(x, k, cutoff) for x in t[2:])
    if c == "split":
        # (split q scrut motive body): the motive has one binder (`z`), the body two
        # (`x`, `y`)
        return ("split", t[1], shift(t[2], k, cutoff), shift(t[3], k, cutoff + 1),
                shift(t[4], k, cutoff + 2))
    if c == "interp":
        # an internal lazy `⟦D⟧` (never serialized): no binder at the node
        return (c, t[1]) + tuple(shift(x, k, cutoff) for x in t[2:])
    if c == "all":
        # an internal lazy `All` (never serialized): no binder at the node
        return (c, t[1], t[2]) + tuple(shift(x, k, cutoff) for x in t[3:])
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
    if c == "delim":
        return (c, t[1]) + tuple(subst(x, j, s) for x in t[2:])
    if c == "ind":
        return (c, t[1]) + tuple(subst(x, j, s) for x in t[2:])
    if c == "split":
        return (c, t[1], subst(t[2], j, s), subst(t[3], j + 1, shift(s, 1)),
                subst(t[4], j + 2, shift(s, 2)))
    if c == "interp":
        return (c, t[1]) + tuple(subst(x, j, s) for x in t[2:])
    if c == "all":
        return (c, t[1], t[2]) + tuple(subst(x, j, s) for x in t[3:])
    return t


def subst_top(body, arg):
    # `subst` already decrements the variables above the removed binder, so there is no
    # second closing shift (a shift(-1) here under-counted every outer variable)
    return subst(body, 0, arg)


def subst_add0(t, s, add):
    """Substitute `s` for variable 0 and add `add` to every other *free* variable.

    `add = -1` is `subst_top` (remove a binder).  `add = +1` opens a binder in a
    context with one more binder, which is what `split`'s motive needs: its `z` is
    replaced by the pair `(x, y)` (two binders replace one)."""
    c = t[0]
    if c == "var":
        return s if t[1] == 0 else ("var", t[1] + add)
    if c == "pi" or c == "sigma":
        return (c, t[1], t[2], t[3], subst_add0(t[4], s, add),
                subst_add0(t[5], shift(s, 1), add))
    if c == "sigmaQ":
        return (c, subst_add0(t[1], s, add), t[2], t[3],
                subst_add0(t[4], s, add), subst_add0(t[5], shift(s, 1), add))
    if c == "lam":
        return ("lam", subst_add0(t[1], shift(s, 1), add))
    if c == "letE":
        return (c, subst_add0(t[1], s, add), subst_add0(t[2], s, add),
                subst_add0(t[3], shift(s, 1), add))
    if c == "letq":
        return (c, t[1], subst_add0(t[2], s, add), subst_add0(t[3], s, add),
                subst_add0(t[4], shift(s, 1), add))
    if c in ("ann", "letUnit", "pair", "app", "eqTy", "eqRefl", "exfalso",
             "szSuc", "sizeLt"):
        return (c,) + tuple(subst_add0(x, s, add) for x in t[1:])
    if c == "ecase":
        return (c, subst_add0(t[1], s, add), subst_add0(t[2], s, add),
                tuple(subst_add0(b, s, add) for b in t[3]))
    if c in ("eq", "coe", "subst", "darg", "drec", "dhrec"):
        return (c,) + tuple(subst_add0(x, s, add) for x in t[1:])
    if c == "delim" or c == "ind":
        return (c, t[1]) + tuple(subst_add0(x, s, add) for x in t[2:])
    if c == "tyRefl" or c in ("con", "out", "cocon", "up", "down", "dret", "fst", "snd"):
        return (c, subst_add0(t[1], s, add))
    if c in ("mu", "mus", "nu"):
        return (c, t[1]) + tuple(subst_add0(x, s, add) for x in t[2:])
    if c == "descr":
        return (c, t[1], subst_add0(t[2], s, add))
    if c == "prf":
        return (c, t[1], subst_add0(t[2], s, add))
    if c == "const":
        return (c, t[1], t[2], t[3], subst_add0(t[4], s, add),
                subst_add0(t[5], s, add))
    if c == "axiomC":
        return (c, t[1], subst_add0(t[2], s, add))
    if c == "split":
        return (c, t[1], subst_add0(t[2], s, add),
                subst_add0(t[3], shift(s, 1), add),
                subst_add0(t[4], shift(s, 2), add))
    if c == "interp":
        return (c, t[1]) + tuple(subst_add0(x, s, add) for x in t[2:])
    if c == "all":
        return (c, t[1], t[2]) + tuple(subst_add0(x, s, add) for x in t[3:])
    return t


def subst_tm_levels(ps, ls, t):
    """Instantiate a term's level parameters (the kernel's `tmSubst`)."""
    c = t[0]
    if c == "sortL":
        return ("sortL", subst_lvl(ps, ls, t[1]))
    if c == "pi":
        return ("pi", t[1], subst_lvl(ps, ls, t[2]), subst_lvl(ps, ls, t[3]),
                subst_tm_levels(ps, ls, t[4]), subst_tm_levels(ps, ls, t[5]))
    if c == "sigma":
        return ("sigma", t[1], subst_lvl(ps, ls, t[2]), subst_lvl(ps, ls, t[3]),
                subst_tm_levels(ps, ls, t[4]), subst_tm_levels(ps, ls, t[5]))
    if c == "sigmaQ":
        return ("sigmaQ", subst_tm_levels(ps, ls, t[1]),
                subst_lvl(ps, ls, t[2]), subst_lvl(ps, ls, t[3]),
                subst_tm_levels(ps, ls, t[4]), subst_tm_levels(ps, ls, t[5]))
    if c == "prf":
        return ("prf", subst_lvl(ps, ls, t[1]), subst_tm_levels(ps, ls, t[2]))
    if c == "const":
        return ("const", t[1], t[2],
                tuple(subst_lvl(ps, ls, l) for l in t[3]),
                subst_tm_levels(ps, ls, t[4]), subst_tm_levels(ps, ls, t[5]))
    if c == "var" or c in ("univ", "prop", "star", "unit", "empty", "ptrue",
                           "pfalse", "enum", "tag", "qty", "qlit", "size", "szInf",
                           "descr", "mu", "mus", "nu", "dret", "darg", "drec",
                           "dhrec", "axiomC"):
        # the term constructors whose payload is not a term or whose numeric fields
        # are level-free; recurse where there is one
        if c in ("dret",):
            return (c, subst_tm_levels(ps, ls, t[1]))
        if c in ("darg", "drec", "dhrec"):
            return (c,) + tuple(subst_tm_levels(ps, ls, x) for x in t[1:])
        if c in ("descr",):
            return (c, t[1], subst_tm_levels(ps, ls, t[2]))
        if c in ("mu", "mus", "nu"):
            return (c, t[1]) + tuple(subst_tm_levels(ps, ls, x) for x in t[2:])
        if c == "axiomC":
            return (c, t[1], subst_tm_levels(ps, ls, t[2]))
        return t
    if c == "lam":
        return ("lam", subst_tm_levels(ps, ls, t[1]))
    if c == "letE":
        return (c,) + tuple(subst_tm_levels(ps, ls, x) for x in t[1:])
    if c in ("app", "ann", "letUnit", "pair", "eq", "eqTy", "eqRefl", "coe",
             "subst", "exfalso", "szSuc", "sizeLt", "tyRefl", "con", "out",
             "cocon", "up", "down", "fst", "snd"):
        return (c,) + tuple(subst_tm_levels(ps, ls, x) for x in t[1:])
    if c == "ecase":
        return (c, subst_tm_levels(ps, ls, t[1]), subst_tm_levels(ps, ls, t[2]),
                tuple(subst_tm_levels(ps, ls, b) for b in t[3]))
    if c == "delim" or c == "ind":
        return (c, t[1]) + tuple(subst_tm_levels(ps, ls, x) for x in t[2:])
    if c == "split":
        return (c, t[1], subst_tm_levels(ps, ls, t[2]),
                subst_tm_levels(ps, ls, t[3]), subst_tm_levels(ps, ls, t[4]))
    return t


def inst_levels(t, ps, ls):
    """Instantiate a constant's level parameters (`substIfAny`)."""
    if not ps:
        return t
    return subst_tm_levels(ps, ls, t)


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
            # A self-hosted constant carries its value and type and its level
            # parameters; instantiate them before unfolding (the kernel's `vglued`
            # memo does the same).
            t = inst_levels(t[4], t[2], t[3])
            continue
        if c == "sigmaQ":
            # a Σ at a literal quantity *is* a Σ (`vSigmaQ` evaluates `q`); at a stuck
            # quantity (a `Desc.elim` method's `q`) it stays `sigmaQ`
            q = whnf(t[1])
            if q[0] == "qlit":
                t = ("sigma", q[1], t[2], t[3], t[4], t[5])
                continue
            return ("sigmaQ", q, t[2], t[3], t[4], t[5])
        if c == "split":
            # η for Σ: `let q (x, y) := (a, b); u` computes to `u[a/x, b/y]`
            sc = whnf(t[2])
            if sc[0] == "pair":
                t = subst_top(subst_top(t[4], sc[2]), sc[1])
                continue
            return ("split", t[1], sc, t[3], t[4])
        if c == "interp":
            # the internal lazy payload template: compute it now that `D` is known
            r = interp(t[1], t[2], t[3], t[4], t[5])
            if r[0] == "interp":
                return r
            t = r
            continue
        if c == "all":
            # the internal lazy `All` template: compute it when `D` is a constructor
            D = whnf(t[4])
            if D[0] not in ("dret", "darg", "drec", "dhrec"):
                return ("all", t[1], t[2], t[3], D, t[5], t[6], t[7], t[8])
            t = all_type(t[1], t[2], t[3], D, t[5], t[6], t[7], t[8])
            continue
        # `True` and `False` are their own values (`.`vunit 0` / `.vempty 0` in the
        # kernel): they are propositions, not `Unit 0`/`Empty 0` (which live one level
        # up).  Keeping them distinct matters for the sort of a `prf` marker.
        if c == "ptrue" or c == "pfalse":
            return t
        if c == "eq":
            # `vEq` for the canonical types the corpus uses: an equation at a
            # proposition is True (proof irrelevance); at Unit/Empty it is True; at an
            # enumeration two tags are equal exactly when they are the same tag
            # (different tags are False); at a `ULift` of a type it is the equation of
            # the content (a lifted proposition has one inhabitant).  Other equations
            # stay stuck.
            A = whnf(t[1])
            if A[0] in ("unit", "empty", "ptrue", "pfalse", "eq", "eqTy"):
                return ("ptrue",)
            if A[0] == "pi":
                if is_zero_level(A[3]):
                    return ("ptrue",)
            elif A[0] == "sigma":
                if is_zero_level(A[2]) and is_zero_level(A[3]):
                    return ("ptrue",)
            elif A[0] == "ulift":
                if is_zero_level(A[2]):
                    return ("ptrue",)
                return ("eq", A[3], ("down", t[2]), ("down", t[3]))
            elif A[0] == "enum":
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
    # A cast between propositions is itself a proof: with lazy proofs the kernel keeps
    # it stuck (it is accepted by proof irrelevance, never computed).
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
    if ca == "prf":
        return level_eq(a[1], b[1]) and conv(a[2], b[2])
    if ca in ("fst", "snd", "down", "up", "con", "out", "cocon"):
        return conv(a[-1], b[-1])
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
    if ca == "split":
        return (a[1] == b[1] and conv(a[2], b[2]) and conv(a[3], b[3])
                and conv(a[4], b[4]))
    if ca == "delim":
        return a[1] == b[1] and all(conv(x, y) for x, y in zip(a[2:], b[2:]))
    if ca == "ind":
        return a[1] == b[1] and all(conv(x, y) for x, y in zip(a[2:], b[2:]))
    if ca == "interp":
        return a[1] == b[1] and all(conv(x, y) for x, y in zip(a[2:], b[2:]))
    if ca == "all":
        return (a[1] == b[1] and a[2] == b[2]
                and all(conv(x, y) for x, y in zip(a[3:], b[3:])))
    if ca in ("sfix", "scase", "scofix", "coit"):
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
    """`t` is a type; return its sort level (a Lvl).  Types are erased positions."""
    ty, _ = infer(ctx, t, True)
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


def check(ctx, t, ty, erased=False):
    ty = whnf(ty)
    c = t[0]
    if c == "lam":
        pi_ = expect_pi(ty)
        q = {"0": 0, "1": 1, "w": 2}[pi_[1]]
        inner = bind(ctx, q, pi_[4])
        u = check(inner, t[1], pi_[5], erased)
        if not qle(u[0], q):
            fail(f"quantity violation: a {q!r} binder is used {u[0]!r} times")
        return u[1:]
    if c == "pair":
        sg = expect_sigma(ty)
        if sg[0] == "sigmaQ":
            qv = whnf(sg[1])
            if qv[0] == "qlit":
                q = {"0": 0, "1": 1, "w": 2}[qv[1]]
            elif qv[0] == "var":
                # the kernel's `qtyPoly` case: only a variable is accepted, and the
                # first part is counted ω times (at least as much as at any value)
                q = 2
            else:
                fail(f"a pair at a stuck quantity needs a literal or variable: {qv}")
        else:
            q = {"0": 0, "1": 1, "w": 2}[sg[1]]
        ua = check(ctx, t[1], sg[4], erased or q == 0)
        ub = check(ctx, t[2], subst_top(sg[5], t[1]), erased)
        return usage_add(usage_scale(q, ua), ub)
    if c == "letUnit":
        uu = check_unit(ctx, t[1], erased)
        ub = check(ctx, t[2], ty, erased)
        return usage_add(uu, ub)
    if c == "star":
        if ty[0] not in ("unit", "ptrue"):
            fail(f"tt is not a Unit/True: {ty}")
        return usage_zero(len(ctx))
    if c == "up":
        if ty[0] != "ulift":
            fail(f"up is not a ULift: {ty}")
        return check(ctx, t[1], ty[3], erased)
    if c == "con":
        if ty[0] != "mu":
            fail(f"con is not a μ type: {ty}")
        l, I, D, i = ty[1], ty[2], ty[3], ty[4]
        fam = ("lam", ("mu", l, shift(I, 1), shift(D, 1), V(0)))
        payload = interp(l, I, D, fam, i)
        return check(ctx, t[1], payload, erased)
    if c == "dret":
        if ty[0] != "descr":
            fail(f"dret is not a description: {ty}")
        return check(ctx, t[1], ty[2], erased)
    if c == "darg":
        if ty[0] != "descr":
            fail(f"darg is not a description: {ty}")
        l, I = ty[1], ty[2]
        check_qty(ctx, t[1])
        check_type(ctx, t[2], N(l + 1))
        # D : (w s : S) -> Desc l I, with the index type shifted under the binder
        dty = ("pi", "w", N(l + 1), N(l + 2), t[2], ("descr", l, shift(I, 1)))
        u = check(bind(ctx, 2, t[2]), t[3], dty, erased)
        return u[1:]
    if c == "drec":
        if ty[0] != "descr":
            fail(f"drec is not a description: {ty}")
        l, I = ty[1], ty[2]
        uj = check(ctx, t[2], I, erased)
        ud = check(ctx, t[3], ty, erased)
        return usage_add(uj, ud)
    if c == "dhrec":
        if ty[0] != "descr":
            fail(f"dhrec is not a description: {ty}")
        l, I = ty[1], ty[2]
        check_type(ctx, t[2], N(l + 1))
        inner = bind(ctx, 2, t[2])
        # j : (w h : H) -> I, under the binder
        jty = ("pi", "w", N(l + 1), N(l + 1), shift(t[2], 1), shift(I, 1))
        uj = check(inner, t[3], jty, erased)
        ud = check(inner, t[4], ("descr", l, shift(I, 1)), erased)
        return usage_add(uj[1:], ud[1:])
    if c == "letE" or c == "letq":
        if c == "letE":
            q, lty, v, b = 2, t[1], t[2], t[3]
        else:
            q, lty, v, b = {"0": 0, "1": 1, "w": 2}[t[1]], t[2], t[3], t[4]
        check_type(ctx, lty)
        uv = check(ctx, v, lty, erased or q == 0)
        ub = check(bind(ctx, q, lty), b, shift(ty, 1), erased)
        if not qle(ub[0], q):
            fail(f"the let-bound variable's usage does not fit its quantity: {ub[0]!r} at {q!r}")
        return usage_add(usage_scale(q, uv), ub[1:])
    if c == "prf":
        # check the type's sort is the marker's level
        st = check_type(ctx, ty)
        if not level_eq(st, t[1]):
            fail(f"proof marker at {t[1]} on a term of sort {st}")
        return check(ctx, t[2], ty, erased)
    # default: infer, then conversion
    u = infer(ctx, t, erased)
    if not conv(u[0], ty):
        fail(f"type mismatch: inferred {u[0]}, expected {ty}")
    return u[1]


def check_qty(ctx, q):
    u = infer(ctx, q, True)
    if not conv(u[0], ("qty",)):
        fail(f"not a quantity: {q}")
    return u


def check_unit(ctx, u, erased=False):
    """`u : Unit` for `let () := u; b`; returns u's usage."""
    if u[0] == "star":
        return usage_zero(len(ctx))
    ty, uu = infer(ctx, u, erased)
    ty = whnf(ty)
    if ty[0] != "unit":
        fail(f"let () := u needs u of type Unit, not {ty}")
    return uu


def expected_transp_type(ctx, A, a, sortA):
    """(0 b : A) -> (0 _ : a =_A b) -> Prop"""
    return ("pi", "0", sortA, N(1), A,
            ("pi", "0", N(0), N(1),
             ("eq", shift(A, 1), shift(a, 1), V(0)), PROP))


def infer(ctx, t, erased=False):
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
        tf, uf = infer(ctx, t[1], erased)
        pi_ = expect_pi(tf)
        q = {"0": 0, "1": 1, "w": 2}[pi_[1]]
        ua = check(ctx, t[2], pi_[4], erased or q == 0)
        return subst_top(pi_[5], t[2]), usage_add(uf, usage_scale(q, ua))
    if c == "letE" or c == "letq":
        if c == "letE":
            q, ty, v, b = 2, t[1], t[2], t[3]
        else:
            q, ty, v, b = {"0": 0, "1": 1, "w": 2}[t[1]], t[2], t[3], t[4]
        check_type(ctx, ty)
        uv = check(ctx, v, ty, erased or q == 0)
        # the body is checked with its variable bound at `q`, so a variable used twice
        # under a `1` let is rejected (substituting the value first would lose this)
        tb, ub = infer(bind(ctx, q, ty), b, erased)
        if not qle(ub[0], q):
            fail(f"the let-bound variable's usage does not fit its quantity: {ub[0]!r} at {q!r}")
        return subst_top(tb, v), usage_add(usage_scale(q, uv), ub[1:])
    if c == "ann":
        check_type(ctx, t[2])
        u = check(ctx, t[1], t[2], erased)
        return t[2], u
    if c == "fst":
        ts, u = infer(ctx, t[1], erased)
        sg = expect_sigma(ts)
        if not erased:
            if sg[0] == "sigmaQ":
                fail("cannot project a field whose quantity is a variable")
            q = {"0": 0, "1": 1, "w": 2}[sg[1]]
            if q == 0 and not (is_zero_level(sg[2]) and is_zero_level(sg[3])):
                fail("cannot project an erased field")
            u = usage_scale(2, u)
        return sg[4], u
    if c == "snd":
        ts, u = infer(ctx, t[1], erased)
        sg = expect_sigma(ts)
        if not erased:
            if sg[0] == "sigmaQ":
                # the second component at a stuck quantity is projectable only in an
                # erased position (Kernel.wiz; projections otherwise need ω)
                fail("cannot project a field whose quantity is a variable")
            u = usage_scale(2, u)
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
        tt, _ = infer(ctx, t[2], erased)
        tt = whnf(tt)
        if tt[0] not in ("empty", "pfalse"):
            fail(f"exfalso needs a proof of Empty, got {tt}")
        return t[1], z
    if c == "letUnit":
        uu = check_unit(ctx, t[1], erased)
        tb, ub = infer(ctx, t[2], erased)
        return tb, usage_add(uu, ub)
    if c == "enum":
        return mk_sort(1), z
    if c == "tag":
        if t[2] >= t[1]:
            fail("tag out of range")
        return ("enum", t[1]), z
    if c == "ecase":
        ts, us = infer(ctx, t[2], erased)
        ts = whnf(ts)
        if ts[0] != "enum":
            fail(f"ecase on a non-enumeration: {ts}")
        k = ts[1]
        if len(t[3]) != k:
            fail(f"ecase has {len(t[3])} branches for {k} tags")
        check_type(bind(ctx, 0, ts), t[1])
        ub = usage_zero(len(ctx))
        for j, b in enumerate(t[3]):
            uj = check(ctx, b, subst_top(t[1], ("tag", k, j)), erased)
            ub = usage_join(ub, uj)
        return subst_top(t[1], t[2]), usage_add(us, ub)
    if c == "eq":
        s = check_type(ctx, t[1])
        if not never_zero(s):
            fail(f"eq is formed at a sort that may be 0: {s}")
        check(ctx, t[2], t[1], erased)
        check(ctx, t[3], t[1], erased)
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
        check(ctx, t[2], t[1], erased)
        return ("eq", t[1], t[2], t[2]), z
    if c == "tyRefl":
        check_type(ctx, t[1])
        return ("eqTy", t[1], t[1]), z
    if c == "coe":
        s1 = check_type(ctx, t[1])
        s2 = check_type(ctx, t[2])
        if not level_eq(s1, s2):
            fail(f"cast between types at different levels: {s1}, {s2}")
        check(ctx, t[3], ("eqTy", t[1], t[2]), erased)
        u = check(ctx, t[4], t[1], erased)
        return t[2], u
    if c == "subst":
        A, a, P, p, b, e = t[1], t[2], t[3], t[4], t[5], t[6]
        s = check_type(ctx, A)
        if not never_zero(s):
            fail(f"transp at a sort that may be 0: {s}")
        check(ctx, a, A, erased)
        check(ctx, P, expected_transp_type(ctx, A, a, s), erased)
        pty = ("app", ("app", P, a), ("eqRefl", A, a))
        check(ctx, p, pty, erased)
        check(ctx, b, A, erased)
        ety = ("eq", A, a, b)
        check(ctx, e, ety, erased)
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
        check(ctx, D, ("descr", l, I), erased)
        check(ctx, i, I, erased)
        return mk_sort(l + 1), z
    if c == "con":
        fail("cannot infer the type of a constructor (check only)")
    if c == "size":
        return mk_sort(1), z
    if c == "szInf":
        return ("size",), z
    if c == "szSuc":
        check(ctx, t[1], ("size",), erased)
        return ("size",), z
    if c == "sizeLt":
        check(ctx, t[1], ("size",), erased)
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
        tt, u = infer(ctx, t[1], erased)
        tt = whnf(tt)
        if tt[0] != "ulift":
            fail(f"down on a non-ULift: {tt}")
        return tt[3], u
    if c == "prf":
        tt, u = infer(ctx, t[2], erased)
        st = sort_level(tt)
        if st is None or not level_eq(st, t[1]):
            fail(f"proof marker at {t[1]} on a term of sort {st}")
        return tt, u
    if c == "const":
        _, name, ps, ls, v, ty = t
        check_type(ctx, ty)
        check(ctx, v, ty, True)
        return inst_levels(ty, ps, ls), z
    if c == "axiomC":
        check_type(ctx, t[2])
        return t[2], z
    if c == "delim":
        return infer_delim(ctx, t, erased)
    if c == "ind":
        return infer_ind(ctx, t, erased)
    if c == "split":
        return infer_split(ctx, t, erased)
    if c in ("sfix", "scase", "scofix", "coit", "out", "cocon"):
        fail(f"out of scope: {c}")
    fail(f"cannot infer {t}")


# ---------------------------------------------------------------------------------
# descriptions' eliminator and induction (the rules of selfhost/Kernel.wiz)

def sort_term(v):
    return PROP if v == 0 else U(v - 1)


def unit_term(v):
    return PTRUE if v == 0 else UNIT(v - 1)


def imax_n(a, b):
    return imax_level(N(a), N(b))


def tm_subst_vars(t, env):
    """Substitute `env[0], env[1], ...` for variables 0, 1, ... (an evaluator for the
    closed method-type templates, which mention only their arguments)."""
    for i in range(len(env) - 1, -1, -1):
        t = subst(t, i, env[i])
    return t


def delim_motive_ty(l, v, I):
    """`P : Desc.{l} I -> Sort v`"""
    return ("pi", "w", N(l + 2), N(v + 1), ("descr", l, I), sort_term(v))


def delim_mret(l, v, I, P):
    # (i : I) -> P (ret i)
    tmpl = ("pi", "w", N(l + 1), N(v), V(1), ("app", V(1), ("dret", V(0))))
    return tm_subst_vars(tmpl, [P, I])


def delim_marg(l, v, I, P):
    # (q : Qty) -> (S : Sort (l+1)) -> (E : S -> Desc I) ->
    # (ih : (s : S) -> P (E s)) -> P (arg q S E)
    l1 = l + 1
    ety = ("pi", "w", N(l1), N(l1 + 1), V(0), ("descr", l, V(4)))
    # ih type, in the context q, S, E
    ihty = ("pi", "w", N(l1), N(v), V(1), ("app", V(4), ("app", V(1), V(0))))
    # result type, in q, S, E, ih
    res = ("app", V(4), ("darg", V(3), V(2), V(1)))
    t3 = ("pi", "w", imax_n(l1, v), N(v), ihty, res)
    t2 = ("pi", "w", imax_level(N(l1 + 1), imax_n(l1, v)), imax_n(l1, v), ety, t3)
    t1 = ("pi", "w", N(l1 + 1), N(l1 + 1), ("univ", l), t2)
    tmpl = ("pi", "w", N(1), N(l1 + 1), ("qty",), t1)
    return tm_subst_vars(tmpl, [P, I])


def delim_mrec(l, v, I, P):
    # (q : Qty) -> (j : I) -> (E : Desc I) -> (ih : P E) -> P (rec q j E)
    l1 = l + 1
    t4 = ("pi", "w", N(v), N(v),
          ("app", V(3), V(0)), ("app", V(4), ("drec", V(3), V(2), V(1))))
    t3 = ("pi", "w", N(l1 + 1), N(l1 + 1), ("descr", l, V(3)), t4)
    t2 = ("pi", "w", N(l1), N(l1 + 1), V(2), t3)
    tmpl = ("pi", "w", N(1), N(l1 + 1), ("qty",), t2)
    return tm_subst_vars(tmpl, [P, I])


def delim_mhrec(l, v, I, P):
    # (q : Qty) -> (H : Sort (l+1)) -> (j : H -> I) -> (E : Desc I) ->
    # (ih : P E) -> P (hrec q H j E)
    l1 = l + 1
    t5 = ("pi", "w", N(v), N(v),
          ("app", V(4), V(0)), ("app", V(5), ("dhrec", V(4), V(3), V(2), V(1))))
    t4 = ("pi", "w", N(l1 + 1), N(l1 + 1), ("descr", l, V(4)), t5)
    jty = ("pi", "w", N(l1), N(l1), V(0), V(4))
    t3 = ("pi", "w", N(l1), N(l1 + 1), jty, t4)
    t2 = ("pi", "w", N(l1 + 1), N(l1 + 1), ("univ", l), t3)
    tmpl = ("pi", "w", N(1), N(l1 + 1), ("qty",), t2)
    return tm_subst_vars(tmpl, [P, I])


def all_type(l, v, I, D, X, P, i, xs):
    """`All D X P i xs` (the template of CoreSpec §9.2), as a type term."""
    D = whnf(D)
    aL = max(l + 1, v)
    c = D[0]
    if c == "dret":
        return unit_term(aL)
    if c == "darg":
        q, S, E = D[1], D[2], D[3]
        return ("all", l, v, I, ("app", E, ("fst", xs)), X, P, i, ("snd", xs))
    if c == "drec":
        q, j, E = D[1], D[2], D[3]
        head = ("app", ("app", P, j), ("fst", xs))
        tail = ("all", l, v, I, E, X, P, i, ("snd", xs))
        return ("sigma", "w", N(v), N(aL), head, shift(tail, 1))
    if c == "dhrec":
        q, H, j, E = D[1], D[2], D[3], D[4]
        field = ("pi", "w", N(l + 1), N(v), H,
                 ("app", ("app", shift(P, 1), ("app", shift(j, 1), V(0))),
                  ("app", ("fst", shift(xs, 1)), V(0))))
        tail = ("all", l, v, I, E, X, P, i, ("snd", xs))
        return ("sigma", "w", imax_n(l + 1, v), N(aL), field, shift(tail, 1))
    return ("all", l, v, I, D, X, P, i, xs)


def ind_motive_ty(l, v, I, D):
    # (ω _ : μ D i) -> Sort v, under the index binder (written as a Π of sorts)
    return ("pi", "w", N(l + 1), N(l + 1), I,
            ("pi", "w", N(l + 1), N(v + 1),
             ("mu", l, shift(I, 1), shift(D, 1), V(0)), sort_term(v)))


def ind_method_ty(l, v, I, D, P):
    l1 = l + 1
    aL = max(l1, v)
    X = ("lam", ("mu", l, shift(I, 1), shift(D, 1), V(0)))
    payload = interp(l, shift(I, 1), shift(D, 1), shift(X, 1), V(0))
    all_ty = all_type(l, v, shift(I, 2), shift(D, 2), shift(X, 2), shift(P, 2),
                      V(1), V(0))
    result = ("app", ("app", shift(P, 3), V(2)), ("con", V(1)))
    return ("pi", "0", N(l1), N(l1), I,
            ("pi", "w", N(l1), N(aL), payload,
             ("pi", "w", N(aL), N(v), all_ty, result)))


def infer_delim(ctx, t, erased):
    _, v, P, a, b, d, e, D = t
    dty, uD = infer(ctx, D, erased)
    dty = whnf(dty)
    if dty[0] != "descr":
        fail(f"delim on a non-description: {dty}")
    l, I = dty[1], dty[2]
    check(ctx, P, delim_motive_ty(l, v, I), erased)
    ua = check(ctx, a, delim_mret(l, v, I, P), erased)
    ub = check(ctx, b, delim_marg(l, v, I, P), erased)
    ud = check(ctx, d, delim_mrec(l, v, I, P), erased)
    ue = check(ctx, e, delim_mhrec(l, v, I, P), erased)
    u = usage_add(usage_add(ua, usage_add(ub, usage_add(ud, ue))), uD)
    return ("app", P, D), usage_scale(2, u)


def infer_ind(ctx, t, erased):
    _, l, I, D, v, P, m, i, x = t
    sI = check_type(ctx, I)
    if not level_eq(sI, N(l + 1)):
        fail(f"an index type must be in Sort {l+1}, not Sort {sI}")
    check(ctx, D, ("descr", l, I), erased)
    check(ctx, P, ind_motive_ty(l, v, I, D), erased)
    um = check(ctx, m, ind_method_ty(l, v, I, D, P), erased)
    check(ctx, i, I, erased)
    ux = check(ctx, x, ("mu", l, I, D, i), erased)
    return ("app", ("app", P, i), x), usage_scale(2, usage_add(um, ux))


def infer_split(ctx, t, erased):
    _, q, scrut, motive, body = t
    rho = {"0": 0, "1": 1, "w": 2}[q]
    ts, u1 = infer(ctx, scrut, erased or rho == 0)
    sg = expect_sigma(ts)
    p = qty_value(sg[1]) if sg[0] == "sigmaQ" else {"0": 0, "1": 1, "w": 2}[sg[1]]
    check_type(bind(ctx, 0, ts), motive)
    # `M[(x, y)/z]`: one binder (`z`) is replaced by two (`x`, `y`)
    expected = subst_add0(motive, ("pair", V(1), V(0)), 1)
    xctx = bind(ctx, qmul(rho, p), sg[4])
    xyctx = bind(xctx, rho, sg[5])
    u = check(xyctx, body, expected, erased or rho == 0)
    if not qle(u[0], rho):
        fail(f"quantity violation: split's y is used {u[0]!r} times at {rho!r}")
    if not qle(u[1], qmul(rho, p)):
        fail(f"quantity violation: split's x is used {u[1]!r} times at {qmul(rho, p)!r}")
    return subst_top(motive, scrut), usage_add(usage_scale(rho, u1), u[2:])


# ---------------------------------------------------------------------------------
# the descriptions' payload (the `⟦D⟧` template, as in selfhost/Kernel.wiz)

def interp(l, I, D, X, i):
    D = whnf(D)
    c = D[0]
    if c == "dret":
        return ("sigma", "0", N(0), N(l + 1), ("eq", I, D[1], i), ("unit", l))
    if c == "darg":
        q, S, E = D[1], D[2], D[3]
        # the rest is *dependent*: keep `⟦E s⟧` lazy in `s`, so that checking the
        # pair's second component substitutes the tag first and then computes it
        rest = ("interp", l, shift(I, 1), ("app", shift(E, 1), V(0)),
                shift(X, 1), shift(i, 1))
        return ("sigmaQ", q, N(l + 1), N(l + 1), S, rest)
    if c == "drec":
        q, j, E = D[1], D[2], D[3]
        rest = ("interp", l, shift(I, 1), shift(E, 1), shift(X, 1), shift(i, 1))
        return ("sigmaQ", q, N(l + 1), N(l + 1), ("app", X, j), rest)
    if c == "dhrec":
        q, H, j, E = D[1], D[2], D[3], D[4]
        field = ("pi", "w", N(l + 1), N(l + 1), H,
                 ("app", shift(X, 1), ("app", shift(j, 1), V(0))))
        rest = ("interp", l, shift(I, 1), shift(E, 1), shift(X, 1), shift(i, 1))
        return ("sigmaQ", q, N(l + 1), N(l + 1), field, rest)
    # a stuck description: stay stuck (the pair checker will substitute the field first)
    return ("interp", l, I, D, X, i)


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
    if h == "split": return ("split", parse_qty(a[0]), parse_term(a[1]),
                             parse_term(a[2]), parse_term(a[3]))
    if h == "mu": return ("mu", int(a[0]), parse_term(a[1]), parse_term(a[2]),
                          parse_term(a[3]))
    if h == "con": return ("con", parse_term(a[0]))
    if h == "ind":
        return ("ind", int(a[0]), parse_term(a[1]), parse_term(a[2]), int(a[3]),
                parse_term(a[4]), parse_term(a[5]), parse_term(a[6]),
                parse_term(a[7]))
    if h == "suc": return ("szSuc", parse_term(a[0]))
    if h == "lt": return ("sizeLt", parse_term(a[0]))
    if h == "mus": return ("mus", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "nu": return ("nu", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "out": return ("out", parse_term(a[0]))
    if h == "cocon": return ("cocon", parse_term(a[0]))
    if h == "scofix": return ("scofix", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "coit": return ("coit", int(a[0])) + tuple(parse_term(y) for y in a[1:])
    if h == "const":
        ps = tuple(a[1][1:]) if isinstance(a[1], list) and a[1] else ()
        ls = tuple(parse_lvl(y) for y in (a[2][1:] if isinstance(a[2], list) and a[2] else ()))
        return ("const", a[0], ps, ls, parse_term(a[3]), parse_term(a[4]))
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
