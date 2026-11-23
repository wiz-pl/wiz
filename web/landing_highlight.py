#!/usr/bin/env python3
"""The landing page's build-time highlighter, and the four classes it may emit.

This is **not** a second Wiz lexer. It reproduces the part of
`Wiz.Doc.Highlight.lean` (the documentation's highlighter) that the landing page uses:
the parser's comment rules (`Token.commentEnd?`), its string rule (`Token.readStr`),
its number rule, and the reserved atoms that `classOfToken` maps to `hl-kw`. It emits
only the four classes `wiz doc` emits — `hl-kw`, `hl-com`, `hl-str`, `hl-num` — and
leaves identifiers and operators plain, exactly as the docs do.

`web/landing/test.sh` is the check: it renders the same snippets through `wiz doc` and
requires byte-identical HTML, and it probes every key in `KEYWORDS` to require that the
parser's own token table highlights it. A keyword this file invents, or one it misses,
therefore fails a test rather than reaching the page.

The reserved set below was read out of `Wiz/Parser/Builtin.lean`'s token atoms and
verified with the docs highlighter on 2026-11-23. Add a word only when the probe test
accepts it.
"""

import re

# `Wiz.Builtin.tables`' alphabetic atoms (the ones `classOfToken` colours: a first
# character that is ASCII alpha or `_`/`#`/`@`), plus `import` (reserved by the header)
# and the hole `_`. Verified by the keyword probe in web/landing/test.sh.
KEYWORDS = frozenset("""
Prop Sort Type _ absurd app_unexpander attribute axiom builtin by c_struct cast class
coinductive declare_syntax_cat def deriving end export extern forall foreign_type fun
glue import import_c include_str inductive infix infixl infixr instance let link_c
link_lib macro_rules match mutual native_refl notation partial private
register_attribute register_option rfl sealed set_option structure syntax transp where
with
""".split())

# `Token.isIdStart`: ASCII letters, `_`, α–ω except λ, Α–Ω except Π/Σ.
def _id_start(c):
    return ("A" <= c <= "Z") or ("a" <= c <= "z") or c == "_" or \
        ("α" <= c <= "ω" and c != "λ") or ("Α" <= c <= "Ω" and c != "Π" and c != "Σ")


# `Token.isIdRest`: an identifier start, a digit, `'`, `!`, or a subscript digit.
def _id_rest(c):
    return (_id_start(c) or ("0" <= c <= "9") or c in "'!"
            or ("₀" <= c <= "₉"))


def esc(text):
    """The docs' `Wiz.Doc.htmlEscape`, in the same order."""
    return (text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace('"', "&quot;").replace("'", "&#39;"))


def _line_end(src, i):
    """`Token.lineEnd`: the offset *after* the newline (the docs include it)."""
    j = src.find("\n", i)
    return len(src) if j < 0 else j + 1


def _block_end(src, i):
    """`Token.blockEnd` from the body start, with the opening depth already counted."""
    depth = 1
    j = i
    while j < len(src):
        if src.startswith("-/", j):
            depth -= 1
            j += 2
            if depth == 0:
                return j
        elif src.startswith("/-", j):
            depth += 1
            j += 2
        else:
            j += 1
    return len(src)


def _string_end(src, i):
    """`Token.readStr`: the offset after the closing quote, or None (a lexical error).

    The docs' scanner stops at an error, leaving the rest of the block plain.
    """
    j = i + 1
    while j < len(src):
        c = src[j]
        if c == '"':
            return j + 1
        if c == "\\":
            if j + 1 >= len(src):
                return None
            e = src[j + 1]
            if e in "ntr0\\\"'":
                j += 2
            elif e == "x" and re.fullmatch(r"[0-9A-Fa-f]{2}", src[j + 2:j + 4] or ""):
                j += 4
            elif e == "u" and src[j + 2:j + 3] == "{" and \
                    re.fullmatch(r"[0-9A-Fa-f]{1,6}\}", src[j + 3:j + 10] or ""):
                close = src.find("}", j + 3)
                j = close + 1
            else:
                return None
        else:
            j += 1
    return None


def _number_end(src, i):
    """`Token.readToken`'s number branch: `0x`/`0b` prefixed, else decimal digits."""
    if src[i] == "0" and i + 1 < len(src) and src[i + 1] in "xXbB":
        digits = "0123456789abcdefABCDEF" if src[i + 1] in "xX" else "01"
        j = i + 2
        while j < len(src) and src[j] in digits:
            j += 1
        if j > i + 2:
            return j
    j = i
    while j < len(src) and "0" <= src[j] <= "9":
        j += 1
    return j


def _ident_end(src, i):
    """`Token.readIdent`: id chars, and a dot only when an id start follows it."""
    j = i
    while j < len(src):
        c = src[j]
        if _id_rest(c):
            j += 1
        elif c == "." and j + 1 < len(src) and _id_start(src[j + 1]):
            j += 1
        else:
            break
    return j


def spans(src):
    """The `(start, stop, class)` spans of `src`, in order (the docs' `scan`)."""
    out = []
    i = 0
    while i < len(src):
        if src.startswith("--", i):
            j = _line_end(src, i + 2)
            out.append((i, j, "hl-com"))
        elif src.startswith("/-", i):
            j = _block_end(src, i + 2)
            out.append((i, j, "hl-com"))
        elif src[i] == '"':
            j = _string_end(src, i)
            if j is None:
                break
            out.append((i, j, "hl-str"))
        elif src[i].isdigit():
            out.append((i, _number_end(src, i), "hl-num"))
            j = out[-1][1]
        elif _id_start(src[i]):
            j = _ident_end(src, i)
            if src[i:j] in KEYWORDS:
                out.append((i, j, "hl-kw"))
        else:
            i += 1
            continue
        i = j
    return out


def highlight(src):
    """The escaped source with the docs' span wrappers; no other class appears."""
    out = []
    pos = 0
    for start, stop, cls in spans(src):
        if stop <= pos:
            continue
        out.append(esc(src[pos:start]))
        out.append('<span class="' + cls + '">' + esc(src[start:stop]) + "</span>")
        pos = stop
    out.append(esc(src[pos:]))
    return "".join(out)
