# Termination: structural recursion, `partial`, and sizes

What Wiz checks, where it gives up, and how the check interacts with the size index of
`μ`. The short version: a non-partial definition must recurse on a field of a value it
matched, compiled code's derived equations are checked for the same property by the
kernel, and `partial` (and therefore every `mutual` block) is the explicit boundary at
which the kernel stops talking about termination.

## The elaborator: structural recursion on one argument

A definition by equations (`def f : T → U | …`) is compiled to the type's recursor
(`ind`, `T.rec`) and its compiled equations (`Decl.impl`, `deriveImpl`) replace each
induction hypothesis by the direct call it stands for. The elaborator (`compileMatch`,
`rewriteRecCalls` in `Wiz/Elab/Term.lean`) accepts a recursive call only when

* its structural argument is a variable bound by the pattern that split the structural
  argument (a field of the matched constructor), or a field of an infinitary field applied
  to arguments (`k e` for `k : (h : H) → T`), and
* its parameters (the binders before the colon) are passed unchanged, and
* the recursive call sits in the branch of the constructor that owns that field.

The structural column is the first constructor pattern of the first clause (`pos`); the
other matched columns follow it. An as-pattern `x@p` binds `x` to the matched value
itself, so recursion on `x` is recursion on that column.

The accepted shapes are: a field (`| .succ n => f n`), a field of an infinitary field
(`| .sup k => f (k z)`), a later matched column when the first one is a parameter
(`def f (w : Nat) : List Nat → … | .cons x xs => f w xs`), and nested splits on fields as
long as the recursion is on a field that has a hypothesis of its own.

The rejected shapes each get a specific message (the reason and what to do instead):

| shape | message |
|---|---|
| a computed argument (`f (s n)`, `f (g n)`, `f (n + 1)`) | "must be on a variable, not …": nested recursion |
| the scrutinee itself (`match n with … => f n`) | "the scrutinee itself, which is not smaller" |
| a changed parameter (`f n m` where `m` is a parameter) | "must pass the parameter m unchanged": recursion on another argument |
| a field of an enclosing match, a field of a nested pattern, or `p + 2` | "not structurally smaller": no hypothesis of its own |

Wiz has **no lexicographic measure and no nested-recursion measure**: the last two rows
are refused rather than guessed at, and the message says so. The escape hatch is
`partial def`, which is also what a `mutual` block elaborates to (below). A definition
that is structurally recursive but at a *sized* argument goes through `sfix` instead
(see the last section).

## The kernel: every derived call is on a field

For a definition whose implementation is derived from its checked value
(`Decl.derivedEquations`), `addDecl` also runs `checkImplAgrees`
(`Wiz/Core/Check.lean`). Besides checking that the compiled equations compute the value
(one conversion per constructor, by induction on the scrutinee), it runs
`checkCallsOnFields`: the implementation must be the definition's own split
(`T.casesOn` on the same column), and every call of the definition inside a method must
pass, at the structural position, a field of that method's constructor.

That check is syntactic and deliberately small: it is the kernel's own guarantee that
compiled code terminates as the kernel's recursion does, independent of the elaborator's
good behaviour. A call on a computed argument, a call on the scrutinee, or a call on a
field of a *different* column (which a lexicographic measure might justify) is rejected
with the method and the argument named, because the kernel cannot see the measure either.
The accepted set is the same as before this diagnostic change; only the message is more
precise. Hand-made implementations that agree with the value but loop (the "M1" probes,
`Tests/Groups/Trust.lean`) are rejected by this check, not by the conversion.

The check runs before the implementation is compared with the value, so an implementation
that is not the definition's split at all (`λ n. f n`) says "a call of f is not under a
match on the argument it recurses on" rather than "not an induction on an argument".

## The boundary: `partial` and `mutual`

A `partial def f : T := body` declares `f` as an **opaque** constant and checks a
**witness** `w : T` (written with `partial (default := w)`, or found by the elaborator).
The witness is what keeps the kernel sound: `f` proves nothing that `w` does not, even if
`body` loops. The body is checked at `T` (`addPartialImpl`) and kept as `Decl.impl` for
compiled code; the kernel never unfolds it and never compares it with a value, because
there is no value.

`mutual … end` is elaborated as a block of partial definitions: each member's signature is
declared (opaque, with a witness) before any body is checked, so the members can call each
other. Consequences, all intentional:

* a member needs an inhabited type even if its recursion is structural — the error says
  that a `mutual` member is opaque to the kernel, not just "no witness";
* a member's recursion need not decrease; `mutual` is `partial` for the whole group;
* a member is not transparent in proofs, so `#reduce`/conversion does not unfold it (the
  witness is what `#print axioms` sees, not the body).

A non-structural `partial` or `mutual` body can loop when compiled. That is the boundary,
not a bug: the kernel's guarantees are about the checked value, and a partial definition
has none.

## Sizes and `μ`

Structural recursion and sized recursion are two different termination disciplines, and
the checks do not overlap:

* **Structural.** A `μ^s I D i` value's recursive fields are `Desc.rec` positions in `D`
  — fields of the constructor. A call on such a field is on a strictly smaller *value*
  regardless of the size index, so `checkCallsOnFields` is size-blind and does not need to
  look at `s`. The description's **guardedness** (every `Desc.rec` under an `Desc.arg`) is
  what makes "field of the constructor" a smaller value; it is checked by the `μ` type
  former, and it is the size-level counterpart of the structural check.
* **Sized.** `def f {i : Size} : T^i → …` is compiled to `sfix`, not to a `casesOn`
  implementation: `elabDefEqns` returns no `Decl.impl` for it, so neither `checkImpl` nor
  `checkCallsOnFields` sees it. Its termination is the *type*: inside the definition `f`
  is a local `{j : Size< s} → T^j → P j`, so a recursive call only type-checks at a
  strictly smaller size, and matching a constructor gives its fields sizes below the
  scrutinee's. Course-of-values recursion (`fib`) works because the sizes are kept.
* **Interaction and its limit.** The size argument of `μ`/`ν` is **trusted by both
  kernels** (the frontend forms it; the kernel checks that it is a `Size` but not that it
  bounds the value — the `selfhost-parity` B5 gap). A forged `μ` at a size that does not
  bound its fields would let `sfix`'s type accept a call the sizes do not justify, so the
  sized discipline is only as strong as size formation. The structural discipline does not
  depend on that: it only uses the description's fields, and constructing a `μ` at a
  neutral size is not possible (`con` needs `↑s` or `∞`), so a compiled call on a field is
  on a smaller value even when the size index is the same.

Neither check applies to a **partial/mutual** body or to an `implemented_by` constant:
the first is opaque by construction, the second is trusted and listed by `#print axioms`.

## Tests

* `Tests/Groups/Inductive.lean` (group `inductive`): the accepted shapes (field,
  parameter, later column, infinitary field), and the rejected ones with the exact
  reason (computed argument, scrutinee, changed parameter, nested pattern), plus the
  kernel's rejection of a looping hand-made implementation.
* `Tests/Groups/Language.lean` (group `language`): `mutual` needs a witness and is not
  made transparent by structural recursion; `mutual`/`partial` may recurse without
  decreasing; nested/lexicographic calls are rejected with the "no measure" hint.
* `Tests/Groups/Trust.lean` (group `trust`): the M1 probes (calls on rebuilt scrutinees,
  on a constructor field of a different argument, at `Unit`) and the new messages naming
  the method and the argument.
* `Tests/Check.lean` (group `check: termination`): the kernel's partial boundary
  (`addPartialDecl` needs a witness, only a partial declaration takes an implementation).
