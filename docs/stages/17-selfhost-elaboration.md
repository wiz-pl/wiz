# Stage 17: elaboration in the self-hosted frontend

## 17a–b: implicit arguments

The self-hosted frontend now elaborates with types (`inferT`/`checkT` in
`Frontend.wiz`), so `{A : Type}` binders work: `List.cons x xs`, `id Nat.zero`,
`map f l`. A metavariable `?mN` is the kernel's opaque constant (`axiomC`) of type
`Π Γ. A`, applied to the variables of the context `Γ` it was made in, so the kernel needs
nothing new; unification (`unify`) solves `?mN Γ =?= t` when `t` lives in `Γ`
(`lowerTm`, with an occurs check), compares Π types and spines structurally, and leaves
the rest to the kernel's conversion. Before the kernel checks a definition, the
solutions are put in (`zonk`). A global records which of its parameters are implicit:
`{…}` binders, and an inductive type's parameters in its constructors.

The match compiler elaborates its right-hand sides with types too: it keeps the typing
context of its binders (the method's `i`, `xs`, `ih`, the payload, the fields, the
hypotheses, `cur✝`, the generalised parameters) alongside their names, and the expected
type as a value (at the structural split, the generalised motive's body, peeled as the
later parameters are bound again). Recursive calls leave out the implicit parameters.
Typed elaboration produces constants, so for `#reduce` the definitions are inlined
afterwards (`inlineTm`) instead of being compiled twice.

## 17c: `.c` and `@f`

A constructor can be written `.c` (or `.c a b`) where the expected type is `T …`: it is
`T.c`. An argument written so whose type is still an unsolved metavariable (the `.zero`
in `.cons .zero xs`, before `xs` fixes the list's type) is postponed: a metavariable
stands for it until the other arguments are elaborated, then it is checked and unified
with that metavariable. `@f` inserts no implicit arguments.

## 17d: `partial` and `mutual`

`partial def` and `mutual … end` blocks of definitions: each function is first an axiom
of its type (`addPartials`, justified by a witness the kernel checks, 22f), so that the
bodies may call any of them, as the Lean kernel sees partial definitions; then each body
is checked as usual and replaces the axiom.
