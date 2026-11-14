# Stage 19: the frontend checks the self-hosted sources

## 19a: a Prelude, `if`, strings

`import Prelude` checks a small Prelude (written in the subset itself, kept as a string
in `Frontend.wiz`) before the file: `Nat`, `Bool`, `List`, `Option`, `Prod`, `Char`
(a structure over its code) and `String` (a structure over a `List Char`), with
arithmetic, comparisons, the Boolean connectives and a few list functions. `if c then a
else b` is a `match c` with `.true`/`.false` clauses; a string literal is `String.mk`
of a list of `Char.mk` numerals. A definition whose `match` scrutinises something other
than its parameters (`match s.data with …`) is compiled as a `match` term.

Only the structural split of a match needs induction; the other splits are now case
analysis (the kernel's `scase` at `∞`, whose method sees the payload at `μ^j D i` for a
size `j`). Computing induction hypotheses nobody uses made nested matches exponential:
`Nat.beq 14 14` took 0.7 s, `Nat.beq 65 65` now takes 0.17 s.

## 19b: infix operators

`infixl:65 " + " => Nat.add` (and `infixr`, `infix`) extends the self-hosted parser
while it runs: a trailing `term` parser `a + b` at the declared precedence, and the
token `+`. Each later command is expanded before it is elaborated, `a + b` standing for
`Nat.add a b`, like the Lean side's macro rule. The Prelude declares `+ - *` and `++`;
in a pattern, `n + 2` is `.succ (.succ n)`. **Exercise 19.1** is `infixCmd`, the new
parser entry and notation.

## 19c: axioms, `IO`, `do` — the frontend checks `Lex.wiz`

`axiom f (bs) : T` and `extern "c_name" f : T` (a foreign function is an axiom to the
checker) declare constants. `Unit` and `()` are built in. The Prelude declares `Array`
and its operations as axioms, and `IO A := World → Prod A World` with `IO.pure`,
`IO.bind` and the axioms `IO.println`, `IO.readFile`. `import Prelude` also adds the
`do` grammar to the parser's tables (there are no type classes, so `do` is for `IO`
only): `x ← e; rest`, `e; rest` and `let x := v; rest` expand to `IO.bind`. A `let`
may now leave out its type (the value's inferred type is used).

With these, the self-hosted frontend checks the first file of its own source,
`selfhost/Lex.wiz` (every declaration, no errors; about 18 s).

## 19d: `Syntax`, `StrMap` — the frontend checks `Parse.wiz`

The Prelude adds the syntax trees (`SyntaxF : Bool → Type` and `Syntax := SyntaxF
.true`, with `getArg`), `Nat.toString`, and `Str`/`StrMap` as axioms. Three gaps
closed on the way:

* a type that is a definition (`Syntax`) is unfolded where an inductive type is
  needed: for `.c` (`dotName`), for a match (`unfoldTy`), and in unification, which
  unfolds one definition at a time before comparing whole values (`SyntaxF ?b =?=
  Syntax` solves `?b := .true`);
* in an indexed family, the index `.c` of a constructor's result type is `I.c` (the
  constructors are scope-checked, not typed);
* a metavariable's solution may contain projections and pairs (`lowerTm`): the fields
  of a pattern are projections of its payload, so `.some (.mk n l)` inside a branch
  needs them.

The self-hosted frontend now checks `Lex.wiz` and `Parse.wiz` together (96
declarations, about 20 s).

## 19e: towards `Kernel.wiz`

* A field `(v : Unit → Val)` of a mutual type is higher-order recursive: `dhrec H (fun _
  => tag j) D` in the description.
* Induction only where it is needed: a definition's match uses `ind` only when the
  definition calls itself and isn't partial (a partial definition calls its axiom);
  every other split is case analysis. This also avoids building hypotheses for
  function fields.
* A catch-all at the structural split of a mutual member (a closed index, [18b](18-selfhost-more-data.md)) used to
  bind the variable to `con (tag, rest)` at the method's index; it is now moved to the
  scrutinee's index with `coe` along `F i = F idx` (obtained by `subst` from `tyRefl`),
  so `| t => t` has the right type.
* `Unit` in constructor fields, `fun _ => …`, and `Nat.max` in the Prelude.

## 19f: the frontend checks `Kernel.wiz`

* **Big numerals**: a numeral is `Nat.succ` applied `n` times, so `quote 100000 A` in
  the kernel was a term 100000 deep. With `Nat.mul` around, a numeral of 16 or more is
  built in binary (`2 * (n / 2)`, plus `succ` when odd).
* **Recursion through a function field**: `whnf (v ())` with `v : Unit → Val`. The
  hypothesis for such a field is a function, `(h : H) → P (j h) (v h)` (pre-applied to
  `refl` in mode B), and a recursive call on `v a` becomes `ih a`.
* **The structural parameter first**: when a recursive call changes a parameter before
  the structural one (`tApps (.app f a) rest`), `f` is defined through `f✝s`, with the
  structural parameter moved to the front, so the others are generalised in the motive.
* **A shared catch-all**: a big last clause of variables in a match that only does
  case analysis is checked once as a definition `f✝d`, and the leaves call it, instead
  of copying it into every leaf.
* `memo` in the Prelude.

The self-hosted frontend now checks `Lex.wiz`, `Parse.wiz` and `Kernel.wiz` (272
declarations, about two minutes). Next: `Frontend.wiz` itself.
