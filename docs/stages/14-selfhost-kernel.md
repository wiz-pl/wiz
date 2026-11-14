# Stage 14: the kernel in Wiz

## 14a: a type checker

`selfhost/Kernel.wiz`: normalisation by evaluation for a core calculus (variables,
universes, Π, λ, application, `let`, ascription), with values and environments mutually
inductive (closures), and bidirectional checking.

| #    | Where                 | What                                    |
|------|-----------------------|-----------------------------------------|
| 14.1 | `selfhost/Kernel.wiz` | `eval`, `vapp`                          |
| 14.2 | `selfhost/Kernel.wiz` | `quote`                                 |
| 14.3 | `selfhost/Kernel.wiz` | `infer`, `check`                        |

## 14b–c: from text to checked definitions

`selfhost/Frontend.wiz` scope-checks Wiz syntax (identifiers, `Type n`, Π and arrows,
`fun`, application, `let`, ascription) into the kernel's terms, and processes a file of
`def`, `#check` and `#reduce` commands, the globals being the kernel's constants (each
command is checked in the empty context). Lexer, parser, scope checker and type checker all run as compiled Wiz.

| #    | Where                   | What                                     |
|------|-------------------------|------------------------------------------|
| 14.4 | `selfhost/Frontend.wiz` | `elab`: names to de Bruijn indices       |
| 14.5 | `selfhost/Frontend.wiz` | `command`: one command                   |

## 14d: differential testing

Conversion in the Wiz kernel compares values, with η for functions, like `Conv.lean`.
A test generates 300 pseudo-random closed terms, checks each with both kernels (the
Lean kernel through the same terms, quantities `ω`), and requires the same verdict and
the same inferred type.

| #    | Where                 | What                                    |
|------|-----------------------|-----------------------------------------|
| 14.6 | `selfhost/Kernel.wiz` | `conv`: values, with η                  |

## 14e: Σ types

Pairs, projections and Σ types in the Wiz kernel, with η for pairs (`p` and `(p.1, p.2)`
are convertible); neutral values carry a spine of eliminations (`Val`, `Env` and
`Spine` are mutually inductive). The differential generator mixes in well-typed pairs,
so its 400 terms exercise them. Exercises 14.1–14.3 and 14.6 now include Σ.

## 14f: finite types

`Unit n`, `Empty n` (with `exfalso`), and enumerations of `k` tags with case analysis
(a motive under a binder; a stuck case is an elimination in the spine). Terms are now a
mutual inductive (`Tm` and its lists `Tms`). The generator adds them, often
well-typed (cases returning tags), and both kernels agree on all 400 terms.

## 14g: `Prop`, and conversion at a type

`Prop` (`Sort 0`) with impredicative Π (`imax`), `True` and `False`, and conversion
**at a type** like `Conv.lean`: all proofs of a proposition are equal, functions and
pairs are compared by η, types structurally, neutrals by their eliminations at their
types (computed from the variable's type, `typeOfNe`). Exercise 14.6 is now typed.
(Also fixed: the index-equation binder of a match could shadow a variable `e`.)

## 14h: observational equality

`a = b` and `A = B` compute by type, as in `Eval.lean` (with the same closure templates):
pointwise for functions, componentwise (with a cast of the second component) for pairs,
`True`/`False` for tags, logical equivalence for propositions. `cast` computes by the
two types, and `refl`, `reflTy`, `transp` are proofs. A neutral now has a **head**: a
variable, or a stuck equality, cast or proof. (In the Wiz source the constructors are
`eqRefl`, `tyRefl`, `coe` and `subst`: `refl`, `cast` and `transp` are keywords.) The
differential generator adds equalities and their proofs, often well-typed.

(Checking the Wiz kernel had become slow, 24 seconds. A profile showed the cause: the
inhabitedness check for partial definitions evaluated the type of every global, for
each definition. It now looks only at constants whose type visibly ends in the right
type: 3 seconds.)

## 14i: descriptions and data

Descriptions (`descr l I` for `Desc.{l} I`, with `ret`, `arg`, `rec`, `hrec`),
`Desc.elim`, `μ D i` and constructors, as in the Lean kernel: `⟦D⟧ X i` is the same
`interpTm` template, written with `Desc.elim`, and `con x = con y` is equality of the
payloads. This kernel has no quantities: where the templates take one, it passes `tt`
(and the method types bind it at `Unit`). The differential test now always checks a
list of samples first (the natural numbers, constructors, `Desc.elim` into `Unit`,
ill-typed payloads), then the random terms.

## 14j: induction

`ind` on `μ D i`, with the motive and method types of the Lean kernel and the `All`
and hypotheses templates (`allTm`, `hypsTm`, the same `Desc.elim` terms): on a
constructor, the method gets the payload and the induction hypotheses; on a variable
it is stuck. The samples check that it computes (`tt : ind … 1 = #1` checks, and
`= #0` doesn't) and agree with the Lean kernel.

The Wiz kernel now covers the Lean kernel's dependent types, equality and data, apart
from quantities, sizes, coinduction, globals and universe polymorphism.

## 14k: global constants

A global definition is a term `const name value type` that carries its (closed) value
and type, shared rather than looked up in a table; an axiom is `axiomC name type`.
Definitions are **glued** as in the Lean kernel: a constant applied to arguments keeps
its name and spine together with its unfolding, quotation keeps the name, conversion
compares two applications of the same constant by their arguments before unfolding
(lazy delta), and `whnf` looks through them before matching on a value's shape. The
differential test builds the same globals in the Lean kernel (with `addDecl`) and
uses them in samples and random terms.

## 14l: universe polymorphism

Levels in terms are expressions over level parameters (`Lvl`: numerals, parameters,
successor, `max`, `imax`), and `Sort l` takes any of them. A universe-polymorphic
constant carries its parameters and the levels it is used at; using it substitutes the
levels into its definition (`tmSubst`) before evaluating. Every term the kernel
evaluates is closed, so values only ever see numeric levels. (Checking a polymorphic
definition itself, with symbolic level equivalence, comes with checking declarations.)
The differential test adds polymorphic globals (`idP.{u}`, `constP.{u v}`) used at
various levels.

## 14m: quantities

Binders carry a quantity (`0`, `1`, `ω`: `piq`, `sigmaq`, `letq`; the plain forms are
`ω`), and every judgement returns a **usage vector**, as in `Check.lean`: a variable
counts once, an application adds its argument's usage scaled by the binder's
quantity, leaving a binder checks its variable's usage against the quantity, case
branches join, and types and proofs count nothing (erased positions, where an erased
field may also be projected). The kernel's own templates use the Lean kernel's
quantities (equations and indices are erased), and printing shows `:0` and `:1`.
The differential test adds linear and erased binders, in samples and at random.

## 14n: sizes and subtyping

`Size`, `∞`, `↑s`, `Size< s`, and `μ D i` at a size (`∞` by default); a constructor
builds a value of size `↑s` from fields at `s`. Checking falls back to **subtyping**
(`subTy`, exercise 14.7) as in the Lean kernel: data types are covariant in their size
(`sizeLe`, which uses a variable's `Size< u` bound), functions contravariant in their
domain (and may differ in quantity when they are propositions), pairs covariant.

## 14o: sized recursion

`sfix` (recursion whose function takes a smaller size `Size< s`) and `scase` (case
analysis giving the fields at the predecessor size), with the method types computed
from the description as in the Lean kernel (`sfixFunTy`, `scaseMethodTy`). Both reduce
on a constructor; the recursive function is used ω times. The differential test checks
that they compute, and that the index can't be returned (it is erased).

## 14p: coinduction

`ν^s D i`, `out`, `cocon`, coiteration (`coit`) and sized corecursion (`scofix`), as
in the Lean kernel: unfoldings compute only when observed (`out` re-wraps the recursive
fields with the `map` template), only a value of size `↑s` or `∞` can be observed, and
`ν` is contravariant in its size. Unfoldings are compared structurally (there is no
bisimulation). The differential test observes streams built both ways.

The parser got a per-offset token cache (each alternative used to re-lex, scanning the
whole token table) and no longer shares its memo table with candidate states (each
store copied the table): `Kernel.wiz` now checks in a third of the time.

Compiling the kernel (which the self-hosting tests do) had grown to 8 minutes. A
catch-all row of a multi-column `match` is copied into every leaf of the split, so
`checkW`'s now calls a helper (`checkByInfer`); and erasure no longer asks the kernel's
full `infer` for the type of each subterm (which re-checked every subterm once per
enclosing node) but follows the elimination spine (`Erase.quickType`). Now 37 seconds.

## 14q: declarations at symbolic levels

Values carry symbolic levels (`vsort (l : Lvl)`), compared as in `Level.lean`: normal
forms are sorted lists of `atom + k` (exercise 14.8, `lvlNorm`), and when an `imax`
keeps them apart, `lvlEquiv` splits on the parameter it depends on (`p = 0` or
`p = p + 1`). `checkDecl` checks a declaration with its parameters symbolic, so at
every level at once. A differential test checks declarations, and 200 random level
puzzles (`Sort a : Sort b`, Π's of sorts; the true ones made by rewriting with
identities), against the Lean kernel's `addDecl`. (The Lean kernel also rejects unknown
or duplicate level parameter names; this one doesn't look.)

The Wiz kernel now covers the Lean kernel's calculus.

The `match` compiler now shares a large catch-all last row of a multi-column match: it
is elaborated once, as a local function `dflt✝` of the scrutinees, and the row calls it
(falling back to copying when the right-hand side doesn't check without what the other
rows learnt).
