# Roadmap

The wishlist is a multi-year project, so the plan builds it as a sequence of stages.
Each stage ends in a working, tested system. This document covers the order, the
reasons for it, and the design questions you'll face at each stage. The design
questions are the actual decisions to make, not homework.

## Decisions so far

| Topic | Decision |
|---|---|
| Surface syntax | Lean-like: `def f (x : A) : B := ...`, `fun x => ...` |
| Quantities | Idris 2 prefix: `(1 x : A) → B`, `{0 A : Type}`. Omitted: ω explicit, 0 implicit |
| Data | μ/ν over a universe of indexed descriptions; kernel types are **anonymous**, with names kept as metadata for error messages |
| Structs | Σ / ⊤ with definitional η; variants and recursive types are μ |
| Recursion | Kernel has eliminators only; pattern matching compiles to them |
| Equality | Observational type theory now: proof-irrelevant `Prop`, `Eq` computed by type, `cast` |
| Universes | Lean-style level parameters, `Sort 0 = Prop` impredicative |
| Quantities | First-class: a `Qty` type, binder quantities are terms, usage polynomials decided over finite rigs |
| Matching / recursion / ν | Dependent (Cockx-style) pattern matching; structural (course-of-values) and well-founded recursion; copatterns compiled to `coit` |
| Tags / desc ops / ν equality | Finite enums (labels as metadata); ⟦D⟧, All, hyps and map from a `Desc` eliminator via kernel templates; equality on ν is stuck for now |

## Suggested order

```
 1 kernel ─▶ 2 parser ─▶ 3 elaborator ─▶ 4 data ─▶ 5 IR + interpreter ─▶ 6 macros/tactics
                                                         │
          ┌──────────────────────────────────────────────┘
          ▼
   7 typeclasses ─▶ 8 C backend + RC ─▶ 9 FFI ─▶ 10 effects ─▶ 11 build/queries/LSP ─▶ 12 self-host
                                                                                            │
                                                                       stretch: cubical ◀───┘
```

The reasons for this order:

* **Macros need an evaluator.** User-defined syntax and tactics are Wiz programs run at
  compile time, so an IR interpreter (stage 5) has to come before stage 6. Lean
  does the same thing.
* **Typeclasses need nominal heads**, so data (stage 4) comes first.
* **Effects lower to monads, and monads are typeclasses.**
* **Self-hosting needs everything else**: data, classes, IO through FFI, and a native
  backend fast enough to compile the compiler.

---

## Stage 1: Core kernel — scaffolded

NbE kernel with bidirectional QTT checking, parametric in the rig. See
[docs/stages/01-kernel.md](docs/stages/01-kernel.md) for the exercises.

**Design question: how general should "arbitrary rigs" be?** Right now the kernel is
parametric in `R` at the Lean level, so each program uses one fixed rig. There are three
levels of ambition:

1. **One rig per compilation.** This is the current design. It is easy, and enough to
   experiment with linear vs affine vs exact counting.
2. **One rig per module**, declared with something like `rig ZeroOneMany`, where
   cross-module calls need a rig morphism. This is useful but adds bookkeeping.
3. **Quantities as first-class terms with quantity polymorphism**, e.g.
   `map : ∀ (π : Q). (f :π A → B) → ...`. This brings usage *constraints* that must be
   solved, much like universe constraints. Several research systems explore it. Don't
   start here.

Reading:
- McBride, *I Got Plenty o' Nuttin'* (2016)
- Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018)
- Brady, *Idris 2: Quantitative Type Theory in Practice* (ECOOP 2021)
- Kovács, *elaboration-zoo*, the closest thing to a textbook for this style of kernel
- Abel & Bernardy, *A Unified View of Modalities in Type Systems* (ICFP 2020)
- Moon, Eades & Orchard, *Graded Modal Dependent Type Theory* (ESOP 2021)

## Stage 2: Surface syntax with an extensible parser — scaffolded

Copy Lean's architecture, because it is what makes Lean extensible:

* A single untyped **`Syntax`** tree (node kind + children + source info) is the
  interchange format between parser, macros and elaborator.
* **Syntax categories** (`term`, `command`, `tactic`, user-defined ones) each hold a
  table of *leading* and *trailing* parsers. This is Pratt parsing, with precedence
  on every parser.
* The **token table** is derived from the registered parsers, so new syntax can add
  tokens.
* Parser tables live in the **environment** as scoped extensions. Opening a namespace
  activates its syntax, and ordering is by declaration order, which keeps it
  deterministic.

**Decision:** represent user-declared parsers as **data** (Lean's `ParserDescr`),
interpreted by the parser, not as compiled code. That lets `syntax` declarations work
long before Wiz has a backend, and keeps them serialisable for caching.

Build in error recovery early (synchronise on command keywords), because the LSP needs
partial parses.

Reading: Ullrich & de Moura, *Beyond Notations: Hygienic Macro Expansion for Theorem
Proving Languages* (IJCAR 2020); the Lean 4 sources `Lean/Parser/*.lean`.

## Stage 3: Elaborator — scaffolded

`Syntax → core Term`, with:

* **Metavariables** and **pattern unification** (elaboration-zoo 03–05: holes,
  implicit arguments, first-class polymorphism).
* **Implicit binders default to quantity 0.** This is the main way QTT stays out of the
  way in practice.
* An `ElabM` monad (context, metavariable context, messages, a name generator) and an
  **elaborator table keyed by syntax kind**, so extensions can add elaborators (Lean's
  `@[term_elab]`).
* Postponement: if an elaboration problem is stuck on a metavariable, retry later.

**Determinism:** name metavariables and fresh variables with per-declaration counters,
never by pointer address or global counters shared across threads.

## Stage 4: Data as μ/ν, structural types, nominal wrappers (4a universes, 4b Σ/⊤/⊥, 4c OTT, 4d quantity polymorphism + descriptions, μ/ν, 4e inductive/structure)

This stage has the most open design space.

**Structural core.** Kernel type formers for *records* (dependent field telescopes,
with η), *variants* (tagged sums), and **μ / ν** fixed points over strictly positive
functors. For mutual types, take fixed points of *indexed* functors over a finite index
set, e.g. `μ (i : Fin 2). F i`.

Choices you'll face:

* **Positivity:** use a syntactic strict-positivity check on functors written with
  record and variant formers, or a universe of *descriptions* (`Desc`) where
  positivity holds by construction. Descriptions also give generic programming for
  free (deriving `Eq`, `Show` and friends as ordinary functions).
* **Eliminators vs pattern matching in the kernel.** Recommended: the kernel only has
  `fold`/`ind` for μ and `unfold`/coiteration for ν, so it stays obviously total.
  Surface pattern matching and recursion compile to these, or you add a
  termination checker later.
* **Coinduction:** define ν by observations, i.e. **copatterns** (Abel, Pientka,
  Thibodeau & Setzer, POPL 2013). Expect no definitional η for ν, and equality of
  streams has to go through bisimulation.
* **Quantities on fields:** each constructor field carries a quantity, as in Idris 2.
  The eliminator's usage rule follows from it.

**Nominal wrappers.** `def Nat := μ X. [zero : {} | succ : X]` gives a *name* to a
structural type. The name is where typeclass instances attach (stage 7). You need
**transparency levels**: the kernel may unfold `Nat` during conversion, but instance
resolution and unification treat it as an opaque head unless forced. Lean has the same
split (`@[reducible]`, `@[irreducible]`, instance transparency).

Reading: Dagand, *A Cosmology of Datatypes* (PhD thesis, 2013); Chapman, Dagand,
McBride & Morris, *The Gentle Art of Levitation* (ICFP 2010).

## Stage 5: Erasure, IR, interpreter

* **Erasure:** everything at quantity 0 disappears. This is QTT's main practical
  payoff: types, proofs and indices cost nothing at runtime.
* Lower to an ANF **λ_pure IR**, as in Lean's `Lean.IR`: first-order functions,
  explicit closures, constructors with tags and fields, `case`, `jmp` and join points.
* Write an **IR interpreter**. You need it for compile-time evaluation (macros,
  tactics, `#eval`) and as a reference semantics for the backends.

## Stage 6: Macros and tactics

* `macro`: `Syntax → MacroM Syntax`, with **hygiene through macro scopes** (Ullrich &
  de Moura 2020).
* `elab`: user code that runs inside `ElabM`.
* Tactics are `TacticM` programs over a list of goal metavariables. Start with
  `intro`, `exact`, `apply` and `refine`, then build the rest from those.
* **Bootstrap problem:** until self-hosting, extensions written *in Wiz* run in the IR
  interpreter, and built-in elaborators are written in Lean and registered
  natively. Keep both paths behind the same table interface.

## Stage 7: Typeclasses with tabled resolution

* Classes are ordinary records. An instance is a declaration tagged `@[instance]`,
  attached to the **nominal head** of the type it is for.
* Index instances with a **discrimination tree** over head symbols, at instance
  transparency.
* Resolution uses **SLG-style tabling** (Selsam, Ullrich & de Moura, *Tabled Typeclass
  Resolution*, 2020): it avoids exponential blow-up and loops on diamonds and cyclic
  instances (`A → B`, `B → A`).
* `outParam`s, default instances, priorities. **Determinism:** break ties by priority
  and then declaration order, never by hash order.

## Stage 8: C backend and reference counting

* Follow **Ullrich & de Moura, *Counting Immutable Beans*** (IFL 2019): explicit
  `inc`/`dec` insertion, **borrow inference**, and **reset/reuse** for in-place
  updates. Emit C first (Lean's `EmitC.lean` is a good model). Add LLVM later, either
  as textual `.ll` (simpler) or through LLVM-C bindings over FFI (what Lean does).
* Also read **Perceus** (Reinking, Xie, de Moura & Leijen, PLDI 2021).

**Linearity and RC.** A QTT `1` means *the callee consumes its argument exactly
once*. It does **not** mean the caller holds the only reference, because an `ω` value
can be passed to a `1` binder. So linearity alone cannot remove `dec`s or prove that
an update can happen in place. That property is **uniqueness**, the dual of linearity.
See Marshall, Vollmer & Orchard, *Linearity and Uniqueness: An Entente Cordiale*
(ESOP 2022). Options:

1. Use linearity for what it does guarantee. A linear parameter is *owned* and has
   exactly one consuming use, so no `inc` is needed before that use and no `dec` at
   scope exit. Borrow inference mostly finds this already. Linearity makes it a
   checked guarantee instead of a heuristic.
2. Add a **uniqueness** mode or rig element, so `reset/reuse` is statically
   guaranteed. See *FP²: Fully in-Place Functional Programming* (Lorenzen, Leijen &
   Swierstra, ICFP 2023) for a clean `fip` check that fits QTT well.

## Stage 9: C FFI

* `@[extern "sym"]` declarations with a defined ABI for boxed and unboxed scalars.
* **External objects:** opaque runtime objects with a registered class
  (`finalize`, `foreach`), like Lean's `lean_external_class`. Finalizers run when
  the RC drops to zero.
* **Header import:** parsing real headers means running the preprocessor first. The
  pragmatic route is `libclang` through the FFI, or `cc -E` followed by a declaration-only
  C parser. Only bind declarations (functions, structs, enums, typedefs) and skip
  bodies.
* **C glue subset:** a small C-like sublanguage with its own parser and type checker,
  printed straight into the emitted C file. Keep it first-order with no preprocessor.

## Stage 10: Effects

Algebraic effects with **row-typed effect sets** (Koka, Frank). Ways to lower them:

1. **Free/freer monads.** Simple, and fine as reference semantics. Slow.
2. **Evidence passing** (Xie & Leijen, *Generalized Evidence Passing for Effect
   Handlers*, ICFP 2021). This is what Koka compiles to and gives near-direct-style
   performance for tail-resumptive handlers.
3. **Monads with laws.** Each effect is interpreted into a lawful monad, and
   commutation is a *class*:
   `class Commutes (m n) : ∀ a b k, (do x ← a; y ← b; k x y) = (do y ← b; x ← a; k x y)`.
   Proved commutativity licenses reordering and parallel evaluation, and gives a
   real use for the dependent types.

**Tie-in with QTT:** a continuation resumed **at most once** is a `1`-quantity
continuation, which allows stack reuse instead of copying. Multi-shot handlers
take the continuation at `ω`. Quantities therefore describe the handler's
operational cost in its type.

## Stage 11: Deterministic builds, query engine, LSP

**Determinism comes first, because caching depends on it:**

* No pointer-based hashing or ordering. Never iterate a hash map into output (see
  `Globals.order`).
* Fresh names come from per-declaration counters. Serialised output is in canonical
  form.
* Parallel elaboration merges results in declaration order.
* CI check: build twice and diff the artifact hashes.

**Query engine:** compile as memoised queries per declaration (`parse`, `elab`,
`type`, `ir`, ...) using a red-green or early-cutoff algorithm. See Mokhov, Mitchell &
Peyton Jones, *Build Systems à la Carte* (ICFP 2018) and rust-analyzer's *salsa*.
Key each result by a **content hash** of its inputs: the declaration plus the hashes of
its dependencies (a Merkle DAG). Then a **shared cache server** is just a
content-addressed key-value store, like Bazel's remote cache.

**LSP:** while you're Lean-hosted, reuse `Lean.Data.Lsp` and `Lean.Data.JsonRpc`
instead of writing JSON-RPC yourself. Hover, go-to-definition and diagnostics are all
queries.

## Stage 12: Self-hosting (12a–d: stdlib, flat objects, lexer and parser in Wiz)

* Use Lean's **stage0** approach: commit the *generated C* of the compiler. Stage 1 is
  stage0's C compiling the current sources.
* Port the **kernel first**. It's the smallest piece, and you can **differentially
  test** it: run the Lean-hosted kernel and the Wiz-hosted kernel on the same corpus and
  compare results.
* Keep the Lean implementation as the reference until the Wiz one passes everything.

Stage 13 improved the language for this (mutual and partial definitions, mutual
inductive types, recursion on any argument, tuple patterns, inferred `match`), and
stage 14 (a, b, c) has a Wiz type checker for a core calculus, with a frontend from
text. Growing it to the full kernel, with differential tests, is next.

## Stretch: cubical type theory

I don't know of an established theory that combines cubical type theory with QTT,
let alone with arbitrary rigs. Questions such as what quantity an interval variable
has, and whether path abstraction can be linear, are research. Suggested stepping
stones:

1. **Observational type theory** (Pujet & Tabareau, *Observational Equality: Now for
   Good*, POPL 2022). It gives function extensionality, propositional extensionality
   and quotients with a much smaller kernel change, and fits an NbE kernel
   well.
2. Then a cubical mode (CCHM or cartesian) as a separate kernel flag, studying
   `cooltt` and Agda `--cubical`. Keep μ/ν structural so higher inductive types can
   be added as a new kind of description.

## Where the wishlist items pull against each other

| Tension | Resolution |
|---|---|
| Structural types vs instances attached to names | Nominal wrappers plus transparency levels (stage 4) |
| Linearity vs RC elision | Linearity ≠ uniqueness; add uniqueness for reuse (stage 8) |
| Macros in Wiz vs no backend yet | IR interpreter (stage 5) before macros (stage 6) |
| Parallel elaboration vs determinism | Per-declaration name supplies, ordered merge (stage 11) |
| Extensible parser vs caching | Parsers as data (`ParserDescr`), not code (stage 2) |
| Cubical vs QTT | Open research; OTT first |
| Literals as encodings vs a fast kernel | Kernel `natLit` for the `builtin nat` type, unfolding one step on demand (stage 6b) |
