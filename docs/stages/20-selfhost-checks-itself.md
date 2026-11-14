# Stage 20: the frontend checks itself, and gets faster

## 20a: towards `Frontend.wiz`

* A `match` or `fun` argument whose expected type is still a metavariable waits, like
  a `.c` one (`.cons (match s with …) rest`), and a postponed argument's metavariable
  takes any term at its own depth (a `match` elaborates to `let`s and `scase`).
* A `match` or `if` without an expected type (`let x := match …`) is checked against a
  new metavariable; `fun (x : A) => b` with typed binders infers `(x : A) → B`.
* `zonk` reaches every form the elaborator makes (`ecase`, `scase`, `delim`, `piq`,
  …): a solved metavariable inside a match's motive used to reach the kernel.
* Pruning: a solution at depth `k` that mentions a deeper metavariable whose type
  doesn't depend on the deeper variables (`?m := List ?n`, `?n` made under more
  `let`s) solves that one by a new metavariable at depth `k`.
* The structural parameter can be moved first past grouped binders (`(Tc TcI : Tm)`).

## 20b: the frontend checks `Frontend.wiz`

The rest was performance, found by profiling the checker (flat `perf` profiles, and
stacks sampled by interrupting it under `gdb`):

* **A `let`'s variable is glued to its value** in the elaborator's context: it quotes
  back as the variable. Every metavariable is applied to the whole context, and each
  application used to carry the values of all the `let`s before it (`splitCol` ran out
  of memory).
* **The binders' types are quoted once**, lazily, for the Π type of every new
  metavariable, instead of once per metavariable.
* **A catch-all in case analysis is elaborated once**: the last clause of variables
  becomes `let dflt✝ := …` before the split, and the branches refer to it (a match on
  a `Val` with `| t => …` copied the body into some 70 branches).
* String literals' character codes are binary numerals too.

On a prefix where `Lex.wiz`, `Parse.wiz` and `Kernel.wiz` keep their types and their
functions become axioms, the self-hosted frontend checks all 650 declarations of
`Frontend.wiz` without an error, in about a quarter of an hour. So every file of the
self-hosted frontend is accepted by the self-hosted frontend.

## 20c: the self-check in the test suite

Two more quadratic costs, both found by sampling stacks: the kernel's rule for an
application evaluated the argument to instantiate the codomain even when the codomain
doesn't mention it (`List.cons c rest` nested 2000 deep evaluated the rest at every
level: `usesVar`), and string literals' codes were unary. The whole self-hosted
frontend (`Lex`, `Parse`, `Kernel` and `Frontend.wiz`, 651 declarations) now checks
itself, unstubbed, in about 40 s; the test suite runs it.

## 20d: a faster kernel

Profiling the self-check by call counts (`gprof`; the work runs on a second thread, so
its timings are useless but its counts are exact) pointed at universe levels: every
unfolding of a constant substituted its level parameters even when it had none
(`substIfAny`), and `conv` computed the full sort of a type at every step to test for
proof irrelevance. `isProp` now looks only at what decides it (a Π type is a
proposition when its codomain is), and `conv` doesn't ask at Π and Σ types (the
comparison of the bodies or components asks again). The self-check went from 40 s to
20 s. What remains is mostly allocation: comparing stuck `ecase`s (the payload types of
big data types) branch by branch.

## 20e: dead code in the backend

The generated C showed allocations nobody used: `whnf` built a pair of erased values on
every call, and branches read fields their pattern variables never mentioned (an
increment and a decrement each). The backend now drops pure values nobody uses
(`erased`, numbers, constructors, projections, partial applications) before reference
counting (`elimDead` in `Reuse.lean`). In the kernel, two stuck `ecase`s with the same
branches over structurally equal environments (checked within a budget of nodes, without
allocating: `valSame`) are equal without comparing the branches. The self-check: 20 s to
13 s.

## 20f: sparse usages, shared constants

* The kernel's usage lists (how often each variable is used, for quantities) may stop
  early, the variables after the end unused: no usage is the empty list, instead of a
  list as long as the context for every term (a third of the kernel's allocations).
* **Constants are hoisted** (`hoistConsts` in `Reuse.lean`): a string literal is a list
  of characters, and was built again at every use (`strEq (kindOf s) "term.ident"`:
  about twenty allocations). A closed constant used as a value becomes a function
  `wiz.const.k` without parameters, which the C backend runs once, marking the result
  immortal (never freed, not counted as a leak); the other backends just call it.
  Constants are interned in a table: each constructor node caches its hash, computed
  from its children's by the smart constructor `Const.mkCtor`, so interning is linear in
  their size, and only the constants used as values (not every suffix of a string) get
  a function.

The self-check: 13 s to 11 s. Since the start of stage 20 it went from about 17
minutes (on a stubbed prefix) to 11 s.
