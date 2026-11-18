# Stage 21: bootstrap

## 21a–c: a self-hosted backend

`selfhost/Backend.wiz` compiles what the self-hosted frontend checked to C, and
`selfhost/rt.c` is its runtime. A minimal first version:

* **Erasure** (`eraseCheck`, **exercise 21.1**; `eraseInfer`), type directed through the
  self-hosted kernel (`quickType` follows elimination spines, else `infer`): types,
  proofs, sizes and quantity-`0` arguments become `◾`. A value of `μ D i` stays its
  payload, nested pairs, except for a type shaped like the natural numbers, whose
  values are native numbers (unpacked for a match). Descriptions become objects, which
  the runtime's `ind` walks to build the induction hypotheses, **lazily**: a hypothesis
  is computed when the method first reads it (eagerly, every structural function walked
  its whole argument).
* **Lazy `let`s**: the match compiler's `let`s (a shared catch-all, the hypotheses) are
  substituted when cheap (variables, projections) and else suspended with `memo`;
  evaluated eagerly they made the self-compiled compiler thousands of times slower.
* **C** (`cgE`, **exercise 21.2**): each term one C expression (GNU statement
  expressions for `let` and `case`), `λ`s lifted to C functions over their captured
  variables; a global defined by `k` `λ`s is a C function of `k` arguments, called
  directly when applied to as many (else through a curried closure); other globals are
  values built on first use. Natives by name: `Nat` arithmetic, `IO`, `Str`, arrays
  (persistent: Baker's trick), `StrMap` (a persistent treap), `memo`.
* **Runtime**: tagged words, objects collected by the Boehm garbage collector (no
  reference counts yet); the program re-executes itself once with a large stack.

**Bootstrap**: the self-hosted compiler (frontend and backend, about 12 000 lines of Wiz),
compiled by the Lean toolchain, compiles itself to C (about 90 000 lines); that program
(stage 2) produces the same C as stage 1 on the inputs tried. The test suite compiles
and runs a program with the self-hosted compiler (when `$WIZ_GC_CFLAGS`/`$WIZ_GC_LDFLAGS`
point at the garbage collector).

## 21d: faster self-compilation

Measured, not guessed (`perf`, per-global timestamps from a streaming driver):

* Compiling the toolchain took 5 min 43 s, almost all of it in one global: the Prelude's
  text, a string literal 2600 characters long, i.e. 2600 nested `List.cons`. Two
  quadratic costs: erasure evaluated each argument to instantiate the next parameter's
  type even when the codomain doesn't mention it (`usesVar`, as in the kernel), and the
  C text was built by appending `String`s, lists of characters (now a rope, `Doc`,
  printed piece by piece). Also `quickType` follows `scase`, `let`, `coe` and the like
  instead of inferring the whole match again at every nested split. Now 18 s.
* String literals become their code points in the C code, built once; numerals made of
  `Nat.succ`/`Nat.mul` are folded. The C went from 19 MB to 9.4 MB.
* **Multi-argument closures**: a chain of `λ`s is one C function over its captured
  variables and arguments (`mkfun`), and an application to several arguments calls it
  at once (`apn`), without the closures of the partial applications. 88 000 lifted
  functions became 35 000, the C 5.1 MB, and compiling it takes 31 s instead of 3 min.
  Stage 2 runs about twice as fast.

A note on debugging: under `gdb`, the Boehm collector's stopping of the world hangs,
because `gdb` intercepts its suspend signals; pass them through (`handle SIGPWR nostop
noprint pass`, and the same for `SIGXCPU`).

**Fixpoint.** Stage 2 (the self-hosted compiler compiled by itself) compiles the whole
toolchain to exactly the same C as stage 1 does. It took 15 minutes against stage 1's
18 s, about 70% of it the collector marking: payloads as nested pairs were about four
objects per constructor. A chain of pairs `(e₀, (e₁, … t))` is now one object, its tails
the same pointer with an offset in its low bits (taking one allocates nothing): 8½
minutes. A `match` was a method applied to the payload, a closure built and called each
time; a lambda applied to arguments is now a `let`: 6 minutes. Reference counting comes
next.

## 21g: reference counting in the self-hosted backend (first stage)

A second mode of `Backend.wiz` (`genProgramRC`), chosen by the compiler's flag `--rc`
(21k; before that, a first line `-- wiz: rc` in the program, which still works as a
fallback). The garbage-collected mode is unchanged, byte for byte.

* **Perceus on the erased terms** (`rcE`): the C is in A-normal form, one local per
  intermediate value, statements in evaluation order (C leaves the order of arguments
  unspecified, and with reference counts the order of a use and an `inc` matters).
  Liveness is one backward pass: a term is compiled knowing the variables used after it
  (by de Bruijn level), and returns those used from its start; arguments are compiled
  right to left. The last use of a variable moves it, earlier uses `inc` it, and a
  variable that dies unused is `dec`ed where it dies (after its `let`, at a function's
  start, at the start of each `case` branch that doesn't use it). A projection path from
  a variable reads in place and `inc`s only the field; a `case` on a variable's field
  reads the tag in place.
* **Runtime** (`rt.c` with `WIZ_RC`): a count in every object's header; functions own
  their arguments; function closures pass their collected arguments on (moved out when
  unique); freeing is a worklist (a list a million long frees without recursion);
  `memo` and the lazy hypotheses of `ind` release their suspension once forced; arrays
  are updated in place when unique, else copied (Baker's versions would make cycles);
  map nodes hold their keys. Constants (globals, string literals) are roots, released at
  exit, after which the program checks that every object was freed.

* **Borrowed parameters** (as in Lean): a parameter of a global function that its body
  only reads (projections, a `case`'s tag, borrowed arguments of direct calls) is
  borrowed, found as a greatest fixed point over all functions. A caller lends a
  variable to it (and releases it after the call if that was its last use); the function
  neither `inc`s it nor releases it.

* **Reuse** (Perceus' reuse tokens, as [stage 8c](08-backend.md)): in a branch of a
  `case` on an owned variable `x`, an object built after `x` dies takes `x`'s cell when
  `x` was unique and of the same size class (`reset`/`reuseobj`). Compiling backwards,
  the allocation comes first and leaves a wish for a cell; the place where `x` dies (its
  last projection, a call it was lent to, the branch's start) grants it. Tokens stay
  inside their branch. Constructors (globals that only build an object from their
  parameters) are put in place where they are applied, so that the object is visible to
  reuse; and, as in Lean's borrow inference, a parameter matched on where a branch builds
  an object is owned (its cell may be reused).
* **Drop specialisation**: a variable dying at its projection hands its reference to the
  field when it is unique (`dropTake`: the other fields are released and the cell freed,
  with no `inc`/`dec` of the field); an owned variable a `case` matches on and no branch
  uses dies at each branch's start, where the tag is known.

* **Strict `let`s**: a `let` that every path of its body evaluates (not under a `λ`)
  is evaluated where it stands instead of suspended (a thunk gains nothing when the
  value is needed anyway). Stage 2 on mid.wiz: 10.9% fewer allocations (thunks −30%,
  closures −23%), and the generated C is 17% smaller.
* **Demand analysis for `let`s** (replacing "used on every path"): a source `let` is
  only marked during erasure and decided after pushing and inlining, by a backwards
  analysis (`dmdA`) of how its body uses the variable: bottom (every path ends in
  `unreachable`), strict (evaluated on every path), lazy (on some), or absent, with a
  use count. Strict `let`s are evaluated where they stand, absent ones dropped, and a
  `let` that only one branch of a `case` uses (not its scrutinee) moves into that branch
  and is decided again there; the rest are suspended as before. Application is call by
  value, so only a suspended value and a `λ`'s body are lazy. Stage 2 compiling the
  toolchain: thunks −68%, allocations −10%, peak live objects −8%, C 6% smaller.
  (Absent parameters, found as a fixed point over signatures and passed `◾`, were tried
  and dropped: the analysis cost as much as it saved.)
* **Static objects**: a constructor without fields is `(k, ◾)` every time; the runtime
  keeps one object per `k < 64` with a count that starts high (never freed, not counted
  as allocated), used for constant constructors in the generated code (also the
  globals that are one, put in place) and for the Bools, `nil` and `0`'s payload the
  natives make. Stage 2 on mid.wiz: 9.4% fewer allocations.
* **Tail calls kept** (Lean's `preserveTailCall`): a function calling itself in tail
  position with a borrowed parameter given something it would release after the call
  (a variable it owns, or a temporary) makes that parameter owned, so nothing follows
  the call (17 of 228 borrowed parameters of the toolchain).

**Bootstrap in this mode**: stage 1 compiles the toolchain (with the `-- wiz: rc` line)
to C, and that program (stage 2, reference counted) compiles it again to the same C,
freeing every object by the end.

* **Small branching functions inlined with suspended arguments**: a global whose body
  is a `case` on a parameter with cheap branches (`Bool.and`, `Bool.or`, …) is put in
  place at saturated calls with its arguments bound by marked `let`s, so the demand
  analysis evaluates an argument only in the branches that use it: `Bool.and a b` no
  longer evaluates `b` when `a` is false (call by value did, and `conv`, `tmEq`, `occurs`
  and the like recursed through it).
* **Unmemoised hypotheses** (`indv`): when the method of an `ind` reads its hypotheses
  only as hypotheses (`hs.1ʲ.0`), each at most once on every path and not under a `λ`,
  or is itself a `λ` (a function-valued motive), it gets a view of the payload instead
  of the chain of suspensions, and a read computes the hypothesis where it stands
  (`p_hypAt`). Any other use of `hs` keeps the memoised chain.
* **Static constants**: a `λ` capturing nothing and an object built only from constants
  (an `ind`'s description, typically) are built once, kept as roots and released at
  exit (before the leak check, as string literals).

  Stage 2 compiling the toolchain, same input: 5232 M allocations with master's backend,
  2200 M with these three (−58%); peak live objects +11% (the constants), C +16%.

Next: reference counting by default.

## 21i: phantom parameters in the self-hosted frontend

Parity with 22e. `inductiveCmd` (`Frontend.wiz`) finds the parameters that no
constructor (nor the index type) mentions (`occurs` on the elaborated descriptions) and
gives each `p : P` a phantom domain (`phantomDom`): `D := p` for a type, `(0 x : P) ×
(x = p)` otherwise, none for a proof, a size, or a `D` that would raise the index type's
universe. The index type `Unit` becomes `(0 _ : D₁) → … → Unit`, and every index (the
descriptions' `ret`/`rec`, the type's `μ`, a match's `ind`) its value `fun _ … => tt`
(`phantomVal`); a constructor's index proof is `refl` there. Structures are inductive
types in this frontend, so they get the same. Erasure needs nothing new: in this kernel a
function into `Unit` is a proposition, so the tail is erased already. Not mirrored: an
indexed family with such a parameter (the Lean frontend pairs the index with the tail) is
rejected with an error, rather than accepted with the parameter forgotten. Tests:
`selfhostAgrees` runs the same declarations through both frontends.

## 21j: constructor parameters from the expected type, self-hosted

Parity with the Lean elaborator's `checkApp`: a constructor with implicit parameters
applied in check mode (`appExpected`) first makes the implicit arguments'
metavariables and a placeholder for each explicit argument (`preArgs`), and unifies the
result type with the expected one. The arguments are then checked as before, against
types that mention the solved parameters (`Tagged.mk 3 : Tagged .true` where the field
is `Code b`); the placeholders are dropped. If that unification fails the arguments come
first, as before.

## 21k: command-line arguments; `--rc`

`IO.argCount : IO Nat` and `IO.arg : Nat → IO String` (externs `wiz_io_arg_count`,
`wiz_io_arg`; the C and LLVM `main`s save `argc`/`argv` with `wiz_set_args`), and
`IO.args : IO (List String)` built from them, in `lib/IO.wiz` and in the self-hosted
Prelude (`selfhost/rt.c`'s natives read the `argv` that `rt_start` saves). The arguments
exclude the program's name; `#eval`/`#run` can't call them (they are C). With them the
self-hosted compiler takes its backend mode as a flag: `--rc`, `--rc-owned` or `--gc`
(`genProgramArgs`). The first-line pragma `-- wiz: rc` still works when no flag is
given, for one release. `scripts/fixpoint.sh --rc` runs the bootstrap in that mode.

## 21l: foreign functions and foreign types, self-hosted

Parity with [stage 9a](09-ffi.md) and 9d: the self-hosted compiler takes the same
`extern` and `foreign_type` declarations as the Lean one, and compiles them to the same
calls.

```
import IO
foreign_type FILE (finalizer := "fclose")
extern "fopen" (header := "stdio.h") fopen : String → String → IO FILE
extern "fputs" (header := "stdio.h") fputs : String → FILE → IO Nat
extern "strlen" (header := "string.h") strlen : String → Nat
```

* **Frontend** (`externCmd`, `foreignTypeCmd` in `Frontend.wiz`). To the checker an
  `extern` is an axiom, as before; it now also computes the marshalling kinds from the
  elaborated type (`ffiSig`), as `command.extern` does in `Elab/Command.lean`: `Nat`,
  `UInt64`, `Float64`, `String`, `Bool`, `Unit`, a foreign type, or a value passed as it
  is (a type variable, a Wiz data type, `Array`/`Str`/`StrMap`/`Bytes`); a parameter that
  is a type (or of quantity 0) is not passed; a result in `IO` takes and gives back the
  world. Anything else is the same error as the Lean frontend's. `foreign_type T` is an
  axiom `T : Type` with its finalizer. Both are recorded in a new field of `Globals`
  (`ffi : List Foreign`).
* **Backend** (`ffiDocs` in `Backend.wiz`). Each foreign function becomes a C function
  `d_g` of its arity (and `get_g`, its curried closure, or the constant computed once
  for arity 0) that converts its arguments, calls the C function and converts the
  result back, in both modes (`rt_drop` releases an argument under reference counting).
  The headers are `#include`d once each; without one, a prototype is written from the
  Wiz type, except for the runtime's own `wiz_…` functions (as `C.glue` does).
* **Runtime** (`rt.c`). The conversions (`rt_in_*`, `rt_out_*`), two new object kinds:
  `T_EXT`, a foreign pointer and its finalizer, and `T_RAW`, a 64-bit word (a `UInt64`
  or `Float64` whose top bit is set; smaller ones are scalars). Under reference counting
  the finalizer runs when the last reference goes, as in the Lean runtime; under the
  collector, when the pointer is collected (`GC_register_finalizer`), and the program
  collects once more at exit if there are any. A foreign pointer is lent to C for the
  call and released after it. The runtime functions `lib/IO.wiz` binds for `UInt64` and
  `Float64` (`wiz_u64_add`, `wiz_f64_show`, …) are in `rt.c` too, and the self-hosted
  Prelude declares the same `UInt64` and `Float64` operations.

**Tests** (`ffiAgrees`): the same program compiled by the Lean compiler and by the
self-hosted one (with the collector and with reference counting, which also checks that
nothing leaks) prints the same: C library functions through headers, numbers, strings
(UTF-8 both ways), `Bool`, `Unit`, `IO`, `UInt64` wrapping around, negative floats, a
`FILE` closed by its finalizer when its last reference goes (read back complete), and the
error for a type that can't be marshalled.

Not mirrored yet: `import_c` (9b: the frontend would need the preprocessed header, and a
C parser in Wiz), `glue` (9c), `Bytes`, and big numbers (a `Nat` is 63 bits in this
runtime; 21p). `implemented_by`, callbacks and `c_struct` came later (21q–21t).

## 21m: written quantities in the self-hosted frontend

Finding K10 of audit 2: `Frontend.wiz` built every binder at ω, whatever was written, so
`def twice (1 x : Nat) (f : Nat → Nat → Nat) : Nat := f x x` was accepted. It now reads
the binder's `quantity` node as `elabQuantity` does in the Lean elaborator (`binderQ`,
`writtenQ`): `0`, `1` or `ω`, by default ω on an explicit binder and 0 on an implicit
one; a numeral other than 0 or 1, or a quantity term `%t`, is an error. The quantities
reach the kernel, which already checks usage (`popUsage`):

* the binders of a `def`, an `axiom` and a partial definition's signature (`defT`,
  `teleT`, and the match-compiled definitions' telescope, `piTeleQ`), `(1 x : A) → B`
  (`depPis`, and `pis` in the scope checker for constructor field types), and a typed
  `fun` (`inferLams`);
* a `fun` checked against a Π: a written quantity must be the Π's ("binder quantity 1
  does not match the expected ω", as `checkFun`); an unwritten one takes it;
* `let 1 x := v; b` is the kernel's `letq` (the backend erases the value of a `let 0`);
* a constructor's parameters are implicit at 0 (the Lean elaborator's `implicitΔ`), so
  `List.cons` is `(x0 :0 U0) → (x1 : x0) → …`; an inductive type's own parameters keep
  their binders' quantities. The helper definition that `withDefault'` makes writes an
  implicit binder's 0 out when it makes the binder explicit.

Erasure needs nothing new: arguments at 0 were erased already, and there are more of
them now (an implicit `{w : Nat}` is no longer passed). The self-hosted sources needed no
change: the Lean frontend checks them with the same rules.

What does not match the Lean frontend (pinned in a test, and in
[CoreSpec §15](../CoreSpec.md)): a linear variable used once in each branch of a `match`
is accepted here (the kernel's case joins the branches' usage) and rejected there (a
branch is an ω argument of `T.casesOn`); a constructor field with a quantity is an error
here, since `Kernel.wiz`'s descriptions have none; implicit constructor fields don't
exist here. An unused linear variable (`def drop (1 x : Nat) : Nat := Nat.zero`) and a
match on a linear variable are rejected by both, through the kernel's `popUsage` and
eliminator rules (PR #84).

**Tests** (group `selfhost`): `selfhostAgrees` runs 23 declarations through both
frontends (accepted and rejected alike: linear functions passed and used twice, `let 1`,
`let 0`, implicit parameters used at runtime, a `fun`'s quantity against the expected
one, a quantity `2`); `selfhostVerdicts` pins the three differences above; a program
with quantities is compiled and run under both collectors.

## 21n: `private`, and unknown commands, in the self-hosted frontend

Parity with [13b](13-language.md) as far as it is reachable. `private def …` (any
`command.private`: a definition, axiom, partial definition, `mutual` block, inductive
type or structure) was an error here ("unsupported syntax command.def"); private
constructors (`| private c`), private fields and `private mk ::` were parsed and ignored.
Now `private` before a command declares the same names as without it.

**Privacy is now module-scoped** (with the module loader, A14). In the Lean toolchain a
private name is private to its *module*: another module gets "'x' is private to module
M", and there a type with private parts is opaque (it equals only itself, isn't
matched, isn't built by tuples or look-alike types; its recursors are private). The
self-hosted frontend does the first of those, and only for the ordinary declarations
(this slice):

* **Representation.** A private declaration `x` of module `M` gets the kernel name
  `_private.M._0.x` (the Lean frontend's `Globals.privateName` format), so two modules'
  private `x`s are different constants (`Globals.declName`, `privName`); a public
  declaration keeps its name. `Globals` carries the module being checked
  (`Globals.setModule`; the loader sets it per module, `modRunBody`) and whether the
  current command is `private` (`Globals.setPrivate`; `stepCommand` clears it after each
  command). The scope maps a written name to the current module's private declaration
  first (`privName M.cur x`), then to a public one, and otherwise — if the name is
  private to another module — reports `Scope.privTo`; `Scope.find` is the raw
  kernel-name lookup the internals use (`inlineTm`, the duplicate check). Messages and
  `show` print the source name (`privBase`, also in `Kernel.wiz`, as Lean's
  `Globals.privateBase`).
* **Resolution.** Every path that resolves a written name goes through
  `Scope.lookupV`: term elaboration (`elab`, `identHead`, so `@f`, `f` and `.c`/`T.c`
  resolutions too), constructor-head detection (`ctorHead`), `beqHead` (a literal
  pattern's `T.beq`), induction (`useInd`), structures (`structOf`/`structFields`, with
  the private `structure T` marker under the same module prefix), `#check`/`#reduce`,
  the extern/`c_struct`/`foreign_type` checks and `attribute [inline]`. A private name
  used in the same module still resolves, including in the type or body of a public
  definition (the compiled module references the private constant, which stays
  inlinable: `inlineTm` reads the raw kernel name); an importer gets
  `'x' is private to module A`, not "unknown identifier". `#print` by name is left on
  the kernel-name lookup it needs (a debugging surface, and the frontend has no `#print`
  of its own).
* **Duplicates.** Kernel names are unique (`dupFrom` compares them), so two modules'
  private `x`s are allowed, while a *source name* is declared once per module: a private
  `x` and a public `x` in the same module clash (`Scope.declaredIn`), as they do in Lean,
  and a public name declared in two modules still clashes. A public name shadows another
  module's private one of the same spelling (the private one is invisible outside).
* **Re-export is not attempted.** A module's public names are its exported set; a
  private name is never visible through an importer, nor through a public definition that
  mentions it (the imported *term* works, the name does not).
* **One-shot mode.** `checkFile` (the checker's `--oneshot`, and the old single-file
  behaviour) is one module, `input`: private names are visible throughout the file.
* **Cache.** A module's elaborated output is unchanged, so the cache's module key/graph
  key (`moduleGraphKey`, a hash of the modules' names and texts) stays as it is; the
  visibility check is a lookup on every elaboration, so a warm cache hit replays the
  diagnostics of the same graph (the key covers every module's text, and the toolchain
  id every selfhost source). The driver builds that key from the loader's discovery
  table before elaborating (`tabNames`/`keyOfGraph` in `Cli.wiz`, plus the root's
  `import_c` header texts), so a warm `check`/`run` repeats no command; `--no-cache`
  does not construct the key at all. Before this, `prepare` elaborated the graph first
  and the hit only saved the rendering, so a warm check cost the same as a cold one
  (measured in `bench/selfhost-bench.py`: compiler.wiz warm 10.6 s vs cold 38.3 s after
  the fix; 2.0x the host's RSS (`rss_ratio` 1.9765 in `bench/selfhost-bench.json`), 1.2x
  its cold time).

**Left for later slices.** Constructor- and field-level `private` (`| private c`,
`private f : T`, `private mk ::`) is still parsed and *stripped*: it is not a
module-scoped declaration of its own here. Nor is the opacity of a type with private
parts outside its module (no un-unfoldable `μ`, no refusal to `match` or project), private
recursors (the self-hosted frontend has none: matches are built directly), or private
`deriving`. A private `extern`'s argument-count hint and `attribute [implemented_by]`
on a private declaration are not resolved to its module name (the FFI records the
kernel name; both are reachable only from the declaring module).

An unknown command, or a modifier the frontend doesn't know (`sealed`, `noncomputable`
when the grammar gets them), is an error naming it ("unsupported command
command.sealed"), never ignored.

## 21o: `link_c`, `link_lib` and `export`, self-hosted

Parity with [9f](09-ffi.md) and the first half of 9g.

* **`link_c "f.c"`, `link_lib "m"`** (`linkCmd` in `Frontend.wiz`): recorded once each in
  `Globals`' foreign declarations (a new constructor `Foreign.link`), with the Lean
  frontend's check of a library name. The self-hosted compiler prints one C file with the
  runtime included, so it can't link anything itself: it names the files and libraries
  in the first lines of its output, `// wiz-link-c: f.c` and `// wiz-link-lib: m`, and
  whoever compiles that C adds them (`cc out.c f.c -lm`; the tests do). A path is the one
  written, relative to the input file's directory; the frontend is pure, so a missing
  file is reported by the C compiler rather than at the `link_c`.
* **`export "c_name" f (: T)?`** (`exportCmd`; `Foreign.exported`): the same checks and
  messages as `command.export` (the declaration exists, the optional type converts with
  its type, a C identifier, not exported twice, arguments `Nat`, `UInt64`, `Float64`,
  `String`, `Bool`, a foreign pointer or a Wiz value, a result among those but not a
  foreign pointer, or `Unit`, maybe in `IO`). The backend (`exportDocs`) writes a C
  function `c_name` after the program's definitions, in both modes: C values become Wiz
  values (a `String` copied, a foreign pointer lent without a finalizer, a `Bool` from
  `int`), the definition's closure is applied (`get_f`, with the world for `IO`, whose
  result is the pair's first field), and the result is converted back (a `String` as a
  `malloc`ed `char *` the caller frees, `rt_export_str`; `Unit` as `void`).

Callbacks, `c_struct`, libraries and the handle functions came later (21q–21s).

## 21p: a C `Nat` that doesn't fit is an error

A `Nat` in the self-hosted runtime is a 63-bit scalar (PR #80 makes a numeral from 2^63 on
an error). A foreign function's `Nat` result, or a `Nat` argument C passes to an export,
from 2^63 on used to be cut silently; `rt_out_nat` now stops the program with "a
foreign function's Nat does not fit in 63 bits" (exit code 3). The Lean toolchain's
`Nat`s are unbounded, so there the same program prints the number: a known difference.
UInt64 is unaffected (its large values are objects).

**Tests** (group `selfhost`): `private` in every position both frontends take it, and
`private` inside `mutual` rejected by both; module-scoped privacy through the self-hosted
checker: a private name used in its module and rejected in an importer (naming the
module), a private type and constructor rejected in an importer, two modules' private
names of one spelling allowed, a source name declared once per module (private or
public), a public name shadowing another module's private one, and the one-shot
`checkFile` path; group `selfhost-cli`: a private diagnostic cold and warm in the
driver's cache; unknown commands named in the error; the
`export`/`link_lib` checks (9 declarations, same verdicts); one program with exports
(numbers, strings both ways, `Bool`, `IO`) called from a `link_c` file and `link_lib
"m"`, run by the Lean compiler and by the self-hosted one in both modes, same output;
the 63-bit error in both modes against the Lean toolchain's answer.

## 21q: callbacks, self-hosted

Parity with the callbacks of [9g](09-ffi.md): a foreign function's parameter of function
type is a Wiz closure passed to C as a function pointer and a context.

```
extern "sort_some" sortSome : (Nat → Nat → Bool) → String
extern "on_tick" onTick : Callback (Nat → IO Unit) → IO Unit
```

* **Frontend** (`callbackKind`, `callSig` in `Frontend.wiz`). A parameter whose type is a
  function (`Nat → Nat → Bool`) has the kind `k[nn/b]`, the Lean frontend's key: the
  kinds of the callback's parameters, `/`, `!` if its result is in `IO`, and the result's
  kind. `Callback T` (a transparent definition in the self-hosted Prelude too) is `K[…]`.
  The signature has the same rules as an export's (`callSig` is now shared with
  `exportCmd`, as `ffiCallSig` is in `Elab/Command.lean`): no erased or `Unit`
  parameters, no functions, a result that isn't a foreign pointer. The same errors: the
  extern message now names c_structs and callbacks, and "a foreign function that takes a
  callback in IO must be in IO itself". A runtime native (`wiz_…`) takes closures, and any
  other value, as they are.
* **Backend** (`cbDocs`, `callIntoWiz`). One trampoline per signature,
  `wiz_cb_<params>_[io_]<result>` (the Lean backends' names): it takes a reference to the
  context for the call, applies the closure to the converted arguments and converts the
  result, the code an export's wrapper uses too. The extern's wrapper passes the
  trampoline and the closure; a borrowed closure is released after the call, a
  `Callback` is C's to release with `wiz_release` (21s). Under reference counting a kept
  callback C never releases is reported as a leak at exit, as in the Lean runtime; under
  the collector, a closure C keeps must be where the collector looks (static data of the
  program, as in the tests), not in `malloc`ed memory.

## 21r: `c_struct`, self-hosted

Parity with [9i](09-ffi.md)'s structs by value.

* **Frontend** (`cStructCmd`): `c_struct ["ctype"] [(header := "h")] T where fields` is the
  structure `T` (built as a `structure` command, so `T.mk` and projections are as usual)
  and a new `Foreign.cstruct` with the C type (default `wiz_s_T`, mangled as the Lean
  backend mangles: `hexMangle`), the header, the field names and their kinds (`n u f s b
  p`, `S:U` for a nested `c_struct U`). The Lean frontend's checks and messages (at least
  one field, a field's type on its own, no `:`, `|`, `<` in the C type or header, a field
  must be …). An extern's parameter or result of a `c_struct` type has the kind `S:T`.
* **Backend** (`structHelpers`, `structDefinition`): the header is included, or the
  definition is written from the fields (`struct t { … };` or a `typedef`); for each
  struct `wiz_sin_T(&c, v)` fills `c` from the structure (borrowed; the payload `(tag,
  (f₀, (f₁, … ◾)))`, a string converted with a reference of its own), `wiz_sfree_T` frees
  its strings, and `wiz_sout_T(c)` builds a structure (strings copied, a pointer without a
  finalizer). A struct argument is released after the call.
* Not mirrored: `Bytes` fields (there is no `Bytes` here), fields at quantity 0 (a field
  quantity is an error, 21m), `import_c`'s automatic structs (21t), structs in glue.

## 21s: libraries and handles, self-hosted

Parity with [9g](09-ffi.md)'s `--lib`/`--no-main` and handle functions, for a compiler
that prints one C file.

* `--lib` or `--no-main`: the C has no `main`; every export's wrapper starts the runtime
  first if nothing has (`rt_ensure`: the collector, or the static objects of reference
  counting). The C compiler links it with the program that calls it (`cc main.c lib.c
  -Iselfhost …`). Since this compiler prints C and links nothing, the two flags are the
  same.
* `--header`: instead of the C, the header of the exports, `exportHeader`'s text in
  `C.lean` (the `wiz_val` type, the handle functions and one prototype per export).
* **Handles** (`rt.c`): `wiz_retain(v)` and `wiz_release(v)` take and give back a
  reference to a Wiz value C holds (an export's result of a data type, a `Callback`'s
  context); `wiz_live_objects()` counts the objects alive. Under reference counting that
  is the objects allocated and not freed less the program's constants (everything the
  roots reach: globals computed once, natives' closures), which the Lean runtime makes
  immortal and doesn't count; under the collector they do nothing and the count is 0.

## 21t: `implemented_by` and missing `link_c` files, self-hosted

* `attribute [implemented_by g] f` ([22b](22-numbers.md); `implementedByCmd`, a new
  `Foreign.impl`): the Lean frontend's checks and messages (both names exist, `f` isn't a
  runtime native or an extern, not itself, `g`'s type converts with `f`'s). The backend
  erases `f` as `g` (`eraseGlobals`, `implOf`), so compiled code runs `g`; the kernel
  keeps `f`. The native representations of 22d (`implemented_by mk get` on a
  constructor) are an error here.
* A `link_c` file that doesn't exist is the Lean frontend's error ("link_c: no file
  f.c (paths are relative to the .wiz file)"). The frontend is pure, so the compiler's
  driver checks the paths after it (`missingLinks` in `Backend.wiz`, with C's `access`),
  relative to the input's directory, and reports them with the frontend's errors (exit
  code 1, no C). The checker (`checkerSource`) doesn't check them.
* Still not mirrored: `import_c` (9b, 9i: it needs the preprocessed header, which the
  driver would have to get from `cc -E`, and a C parser in Wiz, `FFI/CParse.lean`) and
  `glue` (9c: the checked C subset of `FFI/CGlue.lean`, again a C parser and checker).

**Tests** (group `selfhost`): callbacks (qsort with Wiz comparators, a string callback,
a `Callback` kept, called in `IO` and released) and `c_struct`s (`div_t` from its header,
a generated struct with every scalar kind passed and returned, a nested one), each run
by the Lean compiler and the self-hosted one in both modes; a kept callback never released
is a leak in both; the checks of callbacks, `c_struct` and `implemented_by` (same
verdicts); a C program using a self-hosted library (`--lib` with the collector,
`--no-main` with reference counting) and its header, with `wiz_retain`, `wiz_release`
and `wiz_live_objects`, against the Lean `--lib` build; `implemented_by` on a definition
and an axiom; a missing `link_c` file in both toolchains.
## 21u: Σ types, `∀`, `#eval` and `attribute [inline]` in the self-hosted frontend

`Frontend.wiz` elaborates the rest of the Lean frontend's Σ and Π syntax (`inferT2`,
`checkTuple`): `A × B` (`term.prod`), `(x : A) × B` with a written quantity
(`term.depSigma`, `depSigmas`), `(a, b, …)` (`term.tuple`: checked against a Σ type, or
inferred as `A × (B × …)` and annotated, since the kernel can't infer a pair), `.1`/`.2`
(`term.proj`), and `∀ x (y : A) {z : B}, C` (`term.forall`; a binder without a type gets a
hole, a metavariable in `Type`). A hole `_` in a type position is now a metavariable too.
There is still no `let (x, y) := …` (`Kernel.wiz` has no `split`, §7.1 of CoreSpec).

`#eval t` is `#reduce t` (the value is printed as the kernel's normal form, not as the
Lean toolchain prints it), and `attribute [inline] f` is checked as in the Lean frontend
(`f` must be a declaration with a definition) and otherwise ignored: inlining is a hint
to the Lean compiler. Not checked here: a second `attribute [inline]` of the same name
(an error in the Lean frontend).

**Tests** (group `selfhost`): 10 Σ/∀ declarations with the same verdicts in both
frontends; `#eval` and `attribute [inline]` (5 verdicts and one output).

## 21v: a linear variable in every branch of a `match` (`T.casesOnA`)

Until now the Lean frontend rejected `def m1 (1 x : Nat) (b : Bool) : Nat := match b with
| .true => x | .false => x` and the self-hosted one accepted it (21m). The self-hosted
frontend was right: `x` is used once on every path, and the kernel's `ecase` joins its
branches' usage (CoreSpec §5.3, `1 ⊔ 1 = 1`). The Lean elaborator compiled the match to
`Bool.casesOn motive m_true m_false b`, whose methods are separate ω arguments, so the
two uses added up to ω.

Every inductive type now also gets `T.casesOnA` (E1 of
`wiz-notes/linear-case-design.md`; `mkRecursor … (additive := true)`): the
methods are bundled into one argument at quantity 1, a function from the tag,

    T.casesOnA : {Δ} → (motive : …) → (1 m : (t : Enum ls) → ecase t [ULift M_c, …]) →
                 {ξ} → (x : T Δ ξ) → motive ξ x

where `M_c` is `T.casesOn`'s method type for `c`, lifted to `Sort (imax (l+1) v)` so that
all branches of the type-level `ecase` live in one universe (universes aren't cumulative).
Its body is the sized case `scase` at `∞` (which runs its method once and doesn't scale it)
calling `down (m 'c)` on the fields. A `match` with a variable bound at a literal
quantity other than 0 and ω in scope (`LocalCtx.linearLvls`: `def`/`fun` binders, `let
1`, equation parameters) passes `fun t => ecase t [up m_c, …]` instead of the separate
methods; a reverted column that is linear is re-bound at 1. Everything else elaborates
exactly as before, to `casesOn`. Structural recursion (`T.rec`) and sized matches are not
additive: a linear variable used by a recursive call is used once per node.

**No kernel change**: `T.casesOnA` and every term using it are checked by the kernel like
all declarations (the usage checker is not on the path changed here; its rules for
`ecase`, `scase`, `up`/`down` were already there). The compiler has no special case for
`casesOnA` (Erase.lean unfolds `casesOn` calls by name), so such a match compiles through
the generic path: correct, possibly slower; only matches with a linear variable in scope
take it.

**Tests** (group `selfhost`): 12 declarations, both frontends alike (Bool, Nat, Option,
List, an indexed family, nested matches, `let 1`; dropping the variable in one branch, or
using it twice or under an ω argument, rejected); a compiled program with additive matches.

## 21w: one value representation for the two runtimes

The Lean toolchain's C/LLVM runtimes (`runtime/wiz.c`) and the self-hosted backend's
runtime (`selfhost/rt.c`) had grown two different value representations: 62-bit scalars
with GMP numbers against 63-bit wrapping ones, different special-tag numbers, an 8-/16-byte
header against `wiz_hdr`'s fixed 16 bytes, a two-argument closure calling convention
against `wiz_apply`'s argument array, and a treap/offset-chain layout against flat
constructors. That is the obstacle in front of moving runtime leaves into Wiz
(`wiz-notes/runtime-in-wiz.md`, decision D5): a Wiz module would have to be written twice
or know which runtime it is running on. This section records the first step: `rt.c` now
uses `wiz.c`'s representation for everything the self-hosted backend needs. (The Lean
runtime's file was split into `runtime/wiz_rt.h` and the `runtime/rt_*.inc` area files
after this section was written; "`wiz.c`" below means that runtime, whose header is now
`wiz_rt.h`.)

**What now agrees** (checked by `_Static_assert`s in `rt.c`):

* **Scalars and tags.** `BOX`/`UNBOX`/`ISBOX` are `wiz.c`'s, and the special tags are its
  numbers: `T_CLO = 0xFFFF0000`, `T_RAW = …0002`, `T_EXT = …0003`, `T_ARR = …0005`,
  `T_STR = …0006`, `T_MAP = …0007`, `T_THUNK = …0008` (the unused `T_BIG`, `T_BYTES`,
  `T_WARRAY`, `T_WMAP`, `T_ITAB` keep their `wiz.c` numbers too).
* **The header.** Every object starts with `wiz_hdr`: `int64_t rc`, `uint32_t tag`,
  `uint32_t size` (16 bytes). `size` means fields for constructors, captured arguments for
  closures, 0 for text/arrays/maps/foreign pointers.
* **Layouts.** Constructors (`wiz_ctor`), closures (`wiz_clo`: `fn`, `arity`, captured
  arguments), thunks (`wiz_thunk`: `fn`/`val`), foreign pointers (`wiz_ext`), text
  (`wiz_str`: `len`, inline UTF-8), arrays (`wiz_array`: `len`, `cap`, `data`) and text
  maps (`wiz_map`: open addressing, `count`, `cap`, `keys`, `vals`) are the same structs,
  field for field. (How a *constructor value* is encoded still differs; see below.)
* **Closure ABI.** A closure's `fn` now takes the whole argument array (`V *a`), captured
  arguments first, exactly like `wiz_boxed_fn`; `arity` counts captured and applied
  arguments. The generated functions (`static V lamN(V *a)`) were already of that shape,
  so `Backend.wiz` did not change. The runtime's own suspensions (`ind`'s hypotheses) were
  rewritten from `fn(env, arg)` to the same array convention.
* **Suspensions.** `memo` and the backend's suspended `let`s are `T_THUNK` objects with
  `wiz.c`'s force protocol (`fn` cleared after the first force, `val` kept), instead of
  closures with a mutable environment.
* **Count rules.** `inc`/`dec` implement `wiz.c`'s rules: `rc > 0` owned by one thread,
  `rc < 0` shared (atomic), `rc == 0` immortal (the static `(k, ◾)` values are now
  `rc == 0`, not a large count). Reuse and drop specialisation use the same `rc == 1`
  tests.
* **Data structures.** Under reference counting, arrays are `wiz_array` (updated in place
  when unique, else copied) and `StrMap` is `wiz_map` (open addressing, linear probing),
  not the Baker array and treap. Text is `wiz_str` in both.

**What is still self-hosted only** (and why it can wait):

* **The constructor payload encoding.** `wiz.c` has flat constructors: an object's tag
  is the constructor index, `size` its number of fields, and a nullary constructor is the
  scalar `BOX(k)`. The self-hosted backend erases a value of `μ D i` to its *payload*
  `(tag, fields…)`: a tag-0 object whose first field is the constructor tag, the rest the
  fields (flattened as a chain), and a match switches on `tagof(fld(x, 0))`. The `Obj`
  struct and the special tag numbers agree, but a constructor value is not interpretable
  by the other runtime until this encoding goes. It goes with the offset chains (below).
* **Offset chains.** A flat pair chain `(e₀, (e₁, … t))` is one tag-0 object, and a tail is
  the same pointer with an index in bits 1–3. `wiz.c` has flat constructors only. Removing
  the chains changes `Backend.wiz`'s object generation and projection code (and costs
  memory and allocations), so it is the next representation step, not this one.
* **63-bit `Nat`.** `rt.c`'s numbers are 63-bit words with wrapping arithmetic; `wiz.c`
  has 62-bit scalars and `T_BIG` GMP objects. The self-hosted tests rely on `2^63 - 1`
  (`=selfhost` case 36), so this cannot change without either GMP in every self-hosted
  program or a deliberate smaller `Nat`.
* **`T_HYP = 0xFFFF000C`.** `ind`'s lazily computed hypotheses have no `wiz.c` counterpart
  (it computes them in compiled Wiz, `PrimCode.lean`). It is the next free special tag;
  it must be added to the shared header before a value can cross runtimes.
* **Boehm mode.** With `WIZ_RC` off, `rt.c` still uses the collector and its persistent
  Baker arrays and treap map. The RC mode is the converged one; retiring Boehm removes
  this branch.
* **Allocation strategy.** `rt.c` allocates small objects from 16-byte size-class free
  lists carved from 1 MB blocks; `wiz.c` calls `malloc` per object. This is not part of
  the ABI, and the self-hosted compiler's measurements depend on it.
* **Data structures missing in `rt.c`.** `Bytes`, `WordArray`, `WordMap`, `Intern` and
  GMP numbers exist only in `wiz.c`; the self-hosted frontend's native list does not name
  them. Adding them is where the first shared Wiz leaves will land.
* **FFI marshalling.** The generated wrappers call `rt_in_nat`/`rt_out_nat`,
  `rt_in_str`/`rt_out_str`, `rt_in_bool`, `rt_in_u64`/`rt_out_u64` and so on; `wiz.c`'s
  ABI names are `wiz_in_nat`, `wiz_out_nat`, `wiz_in_string`, `wiz_out_string`,
  `wiz_in_bool`, `wiz_in_u64`, … The raw `UInt64`/`Float64` boxes and foreign pointers
  already agree; `Nat` is 63-bit here, and a `Bool` result is the constructor payload
  above, not `wiz.c`'s scalar constructor.
* **`lib/Sys` marshalling and threads.** `wiz.c` exports the `wiz_sys_*`, channel, MVar,
  lock and ref entry points; `rt.c` has only the `rt_*` FFI marshalling that `Backend.wiz`
  emits, no POSIX layer and no thread library (the `rc < 0` rule is implemented but never
  used). `wiz_live` and the proof budget are globals, not `__thread`.
* **Leak check exit code.** `wiz.c` reports leaks with exit code 2; the self-hosted
  runtime exits 4 (and only in RC mode), which the `=selfhost` cases test.

**Path to one runtime.**

1. **Land the `runtime/wiz_rt.h` split** (header + area files) so the shared definitions
   have one home. Then replace the top of `selfhost/rt.c` with `#include "wiz_rt.h"` (the
   inline part only) and keep the self-hosted extensions in a small `selfhost/rt_ext.h`.
   The `_Static_assert`s above are the acceptance test.
2. **Flatten constructors.** In `Backend.wiz` and `rt.c`, drop the payload encoding
   (`mkobj(k, fields…)`, match on `tagof(x)`) and the offset chains, then delete
   `OBJ`/`OFF`. This is the last layout difference; after it a constructor value built by
   either backend is the same object.
3. **Retire Boehm** (D2): make `WIZ_RC` unconditional in the self-hosted backend, delete
   the Baker array and treap map, and move the GC cases in `=selfhost` to RC.
4. **Share the leaf layer.** Implement the library-facing `wiz_*` ABI (`wiz_in_string`,
   `wiz_map_*`, `wiz_array_*`, `wiz_str_*`, `wiz_bytes_*`, `wiz_itab_*`, `wiz_sys_*`) in
   `rt.c`, and move the marshalling leaves (`Text`, `Sys`, `Print`, `Intern`) into
   `lib/Runtime/*.wiz` once, compiled by both toolchains (`wiz-notes/runtime-in-wiz.md`,
   option (a)). The self-hosted backend's own `mkobj`/`mkclo`/`apn` can stay: they are the
   backend ABI, not the shared value ABI.
5. **Decide the number story** (D7's sibling): either give the self-hosted runtime GMP
   `T_BIG` objects (one `Nat` representation at last, at a cost), or accept 63-bit `Nat`
   in the self-hosted backend and keep `T_BIG` a Lean-runtime detail. The closure of this
   choice is what lets a *single* runtime object serve both compilers.
6. **Threads last.** Port `wiz_mark_mt`, thunk locking and the channel/MVar/lock/ref
   entry points to `rt.c` (or move the Wiz-side `Session`/`Conc` layer to the shared
   runtime); the `rc < 0` rules are already in place.
7. **Then the runtime is one object**: `wiz_rt.h` + `wiz_rt.c`, `-DWIZ_API=` for the
   object build, embedded inline for the default; the self-hosted compiler links the same
   object, and the fixpoint test checks that both compilers' C output is identical.
## 21x: constructor field quantities and implicit constructor fields, self-hosted

The last two frontend differences of 21m. `Kernel.wiz`'s descriptions now carry each
field's quantity as the Lean kernel's do (`Desc.arg q S D`, CoreSpec §9.1):

* **Quantity terms.** `Tm.qty` (`Qty : U 0`) and `Tm.qlit q` (`vqty`, `vqlit`). Binder
  quantities stay literals (`Q`); a `Qty` term is only a description field's quantity, or
  the first argument of a `Desc.elim` method (`qTy`, which was `Unit`). `qtyOk` is
  `checkQty`: checked erased, and its value must be a literal or a variable.
* **Descriptions.** `darg q S D`, `drec q j D`, `dhrec q H j D` (and `vdarg q S E` …). The
  methods receive `q` (`vDelim`; before, `tt`), and the method types say so.
* **The template `⟦D⟧`** (`interpTm`) builds the field's `Σ` at the method's `q`, with the
  new `sigmaQ l q A B`: a `vsigma` at a literal; at a stuck quantity (a description whose
  field quantity is a variable) a neutral, `Spine.ssigq`, which quotes back to `sigmaQ`,
  is a type in `U l` (`typeOfNe`, `propSort`) and is compared part by part (`convSpine`).
  The Lean kernel builds a Σ at a polynomial quantity there; this kernel has no
  quantity variables on binders, so such a Σ stays stuck, with the rules of a Σ at an
  unknown quantity (at a bare variable only, as `qtyPoly` allows; `cast`, `eqTy` and `eq`
  at it stay stuck, where the Lean kernel computes them): its projections in erased positions (`fst` at run time is rejected,
  as `1 ≤ q` fails at `q = 0`), `snd` at ω, η in conversion, and a pair's first part
  counted ω times. This is not hypothetical: the frontend's `match` hands the kernel
  normal forms of `All`/`⟦D⟧` at a description stuck on a tag, whose `Desc.elim` methods
  project such a Σ (in a type).
* `vEqDesc` (equal quantities ↦ on, two different literals ↦ `False`, else stuck:
  `qtySame`, as `sameQty`/`qtyApart`: the same variable is equal to itself), conversion (`conv` at `Qty`, and the quantities of
  two descriptions), `castDesc`, `groundEqDesc`, `eqPayload`, `quote` and `show`
  (`arg(0 Nat, …)`; nothing is printed at ω) follow the Lean kernel.

`Frontend.wiz`: a field's quantity is read as `elabQuantity` reads it (ω explicit, 0
implicit; `2` and `%t` are errors), kept in `Field` (now `mk name q impl ty`), and goes
into the description (`ctorDesc`, `mctorDesc`) and the constructor's type (`ctorType`).
An implicit field (`| cons {n : Nat} …`) is an implicit argument of the constructor
(`Global.implicits`), so a call leaves it out, and patterns name only the explicit
fields (`explicitPats`, as `explicitIdx`). A match binds each field at its quantity
(`fieldCols`, `bindLetsT`: `letTm`; `Col` and `Ctor` carry the quantities), as
`T.casesOn`'s method takes it: a field at 0 can't be used at run time, a linear one must
be used once. A structure (a data type here, 18e) binds a linear field at ω (the Lean
elaborator takes a structure apart by projections at ω), and a field at 0 has no
projection function (`classMethods` makes none). `Backend.wiz` needed nothing new: a
payload's field at 0 is the first part of a `Σ` at 0, erased already.

A `match` on a structure that has a field at 0 was a difference until #217 (the Lean
elaborator projected the erased field at ω); both now bind it at 0, so no difference is
pinned any more and the 21m test of pinned differences is gone.

**Shapes changed** (selfhost/*.wiz): `Tm.darg/drec/dhrec` and `Val.vdarg/vdrec/vdhrec` take
the quantity first; new `Tm.qty`, `Tm.qlit`, `Tm.sigmaQ`, `Val.vqty`, `Val.vqlit`,
`Spine.ssigq`. Frontend: `Field.mk` has 4 fields, `Ctor.mk` 5, `Col.mk` 4;
`ctorType`, `fieldCols`, `specialize`, `addCtors` take one more argument.

**Tests** (group `selfhost`): field quantities 0/1/ω and implicit fields, the same verdicts
in both frontends (`fieldQtyDecls`); a program with them, compiled by the Lean compiler and
by the self-hosted one (both collectors); the differential test's `MTm` descriptions carry
a quantity (ω in the existing terms); two core terms from the review of this stage
(`wiz-notes/fieldq-review.md, probes 7a and 15b) checked by Kernel.wiz with the
Lean kernel's verdicts.
## 21y: modules and imports (A14, first milestone)

`import M` was silently the embedded Prelude: the self-hosted frontend had one module,
the input file. The frontend now loads a module graph. A module's name is a path
(`A.B.C` is `A/B/C.wiz`), resolved under the roots in order and then in the working
directory; the root module is `Main` (the file `input.wiz`). A root is written `-I DIR`
(or `-IDIR`) or `--include DIR` (or `--include=DIR`), and the first root with the file
wins. `Prelude` is still the embedded `preludeText`: the self-hosted frontend cannot
check `lib/Prelude.wiz` yet (A9-A23). The other library imports the corpus uses (`IO`,
`Std`, `Sys`) are canonicalised to `Prelude` when imports are scanned, since the
embedded prelude declares
the `IO` names and no real `IO.wiz` is checkable yet (without it, every existing
`import IO` program would be a missing module).

The loader (`selfhost/Frontend.wiz`, "A14") is pure: the driver reads the files
(`moduleRootSources`, breadth first, each module once, with `IO.readFile`), and
`moduleCheck` builds the dependency graph. A module's imports are hoisted, in source
order; dependencies are elaborated before their importers into the same `Globals` and
the same parser tables, so an importer sees the imported module's names and notations,
and each module is elaborated once no matter how many modules import it. Declaration
order is deterministic: dependencies in source order, then the module's own commands in
source order. A cycle is an error naming it (`error: import cycle: B -> C -> B`); a
module that cannot be found is `error: cannot find module NAME`. Duplicate names are
rejected across modules as within one (the same `newDuplicate` check).

The cache key (`moduleGraphKey`) is a rolling hash of the loaded modules' names and
texts in load order; the checker prints it with `--key`. It follows a transitive change
(a dependency's text) and ignores a file that no module imports. The real cache (D5)
will key on it, plus the frontend's version. The checker's `--oneshot` runs the
pre-loader single-file path (`checkFile`) instead, for the old behaviour's own tests.

**Not done.** `private` is module-scoped now (21n), but only at the declaration level:
constructor- and field-level `private` is stripped, and a type with private parts is not
opaque outside its module. `namespace`/`open`/`section` are not parsed
(A23). The compiler driver accepts modules for checking, but `link_c` paths and the
`-- wiz: rc` pragma are read from the root file only. Compiling `lib/` still needs
classes/instances (A10), universe polymorphism (A15), the proof surface (A16), tactics
(A13), macros (A12), `deriving` (A11) and the wider runtime (C11/C12); modules were the
first dependency, not the last.

**Tests** (group `selfhost`, sixteen cases): an imported module's declarations in scope, a
transitive import (A→B→C) with a shared Prelude, a diamond (one module imported twice is
checked once), a cycle, a missing module, a duplicate name across modules, a `-I` root,
and the cache key (stable for one graph, different when a module's text changes); then
dotted imports (`A.B.C` is `A/B/C.wiz`), `-I` order (the first root with the file wins,
a root without it is skipped), a cycle through three modules, a duplicate name in two
imported modules, a transitive cache-key change (and no change for an unimported file),
`IO`/`Std`/`Sys` loading the embedded Prelude once, the CLI root spellings, and the
compiler driver resolving its roots too. `wiz check` of the generated self-hosted
sources passes, and the self-hosted frontend still checks itself.

## 21z: the proof surface in the self-hosted frontend (A16)

The self-hosted frontend could define data and functions but not state or prove a
proposition: `term.prop`, `term.sort`, `term.eq`, `term.refl`, `term.rfl`, `term.cast`
and `term.transp` had no handlers (the parser already produced them, the kernel already
had the forms). `Frontend.wiz` now elaborates them:

* `Prop` is the kernel's `.prop` (`Sort 0`); `Sort l` is `.sortL l`, with the level
  from U1's level elaborator (`levelArg`/`elabLevel`): numerals, `max`, `imax`, `+ n`,
  the declaration's universe parameters (`Sort u` in a `.{u}` definition) and `_` level
  metavariables. `Sort 0`, `Sort (max 1 2)` and (with U1) `Sort u` are the tests; `Type`
  keeps its handler, and a level that is not in scope is an error naming it.
* `a = b` is `.eq A a b` (`A` the inferred type of `a`, the result in `Prop`).
* `refl a` is `.tyRefl a` when `a` is a type and `.eqRefl A a` otherwise; `rfl` is
  checked against the expected equation (`.eqRefl`, `.tyRefl`, or the unit proof for an
  equation that computed to `True`), and a non-equation expected type is an error.
* `cast e t` is `.coe A B e t`, with `e : A ≡ B` (the equation's type must still show
  its sides: a computed one is reported, as in the Lean frontend).
* `transp P p e` is `.subst A a P p b e`, with `P : (b : A) → a = b → Prop` and
  `p : P a (refl A a)`.
* `True` and `False` are built-in names for `.ptrue`/`.pfalse` (like `Unit`).

Nothing in `Kernel.wiz` changed for A16 (U1 changed it for levels): the kernel
infers/checks and marks the terms like every other declaration. Types still have no
`Eq` name (only the `a = b` form), and `by` (tactics, A13), macros/notation (A12) and
`deriving` (A11) remain the next surface pieces.

**Tests** (group `selfhost`): a file with `n = n` by `rfl`, a `Prop`-valued definition,
`Prop`, `Sort 0`, `Sort (max 1 2)`, a `Sort`-typed definition, a polymorphic `cast`, a
`transp` along an equality (its motive a proposition), `True`/`False`, four rejected
proofs/types (a wrong equation by `rfl`, `Prop := Type`, `Sort 1 := Type 1`, `cast` on
`False`) and an unknown-level error; a differential case with the same 12 declarations
accepted/rejected by the Lean frontend and the self-hosted one; U1's own cases cover
`Sort u`, `Type u` and level inference. `wiz check` of the generated self-hosted sources
passes, and the self-hosted frontend still checks itself.

## 21ab: named arguments (A9)

`f a (x := e) b` now elaborates in the self-hosted frontend. The kernel's `Tm` and `Val`
carry no binder names, so a `Global` keeps its parameters' names beside their implicit
mask (`paramNames`, as `paramMask`; filled for definitions, axioms and partial
definitions from their written binders, and for a constructor from the type's parameters
followed by the constructor's fields; an `extern` writes no binders). An application
with `term.namedArg`
arguments is split into named and positional lists, in source order. A duplicate name is
`argument 'x' was already given`. The telescope is then walked: a binder whose name has
a named argument takes it (explicit, implicit or instance), otherwise an implicit binder
gets a metavariable and an explicit binder takes the next positional argument. The
result is a positional argument list (with `_` for each implicit binder passed over), so
the existing `appArgsT` still inserts implicits, postpones constructor arguments and
applies the expected type. A named argument that would have to cross an explicit
parameter with no argument is `named argument 'y' comes after the explicit parameter
'x', which has no argument`; a name no binder has is `no parameter named 'y'`, and a
named argument outside an application is `a named argument `(x := e)` is only allowed as
an argument of an application`. `@f` still makes every binder positional (named
arguments still match by name), and `f (b := 1) 5` gives `a` the `5`.

Named arguments work for a global function whose parameters are written as binders, or
in the leading Π binders of its type (`axiom f : {A : Type} → …`, so `MVar.new
(A := B)` is accepted; that also reads the names an `extern` writes in its type).
A constructor's parameters and fields are named too (`paramNames` is the type's `ps`
followed by the constructor's fields, beside the same implicit mask): `P.mk (y := 2)
(x := 1)` fills `x` and `y` in the telescope's own order, so a later field's type may
mention an earlier named one, and an implicit constructor field or a parameter can be
named (`Imp.mk (n := 3) 7`). A local variable's Π type, a dot-constructor (`.mk`, whose
head needs the expected type) and an inductive type's own parameters
(`List (A := Nat)`) keep no names yet, so a named argument there is rejected
(a clear error, not a silent mismatch); class/instance binders will use the same path
once A10 stores their names. An implicit parameter written only in a declaration's type
is still not inserted positionally when it is omitted (A3); it can be supplied by name.

**Tests** (groups `selfhost`, `language`): explicit, implicit, reordered and interleaved
named arguments, a named implicit, `@f` with a named implicit and with a named explicit,
and implicit insertion around named arguments, checked against the Lean frontend; a
constructor's named fields and parameters (reordered, a dependent later field, an
implicit field); unknown, duplicate, ordering and bare named-argument errors; and the
self-hosted frontend still checks itself.
## 21aa: `import_c`, `glue` and native representations, self-hosted

The self-hosted frontend now reads C headers (`selfhost/CParse.wiz`) and checks the C
glue subset (`selfhost/CGlue.wiz`). The driver reads each `import_c "h"` header from the
file system (the frontend is pure) and passes the texts in `Globals.headers`; there is
no C preprocessor, so a header must be self-contained. `CParse` parses prototypes,
typedefs and struct definitions. `import_c` binds the scalar prototypes it can marshal
(`Nat`, `UInt64`, `Float64`, `String`, `Bool`, `Unit`, foreign pointers and declared
`c_struct`s) as `C.name`, emits an implicit `#include`, and records the functions for
`glue`; `(pure)`, `(no_auto)` and `(skip := "…")` are read as in the Lean frontend.
`glue` checks numbers, strings, calls, assignments, `if`/`while` and struct field
access, then emits a static C wrapper called by the backend's normal foreign path.

`attribute [implemented_by mk get] T.mk` is accepted on a sealed constructor; the
constructor's implementation is registered (`mk`), as is the representation. A type
whose operations are all `implemented_by` runtime natives (the `U32Array`/`U64Map`
pattern) therefore compiles to its natives. Direct pattern matching on a native value
still needs `get` in erasure.

**Not done.** No preprocessor, no automatic struct/pointer mapping from a header (declare
a `c_struct`/`foreign_type`), no `for` loops, struct locals or `&struct` in self-hosted
glue, no rewriting of matches through `get` (buffer parameters came in 21ad).

**Tests** (group `selfhost`): an `import_c` header whose functions are called from Wiz
and from `glue`, and a native representation on a sealed constructor that runs through
`wiz_u32array_*`, in GC and RC modes.

**ABI v1 (aligned with `wiz-notes/prior-art/compilers-runtime-ffi.md` §2.2, cheap
parts only).** Kinds are explicit in every `Foreign.fn`: `n`/`u` are `uint64_t`, `f`
is `double`, `s` is `const char *` (borrowed in, caller-owned out), `b` is `int`, `p`
is `void *` (+1 wrapped, borrowed for a call), `w` is a Wiz `wiz_val` (+0 in, +1 out),
and `e`/`v` are omitted from the C prototype (`y`, a byte buffer, is 21ag: the buffer's
pointer and length). Structs by value go only through an
explicit `c_struct`; a native representation is accepted only on a **sealed** type
whose constructor's `mk`/`get` are registered, so values of the type are the runtime
natives. The generated `--header` now defines `WIZ_ABI_MAJOR`/`WIZ_ABI_MINOR` (1/0)
and carries the ownership table as comments. Deferred (documented, not implemented):
a linked `wiz_abi_version` symbol, `_Static_assert`s for `c_struct` layouts, boxed
`Nat`/`NatObj` by default, callback roots on both collectors, and the preprocessor or
automatic struct/pointer import for `import_c`.

## 21ac: notation and macros in the self-hosted frontend (A12, first milestone)

The frontend had one form of notation (`infixl`/`infixr`, stage 19b) and expanded it
with an ad-hoc `Note`; `syntax`, `notation`, `macro_rules` and the macro/tactic
registrations were "unsupported command". `lib/` uses them: counting declarations at the
start of a line in the 78 `lib/**/*.wiz` files (comments skipped, including `lib/Hdl/`,
2026-11-15 at `24218ce4`) gives

| form                            | declarations | files |
|---------------------------------|-------------:|------:|
| `syntax`                        | 123 | 13 |
| `attribute [tactic …]`          |  37 |  5 |
| `macro_rules`                   |  27 |  5 |
| `infix` (plain)                 |  18 |  4 |
| `infixr`                        |  17 |  8 |
| `infixl`                        |  13 |  3 |
| `declare_syntax_cat`            |  14 |  3 |
| `attribute [macro …]`           |  11 |  6 |
| `notation`                      |   9 |  4 |
| `app_unexpander`                |   6 |  5 |
| `attribute [app_unexpander …]`  |   2 |  1 |
| `prefix` / `postfix`            |   0 | 0 |
| `macro` (a declaration)         |   0 | 0 |

17 files use at least one of the forms (12 use `macro_rules`/`notation`/
`attribute [macro]`; 15 without the plain infix operators). The `syntax` rules target
`tactic` 39 times, `term` 19, `doSeq` 9, `command` 3, `exBinder` 2 and 49 Feral DSL
categories. `prefix`/`postfix` and a `macro` command do not exist in the Lean host
either (a prefix operator is a `notation` whose first item is an atom; the host has only
`macro_rules`), so there is nothing to mirror.

**Implemented.** The frontend's `Note` is now a real macro rule — a node kind, a pattern
tree, a template and the argument names `notation` binds — and:
* `notation:p items => rhs` registers a leading rule (or, if the first item is an
  argument with a precedence, a trailing one, the host's `notationRule`); the pattern
  is the item list with `antiquot`s for the arguments, and the template substitutes them
  (`term.ident x` nodes for a `notation`'s `vars`, `$x` nodes for a `macro_rules`).
* `infixl`/`infixr`/`infix` build the same trailing rule and rule shape as the host
  (`a op b => f a b`), with `p`/`p+1` operand precedences; the kind comes from the
  host's `mkKindName` (`term.+`, `term.+_1`, …).
* `declare_syntax_cat`, `syntax` (with `(name := …)`, `(priority := …)`, `p`, the `stx`
  item grammar: atoms, categories with a precedence, `(...)`, `sepBy`/`sepBy1`,
  `withPosition`, `* + ?`), the meta parsers (antiquotations and `` `(c| …) `` for a new
  category) and `Wiz/Parser/SyntaxCmd.lean`'s leading/trailing split. Atoms are
  unreserved outside `term`/`command`, and a rule's atoms are added to the token table
  as the host's `ParserTables.addTokens` does.
* `macro_rules` with quotations, `$x` pattern variables, structural matching and
  hygiene: a template identifier the rule introduces gets a fresh `x✝N` scope, and
  `Scope.lookupV` falls back to the scope-stripped name for a global (the host's
  `stripScope`). The host has **no repetition** in patterns (`$[…]`), so neither has
  this.
* command macros written as `macro_rules` (a rule whose pattern is a `command` node
  expands before dispatch, so `def_one x` can stand for a `def`).
* `attribute [macro K] f` / `[tactic K] f` check that `f` is declared and record nothing
  (see below); `app_unexpander`, `attribute [app_unexpander …]` and
  `set_option pp.notation`/`pp.all` are parsed and accepted (their printing is the
  remaining half).

Expansion is outermost first: a node is rewritten to a fixed point (bounded per
position), then its children are expanded, so an argument a rule splices is expanded
like any other node. Tables change command by command, as they do in the host: the next
command is parsed with the rules declared by the previous ones.

**Not done.** The macro and tactic registrations name a *function* the host executes at
elaboration time (`ListLit.expand`, `Ex.binderMacro`, ring reification, Feral's whole
DSL). The self-hosted frontend has no elaborator-time evaluator, so it cannot run one:
`lib/Prelude.wiz`'s list literals, `Logic`'s `∃` and the ring macros would elaborate to
an "unsupported syntax" error. That is A12's other half, and it depends on the
elaborator-time evaluation that A11 and A13 also need. Printing notation
(`app_unexpander`) is accepted but `#check`/`#reduce` still print kernel terms; the
host's notation-aware printer (`Wiz/Core/Pretty.lean`) is not ported. Keyword scopes
(`declare_syntax_cat c (keywords := s)`) are accepted and the category is declared, but
the scope's reserved words are not tracked (only `lib/Feral.wiz` uses them, with a
procedural macro). `local notation`/`local macro_rules` are unwrapped and stay visible
to importers (A14's module-local dropping is not wired to the new rules).

**Tests** (new group `selfhost-macro`, 13 cases, added to the `selfhost` shard):
* notation/infix differential: `selfhostSameNats` compares what the Lean frontend's
  `#eval` and the self-hosted one's `#reduce` compute for `10 − 3 − 2` (5), `10 ⊖ 3 ⊖ 2`
  (9), `1 ⊕ 2 * 3` (7), `⌜1 + 2⌝` (4), `⌜⌜3⌝⌝` (5), the postfix `5 !` (10) and
  `5 ! !` (20), and the prefix `~3` (2) and `~ ~3` (3) — left/right associativity,
  precedence, a leading notation with a default and with an explicit argument
  precedence, and a trailing (postfix) rule.
* `macro_rules` differential: a `syntax:lead` rule, pattern variables, hygiene (`under e`
  = `let y := 3; e + y`, so `hyg 5` is 9 with hygiene and 7 without), a declared
  category with a rule of its own (`get ⟨7⟩` = 70, via a second expansion), and a
  command macro (`def_one one`).
* a `syntax` rule whose items are a `sepBy(term, ",")` and the macro rule that matches
  the `null` node and splices both elements (`pair(1, 2)` = 3).
* `syntax ... : tactic` rules (39 of the 123 in `lib/` target `tactic`), a `tactic`
  reference and a `(keywords := …)` category, accepted by both frontends.
* a second `infixl` on the Prelude's `+`: a fresh kind (`term.+_1`), and the later rule
  wins (`3 + 1` is 2 both places); `infix` (both operands `p + 1`) does not parse a
  chain (`1 ? 2 ? 3`) in either frontend.
* pinned diagnostics: a malformed rule, an unknown syntax category and an unknown
  registration name.
* the declarations a macro file produces in the self-hosted frontend (names and types).
* `app_unexpander`/`set_option` accepted by both frontends; the macro/tactic
  registrations accepted by the self-hosted one.
* two pinned differences (`selfhostVerdicts`): the host rejects a registration whose
  function has the wrong type and an unexpander whose pattern is not an application,
  while the self-hosted frontend only checks that the name exists.
* the same macro-using program compiled and run by **both** toolchains (`ioRun` and
  `selfhostCompileRun`), printing the same five lines — the terms the macros desugar to
  compute identically.

**Verification (2026-11-15).** The groups run on these sources: `=selfhost-macro`
**13 passed, 0 failed** (417 s) and `=selfhost` **143 passed, 0 failed** (2195 s),
including the self-check (28.3 s) and the repinned `#67`, which matches its new
expected output. The same cases were also exercised case by case with light probes
(`wiz check`/`wiz run` for the Lean frontend, the checker and compiler for the
Wiz-hosted one), and the macro-using program prints `25 2 1 9 71` from both toolchains.

## 21ad: tactics in the self-hosted frontend (A13, core)

`by` and `term.by` are now elaborated by the Wiz-hosted frontend, not rejected. The
engine is the host's (`Wiz/Elab/Tactic.lean`, `Wiz/Elab/Term.lean` `runTac`) in the
self-hosted surface: a goal is a context (`Cx`: names, types and values), an expected
type (`Val`) and a hole (`Tm`, the `MVarId` analogue — goals are numbered by position,
as in `TacState`), and a tactic script is an `STac` request tree (`op`, `seq`, `try`,
`first`, `repeat`) interpreted against a goal list and an elaborator state.

**Surface.** `by tac₁; tac₂ …` in a checking and in an inferring position. The core
tactics are `intro`, `intros`, `exact`, `apply`, `assumption`, `rfl`, `rw`/`rw ←`
(syntactic occurrence rewriting of the goal type, as the host's `abstractOcc`),
`change`, `unfold f, g` (one unfolding per definition; fails when nothing changes),
`calc`, `have`, `suffices`, `obtain ⟨x, y⟩ := e`, `constructor` (the first constructor
of the goal's type whose application succeeds), and `try`/`first`/`repeat`/`(…; …)`.
`constructor`'s siblings `cases`/`induction` are not in this milestone (they need the
match compiler's motive/recursor surface exposed to tactics). The tactic grammar is
built into the parser tables (`Wiz/Selfhost.lean` `selfhostTacticRules`, hence
`selfhost/Tables.wiz`), because the host gets it from `syntax … : tactic` declarations
in `lib/Prelude.wiz` and the self-hosted frontend does not run macro/tactic
registrations yet (21ac).

**Solved means solved.** A block makes one metavariable; a tactic's `exact`/`apply`/
`assumption` either closes its goal (its hole zonks) or replaces it. At the end of the
block the open list is filtered by zonk: a goal that a later argument's unification
determined is not reported. If any goal is left the command fails with
`unsolved goals:` and each goal's context, one hypothesis per line (`n : Nat`) and
`⊢ type`; a failed tactic additionally appends `remaining goals:` and the state it
failed in. A term `apply`/`assumption` assigns with holes is kept in an `unchecked`
list and its type is inferred and compared with its goal at the end of the block (the
host's `assign` path), so a hole cannot become a proof of the wrong thing; a solved
block is handed to the kernel as an ordinary term and checked as usual.

**Frequency in `lib/`.** A token scan of the `by` blocks in the 95 `lib/**/*.wiz` files
at this commit (comments and strings excluded, equation bodies included) finds **40
blocks / 47 tactic steps in 4 files**. The frequency order is:

| tactic | steps | files | note |
|---|---:|---:|---|
| `xgo` | 12 | 3 | Hoare/Eff custom tactic (`syntax … : tactic`) |
| `xstep` | 10 | 1 | custom |
| `xunfold` | 8 | 1 | custom |
| `xapp` | 5 | 1 | custom |
| `unfold` | 4 | 1 | built in, implemented here |
| `rw` | 4 | 1 | built in, implemented here |
| `rfl` | 4 | 1 | built in, implemented here |

The custom four are 35 of 47 steps and are declared with `syntax … : tactic` /
`macro_rules` and registered with `attribute [tactic …]`; they need the
elaboration-time evaluator that A12 has not ported, so they parse but have no meaning in
the self-hosted frontend (the error names the syntax kind). The parity matrix's "46
`lib` files use `by`" is a raw `\bby\b` grep that also matches the English word in
comments; the real proof blocks are in `HoareExamples`, `HeapBorrow`, `EffHeap` and
`ListLemmas`. That is why the top built-in form is `unfold`, and why it and `rw`/`rfl`
were the first ones implemented; `calc`/`have`/`suffices`/`obtain` are included for the
proof surface even though `lib/` does not use them as tactics yet.

**Tests.** `=selfhost` gains five cases: a real block (`intro`/`apply`/`assumption`), the
per-tactic cases (`intros`, `change`, `unfold`, `constructor`, `try`/`first`/`repeat`),
unsolved goals with their context, a tactic failure with the remaining goals, and the
differential. The differential case runs the same `ap` proof in the Lean and Wiz-hosted
frontends, and the same failing `rw` in both, comparing verdicts and the error text
(`rewrite: the goal does not mention c`). `=tactics` (the Lean host's group) is
unchanged and remains the host-side regression.

**Verification on this branch** (A12+A11+A13 merged; the self-hosted compiler built from
the current `selfhost/*.wiz`): all five A13 cases pass (`=selfhost` #147–#151), and
`=tactics` is 28/28. A full `=selfhost` run reached **112 cases, 0 failures** (and
#112–#114 also passed) before the machine restarted; the remaining tail was being
re-run when it restarted again, and the A13 cases were then re-checked individually. The
fixpoint was not run: `selfhost/*.wiz` does not use `by` yet, and the 6 GiB heavy slot
was not available; a fixpoint run is the remaining gate for the compiler's own sources.

**Limits.** No `simp`/`simp`-set management, no decision procedures (`decide`,
`omega`, `linarith`, `ring`, `bv_decide`), no `cases`/`induction` (and `constructor`
covers ordinary inductives only), no rewriting in hypotheses, no
`trace_state`/`rename_i`, no unfolding of a hypothesis, and no user tactic functions
(A12's evaluator). `unfold` replaces syntactic occurrences that are still in the goal
type (e.g. `List (F Nat)`); it cannot find one whose equation the kernel has already
whnf'd (the selfhost `vEq` reduces the sides of an equation where the host keeps the
written ones), so the exact `unfold List.filter` steps of `lib/ListLemmas` are not
guaranteed to match the host. The error position is the failed command, as for the rest
of the self-hosted diagnostics (D6), and the host's multi-line expected/inferred blocks
are not reproduced.

## 21ae: the library against the self-hosted compiler (`=selfhost-libdiff`)

The matrix above counts **features**; this measures the **library**. A new group,
`selfhost-libdiff`, runs both compilers on every `*.wiz` under `lib/` and `scry/` (the
file as a root module, its imports under `lib/`, `drafts/feral/lib` and the `scry/`
package roots) and compares

* **acceptance** (does the frontend report an error at all),
* the **code** of the first error (`ErrorCode` on the Lean side, the self-hosted
  driver's table on the other),
* its **span** (file, line, column),
* its **message** (whitespace-normalised; the driver's `[code]` suffix moved out), and
* the **number of declarations** the file produced.

The first divergence is reported per file. A file both compilers accept with the same
declaration count is `ok`; one both reject is `rejected` (the counts of the same code,
same span and same message are reported apart, because D6's positioning differs by
design); one whose verdicts differ is `diverging` — that is the gap list. A run that
hits the per-file time or memory bound is `bounded`, not a gap. That includes exit
status 3, the self-hosted runtime giving up (`wiz: out of memory` when an allocation
fails under the memory bound); the report carries its `wiz:` line.

The host side is the Lean frontend in a child process (`tests --libdiff-host FILE`, the
same `runFrontend` `wiz check` runs, with `Module.loadClosure`/`includeTable`/
`cSourceTable`/`preprocessHeaders` as `Main.initState` sets them), so the sweep can
bound it; its declaration count is the file's `declSites` in module `""` without a
structure's constructors, fields and projections, plus its `#check` info messages. The
self-hosted side is the compiler binary `selfhostCompiler` builds, `check FILE --types`:
its info lines are the per-declaration reports (a structure's projections dropped), so
the two counts are the same notion.

The files are found by walking the tree (not a list), `--only` takes a path, a path
suffix or a module name, and `--limit N` the first N — a work list, not a gate. To make
progress a diff rather than a number, `--baseline FILE` writes the current
`verdict/divergence/class` per file when the file does not exist, and reports
`fixed`/`regressed`/`changed`/`new` against it when it does. `--json` writes one record
per file (both sides: acceptance, exit, errors, decls, first error code/span/message;
plus the verdict, the first divergence, the missing construct and the note) and a final
summary record. `--timeout`/`--host-timeout`/`--self-timeout` (seconds) and `--mem`
(megabytes, the self-hosted side's `ulimit -v`) bound each file.

Usage:

```sh
heavy --mem 4G .lake/build/bin/tests --libdiff                 # everything
heavy --mem 4G .lake/build/bin/tests --libdiff --limit 10      # a first look
heavy --mem 4G .lake/build/bin/tests --libdiff --only lib/Hoare.wiz
heavy --mem 4G .lake/build/bin/tests --libdiff --json > gap.jsonl
heavy --mem 4G .lake/build/bin/tests --libdiff --baseline libdiff-baseline.json
heavy --mem 14G .lake/build/bin/tests --libdiff --jobs 3       # three files at a time
lake test -- '=selfhost-libdiff'                               # the same, as a group
```

The group skips (a skipped case is not a pass) when there is no C toolchain for the
self-hosted compiler, and never fails because of a gap; it writes the full report to
`.lake/libdiff/` (`records.jsonl`, `summary.txt`), because the harness hides a passing
case's output. CI runs it as its own shard (`selfhost-libdiff` in
`.github/test-shards.json`).

The sweep is one case, because building the self-hosted compiler takes minutes and
every file needs it, so it is split inside the case: `--jobs N` (on `tests --libdiff`, or
the driver's `--jobs N`, which a group that runs its cases one at a time passes on to
them; in CI the shard's `"jobs"`) checks N files at a time. The workers take the files off
one list, each exactly once, and the records come back in the files' order, so the
report, the verdicts and the baseline signatures are a sequential sweep's. Each file
keeps its own bounds, which start when its run starts. What could change a verdict is
an oversubscribed machine, so the workers are capped by the CPUs (`nproc`) and by the
free memory at `--mem` per file: the least of `MemAvailable` and each enclosing cgroup's
`memory.max` minus `memory.current`, so a `heavy --mem 7G` job runs one file at a time
and a 16 GB runner three. A worker also starts its next file only while that much memory
is free or no other file is running. The summary reports the slowest host and
self-hosted runs (and `ms` per side in the records), the margin to the 60 s and 120 s
bounds.

`--only` and `--limit` make it usable as the A13 work list: the gap list groups the
files whose verdicts differ by the construct the self-hosted frontend names
(`unsupported syntax term.by` is `by`, `unsupported command command.syntax` is `syntax`,
…), and prints the ten files to start with (most common construct first).

## 21ag: `Bytes`, self-hosted (C11)

`Bytes` (9d/9k, `lib/IO.wiz`) now checks and compiles in the self-hosted toolchain.

* **Prelude** (`Frontend.wiz`, `preludeText`). `axiom Bytes : Type` and the nine
  operations the Lean toolchain declares as `extern`s (`Bytes.empty`, `push`, `size`,
  `get`, `ofString`, `toString`, `slice`, `append`, `eq`), plus the pure helpers
  `isEmpty`, `at`, `take`, `drop`, `ofList`, `toList`, `singleton` and `show`, copied
  from `lib/IO.wiz` so the same program checks in both toolchains. The operations are
  runtime natives (`bytesNatives`, added to `nativeNames`), as `Array`'s are.
* **Runtime** (`rt.c`). `wiz_bytes` with `runtime/wiz_rt.h`'s layout (the header, then
  `len`, `cap`, `data`; a static assert keeps them equal), the nine `get_Bytes_46_*`
  natives, and `rt_bytes_new` for a struct field. `push` and `append` update in place
  when the buffer is unique (reference counting), as `runtime/wiz.c` does; under the
  collector there is no reference count, so they copy instead (a shared buffer must not
  change: `Bytes` is functional). The storage is freed with the object (a copy's old
  buffer becomes garbage), and the bytes are not Wiz values (the collector and the leak
  check ignore them).
* **`import_c` and `glue`** (`Frontend.wiz`, `Backend.wiz`). A C `const void *buf,
  size_t n` (or `const unsigned char *` and a length parameter named `n`, `__n`, `len`,
  `__len`, `nbytes`, `__nbytes`, `length` or `__length`) is one `Bytes` parameter (FFI
  kind `y`), as in `Elab/Command.lean`. The backend passes the buffer's `data` and `len`
  as the two C arguments, releases the buffer after the call, and writes both in a
  prototype. A `c_struct` field of type `Bytes` (with a header) is kind `y` too:
  `wiz_sin_*` copies the buffer into the C array (cut or zero-padded to the array's
  size) and `wiz_sout_*` makes a `Bytes` of the array's size. `glue` does not see such
  a field (as in the Lean frontend) but sees a buffer function's two C parameters.
  An imported function's parameter keeps its own Wiz type name: a `c_struct`
  parameter gets the declared structure's name, not the C parameter's name (the C name
  is only needed to recognize a buffer's length parameter). Glue calls are also checked
  in source order now (`CGlue.wiz` collected the argument types backwards, which only a
  call with differently typed parameters, such as a buffer's pointer and length, shows).

**Tests** (group `selfhost`): every operation, including sharing (a `push` or `append`
that leaves the old buffer alone), compiled by the Lean toolchain and by the
self-hosted one (collector and reference counting, which also checks for leaks);
`import_c` with a buffer argument and a struct with a byte-array field passed to C and
read back; and a `Bytes` `c_struct` field without a header rejected by both frontends.

**Then** (the same stage, extended): the encodings (`ofUtf8`/`toUtf8`, `ofLatin1`/`toLatin1`,
with `Except` added to the Prelude), `ofString`/`toString` with the C-string rule,
`Bytes.ofArray`/`toArray` (in `Std`, where `Array` is) and a **model** for `#reduce`:
`Bytes` is a private constructor over a `List Nat` in the Prelude, so `#reduce
Bytes.size (Bytes.ofList …)`, `Bytes.eq`, `Bytes.get`, `Bytes.slice` and `Bytes.toList`
compute and print in the checker's usual constructor style; the nine names are still in
`nativeNames`, so compiled code is unchanged (the definitions' bodies are never
compiled, and no constructor value can be built outside them). A buffer pointer may also
be spelled `char *` (with a length), `unsigned char *` or `signed char *`/`uint8_t *`
(typedef-resolved), and a `c_struct` parameter is now a `gstruct` in `glueGtyOfKind`
(it was `.gint`, so glue could take a struct but the C parameter was wrong). The
borrowed/owned rule and the struct-field copy are in `docs/stages/09-ffi.md` 9l.

**Tests** (group `selfhost`): the encodings, `Array ↔ Bytes` and the
slice/append/eq boundaries, a `char *`/`uint8_t *`/`unsigned char *` buffer argument
(borrowed: the buffer is used after the call) and a `Bytes` `c_struct` field through
`glue` (passed to C and returned), each compiled by the Lean toolchain and by the
self-hosted one (collector and reference counting); `=ffi` has `#eval`/`#run` of the
operations in the host interpreters.

**Not done:** `Bytes.ofU8s`/`toU8s` (`lib/WordBytes.wiz`, no `U8` in the Prelude),
`U8Array ↔ Bytes` (29), byte I/O on files and descriptors (`FS.readBytes`,
`File.readBytes`, `Fd.read`), and the rest of the native surface (22l/29).

## The two preludes, and the drift check

`import Prelude` names two different values depending on which compiler reads it.

**The host copy.** `lib/Prelude.wiz` (1,574 lines, hand-written) is the library's
prelude. `wiz` reads the `lib/` next to its binary (`Wiz/Module.lean:163`,
`Module.toolchainLib`); the Nix package stages the checkout's `lib/` into
`share/wiz/lib` with a plain copy (`flake.nix:94`), so the installed file is the same
bytes as the source — a staged copy, not a second one that can drift. `Tests/`, the
documentation examples and `wiz check` all see this one (the `check-prelude` corpus
entry in [building.md](../building.md#the-wiz-memory-corpus) is `wiz check
lib/Prelude.wiz`).

**The embedded copy.** `selfhost/Frontend.wiz:7488` defines

```wiz no-check
def preludeText : String := "inductive Nat where\n…"
```

a single-line Wiz string literal (352 lines, about 16 KB when decoded;
`scripts/check-prelude-drift.py --dump-embedded` prints it). It is hand-written from
stage 19a, not generated. The self-hosted module loader substitutes it for every
`import Prelude` (`Frontend.wiz:9210`) and canonicalises `IO`, `Std` and `Sys` to it
(`Frontend.wiz:8963`–`8967`); the comment at `Frontend.wiz:8889` is explicit: "the
self-hosted prelude is what this frontend can check, not `lib/Prelude.wiz`".

**The page's copy is the embedded one.** `web/build-playground.sh` concatenates
`frontendFiles` from `Wiz/Selfhost.lean:123` (which includes `Frontend.wiz`) into the
Wasm engine, and `web/selfhost-lsp-shim.js:68` prepends `import Prelude` to a program
that has no import. There is no third copy under `web/`: the page runs `preludeText`.
The drift check fails if a `web/**/*prelude*.wiz` ever appears, because that would be a
copy it does not compare.

### The divergence, demonstrated

The two are a subset and a superset at once.

* The page is **ahead** of `import Prelude` on the host for two names: `List.map`
  (`lib/Text.wiz:45`) and `String.length` (`lib/Text.wiz:191`) are in the embedded
  prelude, so with only `import Prelude` a page program accepts them and `wiz check`
  rejects them:

  ```text
  $ wiz check maptest.wiz
  maptest.wiz:3:39: error: unknown identifier 'List.map'
  maptest.wiz:4:31: error: unknown identifier 'String.length'
  ```

  (with `wiz 0.1.0-dev (aeaa34ef…)`). `import Text` makes the host accept them. The
  page's Wasm engine is the mirror image: `#check List.map` gives a type, and
  `#check Nat.subFrom` gives `error: unknown identifier Nat.subFrom`. So the roadmap's
  example has the direction reversed: the playground tour's `List.map` works on the
  page and is exactly what `wiz check` rejects. The tour file itself is on an unmerged
  playground branch, not on `master`.

* `Nat.blt` is the sharper case: `lib/Prelude.wiz:174` registers
  `builtin nat.blt := Nat.lt`, but the host has no identifier `Nat.blt` (`#check`
  rejects it; "did you mean `Nat.lt`"). The embedded prelude defines one, so the page
  accepts a name the library does not have.

* The page is **behind** on the library's runtime surface: `Nat.subFrom`
  (`lib/Prelude.wiz:89`), `Nat.powFrom` (221), `pipe` (140), `outParam` (331),
  `castRefl` (37), `Eq.cast`/`Eq.subst`/`Eq.substBack` (45, 52, 55) and all 27 classes
  (283–475) are not in `preludeText`. A `lib/` file that uses them is one of
  `selfhost-libdiff`'s gaps. This is partly deliberate: the embedded prelude is a
  model, its arithmetic is monomorphic (`infixl " + " => Nat.add`), where the host has
  `HAdd`/`Add` and instances.

The checker reports 71 runtime declarations in `lib/Prelude.wiz`, 40 of them embedded,
23 classes, and 8 reviewed gaps. `preludeText` has 162 names: 147 are also declared
under `lib/`, 15 are reviewed embedded-only names (the `Bytes` model's helpers, `Prod`
and its projections, `String.data`, `Nat.blt`). 87 names are *promoted*: the page
offers them with `import Prelude`, while the host declares them in `lib/IO.wiz` (66),
`lib/Std.wiz` (17), `lib/Sys.wiz` (2) or `lib/Text.wiz` (2, the two above).

### The check

`scripts/check-prelude-drift.py` compares the **semantic surface**, not bytes. Bytes —
or a hash of either file — would fail forever, because the copies are not meant to be
equal: one is a class/notation/metaprogramming library, the other a monomorphic model
for a frontend that has none of those. A checked-in hash is the right comparison only
for a *generated* file, and there is no generator, because one would have to elaborate
the host prelude first.

The script parses `lib/Prelude.wiz` (declarations, inductive constructors, structure
and class fields; the line `-- (end of the Boolean section)` at line 479 separates the
runtime surface from the metaprogramming layer) and the decoded `preludeText`, then
enforces three invariants:

1. **coverage** — every runtime `def`/`axiom`/`extern`/`inductive`/`structure` is in
   the embedded copy with the same kind and the same constructors and fields, unless
   it is in the script's `EXEMPT` list with a reason. A PR that adds a value
   declaration to `lib/Prelude.wiz` without touching the embedded copy fails here.
   (Classes and notation are out of scope by design: the embedded prelude defines a
   fixed set of infix operators and no classes.)
2. **origin** — every name in `preludeText` is declared somewhere under `lib/`, or is
   in `EMBEDDED_ONLY` with a reason. The page cannot invent library surface, and a
   private helper added to the embedded copy needs a reviewed entry.
3. **staleness** — an `EXEMPT`, `EMBEDDED_ONLY` or `META_ROOTS` entry that matches
   nothing is an error, so the lists cannot rot into a blanket exemption. `META_ROOTS`
   is the set of namespaces after the runtime marker; it makes appending a declaration
   at the end of the file a reviewed decision instead of an escape from coverage.

Run it with `python3 scripts/check-prelude-drift.py`. It takes well under a second and
needs only Python 3. `--self-test` runs ten fixtures (a clean pair, a new library
name, an invented embedded name, a runtime declaration appended after the marker, a
changed kind, a lost constructor, a stale and a matching exemption, and a redundant
`EMBEDDED_ONLY` entry); `--verbose` lists every name, `--dump-embedded` prints the decoded
prelude, `--root DIR` checks another checkout. CI runs `--self-test` and then the check
in the `prelude_drift` job (`.github/workflows/ci.yml`), and `CI result` requires it. A
failure names the line and the remedy:

```text
[coverage] lib/Prelude.wiz:182: def Nat.flatMap is not in preludeText
(selfhost/Frontend.wiz:7488). Add it there, or add a reviewed EXEMPT entry with a
reason in scripts/check-prelude-drift.py.
```

### What the real fix costs

The destination is one prelude: the self-hosted compiler loads the library's own
`lib/Prelude.wiz`, and the page embeds that same text instead of a second model. Three
routes, cheapest first:

1. **Extract the literal to `selfhost/Prelude.wiz`, and generate the string from it.**
   `include_str` exists in the host but not in the self-hosted frontend
   (`selfhost/Frontend.wiz` has no `term.includeStr`;
   [dogfood notes](../notes/dogfood-new-features.md) item W7 is this extraction), so the
   embedding has to happen where the selfhost sources are assembled. The repo already
   has the pattern: `scripts/GenSelfhostTables.lean` writes `selfhost/Tables.wiz`, a
   checked-in generated source that the `selfhost` group fails when stale. A small
   generator can instead write `selfhost/PreludeText.wiz` — the escaped literal — from
   a hand-maintained `selfhost/Prelude.wiz`; the source list gains that file before
   `Frontend.wiz`, and `web/build-playground.sh` picks it up through `frontendFiles`
   with no change. About a day: the generator, the lake target, the staleness test, and
   moving 352 lines. The drift check then compares two real files. The bootstrap
   identity changes (`toolchainId` hashes the sources), so caches go cold and the
   fixpoint must be rerun. This does not make the two preludes equal; it makes the
   second one readable, diffable, and still checked.
2. **Load `lib/Prelude.wiz` through the `-I` roots (`--prelude-from-roots`).** This is
   the real fix for the native compiler. There is a working opt-in for stage 21af on an
   unmerged branch (669 lines in `Frontend.wiz`, 55 in `Cli.wiz`, 134 test lines and a
   doc section). It is blocked by three elaboration gaps in `lib/Prelude.wiz` itself (a
   constructor field of function type returning the type being defined, `×` in a
   constructor field, a class field in `Type 1`), by `outParam` and default instances,
   and by the Backend not knowing the library's externs and builtins. Cost: that branch
   plus those fixes, and a re-run of `selfhost-libdiff` until `lib/` checks; weeks, not
   days. It also cannot fix the page by itself: Wasm has no filesystem, so the browser
   still needs the prelude text embedded at build time — the same splice as (1), but
   reading `lib/Prelude.wiz`.
3. **A checked-in generated file with a hash.** Only meaningful if a generator can
   produce the embedded subset from `lib/Prelude.wiz`; today it cannot, because the
   frontend cannot elaborate the host prelude. A hash of `lib/Prelude.wiz` in
   `selfhost/Frontend.wiz` would pin an input to a copy that still has to be maintained
   by hand. The surface check above is the honest version of that idea.

Recommendation: keep the check (this change); do (1) next, so the embedded copy is a
reviewable source file; do (2) when the 21af blockers land, and make the page embed
`lib/Prelude.wiz` at build time. Only then is `selfhost-libdiff` on a prelude-only
change a pure no-op.

**Not covered.** Signature and body drift under the same name (the embedded `Nat.sub`
recurses on a different argument than the host's), notations and operator precedence,
and the class/instance layer (a new class or notation in the host prelude does not fail
the check). Those need elaboration, not a regexp; `selfhost-libdiff`
measures their consequences, and the check's report names the known gaps on every run.
