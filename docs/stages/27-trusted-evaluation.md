# Stage 27: trusted evaluation

The kernel decides every equation itself, by evaluation (`refl`). For a closed equation
about a long computation (a circuit simulated for thousands of cycles, a table of every
byte) that takes minutes to hours. Compiled code computes the same thing in seconds; this
stage lets a proof use it, **behind a flag, as an axiom that says what it trusts**, like
Lean's `native_decide` (`Lean.ofReduceBool`).

## 27a: `native_refl` and `--trust-native`

    def Loop.all256 : allBelow 256 (Loop.ok 104 1100) = .true := native_refl

`native_refl` is accepted only

* with **`--trust-native`** (`wiz check`, `build`, `run`, `lsp`; `grail build`, `check`,
  `test`, `lsp`, which passes it on to its jobs and to the `wiz lsp` it starts). Without
  it: "native evaluation is not enabled …". It is off by default and is a flag only, not
  a setting of `grail.local.wiz`: trusting the compiler is a decision per run;
* as the **whole body of a definition** with a type and no parameters or universe
  parameters, whose type is an equation `a = b` between closed terms;
* at a **first-order data** type: inductive data, enumerations, `Unit`, pairs and
  structures, numbers, words (`UIntN`, `BitVec`, through their native representation's
  model). Functions, codata, types and erased (quantity-0) fields that are not proofs
  are refused. An erased proof (a constructor's index equation, a word's range proof
  `Nat.lt n (2^w) = .true`) is not at run time: the read-back builds it, from `Unit`,
  `ULift`, equations that hold and pairs, and the kernel checks it (conversion ignores
  proofs, so any proof is as good as the erased one). Foreign constants (`extern "f" c : Nat`)
  have no value here and are an error.

**How it is decided** (`Wiz/Compiler/Native.lean`). `a` and `b` are erased with the
definitions they reach (as for `#eval`, with the models of foreign functions), and both
run in `#eval`'s interpreter, in a variant with a step limit and errors instead of
`panic!` (`Wiz/Compiler/NativeRun.lean`; `--native-fuel N`, default 2·10¹⁰ steps:
"native evaluation did not finish within N steps"). Each result is read back
**strictly** as a closed term of the type: anything that is not a value of the type's
shape is an error, never a default. The kernel then type-checks both read-back terms and
compares them with `conv` (two normal forms of data: cheap). `b` need not be a literal.
A definition that can't be erased, or a partial definition (whose implementation is
unchecked and may diverge), is an error.

**What it records.** `def X : a = b := native_refl` adds the axiom **`X.native✝ : a = b`**
(an inaccessible name: nothing else can declare it) and `X := X.native✝` (below), with a warning.
`#print axioms X`, and of everything that uses `X`, lists `X.native✝` with a note, and the
native implementations the computation can reach (`native f := g` for `implemented_by`,
`builtin k := f` registered outside the library, axioms): `X`'s value mentions the
`implemented_by` targets the run reached (erased `let`s), so their own dependencies are
listed too. A use of `X` never evaluates anything again. In general `#print axioms`
follows what compiled code runs through every trusted step (t1-review L2): a whole
`implemented_by` chain, and an implementation that is a partial definition through its
body (and the bodies of the partial definitions that body runs).

**What is trusted** (the kernel checks none of it): erasure and the rewrites on erased
code, the interpreter (`NativeRun`) and Lean's natural numbers under the `builtin nat.*`
operations, and every `implemented_by`, `builtin` registered outside `lib/` and native
representation the computation reaches. Not trusted, because none of them runs: the IR
and its optimisations, the C backend, the C runtime, the C compiler. Since PR #126 the
compiled equations of recursive definitions are not trusted either: the kernel checks
that they agree with the definitions (`checkImplAgrees`). A wrong `implemented_by` does
prove a false equation (group *native* has one), and `#print axioms` names it.

**Not evaluating the statement.** The kernel's equality computes: evaluating the type
`a = b` computes both sides (`vEq`; F5 of `wiz-notes/kernel-eval.md`). So the statement is
checked without being evaluated: `X.native✝`'s type is checked to be a well-formed type
(`a b : T`, by inference), its sorts are filled without evaluating it, and `X`'s header is
checked the same way, its value `X.native✝` being at that very type (the constant rule; the
kernel would check it by evaluating the type). **A use of `X`** where the kernel evaluates
an expected type that is the equation (an argument at `h : allBelow n p = .true`) still
computes it, until equation types are glued (P1 of the kernel-eval note): native_refl
pays off for composed proofs only with that.

**The library never uses it**: group *native* greps `lib/` and checks that no library
declaration depends on a `.native✝` axiom (and `lib/` is never checked with the flag).

**The cache.** What ran is already in a command's key (the binary's hash, the text of the
file and of every module it imports, the C headers). The flag and the step limit are mixed
into the keys too (the command chain, every module key, grail's `check` jobs), so an
acceptance is never replayed without the flag, nor the error without it replayed with it.
The first run with the flag elaborates the imports again.

**The self-hosted toolchain** has no native evaluation and no flag. The grammar entry
reaches its parser only through the tables generated at build time from the Lean parser's
(`Selfhost.wizTables`; it is not in `selfhost/Parse.wiz`), so it rejects `native_refl`
either as "unsupported syntax term.nativeRefl" or as an unknown identifier (not run here;
either way it fails closed). It checks sources itself and never receives the Lean
toolchain's declarations, so it never sees a `.native✝` axiom; if it did, it would be an
ordinary axiom.

**Why the interpreter, not the C backend.** The interpreter runs in the (pure) frontend,
needs no C compiler and no process, and keeps the IR, reference counting, the C runtime
and the C compiler out of the trusted base. The IR interpreter (`#run`) is a checked-heap
test harness, slower and fuelled for tests. Compiled code would be faster again (the
UART's 256 bytes at divider 104 run in about a second compiled); a later
`--trust-native=c` could add it behind the same axiom.

Tests: group *native* (accepted with the flag, a 20 000-step word computation, refused
without it, a false equation refuted, non-first-order types refused, only as a closed
definition's body, `#print axioms`, a wrong `implemented_by`, partial definitions, the
step limit, the flags and grail's keys, the cache across the flag and across a changed
import, `lib/`). Design: `wiz-notes/native-refl.md`.
