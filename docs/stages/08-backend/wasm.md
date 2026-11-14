# A WebAssembly target (prototype)

`wiz build FILE -o OUT --wasm` emits a **binary WebAssembly module** for an IO-less
`main`, and `wiz run FILE --wasm` builds it and runs it under Node. This is an additive
prototype: the C (`Compiler/C.lean`) and LLVM (`Compiler/LLVM.lean`) backends are
unchanged, the C toolchain is not used, and nothing in the existing pipeline depends on
it. There is no Emscripten step: `Wiz/Compiler/Wasm.lean` writes the module's sections
and instructions directly.

```
$ wiz run examples/... --wasm     # prints the result like `wiz run`
$ wiz build file.wiz -o out.wasm --wasm
$ node web/wasm-host.mjs out.wasm # same result, from the checked-in host
```

The module is self-contained for values, closures, constructors and arrays. The one
external piece is `web/wasm-host.mjs`, which supplies **big integers** (the C runtime
uses GMP) as JavaScript `BigInt`s and decodes the result in the same generic tree syntax
as `runtime/rt_sys.inc`'s `wiz_print` (`(tag fields…)`, a number, `<fn>`). The result is
therefore read back by `wiz run` with `main`'s type exactly as the C and LLVM backends'
results are.

## What it supports

The prototype covers the part of the language the playground needs:

* an **IO-less `main`** of any type whose values the runtime can build: `Nat`, `Int`
  (constructors over `Nat`), lists, trees, `String` *as algebraic data*, and functions
  (printed `<fn>`);
* **`Nat`** at every size: small scalars (62 bits) in the module, larger values through
  the host's `BigInt`; the operations `succ`, `pred`, `add`, `sub`, `mul`, `div`, `mod`,
  `pow`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, `log2`, `beq`, `blt`;
* constructors and fields, `case` on tags, `dup`/`drop`, `reset`/`reuse`, `dropMoved`;
* direct calls, closures (`pap`/`ap`, partial and over-application), `memo`/thunks,
  `lazyTag`/`lazySet` for codata;
* `join` points (each join body becomes its own Wasm function taking its parameters);
* `Std`'s **`Array`** externs (`empty`, `push`, `size`, `getD`, `set`), functionally
  (updates copy, so sharing is unobservable).

Everything else is rejected when the module is emitted, with a message naming the
foreign function or primitive: `IO`, `Std`'s native `Str`/`StrMap`, `Bytes`, machine
words, the FFI, threads, files, and the rest of `runtime/rt_sys.inc`.

## How it works

A value is an `i64`. Bit 0 set means a scalar (a small number, a tag, `◾`); otherwise the
low 32 bits are a pointer to an object in linear memory: a 16-byte header `{rc, tag,
size}` (the C layout) and `i64` fields. Tags are the C runtime's (`0xFFFF0000` closures,
`0xFFFF0001` big numbers, `0xFFFF0005` arrays, `0xFFFF0008` thunks).

* **Functions**: each IR declaration is a Wasm function with one `i64` parameter per IR
  parameter, plus a *boxed* wrapper `(i32 args) -> i64` for closures. The wrappers are the
  funcref table; a closure stores the table slot, its arity, and its captured arguments.
  `wiz_apply` copies and concatenates arguments, builds a new closure when the
  application is partial, and `call_indirect`s the wrapper when it is complete (then
  applies any extra arguments).
* **Join points** are lifted: a `jmp` calls the join's function and returns its value.
  This keeps the emitted code structured without a relooper; unlike a loop it does not
  reuse a stack frame, which is fine for the non-tail `case` continuations the lowerer
  produces.
* **Memory**: addresses 8–2056 are a scratch buffer for call arguments (`pap`/`ap`),
  big literals' decimal text starts at 4096, and the heap follows it. A bump allocator
  grows memory a page at a time. `dup`/`drop` are no-ops: a run's peak memory is
  everything it allocates.
* **Big numbers**: a `Nat` above `2^62 - 1` is a `BIG` object whose single field is a
  host handle `2^63 | (index << 1)`. The host's `BigInt` table implements the operations
  (`big_op`), comparison (`big_cmp`), `log2`, decimal conversion, and construction from
  a literal's digits. A result below `2^62` comes back as a scalar, so the representation
  is canonical.

The five host imports are `big_of_dec`, `big_op`, `big_cmp`, `big_log2` and
`big_to_dec`; the module exports `memory`, `wiz_main` (the IR's `wiz.entry`) and three
decoders (`wiz_value_tag`, `wiz_value_field`, `wiz_big_digits`). The Wasm runtime is 44
functions (`runtimeNames` in `Wiz/Compiler/Wasm.lean`).

## Limits

These are deliberate for a prototype; none of them affects the C or LLVM backends.

* **No reference counting.** `dup`/`drop` are no-ops and the allocator never frees;
  memory grows with total allocation. A long-running or allocation-heavy program will
  run out of linear memory (the module grows it until the engine's limit).
* **No closed-definition caching.** A zero-argument definition (`def c : Nat := …`) is
  recomputed at each use rather than cached as the C runtime's CAF path does. It is pure,
  so the result is the same; only work and sharing differ (`memo` still shares inside one
  use).
* **No tail calls.** Deep *non-tail* recursion and join chains use the engine's stack;
  Node's default Wasm stack handles thousands of frames, not the C runtime's 1 GB. A
  self tail call in the IR is still a direct call here (there is no tail-call proposal in
  the module), so a loop written as tail recursion can overflow a deep input.
* **No IO or FFI.** `main` must not be `IO`; foreign functions other than the five
  `Array` externs are compile errors. Native `String`/`Bytes`/`StrMap`/`WordArray`/
  `WordMap`/`Intern` operations, machine words, threads and POSIX are not implemented.
* **Call arguments** are copied through a 256-slot scratch buffer: a `pap`/`ap` with more
  than 256 arguments is a compile error. (Direct calls are not limited.)
* **Big integers** live in the host: shifting by or exponentiating to an enormous number
  throws a `RangeError` (the C runtime panics or allocates), and the host table keeps
  every big value it has produced (small intermediates are reclaimed only by the GC of
  the JS numbers, not by the module).
* **Not a library target.** `--wasm` builds a `main`; `--lib`, `--no-main`, `--split`
  and export wrappers are not wired to it. The C/LLVM flags (`--cc`, `--cflags`,
  `--ldflags`, `--gmp`) are ignored.
* The host is checked in and must be present to *run* a module
  (`web/wasm-host.mjs`); a browser or another host can instantiate the module itself by
  providing the five `env` functions.

## Tests and counts

`Tests/Groups/Wasm.lean` is the `wasm` group (`lake test -- wasm`): **11 cases** covering
big `Nat` arithmetic, small numbers/division/powers/bits, closures, join points,
`memo`, closed definitions, `Array`, `Int`, strings-as-data, rejection of an `IO` main,
and rejection of an unsupported foreign function. Each case compiles the program, checks
the `\0asm` magic, runs it under Node with `web/wasm-host.mjs`, and compares the value
read back with `main`'s type. The cases **skip** when `node` is not on the `PATH` or the
host file is missing (as the C tests skip without GMP). The host is spawned without
Lean's `LD_LIBRARY_PATH`, which `lake test` sets and which shadows the system `libgcc`
for Node.

Smoke commands (from a checkout, after `lake build wiz`):

```
$ ./.lake/build/bin/wiz run file.wiz --wasm
$ ./.lake/build/bin/wiz build file.wiz -o /tmp/m.wasm --wasm
$ node web/wasm-host.mjs /tmp/m.wasm
```
