# A WebAssembly target

`wiz build FILE -o OUT --target wasm` emits a **binary WebAssembly module** for an
IO-less `main`, and `wiz run FILE --target wasm` builds it and runs it under Node. The
older spellings `--wasm` (and `--llvm` for LLVM) still work; `--target` is the same
selector the other backends use. (`grail build` is a package-level builder and remains on
C; `wiz build`/`wiz run` are where a backend is selected.) This backend is additive: C
(`Compiler/C.lean`) and LLVM (`Compiler/LLVM.lean`) are unchanged, the C toolchain is not
used, and nothing in the existing pipeline depends on it. There is no Emscripten step: `Wiz/Compiler/Wasm.lean`
writes the module's sections and instructions directly.

```
$ wiz run FILE --target wasm          # prints the result like `wiz run`
$ wiz build FILE -o out.wasm --target wasm
$ node web/wasm-host.mjs out.wasm     # same result, from the checked-in host
```

The module is self-contained for values, closures, constructors and arrays. The one
external piece is `web/wasm-host.mjs`, which supplies **big integers** (the C runtime uses
GMP) as JavaScript `BigInt`s and decodes the result in the same generic tree syntax as
`runtime/rt_sys.inc`'s `wiz_print` (`(tag fields…)`, a number, `<fn>`). The result is
therefore read back by `wiz run` with `main`'s type exactly as the C and LLVM backends'
results are. The host is checked in and is the only thing needed to *run* a module; a
browser or another host can instantiate the module itself by providing the five `env`
functions below.

## The supported subset

The boundary is enforced when the module is emitted: an unsupported construct is an
error naming the foreign function or primitive, never silently wrong code. The supported
programs are:

* an **IO-less `main`** that is a value, of any type whose values the runtime can build:
  `Nat`, `Int` (constructors over `Nat`), lists, trees, `String` *as algebraic data*, and
  functions (printed `<fn>`); there is no command-line argument passing;
* **`Nat`** at every size: small scalars (62 bits) in the module, larger values through
  the host's `BigInt`; the operations `succ`, `pred`, `add`, `sub`, `mul`, `div`, `mod`,
  `pow`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, `log2`, `beq`, `blt`;
* constructors and fields, `case` on tags, `dup`/`drop`, `reset`/`reuse`, `dropMoved`;
* direct calls, closures (`pap`/`ap`, partial and over-application), `memo`/thunks,
  `lazyTag`/`lazySet` for codata;
* **join points** (each join body becomes its own Wasm function taking its parameters);
* `Std`'s **`Array`** externs (`empty`, `push`, `size`, `getD`, `set`), functionally
  (updates copy, so sharing is unobservable).

Everything else is **rejected at compile time**: `IO`, `--lib`/`--no-main`/`--split`,
`Std`'s native `Str`/`StrMap`, `Bytes`, machine words (`UInt64`, `Float64`), the FFI,
threads, files, exceptions, and the rest of `runtime/rt_sys.inc`.
The check also catches an unresolved call, a call with the wrong arity, an out-of-scope
variable, a `jmp` to a missing join point, a constructor tag that does not fit the
encoded `i32`, and a `pap`/`ap` with more than 256 arguments. A `--target wasm` build with `--lib` or `--no-main` is an error
rather than a silently different artefact.

## Validation

`Wiz/Compiler/WasmValidate.lean` is a structural validator with no external tools: it
parses the binary module (magic/version, section order and lengths, types, imports,
functions, tables, memories, globals, exports, elements, data, start), checks the
cross-references and offsets, and type-checks every function body against an operand
stack with `block`/`loop`/`if` frames, branch depths, locals, calls,
`call_indirect`, memory accesses and alignment. It is an **encoder-side** validator: it
knows the instruction subset this backend emits and rejects an unknown opcode.

`Build.compileWasm` runs it on every module before writing the bytes, so an encoder bug
is a compile error (`internal error: the Wasm backend emitted an invalid module: …`),
not an engine rejection later. The test group also damages valid bytes (bad magic, a
truncated module, an unknown section id) and requires the validator to reject them.

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
  applies any extra arguments). A thunk's arguments are copied out of the scratch area
  before it is forced, so a thunk body's own applications cannot overwrite them.
* **Join points** are lifted: a `jmp` calls the join's function and returns its value.
  This keeps the emitted code structured without a relooper; unlike a loop it does not
  reuse a stack frame, which is fine for the non-tail `case` continuations the lowerer
  produces.
* **Memory**: addresses 8–2056 are a scratch buffer for call arguments (`pap`/`ap`), big
  literals' decimal text starts at 4096, and the heap follows it. A bump allocator grows
  memory a page at a time. `dup`/`drop` are no-ops: a run's peak memory is everything it
  allocates.
* **Big numbers**: a `Nat` above `2^62 - 1` is a `BIG` object whose single field is a
  host handle `2^63 | (index << 1)`. The host's `BigInt` table implements the operations
  (`big_op`), comparison (`big_cmp`), `log2`, decimal conversion, and construction from a
  literal's digits. A result below `2^62` comes back as a scalar, so the representation
  is canonical.

The five host imports are `big_of_dec`, `big_op`, `big_cmp`, `big_log2` and
`big_to_dec`; the module exports `memory`, `wiz_main` (the IR's `wiz.entry`) and three
decoders (`wiz_value_tag`, `wiz_value_field`, `wiz_big_digits`). The Wasm runtime is 44
functions (`runtimeNames` in `Wiz/Compiler/Wasm.lean`).

## Limits and what remains

These are deliberate for this target; none of them affects the C or LLVM backends.

* **No reference counting.** `dup`/`drop` are no-ops and the allocator never frees;
  memory grows with total allocation. A long-running or allocation-heavy program will
  run out of linear memory (the module grows it until the engine's limit). This is the
  main remaining piece for general use: a collector or a real `dup`/`drop` counter.
* **No closed-definition caching.** A zero-argument definition (`def c : Nat := …`) is
  recomputed at each use rather than cached as the C runtime's CAF path does. It is pure,
  so the result is the same; only work and sharing differ (`memo` still shares inside one
  use).
* **No tail calls.** Deep *non-tail* recursion and join chains use the engine's stack;
  Node's default Wasm stack handles thousands of frames, not the C runtime's 1 GB. A
  self tail call in the IR is still a direct call here (there is no tail-call proposal in
  the module), so a loop written as tail recursion can overflow a deep input. A trap from
  stack exhaustion is reported by the host as a failure, never as a value.
* **No IO, FFI, exceptions or host imports beyond big integers.** `main` must not be
  `IO`; foreign functions other than the five `Array` externs are compile errors. Native
  `String`/`Bytes`/`StrMap`/`WordArray`/`WordMap`/`Intern` operations, machine words,
  threads and POSIX are not implemented. Wasm exception handling and a GC proposal are
  not used; a future host could provide more imports.
* **Call arguments** are copied through a 256-slot scratch buffer: a `pap`/`ap` with more
  than 256 arguments is a compile error. (Direct calls are not limited.)
* **Big integers** live in the host: shifting by or exponentiating to an enormous number
  throws a `RangeError` (the C runtime panics or allocates), and the host table keeps
  every big value it has produced (small intermediates are reclaimed only by the GC of
  the JS numbers, not by the module). Decimal output uses an 8 KiB scratch buffer; a big
  number with more digits than that is outside this target.
* **Not a library target.** `--target wasm` builds a `main`; `--lib`, `--no-main`, `--split`
  and export wrappers are rejected. The C/LLVM flags (`--cc`, `--cflags`, `--ldflags`,
  `--gmp`) are ignored.
* The host is checked in and must be present to *run* a module
  (`web/wasm-host.mjs`); a browser or another host can instantiate the module itself by
  providing the five `env` functions.

## Tests and counts

`Tests/Groups/Wasm.lean` is the `wasm` group (`lake test -- wasm`): **25 cases**. They
cover:

* **golden arithmetic** (small, big and saturating subtraction), **control flow** (nested
  cases and a join point), **calls** (mutual recursion, closures, partial and
  over-application), **strings as algebraic data**, **codata** (`lazyTag`/`lazySet`),
  **generic data** (a recursive constructor built from variables, which uses
  `pack`/`mkObj`), `Array`, `Int`, `memo`, and closed definitions;
* **traps**: an IR-level `unreachable` entry, and deep non-tail recursion exhausting the
  engine's stack; both must fail under the host, not print a value;
* the **validator**: a valid module passes, and bad magic, a truncated module and an
  unknown section id are rejected;
* the **boundary**: `IO` main, `Bytes`, and a foreign `Str` function are rejected with a
  message naming the reason; `--lib`/`--no-main` are refused by the build path;
* the **build path**: `Build.build` writes a module that validates and
  `Build.runWasmGlobal` reads its result.

The golden cases run the module under Node and compare the read-back value with the
**interpreter's** result for the same source (`#eval main`), so a change in the encoder or
the interpreter shows up as a mismatch. Each case skips (passes with a note) when `node`
is not on the `PATH` or the host file is missing, as the C tests skip without GMP; the
`nix develop` shell (and so CI's shards) puts `node` on the `PATH`, like `cc` and `llc`. The
host is spawned without Lean's `LD_LIBRARY_PATH`, which `lake test` sets and which shadows
the system's `libgcc` for Node. `Wiz.WasmValidate` runs without Node, so the structural
checks are still exercised in that case.

Smoke commands (from a checkout, after `lake build wiz`):

```
$ ./.lake/build/bin/wiz run file.wiz --target wasm
$ ./.lake/build/bin/wiz build file.wiz -o /tmp/m.wasm --target wasm
$ node web/wasm-host.mjs /tmp/m.wasm
```
