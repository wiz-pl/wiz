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
functions below. An installed toolchain ships it as `share/wiz/web/wasm-host.mjs`, beside
`lib/`: `wiz run --target wasm` looks there first and at `web/wasm-host.mjs` after it,
so it does not depend on the current directory.

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
  `lazyTag`/`lazySet` for codata, **tail calls** (`return_call`/`return_call_indirect`
  from the tail-call proposal), and **CAF caching** (a closed definition that does work
  is built once and shared);
* **join points** (each join body becomes its own Wasm function taking its parameters;
  a `jmp` is a tail call, so a self tail call is a loop);
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
`call_indirect`, memory accesses and alignment. It knows the **tail-call proposal**
(`return_call`/`return_call_indirect`: the callee's results must be the current
function's results) and can be run with `Features.tailCalls := false` to prove that a
module does not depend on it. It is an **encoder-side** validator: it knows the
instruction subset this backend emits and rejects an unknown opcode.

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
* **Join points** are lifted: a `jmp` tail-calls the join's function and returns its
  value. This keeps the emitted code structured without a relooper; unlike a loop it does
  not reuse a stack frame, which is fine for the non-tail `case` continuations the lowerer
  produces. A `jmp` is a tail call, so `IR`'s `loopify` (a self tail call rewritten as a
  join loop) is a real Wasm loop rather than a growing call chain.
* **Tail calls**: a direct call immediately followed by returning its result is emitted
  as `return_call`, and an application of a closure (the runtime's `wiz_apply`) in the
  same position as `return_call` too. The boxed closure wrappers, `jmp`s and the
  fall-through path of a `jdecl` are tail calls as well. This uses the Wasm **tail-call
  proposal**; see "Limits" for the engine requirement.
* **CAF caching**: a closed definition `IR.cafs` chooses (no parameters, and work worth
  caching) gets a mutable `i64` global cell initialized to 0 (no Wiz value is 0) and a
  separate build function holding its body. The declaration itself becomes a getter:
  one global load on the hit path, `wiz_inc` for the new reference; on a miss it calls
  the build function, publishes the value in the cell, and returns a reference. The cell
  keeps its reference for the rest of the run, so the value (and everything it reaches)
  is effectively immortal, exactly as the C runtime's `wiz_caf_init` path. No threads
  are involved. The module exports `wiz_caf_builds`, an `i32` global that counts misses,
  so a test can observe that a CAF is built once.
* **Memory and reclamation**: addresses 8–2056 are a scratch buffer for call arguments
  (`pap`/`ap`), the free lists' heads follow it (one `i32` per size class, 2056–2396), big
  literals' decimal text starts at 4096, and the heap follows it. Every object has a
  16-byte header `{rc, tag, size, class}` and the header's fourth word is the block's size
  class while it is live and the next free-list pointer while it is free. The IR's
  `dup`/`drop` are `wiz_inc`/`wiz_dec`: **the last drop releases the object**, decrements
  its fields (a closure's captured arguments, an array's live elements, a thunk's function
  or value — a big number's field is a host handle, not a value, so it is skipped), and
  returns the block to a **segregated free list** for its size class: exact sizes for
  16…520 bytes, powers of two from 1 KiB to 64 MiB above that. `wiz_alloc_raw` pops a block
  of the right class when one is free, and grows memory otherwise (a failed `memory.grow`
  traps rather than spinning). `reset`/`reuse` keep a unique cell and refill it, exactly as
  `runtime/rt_words.inc` does, so a functional update (`map` over a list you own) allocates
  nothing. Freeing is **iterative**: a dead object's children that this drop kills are
  threaded through the dead object's own header (the count becomes `-(class + 1)`, the
  fourth word the link) and drained in a loop, so a long chain does not recurse on the
  engine's stack. The peak is therefore the peak *live* set, not everything allocated.
* **Big numbers**: a `Nat` above `2^62 - 1` is a `BIG` object whose single field is a
  host handle `2^63 | (index << 1)`. The host's `BigInt` table implements the operations
  (`big_op`), comparison (`big_cmp`), `log2`, decimal conversion, and construction from a
  literal's digits. A result below `2^62` comes back as a scalar, so the representation
  is canonical.

The five host imports are `big_of_dec`, `big_op`, `big_cmp`, `big_log2` and
`big_to_dec`; the module exports `memory`, `wiz_main` (the IR's `wiz.entry`), three
decoders (`wiz_value_tag`, `wiz_value_field`, `wiz_big_digits`) and the `i32` global
`wiz_caf_builds` (the number of CAF misses, used by the caching test). The Wasm runtime
is 47 functions (`runtimeNames` in `Wiz/Compiler/Wasm.lean`).

## Limits and what remains

These are deliberate for this target; none of them affects the C or LLVM backends.

* **Reclamation is reference counting, so cycles leak.** The lowering does not build
  cycles (codata's `lazySet` overwrites a *shared* cell with its payload, and the payload's
  corecursive fields are new cells), but a cycle built from constructors would keep its
  blocks. The C runtime has the same property; there is no cycle collector in either.
* **Memory is never returned to the engine.** `memory.grow` is one-way, so the peak is the
  peak live set and stays there. Blocks above 64 MiB are not reused (they are bump
  allocated), and a block that a `lazySet` shrinks is returned to a smaller class than its
  capacity (safe — over-sized — but the capacity is not recovered).
* **Big-number churn grows the host's table, not linear memory.** A freed `BIG` object's
  block is reclaimed, but its `BigInt` stays in the JS host's append-only table (there is
  no `big_free` import). A long loop over big numbers therefore grows the JS heap.
* **No finalizers or foreign objects.** The subset has no FFI, and the C runtime's
  `WIZ_TAG_EXT` (a pointer with a release function) has no Wasm equivalent: an `ext` value
  cannot be built, so there is no finalizer to run. The tags that *can* appear are
  constructors, closures, big numbers, arrays and thunks.
* **CAF values are immortal, as in the C runtime.** A closed definition's value is held
  by its global cell for the rest of the run (and is not counted against a free); this is
  the sharing the native backends have, not a leak. A CAF that is never used is never
  built (the cache is lazy). A CAF that re-enters itself while being built builds itself
  again, and so diverges exactly as it did without the cache. A value that does no work
  (a scalar, a call of another constant) is not cached, matching `IR.cafs`.
* **The tail-call proposal is required.** Every module this backend emits uses
  `return_call` (the tail position of a direct call, a closure application, a `jmp`, a
  boxed wrapper and a `jdecl` fall-through) and the validator checks it. Node 26 and
  current browsers implement it. On an engine without the proposal, instantiation fails
  with a `CompileError`; `web/wasm-host.mjs` detects this with a tiny
  `return_call` probe (`supportsTailCalls`, `WebAssembly.validate` of the smallest module
  using the opcode) and reports that the engine lacks the feature instead of leaving a
  bare compile error. There is no fallback encoding in a module that uses a tail call:
  the module is written once and the engine is not known at `wiz build` time. Modules
  emitted before this change (with no `return_call`) still run unchanged on such an
  engine.
* **Non-tail recursion still uses the engine's stack.** Deep *non-tail* recursion and
  the non-tail case continuations use ordinary frames; Node's default Wasm stack handles
  thousands of frames, not the C runtime's 1 GB. The trap case in the test group is
  deliberately non-tail: it must still exhaust the stack and be reported as a failure,
  never as a value. A tail-recursive chain through a *closure* (`ap`) also keeps one
  `wiz_apply` frame per step, because that runtime function must free its argument
  buffers after the call; a chain through direct calls and joins is fully flat.
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

## Measurements

`scripts/wasm-peak.mjs MODULE.wasm` prints a module's result, its peak linear memory and
the time spent in `wiz_main`. The module's memory only grows, so its size after the call
is the peak. `scripts/wasm-workload.wiz` is a fixed workload: `spin 20 18 0` builds and
consumes a perfect binary tree of `2^18 - 1` constructors (32 bytes each) twenty times,
about 5.2 million allocations, and never holds more than one tree.

Node 26, one machine, best of five runs (the peak is exact and identical run to run):

| workload | allocator | peak linear memory | `wiz_main` |
| --- | --- | --- | --- |
| `wasm-workload.wiz` (20 iterations, 160 MiB allocated) | bump | 160.1 MiB | 0.21 s |
| | reference counting | 8.06 MiB | 0.14 s |
| the same, 40 iterations (320 MiB allocated) | bump | 320.1 MiB | 0.27 s |
| | reference counting | 8.06 MiB | 0.19 s |
| the same, 1000 iterations (7.8 GiB allocated) | bump | impossible (over wasm32's 4 GiB) | — |
| | reference counting | 8.06 MiB | 4.9 s |
| churn: 2000 lists of 1500 constructors of four widths | bump | 160.2 MiB | 0.54 s |
| | reference counting | 128 KiB | 0.12 s |
| functional update: 2000 × `incAll` over a 2000-cell list | bump | 244.2 MiB | 0.73 s |
| | reference counting | 128 KiB | 0.15 s |

The peak with reference counting is one tree (resp. one list), as intended, and does not
grow with the iteration count. The allocator is *faster* than the bump pointer here: it
reuses blocks instead of growing memory (which zeroes new pages) and keeps the working set
in cache, so the free list costs nothing at this scale. The four reclamation cases in the
test group assert a peak of at most 8 pages (512 KiB) as well as the result, and the
algorithms are checked against the module compiled by the previous backend and against the
interpreter for every other case.

CAF caching, Node 26, best of five runs:

| workload | feature | peak linear memory | `wiz_main` |
| --- | --- | --- | --- |
| two live uses of a closed `Tree` of `2^20 - 1` nodes | CAF cached | 257 pages (16.1 MiB) | 23.0 ms |
| the same two uses, with the tree rebuilt per use (unit argument) | no cache | 513 pages (32.1 MiB) | 44.4 ms |

The committed tail-call test is 200,000-deep mutual recursion and a 200,000-step self
tail call (below): both are constant-stack, and the engine's stack is not part of linear
memory. In the CAF row both uses are live at once (`size big + size big`), so caching
halves the peak as well as removing one of the two builds; a loop that rebuilds the tree
each iteration shows the same time difference without the peak change.

## Tests and counts

`Tests/Groups/Wasm.lean` is the `wasm` group (`lake test -- wasm`): **34 cases**. They
cover:

* **golden arithmetic** (small, big and saturating subtraction), **control flow** (nested
  cases and a join point), **calls** (mutual recursion, closures, partial and
  over-application), **strings as algebraic data**, **codata** (`lazyTag`/`lazySet`),
  **generic data** (a recursive constructor built from variables, which uses
  `pack`/`mkObj`), `Array`, `Int`, `memo`, and closed definitions;
* **tail calls**: 200,000-deep mutual tail recursion (a direct `return_call`) and a
  200,000-step self tail call (`IR`'s join loop, `jmp`); both would exhaust the stack
  under the old non-tail encoding. The module bytes from two compilations are compared,
  and the validator is run with `tailCalls := false` to show that it requires the
  proposal;
* **CAF caching**: a closed `List Nat` is used twice; a module-level build counter
  (`wiz_caf_builds`) is non-zero after `main` and does not move when `main` is run a
  second time in the same instance;
* **reclamation**: an allocation loop that would need ~105 MB under the bump allocator
  completes with a peak under 8 pages (512 KiB); a churn loop over constructors of four
  widths (alloc/free/realloc) and a loop of functional list updates (`reset`/`reuse`) stay
  under 8 pages too; a loop that builds, forces and drops closures and `memo` thunks keeps
  its peak bounded. These read the peak from the host (`memory.buffer.byteLength`, which
  only grows) and compare the result with `main`'s type, as the other run cases do;
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
