# A JavaScript target for Wiz (`--target js`)

**Status:** prototype on `integration/train12` (`d853fde79`), branch only, no PR.
New pieces: `Wiz/Compiler/Js.lean`, `web/wiz-js-runtime.mjs`, the `=js` test group
(`Tests/Groups/Js.lean`), and `examples/js-loom/` (a Loom-shaped demo). The other
backends are untouched; `--target js` is additive, like `--target wasm` was.

**One-line result.** The existing untyped IR maps to JavaScript almost one-for-one, so
the Loom glue — router, mount, event delegation, patch list — can be Wiz source that is
compiled and tested, while the DOM stays behind `extern "js.…"`. It is a good target
for *replacing hand-written JS*, not for replacing C: `Nat` is a `BigInt` (exact, but an
allocation per operation), reference counting is the garbage collector's, and there is
no tail-call guarantee or filesystem/process/thread runtime.

## 1. What is emitted

`wiz build --target js FILE -o OUT` writes one self-contained ES module (`OUT.mjs`
unless `OUT` ends in `.mjs`/`.js`): the runtime is pasted at the top, then one JS
function per IR declaration, then `export function main`, then a runner that fires only
when Node executes the file directly (`import.meta.url === wizFileUrl(process.argv[1])`).
Importing the module does not run `main`; the importer calls it.

The IR is the same `Wiz/Compiler/IR.lean` the C, LLVM and Wasm backends consume, after
lowering, Perceus and `Simp`. Every construct has a lowering:

| IR | JavaScript |
| --- | --- |
| `lit n` | `1180591620717411303424n` (a `BigInt` literal) |
| `ctor t #[]` | `0`, `1`, … (the tag is the whole value) |
| `ctor t [x, y]` | `wizCtor(1, [x0, x1])` → `{t: 1, f: [x0, x1]}` |
| `proj 1 x` | `wizProj(x0, 1)` |
| `fap f [x]` | `w_f(x0)` |
| `pap f [x]` | `wizClo(w_f, 2, [x0])` (arity 2, one captured argument) |
| `ap g [x]` | `wizApply(x1, [x0])` (partial and over-application included) |
| `prim .natAdd [a, b]` | `wiz_nat_add(x0, x1)` — the C runtime's name |
| `prim .extern key [a, b]` | `wizExtern("extern:cname:…", [x0, x1])` |
| `reset x` / `reuse tok t …` | `wizReset(x0)` (no token) / a fresh `wizCtor` |
| `case x alts` | `switch (wizTag(x0)) { case 0: … default: throw … }` |
| `jdecl j ps body k` | `const j3 = (p…) => { body }; const r3 = (() => { k })(); while (r3 instanceof WizJmp) …` |
| `jmp j …` | `return new WizJmp(3, [x0])` |
| `dup x` / `drop x` | nothing (the GC owns the reference) |
| `unreachable` | `throw new Error("wiz: reached an impossible case")` |

A join point becomes a function plus a driver loop, so a jump is constant stack: the
`Simp` rewrite that turns a self tail call into `jdecl J … (jmp J params)` really is a
loop in the emitted JS (the `=js` group runs a 100 000-iteration countdown). This is not
general tail calls: a mutual tail call is still a JavaScript call.

Closed definitions (`IR.cafs`) are built on their first use and kept, as in C and Wasm:
a small `__caf_…` slot guards the build.

`wiz run --target js` builds the module in a scratch directory, runs `node`, and reads
the printed result back with `main`'s type, exactly as `wiz run --target wasm` does. A
pure `main` prints the C runtime's generic tree (`(tag fields…)`, a decimal number,
`<fn>`); `wiz run` turns that back into the typed pretty form, so a scalar result is
byte-identical and a structured one is the same value with the generic presentation.
An `IO Unit` program prints only what it prints (the `wiz run` CLI adds a final
newline when the program's output does not end in one; the module itself does not).

## 2. Representation choices

| Wiz | JavaScript | Why |
| --- | --- | --- |
| `Nat` | `BigInt` | arbitrary precision like the GMP path of the C runtime; `0n`, `2n ** 100n` |
| `Int` | the library's data type | `Int` is already constructors over `Nat`; no special case |
| a tag scalar (`Bool`, `Foo.bar` with no fields) | a JS `number` | `case` on it is the scalar's own value, as `WIZ_BOX(t)` in C |
| a constructor with fields | `{t: tag, f: [fields]}` | the C `wiz_ctor` without a header; the GC replaces `rc` |
| `◾` | `null` | one distinguished value; applying it is `◾` |
| a closure | a JS function from `wizClo` | callable from an `extern "js.…"` host directly; `wizApply` handles partial/over-application |
| `String` | the Wiz data type: `String.mk (List Char)` | it is `List Char` in the IR; code-point conversion happens only at the FFI |
| `UInt64` | `BigInt` masked at 64 bits | the `wiz_u64_*` entries mask; `UInt64.toNat` is exact |
| `Float64` | a JS `number` | IEEE 754 double; `wiz_f64_show` reimplements `%.17g` |
| `UIntN w` / `BitVec n` | `BigInt` bits | `wiz_word_*` mask at the width; sign extension for `IntN` |
| `Bytes` | `Uint8Array` | `push`/`slice`/`append` copy, so the Wiz value stays functional |
| `Array` | a JS array | `set`/`push` copy; the runtime's in-place update of a unique buffer is an optimisation, not observable |
| a foreign handle (`foreign_type`) | the host's object | opaque; Wiz only passes it back |

`dup`/`drop` are emitted as nothing. `reset` returns `null` (there is no cell to keep)
and `reuse` allocates. The C runtime's leak and peak-memory observations therefore do
not transfer to this target; the `=js` group does not claim them.

`Nat.toString` calls `wiz_nat_show`, which builds a Wiz `String` value (a `List Char`),
not a JS string. The only places a JS string exists are the `s` marshalling of `extern`
arguments and results.

## 3. The FFI

An `extern` names a JavaScript function by a dotted path under `globalThis`:

```wiz
foreign_type Elem
extern "js.document.createElement" createElement : String → Elem
extern "js.wiz.dom.setAttribute" setAttribute : Elem → String → String → IO Unit
extern "js.wiz.dom.addEventListener" addEventListener :
  Elem → String → Callback (Elem → IO Unit) → IO Unit
```

`wizCallJs` resolves `js.a.b.c` to `globalThis.a.b.c` and calls it with `this` bound to
`a.b`, so `js.document.createElement` is a real method call. The signature is checked by
the existing `extern` path (`Wiz/Elab/Command.lean`): a `foreign_type` is a `p` (opaque
handle, passed as the host's object), `String` is `s` (converted to/from code points),
`Nat` is `n` (a `BigInt`), `UInt64` is `u`, `Float64` is `f`, `Bool` is `b`, `Unit` is
`v`, and `Callback T` is `w` (the Wiz closure, which is a callable JS function).

`wizExtern` implements the runtime's C names too (`wiz_nat_show`, `wiz_io_println`,
`wiz_u64_*`, `wiz_f64_*`, `wiz_bytes_*`, `wiz_array_*`, `wiz_word_*`), so `IO.println`
and friends work unchanged. Everything else is refused **at compile time** by
`checkExterns`, with the name in the message: filesystem (`wiz_io_read_file`,
`wiz_io_write_file`), processes, threads, `MVar`/`Ref`/`Chan`, `Str`, `WordArray`,
`StrMap`, `Store`, kernel/proof counters. A `js.…` host API is the way to add one.

The key grammar is `extern:cname:kinds:result:io:header:finalizer`, colon-delimited, so
`extern "js:document.querySelector"` cannot be spelled without changing the shared key
parser (and the C/LLVM/Wasm backends with it). The dotted spelling is the one-line
compromise of this prototype; it costs nothing at run time and nothing in the other
backends.

Kinds the JS emitter refuses: a C struct (`S`) and a byte buffer with a length
(`y`/`Y`). JavaScript has no C layout for those. A callback (`k`/`K`) is allowed for a
`js.` host function: the Wiz closure *is* the JavaScript function, so `wizExtern` passes
it as one argument (the C glue's function-pointer + context pair is a C detail). A
`Callback (A → IO B)` handed to the host is called with its argument and the world (or
through `wizApply(f, [x, 0])`); the demo's delegated listener is exactly that. A
callback is refused for a `wiz_` native, whose C signature expects the C pair; a
`js.…` extern may still take and return `w` (any Wiz value) and `p` (a handle).

## 4. Blockers, honestly

1. **`Nat` performance, not semantics.** Every `Nat` is a `BigInt`. C keeps numbers
   below 2⁶² as tagged scalars and reaches GMP only beyond that; this target allocates
   for `1 + 2`. Semantics are exact (including `n / 0 = 0`, `n % 0 = n`, `log2 0 = 0`,
   arbitrary shifts), but do not quote a performance number for the JS backend. A
   small-integer fast path (a boxed 53-bit number with a tag, or two representations
   plus checks) is the obvious next optimisation and is not here.
2. **Closures and `partial`.** A Wiz closure is a JS function; partial application
   captures arguments, over-application applies the returned value. A *non-tail*
   recursive Wiz function uses the JavaScript stack: roughly 10⁴–10⁵ frames depending
   on the engine and frame size, not the C backend's 1 GiB thread stack. Self tail calls
   that `Simp` loopifies are loops; mutual tail calls and non-tail recursion are not.
   `partial def` is therefore fine for small inputs and not a substitute for a loop.
3. **Strings versus UTF-16.** A Wiz `String` is a list of code points, and stays that
   way inside the module. At an FFI boundary `wizStringToJs` walks the list and builds a
   JS string with `String.fromCodePoint`, and `wizString` goes back. A code point above
   `U+10FFFF` or a surrogate becomes `U+FFFD`, matching the C runtime's `wiz_in_string`.
   The trap is on the host side: JS `length`, `slice`, `substring` and array indexing
   count UTF-16 units, while a Wiz string position is a code point. The reader and
   parser already convert their own spans; a host that hands Wiz a text offset must
   convert deliberately (`Array.from(s)` or code-point iteration), or a string with an
   astral character drifts by one. The demo uses only ASCII paths, so it does not
   exercise this. A second boundary difference: the C runtime's `const char *` stops at
   the first NUL, so `IO.println "a\0b"` prints `a` under C and `a\0b` here; `Bytes`
   keeps the NUL truncation of `Bytes.ofString`, but `IO.print`/`IO.println` do not.
4. **No reference counting.** The GC decides when an object dies. That is invisible to
   programs (Wiz has no pointer equality or finalisers in this subset), but it changes
   the cost model and makes the C runtime's leak checks meaningless here.
5. **Synchronous `IO` only.** An `IO` action is a function of the world, so the runtime
   runs it to completion. DOM events can call back into Wiz (the demo's listener does),
   but `fetch`, IndexedDB or a dynamic `import()` return promises; there is no
   promise-to-continuation bridge in this prototype. Loom's mount/route/patch path is
   synchronous; its storage path is not, and needs either a callback-shaped host API or
   an `IO` await primitive that does not exist yet.
6. **No user exports.** `export "name" f` is not turned into a JS export; only `main`
   is. The Loom host needs `main` (or a `js.` callback registration), and that is what
   the demo uses. Exported C symbols are the C backend's contract.
7. **Lazy cells are not memoised.** `coit`/`scofix` cells are ordinary constructors and
   `lazySet` returns the payload without rewriting the cell, so a second observation
   recomputes the same pure payload. The values agree; the work may be repeated.
8. **The printer is the generic tree.** A module run by Node cannot know `main`'s type;
   it prints what the C executable prints. `wiz run` does the typed readback.

## 5. The Loom-shaped demo

`examples/js-loom/loom.wiz` is the glue Loom hand-writes today, in Wiz: `route` is a
pure function over `String`, `patchFor` returns a `List Patch`, `applyPatches` walks it
with `IO`, `mount` builds a container/nav/two links/one content element, and one Wiz
closure is registered with `addEventListener` for delegation (`getAttribute
"data-path"`, then render). The DOM operations are the `extern` surface above.

`examples/js-loom/fake-dom.mjs` implements exactly those operations and records every
one (created elements, attributes, text, listener registrations, appends).
`examples/js-loom/run.mjs` installs it, dynamically imports the built module, calls
`main`, and asserts:

* the created tags are `div, nav, a, a, main`;
* the container's `id` is `app`, and both links carry `data-path`;
* exactly one `click` listener is registered, on `nav`;
* the initial patch list renders `Home`/`data-view=home`;
* clicking the `/about` link applies `About`/`data-view=about`;
* clicking an element with `data-path=/missing` applies `Not found`/`data-view=404`;
* six patch operations (three lists × two) reached the content element.

It prints one `PASS` line per assertion and `PASS loom demo: mount, route and patch are
Wiz`. The `=js` group also builds a variant whose first route branch is changed from
`.home` to `.about`; the same harness then reports

```
FAIL the initial patch list renders Home
...
FAIL loom demo: 1 assertion(s) failed
```

and exits 1, which is the evidence that the assertions are about the Wiz code and not
about the harness. The demo is not wired into Loom's `web/source-*.js`; replacing those
files is the next step, and the host adapter (the `wiz.dom` namespace over the real
`Element`) is a thin JS file, not Wiz.

## 6. Tests and files

The `=js` group is in `Tests/Groups/Js.lean`; it runs under the `library` shard (one
selector line in `.github/test-shards.json`). It compares pure programs with the
interpreter (`#eval main`), `IO` programs with their expected output, and the two
acceptance programs with the **C backend** through `Build.runGlobal` and
`Build.runJsGlobal` (the same value for a pure `main`, the same stdout for `IO`). It
also checks that the emitted module is deterministic, has `main` and the `wiz_*` entry
points, that `IO.readFile` and an unimplemented native are refused by name, that
`Build.buildJs` writes `OUT.mjs`, and runs both demo variants. The group is 22 cases;
it ran 22/22 (0 failed) in 37 s on the controller.

Files added:

* `Wiz/Compiler/Js.lean` — the emitter (IR to ES module).
* `web/wiz-js-runtime.mjs` — the runtime the module pastes in.
* `Tests/Groups/Js.lean` — the `=js` group.
* `examples/js-loom/{loom.wiz,fake-dom.mjs,run.mjs}` — the demo.
* `Main.lean` target selection, `Wiz/Compiler/Build.lean` `buildJs`/`runJsGlobal`; no
  change to `IR.lean`, `C.lean`, `LLVM.lean` or `Wasm.lean`.

`wiz build --target js` needs no tool in `Wiz/Toolchain.lean`; `node` is needed only to
run the module (and by the tests, which skip when it is absent).

## 7. Self-hosting

Out of scope, and the boundary is real. `selfhost/Backend.wiz` is a C emitter over the
self-hosted frontend's own `ETm`, not over `Wiz/Compiler/IR.lean`; it has no target
parameter and no JS vocabulary. A self-hosted JS backend would need a second emitter
over `ETm` (or a shared lowered IR), and it would have to refuse the same subset this
one does: no filesystem/process/thread natives, no C structs, the `s`/`p`/callback FFI
only, and the same `Nat`-as-`BigInt` choice or an explicit agreement with `Js.lean` on the
representation. Today the self-hosted compiler emits C only; `--target js` is the Lean
backend. `selfhost/Backend.wiz` must not pretend otherwise until that emitter exists.

## 8. Out of scope for this slice

* promises/`await` in `IO` (the Loom storage path);
* user `export "name" f` as a JS export;
* a native small-integer `Nat`, unboxed records, or any performance claim;
* source maps, bundling, tree-shaking, a browser test bed;
* `Str`, `WordArray`, `StrMap`, `Store`, `MVar`/`Ref`/`Chan`, threads;
* the C struct and byte-buffer FFI kinds (a callback is supported for a `js.` host);
* the self-hosted backend.

## 9. What "adding a target" cost

The closed list for `--target` lives in `Main.lean` (`targets`) and the build path
branches on the name; there is no plugin registry. This target added:

* one emitter file (~250 lines) and one runtime file (~600 lines);
* `buildJs`/`runJsGlobal` in `Build.lean` (the Wasm path is the template);
* one CLI branch in `buildCmd`, one in `runCmd`, one REPL refusal;
* one test group and one shard selector;
* no change to `IR.lean` and no change to the three existing backends.

That is the honest price of a fourth backend over the shared IR: the IR is the
contract, and the runtime/native surface is where the work is.
