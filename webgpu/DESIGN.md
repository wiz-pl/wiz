# A WebGPU target for Wiz: a restricted data-parallel subset

**Status:** exploration, 2026-11-19. Branch `webgpu-target`, worktree `wt/webgpu`.
Prototype only: no PR, no merge, no changes to the C/LLVM/Wasm backends. The artefact is
`webgpu/` in the repository plus this note.

**Verdict.** A *map*-shaped subset of Wiz translates to WGSL honestly and cheaply: one
scalar kernel body per definition, a storage-buffer ABI, and a dispatch. The prototype
compiles `out[i] = a[i] + b[i]` (and a `select`-shaped second kernel) from the real Wiz
syntax tree, has its WGSL validated by wgpu/naga, runs it on a GPU (lavapipe), and gets
exactly the interpreter's numbers. That is the whole positive result. It is not a path to
running arbitrary Wiz on a GPU: the language's default number is an unbounded `Nat`, its
data are heap-allocated with reference counting, and its functions are closures. Those are
not details a WebGPU backend can paper over; they are the three blockers in §6.

## 1. What "adding a target" means today, and why WebGPU is different

The existing backends all consume the **IR** (`Wiz/Compiler/IR.lean`: A-normal form,
first order, explicit `dup`/`drop`, closures as `pap`/`ap`) after lowering and Perceus:

* C (`Compiler/C.lean`) and LLVM (`Compiler/LLVM.lean`) emit code against the C runtime:
  a value is a word, objects have a reference-counted header, big `Nat`s are GMP.
* Wasm (`Compiler/Wasm.lean`) emits a binary module with linear memory, its own
  segmented free-list allocator, `BigInt` host imports, and a structural validator
  (`WasmValidate.lean`). The module can run with no C toolchain; a JS host supplies the
  big integers and decodes the result.

WebGPU cannot take that shape:

* there is no heap, no `malloc`, no finalizer and no reference counting;
* WGSL has no closures or function values, and **forbids recursion**;
* there is no `main` that runs to completion: a dispatch is asynchronous, and buffers are
  read back by mapping them;
* WGSL's only scalar types are `bool`, `i32`, `u32`, `f32` (and optional `f16`); there is
  no `i64`/`u64` and no `f64` in core WebGPU;
* the "runtime" is the browser/Deno WebGPU implementation, which also owns validation,
  binding layouts and buffer limits.

So a WebGPU target is **source-to-source after elaboration**, not an IR backend: pick a
fragment whose values are machine scalars and whose control flow is the dispatch, emit
WGSL text, and hand the host a small ABI. The prototype takes the shape a real backend
would take (parse → restrict → emit), but starts from the *unelaborated* syntax tree
because it must run without a Lean build.

## 2. The subset

### 2.1 A kernel

A kernel file is a sequence of `def`s. The **entry** kernel has the form

```
def add (i : Nat) (a b : Array U32) : U32 := ...
```

* first parameter: the index, type `Nat`, supplied by `@builtin(global_invocation_id).x`;
* remaining parameters: `Array U32` buffers, all the same length as the output;
* result: `U32` (or `Bool`); the host writes it to `out[i]`.

Helper kernels may be called; they take **scalars only** (not buffers) and must be
acyclic. The buffers are module-scope WGSL bindings, so an entry's `Array` parameters are
names for bindings, not values.

### 2.2 Types

| Wiz | WGSL | allowed as |
| --- | --- | --- |
| `U32` | `u32` | scalar parameter/local/result, buffer element |
| `Bool` | `bool` | scalar/local, `match` scrutinee, result |
| `Nat` | `u32` at the boundary | the entry index only; no arithmetic |
| `Array U32` | `array<u32>` storage binding | entry parameter only |
| anything else | — | rejected |

`U32` is Wiz's `UIntN 32`, whose operations reduce mod 2³²; WGSL `u32` wraps too, so
addition/subtraction/multiplication agree exactly. That agreement is tested at the
overflow boundary, not assumed (§5).

### 2.3 Terms

Accepted:

* variables, `let x : T := e; body` (a WGSL `let`, type annotation required);
* application of a **name** (no higher-order application);
* `U32.ofNat N` for `N < 2³²` (a `u32` literal; Wiz reduces it mod 2³², and the subset
  rejects a literal that already exceeds the width so a typo is not silently wrapped);
* `UIntN.add`, `UIntN.sub`, `UIntN.mul`, `UIntN.land`, `UIntN.lor`, `UIntN.xor`;
* `UIntN.lt`, `UIntN.le`, `UIntN.beq` (to `Bool`);
* `Array.getD buf i (U32.ofNat 0)` — the only buffer read. The zero default is required
  because WGSL's robust-access rule returns 0 for an out-of-range read; any other default
  would make the two runtimes differ, so it is rejected;
* `match` on `Bool` with `.true`/`.false` arms, compiled to WGSL `select(false, true,
  cond)` (both arms are evaluated — the subset is pure and total);
* calls to other defs in the file, inlined as WGSL functions, acyclic.

Rejected, each with a message naming the construct:

* `Array.push`, `Array.set`, `Array.size`, any constructor, any `let`-bound array: these
  allocate or inspect the heap;
* `Nat.add`/`Nat.succ`/any `Nat` arithmetic, and a `Nat` result;
* `UIntN.div`/`UIntN.mod`: Wiz defines `a / 0 = 0` and `a % 0 = a`; WGSL leaves a zero
  divisor unspecified, so the semantics do not agree;
* `Float64`, `UInt64`, `IntN`, `String`, `IO`, `Str`, `Bytes`, `Ref`, `Task`, ...;
* lambdas, partial application, a call whose callee is not a name;
* recursion (including mutual recursion: the call stack is checked);
* FFI/externs, axioms, type classes, instances, proofs, implicit binders;
* an `Array.getD` default other than zero;
* a helper that takes a buffer under a name the entry does not bind.

### 2.4 Control flow and the host boundary

The emitter produces straight-line code. The only loop is the dispatch; the only branch
is the entry bounds check:

```wgsl
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let i : u32 = gid.x;
  if (i < arrayLength(&out)) { out[i] = add_at(i); }
}
```

`match` is `select`, so the subset has **no divergent control flow inside a kernel**. That
is a restriction, not an optimisation: supporting `if`/loops would need either uniformly
executed branches or a real SIMT analysis, and WGSL deliberately has no recursion to fall
back on.

The host ABI the prototype fixes (a real target would make it explicit in the source):

* bindings: `Array` parameters in order at `@group(0) @binding(0…n-1)`, all
  `var<storage, read>` `array<u32>`; the result at binding *n*, `var<storage,
  read_write>`;
* all buffers have the output's length;
* one workgroup of 64 invocations per 64 elements; `dispatchWorkgroups(ceil(n/64))`;
* buffer contents are little-endian `u32`; readback through a `MAP_READ` staging buffer.

The host must therefore know the parameter order, the lengths, and which buffer is the
result. The Wiz source does not say any of this yet; the emitter derives it from the
entry signature. A real design needs a kernel declaration with buffer modes
(`in`/`out`/`inout`) and a descriptor the host can consume without string-matching.

## 3. Why the rejections are not fussiness

* **Allocation.** Wiz data (lists, `Vec`, trees, `Array` growth, closures) is
  heap-allocated; the C/Wasm runtimes reclaim it with reference counting. A GPU shader has
  no allocator, and a storage buffer's length is fixed at bind time. Any kernel that
  creates data would need the host to pre-size every buffer and the compiler to prove the
  bound. `Array.push` is the visible edge of that problem, but `List` and `Vec` recursive
  functions are the same problem with more syntax.
* **Recursion.** WGSL forbids recursion (including mutual), because a shader has no
  unbounded call stack. Wiz's standard style is structural recursion on data. A GPU
  backend must either restrict to tail recursion as a loop or refuse; the prototype
  refuses everything.
* **Closures / higher-order.** WGSL has no function values, no indirect calls, and no
  dynamic dispatch. Wiz closures (`pap`/`ap`) and type-class dictionaries are exactly
  that. Monomorphisation can remove many of them, but it is a whole-program transformation
  the prototype does not do.
* **Proofs and dependent types.** The prototype reads the *unelaborated* tree, so it sees
  no types beyond the annotation it checks. Elaboration would let a real backend erase
  proofs and quantities (as the existing erasure does), but it would also force it to
  decide what a `Vec A n` kernel means. The prototype sidesteps this by allowing only
  `Array U32` and a `Nat` index.
* **Numbers.** `Nat` is unbounded; the GPU has 32-bit scalars. Restricting to `U32` is
  honest (the operations agree, including wrap), but it means a kernel cannot use Wiz's
  default numeric type, and Wiz currently has **no `Float32`**: `Float64` is the only
  float, and core WebGPU has no `f64`. A float kernel needs a new Wiz fixed-width float
  type first.

## 4. The pipeline

`webgpu/tools/wgsl.mjs`:

1. runs `wiz parse FILE` — the **real** parser — and reads its s-expression output;
2. builds the def table (binders → parameters, result types, bodies) and a conservative
   type checker/lowerer for the subset;
3. emits WGSL: one function per reachable def, storage bindings for the entry's buffers,
   a `main` compute entry point;
4. writes the text; any violation is an error naming the construct, never silently wrong
   code.

`wiz parse` is deliberately the front end: no second grammar. Two properties of it shaped
the prototype and are worth knowing:

* it prints **builtin syntax only**. `+`, `[a, b]` and `if … then … else` are macros
  declared in `lib/Prelude.wiz`; a file parsed by `wiz parse` alone does not have them.
  That is why the kernel uses `UIntN.add`, fully applied, and `match` rather than `if`.
  A real backend would run after elaboration and would accept the surface syntax.
* it is **unelaborated**: names are resolved by the prototype's own checker, and the
  result type is printed as a *list* (`[(term.ident U32)]`, Wiz has multiple results).
  The prototype requires exactly one.

## 5. The worked example

Source (`webgpu/kernels/add.wiz`), complete:

```wiz
import Word
import Std

def addScalar (x y : U32) : U32 := UIntN.add x y

def maxMulScalar (x y : U32) : U32 :=
  match UIntN.lt x y with
  | .true => UIntN.mul y (U32.ofNat 3)
  | .false => x

def add (i : Nat) (a b : Array U32) : U32 :=
  addScalar (Array.getD a i (U32.ofNat 0)) (Array.getD b i (U32.ofNat 0))

def maxMul (i : Nat) (a b : Array U32) : U32 :=
  maxMulScalar (Array.getD a i (U32.ofNat 0)) (Array.getD b i (U32.ofNat 0))
```

Generated `webgpu/build/add.wgsl`:

```wgsl
@group(0) @binding(0) var<storage, read> a : array<u32>;
@group(0) @binding(1) var<storage, read> b : array<u32>;
@group(0) @binding(2) var<storage, read_write> out : array<u32>;

fn addScalar(x : u32, y : u32) -> u32 {
  return (x + y);
}

fn add_at(i : u32) -> u32 {
  return addScalar(a[i], b[i]);
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let i : u32 = gid.x;
  if (i < arrayLength(&out)) { out[i] = add_at(i); }
}
```

The `maxMul` module is the same shape with
`select(a[i], b[i] * 3u, a[i] < b[i])`.

### 5.1 Inputs and the numerical comparison

Inputs are `webgpu/inputs.json` (8 elements, chosen to cross 2³²):

```
a = [3000000000, 4294967295,        0,          1, 123456789, 2147483648, 42, 4000000000]
b = [2000000000,          1,        0, 4294967295, 987654321, 2147483648,  0, 1000000000]
```

The reference values are produced by `wiz check webgpu/build/ref.wiz`, i.e. by the Wiz
**interpreter** (`#eval`) running the same `addScalar`/`maxMulScalar` definitions on the
same pairs. The interpreter cannot evaluate the `Array` version: `Array.*` are `extern`s
and `#eval` panics with `foreign functions only run in compiled code (wiz run)`. That is
why the reference applies the scalar kernel directly; buffer indexing is the only part not
interpreted. (The compiled path `wiz run` can exercise the `Array` version, but that is a
C build, not the interpreter.)

| i | a[i] | b[i] | Wiz `addScalar` | WGSL `add` | Wiz `maxMulScalar` | WGSL `maxMul` |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 3000000000 | 2000000000 | 705032704 | 705032704 | 3000000000 | 3000000000 |
| 1 | 4294967295 | 1 | 0 | 0 | 4294967295 | 4294967295 |
| 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| 3 | 1 | 4294967295 | 0 | 0 | 4294967293 | 4294967293 |
| 4 | 123456789 | 987654321 | 1111111110 | 1111111110 | 2962962963 | 2962962963 |
| 5 | 2147483648 | 2147483648 | 0 | 0 | 2147483648 | 2147483648 |
| 6 | 42 | 0 | 42 | 42 | 42 | 42 |
| 7 | 4000000000 | 1000000000 | 705032704 | 705032704 | 4000000000 | 4000000000 |

`make.mjs` printed the interpreter's 16 values:

```
make: add    = [705032704, 0, 0, 0, 1111111110, 0, 42, 705032704]
make: maxMul = [3000000000, 4294967295, 0, 4294967293, 2962962963, 2147483648, 42, 4000000000]
```

and they are exactly the WGSL columns. The WGSL was validated and executed with
**wgpu/naga** through Deno 2.9.8's `navigator.gpu` (adapter `llvmpipe`, Mesa 26.2.6
lavapipe, Vulkan): `getCompilationInfo()` returned **no messages** for either module, the
dispatch produced the WGSL column, and `check.mjs` exited 0. The rejected fixtures
(`webgpu/tests/reject/`) are also checked: all eight are refused with a reason. The same
page also ran in headless Chromium 157 through `check-browser.mjs` (both kernels, `ok:
true`, exit 0), so the browser deliverable is not just source.

### 5.2 What the page does

`webgpu/index.html` fetches `build/expected.json` (the interpreter's numbers) and the two
WGSL files, runs each through the same `run.js` used by the Deno check, and prints a table
with a per-row PASS/FAIL plus the naga diagnostics. It needs a secure context, so
`node webgpu/serve.mjs 8080` and `http://127.0.0.1:8080/`; `check-browser.mjs` drives the
page headlessly over the DevTools protocol when a Chromium and a software Vulkan driver
are available. The page is the deliverable; the Deno run is the automated proof.

## 6. What cannot be done, and the three hardest blockers

**Blocker 1: `Nat` is unbounded, and the runtime it needs is a heap.** A `Nat` is a
GMP-style bignum above 62 bits and every aggregate is an RC object. WebGPU has neither
bignums (no 128-bit, let alone arbitrary precision) nor allocation. The prototype can only
accept `U32`; any program whose types are `Nat`, `List`, `Vec`, trees, or `String` cannot
be a kernel. Making this work would mean a monomorphised, bounds-proven machine-number
subset and host-preallocated buffers — a different language surface, not a backend
lowering.

**Blocker 2: closures, higher-order functions, and recursion.** WGSL has no function
values and forbids recursion. Wiz's `pap`/`ap`, type-class dictionaries, generic
eliminators and ordinary structural recursion all need call stacks and indirect calls.
Whole-program monomorphisation and defunctionalisation could remove many of them, but not
all (a runtime-selected function cannot exist in a shader), and the prototype does none of
it. This is the blocker that also rules out "just compile the IR".

**Blocker 3: the host boundary and numeric surface.** There is no synchronous `main` in
WebGPU: the host must create buffers, choose a dispatch, submit, and asynchronously map a
staging buffer. Wiz's `IO`/FFI model has no device or queue, and the Wasm backend's host
imports are a synchronous function call. In addition, the only Wiz float is `Float64` and
core WGSL has no `f64`; without a `Float32` type, there is no float kernel at all. The
prototype fixes a map-shaped ABI by convention; a real target needs it in the language and
in a host runtime, plus explicit limits (this machine: 128 MiB max storage-binding,
256 MiB max buffer, 65,535 workgroups per dimension → 4,194,240 elements per dispatch at
workgroup 64).

Also impossible in this shape, and for the same reasons: proofs (the prototype never
elaborates them; a real target would erase them), dependent types (`Vec A n` has no runtime
length to trust), dynamic dispatch, exceptions, threads/synchronisation beyond workgroups,
and any guarantee that a Wiz program's *observable* result is preserved (NaN payloads,
signed zero, division by zero, and pointer identity have no Wiz meaning to preserve). The
prototype makes no proof claims and no optimisation claims.

## 7. What a real backend would need

1. **A kernel surface in the language**: a declaration that says which parameters are
   buffers, their modes, the dispatch shape, and the index — instead of deriving it from
   the first parameter's type.
2. **Elaboration and erasure**: run after `wiz check`, erase proofs and quantities, and
   monomorphise. That is where `Vec A n` and type classes become usable or are rejected
   with a type error rather than a syntax-shape error.
3. **A machine-number fragment**: `U32`/`I32`/`F32` with explicit wrap/rounding semantics,
   and a `Float32` primitive in Wiz if floats are wanted.
4. **A host runtime and ABI**: buffer descriptors, dispatch, readback; the same shape as
   `web/wasm-host.mjs`, but asynchronous and with limits.
5. **Differential testing**: the interpreter cannot run `Array` externs, so array kernels
   need either `wiz run` (C, exact but slower) or a pure-list reference plus the scalar
   kernel — the prototype's choice. This is a real testing-strategy decision, not a
   detail.
6. **Validation in CI**: naga as a library (not packaged in nixpkgs at the time of
   writing; Deno's `wgpu` gives the same validator and runs headless with lavapipe).

## 8. Files and commands

See `webgpu/README.md` for the layout. The commands used here:

```sh
WIZ=<wiz> node webgpu/tools/make.mjs                  # regenerate WGSL + reference
DENO=<deno> MESA=<mesa> VULKAN_LOADER=<loader> ./webgpu/check.sh
WIZ=<wiz> node webgpu/tests/reject.mjs                # boundary tests
node webgpu/serve.mjs 8080                             # the page
```

## 9. Findings worth keeping

* `#eval` cannot evaluate `Array` (or any extern): it panics "foreign functions only run
  in compiled code". Any future differential-testing scheme for array/IO code must use
  `wiz run` or a pure reference.
* `wiz parse` is a usable front end for a prototype, but it is builtin syntax only: `+`,
  list literals and `if` are `lib/Prelude.wiz` macros, so a parsed-only file cannot use
  them. It is also unelaborated, so the consumer must type-check.
* naga is not a nixpkgs attribute (`naga-cli` does not exist); Deno 2.9.8's WebGPU is the
  practical way to get naga validation *and* a headless GPU run here. Chromium 157 is in
  the store; headless WebGPU is optional and less reliable than Deno.
* Wiz's `U32` (=`UIntN 32`) wraps exactly like WGSL `u32`, so unsigned integer kernels
  are numerically exact. That is a genuinely favourable mismatch; the unbounded `Nat`
  default is not.
