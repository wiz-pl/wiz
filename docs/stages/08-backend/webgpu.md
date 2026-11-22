# A WebGPU (WGSL) prototype

`webgpu/` translates a deliberately small, data-parallel subset of Wiz to WGSL and runs
it on a WebGPU device, comparing every value with the Wiz interpreter. It is a
**source-to-source prototype**, not a compiler backend: `wiz build --target wgpu` does
not exist and nothing in `Wiz/Compiler/` changed. The emitter reads the real syntax tree
printed by `wiz parse`, so it has no second parser, but it also runs before elaboration
and therefore sees builtin syntax only.

```sh
WIZ=/path/to/wiz node webgpu/tools/make.mjs   # regenerate WGSL and expected values
./webgpu/check.sh                             # Deno + wgpu/naga, on a GPU or lavapipe
WIZ=/path/to/wiz node webgpu/tests/reject.mjs # the subset boundary
node webgpu/serve.mjs 8080                    # the browser demo at http://127.0.0.1:8080/
```

`wiz parse` is the front end; `webgpu/tools/wgsl.mjs` is the subset checker and emitter;
`webgpu/tools/make.mjs` regenerates `webgpu/build/*.wgsl`, `ref.wiz`, `expected.json` and
`wide.json`. The generated files are committed, so the page and `check.sh` work from a
checkout without a Wiz binary.

## The subset

A kernel file is a sequence of `def`s. The entry has a `Nat` index first and one or more
`Array U32` buffers after it:

```wiz no-check
def add (i : Nat) (a b : Array U32) : U32 :=
  addScalar (Array.getD a i (U32.ofNat 0)) (Array.getD b i (U32.ofNat 0))
```

| Wiz | WGSL | where |
| --- | --- | --- |
| `U32` | `u32` | scalar parameter, local, result, buffer element |
| `Bool` | `bool` | local, `match` scrutinee, helper result |
| `Nat` | `u32` | the entry index only (no arithmetic) |
| `Array U32` | `array<u32>` storage binding | entry parameters only |

Accepted terms are variables, `let x : T := e; body` (emitted as a WGSL `let`; bindings
are alpha-renamed because WGSL has one scope per function), application of a **name**,
`match` on `Bool` (emitted as `select`, so both arms are evaluated), `U32.ofNat N`,
`UIntN.add`, `UIntN.sub`, `UIntN.mul`, `UIntN.land`, `UIntN.lor`, `UIntN.xor`,
`UIntN.lt`, `UIntN.le`, `UIntN.beq`, and `Array.getD buf i (U32.ofNat 0)`. Helpers take
scalars only and must be acyclic; any name that is a WGSL keyword or reserved word is
refused, as are duplicate parameter names.

Everything else is refused with a message naming the construct: `Float64`/`Float32`,
`String`, `U64`/`I64`, `IO` and FFI, `Nat` arithmetic and `Nat` results, `UIntN.div` and
`UIntN.mod` (Wiz defines `a / 0 = 0`, WGSL leaves a zero divisor unspecified),
`Array.push`/`set`/`size` and any allocation, constructors, lambdas and higher-order
application, direct and mutual recursion, implicit/instance binders, a nonzero
`Array.getD` default, and malformed entries (no buffer, `Bool` or `Nat` result).

The emitter's output is straight-line: one WGSL function per reachable def, storage
bindings for the entry's buffers at `@group(0) @binding(0…)`, the result at binding *n*,
and one compute entry point at `@workgroup_size(64)`:

```wgsl
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let i : u32 = gid.x;
  if (i < arrayLength(&out)) { out[i] = add_at(i); }
}
```

The host creates one `u32` buffer per parameter and the result, all the same length,
dispatches `ceil(n/64)` workgroups, and maps a staging buffer back. `webgpu/run.js` is
the shared host for Deno and the browser.

## What is checked

`webgpu/kernels/add.wiz` has three entry kernels. `add` is the elementwise sum, `maxMul`
exercises `match`/`select` and a multiply, and `mix` uses every supported primitive in
one body (`let`, all arithmetic/bitwise operations, `beq`, `le` and a nested `match`).
`webgpu/check.sh` runs each on 8 inputs that cross 2³² and on 130 generated inputs
(three workgroups, so the bounds guard and a partial last group are exercised), and
compares every element with the Wiz interpreter's `#eval` values:

```
24/24 narrow values, 390/390 wide values, 414/414 in total
```

The reference values come from `wiz check webgpu/build/ref.wiz`: on this base the
interpreter has an `Array` model, so it calls the entry kernel itself
(`add i aNarrow bNarrow`) and interprets `Array.getD` and the buffer indexing too.
`make.mjs` builds the arrays with `Array.push`/`ofList`; only the host's binding order and
dispatch are outside the interpreter. `webgpu/tests/reject.mjs` runs 18 fixtures and
requires each to be rejected with a diagnostic that names the construct (`-- expect:` in
the fixture), not merely to fail.

The browser demo (`webgpu/index.html`, served by `webgpu/serve.mjs`) runs the same
`run.js` and prints the Wiz value, the GPU value and a PASS/FAIL per element. WebGPU needs
a secure context, so use `http://127.0.0.1:8080/`, not `file://`.

## `wiz-gpu/1`: the core profile

`wiz-gpu/1` is the dispatch contract for a Wiz kernel on WebGPU. It is deliberately the
*core* profile: what a browser must support, not what a device may optionally offer.

* **Types.** Scalars are `u32`, `i32` and `f32` only. `Bool` is WGSL `bool` (a local and
  a match scrutinee, not a buffer element). `Nat` may appear only as the entry index. No
  `f64`, `f16`, `u64` or `i64`; no pointers and no aggregates as parameters.
* **Entry.** One compute entry point per dispatch, `@workgroup_size(64)`, a one-dimensional
  `global_invocation_id`; the body starts with the bounds guard
  `if (i < arrayLength(&out))`. One entry means one pipeline per dispatch; a new shape is
  a new entry, not a branch in a mega-kernel.
* **Buffers.** One storage binding per parameter at `@group(0) @binding(n)`, all the same
  length and all `array<u32>` (or `array<i32>`/`array<f32>` in the same position). The
  result is the last binding. The host creates and owns every buffer and maps the staging
  buffer back; nothing allocates on the device inside a kernel.
* **Passes are host-composed.** One compute pass per dispatch, no first-class pass graph,
  and no render/compute interleaving inside a kernel. A pipeline of kernels is a sequence
  of dispatches the host records.
* **No dynamic dispatch.** WGSL has no function values and forbids recursion (mutual too);
  a helper is a direct, acyclic call. That is why the profile has one entry per dispatch
  rather than a tagged union of kernels.
* **Limits.** The WebGPU 2026 CRD defaults are 128 MiB per storage-buffer binding,
  256 MiB per buffer and 65,535 workgroups per dimension. `maxImmediateSize` gates
  immediates; timestamp queries, subgroups and `f16` are optional features and are **not**
  in core v1. The host must query and enforce the limits, not assume them.
* **Status.** The prototype in this directory emits the `u32`/`Bool` part of the profile
  (plus the `Nat` index); `i32`, `f32` and the binding-shape checks are the v1 additions
  and are not implemented. `webgpu/check.sh` checks what exists against the Wiz
  interpreter on lavapipe or a GPU; CI does not run it.
* **Versioning.** `wiz-gpu/1` is this table. A new scalar type, a second entry shape or a
  required feature is `wiz-gpu/2`.

**Unverified.** Mobile WebGPU coverage, Firefox-Android's flag status and the "84 % global
support" figure are secondary sources. Whether `subgroups` and immediates are available in
Safari 26.x or Firefox 14x today is unverified (the CRD lists them; shipping differs), as
is Safari's `f16` support. Per-dispatch and per-call overheads are order-of-magnitude from
secondary benchmarks, not measured here. The limits and feature status are from the WebGPU
CRD as cited in `wiz-notes/sota-web-wasm-gpu.md` §3 and §7 (fetched 2026-11-22); the
emitted subset is defined by `webgpu/tools/wgsl.mjs` and exercised by `webgpu/check.sh`.

## Why this is not yet an IR backend

The existing backends consume the IR after lowering and Perceus (`Compiler/IR.lean`):
values are reference-counted heap objects, `Nat` is a GMP bignum above 62 bits, and
closures are `pap`/`ap`. A WebGPU shader has no heap, no allocator, no function values and
no recursion. Three blockers follow:

1. **Numbers and data.** `Nat` is unbounded and every aggregate is an RC object; WGSL has
   only `bool`, `i32`, `u32`, `f32` (and optional `f16`). This subset is honest but it
   means a kernel must use `U32` and fixed-length buffers, not Wiz's default `Nat`, lists
   or `Vec`.
2. **Control.** WGSL forbids recursion (mutual too) and has no indirect calls. Wiz's
   structural recursion, type-class dictionaries and closures all need a call stack or a
   function value; the prototype refuses them rather than partially compiling them.
3. **The host boundary.** A dispatch is asynchronous: the host creates buffers, submits
   and maps a staging buffer. Wiz's `IO`/FFI model has no device or queue, and there is no
   `Float32` in Wiz (only `Float64`, which core WebGPU lacks).

A real target would need a kernel declaration in the language (buffer modes and dispatch
shape), elaboration and proof/quantity erasure, a monomorphised machine-number fragment,
and a host runtime with explicit limits. The prototype instead fixes a map-shaped ABI by
convention and is useful as a checked answer to "what would a GPU target cost?", not as a
fourth backend.

## Tests and files

The checks are standalone Node/Deno scripts, not `lake test` groups; CI does not run
them. On a headless machine `check.sh` finds Deno and Mesa's 64-bit lavapipe in the Nix
store when they are not on `PATH`; `DENO`, `MESA`, `VULKAN_LOADER` and `VK_ICD_FILENAMES`
override the search. The adapter was `llvmpipe` (Mesa 26.2.6) through Deno 2.9.8, whose
WebGPU is wgpu/naga. `webgpu/check-browser.mjs` is an optional headless-Chromium run of
the page and was not part of the counts above.
