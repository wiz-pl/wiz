# A WebGPU (WGSL) target, as an exploration

This directory is a **prototype**, not a backend: it compiles a deliberately small,
data-parallel subset of Wiz to WGSL, runs one kernel in a browser (and in Deno's WebGPU),
and checks the numbers against the Wiz interpreter. The design note, including what the
subset rejects and why, is `DESIGN.md` (also in `wiz-notes/webgpu-target.md`).

## Layout

| path | what |
| --- | --- |
| `kernels/add.wiz` | the kernel source: scalar `addScalar`/`maxMulScalar` plus the buffer-indexing entry points |
| `tools/wgsl.mjs` | front end (`wiz parse` s-expression) → subset check → WGSL text |
| `tools/make.mjs` | regenerate `build/*.wgsl`, `build/ref.wiz`, `build/expected.json` |
| `build/add.wgsl`, `build/maxMul.wgsl` | generated WGSL (committed, so the page works without Wiz) |
| `build/expected.json` | the interpreter's values for `inputs.json` |
| `run.js` | one WebGPU run; shared by the page and the Deno check |
| `index.html`, `page.js` | the browser example: inputs, Wiz's values, GPU values, pass/fail |
| `check.mjs`, `check.sh` | validate with wgpu/naga and run, under Deno |
| `check-browser.mjs` | optional headless-Chromium run of the page over the DevTools protocol |
| `tests/reject.mjs`, `tests/reject/` | the subset boundary: fixtures that must be rejected |

## Run

```sh
# regenerate the WGSL and the reference values (needs a Wiz binary)
WIZ=/path/to/wiz node webgpu/tools/make.mjs

# validate with wgpu/naga + run on the GPU, compare with the interpreter
./webgpu/check.sh

# the page
node webgpu/serve.mjs 8080      # then open http://127.0.0.1:8080/

# the rejection tests
WIZ=/path/to/wiz node webgpu/tests/reject.mjs
```

`check.sh` uses Deno and Mesa's lavapipe for a headless GPU. On this machine:

```sh
DENO=/nix/store/…-deno-2.9.8/bin/deno \
MESA=/nix/store/…-mesa-26.2.6 \
VULKAN_LOADER=/nix/store/…-vulkan-loader-1.4.363.0 \
./webgpu/check.sh
```

The Deno run is the automated WebGPU run: `createShaderModule` + `getCompilationInfo`
shows naga's validation diagnostics, and the dispatch runs on lavapipe. The page runs the
same `run.js` in a browser.

## The subset, in one paragraph

A kernel is a scalar function `f (i : Nat) (a b : Array U32) : U32`; the host applies it
at every index, and `i < arrayLength(&out)` is the only control flow the emitter adds.
Types are `U32`, `Bool`, `Nat` (index only) and `Array U32` (parameters only). Terms are
variables, `let`, `match` on `Bool`, acyclic calls to other kernels, `U32.ofNat`,
`UIntN.add/sub/mul/land/lor/xor/lt/le/beq`, and `Array.getD buf i 0` (the zero default is
the WGSL out-of-range read). There is no allocation, no recursion, no closure, no
constructor, no `Nat` arithmetic, no division (Wiz defines `a / 0 = 0`, WGSL does not),
no float, and no IO/FFI. `Array` parameters become `@binding` storage buffers; the result
is written to one `array<u32>` at binding *n*.
