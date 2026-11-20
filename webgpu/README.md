# A WebGPU (WGSL) target, as an exploration

This directory is a **prototype, not a backend**: it compiles a deliberately small,
data-parallel subset of Wiz to WGSL, runs three kernels on a WebGPU device, and checks
every value against the Wiz interpreter. It is not `wiz build --target wgpu`; that target
does not exist and the C/LLVM/Wasm compilers are untouched. The design note, including
the subset, the host ABI and the three blockers, is `DESIGN.md` (also in
`wiz-notes/webgpu-target.md`); the stage documentation is
`docs/stages/08-backend/webgpu.md`.

## Proof

One command, after `lake build wiz` in the worktree:

```sh
WIZ=.lake/build/bin/wiz ./webgpu/check-all.sh
```

It prints the value comparison (expected `414/414 values agree with the Wiz interpreter`)
and the boundary result (expected `all 18 non-subset fixtures rejected`). The optional
Chromium page harness (`check-browser.mjs`) was not run here because the environment has
no Chromium binary; Deno 2.9.8 + Mesa 26.2.6 lavapipe (`check.sh`) is the automated proof.

## Layout

| path | what |
| --- | --- |
| `kernels/add.wiz` | three kernels: `add`, `maxMul` (match/select) and `mix` (every primitive) |
| `tools/wgsl.mjs` | front end (`wiz parse` s-expression) → subset check → WGSL text |
| `tools/make.mjs` | regenerate `build/*.wgsl`, `build/ref.wiz`, `build/expected.json`, `build/wide.json` |
| `build/add.wgsl`, `build/maxMul.wgsl`, `build/mix.wgsl` | generated WGSL (committed, so the page works without Wiz) |
| `build/expected.json` | the interpreter's 8-element values for `inputs.json` |
| `build/wide.json` | the interpreter's 130-element values (three workgroups) |
| `build/ref.wiz` | the kernel source plus the `#eval` calls that produce both JSON files |
| `run.js` | one WebGPU run; shared by the page and the Deno check |
| `index.html`, `page.js` | the browser demo: inputs, Wiz's values, GPU values, pass/fail |
| `check.mjs`, `check.sh` | validate with wgpu/naga and run all 414 values, under Deno |
| `check-all.sh` | `check.sh` plus the rejection fixtures |
| `tests/reject.mjs`, `tests/reject/` | the subset boundary: 18 fixtures, each rejected with a named construct |
| `check-browser.mjs` | optional headless-Chromium run of the page over the DevTools protocol |

## Run

```sh
# the whole harness (value tests; needs WIZ for the rejection fixtures)
WIZ=/path/to/wiz ./webgpu/check-all.sh

# regenerate the WGSL and the reference values (needs a Wiz binary)
WIZ=/path/to/wiz node webgpu/tools/make.mjs

# validate with wgpu/naga + run on the GPU, compare with the interpreter
./webgpu/check.sh

# the page
node webgpu/serve.mjs 8080      # then open http://127.0.0.1:8080/

# the rejection tests
WIZ=/path/to/wiz node webgpu/tests/reject.mjs
```

`check.sh` uses Deno and a Vulkan driver. It finds Deno and Mesa's 64-bit lavapipe in the
Nix store when they are not on `PATH`; `DENO`, `MESA`, `VULKAN_LOADER` and
`VK_ICD_FILENAMES` override the search. The current run (Deno 2.9.8, Mesa 26.2.6
lavapipe) reports:

```
✓ add (narrow): 8/8 values
✓ maxMul (narrow): 8/8 values
✓ mix (narrow): 8/8 values
✓ add (wide, 130 elements): 130/130 values
✓ maxMul (wide, 130 elements): 130/130 values
✓ mix (wide, 130 elements): 130/130 values
414/414 values agree with the Wiz interpreter
all kernels agree
```

The Deno run is the automated WebGPU run: `createShaderModule` + `getCompilationInfo`
shows naga's validation diagnostics, and the dispatch runs on the GPU (or lavapipe). The
page runs the same `run.js` in a browser. The rejection harness checks that each fixture
fails *and* that its message contains the construct named in the fixture's `-- expect:`
line.

## The subset, in one paragraph

A kernel is a scalar function `f (i : Nat) (a b : Array U32) : U32`; the host applies it
at every index, and `i < arrayLength(&out)` is the only control flow the emitter adds.
Types are `U32`, `Bool`, `Nat` (index only) and `Array U32` (parameters only). Terms are
variables, `let` (emitted as a WGSL `let`), `match` on `Bool`, acyclic calls to other
kernels, `U32.ofNat`, `UIntN.add/sub/mul/land/lor/xor/lt/le/beq`, and
`Array.getD buf i 0` (the zero default is the WGSL out-of-range read). There is no
allocation, no recursion (direct or mutual), no closure, no constructor, no `Nat`
arithmetic, no division (Wiz defines `a / 0 = 0`, WGSL does not), no float, and no
IO/FFI. `Array` parameters become `@binding` storage buffers; the result is written to
one `array<u32>` at binding *n*. Every other construct is refused with a diagnostic that
names it, and a WGSL keyword used as a name is refused too.
