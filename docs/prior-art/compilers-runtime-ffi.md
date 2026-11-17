# Compilers, runtimes and FFI: prior art

A survey, written in November 2026, of the engineering half of the Wiz toolchain set
against prior art: bootstrap order and trust in the bootstrap, code generation, the
runtime (reference counting against tracing GC), the C FFI and its ABI, native
representations, regions and linearity, cross-compilation, the compiler cache, test
strategy and reproducible builds. It ends with a novelty assessment, a risk register and a
bibliography. Where the toolchain has changed since the survey was first drafted, the text
says what the code does now; package indexes and dependency resolution are covered
separately in [Registries and build systems](registries-build-systems.md).

Confidence markers: **[H]** high (canonical, or checked against the source); **[M]**
medium (known from documentation or the project, not re-read upstream); **[L]** low, an
inference. Literature details marked [M] were not re-checked against the original source.

---

## 0. Summary

1. **The bootstrap shape is standard and sound; the assurance story is partly written
   down.** Appel's *axiomatic bootstrapping* [appel94] is the vocabulary: a bootstrap is a
   claim ("this source, built this way, yields this binary"), and the interesting part is
   which links are axioms. Wiz has a three-stage fixpoint (`scripts/fixpoint.sh`: the
   self-hosted compiler's C is byte-identical across stages, in the Boehm mode by default
   and with `--rc` on request) and a published list of what the kernel trusts
   ([CoreSpec](../CoreSpec.md) §16, [the trust ledger](../trust-ledger.md)). It has no
   recorded hash chain for the compiler binaries and no independent check of the
   Lean-hosted stage 0. Prior art that addresses exactly this: Appel (stages as theorems),
   Wheeler's diverse double-compiling [wheeler05], Strub et al.'s self-certification
   [strub12] and independent kernel checkers [lean4lean25].
2. **The fixpoint is already DDC-shaped.** Stage 1's C is produced by the self-hosted
   compiler as *built by the Lean toolchain*; stage 2's by the same source as *built by
   itself*. Their byte equality is Wheeler's comparison, made at the C level, with the
   Lean toolchain as the diverse compiler. What is missing is to say so, record the
   hashes, and note the shared component (the C compiler builds both binaries).
3. **Byte-for-byte fixpoints are strong but narrow.** The fixpoint runs nightly, not on
   pull requests, and covers one input set (the self-hosted sources) and the default
   flags. Anything outside that set (`lib/`, `examples/`, `--rc` by default, `--header`,
   the LLVM backend) is an unstated axiom.
4. **The FFI is small, typed and mostly well chosen.** The marshalling kinds (`n u f s b p
   w e v`, plus by-value structs and callbacks) are a fixed, documented table (stage 9,
   [09-ffi.md](../stages/09-ffi.md)). The two remaining hazards are (a) `Nat` at the
   boundary (the Lean toolchain stops on a value above 64 bits; the self-hosted runtime
   stops from 2^63, stage 21p) and (b) finalizer timing differing between reference
   counting (deterministic drop) and Boehm GC (at collection). Haskell's FFI [ghcffi],
   Swift's Clang importer and ownership conventions [swiftffi], Rust's `repr(C)`/bindgen
   [rustffi], Nim's `importc`/`header`/`emit` and CakeML's abstract FFI oracle
   [cakeml14] each supply a piece.
5. **Checked `glue` is the most distinctive runtime feature.** A C subset whose
   expressions and statements are typed against imported prototypes, with pointers,
   casts, indexing and `goto` rejected, is not what bindgen, inline-c or Swift do (they
   trust C). The nearest relatives are Checked C [checkedc18] and Cyclone [cyclone02].
   The survey's suggestion: grow in that direction (bounds and ownership annotations)
   rather than toward raw pointers.
6. **Type-level `implemented_by` goes beyond Lean, and needs coherence.** Lean's
   `@[implemented_by]` is function-level and its unboxed integers are built in; Wiz's
   `attribute [implemented_by mk get] T.mk` is user-level and width-independent. The
   hazard is that conversion ignores the attribute, so two convertible types could get
   different layouts. Wiz now accepts a native representation only on a `sealed` type
   (stage 22k), which closes the case the survey worried about.
7. **GC and RC are the right two modes, but they are observably different.** RC frees
   deterministically (fine for `fclose`), Boehm at collection (not fine). The prior-art
   answer: make release explicit (`File.close` exists in `lib/Sys.wiz`) and keep
   finalizers as a backstop. Perceus is leak-free only for acyclic data; mutable cells
   (`lib/Ref.wiz`, `lib/MVar.wiz`) make cycles possible in principle, and Koka's answer is
   Perceus plus an optional tracer [perceus21].
8. **Do not build Tofte–Talpin region inference.** MLKit [tofte94] shows it works and
   what it costs: effect inference, region representation inference and a different
   backend. `lib/Region.wiz` (regions as erased type indices plus scope tokens, the
   `runST` trick [st95] with `Outlives` evidence) gets Rust-style aliasing guarantees
   from QTT alone. Keep it a library; add arena primitives with linear tokens if
   allocation control is wanted.
9. **Cross-compilation is a toolchain problem, not a compiler problem.** The C backend
   emits portable C. What is missing is (a) a target triple that drives `cc`, sysroot
   and flags (`--target` today selects the backend: `c`, `llvm` or `wasm`), (b)
   generated layout assertions, (c) a cross-capable runtime build, and (d) a host-versus-
   target differential test under `qemu-user`. The cache key already carries a target
   tag (host triple and pointer width). Prior art for the shape: Zig's `zig cc`, Rust's
   target tiers, GCC's build/host/target triples.
10. **The highest-value test oracle is mostly free.** Wiz has two interpreters (`#eval`,
    `#run`), two compilers, two memory modes and a value-level semantics matrix that
    already compares some of them ([semantics-matrix.md](../semantics-matrix.md)).
    "Same program, every pipeline, identical output" is a translation-validation oracle
    that catches lowering and RC bugs no unit test will. Prior art on measuring such tests:
    Csmith [csmith11], the OOPSLA'19 compiler-fuzzing study [compfuzz19], Alive2
    [alive2-21], C-Reduce [creduce12].

---

## 1. Landscape

Four tables. "Trusted base" lists what a bootstrap assumes. Read `→` as "bootstraps
through".

### 1.1 Bootstrapping, self-hosting and trust

| system | implementation language | bootstrap chain | trusted base | verified? | lesson for Wiz |
|---|---|---|---|---|---|
| **Lean 4** [lean4-21] [H] | C++ and Lean 4 | stage0 (generated C checked in) → stage1 → stage2 [M] | C compiler, kernel, `@[implemented_by]`/`@[extern]` natives | kernel independently re-checkable (Lean4Lean [lean4lean25], Nanoda [nanoda]); not end-to-end | staged bootstrap with checked-in stage0 is the industrial norm; publish stage hashes |
| **Idris 2** [idris2-21] [H] | Idris 2 | Scheme bootstrap files → Chez → self-hosted compiler [M] | Chez, kernel, `%foreign` | no | the existence proof that a dependently typed elaborator can be self-hosted; Wiz's closest peer |
| **Agda** [M] | Haskell | GHC-hosted; not self-hosting | GHC, Agda kernel, `COMPILE` pragmas | no | not self-hosting is a legitimate choice; backends by pragma keep the kernel clean |
| **GHC** [M] | Haskell | previous GHC → stage1 → stage2 | previous GHC, RTS/Cmm, primops | no | multi-stage builds exist to detect the class of bug Wiz's fixpoint targets |
| **Chez Scheme** [chez06] [H] | Scheme | boot files plus incremental native compiler | boot file, assembler | no | self-hosting with checked-in boot images is the cheapest reproducible bootstrap |
| **MLton** [M] | SML | built by an SML compiler (SML/NJ or a previous MLton) | SML compiler | no | whole-program monomorphisation gives unboxing without type-level layout hacks |
| **CakeML** [cakeml14] [H] | HOL4, generates machine code | verified compiler, bootstrapped inside the logic [M] | HOL4 kernel, FFI oracle, assembler/linker | end-to-end to machine code | the FFI-as-oracle design (§2.2) and proof-gated bootstrapping |
| **CompCert** [compcert09] [M] | Coq, extracted to OCaml | not self-hosting | Coq kernel, extraction, parser, assembler/linker | end-to-end for the middle and back end | a verified pass is worth more than a verified whole; the unverified edges are the risk |
| **Coq/Rocq** [coqcoq20] [H] | OCaml | `coqchk` as an independent checker | Coq kernel, OCaml runtime | a checker verified in Coq (MetaCoq); erasure verified | "two checkers, one term language" is a pattern Wiz also has |
| **F\*** [strub12] [S] | F\* → OCaml | self-certification: the type checker is bootstrapped and proved in Coq | Coq, F\* kernel, OCaml | yes, for the checker | the canonical paper for "bootstrap and prove the bootstrap" |
| **Rust** [M] | Rust | stage0 binary → stage1 → stage2; `mrustc` as an independent implementation | stage0 binary | no | `mrustc` is the DDC-style answer |
| **Swift** [M] | C++ and Swift | previous compiler; ABI-stable since Swift 5 | previous compiler, runtime | no | library evolution and `@frozen` are ABI management done explicitly |
| **Koka** [koka14] [M] | Koka | bootstrapped from an earlier build [L] | host compiler, Perceus runtime | no | Perceus plus optional GC is the runtime model Wiz's RC mode follows |
| **Nim** [M] | Nim | self-hosted, `koch` bootstrap; C backend | C compiler | no | `importc`/`header`/`emit` is the closest FFI analogue to `import_c` and `glue` |

### 1.2 Values, memory, backends

| system | value representation | memory management | backends | notes for Wiz |
|---|---|---|---|---|
| **Lean 4** | one word `lean_object*`; header with count and tag; fixed-width scalars unboxed by type | precise RC (Counting Immutable Beans [beans19]), non-moving, no cycle collector; thread-shared objects have negative, atomic counts | C, LLVM, interpreter | Wiz's host runtime follows the same scheme, including the shared-count rule (stage 25a) |
| **Idris 2** | Chez objects; refc C structs | Chez GC; refc has its own runtime | Chez (default), refc (C), Racket, Node | a dependently typed language with several backends and one default is normal |
| **Agda** | GHC closures / JS objects | host GC | GHC, JS | proofs erased before code generation |
| **GHC** | closures with info tables, tagged pointers, representation polymorphism | generational copying GC (also compacting and non-moving) | native code, LLVM, unregisterised C, via Cmm | Cmm is the precedent for a small, still-typed IR |
| **Chez** | tagged fixnums and records | precise generational GC | native code via nanopass | many tiny IRs; Wiz chose one IR, which is defensible for a readable compiler |
| **MLton** | monomorphised, representation-inferred, untagged where possible | copying GC | native via C or assembly | layout decisions belong to a representation pass, not to type identity |
| **CakeML** | tagged 64-bit words, heap objects | verified copying GC | verified x86-64, ARM, … | the GC itself can be verified; not something Wiz needs |
| **Wiz (Lean toolchain)** | tagged word, low bit marks a scalar; `wiz_hdr` header (`int64_t rc`, tag, size); GMP for large `Nat`; `WIZ_TAG_RAW` box for 64-bit words | Perceus RC with Lean's thread-shared counts; leak check at exit; `WIZ_LEAKS`/`WIZ_WATCH` for debugging | C (runtime pasted in), LLVM (textual IR, runtime compiled with `-DWIZ_API=`), WebAssembly (stage 8f; no RC, no IO/FFI) | three backends over one ANF IR |
| **Wiz (self-hosted)** | the same header, tags and layouts as the host runtime (stage 21w, checked by `_Static_assert`s in `selfhost/rt.c`), plus flat pair chains with low-bit tail offsets and 63-bit `Nat` scalars | Boehm GC by default, or `WIZ_RC` Perceus (size-class free lists, worklist free, exit check that every object was freed) | C only | two memory modes in one backend; not yet thread-safe |

### 1.3 FFI and interop

| system | declare foreign | header import | structs by value | callbacks | ownership/lifetime | finalizers | strings/bytes |
|---|---|---|---|---|---|---|---|
| **Haskell** [ghcffi] [H] | `foreign import ccall safe`/`unsafe` | `hsc2hs`/`c2hs`; `CApiFFI` reads headers | via `hsc2hs` offsets; `Storable` | `"wrapper"` imports + `FunPtr` | `StablePtr` pins a closure; `ForeignPtr` = pointer + finalizer | `ForeignPtr` finalizer, `mkWeak` | `CString`, pinned `ByteString` |
| **Rust** [rustffi] [H] | `extern "C" { fn f(..); }`, `#[no_mangle]` | `bindgen`, `cxx` | `#[repr(C)]` by value | `extern "C" fn`, `extern "C-unwind"` | manual: `Box::into_raw`/`from_raw`, `ManuallyDrop` | `Drop` on the Rust side | `CStr`/`CString`, pointer + length |
| **Swift** [swiftffi] [M] | automatic from imported modules | Clang importer: headers become modules, macros imported | imported C structs by value, `@frozen` | `@convention(c)` | +0/+1 conventions, `Unmanaged`, `withExtendedLifetime` | `deinit`; none for C pointers | `String` ↔ `const char*` bridging |
| **Nim** [M] | `{.importc, header: "h.h".}` | per-proc `header` | `{.bycopy.}` | `{.cdecl.}` procs | manual | `=destroy` hooks | `cstring` |
| **CakeML** [cakeml14] [H] | abstract `ffi` oracle in the semantics; byte arrays in and out | none | none | none | none (the oracle is pure) | none | `Word8Array` |
| **Wiz (Lean toolchain)** | `extern "cname" (header := "h.h")? name : T`; `export` | `import_c "h"` → `C.name`, through `cc -E -P`; pointer types become foreign types, `struct` by value becomes a `c_struct` (stage 9i) | `c_struct` | `A → B` borrowed for the call; `Callback (A → B)` owned until `wiz_release` (stage 9g) | `foreign_type T (finalizer := "f")`: wrapped, reference-counted, borrowed during a call | at the last `dec` | `String` ↔ `const char*`; `Bytes` buffers, `const void *, size_t n` mapped to one `Bytes` |
| **Wiz (self-hosted)** | the same surface | headers read from disk, no preprocessor (`selfhost/CParse.wiz`, `CGlue.wiz`, stage 21aa); declared `c_struct`s only | declared `c_struct` | as above (stage 21q) | as above | at collection (Boehm) or last `dec` (`--rc`) | no `Bytes` buffer arguments yet |

### 1.4 Caching, cross-compilation, tests

| system | artifact cache | separate compilation | cross-compilation | test and validation |
|---|---|---|---|---|
| **Lean 4** [olean] [M] | `.olean` = mmapped compacted region at a name-derived base address | per module | per-host toolchains | Mathlib as a giant regression suite; Lean4Lean/Nanoda re-check |
| **GHC** [M] | `.hi` interface with flag and source hashes; recompilation avoidance | yes | cross GHC via LLVM/C | testsuite with `should_fail`/`run` oracles |
| **ccache** [ccache] [H] | direct mode plus a manifest per source (include list and hashes) | n/a | n/a | n/a |
| **Nix** [nix06] [M] | store paths from inputs; binary caches | n/a | `crossSystem` | reproducibility checks |
| **Wiz** | per-command content-addressed `.wizc`; per-module `.wizr` region with `.wizs` checksum sidecar; read-only layers; SHA-256 output manifests and `wiz cache verify` (stage 11c) | per module | none; native builds on aarch64 | kernel differential and `False` fuzzer, self-hosted differential cases, semantics matrix, nightly fixpoint, reproducibility check in CI |
| **Csmith / YARPGen** [csmith11] [yarpgen20] | n/a | n/a | n/a | typed random program generation, differential execution, reduction |
| **Alive2** [alive2-21] | n/a | n/a | n/a | bounded translation validation of IR→IR with SMT |

---

## 2. Per-feature comparison and recommendations

### 2.1 Bootstrap order and self-hosting discipline

**Where Wiz is.** The self-hosted compiler (`selfhost/*.wiz`: lexer, parser, kernel,
frontend, backend, C header parser and glue checker, driver) is compiled to C by the Lean
toolchain (stage 1); stage 1's binary compiles the same sources again, and so on. The
fixpoint script checks that every stage's C is byte-identical to stage 1's, three stages
by default, in the Boehm mode or with `--rc`. The self-hosted kernel is a second
implementation of the core on a fragment ([CoreSpec](../CoreSpec.md) §15), and the
self-hosted frontend is a bidirectional elaborator with metavariables and unification.

**Prior art, and what each piece is for.**

* **Appel, *Axiomatic bootstrapping* [appel94] [H].** Frames a bootstrap as a chain of
  implications, each proved or assumed. The useful discipline is to write the axiom list
  down. For the kernel, Wiz has done this: [CoreSpec](../CoreSpec.md) §16 lists axioms,
  `builtin` registrations, the templates, the kernel's own motive types, erasure and the
  backends, and [the trust ledger](../trust-ledger.md) tracks every source of trust in
  `lib/` in CI. The bootstrap's own axioms (the Lean compiler and runtime, the C compiler
  and libc, GMP, Boehm GC, the unchecked stage 0) could be listed beside the fixpoint in
  the same way.
* **Thompson [thompson84] [H]** and **Wheeler's DDC [wheeler05] [H].** A self-reproducing
  compiler can hide a backdoor that no source review finds. DDC detects it by compiling
  the source with a second, independent compiler and checking that the results agree
  bit for bit. The Wiz fixpoint is this argument at the C level: stage 1's C comes from
  the compiler as built by the Lean toolchain, stage 2's from the compiler as built by
  itself. Suggestion: record the hashes (Lean toolchain binary, stage binaries, stage C)
  as a manifest per run, extend the compared outputs to `lib/` and `examples/`, and state
  that the C compiler is shared by both paths (so it is a trusted component, which
  Wheeler's method would want to diversify too). Cost: low; it reuses `fixpoint.sh`.
* **Strub et al. [strub12] [S].** The stronger version: prove the checker correct while
  bootstrapping it. Out of scope for Wiz, but it argues for keeping the kernel small and
  the term language stable. A Wiz-hosted kernel checked against the Lean kernel is a
  differential approximation of this, not a proof.
* **Lean4Lean, Nanoda, `coqchk` [lean4lean25] [H] [nanoda] [M].** Independent checkers of
  the same term language are the cheap industrial version of "prove the kernel". Wiz's two
  kernels share an author and an algorithm, so a shared misconception is invisible to
  their differential test, which compares verdicts and printed types. Two of the
  survey's hardening steps now exist: a `False` fuzzer that compares the two kernels'
  verdicts and normal forms on closed terms claiming to inhabit `Empty`
  (`Tests/FalseFuzz.lean`); and a third voter, WizMeta, a declarative specification of
  the core rules with a reference checker written from it, compared with the Lean kernel
  on the differential test's terms ([Status](../Status.md), "Two kernels"). What remains
  is a generator that reaches every former.
* **CakeML [cakeml14] [H]** shows the end state: a verified compiler bootstrapped inside
  the logic. Not a near-term goal, but its shape (verified passes, an explicit oracle,
  a proof-gated bootstrap) is a good target architecture to keep in view.

**Order of the self-hosting work.** The survey proposed an order by dependency: modules
and imports first (nothing else can be a library), then the driver, named arguments,
universe polymorphism, classes, the proof surface and tactics, then elaboration-time
evaluation, macros and `deriving`, and last the wider runtime surface. Most of it has
since landed in the self-hosted frontend: modules (stage 21y), named arguments (21ab),
the proof surface (21z), `import_c` and `glue` (21aa), notation and macros (21ac, first
milestone), tactics (21ad, core), classes and instances (30a) and `deriving` (30b). The
open item from that list is universe polymorphism, which universe-polymorphic classes
need ([30-selfhost-typeclasses.md](../stages/30-selfhost-typeclasses.md), "What remains
for full parity").

The rationale still holds for what remains. Classes are elaborator work over a fixed
kernel; macros need an evaluator; an evaluator needs the frontend to compile its own AST
types, which needs modules and, for `lib/`, classes. Lean took the same order: a
compiler that can bootstrap its own macro expander comes after the language it expands.

### 2.2 FFI design and ABI

**Where Wiz is.** Three declaration forms (`extern`, `import_c`, `glue`), plus
`foreign_type`, `c_struct`, `export` and callbacks. Each parameter and result has a
marshalling kind (`RVal.FKind` in `Wiz/Compiler/Run.lean`): a letter, a by-value struct
`<ctype|header|fields>`, or a callback `k[sig]`/`K[sig]`. The letters are `n` (`Nat` →
`uint64_t`), `u` (`UInt64`), `f` (`Float64` → `double`), `s` (`String` → `const char*`),
`b` (`Bool` → `int`), `p` (a `foreign_type` pointer), `w` (a Wiz value passed as is),
`e` (erased, left out of the prototype) and `v` (`Unit` → `void`). The kinds are part of
the extern's identity: its builtin key is `extern:cname:kinds:result:io:header:finalizer`
(`Wiz/Elab/Command.lean`), so a changed signature cannot silently reuse an old wrapper.
That is a good, cheap ABI-versioning instinct.

**What the prior art says, item by item.**

* **Automatic header import.** Swift's Clang importer is the high-water mark: modules,
  macros, typedefs, structs, nullability. Rust's bindgen and Nim's `importc`/`header` are
  the pragmatic versions. Wiz's `import_c` runs the header through `cc -E -P` and a
  parser for a small C subset (`Wiz/FFI/CParse.lean`). The survey suggested importing
  pointer typedefs as opaque foreign types and requiring an explicit declaration for
  structs by value; the Lean toolchain now does both and more (stage 9i): `struct foo *`
  and `FILE *` become foreign types without a finalizer, `struct foo` by value becomes a
  `c_struct` generated from the header's definition, and `const void *buf, size_t n`
  becomes one `Bytes` argument, each with an opt-out. The self-hosted `import_c` does not
  map structs or pointers automatically yet.
* **Checked `glue`.** The design (scalar locals, assignments, `if`/`while`/`for`/
  `return`, calls to imported prototypes with their types checked; dereference,
  address-of, casts, indexing, `goto`, `asm` and `sizeof` rejected; stage 9c) is the most
  novel FFI feature in the tree. Stage 9i widened it to struct locals, field access and
  `&t` passed directly to a C function that takes a pointer to that struct. Its nearest
  relatives are Checked C [checkedc18] (a safe C dialect with bounds annotations) and
  Cyclone [cyclone02]. Suggestion: grow annotations, not expressiveness. A `Bytes`
  parameter with an explicit length and a checked index construct would cover the common
  "copy or scan a buffer" case; pointer arithmetic should wait until bounds are
  expressible.
* **CakeML's FFI oracle [cakeml14].** In CakeML the FFI is an abstract state machine over
  byte arrays; the verified compiler never sees C, and the only axiom is the oracle's
  behaviour. Wiz cannot adopt it wholesale (its FFI is typed), but the instinct transfers:
  name the FFI boundary in the trusted base. Wiz does: `extern` declarations are axioms in
  [CoreSpec](../CoreSpec.md) §16 and rows in [the trust ledger](../trust-ledger.md).
* **Ownership conventions.** Swift's +0/+1 and GHC's `StablePtr` are the two mature
  answers. Wiz documents its rules per form (stage 9d for foreign pointers, 9g for
  handles and callbacks: borrowed for a call, or owned until `wiz_release`). The
  self-hosted backend's `--header` output carries the ownership table as comments
  (stage 21aa).
* **Finalizers.** `foreign_type T (finalizer := "f")` runs `f` when the last reference
  goes. Under reference counting that is deterministic; under Boehm it is at a
  collection. That is an observable difference between two supported modes: a test that
  checks the order of `fclose` calls can pass in one and fail in the other. Java and
  Cyclone both learned that finalizer timing must not be load-bearing. Suggestions:
  document finalizers as a backstop; make explicit release the supported path (the
  `File.close`/`Fd.close` functions in `lib/Sys.wiz` are this); and test that both modes
  give the same output and live-object count, not the same finalizer order.
* **Callbacks.** Wiz specifies the C shape (a trampoline per signature whose first
  parameter is the context, then the context as `void *`) and the ownership (borrowed
  for the call, or `Callback` kept until `wiz_release`). The open question is rooting
  under Boehm: a context kept in `malloc`ed C memory is not scanned by a conservative
  collector. In the self-hosted runtime's GC mode `wiz_retain`/`wiz_release` do nothing,
  so a closure that C stores across a collection relies on being reachable some other
  way. GHC's `"wrapper"` allocates a stable pointer and requires an explicit
  `freeHaskellFunPtr`; Swift uses `Unmanaged`. Stage 21aa lists "callback roots on both
  collectors" as deferred.
* **ABI drift.** The generated wrapper is C in both backends; everything is `static` when
  the runtime is pasted into the program, and the LLVM backend compiles the runtime with
  `-DWIZ_API=` so its functions are exported. The self-hosted backend's `--header`
  defines `WIZ_ABI_MAJOR`/`WIZ_ABI_MINOR` (1/0). A linked `wiz_abi_version` symbol, which
  would catch linking against a different runtime at link time, is deferred (stage 21aa).

**ABI v1.** The survey proposed a table of kinds, C types and ownership; its cheap parts
were adopted as "ABI v1" in the self-hosted `--header` (stage 21aa). Values are 64-bit;
`wiz_val` is `uintptr_t`.

| Wiz type | kind | C param | C result | ownership | note |
|---|---|---|---|---|---|
| `Nat` | `n` | `uint64_t` | `uint64_t` | value | a value above 64 bits stops the program (Lean toolchain); from 2^63 in the self-hosted runtime |
| `NatObj` | `w` | `wiz_val` | `wiz_val` | +0 in, +1 out | the runtime number itself, possibly big (`lib/Word.wiz`) |
| `UInt64` | `u` | `uint64_t` | `uint64_t` | value | exact |
| `UIntN w` / `IntN w` | `w` | `wiz_val` | `wiz_val` | +0 / +1 | tagged scalar below 2^63, `WIZ_TAG_RAW` box, GMP above 64 bits |
| `Float64` | `f` | `double` | `double` | value | |
| `Bool` | `b` | `int` | `int` | value | 0/1 |
| `String` | `s` | `const char *` | `char *` | borrowed in, caller-owned out | UTF-8, NUL-terminated |
| `Bytes` | `w` | `wiz_val` | `wiz_val` | +0 / +1 | the type for binary data |
| `Unit` | `v` | omitted | `void` | — | |
| a 0-quantity argument | `e` | omitted | — | — | left out of the prototype, not passed as a dummy |
| `foreign_type T` | `p` | `void *` | `void *` | +1 wrapped; borrowed during a call | the wrapper holds the finalizer |
| a Wiz data type | `w` | `wiz_val` | `wiz_val` | +0 / +1 | handles (9g), runtime natives and `implemented_by` targets |

Rules worth writing down with it: fixed-width types (`uint64_t`, `uintptr_t`), never
`long`/`size_t`, in the Wiz-facing ABI; no `_Bool`, bitfields, `long double` or variadic
Wiz functions; structs by value only through `c_struct`; every `extern` gets a prototype
in `--header`.

**The `Nat` decision.** The survey suggested marshalling `Nat` as a boxed `wiz_val` by
default and requiring `UInt64` for the machine word. The current behaviour is safer than
when the survey began: neither toolchain truncates silently any more (the Lean runtime's
`wiz_in_nat` stops with "a number is too big for a C integer"; the self-hosted runtime
stops from 2^63, stage 21p). The remaining issue is that the two toolchains stop at
different values. Boxed `Nat` by default is listed as deferred in stage 21aa.

### 2.3 Native representation

**Where Wiz is.** Tagged words (`WIZ_BOX`/`WIZ_IS_SCALAR` in `runtime/wiz_rt.h`), a
16-byte header `{rc, tag, size}`, reserved tags for closures, big numbers, raw words,
foreign pointers, bytes, arrays, text, maps, thunks, word arrays, word maps and intern
tables, and GMP above `WIZ_MAX_SMALL` (2^62 − 1). The runtime is pasted into every
generated C file (`runtime/WizRuntime.lean`, by `include_str`), so `cc -O2` inlines the
word operations. Type-level native representation is `attribute [implemented_by mk get]
T.mk` (stage 22d): erasure never builds the model's object, a constructor becomes `mk`
and a match reads the field with `get`, while the kernel keeps the model. `UIntN w` is
width-independent: the representation depends only on the bits.

**Comparison.**

* **Lean** [H] unboxes only its built-in fixed-width types, and `@[implemented_by]` is
  function-level; a user cannot define a new unboxed type. Wiz's feature is a real, if
  modest, extension, and width independence means generic code over `w` can build and
  read a word without knowing `w`.
* **GHC and MLton** [M] put unboxing in a representation pass over the whole program
  (strictness, unboxed tuples, worker/wrapper). The lesson is that layout must be a
  function of use and coherent under conversion.
* **Swift** [M] makes layout part of the ABI (`@frozen`), the right precedent for
  `c_struct`: once a struct crosses the FFI boundary, its layout is a compatibility
  promise.

**The coherence hazard.** Conversion ignores `implemented_by`, and the attribute is
stored by name. If two convertible types could carry different native representations,
erasure's choice would depend on which name a term mentions, and a `cast` between them
(the identity at run time) would change layout. Status of the survey's suggestions:

1. **Sealing is mandatory** for a native representation: the elaborator rejects one on a
   type that is not `sealed inductive` (stage 22k; [Status](../Status.md), F14). Done.
2. **The representation is recorded in erasure** as a `repr:` registration (tag, field
   count, arities; `Wiz/Compiler/Erase.lean`), and it is a row in the trust ledger.
   Done.
3. **Layout assertions.** Emit `_Static_assert(sizeof/offsetof)` for each `c_struct`
   and native type, and a command that prints the table (Swift's `MemoryLayout`). Not
   done (deferred in stage 21aa). Because wrappers fill structs by field name in C, a
   header's `c_struct` cannot be laid out wrongly by Wiz; the assertions matter for any
   future backend that lowers structs itself.
4. **Keep the model-versus-native differential.** The interpreters keep the model when
   `mk`/`get` are foreign, and the semantics matrix compares the model with the compiled
   natives cell by cell. A native that disagrees with its model is a test failure there.
5. **Do not make `--unbox-structs` the default.** Unboxing a structure's last field is
   not stable under substitution (`unboxedSigma` in `Erase.lean`; [Status](../Status.md),
   R3 open 1), so it stays off. If unboxed structures are wanted, the MLton/GHC way (per
   variable, in a representation pass, boxed at polymorphic boundaries) avoids the
   problem; stage 22d names the same next step for 64-bit words.

### 2.4 Memory: RC, GC, and what to pick when

**Where Wiz is.** The Lean toolchain's runtime uses precise reference counting
(Perceus), no cycle collector, a leak check at exit, and `WIZ_LEAKS`/`WIZ_WATCH` for
debugging. Since stage 25a it is thread-safe in Lean's way: a positive count belongs to
one thread, a negative count marks an object shared between threads and changes
atomically, zero is immortal. The self-hosted runtime uses Boehm by default, or `WIZ_RC`
for Perceus with size-class free lists, a worklist free and an exit check that every
object was freed; it is not yet thread-safe.

**Comparison.**

* **Boehm [boehm88] [H]** is a good default for a compiler's own bootstrap: conservative,
  non-moving, drop-in `GC_MALLOC`, no type information needed. Costs: no compaction,
  possible retention through false pointers, per-platform stack and register support
  (the hard part for a new target), and stop-the-world pauses.
* **Perceus and Counting Immutable Beans [perceus21] [H] [beans19] [H]** are the right
  default for a language runtime: deterministic, no false retention, reuse in place,
  borrow inference. Costs: cycles leak, and an ownership bug is a use-after-free rather
  than a leak.
* **Koka [M]** runs Perceus with an optional tracing GC for cycles, the mature answer to
  RC in a language with mutable references.
* **GHC, Chez, CakeML [M]** show the tracing end: generational copying, precise roots.
  Wiz's uniform tagged representation could support a precise collector (the tag says
  which fields are pointers), an option Boehm does not use.

**Decision matrix (the survey's suggestion).**

| situation | mode | why |
|---|---|---|
| hosted `wiz build` | RC | deterministic destruction (finalizers, resources), no false retention, matches Lean |
| self-hosted bootstrap | RC for the fixpoint, GC as the portability fallback | the fixpoint must be deterministic; GC is what makes a new target work before its RC port is trusted |
| cross or embedded target | RC first if Boehm is not ported | Boehm needs target support for stack and register scanning (§2.6) |
| concurrency | RC with shared atomic counts (as the host runtime now does), or GC | the self-hosted runtime would need `GC_THREADS` or the host's count rules |
| real-time, no pauses | RC, plus arena regions | GC pauses disqualify; RC has bounded work per drop |

**Two gaps.**

1. **Cycles.** Constructor values are acyclic by construction, but mutable cells
   (`lib/Ref.wiz`, `lib/MVar.wiz`) can in principle hold a value that reaches the cell
   itself. Under RC that is a leak; under Boehm it is collected. The documentation does
   not state an acyclicity invariant. Options: state and test the invariant; add a cycle
   detector (trial deletion à la Bacon–Rajan [M]) in debug builds; or accept the leak and
   say so. The leak check at exit will report such a cycle, which is a useful backstop.
2. **Finalizer timing**: see §2.2.

### 2.5 Region and linear types

**Where Wiz is.** QTT quantities `{0, 1, ω}` with `1` meaning exactly once
([CoreSpec](../CoreSpec.md) §5), a linear `IO` world token (`IO A := (1 w : World) → A ×
World`, stage 9a), and `lib/Region.wiz` (stage 22g): a library encoding of Rust-style
borrowing. `Region` and `Outlives` are axioms; handles are structures indexed by an
erased `ρ`; a borrow scope takes a body polymorphic in a fresh `ρ`; inside a mutable
borrow the lender's name is rebound to a `Lent` token with no operations, so using the
lender while borrowed is a type error. Nothing of `ρ` reaches run time.

**Comparison.**

* **Tofte–Talpin [tofte94] [H]** is inference: regions are assigned by static analysis,
  `letregion` scopes them, and a region representation pass turns them into a stack of
  region pages. MLKit [M] is the implementation. It gives allocation control without a
  GC, at the cost of effect inference and a very different backend. Wiz's `Region`
  library gives the typing half (aliasing) and none of the allocation half.
* **Cyclone [cyclone02] [H]** is the practical hybrid: explicit region annotations,
  unique pointers, and a runtime that frees a region wholesale. Users accept explicit
  annotations if the payoff is predictable allocation.
* **Fluet, Morrisett and Ahmed, *Linear Regions Are All You Need* [linearregions06]
  [H]** shows that a region calculus with linear capabilities is essentially a
  monadic, ST-style type system: QTT plus a phantom `ρ` is the same idea. This is the
  paper to cite for "no separate region type system is needed".
* **Launchbury and Peyton Jones, *State in Haskell* [st95] [H]** is the ancestor of the
  `runST` trick `Region.scope` reuses: a rank-2 body prevents a handle escaping. Wiz adds
  `Outlives` evidence for weakening, Rust's subtyping made explicit.
* **Rust NLL [M]** is a borrow checker over a non-dependent type system; Wiz's version is
  a typing discipline over a dependent one, with no inference and no implicit reborrows
  beyond what `Uniq.reborrow` encodes.
* **Linear Haskell [linearhaskell18] [M]** and **Idris 2 [idris2-21] [H]** are the
  multiplicities-in-a-real-language precedents; Wiz is closer to Idris 2.

**Suggestions.**

1. **Do not build region inference.** The cost is high and there is no evidence Wiz needs
   region-based allocation: it has RC, Boehm and `Bytes`.
2. **Keep `lib/Region.wiz` as a test of the type system**, with positive and negative
   tests for each rule (escape, use while borrowed, double mutable borrow). The
   `Regions` test group exists; linear handles in the region and Feral libraries are an
   open item in [Status](../Status.md).
3. **If allocation control is wanted**, add arena primitives (`Region.new`,
   `Region.alloc` with a linear region token, `Region.free`) backed by a bump allocator.
   That is a small fraction of region inference's cost for most of its value (bulk free,
   no GC pressure), and it composes with RC.
4. **Projections and linearity.** The survey flagged that `p.1`/`p.2` could consume a
   linear pair while dropping the other component, which would make `1` affine. This is
   fixed: projections need an unrestricted pair in both kernels ([CoreSpec](../CoreSpec.md)
   §7.1; [Status](../Status.md), Q1/R1).

### 2.6 Cross-compilation

**Where Wiz is.** There is no cross target. `Wiz/Toolchain.lean` carries `cc`, `cflags`,
`ldflags`, `libs`, `llc`, the GC flags, the cache settings and the search path, and
hashes them into the cache key together with a target tag (the host platform triple and
pointer width; its comment says a future `--target` triple replaces them). `--target`
currently selects the backend (`c`, `llvm` or `wasm`). The toolchain builds natively on
aarch64 Linux ([ci-runner.md](../ci-runner.md)). A cross build today means setting `--cc`
to a cross compiler, with no further support.

**Prior art for the shape.**

* **GCC's build/host/target triples** (and the "Canadian cross") are the terminology and
  the warning: a cross compiler that itself runs on a different host is a third
  configuration, and bootstrapping it is a distinct problem.
* **Rust's target tiers** [M] are the best model for policy: tier 1 (built and tested on
  the target), tier 2 (built, tested under emulation or not at all), tier 3 (may build).
* **Zig** [M] makes cross-compilation the default by shipping libc headers per target and
  a `zig cc` driver. Wiz cannot ship libcs, but it can ship a target table naming the
  sysroot and flags, the ergonomic half.
* **LLVM target triples** [M] (`arch-vendor-os-env`) are the right spelling for the flag;
  `llc -mtriple` and `cc --target=` accept them.
* **AAPCS64** [aapcs64] [H] and the **System V AMD64 psABI** [sysvabi] [H] decide struct
  layout, homogeneous float aggregates, `_Bool`, bitfields and varargs. Wiz needs only a
  small subset, which should be written down (the ABI table in §2.2). Stage 9i notes that
  by-value structs are lowered by the C compiler, which follows the platform ABI; the LLVM
  IR never sees a C struct.

**The survey's plan.**

1. **A target as a toolchain field.** A triple that sets `cc`, `--sysroot`, default flags,
   pointer width and endianness, and enters the cache namespace. The namespace half is in
   place (the target tag); the driver half is not.
2. **Generated layout assertions** (§2.3): catches `long` width, `_Bool` size, bitfield
   packing, aggregate returns, `long double` alignment and `char` signedness.
3. **Runtime portability.** `wiz_val` is `uintptr_t`, and `WIZ_MAX_SMALL` is
   `((uintptr_t)1 << 62) - 1`: on a 32-bit target that shift is undefined. A 32-bit target
   needs a guard (`sizeof(uintptr_t) >= 8`) or a different tagging scheme. GMP and Boehm
   must be built for the target; Boehm needs target support for register and stack
   scanning, so `--rc` is the easier first mode on a new target. The self-hosted runtime
   raises its stack limit with `setrlimit` and re-`exec`s itself, which assumes a hosted
   OS.
4. **Host/target differential.** Run every runtime test natively and under `qemu-aarch64
   -L sysroot`, and compare the output byte for byte. This catches endianness, word size,
   struct layout, float formatting and `Nat`-width divergence in one harness [mckeeman98].
5. **C first, LLVM second.** `llc -mtriple` gives a cross build of the program without a
   C cross toolchain, but the runtime and the foreign wrappers are C anyway, so C with a
   cross `cc` is the simpler first target.
6. **Reproducibility first** (§2.10): a cross build must be comparable with a native one,
   or the differential test in item 4 proves little.

### 2.7 Compiler caching and manifests

**Where Wiz is** (stage 11c, [11-tooling.md](../stages/11-tooling.md)). The cache keeps
each command's effect under a chained content hash; a module key hashes the toolchain,
module name, source text, C header texts, `include_str` contents, imports and trust flag.
Payloads are S-expressions decoded into fresh terms. A module's effects can also be
served from an mmapped `.wizr` region (`--region-cache`, experimental), with an 8-byte
`.wizs` checksum sidecar checked before mapping; the text entries remain the authority.
Directories can be layered (`--cache-ro`, read-only), and `wiz cache prune` removes old
entries from the write cache. Keys have a fast 64-bit half and a domain-separated SHA-256
half; per-module output manifests list each entry's SHA-256, are rooted in a Merkle tree,
and are checked before an effect is applied (`--cache-verify off|warn|strict`, strict for
read-only layers); `wiz cache verify` scans them.

**Prior art.**

* **ccache's manifest** [ccache] [H] is the closest analogue: direct mode hashes the
  source and the include list, stores a manifest keyed by that, and only then looks up the
  object. Wiz's module key does the same for Wiz sources and C headers (header text is in
  the key, a genuine strength).
* **GHC's recompilation avoidance** [M] and **Lean's `.olean`** [olean] [M] are the two
  ends of artifact format: GHC re-reads an interface, Lean mmaps a compacted image. Wiz
  has both (text `.wizc`, region `.wizr`), with text as the authority. The risk is that
  two formats drift.
* **Build Systems à la Carte** [buildsys18] [M] names the properties that matter: early
  cutoff (a change that does not change the output does not invalidate downstream) and
  constructive traces. Wiz's per-command key gives fine-grained invalidation but no
  notion of "same output"; the 11c "Next" item (re-elaborate only what an edit affects)
  is this.
* **Nix** [nix06] [M] and the **Bazel remote-execution API** [M] give the distribution
  shape: content-addressed action results and an explicit trust decision about a shared
  cache. A shared cache is an attack surface: whoever writes it writes your terms.
* **Trustix, SLSA, in-toto** [trustix] [slsa] [intoto19] [M]: for a shared cache, a
  signed manifest over artifact hashes, verified on load, with the cache treated as
  untrusted.

**Status of the survey's suggestions.**

1. **Keep the two-level design** (text authority, region fast path). It is the design:
   a corrupt region is a miss.
2. **Make the manifest first-class.** Done: per-module manifests, a per-layer generation
   index, `wiz cache verify` and `wiz cache manifest`.
3. **Namespace by target.** Done for the host target (the target tag is in the manifest
   and the toolchain digest).
4. **Bound the cache.** Pruning by age exists; a size cap does not.
5. **Never let the cache be a correctness oracle.** Integrity is now checked; the manifests
   are explicitly not signatures. A writer who controls the manifest can rewrite it with
   the bytes; the missing half is an external signature with a key policy (11c, "Not
   signatures").
6. **Region portability.** A region image depends on pointer width, endianness and the
   Lean version. A region's name includes the binary (`binaryId`), a file of the wrong
   format is a miss, and its manifest records the target tag.

### 2.8 Test strategy

**Where Wiz is.** The kernel differential test (the hand-picked samples and 400 random
terms checked by both kernels, same verdict required), the `False` fuzzer (closed terms
claiming to inhabit `Empty`, verdict and normal form compared across kernels), the WizMeta
reference checker, self-hosted differential groups (parser, CLI, macros), the semantics
matrix (model, IR interpreter, Lean→C and self-hosted→C on boundary values), the nightly
fixpoint, the trust ledger check, and a reproducibility check in CI.

**Prior art on what oracle to build.**

* **Csmith [csmith11] [H]**: generate only well-defined, well-typed programs, run them
  under several compilers, compare outputs, then reduce the difference. Lessons: a typed
  generator finds far more than random bytes, and reduction is mandatory, or every finding
  is a 500-line mystery.
* **YARPGen [yarpgen20] [M]** adds "avoid undefined behaviour by construction". For Wiz
  the analogue is generating only terms that normalise within a fuel bound, and
  separately terms expected to be rejected.
* **The OOPSLA'19 compiler-fuzzing study [compfuzz19] [H]** found that fuzzer-found bugs
  do matter in practice, and that differential oracles find bugs crash oracles miss.
  Wiz's kernels, backends and memory modes give several differential oracles.
* **Alive2 [alive2-21] [H]** validates an optimiser: bounded translation validation
  between IR versions with SMT. Wiz's optimiser (reuse, borrow inference, inlining) is
  small enough that interpret-versus-compile per function, with the built-in IR
  interpreter (`#run`) as reference semantics, is a cheap first step.
* **Translation validation** [pnueli98] [M] is the general frame: validate each run
  rather than verify the compiler. Wiz has three natural seams: erasure, lowering, RC
  insertion.
* **QuickCheck [quickcheck00] [M]** and shrinking: the property-test half.
* **Mutation testing** [mutation11] [M]: inject a bug into the kernel (swap a premise,
  drop a usage check) and check that the suite fails. Cheap, and it measures the suite
  rather than the code.

**Suggested tiers.**

| tier | oracle | cost | what it catches |
|---|---|---|---|
| T0 | unit and property tests per kernel rule | low | rule regressions |
| T1 | pipeline differential: Lean→C, Lean→LLVM, self-hosted→C (GC and RC), IR interpreter; compare outputs | medium (one harness; the semantics matrix is a start) | lowering, erasure, RC/GC, codegen, FFI |
| T2 | kernel differential on typed terms, with normal-form comparison | medium (the `False` fuzzer does this for one oracle) | shared misconceptions, conversion bugs |
| T3 | frontend differential: accept/reject, error code and message | low | parser and elaborator drift |
| T4 | fixpoint, DDC record, reproducible build | low | bootstrap integrity, non-determinism |
| T5 | cross differential under `qemu-user` | medium | ABI, word size, layout, endianness |
| T6 | sanitizers (ASan, UBSan, TSan) on generated C, `GC_DEBUG`, leak check at exit | low (TSan was used for stage 25a) | undefined behaviour, ownership bugs, GC rooting |
| T7 | mutation testing of the kernel and suite | low | weak tests |
| T8 | optimiser validation | high | miscompilation by optimisation passes |

Two policy notes: a skipped case is not a pass; and pin exact messages in a differential
corpus, because message drift is how a differential test silently becomes a tautology.

### 2.9 Language-surface items that gate the above

Prior art and the engineering consequence only:

| item | prior art | consequence |
|---|---|---|
| named arguments | Lean 4 named arguments; Agda and Idris `{x = e}` [M] | done in both frontends (self-hosted: 21ab) |
| universe polymorphism | Lean level parameters, `imax`, level metavariables; Agda `Set ℓ`; Coq `Polymorphic` [M] | the remaining self-hosted gap; universe-polymorphic classes need it |
| classes | Wadler–Blott [M]; Coq type classes (Sozeau–Oury) [M]; Lean `class`/`instance` [M] | done in the self-hosted frontend without `outParam` or priorities (30a) |
| proof surface | Pujet–Tabareau [pt22] [pt23] | keep `castRefl` propositional (an axiom, never a conversion rule; [CoreSpec](../CoreSpec.md) §8.4a); it is the safety valve for the design without definitional regularity |
| macros and tactics | Lean 4 `MetaM` in Lean [lean4-21]; Idris `%runElab`; Agda reflection | first milestones done in the self-hosted frontend (21ac, 21ad) |
| `native_refl` | Lean `native_decide`; Coq `native_compute`, `vm_cast_no_check` [M] | an axiom per use, behind `--trust-native`, in the trust ledger (stage 27a); never a conversion rule |
| `smt`, `sat_decide` | SMTCoq; Lean `bv_decide` [M] | `sat_decide` checks an LRAT certificate in the kernel; `smt` is an axiom per use behind `--trust-smt` (stage 28) |

### 2.10 Reproducible builds and the compiler as an artifact

Reproducibility is not a separate feature: DDC (§2.1) is meaningful only if the builds are
comparable, the fixpoint only if the C is deterministic, and a shared cache only if the
hashes are stable. Wiz has a reproducibility check, `scripts/check-repro.sh`, which runs in
CI: it builds a small corpus under two absolute paths with different environment,
locale, `SOURCE_DATE_EPOCH`, thread count and cache directories and compares generated C,
executables (C, `--split`, LLVM, `-g`), a grail build and the cache entries; with
`--compiler` it also compares two builds of the compiler. The C build passes
`-ffile-prefix-map` (`Wiz/Compiler/Build.lean`). The region image is not byte-canonical,
so claims are made at the manifest level, not the region level.

Sources of nondeterminism, in the order they usually bite: (1) iteration order over hash
maps in code generation; (2) counters (generated names assigned by traversal rather than
allocation order in a parallel build); (3) paths (`-ffile-prefix-map`, path-relative
diagnostics); (4) environment (`SOURCE_DATE_EPOCH`, `LC_ALL=C`, `TZ=UTC`,
locale-independent float printing); (5) the C toolchain, whose identity belongs in the
key and in the manifest. Remaining suggestions: run the comparison on the self-hosted
compiler's own outputs, and record the hashes so that "the fixpoint passed" becomes "the
two builds differ only in what is known". Prior art: `reproducible-builds.org` and
`SOURCE_DATE_EPOCH` [reprobuilds] [H]; `diffoscope` and `reprotest` for reports;
in-toto and SLSA for what to do with the hashes [intoto19] [slsa] [M].

---

## 3. Novelty assessment

Ranked by how much of the claim survives contact with the prior art. "Delta" is what is
new, stated as narrowly as possible.

| # | Wiz feature | closest prior art | delta | confidence |
|---|---|---|---|---|
| 1 | A dependent core with QTT, OTT, impredicative `Prop`, descriptions and sizes, without definitional regularity, with `cast` computing on data ([CoreSpec](../CoreSpec.md) §8.4) | Pujet–Tabareau [pt22] [pt23], Abel–Coquand [ac20] (the loop that forced regularity off), levitation [cdmm10], sized NbE [avw17] | the combination, specifically the μ/ν/Desc `cast` rules, the inert-type identity and a propositional `castRefl`. The survey knows of no published system with this rule; [Status](../Status.md) records regularity at inert types as a conjecture | medium-high that it is new; medium-low that it is sound as stated (no normalisation proof) |
| 2 | Independent checkers (Lean kernel, `Kernel.wiz`, the WizMeta reference checker) compared on random and hand-picked terms | lean4checker, Lean4Lean, Nanoda; `coqchk`; CompCert's validators | automated differential checking between implementations of the same calculus, including a self-hosted one. A variant, not a first | medium |
| 3 | Checked inline C (`glue`), a typed subset rejecting pointers, casts, indexing, `goto`, `asm`, `sizeof` | Checked C, Cyclone; inline-c and `hsc2hs` (unchecked); Swift's importer (unchecked mapping); CakeML's byte-array oracle | a C statement subset type-checked against imported prototypes and emitted inline from a dependently typed language. The most defensible novelty claim in the engineering half | medium-high |
| 4 | Type-level native representation, width-independent `UIntN w` | Lean `@[implemented_by]` and built-in `UInt64`; GHC/MLton representation passes; Swift `@frozen` | user-definable unboxed representation with a kernel-side model, one rule for all widths, sealing for coherence | medium-high |
| 5 | Byte-identical bootstrap fixpoint in two memory modes | Appel; GHC and Rust stage discipline; CakeML; Chez boot files | byte equality of C across stages and modes; the idea is old, the discipline is good | low novelty, high assurance value |
| 6 | Per-command content-addressed cache, mmapped regions with checksums, layered read-only caches, SHA-256 output manifests | ccache, Lean `.olean`, GHC `.hi`, Nix, Bazel | the text/region split with text as authority, per-command granularity. Engineering, not research | low |
| 7 | Rust-style borrowing as erased type indices plus `Outlives` evidence in a dependent language | Launchbury–Peyton Jones `ST`, Fluet–Morrisett–Ahmed, Cyclone, Rust NLL, Idris 2 | a library (no new typing rules, no inference); its value is as a stress test of QTT | low as a system; medium as evidence that QTT suffices |
| 8 | A self-hosted elaborator (metavariables, unification, match compilation, classes, macros) | Idris 2 (self-hosted elaborator), Lean 4 | Idris 2's territory; the delta is a small, readable elaborator over an OTT/description kernel | low-medium |
| 9 | A readable, staged specification of the kernel as inference rules, with a "where the code and the stage docs disagree" section ([CoreSpec](../CoreSpec.md) §14) | the tutorial-implementation genre: elaboration-zoo [elabzoo], pi-forall [piforall], Löh–McBride–Swierstra [loh10], *Essentials of Compilation* [siek] | an end-to-end readable pipeline (parser → kernel → erasure → C/LLVM → runtime → FFI → bootstrap) with an explicitly tagged spec. No single work does that; the genre is crowded | medium as pedagogy, low as research |
| 10 | Everything else (modules, classes, universes, tactics, macros, FFI marshalling, caching) | abundant | none claimed | — |

**Verdict.** Wiz is not a research contribution in compiler construction; it is an
unusually complete didactic artifact whose genuinely new pieces sit at the
type-theory/engineering seam: the `cast` design without definitional regularity (new,
unproved) and the checked C glue (new, modest). Its self-hosting story is Idris 2's shape
with a Lean/CakeML-style trust discipline. Since the survey was drafted, the kernel's
trusted base has been published (CoreSpec §16, the trust ledger), a third checker added,
and a reproducibility check put in CI. What would make the remaining claims easiest to
defend is publishing the bootstrap's own axioms and fixpoint hashes, a pipeline
differential harness, and the ABI table as a reference page.

---

## 4. Risk register

Likelihood (L) and impact (I) are 1–5; the score is L×I. Scores are the survey's
judgement, adjusted where the code has changed. "Mitigation" names the source that says
what to do, not a guarantee.

| # | risk | evidence | L | I | score | mitigation |
|---|---|---|---|---|---|---|
| R1 | A bug shared by both kernels is invisible to the differential test | both kernels come from one design; the differential test "cannot find a bug both kernels share" ([Status](../Status.md), "Two kernels") | 3 | 5 | 15 | the WizMeta checker (a third, declarative voter) and the `False` fuzzer's normal-form comparison exist; widen the generator to every former [lean4lean25] |
| R2 | The `cast` design without regularity is unsound or non-normalising | regularity at inert types is a conjecture; no normalisation proof; [ac20] shows the failure mode | 2 | 5 | 10 | keep `castRefl` propositional; fuzz for loops with fuel; formalise the argument; keep a fallback design |
| R3 | A native (`implemented_by`, `repr:`, `native_refl`) disagrees with its model | the kernel keeps the model, so proofs are safe, but run-time behaviour can be wrong | 3 | 4 | 12 | trust ledger rows; the semantics matrix compares model and natives; `#print axioms` lists natives |
| R4 | `Nat` at the FFI boundary behaves differently in the two toolchains | the Lean runtime stops above 64 bits; the self-hosted runtime stops from 2^63 (stage 21p) | 3 | 2 | 6 | boxed `Nat` by default (deferred); test 2^62, 2^63, 2^64 at the boundary in both |
| R5 | Finalizer timing differs between RC and GC | `foreign_type` finalizers run at the last `dec` against at collection | 4 | 3 | 12 | explicit release (`File.close`); finalizers as a backstop; compare output and live counts, not finalizer order |
| R6 | A finalizer runs at an arbitrary point in GC mode | Boehm runs finalizers after a collection, inside unrelated code [M]; a finalizer that allocates or takes a lock can misbehave | 2 | 4 | 8 | document "no allocation, no blocking" for finalizers; GHC `mkWeak` and Java lessons [M] |
| R7 | By-value struct ABI breaks on a new platform | no layout assertions (deferred in 21aa); the C compiler lowers structs by the platform ABI, which limits the risk to new backends | 2 | 3 | 6 | generated `_Static_assert`s; forbid bitfields and `long double`; cross differential under qemu |
| R8 | GC mode is unbuildable for a cross target | Boehm needs target support; `selfhost/rt.c` assumes `alloca`, `setrlimit` and re-`exec` | 3 | 4 | 12 | `--rc` as the cross default; a Boehm port as separate work; a tier table |
| R9 | A 32-bit target breaks the tagging scheme | `WIZ_MAX_SMALL` shifts `uintptr_t` by 62 | 3 | 3 | 9 | a static assertion in the runtime; no 32-bit target before a fix |
| R10 | Cache poisoning through a shared layer | output manifests (SHA-256, Merkle root) now detect corruption and swapped entries, and read-only layers are strict; manifests are unsigned | 2 | 4 | 8 | external signatures with a key policy [trustix] [slsa] |
| R11 | Cache mixing after a cross build | the target tag is the host's triple and pointer width; a cross target must replace it | 1 | 4 | 4 | put the cross triple in the target tag when `--target` gains one |
| R12 | Remaining self-hosting gaps block the Wiz-hosted compiler from replacing Lean | universe polymorphism and parts of class resolution are still missing (30a, "What remains") | 4 | 3 | 12 | the dependency order in §2.1 |
| R13 | `builtin` registrations are trusted | restricted to the toolchain's `lib/`, once per key; any other registration is an axiom ([Status](../Status.md), F4) | 1 | 5 | 5 | keep the registration list small and in the trust ledger |
| R14 | Evaluation or checking loops | no termination proof for the core | 3 | 3 | 9 | fuel and timeouts in CI and in the language server; fuzz with a wall clock |
| R15 | The fixpoint does not run on pull requests and covers one input set | nightly schedule; self-hosted sources only | 4 | 3 | 12 | extend to `lib/` and `examples/`; make flags part of the matrix; record hashes |
| R16 | Stage 0 (the Lean toolchain) is unverified | it is the root of trust for the bootstrap | 2 | 5 | 10 | record toolchain hashes; reproducible builds; the DDC framing of §2.1 |
| R17 | The two cache formats drift | `.wizc` is authoritative, `.wizr` is fast; two writers | 3 | 3 | 9 | a differential test per format change; `regionFormat` bumps |
| R18 | The self-hosted runtime is not thread-safe | stage 25a: `selfhost/rt.c` is not yet covered | 3 | 3 | 9 | the host runtime's shared-count rule; `GC_THREADS` for the Boehm mode |
| R19 | Documentation claims outrun the evidence | [CoreSpec](../CoreSpec.md) §14 item 4 still describes projections consuming a linear pair, which Status Q1/R1 records as fixed; §15 says the self-hosted FFI has no `import_c` or `glue`, which stage 21aa added | 4 | 3 | 12 | a status vocabulary; an explicit "unverified" tag; confidence markers as a house style |

Risks from the original register that no longer apply: `partial` definitions guarded only
by a head-of-type check (fixed: each partial definition carries a kernel-checked witness,
[Status](../Status.md) F3); unchecked `builtin` registrations anywhere (fixed, F4, now R13
above); native representations on unsealed types (fixed, F14); and the projection rule
that made `1` affine (fixed, Q1/R1).

---

## 5. Bibliography

Provenance: **[V]** identifier checked when the survey was written; **[S]** seen in a
search result only; **[M]** from memory or project documentation, DOI not re-checked. Do
not copy a DOI from an [M] entry without checking it.

### Bootstrapping, self-hosting, trust

1. **[appel94] [V]** A. W. Appel. *Axiomatic bootstrapping: a guide for compiler hackers.*
   ACM TOPLAS 16(6):1699–1718, 1994. doi:10.1145/197320.197336.
2. **[thompson84] [M]** K. Thompson. *Reflections on Trusting Trust.* CACM 27(8):761–763,
   1984.
3. **[wheeler05] [V]** D. A. Wheeler. *Countering Trusting Trust through Diverse
   Double-Compiling.* ACSAC 2005, pp. 33–48. doi:10.1109/CSAC.2005.17. Full dissertation:
   `dwheeler.com/trusting-trust/`.
4. **[strub12] [S]** P.-Y. Strub, N. Swamy, C. Fournet, J. Chen. *Self-certification:
   bootstrapping certified typecheckers in F\* with Coq.* POPL 2012.
   doi:10.1145/2103621.2103723.
5. **[cakeml14] [V]** R. Kumar, M. O. Myreen, M. Norrish, S. Owens. *CakeML: A Verified
   Implementation of ML.* POPL 2014. doi:10.1145/2535838.2535841. Retrospective:
   *The CakeML Project's Quest for Ever Stronger Correctness Theorems*, ITP 2021
   (`drops.dagstuhl.de/opus/volltexte/2021/13896`).
6. **[compcert09] [M]** X. Leroy. *Formal Verification of a Realistic Compiler.* CACM
   52(7):107–115, 2009; see also `compcert.org` and the CompCert user manual.
7. **[coqcoq20] [V]** M. Sozeau, S. Boulier, Y. Forster, N. Tabareau, T. Winterhalter.
   *Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq.*
   PACMPL 4(POPL), 2020. doi:10.1145/3371076.
8. **[lean4lean25] [V]** M. Carneiro. *Lean4Lean: Verifying a Typechecker for Lean, in
   Lean.* TYPES 2025. doi:10.4230/LIPIcs.TYPES.2025.2; arXiv:2403.14064.
9. **[nanoda] [M]** *Nanoda*: an independent Lean 4 kernel in Rust
   (`github.com/ammkrn/nanoda_lib`).
10. **[lean4-21] [V]** L. de Moura, S. Ullrich. *The Lean 4 Theorem Prover and Programming
    Language.* CADE-28, LNCS 12699, 2021. doi:10.1007/978-3-030-79876-5_37.
11. **[idris2-21] [V]** E. Brady. *Idris 2: Quantitative Type Theory in Practice.* ECOOP
    2021. doi:10.4230/LIPIcs.ECOOP.2021.9; arXiv:2104.00480.
12. **[chez06] [V]** R. K. Dybvig. *The Development of Chez Scheme.* ICFP 2006, pp. 1–12.
    doi:10.1145/1159803.1159805. Boot files and the nanopass framework: `scheme.com`,
    `cisco.github.io/ChezScheme`.
13. **[mlton] [M]** MLton documentation, `mlton.org` (whole-program compilation,
    representation analysis, `_import`/`_export`).
14. **[gcc-bootstrap] [M]** GCC. *Installing GCC*: the three-stage bootstrap and
    build/host/target configurations (`gcc.gnu.org/install/build.html`).

### Runtime, GC, code generation

15. **[perceus21] [V]** A. Reinking, N. Xie, L. de Moura, D. Leijen. *Perceus: Garbage Free
    Reference Counting with Reuse.* PLDI 2021. doi:10.1145/3453483.3454032.
16. **[beans19] [V]** S. Ullrich, L. de Moura. *Counting Immutable Beans: Reference Counting
    Optimized for Purely Functional Programming.* IFL 2019.
    doi:10.1145/3412932.3412935; arXiv:1908.05647.
17. **[boehm88] [V]** H.-J. Boehm, M. Weiser. *Garbage Collection in an Uncooperative
    Environment.* Software: Practice and Experience 18(9):807–820, 1988.
    doi:10.1002/spe.4380180902. Implementation: `github.com/ivmai/bdwgc`; also Boehm,
    *Space Efficient Conservative Garbage Collection*, PLDI 1993 [M].
18. **[llvm04] [M]** C. Lattner, V. Adve. *LLVM: A Compilation Framework for Lifelong
    Program Analysis & Transformation.* CGO 2004. doi:10.1109/CGO.2004.1281665 (not
    re-checked).
19. **[cmm] [M]** GHC's Cmm: *The Architecture of Open Source Applications*, vol. 2,
    chapter "The Glasgow Haskell Compiler" (Marlow, Peyton Jones); the GHC Commentary.
20. **[koka14] [M]** D. Leijen. *Koka: Programming with Row Polymorphic Effect Types.* MSFP
    2014; the Koka documentation on Perceus.
21. **[olean] [M]** Lean 4 sources: `.olean` loading as a compacted region
    (`src/runtime/compact.cpp`, `src/Lean/Environment.lean`).

### Regions, linearity, ownership

22. **[tofte94] [V]** M. Tofte, J.-P. Talpin. *Implementation of the Typed Call-by-Value
    λ-Calculus using a Stack of Regions.* POPL 1994. doi:10.1145/174675.177855.
23. **[cyclone02] [V]** D. Grossman, G. Morrisett, T. Jim, M. Hicks, Y. Wang, J. Cheney.
    *Region-Based Memory Management in Cyclone.* PLDI 2002. doi:10.1145/512529.512563.
24. **[linearregions06] [V]** M. Fluet, G. Morrisett, A. Ahmed. *Linear Regions Are All You
    Need.* ESOP 2006, LNCS 3924, pp. 7–21. doi:10.1007/11693024_2.
25. **[st95] [V]** J. Launchbury, S. L. Peyton Jones. *State in Haskell.* Lisp and Symbolic
    Computation 8(4):293–341, 1995. doi:10.1007/BF01018827.
26. **[linearhaskell18] [M]** J.-P. Bernardy, M. Boespflug, R. Newton, S. Peyton Jones, A.
    Spiwack. *Linear Haskell: practical linearity in a higher-order polymorphic language.*
    POPL 2018.
27. **[qtt18] [H]** R. Atkey. *Syntax and Semantics of Quantitative Type Theory.* LICS 2018,
    pp. 56–65. doi:10.1145/3209108.3209189. (Also cited in [CoreSpec](../CoreSpec.md)
    §17.)
28. **[checkedc18] [M]** A. S. Elliott et al. *Checked C: Making C Safe by Extension.*
    IEEE SecDev 2018.

### Type theory used by the core (as cited in CoreSpec)

29. **[pt22] [H]** L. Pujet, N. Tabareau. *Observational Equality: Now for Good.*
    PACMPL 6(POPL), 2022. doi:10.1145/3498693.
30. **[pt23] [H]** L. Pujet, N. Tabareau. *Impredicative Observational Equality.*
    PACMPL 7(POPL), 2023, pp. 2171–2196.
31. **[ac20] [H]** A. Abel, T. Coquand. *Failure of Normalization in Impredicative Type
    Theory with Proof-Irrelevant Propositional Equality.* LMCS 16(2), 2020;
    arXiv:1911.08174.
32. **[cdmm10] [H]** J. Chapman, P.-É. Dagand, C. McBride, P. Morris. *The Gentle Art of
    Levitation.* ICFP 2010, pp. 3–14. doi:10.1145/1863543.1863547.
33. **[avw17] [H]** A. Abel, A. Vezzosi, T. Winterhalter. *Normalization by Evaluation for
    Sized Dependent Types.* PACMPL 1(ICFP), 2017. doi:10.1145/3110277.

### FFI and ABI

34. **[ghcffi] [M]** The Haskell 2010 Foreign Function Interface (Chakravarty, Keller,
    Peyton Jones, Marlow), the FFI addendum on `haskell.org`; GHC User's Guide, "Foreign
    function interface" (`foreign import ccall safe/unsafe`, `StablePtr`, `ForeignPtr`,
    `CApiFFI`), `downloads.haskell.org/~ghc/latest/docs/users_guide`.
35. **[rustffi] [M]** *The Rustonomicon*, "FFI" (`doc.rust-lang.org/nomicon/ffi.html`);
    the `std::ffi` documentation; the `bindgen` and `cxx` projects.
36. **[swiftffi] [M]** Swift documentation on imported C functions and the Clang importer;
    `@convention(c)`, `Unmanaged`, and the Swift 5 ABI-stability posts (`swift.org/blog`).
37. **[aapcs64] [H]** Arm. *Procedure Call Standard for the Arm 64-bit Architecture
    (AAPCS64)*, IHI 0055; `github.com/ARM-software/abi-aa`.
38. **[sysvabi] [H]** *System V Application Binary Interface: AMD64 Architecture
    Processor Supplement*; `gitlab.com/x86-psABIs/x86-64-ABI`.
39. **[itaniumabi] [M]** *Itanium C++ ABI* (`itanium-cxx-abi.github.io/cxx-abi/`), the
    reference for struct-passing rules that C ABIs inherit in practice.

### Caching, build systems, supply chain

40. **[ccache] [M]** The ccache manual, "Direct mode" and manifest files (`ccache.dev`).
41. **[buildsys18] [M]** A. Mokhov, N. Mitchell, S. Peyton Jones. *Build Systems à la
    Carte.* ICFP 2018.
42. **[nix06] [M]** E. Dolstra. *The Purely Functional Software Deployment Model.* PhD
    thesis, Utrecht, 2006; E. Dolstra, M. de Jonge, E. Visser, *Nix: A Safe and
    Policy-Free System for Software Deployment*, LISA 2004.
43. **[trustix] [M]** Trustix (`github.com/nix-community/trustix`): Merkle build
    transparency; the project's status has changed over time.
44. **[intoto19] [M]** S. Torres-Arias et al. *in-toto: Providing farm-to-table guarantees
    for bits and bytes.* USENIX Security 2019.
45. **[slsa] [M]** OpenSSF *SLSA* specification (`slsa.dev`): supply-chain levels for build
    provenance.
46. **[reprobuilds] [H]** `reproducible-builds.org`, including the `SOURCE_DATE_EPOCH`
    specification.

### Testing, fuzzing, validation

47. **[csmith11] [H]** X. Yang, Y. Chen, E. Eide, J. Regehr. *Finding and Understanding Bugs
    in C Compilers.* PLDI 2011. doi:10.1145/1993498.1993532.
48. **[compfuzz19] [V]** M. Marcozzi, Q. Tang, A. F. Donaldson, C. Cadar. *Compiler
    Fuzzing: How Much Does It Matter?* PACMPL 3(OOPSLA), 2019. doi:10.1145/3360581.
49. **[alive2-21] [V]** N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr. *Alive2: Bounded
    Translation Validation for LLVM.* PLDI 2021. doi:10.1145/3453483.3454030.
50. **[yarpgen20] [M]** V. Livinskii, D. Babokin, J. Regehr. *Random Testing for C and C++
    Compilers with YARPGen.* PACMPL 4(OOPSLA), 2020.
51. **[creduce12] [M]** J. Regehr, Y. Chen, P. Cuoq, E. Eide, C. Ellison, X. Yang. *Test-Case
    Reduction for C Compiler Bugs.* PLDI 2012.
52. **[pnueli98] [M]** A. Pnueli, M. Siegel, E. Singerman. *Translation Validation.* TACAS
    1998.
53. **[quickcheck00] [M]** K. Claessen, J. Hughes. *QuickCheck: A Lightweight Tool for
    Random Testing of Haskell Programs.* ICFP 2000.
54. **[mutation11] [M]** Y. Jia, M. Harman. *An Analysis and Survey of the Development of
    Mutation Testing.* IEEE TSE 37(5), 2011.
55. **[mckeeman98] [M]** W. M. McKeeman. *Differential Testing for Software.* Digital
    Technical Journal 10(1), 1998.

### Didactic prior art

56. **[elabzoo] [M]** A. Kovács. *elaboration-zoo*
    (`github.com/AndrasKovacs/elaboration-zoo`): minimal dependent elaboration
    implementations.
57. **[piforall] [M]** S. Weirich. *pi-forall*: a small dependently typed language with a
    tutorial implementation.
58. **[loh10] [M]** A. Löh, C. McBride, W. Swierstra. *A Tutorial Implementation of a
    Dependently Typed Lambda Calculus.* Fundamenta Informaticae 102(2), 2010.
59. **[siek] [M]** J. Siek. *Essentials of Compilation: An Incremental Approach in Racket.*
    MIT Press, 2023.
