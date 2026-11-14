# Changelog

All notable changes to Wiz. Versions follow [Semantic Versioning](https://semver.org/)
in its 0.x form: until 1.0, a minor release (0.1 → 0.2) may break anything; a patch
release (0.1.0 → 0.1.1) fixes bugs only. What a patch release keeps is in
[docs/stability.md](docs/stability.md).

Section numbers (`4c`, `22e`, …) refer to the stage docs: section `NNx` is in
`docs/stages/NN-*.md`. `#n` is a pull request on GitHub.

## [Unreleased]

* tower: the Lean reference implementation (`Tower/`, `tests --tower`) is gone; `tower/`
  is the only implementation, and the `tower` test group tests it (26h).
* tower: a `wiz-toolchain.local` next to `wiz-toolchain` (uncommitted; add it to
  `.gitignore`) overrides it with a spec or a path to a toolchain directory or built
  checkout; the shims, `which` and `show` honour it (26a, #281).

## [0.1.0] - unreleased (draft)

The first tagged release. Everything below is new in it; it collects stages 1–26 and the
pull requests merged up to the tag. The repository is https://github.com/wiz-pl/wiz
(moved from `badly-drawn-wizards/wiz`; GitHub redirects the old URLs).

### Stability

* 0.1 is mostly a fixed toolchain to pin (`wiz-toolchain`: `v0.1.0`). Only these are
  promised for 0.1.z ([docs/stability.md](docs/stability.md)): the `wiz-toolchain` file
  and tower's specs, the release tags and their download URLs, grail's core `Package`
  API (`new`, `lib`, `exe`, `tests`, `check`, `dep`), and the `wiz` command line
  without its experimental flags. Everything else, including the language, the
  standard library, the LSP and infoview protocol and the C FFI, may change in 0.2
  without deprecation aliases. Breaking changes will be listed here.
* **Soundness.** Nothing about Wiz as a whole is proved. [docs/Status.md](docs/Status.md)
  lists what is known: the trusted base, the conjectures (regularity at inert types,
  equality of descriptions) and the open issues. Please report a proof of `False`
  (Status.md, "How to report a soundness bug").

### The core theory and the kernel

* A kernel for quantitative type theory, parametric in the rig (quantities `0`, `1`,
  `ω`), with universe polymorphism, Σ, `Unit`, `Empty` (stages 1, 4a–b), quantity
  polymorphism (4d).
* Observational equality with an impredicative, proof-irrelevant `Prop`: function
  extensionality, `cast` that computes on data (4c); equality of descriptions,
  `μ ≡ μ` compares the codes (4g, #40).
* Data as indexed descriptions with `μ`/`ν`, `inductive` and `structure`, dependent
  pattern matching and structural recursion (4d–e), sized types (4f), codata and
  copatterns.
* Regularity off by default (decision D1 (a), #4, #15); regularity at inert types
  decided by ground equality (#46); `castRefl` as a propositional axiom (#23).
* Proofs are never evaluated by the kernels (P2, #61); `Size`/`Qty` handling, `ULift`
  for small description fields (Q4, #26).
* The trusted base made explicit (22f): partial definitions need a witness the kernel
  checks (#5), `builtin` registrations outside the toolchain's library are axioms (#5),
  a builtin key is registered once (#67), compiled equations are derived from the
  checked value and their agreement is checked by the kernel (T1, #82, #126),
  `#print axioms` lists native implementations (#66).
* Soundness fixes, each with regression tests (docs/Status.md §3–4): propositions
  compared by shape (F1), `∞ < ∞` (F2), partial definitions at an empty index (F3, #5),
  unchecked registrations (F4, #5), quantity variables in type equality (F6, #43), a
  variable captured by a native operation (F7, #59), `absurd` on glued values (F8,
  #59), the eliminators' index levels (F9, #83), K3/Q1/Q2/Q3 (#14), projections only on
  unrestricted pairs (R1, #84), two declarations of one name (#104), a variable out of
  scope (#72), the self-hosted kernel's fast path at universe levels (W1, #76),
  `Size ≡ Size` in the self-hosted kernel (O1).
* Kernel lint: every traversal handles every constructor; a panic is not a value (#78).
* WizMeta: a specification of the core theory and a reference checker (#122);
  equations at propositions are `True`, and the Σ rule along a proof component uses
  `reflTy` (NU-TRANSP, #123; the elaborator's `refl a` follows, #130).

### The language and the elaborator

* An extensible parser (stage 2), an elaborator with implicit arguments and unification
  (stage 3), macros by example, procedural macros and tactics written in Wiz (stage 6,
  #88: `trace`, hygienic names, `unfold`/`whnf`/`change`/`rw`, reflection of
  constructors), type classes with tabled resolution and `deriving` (stage 7, #39),
  numeric classes `Add`/`Sub`/`Mul`/`Div`/`Mod`/`Neg`/`OfNat` and `Int` (7e, #85).
* Effects as a library, fusion, one-shot effects (stage 10).
* Named arguments (13a, #33); private declarations, constructors, fields and types,
  per module (13b, #33, #48, #109, #132); `if`/`&&`/`||`/`!`, `Functor`/`Applicative`,
  `∃` binders and ASCII logic, `let` tuple patterns (13c–f, #107); as-patterns,
  structure patterns and `⟨…⟩`, structure update (13g–i, #106); keyword scopes (13j,
  #89); list literals, `++` as `Append`, local notation (13k–m, #115); `rfl` at an
  equation that has computed (13n, #111).
* Phantom fields for unused type parameters (22e, #10); sealed types (22k, #119);
  regions: borrow checking as typing (22g, #19); Feral, a Rust-like surface language as
  a command macro (22j, #125).
* Many elaborator fixes: postponed lambdas, trailing instances, projection functions,
  constructor parameters from the expected type (#25), numeral-sub blowup and computed
  equations (#13), scope escape (#31), unification approximation and do-notation (#92),
  fast-failing unification (#110), `Level.normalize` (#35), linear nested spines (#62),
  a term whose type is the expected definition is unified rather than η-expanded (#116),
  pruning a hole's out-of-scope variables (#158).
* Two modules declaring one name: one error, at the import (#104, #112); private names
  and types are per module (#109, #132).
* Module roots: the toolchain's library first, then `-I` (`./lib` only as a fallback,
  #117).

### Running and compiling programs

* Erasure and an interpreter (`#eval`, stage 5); representations decided by what
  conversion sees (R3, #70).
* An IR with Perceus reference counting and reuse, C and LLVM backends (stage 8),
  borrowed parameters and drop specialisation (8e, #34); optimiser quick wins (#32);
  unboxed structure fields and `attribute [inline]` (22i, #37).
* Numbers for hardware and systems code (stage 22): division, powers and bits,
  `implemented_by`, machine integers, unboxed words (#11), one bit-vector family (#24),
  big numerals (#80).
* The C FFI (stage 9): foreign functions and header import, checked glue, foreign
  pointers and finalizers, `link_c`/`link_lib` (9f, #57), callbacks and exported
  functions (9g, #56), processes, environment and files in `lib/Sys.wiz` (9h, #64), C
  structs by value (9i, #63), bytes on handles, time limits and serial ports (9k, #101).
* Concurrency (stage 25): a thread-safe runtime (#49), session-typed linear channels,
  MVars and locks (#52).

### Self-hosting

* The lexer, parser, kernel, frontend and a backend written in Wiz (`selfhost/*.wiz`,
  stages 12–21). The self-hosted frontend checks its own source, and the bootstrap
  reaches a fixpoint (stage-1 C = stage-2 C).
* Reference counting in the self-hosted backend (#9, #16, #28, #71, #77).
* Parity work: phantom parameters, constructor parameters from the expected type,
  `IO.args`, `--rc` (#44); foreign functions and types (21l, #73); written quantities,
  `private`, `link_c`/`link_lib`/`export` (21m–p, #113).

### Libraries

* The Prelude, `Vec`/`Fin`/`BitVec` (#3), `lib/Json.wiz` and `lib/Infoview.wiz` (#12),
  `lib/Text.wiz` (#103), `lib/Session.wiz` and `lib/MVar.wiz` (#52), `lib/Sys.wiz`
  (#64, #101). See docs/libraries.md.
* Separation logic (stage 24, #65): propositional logic over `Prop`, heaps and heap
  predicates, Hoare triples as a Dijkstra monad, and `x`-tactics (24d, #114, #127).
* HDL (experimental): a hash-consing netlist builder (#30), named ports, registers,
  bundles, composition, reset/enable, Verilog emitters and simulation (#81, #91, #108,
  #118).

### Tooling

* `wiz parse|check|build|run|lsp`.
* A content-addressed elaboration cache shared between projects (11c, #29).
* A language server: info tree, infoview protocol methods, code actions (11d, #6);
  `wiz lsp --infoview SOCK` (11l, #21) and `--ws` (#42); go to definition and hovers
  for syntax, binders, imports and instances (11q, #124); notation-aware printing with
  unexpanders, in messages, hovers and goals (11r, #139).
* Infoview clients in the terminal and in the browser (WebAssembly) (11m–n, #12).
* wiz.nvim, a Neovim plugin (11p, #47, #99).
* grail, a build tool and test runner configured in Wiz (stage 23): modules by path,
  a cache key per module, grail v0 (#7), the self-hosted toolchain as targets and a test
  runner (#17), parallel jobs (#22), git dependencies and `grail.lock` (#27), command
  targets, `grail run` and a job supervisor (#102), `grail lsp` (#95).
* tower, a toolchain manager with `wiz`/`grail` shims and a `wiz-toolchain` file per
  project (stage 26, #54, #90, #93), also written in Wiz (26e, #103). Channels: `stable`
  is the highest `vX.Y.Z` tag; `nightly` is the commit of the tag `nightly` for every
  source, Nix and source builds included (#159).
* `wiz --version`, `grail --version` and `tower --version` (#149), also through the
  toolchain wrappers.

### Distribution

* A Nix flake: `nix develop`, `packages.wiz`, `packages.tower`, `nvim-wiz`, with
  binaries on the Cachix cache `badlydrawnwizards` (#29).
* Release tarballs that need only glibc 2.27 (2.30 for the bundled C compiler), with
  their own C compiler, GMP and Boehm GC (26f, #100); a snapshot release for every
  master commit and a `nightly` tag that moves once CI passes (26g, #97). The bundle's
  downloads are mirrored and retried (#150). The bundle also has CaDiCaL, a SAT solver
  that writes LRAT proofs (the Lean toolchain's copy); z3 is not bundled.
* x86_64 Linux only: glibc 2.27 or later, 2.30 or later for `wiz build` with the bundled
  C compiler (Ubuntu 20.04+, Debian 11+, RHEL 9). Ubuntu 18.04 can check and run.
* CI: a merge queue (#141), heavy shards on a self-hosted runner (#142).

### Licence

* GPL-3.0-or-later, with the Wiz Runtime Library Exception for the runtime and the
  libraries, so programs built with Wiz can be licensed as their authors like (#86).
  Copyright (C) 2026 Reuben Steenekamp.
* The tarball carries `LICENSE`, `COPYING.RUNTIME`, a `NOTICE` listing the third-party
  code in the toolchain, and their licence texts (#150). Programs built with the bundled
  C toolchain link GMP statically: see NOTICE for what the LGPL asks when you
  distribute them.

### Known limitations

From [docs/Status.md](docs/Status.md) (its ledger, §0, has the details and the tests
that pin each one):

* Conjectures, not proved: regularity at inert types (D1; `--inert conv` is
  experimental), `μ` injective in its description (E1), and the rest of the core
  theory's combination (Status §1–2).
* Open issues: the neutral case of NU-TRANSP; Π/Σ/`ULift` casts compute without
  checking their components' sorts (D2, until mandatory sorts); an unannotated Π/Σ
  makes type equality stuck (U5); Σ unboxing is not stable under substitution, so
  `--unbox-structs` stays off (R3 open 1); duplicating a `&mut` and borrowing one
  local twice in Feral are not rejected (pinned "KNOWN GAP" tests).
* "Stuck but sound" cases (Status §5) are incompleteness: some true equations don't
  compute.
* No mechanised model, and no systematic search for proofs of `False` yet.
* Not yet in Wiz: string patterns, `deriving` in the self-hosted frontend, termination
  by measure, machine-integer and vector literals.
