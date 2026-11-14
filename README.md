# wiz

Wiz is a dependently typed language with quantitative types, built in Lean 4 as a
learning project and meant as the basis of a course in the style of *Software
Foundations*: each stage of the implementation is a set of exercises, with a test suite
that tells you when you've got them right. The toolchain is self-hosted: its kernel,
elaborator and compiler are also written in Wiz.

```
def id {0 A : Type} (1 x : A) : A := x
```

## Features

* **Quantitative type theory**: quantities `0`, `1`, `ω` on binders (the kernel is
  parametric in the rig), and quantity polymorphism; erased arguments cost nothing at
  run time.
* **Observational equality** with an impredicative, proof-irrelevant `Prop`: function
  extensionality, and `cast` that computes on data.
* **Data as descriptions**: `inductive` and `structure` elaborate to indexed
  descriptions with `μ`/`ν`; dependent pattern matching, mutual and indexed families.
* **Sized types** for termination and productivity, and **codata** (`ν`, copatterns).
* **Self-hosted**: the kernel, frontend and compiler in `selfhost/*.wiz` check and
  compile themselves, and the bootstrap reaches a fixpoint (stage-1 C = stage-2 C).
* **Native code**: erasure to an IR with Perceus reference counting and reuse, C and
  LLVM backends, a C FFI with header import, and machine integers and bit vectors.
* **Tooling**: a language server with an infoview (terminal and browser clients),
  a content-addressed elaboration cache, and **grail**, a build tool and test runner
  configured in Wiz.
* **Nix**: `nix develop` gives the whole toolchain; prebuilt binaries are on Cachix.

## Quick start

**New to Wiz?** [docs/install.md](docs/install.md) installs a toolchain and sets up an
editor, and [docs/tour.md](docs/tour.md) is a tour of the language.

Run Wiz without a checkout, with the binaries from the public Cachix cache:

```sh
cachix use badlydrawnwizards
nix run github:wiz-pl/wiz#wiz -- check hello.wiz   # `#grail` for grail
```

Or install toolchains with **tower** (like elan/rustup: `wiz` and `grail` shims on
`PATH`, a `wiz-toolchain` file per project; [docs/stages/26-tower.md](docs/stages/26-tower.md)):

```sh
nix profile install github:wiz-pl/wiz#tower
tower --self ~/.nix-profile/bin/tower self install   # shims in ~/.tower/bin: put it on PATH
tower default nightly
```

From a checkout:

```sh
nix develop         # the toolchain; writes this machine's paths to grail.local.wiz
lake build          # the library and the `wiz` executable
lake test           # the test suite (`lake test -- --list` for the groups)
```

See [docs/building.md](docs/building.md) for the details, CI and caches.

## Documentation

* [docs/install.md](docs/install.md): installing Wiz (tower, Nix), editors, a first package.
* [docs/tour.md](docs/tour.md): a tour of the language, with checked examples.
* [docs/index.md](docs/index.md): the stage-by-stage docs, one file per stage.
* [docs/attestation.md](docs/attestation.md): build manifests and TPM 2.0 quotes, and
  how to verify them.
* [docs/CoreSpec.md](docs/CoreSpec.md): the kernel's calculus as inference rules.
* [docs/Status.md](docs/Status.md): what is proved, what is conjectured, and the known
  soundness issues. Nothing about Wiz as a whole is proved yet.
* [ROADMAP.md](ROADMAP.md): the plan and the design decisions behind it.

**Exercises.** This repository is the solution tree; exercises are marked blocks in it.
`scripts/mkexercises.py . ../wiz-exercises` generates the exercise tree, with `sorry`
stubs, from a checkout (see [docs/exercises.md](docs/exercises.md)). There is no exercise
branch any more; the old one is archived as `exercises-archive`.

## Licence

Wiz is free software: you can redistribute it and/or modify it under the terms of the GNU
General Public License as published by the Free Software Foundation, either version 3 of
the License, or (at your option) any later version (SPDX: `GPL-3.0-or-later`). It is
distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; see
[LICENSE](LICENSE) for the full text.

**Programs you build with Wiz are yours to license as you like.** The runtime
(`runtime/`, `selfhost/rt.c`), the libraries (`lib/`) and whatever else a Wiz compiler copies
into its output are under the GPL *with the Wiz Runtime Library Exception*, an additional
permission under section 7 of GPLv3: see [COPYING.RUNTIME](COPYING.RUNTIME). The compilers,
checkers, kernels, grail, tower and the editor support are under the GPL without it.

One file comes
from elsewhere under its own, compatible licence: `editors/nvim/data/lean-abbreviations.json`
(Apache-2.0, see `editors/nvim/data/LICENSE.lean-abbreviations`). Programs built with Wiz link
against GMP (LGPL-3.0-or-later / GPL-2.0-or-later) and, for the self-hosted runtime, the Boehm
collector (MIT-style); the toolchain itself is built with Lean 4 (Apache-2.0).
