# The Hdl package

`Hdl` is Wiz's hardware-description library: a circuit is an ordinary Wiz value, simulated
by evaluation, emitted as Verilog or a netlist, and proved about with the same terms. It
is a **package**, not part of the toolchain's standard library: its sources are
`hdl/src/Hdl/*.wiz` and its modules are imported as `Hdl.*`.

The reference for the library's layers is [libraries.md](libraries.md) (sections H0c, H14
and the stage 34 signals page); this page describes the package: how to build and test it,
what it depends on, and what a release tag means.

## Using it

The import is shown for orientation; `Hdl.Core` is large enough that checking it here would
cost minutes per docs run, so the fence is not executed (`hdl`'s own groups check the
library).

```wiz no-check
import Hdl.Core
-- import Hdl.Sim, Hdl.Temporal, Hdl.Bus, Hdl.Axi4, …
```

The manifest is `hdl/grail.wiz`: a library target rooted at `src/` (so `Hdl.Core` is
`src/Hdl/Core.wiz`) and tests rooted at `examples/`. Its only dependency is the
toolchain's standard library — `BitVec`, `Vec`, `Trace`, `Optic`, `Deriving`, `IO`,
`Text`, `Std` — which `grail` resolves from the toolchain that runs it, not from a root
of this package. The manifest names the tested toolchain range
(`Package.toolchain ">=0.1.0 <0.3.0"`); a build with a toolchain outside that range is
not expected to work.

In this repository the package is co-developed with the root tree: the root `grail.wiz`
adds `hdl/src` as a module root so the examples that import `Hdl.*`
(`examples/rune-*.wiz`, `examples/hardware-tour.wiz`, `examples/tour/10-hdl.wiz`,
`bench/stdlib-bench.wiz`) resolve. That is a one-way dependency: `hdl/` uses `lib/`, and
nothing in `lib/` may import `Hdl.*`.

## Building and testing

```sh
cd hdl
grail build          # check the library in src/
grail build hdl      # just the library
grail test           # every example, its messages against the expected file beside it
```

The package is relocatable: copy `hdl/` anywhere and the same commands work with only a
Wiz toolchain, because both roots are relative to the manifest and the std comes from the
toolchain. `hdl/scripts/check-standalone.sh` proves it — it copies only `hdl/`, then runs
`grail build && grail test` on the copy:

```sh
hdl/scripts/check-standalone.sh
GRAIL=/path/to/toolchain/bin/grail hdl/scripts/check-standalone.sh
```

CI reads the package through `HDL_ROOT` (default `hdl`): the Lean `=hdl-*` groups load
`$HDL_ROOT/src/Hdl` and `$HDL_ROOT/examples`, so the same cases can run against a copy or
a parity checkout. `HDL_ROOT=/tmp/hdl-copy tests =hdl-examples` is the package-copy run;
the in-repo default is `HDL_ROOT=hdl`.

`grail test` compares the examples' **messages** with the 32 committed `.expected` files
(four examples are `-- test: skip` with a reason, and `hdl-spi`/`hdl-stream` have
`-- test: run`, so their program output is compared). It does not synthesise or run a
formal proof: the yosys, Icarus and formal assertions are cases of the Lean `hdl`,
`hdl-protocols`, `hdl-signal`, `hdl-temporal` and related groups, which is why they still
live in the repository's test suite until the package has a harness of its own.

## Layout

| path | what it is |
|---|---|
| `src/Hdl/` | the library: 32 modules, from `Core.wiz` (circuits, bundles, emitters) to the protocol and board modules |
| `examples/` | the package's tests, one `.wiz` and its `.expected` per golden; `scripts/gen-uart-temporal.py` regenerates the UART temporal case analyses |
| `scripts/check-standalone.sh` | the G1 proof above |
| `grail.wiz` | the manifest (`Package.lib`, `Package.tests`, version and toolchain range) |
| `README.md` | the short quick start |
| `LICENSE`, `COPYING.RUNTIME`, `NOTICE` | the package's licence, the Wiz runtime exception and its notice |

## Boundary

The package's dependency is one-way: `hdl/` uses the toolchain's `lib/`, and nothing in
`lib/` may import `Hdl.*`. `scripts/check-boundaries.py` (run by the `docs style` CI job)
enforces that statically: `lib/` may not import `Hdl.*`, `hdl/src` may import only
`Hdl.*` and std modules, the `Hdl.*` consumers outside the package must be in
`examples/`, `bench/` or `drafts/`, and no committed file under `hdl/` may name `../` or
`.lake`.

## Licence

The package is free software under the GNU General Public License, version 3 or later
(`hdl/LICENSE`). Its sources are compiled by the Wiz toolchain, whose runtime carries the
Wiz Runtime Library Exception (`hdl/COPYING.RUNTIME`); the exception covers the runtime,
not this package's sources. There is no third-party source in the package; see
`hdl/NOTICE`.

## Releases and tags

The manifest's `Package.version` is `0.1.0`. **No release tag exists yet**: `0.1.0` is
the development version, not a release.

A release tag is `hdl-vX.Y.Z` — the repository's `vX.Y.Z` tag form with the package
name in front, since one repository can carry more than one package — on a commit with
three properties:

1. `hdl/grail.wiz`'s `Package.version` is exactly `X.Y.Z`;
2. the commit's `=hdl-examples` run is green with a toolchain inside
   `Package.toolchain`, and the toolchain is recorded in the release note;
3. the commit is on `master` (a tag is not a branch head that later moves).

Tags are immutable; a change after the tag is a new version, never a moved tag. The
version follows the repository's 0.x form ([stability.md](stability.md)): a patch release
fixes without changing what the manifest promises, a minor release may break the API.
A tag versions the package only. It does not mean the Wiz toolchain release ships `hdl`
(the release tarball does not), and it does not extend the toolchain's own stability
promise to this package beyond the `Package.toolchain` range.
