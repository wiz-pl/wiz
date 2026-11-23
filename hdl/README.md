# Hdl

`Hdl` is the hardware-description library: circuits are ordinary Wiz values, simulated
by evaluation and emitted as Verilog/Netlist text. It is a package, not part of the
toolchain's `lib/` (`separate-repos.md` §1.2), and its modules are still imported as
`Hdl.*`.

```
grail build          # check the library in src/
grail build hdl      # just the library
grail test           # every example, compared with examples/NAME.expected
```

The package's only dependencies are the toolchain's standard library (`BitVec`, `Vec`,
`Trace`, `Optic`, `Deriving`, `IO`, `Text`, `Std`), so `grail` resolves them from its own
`lib/` root. Both roots in `grail.wiz` are relative to the package, so a copy of `hdl/`
builds and tests with only a toolchain:

```
hdl/scripts/check-standalone.sh          # copy hdl/ alone, then grail build && grail test
GRAIL=/path/to/grail hdl/scripts/check-standalone.sh
```

In a wiz-lang checkout that keeps the examples which import `Hdl.*`
(`examples/rune-*.wiz`, `examples/hardware-tour.wiz`), the root `grail.wiz` adds
`hdl/src` as a module root; that is a co-development root, not a check target. The
dependency is one-way: the std never imports `Hdl.*` (`scripts/check-boundaries.py`).
CI's `=hdl-*` groups read the package through `HDL_ROOT` (default `hdl`).

`scripts/gen-uart-temporal.py` regenerates the marked case analyses inside
`examples/hdl-uart-temporal.wiz`:

```
python3 scripts/gen-uart-temporal.py examples/hdl-uart-temporal.wiz
```

## Licence and releases

GNU GPL version 3 or later (`LICENSE`), with the Wiz Runtime Library Exception
(`COPYING.RUNTIME`) and its notice (`NOTICE`). The manifest's version is `0.1.0`; there
is no release tag yet. A release tag is `hdl-vX.Y.Z` on a commit whose
`Package.version` is `X.Y.Z` and whose `=hdl-examples` run is green; the repository's
`docs/hdl.md` ("Releases and tags") has the policy.
