# Hdl

`Hdl` is the hardware-description library: circuits are ordinary Wiz values, simulated
by evaluation and emitted as Verilog/Netlist text. It is a package, not part of the
toolchain's `lib/` (`separate-repos.md` §1.2), and its modules are still imported as
`Hdl.*`.

```
grail build          # check src/ and run every example in examples/
grail build hdl      # just the library
grail test           # every example, compared with examples/NAME.expected
```

The package's only dependencies are the toolchain's standard library (`BitVec`, `Vec`,
`Trace`, `Optic`, `Deriving`, `IO`, `Text`, `Std`), so `grail` resolves them from its own
`lib/` root. In a wiz-lang checkout that keeps the examples which import `Hdl.*`
(`examples/rune-*.wiz`, `examples/hardware-tour.wiz`), the root `grail.wiz` adds
`hdl/src` as a module root; that is a co-development root, not a check target.

`scripts/gen-uart-temporal.py` regenerates the marked case analyses inside
`examples/hdl-uart-temporal.wiz`:

```
python3 scripts/gen-uart-temporal.py examples/hdl-uart-temporal.wiz
```
