# Wasm fixture programs

Small, IO-less Wiz programs the `packages.wiz-wasm-fixtures` derivation compiles with
`wiz build --target wasm` and runs under `web/wasm-host.mjs`. They are not a test
group (`Tests/Groups/` registers those, and `lake test -- '=wasm'` covers the backend
in-process); this directory is the on-disk fixture for the Nix output, so a change to
the emitter or the JS host has a reproducible artifact a build can check without a
`tests` binary.

Each `NAME.wiz` has one expected line in `expected.tsv`: `NAME<TAB>stdout`, the generic
tree syntax `web/wasm-host.mjs` prints for the module's `main`. Keep the result a
scalar (`Nat`/`Int`) where possible: constructor tags are an internal encoding, and a
fixture should fail loudly on a backend change, not pin the encoding by accident.
