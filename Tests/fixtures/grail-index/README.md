# A minimal, hermetic `grail-index`

This directory is a small package index in the layout a real index repository uses; the
`grail-deps` tests read it directly (no network, no git, no server).

```
registry.sexpr            index metadata (name and format)
entries/NAME.sexpr.in     one S-expression file per package, with @SHA:NAME-V@ holes
sources/NAME-V/           the unpacked sources the archives are made from
make.sh OUT               render the index into OUT (below)
```

Only those inputs are committed. `make.sh OUT` writes the index the tests read:
`OUT/registry.sexpr`, `OUT/packages/NAME-V.tar.gz` (the release archives) and
`OUT/index/NAME.sexpr` (the entries with every hole filled in with the archive's
SHA-256).

The fixture covers:

| package | versions | dependencies |
|---|---|---|
| `std` | `0.1.0` | — |
| `text` | `1.0.0`, `1.1.0` | `std ^0.1` |
| `greet` | `1.0.0`, `1.2.0`, `2.0.0` | `text ~1.0`, `text ^1`, — |

`greet 1.0.0` is the exact-version case, `greet ^1`/`~1.0` exercise the range and
transitive cases, and `greet 2.0.0` is the no-dependency case used for a one-package
fetch. The tests also refer to a package `missing` that is deliberately absent.

`source` fields are **relative** here: `packages/greet-1.2.0.tar.gz`. Grail resolves a
relative source against the directory of the index it read (`Grail/Registry.lean`,
`readIndexDir`), so a local mirror or a checkout is self-contained. A published index
should use absolute `https://` (or `file://`) URLs.

The tests (`indexFixture` in `Tests/Grail.lean`) run `make.sh` into a fresh temporary
directory for every case, so a case never sees another's changes and nothing is written
into the checkout. By hand:

```sh
Tests/fixtures/grail-index/make.sh /tmp/grail-index && grail update --index /tmp/grail-index
```

The archive layout is the fixed one: one top-level `NAME-VERSION/` with `grail.wiz`.
`gzip -n` and `--sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner` make the
bytes deterministic, so the `sha256` values in `index/*.sexpr` are the same on every run (GNU tar is
needed for `--sort`).
