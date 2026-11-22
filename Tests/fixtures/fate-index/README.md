# A minimal, hermetic `fate-index`

This directory is a small package index in the layout a real index repository uses; the
`grail-deps` tests read it directly (no network, no git, no server).

```
registry.sexpr          index metadata (name and format)
index/NAME.sexpr        one S-expression file per package
packages/NAME-V.tar.gz  the immutable release archives
sources/NAME-V/         the unpacked sources the archives are made from
make.sh                 rebuild the archives deterministically
```

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

`make.sh` rebuilds the archives. They are checked in so the tests need no `tar -czf`
at run time (a normal `tar -xzf` is still used by `grail fetch`):

```sh
cd Tests/fixtures/fate-index && ./make.sh
```

The archive layout is the fixed one: one top-level `NAME-VERSION/` with `grail.wiz`.
`gzip -n` and `--sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner` make the
bytes deterministic, so the `sha256` values in `index/*.sexpr` can be re-derived.
