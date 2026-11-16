# Vendored tree-sitter (native parser)

scry parses C and C# with [tree-sitter](https://tree-sitter.github.io/) through one C
shim, `ts_shim.c` (design §4.1; `scry_parse` takes the language, `"c"` or `"c_sharp"`).
The sources are vendored here so a build needs no network and no `link_pkg` (which Wiz
does not have): `link_c` compiles the files with the program.

| source | version | commit |
|---|---|---|
| [tree-sitter](https://github.com/tree-sitter/tree-sitter) | v0.27.2 | `3fb7be49145acfb07e33b61ed5689e2b6771b2e9` |
| [tree-sitter-c](https://github.com/tree-sitter/tree-sitter-c) | v0.24.2 | `b780e47fc780ddc8da13afa35a3f4ed5c157823d` |
| [tree-sitter-c-sharp](https://github.com/tree-sitter/tree-sitter-c-sharp) | v0.23.5 | `cac6d5fb595f5811a076336682d5d595ac1c9e85` |

All three are MIT licensed; the licence texts are `tree-sitter/LICENSE`,
`tree-sitter-c/LICENSE` and `tree-sitter-c-sharp/LICENSE`. Each grammar's
`src/parser.c` is the upstream generated file, not regenerated here
(`LANGUAGE_VERSION 15`, which is the ABI this runtime implements).

tree-sitter-c-sharp is the upstream release tarball of tag `v0.23.5` (annotated tag
object `173c15453b733ccde654032fec7103705b5ad04f`, commit above; Nix
`fetchFromGitHub` hash `sha256-N5AAlwQFGGi47cj0m7Te08bA486gwY6NBOx4Qcy4lpo=`). Only
`src/parser.c`, `src/scanner.c` (the external scanner: interpolated and raw strings,
preprocessor lines), `src/tree_sitter/*.h`, `src/node-types.json` and `LICENSE` are
copied. `parser.c` is 29 664 333 bytes (about 1.3 MB compressed in git) and compiles at
`-O2` in about 1.5 s; the C# frontend's adapter (`src/Scry/CsCst.wiz`) is what reads its
node kinds.

## Layout

```
native/
├── ts_shim.c                     the one C entry point (scry_parse + column accessors)
├── tree-sitter/
│   ├── LICENSE
│   └── lib/
│       ├── include/tree_sitter/api.h        the public runtime API
│       └── src/                             runtime sources; lib.c includes them all
├── tree-sitter-c/
│   ├── LICENSE
│   ├── node-types.json                      the grammar's node/field description
│   └── src/
│       ├── parser.c                         generated parser (4.1 MB)
│       └── tree_sitter/{alloc,array,parser}.h
└── tree-sitter-c-sharp/
    ├── LICENSE
    ├── node-types.json
    └── src/
        ├── parser.c                         generated parser (29.7 MB)
        ├── scanner.c                        the grammar's external scanner
        └── tree_sitter/{alloc,array,parser}.h
```

Two include-path adjustments are vendoring only (no source change); they let
`link_c` compile the files without `-I` flags:

* `tree-sitter/lib/src/tree_sitter/api.h` forwards to
  `../../include/tree_sitter/api.h` (the runtime sources include
  `"tree_sitter/api.h"`);
* `tree-sitter/lib/src/unicode/unicode/*.h` forward to the headers one level up (the
  Unicode headers include each other as `"unicode/…"`).

Everything else is the upstream files: `tree-sitter/lib/src/lib.c`, both `parser.c`
files and `tree-sitter-c-sharp/src/scanner.c` are compiled as they are, at the versions
above (each grammar's `src/` holds its own `tree_sitter/parser.h`, so the two never mix).

## Build

`src/Scry/Native.wiz` has

```wiz
link_c "../../native/ts_shim.c"
link_c "../../native/tree-sitter/lib/src/lib.c"
link_c "../../native/tree-sitter-c/src/parser.c"
link_c "../../native/tree-sitter-c-sharp/src/parser.c"
link_c "../../native/tree-sitter-c-sharp/src/scanner.c"
```

grail compiles the `link_c` files with the same compiler and cflags as the program and
keys the link job by their paths and contents. `wiz check` only checks that the files
exist; the C compiler runs on `wiz build`/`wiz run` and on grail's link job.

The shim uses the runtime's C interface for word arrays (`wiz_warray_of_c`, see
`docs/stages/29-natives.md`): a column is copied into an owned `U32Array`/`U64Array`,
and no C struct crosses the FFI by value.
