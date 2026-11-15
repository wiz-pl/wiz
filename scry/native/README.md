# Vendored tree-sitter (native parser)

scry parses C with [tree-sitter](https://tree-sitter.github.io/) through one C shim,
`ts_shim.c` (design §4.1). Both sources are vendored here so a build needs no network
and no `link_pkg` (which Wiz does not have): `link_c` compiles the files with the
program.

| source | version | commit |
|---|---|---|
| [tree-sitter](https://github.com/tree-sitter/tree-sitter) | v0.27.2 | `3fb7be49145acfb07e33b61ed5689e2b6771b2e9` |
| [tree-sitter-c](https://github.com/tree-sitter/tree-sitter-c) | v0.24.2 | `b780e47fc780ddc8da13afa35a3f4ed5c157823d` |

Both are MIT licensed; the licence texts are `tree-sitter/LICENSE` and
`tree-sitter-c/LICENSE`. `tree-sitter-c/src/parser.c` is generated from that grammar
(`LANGUAGE_VERSION 15`, which is the ABI this runtime implements).

## Layout

```
native/
├── ts_shim.c                     the one C entry point (scry_parse + column accessors)
├── tree-sitter/
│   ├── LICENSE
│   └── lib/
│       ├── include/tree_sitter/api.h        the public runtime API
│       └── src/                             runtime sources; lib.c includes them all
└── tree-sitter-c/
    ├── LICENSE
    ├── node-types.json                      the grammar's node/field description
    └── src/
        ├── parser.c                         generated parser (4.1 MB)
        └── tree_sitter/{alloc,array,parser}.h
```

Two include-path adjustments are vendoring only (no source change); they let
`link_c` compile the files without `-I` flags:

* `tree-sitter/lib/src/tree_sitter/api.h` forwards to
  `../../include/tree_sitter/api.h` (the runtime sources include
  `"tree_sitter/api.h"`);
* `tree-sitter/lib/src/unicode/unicode/*.h` forward to the headers one level up (the
  Unicode headers include each other as `"unicode/…"`).

Everything else is the upstream files: `tree-sitter/lib/src/lib.c` and
`tree-sitter-c/src/parser.c` are compiled as they are, at the version above.

## Build

`src/Scry/Native.wiz` has

```wiz
link_c "../../native/ts_shim.c"
link_c "../../native/tree-sitter/lib/src/lib.c"
link_c "../../native/tree-sitter-c/src/parser.c"
```

grail compiles the `link_c` files with the same compiler and cflags as the program and
keys the link job by their paths and contents. `wiz check` only checks that the files
exist; the C compiler runs on `wiz build`/`wiz run` and on grail's link job.

The shim uses the runtime's C interface for word arrays (`wiz_warray_of_c`, see
`docs/stages/29-natives.md`): a column is copied into an owned `U32Array`/`U64Array`,
and no C struct crosses the FFI by value.
