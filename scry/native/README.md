# tree-sitter (native parser)

scry parses C and C# with [tree-sitter](https://tree-sitter.github.io/) through one C
shim, `ts_shim.c` (design §4.1; `scry_parse` takes the language, `"c"` or `"c_sharp"`).
`link_c` compiles the sources with the program (Wiz has no `link_pkg`). The runtime and
the C grammar are vendored here; the C# grammar is fetched by Nix, because its
generated `parser.c` (29.7 MB) is not committed.

| source | version | commit | provided by |
|---|---|---|---|
| [tree-sitter](https://github.com/tree-sitter/tree-sitter) | v0.27.2 | `3fb7be49145acfb07e33b61ed5689e2b6771b2e9` | vendored, `tree-sitter/` |
| [tree-sitter-c](https://github.com/tree-sitter/tree-sitter-c) | v0.24.2 | `b780e47fc780ddc8da13afa35a3f4ed5c157823d` | vendored, `tree-sitter-c/` |
| [tree-sitter-c-sharp](https://github.com/tree-sitter/tree-sitter-c-sharp) | v0.23.5 | `cac6d5fb595f5811a076336682d5d595ac1c9e85` | Nix, `.#tree-sitter-c-sharp` |

All three are MIT licensed. The vendored licence texts are `tree-sitter/LICENSE` and
`tree-sitter-c/LICENSE`; tree-sitter-c-sharp's is in the fetched tree and copied below.
Each grammar's `src/parser.c` is the upstream generated file, not regenerated here
(`LANGUAGE_VERSION 15`, which is the ABI this runtime implements).

### tree-sitter-c-sharp

`flake.nix` pins it as `fetchFromGitHub` of commit `cac6d5fb…` (tag `v0.23.5`, annotated
tag object `173c15453b733ccde654032fec7103705b5ad04f`) with hash
`sha256-N5AAlwQFGGi47cj0m7Te08bA486gwY6NBOx4Qcy4lpo=`. The build reads
`src/parser.c`, `src/scanner.c` (the external scanner: interpolated and raw strings,
preprocessor lines) and `src/tree_sitter/*.h`; `src/node-types.json` describes the node
kinds that `src/Scry/CsCst.wiz` reads. `parser.c` is 29 664 333 bytes and compiles at
`-O2` in about 1.5 s.

To compile scry's native code (`grail build`, `wiz build tools/CstMain.wiz`, …), make
the out-link from the repository root first:

```sh
nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp
```

`scry/native/tree-sitter-c-sharp` is then a symlink into the store (and a GC root); it
is gitignored. Without it, `wiz check` of `src/Scry/Native.wiz` reports
`link_c: no file ../../native/tree-sitter-c-sharp/src/parser.c`. The Lean test groups
don't need it: they read checked-in spills (`corpus/**/*.cst`).

`.#scry-native` builds the whole native side in Nix, as `lib/libscry-ts.a`: the
runtime, both grammars and the shim. Its check parses a C file and a C# file through
`scry_parse`. It is pushed to Cachix, so a checkout can substitute it instead of
compiling.

The tree-sitter-c-sharp licence (`LICENSE` at the commit above):

```
The MIT License (MIT)

Copyright (c) 2014-2023 Max Brunsfeld, Damien Guard, Amaan Qureshi, and contributors.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

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
└── tree-sitter-c-sharp -> /nix/store/…-source   uncommitted out-link (above)
```

Two include-path adjustments are local to the vendored runtime (no source change); they let
`link_c` compile the files without `-I` flags:

* `tree-sitter/lib/src/tree_sitter/api.h` forwards to
  `../../include/tree_sitter/api.h` (the runtime sources include
  `"tree_sitter/api.h"`);
* `tree-sitter/lib/src/unicode/unicode/*.h` forward to the headers one level up (the
  Unicode headers include each other as `"unicode/…"`).

Everything else is the upstream files: `tree-sitter/lib/src/lib.c`, both `parser.c`
files and tree-sitter-c-sharp's `src/scanner.c` are compiled as they are, at the versions
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
