# Wiz for VS Code

Wiz language support for Visual Studio Code: the `wiz`/`grail` language server,
syntax highlighting, an infoview, and commands to check and build Wiz files.

This extension uses the same server launch and root rules as `editors/nvim` (the
parity matrix and the rules are in `editors/README.md`):

* start `wiz lsp` rooted at the nearest directory with `grail.wiz`,
  `wiz-toolchain`, `lakefile.toml` or `.git`, else at the file's own directory;
* in a grail package (the root has a `grail.wiz`) start `grail lsp -C ROOT`, so
  the server sees the package's modules and toolchain settings;
* a file in an installed toolchain's `share/wiz/lib` is served by that
  toolchain's own `wiz lsp`, one server per toolchain.

`wiz` (and `grail` for a grail package) must be on `PATH`, or set
`wiz.server.path` / `wiz.grail.path`.

## Settings

| setting | default | |
|---|---|---|
| `wiz.server.path` | `wiz` | the wiz executable |
| `wiz.server.args` | `["lsp"]` | arguments for the server |
| `wiz.grail.enabled` | `true` | use `grail lsp` in a grail package |
| `wiz.grail.path` | `grail` | the grail executable |
| `wiz.grail.args` | `["lsp"]` | `-C ROOT` is appended |
| `wiz.toolchains.enabled` | `true` | per-toolchain servers for library files |
| `wiz.rootMarkers` | `["grail.wiz","wiz-toolchain","lakefile.toml",".git"]` | project roots |
| `wiz.infoview.autoOpen` | `true` | open on the first Wiz file |
| `wiz.infoview.followCursor` | `true` | follow the cursor |
| `wiz.infoview.debounce` | `150` | milliseconds |
| `wiz.format.command` | `[]` | external formatter; `{file}` is replaced |
| `wiz.check.extraArgs` | `[]` | extra arguments for `wiz check` |
| `wiz.build.target` | `""` | a grail target (empty: every target) |

## Commands

* **Wiz: Restart Language Server** (`wiz.restartServer`)
* **Wiz: Format File** (`wiz.format`) — uses `textDocument/formatting` when the
  server provides it, else `wiz.format.command`;
* **Wiz: Check File** (`wiz.lint`) — runs `wiz check` (with `-I src` in a grail
  package) in a terminal;
* **Wiz: Build** (`wiz.build`) — `grail build` in a grail package, else
  `wiz build FILE -o .wiz-build/NAME`;
* **Wiz: Show Infoview** (`wiz.infoview.show`), **Refresh Infoview**;
* **Wiz: Show Language Server Log**.

## Infoview

The infoview is a Webview beside the editor. It follows the cursor and shows the
tactic state, the expected type, messages, syntax/expansion/import/instances/
declarations, and tactic widgets (in a sandboxed iframe; the 11af server is not on master yet). Click a subterm to see
its text, type and declaration; click an info title to jump to it.

## Development

```sh
npm install
npm run typecheck
npm test           # shared root/launch cases + the TextMate grammar
npm run package    # dist/extension.js and wiz-0.1.0.vsix
```

The root/launch rules live in `src/root.ts` and do not import `vscode`, so they
are tested with plain Node. The TextMate grammar is derived from
`editors/nvim/syntax/wiz.vim`.

## License

GPL-3.0-or-later (the abbreviation table of the Neovim plugin is Apache-2.0; this
extension does not vendor it).
