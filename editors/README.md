# Wiz editor support

Three clients for the Wiz language server: **wiz.nvim** (`editors/nvim`, the
original), **Wiz for VS Code** (`editors/vscode`) and **Wiz for JetBrains**
(`editors/jetbrains`). They share the server launch and root rules below; the
parity matrix records what each one shows and what is still missing.

The server protocol is in `wiz-notes/infoview-protocol.md`; the Neovim plugin's
stage notes are in `docs/stages/11-tooling.md` (11p), and the widget protocol in
`wiz-notes/infotree-widgets.md`.

## Server launch and root rules (normative)

These are the rules `editors/nvim/lua/wiz/lsp.lua` implements; the VS Code
`src/root.ts` and the JetBrains `WizRoots.kt` are ports of them, and
`editors/testdata/lsp-root-cases.json` is the shared test suite (both clients run
the same cases).

1. **An installed toolchain's library file.** Walk up from the file. If a parent
   directory is named `lib` and
   * `lib/Prelude.wiz` exists,
   * `../.lake/build/bin/wiz` exists (relative to `lib/`: `share/wiz/.lake/build/bin/wiz`), and
   * `share/wiz/TOOLCHAIN` (older installations: `REVISION`) exists,

   then the root is that `lib/` and the server is **that toolchain's own `wiz lsp`**:
   `share/wiz/bin/wiz` (the wrapper) when it is executable, else
   `share/wiz/.lake/build/bin/wiz`. One server per toolchain; the version of the
   server matches the library files. `wiz.toolchains.enabled` (VS Code) /
   `toolchains` (JetBrains) turns this off.
2. **The nearest project marker.** Otherwise the root is the nearest ancestor
   directory of the file (its own directory included) containing any of
   `grail.wiz`, `wiz-toolchain`, `lakefile.toml`, `.git`. The marker list is
   configurable (`wiz.rootMarkers` / root markers in Settings | Tools | Wiz).
3. **No marker.** The root is the file's own directory.
4. **grail package.** If the root has a `grail.wiz` and grail is enabled, start
   **`grail lsp -C ROOT`** with cwd `ROOT`, so the server finds the package's
   modules (`src/` of its `Package.lib` targets and its dependencies) and uses its
   toolchain settings. If the grail executable is not found, warn once and fall
   back to `wiz lsp`.
5. **Otherwise** start **`wiz lsp`** with cwd `ROOT`.

`wiz` and `grail` are taken from `PATH` unless configured
(`wiz.server.path`/`wiz.grail.path`, or the JetBrains settings). A VS Code
workspace can have several roots (or toolchains) open at once; each gets its own
client. JetBrains starts one `LspClient` per root as files open.

## Installing and building

### Neovim

See `editors/nvim/README.md`. The plugin itself is unchanged by this work;
`lake test -- '=nvim'` still runs its headless tests.

### VS Code

```sh
cd editors/vscode
npm install
npm run typecheck          # tsc --noEmit
npm test                   # the shared root/launch cases and the TextMate grammar
npm run package            # dist/extension.js + wiz-0.1.0.vsix
code --install-extension wiz-0.1.0.vsix
```

For development, `code --extensionDevelopmentPath="$PWD" /path/to/file.wiz`
after `npm run compile`. The TextMate grammar (`syntaxes/wiz.tmLanguage.json`)
is derived from `editors/nvim/syntax/wiz.vim`.

### JetBrains

The project targets IntelliJ Platform 2026.2+ (`since-build 262`) and uses the
2026.1.4+ LSP API (`com.intellij.platform.lsp`: `LspIntegrationProvider`,
`LspClientDescriptor`). The LSP module is an optional dependency (`lsp.xml`), so
syntax highlighting still works in IDEs without it.

```sh
cd editors/jetbrains
gradle wrapper --gradle-version 8.14.6   # once; the wrapper jar is not committed
./gradlew test                           # WizRootsTest (the shared cases)
./gradlew buildPlugin                    # build/distributions/wiz-jetbrains-0.1.0.zip
./gradlew runIde                         # an IDE with the plugin
```

Without a local Gradle: `nix shell nixpkgs#gradle -c gradle buildPlugin` (the
first build downloads the IntelliJ Platform SDK). `buildPlugin` is the package
step; publishing to the JetBrains Marketplace (`./gradlew publishPlugin` with a
token) is not done.

## Feature inventory and parity matrix

Legend: **yes** = implemented; **partial** = works with a documented limit;
**—** = not implemented (gap); **n/a** = not a feature of that client.
The Neovim column is the baseline (`editors/nvim/README.md`).

| feature | nvim | VS Code | JetBrains | notes |
|---|---|---|---|---|
| filetype `wiz`, `*.wiz` | yes | yes | yes | |
| syntax highlighting | yes (Vim regex) | yes (TextMate) | yes (hand-written lexer) | same scope categories; the JetBrains lexer is an approximation |
| `wiz lsp` | yes | yes | yes | same rules |
| `grail lsp -C ROOT` in a package | yes | yes | yes | |
| root markers (`grail.wiz`, `wiz-toolchain`, `lakefile.toml`, `.git`) | yes | yes | yes | configurable |
| per-toolchain server for `share/wiz/lib` | yes | yes | yes | |
| diagnostics | yes | yes | yes | LSP `publishDiagnostics` |
| hover | yes | yes | yes | |
| go to definition / declaration | yes | yes | yes | |
| completion | yes | yes | yes | |
| signature help | yes | yes | yes (2025.3+) | platform version gate |
| code actions (did-you-mean, missing cases, ascription, hole fill) | yes | yes | yes | server-side |
| references, rename, document highlights | yes | yes | yes (rename 2026.1.1+) | |
| outline, workspace symbols | yes | yes | yes (2025.3+) | |
| folding | yes (opt-in) | yes | yes (2025.2.2+) | |
| inlay hints | yes (opt-in) | yes | yes (2025.2.2+) | |
| semantic tokens | yes | yes | yes (2024.2.2+) | server provides `keyword` only |
| infoview: goals | yes | yes | yes | |
| infoview: expected type | yes | yes | yes | |
| infoview: subterm inspection | yes (`K`) | yes (click) | yes (click a leaf) | JetBrains detail pane |
| infoview: syntax / expansion / import / instances / declarations / messages | yes | yes | yes | `wiz/interactiveInfo` |
| infoview: tactic widgets | — | partial (sandboxed iframe; unverified) | partial (titles only) | nvim/terminal/web do not draw widgets; 11af was not on master to exercise |
| infoview follows cursor / auto-open | yes | yes | yes | |
| infoview: browser (`wiz/browserInfoview`) | yes | — | — | gap |
| format file | — | partial | partial | server advertises no `textDocument/formatting`; VS Code uses an external command, JetBrains shows a hint |
| check / lint command | — | yes (`wiz check` terminal) | yes (action + run configuration) | |
| build command | — | yes (`grail build` / `wiz build`) | yes (action + run configuration) | |
| restart server | yes | yes | yes | |
| run configurations | n/a | n/a | yes | check/build |
| unicode abbreviations (`\lam` → λ) | yes | — | — | gap; table is `editors/nvim/data/lean-abbreviations.json` |
| abbreviation list / lookup | yes | — | — | gap |
| tests | headless Neovim | Node root/launch tests | JUnit root/launch tests | |

### Gaps, in order of what a user notices

1. **Unicode input** is Neovim-only. VS Code cannot intercept insert-mode text
   the way `InsertCharPre` does; a proper port needs a completion provider or a
   document-change abbreviation expander (the same table could be generated from
   `editors/nvim/data/lean-abbreviations.json`). JetBrains has the same problem
   (a `TypedHandler` plus an `EditorActionHandler` would be the route).
2. **Widgets** are wired in VS Code to a sandboxed `iframe`, but no widget-emitting
   server was on master to exercise it; JetBrains lists their titles and does not
   render the HTML yet. nvim/terminal/web do not draw them.
3. **Browser infoview** (`wiz/browserInfoview`) is not wired in VS Code or
   JetBrains; both use an in-editor view.
4. **Formatting** has no server support. The commands are present and fall back to
   an external `wiz.format.command` (VS Code) / Settings | Tools | Wiz formatter
   (JetBrains); `wiz` has no `fmt` subcommand yet.
5. **Position encoding.** The server counts Unicode characters, not UTF-16 code
   units (protocol §0). Both clients convert columns at the boundary, but a
   non-BMP character in a line is still a risk until the server advertises
   `positionEncoding`.
6. **Publishing.** The VSIX is built locally; the JetBrains ZIP is built by
   `buildPlugin`; neither is published. The JetBrains build was not run in the
   development environment (no Gradle/IntelliJ SDK), so it is unverified; the
   pure root logic was compiled and tested with `kotlinc`.
7. **JetBrains notifications.** The JetBrains client does not request the
   `wiz/elaborated` notification; the infoview refreshes on caret/document changes
   and after its own requests instead.
8. **Nested roots.** A document selector cannot exclude a subtree: when a
   directory inside a root has its own marker, a file in it may be seen by both the
   outer and the inner server (duplicate diagnostics). Keep such packages in
   separate windows, or stop the outer server.

## Tests

* `editors/testdata/lsp-root-cases.json` — the shared cases (plain project,
  nearest marker, grail package, grail disabled/missing, toolchain wrapper,
  toolchain without wrapper, `REVISION`, toolchains disabled, no marker, custom
  markers, nested package).
* VS Code: `cd editors/vscode && npm test` (20 Node tests: 15 launch/root and 5 grammar; 2026-11-14).
* JetBrains: `WizRootsTest` runs the same file. The test was compiled with
  `kotlinc 2.4.21` and JUnit 4.13.2 and passed; `gradle test` is unverified here.
* End-to-end smoke: VS Code was started under Xvfb with `--extensionDevelopmentPath`
  and a fake `wiz`/`grail` on PATH. It launched `wiz lsp` with cwd at the plain
  project root and `grail lsp -C /path/to/pkg` with cwd at the package root.
