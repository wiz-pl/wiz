# Wiz for JetBrains

A JetBrains IDE plugin for Wiz. It provides the `wiz`/`grail` language server,
syntax highlighting, an infoview tool window, run configurations and commands.

The launch and root rules are the same as `editors/nvim` (and the VS Code
extension); the shared test cases are in `editors/testdata/lsp-root-cases.json`.
The full parity matrix is in `editors/README.md`.

## Requirements

* IntelliJ Platform 2026.2+ (`since-build 262`), because the plugin uses the
  2026.1.4+ LSP API (`com.intellij.platform.lsp`: `LspIntegrationProvider`,
  `LspClientDescriptor`). The LSP module is an optional dependency
  (`META-INF/lsp.xml`); without it the syntax support still works.
* `wiz` on `PATH` (or Settings | Tools | Wiz), and `grail` for a grail package.
* JDK 21 and Gradle 8.14+ to build.

## Build

```sh
gradle wrapper --gradle-version 8.14.6   # once; the wrapper jar is not in the repo
./gradlew test                           # WizRootsTest
./gradlew buildPlugin                    # build/distributions/wiz-jetbrains-0.1.0.zip
./gradlew runIde                         # a sandbox IDE with the plugin
```

Or, without a local Gradle:

```sh
nix shell nixpkgs#gradle -c gradle buildPlugin
```

The first build downloads the IntelliJ Platform SDK (a large download).
Publishing (`./gradlew publishPlugin`) is not configured.

## What it does

* **Language.** `*.wiz` is a `Wiz` file type with a hand-written lexer and syntax
  highlighter (`WizLexer.kt`, `WizSyntaxHighlighter.kt`), a no-op parser/PSI tree
  for platform integration, and the LSP client started per root.
* **LSP.** `WizLspIntegrationProvider` starts one client per root with
  `wiz lsp`, `grail lsp -C ROOT` in a grail package, or an installed toolchain's
  own `wiz lsp` for `share/wiz/lib` files. The platform provides diagnostics,
  hover, completion, navigation, code actions, references, symbols, folding,
  inlay hints, semantic tokens and (on recent versions) signature help and
  rename.
* **Infoview.** The `Wiz Infoview` tool window asks `wiz/interactiveGoals`,
  `wiz/interactiveTermGoal` and `wiz/interactiveInfo` through
  `WizLsp4jServer` (custom lsp4j requests), shows the goals, expected type,
  messages and info sections, and a detail pane for `wiz/subtermInfo`. Widget
  titles are listed; widget HTML is not rendered yet.
* **Commands and run configurations.** Tools | Wiz: Show Infoview, Restart
  Language Server, Check File, Build, Format File. The `Wiz` run configuration
  runs `wiz check` or `grail build`/`wiz build` in a console.
* **Settings.** Settings | Tools | Wiz: executables, root markers, grail and
  toolchain toggles, infoview behaviour, external formatter.

## Verification status

`WizRoots.kt` and `WizRootsTest.kt` were compiled with `kotlinc 2.4.21` against
JUnit 4.13.2 and Gson 2.11.0, and the shared cases pass. The full Gradle build
was **not** run in the development environment (Gradle and the IntelliJ SDK are
large downloads); use the commands above and expect to fix any API drift against
the exact IDE version you target.
