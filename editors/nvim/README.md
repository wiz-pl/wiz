# wiz.nvim

Wiz in Neovim (0.10 or later; tested with 0.12):

* **the language server**: the `wiz` filetype for `*.wiz`, highlighting from a syntax file
  (no tree-sitter needed), and `wiz lsp` started for every Wiz buffer. Its root is the
  nearest directory with `grail.wiz`, `wiz-toolchain`, `lakefile.toml` or `.git`, else the file's own
  directory. In a grail package (the root has a `grail.wiz`) the plugin starts `grail lsp`
  instead, so that the server finds the package's modules (`import Icestick.Gates` from
  `src/` of a `Package.lib "lib" "src"`) and uses its toolchain settings. A file of an
  installed toolchain's standard library (where go to definition takes you) is served by
  that toolchain's own `wiz lsp`, rooted at its `lib/`: one server per toolchain, the
  same version as the files. Diagnostics,
  hover, go to definition, completion and code actions are the ones Neovim's LSP client
  already provides.
* **unicode input like Lean's**: `\lam` → `λ`, `\r` → `→`, `\forall` → `∀`, …
* **an infoview**: a split that follows the cursor and shows the tactic state and the
  expected type there, with subterms you can inspect, and what else is there: a use of
  syntax and what it expands to, an import, the instances found, the command's
  declarations, `#check`/`#eval` output.

The protocol behind the infoview is in `wiz-notes/infoview-protocol.md`; the stage
notes are in `docs/stages/11-tooling.md` (11p).

## Installing

`wiz` must be on `PATH` (or set `lsp.cmd`), and `grail` too for grail packages (or set
`lsp.grail.cmd`), e.g. from `nix profile install github:wiz-pl/wiz`, tower's
shims, or a checkout's `.lake/build/bin`. Without `grail`, the plugin warns once and
starts `wiz lsp`.

**Try it with Nix**, without touching your configuration (Neovim with only this plugin,
and the packaged `wiz` on `PATH`):

```sh
nix run github:wiz-pl/wiz#nvim-wiz -- examples/tactics.wiz
```

(The Cachix cache of docs/building.md saves building wiz.)

**lazy.nvim** (the plugin is in a subdirectory of the repository):

```lua
{
  'wiz-pl/wiz',
  ft = 'wiz',
  config = function(plugin)
    vim.opt.rtp:append(plugin.dir .. '/editors/nvim')
    require('wiz').setup {}
    -- lazy loaded on `ft = 'wiz'`: the buffer that triggered it needs its ftplugin
    vim.cmd 'doautocmd FileType wiz'
  end,
  init = function()
    vim.filetype.add { extension = { wiz = 'wiz' } }
  end,
}
```

Or with a local checkout: `{ dir = '/path/to/wiz/editors/nvim', opts = {} }`.

**packer.nvim**:

```lua
use { 'wiz-pl/wiz', rtp = 'editors/nvim', config = function() require('wiz').setup {} end }
```

**Nix** (home-manager or a NixOS Neovim): the flake's `packages.<system>.wiz-nvim` is a
`vimUtils.buildVimPlugin`, so it goes wherever your other plugins go:

```nix
programs.neovim.plugins = [ inputs.wiz.packages.${pkgs.system}.wiz-nvim ];
home.packages = [ inputs.wiz.packages.${pkgs.system}.wiz ];
```

**Without a plugin manager**: `vim.opt.rtp:append '/path/to/wiz/editors/nvim'`.

`setup` is optional (the defaults apply without it; `vim.g.wiz_config = { ... }` works
too). To start the server yourself with Neovim 0.11's `vim.lsp.enable 'wiz'` (the plugin
ships `lsp/wiz.lua`), set `lsp = { enable = false }` so the plugin doesn't start a second
one.

## Configuration

```lua
require('wiz').setup {
  lsp = {
    enable = true,
    cmd = { 'wiz', 'lsp' },            -- e.g. { 'wiz', '-I', 'src', 'lsp' }
    grail = {                          -- in a directory with a grail.wiz:
      enable = true,                   --   start `grail lsp -C ROOT` instead of `cmd`
      cmd = { 'grail', 'lsp' },
    },
    toolchains = true,                 -- a toolchain's lib/ file: that toolchain's wiz lsp
    root_markers = { 'grail.wiz', 'wiz-toolchain', 'lakefile.toml', '.git' },
    on_attach = nil,                   -- function(client, bufnr)
    capabilities = nil,                -- merged into the defaults
    inlay_hints = false,               -- show binder types inline (0.10+)
    completion = 'auto',               -- Neovim's own LSP completion (0.11+), after `.` and on
                                       --   <C-Space>: true | false | 'auto' (off with nvim-cmp/blink.cmp)
    folding = false,                   -- fold with the server's ranges (0.11+)
  },
  abbreviations = {
    enable = true,
    leader = '\\',                     -- one character
    extra = {},                        -- { ok = '✓' }: your own, they win
  },
  infoview = {
    autoopen = true,                   -- open with the first Wiz buffer
    position = 'right',                -- 'left' | 'top' | 'bottom'
    width = 50, height = 15,
    debounce = 100,                    -- ms after the cursor stops
  },
  mappings = true,                     -- the keymaps below
}
```

## Commands and keymaps

| command | |
|---|---|
| `:WizInfoviewToggle`, `:WizInfoviewOpen`, `:WizInfoviewClose` | the infoview window |
| `:WizInfoviewRefresh` | ask the server again |
| `:WizInfoviewBrowser` | open the infoview in a browser (`vim.ui.open`): the buffer's `wiz lsp` starts listening on a WebSocket on 127.0.0.1 and serves the web infoview's page on the same port; the page follows this editor's cursor. Needs the page built: a release toolchain has it (`share/wiz/web`), in a checkout run `web/build.sh` |
| `:WizAbbrev [x]` | how to type `x` (`:WizAbbrev λ` → `\lam \la \fun …`), what an abbreviation types (`:WizAbbrev lam`), or with no argument how to type the character under the cursor |
| `:WizAbbrevList` | every abbreviation, in a scratch buffer |
| `:WizLspRestart` | restart the language server (`wiz lsp` or `grail lsp`) |

In Wiz buffers (normal mode): `<LocalLeader>i` toggles the infoview, `<LocalLeader>r`
refreshes it, `<LocalLeader>b` is `:WizInfoviewBrowser`, `<LocalLeader>\` is
`:WizAbbrev` (each with a `desc`, which which-key shows). The usual LSP keymaps (`K` hover,
`gd`, `grn`, `gra`, `]d`, …) are Neovim's own.

What the server offers, and Neovim's keys for it:

| | |
|---|---|
| inlay hints (`lsp.inlay_hints`, or `:lua vim.lsp.inlay_hint.enable()`) | `: T` after a `fun`/`let` binder written without a type |
| semantic tokens (on by default) | the keywords of the file's own syntax and of keyword-scoped DSLs, as `@lsp.type.keyword` |
| completion (`lsp.completion`: pops up after `.`, `<C-Space>` in insert mode; else `<C-x><C-o>` or your completion plugin) | after `x.`: the fields of `x`'s type and the functions of its namespace (`p.norm` for `Point.norm p`); after `Nat.`: the names in `Nat`; where a term goes: the locals (with their types), then the globals whose type ends in the expected one; tactic names inside `by`, command keywords in column 0, a keyword-scoped DSL's keywords inside it; module names after `import` |
| code actions (`gra`) | did you mean (an unknown identifier), add missing cases, add a type ascription, fill a hole `_`/`?x` from its expected type (a constructor `(.c ?x ?y)`, an anonymous constructor `⟨?px, ?py⟩`, `fun x => ?body`) |
| signature help (`<C-s>` in insert mode) | the binders of the function being applied, the next explicit one highlighted |
| references (`grr`), rename (`grn`) | a global's uses in the open files and the package's modules; a local's in its declaration. Rename refuses the toolchain's library |
| outline (`gO`), workspace symbols (`:lua vim.lsp.buf.workspace_symbol()`) | the file's declarations (fields and constructors as children); every declaration of the open files and their imports |
| folding (`lsp.folding`) | commands, `by` blocks, `match`es, block comments |

In the infoview: `K` or `<CR>` shows what the subterm under the cursor is (its text,
type, kind and, for a constant, where it is declared: `wiz/subtermInfo`); moving the
cursor highlights that subterm; `gd` jumps to the constant's declaration (or, on a
syntax, expansion or import line, to the `syntax` command, the macro rule or the
module); `r` refreshes; `q` closes.

## The infoview

```
Goals.wiz:4:9
Tactic state
1 goal
n : Nat
⊢ Bool → Nat

Expected type
⊢ Nat → Bool → Nat
```

It shows the state at the cursor of the last Wiz window you were in: the goals inside a
`by` block (`wiz/interactiveGoals`), the expected type of the term at the cursor
(`wiz/interactiveTermGoal`; on a binder or pattern variable, its type in its context),
and the rest (`wiz/interactiveInfo`: sections Syntax, Import, Instances, Declarations,
Messages), after a short debounce, and again after each edit (on the
server's `wiz/elaborated`). The terms are tagged text, coloured by kind:
`WizInfoviewConst`, `WizInfoviewVar`, `WizInfoviewSort`, `WizInfoviewLit`, with
`WizInfoviewTitle`, `WizInfoviewHypName`, `WizInfoviewTurnstile`, `WizInfoviewCase`,
`WizInfoviewSelection` (the subterm under the cursor); all are `default` links, so a
colour scheme can override them.

## Unicode input

Type the leader `\` and an abbreviation; it is replaced as soon as the next character
can't continue any abbreviation (a space or most punctuation, which is then typed as
usual), or as soon as it is complete and nothing longer starts with it (`\lambda`), or on
`<Tab>` (swallowed), `<CR>`, or leaving insert mode. While you type it, it is underlined
(`WizAbbreviationMark`). `\\` types a backslash. `\r\x` is two abbreviations, `→×`.
Text that isn't an abbreviation stays as typed; the longest abbreviation that starts it
wins (`\lamb` → `λb`).

The table is Lean's (`data/lean-abbreviations.json`, from vscode-lean4, Apache-2.0: see
`data/LICENSE.lean-abbreviations`), so anything you type in Lean works here, plus Wiz's
additions (`lua/wiz/abbreviations_extra.lua`). `:WizAbbrevList` shows all of them. The
ones Wiz code uses:

| type | get | | type | get | | type | get |
|---|---|---|---|---|---|---|---|
| `\r` `\to` `\->` | → | | `\l` `\<-` | ← | | `\lr` `\iff` | ↔ |
| `\=>` | ⇒ | | `\l=` | ⇐ | | `\-->` | ⟶ |
| `\lam` `\fun` | λ | | `\forall` `\all` | ∀ | | `\ex` | ∃ |
| `\Pi` `\P` | Π | | `\Sigma` `\S` | Σ | | `\x` `\times` | × |
| `\==` | ≡ | | `\==n` | ≢ | | `\ne` | ≠ |
| `\le` | ≤ | | `\ge` | ≥ | | `\|-` | ⊢ |
| `\-\|` | ⊣ | | `\<` `\>` | ⟨ ⟩ | | `\[[` `\]]` | ⟦ ⟧ |
| `\.` `\cdot` | · | | `\o` `\circ` | ∘ | | `\mapsto` | ↦ |
| `\and` | ∧ | | `\or` | ∨ | | `\not` | ¬ |
| `\in` | ∈ | | `\top` `\bot` | ⊤ ⊥ | | `\u` `\d` | ↑ ↓ |
| `\-1` | ⁻¹ | | `\0` … `\9` | ₀ … ₉ | | `\_n` `\_i` `\^k` | ₙ ᵢ ᵏ |
| `\infty` | ∞ | | `\N` `\Z` | ℕ ℤ | | `\ell` | ℓ |
| `\++` | ⧺ | | `\done` | ✅ | | `\cross` | ✗ |
| `\t` | ▸ | | `\ldots` | … | | `\o+` `\ox` | ⊕ ⊗ |

Greek: `\a` α, `\b` β, `\g` γ, `\de` δ, `\e` ε, `\z` ζ, `\h` η, `\q` θ, `\io` ι, `\k`
κ, `\la` λ, `\m` μ, `\nu` ν, `\j` ξ, `\pi` π, `\rh` ρ, `\s` σ, `\ta` τ, `\y` υ, `\f`
φ, `\c` χ, `\ps` ψ, `\w` ω; capitals `\G` Γ, `\D` Δ, `\Theta` Θ, `\L` Λ, `\Xi` Ξ, `\Pi`
Π, `\S` Σ, `\Phi` Φ, `\Psi` Ψ, `\Omega` Ω; any letter with `\G` (`\Gl` λ, `\GL` Λ).
Lean gives most single letters a meaning that isn't Greek (`\l` ←, `\r` →, `\x` ×,
`\t` ▸, `\o` ∘, `\d` ↓, `\u` ↑, `\v` ∨, `\i` ∩, `\p` Π); those stay. The nine letters
Lean leaves free are Wiz's Greek letters, after the Greek keyboard where it has them:
`\f` φ, `\h` η, `\j` ξ, `\k` κ, `\q` θ, `\s` σ, `\w` ω, `\y` υ, `\z` ζ. `\hat` and `\vec`
are combining accents (`x\hat` → x̂).

## Tests and feature parity

```sh
editors/nvim/tests/run.sh          # or: lake test -- '=nvim'
```

Headless Neovim with this plugin and the real `wiz lsp` (`WIZ` and `GRAIL` pick the
executables; the defaults are this checkout's `.lake/build/bin/{wiz,grail}`, then `wiz`
and `grail` on `PATH`; `WIZ_LIB` is the standard library). Without `nvim` on `PATH` the
script is skipped. A case may report a **gap** (`○`): a feature this toolchain or the
plugin does not have yet. Gaps are listed in the output and do not fail the run. Use a
`wiz` built from this checkout (or a matching toolchain): an old binary may panic while
serving a newer `lib/`, which fails the installed-toolchain case.

| feature | status | what the suite covers |
|---|---|---|
| LSP start and root detection | ✅ | `wiz lsp`, `grail lsp -C ROOT` in a package, an installed toolchain's own `wiz lsp`, one client per toolchain, `lsp.enable = false`, `lsp.toolchains = false`, the nearest root marker (`grail.wiz`, `wiz-toolchain`, `lakefile.toml`, `.git`) and the file's own directory |
| diagnostics | ✅ | `textDocument/publishDiagnostics` (source, severity, range, message) and that an edit clears them |
| hover | ✅ | a global's type and doc comment, and a local's type |
| completion | ✅ | names after a namespace dot (`Nat.` → `Nat.add`), their kind, insertion and doc |
| infoview: goals and expected type | ✅ | the tactic state after `intro n`, the expected type of an argument, the goal after an edit |
| infoview: info sections | ✅ | syntax and its expansion, an import and its file, declarations, `trace_state` messages, “No goals” |
| infoview: subterms | ✅ | tagged text highlighted by kind, `K` (`wiz/subtermInfo`), `gd` to a declaration or macro rule |
| infoview: window | ✅ | autoopen, toggle, browser (`wiz/browserInfoview` plus the WebSocket handshake) |
| term-aware requests | ✅ | `wiz/interactiveTermGoal` and `wiz/plainTermGoal` directly, `wiz/subtermInfo` through the infoview |
| unicode input | ✅ | expansion through real insert mode (also one key at a time), longest prefix, punctuation, `<Tab>`/`<CR>`/insert-leave, `$CURSOR` abbreviations, combining accents, `abbreviations.extra`, a custom leader, `:WizAbbrev`, `:WizAbbrevList`, every non-ASCII symbol in `lib/*.wiz` |
| hooks | ✅ | `lsp.on_attach(client, buf)`, `lsp.capabilities` merging, `wiz/elaborated` registration |
| infoview: instances | ◐ | the server's `instance` info items are not in a fixture yet; the section is rendered by `infoview.lua` |
| inlay hints, folding, completion autotrigger | ◐ | the options are documented; the suite checks the attach hook, not their visual effect |
| tactic widgets (11af) | ✗ | this server sends no `widgets` in `wiz/interactiveGoals`, and the Neovim infoview reads only goals, messages and items |
| term-aware extension hook (11ae follow-up) | ✗ | no `wiz/term*` method beyond the term-goal/subterm requests, and no editor hook for one |
| `wiz fmt` | ✗ | this toolchain's CLI has no `fmt` subcommand (the formatter is 11aa on another branch) |
| `wiz lint` | ✗ | this toolchain's CLI has no `lint` subcommand (ward/11ad is on another branch) |
| fmt/lint editor commands | ✗ | no `:WizFmt`, `:WizLint` or format-on-save in the plugin |

The gap rows are probed by the suite (they are reported with the reason and the usage
text); when the server or CLI grows the feature, the probes exercise it and the matrix
row can be updated.

## Credits

The design follows [lean.nvim](https://github.com/Julian/lean.nvim) (MIT) and Lean's
VS Code extension; the code is this plugin's own. The abbreviation table is
vscode-lean4's (Apache-2.0).

## Toolchain files

An installed toolchain (tower's `~/.tower/toolchains/NAME`, the Nix package, a release
tarball) is recognised by its layout: `share/wiz/TOOLCHAIN` (a marker every installation
writes; older ones have `share/wiz/REVISION`), `share/wiz/lib/Prelude.wiz` and
`share/wiz/.lake/build/bin/wiz`. A file under its `share/wiz/lib/` gets a client rooted at
that directory whose command is the toolchain's `bin/wiz lsp` (else the binary itself),
whatever `lsp.cmd` says: a `wiz` on `PATH` may be a tower shim that picks a toolchain by
the server's directory, which for a library file is not the project's. Set
`lsp.toolchains = false` to treat such files like any other.
