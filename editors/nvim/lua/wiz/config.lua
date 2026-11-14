-- wiz.nvim configuration: the defaults, merged with `require('wiz').setup(opts)` or
-- `vim.g.wiz_config` (whichever comes first; setup wins over the global).
local M = {}

M.defaults = {
  lsp = {
    -- Start `wiz lsp` for every wiz buffer. Turn this off if you start the server
    -- yourself (e.g. `vim.lsp.enable 'wiz'` with this plugin's lsp/wiz.lua).
    enable = true,
    cmd = { 'wiz', 'lsp' },
    -- In a grail package (the root has a grail.wiz), start `grail lsp` instead: the
    -- server then finds the package's modules (its lib targets' roots and its
    -- dependencies') and uses its toolchain settings. `cmd` above is for other files.
    grail = {
      enable = true,
      cmd = { 'grail', 'lsp' },
    },
    -- A file in an installed toolchain's standard library (go to definition opens them)
    -- is served by that toolchain's own `wiz lsp`, one server per toolchain.
    toolchains = true,
    root_markers = { 'grail.wiz', 'wiz-toolchain', 'lakefile.toml', '.git' },
    on_attach = nil, -- function(client, bufnr)
    capabilities = nil, -- merged into the client's capabilities
    -- Show the types of binders written without one (`fun x => …`) inline (0.10+).
    inlay_hints = false,
    -- Neovim's own completion from the server (0.11+, `vim.lsp.completion`), popping up
    -- as you type: true, false, or 'auto' (on unless nvim-cmp or blink.cmp is loaded).
    completion = 'auto',
    -- Fold with the server's folding ranges (commands, `by` blocks, comments) in the
    -- windows showing a Wiz buffer (0.11+, `vim.lsp.foldexpr`; all folds start open).
    folding = false,
  },
  abbreviations = {
    enable = true,
    -- A single character that begins an abbreviation (`\lam` → λ).
    leader = '\\',
    -- Extra abbreviations, without the leader: { ['ok'] = '✓' }. They win over the
    -- built-in ones.
    extra = {},
  },
  infoview = {
    -- Open the infoview when the first wiz buffer is opened.
    autoopen = true,
    -- 'right' | 'left' | 'top' | 'bottom'
    position = 'right',
    width = 50,
    height = 15,
    -- Milliseconds to wait after the cursor stops before asking the server.
    debounce = 100,
  },
  -- Set the default buffer-local keymaps (see the README).
  mappings = true,
}

local current = nil

function M.set(opts)
  current = vim.tbl_deep_extend('force', vim.deepcopy(M.defaults), vim.g.wiz_config or {}, opts or {})
  return current
end

function M.get()
  return current or M.set()
end

return M
