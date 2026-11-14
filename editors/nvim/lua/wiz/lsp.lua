-- Starting `wiz lsp` and talking to it.
local config = require 'wiz.config'

local M = {}

local function on_elaborated(_, result, ctx)
  require('wiz.infoview').on_elaborated(result, ctx)
end

M.handlers = { ['wiz/elaborated'] = on_elaborated }

--- The client capabilities wiz.nvim asks for: the defaults, plus the
--- `wiz/elaborated` notification (the infoview refreshes on it).
function M.capabilities(extra)
  local caps = vim.lsp.protocol.make_client_capabilities()
  caps.experimental = vim.tbl_extend('force', caps.experimental or {}, { wizElaborated = true })
  return vim.tbl_deep_extend('force', caps, extra or {})
end

local function exists(p)
  return vim.uv.fs_stat(p) ~= nil
end

--- The installed toolchain whose standard library `path` lies in, if any: `share/wiz/`
--- of a toolchain (tower's, the Nix package, a release tarball) has the marker
--- `TOOLCHAIN` (older installations: `REVISION` or the binary in `.lake/build/bin/`),
--- its library in `lib/` and its binary in `.lake/build/bin/wiz`. Returns
--- `{ lib = <share/wiz/lib>, wiz = <the toolchain's bin/wiz, else its binary> }`.
function M.toolchain(path)
  if not path or path == '' then
    return nil
  end
  for dir in vim.fs.parents(path) do
    if vim.fs.basename(dir) == 'lib' then
      local share = vim.fs.dirname(dir)
      local bin = share .. '/.lake/build/bin/wiz'
      if exists(dir .. '/Prelude.wiz') and exists(bin)
          and (exists(share .. '/TOOLCHAIN') or exists(share .. '/REVISION')) then
        local wrapper = vim.fs.dirname(vim.fs.dirname(share)) .. '/bin/wiz'
        return { lib = dir, wiz = vim.fn.executable(wrapper) == 1 and wrapper or bin }
      end
    end
  end
  return nil
end

--- The project root of `buf`: a toolchain's library directory for a file of an
--- installed toolchain (it is served by that toolchain's own `wiz lsp`), else the
--- nearest directory with a root marker, else the file's own directory.
function M.root(buf)
  local tc = config.get().lsp.toolchains ~= false and M.toolchain(vim.api.nvim_buf_get_name(buf))
  if tc then
    return tc.lib
  end
  local markers = config.get().lsp.root_markers
  local root = vim.fs.root(buf, markers)
  if root then
    return root
  end
  local name = vim.api.nvim_buf_get_name(buf)
  return name ~= '' and vim.fs.dirname(name) or vim.uv.cwd()
end

--- The server command for a project root: `grail lsp -C ROOT` when the root is a grail
--- package (has a grail.wiz) and `lsp.grail.enable` is on, else `lsp.cmd`. If grail is
--- not executable, warns once and falls back to `lsp.cmd`.
function M.cmd(root)
  local cfg = config.get().lsp
  -- a toolchain's library: that toolchain's wiz (the same version serves its own files)
  local tc = root and M.toolchain(root .. '/Prelude.wiz')
  if cfg.toolchains ~= false and tc and tc.lib == root then
    return { tc.wiz, 'lsp' }
  end
  local g = cfg.grail or {}
  if g.enable ~= false and root and vim.uv.fs_stat(root .. '/grail.wiz') then
    local cmd = vim.deepcopy(g.cmd or { 'grail', 'lsp' })
    if vim.fn.executable(cmd[1]) == 1 then
      table.insert(cmd, '-C')
      table.insert(cmd, root)
      return cmd
    end
    vim.notify_once(('wiz.nvim: %s has a grail.wiz but %s is not on PATH; starting %s without the package\'s modules')
      :format(root, cmd[1], cfg.cmd[1]), vim.log.levels.WARN)
  end
  return cfg.cmd
end

--- Turn on Neovim's built-in completion for the client (`lsp.completion`), and
--- `lsp.folding`: fold with the server's ranges in the current window.
--- `lsp.inlay_hints`: show the server's inlay hints in the buffer.
function M.on_attach(client, buf)
  local cfg = config.get().lsp
  if cfg.folding and vim.lsp.foldexpr and vim.api.nvim_get_current_buf() == buf then
    vim.wo.foldmethod = 'expr'
    vim.wo.foldexpr = 'v:lua.vim.lsp.foldexpr()'
    vim.wo.foldlevel = 99
  end
  local want = cfg.completion
  if want == 'auto' then
    want = not (package.loaded['cmp'] or package.loaded['blink.cmp'])
  end
  if want and vim.lsp.completion and vim.lsp.completion.enable then
    vim.lsp.completion.enable(true, client.id, buf, { autotrigger = true })
    if config.get().mappings then
      vim.keymap.set('i', '<C-Space>', vim.lsp.completion.get,
        { buffer = buf, desc = 'wiz.nvim: complete (the language server)' })
    end
  end
  if cfg.inlay_hints and vim.lsp.inlay_hint then
    vim.lsp.inlay_hint.enable(true, { bufnr = buf })
  end
  if cfg.on_attach then
    cfg.on_attach(client, buf)
  end
end

--- A `vim.lsp.start` config for `buf`.
function M.client_config(buf)
  local cfg = config.get().lsp
  local root = M.root(buf)
  return {
    name = 'wiz',
    cmd = M.cmd(root),
    cmd_cwd = root,
    root_dir = root,
    capabilities = M.capabilities(cfg.capabilities),
    handlers = M.handlers,
    on_attach = M.on_attach,
  }
end

function M.start(buf)
  if not config.get().lsp.enable then
    return
  end
  local cc = M.client_config(buf)
  if vim.fn.executable(cc.cmd[1]) ~= 1 then
    vim.notify_once(('wiz.nvim: %s is not on PATH; no language server'):format(cc.cmd[1]), vim.log.levels.WARN)
    return
  end
  return vim.lsp.start(cc, { bufnr = buf })
end

--- The wiz client attached to `buf`, if any.
function M.client(buf)
  return vim.lsp.get_clients({ bufnr = buf, name = 'wiz' })[1]
end

--- Send `method` with `params` to the wiz client of `buf`; `handler(err, result)`.
function M.request(buf, method, params, handler)
  local client = M.client(buf)
  if not client then
    handler({ code = -1, message = 'no wiz language server for this buffer' }, nil)
    return
  end
  local cb = function(err, result)
    handler(err, result)
  end
  if vim.fn.has 'nvim-0.11' == 1 then
    client:request(method, params, cb, buf)
  else
    client.request(method, params, cb, buf)
  end
end

--- Position params for `win` (its cursor) in the client's encoding.
function M.position_params(win, buf)
  local client = M.client(buf)
  local enc = client and client.offset_encoding or 'utf-16'
  return vim.lsp.util.make_position_params(win, enc)
end

function M.restart()
  for _, client in ipairs(vim.lsp.get_clients { name = 'wiz' }) do
    client:stop()
  end
  vim.defer_fn(function()
    for _, buf in ipairs(vim.api.nvim_list_bufs()) do
      if vim.api.nvim_buf_is_loaded(buf) and vim.bo[buf].filetype == 'wiz' then
        M.start(buf)
      end
    end
  end, 500)
end

return M
