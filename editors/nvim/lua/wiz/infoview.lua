-- The infoview: a split beside the editor that follows the cursor and shows the tactic
-- state (`wiz/interactiveGoals`), the expected type (`wiz/interactiveTermGoal`) and what
-- else is there (`wiz/interactiveInfo`: syntax and its expansion, an import, instances,
-- the command's declarations, messages) at it, as tagged text: every subterm is a range that knows its kind and its ref, so
-- `K` in the infoview asks the server what the subterm under the cursor is
-- (`wiz/subtermInfo`). Protocol: docs/design/infoview-protocol.md.
local config = require 'wiz.config'
local lsp = require 'wiz.lsp'

local M = {}

local ns = vim.api.nvim_create_namespace 'wiz.infoview'
local ns_sel = vim.api.nvim_create_namespace 'wiz.infoview.selection'

-- One infoview (shared by every tab). `M.state` is public for tests.
M.state = {
  buf = nil, -- the infoview buffer
  src = nil, -- { buf, uri, position } the infoview shows
  session = nil,
  tags = {}, -- { srow, scol, erow, ecol, ref, kind, name, depth } (0-based, end exclusive)
  links = {}, -- { srow, erow, location } (rows of an info item with a place to go to)
  tick = 0,
  pending = 0, -- requests in flight
  subterm = nil, -- the last wiz/subtermInfo result
}
local S = M.state

local kind_hl = {
  const = 'WizInfoviewConst',
  var = 'WizInfoviewVar',
  sort = 'WizInfoviewSort',
  lit = 'WizInfoviewLit',
  data = 'WizInfoviewConst',
}

local function set_highlights()
  local hl = function(name, link)
    vim.api.nvim_set_hl(0, name, { default = true, link = link })
  end
  hl('WizInfoviewTitle', 'Title')
  hl('WizInfoviewTurnstile', 'Operator')
  hl('WizInfoviewHypName', 'Identifier')
  hl('WizInfoviewCase', 'Label')
  hl('WizInfoviewConst', 'Function')
  hl('WizInfoviewVar', 'Identifier')
  hl('WizInfoviewSort', 'Type')
  hl('WizInfoviewLit', 'Number')
  hl('WizInfoviewNoGoals', 'DiagnosticOk')
  hl('WizInfoviewMuted', 'Comment')
  hl('WizInfoviewSelection', 'Visual')
end

------------------------------------------------------------------------------
-- Rendering tagged text into lines + highlight ranges.

local Builder = {}
Builder.__index = Builder

function Builder.new()
  return setmetatable({ lines = { '' }, hls = {}, tags = {}, links = {} }, Builder)
end

function Builder:pos()
  return #self.lines - 1, #self.lines[#self.lines]
end

-- Append `s` (may contain newlines), highlighted with `hl` if given.
function Builder:text(s, hl)
  local parts = vim.split(s, '\n', { plain = true })
  for i, part in ipairs(parts) do
    if i > 1 then
      table.insert(self.lines, '')
    end
    local row, col = self:pos()
    self.lines[#self.lines] = self.lines[#self.lines] .. part
    if hl and #part > 0 then
      table.insert(self.hls, { row, col, row, col + #part, hl })
    end
  end
end

function Builder:newline()
  table.insert(self.lines, '')
end

-- Tagged text (protocol §2).
function Builder:tagged(tt, depth)
  depth = depth or 0
  if type(tt) ~= 'table' then
    return
  end
  if tt.text ~= nil then
    self:text(tt.text)
  elseif tt.append ~= nil then
    for _, t in ipairs(tt.append) do
      self:tagged(t, depth)
    end
  elseif tt.tag ~= nil then
    local info, body = tt.tag[1] or {}, tt.tag[2]
    local srow, scol = self:pos()
    self:tagged(body, depth + 1)
    local erow, ecol = self:pos()
    table.insert(self.tags, {
      srow = srow,
      scol = scol,
      erow = erow,
      ecol = ecol,
      ref = info.ref,
      kind = info.kind,
      name = info.name,
      depth = depth,
    })
    if kind_hl[info.kind] then
      table.insert(self.hls, { srow, scol, erow, ecol, kind_hl[info.kind], depth })
    end
  end
end

--- Tagged text, flattened to a string (the plain printing).
function M.flatten(tt)
  local b = Builder.new()
  b:tagged(tt)
  return table.concat(b.lines, '\n')
end

function Builder:goal(g)
  if g.userName and g.userName ~= vim.NIL and g.userName ~= '' then
    self:text('case ' .. g.userName, 'WizInfoviewCase')
    self:newline()
  end
  for _, h in ipairs(g.hyps or {}) do
    self:text(table.concat(h.names or {}, ' '), 'WizInfoviewHypName')
    self:text ' : '
    self:tagged(h.type)
    if h.val and h.val ~= vim.NIL then
      self:text ' := '
      self:tagged(h.val)
    end
    self:newline()
  end
  local prefix = (g.goalPrefix and g.goalPrefix ~= vim.NIL) and g.goalPrefix or '⊢ '
  self:text(prefix, 'WizInfoviewTurnstile')
  self:tagged(g.type)
end

local item_titles = {
  syntax = 'Syntax',
  expansion = 'Syntax',
  import = 'Import',
  instance = 'Instances',
  declaration = 'Declarations',
  widget = 'Widgets',
  message = 'Messages',
}

local function present(x)
  return x ~= nil and x ~= vim.NIL
end

--- One item of wiz/interactiveInfo.
function Builder:item(it)
  local srow = self:pos()
  if it.kind == 'widget' then
    -- A terminal cannot draw the SVG; name it and point at the browser infoview.
    self:text(it.title or 'widget', 'WizInfoviewHypName')
    self:text(' (open the browser infoview to draw it)', 'WizInfoviewMuted')
  elseif it.kind == 'declaration' then
    self:text(it.title or '', 'WizInfoviewHypName')
    if present(it.type) then
      self:text ' : '
      self:tagged(it.type)
    end
  elseif it.kind == 'instance' then
    self:text((present(it.text) and it.text or '?') .. ' : ', 'WizInfoviewHypName')
    if present(it.type) then
      self:tagged(it.type)
    end
  else
    self:text(it.title or '', it.kind == 'message' and 'WizInfoviewMuted' or nil)
    if present(it.text) then
      for _, line in ipairs(vim.split(it.text, '\n', { plain = true })) do
        self:newline()
        self:text('  ' .. line)
      end
    end
  end
  local erow = self:pos()
  if present(it.location) and it.location.uri then
    table.insert(self.links, { srow = srow, erow = erow, location = it.location })
  end
  self:newline()
end

--- Lines, highlights and tags for a state: `goals` (a wiz/interactiveGoals result or
--- nil), `term` (a wiz/interactiveTermGoal result or nil) and `info` (a
--- wiz/interactiveInfo result or nil).
function M.layout(src, goals, term, err, info)
  local b = Builder.new()
  if src then
    local name = vim.fn.fnamemodify(vim.uri_to_fname(src.uri), ':t')
    b:text(('%s:%d:%d'):format(name, src.position.line + 1, src.position.character + 1), 'WizInfoviewMuted')
    b:newline()
  end
  if err then
    b:text('Error: ' .. err, 'ErrorMsg')
    return b
  end
  if goals then
    b:text('Tactic state', 'WizInfoviewTitle')
    b:newline()
    local gs = goals.goals or {}
    if #gs == 0 then
      b:text('No goals', 'WizInfoviewNoGoals')
      b:newline()
    else
      b:text(#gs == 1 and '1 goal' or (#gs .. ' goals'), 'WizInfoviewMuted')
      b:newline()
      for i, g in ipairs(gs) do
        if i > 1 then
          b:newline()
        end
        b:goal(g)
        b:newline()
      end
    end
  end
  -- the info messages (`trace`, `trace_state`) of the tactic the state belongs to
  local msgs = goals and goals.messages or {}
  if type(msgs) == 'table' and #msgs > 0 then
    b:newline()
    b:text('Messages', 'WizInfoviewTitle')
    b:newline()
    for i, m in ipairs(msgs) do
      if i > 1 then
        b:newline()
      end
      for _, line in ipairs(vim.split(m, '\n', { plain = true })) do
        b:text(line)
        b:newline()
      end
    end
  end
  if term and term.goal then
    if goals then
      b:newline()
    end
    b:text('Expected type', 'WizInfoviewTitle')
    b:newline()
    b:goal(term.goal)
    b:newline()
  end
  local items = info and info.items or {}
  if type(items) == 'table' then
    local section = nil
    for _, it in ipairs(items) do
      local title = item_titles[it.kind] or 'Info'
      if title ~= section then
        if goals or (term and term.goal) or section then
          b:newline()
        end
        b:text(title, 'WizInfoviewTitle')
        b:newline()
        section = title
      end
      b:item(it)
    end
  end
  if not goals and not (term and term.goal) and #items == 0 then
    b:text('No info.', 'WizInfoviewMuted')
  end
  if b.lines[#b.lines] == '' and #b.lines > 1 then
    table.remove(b.lines)
  end
  return b
end

------------------------------------------------------------------------------
-- The window.

local function ensure_buf()
  if S.buf and vim.api.nvim_buf_is_valid(S.buf) then
    return S.buf
  end
  local buf = vim.api.nvim_create_buf(false, true)
  vim.api.nvim_buf_set_name(buf, 'wiz://infoview')
  vim.bo[buf].buftype = 'nofile'
  vim.bo[buf].bufhidden = 'hide'
  vim.bo[buf].swapfile = false
  vim.bo[buf].modifiable = false
  vim.bo[buf].filetype = 'wizinfoview'
  S.buf = buf
  local map = function(lhs, fn, desc)
    vim.keymap.set('n', lhs, fn, { buffer = buf, nowait = true, silent = true, desc = desc })
  end
  if config.get().mappings then
    map('K', M.inspect, 'wiz.nvim: what is the subterm under the cursor')
    map('<CR>', M.inspect, 'wiz.nvim: what is the subterm under the cursor')
    map('gd', M.goto_definition, 'wiz.nvim: go to the definition of the constant under the cursor')
    map('q', M.close, 'wiz.nvim: close the infoview')
    map('r', M.refresh, 'wiz.nvim: refresh the infoview')
  end
  vim.api.nvim_create_autocmd('CursorMoved', {
    buffer = buf,
    callback = function()
      M.select_under_cursor()
    end,
  })
  return buf
end

function M.win()
  if not (S.buf and vim.api.nvim_buf_is_valid(S.buf)) then
    return nil
  end
  for _, w in ipairs(vim.api.nvim_tabpage_list_wins(0)) do
    if vim.api.nvim_win_get_buf(w) == S.buf then
      return w
    end
  end
  return nil
end

function M.is_open()
  return M.win() ~= nil
end

function M.open()
  M.closed_by_user = false
  if M.is_open() then
    return M.win()
  end
  set_highlights()
  local buf = ensure_buf()
  local cfg = config.get().infoview
  local prev = vim.api.nvim_get_current_win()
  local split = ({ right = 'botright vsplit', left = 'topleft vsplit', top = 'topleft split', bottom = 'botright split' })[cfg.position]
    or 'botright vsplit'
  vim.cmd(split)
  local win = vim.api.nvim_get_current_win()
  vim.api.nvim_win_set_buf(win, buf)
  if cfg.position == 'top' or cfg.position == 'bottom' then
    vim.api.nvim_win_set_height(win, cfg.height)
    vim.wo[win].winfixheight = true
  else
    vim.api.nvim_win_set_width(win, cfg.width)
    vim.wo[win].winfixwidth = true
  end
  for opt, v in pairs { number = false, relativenumber = false, signcolumn = 'no', wrap = true, linebreak = true, list = false, spell = false, cursorline = false, foldcolumn = '0' } do
    vim.wo[win][opt] = v
  end
  if vim.api.nvim_win_is_valid(prev) then
    vim.api.nvim_set_current_win(prev)
  end
  M.update_now()
  return win
end

function M.close()
  M.closed_by_user = true
  local win = M.win()
  if win then
    if #vim.api.nvim_tabpage_list_wins(0) == 1 then
      vim.cmd 'enew'
    else
      vim.api.nvim_win_close(win, true)
    end
  end
end

function M.toggle()
  if M.is_open() then
    M.close()
  else
    M.open()
  end
end

------------------------------------------------------------------------------
-- Drawing.

local function draw(b)
  local buf = ensure_buf()
  vim.bo[buf].modifiable = true
  vim.api.nvim_buf_set_lines(buf, 0, -1, false, b.lines)
  vim.bo[buf].modifiable = false
  vim.api.nvim_buf_clear_namespace(buf, ns, 0, -1)
  vim.api.nvim_buf_clear_namespace(buf, ns_sel, 0, -1)
  for _, h in ipairs(b.hls) do
    pcall(vim.api.nvim_buf_set_extmark, buf, ns, h[1], h[2], {
      end_row = h[3],
      end_col = h[4],
      hl_group = h[5],
      priority = 100 + (h[6] or 0),
    })
  end
  S.tags = b.tags
  S.links = b.links
end

--- The innermost tag at (row, col) of the infoview buffer (0-based), if any.
function M.tag_at(row, col)
  local best = nil
  for _, t in ipairs(S.tags) do
    local after_start = row > t.srow or (row == t.srow and col >= t.scol)
    local before_end = row < t.erow or (row == t.erow and col < t.ecol)
    if after_start and before_end and (not best or t.depth > best.depth) then
      best = t
    end
  end
  return best
end

function M.select_under_cursor()
  local win = M.win()
  if not win then
    return nil
  end
  local cur = vim.api.nvim_win_get_cursor(win)
  local t = M.tag_at(cur[1] - 1, cur[2])
  vim.api.nvim_buf_clear_namespace(S.buf, ns_sel, 0, -1)
  if t then
    vim.api.nvim_buf_set_extmark(S.buf, ns_sel, t.srow, t.scol, {
      end_row = t.erow,
      end_col = t.ecol,
      hl_group = 'WizInfoviewSelection',
      priority = 200,
    })
  end
  return t
end

------------------------------------------------------------------------------
-- Following the cursor.

local timer = nil

local function source_here()
  local win = vim.api.nvim_get_current_win()
  local buf = vim.api.nvim_win_get_buf(win)
  if vim.bo[buf].filetype ~= 'wiz' or not lsp.client(buf) then
    return nil
  end
  local params = lsp.position_params(win, buf)
  return { buf = buf, uri = params.textDocument.uri, position = params.position }
end

--- Ask the server for the state at `src` (default: the cursor) and draw it.
function M.update_now(src)
  src = src or source_here() or S.src
  if not src or not M.is_open() then
    return
  end
  if not vim.api.nvim_buf_is_valid(src.buf) then
    return
  end
  S.src = src
  S.tick = S.tick + 1
  local tick = S.tick
  local params = { textDocument = { uri = src.uri }, position = src.position }
  local results, errors, left = {}, {}, 3
  S.pending = S.pending + 1
  local function done()
    left = left - 1
    if left > 0 then
      return
    end
    S.pending = S.pending - 1
    if tick ~= S.tick then
      return -- a newer request superseded this one
    end
    local goals = results.goals ~= vim.NIL and results.goals or nil
    local term = results.term ~= vim.NIL and results.term or nil
    local info = results.info ~= vim.NIL and results.info or nil
    S.session = (goals and goals.session) or (term and term.session) or (info and info.session) or S.session
    local err = errors.goals or errors.term
    draw(M.layout(src, goals, term, (not goals and not term) and err or nil, info))
  end
  local function handler(key)
    return function(err, result)
      if err then
        errors[key] = err.message or vim.inspect(err)
      end
      results[key] = result
      vim.schedule(done)
    end
  end
  lsp.request(src.buf, 'wiz/interactiveGoals', params, handler 'goals')
  lsp.request(src.buf, 'wiz/interactiveTermGoal', params, handler 'term')
  -- (a server without it answers with an error, which is not shown)
  lsp.request(src.buf, 'wiz/interactiveInfo', params, handler 'info')
end

--- Debounced update (on cursor moves).
function M.update()
  if not M.is_open() then
    return
  end
  local src = source_here()
  if not src then
    return
  end
  if S.src and S.src.uri == src.uri and S.src.position.line == src.position.line
    and S.src.position.character == src.position.character then
    return
  end
  timer = timer or vim.uv.new_timer()
  timer:stop()
  timer:start(config.get().infoview.debounce, 0, vim.schedule_wrap(function()
    M.update_now(source_here())
  end))
end

function M.refresh()
  M.update_now(S.src and vim.api.nvim_buf_is_valid(S.src.buf) and S.src or nil)
end

function M.on_elaborated(result, _)
  if not M.is_open() or not S.src or not result then
    return
  end
  if result.uri == S.src.uri then
    vim.schedule(M.refresh)
  end
end

--- Has the infoview drawn the latest request? (for tests)
function M.idle()
  return S.pending == 0
end

--- The infoview's text (for tests and :WizInfoviewText).
function M.lines()
  if not (S.buf and vim.api.nvim_buf_is_valid(S.buf)) then
    return {}
  end
  return vim.api.nvim_buf_get_lines(S.buf, 0, -1, false)
end

------------------------------------------------------------------------------
-- Subterms.

local function subterm_request(tag, cb)
  if not (S.src and S.session and tag and tag.ref) then
    return
  end
  local params = { textDocument = { uri = S.src.uri }, session = S.session, ref = tag.ref }
  lsp.request(S.src.buf, 'wiz/subtermInfo', params, function(err, result)
    vim.schedule(function()
      if err then
        if err.code == -32801 then
          vim.notify('wiz.nvim: the document changed; refreshing the infoview', vim.log.levels.INFO)
          M.refresh()
        else
          vim.notify('wiz.nvim: ' .. (err.message or 'subtermInfo failed'), vim.log.levels.WARN)
        end
        return
      end
      S.subterm = result
      cb(result)
    end)
  end)
end

local function describe(info)
  local lines = {}
  local ty = info.type and info.type ~= vim.NIL and M.flatten(info.type) or nil
  local head = info.text or ''
  local typed = ty and (head .. ' : ' .. ty) or head
  vim.list_extend(lines, vim.split(typed, '\n', { plain = true }))
  local name = info.name ~= vim.NIL and info.name or nil
  table.insert(lines, '')
  table.insert(lines, ('-- %s%s'):format(info.kind or '?', name and (' ' .. name) or ''))
  local def = info.definition
  if def and def ~= vim.NIL and def.uri then
    table.insert(lines, ('-- defined in %s:%d'):format(vim.fn.fnamemodify(vim.uri_to_fname(def.uri), ':~:.'),
      def.range.start.line + 1))
  end
  return lines
end

--- `K` in the infoview: what the subterm under the cursor is, in a float.
function M.inspect()
  local t = M.select_under_cursor()
  if not t then
    vim.notify('wiz.nvim: no subterm under the cursor', vim.log.levels.INFO)
    return
  end
  subterm_request(t, function(info)
    vim.lsp.util.open_floating_preview(describe(info), 'wiz', { focus_id = 'wiz_subterm', border = 'rounded' })
  end)
end

local function show_location(loc)
  for _, w in ipairs(vim.api.nvim_tabpage_list_wins(0)) do
    if S.src and vim.api.nvim_win_get_buf(w) == S.src.buf then
      vim.api.nvim_set_current_win(w)
      break
    end
  end
  local client = lsp.client(S.src.buf)
  vim.lsp.util.show_document(loc, client and client.offset_encoding or 'utf-16', { focus = true })
end

--- The info item with a location at a row of the infoview (0-based), if any.
function M.link_at(row)
  for _, l in ipairs(S.links or {}) do
    if row >= l.srow and row <= l.erow then
      return l
    end
  end
  return nil
end

--- `gd` in the infoview: jump (in the source window) to where the constant under the
--- cursor is declared, or to where an info item's syntax, macro or module is.
function M.goto_definition()
  local t = M.select_under_cursor()
  if not t then
    local win = M.win()
    local l = win and M.link_at(vim.api.nvim_win_get_cursor(win)[1] - 1)
    if l and S.src then
      show_location(l.location)
    end
    return
  end
  subterm_request(t, function(info)
    local def = info.definition
    if not def or def == vim.NIL then
      vim.notify('wiz.nvim: no definition for ' .. (info.text or 'this subterm'), vim.log.levels.INFO)
      return
    end
    for _, w in ipairs(vim.api.nvim_tabpage_list_wins(0)) do
      if S.src and vim.api.nvim_win_get_buf(w) == S.src.buf then
        vim.api.nvim_set_current_win(w)
        break
      end
    end
    local client = lsp.client(S.src.buf)
    vim.lsp.util.show_document(def, client and client.offset_encoding or 'utf-16', { focus = true })
  end)
end

------------------------------------------------------------------------------
-- The infoview in a browser (11w): the buffer's own server listens on a WebSocket and
-- serves the web infoview's page on the same port (`wiz/browserInfoview`); the page
-- follows this editor's cursor.

--- Open the web infoview for `buf`'s server (default: the current buffer). The result
--- (`{ port, url, token, message? }`; #430: the url carries the token) is kept in `M.state.browser`, for tests.
function M.open_browser(buf)
  buf = buf or vim.api.nvim_get_current_buf()
  lsp.request(buf, 'wiz/browserInfoview', vim.empty_dict(), function(err, result)
    vim.schedule(function()
      if err then
        vim.notify('wiz.nvim: ' .. (err.message or 'wiz/browserInfoview failed'), vim.log.levels.WARN)
        return
      end
      S.browser = result
      if not result or result.url == nil or result.url == vim.NIL then
        vim.notify('wiz.nvim: ' .. ((result and result.message ~= vim.NIL and result.message) or 'no web infoview'),
          vim.log.levels.WARN)
        return
      end
      vim.ui.open(result.url)
      vim.notify('wiz.nvim: web infoview at ' .. result.url, vim.log.levels.INFO)
    end)
  end)
end

------------------------------------------------------------------------------

local attached_group = nil

--- Follow the cursor in `buf`.
function M.attach(buf)
  attached_group = attached_group or vim.api.nvim_create_augroup('wiz.infoview', { clear = true })
  vim.api.nvim_clear_autocmds { group = attached_group, buffer = buf }
  vim.api.nvim_create_autocmd({ 'CursorMoved', 'CursorMovedI', 'BufEnter' }, {
    group = attached_group,
    buffer = buf,
    callback = function()
      M.update()
    end,
  })
  vim.api.nvim_create_autocmd('LspAttach', {
    group = attached_group,
    buffer = buf,
    callback = function()
      if config.get().infoview.autoopen and not M.is_open() and not M.closed_by_user then
        M.open()
      else
        M.update()
      end
    end,
  })
end

return M
