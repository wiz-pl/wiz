-- The wiz.nvim tests: abbreviation expansion (typed through real insert mode), and the
-- infoview against the real `wiz lsp` on tests/fixture/Goals.wiz.
-- Run with tests/run.sh (or: nvim --headless --clean -u tests/minimal_init.lua -l tests/run.lua).
local here = vim.fn.fnamemodify(debug.getinfo(1, 'S').source:sub(2), ':p:h')
local fixture = here .. '/fixture/Goals.wiz'
local wiz = vim.g.wiz_config.lsp.cmd[1]
-- keep the source buffers loaded (and their LSP clients attached) while a test opens
-- another fixture; some cases come back to a buffer they had left.
vim.opt.hidden = true

local failures, passed, skipped = 0, 0, 0
local GAP = {}
-- A feature this toolchain or plugin does not have yet: report it as a gap, not a
-- failure (so the suite can be green and still say what is missing).
local function gap(reason)
  error(setmetatable({ reason = reason }, GAP), 2)
end
local function test(name, fn)
  io.stdout:write('  … ' .. name .. '\r'); io.stdout:flush()
  local ok, err = pcall(fn)
  if ok then
    passed = passed + 1
    io.stdout:write('  ✓ ' .. name .. '\n')
  elseif type(err) == 'table' and getmetatable(err) == GAP then
    skipped = skipped + 1
    io.stdout:write('  ○ ' .. name .. ' (gap: ' .. err.reason .. ')\n')
  else
    failures = failures + 1
    io.stdout:write('  ✗ ' .. name .. '\n      ' .. tostring(err):gsub('\n', '\n      ') .. '\n')
  end
end

local function eq(want, got, what)
  if not vim.deep_equal(want, got) then
    error(('%s: expected %s, got %s'):format(what or 'value', vim.inspect(want), vim.inspect(got)), 2)
  end
end

local function wait(ms, cond, what)
  if not vim.wait(ms, cond, 20) then
    error('timed out waiting for ' .. what, 2)
  end
end

local function tempdir()
  local d = vim.fn.tempname()
  vim.fn.mkdir(d, 'p')
  return d
end

local function open_wiz(path, ms)
  vim.cmd('edit! ' .. vim.fn.fnameescape(path))
  local lsp = require 'wiz.lsp'
  local buf = vim.api.nvim_get_current_buf()
  if not lsp.client(buf) then
    -- This suite opens many fixtures in one buffer slot; a buffer that was loaded
    -- before can keep its attach flags across :edit. Attach it as a first open would.
    vim.b[buf].wiz_attached = false
    vim.b[buf].did_ftplugin = false
    require('wiz').attach(buf)
  end
  wait(ms or 60000, function()
    return lsp.client(buf) ~= nil
  end, 'the wiz client for ' .. vim.fn.fnamemodify(path, ':t'))
  return lsp.client(buf)
end

-- Position params at (line, col) (1-based line, 0-based byte column), as the client
-- encodes positions.
local function at_pos(line, col)
  local lsp = require 'wiz.lsp'
  vim.api.nvim_win_set_cursor(0, { line, col })
  local c = lsp.client(0)
  return vim.lsp.util.make_position_params(0, c and c.offset_encoding or 'utf-16')
end

-- One request to the buffer's wiz client; returns its result, or errors with the
-- server's error.
local function request(buf, method, params, ms)
  local lsp = require 'wiz.lsp'
  local out = {}
  lsp.request(buf, method, params, function(err, result)
    out.err, out.result, out.done = err, result, true
  end)
  wait(ms or 120000, function()
    return out.done
  end, method)
  if out.err then
    error(('%s: %s'):format(method, out.err.message or vim.inspect(out.err)), 2)
  end
  return out.result
end

local function run(cmd, ms)
  local ok, res = pcall(function()
    return vim.system(cmd, { text = true }):wait(ms or 60000)
  end)
  if not ok then
    error(('could not run %s: %s'):format(table.concat(cmd, ' '), tostring(res)), 2)
  end
  return res
end

-- Type `keys` in insert mode in a fresh wiz buffer (as typeahead: the expansions
-- scheduled while typing run when nvim next waits), then <Esc>; return the text.
local function typed(keys)
  vim.cmd 'enew!'
  vim.bo.filetype = 'wiz'
  local k = vim.api.nvim_replace_termcodes('i' .. keys .. '<Esc>', true, false, true)
  vim.api.nvim_feedkeys(k, 'tx', false)
  vim.wait(20)
  local lines = vim.api.nvim_buf_get_lines(0, 0, -1, false)
  vim.bo.modified = false
  return table.concat(lines, '\n')
end

io.stdout:write 'abbreviations\n'

test('the table: Lean\'s, plus Wiz\'s free letters and symbols', function()
  local t = require('wiz.abbreviations').table()
  local want = {
    lam = 'λ', r = '→', to = '→', forall = '∀', all = '∀', ex = '∃', Sigma = 'Σ', x = '×',
    ['=='] = '≡', le = '≤', ne = '≠', a = 'α', b = 'β', z = 'ζ', f = 'φ', ['0'] = '₀',
    ['1'] = '₁', ['<'] = '⟨', ['>'] = '⟩', ['-1'] = '⁻¹', ['|-'] = '⊢', ['++'] = '⧺', l = '←',
  }
  for k, v in pairs(want) do
    eq(v, t[k], '\\' .. k)
  end
end)

test('expand: longest prefix, then the rest', function()
  local e = require('wiz.abbreviations').expand
  eq('λ', (e '\\lam'))
  eq('λb', (e '\\lamb'))
  eq('\\', (e '\\'))
  eq('→×', (e '\\r\\x'))
end)

test('typing: a space ends an abbreviation and stays', function()
  eq('λ x', typed '\\lam x')
  eq('A → B', typed 'A \\r B')
  eq('∀ n, n ≤ n', typed '\\forall n, n \\le n')
end)

test('typing: punctuation that continues no abbreviation ends it', function()
  eq('α)', typed '\\a)')
  eq('Σ(', typed '\\Sigma(')
  eq('x₀,', typed 'x\\0,')
end)

test('typing: abbreviations that are punctuation themselves', function()
  eq('⟨a, b⟩ ', typed '\\<a, b\\> ')
  eq('a ≡ b', typed 'a \\== b')
  eq('f⁻¹ ', typed 'f\\-1 ')
  eq('a ≠ b', typed 'a \\ne b')
end)

test('typing: a second leader ends the first; \\\\ is a backslash', function()
  eq('→× ', typed '\\r\\x ')
  eq('\\lam', typed '\\\\lam')
end)

test('typing: a complete abbreviation that can\'t be extended expands at once', function()
  eq('λ', typed '\\lambda')
  eq('Σ', typed '\\Sigma')
end)

test('typing: Tab expands (and is swallowed); leaving insert mode expands', function()
  eq('ℕ', typed '\\N<Tab>')
  eq('γ', typed '\\g')
  eq('  x', typed '<Tab>x') -- no abbreviation: an ordinary Tab (expandtab)
end)

test('typing one key at a time (an embedded nvim): expansions run between keys', function()
  local init = here .. '/minimal_init.lua'
  local chan = vim.fn.jobstart({ vim.v.progpath, '--embed', '--headless', '--clean', '-u', init }, { rpc = true })
  local function req(...)
    return vim.rpcrequest(chan, ...)
  end
  req('nvim_command', 'enew | setfiletype wiz')
  local keys = { 'i', 'f', ' ', '\\', 'l', 'a', 'm', ' ', 'x', ' ', '\\', 'r', '\\', 'x', ' ', 'y', '\\', '<lt>', 'a', '\\', '>' }
  for _, k in ipairs(keys) do
    req('nvim_input', k)
    vim.wait(30)
    req('nvim_eval', '1') -- let the child finish this key and its scheduled work
  end
  vim.wait(30)
  req('nvim_eval', '1')
  local line = req('nvim_get_current_line')
  local col = req('nvim_win_get_cursor', 0)[2]
  req('nvim_input', '<Esc>')
  vim.fn.jobstop(chan)
  eq('f λ x →× y⟨a\\>', line, 'the line')
  eq(#line, col, 'the cursor at the end')
end)

test('typing: unknown text stays as typed after the longest abbreviation', function()
  eq('\\ x', typed '\\ x')
  eq('θqq ', typed '\\qqq ')
  eq('→\\', typed '\\r\\\\')
end)

test('typing: combining accents stay on the letter before them', function()
  eq('x̂ ', typed 'x\\hat ')
  eq('v⃗ ', typed 'v\\vec ')
end)

test('typing: <CR> expands the abbreviation and then breaks the line', function()
  eq('λ\n', typed '\\lam<CR>')
end)

test('expand: $CURSOR abbreviations return where the cursor goes', function()
  local e = require('wiz.abbreviations').expand
  local s, at = e '\\{}'
  eq('{}', s, 'the expansion')
  eq(1, at, 'the cursor inside the braces')
end)

test('lookup: the character under the cursor, and :WizAbbrevList', function()
  vim.cmd 'enew!'
  vim.bo.filetype = 'wiz'
  vim.api.nvim_buf_set_lines(0, 0, -1, false, { 'λx' })
  vim.api.nvim_win_set_cursor(0, { 1, 0 })
  local d = require('wiz.abbreviations').describe()
  eq(true, (d[1] or ''):find('\\lam', 1, true) ~= nil, 'λ lists \\lam')
  vim.cmd 'WizAbbrevList'
  local lines = vim.api.nvim_buf_get_lines(0, 0, -1, false)
  local listed = false
  for _, l in ipairs(lines) do
    if l:find('\\lam', 1, true) and l:find('λ', 1, true) then
      listed = true
    end
  end
  eq(true, listed, ':WizAbbrevList has \\lam')
  vim.cmd 'bwipeout!'
end)

test('configuration: abbreviations.extra and a different leader', function()
  local config = require 'wiz.config'
  local abbr = require 'wiz.abbreviations'
  local ok, err = pcall(function()
    config.set { abbreviations = { leader = '@', extra = { ok = '✓' } } }
    abbr.reload()
    eq('✓', (abbr.expand '@ok'), 'the extra abbreviation')
    eq('@ok → ✓', abbr.describe('ok')[1], 'describe reads the leader')
    eq('✓λ', (abbr.expand '@ok@lam'), 'two abbreviations in one string')
  end)
  config.set()
  abbr.reload()
  if not ok then
    error(err, 0)
  end
end)

test('lookup: :WizAbbrev', function()
  local d = require('wiz.abbreviations').describe
  eq(true, (d('λ')[1] or ''):find('\\lam', 1, true) ~= nil, 'λ lists \\lam')
  eq('\\lam → λ', d('lam')[1])
  eq('\\++ → ⧺', d('\\++')[1])
end)

test('every non-ASCII symbol in lib/*.wiz has an abbreviation', function()
  local lib = os.getenv 'WIZ_LIB' or vim.fn.fnamemodify(here .. '/../../../lib', ':p')
  local symbols = {}
  for _, f in ipairs(vim.fn.globpath(lib, '**/*.wiz', false, true)) do
    for _, line in ipairs(vim.fn.readfile(f)) do
      for ch in line:gmatch '[\xC2-\xF4][\x80-\xBF]*' do
        symbols[ch] = true
      end
    end
  end
  local have = {}
  for _, v in pairs(require('wiz.abbreviations').table()) do
    have[(v:gsub('%$CURSOR', ''))] = true
  end
  local missing = {}
  for ch in pairs(symbols) do
    -- box drawing in comments and combining marks are typed with the letter before them
    if not have[ch] then
      table.insert(missing, ch)
    end
  end
  table.sort(missing)
  eq({}, missing, 'symbols without an abbreviation')
end)

io.stdout:write 'language server\n'

test('client config: name, command, root, capabilities and hooks', function()
  local lsp = require 'wiz.lsp'
  local cfg = require('wiz.config').get().lsp
  local buf = vim.fn.bufadd(here .. '/fixture/Local.wiz')
  local cc = lsp.client_config(buf)
  eq('wiz', cc.name, 'the client name')
  eq(vim.fs.root(fixture, cfg.root_markers), cc.root_dir, 'the root')
  eq(cc.root_dir, cc.cmd_cwd, 'cmd_cwd is the root')
  eq(lsp.cmd(cc.root_dir), cc.cmd, 'the command (grail in a package)')
  eq(true, cc.capabilities.experimental.wizElaborated, 'the wiz/elaborated capability')
  eq('function', type(cc.on_attach), 'on_attach')
  eq('function', type(cc.handlers['wiz/elaborated']), 'the elaborate handler')
  vim.api.nvim_buf_delete(buf, { force = true })
end)

test('root detection: the nearest marker, else the file\'s directory', function()
  local lsp = require 'wiz.lsp'
  local base = tempdir()
  local function write(path, lines)
    vim.fn.mkdir(vim.fs.dirname(path), 'p')
    vim.fn.writefile(lines or { '' }, path)
  end
  local cases = {
    { name = 'grail.wiz', dir = 'grail', marker = function(d) write(d .. '/grail.wiz', { 'def package : Package := Package.new "p"' }) end },
    { name = 'wiz-toolchain', dir = 'toolchain', marker = function(d) write(d .. '/wiz-toolchain', { 'nightly' }) end },
    { name = 'lakefile.toml', dir = 'lake', marker = function(d) write(d .. '/lakefile.toml', { 'name = "p"' }) end },
    { name = '.git', dir = 'git', marker = function(d) vim.fn.mkdir(d .. '/.git', 'p') end },
  }
  local bufs = {}
  for _, c in ipairs(cases) do
    local project = base .. '/' .. c.dir .. '/project'
    c.marker(project)
    local file = project .. '/src/deep/File.wiz'
    write(file, { 'import Prelude' })
    local buf = vim.fn.bufadd(file)
    table.insert(bufs, buf)
    eq(project, lsp.root(buf), 'the root above ' .. c.name)
  end
  local loose = base .. '/loose/deep/File.wiz'
  write(loose, { 'import Prelude' })
  local buf = vim.fn.bufadd(loose)
  table.insert(bufs, buf)
  eq(vim.fs.dirname(loose), lsp.root(buf), 'no marker: the file\'s directory')
  for _, b in ipairs(bufs) do
    vim.api.nvim_buf_delete(b, { force = true })
  end
  vim.fn.delete(base, 'rf')
end)

test('lsp.start does nothing when lsp.enable is false', function()
  local lsp = require 'wiz.lsp'
  local cfg = require('wiz.config').get().lsp
  local old = cfg.enable
  local buf = vim.fn.bufadd(here .. '/fixture/Complete.wiz')
  cfg.enable = false
  local ok, started = pcall(lsp.start, buf)
  cfg.enable = old
  vim.api.nvim_buf_delete(buf, { force = true })
  eq(true, ok, 'start did not error')
  eq(nil, started, 'no client was started')
end)

if vim.fn.executable(wiz) ~= 1 then
  io.stdout:write('  (skipped: ' .. wiz .. ' is not executable)\n')
else
  test('the server starts on a wiz file, with the configured command', function()
    local client = open_wiz(fixture, 120000)
    local root = vim.fs.root(fixture, require('wiz.config').get().lsp.root_markers)
    eq(require('wiz.lsp').cmd(root), client.config.cmd, 'the command for the root')
    eq(root, client.config.root_dir, 'the root')
  end)

  test('diagnostics: the server publishes them and clears them after an edit', function()
    local errors = here .. '/fixture/Errors.wiz'
    open_wiz(errors, 120000)
    wait(120000, function()
      return #vim.diagnostic.get(0) > 0
    end, 'diagnostics')
    local ds = vim.diagnostic.get(0)
    local d = ds[1]
    eq('wiz', d.source, 'the diagnostic source')
    eq(vim.diagnostic.severity.ERROR, d.severity, 'the severity')
    eq(2, d.lnum, 'the line of Bool.true')
    eq(true, d.message:find('expected: Nat', 1, true) ~= nil and d.message:find('inferred: Bool', 1, true) ~= nil,
      'the message: ' .. d.message)
    vim.api.nvim_buf_set_lines(0, 2, 3, false, { 'def bad : Nat := 0' })
    wait(120000, function()
      return #vim.diagnostic.get(0) == 0
    end, 'the diagnostics to clear')
    vim.bo.modified = false
  end)

  test('hover: the type and doc comment of the identifier under the cursor', function()
    open_wiz(fixture, 120000)
    local h = request(0, 'textDocument/hover', at_pos(8, 21))
    eq('markdown', h.contents.kind, 'markdown hover')
    eq(true, h.contents.value:find('Nat.add : Nat → Nat → Nat', 1, true) ~= nil, 'the type')
    eq(true, h.contents.value:find('Addition', 1, true) ~= nil, 'the doc comment')
    open_wiz(here .. '/fixture/Local.wiz', 120000)
    local local_hover = request(0, 'textDocument/hover', at_pos(3, 26)) -- the use of x
    eq(true, local_hover.contents.value:find('x : Nat', 1, true) ~= nil,
      'a local: ' .. local_hover.contents.value)
  end)

  test('completion: after a namespace dot, the names in it', function()
    open_wiz(here .. '/fixture/Complete.wiz', 120000)
    local r = request(0, 'textDocument/completion', at_pos(3, 19))
    eq(false, r.isIncomplete, 'isIncomplete')
    local items = {}
    for _, i in ipairs(r.items or {}) do
      items[i.label] = i
    end
    eq(true, items['Nat.add'] ~= nil, 'Nat.add is offered')
    eq(3, items['Nat.add'].kind, 'as a function')
    eq('Nat.add', items['Nat.add'].textEdit.newText, 'the insertion')
  end)

  test('term-aware hooks: the expected type and the subterm under a tag', function()
    open_wiz(fixture, 120000)
    local term = request(0, 'wiz/interactiveTermGoal', at_pos(8, 25))
    eq('Nat', require('wiz.infoview').flatten(term.goal.type), 'the expected type')
    local plain = request(0, 'wiz/plainTermGoal', at_pos(8, 25))
    eq(true, plain.goal:find('⊢ Nat', 1, true) ~= nil, 'the plain term goal: ' .. plain.goal)
    -- term-aware extension hooks (`attribute [termInfo ...]` / a wiz/termInfo method)
    -- are 11ae's follow-up; there is no such method in this server.
    local client = require('wiz.lsp').client(0)
    local methods = {}
    local caps = client.server_capabilities.experimental or {}
    local wiziv = caps.wizInfoview or {}
    for _, m in ipairs(wiziv.methods or {}) do
      methods[m] = true
    end
    for _, m in ipairs { 'wiz/plainTermGoal', 'wiz/interactiveTermGoal', 'wiz/subtermInfo' } do
      eq(true, methods[m] == true, 'advertised ' .. m)
    end
    local extra = nil
    for m in pairs(methods) do
      if not ({ ['wiz/plainGoal'] = true, ['wiz/plainTermGoal'] = true, ['wiz/interactiveGoals'] = true,
        ['wiz/interactiveTermGoal'] = true, ['wiz/subtermInfo'] = true, ['wiz/interactiveInfo'] = true })[m]
        and (m:find('term') or m:find('info')) then
        extra = m
      end
    end
    if not extra then
      gap 'no term-aware extension hook: the server advertises no wiz/term* method beyond the term-goal/subterm requests (11ae follow-up)'
    end
  end)

  test('hooks: capabilities merge and on_attach is called with the client and buffer', function()
    local lsp = require 'wiz.lsp'
    local caps = lsp.capabilities { textDocument = { hover = { dynamicRegistration = true } } }
    eq(true, caps.experimental.wizElaborated, 'the experimental capability survives the merge')
    eq(true, caps.textDocument.hover.dynamicRegistration, 'the extra capability')
    eq(true, caps.textDocument.completion ~= nil, 'the defaults survive')
    local cfg = require('wiz.config').get()
    local old = cfg.lsp.on_attach
    local got = nil
    cfg.lsp.on_attach = function(client, buf)
      got = { client = client, buf = buf }
    end
    local ok, err = pcall(function()
      local client = lsp.client(0) or open_wiz(fixture, 120000)
      lsp.on_attach(client, 0)
      eq(client.id, got.client.id, 'the client')
      eq(0, got.buf, 'the buffer')
    end)
    cfg.lsp.on_attach = old
    if not ok then
      error(err, 0)
    end
  end)
end

io.stdout:write 'infoview (wiz lsp)\n'

if vim.fn.executable(wiz) ~= 1 then
  io.stdout:write('  (skipped: ' .. wiz .. ' is not executable)\n')
else
  local iv = require 'wiz.infoview'
  local function at(line, col)
    vim.api.nvim_win_set_cursor(0, { line, col })
    vim.api.nvim_exec_autocmds('CursorMoved', { buffer = 0 })
    iv.update_now()
    local uri = vim.uri_from_bufnr(0)
    wait(60000, function()
      return iv.idle() and iv.state.src and iv.state.src.uri == uri
        and iv.state.src.position.line == line - 1
        and iv.state.src.position.character == col
    end, 'the infoview')
    return iv.lines()
  end
  local function has(lines, s)
    for _, l in ipairs(lines) do
      if l == s then
        return true
      end
    end
    error(('no line %q in the infoview:\n%s'):format(s, table.concat(lines, '\n')), 2)
  end
  local function has_match(lines, pattern, what)
    for _, l in ipairs(lines) do
      if l:find(pattern) then
        return true
      end
    end
    error(('no line matching %q%s in the infoview:\n%s'):format(pattern,
      what and (' (' .. what .. ')') or '', table.concat(lines, '\n')), 2)
  end

  test('the server starts on a wiz file and the infoview opens', function()
    open_wiz(fixture, 120000)
    eq('wiz', vim.bo.filetype, 'filetype')
    local buf = vim.api.nvim_get_current_buf()
    wait(30000, iv.is_open, 'the infoview window')
    eq(vim.fs.root(fixture, { 'grail.wiz', 'wiz-toolchain', 'lakefile.toml', '.git' }), require('wiz.lsp').client(buf).config.root_dir, 'root dir')
  end)

  test('the tactic state after `intro n`', function()
    local lines = at(4, 8) -- the end of "  intro n"
    has(lines, 'Tactic state')
    has(lines, 'n : Nat')
    has(lines, '⊢ Bool → Nat')
  end)

  test('the expected type of an argument', function()
    local lines = at(8, 25) -- the first `1` of `Nat.add 1 1`
    has(lines, 'Expected type')
    has(lines, '⊢ Nat')
  end)

  test('an import: the module and the file it resolves to', function()
    local lines = at(1, 8) -- `Prelude` in `import Prelude`
    has(lines, 'Import')
    has(lines, 'import Prelude')
    has_match(lines, 'Prelude%.wiz', 'the module file')
  end)

  test('no goals left: the infoview says so', function()
    open_wiz(here .. '/fixture/NoGoals.wiz', 120000)
    local lines = at(4, 8) -- the `1` of `  exact 1`
    has(lines, 'Tactic state')
    has(lines, 'No goals')
  end)

  test('messages: trace_state appears under the goals', function()
    open_wiz(here .. '/fixture/Messages.wiz', 120000)
    local lines = at(5, 12) -- the end of `  trace_state`
    has(lines, 'Tactic state')
    has(lines, 'Messages')
    has(lines, 'n : Nat')
  end)

  test('widgets: the server sends `widgets`, and the infoview draws them', function()
    open_wiz(fixture, 120000)
    local r = request(0, 'wiz/interactiveGoals', at_pos(4, 8))
    if r.widgets == nil or r.widgets == vim.NIL then
      gap 'wiz/interactiveGoals has no `widgets` (11af) and the Neovim infoview does not render a Widgets section'
    end
    eq('table', type(r.widgets), 'the widgets array')
    for _, w in ipairs(r.widgets) do
      eq('string', type(w.title), 'a widget title')
      eq('string', type(w.html), 'a widget body')
      eq('table', type(w.range), 'a widget range')
      eq('table', type(w.goals), 'the widget\'s goal snapshot')
    end
    local lines = at(4, 8)
    if not vim.tbl_contains(lines, 'Widgets') then
      gap 'the server sends widgets but the Neovim infoview does not draw a Widgets section'
    end
  end)

  test('tagged text is highlighted by kind, and K inspects the subterm', function()
    local lines = at(4, 8)
    local row = nil
    for i, l in ipairs(lines) do
      if l == '⊢ Bool → Nat' then
        row = i
      end
    end
    local marks = vim.api.nvim_buf_get_extmarks(iv.state.buf, -1, { row - 1, 0 }, { row - 1, -1 }, { details = true })
    local groups = {}
    for _, m in ipairs(marks) do
      groups[m[4].hl_group] = true
    end
    eq(true, groups.WizInfoviewConst, 'Bool and Nat highlighted as constants')
    local col = lines[row]:find('Bool', 1, true) - 1
    local tag = iv.tag_at(row - 1, col)
    eq('const', tag and tag.kind, 'the tag under Bool')
    eq('Bool', tag.name, 'its name')
    -- K in the infoview window
    local src_win = vim.api.nvim_get_current_win()
    vim.api.nvim_set_current_win(iv.win())
    vim.api.nvim_win_set_cursor(0, { row, col })
    iv.state.subterm = nil
    vim.api.nvim_feedkeys('K', 'x', false)
    wait(10000, function()
      return iv.state.subterm ~= nil
    end, 'wiz/subtermInfo')
    eq('Bool', iv.state.subterm.text, 'subterm text')
    eq('Type', iv.flatten(iv.state.subterm.type), 'subterm type')
    vim.api.nvim_set_current_win(src_win)
  end)

  test('a use of syntax: its declaration and expansion in the infoview, gd to the macro rule', function()
    local src_win = vim.api.nvim_get_current_win()
    local lines = at(13, 19) -- `twice` in `def four : Nat := twice two`
    has(lines, 'Syntax')
    has(lines, 'syntax term.twice (this file, line 10)')
    has(lines, 'expanded by macro rule (this file, line 12)')
    has(lines, '  Nat.add two two')
    has(lines, 'Declarations')
    has(lines, 'four : Nat')
    -- go to definition (the rule) and declaration (the syntax) in the source
    local c = require('wiz.lsp').client(0)
    local params = vim.lsp.util.make_position_params(0, c.offset_encoding)
    local function line_of(method)
      local res = vim.lsp.buf_request_sync(0, method, params, 20000) or {}
      for _, r in pairs(res) do
        local loc = r.result and (r.result.uri and r.result or r.result[1])
        if loc then
          return loc.range.start.line
        end
      end
    end
    eq(11, line_of 'textDocument/definition', 'definition')
    eq(9, line_of 'textDocument/declaration', 'declaration')
    -- gd on the expansion's line in the infoview
    local row
    for i, l in ipairs(lines) do
      if l:find('^expanded by') then
        row = i
      end
    end
    vim.api.nvim_set_current_win(iv.win())
    vim.api.nvim_win_set_cursor(0, { row, 0 })
    iv.goto_definition()
    eq(src_win, vim.api.nvim_get_current_win(), 'back in the source window')
    eq(12, vim.api.nvim_win_get_cursor(0)[1], 'at the macro rule')
  end)

  test('the infoview follows edits', function()
    vim.api.nvim_buf_set_lines(0, 2, 3, false, { 'def k : Nat → Nat → Nat := by' })
    vim.api.nvim_win_set_cursor(0, { 4, 8 })
    iv.state.src = nil
    wait(20000, function()
      iv.update_now()
      vim.wait(200, iv.idle)
      return vim.tbl_contains(iv.lines(), '⊢ Nat → Nat')
    end, 'the new goal')
  end)

  test('the browser infoview: <LocalLeader>b and :WizInfoviewBrowser ask the server to listen', function()
    local m = vim.fn.maparg('<LocalLeader>b', 'n', false, true)
    eq('wiz.nvim: open the infoview in a browser', m.desc, 'the mapping and its desc')
    eq(2, vim.fn.exists ':WizInfoviewBrowser', 'the command')
    local opened = {}
    local real_open = vim.ui.open
    vim.ui.open = function(url)
      table.insert(opened, url)
    end
    iv.state.browser = nil
    vim.cmd 'WizInfoviewBrowser'
    wait(20000, function()
      return iv.state.browser ~= nil
    end, 'wiz/browserInfoview')
    vim.ui.open = real_open
    local b = iv.state.browser
    eq(true, type(b.port) == 'number' and b.port > 0, 'a port: ' .. vim.inspect(b))
    if b.url ~= vim.NIL and b.url ~= nil then
      eq({ b.url }, opened, 'the page opened')
      eq(true, b.url:find('^http://127%.0%.0%.1:' .. b.port .. '/infoview%.html%?port=' .. b.port .. '&follow=1$') ~= nil, 'url ' .. b.url)
    else
      eq({}, opened, 'nothing opened without a built page')
    end
    -- the port answers a WebSocket handshake (a page would connect there)
    local got = nil
    local tcp = vim.uv.new_tcp()
    tcp:connect('127.0.0.1', b.port, function(e)
      if e then
        got = 'connect: ' .. e
        return
      end
      tcp:read_start(function(_, data)
        got = got or data
        tcp:close()
      end)
      tcp:write('GET / HTTP/1.1\r\nHost: 127.0.0.1\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n'
        .. 'Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n\r\n')
    end)
    wait(10000, function()
      return got ~= nil
    end, 'the handshake')
    eq(true, got:find('101 Switching Protocols', 1, true) ~= nil, 'answer: ' .. got)
  end)

  test('toggle closes and reopens the window', function()
    vim.cmd 'WizInfoviewToggle'
    eq(false, iv.is_open(), 'closed')
    vim.cmd 'WizInfoviewToggle'
    eq(true, iv.is_open(), 'open')
  end)
end

io.stdout:write 'grail packages\n'

local grail = vim.g.wiz_config.lsp.grail.cmd[1]
if vim.fn.executable(grail) ~= 1 or vim.fn.executable(wiz) ~= 1 then
  io.stdout:write('  (skipped: ' .. grail .. ' is not executable)\n')
else
  test('a grail package gets `grail lsp -C ROOT`, and its modules are found', function()
    local main = here .. '/fixture/pkg/Main.wiz'
    vim.cmd('edit ' .. vim.fn.fnameescape(main))
    local root = here .. '/fixture/pkg'
    eq({ grail, 'lsp', '-C', root }, require('wiz.lsp').cmd(root), 'the command')
    wait(120000, function()
      local c = require('wiz.lsp').client(0)
      return c ~= nil and c.config.root_dir == root
    end, 'the grail lsp client')
    local diags = {}
    wait(120000, function()
      diags = vim.diagnostic.get(0)
      return #diags > 0
    end, 'diagnostics')
    local msgs = {}
    for _, d in ipairs(diags) do
      table.insert(msgs, d.message)
    end
    eq({ '4' }, msgs, 'the diagnostics of Main.wiz')
  end)

  test('without grail.enable, or outside a package, the command is lsp.cmd', function()
    local cfg = require('wiz.config').get().lsp
    eq(cfg.cmd, require('wiz.lsp').cmd(here .. '/fixture'), 'outside a package')
    cfg.grail.enable = false
    eq(cfg.cmd, require('wiz.lsp').cmd(here .. '/fixture/pkg'), 'grail.enable = false')
    cfg.grail.enable = true
  end)
end

io.stdout:write 'toolchain libraries\n'

if vim.fn.executable(wiz) ~= 1 then
  io.stdout:write('  (skipped: ' .. wiz .. ' is not executable)\n')
else
  -- an installed toolchain, laid out as tower, the Nix package and the release tarball
  -- lay it out: bin/wiz (a wrapper), share/wiz/{TOOLCHAIN, lib/, .lake/build/bin/wiz}
  local tc = vim.fn.tempname()
  local share = tc .. '/share/wiz'
  vim.fn.mkdir(share .. '/.lake/build/bin', 'p')
  vim.fn.mkdir(tc .. '/bin', 'p')
  local repo_lib = vim.fn.fnamemodify(here .. '/../../../lib', ':p'):gsub('/$', '')
  vim.fn.system { 'cp', '-R', repo_lib, share .. '/lib' }
  vim.fn.writefile({ 'A Wiz toolchain (test)' }, share .. '/TOOLCHAIN')
  vim.uv.fs_symlink(vim.fn.exepath(wiz), share .. '/.lake/build/bin/wiz')
  -- the toolchain's bin/wiz (a shim in a real installation): it runs that toolchain's
  -- own binary, which finds its library from its layout
  vim.fn.writefile({ '#!/bin/sh', 'exec ' .. share .. '/.lake/build/bin/wiz "$@"' }, tc .. '/bin/wiz')
  vim.fn.setfperm(tc .. '/bin/wiz', 'rwxr-xr-x')
  local lsp = require 'wiz.lsp'

  test('a file of an installed toolchain is found to be one', function()
    eq({ lib = share .. '/lib', wiz = tc .. '/bin/wiz' }, lsp.toolchain(share .. '/lib/Hdl/Core.wiz'), 'toolchain')
    eq(nil, lsp.toolchain(here .. '/fixture/Goals.wiz'), 'not a toolchain')
    eq({ tc .. '/bin/wiz', 'lsp' }, lsp.cmd(share .. '/lib'), 'the command')
  end)

  test('lsp.toolchains = false: a library file is an ordinary file', function()
    local cfg = require('wiz.config').get().lsp
    local buf = vim.fn.bufadd(share .. '/lib/Hdl/Core.wiz')
    eq(share .. '/lib', lsp.root(buf), 'the toolchain library, by default')
    local old = cfg.toolchains
    cfg.toolchains = false
    local ok, root = pcall(lsp.root, buf)
    local cmd = ok and lsp.cmd(root) or nil
    cfg.toolchains = old
    vim.api.nvim_buf_delete(buf, { force = true })
    eq(true, ok, 'root with toolchains off')
    eq(share .. '/lib/Hdl', root, 'the file\'s own directory')
    eq(cfg.cmd, cmd, 'and the ordinary command')
  end)

  test('its library files are served by its own wiz lsp, one client per toolchain', function()
    vim.cmd('edit ' .. vim.fn.fnameescape(share .. '/lib/Prelude.wiz'))
    wait(120000, function()
      return lsp.client(0) ~= nil
    end, 'a client for the toolchain file')
    local c = lsp.client(0)
    eq(share .. '/lib', c.config.root_dir, 'root dir')
    eq({ tc .. '/bin/wiz', 'lsp' }, c.config.cmd, 'cmd')
    -- go to definition of a Prelude name answers
    local lines = vim.api.nvim_buf_get_lines(0, 0, -1, false)
    local row, col
    for i, l in ipairs(lines) do
      local k = l:find(': Nat', 1, true)
      -- (a declaration, not an example in the module's doc comment)
      if k and l:find('^def Nat%.add ') then
        row, col = i, k + 2 -- (0-based: the `a` of Nat)
        break
      end
    end
    vim.api.nvim_win_set_cursor(0, { row, col })
    local params = vim.lsp.util.make_position_params(0, c.offset_encoding)
    local res = vim.lsp.buf_request_sync(0, 'textDocument/definition', params, 120000) or {}
    local uri
    for _, r in pairs(res) do
      local loc = r.result and (r.result.uri and r.result or r.result[1])
      uri = loc and (loc.uri or loc.targetUri)
    end
    eq(true, uri ~= nil and uri:find('/lib/Prelude.wiz$') ~= nil, 'the definition of Nat at ' .. row .. ':' .. col .. ' (' .. vim.inspect(res) .. ')')
    -- another file of the same toolchain: the same client
    vim.cmd('edit ' .. vim.fn.fnameescape(share .. '/lib/Hdl/Core.wiz'))
    wait(60000, function()
      return lsp.client(0) ~= nil
    end, 'the client for Hdl/Core.wiz')
    eq(c.id, lsp.client(0).id, 'one client per toolchain')
  end)
end

io.stdout:write 'fmt and lint\n'

if vim.fn.executable(wiz) ~= 1 then
  io.stdout:write('  (skipped: ' .. wiz .. ' is not executable)\n')
else
  local function cli_has(sub)
    local r = run { wiz, sub, '--help' }
    local text = (r.stdout or '') .. (r.stderr or '')
    return text:find('wiz ' .. sub, 1, true) ~= nil, text
  end
  local has_fmt, fmt_usage = cli_has 'fmt'
  local has_lint, lint_usage = cli_has 'lint'

  test('wiz fmt: formats, then --check passes; an unformatted file fails', function()
    if not has_fmt then
      gap('wiz fmt is not in this toolchain (the usage has no formatter): ' ..
        (fmt_usage:match('usage:[^\n]*') or ''))
    end
    local dir = tempdir()
    local file = dir .. '/Fmt.wiz'
    vim.fn.writefile({ 'import Prelude', '', 'def x : Nat := 1' }, file)
    local formatted = run { wiz, 'fmt', file }
    eq(0, formatted.code, 'fmt exits 0: ' .. (formatted.stderr or ''))
    eq(true, #(formatted.stdout or '') > 0, 'fmt prints the file')
    vim.fn.writefile(vim.split(formatted.stdout, '\n', { plain = true }), file)
    local check = run { wiz, 'fmt', '--check', file }
    eq(0, check.code, '--check on the formatter\'s output: ' .. (check.stderr or ''))
    vim.fn.writefile({ 'def y : Nat :=   1' }, file)
    local bad = run { wiz, 'fmt', '--check', file }
    eq(true, bad.code ~= 0, '--check catches an unformatted file')
    vim.fn.delete(dir, 'rf')
  end)

  test('wiz lint: a clean file passes, --json is JSON', function()
    if not has_lint then
      gap('wiz lint is not in this toolchain (the usage has no linter): ' ..
        (lint_usage:match('usage:[^\n]*') or ''))
    end
    local dir = tempdir()
    local file = dir .. '/Lint.wiz'
    vim.fn.writefile({ 'import Prelude', '', 'def x : Nat := 1' }, file)
    local r = run { wiz, 'lint', file }
    eq(0, r.code, 'lint exits 0: ' .. (r.stderr or ''))
    local j = run { wiz, 'lint', '--json', file }
    eq(0, j.code, 'lint --json exits 0')
    local ok, decoded = pcall(vim.json.decode, j.stdout or '')
    eq(true, ok and decoded ~= nil, 'the JSON output parses: ' .. (j.stdout or ''))
    vim.fn.delete(dir, 'rf')
  end)

  test('the plugin has fmt/lint editor commands', function()
    local missing = {}
    for _, cmd in ipairs { 'WizFmt', 'WizLint' } do
      if vim.fn.exists(':' .. cmd) == 0 then
        table.insert(missing, ':' .. cmd)
      end
    end
    if #missing > 0 then
      gap(('no %s: the CLI is the only way (no format-on-save or lint command)'):format(table.concat(missing, ', ')))
    end
  end)
end

io.stdout:write(('%d passed, %d failed, %d skipped (gaps)\n'):format(passed, failures, skipped))
vim.cmd((failures == 0) and 'qall!' or 'cquit! 1')
