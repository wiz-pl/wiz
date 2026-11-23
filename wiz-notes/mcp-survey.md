# MCP servers: inventory, push and coordination (2026-11-23)

Status: live survey, read-only. No config or product change was made.
Lane: `agent/mcp-survey`, based on `integration/train12` `16c7b0002`.

This is the public extract. The full machine inventory, exact private paths and the
current credential posture are in the shared `wiz-notes/mcp-survey.md` on the agent
machine; it is deliberately not committed here.

Versions observed at the time of writing: OpenCode **2.3.0**, Claude Code **2.1.318**,
ghostbus **0.5.12**, Node **26.13.0**. `uvx` and `bun` were not installed.

Related notes: [`claude-code-parity.md`](claude-code-parity.md),
[`opencode-catalog-2026-11-22.md`](opencode-catalog-2026-11-22.md),
[`opencode-tooling.md`](opencode-tooling.md),
[`mcp-plan-2026-11-17.md`](mcp-plan-2026-11-17.md).

## 0. Bottom line

1. An OpenCode location has six MCP servers: `playwright`, `github`, `agent-bus`,
   `nixos`, and project-scoped `wiz` and `scry`. Claude Code has the same three
   machine-wide servers plus the Playwright plugin and a Claude-only docs connector;
   `wiz`/`scry` are also present twice in Claude scopes with different endpoints.
2. **None of the installed servers sends an MCP notification or advertises resource
   subscriptions.** `wiz`/`scry` expose resources but declare `subscribe: false`;
   ghostbus advertises `tools` only. ghostbus has an HTTP relay with SSE
   (`/api/stream`) and long-poll (`/api/wait`), but that is outside MCP and the relay
   is not running.
3. **No current client turns a generic MCP notification into a model-visible event.**
   OpenCode 2.3.0 reads resources through `list_mcp_resources` / `read_mcp_resource`
   and refreshes tools on `notifications/tools/list_changed`; it has no resource-update
   event. Claude Code 2.1.318 reads resources via `@server:uri` and refreshes lists, but
   documents no generic notification surfacing. Claude **channels** are the one
   exception: proprietary, research preview, one client only.
4. **The realistic push path today is a watcher, not a notification.** Long-poll
   ghostbus `/api/wait` (or hold `/api/stream`) and inject the result into the client:
   OpenCode has `context.session.prompt` (used by the installed cross-session plugin);
   Claude Code has no stable headless equivalent. `bus_wait` is the right portable
   primitive; MCP notifications are not.
5. **Human push already exists and should not be duplicated.** `/workspace/wiz-tools/notify.sh`
   posts to a self-hosted ntfy topic with a token file. Adding `ntfy-mcp-server` or
   `pushover-mcp` would add a second credential path and a second API surface for the
   same result.
6. **The highest-risk current item is not a missing server.** An unpinned
   `github-mcp-server-kosta` process receives a `gh` token with broad account scopes,
   and Claude Code has no deny rules for its write tools. Pinning (or replacing) that
   server is worth more than any addition below.

## 1. Inventory

`~` is `$HOME`. The one shared bus store is `~/.local/share/ghostbus/bus.json`.

### 1.1 OpenCode machine-wide

| server | purpose | transport | auth/secrets | overlap with current tools | verdict |
| --- | --- | --- | --- | --- | --- |
| `playwright` | Headless browser automation: DOM/accessibility snapshots, clicks, console, network | local stdio, `npx -y @playwright/mcp@0.0.86`, headless/isolated/Chromium, loopback origins only | none; page content untrusted; unsafe run-code and upload denied | Chrome DevTools MCP, desktop browser pane, one-off CDP scripts | **keep**, pinned and loopback-confined |
| `github` | GitHub reads (PRs, issues, checks, logs) | local stdio, `sh -c 'exec env GITHUB_TOKEN="$(gh auth token)" npx -y github-mcp-server-kosta'` | token read at runtime from `gh`; no secret in config; current token has broad scopes | `gh` CLI, CI poller, official GitHub MCP | **keep read-only, harden**: pin/replace, least-privilege token, same write denies in Claude Code |
| `agent-bus` | Cross-lane messages, tasks, shared files/context, provenance | local stdio, `npx -y ghostbus --store ~/.local/share/ghostbus/bus.json` | none on stdio; store mode 0600; per-agent tokens exist but enforcement off; relay needs `GHOSTBUS_KEY` | OpenCode `send_message_across_sessions`, notes, build queue | **keep**, pin `ghostbus@0.5.12`; see the cross-process caveat |
| `nixos` | NixOS/Home Manager/nix-darwin options, packages, flakes, cache, store | local stdio, `nix run github:utensils/mcp-nixos/v3.1.1 --` | none; public APIs plus local Nix | `nix` CLI, web search | **keep**, pinned tag |
| `wiz` (project) | Wiz toolchain and LSP: 20 declared tools (check/parse/fmt, diagnostics, hover, goals, search, doc, symbols, completion, code actions, rename), with `build` gated, plus 7 runner tools gated by flags; one lazy `wiz lsp` per process; path confinement | local stdio, `sh /workspace/wiz-tools/wiz-mcp --idle 600 --timeout 300` | none; no network; `build` hidden unless `--allow-build`; runners add flags and a `bwrap` sandbox | OpenCode has no LSP client; Claude has C#/TS LSP plugins for other projects | **keep project-scoped** |
| `scry` (project) | Read-only Scry static analysis: taint, project, facts, query, explain, findings; SARIF/JSON resources | local stdio, `sh /workspace/wiz-tools/scry-mcp --timeout 300` | none; read-only for the workspace; reports in a private temp dir | no other static analyser | **keep project-scoped** |

### 1.2 Claude Code

`programs.claude-code.mcpServers` emits a generated personal plugin; servers appear as
`plugin:hm:<server>` and tools as `mcp__plugin_hm_<server>__<tool>`. The parity table is
in [`claude-code-parity.md`](claude-code-parity.md).

| server | purpose | transport | auth/secrets | overlap | verdict |
| --- | --- | --- | --- | --- | --- |
| `plugin:hm:agent-bus` | Same bus, same store | stdio ghostbus | same as OpenCode | OpenCode bus | **keep** |
| `plugin:hm:github` | Same GitHub server | stdio, same wrapper | same token | `gh` CLI | **keep, harden** |
| `plugin:hm:nixos` | Same NixOS server | stdio, same pin | none | `nix` | **keep** |
| `plugin:playwright:playwright` | Browser automation | enabled Playwright plugin | none | OpenCode Playwright | **keep**; not duplicated |
| `claude.ai Claude Docs` | Anthropic docs lookup | Claude-only connector | claude.ai auth | web fetch | **keep** |
| `wiz`, `scry` | Wiz/Scry tools | project `.mcp.json` plus a second **local** scope with a different endpoint | none | OpenCode `wiz`/`scry` | **project scope only**; remove the local duplicate |

The duplicate-scope warning is real: `claude mcp list` reports both servers as
"defined in multiple scopes with different endpoints" (project uses
`tools/.../wiz-mcp.sh`, local uses `/workspace/wiz-tools/wiz-mcp`). One definition per
server is the correct state.

### 1.3 Custom servers in `/workspace/wiz-tools`

| server | what it exposes | transport | auth/secrets | scope verdict |
| --- | --- | --- | --- | --- |
| `wiz-mcp` | 20 declared tools (`build` gated) plus 7 runner tools; resources `wiz://error-codes/{code}`, `wiz://stages/{name}`, `wiz://trust-ledger/{module}`; `resources.subscribe: false` | Python stdlib, stdio; one lazy `wiz lsp` per process | none; path confinement; env allowlist; runners sandboxed | **project-scoped**, not machine-wide |
| `scry-mcp` | 7 base tools plus gated dynamic/triage tools; resources `scry://runs/{id}/sarif` and `.../json`; `subscribe: false` | Python stdlib, stdio, shares the wiz transport/policy | none; read-only workspace; compile-db flags allowlisted | **project-scoped** |
| ghostbus | 29 tools: presence, messages, tasks, workspace files/context/capsules, event log; no notifications | stdio; optional HTTP relay | open by default on stdio; file 0600; optional tokens; relay key optional | **keep**, pin |

`wiz`/`scry` derive the workspace from cwd and look for the bridge under `./tools/...`.
They should never be machine-wide: starting them in an arbitrary project would fail or
attach to the wrong tree. The action is to remove the duplicate Claude **local** entries,
not to add the servers globally.

## 2. Notification and push

### 2.1 The notification families (and why none is a wake-up)

| Family | What it carries | When it works | Why it is not a user-visible push |
| --- | --- | --- | --- |
| `notifications/message` (logging) | level, logger, free-form data | 2025-era after `logging/setLevel`; logging is deprecated in 2026-07-28, where the log level is per-request `_meta` and servers must not emit for requests that did not ask | clients log it; not a conversational event |
| `notifications/resources/updated` | only a URI | 2025-era after `resources/subscribe`; 2026-07-28 replaces it with `subscriptions/listen` | no payload, no parameters, no cursor; a missed event is lost |
| `notifications/{tools,prompts,resources}/list_changed` | a catalog changed | both eras; 2026-07-28 over `subscriptions/listen` | refreshes lists; says nothing about content |
| `notifications/progress` | progress token, value, total | request-scoped on the response stream | only inside a call the client already made |

The **MCP Events** extension (SEP-3415, Final, extension stage Beta) exists because
those notifications are insufficient: it adds `events/list`, typed payload schemas,
subscription arguments and three delivery modes — `events/poll`, `events/stream`
(push), `events/subscribe` (webhook) — with cursors and replay. It requires protocol
**2026-07-28**. That is the right long-term primitive; no installed server implements it.

### 2.2 Client capability matrix

| Capability | OpenCode 2.3.0 (installed) | OpenCode 2.4.0 (released 2026-11-23, not installed) | Claude Code 2.1.318 |
| --- | --- | --- | --- |
| MCP tools | yes, via Code Mode | yes | yes |
| MCP resources | yes: `list_mcp_resources`, `read_mcp_resource`; permission actions exist | yes | yes: `@server:uri` mentions and automatic list/read tools |
| `tools/list_changed` | refreshes the tool catalog | yes | refreshes tools/prompts/resources in an interactive session |
| `notifications/resources/updated` | **no evidence of subscription wiring**; SDK method exists, no `mcp.resource.updated` event, and the PR adding one was closed unmerged | MCP Events supersedes this for push | v2 runtime holds a `subscriptions/listen` stream for `list_changed`; resource updates are not documented as surfaced |
| Generic notification → model context | no; server log notifications go to OpenCode logs | MCP Events can hand an event to an **automation** (prompt, script or shell command) | no; standard MCP is "Claude queries it; nothing is pushed" |
| In-session push | **no** | **yes, beta**: `io.modelcontextprotocol/events` + automations | **channels**, research preview: server declares `experimental["claude/channel"]`, emits `notifications/claude/channel`; `--channels` or `--dangerously-load-development-channels` |
| Cross-session message today | yes: `send_message_across_sessions` plugin; `context.session.prompt({sessionID, text, delivery})` | yes | no equivalent |
| Protocol 2026-07-28 | per-server `protocol` setting; legacy default | probes newest first, falls back to legacy | v2 runtime negotiates it; channel servers on 2026-07-28 do **not** register |

Consequences:

- **OpenCode 2.3.0 cannot be woken by an MCP server.** It can read a resource or
  refresh a list during a turn. OpenCode 2.4.0 is the first supported event path; it is
  one day old at the time of this survey and not in the Nix profile.
- **Claude Code channels are real push but not a general answer.** They require
  Anthropic auth (not Bedrock/Vertex/Foundry), the `--channels` opt-in, an allowlist, and
  an open session. Custom channels need `--dangerously-load-development-channels`, which
  is ignored in `-p`/Agent SDK runs; it is an interactive-session pilot.
- **The v2 runtime's `subscriptions/listen` is documented for `list_changed` only.** No
  evidence that a resource-update or logging notification reaches the model.

### 2.3 Which servers actually send MCP notifications?

| server | Sends MCP notifications? | Supports resource subscription? | Evidence |
| --- | --- | --- | --- |
| `agent-bus` (ghostbus 0.5.12) | **no** — `initialize` returns `capabilities: { tools: {} }` | no resources | `src/mcp-server.mjs` |
| `wiz` | **no** | resources list/read, `subscribe: false` | `tools/wiz-mcp/wiz_mcp.py` |
| `scry` | **no** | resources list/read, `subscribe: false` | `tools/scry-mcp/scry_mcp.py` |
| `playwright` / `github` / `nixos` | no notification surface used by the client | not used | tool-only in practice |
| `@modelcontextprotocol/server-everything` 2.3.1 | **yes** — trigger log messages, resource updates, list changes, progress | **yes** (2025-era `resources/subscribe`; 2026-07-28 `subscriptions/listen`) | its feature doc |
| `ntfy-mcp-server` 2.4.2 | **no** — it publishes to ntfy; its resource is a topic snapshot; `ntfy_fetch_messages` has `wait_seconds` (≤40 s) long-poll | no | its README |
| `pushover-mcp` 2.0.0 | no | no | tools only |
| `mcp-notifications` 2.5.2 / `@topvisor/mcp-notifications` 1.0.5 | no | no | webhook/desktop tools only |
| `walktalk-listen` 0.4.1 | **yes, Claude-only** — emits `notifications/claude/channel` | n/a | its README; proves the channel pattern |
| Claude channel plugins (Telegram/Discord/iMessage/fakechat) | **yes, Claude-only** — proprietary notification | n/a | Claude docs |

**The notification-branded servers mostly are not MCP push servers.** They expose a
`send` tool (and sometimes a `fetch`/long-poll tool) so the model can push to a phone or
chat service. That is outbound human messaging, not server-to-client MCP push.

### 2.4 Is SSE or long-poll the realistic path?

For our clients, **yes — with a watcher that injects the event**, not by itself:

- **Long-poll** `GET /api/wait?agent=<name>&sinceSeq=<n>&timeout=<seconds>` returns the
  next relevant event or an empty result after the timeout. ghostbus clamps the timeout
  to 0–55 s (default 25), filters `message.send` to `to`, `*` or the actor, and returns
  `{events, headSeq, waited}`. Simple, proxy-friendly, one request per wait, no stream
  cap; a natural MCP `bus_wait`.
- **SSE** `GET /api/stream?agent=<name>` emits a `ready` event, then one event per
  occurrence, with a `: ping` every 25 s. Better for one long-lived watcher or a board:
  no polling latency, but holds a connection and needs reconnect logic. The relay caps
  it at 100 streams per workspace and 1000 per server.
- **MCP notification** would be better if it existed end-to-end, but it does not:
  ghostbus does not emit one, OpenCode 2.3.0 does not subscribe, and Claude Code does
  not surface generic ones. Claude channels are the only exception and are one-client,
  preview and allowlist-gated.
- **MCP Events** is the right answer once the client and server both support it. OpenCode
  2.4.0 is the first client here; ghostbus would need an `io.modelcontextprotocol/events`
  implementation (an `events/list` type such as `bus.message`, delivery `poll` and
  `push`, cursor = `seq`).

## 3. Coordination, messaging and task queues

### 3.1 What ghostbus gives us (and what it does not)

- **Surface**: 29 tools across presence (`register`, `heartbeat`, `agents`), messages
  (`send`, `inbox`, `thread`, `search`, `channels`), tasks (`create`, `list`, `claim`,
  `complete`, `cancel`, `approve`, `comment`), workspace files/context/capsules, and
  provenance (`events`, `sync`). One 0600 JSON file.
- **Live state at the sample**: more than a hundred historical agents, roughly 380
  messages, **zero tasks**, a handful of shared files and a few hundred events. The bus
  is being used as a message log, not as a task queue. That is direct evidence against
  adding a second task manager.
- **Atomicity caveat**: the per-instance mutex serializes operations only inside one
  process. Every OpenCode location and every Claude session has its own ghostbus
  process; each mutation is a read-modify-write against the same file with an atomic
  rename, but there is **no cross-process lock**. Concurrent lanes can lose each
  other's writes (last writer wins). The source comment says so explicitly. A single
  relay process would serialize writes, but its `/mcp` endpoint implements only
  `tools/list` and `tools/call`, not `initialize`/`server/discover`, so standard clients
  cannot use it as their MCP transport today. **This is a reliability bug to fix or
  document before scaling the bus further.**
- **Surface drift**: the `agent-bus` skill still shows
  `workspace_put_context({key, value})` and `workspace_get_capsule()`; 0.5.12 actually
  requires `{agent, context}` and a `slug`. Fix the skill when the bus is next touched.
- **No notifications**: no `notifications/message`, no resource subscription, no
  `bus_wait`. The HTTP relay's SSE/long-poll are the only push primitives.

### 3.2 Other coordination servers

| server | purpose | transport | auth/secrets | overlap | verdict |
| --- | --- | --- | --- | --- | --- |
| `@modelcontextprotocol/server-memory` 2.2.1 | Local knowledge graph in one JSON file | stdio | none | Notes + ghostbus files/capsules are the durable shared memory; a second store diverges | **do not add** |
| `memory-bank-mcp` / `basic-memory` | Markdown memory banks / graph with embeddings | stdio | none / heavy Python deps | same | **do not add** |
| `task-master-ai` 0.43.1 | Project task files + its own provider stack | stdio | many provider keys; 40+ dependencies | Build queue + ghostbus tasks; zero tasks used; its model calls bypass the harness | **do not add** |
| `@kazuph/mcp-taskmanager` 1.1.1 | Simple task queue | stdio | none | ghostbus tasks already have leases, approval and provenance | **do not add** |
| `claude-flow` / Ruflo 3.80.1 | Swarm orchestration, memory, consensus, 60+ agents | stdio/HTTP | provider keys, large dependency tree | Overlaps ghostbus + build queue + subagents | **do not add** |
| `agent-mcp` (npm) | `0.0.0` WIP placeholder | — | — | — | **do not add** |
| A2A servers | Agent2Agent protocol, not MCP | varies | varies | Separate protocol; no client support | **out of scope** |
| OpenCode `send_message_across_sessions` | Peer-session user messages; `steer`/`queue`; `need_reply` | in-process plugin | none | Overlaps ghostbus messaging, but is the **delivery** mechanism a watcher can reuse | **keep, not a bus replacement** |

**What the alternatives add beyond the shared bus: essentially nothing for this
workflow.** The bus already has messages, tasks with leases and approval, shared files,
context, capsules and a provenance log. The missing piece is delivery (wake), not
storage or another API.

## 4. General-purpose servers: security and permission implications

| server | purpose | transport | auth/secrets | overlap | verdict |
| --- | --- | --- | --- | --- | --- |
| `@modelcontextprotocol/server-filesystem` 2.4.0 | Read/write/search under allowed roots | stdio | none; root confinement | Built-in read/write/edit/glob/grep; widens file access | **do not add** |
| `mcp-server-git` 2026.11.18 | Git read/search/manipulate | stdio via `uvx` | none | `git` CLI is the interface; no `uvx` here | **do not add** |
| `mcp-server-fetch` 2026.11.18 | Fetch URL → markdown | stdio via `uvx` | none | Built-in web fetch; extra SSRF/prompt-injection boundary; npm name is a security-holding package | **do not add** |
| `@wonderwhy-er/desktop-commander` 0.3.4 | Shell, file editing, process control | stdio | none; full user authority; ~30 deps | Built-in shell + build queue; RCE-equivalent | **do not add** |
| `mcp-server-time` 2026.11.18 | Time/timezone conversion | stdio | none | System clock | **do not add** |
| `@modelcontextprotocol/server-sequential-thinking` 2.2.0 | Structured thought tool | stdio | none | Model reasoning; no new action | **do not add** |
| `serena-agent` 2.1.0 | LSP-based semantic retrieval/refactor, 40+ languages | stdio | none; GPL-3.0 app; downloads language servers | `wiz` LSP for Wiz; `mcp-language-server` for C#/TS projects; Claude LSP plugins | **do not add** |
| `@upstash/context7-mcp` 4.7.3 / remote | Library documentation lookup | remote HTTP or stdio | optional API key/OAuth; queries leave the machine | `nixos` covers Nix; web fetch covers docs; adds a remote trust boundary | **conditional**, project-scoped |
| `chrome-devtools-mcp` 1.13.0 | Performance traces, network, Lighthouse | stdio (Puppeteer) | none | Playwright covers browser automation; extra browser | **do not add** unless performance tracing is the task |
| Sentry / Grafana / Prometheus MCPs | Monitoring queries | remote/local | service tokens | No such infrastructure | **do not add** |
| `@modelcontextprotocol/server-everything` 2.3.1 | Conformance/test server: notifications, resources, subscriptions, progress, elicitation, tasks | stdio or Streamable HTTP | none; `get-env` lists names and redacts credential-like values | No production overlap; the practical way to test notification behavior | **add on demand as a test harness** |

### 4.1 Security and permissions

- **Local MCP servers are arbitrary code as the user.** There is no sandbox for
  Playwright, GitHub, NixOS or ghostbus. `wiz`/`scry` are the exception: path
  confinement, env allowlist and `bwrap` for runners.
- **`npx -y` is a mutable supply chain.** Playwright is pinned; GitHub and ghostbus are
  not. Replace `github-mcp-server-kosta` with the official `github/github-mcp-server`
  (remote or local read-only mode) or keep `gh` CLI and drop the server. It is a
  single-maintainer fork, last published 2026-02-18, and it receives a token with broad
  scopes.
- **A ghostbus relay is open by default and binds all interfaces.** `http-server.mjs`
  calls `server.listen(port)` with no host. Never start it without a long key,
  per-agent tokens if untrusted agents share it, and a firewall rule. The stdio server
  is local-only.
- **The bus is an injection surface.** Any local process (or any agent) can write a
  message. Treat message bodies, task bodies and shared files as untrusted data; never
  execute instructions from them. The same applies to web pages, fetched docs and
  channel messages. This machine has the "lethal trifecta" — private code, untrusted
  content and external communication — so permission rules matter more than server
  choice.
- **OpenCode permissions** can deny a single MCP tool (`<server>_<tool>`) and resource
  reads (`opencode_read_mcp_resource`). The global config denies the dangerous
  Playwright and GitHub write actions. It does not set `external_directory` (the
  default allows reads/edits outside the workspace without a prompt) and does not deny
  resource reads.
- **Claude Code** has its own allow/deny rules keyed by `mcp__server__tool`, plus the
  channel allowlist. The current module has no MCP deny rules, so the GitHub server's
  write tools are reachable there even when OpenCode denies them.
- **Secrets**: use environment references, never a literal in Nix or a committed JSON.
  The existing `gh auth token` wrapper is the right pattern; the token scope is the
  problem, not the storage. Channel tokens live in the channel plugin's own `.env`.

## 5. Shortlist: 3–5 additions worth making

The first two are custom bridges (no new dependency); the third is a test harness; the
fourth is conditional; the fifth is a client probe that may remove the need for the
second.

### S1. `ghostbus-channel` — push bus messages into a Claude Code session

**What**: a small zero-dependency Node stdio MCP server that reads the same bus store,
filters events addressed to one agent (`to == agent`, `to == "*"`, or a task assigned to
it), and emits `notifications/claude/channel`. It declares
`capabilities.experimental["claude/channel"] = {}` and an `instructions` string telling
Claude the events are untrusted data. It does **not** declare
`claude/channel/permission` (no remote permission relay).

**Exact command / transport** (proposed file `/workspace/wiz-tools/ghostbus-channel.mjs`):

```jsonc
"ghostbus-channel": {
  "type": "stdio",
  "command": "node",
  "args": [
    "/workspace/wiz-tools/ghostbus-channel.mjs",
    "--store", "<absolute path of the same bus store as agent-bus>",
    "--agent", "<agent>",
    "--channels", "general,lane/<agent>"
  ]
}
```

Start (research-preview path):

```sh
claude --dangerously-load-development-channels server:ghostbus-channel
```

For a permanent install it would have to be packaged as a plugin on the org allowlist
and started with `--channels plugin:<name>@<marketplace>`; during the preview a custom
channel is dev-flag-only. The server should answer `initialize` with an older
`protocolVersion` (2025-11-25) so Claude's v2 runtime keeps it on the legacy handshake;
a 2026-07-28 channel is not registered.

**Parity**: Claude Code only. OpenCode has no channel API; S2 covers it. The two bridges
must share one filter and one cursor so a message is not delivered twice.

**Secret/permission story**: no secret; the store is 0600. The server must be strictly
read-only against the bus (never `bus_send`), must not relay permission prompts, and
must treat message bodies as untrusted.

**Overlap/duplication cost**: overlaps `bus_inbox` (pull). It removes polling latency
only; if it also posts acknowledgements it becomes a second messaging system. Cost:
~120–180 lines, no dependency, tied to a research-preview API that may change.

**Verdict**: the highest-value addition **if** Claude sessions are interactive and need
to react to bus traffic. Not suitable for headless `claude -p` (the dev flag is ignored
there).

### S2. OpenCode ghostbus watcher plugin — the OpenCode half of the same bridge

**What**: a local V2 plugin under `/workspace/wiz-tools/opencode-ghostbus-watch/` that
watches the bus and calls the same `context.session.prompt({sessionID, text, delivery})`
API the installed cross-session plugin already uses. Prefer `delivery: "queue"` for busy
sessions so it does not interrupt a tool call. It can poll `bus_sync` from a per-agent
cursor every 2–5 s, or subscribe to the relay's SSE stream if the relay is running.

**Exact command / transport**:

```jsonc
// /workspace/opencode.json (project) or global opencode.json, proposed
"plugins": ["/workspace/wiz-tools/opencode-ghostbus-watch"]
```

The plugin directory needs `package.json` + `index.js` in the V2 plugin shape; a single
`.js` file can also be dropped in `.opencode/plugins/`. If it uses the relay instead of
the file, it needs `--relay http://127.0.0.1:8377` and a key file (0600).

**Parity**: OpenCode only; Claude uses S1. The mapping from bus agent name to OpenCode
session ID is the hard part: the bus registers by branch/lane, while a session has an
ID and a title. Build the map from `context.session.list()` and the worktree/title, or
carry the session ID in a registration extension. Do not guess a session from a
substring.

**Secret/permission story**: none if it reads the file; a 0600 key file if it uses the
relay. It must not create a second message store, must not echo its own injections back
to the bus, and must dedupe by message id.

**Overlap/duplication cost**: the existing `send_message_across_sessions` is the
transport; this is only a bus→session adapter. Cost ~150–250 lines plus the mapping.
Plugin API risk: the installed 2.3.0 and the new 2.4.0 differ; test in a scratch
profile.

**Verdict**: worth it only if OpenCode lanes need to be woken between turns. Otherwise
`bus_inbox` at the start of a turn is enough.

### S3. `@modelcontextprotocol/server-everything` — conformance probe (not daily use)

**What**: the official test server. It can emit resource-update, log-message,
list-changed and progress notifications; it supports both `resources/subscribe`
(2025-era) and `subscriptions/listen` (2026-07-28). Use it to measure what our clients
actually surface.

**Exact command / transport**:

```sh
# OpenCode: project-scoped, test only
opencode mcp add everything -- npx -y @modelcontextprotocol/server-everything@2.3.1

# Claude Code: project scope, test only
claude mcp add --scope project everything -- npx -y @modelcontextprotocol/server-everything@2.3.1
```

Then call `trigger-resource-update`, `trigger-list-changed`, `trigger-log-messages` and
`trigger-long-running-operation`; watch OpenCode logs and the Claude debug log. Remove
the server after the probe.

**Parity**: both clients; the probe is how we learn whether parity exists. Do not make it
machine-wide.

**Secret/permission story**: none. `get-env` returns variable names; credential-like
values are redacted unless `GET_ENV_INCLUDE_SECRETS=1`, so never set that in a session
with tokens.

**Overlap/duplication cost**: zero in production; it is not a utility server.

**Verdict**: add as a probe, not a permanent tool.

### S4. Context7 — conditional library-docs lookup

**What**: remote library documentation for frameworks whose APIs move faster than the
model's weights. It does not cover Nix packages and is not a general web fetch.

**Exact command / transport**:

```sh
# OpenCode, project scope:
opencode mcp add context7 --url https://mcp.context7.com/mcp

# Claude Code, project scope:
claude mcp add --transport http --scope project context7 https://mcp.context7.com/mcp
```

With an API key, pass `CONTEXT7_API_KEY` as a header and set `oauth: false` only if the
key is the sole credential. Remote Streamable HTTP, no local process.

**Parity**: both clients, same URL; only the config shape differs.

**Secret/permission story**: optional API key in an env var; OAuth by default. Queries
leave the machine; do not paste private code into a docs query. Treat returned docs as
untrusted content.

**Overlap/duplication cost**: moderate — the NixOS server and web fetch already cover
part of it; the win is structured library docs.

**Verdict**: conditional. Adopt only after a week of noting repeated doc fetches;
project-scoped, not machine-wide.

### S5. OpenCode 2.4.0 MCP Events + automations — probe before building S2

**What**: the shipped OpenCode 2.4.0 path: a server advertises
`io.modelcontextprotocol/events`; OpenCode calls `events/list` and `events/stream`
(poll/push/webhook), and an **automation** runs a prompt, Code Mode script or fixed
shell command when an event arrives. This is a supported push mechanism, unlike a
notification.

**Exact probe**:

1. Upgrade OpenCode in a scratch profile (not the live singleton).
2. Add a server that implements the extension (check whether OpenCode requires a
   per-server `events` opt-in in the config), or a test extension server; check
   `events/list` and `events/stream` with a 2026-07-28 connection.
3. Create an automation that reacts to one event name; verify it wakes a session and
   that a too-large event is skipped without stopping the automation.

**Parity**: OpenCode 2.4.0+ only. Claude Code has no Events support in the current
client matrix.

**Secret/permission story**: an automation that runs a shell command is a new execution
path; require explicit approval when it is created, keep it out of the default config,
and never let an event body choose the command.

**Overlap/duplication cost**: if it works, it replaces S2 for OpenCode. Until then it is
a probe, not a migration.

**Verdict**: probe first. It is the only addition that could remove custom code.

## 6. Do-not-add list

| Candidate | Why not |
| --- | --- |
| `ntfy-mcp-server`, `pushover-mcp` | `notify.sh` already sends to the phone with a token file; these add a second credential, topic and API surface. They are **tools-only** (no MCP notification), so they do not solve agent wake. Wrap `notify.sh` in one tiny local tool if a tool is wanted. |
| `mcp-notifications`, `@topvisor/mcp-notifications` | Stale or desktop-only; tools-only; duplicate the existing notifier; no agent push. |
| `walktalk-listen` | External SaaS + OAuth credential discovery; Claude-only channel adapter; not our chat system. Useful as a code reference, not an install. |
| `@modelcontextprotocol/server-memory`, `memory-bank-mcp`, `basic-memory` | Duplicate the notes + ghostbus workspace files/capsules. A second memory store diverges; none has cross-process merge/locking. |
| `task-master-ai`, `@kazuph/mcp-taskmanager`, `claude-flow`/Ruflo | Duplicate the build queue and ghostbus tasks (zero use today). Task Master adds 40+ dependencies and its own provider stack; Ruflo adds a swarm runtime. Both bypass the one-job/one-heavy discipline. |
| `@modelcontextprotocol/server-filesystem` | Built-in read/write/edit/glob/grep already cover it; a second filesystem server widens access and duplicates permission rules. |
| `mcp-server-git`, `mcp-server-fetch` | `git` and web fetch are already the interfaces; `uvx` is not installed; the npm names are security-holding packages. |
| `@wonderwhy-er/desktop-commander`, any shell server | Full user-level code execution, 30+ dependencies, bypasses the build queue and shell permission scanner. |
| `mcp-server-time`, `@modelcontextprotocol/server-sequential-thinking` | Trivial/covered capabilities; extra tools and context for no new action. |
| `serena-agent` | GPL-3.0 application, heavy LSP downloads, duplicates the Wiz LSP and per-project `mcp-language-server`; no Lean support out of the box. |
| `chrome-devtools-mcp` | Duplicates Playwright for browser work; reconsider only when a Wasm performance trace is the task. |
| Sentry/Grafana/Prometheus/Slurm MCPs | No matching infrastructure; Slurm MCPs bypass the build queue and one-job discipline. |
| Any registry "top 100" server added casually | The official reference servers call themselves educational, not production-ready; `npx -y` runs mutable code with the user's authority. Pin, read the source, or don't add. |

## 7. How `bus_wait` fits

`bus_wait` is a separate lane and is **not in ghostbus 0.5.12** (its 29 tools have no
wait/poll tool). The right contract, based on the relay's existing primitive, is:

```text
bus_wait({ agent, sinceSeq?, timeout? })
  -> { events: [...], headSeq, waited: bool }
```

with the relay's semantics: filter `message.send` to `to == agent`, `to == "*"` or the
actor; default 25 s; clamp to 55 s; return immediately if events after `sinceSeq` already
exist; otherwise block until one arrives or the timeout expires. If it is implemented
in-process on the stdio server, it must use the same event sequence as `bus_sync` so a
caller can resume with `headSeq`.

Why it fits:

- **Portable**: both clients can call an MCP tool; neither needs channel/Events support.
- **Cheap**: one request per wait, no stream, no subscription state.
- **Composable**: a supervisor or watcher can call it and then inject the event into a
  session; a model can call it once at the end of a turn instead of polling.
- **Bounded**: 55 s max keeps it under a typical client timeout.

Why it is not sufficient alone:

- It **cannot wake an idle session**. The agent must already be in a turn to call it.
  For wake, pair it with S1 (Claude channel) or S2 (OpenCode plugin), or with an
  external supervisor that calls the OpenCode API.
- It is **pull**, so a dead session never sees the message; the bus still has it for
  `bus_inbox` at the next turn.

**Recommendation**: implement `bus_wait` as the single portable wait primitive, with the
relay semantics above. Do **not** also build a second notification protocol into
ghostbus.

## 8. What could not be verified, and the next probes

| Unverified | Why it matters | Next probe |
| --- | --- | --- |
| OpenCode 2.3.0's handling of log/resource notifications | The binary contains the SDK methods but no `mcp.resource.updated` event; docs do not promise model-visible notifications | Add `server-everything@2.3.1` in a scratch project, call the trigger tools, watch logs and the session |
| OpenCode 2.4.0 MCP Events + automations | This is the supported push path and may replace S2 | Install 2.4.0 in a scratch profile; test `events/list` / `events/stream`; create one automation |
| Claude Code channels on 2.1.318 | `--channels` is hidden; allowlist/org policy and the 2026-07-28 registration rule are easy to get wrong | Install `fakechat@claude-plugins-official`, run `claude --channels plugin:fakechat@claude-plugins-official`, send a message; then test a local channel with `--dangerously-load-development-channels server:<name>` |
| `bus_wait` exact contract | It is a separate lane and not in 0.5.12 | Ask the lane for the signature; compare against `/api/wait`; verify `sinceSeq`/`headSeq` and timeout clamping |
| Ghostbus cross-process lost updates | Many agents/processes share one file with only a per-instance mutex | Run two stdio servers, send interleaved messages, compare count/seq; then add a file lock or a single-writer broker |
| Exact MCP capabilities of `playwright`, `github`, `nixos` | The inventory says "tool-only in practice" but `initialize` was not captured | Probe each with a JSON-RPC `initialize` and record `capabilities` |
| Claude v2 `subscriptions/listen` resource updates | Docs mention `list_changed`, not resource payloads | Use `server-everything` with a 2026-07-28 connection and a subscribed resource; watch the debug log |
| `github-mcp-server-kosta` provenance | Single-maintainer fork, last publish 2026-02-18, broad token | Diff against the official server; replace or pin; use a read-only fine-grained token |
| ntfy reachability/token scope | The notifier is the human path; no test notification was sent | Send one harmless notification after coordinating with the human |
| Context7 API key/OAuth and retention | Remote docs service; queries leave the machine | Read its auth/retention docs; test with a throwaway library query |

## 9. References

Local:

- `/etc/nixos/home-manager/opencode/opencode.json` — machine-wide OpenCode servers,
  permissions, plugins.
- `/etc/nixos/home-manager/claude-code.nix` and
  `/etc/nixos/home-manager/claude-code/README.md` — Claude parity and the generated
  plugin mechanism.
- `/workspace/opencode.json` — project-scoped `wiz`/`scry`.
- `/workspace/wiz-lang/.mcp.json` — Claude project-scoped `wiz`/`scry`.
- `/workspace/wiz-tools/{wiz-mcp,scry-mcp,notify.sh}`;
  `tools/wiz-mcp/wiz_mcp.py`, `tools/scry-mcp/scry_mcp.py`.
- `~/.local/share/ghostbus/bus.json`; the installed `ghostbus` package (0.5.12).

Specs and client docs:

- MCP 2026-07-28 changelog:
  <https://modelcontextprotocol.io/specification/2026-07-28/changelog>
- MCP Events extension (SEP-3415):
  <https://modelcontextprotocol.io/extensions/events/overview>
- MCP security best practices:
  <https://modelcontextprotocol.io/specification/2026-07-28/basic/security_best_practices>
- OpenCode MCP servers / permissions:
  <https://opencode.ai/docs/mcp-servers>, <https://opencode.ai/docs/permissions>
- OpenCode 2.4.0 changelog (MCP Events, automations):
  <https://opencode.ai/changelog/v2.4.0>
- Claude Code MCP: <https://code.claude.com/docs/en/mcp>
- Claude Code channels: <https://code.claude.com/docs/en/channels>,
  <https://code.claude.com/docs/en/channels-reference>

Server sources:

- ghostbus: <https://github.com/littlestjames82-sys/ghostbus>
- ntfy MCP: <https://github.com/cyanheads/ntfy-mcp-server>
- Pushover MCP: <https://github.com/AshikNesin/pushover-mcp>
- Everything server: <https://github.com/modelcontextprotocol/servers>
- Serena: <https://github.com/oraios/serena>
- Context7: <https://github.com/upstash/context7>
- Official GitHub MCP: <https://github.com/github/github-mcp-server>

## Addendum (2026-11-23, after this survey): `bus_wait` is implemented

The separate lane did land, and it is live on this machine (applied by `nrs`):
`ghostbus-wait`, a dependency-free stdio MCP proxy in the dotfiles repo
(`agent-bus-wait` @ `afa3a450a`). It spawns the existing `ghostbus --store
~/.local/share/ghostbus/bus.json`, forwards the 29 tools unchanged, and adds one:

```text
bus_wait({ agent, timeoutMs = 30000 (max 600000), sinceSeq?, afterId?, unreadOnly? })
  -> { messages: [...], timedOut: bool, headSeq, ... }
```

- It waits for a new **direct message to `agent` or a broadcast**, excludes the agent's
  own sends, and returns the messages **without marking them read** (`bus_inbox` is
  still the reader).
- Timeouts are normal results (`timedOut: true`), not errors. `sinceSeq`/`afterId` are
  cursors; `unreadOnly` filters by `readBy`.
- It watches the store **directory** (`fs.watch` plus a 1 s fallback) because the store is
  replaced by atomic rename; it is not implemented on the relay's `/api/wait`.
- Tested through the Nix-built wrapper: 30 tools (`bus_wait` added), a ~302 ms timeout,
  a real `ghostbus-cli` message woke it and stayed unread until `bus_inbox`, broadcast
  vs own-message filtering, both cursors, malformed-frame recovery and child-exit error.
  Both clients are configured to the same `/nix/store/...-ghostbus-wait` path.

Contract differences from §7's proposal: the default is 30 s (clamp 600 s) rather than
25 s/55 s, and it is store-driven rather than relay/sequence-driven. For an interactive
call keep `timeoutMs` below the client's tool timeout (OpenCode's `agent-bus` execution
timeout is 120 s), so 30–55 s remains the sensible range. This resolves the
“`bus_wait` exact contract” row in §8; the client-side wake gap (S1/S2/S5) is unchanged.
