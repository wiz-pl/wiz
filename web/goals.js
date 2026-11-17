// The goals panel: the LSP answers (`wiz/interactiveGoals`, `wiz/interactiveTermGoal`,
// their `plainGoal` fallbacks, diagnostics) as HTML, and the geometry that connects a
// rendered subterm to a source span. No DOM: the page sets `innerHTML` from these
// strings, and the Node test calls the same functions with a stub element.
//
// The markup is the web infoview's (`lib/Tagged.wiz`, `web/infoview.html`): tagged text
// becomes nested `<span class="tt k-KIND" data-ref data-idx>` elements, a goal a
// `.goal` with `.names`, `.turnstile` and the expected type. `web/playground-lsp.js`
// reuses `web/tagged.js`'s `delegate` for hover and keyboard handling, so the panel
// behaves like the infoview's.
//
// **Source spans.** A range becomes `data-span="LINE:CHAR-LINE:CHAR"`, which
// `parseSpan` reads back; a click on any element inside `[data-span]` selects that
// source span in the editor. The server's protocol has ranges on the goal (the tactic
// or `by` block) and, when a server provides them, on a hypothesis (`Hyp.range`) and on
// a tagged subterm (`SubtermTag.range`); a click falls back to the enclosing goal's
// range. `docs/playground-lsp.md` is the contract.
"use strict";

// ## Text, positions and spans

export function escapeHtml(value) {
  return String(value === null || value === undefined ? "" : value)
    .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;").replace(/'/g, "&#39;");
}

const num = (x) => (typeof x === "number" && isFinite(x) ? Math.trunc(x) : 0);

// A JavaScript string index is a UTF-16 code unit index, which is what LSP counts: the
// offset of a position in `text` (0-based line, 0-based character; `\n` ends a line).
export function offsetAt(text, position) {
  if (!text || !position) return 0;
  const line = Math.max(0, num(position.line));
  const character = Math.max(0, num(position.character));
  let offset = 0;
  for (let l = 0; l < line; l++) {
    const newline = text.indexOf("\n", offset);
    if (newline < 0) return text.length;
    offset = newline + 1;
  }
  // `character` counts within its line: a past-the-end character stops at the line
  // break, not at the same column of the next line.
  const newline = text.indexOf("\n", offset);
  const lineEnd = newline < 0 ? text.length : newline;
  return Math.min(lineEnd, offset + character);
}

// The inverse: an LSP position for a JavaScript string index.
export function positionAt(text, offset) {
  const at = Math.max(0, Math.min(text ? text.length : 0, num(offset)));
  const before = text ? text.slice(0, at) : "";
  const line = (before.match(/\n/g) || []).length;
  const character = at - (before.lastIndexOf("\n") + 1);
  return { line, character };
}

// `{start,end}` offsets of a range, clamped to the text and never inverted.
export function rangeOffsets(text, range) {
  const start = offsetAt(text, (range && range.start) || {});
  const end = Math.max(start, offsetAt(text, (range && range.end) || (range && range.start) || {}));
  return { start, end };
}

// A range as the `data-span` attribute (no quotes, so the attribute stays plain).
export function spanText(range) {
  if (!range || !range.start) return null;
  const start = range.start;
  const end = range.end || range.start;
  return `${num(start.line)}:${num(start.character)}-${num(end.line)}:${num(end.character)}`;
}

export function parseSpan(text) {
  const m = /^(\d+):(\d+)-(\d+):(\d+)$/.exec(String(text || ""));
  if (!m) return null;
  return {
    start: { line: Number(m[1]), character: Number(m[2]) },
    end: { line: Number(m[3]), character: Number(m[4]) },
  };
}

const spanAttr = (range) => {
  const span = spanText(range);
  return span === null ? "" : ` data-span="${span}"`;
};

// ## Tagged text (infoview protocol §2)

// The plain printing of tagged text: every `text` in order.
export function plainText(tt) {
  if (tt === null || tt === undefined) return "";
  if (typeof tt === "string") return tt;
  if (Array.isArray(tt)) return tt.map(plainText).join("");
  if (typeof tt.text === "string") return tt.text;
  if (Array.isArray(tt.append)) return tt.append.map(plainText).join("");
  if (Array.isArray(tt.tag)) return plainText(tt.tag[1]);
  return "";
}

const tagKind = (tag) => {
  const kind = tag && typeof tag.kind === "string" ? tag.kind : "other";
  return kind.replace(/[^A-Za-z0-9_-]/g, "") || "other";
};

// Tagged text as the infoview's nested spans. Returns the HTML and the next `data-idx`.
export function taggedToHtml(tt, options = {}) {
  const out = { html: "", next: options.next || 0 };
  walkTagged(tt, out);
  return out;
}

function walkTagged(tt, out) {
  if (tt === null || tt === undefined) return;
  if (typeof tt === "string") { out.html += escapeHtml(tt); return; }
  if (Array.isArray(tt)) { for (const x of tt) walkTagged(x, out); return; }
  if (typeof tt.text === "string") { out.html += escapeHtml(tt.text); return; }
  if (Array.isArray(tt.append)) { for (const x of tt.append) walkTagged(x, out); return; }
  if (Array.isArray(tt.tag)) {
    const tag = tt.tag[0] || {};
    const idx = out.next++;
    const kind = tagKind(tag);
    const title = tag.name ? ` title="${escapeHtml(tag.name)}"` : "";
    const ref = tag.ref !== undefined && tag.ref !== null ? ` data-ref="${escapeHtml(tag.ref)}"` : "";
    out.html += `<span class="tt k-${kind}" data-idx="${idx}"${ref}${title}${spanAttr(tag.range)}>`;
    walkTagged(tt.tag[1], out);
    out.html += "</span>";
    return;
  }
  // Unknown shapes are ignored (a newer server may add fields).
}

// Tagged text as an indented tree: one `<li>` per tag, its printed text as the label,
// its subterms nested. `maxNodes` bounds a pathological term. Returns HTML and the
// number of nodes drawn.
export function taggedTreeHtml(tt, options = {}) {
  const maxNodes = options.maxNodes || 200;
  const budget = { left: maxNodes, next: options.next || 0 };
  const body = treeNode(tt, budget);
  return { html: `<ul class="tree">${body}</ul>`, nodes: maxNodes - budget.left };
}

function treeNode(tt, budget, inner = false) {
  if (budget.left <= 0) return "";
  if (tt === null || tt === undefined) return "";
  if (Array.isArray(tt)) return tt.map((t) => treeNode(t, budget, inner)).join("");
  if (typeof tt.text === "string") {
    // A tag's label already prints its own text; only a top-level append shows text.
    if (inner || !tt.text.trim()) return "";
    budget.left -= 1;
    return `<li class="leaf">${escapeHtml(tt.text)}</li>`;
  }
  if (typeof tt === "string") {
    if (inner || !tt.trim()) return "";
    budget.left -= 1;
    return `<li class="leaf">${escapeHtml(tt)}</li>`;
  }
  if (Array.isArray(tt.append)) return tt.append.map((t) => treeNode(t, budget, inner)).join("");
  if (Array.isArray(tt.tag)) {
    const tag = tt.tag[0] || {};
    const body = tt.tag[1];
    budget.left -= 1;
    const idx = budget.next++;
    const kind = tagKind(tag);
    const text = plainText(body);
    const shown = text.length > 80 ? text.slice(0, 79) + "…" : text;
    const title = escapeHtml((tag.name ? tag.name + " · " : "") + kind + (text.length > 80 ? " · " + text : ""));
    const ref = tag.ref !== undefined && tag.ref !== null ? ` data-ref="${escapeHtml(tag.ref)}"` : "";
    const children = treeNode(body, budget, true);
    const nested = children ? `<ul>${children}</ul>` : "";
    return `<li><span class="tt k-${kind}" data-idx="${idx}"${ref} title="${title}"${spanAttr(tag.range)}>${escapeHtml(shown)}</span>${nested}</li>`;
  }
  return "";
}

// ## Goals, terms and diagnostics

// The session a result belongs to (top level or in a term goal).
export function resultSession(result) {
  if (!result || typeof result !== "object") return null;
  if (typeof result.session === "number") return result.session;
  if (result.goal && typeof result.goal.session === "number") return result.goal.session;
  return null;
}

function hypHtml(hyp, fallback) {
  const names = Array.isArray(hyp.names) ? hyp.names : (hyp.names ? [hyp.names] : []);
  const span = hyp.range || fallback;
  const namesHtml = names.map((name) =>
    `<span class="names"${spanAttr(hyp.range || span)} title="${escapeHtml(name)}">${escapeHtml(name)}</span>`
  ).join(" ");
  const type = hyp.type === null || hyp.type === undefined
    ? "" : (typeof hyp.type === "string" ? escapeHtml(hyp.type) : taggedToHtml(hyp.type).html);
  const value = hyp.val === null || hyp.val === undefined
    ? "" : " := " + (typeof hyp.val === "string" ? escapeHtml(hyp.val) : taggedToHtml(hyp.val).html);
  return `<div class="hyp"${spanAttr(span)}>${namesHtml} : ${type}${value}</div>`;
}

// One interactive goal (`wiz/interactiveGoals` / `wiz/interactiveTermGoal` shape).
export function interactiveGoalHtml(goal, fallbackRange) {
  if (!goal || typeof goal !== "object") return "";
  const span = goal.range || fallbackRange;
  const hyps = Array.isArray(goal.hyps) ? goal.hyps.map((h) => hypHtml(h, span)).join("") : "";
  const prefix = typeof goal.goalPrefix === "string" && goal.goalPrefix ? goal.goalPrefix : "⊢ ";
  const type = goal.type === null || goal.type === undefined
    ? "" : (typeof goal.type === "string" ? escapeHtml(goal.type) : taggedToHtml(goal.type).html);
  const name = typeof goal.userName === "string" && goal.userName
    ? `<div class="case">case <span class="names"${spanAttr(span)}>${escapeHtml(goal.userName)}</span></div>` : "";
  return `<div class="goal"${spanAttr(span)}>${name}<div class="hyps">${hyps}</div>` +
    `<div class="target"><span class="turnstile">${escapeHtml(prefix)}</span>${type}</div></div>`;
}

// `wiz/plainGoal`'s text (Markdown with a ```wiz fence), as the goals it shows.
export function plainGoals(result) {
  if (!result) return [];
  if (Array.isArray(result.goals) && result.goals.every((g) => typeof g === "string")) return result.goals;
  const rendered = typeof result.rendered === "string" ? result.rendered : "";
  const fenced = /```[A-Za-z]*\n([\s\S]*?)\n?```/.exec(rendered);
  const text = fenced ? fenced[1] : rendered;
  if (!text.trim() || text.trim() === "no goals") return [];
  return text.split(/\n\s*\n/).map((g) => g.trim()).filter((g) => g !== "");
}

function messagesHtml(messages) {
  if (!Array.isArray(messages) || messages.length === 0) return "";
  return `<div class="messages"><h4>messages</h4>${messages.map((m) =>
    `<pre class="message">${escapeHtml(m)}</pre>`).join("")}</div>`;
}

// Render a goals result: `"interactive"` (`{goals: [InteractiveGoal], range, …}`) or
// `"plain"` (`{goals: [string], rendered, …}`). `null` is "nothing at the cursor".
export function renderGoalResult(result, kind) {
  if (kind === "plain") {
    const goals = plainGoals(result);
    if (!goals.length) {
      return result ? `<div class="no-goals">no goals</div>` : `<div class="nothing">nothing at the cursor</div>`;
    }
    const block = goals.map((g) =>
      `<div class="goal plain"${spanAttr(result && result.range)}><pre>${escapeHtml(g)}</pre></div>`).join("");
    return block + messagesHtml(result && result.messages);
  }
  if (!result) return `<div class="nothing">nothing at the cursor</div>`;
  const goals = Array.isArray(result.goals) ? result.goals : [];
  const html = goals.length === 0
    ? `<div class="no-goals">no goals</div>`
    : goals.map((g) => interactiveGoalHtml(g, result.range)).join("");
  const tree = result.tree || result.term;
  const withTree = tree && typeof tree === "object"
    ? treeSection(tree) : "";
  return html + withTree + messagesHtml(result.messages);
}

// An optional tagged `tree`/`term` in a goals result: the term or syntax at the cursor.
function treeSection(tree) {
  const drawn = taggedTreeHtml(tree);
  if (drawn.nodes <= 1) return "";
  return `<details class="tree-wrap"><summary>term tree</summary>${drawn.html}</details>`;
}

// The expected type: `wiz/interactiveTermGoal` (`{goal, range}`), `plainTermGoal`
// (`{goal: string, range}`), or a bare interactive goal. A tagged expected type also
// gives the term tree (inside a `<details>`); plain text has none.
export function renderTermResult(result, kind) {
  if (!result) return `<div class="nothing">nothing at the cursor</div>`;
  if (kind === "plain" || typeof result.goal === "string") {
    const text = typeof result.goal === "string" ? result.goal : plainText(result.goal);
    return `<div class="goal plain"${spanAttr(result.range)}><pre>${escapeHtml(text)}</pre></div>`;
  }
  const goal = result.goal || result;
  const html = interactiveGoalHtml(goal, result.range);
  const tree = result.tree || (goal && goal.type && typeof goal.type === "object" ? goal.type : null);
  return html + (tree ? treeSection(tree) : "");
}

const SEVERITY = { 1: "error", 2: "warning", 3: "info", 4: "hint" };

export function renderDiagnostics(diagnostics) {
  const list = Array.isArray(diagnostics) ? diagnostics : [];
  if (list.length === 0) return `<div class="nothing">no diagnostics</div>`;
  return `<div class="diags">${list.map((d) => {
    const sev = SEVERITY[d.severity] || "info";
    const where = d.range && d.range.start ? `${num(d.range.start.line) + 1}:${num(d.range.start.character) + 1}` : "";
    const text = d.message === undefined ? "" : d.message;
    const title = d.source ? ` title="${escapeHtml(d.source)}${d.code !== undefined ? " " + escapeHtml(d.code) : ""}"` : "";
    return `<div class="diag sev-${sev}"${spanAttr(d.range)}${title}><span class="sev">${sev}</span>` +
      `<span class="msg">${escapeHtml(text)}</span><span class="where">${where}</span></div>`;
  }).join("")}</div>`;
}

// What the cursor selects (an optional `wiz/subtermInfo` answer).
export function renderSelection(info) {
  if (!info || typeof info !== "object") return "";
  const name = info.name || info.text || "";
  const type = info.type === null || info.type === undefined
    ? "" : " : " + (typeof info.type === "string" ? escapeHtml(info.type) : taggedToHtml(info.type).html);
  const kind = info.kind ? ` <span class="kind">${escapeHtml(info.kind)}</span>` : "";
  const definition = info.definition && info.definition.uri
    ? ` <span class="def">${escapeHtml(info.definition.uri)}</span>` : "";
  return `<div class="selection"><span class="names">${escapeHtml(name)}</span>${kind}${type}${definition}</div>`;
}

function statusHtml(view) {
  const state = view.state || "no-server";
  if (state === "open") {
    const server = view.serverInfo && view.serverInfo.name
      ? ` · ${escapeHtml(view.serverInfo.name)}${view.serverInfo.version ? " " + escapeHtml(view.serverInfo.version) : ""}`
      : "";
    const tag = view.infoview ? ` · wiz infoview v${escapeHtml(view.infoview.version)}` : "";
    const where = view.endpoint ? ` to ${escapeHtml(view.endpoint)}` : "";
    return `<div class="lsp-status ok"><span class="dot"></span>connected${where}${server}${tag}</div>`;
  }
  if (state === "connecting") {
    return `<div class="lsp-status running"><span class="dot"></span>connecting to ${escapeHtml(view.endpoint || "the language server")}…</div>`;
  }
  if (state === "closed") {
    return `<div class="lsp-status bad"><span class="dot"></span>the language server disconnected` +
      (view.endpoint ? ` (${escapeHtml(view.endpoint)})` : "") + `</div>`;
  }
  return `<div class="lsp-status idle"><span class="dot"></span>no language server</div>`;
}

function hintHtml(view) {
  const state = view.state || "no-server";
  const reason = view.message ? `<p class="lsp-reason">${escapeHtml(view.message)}</p>` : "";
  const retry = view.canReconnect && (state === "closed" || state === "failed")
    ? `<p class="lsp-actions"><button type="button" data-action="reconnect">reconnect</button></p>` : "";
  if (state === "open") return reason ? reason + retry : "";
  if (state === "connecting") return reason;
  const start = state === "closed" ? "Start it again" : "Start it";
  return `${reason}<p class="lsp-hint">The playground evaluates locally; goals need a language server. ` +
    `${start} with <code>wiz lsp --ws 8765 --no-stdio</code> and open this page with ` +
    `<code>?lsp=ws://127.0.0.1:8765</code>.</p>${retry}`;
}

// Render the whole panel. `view` is the page's model:
//   {state, endpoint, serverInfo, infoview, message, diagnostics, goals, goalsKind,
//    term, termKind, info, position}
// A stub `{innerHTML}` is enough (the Node test uses one).
export function renderPanel(element, view) {
  if (!element) return;
  const state = view.state || "no-server";
  const open = state === "open";
  const parts = [`<div class="lsp-view" data-state="${escapeHtml(state)}">`, statusHtml(view), hintHtml(view)];
  if (open) {
    parts.push(`<h3>Goals</h3>`);
    parts.push(view.goalsKind
      ? renderGoalResult(view.goals, view.goalsKind)
      : `<div class="nothing">asking the server…</div>`);
    parts.push(`<h3>Expected type</h3>`);
    parts.push(view.termKind
      ? renderTermResult(view.term, view.termKind)
      : `<div class="nothing">asking the server…</div>`);
    if (view.info) parts.push(`<h3>Selected subterm</h3>`, renderSelection(view.info));
    parts.push(`<h3>Diagnostics</h3>`, renderDiagnostics(view.diagnostics));
  }
  parts.push("</div>");
  element.innerHTML = parts.join("");
}

// ## Reading both goal shapes from a server, with the fallback ladder

// Ask for goals and the expected type. `wiz/interactiveGoals`/`wiz/interactiveTermGoal`
// are preferred (they carry tagged text); any failure falls back to
// `wiz/plainGoal`/`wiz/plainTermGoal`, which every Wiz server has. The result is
// `{goals, goalsKind, term, termKind, session, errors}`; nothing throws, so the page
// never sees an unhandled rejection.
export async function readGoalState(client, uri, position) {
  const out = { goals: null, goalsKind: null, term: null, termKind: null, session: null, errors: [] };
  if (!client || client.state !== "open") {
    out.errors.push("not connected");
    return out;
  }
  try {
    out.goals = await client.interactiveGoals(uri, position);
    out.goalsKind = "interactive";
  } catch (e) {
    out.errors.push("wiz/interactiveGoals: " + (e && e.message ? e.message : e));
    try {
      out.goals = await client.plainGoal(uri, position);
      out.goalsKind = "plain";
      out.errors = [];
    } catch (e2) {
      out.errors.push("wiz/plainGoal: " + (e2 && e2.message ? e2.message : e2));
    }
  }
  const session = resultSession(out.goals);
  if (session !== null) out.session = session;
  try {
    out.term = await client.interactiveTermGoal(uri, position);
    out.termKind = "interactive";
  } catch (e) {
    out.errors.push("wiz/interactiveTermGoal: " + (e && e.message ? e.message : e));
    try {
      out.term = await client.plainTermGoal(uri, position);
      out.termKind = "plain";
    } catch (e2) {
      out.errors.push("wiz/plainTermGoal: " + (e2 && e2.message ? e2.message : e2));
    }
  }
  const termSession = resultSession(out.term);
  if (termSession !== null && out.session === null) out.session = termSession;
  return out;
}
