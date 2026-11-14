// The infoview: a Webview beside the editor that follows the cursor and shows the
// tactic state (wiz/interactiveGoals), the expected type (wiz/interactiveTermGoal) and
// everything else at the cursor (wiz/interactiveInfo) as tagged text. Clicking a
// subterm asks wiz/subtermInfo; clicking an info item's title goes to its location.
// Protocol: wiz-notes/infoview-protocol.md.
import * as crypto from 'node:crypto';
import * as path from 'node:path';
import * as vscode from 'vscode';
import type { LanguageClient } from 'vscode-languageclient/node';
import type { WizSettings } from './root';
import * as proto from './protocol';

export interface InfoviewHost {
  clientFor(uri: vscode.Uri): Promise<LanguageClient | undefined>;
  settings(): WizSettings;
  debounce(): number;
  followCursor(): boolean;
  autoOpen(): boolean;
}

type Source = {
  uri: vscode.Uri;
  lsp: proto.Position;
  vscode: vscode.Position;
  document: vscode.TextDocument;
};

interface Result<T> {
  value?: T;
  error?: unknown;
}

function esc(s: string): string {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function attr(s: string): string {
  return esc(s);
}

/** A LSP position from a VS Code position: the server counts Unicode characters, not
 * UTF-16 units (protocol §0), so an astral character is one column, not two. */
function lspPosition(doc: vscode.TextDocument, position: vscode.Position): proto.Position {
  if (position.line >= doc.lineCount) {
    return { line: position.line, character: 0 };
  }
  const line = doc.lineAt(position.line).text;
  const prefix = line.slice(0, position.character);
  return { line: position.line, character: [...prefix].length };
}

/** The inverse: a LSP position to a VS Code position with UTF-16 columns. */
function vscodePosition(doc: vscode.TextDocument, position: proto.Position): vscode.Position {
  if (position.line >= doc.lineCount) {
    return new vscode.Position(Math.max(0, doc.lineCount - 1), 0);
  }
  const chars = [...doc.lineAt(position.line).text];
  return new vscode.Position(position.line, chars.slice(0, position.character).join('').length);
}

function tagged(tt: proto.TaggedText | null | undefined): string {
  if (!tt || typeof tt !== 'object') {
    return '';
  }
  if ('text' in tt) {
    return esc(tt.text ?? '');
  }
  if ('append' in tt && Array.isArray(tt.append)) {
    return tt.append.map(tagged).join('');
  }
  if ('tag' in tt && Array.isArray(tt.tag)) {
    const [info, body] = tt.tag;
    const kind = info?.kind ?? 'other';
    const title = info?.name ? ` title="${attr(info.name)}"` : '';
    return `<span class="tag k-${attr(kind)}" data-ref="${info?.ref ?? 0}"${title}>${tagged(body)}</span>`;
  }
  return '';
}

function goalHtml(g: proto.InteractiveGoal): string {
  const out: string[] = ['<div class="goal">'];
  if (g.userName) {
    out.push(`<div class="case">case ${esc(g.userName)}</div>`);
  }
  for (const h of g.hyps ?? []) {
    const value = h.val ? ` := ${tagged(h.val)}` : '';
    out.push(
      `<div class="hyp"><span class="names">${esc((h.names ?? []).join(' '))}</span> : ${tagged(h.type)}${value}</div>`,
    );
  }
  out.push(
    `<div class="goaltype"><span class="turnstile">${esc(g.goalPrefix ?? '⊢ ')}</span>${tagged(g.type)}</div>`,
  );
  out.push('</div>');
  return out.join('');
}

function section(title: string): string {
  return `<div class="section">${esc(title)}</div>`;
}

function sectionTitle(kind: proto.InfoKind): string {
  switch (kind) {
    case 'syntax':
    case 'expansion':
      return 'Syntax';
    case 'import':
      return 'Import';
    case 'instance':
      return 'Instances';
    case 'declaration':
      return 'Declarations';
    case 'message':
      return 'Messages';
    default:
      return 'Info';
  }
}

function link(loc: proto.Location | null | undefined, text: string): string {
  if (!loc?.uri) {
    return text;
  }
  return (
    `<a href="#" data-goto-uri="${attr(loc.uri)}"` +
    ` data-goto-line="${loc.range.start.line}" data-goto-char="${loc.range.start.character}">${text}</a>`
  );
}

function itemHtml(it: proto.InfoItem): string {
  const title = link(it.location ?? undefined, esc(it.title ?? ''));
  if (it.kind === 'declaration') {
    const type = it.type ? ` : ${tagged(it.type)}` : '';
    return `<div class="item"><span class="decl">${title}</span>${type}</div>`;
  }
  if (it.kind === 'instance') {
    const text = esc(it.text ?? '?');
    const type = it.type ? ` : ${tagged(it.type)}` : '';
    return `<div class="item"><span class="decl">${text}</span>${type}</div>`;
  }
  const text = it.text
    ? it.text
        .split('\n')
        .map((line) => `<div class="indent">${esc(line)}</div>`)
        .join('')
    : '';
  return `<div class="item${it.kind === 'message' ? ' muted' : ''}"><div>${title}</div>${text}</div>`;
}

function widgetHtml(w: proto.Widget): string {
  // The server sanitises the HTML (no scripts, event handlers or javascript: URLs), but
  // it is still untrusted: the sandbox is the boundary.
  return (
    `<details class="widget"><summary>${esc(w.title)}</summary>` +
    `<iframe sandbox="" srcdoc="${attr(w.html ?? '')}"></iframe></details>`
  );
}

function detailHtml(info: proto.SubtermInfo): string {
  const type = info.type ? ` : ${tagged(info.type)}` : '';
  const name = info.name ? ` ${esc(info.name)}` : '';
  const where = info.definition
    ? `<div>${link(info.definition, `defined in ${esc(path.basename(info.definition.uri))}:${info.definition.range.start.line + 1}`)}</div>`
    : '';
  return (
    `<div class="detailtext">${esc(info.text)}${type}</div>` +
    `<div class="muted">-- ${esc(info.kind)}${name}</div>${where}`
  );
}

export class WizInfoview implements vscode.Disposable {
  private panel: vscode.WebviewPanel | undefined;
  private nonce = '';
  private source: Source | undefined;
  private session: number | undefined;
  private timer: ReturnType<typeof setTimeout> | undefined;
  private requestId = 0;
  private disposed = false;
  private readonly disposables: vscode.Disposable[] = [];

  constructor(private readonly host: InfoviewHost) {
    this.disposables.push(
      vscode.window.onDidChangeTextEditorSelection((event) => {
        if (!this.host.followCursor()) {
          return;
        }
        if (event.textEditor.document.languageId === 'wiz' && this.panel?.visible) {
          this.schedule();
        }
      }),
    );
    this.disposables.push(
      vscode.workspace.onDidChangeTextDocument((event) => {
        if (event.document.languageId !== 'wiz' || !this.panel?.visible) {
          return;
        }
        if (vscode.window.activeTextEditor?.document === event.document) {
          this.schedule(250);
        }
      }),
    );
  }

  /** Open the infoview, or reveal it if it is already open. */
  show(): void {
    if (this.disposed) {
      return;
    }
    if (!this.panel) {
      this.nonce = crypto.randomBytes(16).toString('base64');
      this.panel = vscode.window.createWebviewPanel(
        'wiz.infoview',
        'Wiz Infoview',
        { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
        {
          enableScripts: true,
          retainContextWhenHidden: true,
          localResourceRoots: [],
        },
      );
      this.panel.webview.html = this.shell();
      this.panel.onDidDispose(() => {
        this.panel = undefined;
        this.setVisibleContext(false);
      });
      this.panel.webview.onDidReceiveMessage((message) => this.onMessage(message));
      this.panel.onDidChangeViewState((event) => {
        if (event.webviewPanel.visible) {
          this.setVisibleContext(true);
          this.update(true);
        }
      });
    }
    this.panel.reveal(undefined, true);
    this.setVisibleContext(true);
    this.update(true);
  }

  /** Open the infoview the first time a Wiz file is shown, if configured. */
  maybeAutoOpen(): void {
    if (this.panel || this.disposed) {
      return;
    }
    if (this.host.autoOpen() && vscode.window.activeTextEditor?.document.languageId === 'wiz') {
      this.show();
    }
  }

  visible(): boolean {
    return !!this.panel?.visible;
  }

  /** The server re-elaborated a document (`wiz/elaborated`). */
  onElaborated(params: proto.ElaboratedParams): void {
    if (!this.panel?.visible || !this.source) {
      return;
    }
    if (params.uri === this.source.uri.toString()) {
      this.schedule(40);
    }
  }

  schedule(delay = this.host.debounce()): void {
    if (this.timer) {
      clearTimeout(this.timer);
    }
    this.timer = setTimeout(() => {
      this.timer = undefined;
      void this.update(true);
    }, delay);
  }

  async update(force = false): Promise<void> {
    const panel = this.panel;
    if (!panel || this.disposed) {
      return;
    }

    const editor = vscode.window.activeTextEditor;
    let source: Source | undefined;
    if (editor?.document.languageId === 'wiz') {
      const lsp = lspPosition(editor.document, editor.selection.active);
      source = {
        uri: editor.document.uri,
        lsp,
        vscode: editor.selection.active,
        document: editor.document,
      };
    } else if (this.source) {
      const document =
        this.source.document.isClosed === false
          ? this.source.document
          : vscode.workspace.textDocuments.find(
              (doc) => doc.uri.toString() === this.source?.uri.toString(),
            );
      if (document) {
        source = {
          uri: document.uri,
          lsp: this.source.lsp,
          vscode: this.source.vscode,
          document,
        };
      }
    }
    if (!source) {
      await panel.webview.postMessage({ type: 'content', where: '', html: '<div class="muted">Open a Wiz file.</div>' });
      return;
    }
    const previous = this.source;
    if (
      !force &&
      previous &&
      previous.uri.toString() === source.uri.toString() &&
      previous.lsp.line === source.lsp.line &&
      previous.lsp.character === source.lsp.character
    ) {
      return;
    }
    this.source = source;

    const client = await this.host.clientFor(source.uri);
    if (!client) {
      await panel.webview.postMessage({
        type: 'content',
        where: '',
        html: '<div class="error">No Wiz language server for this file (is <code>wiz</code> on PATH?).</div>',
      });
      return;
    }

    const id = ++this.requestId;
    const params = { textDocument: { uri: source.uri.toString() }, position: source.lsp };
    const safe = async <T>(method: string): Promise<Result<T>> => {
      try {
        return { value: await client.sendRequest<T>(method, params) };
      } catch (error) {
        return { error };
      }
    };
    const [goalsResult, termResult, infoResult] = await Promise.all([
      safe<proto.GoalsResult | null>('wiz/interactiveGoals'),
      safe<proto.TermGoalResult | null>('wiz/interactiveTermGoal'),
      safe<proto.InfoResult | null>('wiz/interactiveInfo'),
    ]);
    if (id !== this.requestId || this.disposed) {
      return;
    }

    const goals = goalsResult.value ?? undefined;
    const term = termResult.value ?? undefined;
    const info = infoResult.value ?? undefined;
    this.session = goals?.session ?? term?.session ?? info?.session ?? this.session;

    const error = !goals && !term?.goal ? (goalsResult.error ?? termResult.error) : undefined;
    const where = `${path.basename(source.uri.fsPath)}:${source.lsp.line + 1}:${source.lsp.character + 1}`;
    await panel.webview.postMessage({
      type: 'content',
      where,
      html: this.render(goals, term, info, error),
    });
  }

  private render(
    goals: proto.GoalsResult | undefined,
    term: proto.TermGoalResult | undefined,
    info: proto.InfoResult | undefined,
    error: unknown,
  ): string {
    if (error) {
      const message = (error as { message?: string })?.message ?? String(error);
      return `<div class="error">${esc(message)}</div>`;
    }
    const parts: string[] = [];
    if (goals) {
      parts.push(section('Tactic state'));
      const list = goals.goals ?? [];
      if (list.length === 0) {
        parts.push('<div class="nog">No goals</div>');
      } else {
        parts.push(`<div class="muted">${list.length === 1 ? '1 goal' : `${list.length} goals`}</div>`);
        parts.push(list.map(goalHtml).join(''));
      }
      if (goals.messages?.length) {
        parts.push(section('Messages'));
        parts.push(goals.messages.map((m) => `<pre class="msg">${esc(m)}</pre>`).join(''));
      }
      if (goals.widgets?.length) {
        parts.push(section('Widgets'));
        parts.push(goals.widgets.map(widgetHtml).join(''));
      }
    }
    if (term?.goal) {
      parts.push(section('Expected type'));
      parts.push(goalHtml(term.goal));
    }
    if (info?.items?.length) {
      let current: string | undefined;
      for (const item of info.items) {
        const title = sectionTitle(item.kind);
        if (title !== current) {
          parts.push(section(title));
          current = title;
        }
        parts.push(itemHtml(item));
      }
    }
    if (!goals && !term?.goal && !info?.items?.length) {
      parts.push('<div class="muted">No info.</div>');
    }
    return parts.join('\n');
  }

  private async onMessage(message: { type?: string; ref?: number; uri?: string; line?: number; character?: number; message?: string }): Promise<void> {
    switch (message.type) {
      case 'refresh':
        await this.update(true);
        return;
      case 'inspect':
        if (typeof message.ref === 'number') {
          await this.inspect(message.ref);
        }
        return;
      case 'goto':
        if (message.uri !== undefined && message.line !== undefined && message.character !== undefined) {
          await this.goto(message.uri, message.line, message.character);
        }
        return;
      default:
        return;
    }
  }

  private async inspect(ref: number): Promise<void> {
    const source = this.source;
    if (!source || this.session === undefined) {
      return;
    }
    const client = await this.host.clientFor(source.uri);
    if (!client) {
      return;
    }
    try {
      const info = await client.sendRequest<proto.SubtermInfo>('wiz/subtermInfo', {
        textDocument: { uri: source.uri.toString() },
        session: this.session,
        ref,
      });
      if (!this.disposed && info) {
        await this.panel?.webview.postMessage({ type: 'detail', html: detailHtml(info) });
      }
    } catch (error) {
      const code = (error as { code?: number })?.code;
      if (code === -32801) {
        // The document changed: the refs are stale. Ask again for the state.
        await this.update(true);
        return;
      }
      const message = (error as { message?: string })?.message ?? String(error);
      await this.panel?.webview.postMessage({ type: 'detailError', message });
    }
  }

  private async goto(uri: string, line: number, character: number): Promise<void> {
    const parsed = vscode.Uri.parse(uri);
    const document = await vscode.workspace.openTextDocument(parsed);
    const position = vscodePosition(document, { line, character });
    const editor = await vscode.window.showTextDocument(document, {
      preview: false,
      viewColumn: vscode.ViewColumn.One,
    });
    editor.selection = new vscode.Selection(position, position);
    editor.revealRange(
      new vscode.Range(position, position),
      vscode.TextEditorRevealType.InCenterIfOutsideViewport,
    );
  }

  private async setVisibleContext(visible: boolean): Promise<void> {
    await vscode.commands.executeCommand('setContext', 'wiz.infoviewVisible', visible);
  }

  private shell(): string {
    const nonce = this.nonce;
    const csp = [
      "default-src 'none'",
      "style-src 'unsafe-inline'",
      `script-src 'nonce-${nonce}'`,
      "frame-src 'self' data:",
    ].join('; ');
    return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta http-equiv="Content-Security-Policy" content="${csp}">
<style>
  body { font-family: var(--vscode-editor-font-family); font-size: var(--vscode-editor-font-size); color: var(--vscode-editor-foreground); padding: 0 0.8em 1em; }
  header { display: flex; align-items: center; justify-content: space-between; padding: 0.4em 0; position: sticky; top: 0; background: var(--vscode-editor-background); }
  header .title { font-weight: 600; }
  button { background: var(--vscode-button-background); color: var(--vscode-button-foreground); border: 0; padding: 0.2em 0.7em; cursor: pointer; }
  #where { color: var(--vscode-descriptionForeground); margin-bottom: 0.4em; }
  .section { font-weight: 600; margin: 0.9em 0 0.25em; }
  .muted { color: var(--vscode-descriptionForeground); }
  .goal { border-left: 2px solid var(--vscode-editorIndentGuide-activeBackground); padding-left: 0.6em; margin: 0.35em 0; white-space: pre-wrap; }
  .case { color: var(--vscode-symbolIcon-classForeground); }
  .hyp .names { color: var(--vscode-symbolIcon-variableForeground); }
  .turnstile { color: var(--vscode-symbolIcon-operatorForeground); }
  .tag { border-radius: 2px; }
  .tag:hover { background: var(--vscode-editor-hoverHighlightBackground); }
  .k-const, .k-data { color: var(--vscode-symbolIcon-functionForeground); }
  .k-var { color: var(--vscode-symbolIcon-variableForeground); }
  .k-sort { color: var(--vscode-symbolIcon-typeParameterForeground); }
  .k-lit { color: var(--vscode-symbolIcon-numberForeground); }
  .item { margin: 0.15em 0; white-space: pre-wrap; }
  .item .decl { color: var(--vscode-symbolIcon-fieldForeground); }
  .indent { margin-left: 1.2em; }
  .msg { margin: 0.2em 0 0.2em 1.2em; white-space: pre-wrap; }
  a { color: var(--vscode-textLink-foreground); cursor: pointer; text-decoration: none; }
  a:hover { text-decoration: underline; }
  .nog { color: var(--vscode-testing-iconPassed); }
  .error { color: var(--vscode-errorForeground); white-space: pre-wrap; }
  .widget iframe { width: 100%; min-height: 80px; border: 1px solid var(--vscode-editorWidget-border); background: var(--vscode-editor-background); }
  #detail { position: sticky; bottom: 0; margin-top: 1em; padding: 0.5em; border-top: 1px solid var(--vscode-editorWidget-border); background: var(--vscode-editorWidget-background); white-space: pre-wrap; }
  #detail[hidden] { display: none; }
</style>
</head>
<body>
<header><span class="title">Wiz Infoview</span><button id="refresh" title="Ask the server again">Refresh</button></header>
<div id="where"></div>
<div id="content"><div class="muted">Open a Wiz file.</div></div>
<div id="detail" hidden></div>
<script nonce="${nonce}">
  const vscode = acquireVsCodeApi();
  const content = document.getElementById('content');
  const where = document.getElementById('where');
  const detail = document.getElementById('detail');
  document.getElementById('refresh').addEventListener('click', () => vscode.postMessage({ type: 'refresh' }));
  document.addEventListener('click', (event) => {
    const target = event.target instanceof Element ? event.target : event.target.parentElement;
    if (!target) return;
    const tag = target.closest('[data-ref]');
    if (tag) {
      event.preventDefault();
      vscode.postMessage({ type: 'inspect', ref: Number(tag.getAttribute('data-ref')) });
      return;
    }
    const link = target.closest('[data-goto-uri]');
    if (link) {
      event.preventDefault();
      vscode.postMessage({
        type: 'goto',
        uri: link.getAttribute('data-goto-uri'),
        line: Number(link.getAttribute('data-goto-line')),
        character: Number(link.getAttribute('data-goto-char')),
      });
    }
  });
  window.addEventListener('message', (event) => {
    const message = event.data;
    if (message.type === 'content') {
      where.textContent = message.where || '';
      content.innerHTML = message.html || '';
      detail.hidden = true;
      detail.innerHTML = '';
    } else if (message.type === 'detail') {
      detail.hidden = false;
      detail.innerHTML = message.html || '';
    } else if (message.type === 'detailError') {
      detail.hidden = false;
      detail.textContent = message.message || 'subtermInfo failed';
    }
  });
</script>
</body>
</html>`;
  }

  dispose(): void {
    this.disposed = true;
    if (this.timer) {
      clearTimeout(this.timer);
      this.timer = undefined;
    }
    for (const disposable of this.disposables) {
      disposable.dispose();
    }
    this.panel?.dispose();
    this.panel = undefined;
  }
}
