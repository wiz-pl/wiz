// The VS Code client: one language server per project root (or per installed
// toolchain's library), started exactly as editors/nvim does: `wiz lsp` rooted at the
// nearest grail.wiz / wiz-toolchain / lakefile.toml / .git, `grail lsp -C ROOT` in a
// grail package, and an installed toolchain's own `wiz lsp` for its lib/ files.
import * as path from 'node:path';
import * as vscode from 'vscode';
import {
  InitializeParams,
  LanguageClient,
  LanguageClientOptions,
  RelativePattern as ProtocolRelativePattern,
  ServerOptions,
} from 'vscode-languageclient/node';
import { WizInfoview } from './infoview';
import {
  defaultSettings,
  LaunchSpec,
  launchForFile,
  nodeProbe,
  WizSettings,
} from './root';
import type * as proto from './protocol';

interface Entry {
  client: LanguageClient;
  spec: LaunchSpec;
  output: vscode.LogOutputChannel;
}

/** A LanguageClient that also asks for the `wiz/elaborated` notification. A plain
 * LanguageClientOptions has no capabilities field, so the request is added to the
 * initialize params. */
class WizLanguageClient extends LanguageClient {
  protected override fillInitializeParams(params: InitializeParams): void {
    super.fillInitializeParams(params);
    const capabilities = params.capabilities as typeof params.capabilities & {
      experimental?: Record<string, unknown>;
    };
    capabilities.experimental = {
      ...(capabilities.experimental ?? {}),
      wizElaborated: true,
    };
  }
}

function readSettings(): WizSettings {
  const config = vscode.workspace.getConfiguration('wiz');
  const defaults = defaultSettings();
  return {
    wizPath: config.get<string>('server.path', defaults.wizPath),
    wizArgs: config.get<string[]>('server.args', defaults.wizArgs),
    grailPath: config.get<string>('grail.path', defaults.grailPath),
    grailArgs: config.get<string[]>('grail.args', defaults.grailArgs),
    grailEnabled: config.get<boolean>('grail.enabled', defaults.grailEnabled),
    toolchains: config.get<boolean>('toolchains.enabled', defaults.toolchains),
    rootMarkers: config.get<string[]>('rootMarkers', defaults.rootMarkers),
  };
}

function shellQuote(value: string): string {
  if (process.platform === 'win32') {
    return /^[A-Za-z0-9_@%+=:,./\\-]+$/.test(value) ? value : `"${value.replace(/"/g, '""')}"`;
  }
  if (/^[A-Za-z0-9_@%+=:,./-]+$/.test(value)) {
    return value;
  }
  return `'${value.replace(/'/g, `'\\''`)}'`;
}

function activeWizEditor(): vscode.TextEditor | undefined {
  const editor = vscode.window.activeTextEditor;
  return editor?.document.languageId === 'wiz' ? editor : undefined;
}

async function runInTerminal(name: string, cwd: string, command: string, args: string[]): Promise<void> {
  const terminal = vscode.window.createTerminal({ name, cwd });
  terminal.show(true);
  terminal.sendText([command, ...args].map(shellQuote).join(' '));
}

class ClientManager implements vscode.Disposable {
  private readonly entries = new Map<string, Entry>();
  private readonly pending = new Map<string, Promise<Entry | undefined>>();
  private readonly warned = new Set<string>();
  private readonly probe = nodeProbe();
  private infoview: WizInfoview | undefined;
  private disposed = false;

  attachInfoview(infoview: WizInfoview): void {
    this.infoview = infoview;
  }

  settings(): WizSettings {
    return readSettings();
  }

  debounce(): number {
    return vscode.workspace.getConfiguration('wiz').get<number>('infoview.debounce', 150);
  }

  followCursor(): boolean {
    return vscode.workspace.getConfiguration('wiz').get<boolean>('infoview.followCursor', true);
  }

  autoOpen(): boolean {
    return vscode.workspace.getConfiguration('wiz').get<boolean>('infoview.autoOpen', true);
  }

  /** The client for a document's root, starting it if this is the first file there. */
  async clientFor(uri: vscode.Uri): Promise<LanguageClient | undefined> {
    if (this.disposed || uri.scheme !== 'file') {
      return undefined;
    }
    const spec = launchForFile(uri.fsPath, this.settings(), this.probe);
    const key = [spec.kind, spec.cwd, spec.command, ...spec.args].join('\u0000');
    const existing = this.entries.get(key);
    if (existing) {
      return existing.client;
    }
    const inFlight = this.pending.get(key);
    if (inFlight) {
      return (await inFlight)?.client;
    }
    const starting = this.start(key, spec);
    this.pending.set(key, starting);
    try {
      return (await starting)?.client;
    } finally {
      this.pending.delete(key);
    }
  }

  private async start(key: string, spec: LaunchSpec): Promise<Entry | undefined> {
    const label = path.basename(spec.root) || spec.root;
    const output = vscode.window.createOutputChannel(`Wiz (${label})`, { log: true });
    output.appendLine(`[wiz] ${spec.kind}: ${spec.command} ${spec.args.join(' ')}`);
    output.appendLine(`[wiz] root ${spec.root}`);
    for (const warning of spec.warnings) {
      if (!this.warned.has(warning)) {
        this.warned.add(warning);
        void vscode.window.showWarningMessage(warning);
      }
    }

    const serverOptions: ServerOptions = {
      command: spec.command,
      args: spec.args,
      options: { cwd: spec.cwd, env: process.env },
    };
    // Scope the client to its own root: one server per root, and a file of a
    // sibling root is not sent to this one.
    const selectorPattern: ProtocolRelativePattern = {
      baseUri: vscode.Uri.file(spec.root).toString(),
      pattern: '**/*.wiz',
    };
    const watchPattern = new vscode.RelativePattern(vscode.Uri.file(spec.root), '**/*.wiz');
    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ scheme: 'file', language: 'wiz', pattern: selectorPattern }],
      outputChannel: output,
      traceOutputChannel: output,
      synchronize: {
        fileEvents: vscode.workspace.createFileSystemWatcher(watchPattern),
      },
    };
    const client = new WizLanguageClient(
      `wiz:${spec.cwd}`,
      `Wiz (${label})`,
      serverOptions,
      clientOptions,
    );
    client.onNotification('wiz/elaborated', (params: proto.ElaboratedParams) => {
      this.infoview?.onElaborated(params);
    });

    try {
      await client.start();
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      output.appendLine(`[wiz] failed to start: ${message}`);
      output.show(true);
      void vscode.window.showErrorMessage(`Wiz: could not start ${spec.command}: ${message}`);
      output.dispose();
      return undefined;
    }
    const entry = { client, spec, output };
    this.entries.set(key, entry);
    return entry;
  }

  async restartAll(): Promise<void> {
    const entries = [...this.entries.values()];
    this.entries.clear();
    this.pending.clear();
    await Promise.all(
      entries.map(async (entry) => {
        try {
          await entry.client.stop();
        } catch {
          // The process is gone already.
        }
        entry.output.dispose();
      }),
    );
    const documents = vscode.workspace.textDocuments.filter((doc) => doc.languageId === 'wiz');
    for (const doc of documents) {
      await this.clientFor(doc.uri);
    }
  }

  showLog(): void {
    const first = this.entries.values().next().value as Entry | undefined;
    if (first) {
      first.output.show(true);
    } else {
      void vscode.window.showInformationMessage('Wiz: no language server has started yet.');
    }
  }

  resetWarnings(): void {
    this.warned.clear();
  }

  dispose(): void {
    this.disposed = true;
    for (const entry of this.entries.values()) {
      void entry.client.stop();
      entry.output.dispose();
    }
    this.entries.clear();
  }
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  const manager = new ClientManager();
  const infoview = new WizInfoview(manager);
  manager.attachInfoview(infoview);
  context.subscriptions.push(manager, infoview);

  const probe = nodeProbe();
  const need = (): vscode.TextEditor => {
    const editor = activeWizEditor();
    if (!editor) {
      throw new Error('Open a Wiz file first.');
    }
    return editor;
  };

  context.subscriptions.push(
    vscode.commands.registerCommand('wiz.restartServer', async () => {
      manager.resetWarnings();
      await manager.restartAll();
      void vscode.window.showInformationMessage('Wiz: language server restarted.');
    }),
    vscode.commands.registerCommand('wiz.showServerLog', () => manager.showLog()),
    vscode.commands.registerCommand('wiz.infoview.show', () => infoview.show()),
    vscode.commands.registerCommand('wiz.infoview.refresh', async () => {
      infoview.show();
      await infoview.update(true);
    }),
    vscode.commands.registerCommand('wiz.format', async () => {
      const editor = need();
      const command = vscode.workspace.getConfiguration('wiz').get<string[]>('format.command', []);
      const spec = launchForFile(editor.document.uri.fsPath, manager.settings(), probe);
      if (command.length > 0) {
        const args = command.map((arg) => arg.replace(/\{file\}/g, editor.document.uri.fsPath));
        await runInTerminal('Wiz: Format', spec.cwd, args[0], args.slice(1));
        return;
      }
      let edits: vscode.TextEdit[] | undefined;
      try {
        edits = await vscode.commands.executeCommand<vscode.TextEdit[] | undefined>(
          'vscode.executeFormatDocumentProvider',
          editor.document.uri,
          { tabSize: 2, insertSpaces: true },
        );
      } catch {
        edits = undefined;
      }
      if (edits && edits.length > 0) {
        const edit = new vscode.WorkspaceEdit();
        edit.set(editor.document.uri, edits);
        await vscode.workspace.applyEdit(edit);
      } else {
        void vscode.window.showInformationMessage(
          'Wiz: the language server does not provide formatting yet. Set wiz.format.command to an external formatter.',
        );
      }
    }),
    vscode.commands.registerCommand('wiz.lint', async () => {
      const editor = need();
      const spec = launchForFile(editor.document.uri.fsPath, manager.settings(), probe);
      const settings = manager.settings();
      const args = ['check'];
      const src = path.join(spec.root, 'src');
      if (probe.exists(path.join(spec.root, 'grail.wiz')) && probe.isDirectory(src)) {
        args.push('-I', src);
      }
      args.push(editor.document.uri.fsPath);
      args.push(...vscode.workspace.getConfiguration('wiz').get<string[]>('check.extraArgs', []));
      await runInTerminal('Wiz: Check', spec.root, settings.wizPath, args);
    }),
    vscode.commands.registerCommand('wiz.build', async () => {
      const editor = need();
      const spec = launchForFile(editor.document.uri.fsPath, manager.settings(), probe);
      const settings = manager.settings();
      const target = vscode.workspace.getConfiguration('wiz').get<string>('build.target', '').trim();
      if (probe.exists(path.join(spec.root, 'grail.wiz')) && probe.isExecutable(settings.grailPath)) {
        const args = ['build'];
        if (target) {
          args.push(target);
        }
        await runInTerminal('Wiz: Build', spec.root, settings.grailPath, args);
        return;
      }
      const out = path.join(spec.root, '.wiz-build', path.basename(editor.document.uri.fsPath, '.wiz'));
      await runInTerminal('Wiz: Build', spec.root, settings.wizPath, [
        'build',
        editor.document.uri.fsPath,
        '-o',
        out,
      ]);
    }),
  );

  const startFor = (editor: vscode.TextEditor | undefined): void => {
    if (editor?.document.languageId !== 'wiz') {
      return;
    }
    void manager.clientFor(editor.document.uri).then(() => infoview.maybeAutoOpen());
  };

  for (const document of vscode.workspace.textDocuments) {
    if (document.languageId === 'wiz') {
      void manager.clientFor(document.uri);
    }
  }
  startFor(vscode.window.activeTextEditor);
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor(startFor),
    vscode.workspace.onDidOpenTextDocument((document) => {
      if (
        document.languageId === 'wiz' &&
        vscode.window.activeTextEditor?.document.uri.toString() === document.uri.toString()
      ) {
        void manager.clientFor(document.uri).then(() => infoview.maybeAutoOpen());
      }
    }),
  );
}

export function deactivate(): void {
  // Disposables in context.subscriptions stop the clients.
}
