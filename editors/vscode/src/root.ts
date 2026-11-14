// Server launch and root detection, shared with the JetBrains client by the cases in
// editors/testdata/lsp-root-cases.json. This module deliberately does not import
// `vscode`, so the rules can be tested with plain Node (test/root.test.mjs).
import * as fs from 'node:fs';
import * as path from 'node:path';

export interface WizSettings {
  wizPath: string;
  wizArgs: string[];
  grailPath: string;
  grailArgs: string[];
  grailEnabled: boolean;
  toolchains: boolean;
  rootMarkers: string[];
}

export interface FsProbe {
  exists(p: string): boolean;
  isDirectory(p: string): boolean;
  isExecutable(p: string): boolean;
}

export type LaunchKind = 'wiz' | 'grail' | 'toolchain';

export interface LaunchSpec {
  root: string;
  kind: LaunchKind;
  command: string;
  args: string[];
  cwd: string;
  warnings: string[];
}

export interface Toolchain {
  /** The toolchain's share/wiz/lib directory. */
  lib: string;
  /** The toolchain's bin/wiz wrapper, else its .lake/build/bin/wiz. */
  wiz: string;
}

/** The installed toolchain whose standard library `file` lies in, if any.
 *
 * A toolchain's share/wiz has the marker TOOLCHAIN (older installations: REVISION),
 * its library in lib/ and its binary in .lake/build/bin/wiz (wrapped by bin/wiz).
 * This is the same rule as editors/nvim/lua/wiz/lsp.lua `M.toolchain`. */
export function findToolchain(file: string, probe: FsProbe): Toolchain | undefined {
  let dir = path.dirname(path.resolve(file));
  for (;;) {
    if (path.basename(dir) === 'lib') {
      const share = path.dirname(dir);
      const binary = path.join(share, '.lake', 'build', 'bin', 'wiz');
      const marked = probe.exists(path.join(share, 'TOOLCHAIN')) || probe.exists(path.join(share, 'REVISION'));
      if (probe.exists(path.join(dir, 'Prelude.wiz')) && probe.exists(binary) && marked) {
        const wrapper = path.join(path.dirname(path.dirname(share)), 'bin', 'wiz');
        return { lib: dir, wiz: probe.isExecutable(wrapper) ? wrapper : binary };
      }
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      return undefined;
    }
    dir = parent;
  }
}

/** The nearest ancestor directory of `file` (the file's own directory included) that
 * has one of `markers`, else the file's own directory. */
export function findRoot(file: string, markers: readonly string[], probe: FsProbe): string {
  const own = path.dirname(path.resolve(file));
  let dir = own;
  for (;;) {
    if (markers.some((marker) => probe.exists(path.join(dir, marker)))) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      return own;
    }
    dir = parent;
  }
}

/** The server command for a project root: a toolchain's own wiz for its library,
 * `grail lsp -C ROOT` in a grail package, else `wiz lsp`. */
export function launchForFile(file: string, settings: WizSettings, probe: FsProbe): LaunchSpec {
  const resolved = path.resolve(file);
  const warnings: string[] = [];

  if (settings.toolchains) {
    const toolchain = findToolchain(resolved, probe);
    if (toolchain) {
      return {
        root: toolchain.lib,
        kind: 'toolchain',
        command: toolchain.wiz,
        args: ['lsp'],
        cwd: toolchain.lib,
        warnings,
      };
    }
  }

  const root = findRoot(resolved, settings.rootMarkers, probe);
  if (settings.grailEnabled && probe.exists(path.join(root, 'grail.wiz'))) {
    if (probe.isExecutable(settings.grailPath)) {
      return {
        root,
        kind: 'grail',
        command: settings.grailPath,
        args: [...settings.grailArgs, '-C', root],
        cwd: root,
        warnings,
      };
    }
    warnings.push(
      `${settings.grailPath} is not on PATH; using ${settings.wizPath} lsp without the package's modules`,
    );
  }

  return {
    root,
    kind: 'wiz',
    command: settings.wizPath,
    args: [...settings.wizArgs],
    cwd: root,
    warnings,
  };
}

export function defaultSettings(): WizSettings {
  return {
    wizPath: 'wiz',
    wizArgs: ['lsp'],
    grailPath: 'grail',
    grailArgs: ['lsp'],
    grailEnabled: true,
    toolchains: true,
    rootMarkers: ['grail.wiz', 'wiz-toolchain', 'lakefile.toml', '.git'],
  };
}

/** A probe backed by the real filesystem. A bare command name is looked up on PATH. */
export function nodeProbe(env: NodeJS.ProcessEnv = process.env): FsProbe {
  return {
    exists(p: string): boolean {
      try {
        fs.statSync(p);
        return true;
      } catch {
        return false;
      }
    },
    isDirectory(p: string): boolean {
      try {
        return fs.statSync(p).isDirectory();
      } catch {
        return false;
      }
    },
    isExecutable(p: string): boolean {
      const isFile = (candidate: string): boolean => {
        try {
          fs.accessSync(candidate, fs.constants.X_OK);
          return fs.statSync(candidate).isFile();
        } catch {
          return false;
        }
      };
      if (p.includes('/') || (path.sep === '\\' && p.includes('\\'))) {
        return isFile(p);
      }
      const pathVariable = env.PATH ?? env.Path ?? '';
      for (const dir of pathVariable.split(path.delimiter)) {
        if (dir && isFile(path.join(dir, p))) {
          return true;
        }
      }
      return false;
    },
  };
}
