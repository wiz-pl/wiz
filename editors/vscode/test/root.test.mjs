// Parity tests for the server launch and root rules. The cases are shared with the
// JetBrains client (editors/testdata/lsp-root-cases.json); run with `npm test`.
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import { defaultSettings, findRoot, findToolchain, launchForFile } from '../out/root.js';

const here = path.dirname(fileURLToPath(import.meta.url));
const casesPath = path.resolve(here, '..', '..', 'testdata', 'lsp-root-cases.json');
const fixture = JSON.parse(fs.readFileSync(casesPath, 'utf8'));

function writeFile(file, contents = 'fixture\n') {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, contents);
}

function makeProbe(executables) {
  return {
    exists(p) {
      try {
        fs.statSync(p);
        return true;
      } catch {
        return false;
      }
    },
    isDirectory(p) {
      try {
        return fs.statSync(p).isDirectory();
      } catch {
        return false;
      }
    },
    isExecutable(p) {
      if (p.includes('/') || p.includes(path.sep)) {
        try {
          fs.accessSync(p, fs.constants.X_OK);
          return fs.statSync(p).isFile();
        } catch {
          return false;
        }
      }
      return executables.has(p);
    },
  };
}

function expand(value, base, root) {
  return value.replace(/\{base\}/g, base).replace(/\{root\}/g, root);
}

for (const testCase of fixture.cases) {
  test(testCase.name, () => {
    const base = fs.mkdtempSync(path.join(os.tmpdir(), 'wiz-root-'));
    try {
      for (const dir of testCase.dirs ?? []) {
        fs.mkdirSync(path.join(base, dir), { recursive: true });
      }
      for (const file of testCase.files ?? []) {
        writeFile(path.join(base, file));
      }
      const executables = new Set();
      for (const executable of testCase.executables ?? []) {
        if (executable.includes('/') || executable.includes(path.sep)) {
          fs.chmodSync(path.join(base, executable), 0o755);
        } else {
          executables.add(executable);
        }
      }

      const settings = { ...defaultSettings(), ...(testCase.settings ?? {}) };
      const file = path.join(base, testCase.file);
      const probe = makeProbe(executables);
      const spec = launchForFile(file, settings, probe);

      const expectedRoot = path.join(base, testCase.expect.root);
      assert.equal(spec.root, expectedRoot, 'root');
      assert.equal(spec.kind, testCase.expect.kind, 'kind');
      assert.equal(spec.cwd, path.join(base, testCase.expect.cwd), 'cwd');
      assert.equal(spec.command, expand(testCase.expect.command, base, expectedRoot), 'command');
      assert.deepEqual(
        spec.args,
        testCase.expect.args.map((arg) => expand(arg, base, expectedRoot)),
        'args',
      );
      for (const warning of testCase.expect.warnings ?? []) {
        assert.ok(
          spec.warnings.some((w) => w.includes(warning)),
          `expected a warning containing ${JSON.stringify(warning)}, got ${JSON.stringify(spec.warnings)}`,
        );
      }
    } finally {
      fs.rmSync(base, { recursive: true, force: true });
    }
  });
}

test('findToolchain and findRoot are usable on their own', () => {
  const base = fs.mkdtempSync(path.join(os.tmpdir(), 'wiz-root-'));
  try {
    fs.mkdirSync(path.join(base, 't', 'share', 'wiz', 'lib'), { recursive: true });
    fs.mkdirSync(path.join(base, 't', 'share', 'wiz', '.lake', 'build', 'bin'), { recursive: true });
    writeFile(path.join(base, 't', 'share', 'wiz', 'TOOLCHAIN'));
    writeFile(path.join(base, 't', 'share', 'wiz', 'lib', 'Prelude.wiz'));
    const binary = path.join(base, 't', 'share', 'wiz', '.lake', 'build', 'bin', 'wiz');
    writeFile(binary);
    const probe = makeProbe(new Set());
    const toolchain = findToolchain(path.join(base, 't', 'share', 'wiz', 'lib', 'A.wiz'), probe);
    assert.equal(toolchain?.lib, path.join(base, 't', 'share', 'wiz', 'lib'));
    assert.equal(toolchain?.wiz, binary);
    assert.equal(findRoot(path.join(base, 't', 'share', 'wiz', 'lib', 'A.wiz'), ['.git'], probe), path.join(base, 't', 'share', 'wiz', 'lib'));
  } finally {
    fs.rmSync(base, { recursive: true, force: true });
  }
});
