// Compile and tokenise the TextMate grammar, so a bad regex or scope is caught
// without opening VS Code. Run with `npm test` (after `npm run build:test`).
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createRequire } from 'node:module';
import * as path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import oniguruma from 'vscode-oniguruma';
import textmate from 'vscode-textmate';

const require = createRequire(import.meta.url);
const here = path.dirname(fileURLToPath(import.meta.url));
const grammarPath = path.resolve(here, '..', 'syntaxes', 'wiz.tmLanguage.json');

let grammarPromise;

async function loadGrammar() {
  if (!grammarPromise) {
    grammarPromise = (async () => {
      const wasm = await readFile(require.resolve('vscode-oniguruma/release/onig.wasm'));
      await oniguruma.loadWASM(
        wasm.buffer.slice(wasm.byteOffset, wasm.byteOffset + wasm.byteLength),
      );
      const raw = await readFile(grammarPath, 'utf8');
      const parsed = textmate.parseRawGrammar(raw, grammarPath);
      const registry = new textmate.Registry({
        onigLib: Promise.resolve({
          createOnigScanner(patterns) {
            return new oniguruma.OnigScanner(patterns);
          },
          createOnigString(s) {
            return new oniguruma.OnigString(s);
          },
        }),
        loadGrammar: async (scopeName) => (scopeName === 'source.wiz' ? parsed : null),
      });
      const grammar = await registry.loadGrammar('source.wiz');
      assert.ok(grammar, 'the grammar loads');
      return grammar;
    })();
  }
  return grammarPromise;
}

async function scopesAt(line, index) {
  const grammar = await loadGrammar();
  const result = grammar.tokenizeLine(line, textmate.INITIAL);
  const token = result.tokens
    .filter((t) => t.startIndex <= index && index < t.endIndex)
    .pop();
  return token?.scopes ?? [];
}

function hasScope(scopes, scope) {
  return scopes.some((s) => s === scope);
}

test('declarations, types, numbers', async () => {
  const line = 'def foo : Nat := 0';
  assert.ok(hasScope(await scopesAt(line, 1), 'keyword.other.command.wiz'), 'def is a command');
  assert.ok(hasScope(await scopesAt(line, 5), 'entity.name.function.wiz'), 'foo is the declaration');
  assert.ok(hasScope(await scopesAt(line, 11), 'entity.name.type.wiz'), 'Nat is a type');
  assert.ok(hasScope(await scopesAt(line, 17), 'constant.numeric.wiz'), '0 is a number');
});

test('comments, including Todo and nesting', async () => {
  assert.ok(
    hasScope(await scopesAt('-- TODO: later', 3), 'comment.line.double-dash.wiz'),
    'line comment',
  );
  assert.ok(hasScope(await scopesAt('-- TODO: later', 4), 'keyword.todo.wiz'), 'todo inside comment');
  assert.ok(hasScope(await scopesAt('/- /- nested -/ -/', 4), 'comment.block.wiz'), 'nested block');
  assert.ok(
    hasScope(await scopesAt('/-- doc -/', 4), 'comment.block.documentation.wiz'),
    'doc comment',
  );
});

test('strings, raw strings, characters and holes', async () => {
  assert.ok(hasScope(await scopesAt('"a\\n"', 1), 'string.quoted.double.wiz'), 'string');
  assert.ok(hasScope(await scopesAt('"a\\n"', 2), 'constant.character.escape.wiz'), 'escape');
  assert.ok(hasScope(await scopesAt('r#"raw"#', 4), 'string.quoted.raw.wiz'), 'raw string');
  assert.ok(hasScope(await scopesAt("'x'", 1), 'string.quoted.single.wiz'), 'character');
  assert.ok(hasScope(await scopesAt('?hole', 2), 'variable.other.hole.wiz'), 'named hole');
  assert.ok(hasScope(await scopesAt('_', 0), 'variable.other.hole.wiz'), 'anonymous hole');
});

test('keywords, tactics, sorts and constructors', async () => {
  assert.ok(hasScope(await scopesAt('by rfl', 1), 'keyword.control.wiz'), 'by');
  assert.ok(hasScope(await scopesAt('by rfl', 4), 'keyword.other.tactic.wiz'), 'rfl');
  assert.ok(hasScope(await scopesAt('Type', 1), 'storage.type.sort.wiz'), 'Type');
  assert.ok(hasScope(await scopesAt('x.ctor', 3), 'entity.name.function.constructor.wiz'), '.ctor');
  assert.ok(hasScope(await scopesAt('#check Nat', 2), 'keyword.other.command.wiz'), '#check');
  assert.ok(hasScope(await scopesAt('@[simp]', 2), 'meta.annotation.wiz'), 'attribute');
});

test('the grammar has no uncompiled Oniguruma patterns', async () => {
  // tokenizeLine throws on a bad pattern; tokenise a line full of syntax.
  const grammar = await loadGrammar();
  assert.doesNotThrow(() =>
    grammar.tokenizeLine('def f (x : Nat) : Nat := by simp [x] -- c', textmate.INITIAL),
  );
});
