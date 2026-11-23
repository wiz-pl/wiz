#!/usr/bin/env node
// The subset boundary is a claim; this checks it.  Every fixture under tests/reject/ has
// a `-- expect: <construct>` line, must be *rejected* by the emitter, and the rejection
// must name that construct — not silently compile and not fail for an unrelated reason.
//
//   WIZ=/path/to/wiz node webgpu/tests/reject.mjs
//
// `wiz parse` only parses, so these fixtures need no imports and need not typecheck.

import { execFileSync } from 'node:child_process';
import { readdirSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const wgsl = join(here, '..', 'tools', 'wgsl.mjs');
const wiz = process.env.WIZ || 'wiz';
const files = readdirSync(join(here, 'reject')).filter((f) => f.endsWith('.wiz')).sort();
let failed = 0, ok = 0;
for (const f of files) {
  const path = join(here, 'reject', f);
  const source = readFileSync(path, 'utf8');
  const m = source.match(/--\s*expect:\s*(.+?)\s*$/m);
  const expect = m && m[1];
  let rc = 0, stderr = '';
  try {
    execFileSync(process.execPath, [wgsl, '--input', path, '--entry', 'f', '--wiz', wiz], {
      encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'],
    });
  } catch (e) {
    rc = e.status || 1;
    stderr = (e.stderr || '').trim();
  }
  const reason = stderr.split('\n').filter((l) => l.includes('rejected')).join(' ');
  const named = !!expect && reason.includes(expect);
  const good = rc !== 0 && reason !== '' && named;
  console.log(`${good ? '✓' : '✗'} ${f}: ` +
    (reason || 'NOT REJECTED') +
    (expect ? (named ? '' : ` (does not name "${expect}")`) : ' (fixture has no -- expect: line)'));
  if (good) ok++; else failed++;
}
console.log(failed
  ? `${ok}/${files.length} fixtures rejected with the named construct; ${failed} failed`
  : `all ${files.length} non-subset fixtures rejected, each naming its construct`);
process.exit(failed ? 1 : 0);
