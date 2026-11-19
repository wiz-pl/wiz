#!/usr/bin/env node
// The subset boundary is a claim; this checks it.  Every fixture under tests/reject/ must
// be *rejected* by the emitter with a message, not silently compiled.
//
//   WIZ=/path/to/wiz node webgpu/tests/reject.mjs
//
// `wiz parse` only parses, so these fixtures need no imports and need not typecheck.

import { execFileSync } from 'node:child_process';
import { readdirSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const wgsl = join(here, '..', 'tools', 'wgsl.mjs');
const wiz = process.env.WIZ || 'wiz';
const files = readdirSync(join(here, 'reject')).filter((f) => f.endsWith('.wiz')).sort();
let failed = 0;
for (const f of files) {
  let rc = 0, stderr = '';
  try {
    execFileSync(process.execPath, [wgsl, '--input', join(here, 'reject', f), '--entry', 'f', '--wiz', wiz], {
      encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'],
    });
  } catch (e) {
    rc = e.status || 1;
    stderr = (e.stderr || '').trim();
  }
  const reason = stderr.split('\n').filter((l) => l.includes('rejected')).join(' ');
  const ok = rc !== 0 && reason !== '';
  console.log(`${ok ? '✓' : '✗'} ${f}: ${reason || 'NOT REJECTED'}`);
  if (!ok) failed++;
}
console.log(failed ? `${failed} fixture(s) were not rejected` : `all ${files.length} non-subset fixtures rejected`);
process.exit(failed ? 1 : 0);
