#!/usr/bin/env -S deno run --allow-read
// Validate and run the generated WGSL through a real WebGPU implementation, then compare
// with the Wiz interpreter's numbers in build/expected.json.
//
//   deno run --allow-read webgpu/check.mjs
//
// Deno's WebGPU is wgpu (the same Rust stack as naga), so createShaderModule +
// getCompilationInfo is the validation step and dispatch is an actual GPU run.  On a
// headless Linux box wgpu needs an ICD; webgpu/check.sh sets up Mesa's lavapipe.

import { runWebGPU, compare } from './run.js';

const root = new URL('./', import.meta.url);
const expected = JSON.parse(await Deno.readTextFile(new URL('build/expected.json', root)));

let failed = 0;
for (const [name, k] of Object.entries(expected.kernels)) {
  const shader = await Deno.readTextFile(new URL(`build/${k.wgsl}`, root));
  const r = await runWebGPU({ shader, a: expected.a, b: expected.b, label: name });
  if (!r.ok) {
    console.log(`✗ ${name}: ${r.stage}: ${r.error || 'shader validation failed'}`);
    for (const m of r.messages || []) console.log(`    ${m.type} ${m.line}:${m.column} ${m.message}`);
    failed++;
    continue;
  }
  const ok = compare(r.out, k.values);
  console.log(`${ok ? '✓' : '✗'} ${name}: ${r.out.length} values, ` +
    `${ok ? 'equal to the Wiz interpreter' : 'DIFFER from the Wiz interpreter'}`);
  if (!ok) {
    console.log(`    wgpu:  [${r.out.join(', ')}]`);
    console.log(`    wiz:   [${k.values.join(', ')}]`);
    failed++;
  }
  const notes = r.messages.filter((m) => m.type !== 'error');
  for (const m of notes) console.log(`    note ${m.line}:${m.column} ${m.message}`);
}
if (failed) {
  console.log(`${failed} kernel(s) failed`);
  Deno.exit(1);
}
console.log('all kernels agree');
