#!/usr/bin/env -S deno run --allow-read
// Validate and run the generated WGSL through a real WebGPU implementation, then compare
// with the Wiz interpreter's numbers in build/expected.json (8 elements) and
// build/wide.json (130 elements, three workgroups).
//
//   deno run --allow-read webgpu/check.mjs
//
// Deno's WebGPU is wgpu (the same Rust stack as naga), so createShaderModule +
// getCompilationInfo is the validation step and dispatch is an actual GPU run.  On a
// headless Linux box wgpu needs an ICD; webgpu/check.sh sets up Mesa's lavapipe.

import { runWebGPU, compare } from './run.js';

const root = new URL('./', import.meta.url);
const files = [
  ['expected.json', 'narrow'],
  ['wide.json', 'wide'],
];

let total = 0, passed = 0, failed = 0, kernels = 0;
let adapter = null;

for (const [file, label] of files) {
  let expected;
  try {
    expected = JSON.parse(await Deno.readTextFile(new URL(`build/${file}`, root)));
  } catch (e) {
    if (file === 'wide.json') continue; // optional: an older build tree
    throw e;
  }
  for (const [name, k] of Object.entries(expected.kernels)) {
    kernels++;
    const shader = await Deno.readTextFile(new URL(`build/${k.wgsl}`, root));
    const r = await runWebGPU({ shader, a: expected.a, b: expected.b, label: `${name}-${label}` });
    if (!r.ok) {
      console.log(`✗ ${name} (${label}): ${r.stage}: ${r.error || 'shader validation failed'}`);
      for (const m of r.messages || []) console.log(`    ${m.type} ${m.line}:${m.column} ${m.message}`);
      failed += k.values.length;
      total += k.values.length;
      continue;
    }
    if (!adapter && r.info) adapter = r.info;
    const ok = compare(r.out, k.values);
    total += k.values.length;
    if (ok) passed += k.values.length; else failed += k.values.length;
    const extra = label === 'wide' ? `, ${expected.length} elements` : '';
    console.log(`${ok ? '✓' : '✗'} ${name} (${label}${extra}): ` +
      `${ok ? 'equal' : 'DIFFER from'} the Wiz interpreter (${r.out.length}/${k.values.length} values)`);
    if (!ok) {
      console.log(`    wgpu:  [${r.out.join(', ')}]`);
      console.log(`    wiz:   [${k.values.join(', ')}]`);
    }
    for (const m of r.messages.filter((m) => m.type !== 'error'))
      console.log(`    note ${m.line}:${m.column} ${m.message}`);
  }
}

const who = adapter && (adapter.description || adapter.architecture || adapter.vendor);
console.log(`${passed}/${total} values agree with the Wiz interpreter ` +
  `(${kernels} kernel${kernels === 1 ? '' : 's'}${who ? `, adapter ${who}` : ''})`);
if (failed) {
  console.log(`${failed} value(s) failed`);
  Deno.exit(1);
}
console.log('all kernels agree');
