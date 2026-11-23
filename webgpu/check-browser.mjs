#!/usr/bin/env node
// Drive the worked-example page in headless Chromium and read window.__webgpuResult.
// This is optional: the page is the deliverable and check.mjs (Deno) is the automated
// WebGPU run.  Chromium's headless WebGPU needs a software Vulkan driver or a GPU; when
// the adapter is missing the page reports that and this exits 2.
//
//   CHROME=/path/to/chromium node webgpu/check-browser.mjs
//
// The CDP plumbing is web/chrome_test.mjs's, reduced to one page and one JSON answer.

import { spawn } from 'node:child_process';
import { mkdtempSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { startServer } from './serve.mjs';

const chrome = process.env.CHROME || 'chromium';
const server = await startServer(new URL('./', import.meta.url).pathname, 0);
const url = `http://127.0.0.1:${server.address().port}/`;
const port = 9400 + Math.floor(Math.random() * 400);
const profile = mkdtempSync(join(tmpdir(), 'wiz-webgpu-'));
const proc = spawn(chrome, [
  '--headless=new', '--no-sandbox', '--disable-dev-shm-usage',
  '--enable-unsafe-webgpu', '--enable-features=Vulkan',
  '--use-angle=swiftshader', '--use-vulkan=swiftshader',
  `--remote-debugging-port=${port}`, `--user-data-dir=${profile}`, 'about:blank',
], { stdio: 'ignore' });
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const done = (code) => { proc.kill(); server.close(); process.exit(code); };
setTimeout(() => { console.log('timeout'); done(1); }, 90000);

let target = null;
for (let i = 0; i < 100 && !target; i++) {
  await sleep(200);
  try { target = (await (await fetch(`http://127.0.0.1:${port}/json/list`)).json()).find((t) => t.type === 'page'); } catch {}
}
if (!target) { console.log('chromium did not open a debugging target'); done(1); }
const ws = new WebSocket(target.webSocketDebuggerUrl);
await new Promise((r) => ws.addEventListener('open', r));
let id = 0;
const pending = new Map();
ws.addEventListener('message', (m) => {
  const msg = JSON.parse(m.data);
  if (msg.id && pending.has(msg.id)) { pending.get(msg.id)(msg.result); pending.delete(msg.id); }
});
const call = (method, params = {}) => new Promise((r) => { pending.set(++id, r); ws.send(JSON.stringify({ id, method, params })); });
const evaluate = async (expr) => (await call('Runtime.evaluate', { expression: expr, returnByValue: true, awaitPromise: true })).result.value;
await call('Runtime.enable');
await call('Page.navigate', { url });

let result = null;
for (let i = 0; i < 200 && !result; i++) {
  await sleep(250);
  const r = await evaluate('window.__webgpuResult || null');
  if (r && r.done) result = r;
}
if (!result) { console.log('page produced no result'); done(1); }
console.log(JSON.stringify(result, null, 2));
if (result.error) { console.log(`page error: ${result.error}`); done(1); }
if (Object.values(result.kernels || {}).some((k) => k.stage === 'device')) {
  console.log('no WebGPU adapter in this Chromium (reported by the page)');
  done(2);
}
done(result.ok ? 0 : 1);
