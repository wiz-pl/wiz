// The worked example: run each generated WGSL module over the buffers in
// build/expected.json and compare with the Wiz interpreter's values.  The WebGPU code is
// shared with the Deno check (run.js), so this page is a second host, not a second
// implementation.
import { runWebGPU, compare } from './run.js';

const statusEl = document.getElementById('status');
const outEl = document.getElementById('out');
const result = { ok: true, done: false, kernels: {} };
window.__webgpuResult = result;

const text = (tag, s, cls) => {
  const el = document.createElement(tag);
  el.textContent = s;
  if (cls) el.className = cls;
  return el;
};

try {
  const expected = await fetch('./build/expected.json').then((r) => {
    if (!r.ok) throw new Error(`expected.json: HTTP ${r.status}`);
    return r.json();
  });
  statusEl.textContent = 'requesting a WebGPU adapter…';
  for (const [name, k] of Object.entries(expected.kernels)) {
    const shader = await fetch(`./build/${k.wgsl}`).then((r) => {
      if (!r.ok) throw new Error(`${k.wgsl}: HTTP ${r.status}`);
      return r.text();
    });
    const display = name;
    const section = document.createElement('section');
    section.appendChild(text('h2', `${display} — ${expected.length} elements`));
    const r = await runWebGPU({ shader, a: expected.a, b: expected.b, label: display });
    if (!r.ok) {
      result.ok = false;
      result.kernels[name] = { ok: false, stage: r.stage, error: r.error };
      section.appendChild(text('p', `${r.stage}: ${r.error || 'shader validation failed'}`, 'fail'));
      for (const m of r.messages || [])
        section.appendChild(text('pre', `${m.type} ${m.line}:${m.column} ${m.message}`));
    } else {
      const ok = compare(r.out, k.values);
      result.kernels[name] = { ok, out: r.out, expected: k.values };
      if (!ok) result.ok = false;
      const adapter = r.info && (r.info.vendor || r.info.architecture || r.info.description);
      section.appendChild(text('p',
        ok ? `✓ equal to the Wiz interpreter${adapter ? ` (${adapter})` : ''}`
           : '✗ differs from the Wiz interpreter', ok ? 'pass' : 'fail'));
      const table = document.createElement('table');
      const head = document.createElement('tr');
      for (const h of ['i', 'a[i]', 'b[i]', `Wiz ${name}`, 'WGSL', '']) head.appendChild(text('th', h));
      table.appendChild(head);
      expected.a.forEach((a, i) => {
        const row = document.createElement('tr');
        row.appendChild(text('td', String(i)));
        row.appendChild(text('td', String(a)));
        row.appendChild(text('td', String(expected.b[i])));
        row.appendChild(text('td', String(k.values[i])));
        row.appendChild(text('td', String(r.out[i])));
        row.appendChild(text('td', r.out[i] === k.values[i] ? 'ok' : 'MISMATCH', r.out[i] === k.values[i] ? 'pass' : 'fail'));
        table.appendChild(row);
      });
      section.appendChild(table);
      for (const m of r.messages.filter((m) => m.type !== 'error'))
        section.appendChild(text('p', `naga note ${m.line}:${m.column} ${m.message}`, 'muted'));
    }
    const details = document.createElement('details');
    details.appendChild(text('summary', `generated WGSL (${k.wgsl})`));
    details.appendChild(text('pre', shader));
    section.appendChild(details);
    outEl.appendChild(section);
  }
  statusEl.textContent = result.ok ? 'all kernels agree with the interpreter' : 'a kernel disagreed or failed';
  statusEl.className = result.ok ? 'pass' : 'fail';
} catch (e) {
  result.ok = false;
  result.error = String(e && e.stack || e);
  statusEl.textContent = `error: ${e.message || e}`;
  statusEl.className = 'fail';
} finally {
  result.done = true;
}
