// Peak linear memory and wall time of a Wasm module for the experimental backend.
//
//   node scripts/wasm-peak.mjs FILE.wasm
//
// The module's memory never shrinks (it only grows), so its size after `wiz_main` is its
// peak. Prints one JSON object: the result, the peak in bytes and pages, and the time
// spent in `wiz_main` in milliseconds.
import { instantiate, show } from '../web/wasm-host.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node scripts/wasm-peak.mjs FILE.wasm');
  process.exit(2);
}

const ex = await instantiate(path);
const t0 = process.hrtime.bigint();
const v = ex.wiz_main();
const t1 = process.hrtime.bigint();
const peak = ex.memory.buffer.byteLength;
console.log(JSON.stringify({
  result: show(ex, v),
  peakBytes: peak,
  peakPages: peak / 65536,
  ms: Number(t1 - t0) / 1e6,
}));
