// The playground's engine guard (web/playground-engine.js) under Node, with a stub
// Emscripten module in place of the Wasm build, so the test needs no emcc, no Wiz build
// and no browser.
//
//   usage: node web/playground_engine_test.mjs
//
// The stub's sources: "fork" prints the runtime's no-threads message on stderr and
// throws `ExitStatus(3)` (runtime/wiz_rt.c in a WIZ_NO_THREADS build); "block" the same
// for a program that would block forever; "oom" aborts (Emscripten's "Aborted(OOM)",
// after which the module is dead); "trap" throws a `WebAssembly.RuntimeError`; "boom" a
// plain Error, which is not the guard's to catch. Anything else evaluates to "ok: <src>".
// Covers: run/eval/check each turning an exit, an abort and a trap into an
// `EngineFailure` with the stderr text and exit code, the output pane's lines, the module
// replaced and the next call answered by the new one, a load that fails once and then
// succeeds, the language-server shim's diagnostic, and no unhandled rejection.
"use strict";
import { createEngine, failureLines, isExitStatus, EngineFailure } from "./playground-engine.js";
import { SelfhostServer } from "./selfhost-lsp-shim.js";

let failed = 0;
function check(name, got, want) {
  const same = typeof want === "object" ? JSON.stringify(got) === JSON.stringify(want) : Object.is(got, want);
  if (same) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`); }
}
const rejections = [];
process.on("unhandledRejection", (reason) => rejections.push(reason));

// Emscripten's own shape: not an Error.
class ExitStatus {
  constructor(status) {
    this.name = "ExitStatus";
    this.message = `Program terminated with exit(${status})`;
    this.status = status;
  }
}
const NO_THREADS = "wiz: Task.spawn: threads are not available in this build (WIZ_NO_THREADS)";
const BLOCKS = "wiz: IO.wait: this would block forever in a one-threaded build (WIZ_NO_THREADS)";

let instances = 0;
let loadFailures = 0;   // the next N loads reject
function stubModule(options) {
  if (loadFailures > 0) { loadFailures--; return Promise.reject(new Error("fetch failed")); }
  const id = ++instances;
  const heap = new Map();
  let next = 8;
  let dead = false;
  const alloc = (s) => { const p = next++; heap.set(p, s); return BigInt(p); };
  function engine(kind) {
    return (p) => {
      if (dead) throw new WebAssembly.RuntimeError("Aborted(Assertion failed: cannot call into a dead module)");
      const src = heap.get(Number(p)).split("\n").pop();   // after the Prelude line the shim adds
      if (src === "fork" || src === "block") {
        options.printErr(src === "fork" ? NO_THREADS : BLOCKS);
        options.quit(3, new ExitStatus(3));
      }
      if (src === "oom") {
        options.printErr("Cannot enlarge memory arrays to size 4294967296 bytes (OOM).");
        dead = true;
        throw new WebAssembly.RuntimeError("Aborted(OOM). Build with -sASSERTIONS for more info.");
      }
      if (src === "trap") throw new WebAssembly.RuntimeError("unreachable");
      if (src === "boom") throw new Error("not the engine's");
      return alloc(kind === "check" ? JSON.stringify({ instance: id, src }) : `ok#${id}: ${src}\n`);
    };
  }
  return Promise.resolve({
    id,
    stringToNewUTF8: alloc,
    UTF8ToString: (p) => heap.get(Number(p)),
    _free: (p) => { if (dead) throw new WebAssembly.RuntimeError("Aborted(dead)"); heap.delete(Number(p)); },
    _wiz_playground_eval: engine("eval"),
    _wiz_playground_check: engine("check"),
    heap,
  });
}

const errs = [];
const restarts = [];
const engine = createEngine(stubModule, { printErr: (s) => errs.push(s), onRestart: (f) => restarts.push(f.kind) });
await engine.ready;
check("one instance at start", instances, 1);
check("eval", await engine.evaluate("1"), "ok#1: 1\n");
check("check", JSON.parse(await engine.check("2")), { instance: 1, src: "2" });

async function failureOf(p) {
  try { await p; return null; } catch (e) { return e; }
}

// ExitStatus from eval (Run uses the same call)
let f = await failureOf(engine.evaluate("fork"));
check("exit: an EngineFailure", f instanceof EngineFailure, true);
check("exit: kind", f.kind, "exit");
check("exit: code", f.code, 3);
check("exit: stderr captured", f.stderr, [NO_THREADS]);
check("exit: message has stderr and code", f.message, `${NO_THREADS} (the engine exited with code 3)`);
check("exit: the cause is the ExitStatus", isExitStatus(f.cause), true);
check("exit: pane lines", failureLines(f), [
  "error: " + NO_THREADS,
  "error: the engine exited with code 3; it was restarted, so Run again works",
]);
check("exit: printErr still sees stderr", errs.includes(NO_THREADS), true);
check("exit: the next eval is answered by a new module", await engine.evaluate("1"), "ok#2: 1\n");
check("exit: two instances", instances, 2);

// ExitStatus from check (wiz_playground_check), the blocking case
f = await failureOf(engine.check("block"));
check("check exit: kind and code", [f.kind, f.code], ["exit", 3]);
check("check exit: stderr is this call's only", f.stderr, [BLOCKS]);
check("check exit: the next check works", JSON.parse(await engine.check("3")).instance, 3);

// out of memory: the module is dead after it
f = await failureOf(engine.evaluate("oom"));
check("oom: kind", f.kind, "abort");
check("oom: code", f.code, null);
check("oom: pane lines", failureLines(f), [
  "error: Cannot enlarge memory arrays to size 4294967296 bytes (OOM).",
  "error: the engine aborted (OOM); it was restarted, so Run again works",
]);
check("oom: eval works on the new module", await engine.evaluate("4"), "ok#4: 4\n");
check("oom: check works on the new module", JSON.parse(await engine.check("5")).instance, 4);

// a trap, with nothing on stderr
f = await failureOf(engine.check("trap"));
check("trap: kind", f.kind, "trap");
check("trap: no stderr", f.stderr, []);
check("trap: pane lines", failureLines(f), ["error: the engine trapped (unreachable); it was restarted, so Run again works"]);
check("trap: eval works after", await engine.evaluate("6"), "ok#5: 6\n");

// two calls queued behind one restart both wait for the same new module
f = await failureOf(engine.evaluate("fork"));
const [a, b] = await Promise.all([engine.evaluate("7"), engine.check("8")]);
check("queued: both answered by one new module", [a, JSON.parse(b).instance], ["ok#6: 7\n", 6]);
check("restarts reported", restarts, ["exit", "exit", "abort", "trap", "exit"]);

// a plain Error is not swallowed, and the module is kept
f = await failureOf(engine.evaluate("boom"));
check("other errors pass through", [f instanceof EngineFailure, f.message], [false, "not the engine's"]);
check("other errors keep the module", await engine.evaluate("9"), "ok#6: 9\n");

// the restart's load fails once: that call reports it, the next one loads again
loadFailures = 1;
f = await failureOf(engine.evaluate("fork"));
check("failed reload: the exit is still reported", f.kind, "exit");
f = await failureOf(engine.evaluate("10"));
check("failed reload: the next call says why", f && f.message, "fetch failed");
check("failed reload: then a fresh load", await engine.evaluate("11"), "ok#7: 11\n");

// a module built before wiz_playground_check: null, not a failure
const old = createEngine((o) => stubModule(o).then((m) => { delete m._wiz_playground_check; return m; }));
await old.ready;
check("no check export: null", await old.check("x"), null);

// the in-page language server (?lsp=selfhost) on the same engine: an exit is a
// diagnostic with the runtime's message, and the next change is checked again
const server = new SelfhostServer({ evaluate: engine.evaluate, check: engine.check });
const open = (text, version) => server.handle(JSON.stringify({
  jsonrpc: "2.0", method: version === 1 ? "textDocument/didOpen" : "textDocument/didChange",
  params: version === 1
    ? { textDocument: { uri: "file:///p.wiz", version, text } }
    : { textDocument: { uri: "file:///p.wiz", version }, contentChanges: [{ text }] },
}));
const before = instances;
let out = await open("fork", 1);
const diag = out[0] && out[0].params.diagnostics[0];
check("lsp: one diagnostic", out[0] && out[0].params.diagnostics.length, 1);
check("lsp: it carries the runtime's message and code",
  diag && diag.message, `the self-hosted engine failed: ${NO_THREADS} (the engine exited with code 3)`);
out = await open("def x := 1", 2);
check("lsp: the next change reaches a new module", instances, before + 1);
check("lsp: and publishes", out[0] && out[0].method, "textDocument/publishDiagnostics");

await new Promise((r) => setTimeout(r, 10));
check("no unhandled rejection", rejections.map(String), []);

if (failed) { console.log(`${failed} failed`); process.exit(1); }
console.log("playground engine: all checks passed");
