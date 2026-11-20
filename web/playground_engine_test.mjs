// The playground's engine guard (web/playground-engine.js) under Node, with a stub
// Emscripten module in place of the Wasm build, so the test needs no emcc, no Wiz build
// and no browser.
//
//   usage: node web/playground_engine_test.mjs
//
// The stub's sources mirror the runtime's two kinds of ending:
//
//   - "fork"/"block": a clean stop. The runtime prints its message on stderr and
//     longjmps back to the call's boundary (runtime/rt_con.inc, `wiz_stop_run`), so the
//     export returns "" and `wiz_playground_exit` has the code + 1. The module stays
//     alive: the engine reports `EngineFailure` of kind "exit" and the next call runs on
//     the same instance (no new instantiation, the same instance id, `generation`
//     unchanged).
//   - "panic": `wiz_panic` still calls `exit`, so Emscripten throws `ExitStatus(3)`; the
//     instance is replaced. "oom" aborts (Emscripten's "Aborted(OOM)", after which the
//     module is dead), "trap" throws a `WebAssembly.RuntimeError`; both re-instantiate.
//     "boom" is a plain Error, which is not the guard's to catch.
//
// Anything else evaluates to "ok: <src>". Covers: run/eval/check each turning a clean
// exit into an `EngineFailure` while keeping the instance, an abort and a trap into one
// that replaces it, the stderr text and exit code, the output pane's lines, a load that
// fails once and then succeeds, the language-server shim's diagnostic, and no unhandled
// rejection.
"use strict";
import { createEngine, failureLines, isExitStatus, EngineFailure } from "./playground-engine.js";
import { SelfhostServer } from "./selfhost-lsp-shim.js";
import { index as indexOracle } from "./framework/index-oracle.mjs";

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
const PANIC = "wiz: out of memory";

let instances = 0;
let loadFailures = 0;   // the next N loads reject
function stubModule(options) {
  if (loadFailures > 0) { loadFailures--; return Promise.reject(new Error("fetch failed")); }
  const id = ++instances;
  const heap = new Map();
  let next = 8;
  let dead = false;
  let lastExit = -1;   // the code the runtime's boundary caught, -1: none
  const alloc = (s) => { const p = next++; heap.set(p, s); return BigInt(p); };
  function engine(kind) {
    return (p) => {
      lastExit = -1;
      if (dead) throw new WebAssembly.RuntimeError("Aborted(Assertion failed: cannot call into a dead module)");
      const src = heap.get(Number(p)).split("\n").pop();   // after the Prelude line the shim adds
      // A clean stop: the runtime's message, then the boundary's "" and its code.
      if (src === "fork" || src === "block") {
        options.printErr(src === "fork" ? NO_THREADS : BLOCKS);
        lastExit = 3;
        return alloc("");
      }
      // wiz_panic: exit() is not a clean stop, so Emscripten throws ExitStatus.
      if (src === "panic") {
        options.printErr(PANIC);
        dead = true;
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
    // The runtime's `wiz_playground_exit`: code + 1, so 0 is "ran to the end".
    _wiz_playground_exit: (_dummy) => BigInt(lastExit + 1),
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

// A clean stop (Run's exit, the one-threaded build refusing to fork): the module is kept.
let f = await failureOf(engine.evaluate("fork"));
check("exit: an EngineFailure", f instanceof EngineFailure, true);
check("exit: kind", f.kind, "exit");
check("exit: code", f.code, 3);
check("exit: stderr captured", f.stderr, [NO_THREADS]);
check("exit: message has stderr and code", f.message, `${NO_THREADS} (the program exited with code 3)`);
check("exit: there is no cause to restart for", f.cause, null);
check("exit: pane lines", failureLines(f), [
  "error: " + NO_THREADS,
  "error: the program exited with code 3",
]);
check("exit: printErr still sees stderr", errs.includes(NO_THREADS), true);
check("exit: the module was not replaced", instances, 1);
check("exit: the generation did not change", engine.generation, 1);
check("exit: not reported as a restart", restarts, []);
check("exit: the next eval runs on the same instance", await engine.evaluate("1"), "ok#1: 1\n");
check("exit: still one instance after it", instances, 1);

// The same from check (wiz_playground_check), the blocking case.
f = await failureOf(engine.check("block"));
check("check exit: kind and code", [f.kind, f.code], ["exit", 3]);
check("check exit: stderr is this call's only", f.stderr, [BLOCKS]);
check("check exit: the next check runs on the same instance", JSON.parse(await engine.check("3")).instance, 1);
check("check exit: still one instance", instances, 1);

// wiz_panic (OOM) still exits outside the boundary: ExitStatus, and the instance goes.
f = await failureOf(engine.evaluate("panic"));
check("panic: kind", f.kind, "abort");
check("panic: code", f.code, 3);
check("panic: the cause is the ExitStatus", isExitStatus(f.cause), true);
check("panic: pane lines", failureLines(f), [
  "error: " + PANIC,
  "error: the engine aborted (exit 3 outside the exit boundary); it was restarted, so Run again works",
]);
check("panic: a new instance", instances, 2);
check("panic: eval works on it", await engine.evaluate("4"), "ok#2: 4\n");
check("panic: check works on it", JSON.parse(await engine.check("5")).instance, 2);

// out of memory: the module is dead after it
f = await failureOf(engine.evaluate("oom"));
check("oom: kind", f.kind, "abort");
check("oom: code", f.code, null);
check("oom: pane lines", failureLines(f), [
  "error: Cannot enlarge memory arrays to size 4294967296 bytes (OOM).",
  "error: the engine aborted (OOM); it was restarted, so Run again works",
]);
check("oom: eval works on the new module", await engine.evaluate("6"), "ok#3: 6\n");
check("oom: check works on the new module", JSON.parse(await engine.check("7")).instance, 3);

// a trap, with nothing on stderr
f = await failureOf(engine.check("trap"));
check("trap: kind", f.kind, "trap");
check("trap: no stderr", f.stderr, []);
check("trap: pane lines", failureLines(f), ["error: the engine trapped (unreachable); it was restarted, so Run again works"]);
check("trap: eval works after", await engine.evaluate("8"), "ok#4: 8\n");

// two calls queued behind one restart both wait for the same new module
f = await failureOf(engine.evaluate("trap"));
check("queued: the trap restarted", instances, 5);
const [a, b] = await Promise.all([engine.evaluate("9"), engine.check("10")]);
check("queued: both answered by one new module", [a, JSON.parse(b).instance], ["ok#5: 9\n", 5]);
check("restarts reported (clean exits are not restarts)", restarts, ["abort", "abort", "trap", "trap"]);

// a plain Error is not swallowed, and the module is kept
f = await failureOf(engine.evaluate("boom"));
check("other errors pass through", [f instanceof EngineFailure, f.message], [false, "not the engine's"]);
check("other errors keep the module", await engine.evaluate("11"), "ok#5: 11\n");

// the restart's load fails once: that call reports it, the next one loads again
loadFailures = 1;
f = await failureOf(engine.evaluate("trap"));
check("failed reload: the trap is still reported", f.kind, "trap");
f = await failureOf(engine.evaluate("12"));
check("failed reload: the next call says why", f && f.message, "fetch failed");
check("failed reload: then a fresh load", await engine.evaluate("13"), "ok#6: 13\n");

// a module built before wiz_playground_check: null, not a failure
const old = createEngine((o) => stubModule(o).then((m) => { delete m._wiz_playground_check; return m; }));
await old.ready;
check("no check export: null", await old.check("x"), null);

// the in-page language server (?lsp=selfhost) on the same engine: an exit is a
// diagnostic with the runtime's message, and the next change runs on the same module
const server = new SelfhostServer({ evaluate: engine.evaluate, check: engine.check, index: indexOracle });
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
  diag && diag.message, `the self-hosted engine failed: ${NO_THREADS} (the program exited with code 3)`);
out = await open("def x := 1", 2);
check("lsp: the exit did not replace the module", instances, before);
check("lsp: and publishes", out[0] && out[0].method, "textDocument/publishDiagnostics");

await new Promise((r) => setTimeout(r, 10));
check("no unhandled rejection", rejections.map(String), []);

if (failed) { console.log(`${failed} failed`); process.exit(1); }
console.log("playground engine: all checks passed");
