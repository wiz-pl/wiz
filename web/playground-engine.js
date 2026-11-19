// The playground's Wasm engine behind one guard. Every call into the module (run, eval,
// check, `wiz_playground_check`) goes through `call`, which turns what the module can
// report into an `EngineFailure` the page can show.
//
//   - a clean stop: the program finished (`Process.exit`, or the one-threaded build
//     refusing to fork or block, or a failed write). The runtime's boundary
//     (runtime/rt_con.inc, `wiz_stop_run`) longjmps back with the code instead of
//     calling `exit`, so the module and its heap stay alive: the call throws an
//     `EngineFailure` of kind "exit", and the next call runs on the same instance.
//     `wiz_playground_exit` holds the code + 1 (0: no stop). The text the runtime
//     printed on stderr just before is kept with the failure.
//   - `abort()`, out of memory (`wiz_panic`'s `exit`, which Emscripten turns into an
//     `ExitStatus`) or a trap (unreachable, out-of-bounds access, stack overflow): the
//     heap or the stack is unusable, so the module is dropped and a fresh one
//     instantiated (the compiled Wasm is cached, so this is the instantiation, not a
//     download); the next call waits for it. Nothing else the module throws is caught.
//
//   const engine = createEngine((options) => createModule(options));
//   await engine.ready;
//   const text = await engine.evaluate(src);   // or engine.check(src): string | null
"use strict";

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

// Emscripten's `ExitStatus` is not an Error: `{ name: "ExitStatus", message, status }`.
// After the runtime boundary, a clean stop no longer produces one; seeing it means the
// module called `exit` outside the boundary (wiz_panic out of memory), which is fatal
// to the instance.
export function isExitStatus(e) {
  return !!e && e.name === "ExitStatus" && typeof e.status === "number";
}

// What the module throws when it aborts or traps.
export function isWasmFailure(e) {
  if (!e) return false;
  if (typeof WebAssembly !== "undefined" && WebAssembly.RuntimeError && e instanceof WebAssembly.RuntimeError) return true;
  return typeof e.message === "string" && /^Aborted\(/.test(e.message);
}

export class EngineFailure extends Error {
  // kind: "exit" (a clean stop; the module survives) | "abort" | "trap";
  // code: the exit status (null otherwise); stderr: the lines the module printed on
  // stderr during the call.
  constructor(kind, code, stderr, cause) {
    const said = stderr.length ? stderr.join("\n") : "";
    const what = kind === "exit" ? `the program exited with code ${code}`
      : kind === "abort" ? "the engine aborted (" + abortReason(cause) + ")"
      : "the engine trapped (" + (cause && cause.message ? cause.message : String(cause)) + ")";
    super(said ? `${said} (${what})` : what);
    this.name = "EngineFailure";
    this.what = what;
    this.kind = kind;
    this.code = code;
    this.stderr = stderr;
    this.cause = cause;
  }
}

function abortReason(e) {
  if (isExitStatus(e)) return `exit ${e.status} outside the exit boundary`;
  const m = e && e.message ? String(e.message) : String(e);
  const inner = /^Aborted\((.*)\)/s.exec(m);
  return inner && inner[1] ? inner[1].split(/\. /)[0] : "abort";
}

function failureOf(e, stderr) {
  // `wiz_panic` (out of memory) still calls exit: Emscripten's ExitStatus is then an
  // abort, not a clean stop, and the instance has to go.
  if (isExitStatus(e)) return new EngineFailure("abort", e.status, stderr, e);
  if (isWasmFailure(e)) {
    const aborted = /^Aborted\(/.test(String(e.message || ""));
    return new EngineFailure(aborted ? "abort" : "trap", null, stderr, e);
  }
  return null;
}

// The output pane's lines for a failure: what the engine printed, then what happened.
// An exit is how a program finishes, so it says so instead of promising a restart.
export function failureLines(f) {
  const lines = f.stderr.filter((l) => l !== "").map((l) => "error: " + l);
  if (f.kind === "exit") lines.push(`error: the program exited with code ${f.code}`);
  else lines.push(`error: ${f.what}; it was restarted, so Run again works`);
  return lines;
}

// `load(options) → Promise<module>` is the Emscripten factory (`createModule`).
// `printErr` gets every stderr line as well (the console, say); `onRestart(failure)` is
// told when a module is replaced (never for a clean exit).
export function createEngine(load, { print = () => {}, printErr = () => {}, onRestart = () => {} } = {}) {
  let wasm = null;
  let captured = null;   // stderr lines of the call in progress
  let loading = null;
  let generation = 0;

  const options = () => ({
    print: (s) => print(s),
    printErr: (s) => { if (captured) captured.push(String(s)); printErr(s); },
    // Node's default sets `process.exitCode`; the page only wants the throw.
    quit: (_status, toThrow) => { throw toThrow; },
  });

  function start() {
    const mine = ++generation;
    loading = Promise.resolve().then(() => load(options())).then((m) => {
      if (mine === generation) wasm = m;
      return m;
    }, (e) => {
      if (mine === generation) loading = null;   // the next call tries again
      throw e;
    });
    return loading;
  }

  // The code of the call's clean stop, or -1 when it ran to the end. The module's
  // `wiz_playground_exit` returns code + 1 so that 0 is unambiguously "no stop" (an
  // `exit 0` is a stop too). A module built before the boundary has no export: then a
  // remaining exit still arrives as Emscripten's ExitStatus.
  function exitCode(m) {
    if (typeof m._wiz_playground_exit !== "function") return -1;
    const raw = Number(m._wiz_playground_exit(big(0)));
    return raw > 0 ? raw - 1 : -1;
  }

  async function call(fn) {
    if (!wasm) await (loading || start());
    const m = wasm;
    captured = [];
    try {
      const out = fn(m);
      const code = exitCode(m);
      if (code >= 0) throw new EngineFailure("exit", code, captured, null);
      return out;
    } catch (e) {
      if (e instanceof EngineFailure) throw e;   // a clean stop: the module is kept
      const failure = failureOf(e, captured);
      if (!failure) throw e;
      wasm = null;
      start().catch(() => { /* the next call reports it */ });
      onRestart(failure);
      throw failure;
    } finally {
      captured = null;
    }
  }

  function passString(m, name, src) {
    const p = m.stringToNewUTF8(src);
    let r;
    try {
      r = m[name](big(p));
    } finally {
      // the module is alive here even after a clean stop; after a trap, _free throws
      try { m._free(big(p)); } catch (_) { /* a dead module */ }
    }
    const text = r ? m.UTF8ToString(Number(r)) : null;
    if (r) m._free(r);
    return text;
  }

  const ready = start();
  return {
    ready,
    // `wiz_playground_eval`: the lines Run shows.
    evaluate: (src) => call((m) => passString(m, "_wiz_playground_eval", src) || ""),
    // `wiz_playground_check`: JSON, or null with a module built before it existed.
    check: (src) => call((m) => (typeof m._wiz_playground_check === "function"
      ? passString(m, "_wiz_playground_check", src) : null)),
    get generation() { return generation; },
  };
}
