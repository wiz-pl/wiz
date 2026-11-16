// The playground's Wasm engine behind one guard. Every call into the module (run, eval,
// check, `wiz_playground_check`) goes through `call`, which turns what the module can
// throw into an `EngineFailure` the page can show, then replaces the module:
//
//   - `exit(n)`: the runtime exits (status 3 when a program forks a thread or blocks
//     forever in this one-threaded build, runtime/wiz_rt.c). Emscripten throws its
//     `ExitStatus` to the caller. The text the runtime printed on stderr just before is
//     kept with the failure.
//   - `abort()` / out of memory: Emscripten throws a `RuntimeError` ("Aborted(…)") and
//     marks the module dead; every later call would throw again.
//   - a trap (unreachable, out-of-bounds access, stack overflow): a `RuntimeError` with
//     the module half-way through a call, its heap in no state to trust.
//
// In each case the module is dropped and a fresh one instantiated (the compiled Wasm is
// cached, so this is the instantiation, not a download); the next call waits for it.
// Nothing else the module throws is caught here.
//
//   const engine = createEngine((options) => createModule(options));
//   await engine.ready;
//   const text = await engine.evaluate(src);   // or engine.check(src): string | null
"use strict";

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

// Emscripten's `ExitStatus` is not an Error: `{ name: "ExitStatus", message, status }`.
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
  // kind: "exit" | "abort" | "trap"; code: the exit status (null otherwise); stderr: the
  // lines the module printed on stderr during the call.
  constructor(kind, code, stderr, cause) {
    const said = stderr.length ? stderr.join("\n") : "";
    const what = kind === "exit" ? `the engine exited with code ${code}`
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
  const m = e && e.message ? String(e.message) : String(e);
  const inner = /^Aborted\((.*)\)/s.exec(m);
  return inner && inner[1] ? inner[1].split(/\. /)[0] : "abort";
}

function failureOf(e, stderr) {
  if (isExitStatus(e)) return new EngineFailure("exit", e.status, stderr, e);
  if (isWasmFailure(e)) {
    const aborted = /^Aborted\(/.test(String(e.message || ""));
    return new EngineFailure(aborted ? "abort" : "trap", null, stderr, e);
  }
  return null;
}

// The output pane's lines for a failure: what the engine printed, then what happened
// and that the page carries on.
export function failureLines(f) {
  const lines = f.stderr.filter((l) => l !== "").map((l) => "error: " + l);
  lines.push(`error: ${f.what}; it was restarted, so Run again works`);
  return lines;
}

// `load(options) → Promise<module>` is the Emscripten factory (`createModule`).
// `printErr` gets every stderr line as well (the console, say); `onRestart(failure)` is
// told when a module is replaced.
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

  async function call(fn) {
    if (!wasm) await (loading || start());
    const m = wasm;
    captured = [];
    try {
      return fn(m);
    } catch (e) {
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
      // after an exit or a trap the module is replaced, heap and all
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
