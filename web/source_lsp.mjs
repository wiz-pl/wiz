// Start `wiz lsp --ws 0 --ws-insecure --no-stdio` for a test and report its port. The
// server prints `wiz lsp: WebSocket on port N` on stderr once it listens; the
// `--ws-insecure` is loopback-only by the server's own check (`Main.lean`), which is
// what a test on this machine needs.
//
//   const srv = await startWizLsp("/path/to/wiz", "/path/to/checkout");
//   ... connect to `ws://127.0.0.1:${srv.port}` ...
//   await srv.close();
"use strict";
import { spawn } from "node:child_process";

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

export async function startWizLsp(bin, root, { timeoutMs = 20000 } = {}) {
  const proc = spawn(bin, ["lsp", "--ws", "0", "--ws-insecure", "--no-stdio"], {
    cwd: root, stdio: ["ignore", "pipe", "pipe"],
  });
  let err = "";
  proc.stderr.on("data", (d) => { err += String(d); });
  let port;
  try {
    port = await new Promise((done, fail) => {
      const deadline = Date.now() + timeoutMs;
      const poll = setInterval(() => {
        const m = /WebSocket on port (\d+)/.exec(err);
        if (m) { clearInterval(poll); done(Number(m[1])); return; }
        if (proc.exitCode !== null || Date.now() > deadline) {
          clearInterval(poll);
          fail(new Error("wiz lsp did not report a port" + (err ? ": " + err.trim() : "")));
        }
      }, 100);
    });
  } catch (e) {
    try { proc.kill("SIGKILL"); } catch (_) { /* gone */ }
    throw e;
  }
  return {
    port,
    url: "ws://127.0.0.1:" + port,
    stderr: () => err,
    async close() {
      try { proc.kill("SIGTERM"); } catch (_) { /* gone */ }
      const exited = new Promise((r) => proc.once("exit", r));
      const ready = await Promise.race([exited.then(() => true), sleep(1500).then(() => false)]);
      if (!ready) { try { proc.kill("SIGKILL"); } catch (_) { /* gone */ } }
    },
  };
}
