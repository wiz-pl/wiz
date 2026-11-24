// The page half of the OPFS mechanism test. It starts the worker that owns the
// "instance" (web/opfs/opfs-worker.mjs), keeps the result on `window` for the CDP
// driver, and probes the two walls a main-thread instance would hit:
//   * `createSyncAccessHandle()` on the main thread;
//   * `Atomics.wait` on the main thread.
//
//   ?role=primary  mount, write, seek, read, and keep the lock
//   ?role=locker   try the same file from a second tab (must be refused)
"use strict";

const role = new URLSearchParams(location.search).get("role") || "primary";
const worker = new Worker(new URL("./opfs-worker.mjs", import.meta.url), { type: "module" });
const out = document.getElementById("out");

const done = (value) => {
  window.__opfsResult = value;
  out.textContent = JSON.stringify(value, null, 2);
  window.__opfsDone = true;
};

const ask = (op) => new Promise((resolve) => {
  const onMessage = (e) => {
    if (e.data && e.data.op === op) {
      worker.removeEventListener("message", onMessage);
      resolve(e.data);
    }
  };
  worker.addEventListener("message", onMessage);
  worker.postMessage({ op });
});

window.__opfsClose = async () => {
  const r = await ask("close");
  worker.terminate();
  return r;
};

async function mainThreadProbes() {
  const probes = {};
  // 1. path resolution is async on the main thread too (the *directory* API works
  //    there; only the sync handle is worker-only)
  const root = await navigator.storage.getDirectory();
  const dir = await root.getDirectoryHandle("wiz-fs", { create: true });
  const fh = await dir.getFileHandle("probe.txt", { create: true });
  const call = typeof fh.createSyncAccessHandle === "function"
    ? fh.createSyncAccessHandle.bind(fh) : null;
  if (!call) {
    probes.createReturnsPromise = "absent";
    probes.mainThreadHandle = "absent";
  } else {
    const p = call();
    probes.createReturnsPromise = typeof p.then === "function";
    try {
      const h = await p;
      h.close();
      probes.mainThreadHandle = "allowed";
    } catch (e) {
      probes.mainThreadHandle = e && e.name ? e.name : String(e);
    }
  }
  // 2. a main-thread instance cannot block on a worker
  probes.crossOriginIsolated = self.crossOriginIsolated === true;
  if (typeof SharedArrayBuffer !== "function") {
    probes.atomicsWait = "no SharedArrayBuffer";   // no COOP/COEP: SAB is not exposed
  } else {
    try {
      const sab = new Int32Array(new SharedArrayBuffer(4));
      Atomics.wait(sab, 0, 0, 10);
      probes.atomicsWait = "returned";
    } catch (e) {
      probes.atomicsWait = e && e.name ? e.name : String(e);
    }
  }
  return probes;
}

(async () => {
  try {
    const result = await ask(role === "locker" ? "lock" : "hold");
    result.probes = await mainThreadProbes();
    done(result);
  } catch (e) {
    done({ ok: false, error: e && e.name ? e.name : String(e), detail: String(e) });
  }
})();
