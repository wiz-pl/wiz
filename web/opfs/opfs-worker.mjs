// The `opfs` implementation of the `fs` capability, in the worker that owns the
// instance (a JS stand-in for the Wasm module here: see web/opfs/opfs-page.mjs).
//
// The split this file exists to prove:
//   * `mount`/`reserve`/`preopen` are async (OPFS path resolution and
//     `createSyncAccessHandle()` return promises) and run before "main";
//   * everything after that -- write, seek, read, getSize, close -- is a plain
//     synchronous call, because this worker holds the handle.
// A second tab is refused the exclusive lock, which is a startup diagnostic, not a race.
"use strict";

let root = null;
const paths = new Map();   // name -> FileSystemFileHandle
const open = new Map();    // fd -> { h, pos, name }
let next = 1;
let held = null;           // the handle `hold` keeps open for the multi-tab probe

async function mount(dir = "wiz-fs") {
  root = await navigator.storage.getDirectory();
  let d = root;
  for (const part of dir.split("/").filter(Boolean)) {
    d = await d.getDirectoryHandle(part, { create: true });
  }
  for await (const [name, h] of d.entries()) {
    if (h.kind === "file") paths.set(name, h);
  }
  return d;
}

async function reserve(dir, name) {
  const fh = await dir.getFileHandle(name, { create: true });
  paths.set(name, fh);
  return fh;
}

/* ---- the synchronous module side (the part the runtime's contract allows) ---- */

function syncOpen(name, mode) {
  const fh = paths.get(name);
  if (!fh) throw new Error("ENOENT: " + name);
  const h = fh.__h;
  if (!h) throw new Error("ENOENT: " + name + " (not pre-opened)");
  const fd = next++;
  open.set(fd, { h, pos: mode.includes("a") ? h.getSize() : 0, name });
  return fd;
}
function syncWrite(fd, s) {
  const f = open.get(fd);
  const bytes = new TextEncoder().encode(s);
  f.h.write(bytes, { at: f.pos });
  f.pos += bytes.length;
  return s.length;
}
function syncRead(fd, n) {
  const f = open.get(fd);
  const buf = new Uint8Array(Number(n));
  const got = f.h.read(buf, { at: f.pos });
  f.pos += got;
  return new TextDecoder().decode(buf.subarray(0, got));
}
function syncSeek(fd, whence, off, back) {
  const f = open.get(fd);
  const o = Number(off) * (back ? -1 : 1);
  f.pos = whence === 0 ? o : whence === 1 ? f.pos + o : f.h.getSize() + o;
  return f.pos;
}
function syncClose(fd) {
  const f = open.get(fd);
  f.h.flush();
  open.delete(fd);
  return 0;
}

/* ---- the message protocol ---- */

async function hold() {
  const dir = await mount();
  const fh = await reserve(dir, "note.txt");
  // `createSyncAccessHandle()` is a promise even in a worker: the pre-open is async.
  const h = await fh.createSyncAccessHandle();
  fh.__h = h;
  const fd = syncOpen("note.txt", "w");
  const wrote = syncWrite(fd, "hello, opfs");
  const atStart = syncSeek(fd, 0, 7, false);
  const a = syncRead(fd, 4);
  const atEnd = syncSeek(fd, 2, 4, true);
  const b = syncRead(fd, 4);
  const size = h.getSize();
  // keep the handle (and the fd) open so a second tab must be refused the lock
  held = { fd, h };
  return { wrote, atStart, atEnd, a, b, size };
}

self.onmessage = async (e) => {
  const msg = e.data || {};
  try {
    if (msg.op === "hold") {
      const t = performance.now();
      const r = await hold();
      self.postMessage({ op: msg.op, ok: true, ...r, asyncMs: performance.now() - t });
    } else if (msg.op === "lock") {
      const dir = await mount();
      const fh = await dir.getFileHandle("note.txt", { create: false });
      const h = await fh.createSyncAccessHandle();   // the exclusive lock
      h.close();
      self.postMessage({ op: msg.op, ok: true });
    } else if (msg.op === "close") {
      if (held) {
        syncClose(held.fd);
        held.h.close();
        held = null;
      }
      self.postMessage({ op: msg.op, ok: true });
    } else {
      self.postMessage({ op: msg.op, ok: false, error: "unknown op" });
    }
  } catch (err) {
    self.postMessage({ op: msg.op, ok: false, error: err && err.name ? err.name : String(err),
      detail: err && err.message ? err.message : "" });
  }
};
