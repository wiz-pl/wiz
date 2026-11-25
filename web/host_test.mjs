// The capability seam, end to end, with no browser: run a `--target js` module through
// `host.fs.*` twice.
//
//   1. import the module and call `main()` with nothing registered: the generated
//      prologue must fail with `WIZ_HOST_MISSING: fs.open` *before* any user code, and
//      the run must not have produced output;
//   2. register a `mem` implementation of the same five capabilities and run `main()`
//      again: the program opens, writes, seeks (from the start and back from the end),
//      reads and closes through the seam.
//
//   usage: node web/host_test.mjs MODULE.mjs
//
// The module is imported, not executed as a CLI, so `main` is ours to call (the same
// shape a browser page uses: import, register, then run).

const [modulePath] = process.argv.slice(2);
if (!modulePath) {
  console.error("usage: node web/host_test.mjs MODULE.mjs");
  process.exit(2);
}

const mod = await import(new URL(modulePath, `file://${process.cwd()}/`).href);

let missing = null;
try {
  mod.main();
} catch (e) {
  missing = e && e.message ? e.message : String(e);
}
if (missing === null || !missing.startsWith("WIZ_HOST_MISSING: ")) {
  console.error("expected WIZ_HOST_MISSING, got: " + missing);
  process.exit(1);
}
const names = missing.slice("WIZ_HOST_MISSING: ".length).split(", ");
for (const cap of ["fs.open", "fs.read", "fs.write", "fs.seek", "fs.close"]) {
  if (!names.includes(cap)) {
    console.error("the diagnostic omits " + cap + ": " + missing);
    process.exit(1);
  }
}
console.log("host: missing ok");

/* A `mem` filesystem: fully synchronous, which is the whole point of the seam. */
const files = new Map();
const handles = new Map();
let next = 1;

function required(fd) {
  const h = handles.get(Number(fd));
  if (!h) throw new Error("EBADF");
  return h;
}

mod.registerHost({
  "fs.mount": (_dir) => 0n,
  "fs.reserve": (path) => {
    if (!files.has(path)) files.set(path, "");
    return 0n;
  },
  "fs.open": (path, mode) => {
    if (!files.has(path)) {
      if (!mode.includes("w") && !mode.includes("a") && !mode.includes("+")) {
        return 0n; // ENOENT: the caller reads Sys.errno, which this prototype leaves 0
      }
      files.set(path, "");
    }
    if (mode.includes("w") && !mode.includes("+")) files.set(path, "");
    const fd = next++;
    handles.set(Number(fd), { path, pos: mode.includes("a") ? files.get(path).length : 0 });
    return BigInt(fd);
  },
  "fs.write": (fd, s) => {
    const h = required(fd);
    const cur = files.get(h.path);
    files.set(h.path, cur.slice(0, h.pos) + s + cur.slice(h.pos + s.length));
    h.pos += s.length;
    return BigInt(s.length);
  },
  "fs.read": (fd, n) => {
    const h = required(fd);
    const s = files.get(h.path).slice(h.pos, h.pos + Number(n));
    h.pos += s.length;
    return s;
  },
  "fs.seek": (fd, whence, off, back) => {
    const h = required(fd);
    const w = Number(whence);                 // a Wiz Nat arrives as a BigInt
    const o = Number(off) * (back ? -1 : 1);
    h.pos = w === 0 ? o : w === 1 ? h.pos + o : files.get(h.path).length + o;
    return BigInt(h.pos);
  },
  "fs.close": (fd) => {
    if (!handles.delete(Number(fd))) return 1n; // EBADF
    return 0n;
  },
});

mod.main();
console.log("host: all checks passed");
