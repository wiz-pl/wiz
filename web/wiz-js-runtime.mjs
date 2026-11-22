/* The JavaScript runtime for `wiz build --target js`.
 *
 * `Wiz/Compiler/Js.lean` pastes this file, verbatim, at the top of every emitted
 * module, so the module is self-contained: `node prog.mjs` needs nothing else. The
 * names the emitted code calls are the C runtime's (`wiz_nat_add`, `wiz_nat_show`,
 * `wiz_io_println`, …) where an entry point is honest, and `wizCtor`/`wizClo`/
 * `wizApply` for the three representation choices JavaScript actually changes.
 *
 * Values, as the emitter and this file agree:
 *
 *   Wiz                 JavaScript
 *   ------------------  -----------------------------------------------------------
 *   Nat                 BigInt (arbitrary precision: the GMP bignum of the C runtime)
 *   a constructor       `{ t: tag, f: [fields] }`; with no fields, the tag `t` alone
 *   a tag scalar        a JS number (Bool, an empty constructor, a case tag)
 *   `◾`                 null
 *   a closure           a JS function made by `wizClo` (callable from FFI too)
 *   String              the Wiz data type: `String.mk (List Char)`, code points
 *   UInt64              BigInt below 2^64 (masked by the `wiz_u64_*` entries)
 *   Float64             a JS number
 *   UIntN / BitVec      BigInt (the bits; `wiz_word_*` masks at the width)
 *   Bytes               Uint8Array
 *   Array               a JS array (copy-on-write: `set`/`push` copy)
 *   a foreign handle    the host's object, as it is (`js.document…` results)
 *
 * Reference counting is the garbage collector's: `dup`/`drop` emit nothing,
 * `reset` produces no token, and `reuse` allocates a fresh object. The note
 * `wiz-notes/js-target.md` says what that costs and what it does not change.
 */

const WIZ_MASK64 = (1n << 64n) - 1n;
/* The C runtime refuses a number result with more than 2^24 bits; the JS backend
 * keeps the same limit (an accidental `Nat.pow 2 1000000000` would otherwise hang
 * the page or the Node process rather than report an error). */
const WIZ_MAX_BITS = 16777216n;

/* ---- constructors and closures ---- */

export function wizCtor(tag, fields) {
  return { t: tag, f: fields };
}

/* A closure is a JS function: its captured arguments are the closure's own. It
 * handles partial application (fewer arguments than the arity) and over-application
 * (more), like `wiz_apply` in the C runtime. */
export function wizClo(fn, arity, captured) {
  const clo = (...more) => {
    const all = captured.concat(more);
    if (all.length < arity) return wizClo(fn, arity, all);
    const r = fn(...all.slice(0, arity));
    return all.length === arity ? r : wizApply(r, all.slice(arity));
  };
  clo.wizClo = true;
  return clo;
}

/* A jump to a join point. The emitter turns `jdecl` into a function plus a driver loop
 * and `jmp` into `new WizJmp(j, args)`, so a self tail call stays constant stack. */
export class WizJmp {
  constructor(id, args) {
    this.id = id;
    this.args = args;
  }
}

export function wizApply(f, args) {
  /* `◾` applied is `◾` (a proof, or a function with no runtime content) */
  if (f === null) return null;
  if (typeof f !== "function") throw new Error("wiz: applying a non-function");
  return f(...args);
}

export function wizReset(x) {
  /* the C runtime keeps a unique constructor's cell for `reuse`; with a GC the
   * token has nothing to keep, and `reuse` allocates. */
  return null;
}

export function wizReuse(token, tag, fields) {
  return fields.length === 0 ? tag : wizCtor(tag, fields);
}

/* ---- tags, fields, the flat-object operations of `pack`/`unpack` ---- */

export function wizTag(v) {
  if (typeof v === "bigint") return v === 0n ? 0 : 1;
  if (typeof v === "number") return v;
  if (v === null) return 0;
  if (typeof v === "function") throw new Error("wiz: tag of a function");
  if (v && typeof v.t === "number") return v.t;
  throw new Error("wiz: tag of a value with no tag");
}

export function wizProj(v, i) {
  /* a projection of `◾` is `◾` (as in the C runtime and the interpreters) */
  if (v === null) return null;
  if (typeof v === "bigint" || typeof v === "number") {
    if (i === 0) return v === 0n || v === 0 ? 0 : 1;
    throw new Error("wiz: internal error: proj of a field of a number (use natTag/pred)");
  }
  if (!Array.isArray(v.f)) throw new Error("wiz: projection from a non-constructor");
  return v.f[i];
}

export function wizTagOf(v) {
  return wizTag(v);
}

export function wizNatTag(v) {
  return v === 0n || v === 0 || v === null ? 0 : 1;
}

export function wizFieldAt(v, n) {
  if (!v || !Array.isArray(v.f)) throw new Error("wiz: fieldAt of a non-constructor");
  const i = Number(n);
  return i < v.f.length ? v.f[i] : null;
}

export function wizMkObj(t, l) {
  const tag = wizTag(t);
  const fields = [];
  let cur = l;
  let fuel = 1000000;
  while (cur !== null && cur !== 0 && cur !== 0n && typeof cur === "object" && cur.t === 1) {
    if (fuel-- === 0) throw new Error("wiz: mkObj: the field list is cyclic");
    fields.push(cur.f[0]);
    cur = cur.f[1];
  }
  return fields.length === 0 ? tag : wizCtor(tag, fields);
}

export function wizDropMoved(x, mask) {
  /* the reference counts `mask` is about are the GC's; the IR value is dropped */
  return 0;
}

export function wizMemo(ty, f) {
  let forced = false;
  let value;
  const thunk = (...args) => {
    if (!forced) {
      forced = true;
      value = wizApply(f, [args[0]]); /* memo A f: f takes the unit */
    }
    return args.length > 1 ? wizApply(value, args.slice(1)) : value;
  };
  thunk.wizThunk = true;
  return thunk;
}

export function wizLazyTag(v) {
  if (v === null) return 0;
  if (typeof v === "object" && typeof v.t === "number") {
    return v.t === 1000 ? 1 : v.t === 1001 ? 2 : v.t === 1002 ? 3 : 0;
  }
  return 0;
}

export function wizLazySet(x, p) {
  /* an observation of a lazy cell: without sharing counts the cell is not
   * overwritten, so a second observation recomputes the same payload. */
  return p;
}

/* ---- numbers: Nat is BigInt, the C runtime's GMP ---- */

export function wizNatLit(digits) {
  return BigInt(digits);
}
export function wiz_nat_succ(a) { return a + 1n; }
export function wiz_nat_pred(a) { return a === 0n ? 0n : a - 1n; }
export function wiz_nat_add(a, b) { return a + b; }
export function wiz_nat_sub(a, b) { return a > b ? a - b : 0n; }
export function wiz_nat_mul(a, b) { return a * b; }
export function wiz_nat_beq(a, b) { return a === b ? 1 : 0; }
export function wiz_nat_blt(a, b) { return a < b ? 1 : 0; }
export function wiz_nat_div(a, b) { return b === 0n ? 0n : a / b; }
export function wiz_nat_mod(a, b) { return b === 0n ? a : a % b; }
export function wiz_nat_land(a, b) { return a & b; }
export function wiz_nat_lor(a, b) { return a | b; }
export function wiz_nat_xor(a, b) { return a ^ b; }
export function wiz_nat_shiftLeft(a, n) {
  if (a !== 0n && n >= WIZ_MAX_BITS) {
    throw new Error("wiz: Nat.shiftLeft: the result would have more than 16777216 bits");
  }
  return a << n;
}
export function wiz_nat_shiftRight(a, n) {
  return n >= 64n && a < (1n << 64n) ? 0n : a >> n;
}
export function wiz_nat_pow(b, e) {
  if (e > WIZ_MAX_BITS) {
    throw new Error("wiz: Nat.pow: the exponent is too large for the JS backend");
  }
  if (b > 1n && e * BigInt(b.toString(2).length) > WIZ_MAX_BITS) {
    throw new Error("wiz: Nat.pow: the result would have more than 16777216 bits");
  }
  return b ** e;
}
export function wiz_nat_log2(a) {
  return a === 0n ? 0n : BigInt(a.toString(2).length - 1);
}

/* ---- UInt64: BigInt below 2^64 ---- */

function wizU64(x) {
  return BigInt(x) & WIZ_MASK64;
}
export function wiz_u64_id(a) { return wizU64(a); }
export function wiz_u64_add(a, b) { return wizU64(a + b); }
export function wiz_u64_sub(a, b) { return wizU64(a - b); }
export function wiz_u64_mul(a, b) { return wizU64(a * b); }
export function wiz_u64_div(a, b) { return b === 0n ? 0n : a / b; }
export function wiz_u64_mod(a, b) { return b === 0n ? a : a % b; }
export function wiz_u64_lt(a, b) { return a < b ? 1 : 0; }
export function wiz_u64_eq(a, b) { return a === b ? 1 : 0; }

/* ---- Float64: a JS number ---- */

export function wiz_f64_of_nat(a) { return Number(a); }
export function wiz_f64_add(a, b) { return a + b; }
export function wiz_f64_sub(a, b) { return a - b; }
export function wiz_f64_mul(a, b) { return a * b; }
export function wiz_f64_div(a, b) { return a / b; }
export function wiz_f64_lt(a, b) { return a < b ? 1 : 0; }

/* `snprintf("%.17g")`, which is what the C runtime's `wiz_f64_show` uses. */
export function wiz_f64_show(x) {
  if (Number.isNaN(x)) return "nan";
  if (!Number.isFinite(x)) return x > 0 ? "inf" : "-inf";
  let mant;
  let exp;
  const sci = x.toExponential(16);
  const e = sci.indexOf("e");
  mant = sci.slice(0, e);
  exp = Number(sci.slice(e + 1));
  let out;
  if (exp >= -4 && exp < 17) out = x.toFixed(16 - exp);
  else out = mant + "e" + (exp >= 0 ? "+" : "-") + String(Math.abs(exp)).padStart(2, "0");
  if (out.indexOf(".") >= 0) {
    const ei = out.indexOf("e");
    let head = ei >= 0 ? out.slice(0, ei) : out;
    const tail = ei >= 0 ? out.slice(ei) : "";
    head = head.replace(/0+$/, "").replace(/\.$/, "");
    out = head + tail;
  }
  return out;
}

/* ---- word operations: `UIntN w` / `IntN w` are BigInt bits ---- */

function wizWordMask(w) {
  return (1n << w) - 1n;
}
function wizWordSigned(w, a) {
  if (w === 0n) return 0n;
  const bit = 1n << (w - 1n);
  return (a & bit) !== 0n ? a - (1n << w) : a;
}
function wizWordBin(w, a, b, f) {
  return f(a, b) & wizWordMask(w);
}
export function wiz_word_of_bits(n) { return n; }
export function wiz_word_to_bits(a) { return a; }
export function wiz_word_of_nat(w, n) { return n & wizWordMask(w); }
export function wiz_word_of_neg(w, n) { return (-n) & wizWordMask(w); }
export function wiz_word_cast(a) { return a; }
export function wiz_word_zext(v, a) { return a & wizWordMask(v); }
export function wiz_word_sext(w, v, a) {
  return wizWordSigned(w, a) & wizWordMask(v);
}
export function wiz_word_add(w, a, b) { return wizWordBin(w, a, b, (x, y) => x + y); }
export function wiz_word_sub(w, a, b) { return wizWordBin(w, a, b, (x, y) => x - y); }
export function wiz_word_mul(w, a, b) { return wizWordBin(w, a, b, (x, y) => x * y); }
export function wiz_word_udiv(w, a, b) { return b === 0n ? 0n : a / b; }
export function wiz_word_umod(w, a, b) { return b === 0n ? a : a % b; }
export function wiz_word_sdiv(w, a, b) {
  if (b === 0n) return 0n;
  const x = wizWordSigned(w, a);
  const y = wizWordSigned(w, b);
  return (x / y) & wizWordMask(w);
}
export function wiz_word_srem(w, a, b) {
  if (b === 0n) return a;
  const x = wizWordSigned(w, a);
  const y = wizWordSigned(w, b);
  return (x % y) & wizWordMask(w);
}
export function wiz_word_and(a, b) { return a & b; }
export function wiz_word_or(a, b) { return a | b; }
export function wiz_word_xor(a, b) { return a ^ b; }
export function wiz_word_not(w, a) { return (~a) & wizWordMask(w); }
export function wiz_word_shl(w, a, k) {
  return k >= w ? 0n : (a << k) & wizWordMask(w);
}
export function wiz_word_lshr(a, k) { return a >> k; }
export function wiz_word_ashr(w, a, k) {
  if (w === 0n) return 0n;
  const x = wizWordSigned(w, a);
  return (x >> (k >= w ? w - 1n : k)) & wizWordMask(w);
}
export function wiz_word_eq(a, b) { return a === b ? 1 : 0; }
export function wiz_word_ult(a, b) { return a < b ? 1 : 0; }
export function wiz_word_ule(a, b) { return a <= b ? 1 : 0; }
export function wiz_word_slt(w, a, b) {
  return wizWordSigned(w, a) < wizWordSigned(w, b) ? 1 : 0;
}
export function wiz_word_sle(w, a, b) {
  return wizWordSigned(w, a) <= wizWordSigned(w, b) ? 1 : 0;
}
export function wiz_word_bit(a, i) { return ((a >> i) & 1n) === 1n ? 1 : 0; }
export function wiz_word_msb(w, a) { return w === 0n ? 0 : wiz_word_bit(a, w - 1n); }

/* ---- Bytes: a Uint8Array (functional: push copies) ---- */

export function wiz_bytes_empty() { return new Uint8Array(0); }
export function wiz_bytes_push(v, x) {
  const out = new Uint8Array(v.length + 1);
  out.set(v);
  out[v.length] = Number(x & 0xffn);
  return out;
}
export function wiz_bytes_size(v) { return BigInt(v.length); }
export function wiz_bytes_get(v, i) {
  return i < BigInt(v.length) ? BigInt(v[Number(i)]) : 0n;
}
export function wiz_bytes_of_string(s) {
  const b = new TextEncoder().encode(s);
  const nul = b.indexOf(0);
  return nul < 0 ? b : b.slice(0, nul);
}
export function wiz_bytes_to_string(v) {
  const nul = v.indexOf(0);
  return new TextDecoder().decode(nul < 0 ? v : v.slice(0, nul));
}
export function wiz_bytes_slice(v, start, len) {
  return v.slice(Number(start), Number(start) + Number(len));
}
export function wiz_bytes_append(a, b) {
  const out = new Uint8Array(a.length + b.length);
  out.set(a);
  out.set(b, a.length);
  return out;
}
export function wiz_bytes_eq(a, b) {
  if (a.length !== b.length) return 0;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return 0;
  return 1;
}

/* ---- Array: a JS array, copied on `set` (the Wiz value is functional) ---- */

export function wiz_array_empty() { return []; }
export function wiz_array_push(v, x) { return v.concat([x]); }
export function wiz_array_size(v) { return BigInt(v.length); }
export function wiz_array_get(v, i, dflt) {
  const k = Number(i);
  return k < v.length ? v[k] : dflt;
}
export function wiz_array_set(v, i, x) {
  const k = Number(i);
  if (k >= v.length) return v;
  const out = v.slice();
  out[k] = x;
  return out;
}

/* ---- strings are the Wiz data type (code points), converted at the FFI ---- */

function wizCodePoint(c) {
  const cp = Number(c);
  if (!Number.isInteger(cp) || cp < 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) {
    return 0xfffd; /* the C runtime encodes a non-scalar as U+FFFD */
  }
  return cp;
}

export function wizStringToJs(v) {
  if (typeof v === "string") return v;
  if (!v || !Array.isArray(v.f)) throw new Error("wiz: not a String");
  let l = v.f[0];
  const parts = [];
  let fuel = 10000000;
  while (l !== null && typeof l === "object" && l.t === 1) {
    if (fuel-- === 0) throw new Error("wiz: a String is cyclic");
    const ch = l.f[0];
    parts.push(String.fromCodePoint(wizCodePoint(ch.f[0])));
    l = l.f[1];
  }
  return parts.join("");
}

export function wizString(s) {
  const chars = Array.from(s); /* code points, not UTF-16 units */
  let l = 0; /* List.nil: a constructor without fields is its tag */
  for (let i = chars.length - 1; i >= 0; i--) {
    const cp = wizCodePoint(chars[i].codePointAt(0));
    l = wizCtor(1, [wizCtor(0, [BigInt(cp)]), l]);
  }
  return wizCtor(0, [l]); /* String.mk (data : List Char) */
}

/* ---- output and the command-line runner ---- */

export function wizOut(s) {
  if (typeof process !== "undefined" && process.stdout && process.stdout.write) {
    process.stdout.write(s);
  } else if (s.endsWith("\n")) {
    console.log(s.slice(0, -1));
  } else {
    console.log(s);
  }
}

function wizArgv() {
  return typeof process !== "undefined" && process.argv ? process.argv.slice(2) : [];
}

export function wizShow(v) {
  if (typeof v === "bigint") return v.toString();
  if (typeof v === "number") return String(v);
  if (v === null) return "0";
  if (typeof v === "function") return "<fn>";
  if (v && Array.isArray(v.f)) {
    return "(" + v.t + (v.f.length === 0 ? "" : " " + v.f.map(wizShow).join(" ")) + ")";
  }
  return "<handle>";
}

export function wizRunCli(main, io) {
  try {
    if (io) {
      main();
    } else {
      wizOut(wizShow(main()) + "\n");
    }
  } catch (e) {
    const msg = e && e.message ? e.message : String(e);
    if (typeof process !== "undefined" && process.stderr) process.stderr.write(msg + "\n");
    else console.error(msg);
    if (typeof process !== "undefined") process.exitCode = 1;
  }
}

export function wizFileUrl(path) {
  const p = path.startsWith("/") ? path : "/" + path;
  return new URL("file://" + p).href;
}

export function wizIoResult(v, world) {
  return wizCtor(0, [v, world]);
}

/* ---- the FFI: `extern "js.path"` and the runtime natives ---- */

const WIZ_NATIVES = Object.create(null);
function wizNative(name, fn) {
  WIZ_NATIVES[name] = fn;
}

wizNative("wiz_nat_show", (n) => n.toString());
wizNative("wiz_io_println", (s) => {
  wizOut(s + "\n");
  return 0;
});
wizNative("wiz_io_print", (s) => {
  wizOut(s);
  return 0;
});
wizNative("wiz_io_arg_count", () => BigInt(wizArgv().length));
wizNative("wiz_io_arg", (i) => wizArgv()[Number(i)] ?? "");

for (const [name, fn] of Object.entries({
  wiz_u64_id,
  wiz_u64_add,
  wiz_u64_sub,
  wiz_u64_mul,
  wiz_u64_div,
  wiz_u64_mod,
  wiz_u64_lt,
  wiz_u64_eq,
  wiz_f64_of_nat,
  wiz_f64_add,
  wiz_f64_sub,
  wiz_f64_mul,
  wiz_f64_div,
  wiz_f64_lt,
  wiz_f64_show,
  wiz_bytes_empty,
  wiz_bytes_push,
  wiz_bytes_size,
  wiz_bytes_get,
  wiz_bytes_of_string,
  wiz_bytes_to_string,
  wiz_bytes_slice,
  wiz_bytes_append,
  wiz_bytes_eq,
  wiz_array_empty,
  wiz_array_push,
  wiz_array_size,
  wiz_array_get,
  wiz_array_set,
  wiz_word_of_bits,
  wiz_word_to_bits,
  wiz_word_of_nat,
  wiz_word_of_neg,
  wiz_word_cast,
  wiz_word_zext,
  wiz_word_sext,
  wiz_word_add,
  wiz_word_sub,
  wiz_word_mul,
  wiz_word_udiv,
  wiz_word_umod,
  wiz_word_sdiv,
  wiz_word_srem,
  wiz_word_and,
  wiz_word_or,
  wiz_word_xor,
  wiz_word_not,
  wiz_word_shl,
  wiz_word_lshr,
  wiz_word_ashr,
  wiz_word_eq,
  wiz_word_ult,
  wiz_word_ule,
  wiz_word_slt,
  wiz_word_sle,
  wiz_word_bit,
  wiz_word_msb,
})) {
  wizNative(name, fn);
}

function wizToBigInt(v) {
  if (typeof v === "bigint") return v;
  if (typeof v === "number") return BigInt(Math.trunc(v));
  if (typeof v === "string") return BigInt(v);
  if (typeof v === "boolean") return v ? 1n : 0n;
  throw new Error("wiz: not a number: " + wizShow(v));
}

function wizToJs(kind, v) {
  switch (kind) {
    case "n":
    case "u":
      return wizToBigInt(v);
    case "f":
      return Number(v);
    case "s":
      return wizStringToJs(v);
    case "b":
      return !(v === 0 || v === 0n || v === null);
    case "v":
      return v;
    case "p":
    case "w":
    default:
      return v;
  }
}

function wizFromJs(kind, v) {
  switch (kind) {
    case "n":
      return wizToBigInt(v);
    case "u":
      return wizToBigInt(v) & WIZ_MASK64;
    case "f":
      return Number(v);
    case "s":
      return wizString(v === undefined || v === null ? "" : String(v));
    case "b":
      return v ? 1 : 0;
    case "v":
      return v === undefined ? 0 : v;
    case "p":
    case "w":
    default:
      return v;
  }
}

function wizResolve(path) {
  const parts = path.split(".");
  let self = globalThis;
  for (let i = 0; i < parts.length - 1; i++) {
    self = self != null ? self[parts[i]] : undefined;
    if (self == null) throw new Error("wiz: no JavaScript host object at `" + path + "`");
  }
  const name = parts[parts.length - 1];
  const fn = self[name];
  if (typeof fn !== "function") {
    throw new Error("wiz: `" + path + "` is not a JavaScript function");
  }
  return [self, fn];
}

export function wizCallJs(path, args) {
  const [self, fn] = wizResolve(path);
  return fn.apply(self, args);
}

/* A foreign call: the key is the IR's `extern:cname:kinds:result:io:header:fin`.
 * The kinds are checked by the emitter (`Wiz/Compiler/Js.lean`): structs, callbacks
 * and byte buffers with a length are refused there, so a kind here is one letter. */
export function wizExtern(key, args) {
  const parts = key.split(":");
  if (parts.length !== 7 || parts[0] !== "extern") {
    throw new Error("wiz: not a foreign-function key: " + key);
  }
  const cname = parts[1];
  const kinds = parts[2];
  const resultKind = parts[3];
  const io = parts[4] === "io";
  const callArgs = [];
  for (let i = 0; i < kinds.length; i++) {
    /* an erased parameter (`{0 w : Nat}`, a proof) is passed as `◾` and skipped,
     * exactly as the C glue skips an `e` kind */
    if (kinds[i] === "e") continue;
    callArgs.push(wizToJs(kinds[i], args[i]));
  }
  const world = io ? args[kinds.length] : undefined;
  let r;
  const native = WIZ_NATIVES[cname];
  if (native) {
    r = native(...callArgs);
  } else if (cname.startsWith("js.")) {
    r = wizCallJs(cname.slice(3), callArgs);
  } else {
    throw new Error("wiz: no JavaScript runtime for `" + cname + "`");
  }
  const value = wizFromJs(resultKind, r);
  return io ? wizIoResult(value, world) : value;
}
