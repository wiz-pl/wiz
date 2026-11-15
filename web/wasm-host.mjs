// The JS host of the experimental WebAssembly backend (stage 8f).
//
//   node web/wasm-host.mjs FILE.wasm      print the result of `wiz_main`
//
// The module owns all values (constructors, closures, arrays) in its linear memory; the
// host supplies only big integers (Nat above 62 bits) as BigInts, and decodes the result
// in the same generic tree syntax as the C runtime (`web/build.sh`'s modules do not use
// this file).
//
// Import convention for a "big value": 0n means "a small value, use the second word",
// otherwise the word is a handle with bit 63 set (the index of a BigInt in the table).
// A host result is either a Wiz scalar (`(v << 1) | 1`, for v < 2^62) or a handle.
const SMALL = 1n << 62n;
const HANDLE_BIT = 1n << 63n;
const HANDLE_MASK = HANDLE_BIT - 1n;
const TAG_CLO = 0xffff0000;
const TAG_BIG = 0xffff0001;
const TAG_THUNK = 0xffff0008;

function decodeUTF8(bytes) {
  return new TextDecoder().decode(bytes);
}

export async function instantiate(source) {
  // (a path needs Node's `fs`; bytes work in a browser too, so the import is lazy)
  const bytes = typeof source === 'string' ? (await import('node:fs')).readFileSync(source) : source;
  const bigs = [];
  let ex = null;

  const view = () => new DataView(ex.memory.buffer);
  const u8 = () => new Uint8Array(ex.memory.buffer);
  const text = (ptr, len) => decodeUTF8(u8().subarray(ptr, ptr + len));

  // (the index is shifted left so a handle's bit 0 stays 0, like an object pointer:
  // the module uses bit 0 to tell a scalar from a boxed value)
  const allocBig = (v) => {
    bigs.push(v);
    return HANDLE_BIT | (BigInt(bigs.length - 1) << 1n);
  };
  const handleIndex = (h) => Number((h & HANDLE_MASK) >> 1n);
  const valueOf = (h, small) => (h !== 0n ? bigs[handleIndex(h)] : small);
  // A BigInt as a Wiz value: a small scalar when it fits, else a host handle.
  const norm = (v) => (v >= 0n && v < SMALL ? (v << 1n) | 1n : allocBig(v));
  const asIndex = (v) => {
    const n = Number(v);
    if (!Number.isSafeInteger(n) || n < 0 || n > 0x1_0000_0000_0000) {
      throw new RangeError('Wiz (Wasm): big shift or exponent out of range in this prototype');
    }
    return n;
  };

  const imports = {
    env: {
      big_of_dec(ptr, len) {
        return norm(BigInt(text(ptr, len)));
      },
      big_op(op, ah, av, bh, bv) {
        const a = valueOf(ah, av);
        const b = valueOf(bh, bv);
        let r;
        switch (op) {
          case 0: r = a + b; break;
          case 1: r = a > b ? a - b : 0n; break;             // saturating Nat subtraction
          case 2: r = a * b; break;
          case 3: r = b === 0n ? 0n : a / b; break;          // n / 0 = 0
          case 4: r = b === 0n ? a : a % b; break;           // n % 0 = n
          case 5: r = a & b; break;
          case 6: r = a | b; break;
          case 7: r = a ^ b; break;
          case 8: r = a << BigInt(asIndex(b)); break;
          case 9: r = b >= 64n ? 0n : a >> b; break;
          case 10: {
            const e = asIndex(b);
            if (e > 100000) throw new RangeError('Wiz (Wasm): exponent too large in this prototype');
            r = a ** BigInt(e);
            break;
          }
          default: throw new RangeError(`Wiz (Wasm): unknown big operation ${op}`);
        }
        return norm(r);
      },
      big_cmp(ah, av, bh, bv) {
        const a = valueOf(ah, av);
        const b = valueOf(bh, bv);
        return a < b ? -1 : a > b ? 1 : 0;
      },
      big_log2(ah, av) {
        const a = valueOf(ah, av);
        if (a === 0n) return 1n; // WIZ_BOX(0)
        const n = a.toString(2).length - 1;
        return (BigInt(n) << 1n) | 1n;
      },
      big_to_dec(h, ptr) {
        const digits = bigs[handleIndex(h)].toString(10);
        const bytes = new TextEncoder().encode(digits);
        u8().set(bytes, ptr);
        return bytes.length;
      },
    },
  };

  const { instance } = await WebAssembly.instantiate(bytes, imports);
  ex = instance.exports;
  return ex;
}

/** The generic tree syntax of the C runtime (runtime/rt_sys.inc's `wiz_print`). */
export function show(ex, v) {
  if ((v & 1n) !== 0n) return (v >> 1n).toString();
  const p = Number(v);
  const tag = ex.wiz_value_tag(v) >>> 0;
  if (tag === TAG_CLO || tag === TAG_THUNK) return '<fn>';
  if (tag === TAG_BIG) {
    const packed = ex.wiz_big_digits(v);
    const ptr = Number(packed >> 32n);
    const len = Number(packed & 0xffff_ffffn);
    return decodeUTF8(new Uint8Array(ex.memory.buffer, ptr, len));
  }
  const size = new DataView(ex.memory.buffer).getUint32(p + 8, true);
  let out = `(${tag}`;
  for (let i = 0; i < size; i++) out += ' ' + show(ex, ex.wiz_value_field(v, i));
  return out + ')';
}

/** Run an IO-less `main` and return its result as text. */
export async function run(source) {
  const ex = await instantiate(source);
  return show(ex, ex.wiz_main());
}

if (typeof process !== 'undefined' && process.argv[1] &&
    import.meta.url === (await import('node:url')).pathToFileURL(process.argv[1]).href) {
  const file = process.argv[2];
  if (!file) {
    console.error('usage: node web/wasm-host.mjs FILE.wasm');
    process.exit(2);
  }
  const ex = await instantiate(file);
  process.stdout.write(show(ex, ex.wiz_main()) + '\n');
}
