#!/usr/bin/env node
// Prototype WGSL emitter for a data-parallel Wiz subset.
//
//   node webgpu/tools/wgsl.mjs --input webgpu/kernels/add.wiz --entry add
//
// The front end is the *real* Wiz parser: `wiz parse FILE` prints one s-expression per
// command (see `wiz parse` in Main.lean), and this file only reads that tree. It does not
// parse Wiz itself, so the subset below is a restriction on what the parser can produce,
// not a second grammar. `wiz parse` sees builtin syntax only (no `import`-provided
// notation: `+`, `[a, b]` and `if … then … else` are library macros), which is why the
// kernels use `U32.add`, `Array.getD`, and `match` instead.
//
// What is accepted (the v0 subset — see wiz-notes/webgpu-target.md):
//   types      U32, Bool, Nat (index only), Array U32 (buffer parameters only)
//   terms      variables, let, match on Bool, calls to other kernels (acyclic)
//   prims      U32.ofNat, UIntN.add/sub/mul/land/lor/xor, UIntN.lt/le/beq,
//              Array.getD buf i 0  (division/modulo are rejected: WGSL leaves a zero
//              divisor unspecified while Wiz defines a / 0 = 0)
//   rejected   everything else: no constructors, no closures, no recursion, no
//              allocation, no Array.push/set, no Nat arithmetic, no floats, no IO/FFI.
//
// The emitted WGSL is straight-line: a kernel is a scalar function applied at every
// index; the loop is the dispatch and `match` becomes `select` (both arms evaluated).
// Buffer parameters become storage bindings; the one result buffer is written by `main`.

import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname, resolve } from 'node:path';

class Reject extends Error {}

const fail = (msg) => { throw new Reject(msg); };

// ---------------------------------------------------------------- s-expressions

// `wiz parse` prints `(a b [c d])` with both kinds of brackets as grouping. Atoms are
// everything else. Strings are not needed by the subset and are rejected.
function parseSexpr(text) {
  let i = 0;
  const ws = () => { while (i < text.length && /\s/.test(text[i])) i++; };
  const atom = () => {
    const start = i;
    while (i < text.length && !/[\s()\[\]]/.test(text[i])) i++;
    return text.slice(start, i);
  };
  const list = (close) => {
    i++; // ( or [
    const out = [];
    for (;;) {
      ws();
      if (i >= text.length) fail(`unterminated ${close}`);
      if (text[i] === close) { i++; return out; }
      if (text[i] === '(') out.push(list(')'));
      else if (text[i] === '[') out.push(list(']'));
      else out.push(atom());
    }
  };
  const out = [];
  for (;;) {
    ws();
    if (i >= text.length) break;
    if (text[i] === '(') out.push(list(')'));
    else if (text[i] === '[') out.push(list(']'));
    else {
      const a = atom();
      if (a === '') fail(`unexpected '${text[i]}' at ${i}`);
      out.push(a);
    }
  }
  return out;
}

// ---------------------------------------------------------------- kernel IR

// A parsed kernel parameter: a name and a subset type.
//   { kind: 'Nat' } | { kind: 'U32' } | { kind: 'Bool' } | { kind: 'Array', elem: 'U32' }

const isIdent = (t) => Array.isArray(t) && t.length >= 1 && t[0] === 'term.ident';

// A printable form of a type expression, so a rejection names what the reader wrote
// (`Float64`, `IO U32`, `Array Bool`) rather than "unsupported type expression".
function renderType(t) {
  if (isIdent(t)) return t[1];
  if (Array.isArray(t) && t[0] === 'term.paren') return renderType(t[1]);
  if (Array.isArray(t) && t[0] === 'term.app' && isIdent(t[1]))
    return [t[1][1], ...(t[2] || []).map(renderType)].join(' ');
  return 'this type expression';
}

function typeOfTerm(t, where) {
  if (isIdent(t)) {
    const name = t[1];
    if (name === 'Nat') return { kind: 'Nat' };
    if (name === 'U32') return { kind: 'U32' };
    if (name === 'Bool') return { kind: 'Bool' };
    fail(`${where}: unsupported type ${name} (the WebGPU subset has only U32, Bool, Nat and Array U32)`);
  }
  if (Array.isArray(t) && t[0] === 'term.app' && isIdent(t[1]) && t[1][1] === 'Array') {
    const args = t[2] || [];
    if (args.length !== 1) fail(`${where}: Array needs one element type`);
    if (!isIdent(args[0]) || args[0][1] !== 'U32')
      fail(`${where}: only Array U32 buffers are supported (got Array ${renderType(args[0])})`);
    return { kind: 'Array', elem: 'U32' };
  }
  fail(`${where}: unsupported type ${renderType(t)} (the WebGPU subset has only U32, Bool, Nat and Array U32)`);
}

// WGSL has one namespace and a fixed keyword list; a Wiz name that is a WGSL keyword
// would either fail validation or, worse, name a different thing after renaming.
const WGSL_RESERVED = new Set([
  'alias', 'array', 'atomic', 'binding', 'bitcast', 'bool', 'break', 'builtin', 'case',
  'const', 'continue', 'default', 'discard', 'else', 'f16', 'f32', 'false', 'fn', 'for',
  'function', 'global_invocation_id', 'group', 'i32', 'if', 'in', 'let', 'location', 'loop',
  'main', 'out', 'override', 'private', 'ptr', 'read', 'read_write', 'return', 'storage',
  'struct', 'switch', 'true', 'u32', 'uniform', 'var', 'vec2', 'vec3', 'vec4', 'while',
  'workgroup', 'write',
]);
function checkName(name, at) {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name))
    fail(`${at}: '${name}' is not a WGSL identifier`);
  if (WGSL_RESERVED.has(name))
    fail(`${at}: '${name}' is a WGSL keyword or reserved name (rename it)`);
}

function flattenBinders(binders, where) {
  const params = [];
  const seen = new Set();
  for (const b of binders) {
    if (!Array.isArray(b) || b[0] !== 'binder.explicit')
      fail(`${where}: implicit/instance binders are not in the subset`);
    const names = b[2] || [];
    const types = b[3] || [];
    if (types.length !== 1) fail(`${where}: every parameter needs one type`);
    const ty = typeOfTerm(types[0], where);
    for (const n of names) {
      if (seen.has(n)) fail(`${where}: duplicate parameter '${n}'`);
      seen.add(n);
      checkName(n, where);
      params.push({ name: n, type: ty });
    }
  }
  return params;
}

function defsOf(forms) {
  const defs = new Map();
  for (const f of forms) {
    if (!Array.isArray(f) || f[0] !== 'command.def') continue;
    // (command.def NAME UNIVERSE? BINDERS RET BODY)
    const [, rawName, universes, binders, ret, body] = f;
    if (universes && universes.length) fail(`${rawName}: universe parameters are not in the subset`);
    if (body === undefined) fail(`${rawName}: a def without a body (a declaration/axiom) is not a kernel`);
    const name = rawName;
    if (typeof name !== 'string' || !/^[A-Za-z_][A-Za-z0-9_]*$/.test(name))
      fail(`${name}: kernel names must be plain identifiers (no namespaces or operators)`);
    checkName(name, name);
    if (defs.has(name)) fail(`${name}: duplicate kernel definition`);
    // `wiz parse` prints the result types as a list (Wiz has multiple results); a kernel
    // has exactly one.
    if (!Array.isArray(ret) || ret.length !== 1) fail(`${name}: a kernel returns exactly one type`);
    defs.set(name, {
      name,
      params: flattenBinders(binders || [], name),
      ret: typeOfTerm(ret[0], name),
      rawBody: body,
    });
  }
  return defs;
}

// Type inference and lowering share one pass.  `env` maps local names to subset types;
// `buffers` is the set of Array-typed parameter names visible in this def.
//
// The result is an expression tree:
//   { k: 'var', name } | { k: 'u32', value } | { k: 'read', buf, index, def }
//   { k: 'bin', op, left, right } | { k: 'cmp', op, left, right }
//   { k: 'select', cond, yes, no } | { k: 'call', name, args }
// Every node carries `type`.
function lowerExpr(term, ctx) {
  const at = ctx.where;
  if (isIdent(term)) {
    const name = term[1];
    const ty = ctx.env.get(name);
    if (!ty) fail(`${at}: '${name}' is not a parameter or local (a global/axiom is not in the subset)`);
    if (ty.kind === 'Array') fail(`${at}: a buffer may only be read with Array.getD (a buffer is not a value)`);
    return { k: 'var', name: ctx.rename.get(name) ?? name, type: ty };
  }
  if (Array.isArray(term) && term[0] === 'term.paren') return lowerExpr(term[1], ctx);
  if (Array.isArray(term) && term[0] === 'term.fun')
    fail(`${at}: lambdas and closures are not in the subset (WGSL has no function values)`);
  if (Array.isArray(term) && term[0] === 'term.num')
    fail(`${at}: bare numerals are not in the subset; write U32.ofNat N`);
  if (Array.isArray(term) && term[0] === 'term.let') {
    // (term.let IMPLICIT NAME TYPE VALUE ? BODY)
    const [, implicit, name, tyTerm, value, extra, body] = term;
    if ((implicit && implicit.length) || (extra && extra.length))
      fail(`${at}: implicit let bindings are not in the subset`);
    if (!body) fail(`${at}: malformed let`);
    if (typeof name !== 'string') fail(`${at}: a let must bind a plain name (pattern lets are not in the subset)`);
    checkName(name, at);
    // The annotation is a list of result types; a kernel let binds exactly one value.
    const types = Array.isArray(tyTerm) ? tyTerm : [tyTerm];
    if (types.length !== 1) fail(`${at}: a let must bind one value (multiple results are not in the subset)`);
    const ty = typeOfTerm(types[0], at);
    if (ty.kind === 'Array') fail(`${at}: a let-bound Array would be an allocation; buffers are parameters`);
    const v = lowerExpr(value, ctx);
    checkEq(v.type, ty, `${at}: let ${name}`);
    const inner = new Map(ctx.env);
    // Alpha-rename the binding: WGSL has one flat scope per function and the emitter
    // hoists every let, so a shadowing Wiz let must not reuse the outer name.
    const local = freshLocal(name, ctx.taken);
    inner.set(name, ty);
    const renaming = new Map(ctx.rename);
    renaming.set(name, local);
    const lowered = lowerExpr(body, { ...ctx, env: inner, rename: renaming });
    return { k: 'let', name: local, value: v, body: lowered, type: ty };
  }
  if (Array.isArray(term) && term[0] === 'term.match') {
    const scrutinees = term[1] || [];
    const alts = term[2] || [];
    if (scrutinees.length !== 1) fail(`${at}: only a one-scrutinee match on Bool is in the subset`);
    const cond = lowerExpr(scrutinees[0], ctx);
    if (cond.type.kind !== 'Bool') fail(`${at}: only match on Bool is in the subset`);
    if (alts.length !== 2) fail(`${at}: a Bool match needs exactly two arms`);
    let yes = null, no = null;
    for (const alt of alts) {
      // (match.alt [(term.dotIdent true)] BODY)
      const pats = alt[1] || [];
      if (pats.length !== 1 || !Array.isArray(pats[0]) || pats[0][0] !== 'term.dotIdent')
        fail(`${at}: only the patterns .true and .false are in the subset`);
      const tag = pats[0][1];
      if (tag !== 'true' && tag !== 'false') fail(`${at}: only .true/.false patterns are in the subset`);
      if ((tag === 'true' ? yes : no) !== null) fail(`${at}: duplicate match arm .${tag}`);
      const body = lowerExpr(alt[2], ctx);
      if (tag === 'true') yes = body; else no = body;
    }
    if (!yes || !no) fail(`${at}: a Bool match needs both .true and .false`);
    checkEq(yes.type, no.type, `${at}: match arms`);
    return { k: 'select', cond, yes, no, type: yes.type };
  }
  if (Array.isArray(term) && term[0] === 'term.app') {
    const callee = term[1];
    const args = term[2] || [];
    if (!isIdent(callee)) {
      if (Array.isArray(callee) && callee[0] === 'term.fun')
        fail(`${at}: lambdas and closures are not in the subset (WGSL has no function values)`);
      if (Array.isArray(callee) && callee[0] === 'term.paren' &&
          Array.isArray(callee[1]) && callee[1][0] === 'term.fun')
        fail(`${at}: lambdas and closures are not in the subset (WGSL has no function values)`);
      fail(`${at}: higher-order application is not in the subset (the callee must be a name)`);
    }
    const name = callee[1];
    // `Array.getD` must see its first argument as a buffer name, not as a value, so it is
    // handled before the arguments are lowered.
    if (name === 'Array.getD') {
      needArity(name, args, 3, at);
      const buf = args[0];
      if (!isIdent(buf)) fail(`${at}: Array.getD's first argument must be a buffer parameter`);
      const ty = ctx.env.get(buf[1]);
      if (!ty || ty.kind !== 'Array') fail(`${at}: '${buf[1]}' is not an Array U32 parameter`);
      const index = lowerExpr(args[1], ctx);
      if (index.type.kind !== 'Nat') fail(`${at}: a buffer index must be a Nat`);
      const dflt = lowerExpr(args[2], ctx);
      // The default must be the zero the WGSL robust-access rule gives for an
      // out-of-range read; otherwise the two runtimes would differ.
      if (!(dflt.k === 'u32' && dflt.value === 0))
        fail(`${at}: Array.getD's default must be U32.ofNat 0 (WGSL reads 0 out of range)`);
      if (!ctx.buffers.has(buf[1])) fail(`${at}: '${buf[1]}' is not a buffer parameter of this kernel`);
      return { k: 'read', buf: buf[1], index, type: { kind: 'U32' } };
    }
    // `U32.ofNat` takes a syntax-level numeral, so it is handled before the arguments are
    // lowered too (a bare numeral is not otherwise a term of the subset).
    if (name === 'U32.ofNat') {
      needArity(name, args, 1, at);
      const n = args[0];
      if (!Array.isArray(n) || n[0] !== 'term.num') fail(`${at}: U32.ofNat takes a numeral`);
      const v = Number(n[1]);
      if (!Number.isInteger(v) || v < 0 || v >= 2 ** 32) fail(`${at}: ${n[1]} is not a u32 literal`);
      return { k: 'u32', value: v, type: { kind: 'U32' } };
    }
    // Name-based rejections run before the arguments are lowered, so the diagnostic names
    // the construct the reader wrote even when an argument is itself outside the subset.
    if (name.startsWith('Array.'))
      fail(`${at}: ${name} is not in the subset (a kernel cannot allocate or resize; only Array.getD buf i (U32.ofNat 0) reads a buffer)`);
    if (name.startsWith('Nat.'))
      fail(`${at}: Nat arithmetic is not in the subset (${name}: Nat is unbounded and a GPU has only 32-bit words)`);
    if (name === 'UIntN.div' || name === 'UIntN.mod')
      fail(`${at}: ${name} is not in the subset (Wiz defines a / 0 = 0; WGSL leaves a zero divisor unspecified)`);
    const lowered = args.map((a) => lowerExpr(a, ctx));
    switch (name) {
      case 'UIntN.add': case 'UIntN.sub': case 'UIntN.mul':
      case 'UIntN.land': case 'UIntN.lor': case 'UIntN.xor':
        needArity(name, args, 2, at);
        needU32(name, lowered, at);
        return { k: 'bin', op: name.slice(6).toLowerCase(), left: lowered[0], right: lowered[1], type: { kind: 'U32' } };
      case 'UIntN.lt': case 'UIntN.le': case 'UIntN.beq':
        needArity(name, args, 2, at);
        needU32(name, lowered, at);
        const op = name.slice(6).toLowerCase() === 'beq' ? 'eq' : name.slice(6).toLowerCase();
        return { k: 'cmp', op, left: lowered[0], right: lowered[1], type: { kind: 'Bool' } };
      default: {
        const def = ctx.defs.get(name);
        if (!def) fail(`${at}: '${name}' is not in the subset (unknown or non-kernel function; FFI, Array.push/set, Nat arithmetic, floats and IO are rejected)`);
        if (ctx.stack.includes(name)) fail(`${at}: recursion is not in the subset (${[...ctx.stack, name].join(' -> ')})`);
        if (ctx.calls) ctx.calls.add(name);
        if (def.params.length !== lowered.length) fail(`${at}: ${name} takes ${def.params.length} arguments, got ${lowered.length}`);
        for (let i = 0; i < lowered.length; i++) {
          if (def.params[i].type.kind === 'Array')
            fail(`${at}: helper kernels may not take buffers (buffer reads belong to the entry kernel)`);
          checkEq(lowered[i].type, def.params[i].type, `${at}: argument ${i + 1} of ${name}`);
        }
        return {
          k: 'call', name, args: lowered, type: def.ret,
          // the callee's own body is lowered when the def is emitted; this records the
          // edge for the acyclicity check below.
        };
      }
    }
  }
  fail(`${at}: unsupported term ${JSON.stringify(term).slice(0, 120)}`);
}

// WGSL lets are statements, and the subset has no control flow inside a kernel, so the
// lowerer keeps let nodes and `flatten` emits them in evaluation order before the return.
// Bindings are alpha-renamed (freshLocal) so hoisting them into one flat scope is sound.
let localCounter = 0;
function freshLocal(name, taken) {
  let n;
  do { n = `${name}_${localCounter++}`; } while (taken.has(n));
  taken.add(n);
  return n;
}

function flatten(e, decls) {
  switch (e.k) {
    case 'var':
    case 'u32': return e;
    case 'read': return { ...e, index: flatten(e.index, decls) };
    case 'bin':
    case 'cmp': return { ...e, left: flatten(e.left, decls), right: flatten(e.right, decls) };
    case 'select': return {
      ...e,
      cond: flatten(e.cond, decls),
      yes: flatten(e.yes, decls),
      no: flatten(e.no, decls),
    };
    case 'call': return { ...e, args: e.args.map((a) => flatten(a, decls)) };
    case 'let': {
      // The value's own lets come first, then this binding, then the body.
      const value = flatten(e.value, decls);
      decls.push(`let ${e.name} : ${WGSL_TYPE[e.type.kind]} = ${emitExpr(value)};`);
      return flatten(e.body, decls);
    }
    default: throw new Error(`internal: flatten ${e.k}`);
  }
}

function checkEq(got, want, at) {
  if (got.kind !== want.kind || (want.kind === 'Array' && got.elem !== want.elem))
    fail(`${at}: expected ${typeName(want)}, got ${typeName(got)}`);
}
function typeName(t) { return t.kind === 'Array' ? `Array ${t.elem}` : t.kind; }
function needArity(name, args, n, at) { if (args.length !== n) fail(`${at}: ${name} takes ${n} arguments, got ${args.length}`); }
function needU32(name, args, at) {
  for (const a of args) if (a.type.kind !== 'U32') fail(`${at}: ${name} takes U32 arguments`);
}

// ---------------------------------------------------------------- WGSL text

const WGSL_BIN = { add: '+', sub: '-', mul: '*', div: '/', mod: '%', land: '&', lor: '|', xor: '^' };
const WGSL_CMP = { lt: '<', le: '<=', eq: '==' };
const WGSL_TYPE = { U32: 'u32', Bool: 'bool', Nat: 'u32' };

function emitExpr(e) {
  switch (e.k) {
    case 'var': return e.name;
    case 'u32': return `${e.value}u`;
    case 'read': return `${e.buf}[${emitExpr(e.index)}]`;
    case 'bin': return `(${emitExpr(e.left)} ${WGSL_BIN[e.op]} ${emitExpr(e.right)})`;
    case 'cmp': return `(${emitExpr(e.left)} ${WGSL_CMP[e.op]} ${emitExpr(e.right)})`;
    case 'select': return `select(${emitExpr(e.no)}, ${emitExpr(e.yes)}, ${emitExpr(e.cond)})`;
    case 'call': return `${e.name}(${e.args.map(emitExpr).join(', ')})`;
    default: throw new Error(`internal: ${e.k}`);
  }
}

// A lowered def is kept as the raw term plus its environment; `emitDef` lowers it again
// with the def's own parameters in scope. (The lowering is total and cheap, and doing it
// twice keeps the two call sites — entry and helper — independent.)
function lowerDef(def, defs, calls = null) {
  const env = new Map();
  const buffers = new Set();
  for (const p of def.params) {
    env.set(p.name, p.type);
    if (p.type.kind === 'Array') buffers.add(p.name);
  }
  localCounter = 0;
  return lowerExpr(def.rawBody, {
    env, buffers, defs, calls, stack: [def.name], where: def.name, rename: new Map(),
    taken: new Set(def.params.map((p) => p.name)),
  });
}

// A lowered def becomes `let …` declarations plus one return expression.
function emitFunctionBody(e) {
  const decls = [];
  const body = flatten(e, decls);
  return `${decls.map((d) => `  ${d}`).join('\n')}${decls.length ? '\n' : ''}  return ${emitExpr(body)};`;
}

function emitDef(def, defs) {
  const scalarParams = def.params.filter((p) => p.type.kind !== 'Array');
  const ret = def.ret.kind === 'Bool' ? 'bool' : 'u32';
  const body = lowerDef(def, defs);
  const head = `fn ${def.name}(${scalarParams.map((p) => `${p.name} : ${WGSL_TYPE[p.type.kind]}`).join(', ')}) -> ${ret}`;
  return `${head} {\n${emitFunctionBody(body)}\n}`;
}

function emitModule({ sourceName, defs, entryName }) {
  const entry = defs.get(entryName);
  if (!entry) fail(`entry kernel '${entryName}' is not defined`);
  if (entry.params.length < 1) fail(`${entryName}: the entry kernel needs a Nat index as its first parameter`);
  if (entry.params[0].type.kind !== 'Nat') fail(`${entryName}: the entry kernel's first parameter must be a Nat index`);
  const buffers = entry.params.slice(1);
  for (const b of buffers) {
    if (b.type.kind !== 'Array') fail(`${entryName}: parameters after the index must be Array U32 buffers (got ${typeName(b.type)})`);
  }
  if (buffers.length === 0) fail(`${entryName}: the entry kernel needs at least one Array U32 buffer`);
  for (const b of buffers) {
    if (b.name === 'out') fail(`${entryName}: a buffer may not be named 'out' (the result buffer)`);
    if (b.name === 'i' || b.name === 'gid')
      fail(`${entryName}: a buffer may not be named '${b.name}' (the generated entry point uses it)`);
  }
  // The result buffer is `array<u32>`; a Bool entry result would need a different ABI.
  // (Bool is still useful as a helper's return type, in a match condition.)
  if (entry.ret.kind !== 'U32')
    fail(`${entryName}: an entry kernel returns U32 (got ${typeName(entry.ret)}; Nat is an index type and Bool has no output ABI yet)`);

  // Acyclicity and reachability: lower from the entry, which walks call edges, rejects a
  // name already on the stack (direct recursion), and tells us which defs to emit.
  const reachable = new Set([entryName]);
  const queue = [entryName];
  const edges = new Map();
  while (queue.length) {
    const d = defs.get(queue.shift());
    const calls = new Set();
    lowerDef(d, defs, calls);
    edges.set(d.name, calls);
    for (const c of calls) {
      if (!reachable.has(c)) { reachable.add(c); queue.push(c); }
    }
  }
  // WGSL forbids recursion, including mutual recursion, which the per-def stack above
  // cannot see.  A DFS of the reachable call graph finds every cycle.
  const colour = new Map(); // 1 = on the path, 2 = done
  const path = [];
  const visit = (n) => {
    const c = colour.get(n);
    if (c === 1) {
      const cycle = [...path.slice(path.indexOf(n)), n];
      fail(`${entryName}: recursion is not in the subset (${cycle.join(' -> ')})`);
    }
    if (c === 2) return;
    colour.set(n, 1);
    path.push(n);
    for (const m of edges.get(n) || []) visit(m);
    path.pop();
    colour.set(n, 2);
  };
  visit(entryName);
  // A helper's buffer parameters are names for module-scope bindings (a helper call may
  // not pass a buffer), so they must be the entry's buffers under the same names.
  const entryBuffers = new Set(buffers.map((b) => b.name));
  for (const n of reachable) {
    for (const p of defs.get(n).params) {
      if (p.type.kind === 'Array' && !entryBuffers.has(p.name))
        fail(`${n}: a helper that reads a buffer must use one of the entry's buffer names (${[...entryBuffers].join(', ')})`);
    }
  }

  for (const n of reachable) {
    if (entryBuffers.has(n) || n === 'out' || n === 'main' || n === `${entryName}_at`)
      fail(`${n}: a kernel name collides with a buffer, the entry point, or the generated entry wrapper (WGSL has one namespace)`);
  }

  const bindings = buffers.map((b, i) =>
    `@group(0) @binding(${i}) var<storage, read> ${b.name} : array<u32>;`).join('\n');
  const outBinding = `@group(0) @binding(${buffers.length}) var<storage, read_write> out : array<u32>;`;
  const helpers = [...reachable].filter((n) => n !== entryName).map((n) => emitDef(defs.get(n), defs));
  const entryFn = `fn ${entryName}_at(${entry.params[0].name} : u32) -> u32 {\n${emitFunctionBody(lowerDef(entry, defs))}\n}`;
  const main = `@compute @workgroup_size(64)\nfn main(@builtin(global_invocation_id) gid : vec3<u32>) {\n  let i : u32 = gid.x;\n  // The one bounds check: every buffer is known to have the output's length.  WGSL's\n  // robust access rule returns 0 for an out-of-range read, which is the kernel's\n  // Array.getD default, so indices inside the guard are the only ones that matter.\n  if (i < arrayLength(&out)) {\n    out[i] = ${entryName}_at(i);\n  }\n}`;
  return `// Generated by webgpu/tools/wgsl.mjs from ${sourceName}: do not edit.\n` +
    `// entry: ${entryName}(i : Nat, ${buffers.map((b) => `${b.name} : Array U32`).join(', ')}) : ${typeName(entry.ret)}\n` +
    `// A kernel is the scalar body; the loop is the dispatch, workgroup_size = 64.\n\n` +
    `${bindings}\n${outBinding}\n\n${[...helpers, entryFn].join('\n\n')}\n\n${main}\n`;
}

// ---------------------------------------------------------------- CLI

function main(argv) {
  let input = null, out = null, entry = null, wiz = process.env.WIZ || 'wiz';
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--input') input = argv[++i];
    else if (a === '--out') out = argv[++i];
    else if (a === '--entry') entry = argv[++i];
    else if (a === '--wiz') wiz = argv[++i];
    else if (a === '--help' || a === '-h') {
      console.log('usage: wgsl.mjs --input KERNEL.wiz [--entry NAME] [--out FILE.wgsl] [--wiz WIZ]');
      return 0;
    } else { console.error(`wgsl: unknown argument ${a}`); return 2; }
  }
  if (!input) { console.error('wgsl: --input is required'); return 2; }
  let text;
  try {
    text = execFileSync(wiz, ['parse', input], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  } catch (e) {
    console.error(`wgsl: \`${wiz} parse ${input}\` failed:\n${e.stderr || e.message}`);
    return 1;
  }
  try {
    const forms = parseSexpr(text);
    const defs = defsOf(forms);
    if (defs.size === 0) fail('no kernel definitions (command.def) in the file');
    entry = entry || [...defs.keys()][0];
    const wgsl = emitModule({ sourceName: input, defs, entryName: entry });
    if (out) {
      mkdirSync(dirname(resolve(out)), { recursive: true });
      writeFileSync(out, wgsl);
      console.error(`wgsl: wrote ${out} (${defs.size} kernel definition(s), entry ${entry})`);
    } else process.stdout.write(wgsl);
    return 0;
  } catch (e) {
    if (e instanceof Reject) { console.error(`wgsl: rejected: ${e.message}`); return 1; }
    throw e;
  }
}

if (import.meta.main) process.exit(main(process.argv.slice(2)));
