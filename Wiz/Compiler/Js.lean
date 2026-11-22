import Wiz.Compiler.C

/-!
# A JavaScript target (prototype)

`Wiz.Js.program runtime decls io` emits an ES module for the IR that the C, LLVM and
Wasm backends consume. `wiz build --target js prog.wiz -o prog.mjs` writes it; the
module is self-contained (the runtime `web/wiz-js-runtime.mjs` is pasted at its top),
exports `main`, and runs `main` when Node executes the file directly.

The representation is the runtime's (see the header of `web/wiz-js-runtime.mjs`):
`Nat` is a `BigInt`, a constructor with fields is `{t, f}`, a constructor without
fields is its tag number, `◾` is `null`, a closure is a JS function made by `wizClo`,
and `dup`/`drop` are the garbage collector's. Closed primitives call the C runtime's
names (`wiz_nat_add`, …); a foreign function is `wizExtern(key, args)`.

What this prototype does *not* do is in `wiz-notes/js-target.md`: there is no
reference counting (so the C runtime's leak and peak-memory observations do not
transfer), no deep non-tail recursion (JS has no tail calls and a smaller stack), and
no filesystem, process, thread, MVar/Ref/Chan, `Str`, `WordArray` or `StrMap` native.
An `extern "js.…"` names a JavaScript function on `globalThis` (for example
`extern "js.wiz.dom.setAttribute" …`), with the signature checked by the existing
`extern` path.
-/

namespace Wiz.Js

open IR

private def lb : String := "{"
private def rb : String := "}"

/-- A JS string literal for `s`. -/
def jsStr (s : String) : String :=
  let hex4 (n : Nat) : String :=
    let ds := String.ofList (Nat.toDigits 16 n)
    ("0000".drop ds.length).toString ++ ds
  "\"" ++ String.join (s.toList.map fun c =>
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c => if c.toNat < 0x20 then "\\u" ++ hex4 c.toNat else c.toString) ++ "\""

/-- The JS name of a Wiz function (the same mangling as the C backend). -/
def mangle (n : Name) : String := C.mangle n

def var (x : Var) : String := s!"x{x}"

def args (xs : Array Var) : String := ", ".intercalate (xs.toList.map var)

/-- The invariants the emission relies on: a partial application names a declaration
with a known arity, and every jump has a join point in scope. (The same check as the C
backend's, kept here so this file depends only on `C.bound`/`C.externs`.) -/
private def checkExpr (arities : Std.HashMap Name Nat) : Expr → Except String Unit
  | .pap f _ =>
    if arities.contains f then .ok ()
    else .error s!"partial application of `{f}`, which has no known arity"
  | _ => .ok ()

private partial def checkBody (arities : Std.HashMap Name Nat) (joins : Std.HashSet JoinId) :
    Body → Except String Unit
  | .vdecl _ e b => do
    checkExpr arities e
    checkBody arities joins b
  | .case _ alts => alts.foldl (fun acc a => acc.bind fun _ => checkBody arities joins a) (.ok ())
  | .jdecl j _ body k => do
    checkBody arities (joins.insert j) k
    checkBody arities (joins.insert j) body
  | .jmp j _ =>
    if joins.contains j then .ok () else .error s!"jump to `j{j}`, which has no join point in scope"
  | .dup _ b | .drop _ b => checkBody arities joins b
  | _ => .ok ()

def checkDecls (decls : Array IR.Decl) : Except String Unit :=
  let arities := decls.foldl (fun m d => m.insert d.name d.params.size) {}
  decls.foldl (fun acc d => acc.bind fun _ => checkBody arities {} d.body) (.ok ())

/-- The JS expression for one IR expression. (The variable it is bound to is the
caller's; the expression only names its operands.) -/
def exprE (arities : Std.HashMap Name Nat) : Expr → Except String String
  | .erased => pure "null"
  | .lit n => pure s!"{n}n"
  | .ctor t as =>
    if as.isEmpty then pure (toString t)
    else pure s!"wizCtor({t}, [{args as}])"
  | .proj i y => pure s!"wizProj({var y}, {i})"
  | .fap f as => pure s!"{mangle f}({args as})"
  | .pap f as =>
    match arities.get? f with
    | some n => pure s!"wizClo({mangle f}, {n}, [{args as}])"
    | none => .error s!"JS backend: partial application of `{f}`, which has no known arity"
  | .ap f as => pure s!"wizApply({var f}, [{args as}])"
  | .prim op as =>
    match op with
    | .extern key => pure s!"wizExtern({jsStr key}, [{args as}])"
    | _ =>
      match PrimOp.runtimeSymbols.find? (fun (p, _) => p == op) with
      | some (_, sym) => pure s!"{sym}({args as})"
      | none => .error s!"JS backend: no runtime symbol for `{op.key}`"
  | .reset y => pure s!"wizReset({var y})"
  | .reuse tok t as => pure s!"wizReuse({var tok}, {t}, [{args as}])"

/-- Emit a body. Locals are declared by `declE`; a join point becomes a function plus a
driver loop, so a jump to it is constant stack (the C backend's `goto`). -/
partial def bodyE (arities : Std.HashMap Name Nat) (ind : String) : Body → Except String String
  | .vdecl x e rest => do
    let r ← exprE arities e
    let rest ← bodyE arities ind rest
    pure s!"{ind}{var x} = {r};\n{rest}"
  | .case x alts => do
    let branches ← alts.toList.zipIdx.mapM fun (a, i) => do
      let t ← bodyE arities (ind ++ "  ") a
      pure s!"{ind}case {i}: {lb}\n{t}{ind}{rb}\n"
    pure (s!"{ind}switch (wizTag({var x})) {lb}\n" ++ String.join branches ++
      s!"{ind}default: throw new Error(\"wiz: no branch for tag \" + wizTag({var x}));\n{ind}{rb}\n")
  | .ret x => pure s!"{ind}return {var x};\n"
  | .jdecl j ps jb k => do
    let jbT ← bodyE arities (ind ++ "  ") jb
    let kT ← bodyE arities (ind ++ "  ") k
    pure (
      s!"{ind}const j{j} = ({args ps}) => {lb}\n{jbT}{ind}{rb};\n" ++
      s!"{ind}let r{j} = (() => {lb}\n{kT}{ind}{rb})();\n" ++
      s!"{ind}while (r{j} instanceof WizJmp) {lb}\n" ++
      s!"{ind}  if (r{j}.id === {j}) {lb} r{j} = j{j}(...r{j}.args); {rb} else {lb} return r{j}; {rb}\n" ++
      s!"{ind}{rb}\n" ++
      s!"{ind}return r{j};\n")
  | .jmp j as => pure s!"{ind}return new WizJmp({j}, [{args as}]);\n"
  | .dup _ b => bodyE arities ind b
  | .drop _ b => bodyE arities ind b
  | .unreachable => pure s!"{ind}throw new Error(\"wiz: reached an impossible case\");\n"

/-- One IR function. A closed definition (`IR.cafs`) is built on its first use and kept,
as the C and Wasm backends do; the rest is a plain JS function of the IR parameters. -/
def declE (arities : Std.HashMap Name Nat) (cafs : Std.HashSet Name) (d : IR.Decl) :
    Except String String := do
  let locals := (C.bound d.body).filter (fun x => !d.params.contains x)
  let loc := if locals.isEmpty then "" else
    s!"  let {", ".intercalate (locals.toList.map var)};\n"
  let bodyT ← bodyE arities "  " d.body
  let m := mangle d.name
  if cafs.contains d.name then
    pure (s!"function {m}() {lb}\n  if (__caf_{m} === undefined) __caf_{m} = {m}_build();\n" ++
      s!"  return __caf_{m};\n{rb}\n" ++
      s!"function {m}_build() {lb}\n{loc}{bodyT}{rb}\n" ++
      s!"let __caf_{m};\n")
  else
    pure s!"function {m}({args d.params}) {lb}\n{loc}{bodyT}{rb}\n"

/-- The kinds `wizExtern` marshals. A struct (`S`) and a byte buffer (`y`/`Y`) need
the C layout, so they are refused at compile time. A callback (`k`/`K`) is refused for
a `wiz_` native (the C runtime expects a function pointer and a context) and allowed for
a `js.` host function, which receives the Wiz closure itself (a callable JS function). -/
def simpleKinds : List Char := ['e', 'n', 'u', 'f', 's', 'b', 'v', 'p', 'w']

/-- Is this a kind the JS backend marshals for a `js.` extern (a simple letter, or a
callback)? -/
def simpleOrCallback (cname : String) (kind : String) : Bool :=
  match kind.toList with
  | [c] => simpleKinds.contains c
  | 'k' :: '[' :: _ | 'K' :: '[' :: _ => cname.startsWith "js."
  | _ => false

/-- The C runtime's foreign functions this backend implements. (`wiz_io_read_file` and
`wiz_io_write_file` are deliberately absent: there is no filesystem in a browser, and
this prototype does not pretend there is one in Node either.) -/
def nativeNames : List String := [
  "wiz_nat_show", "wiz_io_println", "wiz_io_print", "wiz_io_arg_count", "wiz_io_arg",
  "wiz_u64_id", "wiz_u64_add", "wiz_u64_sub", "wiz_u64_mul", "wiz_u64_div",
  "wiz_u64_mod", "wiz_u64_lt", "wiz_u64_eq",
  "wiz_f64_of_nat", "wiz_f64_add", "wiz_f64_sub", "wiz_f64_mul", "wiz_f64_div",
  "wiz_f64_lt", "wiz_f64_show",
  "wiz_bytes_empty", "wiz_bytes_push", "wiz_bytes_size", "wiz_bytes_get",
  "wiz_bytes_of_string", "wiz_bytes_to_string", "wiz_bytes_slice", "wiz_bytes_append",
  "wiz_bytes_eq",
  "wiz_array_empty", "wiz_array_push", "wiz_array_size", "wiz_array_get",
  "wiz_array_set",
  "wiz_word_of_bits", "wiz_word_to_bits", "wiz_word_of_nat", "wiz_word_of_neg",
  "wiz_word_cast", "wiz_word_zext", "wiz_word_sext", "wiz_word_add", "wiz_word_sub",
  "wiz_word_mul", "wiz_word_udiv", "wiz_word_umod", "wiz_word_sdiv", "wiz_word_srem",
  "wiz_word_and", "wiz_word_or", "wiz_word_xor", "wiz_word_not", "wiz_word_shl",
  "wiz_word_lshr", "wiz_word_ashr", "wiz_word_eq", "wiz_word_ult", "wiz_word_ule",
  "wiz_word_slt", "wiz_word_sle", "wiz_word_bit", "wiz_word_msb"
]

def checkExtern (key : Name) : Except String Unit :=
  match RVal.ExternSig.ofKey? key with
  | none => .error s!"JS backend: `{key}` is not a foreign-function key"
  | some sig =>
    let kinds := sig.params.map (fun k => k.toKey) ++ [sig.result.toKey]
    if kinds.any (fun k => !simpleOrCallback sig.cname k) then
      .error s!"JS backend: `{sig.cname}` passes a struct or byte buffer, which the JS \
backend does not marshal (it marshals {String.ofList simpleKinds} and, for a `js.` host, \
callbacks)"
    else if sig.cname.startsWith "js." then
      if sig.cname == "js." then .error "JS backend: `js.` needs a function name"
      else .ok ()
    else if nativeNames.contains sig.cname then .ok ()
    else if sig.cname == "wiz_io_read_file" || sig.cname == "wiz_io_write_file" then
      .error s!"JS backend: `{sig.cname}` needs a filesystem, which this target does not \
have (a browser has none, and the prototype does not add Node's). Use a `js.` extern to \
hand the host's storage API to Wiz."
    else
      .error s!"JS backend: no JavaScript runtime for `{sig.cname}`. Filesystem, processes, \
threads, MVar/Ref/Chan, `Str`, `WordArray` and `StrMap` natives are out of scope \
(wiz-notes/js-target.md); a host API goes through `extern \"js.…\"`."

/-- Every foreign function a program uses is supported (or the program is refused). -/
def checkExterns (decls : Array IR.Decl) : Except String Unit :=
  (C.externs decls).foldl (fun acc key => acc.bind (fun _ => checkExtern key)) (.ok ())

/-- The whole ES module: the runtime, the functions, `main`, and a runner for
`node prog.mjs` (not for an import: the importer's `main` is its own). -/
def program (runtime : String) (decls : Array IR.Decl) (io : Bool := false) :
    Except String String := do
  match checkDecls decls with
  | .error e => .error s!"JS backend: {e}"
  | .ok () => pure ()
  checkExterns decls
  let arities := decls.foldl (fun m d => m.insert d.name d.params.size) {}
  let cafs := IR.cafs decls
  let texts ← decls.toList.mapM (declE arities cafs)
  let entry := mangle "wiz.entry"
  let mainBody := if io then s!"  return wizApply({entry}(), [0]);\n" else s!"  return {entry}();\n"
  let runner := if io then "wizRunCli(main, true);" else "wizRunCli(main, false);"
  pure (
    "/* generated by wiz build --target js (Wiz/Compiler/Js.lean); the runtime is\n" ++
    "   web/wiz-js-runtime.mjs, pasted here so the module is self-contained. */\n\n" ++
    runtime ++ "\n/* ---- generated ---- */\n\n" ++
    String.join texts ++
    s!"\nexport function main() {lb}\n{mainBody}{rb}\n" ++
    s!"\nfunction __wizIsCli() {lb}\n" ++
    "  return typeof process !== \"undefined\" && process.argv && process.argv[1] &&\n" ++
    "    import.meta.url === wizFileUrl(process.argv[1]);\n" ++
    s!"{rb}\n" ++
    s!"if (__wizIsCli()) {lb}\n  {runner}\n{rb}\n")

end Wiz.Js
