import Wiz.Compiler.IR
import Wiz.Compiler.Run
import WizRuntime

/-!
# C code generation

Each IR function becomes a C function on `wiz_val`s, plus a *boxed* version taking an
array, which closures point to. Variables become locals, `case` a `switch` on the
tag, join points labelled blocks entered with `goto` (their parameters are locals
assigned before the jump), and `dup`/`drop` calls to the runtime (`runtime/`,
which is pasted at the top of the output; `Wiz.C.runtime`, in `runtime/WizRuntime.lean`).
-/

namespace Wiz.C

open IR

/-- A C identifier for a Wiz name: letters and digits stay, anything else is `_xx`. -/
def mangle (n : Name) : String :=
  "w_" ++ String.join (n.toList.map fun c =>
    if c.isAlphanum then c.toString
    else "_" ++ (Nat.toDigits 16 c.toNat).asString ++ "_")

def var (x : Var) : String := s!"x{x}"

/-- The C wrapper of a foreign function. -/
def externWrapper (key : Name) : String := "wiz_ext" ++ (mangle key).drop 1

/-- The variables a body binds (to declare them up front). -/
partial def bound (b : Body) (acc : Array Var := #[]) : Array Var :=
  match b with
  | .vdecl x _ b => bound b (acc.push x)
  | .case _ alts => alts.foldl (fun acc a => bound a acc) acc
  | .jdecl _ ps body k => bound k (bound body (acc ++ ps))
  | .dup _ b | .drop _ b => bound b acc
  | _ => acc

def args (xs : Array Var) : String := ", ".intercalate (xs.toList.map var)

def expr (arities : Std.HashMap Name Nat) (x : Var) : Expr → String
  | .erased => s!"{var x} = WIZ_BOX(0);"
  | .lit n =>
    if n < 2 ^ 62 then s!"{var x} = WIZ_BOX({n}UL);" else s!"{var x} = wiz_nat_lit(\"{n}\");"
  | .ctor t as =>
    if as.isEmpty then s!"{var x} = WIZ_BOX({t});"
    else
      let sets := as.toList.zipIdx.map fun (a, i) => s!" WIZ_SET({var x}, {i}, {var a});"
      s!"{var x} = wiz_ctor_new({t}, {as.size});" ++ String.join sets
  | .proj i y => s!"{var x} = wiz_proj({var y}, {i});"
  | .fap f as => s!"{var x} = {mangle f}({args as});"
  | .pap f as =>
    let arr := if as.isEmpty then "NULL" else s!"(wiz_val[]){lb}{args as}{rb}"
    s!"{var x} = wiz_clo_new({mangle f}_boxed, {(arities.get? f).getD 0}, {as.size}, {arr});"
  | .ap f as => s!"{var x} = wiz_apply({var f}, {as.size}, (wiz_val[]){lb}{args as}{rb});"
  | .reset y => s!"{var x} = wiz_reset({var y});"
  | .reuse tok t as =>
    let sets := as.toList.zipIdx.map fun (a, i) => s!" WIZ_SET({var x}, {i}, {var a});"
    s!"{var x} = wiz_reuse({var tok}, {t}, {as.size});" ++ String.join sets
  | .prim op as =>
    let fn := match op with
      | "nat.succ" => "wiz_nat_succ" | "nat.pred" => "wiz_nat_pred"
      | "nat.add" => "wiz_nat_add" | "nat.sub" => "wiz_nat_sub" | "nat.mul" => "wiz_nat_mul"
      | "nat.beq" => "wiz_nat_beq" | "nat.blt" => "wiz_nat_blt" | "lazyTag" => "wiz_lazy_tag" | "lazySet" => "wiz_lazy_set" | "memo" => "wiz_memo"
      | "tag" => "wiz_tag_of" | "natTag" => "wiz_nat_tag" | "fieldAt" => "wiz_field_at" | "mkObj" => "wiz_mk_obj"
      | "dropMoved" => "wiz_drop_moved"
      | op => if op.startsWith "nat." then "wiz_nat_" ++ (op.drop 4).toString
        else if (RVal.ExternSig.ofKey? op).isSome then externWrapper op else "wiz_unknown_prim"
    s!"{var x} = {fn}({args as});"
where
  lb := "{"
  rb := "}"

/-- The foreign functions a program uses. -/
partial def externs (decls : Array IR.Decl) : Array Name :=
  let rec go : Body → Array Name → Array Name
    | .vdecl _ (.prim op _) b, acc => go b (if (RVal.ExternSig.ofKey? op).isSome && !acc.contains op then acc.push op else acc)
    | .vdecl _ _ b, acc | .dup _ b, acc | .drop _ b, acc => go b acc
    | .case _ alts, acc => alts.foldl (fun acc a => go a acc) acc
    | .jdecl _ _ jb k, acc => go k (go jb acc)
    | _, acc => acc
  (decls.foldl (fun acc d => go d.body acc) #[]).qsort (· < ·)

def ctype : Char → String
  | 'n' | 'u' => "uint64_t"
  | 'f' => "double"
  | 's' => "const char *"
  | 'b' => "int"
  | 'p' => "void *"
  | 'w' => "wiz_val"
  | _ => "void"

open RVal (FKind)

/-- The C type of a kind (a struct's own type name). -/
def ftype : FKind → String
  | .k c => ctype c
  | .struct c _ _ => c
  | .callback .. => "void *"

/-- (9i) The C definition of a struct whose layout is declared in Wiz without a header:
`struct t { … };` for a name `struct t`, else a `typedef`. Fields: `uint64_t` for `Nat`
and `UInt64`, `double`, `int` for `Bool`, `const char *`, `void *` for foreign pointers,
and the C types of nested structs. -/
def structDefinition (ctype : String) (fields : List (String × FKind)) : String :=
  let fs := fields.filter (fun (_, k) => k != .k 'e') |>.map fun (f, k) => s!"  {ftype k} {f};\n"
  if ctype.startsWith "struct " then s!"{ctype} \{\n{String.join fs}};\n"
  else s!"typedef struct \{\n{String.join fs}} {ctype};\n"

/-- The Wiz value of a structure's field `i` of `n`, borrowed from `v`. A structure is
nested pairs ending in `◾` (its tail): field `i` is the first component after `i`
seconds. With `unbox` (`--unbox-structs`, 22i) the last pair is unboxed, so the last
field is the value left after `n - 1` seconds, and a one-field structure is its field. -/
def fieldPath (v : String) (i n : Nat) (unbox : Bool := false) : String :=
  let rec seconds : Nat → String → String
    | 0, e => e
    | k + 1, e => seconds k s!"wiz_field_ref({e}, 1)"
  if unbox && i + 1 == n then seconds i v else s!"wiz_field_ref({seconds i v}, 0)"

/-- (9i) Marshalling helpers for the structs a program passes by value: `wiz_sin_N(&c, v)`
fills `c` from the (borrowed) Wiz value `v`, `wiz_sfree_N(&c)` frees what that allocated
(strings), `wiz_sout_N(c)` makes a Wiz value. Nested structs get their own helpers,
defined first. Returns the helpers and the number of each struct (by its key). -/
partial def structHelpers (ks : List FKind) (unbox : Bool := false) : String × List (String × Nat) := Id.run do
  let mut out := ""
  let mut seen : List (String × Nat) := []
  let rec collect : FKind → List FKind
    | .struct c h fs => fs.flatMap (collect ·.2) ++ [.struct c h fs]
    | _ => []
  for k in ks.flatMap collect do
    let .struct c _ fs := k | continue
    if seen.any (·.1 == k.toKey) then continue
    let id := seen.length
    let num (k : FKind) : Nat := ((seen.find? (·.1 == k.toKey)).map (·.2)).getD 0
    let n := fs.length
    let mut sin := ""
    let mut sfree := ""
    let mut sout := ""
    for (f, fk) in fs, i in [0:n] do
      let path := fieldPath "v" i n unbox
      let lhs := s!"c->{f}"
      match fk with
      | .k 'n' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_nat(t); {rb}\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_nat((uint64_t)c.{f});\n"
      | .k 'u' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_u64(t); {rb}\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_u64((uint64_t)c.{f});\n"
      | .k 'f' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_f64(t); {rb}\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_f64((double)c.{f});\n"
      | .k 'b' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_bool(t); {rb}\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_bool(c.{f} != 0);\n"
      | .k 's' => sin := sin ++ s!"  {lb} wiz_val t = {path}; wiz_inc(t); {lhs} = wiz_in_string(t); {rb}\n"
                  sfree := sfree ++ s!"  free((void *){lhs});\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_string(c.{f} ? c.{f} : \"\");\n"
      -- a foreign pointer in a struct: borrowed while the call runs; one that comes back
      -- is not owned (no finalizer)
      | .k 'p' => sin := sin ++ s!"  {lhs} = wiz_in_ptr({path});\n"
                  sout := sout ++ s!"  fs[{i}] = wiz_out_ptr((void *)c.{f}, NULL);\n"
      -- a byte array of fixed size (`char f[N]`): copied, zero-padded or cut to size
      | .k 'y' => sin := sin ++ s!"  {lb} wiz_bytes *b = (wiz_bytes *){path}; size_t m = b->len < sizeof {lhs} ? b->len : sizeof {lhs};\n" ++
                    s!"    memset({lhs}, 0, sizeof {lhs}); if (m) memcpy({lhs}, b->data, m); {rb}\n"
                  sout := sout ++ s!"  {lb} wiz_bytes *b = (wiz_bytes *)wiz_bytes_empty(); b->len = b->cap = sizeof c.{f};\n" ++
                    s!"    b->data = (unsigned char *)malloc(b->len); memcpy(b->data, c.{f}, b->len); fs[{i}] = (wiz_val)b; {rb}\n"
      | .struct .. =>
        sin := sin ++ s!"  wiz_sin_{num fk}(&{lhs}, {path});\n"
        sfree := sfree ++ s!"  wiz_sfree_{num fk}(&{lhs});\n"
        sout := sout ++ s!"  fs[{i}] = wiz_sout_{num fk}(c.{f});\n"
      | _ => sout := sout ++ s!"  fs[{i}] = WIZ_BOX(0);\n"
    -- (boxed: every field in a pair, the innermost second component the erased tail)
    let build := if !unbox then
      s!"  wiz_val r = WIZ_BOX(0);\n  for (int i = {n - 1}; i >= 0; i--) {lb} wiz_val p = wiz_ctor_new(0, 2); WIZ_SET(p, 0, fs[i]); WIZ_SET(p, 1, r); r = p; {rb}\n  return r;\n"
      else if n ≤ 1 then "  return fs[0];\n" else
      s!"  wiz_val r = fs[{n - 1}];\n  for (int i = {n - 2}; i >= 0; i--) {lb} wiz_val p = wiz_ctor_new(0, 2); WIZ_SET(p, 0, fs[i]); WIZ_SET(p, 1, r); r = p; {rb}\n  return r;\n"
    out := out ++
      s!"static void wiz_sin_{id}({c} *c, wiz_val v) {lb}\n  memset(c, 0, sizeof *c);\n{sin}{rb}\n" ++
      s!"static void wiz_sfree_{id}({c} *c) {lb}\n  (void)c;\n{sfree}{rb}\n" ++
      s!"static wiz_val wiz_sout_{id}({c} c) {lb}\n  wiz_val fs[{max n 1}];\n{sout}{build}{rb}\n"
    seen := seen ++ [(k.toKey, id)]
  pure (out, seen)
where
  lb := "{"
  rb := "}"

/-- Is this a C identifier? (an exported function's name) -/
def isCIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_')
  | [] => false

/-! ### Calls from C into Wiz (stage 9g)

An exported function and a callback both turn C values into Wiz values (`wiz_out_*`),
apply a Wiz closure, and turn the result back (`wiz_in_*`): the reverse of a foreign
function's wrapper. A result in `IO` gets the world (a scalar) and drops it after. -/

/-- The C type of a value C passes to Wiz (`const char *` is borrowed: Wiz copies it). -/
def ctypeIn : Char → String
  | 's' => "const char *"
  | k => ctype k

/-- The C type of a value Wiz gives C: a string is `malloc`ed, the caller frees it. -/
def ctypeOut : Char → String
  | 's' => "char *"
  | k => ctype k

/-- A C value of kind `k` as a Wiz value (C → Wiz). A pointer is lent: no finalizer. -/
def wizOfC (k : Char) (x : String) : String := match k with
  | 'n' => s!"wiz_out_nat({x})" | 'u' => s!"wiz_out_u64({x})" | 'f' => s!"wiz_out_f64({x})"
  | 's' => s!"wiz_out_string({x})" | 'b' => s!"wiz_out_bool({x})"
  | 'p' => s!"wiz_out_ptr((void *)({x}), NULL)"
  | _ => x

/-- A Wiz value (owned) as a C value of kind `k` (Wiz → C). -/
def cOfWiz (k : Char) (x : String) : String := match k with
  | 'n' => s!"wiz_in_nat({x})" | 'u' => s!"wiz_in_u64({x})" | 'f' => s!"wiz_in_f64({x})"
  | 's' => s!"wiz_in_string({x})" | 'b' => s!"wiz_in_bool({x})"
  | _ => x

/-- The body of a C function that applies the closure `f` (an owned `wiz_val`
expression) to its parameters `a0 …` of the signature `c`. -/
def callIntoWiz (c : RVal.CallbackSig) (f : String) : String :=
  let n := c.params.length + (if c.io then 1 else 0)
  let args := (c.params.zipIdx.map fun (k, i) => wizOfC k s!"a{i}") ++ (if c.io then ["WIZ_BOX(0)"] else [])
  let call := if n == 0 then s!"  wiz_val r = {f};\n"
    else s!"  wiz_val f = {f};\n  wiz_val args[{n}] = {lb}{", ".intercalate args}{rb};\n  wiz_val r = wiz_apply(f, {n}, args);\n"
  let io := if c.io then "  r = wiz_io_value(r);\n" else ""
  let ret := if c.result == 'v' then "  wiz_dec(r);\n" else s!"  return {cOfWiz c.result "r"};\n"
  call ++ io ++ ret
where
  lb := "{"
  rb := "}"

def cParams (c : RVal.CallbackSig) : List String :=
  c.params.zipIdx.map fun (k, i) => s!"{ctypeIn k} a{i}"

/-- The trampoline of a callback signature: C calls it with the context first. -/
def trampoline (c : RVal.CallbackSig) : String :=
  "wiz_cb_" ++ String.ofList c.params ++ "_" ++ (if c.io then "io_" else "") ++ c.result.toString

def trampolineDef (c : RVal.CallbackSig) : String :=
  let ps := ", ".intercalate ("void *ctx" :: cParams c)
  s!"static {ctypeOut c.result} {trampoline c}({ps}) {lb}\n  wiz_inc((wiz_val)ctx);\n{callIntoWiz c "(wiz_val)ctx"}{rb}\n"
where
  lb := "{"
  rb := "}"

/-- The C type of a callback's function pointer. -/
def callbackType (c : RVal.CallbackSig) : String :=
  s!"{ctypeOut c.result} (*)({", ".intercalate ("void *" :: c.params.map ctypeIn)})"

/-- An exported function's C prototype. -/
def exportProto (sig : RVal.ExternSig) : String :=
  let ps := (sig.params.zipIdx.map fun (k, i) => s!"{ctypeIn k.letter} a{i}")
  s!"{ctypeOut sig.result.letter} {sig.cname}({if ps.isEmpty then "void" else ", ".intercalate ps})"

/-- The IR function that gives an exported function's closure. -/
def exportEntry (cname : String) : Name := "wiz.export." ++ cname

/-- The C functions of the exports (after the generated code; with `llvm`, the closures
come from the LLVM module). -/
def exportWrappers (exports : List RVal.ExternSig) (llvm : Bool := false) (declareEntries : Bool := false) : String :=
  String.join (exports.map fun sig =>
    let entry := mangle (exportEntry sig.cname)
    let decl := if llvm || declareEntries then s!"extern wiz_val {entry}(void);\n" else ""
    let c : RVal.CallbackSig := { params := sig.params.map (·.letter), result := sig.result.letter, io := sig.io }
    decl ++ s!"{exportProto sig} {lb}\n{callIntoWiz c s!"{entry}()"}{rb}\n")
where
  lb := "{"
  rb := "}"

/-- A header for a library's exports (`wiz build --lib`). -/
def exportHeader (exports : List RVal.ExternSig) : String :=
  "/* generated by wiz build --lib: the functions the Wiz program exports (stage 9g) */\n" ++
  "#include <stdint.h>\n#ifndef WIZ_VAL_DEFINED\n#define WIZ_VAL_DEFINED\ntypedef uintptr_t wiz_val;\n#endif\n" ++
  "void wiz_release(void *v);\nvoid wiz_retain(void *v);\nlong wiz_live_objects(void);\n" ++
  String.join (exports.map (exportProto · ++ ";\n"))

/-- The headers of a struct kind (and of its nested structs). -/
partial def structHeaders : FKind → List String
  | .struct _ h fs => (if h == "" then [] else [h]) ++ fs.flatMap (structHeaders ·.2)
  | _ => []

/-- C glue for the foreign functions: their headers (or prototypes), and a marshalling
wrapper for each (`WIZ_API`, so the LLVM backend can call them). Headers already
included by `before` (the program's own C code) aren't included again. -/
def glue (keys : Array Name) (before : String := "") (unbox : Bool := false) : String := Id.run do
  let mut includes : Array String := #[]
  let mut out := ""
  let sigs := keys.toList.filterMap fun key => (RVal.ExternSig.ofKey? key).map (key, ·)
  for (_, sig) in sigs do
    for h in (if sig.header == "" then [] else [sig.header]) ++ (sig.result :: sig.params).flatMap structHeaders do
      unless includes.contains h || (before.splitOn s!"#include <{h}>").length > 1 do includes := includes.push h
  let (helpers, nums) := structHelpers (sigs.flatMap fun (_, sig) => sig.result :: sig.params) unbox
  let num (k : FKind) : Nat := ((nums.find? (·.1 == k.toKey)).map (·.2)).getD 0
  out := out ++ helpers
  -- (9g) the trampolines of the callbacks
  let mut cbs : Array String := #[]
  for (_, sig) in sigs do
    for k in sig.params do
      if let .callback _ c := k then
        let t := trampolineDef c
        unless cbs.contains t do cbs := cbs.push t
  out := out ++ String.join cbs.toList
  for (key, sig) in sigs do
    if sig.header == "" && !sig.cname.startsWith "wiz_" then
      let ps := sig.params.filter (fun k => k != .k 'v' && k != .k 'e') |>.flatMap fun k =>
        if k == .k 'y' then ["const void *", "size_t"]
        else if let .callback _ c := k then [callbackType c, "void *"] else [ftype k]
      out := out ++ s!"extern {ftype sig.result} {sig.cname}({if ps.isEmpty then "void" else ", ".intercalate ps});\n"
    let n := sig.params.length
    let params := (List.range n).map (s!"wiz_val a{·}") ++ (if sig.io then ["wiz_val w"] else [])
    let mut body := ""
    let mut cargs : Array String := #[]
    let mut cb := 0
    for k in sig.params, i in [0:n] do
      match k with
      -- (9g) a callback: the trampoline and the closure
      | .callback _ c => cargs := cargs ++ #[trampoline c, s!"(void *)a{i}"]
      | .k 'n' => body := body ++ s!"  uint64_t c{i} = wiz_in_nat(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 'u' => body := body ++ s!"  uint64_t c{i} = wiz_in_u64(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 'f' => body := body ++ s!"  double c{i} = wiz_in_f64(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 's' => body := body ++ s!"  char *c{i} = wiz_in_string(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 'b' => body := body ++ s!"  int c{i} = wiz_in_bool(a{i});\n"; cargs := cargs.push s!"c{i}"
      | .k 'p' => body := body ++ s!"  void *c{i} = wiz_in_ptr(a{i});\n"; cargs := cargs.push s!"c{i}"
      -- (9i) a byte buffer: its data and length, borrowed for the call
      | .k 'y' => cargs := cargs.push s!"(const void *)((wiz_bytes *)a{i})->data" |>.push s!"(size_t)((wiz_bytes *)a{i})->len"
      | .k 'w' => cargs := cargs.push s!"a{i}"
      | .k 'e' => pure ()
      -- (9i) a struct by value: filled from the Wiz structure, which is released after the call
      | .struct c .. => body := body ++ s!"  {c} c{i}; wiz_sin_{num k}(&c{i}, a{i});\n"; cargs := cargs.push s!"c{i}"
      | _ => body := body ++ s!"  wiz_dec(a{i});\n"
    let call := s!"{sig.cname}({", ".intercalate cargs.toList})"
    body := body ++ match sig.result with
      | .k 'n' => s!"  wiz_val r = wiz_out_nat({call});\n"
      | .k 'u' => s!"  wiz_val r = wiz_out_u64({call});\n"
      | .k 'f' => s!"  wiz_val r = wiz_out_f64({call});\n"
      | .k 's' => s!"  wiz_val r = wiz_out_string({call});\n"
      | .k 'b' => s!"  wiz_val r = wiz_out_bool({call});\n"
      | .k 'p' =>
        let fin := if sig.fin == "" then "NULL" else s!"(void (*)(void *)){sig.fin}"
        s!"  wiz_val r = wiz_out_ptr((void *){call}, {fin});\n"
      | .k 'w' => s!"  wiz_val r = {call};\n"
      | .struct .. => s!"  wiz_val r = wiz_sout_{num sig.result}({call});\n"
      | _ => s!"  {call};\n  wiz_val r = WIZ_BOX(0);\n"
    for k in sig.params, i in [0:n] do
      if k == .k 's' then body := body ++ s!"  free(c{i});\n"
      -- a foreign pointer or a buffer is borrowed for the call: release it after
      if k == .k 'p' || k == .k 'y' then body := body ++ s!"  wiz_dec(a{i});\n"
      if let .struct .. := k then body := body ++ s!"  wiz_sfree_{num k}(&c{i});\n  wiz_dec(a{i});\n"
      -- (9g) a borrowed callback is released after the call; an owned one is C's now
      if let .callback false _ := k then body := body ++ s!"  wiz_dec(a{i});\n"
    body := body ++ (if sig.io then "  return wiz_io_result(r, w);\n" else "  return r;\n")
    out := out ++ s!"WIZ_API wiz_val {externWrapper key}({", ".intercalate params}) {lb}\n{body}{rb}\n"
  pure (String.join (includes.toList.map (s!"#include <{·}>\n")) ++ out)
where
  lb := "{"
  rb := "}"

/-- **Exercise 8.2.** Emit the C statements of a body (see the module docstring). A
join point's body goes after the code that jumps to it, under the label `jN:`; a
jump assigns the parameters (through temporaries, since arguments may overlap them)
and `goto`s the label. -/
partial def body (arities : Std.HashMap Name Nat) (joins : Std.HashMap JoinId (Array Var)) (b : Body)
    (ind : String := "  ") : String :=
  --<sol
  match b with
  | .vdecl x e rest => s!"{ind}{expr arities x e}\n{body arities joins rest ind}"
  | .case x alts =>
    let cases := alts.toList.zipIdx.map fun (a, i) =>
      s!"{ind}case {i}: {lb}\n{body arities joins a (ind ++ "  ")}{ind}{rb}\n"
    s!"{ind}switch (wiz_tag({var x})) {lb}\n{String.join cases}{ind}default: wiz_unreachable(); return 0;\n{ind}{rb}\n"
  | .ret x => s!"{ind}return {var x};\n"
  | .jdecl j ps jb k =>
    let joins := joins.insert j ps
    s!"{body arities joins k ind}{ind}j{j}: {lb}\n{body arities joins jb (ind ++ "  ")}{ind}{rb}\n"
  | .jmp j as =>
    let ps := (joins.get? j).getD #[]
    let tmps := as.toList.zipIdx.map fun (a, i) => s!"wiz_val t{i} = {var a}; "
    let sets := ps.toList.zipIdx.map fun (p, i) => s!"{var p} = t{i}; "
    s!"{ind}{lb} {String.join tmps}{String.join sets}goto j{j}; {rb}\n"
  | .dup x rest => s!"{ind}wiz_inc({var x});\n{body arities joins rest ind}"
  | .drop x rest => s!"{ind}wiz_dec({var x});\n{body arities joins rest ind}"
  | .unreachable => s!"{ind}wiz_unreachable(); return 0;\n"
where
  lb := "{"
  rb := "}"
  --|ex
  --| sorry
  --sol>

def signatureOf (pub : Bool) (d : IR.Decl) : String :=
  let ps := if d.params.isEmpty then "void" else ", ".intercalate (d.params.toList.map (s!"wiz_val {var ·}"))
  s!"{if pub then "" else "static "}wiz_val {mangle d.name}({ps})"

def signature (d : IR.Decl) : String := signatureOf false d

def decl (arities : Std.HashMap Name Nat) (cafs : Std.HashSet Name) (d : IR.Decl) (pub : Bool := false) : String :=
  -- (a reuse token may be bound in several branches: declare it once)
  let locals := ((bound d.body).filter (!d.params.contains ·)).toList.eraseDups.toArray
  let decls := if locals.isEmpty then "" else s!"  wiz_val {", ".intercalate (locals.toList.map var)};\n"
  let boxedArgs := ", ".intercalate ((List.range d.params.size).map (s!"a[{·}]"))
  -- (a closed definition, `IR.cafs`: built on its first use, made immortal, and shared;
  -- the fast path is one load, `wiz_caf_init` builds it)
  if cafs.contains d.name then
    let m := mangle d.name
    s!"static wiz_val {m}_build(void) {lb}\n{decls}{body arities {} d.body}{rb}\n" ++
    s!"static wiz_val {m}_slot = 0;\n" ++
    s!"{signatureOf pub d} {lb} wiz_val v = __atomic_load_n(&{m}_slot, __ATOMIC_ACQUIRE); " ++
    s!"if (__builtin_expect(v != 0, 1)) {lb} wiz_inc(v); return v; {rb} return wiz_caf_init(&{m}_slot, {m}_build); {rb}\n" ++
    s!"{if pub then "" else "static "}wiz_val {m}_boxed(wiz_val *a) {lb} return {m}(); {rb}\n"
  else
  s!"{signatureOf pub d} {lb}\n{decls}{body arities {} d.body}{rb}\n" ++
  s!"{if pub then "" else "static "}wiz_val {mangle d.name}_boxed(wiz_val *a) {lb} return {mangle d.name}({boxedArgs}); {rb}\n"
where
  lb := "{"
  rb := "}"

/-! ### A program in several translation units

`wiz build --split N` (stage 15k) compiles a large program as a **support** unit (the
runtime, the foreign glue and a `main`) plus `N` units of generated functions, so the
C compiler's optimiser runs on the parts in parallel. The split changes nothing that
is generated the single-file way: `program` is still what the tests and the selfhost
fixpoint see; the parts are the same declarations, only not `static`, with a header of
prototypes (the runtime's exported ones included). -/

/-- The types and macros the generated functions use. The runtime defines the same
ones; a part includes this header instead of the runtime. -/
def splitPrelude : String :=
  "#include <stdint.h>\n#include <stddef.h>\n\ntypedef uintptr_t wiz_val;\n" ++
  "typedef struct { int64_t rc; uint32_t tag; uint32_t size; } wiz_hdr;\n" ++
  "typedef struct { wiz_hdr h; wiz_val fields[]; } wiz_ctor;\n" ++
  "typedef wiz_val (*wiz_boxed_fn)(wiz_val *);\n" ++
  "#define WIZ_BOX(n) ((((wiz_val)(n)) << 1) | 1)\n" ++
  "#define WIZ_UNBOX(v) ((v) >> 1)\n" ++
  "#define WIZ_IS_SCALAR(v) ((v) & 1)\n" ++
  "#define WIZ_SET(o, i, v) (((wiz_ctor *)(o))->fields[i] = (v))\n"

/-- The prototypes of the runtime's `WIZ_API` functions, read from `runtime`: each
definition's signature (up to its `{`), with `WIZ_API` dropped. -/
def runtimeProtos : String := Id.run do
  let mut out := ""
  let mut acc := ""
  for line in runtime.splitOn "\n" do
    let hasBrace := line.any (· == '{')
    if !acc.isEmpty then
      acc := acc ++ " " ++ line.trimAscii.toString
      if hasBrace then
        out := out ++ ((acc.splitOn "{").headD "" |>.trimAsciiEnd.toString) ++ ";\n"
        acc := ""
    else if line.startsWith "WIZ_API " then
      let l := (line.drop 8).toString
      if hasBrace then
        out := out ++ ((l.splitOn "{").headD "" |>.trimAsciiEnd.toString) ++ ";\n"
      else acc := l
  pure out

/-- The runtime's word operations made by a macro (`WIZ_WORD_BIN`/`ANY`/`CMP`), whose
definitions `runtimeProtos` cannot see. -/
def wordProtos : String :=
  String.join ((["add", "sub", "mul", "udiv", "umod", "sdiv", "srem"].map fun n =>
      s!"wiz_val wiz_word_{n}(uint64_t, wiz_val, wiz_val);\n") ++
    (["and", "or", "xor"].map fun n => s!"wiz_val wiz_word_{n}(wiz_val, wiz_val);\n") ++
    (["slt", "sle"].map fun n => s!"int wiz_word_{n}(uint64_t, wiz_val, wiz_val);\n"))

/-- The runtime's C interface, which is exported whatever `WIZ_API` is. -/
def cInterfaceProtos : String :=
  "void wiz_release(void *v);\nvoid wiz_retain(void *v);\nlong wiz_live_objects(void);\n" ++
  "void *wiz_warray_data(wiz_val v);\nsize_t wiz_warray_len(wiz_val v);\n" ++
  "wiz_val wiz_warray_of_c(uint32_t width, const void *p, size_t n);\n"

/-- The prototypes of the foreign wrappers a program uses. -/
def externProtos (decls : Array IR.Decl) : String :=
  String.join ((externs decls).toList.map fun key =>
    let n := match RVal.ExternSig.ofKey? key with
      | some sig => sig.params.length + (if sig.io then 1 else 0)
      | none => 0
    let ps := if n == 0 then "void" else ", ".intercalate ((List.range n).map fun i => s!"wiz_val a{i}")
    s!"wiz_val {externWrapper key}({ps});\n")

/-- The prototypes of the generated functions (and their boxed versions). -/
def declProtos (decls : Array IR.Decl) : String :=
  String.join (decls.toList.map fun d =>
    s!"{signatureOf true d};\nwiz_val {mangle d.name}_boxed(wiz_val *a);\n")

/-- The header of a split program: the prelude, the runtime and foreign prototypes, and
the generated functions the other units may call. -/
def splitHeader (decls : Array IR.Decl) (exports : List RVal.ExternSig) : String :=
  "/* generated by wiz build: a program in several translation units (stage 15k) */\n" ++
  splitPrelude ++ "\n/* ---- runtime ---- */\n" ++ runtimeProtos ++
  wordProtos ++ "\n/* ---- C interface ---- */\n" ++ cInterfaceProtos ++
  "\n/* ---- foreign functions ---- */\n" ++ externProtos decls ++
  "\n/* ---- generated ---- */\n" ++ declProtos decls ++
  (if exports.isEmpty then "" else
    "\n/* ---- exported functions ---- */\n" ++
    String.join (exports.map fun sig => s!"wiz_val {mangle (exportEntry sig.cname)}(void);\n"))

/-- The generated declarations cut into at most `n` contiguous parts, balanced by their
C text, in declaration order (which `lowerProgram` sorts by name): deterministic, and
functions that call each other usually stay together. -/
def splitParts (decls : Array IR.Decl) (n : Nat) : Array String := Id.run do
  let arities := decls.foldl (fun m d => m.insert d.name d.params.size) {}
  let cafs := IR.cafs decls
  let texts := decls.map fun d => decl arities cafs d true
  let total := texts.foldl (fun a s => a + s.utf8ByteSize) 0
  let target := max 1 (total / max 1 n)
  let mut parts : Array String := #[]
  let mut cur := ""
  let mut size := 0
  for t in texts do
    if !cur.isEmpty && size + t.utf8ByteSize > target && parts.size + 1 < n then
      parts := parts.push cur
      cur := ""
      size := 0
    cur := cur ++ t
    size := size + t.utf8ByteSize
  if cur.isEmpty then parts else parts.push cur

/-- A part's C text. -/
def splitPartText (header body : String) : String :=
  s!"#include \"{header}\"\n\n" ++ body

/-- The support unit: the runtime (`-DWIZ_API=` exports its functions), the foreign
glue, the exported wrappers, and `main`. -/
def splitSupport (decls : Array IR.Decl) (io : Bool) (extra : String) (unbox : Bool)
    (exports : List RVal.ExternSig) (noMain : Bool) : String :=
  let code := runtime ++ "\n/* ---- foreign functions ---- */\n\n" ++ extra ++ "\n" ++
    glue (externs decls) extra unbox ++
    (if exports.isEmpty then "" else
      "\n/* ---- exported functions ---- */\n\n" ++ exportWrappers exports false true)
  if noMain then code else
  let entry := match decls.find? (·.name == "wiz.entry") with
    | some d => s!"{signatureOf true d};\n"
    | none => s!"wiz_val {mangle "wiz.entry"}(void);\n"
  code ++ s!"\n{entry}int main(int argc, char **argv) \{ wiz_set_args(argc, argv); return wiz_run_main({mangle "wiz.entry"}, {if io then "1" else "0"}); }\n"

/-- A whole C program: the runtime, the foreign glue, the functions, and a `main` that
prints the result of the Wiz `main` (or, for `main : IO A`, runs it) and checks for
leaks. -/
def program (decls : Array IR.Decl) (io : Bool := false) (extra : String := "") (unbox : Bool := false)
    (exports : List RVal.ExternSig := []) (lib : Bool := false) : String :=
  let arities := decls.foldl (fun m d => m.insert d.name d.params.size) {}
  let cafs := IR.cafs decls
  let protos := decls.toList.map fun d =>
    s!"{signature d};\nstatic wiz_val {mangle d.name}_boxed(wiz_val *a);\n"
  let finish := if io then "1" else "0"
  runtime ++ "\n/* ---- foreign functions ---- */\n\n" ++ extra ++ "\n" ++ glue (externs decls) extra unbox ++
    "\n/* ---- generated ---- */\n\n" ++ String.join protos ++ "\n" ++
    String.join (decls.toList.map (decl arities cafs ·)) ++
    (if exports.isEmpty then "" else "\n/* ---- exported functions ---- */\n\n" ++ exportWrappers exports) ++
    -- (a library has no `main`: C calls its exports)
    if lib then "" else
    s!"\nint main(int argc, char **argv) \{ wiz_set_args(argc, argv); return wiz_run_main({mangle "wiz.entry"}, {finish}); }\n"

end Wiz.C
