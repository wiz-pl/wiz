import Wiz.Compiler.C

/-!
# LLVM IR code generation

The same IR as `C.lean`, as textual LLVM IR, compiled with `llc` and linked with the
runtime (compiled separately, with its functions exported). Values are `i64`.

**The LLVM backend is 64-bit only.** Its values are `i64` and its literals are
`2 * n + 1`, so the module and the runtime must be built for a 64-bit pointer width; a
32-bit target must use the C backend (`--cc` with the target's flags), whose runtime
selects the 30-bit small-int path at compile time (`runtime/wiz_abi.h`). `llc` is never
given a pointer-width flag by Wiz, so a 32-bit `--llc` wrapper would produce a module
whose `i64` values disagree with a 32-bit `wiz_val` — do not use one.

LLVM is in SSA form, so two things change compared to C:

* a join point's parameters live in stack slots (`alloca`): a jump stores the
  arguments and branches, and the join block loads them. (`llc`'s optimiser turns
  these into registers);
* a variable bound in several branches (a reuse token) gets a distinct SSA name in
  each, so names are tracked in an environment.
-/

namespace Wiz.LLVM

open IR

structure St where
  out : Array String := #[]
  next : Nat := 0
  /-- join point ↦ its parameters (whose stack slots are `%jp<x>`) -/
  joins : Std.HashMap JoinId (Array Var) := {}

abbrev M := StateM St

def emit (line : String) : M Unit := modify fun s => { s with out := s.out.push line }
def fresh (base : String) : M String := modifyGet fun s => (s!"%{base}.{s.next}", { s with next := s.next + 1 })

def fn (n : Name) : String := "@" ++ C.mangle n

/-- The SSA name of a variable. -/
def val (env : Std.HashMap Var String) (x : Var) : String := env.getD x s!"%x{x}"

def bind (env : Std.HashMap Var String) (x : Var) : M (Std.HashMap Var String × String) := do
  let name ← fresh s!"x{x}"
  pure (env.insert x name, name)

/-- An array of values on the stack, for closures. -/
def array (env : Std.HashMap Var String) (xs : Array Var) : M String := do
  if xs.isEmpty then return "null"
  let arr ← fresh "arr"
  emit s!"  {arr} = alloca [{xs.size} x i64]"
  for x in xs, i in [0:xs.size] do
    let p ← fresh "p"
    emit s!"  {p} = getelementptr [{xs.size} x i64], ptr {arr}, i64 0, i64 {i}"
    emit s!"  store i64 {val env x}, ptr {p}"
  pure arr

def args (env : Std.HashMap Var String) (xs : Array Var) : String :=
  ", ".intercalate (xs.toList.map (s!"i64 {val env ·}"))

def expr (arities : Std.HashMap Name Nat) (env : Std.HashMap Var String) (x : String) : Expr → M Unit
  | .erased => emit s!"  {x} = add i64 0, 1"
  | .lit n =>
    if n < 2 ^ 62 then emit s!"  {x} = add i64 0, {2 * n + 1}"
    else do
      -- a big literal: through the runtime, from its digits
      let s := toString n
      -- (named after the number: one global per literal in the module. A counter per
      -- function gave two functions the same `@lit.1.str`, so a program with two big
      -- literals was not a valid module: 15g)
      let g := s!"@wiz.lit.{n}"
      emit s!"  {x} = call i64 @wiz_nat_lit(ptr {g})"
      modify fun st => { st with out := st.out.push s!";global {g} = private constant [{s.length + 1} x i8] c\"{s}\\00\"" }
  | .ctor t as =>
    if as.isEmpty then emit s!"  {x} = add i64 0, {2 * t + 1}"
    else do
      emit s!"  {x} = call i64 @wiz_ctor_new(i32 {t}, i32 {as.size})"
      for a in as, i in [0:as.size] do emit s!"  call void @wiz_set(i64 {x}, i32 {i}, i64 {val env a})"
  | .proj i y => emit s!"  {x} = call i64 @wiz_proj(i64 {val env y}, i32 {i})"
  | .fap f as => emit s!"  {x} = call i64 {fn f}({args env as})"
  | .pap f as => do
    let arr ← array env as
    emit s!"  {x} = call i64 @wiz_clo_new(ptr {fn f}_boxed, i32 {(arities.get? f).getD 0}, i32 {as.size}, ptr {arr})"
  | .ap f as => do
    let arr ← array env as
    emit s!"  {x} = call i64 @wiz_apply(i64 {val env f}, i32 {as.size}, ptr {arr})"
  | .prim op as =>
    let f := match op with
      | "nat.succ" => "wiz_nat_succ" | "nat.pred" => "wiz_nat_pred"
      | "nat.add" => "wiz_nat_add" | "nat.sub" => "wiz_nat_sub" | "nat.mul" => "wiz_nat_mul"
      | "nat.beq" => "wiz_nat_beq" | "nat.blt" => "wiz_nat_blt" | "lazyTag" => "wiz_lazy_tag" | "lazySet" => "wiz_lazy_set" | "memo" => "wiz_memo"
      | "tag" => "wiz_tag_of" | "natTag" => "wiz_nat_tag" | "fieldAt" => "wiz_field_at" | "mkObj" => "wiz_mk_obj"
      | "dropMoved" => "wiz_drop_moved"
      | op => if op.startsWith "nat." then "wiz_nat_" ++ (op.drop 4).toString
        else if (RVal.ExternSig.ofKey? op).isSome then C.externWrapper op else "wiz_unknown_prim"
    emit s!"  {x} = call i64 @{f}({args env as})"
  | .reset y => emit s!"  {x} = call i64 @wiz_reset(i64 {val env y})"
  | .reuse tok t as => do
    emit s!"  {x} = call i64 @wiz_reuse(i64 {val env tok}, i32 {t}, i32 {as.size})"
    for a in as, i in [0:as.size] do emit s!"  call void @wiz_set(i64 {x}, i32 {i}, i64 {val env a})"

partial def body (arities : Std.HashMap Name Nat) (env : Std.HashMap Var String) : Body → M Unit
  | .vdecl x e rest => do
    let (env, name) ← bind env x
    expr arities env name e
    body arities env rest
  | .case x alts => do
    let t ← fresh "tag"
    emit s!"  {t} = call i32 @wiz_tag(i64 {val env x})"
    let labels ← alts.mapM fun _ => fresh "case"
    let dflt ← fresh "default"
    let cases := labels.toList.zipIdx.map fun (l, i) => s!"i32 {i}, label {l}"
    emit s!"  switch i32 {t}, label {dflt} [ {" ".intercalate cases} ]"
    for a in alts, l in labels do
      emit s!"{l.drop 1}:"
      body arities env a
    emit s!"{dflt.drop 1}:"
    emit "  call void @wiz_unreachable()"
    emit "  unreachable"
  | .ret x => emit s!"  ret i64 {val env x}"
  | .jdecl j ps jb k => do
    modify fun s => { s with joins := s.joins.insert j ps }
    body arities env k
    emit s!"j{j}:"
    let mut env' : Std.HashMap Var String := {}
    for p in ps do
      let (e, name) ← bind env' p
      env' := e
      emit s!"  {name} = load i64, ptr %jp{p}"
    body arities env' jb
  | .jmp j as => do
    let ps := ((← get).joins.get? j).getD #[]
    for p in ps, a in as do emit s!"  store i64 {val env a}, ptr %jp{p}"
    emit s!"  br label %j{j}"
  | .dup x rest => do emit s!"  call void @wiz_inc(i64 {val env x})"; body arities env rest
  | .drop x rest => do emit s!"  call void @wiz_dec(i64 {val env x})"; body arities env rest
  | .unreachable => do emit "  call void @wiz_unreachable()"; emit "  unreachable"

/-- The join point parameters of a body (each gets a stack slot). -/
partial def joinParams : Body → Array Var
  | .vdecl _ _ b | .dup _ b | .drop _ b => joinParams b
  | .case _ alts => alts.foldl (fun acc a => acc ++ joinParams a) #[]
  | .jdecl _ ps jb k => ps ++ joinParams jb ++ joinParams k
  | _ => #[]

def decl (arities : Std.HashMap Name Nat) (cafs : Std.HashSet Name) (d : IR.Decl) : Array String × Array String :=
  let ps := ", ".intercalate (d.params.toList.map (s!"i64 %x{·}"))
  let ((), st) := (do
    for p in joinParams d.body do emit s!"  %jp{p} = alloca i64"
    body arities {} d.body : M Unit).run {}
  -- big literals are globals: move them out of the function
  let (globals, lines) := st.out.partition (·.startsWith ";global ")
  let globals := globals.map fun g => (g.drop 8).toString
  let boxedLoads := (List.range d.params.size).map fun i =>
    s!"  %p{i} = getelementptr i64, ptr %a, i64 {i}\n  %a{i} = load i64, ptr %p{i}"
  let boxedArgs := ", ".intercalate ((List.range d.params.size).map (s!"i64 %a{·}"))
  -- (an export's closure is called from the C glue)
  let linkage := if d.name.startsWith "wiz.export." then "" else "internal "
  let boxed := s!"define internal i64 {fn d.name}_boxed(ptr %a) {lb}\n{"\n".intercalate boxedLoads}\n  %r = call i64 {fn d.name}({boxedArgs})\n  ret i64 %r\n{rb}"
  -- (a closed definition, `IR.cafs`: its body is `_build`, run once by `wiz_caf_init`;
  -- the function loads the cached value from the slot)
  if cafs.contains d.name then
    let f := fn d.name
    (globals.push s!"{f}.slot = internal global i64 0, align 8",
      #[s!"define internal i64 {f}.build() {lb}", "entry:"] ++ lines ++ #[rb,
        s!"define internal i64 {f}() {lb}\nentry:\n  %v = load atomic i64, ptr {f}.slot acquire, align 8\n" ++
        s!"  %c = icmp ne i64 %v, 0\n  br i1 %c, label %hit, label %miss\nhit:\n" ++
        s!"  call void @wiz_inc(i64 %v)\n  ret i64 %v\nmiss:\n" ++
        s!"  %r = call i64 @wiz_caf_init(ptr {f}.slot, ptr {f}.build)\n  ret i64 %r\n{rb}", boxed])
  else
  (globals, #[s!"define {linkage}i64 {fn d.name}({ps}) {lb}", "entry:"] ++ lines ++ #[rb, boxed])
where
  lb := "{"
  rb := "}"

def runtimeDecls : String := "
declare i64 @wiz_ctor_new(i32, i32)
declare void @wiz_set(i64, i32, i64)
declare void @wiz_inc(i64)
declare void @wiz_dec(i64)
declare i32 @wiz_tag(i64)
declare i64 @wiz_proj(i64, i32)
declare i64 @wiz_nat_lit(ptr)
declare i64 @wiz_nat_add(i64, i64)
declare i64 @wiz_nat_sub(i64, i64)
declare i64 @wiz_nat_mul(i64, i64)
declare i64 @wiz_nat_succ(i64)
declare i64 @wiz_nat_pred(i64)
declare i64 @wiz_nat_beq(i64, i64)
declare i64 @wiz_nat_blt(i64, i64)
declare i64 @wiz_nat_div(i64, i64)
declare i64 @wiz_nat_mod(i64, i64)
declare i64 @wiz_nat_pow(i64, i64)
declare i64 @wiz_nat_land(i64, i64)
declare i64 @wiz_nat_lor(i64, i64)
declare i64 @wiz_nat_xor(i64, i64)
declare i64 @wiz_nat_shiftLeft(i64, i64)
declare i64 @wiz_nat_shiftRight(i64, i64)
declare i64 @wiz_nat_log2(i64)
declare i64 @wiz_memo(i64, i64)
declare i64 @wiz_lazy_tag(i64)
declare i64 @wiz_lazy_set(i64, i64)
declare i64 @wiz_tag_of(i64)
declare i64 @wiz_nat_tag(i64)
declare i64 @wiz_field_at(i64, i64)
declare i64 @wiz_mk_obj(i64, i64)
declare i64 @wiz_clo_new(ptr, i32, i32, ptr)
declare i64 @wiz_apply(i64, i32, ptr)
declare i64 @wiz_reset(i64)
declare i64 @wiz_drop_moved(i64, i64)
declare i64 @wiz_reuse(i64, i32, i32)
declare void @wiz_unreachable()
declare i64 @wiz_caf_init(ptr, ptr)
declare i32 @wiz_finish(i64)
"

/-- A whole LLVM module: the functions and a `main` that prints `wiz.entry`'s value (or
runs it, for `IO`). The foreign wrappers are C (`C.glue`), compiled with the runtime. -/
def program (decls : Array IR.Decl) (io : Bool := false) (lib : Bool := false) : String :=
  let arities := decls.foldl (fun m d => m.insert d.name d.params.size) {}
  let cafs := IR.cafs decls
  let parts := decls.map (decl arities cafs)
  let globals := (parts.foldl (fun acc (g, _) => acc ++ g) #[]).toList.eraseDups.toArray
  let fns := parts.foldl (fun acc (_, f) => acc ++ f) #[]
  let externDecls := (C.externs decls).toList.map fun key =>
    let n := RVal.nativeArity key
    s!"declare i64 @{C.externWrapper key}({", ".intercalate (List.replicate n "i64")})\n"
  let io' := if io then 1 else 0
  runtimeDecls ++ "declare i32 @wiz_run_main(ptr, i32)\ndeclare void @wiz_set_args(i32, ptr)\n" ++ String.join externDecls ++
    "\n".intercalate globals.toList ++ "\n" ++ "\n".intercalate fns.toList ++
    if lib then "\n" else s!"\ndefine i32 @main(i32 %argc, ptr %argv) \{\n  call void @wiz_set_args(i32 %argc, ptr %argv)\n  %c = call i32 @wiz_run_main(ptr {fn "wiz.entry"}, i32 {io'})\n  ret i32 %c\n}\n"

end Wiz.LLVM
