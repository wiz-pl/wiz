import Wiz.Elab.Command
import Wiz.Compiler.C
import Wiz.Compiler.LLVM
import Wiz.Compiler.Lower
import Wiz.Toolchain

/-!
# Building executables

`wiz build FILE -o OUT` compiles the definition `main` of a file to C (`C.lean`) and
then to an executable with the C compiler of the **toolchain** (`Wiz/Toolchain.lean`:
`--cc`, `--cflags`, `--ldflags`, for example where GMP lives), passed explicitly; nothing
is read from the environment. The executable
prints its result as a generic tree (`(tag fields…)` and numbers); `wiz run` reads
that back with `main`'s type, like `#eval`.
-/

namespace Wiz.Build

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- The exported functions (`export "c" f`, stage 9g), in order: their C signatures and
definitions. -/
def exports (s : CommandState R) : List (RVal.ExternSig × Name) :=
  s.builtins.reverse.filterMap fun (k, f) => (RVal.ExternSig.ofExportKey? k).map (·, f)

/-! ### Representations at build time (22m)

A `repr:` registration is trusted (the kernel never runs it), and a stale or foreign one
must not compile: `reprCoherence` re-derives every registration's shape, requires a seal
in the type's index, and requires erasure to find the same representation by that seal.
`layoutAsserts` writes the target's and the C structs' layout checks into the C; `wiz
repr` prints the table below and `Main.reprCmd` runs the same coherence check. -/

/-- The native representations registered in the environment: the type, the constructor
the registration is on, and the representation (`repr:T:mk:get:…`). -/
def nativeReprs (s : CommandState R) : List (Name × Name × ReprInfo) :=
  s.builtins.reverse.filterMap fun (k, ctor) => (ReprInfo.parse? k).map fun (T, ri) => (T, ctor, ri)

/-- The `c_struct`s declared or imported in this state, by the `cstruct:<layout>` keys:
their C layout under the ABI model, sorted by C type (deterministic output). -/
def cStructAbis (s : CommandState R) (ptrBits : Nat) : List C.CStructAbi :=
  let parse (k : Name) : Option RVal.FKind :=
    if k.startsWith "cstruct:" then (RVal.FKind.parseOne (k.drop 8).toString.toList).map (·.1) else none
  let all := s.builtins.filterMap fun (k, _) => parse k
  let dedup := all.foldl (fun acc k => if acc.any (fun k' => k'.toKey == k.toKey) then acc else acc ++ [k]) []
  (dedup.filterMap fun k => match k with
    | .struct c h fs => some (C.cStructAbi (ptrBits / 8) c h fs)
    | _ => none).toArray.qsort (fun a b => a.ctype < b.ctype) |>.toList

/-- (22m) The coherence of every `repr:` registration with the environment: a seal, the
seal in the type's own index, `mk`/`get` present and arities right, and the shape the
registration records equal to the constructor's erased shape. The build refuses to
compile when this is not empty (`irProgram`); `wiz repr` prints the same errors. -/
def reprCoherence (s : CommandState R) : List String := Id.run do
  let g := s.globals
  let reprs := nativeReprs s
  let rec nPis : Term R → Nat
    | .pi _ _ _ _ b _ => nPis b + 1
    | _ => 0
  let mut errs : Array String := #[]
  for (T, ctor, ri) in reprs do
    if (reprs.filter fun (T', _, _) => T' == T).length > 1 then
      errs := errs.push s!"{T} has more than one native representation"
    unless s.builtins.any (fun (k, _) => k == sealKey T) do
      errs := errs.push s!"{T} has a native representation but is not `sealed` (no `{sealKey T}`): a look-alike of an unsealed type is the same type"
    unless sealedInTail g T do
      errs := errs.push s!"{T}'s representation is not found by a seal in its index (`sealed inductive {T}`): erasure cannot use it"
    match g.find? ri.mkImpl, g.find? ri.getImpl with
    | none, _ => errs := errs.push s!"{T}: the native constructor {ri.mkImpl} does not exist"
    | _, none => errs := errs.push s!"{T}: the native field reader {ri.getImpl} does not exist"
    | some _, some dg =>
      if nPis dg.type != ri.getArity then
        errs := errs.push s!"{T}: {ri.getImpl} has {nPis dg.type} arguments, the registration says {ri.getArity}"
    match g.find? ctor with
    | none => errs := errs.push s!"{T}: the constructor {ctor} does not exist"
    | some d =>
      match ctorReprShape? g d with
      | some (tag, nf, r, mkArity, p) =>
        if (tag, nf, r, mkArity, p) != (ri.tag, ri.nfields, ri.r, ri.mkArity, ri.p) then
          errs := errs.push s!"{T}: the registration (tag {ri.tag}, {ri.nfields} fields, runtime field {ri.r}, mk arity {ri.mkArity}, argument {ri.p}) disagrees with {ctor}'s erased shape (tag {tag}, {nf} fields, runtime field {r}, mk arity {mkArity}, argument {p})"
      | none => errs := errs.push s!"{T}: {ctor} has no single runtime field (its erased shape changed)"
    match appliedType? g T with
    | none => errs := errs.push s!"{T} does not exist"
    | some ty => match nativeTy? g ty with
      | some (T', ri') =>
        if T' != T || ri' != ri then
          errs := errs.push s!"{T}: erasure finds {T'} (or a different representation) by the seal"
      | none => errs := errs.push s!"{T}: erasure cannot find a representation by the seal"
  errs.toList

/-- A field kind's name in `wiz repr` (the Wiz type it marshals). -/
def kindName : RVal.FKind → String
  | .k 'n' => "Nat" | .k 'u' => "UInt64" | .k 'f' => "Float64" | .k 's' => "String"
  | .k 'b' => "Bool" | .k 'p' => "pointer" | .k 'w' => "wiz_val" | .k 'y' => "Bytes"
  | .k 'e' => "0" | .k c => c.toString
  | .struct c .. => c | .callback .. => "callback"

/-- (22m) `wiz repr`: the target, the registered native representations, and the C
structs by value with their layouts. The same data the generated `_Static_assert`s
check. -/
def reprReport (tc : Toolchain) (s : CommandState R) : String := Id.run do
  let ptrBytes := tc.ptrBits / 8
  let mut out := "wiz repr\n"
  out := out ++ s!"  target: {if tc.target.isEmpty then "(the host)" else tc.target} ({tc.ptrBits}-bit pointers, {tc.endian}-endian)\n"
  out := out ++ s!"  value: one pointer ({ptrBytes} bytes); a scalar uses its low bit\n"
  out := out ++ s!"  abi: uint64_t 8/8, double 8/8, int 4/4, pointer {ptrBytes}/{ptrBytes}\n"
  let reprs := (nativeReprs s).toArray.qsort (fun a b => a.1 < b.1) |>.toList
  if reprs.isEmpty then out := out ++ "  native representations: none\n"
  else
    out := out ++ s!"  native representations ({reprs.length}):\n"
    for (T, ctor, ri) in reprs do
      let sealed := if s.builtins.any (·.1 == sealKey T) then "" else "  [no seal: not compiled]"
      out := out ++ s!"    {T}: {ri.mkImpl} / {ri.getImpl} on {ctor}, tag {ri.tag}, {ri.nfields} fields, runtime field {ri.r} (one word){sealed}\n"
  let structs := cStructAbis s tc.ptrBits
  if structs.isEmpty then out := out ++ "  c_structs: none\n"
  else
    out := out ++ s!"  c_structs ({structs.length}):\n"
    for a in structs do
      let origin := if a.header.isEmpty then "generated" else s!"header {a.header}"
      let size := match a.size, a.align with
        | some sz, some al => s!"size {sz}, align {al}"
        | _, _ => "size from the header"
      out := out ++ s!"    {a.ctype} ({origin}): {a.fields.length} fields, {size}\n"
      for (f, k) in a.fields do
        -- a header's field types are the header's (an `int` can stand for a `Nat`): only
        -- a generated struct's widths are the model's
        let sz := if a.header.isEmpty then
            (match a.bytes.find? (·.1 == f) with
              | some (_, some n) => s!", {n} bytes"
              | _ => "")
          else ""
        let off := match a.offsets.find? (·.1 == f) with
          | some (_, o) => s!", offset {o}"
          | none => ""
        out := out ++ s!"      {f}: {kindName k}{sz}{off}\n"
  pure out

/-- (22m) The ABI checks a build writes into its generated C: the target's scalar widths,
pointer width and byte order, every native representation, and every C struct passed by
value (an extern's or an export's). -/
def layoutAsserts (tc : Toolchain) (s : CommandState R) (decls : Array IR.Decl)
    (exports : List RVal.ExternSig) : String :=
  let externs := (C.externs decls).toList.filterMap (fun k => RVal.ExternSig.ofKey? k)
  let kinds := (externs.map (·.result) ++ externs.flatMap (·.params)) ++
    (exports.map (·.result) ++ exports.flatMap (·.params))
  C.layoutAsserts tc.ptrBits tc.endian kinds (nativeReprs s |>.map fun (T, _, ri) => (T, ri))

/-- The optimised IR of a program computing the global `n`, and `n`'s type, with the
exported functions. A library (`lib`) has only the exports. -/
def irProgram (s : CommandState R) (n : Name) (lib : Bool := false) : Except String (Array IR.Decl × Term R) := do
  -- (22m) a native representation is trusted; a stale or incoherent registration (no
  -- seal, a shape that changed, a type its seal does not name) must not compile
  if let e :: _ := reprCoherence s then throw s!"native representation: {e}"
  -- (22m) and a generated struct must have a C field (C has no empty struct)
  for a in cStructAbis s 64 do
    if a.header.isEmpty && a.fields.isEmpty then
      throw s!"c_struct {a.ctype} has no C fields (every field is `0`)"
  let ex := exports s
  let (roots, main, ty) ← if lib then
      if ex.isEmpty then throw "a library must export something (`export \"name\" f`)"
      pure ([], ETerm.erased, (Term.unit 1 : Term R))
    else do
      let some d := s.globals.find? n | throw s!"no definition {n}"
      pure ([n], ETerm.global n, d.type)
  let code ← (compileReachable s.globals s.builtins (roots ++ ex.map (·.2))).mapError toString
  let decls ← IR.lowerProgram code main (ex.toArray.map fun (sig, f) => (C.exportEntry sig.cname, .global f))
  pure (IR.optimizeProgram (IR.hoistConsts decls), ty)

/-- Header includes and glue functions, in order. -/
def extraC (s : CommandState R) : String := "\n".intercalate s.cCode.toList

/-- (9f) What a program links besides the runtime: C source files (`link_c`, absolute
paths) and libraries (`link_lib "m"`: `-lm`). -/
structure Link where
  sources : Array String := #[]
  libs : Array String := #[]
  deriving Inhabited, Repr

def linkOf (s : CommandState R) : Link := { sources := s.linkC, libs := s.linkLibs }

/-- The linker arguments of the libraries. -/
def Link.libFlags (l : Link) : Array String := l.libs.map ("-l" ++ ·)

/-- Is this the type `IO A`? Then `main` is run, not printed. -/
def isIO (ty : Term R) : Bool := match (Term.spine ty).1 with
  | .const "IO" _ => true
  | _ => false

/-- The C program that computes the global `n`, and `n`'s type. `tc` names the target
and sizes its ABI checks (22m); the default is the host (`64`-bit, little-endian). -/
def cProgram (s : CommandState R) (n : Name) (tc : Toolchain := {}) : Except String (String × Term R) := do
  let (decls, ty) ← irProgram s n
  let ex := (exports s).map (·.1)
  let extra := extraC s ++ layoutAsserts tc s decls ex
  pure (C.program decls (isIO ty) extra s.globals.unboxStructs ex, ty)

def words (s : Option String) : List String :=
  ((s.getD "").splitOn " ").filter (· ≠ "")

/-- Compile C source to an executable. -/
def compileC (tc : Toolchain) (src : String) (exe : System.FilePath) (link : Link := {}) (lib : Bool := false) : IO (Except String Unit) := do
  let cFile := exe.withExtension "c"
  IO.FS.writeFile cFile src
  let cc := tc.cc
  -- (9f) the `link_c` files are compiled with the program, with the same flags
  -- (9g: a library is an object file, linked by the C program that uses it, which
  -- also brings the `link_c` files and libraries)
  let args := if lib then #["-O2", "-w", "-c", "-o", exe.toString, cFile.toString] ++ tc.cflags.toArray else
    #["-O2", "-w", "-o", exe.toString, cFile.toString] ++ link.sources ++ tc.cflags.toArray ++
    tc.gmp.toArray ++ tc.ldflags.toArray ++ tc.libs.toArray ++ link.libFlags
  try
    let out ← IO.Process.output { cmd := cc, args }
    if out.exitCode == 0 then pure (.ok ()) else pure (.error s!"{cc} failed:\n{out.stderr}")
  catch e => pure (.error s!"{cc}: {e}")

/-- Run a C compiler; its output as an error when it fails. -/
def runCC (cmd : String) (args : Array String) : IO (Except String Unit) := do
  try
    let out ← IO.Process.output { cmd, args }
    pure (if out.exitCode == 0 then .ok () else .error s!"{cmd} failed:\n{out.stderr}")
  catch e => pure (.error s!"{cmd}: {e}")

/-- Compile the C of a program. One translation unit by default; with `--split N` a
support unit (`-DWIZ_API=`: the runtime and glue are exported) and `N` units of generated
functions are compiled by `cc -c` in parallel (stage 15k), then linked. `--lib` stays one
object file. The split is opt-in: it makes the build faster but the C compiler cannot
inline across unit boundaries, so the generated program runs slower (see 15k). -/
def compileDecls (tc : Toolchain) (decls : Array IR.Decl) (io : Bool) (extra : String)
    (unbox : Bool) (exports : List RVal.ExternSig) (link : Link) (lib noMain : Bool)
    (out : System.FilePath) (split : Nat := 0) : IO (Except String Unit) := do
  let src := C.program decls io extra unbox exports noMain
  let n := split
  if lib || n < 2 || decls.size < 2 then
    return ← compileC tc src out link lib
  let dir := (out.parent.getD ".") / ((out.fileName.getD "wiz") ++ ".split")
  IO.FS.createDirAll dir
  let header := "wiz_split.h"
  let headerText := C.splitHeader decls exports
  IO.FS.writeFile (dir / header) headerText
  let parts := C.splitParts decls n
  -- (deterministic inputs; a part whose text and flags are unchanged reuses its object)
  let inputs : Array (String × String × Bool) :=
    #[("support", C.splitSupport decls io extra unbox exports noMain, true)] ++
    parts.zipIdx.map fun (p : String × Nat) => (s!"part{p.2}", C.splitPartText header p.1, false)
  let cc := tc.cc
  let cflags := tc.cflags.toArray
  let keyOf (text : String) (api : Bool) : String :=
    toString (mixHash (hash text) (hash s!"{cc} {" ".intercalate tc.cflags} -O2 -w {api}"))
  let ccOne (file obj : String) (api : Bool) : IO (Except String Unit) :=
    runCC cc (#["-O2", "-w", "-c", "-o", (dir / obj).toString, (dir / file).toString] ++
      (if api then #["-DWIZ_API="] else #[]) ++ cflags)
  let err ← IO.mkRef (none : Option String)
  let mut todo : Array (String × Bool × String) := #[]
  for (name, text, api) in inputs do
    let stamp := keyOf text api
    let hit ← if (← (dir / (name ++ ".stamp")).pathExists) && (← (dir / (name ++ ".o")).pathExists) then
        pure ((← IO.FS.readFile (dir / (name ++ ".stamp"))).trimAscii.toString == stamp)
      else pure false
    unless hit do
      IO.FS.writeFile (dir / (name ++ ".c")) text
      todo := todo.push (name, api, stamp)
  let tasks ← todo.mapM fun (name, api, stamp) =>
    IO.asTask (prio := .dedicated) do
      match ← ccOne (name ++ ".c") (name ++ ".o") api with
      | .ok () => IO.FS.writeFile (dir / (name ++ ".stamp")) stamp; pure (.ok ())
      | .error e => pure (.error e)
  let collect (t : Task (Except IO.Error (Except String Unit))) : IO Unit := do
    match t.get with
    | .ok (.ok ()) => pure ()
    | .ok (.error e) => if (← err.get).isNone then err.set (some e)
    | .error e => if (← err.get).isNone then err.set (some (toString e))
  for t in tasks do collect t
  if let some e ← err.get then return .error e
  let objs := inputs.map fun (name, _, _) => (dir / (name ++ ".o")).toString
  let srcArgs := if link.sources.isEmpty then #[] else #["-O2", "-w"] ++ link.sources ++ cflags
  runCC cc (#["-o", out.toString] ++ objs ++ srcArgs ++ tc.gmp.toArray ++ tc.ldflags.toArray ++
    tc.libs.toArray ++ link.libFlags)

/-- Compile an LLVM module to an executable: `llc` (the toolchain's) for the module, the C
compiler for the runtime (exported with `-DWIZ_API=`), and the C compiler to link. -/
def compileLLVM (tc : Toolchain) (ll : String) (exe : System.FilePath) (glue : String := "") (link : Link := {}) (lib : Bool := false) : IO (Except String Unit) := do
  let llFile := exe.withExtension "ll"
  let rtFile := exe.withFileName "wiz_runtime.c"
  IO.FS.writeFile llFile ll
  IO.FS.writeFile rtFile (C.runtime ++ "\n" ++ glue)
  let cc := tc.cc
  let llc := tc.llc
  let cflags := tc.cflags.toArray
  let step (cmd : String) (args : Array String) : IO (Except String Unit) := do
    try
      let out ← IO.Process.output { cmd, args }
      pure (if out.exitCode == 0 then .ok () else .error s!"{cmd} failed:\n{out.stderr}")
    catch e => pure (.error s!"{cmd}: {e}")
  let rtObj := exe.withFileName "wiz_runtime.o"
  let mainObj := if lib then exe.withFileName ((exe.fileStem.getD "wiz") ++ "_module.o") else exe.withExtension "o"
  if let .error e ← step cc (#["-O2", "-w", "-c", "-DWIZ_API=", "-o", rtObj.toString, rtFile.toString] ++ cflags) then
    return .error e
  if let .error e ← step llc #["-O2", "-filetype=obj", "-relocation-model=pic", "-o", mainObj.toString, llFile.toString] then
    return .error e
  -- (9g: a library is the two objects as one, `-r`)
  if lib then return ← step cc #["-r", "-o", exe.toString, mainObj.toString, rtObj.toString]
  -- (9f) the `link_c` files are compiled by the linking step, with the C flags
  let srcArgs := if link.sources.isEmpty then #[] else #["-O2", "-w"] ++ link.sources ++ cflags
  step cc (#["-o", exe.toString, mainObj.toString, rtObj.toString] ++ srcArgs ++ tc.gmp.toArray ++
    tc.ldflags.toArray ++ tc.libs.toArray ++ link.libFlags)

/-- Build the program computing `main`, through C or LLVM. With `lib`, the exports as
an object file, with a header `OUT.h` for them; with `noMain`, the exports linked like
a program but without a `main` (a Wasm module, a shared library: the toolchain's flags
say which). -/
def build (tc : Toolchain) (s : CommandState R) (n : Name) (out : System.FilePath) (llvm lib : Bool)
    (noMain : Bool := false) (split : Nat := 0) : IO (Except String (Term R)) := do
  let bare := lib || noMain
  match irProgram s n bare with
  | .error e => pure (.error e)
  | .ok (decls, ty) =>
    let io := isIO ty
    let ex := (exports s).map (·.1)
    let unbox := s.globals.unboxStructs
    -- (22m) the target's and the structs' layout checks, after the struct definitions
    let extra := extraC s ++ "\n" ++ layoutAsserts tc s decls ex
    if lib then IO.FS.writeFile (out.withExtension "h") (C.exportHeader ex)
    let r ← if llvm then
        compileLLVM tc (LLVM.program decls io bare) out
          (extra ++ "\n" ++ C.glue (C.externs decls) extra unbox ++ "\n" ++ C.exportWrappers ex true) (linkOf s) lib
      else compileDecls tc decls io extra unbox ex (linkOf s) lib bare out split
    pure (r.map fun () => ty)

/-- Parse the printed result: numbers, `(tag fields…)`, `<fn>`, `#bits`. -/
partial def parseValue (s : String) : Option RVal :=
  match go s.toList with
  | some (v, rest) => if rest.all (·.isWhitespace) then some v else none
  | none => none
where
  ws (cs : List Char) : List Char := cs.dropWhile (·.isWhitespace)
  num (cs : List Char) : Option (Nat × List Char) :=
    let ds := cs.takeWhile Char.isDigit
    if ds.isEmpty then none else some (String.mk ds |>.toNat!, cs.drop ds.length)
  go (cs : List Char) : Option (RVal × List Char) := do
    match ws cs with
    | '(' :: rest =>
      let (t, rest) ← num (ws rest)
      let rec fields (cs : List Char) (acc : Array RVal) : Option (Array RVal × List Char) :=
        match ws cs with
        | ')' :: rest => some (acc, rest)
        | cs => do let (v, rest) ← go cs; fields rest (acc.push v)
      let (fs, rest) ← fields rest #[]
      return (.obj t fs, rest)
    | '<' :: 'f' :: 'n' :: '>' :: rest => return (.clo [] .erased, rest)
    -- a raw machine word (a native word of 64 bits, stage 22d)
    | '#' :: rest => let (n, rest) ← num rest; return (.nat n, rest)
    | cs => let (n, rest) ← num cs; return (.nat n, rest)

/-- Build and run the global `n` (through C, or LLVM); returns its result, read back
with its type. With `timeout`, the program is stopped after that many seconds (by
coreutils' `timeout`). -/
def runGlobal (tc : Toolchain) (s : CommandState R) (n : Name) (dir : System.FilePath) (llvm : Bool := false)
    (timeout : Option Nat := none) (args : Array String := #[]) (split : Nat := 0) :
    IO (Except String String) := do
  let exe := dir / "wiz_main"
  match ← build tc s n exe llvm false (split := split) with
    | .error e => pure (.error e)
    | .ok ty =>
      let io := isIO ty
      let out ← match timeout with
        | some t => IO.Process.output { cmd := "timeout", args := #[toString t, exe.toString] ++ args }
        | none => IO.Process.output { cmd := exe.toString, args }
      if out.exitCode == 124 && timeout.isSome then return .error "the program timed out"
      if out.exitCode != 0 then return .error s!"the program failed ({out.exitCode}): {out.stderr}"
      -- an `IO` program prints for itself
      if io then return .ok out.stdout
      match parseValue out.stdout with
      | none => pure (.error s!"could not read the result: {out.stdout}")
      | some v => pure (.ok (readback s.globals s.builtins (eval s.globals [] ty) v).pretty)

/-- Preprocess the headers a file imports (`import_c "h"`), since the frontend is pure. -/
def preprocessHeaders (tc : Toolchain) (input : String) : IO (Std.HashMap String String) := do
  let mut m : Std.HashMap String String := {}
  for part in (input.splitOn "import_c \"").drop 1 do
    let h := (part.splitOn "\"").headD ""
    if h.isEmpty || m.contains h then continue
    let cc := tc.cc
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "h.c") s!"#include <{h}>\n"
    let out ← IO.Process.output { cmd := cc, args := #["-E", "-P", (dir / "h.c").toString] ++ tc.cflags.toArray }
    if out.exitCode == 0 then m := m.insert h out.stdout
  pure m


end Wiz.Build
