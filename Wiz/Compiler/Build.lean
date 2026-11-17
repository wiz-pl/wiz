import Wiz.Elab.Command
import Wiz.Compiler.C
import Wiz.Compiler.LLVM
import Wiz.Compiler.Wasm
import Wiz.Compiler.WasmValidate
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

/-- The optimised IR of a program computing the global `n`, and `n`'s type, with the
exported functions. A library (`lib`) has only the exports. -/
def irProgram (s : CommandState R) (n : Name) (lib : Bool := false) : Except String (Array IR.Decl × Term R) := do
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

/-- The C program that computes the global `n`, and `n`'s type. -/
def cProgram (s : CommandState R) (n : Name) : Except String (String × Term R) := do
  let (decls, ty) ← irProgram s n
  pure (C.program decls (isIO ty) (extraC s) s.globals.unboxStructs ((exports s).map (·.1)), ty)

def words (s : Option String) : List String :=
  ((s.getD "").splitOn " ").filter (· ≠ "")

/-- Is debug information requested (`-g`, `-g3`, `-ggdb`, `-gdwarf-5`, …)? The
`-gc…` flags are not debug flags. -/
def wantsDebug (cflags : List String) : Bool :=
  cflags.any fun f => f == "-g" || (f.startsWith "-g" && !f.startsWith "-gc")

/-- Keep debug information (and `__FILE__`) from naming the build directory: with
`-g`, `cc` records the generated C file's absolute path and the compilation directory,
so the same program built under two absolute paths would differ. `-ffile-prefix-map`
maps both to `.` (`-g` without it is not reproducible; without `-g` the flag changes
nothing and is not passed). -/
def pathMapFlags (cflags : List String) (dir : System.FilePath) : IO (Array String) := do
  if !wantsDebug cflags then return #[]
  let abs ← IO.FS.realPath dir
  -- the compilation directory (`DW_AT_comp_dir`) is the cwd, which is not the generated
  -- C file's directory; map both
  let cwd ← IO.currentDir
  let maps := #[s!"-ffile-prefix-map={abs}=."]
  pure (if cwd == abs then maps else maps.push s!"-ffile-prefix-map={cwd}=.")

/-- Compile C source to an executable. -/
def compileC (tc : Toolchain) (src : String) (exe : System.FilePath) (link : Link := {}) (lib : Bool := false) : IO (Except String Unit) := do
  let cFile := exe.withExtension "c"
  IO.FS.writeFile cFile src
  let cc := tc.cc
  -- (debug info and `__FILE__` must not name the checkout; the generated C is beside OUT)
  let map ← pathMapFlags tc.cflags (cFile.parent.getD ".")
  -- (9f) the `link_c` files are compiled with the program, with the same flags
  -- (9g: a library is an object file, linked by the C program that uses it, which
  -- also brings the `link_c` files and libraries)
  let args := if lib then #["-O2", "-w", "-c", "-o", exe.toString, cFile.toString] ++ tc.cflags.toArray ++ map else
    #["-O2", "-w", "-o", exe.toString, cFile.toString] ++ link.sources ++ tc.cflags.toArray ++ map ++
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
  let map ← pathMapFlags tc.cflags dir
  let keyOf (text : String) (api : Bool) : String :=
    toString (mixHash (hash text) (hash s!"{cc} {" ".intercalate tc.cflags} -O2 -w {api}"))
  let ccOne (file obj : String) (api : Bool) : IO (Except String Unit) :=
    runCC cc (#["-O2", "-w", "-c", "-o", (dir / obj).toString, (dir / file).toString] ++
      (if api then #["-DWIZ_API="] else #[]) ++ cflags ++ map)
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
  let map ← pathMapFlags tc.cflags (rtFile.parent.getD ".")
  let step (cmd : String) (args : Array String) : IO (Except String Unit) := do
    try
      let out ← IO.Process.output { cmd, args }
      pure (if out.exitCode == 0 then .ok () else .error s!"{cmd} failed:\n{out.stderr}")
    catch e => pure (.error s!"{cmd}: {e}")
  let rtObj := exe.withFileName "wiz_runtime.o"
  let mainObj := if lib then exe.withFileName ((exe.fileStem.getD "wiz") ++ "_module.o") else exe.withExtension "o"
  if let .error e ← step cc (#["-O2", "-w", "-c", "-DWIZ_API=", "-o", rtObj.toString, rtFile.toString] ++ cflags ++ map) then
    return .error e
  if let .error e ← step llc #["-O2", "-filetype=obj", "-relocation-model=pic", "-o", mainObj.toString, llFile.toString] then
    return .error e
  -- (9g: a library is the two objects as one, `-r`)
  if lib then return ← step cc #["-r", "-o", exe.toString, mainObj.toString, rtObj.toString]
  -- (9f) the `link_c` files are compiled by the linking step, with the C flags
  let srcArgs := if link.sources.isEmpty then #[] else #["-O2", "-w"] ++ link.sources ++ cflags
  step cc (#["-o", exe.toString, mainObj.toString, rtObj.toString] ++ srcArgs ++ tc.gmp.toArray ++
    tc.ldflags.toArray ++ tc.libs.toArray ++ link.libFlags)

/-- (8f) Write the WebAssembly module of the program to `out`. The JS host
(`web/wasm-host.mjs`) prints its result; `runWasm` below uses it. The bytes are parsed
and type-checked by `WasmValidate.validate` before they are written, so an encoder bug
(or an instruction outside the supported subset) is a compile error, not a module that
an engine rejects later. -/
def compileWasm (decls : Array IR.Decl) (io : Bool) (out : System.FilePath) : IO (Except String Unit) := do
  match Wasm.program decls io with
  | .error e => pure (.error e)
  | .ok bytes =>
    match WasmValidate.validate bytes with
    | .error e => pure (.error s!"internal error: the Wasm backend emitted an invalid module: {e}")
    | .ok () =>
      IO.FS.writeBinFile out bytes
      pure (.ok ())

/-- Build the program computing `main`, through C, LLVM, or WebAssembly. With `lib`, the
exports as an object file, with a header `OUT.h` for them; with `noMain`, the exports
linked like a program but without a `main` (a Wasm module, a shared library: the
toolchain's flags say which). -/
def build (tc : Toolchain) (s : CommandState R) (n : Name) (out : System.FilePath) (llvm lib : Bool)
    (noMain : Bool := false) (split : Nat := 0) (wasm : Bool := false) : IO (Except String (Term R)) := do
  if wasm && llvm then
    return .error "choose one backend: --target wasm, --target llvm, or --target c"
  if wasm && (lib || noMain) then
    return .error "the Wasm backend builds a `main`; `--lib` and `--no-main` are not supported (stage 8f)"
  if wasm && split != 0 then
    return .error "the Wasm backend has one module; `--split` does not apply (stage 8f)"
  if wasm && !(exports s).isEmpty then
    return .error "the Wasm backend rejects `export` wrappers (`export \"name\" f`); use the C target (stage 8f)"
  let bare := lib || noMain
  match irProgram s n bare with
  | .error e => pure (.error e)
  | .ok (decls, ty) =>
    let io := isIO ty
    let ex := (exports s).map (·.1)
    let unbox := s.globals.unboxStructs
    if lib then IO.FS.writeFile (out.withExtension "h") (C.exportHeader ex)
    let r ← if wasm then compileWasm decls io out
      else if llvm then
        compileLLVM tc (LLVM.program decls io bare) out
          (extraC s ++ "\n" ++ C.glue (C.externs decls) (extraC s) unbox ++ "\n" ++ C.exportWrappers ex true) (linkOf s) lib
      else compileDecls tc decls io (extraC s) unbox ex (linkOf s) lib bare out split
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

/-- (8f) Build `main` as a WebAssembly module and run it under Node with the JS host
(`web/wasm-host.mjs`), reading the printed result back with `main`'s type. -/
def runWasmGlobal (s : CommandState R) (n : Name) (dir : System.FilePath) : IO (Except String String) := do
  match irProgram s n with
  | .error e => pure (.error e)
  | .ok (decls, ty) =>
    let wasmFile := dir / "wiz_main.wasm"
    match ← compileWasm decls (isIO ty) wasmFile with
    | .error e => pure (.error e)
    | .ok () =>
      let host : System.FilePath := "web" / "wasm-host.mjs"
      unless ← host.pathExists do
        return .error "web/wasm-host.mjs is missing (run from the Wiz checkout)"
      let out ← try
        -- (under `lake env`, Lean's LD_LIBRARY_PATH breaks Node's own library lookup)
        IO.Process.output
          { cmd := "node", args := #[host.toString, wasmFile.toString], env := #[("LD_LIBRARY_PATH", none)] }
      catch e => return .error s!"node: {e}"
      if out.exitCode != 0 then
        return .error s!"the Wasm program failed ({out.exitCode}): {out.stderr.take 1000}"
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
