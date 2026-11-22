import Wiz.Elab.Command
import Wiz.Compiler.C
import Wiz.Compiler.LLVM
import Wiz.Compiler.Wasm
import Wiz.Compiler.WasmValidate
import Wiz.Compiler.Js
import Wiz.Compiler.Lower
import Wiz.Module
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

/-- (F36) The inputs of one split unit's object file (`splitObjectKey` hashes them all). -/
structure SplitObject where
  /-- the C compiler -/
  cc : String
  /-- every flag `cc` gets for this unit: `-O2 -w -c`, `-DWIZ_API=` for the support unit,
  `--cflags`, and the `-ffile-prefix-map`s that name the build directory (which `-g`
  records in the object) -/
  flags : Array String
  /-- the include-path variables `cc` reads (`CPATH`, `C_INCLUDE_PATH`, …): they change
  what an `#include` finds, so they change the object -/
  env : Array (String × Option String) := #[]
  /-- the unit's own C text -/
  text : String
  /-- the generated header (`wiz_split.h`); a part's text only includes it, so the
  declarations it compiles against are an input of the part's object, not of its text -/
  header : String
  deriving Repr, Inhabited

/-- (F36) The environment variables a C compiler takes include paths from. They are not
read through a flag, and they change what `#include` finds, so the split object key names
them too. -/
def includeEnv : IO (Array (String × Option String)) := do
  let cpath ← IO.getEnv "CPATH"
  let cinclude ← IO.getEnv "C_INCLUDE_PATH"
  let cplus ← IO.getEnv "CPLUS_INCLUDE_PATH"
  let objc ← IO.getEnv "OBJC_INCLUDE_PATH"
  pure #[("CPATH", cpath), ("C_INCLUDE_PATH", cinclude), ("CPLUS_INCLUDE_PATH", cplus),
    ("OBJC_INCLUDE_PATH", objc)]

/-- (F36) The key of one split unit's object: a SHA-256 of every input, so a collision
cannot reuse an unrelated object (the old key was a 64-bit `mixHash` of the text and a
re-spelling of the flags, which left the header, the `-ffile-prefix-map`s and the
compiler's include environment out). -/
def splitObjectKey (i : SplitObject) : String :=
  Smt.Sha256.hexFramed "wiz-build/split-object-v2"
    ([i.cc, "\n".intercalate i.flags.toList, i.text, i.header] ++
      i.env.toList.map fun (k, v) => k ++ "=" ++ v.getD "")

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
  -- (deterministic inputs; a part whose inputs are unchanged reuses its object)
  let inputs : Array (String × String × Bool) :=
    #[("support", C.splitSupport decls io extra unbox exports noMain, true)] ++
    parts.zipIdx.map fun (p : String × Nat) => (s!"part{p.2}", C.splitPartText header p.1, false)
  let cc := tc.cc
  let cflags := tc.cflags.toArray
  let map ← pathMapFlags tc.cflags dir
  let env ← includeEnv
  -- (F36) the key names the *actual* flags `cc -c` is given for the unit (plus its
  -- include environment), not a re-spelling of some of them
  let flagsOf (api : Bool) : Array String :=
    #["-O2", "-w", "-c"] ++ (if api then #["-DWIZ_API="] else #[]) ++ cflags ++ map
  let keyOf (text header : String) (api : Bool) : String :=
    splitObjectKey { cc, flags := flagsOf api, env, text, header }
  let ccOne (file obj : String) (api : Bool) : IO (Except String Unit) :=
    runCC cc (#["-O2", "-w", "-c", "-o", (dir / obj).toString, (dir / file).toString] ++
      (if api then #["-DWIZ_API="] else #[]) ++ cflags ++ map)
  let err ← IO.mkRef (none : Option String)
  let mut todo : Array (String × Bool × String) := #[]
  for (name, text, api) in inputs do
    -- (F36) the support unit does not include `wiz_split.h`; a part's object is compiled
    -- against it, so the header is part of a part's key
    let stamp := keyOf text (if api then "" else headerText) api
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
    match ds with
    | [] => none
    | _ => (String.ofList ds).toNat?.map fun n => (n, cs.drop ds.length)
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

/-- Why a compiled program did not give a result (`runGlobal`). The distinction is what
lets a test tell "this machine has no C toolchain" (a skip) from "the program failed" (a
failed case). Only `.toolchain` is a *build* failure that names the compiler, `llc` or a
header; a program's own stderr is never a toolchain condition, whatever it contains. -/
inductive RunError where
  /-- The build failed: no program ran. -/
  | build (msg : String)
  /-- The build could not find the C toolchain: the compiler or `llc` could not be started,
  or `gmp.h` is absent. The one failure a test may record as a skip. -/
  | toolchain (msg : String)
  /-- The program ran and exited with this code; `stderr` is what it wrote on standard
  error (reported with the code, so a failing case says why). -/
  | run (exitCode : UInt32) (stderr : String)
  /-- The program did not finish within its time limit. -/
  | timeout
  /-- The program ran and printed something that is not a value of its type. -/
  | readback (msg : String)

namespace RunError

/-- The failure as `wiz run` and the tests print it. -/
def message : RunError → String
  | .build m => m
  | .toolchain m => m
  | .run exitCode stderr => s!"the program failed ({exitCode}): {stderr}"
  | .timeout => "the program timed out"
  | .readback m => m

/-- Is the machine missing the C toolchain? This is the only `runGlobal` failure a test may
record as `skip "no toolchain"`; everything else (including `.run`) is the case's failure. -/
def isToolchain : RunError → Bool
  | .toolchain _ => true
  | _ => false

end RunError

/-- Is this build failure a missing C toolchain? The message names the compiler (or `llc`)
as a program that could not be started ("could not execute external process 'cc'", or
`cc: no such file…`), or the compiler cannot find `gmp.h`. A compiler that ran and
rejected the program does not count — and neither does a message that merely mentions a
missing file (such as a `link_c` source in the test): that is a failing build, not a
missing toolchain. -/
def missingToolchain (tc : Toolchain) (msg : String) : Bool :=
  let lower := msg.toLower
  let names (p : String) : Bool :=
    p != "" && ((msg.splitOn s!"could not execute external process '{p}'").length > 1 ||
      (msg.startsWith (p ++ ":") && (lower.splitOn "no such file").length > 1))
  (msg.splitOn "gmp.h").length > 1 || [tc.cc, tc.llc].any names

/-- Build and run the global `n` (through C, or LLVM); returns its result, read back
with its type. With `timeout`, the program is stopped after that many seconds (by
coreutils' `timeout`). A failure says whether it happened before the program ran
(`RunError.build`/`.toolchain`) or was the program itself (`.run`, with its exit code and
stderr; `.timeout`; `.readback`). -/
def runGlobal (tc : Toolchain) (s : CommandState R) (n : Name) (dir : System.FilePath) (llvm : Bool := false)
    (timeout : Option Nat := none) (args : Array String := #[]) (split : Nat := 0) :
    IO (Except RunError String) := do
  let exe := dir / "wiz_main"
  match ← build tc s n exe llvm false (split := split) with
    | .error e => pure (.error (if missingToolchain tc e then .toolchain e else .build e))
    | .ok ty =>
      let io := isIO ty
      let out ← match timeout with
        | some t => IO.Process.output { cmd := "timeout", args := #[toString t, exe.toString] ++ args }
        | none => IO.Process.output { cmd := exe.toString, args }
      if out.exitCode == 124 && timeout.isSome then return .error .timeout
      if out.exitCode != 0 then return .error (.run out.exitCode out.stderr)
      -- an `IO` program prints for itself
      if io then return .ok out.stdout
      match parseValue out.stdout with
      | none => pure (.error (.readback s!"could not read the result: {out.stdout}"))
      | some v => pure (.ok (readback s.globals s.builtins (eval s.globals [] ty) v).pretty)

/-- (8f, F12) The JS host of a Wasm module: beside the toolchain's library, so
`share/wiz/web` in a Nix package or release tarball and `web` in a checkout (as `webDir`
does for the infoview), else `./web/wasm-host.mjs` for a checkout run from its root. -/
def wasmHostPath : IO System.FilePath := do
  let base := (← Module.toolchainLib).parent.getD "."
  let installed := base / "web" / "wasm-host.mjs"
  if ← installed.pathExists then return installed
  pure ("web" / "wasm-host.mjs")

/-- The JavaScript runtime the `--target js` modules paste in (`web/wiz-js-runtime.mjs`):
beside the toolchain's library in an installation, `web/` in a checkout. -/
def jsRuntimePath : IO System.FilePath := do
  let base := (← Module.toolchainLib).parent.getD "."
  let installed := base / "web" / "wiz-js-runtime.mjs"
  if ← installed.pathExists then return installed
  pure ("web" / "wiz-js-runtime.mjs")

/-- Build `main` as a self-contained ES module. `OUT` ends in `.mjs` or `.js`, or the
extension is chosen (`.mjs`). The IR is the C/LLVM/Wasm IR; the representation and the
supported subset are in `Wiz/Compiler/Js.lean` and `wiz-notes/js-target.md`. -/
def buildJs (s : CommandState R) (n : Name) (out : System.FilePath) : IO (Except String (Term R)) := do
  match irProgram s n with
  | .error e => pure (.error e)
  | .ok (decls, ty) =>
    let runtimePath ← jsRuntimePath
    unless ← runtimePath.pathExists do
      return .error s!"the JS runtime is missing: no {runtimePath} (a toolchain ships it in share/wiz/web; a checkout has web/wiz-js-runtime.mjs)"
    let runtime ← IO.FS.readFile runtimePath
    match Js.program runtime decls (isIO ty) with
    | .error e => pure (.error e)
    | .ok text =>
      let outPath : System.FilePath :=
        if out.toString.endsWith ".mjs" || out.toString.endsWith ".js" then out
        else out.withExtension "mjs"
      IO.FS.writeFile outPath text
      pure (.ok ty)

/-- Build `main` with the JS backend and run it under Node, reading the printed result
back with `main`'s type (as `runGlobal` does for C); an `IO` program's standard output is
the result, since it prints for itself. -/
def runJsGlobal (s : CommandState R) (n : Name) (dir : System.FilePath) :
    IO (Except String String) := do
  let file := dir / "wiz_main.mjs"
  match ← buildJs s n file with
  | .error e => pure (.error e)
  | .ok ty =>
    let out ← try
      -- (under `lake env`, Lean's LD_LIBRARY_PATH breaks Node's own library lookup)
      IO.Process.output
        { cmd := "node", args := #[file.toString], env := #[("LD_LIBRARY_PATH", none)] }
    catch e => return .error s!"node: {e}"
    if out.exitCode != 0 then
      return .error s!"the JS program failed ({out.exitCode}): {out.stderr.take 1500}"
    if isIO ty then return .ok out.stdout
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
      let host ← wasmHostPath
      unless ← host.pathExists do
        return .error s!"the Wasm host is missing: no {host} (a toolchain ships it in share/wiz/web; a checkout has web/wasm-host.mjs)"
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

/-- (F09) A header name that may be written into `#include <…>`. A name with `"`, `<`,
`>`, a backslash, whitespace or a newline would leave the directive (a newline starts
another one) or close the bracket, so a string in the source could inject preprocessor
directives — and their output is the C text spliced into the program. Paths (`stdio.h`,
`sys/types.h`, `/tmp/x.h`) are names; only the characters are checked. -/
def validHeaderName (h : String) : Bool :=
  !h.isEmpty && h.toList.all fun c =>
    c.isAlphanum || c == '_' || c == '.' || c == '/' || c == '-' || c == '+'

/-- (F09) The error for a header name that is not a header name. The offending text is
not quoted back: it may hold a newline and a preprocessor directive, which would then be
a directive in a log as well. -/
def badHeaderName : String :=
  "import_c: not a valid C header name (letters, digits and `_ . / + -` only; a newline, " ++
  "quote, angle bracket or backslash would inject a preprocessor directive)"

/-- (F09) The error for a header the C compiler could not preprocess. -/
def preprocessFailed (cc h : String) (exitCode : UInt32) (stderr : String) : String :=
  s!"import_c {h}: {cc} -E failed ({exitCode}): {stderr.trimAscii}"

/-- Preprocess the headers a file imports (`import_c "h"`), since the frontend is pure. -/
def preprocessHeaders (tc : Toolchain) (input : String) : IO (Std.HashMap String String) := do
  let mut m : Std.HashMap String String := {}
  for part in (input.splitOn "import_c \"").drop 1 do
    let h := (part.splitOn "\"").headD ""
    if h.isEmpty || m.contains h then continue
    -- (F09) only a plausible header name reaches `cc`: a newline or `>` in it would
    -- splice another preprocessor directive into the generated `#include`
    unless validHeaderName h do throw (IO.userError badHeaderName)
    let cc := tc.cc
    let dir ← IO.FS.createTempDir
    -- (F11) one scratch directory per header, removed whatever `cc` does
    try
      IO.FS.writeFile (dir / "h.c") s!"#include <{h}>\n"
      let out ← IO.Process.output { cmd := cc, args := #["-E", "-P", (dir / "h.c").toString] ++ tc.cflags.toArray }
      -- (F09) a header that cannot be preprocessed is an error: skipping it would let a
      -- check pass with types that nothing read (and hide a broken `--cflags`)
      if out.exitCode != 0 then
        throw (IO.userError (preprocessFailed cc h out.exitCode out.stderr))
      m := m.insert h out.stdout
    finally
      try IO.FS.removeDirAll dir catch _ => pure ()
  pure m


end Wiz.Build
