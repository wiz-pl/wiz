import Wiz
import Wiz.Version
import Wiz.Doc.Site

open Wiz

def usage : String := "usage:
  wiz --version           print the version (and, for a release, its commit)
  wiz parse FILE          print the syntax tree of every command
  wiz check [-I DIR] FILE elaborate and type check (quantities: 0, 1, ω); -I DIR: another
                          module root (a package's src/), before or after FILE
  wiz build FILE -o OUT [--llvm]   compile the definition `main` to an executable (via C or LLVM)
  wiz build FILE -o OUT --lib      … or the exported functions to an object file, with OUT.h
  wiz build FILE -o OUT --no-main  … or the exported functions, linked without a `main`
                                   (say, a Wasm module: --cc emcc --ldflags --no-entry)
  wiz run FILE [--llvm]            build and run `main`, printing its value
  wiz doc [MODULE|FILE|DIR…] -o OUT [--lib] [--source-url URL] [--title T] [--web DIR]
                                   documentation: a static site (one page per module,
                                   index, search); --lib: the toolchain's library;
                                   source links are URL + path in its root + #L<line>
  wiz lsp                          a language server on stdin/stdout
  wiz lsp --infoview SOCK          … and for infoviews on the Unix socket SOCK
  wiz lsp --ws [ADDR:]PORT         … and on a WebSocket (127.0.0.1 unless ADDR is given;
                                   both flags may be given; --no-stdio: no editor on stdin)
  wiz lsp … --web DIR              the web infoview's files, served on the WebSocket's port
                                   (default: share/wiz/web, or web/out in a checkout)
options: --cache DIR (the elaboration cache, default ~/.cache/wiz; shared, since it is
content-addressed), --no-cache, -I DIR (another module root, after lib/)
trust: --trust-native (27a: `def X : a = b := native_refl` is decided by running a and b;
the kernel does not check it, `#print axioms` lists it), --native-fuel N (its step limit)
experimental kernel options (D1, they turn the cache off): --regularity off|full (full:
Cast-Refl at every type, decided in conversion; default off),
--predicative-prop, --eager-proofs (P2: the evaluator runs proofs, as it did before; the
default never evaluates them),
--inert ground|conv (P1: regularity at inert types, decided by conversion (conv, the
default) or only by the evaluator's fast path (ground))
compiler option (turns the cache off): --unbox-structs (22i: a structure's last field is
unboxed; not stable under substitution, so off by default)
--strict-privacy (13b, an experiment; turns the cache off): check each declaration again with
  the definitions of other modules' types with private parts hidden
--pp-all (11r; turns the cache off): print terms without notation (as `set_option pp.all true`)
toolchain: --cc X (default: a release's own share/wiz/cc, else cc), --cflags \"…\" --ldflags \"…\" (where GMP lives),
  --libs \"…\" (say -lm), --gmp \"…\" (default -lgmp), --llc X (default llc)"

def parseCmd (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let r := parseFile input
  for cmd in r.commands do
    IO.println cmd.toSExpr
  for m in r.messages do
    IO.eprintln s!"{path}:{m.render input}"
  pure (if r.messages.isEmpty then 0 else 1)

/-- The module roots: the toolchain's library (`Module.toolchainLib`, the binary's own,
whatever the current directory; `./lib` only when there is none), then the `-I`
directories. Only the first root's modules are trusted (stage 22f), and since the first
root that has a module wins, no other directory can stand in for one of them. (`./lib`
is not searched besides: run in another checkout, every module of its `lib/` would be
reported as shadowed.) -/
def moduleRoots (tc : Toolchain) : IO (List System.FilePath) :=
  Module.roots tc.searchPath

/-- The library modules from the toolchain's own `lib/` (the first root): their
`builtin` registrations are trusted. -/
def libTrusted (tc : Toolchain) : IO (List String) := do
  let roots ← moduleRoots tc
  return Module.fromFirstRoot roots (← Module.loadAll roots)

/-- Library modules with their paths (for the language server's go-to-definition). -/
def loadLibraryPaths (tc : Toolchain) : IO (Std.HashMap String (String × String)) := do
  let mut m : Std.HashMap String (String × String) := {}
  for (n, p, src) in (← Module.loadAll (← moduleRoots tc)).toList do
    m := m.insert n ((← IO.FS.realPath p).toString, src)
  pure m

/-- `wiz lsp`'s options: `--infoview SOCK`, `--ws [ADDR:]PORT`, `--no-stdio`. -/
def lspOptions : List String → Option (LSP.Listen × Bool)
  | [] => some ({}, true)
  | "--infoview" :: sock :: rest => do let (l, io) ← lspOptions rest; pure ({ l with infoview := some sock }, io)
  | "--ws" :: spec :: rest => do
    let (l, io) ← lspOptions rest
    let (addr, port) ← match spec.splitOn ":" with
      | [p] => pure (Socket.loopback, p)
      | [a, p] => do pure (← Socket.parseIPv4 a, p)
      | _ => none
    let port ← port.toNat?
    if port ≥ 65536 then none
    pure ({ l with ws := some (addr, port.toUInt16) }, io)
  | "--no-stdio" :: rest => do let (l, _) ← lspOptions rest; pure (l, false)
  | "--web" :: dir :: rest => do let (l, io) ← lspOptions rest; pure ({ l with web := some dir }, io)
  | _ => none

/-- (11w) The web infoview's files (`web/build.sh`'s output) beside the toolchain's
library: `share/wiz/web` in a release, `web/out` in a checkout. -/
def webDir : IO (Option String) := do
  let lib ← Module.toolchainLib
  let base := (lib.parent.getD ".")
  for d in [base / "web", base / "web" / "out"] do
    if ← (d / "wiz-infoview.mjs").pathExists then return some (← IO.FS.realPath d).toString
  pure none

/-- The experimental kernel options (D1): `--regularity MODE`, `--predicative-prop`. -/
initialize kernelOpts : IO.Ref (Regularity × Bool) ← IO.mkRef (.off, false)

/-- `--strict-privacy` (13b, an experiment): the second check of every declaration against
the elaborator's view. Off by default. -/
initialize strictPrivacyOpt : IO.Ref Bool ← IO.mkRef false

/-- (11r) `--pp-all`: terms print without notation. -/
initialize ppAllOpt : IO.Ref Bool ← IO.mkRef false

/-- P2: proofs are never evaluated, unless `--eager-proofs` (the old behaviour). -/
initialize lazyProofsOpt : IO.Ref Bool ← IO.mkRef true

/-- (P2) `--proof-steps N`: the step budget for reading one proof back, outside the kernel
(`Budget`); and `--trace-proof-steps`, which prints what each read-back took. -/
initialize proofStepsOpt : IO.Ref (Nat × Bool) ← IO.mkRef (Budget.defaultSteps, false)

/-- Take `--proof-steps N` and `--trace-proof-steps` out of the arguments. -/
def takeProofSteps : List String → Except String (Option Nat × Bool × List String)
  | "--proof-steps" :: n :: rest => do
    let some k := n.toNat? | throw s!"--proof-steps needs a number, not {n}"
    let (_, t, rest) ← takeProofSteps rest
    return (some k, t, rest)
  | "--trace-proof-steps" :: rest => do
    let (k, _, rest) ← takeProofSteps rest
    return (k, true, rest)
  | a :: rest => do
    let (k, t, rest) ← takeProofSteps rest
    return (k, t, a :: rest)
  | [] => return (none, false, [])

/-- (P1) `--inert MODE`: regularity at inert types. -/
initialize inertOpt : IO.Ref InertReg ← IO.mkRef .conv

/-- `--unbox-structs` (22i): the last field of a structure is unboxed. Off by default: the
representation is not stable under substitution (`unboxedSigma` in `Erase.lean`). -/
initialize unboxOpt : IO.Ref Bool ← IO.mkRef false

/-- Take `--inert MODE` out of the arguments. -/
def takeInertOpt : List String → Except String (Option InertReg × List String)
  | "--inert" :: m :: rest => do
    let r ← match m with
      | "ground" => pure InertReg.ground | "conv" => pure .conv
      | _ => throw s!"unknown inert mode {m}"
    let (_, rest) ← takeInertOpt rest
    return (some r, rest)
  | a :: rest => do
    let (r, rest) ← takeInertOpt rest
    return (r, a :: rest)
  | [] => return (none, [])

/-- Elaborate a file, through the toolchain's cache (if any). -/
def elaborate (tc : Toolchain) (path : String) (input : String) : IO (CommandState ZeroOneMany) := do
  -- every module the file can reach (`import A.B` is `A/B.wiz` under a root), read up
  -- front: the frontend is pure
  let roots ← moduleRoots tc
  let closure ← Module.loadClosure roots input
  let lib : Std.HashMap Name String := closure.fold (fun m n (_, src) => m.insert n src) {}
  -- the C headers of the file and of the modules it imports
  let headers ← Build.preprocessHeaders tc (String.join (input :: lib.values))
  -- (9f) the `link_c` files, each relative to its own file
  let sources ← Module.cSourceTable ((System.FilePath.mk path).parent.getD ".") input closure
  -- (include-str) the `include_str` files, each relative to its own file
  let includes ← Module.includeTable ((System.FilePath.mk path).parent.getD ".") input closure
  let (regularity, predicativeProp) ← kernelOpts.get
  let lazyProofs ← lazyProofsOpt.get
  let inertReg ← inertOpt.get
  let (proofSteps, traceProofSteps) ← proofStepsOpt.get
  let unboxStructs ← unboxOpt.get
  -- `builtin` registrations are trusted only in the toolchain's own library
  let own := Module.fromFirstRoot roots closure
  -- a file that would replace one of them is ignored: say so (loudly: it may be meant
  -- to stand in for the toolchain's module, `builtin`s and all)
  let shadow := (← Module.shadowed roots closure).map fun (n, p) =>
    ({ info := {}, severity := .warning,
       text := s!"{p} is ignored: module {n} is the toolchain's own ({roots.head!}), which a module root cannot replace" } : Msg)
  let init : CommandState ZeroOneMany :=
    { loader := (lib[·]?), cHeaders := (headers[·]?), cSources := some (Module.cSourceResolver sources),
      includes := some (Module.includeResolver includes),
      messages := shadow.toArray,
      globals := { regularity, predicativeProp, lazyProofs, inertReg, unboxStructs, proofSteps, traceProofSteps,
                   strictPrivacy := ← strictPrivacyOpt.get, pp := { useNotation := !(← ppAllOpt.get) } },
      trustedModule := own.contains, trustNative := tc.trustNative,
      nativeFuel := tc.nativeFuel.getD NativeRun.defaultFuel, smt := ← tc.smt.resolve }
  -- the cache doesn't know the experimental options
  let cache := if regularity == .off && !predicativeProp && lazyProofs && inertReg == .conv && !unboxStructs &&
      proofSteps == Budget.defaultSteps && !traceProofSteps && !(← strictPrivacyOpt.get) && !(← ppAllOpt.get)
    then tc.cacheDir else none
  match cache with
  | none => Cache.elaborateUncached input init
  | some dir =>
    -- the key starts from the headers the file sees; modules enter it by their own keys
    let key₀ := hash (toString (headers.toList.map (·.2)))
    pure (← Cache.elaborateCached dir input init key₀).1

/-- (27a) `--trust-native` and `--native-fuel N`. -/
def nativeOpts (tc : Toolchain) : Bool × Nat := (tc.trustNative, tc.nativeFuel.getD NativeRun.defaultFuel)

/-- (11s) `wiz doc`'s options. -/
structure DocArgs where
  out : Option String := none
  lib : Bool := false
  sourceUrl : Option String := none
  title : Option String := none
  web : Option String := none
  inputs : List String := []

def docArgs (a : DocArgs) : List String → Except String DocArgs
  | [] => pure { a with inputs := a.inputs.reverse }
  | "-o" :: o :: rest => docArgs { a with out := some o } rest
  | "--lib" :: rest => docArgs { a with lib := true } rest
  | "--source-url" :: u :: rest => docArgs { a with sourceUrl := some u } rest
  | "--title" :: t :: rest => docArgs { a with title := some t } rest
  | "--web" :: w :: rest => docArgs { a with web := some w } rest
  | x :: rest => if x.startsWith "-" then throw s!"wiz doc: unknown option {x}" else docArgs { a with inputs := x :: a.inputs } rest

/-- The path of `p` relative to `root` (`p` itself if it isn't under it). -/
def relativeTo (root p : System.FilePath) : IO String := do
  let r := (← IO.FS.realPath root).toString
  let q := (← IO.FS.realPath p).toString
  pure (if q.startsWith (r ++ "/") then (q.drop (r.length + 1)).toString else p.toString)

/-- (11s) `wiz doc`: the modules to document, then the site (`Wiz.Doc.run`). -/
def docCmd (tc : Toolchain) (args : List String) : IO UInt32 := do
  let a ← match docArgs {} args with
    | .ok a => pure a
    | .error e => do IO.eprintln e; return 2
  let some out := a.out | IO.eprintln "wiz doc: -o OUT is required"; return 2
  -- every input that is a directory or a file is a module root
  let mut tc := tc
  let mut wanted : Array (String × System.FilePath × System.FilePath) := #[]
  let lib ← Module.toolchainLib
  if a.lib then
    for (n, p) in ← Module.listRoot lib do wanted := wanted.push (n, p, lib)
  for i in a.inputs do
    let p : System.FilePath := i
    if ← p.isDir then
      tc := { tc with searchPath := tc.searchPath ++ [p] }
      for (n, f) in ← Module.listRoot p do wanted := wanted.push (n, f, p)
    else if p.extension == some "wiz" then
      let root := p.parent.getD "."
      tc := { tc with searchPath := tc.searchPath ++ [root] }
      wanted := wanted.push ((p.fileStem.getD i), p, root)
    else
      let all ← Module.loadAll (← moduleRoots tc)
      match all.get? i with
      | some (f, _) => wanted := wanted.push (i, f, f.parent.getD ".")
      | none => IO.eprintln s!"wiz doc: no module {i}"; return 1
  if wanted.isEmpty then IO.eprintln "wiz doc: nothing to document (give modules, files, directories or --lib)"; return 2
  -- (a module found twice, as a file and in a directory: once)
  let mut mods : Array Doc.Module := #[]
  for (n, f, root) in wanted do
    if mods.any (·.name == n) then continue
    mods := mods.push { name := n, src := ← IO.FS.readFile f, rel := ← relativeTo root f }
  let web ← match a.web with
    | some w => pure (some (System.FilePath.mk w))
    | none => do pure ((← webDir).map System.FilePath.mk)
  -- the site's own files: beside the Wasm module (a release), or web/ of the checkout
  let base := lib.parent.getD "."
  let mut assets : Option System.FilePath := none
  for d in (web.toList ++ [base / "web", base / "share" / "wiz" / "web"]) do
    if assets.isNone && (← (d / "scroll.css").pathExists) then assets := some d
  let o : Doc.Options := { out, sourceUrl := a.sourceUrl, title := a.title.getD "Wiz documentation", web, assets }
  let n ← Doc.run (fun m => elaborate tc "<doc>" s!"import {m}\n") mods o
  IO.println s!"wiz doc: {n} modules, {out}/index.html"
  if web.isNone then IO.println "wiz doc: no Wasm module (web/build.sh): the pages are plain HTML"
  pure 0

def checkCmd (tc : Toolchain) (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let s ← elaborate tc path input
  for m in s.messages do
    let line := s!"{path}:{m.render input}"
    if m.severity == .error then IO.eprintln line else IO.println line
  pure (if s.messages.any (·.severity == .error) then 1 else 0)

def elabFile (tc : Toolchain) (path : String) : IO (Option (CommandState ZeroOneMany)) := do
  let input ← IO.FS.readFile path
  let s ← elaborate tc path input
  for m in s.messages do
    if m.severity == .error then IO.eprintln s!"{path}:{m.render input}"
  pure (if s.messages.any (·.severity == .error) then none else some s)

def buildCmd (tc : Toolchain) (path out : String) (llvm : Bool) (lib : Bool := false) (noMain : Bool := false) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  match ← Build.build tc s "main" out llvm lib noMain with
  | .error e => IO.eprintln e; pure 1
  | .ok _ => pure 0

def runCmd (tc : Toolchain) (path : String) (llvm : Bool) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal tc s "main" dir llvm with
  | .error e => IO.eprintln e; pure 1
  | .ok v => IO.print (if v.endsWith "\n" then v else v ++ "\n"); pure 0

/-- The experimental kernel options, taken out of the arguments. -/
def kernelOpt : List String → Except String (Regularity × Bool × List String)
  | "--regularity" :: m :: rest => do
    let r ← match m with
      | "full" => pure Regularity.full
      | "off" => pure .off | _ => throw s!"unknown regularity mode {m}"
    let (_, p, rest) ← kernelOpt rest
    return (r, p, rest)
  | "--predicative-prop" :: rest => do
    let (r, _, rest) ← kernelOpt rest
    return (r, true, rest)
  | a :: rest => do
    let (r, p, rest) ← kernelOpt rest
    return (r, p, a :: rest)
  | [] => return (.off, false, [])

def main (args : List String) : IO UInt32 := do
  -- (after the toolchain flags: the tarball's and tower's wrappers put `-I LIB` and
  -- their flags before the user's arguments)
  if ((({} : Toolchain).parseFlags args).2) == ["--version"] then
    IO.println (← versionLine "wiz"); return 0
  let home := (← IO.getEnv "HOME").getD "."
  -- the toolchain comes from flags only (no environment variables)
  -- (26f) a release toolchain's own C compiler, GMP and GC are the defaults
  let defaults ← ({ cacheDir := some (System.FilePath.mk home / ".cache" / "wiz") } : Toolchain).withBundled
  let (tc, args) := defaults.parseFlags args
  if args.contains "--strict-privacy" then strictPrivacyOpt.set true
  let args := args.filter (· != "--strict-privacy")
  if args.contains "--pp-all" then ppAllOpt.set true
  let args := args.filter (· != "--pp-all")
  if args.contains "--unbox-structs" then unboxOpt.set true
  let args := args.filter (· != "--unbox-structs")
  lazyProofsOpt.set (!args.contains "--eager-proofs")
  let args := args.filter (· != "--eager-proofs")
  let args ← match takeProofSteps args with
    | .ok (k, t, a) => do proofStepsOpt.set (k.getD Budget.defaultSteps, t); pure a
    | .error e => do IO.eprintln e; return 1
  let args ← match takeInertOpt args with
    | .ok (r, a) => do if let some r := r then inertOpt.set r
                       pure a
    | .error e => do IO.eprintln e; return 1
  let args ← match kernelOpt args with
    | .ok (r, p, a) => do kernelOpts.set (r, p); pure a
    | .error e => do IO.eprintln e; return 1
  -- a `panic!` (a kernel-internal failure) ends a batch command with status 1 instead of
  -- going on with a default value; the language server keeps running
  unless args.head? == some "lsp" do exitOnPanic
  match args with
  | ["parse", path] => parseCmd path
  | ["check", path] => checkCmd tc path
  | ["build", path, "-o", out] => buildCmd tc path out false
  | ["build", path, "-o", out, "--llvm"] => buildCmd tc path out true
  | ["build", path, "-o", out, "--lib"] => buildCmd tc path out false true
  | ["build", path, "-o", out, "--lib", "--llvm"] | ["build", path, "-o", out, "--llvm", "--lib"] =>
    buildCmd tc path out true true
  | ["build", path, "-o", out, "--no-main"] => buildCmd tc path out false false true
  | ["build", path, "-o", out, "--no-main", "--llvm"] | ["build", path, "-o", out, "--llvm", "--no-main"] =>
    buildCmd tc path out true false true
  | "doc" :: rest => docCmd tc rest
  | ["run", path] => runCmd tc path false
  | ["run", path, "--llvm"] => runCmd tc path true
  | "lsp" :: opts => do
    match lspOptions opts with
    | none => IO.println usage; pure 2
    | some (listen, stdio) =>
      let listen ← if listen.web.isSome then pure listen else do pure { listen with web := ← webDir }
      LSP.serve (← loadLibraryPaths tc) listen stdio (← libTrusted tc) (nativeOpts tc) (← tc.smt.resolve)
      -- (an infoview's reader thread may still be blocked: don't wait for it)
      IO.Process.exit 0
  | [] | ["help"] | ["--help"] | ["-h"] => do IO.println usage; pure 0
  | _ => do
    -- (an unknown flag, `--impl` say, or a command used wrongly: an error, not the usage
    -- with success)
    match args.find? (·.startsWith "-") with
    | some f => IO.eprintln s!"unknown flag: {f}"
    | none => IO.eprintln s!"unknown command: {" ".intercalate args}"
    IO.eprintln usage
    pure 2
