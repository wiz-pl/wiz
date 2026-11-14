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
  wiz build FILE -o OUT [--split N]  compile the program as N C units in parallel
                                   (default 1: one unit; a split build is faster but the
                                   generated program runs somewhat slower, stage 15k)
  wiz build FILE -o OUT --lib      … or the exported functions to an object file, with OUT.h
  wiz build FILE -o OUT --no-main  … or the exported functions, linked without a `main`
                                   (say, a Wasm module: --cc emcc --ldflags --no-entry)
  wiz run FILE [--llvm]            build and run `main`, printing its value
  wiz repl [--llvm]                read one command per line, keeping definitions (`:help`;
                                   a pipe: one command per line, no prompt; `:type EXPR`,
                                   `:load FILE`)
  wiz test-driver [GROUPS…] [--jobs N] [--list]
                                   run the test driver (`.lake/build/bin/tests`, or WIZ_TESTS)
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
content-addressed), --cache-ro DIR (repeatable: a read-only cache, searched in order
after the write cache and never written, as in a Nix package's share/wiz/cache),
--no-cache (both), -I DIR (another module root, after lib/)
  --region-cache (experimental: also serve cached modules from mmap'ed .wizr regions,
  read from the same caches and written to the write cache), --region-stats (print what
  the regions served, with --region-cache)
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

/-- `--region-cache` (experimental): serve a module's cached effects from an mmap'ed `.wizr`
region instead of decoding its `.wizc` entries. The text entries stay the authority and the
fallback; off by default. -/
initialize regionCacheOpt : IO.Ref Bool ← IO.mkRef false

/-- `--region-stats`: with `--region-cache`, print what the regions served (to stderr). -/
initialize regionStatsOpt : IO.Ref Bool ← IO.mkRef false

/-- `--region-stats`' counters (per process). -/
initialize regionStats : IO.Ref Cache.RegionCounts ← IO.mkRef {}

/-- (15k) `--split N`: compile a large program as `N` C translation units in parallel
(0: automatically, for a large program; 1: one unit). -/
initialize splitOpt : IO.Ref Nat ← IO.mkRef 0

/-- Take `--split N` out of the arguments. -/
def takeSplitOpt : List String → Except String (Option Nat × List String)
  | "--split" :: n :: rest => do
    let some k := n.toNat? | throw s!"bad --split {n}"
    let (_, rest) ← takeSplitOpt rest
    return (some k, rest)
  | a :: rest => do
    let (k, rest) ← takeSplitOpt rest
    return (k, a :: rest)
  | [] => return (none, [])

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

/-- The state every elaboration starts from: the kernel and printing options, the
`builtin` registrations trusted (the toolchain's own modules), and the hooks the pure
frontend needs (the loader, the C headers, the `link_c` files). -/
def initStateOf (tc : Toolchain) (lib : Std.HashMap Name String) (headers : Std.HashMap String String)
    (cSources : Option (String → String → Option String)) (own : List Name)
    (messages : Array Msg := #[]) : IO (CommandState ZeroOneMany) := do
  let (regularity, predicativeProp) ← kernelOpts.get
  let lazyProofs ← lazyProofsOpt.get
  let inertReg ← inertOpt.get
  let (proofSteps, traceProofSteps) ← proofStepsOpt.get
  let unboxStructs ← unboxOpt.get
  let init : CommandState ZeroOneMany :=
    { loader := (lib[·]?), cHeaders := (headers[·]?), cSources,
      messages,
      globals := { regularity, predicativeProp, lazyProofs, inertReg, unboxStructs, proofSteps, traceProofSteps,
                   strictPrivacy := ← strictPrivacyOpt.get, pp := { useNotation := !(← ppAllOpt.get) } },
      trustedModule := own.contains, trustNative := tc.trustNative,
      nativeFuel := tc.nativeFuel.getD NativeRun.defaultFuel, smt := ← tc.smt.resolve }
  pure init

/-- Elaborate a file, through the toolchain's cache (if any). -/
def elaborate (tc : Toolchain) (path : String) (input : String) : IO (CommandState ZeroOneMany) := do
  let roots ← moduleRoots tc
  let closure ← Module.loadClosure roots input
  let lib : Std.HashMap Name String := closure.fold (fun m n (_, src) => m.insert n src) {}
  let headers ← Build.preprocessHeaders tc (String.join (input :: lib.values))
  let sources ← Module.cSourceTable ((System.FilePath.mk path).parent.getD ".") input closure
  let own := Module.fromFirstRoot roots closure
  let shadow := (← Module.shadowed roots closure).map fun (n, p) =>
    ({ info := {}, severity := .warning,
       text := s!"{p} is ignored: module {n} is the toolchain's own ({roots.head!}), which a module root cannot replace" } : Msg)
  let init ← initStateOf tc lib headers (some (Module.cSourceResolver sources)) own shadow.toArray
  let (regularity, predicativeProp) ← kernelOpts.get
  let lazyProofs ← lazyProofsOpt.get
  let inertReg ← inertOpt.get
  let (proofSteps, traceProofSteps) ← proofStepsOpt.get
  let unboxStructs ← unboxOpt.get
  -- the cache doesn't know the experimental options
  let cacheOn := regularity == .off && !predicativeProp && lazyProofs && inertReg == .conv && !unboxStructs &&
      proofSteps == Budget.defaultSteps && !traceProofSteps && !(← strictPrivacyOpt.get) && !(← ppAllOpt.get)
  if cacheOn && (tc.cacheDir.isSome || !tc.readCaches.isEmpty) then
    -- the key starts from the headers the file sees; modules enter it by their own keys
    let key₀ := hash (toString (headers.toList.map (·.2)))
    let region ← if ← regionCacheOpt.get then
        pure (some ({ rig := RigTag.tag (R := ZeroOneMany), stats := some regionStats } :
          Cache.RegionOptions))
      else pure none
    pure (← Cache.elaborateCached tc.cacheDir tc.readCaches input init key₀ (region := region)).1
  else
    Cache.elaborateUncached input init
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
  if ← regionStatsOpt.get then
    let c ← regionStats.get
    IO.eprintln s!"region cache: {c.hits} modules from a region, {c.misses} without, {c.commands} commands"
  pure (if s.messages.any (·.severity == .error) then 1 else 0)

def elabFile (tc : Toolchain) (path : String) : IO (Option (CommandState ZeroOneMany)) := do
  let input ← IO.FS.readFile path
  let s ← elaborate tc path input
  for m in s.messages do
    if m.severity == .error then IO.eprintln s!"{path}:{m.render input}"
  pure (if s.messages.any (·.severity == .error) then none else some s)

def buildCmd (tc : Toolchain) (path out : String) (llvm : Bool) (lib : Bool := false) (noMain : Bool := false)
    (split : Nat := 0) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  match ← Build.build tc s "main" out llvm lib noMain split with
  | .error e => IO.eprintln e; pure 1
  | .ok _ => pure 0

def runCmd (tc : Toolchain) (path : String) (llvm : Bool) (split : Nat := 0) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal tc s "main" dir llvm (split := split) with
  | .error e => IO.eprintln e; pure 1
  | .ok v => IO.print (if v.endsWith "\n" then v else v ++ "\n"); pure 0

/-- The modules the REPL can import, and the hooks the frontend needs: every module under
the roots (so a `:reset` need not read them again), its C headers and `link_c` files. -/
def replInit (tc : Toolchain) : IO (CommandState ZeroOneMany) := do
  let roots ← moduleRoots tc
  let all ← Module.loadAll roots
  let lib : Std.HashMap Name String := all.fold (fun m n (_, src) => m.insert n src) {}
  let headers ← Build.preprocessHeaders tc (String.join (all.values.map (·.2)))
  let sources ← Module.cSourceTable "." "" all
  initStateOf tc lib headers (some (Module.cSourceResolver sources)) (Module.fromFirstRoot roots all)

/-- `wiz repl [--llvm]`: read one command per line from stdin, elaborate it against the
accumulated `CommandState` (definitions persist), print its messages and go on after an
error. `:quit`/EOF exit, `:reset` forgets every definition, `:help` lists the commands;
`:type EXPR` prints a type and `:load FILE` elaborates a file into the session. With
`--llvm`, `:run NAME` builds through LLVM instead of C.

The base state stays pristine, so an `import` is checked in isolation as in a file, then
elaborated into the session's state. A pipe has one command per line and no prompt. -/
def replCmd (tc : Toolchain) (llvm : Bool) : IO UInt32 := do
  let base ← replInit tc
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let tty ← stdin.isTty
  -- a session starts with the Prelude, as a file's first line would import it
  let preloaded := match base.loader "Prelude" with
    | some _ => runFrontend.go "import Prelude" base "import Prelude".toList.toArray 0 base
    | none => base
  let help := "commands:\n" ++
    "  LINE          elaborate a command (`def`, `#check`, `#eval`, `import`, …)\n" ++
    "  :type EXPR    print the type of EXPR (like #check)\n" ++
    "  :load FILE    elaborate FILE into this session (its definitions stay)\n" ++
    "  :run NAME     build and run the definition NAME (" ++ (if llvm then "LLVM" else "C") ++ ")\n" ++
    "  :reset        forget every definition\n" ++
    "  :help         this list\n" ++
    "  :quit         leave (EOF does too)\n" ++
    "The Prelude is imported at the start; errors are reported and the session goes on."
  -- print the messages an input added (with its path, for `:load`), then forget them so
  -- the next input does not print them again
  let report (before : Nat) (s' : CommandState ZeroOneMany) (input : String)
      (path? : Option String) : IO Unit := do
    for m in s'.messages.extract before s'.messages.size do
      let text := match path? with
        | some p => s!"{p}:{m.render input}"
        | none => m.render input
      if m.severity == .error then stderr.putStrLn text else stdout.putStrLn text
  let mut state := preloaded
  let mut reading := true
  while reading do
    if tty then
      stdout.putStr "wiz> "
      stdout.flush
    let raw ← stdin.getLine
    if raw.isEmpty then
      -- EOF (an empty line is "\n": `getLine` includes the newline)
      if tty then IO.println ""
      reading := false
    else
      let line := raw.trimAscii.toString
      unless line.isEmpty do
        match line with
        | ":quit" | ":q" => reading := false
        | ":help" | ":h" | ":?" => stdout.putStrLn help; stdout.flush
        | ":reset" =>
          state := preloaded
          stdout.putStrLn "reset"; stdout.flush
        | c =>
          if c.startsWith ":" then
            if c == ":type" then
              stderr.putStrLn "usage: :type EXPR"
            else if c.startsWith ":type " then
              let text := s!"#check {(c.drop 6).trimAscii.toString}"
              let s' := runFrontend.go text base text.toList.toArray 0 state
              report state.messages.size s' text none
              state := { s' with messages := #[] }
            else if c == ":load" then
              stderr.putStrLn "usage: :load FILE"
            else if c.startsWith ":load " then
              let path := (c.drop 6).trimAscii.toString
              let text? ← try
                pure (some (← IO.FS.readFile path))
              catch e =>
                stderr.putStrLn s!"cannot read {path}: {e}"
                pure none
              match text? with
              | none => pure ()
              | some text =>
                let s' := runFrontend.go text base text.toList.toArray 0 state
                report state.messages.size s' text (some path)
                state := { s' with messages := #[] }
            else
              match c.splitOn " " with
              | [":run", name] =>
                let dir ← IO.FS.createTempDir
                match ← Build.runGlobal tc state name dir llvm with
                | .error e => stderr.putStrLn e
                | .ok v => stdout.putStr (if v.endsWith "\n" then v else v ++ "\n")
                stdout.flush
              | _ => stderr.putStrLn s!"unknown command {c} (`:help`)"
          else
            -- the line is one command: elaborate it into the session, from the pristine base
            let s' := runFrontend.go line base line.toList.toArray 0 state
            report state.messages.size s' line none
            state := { s' with messages := #[] }
            stdout.flush
            stderr.flush
  return 0

/-- The test driver: `WIZ_TESTS` (when it is a file), else beside this binary (a
checkout's `.lake/build/bin/tests`), else `.lake/build/bin/tests` under the current
directory. -/
def testDriver : IO (Option System.FilePath) := do
  if let some p ← IO.getEnv "WIZ_TESTS" then
    let p := System.FilePath.mk p
    return (if (← p.pathExists) && !(← p.isDir) then some p else none)
  let beside := (← IO.appPath).parent.getD "." / "tests"
  if (← beside.pathExists) && !(← beside.isDir) then return some beside
  let localPath : System.FilePath := ".lake/build/bin/tests"
  return (if (← localPath.pathExists) && !(← localPath.isDir) then some localPath else none)

/-- `wiz test-driver [GROUPS…] [--jobs N] [--list]`: run the test driver with these
arguments (`lake build wiz tests` builds it). A convenience wrapper: the driver is the
runner. (`wiz test FILE` is the single-file form, stage 11ah.) -/
def testDriverCmd (args : List String) : IO UInt32 := do
  let some driver ← testDriver
    | IO.eprintln "wiz test-driver: no test driver: build it with `lake build wiz tests`, or set WIZ_TESTS to its path"
      return 2
  let child ← IO.Process.spawn { cmd := driver.toString, args := args.toArray }
  child.wait

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
  regionCacheOpt.set (args.contains "--region-cache")
  let args := args.filter (· != "--region-cache")
  regionStatsOpt.set (args.contains "--region-stats")
  let args := args.filter (· != "--region-stats")
  lazyProofsOpt.set (!args.contains "--eager-proofs")
  let args := args.filter (· != "--eager-proofs")
  let args ← match takeProofSteps args with
    | .ok (k, t, a) => do proofStepsOpt.set (k.getD Budget.defaultSteps, t); pure a
    | .error e => do IO.eprintln e; return 1
  let args ← match takeInertOpt args with
    | .ok (r, a) => do if let some r := r then inertOpt.set r
                       pure a
    | .error e => do IO.eprintln e; return 1
  let args ← match takeSplitOpt args with
    | .ok (k, a) => do
      if let some k := k then splitOpt.set k
      pure a
    | .error e => do IO.eprintln e; return 1
  let args ← match kernelOpt args with
    | .ok (r, p, a) => do kernelOpts.set (r, p); pure a
    | .error e => do IO.eprintln e; return 1
  -- a `panic!` (a kernel-internal failure) ends a batch command with status 1 instead of
  -- going on with a default value; the language server keeps running
  unless args.head? == some "lsp" do exitOnPanic
  let split ← splitOpt.get
  match args with
  | ["parse", path] => parseCmd path
  | ["check", path] => checkCmd tc path
  | ["build", path, "-o", out] => buildCmd tc path out false (split := split)
  | ["build", path, "-o", out, "--llvm"] => buildCmd tc path out true (split := split)
  | ["build", path, "-o", out, "--lib"] => buildCmd tc path out false true (split := split)
  | ["build", path, "-o", out, "--lib", "--llvm"] | ["build", path, "-o", out, "--llvm", "--lib"] =>
    buildCmd tc path out true true (split := split)
  | ["build", path, "-o", out, "--no-main"] => buildCmd tc path out false false true (split := split)
  | ["build", path, "-o", out, "--no-main", "--llvm"] | ["build", path, "-o", out, "--llvm", "--no-main"] =>
    buildCmd tc path out true false true (split := split)
  | "doc" :: rest => docCmd tc rest
  | ["run", path] => runCmd tc path false (split := split)
  | ["run", path, "--llvm"] => runCmd tc path true (split := split)
  | ["repl"] => replCmd tc false
  | ["repl", "--llvm"] => replCmd tc true
  | "test-driver" :: rest => testDriverCmd rest
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
