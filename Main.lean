import Wiz
import Wiz.Version
import Wiz.Doc.Build
import Wiz.Doc.Serve

open Wiz

def usage : String := "usage:
  wiz --version           print the version (and, for a release, its commit)
  wiz parse FILE          print the syntax tree of every command
  wiz check [-I DIR] FILE elaborate and type check (quantities: 0, 1, ω); -I DIR: another
                          module root (a package's src/), before or after FILE
  wiz build FILE -o OUT [--target c|llvm|wasm]  compile the definition `main` to an
                                   executable (C or LLVM) or a WebAssembly module (stage
                                   8f: no IO, Nat/Int, closures, arrays; run it with
                                   web/wasm-host.mjs). `--llvm` and `--wasm` still work.
  wiz build FILE -o OUT [--split N]  compile the program as N C units in parallel
                                   (default 1: one unit; a split build is faster but the
                                   generated program runs somewhat slower, stage 15k)
  wiz build FILE -o OUT --lib      … or the exported functions to an object file, with OUT.h
  wiz build FILE -o OUT --no-main  … or the exported functions, linked without a `main`
                                   (say, a Wasm module: --cc emcc --ldflags --no-entry)
  wiz run FILE [--target c|llvm|wasm]  build and run `main`, printing its value
                                   (`--llvm` and `--wasm` are aliases)
  wiz repl [--llvm] [--prelude M] [--script FILE] [--init CMD]
                                   read one command per line, keeping definitions (`:help`;
                                   a pipe: one command per line, no prompt; `:type EXPR`,
                                   `:load FILE`; `--prelude M` imports M at the start,
                                   `--script` reads FILE, `--init` runs CMD first)
  wiz test-driver [--driver PATH] [GROUPS…] [--jobs N] [--list]
                                   run the test driver (`.lake/build/bin/tests`, or PATH)
  wiz doc [MODULE|FILE|DIR…] -o OUT [--lib] [--source-url URL] [--title T] [--web DIR]
                                  [--serve [--port N] [--lsp PORT]]
                                   documentation: a static site (one page per module,
                                   index, search, reference); --lib: the toolchain's library;
                                   source links are URL + path in its root + #L<line>;
                                   --serve: also serve OUT on 127.0.0.1 (default port
                                   8000); --lsp PORT: the pages ask `wiz lsp --ws PORT`
                                   for live types and docs in a panel
  wiz doc … --reference DIR [--check]
                                   also the reference manual (full signatures, doc comments,
                                   class instances, notation table) into DIR/index.md;
                                   --check: change nothing, exit 1 when DIR/index.md differs
  wiz fmt [FILE|-] [--check] [--width N] [--explain] [--self-test]
                                   reprint a file from its syntax tree (stdin/stdout;
                                   --check: change nothing, exit 1 when it differs;
                                   --self-test: run the built-in fixtures)
  wiz cache prune [--days N] [--dry-run]
                                    remove keyed cache files (.wizc/.wizm/.wizr) older than
                                    N days (default 30) from the write cache; a pruned file is
                                    just a miss, and --cache-ro layers are never touched
  wiz cache verify [--strict]        check every cache entry against its output manifest
                                    (a full scan); exit 1 on a mismatch or missing file
  wiz cache manifest                 rebuild the write cache's manifest.sexpr generation
                                    index from its per-module manifests
  wiz lsp                          a language server on stdin/stdout
  wiz lsp --infoview SOCK          … and for infoviews on the Unix socket SOCK
  wiz lsp --ws [ADDR:]PORT         … and on a WebSocket (127.0.0.1 unless ADDR is given;
                                   both flags may be given; --no-stdio: no editor on stdin)
  wiz lsp … --web DIR              the web infoview's files, served on the WebSocket's port
                                   (default: share/wiz/web, or web/out in a checkout)
options: --cache DIR (the elaboration cache, default ~/.cache/wiz; shared, since it is
content-addressed), --cache-ro DIR (repeatable: a read-only cache, searched in order
after the write cache and never written, as in a Nix package's share/wiz/cache),
--no-cache (both), -I DIR (another module root, after lib/),
--cache-prune DAYS (before the run: from the write cache only, remove keyed
  .wizc/.wizm/.wizr files older than DAYS days; a pruned entry is just a miss, and
  --cache-ro layers are never pruned)
  --region-cache (experimental: also serve cached modules from mmap'ed .wizr regions,
  read from the same caches and written to the write cache), --region-stats (print what
  the regions served, with --region-cache)
--cache-verify off|warn|strict (default warn: check an entry's bytes against its output
  manifest before using it; strict: only manifested entries; --cache-verify=strict works
  too), --cache-verify-stats (print what the manifests verified)
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

/-- `--cache-verify`'s counters (per process). -/
initialize verifyStats : IO.Ref Cache.VerifyCounts ← IO.mkRef {}

/-- `--cache-verify-stats`: print what output manifests verified (to stderr). -/
initialize verifyStatsOpt : IO.Ref Bool ← IO.mkRef false

/-- `--cache-prune DAYS`: remove keyed files older than DAYS days from the write cache
before the run (never from `--cache-ro`; a pruned file is just a miss). -/
initialize cachePruneOpt : IO.Ref (Option Nat) ← IO.mkRef none

/-- Take `--cache-prune DAYS` out of the arguments (at least one day: a shorter age would
delete the files this run is about to use). -/
def takeCachePrune : List String → Except String (Option Nat × List String)
  | "--cache-prune" :: n :: rest => do
    let some k := n.toNat? | throw s!"--cache-prune needs a number of days, not {n}"
    if k == 0 then throw "--cache-prune needs at least one day"
    let (_, rest) ← takeCachePrune rest
    return (some k, rest)
  | a :: rest => do
    let (k, rest) ← takeCachePrune rest
    return (k, a :: rest)
  | [] => return (none, [])

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
frontend needs (the loader, the C headers, the `link_c` files, `include_str`). -/
def initStateOf (tc : Toolchain) (lib : Std.HashMap Name String) (headers : Std.HashMap String String)
    (cSources : Option (String → String → Option String))
    (includes : Option (String → String → Except String String)) (own : List Name)
    (messages : Array Msg := #[]) : IO (CommandState ZeroOneMany) := do
  let (regularity, predicativeProp) ← kernelOpts.get
  let lazyProofs ← lazyProofsOpt.get
  let inertReg ← inertOpt.get
  let (proofSteps, traceProofSteps) ← proofStepsOpt.get
  let unboxStructs ← unboxOpt.get
  let init : CommandState ZeroOneMany :=
    { loader := (lib[·]?), cHeaders := (headers[·]?), cSources, includes,
      messages,
      globals := { regularity, predicativeProp, lazyProofs, inertReg, unboxStructs, proofSteps, traceProofSteps,
                   strictPrivacy := ← strictPrivacyOpt.get, pp := { useNotation := !(← ppAllOpt.get) } },
      trustedModule := own.contains, trustNative := tc.trustNative,
      nativeFuel := tc.nativeFuel.getD NativeRun.defaultFuel, smt := ← tc.smt.resolve }
  pure init

/-- The initial state the frontend runs from: the module loader (every module the file can
reach, `import A.B` is `A/B.wiz` under a root, read up front: the frontend is pure), the
C headers, `link_c` sources and `include_str` files, and the kernel/printing options. -/
def initState (tc : Toolchain) (path : String) (input : String) :
    IO (CommandState ZeroOneMany × Std.HashMap String String) := do
  let roots ← moduleRoots tc
  let closure ← Module.loadClosure roots input
  let lib : Std.HashMap Name String := closure.fold (fun m n (_, src) => m.insert n src) {}
  -- the C headers of the file and of the modules it imports
  let headers ← Build.preprocessHeaders tc (String.join (input :: lib.values))
  -- (9f) the `link_c` files, each relative to its own file
  let sources ← Module.cSourceTable ((System.FilePath.mk path).parent.getD ".") input closure
  -- (include-str) the `include_str` files, each relative to its own file
  let includes ← Module.includeTable ((System.FilePath.mk path).parent.getD ".") input closure
  -- `builtin` registrations are trusted only in the toolchain's own library
  let own := Module.fromFirstRoot roots closure
  -- a file that would replace one of them is ignored: say so (loudly: it may be meant
  -- to stand in for the toolchain's module, `builtin`s and all)
  let shadow := (← Module.shadowed roots closure).map fun (n, p) =>
    ({ info := {}, severity := .warning,
       text := s!"{p} is ignored: module {n} is the toolchain's own ({roots.head!}), which a module root cannot replace" } : Msg)
  let init ← initStateOf tc lib headers (some (Module.cSourceResolver sources))
    (some (Module.includeResolver includes)) own shadow.toArray
  pure (init, headers)

/-- Elaborate a file, through the toolchain's cache (if any). -/
def elaborate (tc : Toolchain) (path : String) (input : String) : IO (CommandState ZeroOneMany) := do
  let (init, headers) ← initState tc path input
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
    let key₀Tag := Smt.Sha256.hexFramed "wiz-cache/root-headers-v1"
      (headers.toList.flatMap fun (n, t) => [n, t])
    let region ← if ← regionCacheOpt.get then
        pure (some ({ rig := RigTag.tag (R := ZeroOneMany), stats := some regionStats } :
          Cache.RegionOptions))
      else pure none
    let verify := (Cache.VerifyMode.ofString? tc.cacheVerify).getD .warn
    pure (← Cache.elaborateCached tc.cacheDir tc.readCaches input init key₀ (region := region)
      (verify := verify) (rig := RigTag.tag (R := ZeroOneMany))
      (stats := if verify == .off then none else some verifyStats)
      (strongToolchain := tc.tag) (targetTag := tc.targetTag) (rootTag := key₀Tag)).1
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
  /-- (11s) serve the generated site on the loopback -/
  serve : Bool := false
  port : Option Nat := none
  /-- the port of the language server the pages ask (`wiz lsp --ws PORT`) -/
  lsp : Option Nat := none
  reference : Option String := none
  check : Bool := false
  inputs : List String := []

def docArgs (a : DocArgs) : List String → Except String DocArgs
  | [] => pure { a with inputs := a.inputs.reverse }
  | "-o" :: o :: rest => docArgs { a with out := some o } rest
  | "--lib" :: rest => docArgs { a with lib := true } rest
  | "--source-url" :: u :: rest => docArgs { a with sourceUrl := some u } rest
  | "--title" :: t :: rest => docArgs { a with title := some t } rest
  | "--web" :: w :: rest => docArgs { a with web := some w } rest
  | "--serve" :: rest => docArgs { a with serve := true } rest
  | "--port" :: n :: rest => do
    let some p := n.toNat? | throw s!"wiz doc: --port needs a number, not {n}"
    if p ≥ 65536 then throw s!"wiz doc: --port must be below 65536, not {n}"
    docArgs { a with port := some p } rest
  | "--lsp" :: n :: rest => do
    let some p := n.toNat? | throw s!"wiz doc: --lsp needs a port number, not {n}"
    if p ≥ 65536 then throw s!"wiz doc: --lsp port must be below 65536, not {n}"
    docArgs { a with lsp := some p } rest
  | "--reference" :: d :: rest => docArgs { a with reference := some d } rest
  | "--check" :: rest => docArgs { a with check := true } rest
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
  if !a.serve && (a.port.isSome || a.lsp.isSome) then
    IO.eprintln "wiz doc: --port and --lsp need --serve"; return 2
  if a.check && a.reference.isNone then
    IO.eprintln "wiz doc: --check needs --reference DIR"; return 2
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
  let assets : List System.FilePath :=
    (web.toList ++ [base / "web", base / "share" / "wiz" / "web"]).eraseDups
  -- (the site keeps its title with --reference; the manual has its own)
  let o : Doc.Options := { out := out, sourceUrl := a.sourceUrl, title := a.title.getD "Wiz documentation", web := web, assets := assets, serve := a.serve, lsp := a.lsp, reference := a.reference.map System.FilePath.mk, check := a.check, referenceTitle := a.title.getD "Wiz standard library reference" }
  let r ← Doc.run (fun m => elaborate tc "<doc>" s!"import {m}\n") mods o
  IO.println s!"wiz doc: {r.pages} modules, {out}/index.html"
  for f in r.written do IO.println s!"wiz doc: wrote {f}"
  if web.isNone then IO.println "wiz doc: no Wasm module (web/build.sh): the pages are plain HTML"
  if !r.stale.isEmpty then
    for f in r.stale do
      IO.eprintln s!"wiz doc --check: {f} is out of date (regenerate with `wiz doc --lib --reference {a.reference.getD ""}`)"
    return 1
  if a.check then IO.println s!"wiz doc --check: {a.reference.getD ""}/index.md is up to date"
  unless a.serve do return 0
  -- (11s) serve the tree; the module sources go with it, for the live client to open
  let site : Doc.Serve.Site :=
    { root := System.FilePath.mk out,
      sources := mods.foldl (fun m x => m.insert x.name x.src) (∅ : Std.HashMap String String) }
  let port : UInt16 := (a.port.getD 8000).toUInt16
  let (fd, p) ← try Doc.Serve.listen site port catch e => do
    IO.eprintln s!"wiz doc: cannot listen on 127.0.0.1:{port}: {e}"
    return 1
  IO.println s!"wiz doc: serving http://127.0.0.1:{p}/ (Ctrl-C to stop)"
  match a.lsp with
  | some lp => IO.println s!"wiz doc: the live panel asks wiz lsp --ws {lp}; start it with `wiz lsp --ws {lp} --no-stdio`"
  | none => IO.println "wiz doc: static pages; --lsp PORT shows live types and docs from `wiz lsp --ws PORT`"
  Doc.Serve.acceptLoop fd site
  pure 0

/-- (11aa) `wiz fmt`'s options: the file (or stdin), `--check`, `--width`. -/
structure FmtArgs where
  input : Option String := none
  check : Bool := false
  width : Nat := 100
  explain : Bool := false
  selfTest : Bool := false

def fmtArgs (a : FmtArgs) : List String → Except String FmtArgs
  | [] => pure a
  | "--check" :: rest => fmtArgs { a with check := true } rest
  | "--explain" :: rest => fmtArgs { a with explain := true } rest
  | "--self-test" :: rest => fmtArgs { a with selfTest := true } rest
  | "--width" :: n :: rest => do
    let some w := n.toNat? | throw s!"wiz fmt: --width needs a number, not {n}"
    fmtArgs { a with width := w } rest
  | x :: rest =>
    if x.startsWith "-" && x != "-" then throw s!"wiz fmt: unknown option {x}"
    else match a.input with
      | some _ => throw "wiz fmt: one file at a time (and `-` for stdin)"
      | none => fmtArgs { a with input := some x } rest

/-- (11aa) `wiz fmt`: reprint a file from its syntax tree (stdin/stdout). -/
def fmtCmd (tc : Toolchain) (args : List String) : IO UInt32 := do
  let a ← match fmtArgs {} args with
    | .ok a => pure a
    | .error e => do IO.eprintln e; return 2
  if a.selfTest then
    let bad := Fmt.selfTest
    for b in bad do IO.eprintln s!"wiz fmt --self-test: {b}"
    if bad.isEmpty then
      IO.println s!"wiz fmt --self-test: {Fmt.selfTestFixtures.size} fixtures ok"
      pure 0
    else pure 1
  else
    let path := a.input.getD "-"
    let input ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
    let (init, _) ← initState tc (if path == "-" then "<stdin>" else path) input
    let r := Fmt.run init input { width := a.width, explain := a.explain }
    unless r.errors.isEmpty do
      for e in r.errors do IO.eprintln s!"{path}:{e}"
      IO.eprintln s!"wiz fmt: {path}: not formatted (the file did not parse)"
      return 2
    for m in r.refused do IO.eprintln s!"{path}:{m}"
    if a.check then
      if r.text == input then pure 0
      else
        IO.eprintln s!"wiz fmt: {path}: not formatted"
        pure 1
    else
      IO.print r.text
      pure (if r.refused.isEmpty then 0 else 1)
/-- `wiz cache prune [--days N] [--dry-run]`: remove keyed files older than N days (default
30) from the write cache. Only the write cache: read-only layers are never touched. -/
def cachePruneCmd (tc : Toolchain) (args : List String) : IO UInt32 := do
  let rec parse (days : Nat) (dry : Bool) : List String → Except String (Nat × Bool)
    | [] => pure (days, dry)
    | "--days" :: n :: rest => do
      let some k := n.toNat? | throw s!"--days needs a number of days, not {n}"
      if k == 0 then throw "--days must be at least 1"
      parse k dry rest
    | "--dry-run" :: rest => parse days true rest
    | a :: _ => throw s!"cache prune: unknown argument {a}"
  let (days, dry) ← match parse 30 false args with
    | .ok r => pure r
    | .error e => do IO.eprintln e; return 2
  unless tc.readCaches.isEmpty do
    IO.eprintln "cache prune: --cache-ro layers are read-only and never pruned"
  match tc.cacheDir with
  | none => do IO.eprintln "cache prune: no write cache (--cache DIR)"; pure 1
  | some dir => do IO.println (← Cache.pruneSummary dir days dry); pure 0

/-- `wiz cache verify`: check every manifest in each cache layer against the bytes beside
it (a full scan; normal runs verify only what they read). Exit 1 on a mismatch or a missing
file, and in `strict`/`--strict` also on an unmanifested keyed file. -/
def cacheVerifyCmd (tc : Toolchain) (args : List String) : IO UInt32 := do
  let strict := tc.cacheVerify == "strict" || args.contains "--strict" || !tc.readCaches.isEmpty
  for a in args do
    unless a == "--strict" do
      IO.eprintln s!"cache verify: unknown argument {a}"
      return 2
  let dirs := tc.cacheDir.toList ++ tc.readCaches
  if dirs.isEmpty then
    IO.eprintln "cache verify: no cache (--cache DIR, --cache-ro DIR)"
    return 2
  let mut bad := 0
  for dir in dirs do
    let c ← Cache.verifyLayer dir
    IO.println (s!"cache verify: {dir}: {c.modules} modules, {c.entries} entries, {c.regions} regions, " ++
      s!"{c.mismatches} mismatched, {c.missing} missing, {c.expired} expired, {c.unmanifested} unmanifested")
    if c.mismatches + c.missing + c.expired > 0 || (strict && c.unmanifested > 0) then bad := bad + 1
  pure (if bad == 0 then 0 else 1)

/-- `wiz cache manifest`: rebuild (or, for a read-only layer, report) the generation index
`manifest.sexpr` from a layer's per-module manifests. -/
def cacheManifestCmd (tc : Toolchain) (args : List String) : IO UInt32 := do
  let rec parse (days : Option Nat) : List String → Except String (Option Nat)
    | [] => pure days
    | "--valid-days" :: n :: rest => do
      let some k := n.toNat? | throw s!"--valid-days needs a number, not {n}"
      if k == 0 then throw "--valid-days must be at least 1"
      parse (some k) rest
    | a :: _ => throw s!"cache manifest: unknown argument {a}"
  let days ← match parse none args with
    | .ok d => pure d
    | .error e => do IO.eprintln e; return 2
  let validUntil ← match days with
    | some d => do pure ((← Cache.unixNow) + d * 86400)
    | none => pure 0
  let dirs := tc.cacheDir.toList ++ tc.readCaches
  if dirs.isEmpty then
    IO.eprintln "cache manifest: no cache (--cache DIR, --cache-ro DIR)"
    return 2
  for dir in dirs do
    let write := some dir.toString == tc.cacheDir.map (·.toString)
    let (mods, entries) ← Cache.sealLayer dir write validUntil
    let what := if write then "generation written" else "read-only"
    IO.println s!"cache manifest: {dir}: {mods} modules, {entries} entries ({what})"
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
  if ← verifyStatsOpt.get then
    let c ← verifyStats.get
    IO.eprintln (s!"cache verify: {c.manifests} manifests, {c.hits} entries, {c.regions} regions, " ++
      s!"{c.mismatches} mismatches, {c.unverified} unverified")
  pure (if s.messages.any (·.severity == .error) then 1 else 0)

def elabFile (tc : Toolchain) (path : String) : IO (Option (CommandState ZeroOneMany)) := do
  let input ← IO.FS.readFile path
  let s ← elaborate tc path input
  for m in s.messages do
    if m.severity == .error then IO.eprintln s!"{path}:{m.render input}"
  pure (if s.messages.any (·.severity == .error) then none else some s)

/-- The backend names `wiz build --target` accepts. -/
def targets : List String := ["c", "llvm", "wasm"]

/-- Take `--target NAME`, `--llvm` and `--wasm` out of the arguments; return the selected
backend and the rest. A flag and a conflicting `--target` are an error, as is two
different targets. -/
def takeTarget : List String → Except String (Option String × List String)
  | [] => pure (none, [])
  | "--target" :: [] => throw "--target needs c, llvm or wasm"
  | "--target" :: t :: rest => do
    unless targets.contains t do throw s!"unknown target {t} (choose c, llvm or wasm)"
    let (other, rest) ← takeTarget rest
    match other with
    | some u => if u != t then throw s!"two targets: {t} and {u}" else pure (some t, rest)
    | none => pure (some t, rest)
  | "--llvm" :: rest => do
    let (other, rest) ← takeTarget rest
    match other with
    | some u => if u != "llvm" then throw s!"two targets: llvm and {u}" else pure (some "llvm", rest)
    | none => pure (some "llvm", rest)
  | "--wasm" :: rest => do
    let (other, rest) ← takeTarget rest
    match other with
    | some u => if u != "wasm" then throw s!"two targets: wasm and {u}" else pure (some "wasm", rest)
    | none => pure (some "wasm", rest)
  | a :: rest => do
    let (t, rest) ← takeTarget rest
    pure (t, a :: rest)

def buildCmd (tc : Toolchain) (path out : String) (target : String) (lib : Bool := false)
    (noMain : Bool := false) (split : Nat := 0) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  match ← Build.build tc s "main" out (target == "llvm") lib noMain split (target == "wasm") with
  | .error e => IO.eprintln e; pure 1
  | .ok _ => pure 0

def runCmd (tc : Toolchain) (path : String) (target : String) (split : Nat := 0) : IO UInt32 := do
  let some s ← elabFile tc path | pure 1
  let dir ← IO.FS.createTempDir
  let r ← if target == "wasm" then Build.runWasmGlobal s "main" dir
    else Build.runGlobal tc s "main" dir (target == "llvm") (split := split)
  match r with
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
  let includes ← Module.includeTable "." "" all
  initStateOf tc lib headers (some (Module.cSourceResolver sources))
    (some (Module.includeResolver includes)) (Module.fromFirstRoot roots all)

/-- `wiz repl [--llvm] [--prelude MODULE]`: read one command per line from stdin,
elaborate it against the accumulated `CommandState` (definitions persist), print its
messages and go on after an error. `:quit`/EOF exit, `:reset` forgets every definition,
`:help` lists the commands; `:type EXPR` prints a type and `:load FILE` elaborates a file
into the session. With `--llvm`, `:run NAME` builds through LLVM instead of C.

`--prelude`/`-p` (repeatable, comma-separated) imports its modules after the Prelude and
before the first prompt: a tool can ship a prelude module and be "the ordinary REPL with
an extra prelude" (`scry repl` is `wiz repl --prelude Scry.Repl`). A module that does not
resolve is reported at startup (exit 2), not on the first input.

The base state stays pristine, so an `import` is checked in isolation as in a file, then
elaborated into the session's state. A pipe has one command per line and no prompt. -/
def replCmd (tc : Toolchain) (llvm : Bool) (preludes : List String := [])
    (script : Option String := none) (init : List String := []) : IO UInt32 := do
  let base ← replInit tc
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let tty ← stdin.isTty
  -- a session starts with the Prelude, as a file's first line would import it
  let preloaded := match base.loader "Prelude" with
    | some _ => runFrontend.go "import Prelude" base "import Prelude".toList.toArray 0 base
    | none => base
  -- the `--prelude` modules, on top of the Prelude, before the first prompt: an implicit
  -- `import` each, in the order given (a missing one is a startup error)
  let extra := preludes.flatMap (fun s => (s.splitOn ",").map (fun m => m.trimAscii.toString))
    |>.filter (!·.isEmpty)
  let mut preloaded := preloaded
  let mut preludeErrors := 0
  for m in extra do
    let text := s!"import {m}"
    let s' := runFrontend.go text base text.toList.toArray 0 preloaded
    let msgs := s'.messages.extract preloaded.messages.size s'.messages.size
    for msg in msgs do
      let line := msg.render text
      if msg.severity == .error then
        preludeErrors := preludeErrors + 1
        stderr.putStrLn line
      else stdout.putStrLn line
    preloaded := { s' with messages := #[] }
  if preludeErrors > 0 then
    let names := ", ".intercalate extra
    stderr.putStrLn s!"wiz repl: --prelude {names}: not imported (see the errors above)"
    return 2
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
  -- one input line: `none` when it ends the session (`:quit`), else the next state
  let process (state : CommandState ZeroOneMany) (raw : String) :
      IO (Option (CommandState ZeroOneMany)) := do
    let line := raw.trimAscii.toString
    if line.isEmpty then return some state
    match line with
    | ":quit" | ":q" => return none
    | ":help" | ":h" | ":?" => stdout.putStrLn help; stdout.flush; return some state
    | ":reset" => stdout.putStrLn "reset"; stdout.flush; return some preloaded
    | c =>
      if c.startsWith ":" then
        if c == ":type" then
          stderr.putStrLn "usage: :type EXPR"
          return some state
        else if c.startsWith ":type " then
          let text := s!"#check {(c.drop 6).trimAscii.toString}"
          let s' := runFrontend.go text base text.toList.toArray 0 state
          report state.messages.size s' text none
          return some { s' with messages := #[] }
        else if c == ":load" then
          stderr.putStrLn "usage: :load FILE"
          return some state
        else if c.startsWith ":load " then
          let path := (c.drop 6).trimAscii.toString
          let text? ← try
            pure (some (← IO.FS.readFile path))
          catch e =>
            stderr.putStrLn s!"cannot read {path}: {e}"
            pure none
          match text? with
          | none => return some state
          | some text =>
            let s' := runFrontend.go text base text.toList.toArray 0 state
            report state.messages.size s' text (some path)
            return some { s' with messages := #[] }
        else
          match c.splitOn " " with
          | [":run", name] =>
            let dir ← IO.FS.createTempDir
            match ← Build.runGlobal tc state name dir llvm with
            | .error e => stderr.putStrLn e
            | .ok v => stdout.putStr (if v.endsWith "\n" then v else v ++ "\n")
            stdout.flush
            return some state
          | _ => stderr.putStrLn s!"unknown command {c} (`:help`)"; return some state
      else
        -- the line is one command: elaborate it into the session, from the pristine base
        let s' := runFrontend.go line base line.toList.toArray 0 state
        report state.messages.size s' line none
        stdout.flush
        stderr.flush
        return some { s' with messages := #[] }
  let mut state := preloaded
  let mut reading := true
  -- `--init CMD`s first, then `--script FILE`'s lines (instead of stdin)
  for c in init do
    if reading then
      match ← process state c with
      | some s => state := s
      | none => reading := false
  if let some f := script then
    let text? ← try
      pure (some (← IO.FS.readFile f))
    catch e =>
      stderr.putStrLn s!"wiz repl: cannot read {f}: {e}"
      pure none
    let some text := text? | return 2
    for raw in text.splitOn "\n" do
      if reading then
        match ← process state raw with
        | some s => state := s
        | none => reading := false
    return 0
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
      match ← process state raw with
      | some s => state := s
      | none => reading := false
  return 0

/-- `--prelude MODULE` / `-p MODULE` (`--prelude=MODULE` too; repeatable and
comma-separated): the modules `wiz repl` imports after the Prelude. Returns them in the
order given, with the rest of the arguments. -/
def takePrelude : List String → Except String (List String × List String)
  | [] => pure ([], [])
  | "--prelude" :: [] | "-p" :: [] => throw "--prelude needs a module name"
  | "--prelude" :: m :: rest | "-p" :: m :: rest => do
    let (ps, rest) ← takePrelude rest
    pure (m :: ps, rest)
  | a :: rest => do
    let (ps, rest) ← takePrelude rest
    if a.startsWith "--prelude=" then pure ((a.drop 10).toString :: ps, rest)
    else if a.startsWith "-p" && a.length > 2 && !(a.startsWith "--") then
      pure ((a.drop 2).toString :: ps, rest)
    else pure (ps, a :: rest)

/-- `--script FILE` (the commands, one per line, from FILE instead of stdin) and
`--init CMD` (repeatable: run before the first input) for `wiz repl`, taken out of the
arguments. -/
def takeReplScript : List String → Except String (Option String × List String × List String)
  | [] => pure (none, [], [])
  | "--script" :: [] => throw "--script needs a file"
  | "--init" :: [] => throw "--init needs a command"
  | "--script" :: f :: rest => do
    let (_, init, rest) ← takeReplScript rest
    pure (some f, init, rest)
  | "--init" :: c :: rest => do
    let (script, init, rest) ← takeReplScript rest
    pure (script, c :: init, rest)
  | a :: rest => do
    let (script, init, rest) ← takeReplScript rest
    pure (script, init, a :: rest)

/-- The test driver: the `--driver PATH` flag (when it is a file), else beside this
binary (a checkout's `.lake/build/bin/tests`), else `.lake/build/bin/tests` under the
current directory. A flag, not an environment variable: `wiz` reads none (23a). -/
def testDriver (explicit : Option System.FilePath) : IO (Option System.FilePath) := do
  if let some p := explicit then
    return (if (← p.pathExists) && !(← p.isDir) then some p else none)
  let beside := (← IO.appPath).parent.getD "." / "tests"
  if (← beside.pathExists) && !(← beside.isDir) then return some beside
  let localPath : System.FilePath := ".lake/build/bin/tests"
  return (if (← localPath.pathExists) && !(← localPath.isDir) then some localPath else none)

/-- `--driver PATH` / `--driver=PATH`, taken out of the arguments (the rest go to the
driver unchanged). -/
def takeDriver : List String → Option System.FilePath × List String
  | [] => (none, [])
  | "--driver" :: p :: rest => let (_, r) := takeDriver rest; (some (System.FilePath.mk p), r)
  | a :: rest =>
    let (d, r) := takeDriver rest
    if a.startsWith "--driver=" then (some (System.FilePath.mk (a.drop 9).toString), r) else (d, a :: r)

/-- `wiz test-driver [--driver PATH] [GROUPS…] [--jobs N] [--list]`: run the test driver
with the other arguments (`lake build wiz tests` builds it). A convenience wrapper: the
driver is the runner. (`wiz test FILE` is the single-file form, stage 11ah.) -/
def testDriverCmd (args : List String) : IO UInt32 := do
  let (explicit, args) := takeDriver args
  let some driver ← testDriver explicit
    | IO.eprintln "wiz test-driver: no test driver: build it with `lake build wiz tests`, or pass --driver PATH"
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
  regionCacheOpt.set tc.regionCache
  if args.contains "--strict-privacy" then strictPrivacyOpt.set true
  let args := args.filter (· != "--strict-privacy")
  if args.contains "--pp-all" then ppAllOpt.set true
  let args := args.filter (· != "--pp-all")
  if args.contains "--unbox-structs" then unboxOpt.set true
  let args := args.filter (· != "--unbox-structs")
  regionStatsOpt.set (args.contains "--region-stats")
  let args := args.filter (· != "--region-stats")
  verifyStatsOpt.set (args.contains "--cache-verify-stats")
  let args := args.filter (· != "--cache-verify-stats")
  if (Cache.VerifyMode.ofString? tc.cacheVerify).isNone then
    IO.eprintln s!"--cache-verify: unknown mode {tc.cacheVerify} (off, warn, strict)"
    return 2
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
  let args ← match takeCachePrune args with
    | .ok (k, a) => do
      if let some k := k then cachePruneOpt.set (some k)
      pure a
    | .error e => do IO.eprintln e; return 1
  -- a `panic!` (a kernel-internal failure) ends a batch command with status 1 instead of
  -- going on with a default value; the language server keeps running
  unless args.head? == some "lsp" do exitOnPanic
  -- (`--cache-prune`: before the run, so this process has not mapped a region from the
  -- files it deletes; a pruned entry is just a miss)
  if let some days ← cachePruneOpt.get then
    if let some dir := tc.cacheDir then IO.eprintln (← Cache.pruneSummary dir days)
  let split ← splitOpt.get
  let (target?, args) ← match takeTarget args with
    | .ok r => pure r
    | .error e => do IO.eprintln e; return 1
  let target := target?.getD "c"
  match args with
  | ["parse", path] => parseCmd path
  | "cache" :: "prune" :: rest => cachePruneCmd tc rest
  | "cache" :: "verify" :: rest => cacheVerifyCmd tc rest
  | "cache" :: "manifest" :: rest => cacheManifestCmd tc rest
  | ["check", path] => checkCmd tc path
  | ["build", path, "-o", out] => buildCmd tc path out target (split := split)
  | ["build", path, "-o", out, "--lib"] => buildCmd tc path out target true (split := split)
  | ["build", path, "-o", out, "--no-main"] =>
    buildCmd tc path out target (noMain := true) (split := split)
  | "doc" :: rest => docCmd tc rest
  | "fmt" :: rest => fmtCmd tc rest
  | ["run", path] => runCmd tc path target (split := split)
  -- `--llvm`/`--target llvm` are taken out above (`takeTarget`), so the REPL is LLVM
  -- when the selected target is; there is no wasm REPL (no `:run` through that backend)
  | "repl" :: rest => do
    if target == "wasm" then
      IO.eprintln "wiz repl: targets are c and llvm (not wasm)"
      pure 2
    else match takePrelude rest with
      | .error e => IO.eprintln e; pure 2
      | .ok (preludes, rest) => match takeReplScript rest with
        | .error e => IO.eprintln e; pure 2
        | .ok (script, init, []) => replCmd tc (target == "llvm") preludes script init
        | .ok (_, _, a :: _) =>
          IO.eprintln s!"wiz repl: unknown argument {a}"
          pure 2
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
