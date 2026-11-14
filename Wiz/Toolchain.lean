import Wiz.Smt.Process

/-!
# The toolchain record (stage 23a)

Everything outside Wiz that building needs, passed explicitly instead of read from the
environment: the C compiler and its flags (where GMP and the Boehm collector live),
`llc`, the elaboration cache, and extra module roots. `wiz` fills it from flags, grail
from `grail.wiz`, `grail.local.wiz` and flags. The fields that change generated code
enter the build keys (`Toolchain.id`).
-/

namespace Wiz

/-- (8f) A cross-compilation target: the triple the C compiler produces, its data
layout, how to run its binaries when the host cannot, and the support tier the docs
promise. A target is listed in `BuildTarget.known` only when the C backend has a
compiler for it and `runtime/wiz_abi.h` guards its word width; a target without both is
not advertised. -/
structure BuildTarget where
  /-- the LLVM/`cc --target` spelling (`aarch64-linux-gnu`) -/
  triple : String
  /-- the C compiler that produces this target -/
  cc : String
  /-- the word width of `wiz_val` (32 or 64) -/
  pointerWidth : Nat
  /-- `little` or `big`; part of the build and cache keys -/
  endianness : String := "little"
  /-- the command prefix that runs a target binary (an emulator); empty: run directly -/
  runner : List String := []
  /-- 1: tested on the target; 2: built and exercised under emulation; 3: builds only -/
  tier : Nat := 3
  deriving Repr, Inhabited

namespace BuildTarget

/-- The targets `--target` accepts. Every one has a C compiler and a pointer-width
guard; the docs' tier table is this list (see stage 8f). -/
def known : List BuildTarget :=
  [ { triple := "x86_64-linux-gnu", cc := "cc", pointerWidth := 64, tier := 1 },
    { triple := "aarch64-linux-gnu", cc := "aarch64-linux-gnu-gcc", pointerWidth := 64,
      runner := ["qemu-aarch64", "-L", "/usr/aarch64-linux-gnu"], tier := 2 },
    { triple := "i686-linux-gnu", cc := "i686-linux-gnu-gcc", pointerWidth := 32,
      runner := ["qemu-i386", "-L", "/usr/i686-linux-gnu"], tier := 3 } ]

/-- The target named `s`, if it is one this toolchain advertises. -/
def ofTriple? (s : String) : Option BuildTarget := known.find? (·.triple == s)

/-- The advertised triples, for an error message. -/
def names : String := ", ".intercalate (known.map (·.triple))

/-- The host's triple (an empty `System.Platform.target` falls back to x86-64 Linux). -/
def hostTriple : String :=
  let t := System.Platform.target
  if t.isEmpty then "x86_64-linux-gnu" else t

/-- The tier names the cross-target table in the docs uses. -/
def tierName : Nat → String
  | 1 => "tested on the target"
  | 2 => "built and run under emulation"
  | _ => "builds only"

end BuildTarget

structure Toolchain where
  cc : String := "cc"
  cflags : List String := []
  ldflags : List String := []
  llc : String := "llc"
  /-- libraries a package links with (`-lm`), after `ldflags` -/
  libs : List String := []
  /-- (9f) how to link GMP: `-lgmp`, or for WebAssembly a C file (mini-gmp) -/
  gmp : List String := ["-lgmp"]
  /-- the Boehm collector, for the self-hosted runtime -/
  gcCflags : List String := []
  gcLdflags : List String := []
  /-- the elaboration cache that is also written (none: no writes) -/
  cacheDir : Option System.FilePath := none
  /-- (23c) read-only elaboration caches, searched in order after `cacheDir` and never
  written (a Nix store's `--cache-ro $out/share/wiz/cache`) -/
  readCaches : List System.FilePath := []
  /-- module roots searched after the standard library -/
  searchPath : List System.FilePath := []
  /-- (8f) `--target TRIPLE`: the build target; none is the host -/
  target : Option BuildTarget := none
  /-- `--cc` was given explicitly: `--target` leaves it alone (a bundle's default and a
  target's compiler are both defaults) -/
  ccSet : Bool := false
  /-- (8f) `--runner "CMD ARGS"`: how to run target binaries, overriding the target's
  emulator prefix -/
  runner : List String := []
  /-- (27a) `--trust-native`: `native_refl` may decide equations by running them -/
  trustNative : Bool := false
  /-- (27a) `--native-fuel N`: the interpreter steps one `native_refl` may take (none: the
  default, `NativeRun.defaultFuel`) -/
  nativeFuel : Option Nat := none
  /-- (28b) `--sat-solver CMD` (default `cadical`, or the bundle's), `--solver-timeout MS`
  (default 10000). Flags only: a grail file can't name a program for wiz to run. -/
  satSolver : Option String := none
  solverTimeout : Option Nat := none
  /-- (28a) `--trust-smt`: the `smt` tactic may close goals on an SMT solver's word;
  `--smt-solver CMD` (default `z3`). Flags only. -/
  trustSmt : Bool := false
  smtSolver : Option String := none
  deriving Repr, Inhabited

namespace Toolchain

def words (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

/-- The target's name: the host's triple when none is named. -/
def targetName (t : Toolchain) : String :=
  match t.target with
  | some g => g.triple
  | none => BuildTarget.hostTriple

/-- What namespaces the elaboration cache by target: the triple together with the data
layout the target promises, so two compilers that spell a triple differently (or a
32-bit and a 64-bit target) never share entries. Native and an explicitly named host
triple share the host's namespace. -/
def targetId (t : Toolchain) : UInt64 :=
  match t.target with
  | some g =>
    if g.triple == BuildTarget.hostTriple then
      hash s!"{BuildTarget.hostTriple}/{System.Platform.numBits}/little"
    else hash s!"{g.triple}/{g.pointerWidth}/{g.endianness}"
  | none => hash s!"{BuildTarget.hostTriple}/{System.Platform.numBits}/little"

/-- Is this a target other than the host? (The LLVM backend is not a cross backend.) -/
def isCross (t : Toolchain) : Bool :=
  match t.target with
  | some g => g.triple != BuildTarget.hostTriple
  | none => false

/-- The command that runs a binary built for this toolchain: the target's runner (an
emulator), or the program itself when there is none. -/
def runCommand (t : Toolchain) (exe : System.FilePath) (args : Array String := #[]) :
    String × Array String :=
  let runner := if t.runner.isEmpty then (t.target.map (·.runner)).getD [] else t.runner
  match runner with
  | [] => (exe.toString, args)
  | c :: cs => (c, cs.toArray ++ #[exe.toString] ++ args)

/-- Apply the target's compiler when `--cc` did not name one (a bundle's compiler is a
default too, so `--target` replaces it). -/
def resolveTarget (t : Toolchain) : Toolchain :=
  match t.target with
  | some g => if t.ccSet then t else { t with cc := g.cc }
  | none => t

/-- What identifies the generated code: compilers, flags and the target (not the cache
or roots). -/
def id (t : Toolchain) : UInt64 :=
  hash (toString [t.cc, " ".intercalate t.cflags, " ".intercalate t.ldflags, " ".intercalate t.libs, t.llc, " ".intercalate t.gmp,
    " ".intercalate t.gcCflags, " ".intercalate t.gcLdflags, toString t.targetId])

/-- Set one field by its name (as in `grail.local.wiz` and the flags); `false` if unknown.
Flag lists replace the field's words; `cache-ro` appends to the read-only caches. -/
def set (t : Toolchain) (key value : String) : Option Toolchain :=
  match key with
  | "cc" => some { t with cc := value }
  | "target" =>
    if value == "native" || value == "host" then some { t with target := none }
    else (BuildTarget.ofTriple? value).map fun g => { t with target := some g }
  | "runner" => some { t with runner := words value }
  | "cflags" => some { t with cflags := words value }
  | "ldflags" => some { t with ldflags := words value }
  | "llc" => some { t with llc := value }
  | "libs" => some { t with libs := words value }
  | "gmp" => some { t with gmp := words value }
  | "gc-cflags" => some { t with gcCflags := words value }
  | "gc-ldflags" => some { t with gcLdflags := words value }
  | "cache" => some { t with cacheDir := some (System.FilePath.mk value) }
  | "cache-ro" => some { t with readCaches := t.readCaches ++ [System.FilePath.mk value] }
  | "root" => some { t with searchPath := t.searchPath ++ [System.FilePath.mk value] }
  | "native-fuel" => value.toNat?.map fun n => { t with nativeFuel := some n }
  | _ => none

/-- Take the toolchain flags out of the arguments: `--cc X`, `--target TRIPLE`
(`native`/`host` is the host), `--runner "CMD ARGS"`, `--cflags "…"`, `--ldflags "…"`,
`--libs "…"`, `--gmp "…"`, `--llc X`, `--gc-cflags "…"`, `--gc-ldflags "…"`,
`--cache DIR` (the cache written to), `--cache-ro DIR` (repeatable: a read-only cache,
searched in the order given), `--no-cache` (both: no write cache and no read caches; a
later `--cache` or `--cache-ro` adds one again), `-I DIR`, (27a) `--trust-native`,
`--native-fuel N`, (28b) `--sat-solver CMD`, `--solver-timeout MS`, (28a) `--trust-smt`,
`--smt-solver CMD` (flags only, not settings of a grail file). An unknown target is left
in the arguments, like any unknown flag. -/
partial def parseFlagsCore (t : Toolchain) : List String → Toolchain × List String
  | "--cc" :: c :: rest => parseFlagsCore { t with cc := c, ccSet := true } rest
  | "--no-cache" :: rest => parseFlagsCore { t with cacheDir := none, readCaches := [] } rest
  | "--trust-native" :: rest => parseFlagsCore { t with trustNative := true } rest
  | "--sat-solver" :: cmd :: rest => parseFlagsCore { t with satSolver := some cmd } rest
  | "--trust-smt" :: rest => parseFlagsCore { t with trustSmt := true } rest
  | "--smt-solver" :: cmd :: rest => parseFlagsCore { t with smtSolver := some cmd } rest
  | "--target" :: name :: rest =>
    if name == "native" || name == "host" then parseFlagsCore { t with target := none } rest
    else match BuildTarget.ofTriple? name with
      | some g => parseFlagsCore { t with target := some g } rest
      | none => (t, "--target" :: name :: rest)
  | "--solver-timeout" :: ms :: rest => match ms.toNat? with
    | some n => parseFlagsCore { t with solverTimeout := some n } rest
    | none => let (t, r) := parseFlagsCore t rest; (t, "--solver-timeout" :: ms :: r)
  | "-I" :: dir :: rest => parseFlagsCore { t with searchPath := t.searchPath ++ [System.FilePath.mk dir] } rest
  | flag :: v :: rest =>
    match (if flag.startsWith "--" then t.set (flag.drop 2).toString v else none) with
    | some t' => parseFlagsCore t' rest
    | none => let (t, r) := parseFlagsCore t (v :: rest); (t, flag :: r)
  | [a] => (t, [a])
  | [] => (t, [])

/-- `parseFlagsCore`, then the target's compiler if `--cc` did not name one. -/
def parseFlags (t : Toolchain) (args : List String) : Toolchain × List String :=
  let (t, rest) := parseFlagsCore t args
  (t.resolveTarget, rest)

/-- Flags that give this toolchain (its compilers, flags and caches) to another process.
The read caches are reported in order, one `--cache-ro DIR` each. With no write cache,
`--no-cache` comes first: it clears both, so the read caches have to follow it (a program
that starts from a default cache directory would otherwise keep it). -/
def toFlags (t : Toolchain) : List String :=
  (match t.target with | some g => ["--target", g.triple] | none => []) ++
  ["--cc", t.cc] ++
  (if t.runner.isEmpty then [] else ["--runner", " ".intercalate t.runner]) ++
  ["--cflags", " ".intercalate t.cflags, "--ldflags", " ".intercalate t.ldflags,
   "--libs", " ".intercalate t.libs, "--gmp", " ".intercalate t.gmp, "--llc", t.llc, "--gc-cflags", " ".intercalate t.gcCflags,
   "--gc-ldflags", " ".intercalate t.gcLdflags] ++
  (let reads := t.readCaches.flatMap fun d => ["--cache-ro", d.toString]
   match t.cacheDir with
   | some d => reads ++ ["--cache", d.toString]
   | none => if t.readCaches.isEmpty then ["--no-cache"] else "--no-cache" :: reads) ++
  t.searchPath.flatMap (fun d => ["-I", d.toString]) ++
  (if t.trustNative then ["--trust-native"] else []) ++
  (match t.nativeFuel with | some n => ["--native-fuel", toString n] | none => []) ++
  (match t.satSolver with | some c => ["--sat-solver", c] | none => []) ++
  (match t.solverTimeout with | some n => ["--solver-timeout", toString n] | none => []) ++
  (if t.trustSmt then ["--trust-smt"] else []) ++
  (match t.smtSolver with | some c => ["--smt-solver", c] | none => [])

/-- (28) What the elaborator needs to reach solvers. -/
def smt (t : Toolchain) : Smt.Config :=
  { trust := t.trustSmt, solver := t.smtSolver.getD "z3",
    satSolver := t.satSolver.getD "cadical", timeoutMs := t.solverTimeout.getD 10000,
    cacheDir := t.cacheDir.map toString }

/-- (26f) The C toolchain a release tarball ships, `share/wiz/cc` (scripts/bundle-cc.sh):
clang with a glibc 2.27 sysroot holding static GMP and the Boehm GC, and an `llc` that
runs that clang on IR. Found beside the running binary (`<dir>/.lake/build/bin/wiz` with
`<dir>/cc/bin/cc`, as `toolchainLib` finds `<dir>/lib`). When it is there it gives the
defaults of `cc`, `llc` and `gc-ldflags`; flags, `grail.local.wiz` and tower's settings
still replace any field. (28b) A bundled `cc/bin/cadical` is the default SAT solver.
A checkout and the Nix package have no bundle: `t` unchanged. -/
def withBundled (t : Toolchain) : IO Toolchain := do
  let exe ← IO.appPath
  let root := (((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD "."
  let bin := root / "cc" / "bin"
  unless ← (bin / "cc").pathExists do return t
  -- (28b) and the SAT solver, when the bundle has it (a `--sat-solver` still wins)
  let sat ← if t.satSolver.isNone && (← (bin / "cadical").pathExists) then pure (some (bin / "cadical").toString) else pure t.satSolver
  pure { t with cc := (bin / "cc").toString, llc := (bin / "llc").toString, gcLdflags := ["-lgc", "-lpthread"], satSolver := sat }

/-- `grail config`: one `key value` line per field (`cache-ro` once per read cache, then
the written cache or `(off)`). -/
def render (t : Toolchain) : String :=
  s!"cc {t.cc}\ncflags {" ".intercalate t.cflags}\nldflags {" ".intercalate t.ldflags}\nlibs {" ".intercalate t.libs}\ngmp {" ".intercalate t.gmp}\nllc {t.llc}\n" ++
  s!"gc-cflags {" ".intercalate t.gcCflags}\ngc-ldflags {" ".intercalate t.gcLdflags}\n" ++
  String.join (t.readCaches.map fun d => s!"cache-ro {d}\n") ++
  s!"cache {(t.cacheDir.map toString).getD "(off)"}\nroots {" ".intercalate (t.searchPath.map toString)}\n" ++
  s!"target {t.targetName}\nrunner {" ".intercalate t.runner}\n"

end Toolchain
end Wiz
