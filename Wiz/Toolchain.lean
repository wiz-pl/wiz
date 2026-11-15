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
  /-- (`--region-cache`) serve cached module effects from mmap'ed `.wizr` regions in the
  same cache layers as the text entries; the text entries stay the authority and the
  fallback -/
  regionCache : Bool := false
  /-- module roots searched after the standard library -/
  searchPath : List System.FilePath := []
  /-- `--cache-verify off|warn|strict`: check cache output against its manifest (and
  write manifests to the write cache); default `warn`. It is not in `Toolchain.id` (a
  policy change must not invalidate entries). -/
  cacheVerify : String := "warn"
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

/-- The host target's strong name: the platform triple and pointer width. It is a SHA-256
digest (not the 64-bit `id`) because it names a namespace: two data layouts must never
share cache entries. A future `--target` replaces the triple and width. -/
def targetTag (_t : Toolchain) : String :=
  let triple := System.Platform.target
  Smt.Sha256.hexFramed "wiz-target-id-v1" [if triple.isEmpty then "unknown" else triple,
    toString System.Platform.numBits]

/-- What identifies the generated code, as a SHA-256 digest of the target and the
compilers/flags (not the cache or roots). `id` remains the fast 64-bit index for in-memory
tables and job names; this is the strong namespace for manifests, regions and cache keys. -/
def tag (t : Toolchain) : String :=
  Smt.Sha256.hexFramed "wiz-toolchain-id-v1"
    ([t.targetTag, t.cc, " ".intercalate t.cflags, " ".intercalate t.ldflags,
      " ".intercalate t.libs, t.llc, " ".intercalate t.gmp,
      " ".intercalate t.gcCflags, " ".intercalate t.gcLdflags])

/-- What identifies the generated code: compilers and flags (not the cache or roots).
Fast (64-bit) and for indexing only; `tag` is the SHA-256 namespace used by the cache. -/
def id (t : Toolchain) : UInt64 :=
  hash (toString [t.cc, " ".intercalate t.cflags, " ".intercalate t.ldflags, " ".intercalate t.libs, t.llc, " ".intercalate t.gmp,
    " ".intercalate t.gcCflags, " ".intercalate t.gcLdflags])

/-- Set one field by its name (as in `grail.local.wiz` and the flags); `false` if unknown.
Flag lists replace the field's words; `cache-ro` appends to the read-only caches. -/
def set (t : Toolchain) (key value : String) : Option Toolchain :=
  match key with
  | "cc" => some { t with cc := value }
  | "cflags" => some { t with cflags := words value }
  | "ldflags" => some { t with ldflags := words value }
  | "llc" => some { t with llc := value }
  | "libs" => some { t with libs := words value }
  | "gmp" => some { t with gmp := words value }
  | "gc-cflags" => some { t with gcCflags := words value }
  | "gc-ldflags" => some { t with gcLdflags := words value }
  | "cache" => some { t with cacheDir := some (System.FilePath.mk value) }
  | "cache-ro" => some { t with readCaches := t.readCaches ++ [System.FilePath.mk value] }
  | "cache-verify" => some { t with cacheVerify := value }
  | "region-cache" => some { t with regionCache := value == "true" }
  | "root" => some { t with searchPath := t.searchPath ++ [System.FilePath.mk value] }
  | "native-fuel" => value.toNat?.map fun n => { t with nativeFuel := some n }
  | _ => none

/-- Take the toolchain flags out of the arguments: `--cc X`, `--cflags "…"`,
`--ldflags "…"`, `--libs "…"`, `--gmp "…"`, `--llc X`, `--gc-cflags "…"`,
`--gc-ldflags "…"`, `--cache DIR` (the cache written to), `--cache-ro DIR` (repeatable:
a read-only cache, searched in the order given), `--region-cache` (serve module effects
from `.wizr` regions in those layers; experimental), `--no-cache` (both: no write cache and
no read caches; a later `--cache` or `--cache-ro` adds one again), `-I DIR`, (27a)
`--trust-native`, `--native-fuel N`, (28b) `--sat-solver CMD`, `--solver-timeout MS`,
(28a) `--trust-smt`, `--smt-solver CMD` (flags only, not settings of a grail file). -/
partial def parseFlags (t : Toolchain) : List String → Toolchain × List String
  | "--cache-verify" :: mode :: rest => parseFlags { t with cacheVerify := mode } rest
  | "--no-cache" :: rest => parseFlags { t with cacheDir := none, readCaches := [] } rest
  | "--region-cache" :: rest => parseFlags { t with regionCache := true } rest
  | "--trust-native" :: rest => parseFlags { t with trustNative := true } rest
  | "--sat-solver" :: cmd :: rest => parseFlags { t with satSolver := some cmd } rest
  | "--trust-smt" :: rest => parseFlags { t with trustSmt := true } rest
  | "--smt-solver" :: cmd :: rest => parseFlags { t with smtSolver := some cmd } rest
  | "--solver-timeout" :: ms :: rest => match ms.toNat? with
    | some n => parseFlags { t with solverTimeout := some n } rest
    | none => let (t, r) := parseFlags t rest; (t, "--solver-timeout" :: ms :: r)
  | "-I" :: dir :: rest => parseFlags { t with searchPath := t.searchPath ++ [System.FilePath.mk dir] } rest
  | flag :: v :: rest =>
    if flag.startsWith "--cache-verify=" then
      parseFlags { t with cacheVerify := (flag.drop 15).toString } (v :: rest)
    else
    match (if flag.startsWith "--" then t.set (flag.drop 2).toString v else none) with
    | some t' => parseFlags t' rest
    | none => let (t, r) := parseFlags t (v :: rest); (t, flag :: r)
  | [a] => (t, [a])
  | [] => (t, [])

/-- Flags that give this toolchain (its compilers, flags and caches) to another process.
The read caches are reported in order, one `--cache-ro DIR` each. With no write cache,
`--no-cache` comes first: it clears both, so the read caches have to follow it (a program
that starts from a default cache directory would otherwise keep it). -/
def toFlags (t : Toolchain) : List String :=
  ["--cc", t.cc, "--cflags", " ".intercalate t.cflags, "--ldflags", " ".intercalate t.ldflags,
   "--libs", " ".intercalate t.libs, "--gmp", " ".intercalate t.gmp, "--llc", t.llc, "--gc-cflags", " ".intercalate t.gcCflags,
   "--gc-ldflags", " ".intercalate t.gcLdflags] ++
  (let reads := t.readCaches.flatMap fun d => ["--cache-ro", d.toString]
   match t.cacheDir with
   | some d => reads ++ ["--cache", d.toString]
   | none => if t.readCaches.isEmpty then ["--no-cache"] else "--no-cache" :: reads) ++
  (if t.regionCache then ["--region-cache"] else []) ++
  (if t.cacheVerify == "warn" then [] else ["--cache-verify", t.cacheVerify]) ++
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
  s!"cache {(t.cacheDir.map toString).getD "(off)"}\nregion-cache {t.regionCache}\n" ++
  s!"roots {" ".intercalate (t.searchPath.map toString)}\n" ++
  s!"cache-verify {t.cacheVerify}\n"

end Toolchain
end Wiz
