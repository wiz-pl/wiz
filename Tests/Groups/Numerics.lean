import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# Numerics and solver trust: the host-side recommendations (R2, R4, R6)

`wiz-notes/sota-numerics.md` §5. This group owns the parts that are not the solver
caches (those are the `sat`/`smt` groups in `Tests/Smt.lean`):

* **R2 — GMP identity.** `flake.nix`'s `gmpPin`, `scripts/bundle-cc.sources` (the
  release's bundled source) and `docs/release/gmp-pin.json` are three records of one
  bignum. A disagreement fails with all three named; the flake's own assert names both
  hashes at `nix eval` time. Lean admits GMP into the kernel TCB, so this is the
  *identity* half of the determinism work, not a version comment.
* **R4 — trust boundaries.** A mechanical scan, along with the ledger-backed checks in
  the `native` group: `sat_decide`/`bv_decide` are proof-carrying and allowed;
  `smt`/`native_refl` are per-use axioms and are refused in `lib/`. The audit and its
  findings are `docs/numerics-trust.md`.
* **R6 — `Float64.toString`.** Ryu's shortest round-trip text (not `%.17g`), with the
  exact strings pinned for the boundary values (subnormals, 0.1, 1e308, -0.0, NaN,
  inf), a C round-trip check over random bit patterns, and a build-path scan that
  refuses fast-math flags while requiring `-ffp-contract=off`.

R3 (the SMT range side condition) and R5 (proofs, not verdicts, in the cache) live in
`Tests/Smt.lean` next to the tactics they exercise. R7 (a certificate-producing
`omega`) is a plan only: `docs/numerics-trust.md` §7.
-/

/-- The text between the first `before` and the next `after` (`none` if either is
missing or the order is wrong). -/
def between? (s before after : String) : Option String :=
  match s.splitOn before with
  | _ :: rest => match rest.headD "" |>.splitOn after with
    | x :: _ => some x
    | [] => none
  | [] => none

/-- The first line of `src` that starts with `prefix`. -/
def lineStartingWith? (src prefix : String) : Option String :=
  (src.splitOn "\n").find? (·.startsWith prefix)

/-- `flake.nix`'s GMP pin: its version, nixpkgs' source hash and the release's
(`sha256-…` SRI, as `scripts/bundle-cc.sources` pins it). -/
def flakeGmpPin : IO (String × String × String) := do
  let src ← IO.FS.readFile "flake.nix"
  let some block := between? src "gmpPin = {" "};"
    | throw (IO.userError "flake.nix: no `gmpPin = { … };` block (R2)")
  let some version := between? block "version = \"" "\""
    | throw (IO.userError "flake.nix: gmpPin has no `version = \"…\"`")
  let some nixHash := between? block "nixSrcHash = \"" "\""
    | throw (IO.userError "flake.nix: gmpPin has no `nixSrcHash = \"…\"`")
  let some releaseHash := between? block "releaseSrcHash = \"" "\""
    | throw (IO.userError "flake.nix: gmpPin has no `releaseSrcHash = \"…\"`")
  pure (version, nixHash, releaseHash)

/-- The GMP line of the release's bundled sources: `gmp-6.3.0.tar.xz <sha256> <url>`. -/
def bundleGmpPin : IO (String × String) := do
  let src ← IO.FS.readFile "scripts/bundle-cc.sources"
  let some line := lineStartingWith? src "gmp-"
    | throw (IO.userError "scripts/bundle-cc.sources: no gmp-… line")
  match (line.splitOn " ").filter (· ≠ "") with
  | file :: hash :: _ =>
    let version := ((file.drop 4).toString.splitOn ".tar").headD file
    pure (version, hash)
  | _ => throw (IO.userError s!"scripts/bundle-cc.sources: malformed GMP line `{line}`")

/-- The checked-in attestation record: version, release archive hash, nix archive hash. -/
def recordGmpPin : IO (String × String × String) := do
  let src ← IO.FS.readFile "docs/release/gmp-pin.json"
  let some version := between? src "\"version\": \"" "\""
    | throw (IO.userError "docs/release/gmp-pin.json: no version")
  let some releaseHash := between? src "\"releaseSrcSha256\": \"" "\""
    | throw (IO.userError "docs/release/gmp-pin.json: no releaseSrcSha256")
  let some nixHash := between? src "\"nixSrcSha256\": \"" "\""
    | throw (IO.userError "docs/release/gmp-pin.json: no nixSrcSha256")
  pure (version, releaseHash, nixHash)

/-- Comment lines are not build flags: `--`, `//`, `#`, `/* …`, ` * …`. -/
def codeLines (src : String) : List String :=
  (src.splitOn "\n").filter fun l =>
    let t := l.trimAscii.toString
    !(t.startsWith "--" || t.startsWith "//" || t.startsWith "/*" ||
      t.startsWith "*" || t.startsWith "#")

/-- Every file that can put a flag in front of the C compiler. -/
def buildPathFiles : List String :=
  [ "Wiz/Compiler/Build.lean", "Wiz/Toolchain.lean", "flake.nix",
    "runtime/wiz_rt.h", "runtime/rt_data.inc", "runtime/rt_num.inc",
    "scripts/bundle-cc.sh", "scripts/test-runtime.sh", "scripts/release-tarball.sh",
    "web/build.sh" ]

/-- Every `.wiz` file under `dir`. -/
partial def wizFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← wizFiles e.path)
    else if e.path.extension == some "wiz" then out := e.path :: out
  pure out

/-- The first `cc` on `PATH`. -/
partial def findCC (dirs : List String) : IO (Option String) := do
  match dirs with
  | [] => pure none
  | d :: rest =>
    if d.isEmpty then findCC rest else do
      let p := System.FilePath.mk d / "cc"
      if ← p.pathExists then pure (some p.toString) else findCC rest

/-- A C source that round-trips random and boundary `double`s through `wiz_ryu_d2s` and
`strtod`, from the Ryu block of `runtime/rt_data.inc`. -/
def ryuRoundTripProgram : IO String := do
  let src ← IO.FS.readFile "runtime/rt_data.inc"
  let start := "#define WIZ_RYU_MANTISSA_BITS"
  let marker := "WIZ_API const char *wiz_f64_show(double a) {"
  let some prefix := between? src start marker
    | throw (IO.userError "runtime/rt_data.inc: no Ryu block (R6): the Float64 printer is not Ryu")
  let tail := (src.splitOn marker).drop 1 |>.headD ""
  let body := (tail.splitOn "}").headD ""
  if body.isEmpty then
    throw (IO.userError "runtime/rt_data.inc: wiz_f64_show has no body")
  pure <| "#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n"
    ++ "#define WIZ_API static\n" ++ start ++ prefix ++ marker ++ body ++ "}\n" ++
  "static int check(uint64_t bits) {\n" ++
  "  double d; memcpy(&d, &bits, sizeof d);\n" ++
  "  char buf[64]; int n = wiz_ryu_d2s(d, buf); buf[n] = 0;\n" ++
  "  double back = strtod(buf, NULL); uint64_t b2; memcpy(&b2, &back, sizeof b2);\n" ++
  "  if (b2 != bits) { printf(\"%016llx -> %s -> %016llx\\n\",\n" ++
  "    (unsigned long long)bits, buf, (unsigned long long)b2); return 0; }\n" ++
  "  return 1;\n}\n" ++
  "int main(void) {\n" ++
  "  static const uint64_t fixed[] = { 0x0ull, 0x8000000000000000ull,\n" ++
  "    0x1ull, 0xfffffffffffffull, 0x10000000000000ull, 0x7fefffffffffffffull,\n" ++
  "    0x3fb999999999999aull, 0x3ff0000000000000ull, 0x4340000000000000ull,\n" ++
  "    0x4005bf0a8b145769ull, 0x0010000000000001ull, 0x0000000000000002ull };\n" ++
  "  for (unsigned i = 0; i < sizeof fixed / sizeof fixed[0]; ++i)\n" ++
  "    if (!check(fixed[i])) return 1;\n" ++
  "  uint64_t seed = 0x9e3779b97f4a7c15ull;\n" ++
  "  for (int i = 0; i < 200000; ++i) {\n" ++
  "    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;\n" ++
  "    if (((seed >> 52) & 0x7ff) == 0x7ff) continue; /* NaN/Inf: strtod text is not bit-preserving */\n" ++
  "    if (!check(seed)) return 1;\n" ++
  "  }\n  return 0;\n}\n"

def numericsGroup : Group where
  name := "numerics"
  exercise := "—"
  parallel := true
  cases := [
    { name := "R2: the GMP pin in flake.nix, the bundled source and docs/release/gmp-pin.json agree", run := fun _ => do
        let (fv, fnix, frel) ← flakeGmpPin
        let (bv, bh) ← bundleGmpPin
        let (rv, rrel, rnix) ← recordGmpPin
        let bundleHash := "sha256-" ++ bh
        unless fv == bv && bv == rv && frel == bundleHash && bundleHash == rrel &&
            fnix == rnix do
          throw (IO.userError
            s!"GMP pin mismatch (R2): flake.nix says GMP {fv} (nix {fnix}, release {frel}); \
               scripts/bundle-cc.sources says GMP {bv} (release {bundleHash}); \
               docs/release/gmp-pin.json says GMP {rv} (release {rrel}, nix {rnix}). \n\
               The release's bignum identity is the kernel's trusted base: update all \
               three deliberately (and say why in the record).") },
    { name := "R2: flake.nix asserts the pin and names both hashes on a mismatch", run := fun _ => do
        let src ← IO.FS.readFile "flake.nix"
        check ((src.splitOn "but the pin is GMP").length > 1)
          "flake.nix has no GMP attestation assert: `nix eval` would accept a different GMP silently"
        check ((src.splitOn "gmpSrcHash pkgs").length > 1)
          "flake.nix's GMP assert does not compare the source hash"
        check ((src.splitOn "docs/release/gmp-pin.json").length > 1)
          "flake.nix's GMP assert does not point at the attestation record" },
    { name := "R6: Float64.toString prints Ryu's shortest round-trip text (exact boundary strings)", run := fun _ => do
        -- (every expected string is the shortest decimal that reads back as this double;
        -- `NaN`'s sign bit is not part of the value, and `-0.0` keeps its sign)
        let src := "import IO\n" ++
          "def halve : Nat → Float64 → Float64\n  | .zero, x => x\n" ++
          "  | .succ k, x => halve k (Float64.div x (Float64.ofNat 2))\n" ++
          "def double : Nat → Float64 → Float64\n  | .zero, x => x\n" ++
          "  | .succ k, x => double k (Float64.add x x)\n" ++
          "def main : IO Unit := do\n" ++
          "  IO.println (Float64.toString (Float64.ofNat 0));\n" ++                   -- 0E0
          "  IO.println (Float64.toString (Float64.mul (Float64.ofNat 0) (Float64.sub (Float64.ofNat 0) (Float64.ofNat 1))));\n" ++ -- -0E0
          "  IO.println (Float64.toString (Float64.ofNat 1));\n" ++                   -- 1E0
          "  IO.println (Float64.toString (Float64.div (Float64.ofNat 1) (Float64.ofNat 10)));\n" ++ -- 1E-1
          "  IO.println (Float64.toString (Float64.div (Float64.ofNat 1) (Float64.ofNat 3)));\n" ++ -- 3.333…E-1
          "  IO.println (Float64.toString (Float64.add (Float64.div (Float64.ofNat 1) (Float64.ofNat 10)) (Float64.div (Float64.ofNat 1) (Float64.ofNat 5))));\n" ++ -- 3.0000000000000004E-1
          "  IO.println (Float64.toString (Float64.ofNat 9007199254740992));\n" ++     -- 9.007199254740992E15
          "  IO.println (Float64.toString (Float64.ofNat 9007199254740993));\n" ++     -- rounds to 2^53: the same text
          "  IO.println (Float64.toString (Float64.ofNat 18446744073709551615));\n" ++ -- 1.8446744073709552E19
          "  IO.println (Float64.toString (halve 1074 (Float64.ofNat 1)));\n" ++       -- 5E-324 (min subnormal)
          "  IO.println (Float64.toString (double 1023 (Float64.ofNat 1)));\n" ++      -- 8.98846567431158E307 (2^1023)
          "  IO.println (Float64.toString (Float64.ofNat (Nat.pow 10 308)));\n" ++     -- 1E308
          "  IO.println (Float64.toString (Float64.div (Float64.ofNat 1) (Float64.ofNat 0)));\n" ++ -- Infinity
          "  IO.println (Float64.toString (Float64.div (Float64.sub (Float64.ofNat 0) (Float64.ofNat 1)) (Float64.ofNat 0)));\n" ++ -- -Infinity
          "  IO.println (Float64.toString (Float64.div (Float64.ofNat 0) (Float64.ofNat 0)));\n" ++ -- NaN
          "  IO.pure ()\n"
        let expected := String.intercalate "\n" [
          "0E0", "-0E0", "1E0", "1E-1", "3.333333333333333E-1",
          "3.0000000000000004E-1", "9.007199254740992E15", "9.007199254740992E15",
          "1.8446744073709552E19", "5E-324", "8.98846567431158E307", "1E308",
          "Infinity", "-Infinity", "NaN"] ++ "\n"
        cRunIO src expected },
    { name := "R6: every printed Float64 reads back to the same bits (random patterns and boundaries)", run := fun _ => do
        let some cc ← findCC ((← IO.getEnv "PATH").getD "").splitOn ":"
          | skip "no cc on PATH to build the round-trip probe"
        let src ← ryuRoundTripProgram
        let dir ← IO.FS.createTempDir
        let c := dir / "ryu_roundtrip.c"
        let exe := dir / "ryu_roundtrip"
        IO.FS.writeFile c src
        let built ← IO.Process.output { cmd := cc, args := #["-O2", "-w", "-o", exe.toString, c.toString] }
        unless built.exitCode == 0 do
          throw (IO.userError s!"cc failed on the Ryu probe:\n{built.stderr}")
        let ran ← IO.Process.output { cmd := exe.toString }
        unless ran.exitCode == 0 do
          throw (IO.userError s!"a printed Float64 did not read back to its bits:\n{ran.stdout}") },
    { name := "R6: no build path enables fast-math, and the C backend pins -ffp-contract=off", run := fun _ => do
        let forbidden := ["-ffast-math", "-Ofast", "-funsafe-math-optimizations",
          "-ffinite-math-only", "-freciprocal-math", "-fassociative-math", "-fno-signed-zeros",
          "-ffp-contract=fast"]
        for f in buildPathFiles do
          let src ← IO.FS.readFile f
          for line in codeLines src do
            for tok in forbidden do
              check (!line.contains tok) s!"{f}: `{tok}` in `{line.trimAscii.toString}`: fast-math breaks IEEE semantics and bit-identical output"
        let build ← IO.FS.readFile "Wiz/Compiler/Build.lean"
        check ((build.splitOn "-ffp-contract=off").length > 1)
          "Wiz/Compiler/Build.lean: the C compiler invocations do not pin -ffp-contract=off" },
    { name := "R4: lib/ contains no use of the trusted forms (smt, native_refl, native_decide, sat_decide_native)", run := fun _ => do
        -- `sat_decide`/`bv_decide` are proof-carrying and allowed (they add no axiom);
        -- the grep here is for the *trusted* forms and for the native shortcuts. The
        -- trust-ledger case in the `native` group is the authoritative check that no
        -- `smt✝`/`native✝` axiom reaches a lib/ declaration; this one catches a source
        -- that would add one even if the ledger were not regenerated.
        for f in ← wizFiles "lib" do
          let src ← IO.FS.readFile f
          for line in codeLines src do
            let t := line.trimAscii.toString
            -- a `syntax … "smt" : tactic` line *declares* the tactic (the plumbing is
            -- in lib/); a use is `by smt` or the term-level `native_refl`
            unless t.startsWith "syntax" do
              for tok in ["by smt", "native_refl", "native_decide", "by sat_decide_native"] do
                check (!t.contains tok) s!"{f}: `{tok}` in `{t}`: a trusted form in lib/" }
  ]

builtin_initialize registerGroup numericsGroup

end Tests.Elab
