import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (8f) A target is a triple, the C compiler that produces it, its data layout and (for
a cross target) the command that runs its binaries. -/
def targetArm : Toolchain :=
  (({} : Toolchain).parseFlags ["--target", "aarch64-linux-gnu"]).1

def targetI686 : Toolchain :=
  (({} : Toolchain).parseFlags ["--target", "i686-linux-gnu"]).1

/-- Is `cmd` on `PATH`? (Cross compilers and emulators are optional here.) -/
def hasExe (cmd : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "sh", args := #["-c", "command -v " ++ cmd] }
    pure (out.exitCode == 0)
  catch _ => pure false

/-- An error that means the toolchain for a target is not installed here (so the case
skips rather than fails). -/
def targetMissing (e : String) : Bool :=
  ["gmp.h", "llc:", "No such file", "not found", "cannot find", "command not found",
   "error while loading", "exec format error"].any fun m => (e.splitOn m).length > 1

/-- Build and run `main` with `tc`, then compare a cross target's output with the host's
for the same source. A missing cross compiler, emulator or target GMP is a skip. -/
def differential (triple : String) (src : String) : IO Unit := do
  let some g := BuildTarget.ofTriple? triple
    | throw (IO.userError s!"no advertised target {triple}")
  unless ← hasExe g.cc do skip s!"no {g.cc}"; return
  match g.runner with
  | [] => skip s!"no runner for {triple}"; return
  | emulator :: _ =>
    unless ← hasExe emulator do skip s!"no {emulator}"; return
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← preludeLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let hostTc ← toolchain
  let dir ← IO.FS.createTempDir
  let nativeOut ← match ← Build.runGlobal hostTc s "main" (dir / "native") (timeout := some 120) with
    | .ok v => pure v
    | .error e => if targetMissing e then skip "no C toolchain"; return else throw (IO.userError s!"host build: {e}")
  -- (the target compiler's own sysroot is where qemu finds the target's libraries)
  let sys ← IO.Process.output { cmd := g.cc, args := #["-print-sysroot"] }
  let sysroot := sys.stdout.trimAscii.toString
  let emulator := g.runner.headD ""
  let runner := emulator :: (if sysroot.isEmpty then [] else ["-L", sysroot])
  let target : BuildTarget := { g with runner := runner }
  let cross : Toolchain :=
    { hostTc with target := some target, cc := g.cc, ccSet := true, cflags := [], ldflags := [], libs := [], gmp := ["-lgmp"] }
  match ← Build.runGlobal cross s "main" (dir / "cross") (timeout := some 120) with
  | .ok v => checkEq nativeOut v
  | .error e =>
    if targetMissing e then skip s!"no {triple} C toolchain (GMP/sysroot)"; return
    else throw (IO.userError s!"{triple}: {e}")

def targetSource : String :=
  "import Prelude
def main : List Nat :=
  .cons (Nat.mul 123456789 987654321)
  (.cons (Nat.pow 3 40)
  (.cons (Nat.shiftLeft 1 63)
  (.cons (Nat.div (Nat.pow 10 30) 7) .nil)))
"

def targetGroup : Group where
  name := "target"
  exercise := "Stage 8f"
  cases := [
    { name := "`--target` names a target and the C compiler that produces it, and an explicit --cc wins", run := fun _ => do
        let (tc, rest) := ({} : Toolchain).parseFlags
          ["--target", "aarch64-linux-gnu", "check", "main.wiz"]
        checkEq (some "aarch64-linux-gnu") (tc.target.map (·.triple))
        checkEq "aarch64-linux-gnu-gcc" tc.cc
        checkEq ["check", "main.wiz"] rest
        checkEq (some 64) (tc.target.map (·.pointerWidth))
        -- `--cc` wins in either order
        for args in [["--target", "aarch64-linux-gnu", "--cc", "my-cc"],
                     ["--cc", "my-cc", "--target", "aarch64-linux-gnu"]] do
          let (tc, _) := ({} : Toolchain).parseFlags args
          checkEq "my-cc" tc.cc
          checkEq (some "aarch64-linux-gnu") (tc.target.map (·.triple))
        -- a bundle's or a build file's compiler is a default, so `--target` replaces it
        let (tc, _) := ({ cc := "/bundle/cc" } : Toolchain).parseFlags
          ["--target", "aarch64-linux-gnu"]
        checkEq "aarch64-linux-gnu-gcc" tc.cc
        let fromSettings := (({} : Toolchain).set "cc" "/local/cc").getD {}
        let (tc, _) := fromSettings.parseFlags ["--target", "aarch64-linux-gnu"]
        checkEq "aarch64-linux-gnu-gcc" tc.cc
        -- native, and an unknown target is left for the argument parser (not silently host)
        let (tc, _) := ({} : Toolchain).parseFlags ["--target", "native"]
        check tc.target.isNone "native must be the host"
        let (tc, rest) := ({} : Toolchain).parseFlags ["--target", "bogus-triple", "check", "x.wiz"]
        check tc.target.isNone "an unknown target must not become a build"
        checkEq ["--target", "bogus-triple", "check", "x.wiz"] rest
        -- the flags come back out (another process gets the same target)
        let (back, _) := ({} : Toolchain).parseFlags targetArm.toFlags
        checkEq (targetArm.target.map (·.triple)) (back.target.map (·.triple))
        checkEq targetArm.cc back.cc
        checkEq targetArm.targetId back.targetId
        check ((targetArm.render.splitOn "target aarch64-linux-gnu").length > 1) targetArm.render },
    { name := "the target enters the build and cache keys", run := fun _ => do
        let native : Toolchain := {}
        check (native.id != targetArm.id) "the target is not in the toolchain id"
        check (native.targetId != targetI686.targetId) "the target is not in the cache namespace"
        check (targetArm.targetId != targetI686.targetId) "two targets share a cache namespace"
        check (!native.isCross) "the host is not a cross target"
        check targetI686.isCross "i686 is a cross target from a 64-bit host"
        -- the cache keys of modules differ, and so does every file name built from them
        let loader ← preludeLoader
        let kArm := Cache.moduleKey loader (fun _ => none) targetArm.targetId "Prelude"
        let kI686 := Cache.moduleKey loader (fun _ => none) targetI686.targetId "Prelude"
        check (kArm != kI686) "two targets share a module key"
        check (Cache.regionFileName 1 kArm != Cache.regionFileName 1 kI686)
          "two targets share a region file name" },
    { name := "the elaboration cache is namespaced by target: a warm native cache is cold for a cross target", run := fun _ => do
        let loader ← preludeLoader
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader }
        let src := "import Prelude\ndef two : Nat := 1 + 1\n#eval two\n"
        let dir ← IO.FS.createTempDir
        let run (tc : Toolchain) :=
          Cache.elaborateCached (some dir) [] src init 0 (toolchain := tc.targetId) (binary := some 1)
        let (sArm, h1) ← run targetArm
        let (sI686, h2) ← run targetI686
        let (_, h3) ← run targetArm
        checkEq 0 h1
        checkEq 0 h2
        check (h3 > 0) "the target's own entries were not found"
        let msgs (s : CommandState ZeroOneMany) := s.messages.toList.map (·.render src)
        checkEq (msgs sArm) (msgs sI686) },
    { name := "a 32-bit target is guarded, and LLVM is not a cross backend", run := fun _ => do
        let some i686 := BuildTarget.ofTriple? "i686-linux-gnu"
          | throw (IO.userError "i686-linux-gnu is not advertised")
        checkEq 32 i686.pointerWidth
        checkEq (some 4) (Build.pointerWidthIn "#define __SIZEOF_POINTER__ 4\n#define __BYTE_ORDER__ 1234\n")
        checkEq (some 8) (Build.pointerWidthIn "#define __SIZEOF_POINTER__ 8\n")
        checkEq none (Build.pointerWidthIn "#define __SIZEOF_POINTER__ wide\n")
        match Build.checkWidth i686 "i686-linux-gnu-gcc" 32 with
        | .ok () => pure ()
        | .error e => throw (IO.userError e)
        match Build.checkWidth i686 "cc" 64 with
        | .ok () => throw (IO.userError "a 64-bit compiler passed the 32-bit target")
        | .error e =>
          check ((e.splitOn "32-bit").length > 1) e
          check ((e.splitOn "64-bit code").length > 1) e
        -- the generated C selects 32-bit's 30 small-int bits from the same width
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef main : Nat := 1\n"
          { trustedModule := Tests.libModule, loader := ← preludeLoader }
        let decls ← match Build.irProgram s "main" with
          | .ok (ds, _) => pure ds
          | .error e => throw (IO.userError e)
        let c := C.program decls
        for needle in ["#define WIZ_SMALL_BITS 30", "unsupported pointer width", "wiz_box_checked"] do
          check ((c.splitOn needle).length > 1) s!"the generated C lacks {needle}"
        -- a cross target's binary is run through its runner, unless one is given
        let (cmd, args) := targetArm.runCommand "/tmp/prog" #["x"]
        checkEq "qemu-aarch64" cmd
        checkEq ["-L", "/usr/aarch64-linux-gnu", "/tmp/prog", "x"] args.toList
        let (tc, _) := ({} : Toolchain).parseFlags
          ["--target", "aarch64-linux-gnu", "--runner", "my-qemu -L /s"]
        let (cmd, args) := tc.runCommand "/tmp/prog" #["x"]
        checkEq "my-qemu" cmd
        checkEq ["-L", "/s", "/tmp/prog", "x"] args.toList
        let (cmd, _) := ({} : Toolchain).runCommand "/tmp/prog"
        checkEq "/tmp/prog" cmd
        -- LLVM is refused before a build, so no compiler is needed to see it
        let dir ← IO.FS.createTempDir
        match ← Build.build targetI686 s "main" (dir / "prog") true false with
        | .ok _ => throw (IO.userError "LLVM accepted a cross target")
        | .error e => check ((e.splitOn "not a cross backend").length > 1) e },
    { name := "aarch64-linux-gnu runs the same program as the host, byte for byte (or skips)", run := fun _ =>
        differential "aarch64-linux-gnu" targetSource },
    { name := "i686-linux-gnu (32-bit) runs the same program as the host, through the 30-bit guard (or skips)", run := fun _ =>
        differential "i686-linux-gnu" targetSource }
  ]

builtin_initialize registerGroup targetGroup

end Tests.Elab
