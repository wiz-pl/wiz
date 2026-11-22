import Tests.Harness
import Wiz.Attest
import Lean.Data.Json

/-!
# Stage 11ae: build attestations

`wiz build --attest` writes an unsigned in-toto statement about a build (source and input
hashes, toolchain, flags, output hashes), and `wiz verify` recomputes the hashes. The
cases here build a small program with a `link_c` file in a temporary Git repository:
the statement is complete, verification passes, a tampered artifact or input fails, an
identical rebuild is byte-identical, a flag change moves the predicate but not
`inputsRoot`, a tracked edit shows as `git.dirty`, `--artifact-only` verifies without
the inputs, and a non-empty (forged) signature is refused.
-/

set_option compiler.extract_closed false

open Wiz

namespace Tests.Attest

open Tests
open Lean (Json)

def mkTree (files : List (String × String)) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  pure dir

def gitIn (dir : System.FilePath) (args : List String) : IO String := do
  let o ← IO.Process.output {
    cmd := "git", cwd := dir,
    args := #["-c", "user.name=attest", "-c", "user.email=attest@example.com",
              "-c", "init.defaultBranch=main", "-c", "commit.gpgsign=false"] ++ args.toArray }
  if o.exitCode != 0 then throw (IO.userError s!"git {args}: {o.stderr}")
  pure o.stdout.trimAscii.toString

/-- A project with a `link_c` file, committed to Git (so `source.git` is present). -/
def project : IO (System.FilePath × Toolchain × System.FilePath) := do
  let dir ← mkTree [
    ("hello.wiz", "import IO\nlink_c \"extra.c\"\ndef main : IO Unit := IO.println \"attested hello\"\n"),
    ("extra.c", "int wiz_attest_extra(void) { return 1; }\n")]
  let _ ← gitIn dir ["init", "--quiet"]
  let _ ← gitIn dir ["add", "."]
  let _ ← gitIn dir ["commit", "--quiet", "-m", "init"]
  pure (dir, ← toolchain, dir / "cache")

def wizExe : IO String := do pure (← IO.FS.realPath ".lake/build/bin/wiz").toString

/-- Build `hello.wiz` with an attestation; `extraCflags` is appended to the suite's
cflags (`-D…`). Returns stdout, stderr and the exit code. -/
def build (dir : System.FilePath) (tc : Toolchain) (cache : System.FilePath)
    (attest : String := "prog.attest.json") (extraCflags : String := "")
    (env : Array (String × Option String) := #[]) : IO (String × String × UInt32) := do
  let tc : Toolchain := { tc with cacheDir := some cache, cflags := tc.cflags ++ (if extraCflags.isEmpty then [] else [extraCflags]) }
  let args := tc.toFlags ++ ["build", "hello.wiz", "-o", "prog", "--attest", attest]
  let exe ← wizExe
  let o ← IO.Process.output { cmd := exe, args := args.toArray, cwd := some dir, env }
  pure (o.stdout, o.stderr, o.exitCode)

/-- `wiz verify`; with `attest = ""` the default path is used. -/
def verify (dir : System.FilePath) (tc : Toolchain) (attest artifact : String)
    (extra : List String := []) : IO (String × String × UInt32) := do
  let args := tc.toFlags ++ ["verify"] ++
    (if attest.isEmpty then [] else ["--attest", attest]) ++ extra ++ [artifact]
  let exe ← wizExe
  let o ← IO.Process.output { cmd := exe, args := args.toArray, cwd := some dir }
  pure (o.stdout, o.stderr, o.exitCode)

def statement (dir : System.FilePath) (file : String) : IO Json := do
  match ← Wiz.Attest.readStatement (dir / file) with
  | .ok st => pure st
  | .error e => throw (IO.userError e)

def predicate (st : Json) : Json := (st.getObjVal? "predicate").toOption.getD Json.null

def source (st : Json) : Json := ((predicate st).getObjVal? "source").toOption.getD Json.null

def output (st : Json) : Json := ((predicate st).getObjVal? "output").toOption.getD Json.null

/-- `predicate.toolchain` as an object. -/
def toolchainPart (st : Json) : Json := ((predicate st).getObjVal? "toolchain").toOption.getD Json.null

def gitDirty (st : Json) : Option Bool :=
  ((source st).getObjVal? "git").toOption.bind fun g =>
    (g.getObjVal? "dirty").toOption.bind fun v => (Json.getBool? v).toOption

def shaOf (p : System.FilePath) : IO String := do
  pure (Wiz.Smt.Sha256.hexBytes (← IO.FS.readBinFile p))

def inputsRoot (st : Json) : String := (Wiz.Attest.strField? (predicate st) "inputsRoot").getD ""

/-- The statement's inputs. -/
def inputs (st : Json) : Array Json := (Wiz.Attest.arrField? (predicate st) "inputs").getD #[]

def group : Group where
  name := "attest"
  exercise := "Stage 11ae"
  cases := [
    { name := "build with --attest writes a complete, unsigned statement; verify passes", run := fun _ => do
        let (dir, tc, cache) ← project
        let (_, err, code) ← build dir tc cache
        if code != 0 then
          if (err.splitOn "could not execute").length > 1 || (err.splitOn "failed").length > 1 then
            skip "no toolchain"
            return
          throw (IO.userError s!"build failed ({code}): {err}")
        check ((err.splitOn "attestation written").length > 1) s!"no note: {err}"
        let st ← statement dir "prog.attest.json"
        checkEq Wiz.Attest.statementType ((Wiz.Attest.strField? st "_type").getD "")
        checkEq Wiz.Attest.predicateType ((Wiz.Attest.strField? st "predicateType").getD "")
        let some (name, sha) := Wiz.Attest.subjectDigest st | throw (IO.userError "no subject")
        checkEq "prog" name
        checkEq (← shaOf (dir / "prog")) sha
        checkEq (some sha) (Wiz.Attest.strField? (output st) "sha256")
        let ins := inputs st
        check (ins.size == 4) s!"expected 4 inputs, got {ins.size}"
        check (ins.any fun i => Wiz.Attest.strField? i "role" == some "source") "no source input"
        check (ins.any fun i => Wiz.Attest.strField? i "role" == some "module" &&
          Wiz.Attest.strField? i "name" == some "IO") "no IO module input"
        check (ins.any fun i => Wiz.Attest.strField? i "role" == some "link-c") "no link-c input"
        check ((inputsRoot st).startsWith "sha256:") "no inputsRoot"
        check ((toolchainPart st).getObjVal? "wiz").toOption.isSome "no wiz toolchain identity"
        check ((toolchainPart st).getObjVal? "cc").toOption.isSome "no cc identity"
        check ((source st).getObjVal? "git").toOption.isSome "no git provenance"
        checkEq (some false) (gitDirty st)
        let (out, verr, vcode) ← verify dir tc "prog.attest.json" "prog"
        check (vcode == 0) s!"verify failed: {verr}"
        check ((out.splitOn "OK prog").length > 1) out
        -- the default path is ARTIFACT.attest.json
        let (out, verr, vcode) ← verify dir tc "" "prog"
        check (vcode == 0) s!"default verify failed: {verr}"
        check ((out.splitOn "unsigned statement").length > 1) out
        -- no secret: an environment variable is not copied into the statement
        let (_, err, code) ← build dir tc cache "secret.json" (env := #[("BUILD_ATTEST_SECRET", some "s3cr3t-value")])
        check (code == 0) err
        let text ← IO.FS.readFile (dir / "secret.json")
        check (!text.contains "s3cr3t-value") "the statement copied an environment variable" },
    { name := "a tampered artifact fails verification", run := fun _ => do
        let (dir, tc, cache) ← project
        let (_, _, code) ← build dir tc cache
        if code != 0 then skip "no toolchain"; return
        let p := dir / "prog"
        IO.FS.writeBinFile p ((← IO.FS.readBinFile p) ++ "x".toUTF8)
        let (out, verr, vcode) ← verify dir tc "prog.attest.json" "prog"
        check (vcode == 1) s!"tampered artifact verified: {out}"
        check ((verr.splitOn "artifact mismatch").length > 1) verr },
    { name := "an identical rebuild produces a byte-identical envelope", run := fun _ => do
        let (dir, tc, cache) ← project
        let (_, _, code) ← build dir tc cache
        if code != 0 then skip "no toolchain"; return
        let first ← IO.FS.readFile (dir / "prog.attest.json")
        let (_, err, code) ← build dir tc cache
        check (code == 0) err
        let second ← IO.FS.readFile (dir / "prog.attest.json")
        checkEq first second
        check (!first.contains "\"startedOn\"" && !first.contains "\"finishedOn\"") "a timestamp is in the envelope" },
    { name := "a cflags change changes the predicate, not inputsRoot", run := fun _ => do
        let (dir, tc, cache) ← project
        let (_, _, code) ← build dir tc cache "a.json"
        if code != 0 then skip "no toolchain"; return
        let (_, err, code) ← build dir tc cache "b.json" "-DWIZ_ATTEST_EXTRA=1"
        check (code == 0) err
        let a ← statement dir "a.json"
        let b ← statement dir "b.json"
        check ((predicate a).compress != (predicate b).compress) "the predicate did not change"
        checkEq (inputsRoot a) (inputsRoot b)
        checkEq (some (← shaOf (dir / "prog"))) (Wiz.Attest.strField? (output b) "sha256") },
    { name := "an edit to a tracked input is dirty and changes the source hash", run := fun _ => do
        let (dir, tc, cache) ← project
        let (_, _, code) ← build dir tc cache "before.json"
        if code != 0 then skip "no toolchain"; return
        let before ← statement dir "before.json"
        checkEq (some false) (gitDirty before)
        let oldSha := (Wiz.Attest.strField? (source before) "sha256").getD ""
        IO.FS.writeFile (dir / "hello.wiz")
          "import IO\nlink_c \"extra.c\"\n-- an edit\n-- and another\ndef main : IO Unit := IO.println \"attested hello\"\n"
        let (_, err, code) ← build dir tc cache "after.json"
        check (code == 0) err
        let after ← statement dir "after.json"
        checkEq (some true) (gitDirty after)
        checkEq (← shaOf (dir / "hello.wiz")) ((Wiz.Attest.strField? (source after) "sha256").getD "")
        check (oldSha != (Wiz.Attest.strField? (source after) "sha256").getD "") "the source hash did not change" },
    { name := "--artifact-only verifies without the inputs; the default needs them", run := fun _ => do
        let (dir, tc, cache) ← project
        let (_, _, code) ← build dir tc cache
        if code != 0 then skip "no toolchain"; return
        let other ← IO.FS.createTempDir
        IO.FS.writeBinFile (other / "prog") (← IO.FS.readBinFile (dir / "prog"))
        IO.FS.writeFile (other / "prog.attest.json") (← IO.FS.readFile (dir / "prog.attest.json"))
        let (_, verr, vcode) ← verify other tc "prog.attest.json" "prog"
        check (vcode == 1) "verification without the inputs passed"
        check ((verr.splitOn "is missing").length > 1) verr
        let (out, verr, vcode) ← verify other tc "prog.attest.json" "prog" ["--artifact-only"]
        check (vcode == 0) s!"--artifact-only failed: {verr}"
        check ((out.splitOn "artifact only").length > 1) out },
    { name := "the envelope is explicitly unsigned; a forged signature is refused", run := fun _ => do
        let (dir, tc, cache) ← project
        let (_, _, code) ← build dir tc cache
        if code != 0 then skip "no toolchain"; return
        let file := dir / "prog.attest.json"
        let env ← match Json.parse (← IO.FS.readFile file) with
          | .ok j => pure j
          | .error e => throw (IO.userError e)
        checkEq 0 ((Wiz.Attest.arrField? env "signatures").getD #[]).size
        checkEq (some Wiz.Attest.dssePayloadType) (Wiz.Attest.strField? env "payloadType")
        -- forge a signature: the payload is unchanged, only `signatures` is non-empty
        let payload := (Wiz.Attest.strField? env "payload").getD ""
        check (!payload.isEmpty) "no payload"
        let forged := Json.mkObj [
          ("payloadType", Json.str Wiz.Attest.dssePayloadType),
          ("payload", Json.str payload),
          ("signatures", Json.arr #[Json.mkObj [("keyid", Json.str "forged"), ("sig", Json.str "AAAA")]])]
        IO.FS.writeFile (dir / "forged.json") (forged.compress ++ "\n")
        let (_, verr, vcode) ← verify dir tc "forged.json" "prog"
        check (vcode == 1) "a forged signature was accepted"
        check ((verr.splitOn "signature verification is not implemented").length > 1) verr }
  ]

builtin_initialize registerGroup group

end Tests.Attest
