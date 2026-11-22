import Lean.Data.Json
import Wiz.Module
import Wiz.Smt.Sha256
import Wiz.Toolchain
import Wiz.Version

/-!
# Build attestations (in-toto statements, unsigned)

`wiz build --attest FILE` writes a build provenance statement: an in-toto Statement
(`https://in-toto.io/Statement/v1`) whose predicate names the source, the hashed inputs,
the toolchain, the flags and the output artifact, inside a DSSE-style envelope
(`payloadType`, base64 `payload`, `signatures`). The `signatures` array is empty: this is
the **non-TEE half** of attested builds — a signed statement needs a key and a key
release story (`wiz-notes/build-attest.md`, `wiz-notes/attested-enclave-builds.md`).

`wiz verify --attest FILE ARTIFACT` reads the envelope, recomputes the artifact's SHA-256
and (by default) the hashes of the recorded inputs, and exits non-zero on a mismatch.
The statement is *not* proof that the builder told the truth: it is a claim that anyone
who rebuilds from the same inputs can check (reproducibility), and the slot where a
signature or a TEE quote would go.
-/

namespace Wiz.Attest

open Lean (Json)
open System (FilePath)

/-- The in-toto Statement type this module writes. -/
def statementType : String := "https://in-toto.io/Statement/v1"
/-- The project predicate: compiler-specific facts, not SLSA build-platform facts. -/
def predicateType : String := "https://wiz-lang.org/attestation/wiz-build/v1"
/-- The predicate's shape version (bump when a field changes meaning). -/
def predicateFormat : Nat := 1
/-- The DSSE envelope's payload type. -/
def dssePayloadType : String := "application/vnd.in-toto+json"

/-! ## Hashing -/

/-- The SHA-256 of a file's bytes, or `none` if it cannot be read. -/
def digestFile (p : FilePath) : IO (Option String) := do
  if !(← p.pathExists) then return none
  try
    return some (Wiz.Smt.Sha256.hexBytes (← IO.FS.readBinFile p))
  catch _ => return none

/-- A path relative to `base` when it is under it, else absolute (so a statement built
and checked in one tree does not depend on the machine's temporary directories, and a
path outside the tree is shown honestly). -/
def portablePath (base : FilePath) (p : FilePath) : IO String := do
  try
    let b := (← IO.FS.realPath base).toString
    let q := (← IO.FS.realPath p).toString
    let b := if b.endsWith "/" then b else b ++ "/"
    if q.startsWith b then return (q.drop b.length).toString
    return q
  catch _ => return p.toString

/-! ## Base64 (DSSE's payload encoding; no dependency) -/

private def b64chars : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

/-- Standard base64, as DSSE uses for the payload. -/
def base64Encode (b : ByteArray) : String := Id.run do
  let n := b.size
  let mut out := ""
  let mut i := 0
  while i < n do
    let b0 := (b.get! i).toNat
    let b1 := if i + 1 < n then (b.get! (i + 1)).toNat else 0
    let b2 := if i + 2 < n then (b.get! (i + 2)).toNat else 0
    let x := b0 <<< 16 ||| b1 <<< 8 ||| b2
    out := out.push b64chars[(x >>> 18) &&& 63]!
    out := out.push b64chars[(x >>> 12) &&& 63]!
    out := out.push (if i + 1 < n then b64chars[(x >>> 6) &&& 63]! else '=')
    out := out.push (if i + 2 < n then b64chars[x &&& 63]! else '=')
    i := i + 3
  pure out

private def b64val (c : Char) : Option Nat :=
  if c ≥ 'A' && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if c ≥ 'a' && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if c ≥ '0' && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

/-- Decode base64 (whitespace ignored); `none` on a malformed string. -/
def base64Decode (s : String) : Option ByteArray := Id.run do
  let cs := (s.toList.filter fun c => !c.isWhitespace).toArray
  if cs.size % 4 != 0 then return none
  let mut out : ByteArray := .empty
  let mut i := 0
  while i < cs.size do
    let c0 := cs[i]!; let c1 := cs[i+1]!; let c2 := cs[i+2]!; let c3 := cs[i+3]!
    let (v0, v1) := (b64val c0, b64val c1)
    let v2 := if c2 == '=' then some 0 else b64val c2
    let v3 := if c3 == '=' then some 0 else b64val c3
    match v0, v1, v2, v3 with
    | some a, some b, some c, some d =>
      let x := a <<< 18 ||| b <<< 12 ||| c <<< 6 ||| d
      out := out.push (UInt8.ofNat ((x >>> 16) &&& 255))
      if c2 != '=' then out := out.push (UInt8.ofNat ((x >>> 8) &&& 255))
      if c3 != '=' then out := out.push (UInt8.ofNat (x &&& 255))
    | _, _, _, _ => return none
    i := i + 4
  pure (some out)

/-! ## The inputs manifest -/

/-- One hashed input: the root file (`source`), an imported module (`module`, named by
its module name, so the record does not depend on where the library lives), or a
`link_c` file (`link-c`). -/
structure Input where
  role : String
  name : String := ""
  path : String := ""
  sha256 : String
  deriving Repr, Inhabited

def Input.toJson (i : Input) : Json :=
  Json.mkObj <|
    [("role", Json.str i.role), ("sha256", Json.str i.sha256)] ++
    (if i.name.isEmpty then [] else [("name", Json.str i.name)]) ++
    (if i.path.isEmpty then [] else [("path", Json.str i.path)])

def Input.ofJson (j : Json) : Except String Input := do
  let role ← j.getObjVal? "role" >>= Json.getStr?
  let sha ← j.getObjVal? "sha256" >>= Json.getStr?
  let name := ((j.getObjVal? "name").toOption.bind fun v => (Json.getStr? v).toOption).getD ""
  let path := ((j.getObjVal? "path").toOption.bind fun v => (Json.getStr? v).toOption).getD ""
  unless role == "source" || role == "module" || role == "link-c" do
    throw s!"unknown input role {role}"
  unless sha.length == 64 do throw s!"input {role}: not a SHA-256 digest"
  return { role, name, path, sha256 := sha }

/-- The order of a manifest: stable, so the root and the JSON do not depend on hash-map
iteration order. -/
def Input.lt (a b : Input) : Bool :=
  a.role < b.role ||
  (a.role == b.role && a.name < b.name) ||
  (a.role == b.role && a.name == b.name && a.path < b.path)

/-- The root over the manifest: SHA-256 of the canonical lines. A change to any recorded
input (or to its hash) changes it; the verifier recomputes it from the bytes on disk. -/
def inputsRoot (xs : List Input) : String :=
  let lines := xs.map fun i => s!"{i.role}\t{i.name}\t{i.path}\t{i.sha256}\n"
  Wiz.Smt.Sha256.hex ("wiz-inputs-v1\n" ++ String.join lines)

/-! ## Toolchain identity -/

/-- An executable the build used: its resolved path, its bytes' digest, and the first
line of `--version` (`""` when it could not be run). -/
structure Tool where
  path : String
  version : String := ""
  sha256 : String
  deriving Repr, Inhabited

def Tool.toJson (t : Tool) : Json :=
  Json.mkObj <|
    [("path", Json.str t.path), ("sha256", Json.str t.sha256)] ++
    (if t.version.isEmpty then [] else [("version", Json.str t.version)])

/-- Resolve a command the way the shell would: a path as given, or the first match on
`PATH`. -/
def findOnPath (cmd : String) : IO (Option String) := do
  if cmd.contains '/' then
    let p := FilePath.mk cmd
    if ← p.pathExists then return some p.toString else return none
  let path := (← IO.getEnv "PATH").getD ""
  for d in path.splitOn ":" do
    if d.isEmpty then continue
    let p := FilePath.mk d / cmd
    if ← p.pathExists then return some p.toString
  pure none

/-- The identity of a compiler (`cc`, `llc`): resolved path, byte digest, version line.
None when it cannot be found (the build itself would have failed). -/
def toolOf (cmd : String) : IO (Option Tool) := do
  let some p ← findOnPath cmd | return none
  let p ← try IO.FS.realPath p catch _ => pure p
  let sha := (← digestFile p).getD ""
  let version ← try
      let o ← IO.Process.output { cmd := p.toString, args := #["--version"] }
      if o.exitCode == 0 then pure ((o.stdout.splitOn "\n").headD "").trimAscii.toString else pure ""
    catch _ => pure ""
  pure (some { path := p.toString, version, sha256 := sha })

/-- The Git provenance of the build directory: `HEAD` and whether tracked files differ
from it (untracked build outputs do not count). `none` outside a repository. -/
def gitOf (dir : FilePath) : IO (Option (String × Bool)) := do
  try
    let h ← IO.Process.output { cmd := "git", args := #["-C", dir.toString, "rev-parse", "--verify", "HEAD"] }
    if h.exitCode != 0 then return none
    let st ← IO.Process.output { cmd := "git", args := #["-C", dir.toString, "status", "--porcelain", "--untracked-files=no"] }
    let dirty := st.exitCode == 0 && !st.stdout.trimAscii.isEmpty
    return some (h.stdout.trimAscii.toString, dirty)
  catch _ => pure none

/-! ## Reading a statement -/

/-- A string field of a JSON object (`none` if absent or of another type). -/
def strField? (j : Json) (k : String) : Option String :=
  (j.getObjVal? k).toOption.bind fun v => (Json.getStr? v).toOption

/-- A number field of a JSON object. -/
def natField? (j : Json) (k : String) : Option Nat :=
  (j.getObjVal? k).toOption.bind fun v => (Json.getNat? v).toOption

/-- An array field of a JSON object. -/
def arrField? (j : Json) (k : String) : Option (Array Json) :=
  (j.getObjVal? k).toOption.bind fun v => (Json.getArr? v).toOption

/-- Read the in-toto Statement out of a file and the envelope's `signatures` array
(empty for a bare statement): a DSSE envelope (`payloadType` + base64 `payload`, which is
what this module writes) or the bare statement object. -/
def readEnvelope (p : FilePath) : IO (Except String (Json × Array Json)) := do
  let text ← try IO.FS.readFile p catch e => return .error s!"cannot read {p}: {e}"
  match Json.parse text with
  | .error e => return .error s!"{p}: not JSON: {e}"
  | .ok j =>
    match (j.getObjVal? "payloadType").toOption with
    | none => return .ok (j, #[])
    | some pt =>
      match Json.getStr? pt with
      | .error _ => return .error s!"{p}: payloadType is not a string"
      | .ok pt =>
        if pt != dssePayloadType then return .error s!"{p}: unknown payloadType {pt}"
        let sigs := (arrField? j "signatures").getD #[]
        match (j.getObjVal? "payload").toOption with
        | none => return .error s!"{p}: envelope has no payload"
        | some payload =>
          match Json.getStr? payload with
          | .error _ => return .error s!"{p}: payload is not a string"
          | .ok ps =>
            match base64Decode ps with
            | none => return .error s!"{p}: payload is not base64"
            | some bytes =>
              match String.fromUTF8? bytes with
              | none => return .error s!"{p}: payload is not UTF-8"
              | some st =>
                match Json.parse st with
                | .error e => return .error s!"{p}: payload is not JSON: {e}"
                | .ok st => return .ok (st, sigs)

/-- The statement of an attestation file (see `readEnvelope`). -/
def readStatement (p : FilePath) : IO (Except String Json) := do
  match ← readEnvelope p with
  | .ok (st, _) => return .ok st
  | .error e => return .error e

/-- The artifact's digest from a statement's `subject` (the first subject). -/
def subjectDigest (st : Json) : Option (String × String) := do
  let subjects ← arrField? st "subject"
  let s ← subjects[0]?
  let name ← strField? s "name"
  let digest ← (s.getObjVal? "digest").toOption
  let sha ← strField? digest "sha256"
  pure (name, sha)

/-! ## Emitting -/

/-- The generated files beside the output (`.c`, `.h`, `.ll`, a split's units). -/
def byproductsOf (out : FilePath) (lib : Bool) (split : Nat) : IO (List (String × String)) := do
  let base := out.parent.getD "."
  let mut files : List FilePath := []
  let mut cands := [out.withExtension "c", out.withExtension "ll"]
  if lib then cands := cands ++ [out.withExtension "h"]
  for f in cands do
    if ← f.pathExists then files := files ++ [f]
  if split ≥ 2 then
    let dir := base / ((out.fileName.getD "wiz") ++ ".split")
    if ← dir.isDir then
      for e in ← dir.readDir do
        if e.path.extension == some "c" || e.path.extension == some "h" then
          files := files ++ [e.path]
  let mut out : List (String × String) := []
  for f in files do
    let name ← portablePath base f
    if let some h ← digestFile f then out := out ++ [(name, h)]
  pure out

/-- Write a build attestation for `out` to `attestPath`. `source` is the path as the
user gave it; the input manifest hashes that file, every module `wiz build` loaded
(named by module, so the record is portable), and every `link_c` file. `roots` is the
module search path (default: the toolchain's; `grail` passes the package's roots). -/
def emit (tc : Toolchain) (source : String) (out : FilePath)
    (llvm lib noMain : Bool) (split : Nat) (attestPath : FilePath)
    (roots? : Option (List FilePath) := none) : IO (Except String Unit) := do
  try
    let text ← IO.FS.readFile source
    let roots ← match roots? with
      | some r => pure r
      | none => Module.roots tc.searchPath
    let closure ← Module.loadClosure roots text
    let dir := (FilePath.mk source).parent.getD "."
    -- the manifest: the root file, the modules it reaches, and the link_c files
    let mut inputs : List Input :=
      [{ role := "source", path := source, sha256 := Wiz.Smt.Sha256.hex text }]
    for (n, _, src) in closure.toList do
      inputs := inputs ++ [{ role := "module", name := n, sha256 := Wiz.Smt.Sha256.hex src }]
    let linkC ← Module.cSourceTable dir text closure
    for (_, p) in linkC.toList do
      let f := FilePath.mk p
      if let some h ← digestFile f then
        inputs := inputs ++ [{ role := "link-c", path := ← portablePath (← IO.currentDir) f, sha256 := h }]
    let entries := inputs.toArray.qsort (fun a b => a.lt b) |>.toList
    -- the headers the file and its modules import (names only: the preprocessed text is
    -- the C compiler's, and hashing it would make the statement cc-version-specific)
    let headers := (Module.headersOf text ++ closure.toList.flatMap fun (_, _, s) => Module.headersOf s)
      |>.eraseDups |>.toArray.qsort (· < ·) |>.toList
    let head ← digestFile out
    let some outDigest := head | return .error s!"the output {out} does not exist"
    let wizExe ← try IO.appPath catch _ => pure (FilePath.mk "wiz")
    let wizSha := (← digestFile wizExe).getD ""
    let wizRev ← try Wiz.revision? catch _ => pure none
    let cc ← toolOf tc.cc
    let llc ← toolOf tc.llc
    let byproducts ← byproductsOf out lib split
    let git ← gitOf (← IO.currentDir)
    let kind := if lib then "object" else if noMain then "object-no-main" else "executable"
    let env : List (String × Json) :=
      [("platform", Json.str System.Platform.target)]
    let flags : List (String × Json) := [
      ("backend", Json.str (if llvm then "llvm" else "c")),
      ("kind", Json.str kind),
      ("cc", Json.str tc.cc),
      ("cflags", Json.arr (tc.cflags.map Json.str).toArray),
      ("ldflags", Json.arr (tc.ldflags.map Json.str).toArray),
      ("libs", Json.arr (tc.libs.map Json.str).toArray),
      ("gmp", Json.arr (tc.gmp.map Json.str).toArray),
      ("llc", Json.str tc.llc),
      ("gc-cflags", Json.arr (tc.gcCflags.map Json.str).toArray),
      ("gc-ldflags", Json.arr (tc.gcLdflags.map Json.str).toArray),
      ("split", Json.num split),
      ("roots", Json.arr ((tc.searchPath.map fun d => Json.str d.toString)).toArray)]
    let sourceJson :=
      match git with
      | some (commit, dirty) =>
        Json.mkObj [("file", Json.str source), ("sha256", Json.str (Wiz.Smt.Sha256.hex text)),
                    ("git", Json.mkObj [("commit", Json.str commit), ("dirty", Json.bool dirty)])]
      | none =>
        Json.mkObj [("file", Json.str source), ("sha256", Json.str (Wiz.Smt.Sha256.hex text))]
    let predicate := Json.mkObj [
      ("buildType", Json.str "https://wiz-lang.org/buildtypes/wiz-build/v1"),
      ("format", Json.num predicateFormat),
      ("source", sourceJson),
      ("inputsRoot", Json.str ("sha256:" ++ inputsRoot entries)),
      ("inputs", Json.arr (entries.map Input.toJson).toArray),
      ("headers", Json.arr (headers.map Json.str).toArray),
      ("toolchain", Json.mkObj ([
        ("wiz", Json.mkObj ([("version", Json.str Wiz.version), ("sha256", Json.str wizSha)] ++
          (match wizRev with | some r => [("revision", Json.str r)] | none => [])))] ++
        (match cc with | some t => [("cc", t.toJson)] | none => []) ++
        (match llc with | some t => [("llc", t.toJson)] | none => []))),
      ("flags", Json.mkObj flags),
      ("output", Json.mkObj [("kind", Json.str kind), ("name", Json.str (out.fileName.getD "")),
                             ("sha256", Json.str outDigest)]),
      ("byproducts", Json.arr (byproducts.map fun (n, h) =>
        Json.mkObj [("name", Json.str n), ("sha256", Json.str h)]).toArray),
      ("environment", Json.mkObj env)]
    let statement := Json.mkObj [
      ("_type", Json.str statementType),
      ("subject", Json.arr #[Json.mkObj [("name", Json.str (out.fileName.getD "")),
                                          ("digest", Json.mkObj [("sha256", Json.str outDigest)])]]),
      ("predicateType", Json.str predicateType),
      ("predicate", predicate)]
    let payload := statement.compress
    let envelope := Json.mkObj [
      ("payloadType", Json.str dssePayloadType),
      ("payload", Json.str (base64Encode payload.toUTF8)),
      ("signatures", Json.arr #[])]
    if let some d := attestPath.parent then
      if !d.toString.isEmpty then IO.FS.createDirAll d
    IO.FS.writeFile attestPath (envelope.pretty ++ "\n")
    pure (.ok ())
  catch e => return .error (toString e)

/-! ## Verifying -/

/-- Check a statement against an artifact: the artifact's SHA-256 against `subject` and
`predicate.output`, and (with `checkInputs`) every recorded input against the bytes on
disk, plus the manifest root. The signature is not checked: an envelope with a
non-empty `signatures` array is refused rather than silently accepted. -/
def verify (attestPath : FilePath) (artifact : FilePath) (checkInputs : Bool)
    (tc : Toolchain) : IO (Except String String) := do
  match ← readEnvelope attestPath with
  | .error e => return .error e
  | .ok (st, sigs) =>
    unless sigs.isEmpty do
      return .error s!"the envelope has {sigs.size} signature(s); signature verification is not \
        implemented yet (this prototype verifies unsigned statements only)"
    match strField? st "_type" with
    | some t => if t != statementType then return .error s!"unknown statement type {t}"
    | none => return .error "the statement has no _type"
    match strField? st "predicateType" with
    | some t =>
      if t != predicateType then
        return .error s!"unknown predicate type {t} (this wiz verifies {predicateType})"
    | none => return .error "the statement has no predicateType"
    let some (subjectName, subjectSha) := subjectDigest st | return .error "the statement has no subject digest"
    let some predicate := (st.getObjVal? "predicate").toOption | return .error "the statement has no predicate"
    let fmt := (natField? predicate "format").getD 0
    if fmt != predicateFormat then return .error s!"unsupported predicate format {fmt}"
    let some actual ← digestFile artifact | return .error s!"cannot read the artifact {artifact}"
    if actual != subjectSha then
      return .error s!"artifact mismatch: {artifact} is sha256:{actual}, the statement says sha256:{subjectSha}"
    let some out := (predicate.getObjVal? "output").toOption | return .error "the predicate has no output"
    let outName := (strField? out "name").getD ""
    if outName.isEmpty then return .error "the predicate has no output name"
    let some outSha := strField? out "sha256" | return .error "the predicate has no output digest"
    if outSha != actual then
      return .error s!"predicate.output.sha256 is {outSha}, the artifact is {actual}"
    let mut checked := 0
    if checkInputs then
      let some entries := arrField? predicate "inputs" | return .error "the predicate has no inputs manifest"
      let roots ← Module.roots tc.searchPath
      let mut recomputed : List Input := []
      for e in entries do
        let i ← match Input.ofJson e with
          | .ok i => pure i
          | .error err => return .error err
        let p ← match i.role with
          | "module" => match ← Module.resolve roots i.name with
            | some p => pure p
            | none => return .error s!"module {i.name} is not in the module roots (is -I missing?)"
          | _ => pure (FilePath.mk i.path)
        if !(← p.pathExists) then
          return .error s!"input {i.path} is missing (verify in the build tree, or use --artifact-only)"
        let some h ← digestFile p | return .error s!"cannot read the input {p}"
        if h != i.sha256 then
          return .error s!"input mismatch: {p} is sha256:{h}, the statement says sha256:{i.sha256}"
        recomputed := recomputed ++ [{ i with sha256 := h }]
        checked := checked + 1
      let sorted := recomputed.toArray.qsort (fun a b => a.lt b) |>.toList
      match strField? predicate "inputsRoot" with
      | some r =>
        if r != "sha256:" ++ inputsRoot sorted then
          return .error "the inputs manifest does not match its root (was it edited?)"
      | none => return .error "the predicate has no inputsRoot"
    -- generated C next to the artifact: if it is still there, it must match too
    if let some bp := arrField? predicate "byproducts" then
      for e in bp do
        let some name := strField? e "name" | continue
        let some want := strField? e "sha256" | continue
        let f := artifact.parent.getD "." / name
        if ← f.pathExists then
          let some h ← digestFile f | return .error s!"cannot read the byproduct {f}"
          if h != want then
            return .error s!"byproduct mismatch: {f} is sha256:{h}, the statement says sha256:{want}"
    let unsigned := if checked == 0 then "artifact only" else s!"{checked} inputs"
    return .ok s!"OK {subjectName}: sha256:{actual} ({unsigned}; unsigned statement)"

end Wiz.Attest
