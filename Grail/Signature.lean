import Grail.Index

/-!
# Signed index snapshots (stage 23m, Stage 1)

The static index is text, so a signature over the text is enough to make its state
authentic. One file, `index/snapshot.sexpr`, lists every published `name@version` with
its SHA-256 (and size), plus the index's `(seq …)`, `(updated …)`, the signing key's
fingerprint `(key "SHA256:…")` and the key's `(expires …)` date. A detached SSH
signature, `index/snapshot.sexpr.sig`, signs those bytes with
`ssh-keygen -Y sign -n grail-index`.

    (snapshot
      (name "wiz-pl/grail-index")
      (seq 7)
      (updated "2026-11-15T00:00:00Z")
      (key "SHA256:…")
      (expires "2027-11-15T00:00:00Z")
      (package "base" "0.1.0" "<sha256>" (size 1234))
      …)

Verification is local: `ssh-keygen -Y verify` against an `allowed_signers` file (or the
key a lock pinned) and the bytes of `snapshot.sexpr`. Nothing is fetched. A lock records
the verified fingerprint, key, sequence and snapshot digest, so a later update notices a
different key, a lower `(seq)`, or a rewrite of the same sequence. The snapshot's hash
chain ties every entry to the signature, and `covers` refuses an index whose entries
differ from it.

This is the snapshot variant of the first signing stage in
`wiz-notes/grail-index-signing.md`: one signature covers the whole index, and `(seq)` and
`(updated)` are the rollback and freshness signals. Transparency logs (Sigsum/Rekor) are
deliberately absent.
-/

namespace Grail
open Wiz Cache

/-- One `name@version` in a signed snapshot. `size` is the archive's length in bytes when
the generator could see the archive (`0`: unknown, for a remote source). -/
structure SnapshotEntry where
  name : String
  version : String
  sha256 : String
  size : Nat := 0
  deriving Repr, Inhabited, BEq

/-- `index/snapshot.sexpr`: the signed state of an index. -/
structure Snapshot where
  /-- the index's name, as `registry.sexpr` records it -/
  name : String := ""
  /-- a monotone sequence: a lower number than a lock's is a rollback -/
  seq : Nat := 0
  /-- when this snapshot was made (UTC, `YYYY-MM-DDTHH:MM:SSZ`) -/
  updated : String := ""
  /-- the signing key's fingerprint, `SHA256:…` -/
  key : String := ""
  /-- when the signing key stops being accepted (UTC) -/
  expires : String := ""
  packages : List SnapshotEntry := []
  deriving Repr, Inhabited, BEq

/-- The signature recorded in `grail.lock` (`(index-signature …)`): what was verified,
by whom, and the snapshot bytes it covered. -/
structure Signature where
  /-- `snapshot` (the only kind; a signed git tag is the alternative from the notes) -/
  kind : String := "snapshot"
  /-- the `allowed_signers` identity that signed it -/
  identity : String := ""
  /-- the signer's public key (an SSH key line), so a lock can verify offline later -/
  key : String := ""
  fingerprint : String := ""
  expires : String := ""
  seq : Nat := 0
  updated : String := ""
  /-- the SHA-256 of `snapshot.sexpr`'s bytes -/
  sha256 : String := ""
  deriving Repr, Inhabited, BEq

namespace Snapshot

/-- The snapshot's entries, sorted by name and then version. -/
def sorted (s : Snapshot) : List SnapshotEntry :=
  (s.packages.toArray.qsort fun a b =>
    a.name < b.name || (a.name == b.name && a.version < b.version)).toList

def render (s : Snapshot) : String :=
  let field (tag val : String) : Sx := node tag [str val]
  let pkg (e : SnapshotEntry) : Sx :=
    node "package" ([str e.name, str e.version, str e.sha256] ++
      (if e.size == 0 then [] else [node "size" [nat e.size]]))
  "(snapshot\n  " ++ "\n  ".intercalate
    ([ (field "name" s.name).render,
       (node "seq" [nat s.seq]).render,
       (field "updated" s.updated).render,
       (field "key" s.key).render,
       (field "expires" s.expires).render ] ++
     (sorted s).map fun e => (pkg e).render) ++ ")\n"

/-- Parse `index/snapshot.sexpr`. Unknown fields are ignored (forward compatibility), as
in the index entries. -/
def parse (text : String) : Except String Snapshot := do
  let some (.l xs) := Sx.parse text | throw "snapshot.sexpr: expected (snapshot …)"
  let fields ← match xs.toList with
    | .a "snapshot" :: rest => pure rest
    | _ => throw "snapshot.sexpr: expected (snapshot …)"
  let mut s : Snapshot := {}
  for f in fields do
    match f with
    | .l #[.a "name", .a v] => s := { s with name := v }
    | .l #[.a "seq", .a n] =>
      match n.toNat? with
      | some k => s := { s with seq := k }
      | none => throw s!"snapshot.sexpr: seq {n} is not a number"
    | .l #[.a "updated", .a v] => s := { s with updated := v }
    | .l #[.a "key", .a v] => s := { s with key := v }
    | .l #[.a "expires", .a v] => s := { s with expires := v }
    | .l ys =>
      match ys.toList with
      | .a "package" :: .a name :: .a version :: .a sha :: rest =>
        let mut size : Nat := 0
        for r in rest do
          match r with
          | .l #[.a "size", .a n] =>
            match n.toNat? with
            | some k => size := k
            | none => throw s!"snapshot.sexpr: size {n} is not a number"
          | _ => pure ()
        s := { s with packages := s.packages ++ [{ name, version, sha256 := sha, size }] }
      | _ => pure ()
    | _ => pure ()
  pure s

/-- The entry for `name@version`, if the snapshot lists it. -/
def find? (s : Snapshot) (name version : String) : Option SnapshotEntry :=
  s.packages.find? fun e => e.name == name && e.version == version

/-- The snapshot must describe exactly the index it signs: every entry's versions (with
their SHA-256s) must be listed, and every listed package must still be in the index.
A mismatch is either a stale signature or a hand-edited entry (mix-and-match). -/
def covers (s : Snapshot) (pkgs : Std.HashMap String IxPackage) : Except String Unit := do
  for (name, p) in pkgs.toList do
    for v in p.versions do
      let ver := Version.render v.version
      match s.find? name ver with
      | none => throw s!"the signed snapshot does not cover {name} {ver}"
      | some e =>
        if e.sha256 != v.sha256 then
          throw s!"the signed snapshot has {name} {ver} sha256 {e.sha256}, the index says {v.sha256}"
  for e in s.packages do
    match pkgs[e.name]? with
    | none => throw s!"the signed snapshot lists {e.name} {e.version}, which is not in the index"
    | some p =>
      unless p.versions.any (fun v => Version.render v.version == e.version) do
        throw s!"the signed snapshot lists {e.name} {e.version}, which is not in the index"

end Snapshot

namespace Signature

def node (s : Signature) : Sx :=
  let field (tag val : String) : Sx := Wiz.Cache.node tag [str val]
  Wiz.Cache.node "index-signature"
    ([field "kind" s.kind]
      ++ (if s.identity.isEmpty then [] else [field "identity" s.identity])
      ++ (if s.key.isEmpty then [] else [field "key" s.key])
      ++ (if s.fingerprint.isEmpty then [] else [field "fingerprint" s.fingerprint])
      ++ (if s.expires.isEmpty then [] else [field "expires" s.expires])
      ++ [Wiz.Cache.node "seq" [nat s.seq]]
      ++ (if s.updated.isEmpty then [] else [field "updated" s.updated])
      ++ (if s.sha256.isEmpty then [] else [field "sha256" s.sha256]))

/-- Parse the lock's `(index-signature …)` node; unknown fields are ignored. -/
def parse (x : Sx) : Except String Signature := do
  let .l xs := x | throw s!"grail.lock: expected (index-signature …), got {x.render}"
  let fields ← match xs.toList with
    | .a "index-signature" :: rest => pure rest
    | _ => throw s!"grail.lock: expected (index-signature …), got {x.render}"
  let mut s : Signature := {}
  for f in fields do
    match f with
    | .l #[.a "kind", .a v] => s := { s with kind := v }
    | .l #[.a "identity", .a v] => s := { s with identity := v }
    | .l #[.a "key", .a v] => s := { s with key := v }
    | .l #[.a "fingerprint", .a v] => s := { s with fingerprint := v }
    | .l #[.a "expires", .a v] => s := { s with expires := v }
    | .l #[.a "seq", .a n] =>
      match n.toNat? with
      | some k => s := { s with seq := k }
      | none => throw s!"grail.lock: index-signature seq {n} is not a number"
    | .l #[.a "updated", .a v] => s := { s with updated := v }
    | .l #[.a "sha256", .a v] => s := { s with sha256 := v }
    | _ => pure ()
  pure s

/-- 64 lowercase hex digits: the shape of a SHA-256 in the lock and the snapshot. -/
def isSha256 (s : String) : Bool :=
  s.length == 64 && s.toList.all fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- A lock must carry enough to verify the index offline: a key line, its fingerprint, a
positive sequence and the snapshot digest. -/
def checkFields (s : Signature) : Except String Unit := do
  if s.kind != "snapshot" then throw s!"grail.lock: unknown index signature kind {s.kind}"
  if s.fingerprint.isEmpty then throw "grail.lock: index signature has no fingerprint"
  unless s.fingerprint.startsWith "SHA256:" do
    throw s!"grail.lock: index signature fingerprint {s.fingerprint} is not SHA256:…"
  if s.key.isEmpty then throw "grail.lock: index signature has no signing key (cannot verify offline)"
  if s.seq == 0 then throw "grail.lock: index signature has no sequence"
  unless Signature.isSha256 s.sha256 do
    throw s!"grail.lock: index signature sha256 {s.sha256} is not 64 lowercase hex digits"

/-- A public key without its comment (`ssh-ed25519 AAAA… comment` → `ssh-ed25519 AAAA…`). -/
def keyBody (k : String) : String :=
  " ".intercalate ((k.splitOn " ").filter (!·.isEmpty) |>.take 2)

end Signature

namespace Sign

/-- Is `YYYY-MM-DDTHH:MM:SSZ` (the form the generator writes, and the only one whose
lexicographic order is its chronological order)? -/
def validUtc (s : String) : Bool :=
  let cs := s.toList.toArray
  cs.size == 20 &&
    (List.range 20).all fun i =>
      match cs[i]? with
      | some c =>
        if [4, 7, 10, 13, 16, 19].contains i then
          c == (match i with | 4 | 7 => '-' | 10 => 'T' | 13 | 16 => ':' | _ => 'Z')
        else c.isDigit
      | none => false

/-- The current time, in the snapshot's UTC form; used only for `(expires …)`. -/
def nowUtc : IO (Except String String) := do
  try
    let o ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
    if o.exitCode == 0 then
      let s := o.stdout.trimAscii.toString
      if validUtc s then return .ok s
    pure (.error s!"cannot read the current UTC time (date: {o.stderr.trimAscii})")
  catch e => pure (.error s!"cannot read the current UTC time: {e}")

/-- `index/snapshot.sexpr` (the documented layout) or `snapshot.sexpr` at the root. -/
def snapshotFile (root : System.FilePath) : IO (Option System.FilePath) := do
  for f in [root / "index" / "snapshot.sexpr", root / "snapshot.sexpr"] do
    if ← f.pathExists then return some f
  pure none

def sigFile (snap : System.FilePath) : System.FilePath :=
  System.FilePath.mk (snap.toString ++ ".sig")

/-- Quote one word for `sh` (single quotes; an embedded quote is `'\''`). -/
def shellQuote (s : String) : String :=
  "'" ++ s.replace "'" "'\\''" ++ "'"

/-- Run `cmd args` with `stdin` as the standard input, capturing stdout/stderr. The
redirection goes through `sh` because Lean's `IO.Process.Stdio` has no "open a file"
constructor; the command and arguments are single-quoted, so a path with spaces is safe. -/
def runStdin (cmd : String) (args : Array String) (stdin : System.FilePath) :
    IO (Except String (UInt32 × String × String)) := do
  let line := "exec " ++ shellQuote cmd ++ " " ++
    " ".intercalate (args.toList.map shellQuote) ++ " < " ++ shellQuote stdin.toString
  try
    let o ← IO.Process.output { cmd := "sh", args := #["-c", line] }
    pure (.ok (o.exitCode, o.stdout, o.stderr))
  catch e => pure (.error s!"{cmd}: {e}")

/-- The SHA-256 of a file (the signature covers exactly these bytes). -/
def sha256File (f : System.FilePath) : IO (Except String String) := do
  for cmd in [("sha256sum", #[]), ("shasum", #["-a", "256"])] do
    try
      let o ← IO.Process.output { cmd := cmd.1, args := cmd.2.push f.toString }
      if o.exitCode == 0 then
        match o.stdout.trimAscii.toString.splitOn " " with
        | h :: _ => return .ok h
        | [] => pure ()
    catch _ => pure ()
  pure (.error s!"no sha256sum (or shasum) to hash {f}")

/-- The key fingerprints a line of `allowed_signers` names. A line is
`identity[,identity…] [options] keytype base64 [comment]`. -/
def keyTypes : List String :=
  ["ssh-ed25519", "ssh-rsa", "ssh-dss", "ecdsa-sha2-nistp256", "ecdsa-sha2-nistp384",
   "ecdsa-sha2-nistp521", "sk-ssh-ed25519@openssh.com", "sk-ecdsa-sha2-nistp256@openssh.com"]

/-- `(identities, key line)` for one `allowed_signers` line, if it has a key. -/
def allowedLine (line : String) : Option (List String × String) := do
  let line := line.trimAscii.toString
  guard (!line.isEmpty && !line.startsWith "#")
  let toks := (line.splitOn " ").filter (!·.isEmpty)
  let first ← toks[0]?
  let idx ← (List.range toks.length).find? fun i =>
    (toks[i]?).any (fun t => keyTypes.contains t)
  let keyType ← toks[idx]?
  let b64 ← toks[idx + 1]?
  pure (first.splitOn ",", keyType ++ " " ++ b64)

/-- Every key in an `allowed_signers` file. -/
def allowedKeys (file : System.FilePath) : IO (Except String (List (List String × String))) := do
  let text ← IO.FS.readFile file
  pure (.ok (text.splitOn "\n" |>.filterMap allowedLine))

/-- The fingerprint `ssh-keygen -lf` reports for a public key line. -/
def fingerprintOf (key : String) : IO (Except String String) := do
  let dir ← IO.FS.createTempDir
  let f := dir / "key.pub"
  IO.FS.writeFile f (key ++ "\n")
  let o ← IO.Process.output { cmd := "ssh-keygen", args := #["-lf", f.toString, "-E", "sha256"] }
  IO.FS.removeDirAll dir
  if o.exitCode != 0 then
    return .error s!"ssh-keygen -lf: {o.stderr.trimAscii}"
  let fp := (o.stdout.trimAscii.toString.splitOn " ").find? (·.startsWith "SHA256:")
  match fp with
  | some f => pure (.ok f)
  | none => pure (.error s!"ssh-keygen -lf: no SHA256 fingerprint in {o.stdout.trimAscii}")

/-- Parse `ssh-keygen -Y verify`'s success line:
`Good "grail-index" signature for ID with ED25519 key SHA256:…`. -/
def verifyOutput (out : String) : Option (String × String) := do
  let line ← out.splitOn "\n" |>.find? fun l =>
    l.startsWith "Good \"grail-index\" signature for "
  let rest ← (line.splitOn " signature for ")[1]?
  let id ← (rest.splitOn " with ")[0]?
  let tail ← (rest.splitOn " key ").getLast?
  let fp ← (tail.splitOn " ")[0]?
  pure (id, fp)

/-- Verify `snapshot.sexpr`'s detached SSH signature. `allowed` is a trust root
(`--allowed-signers`); otherwise a lock's pinned key is used, and failing that an
`allowed_signers` file in the index repository. The pinned signature makes the check
offline: the lock already has the public key. With `allowRewind`, a lower `(seq)` is
accepted (a deliberate rewind), but a rewrite at the same sequence is not. -/
def verifySnapshot (root : System.FilePath) (allowed : Option System.FilePath)
    (pinned : Option Signature) (allowRewind : Bool := false) :
    IO (Except String (Snapshot × Signature)) := do
  let some snapPath ← snapshotFile root
    | return .error "the index has no signed snapshot (index/snapshot.sexpr): cannot check its signature"
  let text ← IO.FS.readFile snapPath
  let snap ← match Snapshot.parse text with
    | .ok s => pure s
    | .error e => return .error e
  if snap.seq == 0 then return .error "snapshot.sexpr has no (seq N): a signed snapshot needs a sequence (rollback protection)"
  if snap.key.isEmpty then return .error "snapshot.sexpr has no (key \"SHA256:…\"): the signing key's fingerprint is missing"
  if snap.expires.isEmpty then return .error "snapshot.sexpr has no (expires …): a signed snapshot needs an expiry date"
  let sigPath := sigFile snapPath
  unless ← sigPath.pathExists do
    return .error s!"{sigPath}: no signature (sign the snapshot with ssh-keygen -Y sign -n grail-index)"
  -- the trust root: an explicit allowed signers file, else the lock's pinned key, else
  -- the index repository's own allowed_signers (a convenience for a checkout or mirror)
  let mut tmp : Option System.FilePath := none
  let allowedFile : System.FilePath ←
    match allowed with
    | some f =>
      unless ← f.pathExists do return .error s!"--allowed-signers: {f}: no such file"
      pure f
    | none =>
      match pinned with
      | some p =>
        if p.key.isEmpty then
          return .error "--require-signature: grail.lock records no signing key; pass --allowed-signers FILE"
        let d ← IO.FS.createTempDir
        tmp := some d
        let f := d / "allowed_signers"
        IO.FS.writeFile f s!"{if p.identity.isEmpty then "pinned" else p.identity} {p.key}\n"
        pure f
      | none =>
        -- a trust root shipped inside the tree being verified proves nothing (whoever
        -- can rewrite the snapshot can rewrite that file too): first use needs a policy
        -- from outside, or a lock that already pinned the key.
        return .error "no trust root for the index signature: pass --allowed-signers FILE (or use a grail.lock that pinned the signature)"
  -- `ssh-keygen -Y verify` selects one identity with -I. A lock pins the identity;
  -- otherwise try every identity the allowed_signers file names (a first use has no
  -- baseline, and the file is the policy).
  let ids : List String ←
    match pinned with
    | some p => pure [if p.identity.isEmpty then "pinned" else p.identity]
    | none =>
      match ← allowedKeys allowedFile with
      | .error e => return .error e
      | .ok keys => pure ((keys.flatMap fun (ids, _) => ids).eraseDups)
  if ids.isEmpty then return .error s!"{allowedFile}: no identities to verify"
  let mut good : Option (String × String) := none
  let mut failure := ""
  for id in ids do
    if good.isNone then
      match ← runStdin "ssh-keygen"
          #["-Y", "verify", "-f", allowedFile.toString, "-I", id,
            "-n", "grail-index", "-s", sigPath.toString] snapPath with
      | .error e => failure := e
      | .ok (code, out, err) =>
        if code == 0 then
          match verifyOutput out with
          | some pair => good := some pair
          | none => failure := s!"ssh-keygen -Y verify: unexpected output {out.trimAscii}"
        else
          failure := (if err.trimAscii.toString.isEmpty then out else err).trimAscii.toString
  if let some d := tmp then IO.FS.removeDirAll d
  let some (id, fp) := good
    | return .error s!"the index signature is not valid: {failure}"
  if snap.key != fp then
      return .error s!"snapshot.sexpr names key {snap.key}, but {sigPath} was signed by {fp}"
    if let some p := pinned then
      if !p.fingerprint.isEmpty && p.fingerprint != fp then
        return .error s!"the index is signed by {fp}, but grail.lock pins {p.fingerprint} (key change; re-lock deliberately)"
      if !p.identity.isEmpty && p.identity != id then
        return .error s!"the index is signed by {id}, but grail.lock pins {p.identity}"
    let now ← nowUtc
    let now ← match now with
      | .ok t => pure t
      | .error e => return .error s!"cannot check the snapshot's expiry: {e}"
    unless validUtc snap.expires do
      return .error s!"snapshot.sexpr: expires {snap.expires} is not a UTC date (YYYY-MM-DDTHH:MM:SSZ)"
    if snap.expires ≤ now then
      return .error s!"the index signing key expired at {snap.expires} (now {now})"
    let sha ← match ← sha256File snapPath with
      | .ok h => pure h
      | .error e => return .error e
    -- find the signing key: the allowed line for `id`, or the pinned key
    let signingKey ←
      match pinned with
      | some p => pure p.key
      | none =>
        match ← allowedKeys allowedFile with
        | .error e => return .error e
        | .ok keys =>
          let some (_, key) := keys.find? (fun (ids, _) => ids.contains id)
            | return .error s!"{allowedFile}: no key for identity {id}"
          pure key
    if let some p := pinned then
      if !p.key.isEmpty && Signature.keyBody p.key != Signature.keyBody signingKey then
        return .error "the index signing key is not the key grail.lock pinned (key change; re-lock deliberately)"
      if snap.seq < p.seq then
        if !allowRewind then
          return .error s!"the signed snapshot rolled back (seq {snap.seq}, the lock has seq {p.seq}); pass --allow-rewind to accept"
      if snap.seq == p.seq && !p.sha256.isEmpty && p.sha256 != sha then
        return .error s!"the signed snapshot was rewritten at seq {snap.seq} (sha256 {sha}, the lock has {p.sha256})"
    pure (.ok (snap, {
      kind := "snapshot", identity := id, key := Signature.keyBody signingKey,
      fingerprint := fp, expires := snap.expires, seq := snap.seq,
      updated := snap.updated, sha256 := sha }))

end Sign

namespace Sign

/-- A `source` relative to `root` (the same rule as the index reader: a URL or an
absolute path is not touched). -/
def sourcePath (root : System.FilePath) (s : String) : String :=
  if s.isEmpty || s.contains "://" || s.startsWith "/" then s
  else (root / s).toString

/-- Build a snapshot from every entry of an index. Local archives contribute their size;
a remote (`https://`) source contributes `size 0` (unknown). The caller supplies the
sequence, timestamp, key fingerprint and expiry; `render` is deterministic. -/
def ofIndex (root : System.FilePath) (name : String)
    (pkgs : Std.HashMap String IxPackage) (seq : Nat) (updated key expires : String) :
    IO Snapshot := do
  let mut entries : List SnapshotEntry := []
  for (pname, p) in pkgs.toList do
    for v in p.versions do
      let mut size : Nat := 0
      let src := sourcePath root v.source
      let path : System.FilePath :=
        if src.startsWith "file://" then src.drop 7 |>.toString else src
      if !src.startsWith "http://" && !src.startsWith "https://" && (← path.pathExists) then
        match ← (try some <$> path.metadata catch _ => pure none) with
        | some md => size := md.byteSize.toNat
        | none => pure ()
      entries := entries ++ [{ name := pname, version := Version.render v.version,
                               sha256 := v.sha256, size }]
  pure { name, seq, updated, key, expires, packages := entries }

/-- The index's name from `registry.sexpr` (empty when there is no such file). -/
def registryName (root : System.FilePath) : IO String := do
  let f := root / "registry.sexpr"
  if !(← f.pathExists) then return ""
  match Sx.parse (← IO.FS.readFile f) with
  | some (.l xs) =>
    match xs.toList with
    | .a "registry" :: fields =>
      for field in fields do
        match field with
        | .l #[.a "name", .a n] => return n
        | _ => pure ()
      return ""
    | _ => return ""
  | _ => return ""

/-- The next sequence for a new snapshot: one more than the existing file's, or 1. -/
def nextSeq (root : System.FilePath) : IO Nat := do
  let some f ← Sign.snapshotFile root | return 1
  match Snapshot.parse (← IO.FS.readFile f) with
  | .ok s => pure (s.seq + 1)
  | .error _ => pure 1

end Sign

namespace Snapshot

/-- The selected versions must be the ones the signed snapshot lists (by name, version
and SHA-256). The resolver's selection is one version per name; the snapshot covers the
whole index, so a stale entry cannot slip in. -/
def checkResolved (s : Snapshot) (rs : List Resolved) : Except String Unit := do
  for r in rs do
    let ver := Version.render r.version
    match s.find? r.name ver with
    | none => throw s!"the signed snapshot does not cover the selected {r.name} {ver}"
    | some e =>
      if e.sha256 != r.sha256 then
        throw s!"{r.name} {ver}: the signed snapshot has sha256 {e.sha256}, the index says {r.sha256}"

end Snapshot

end Grail
