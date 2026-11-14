/-
# Witnessed transparency log for cache generations (P4)

A signed generation index (`manifest.sexpr` + `manifest.sexpr.sig`) makes one layer
authentic, but it does not stop a writer from serving two different signed generations to
two clients (a split view), nor a mirror from replaying an older signed generation. This
module adds the missing piece: an **append-only, signed log** of generation indices, an
RFC 6962 inclusion proof for any entry, a `prev` hash chain, and an **offline monitor**
that compares the log with a local **witness** file.

The log is a local file, not a public service. That is a deliberate limit: without
independent witnesses or a public log (Sigsum, Rekor), a log detects a mirror that cannot
rewrite the witness; it cannot detect an equivocating writer who controls every witness.
`docs/cache-transparency.md` gives the Sigsum/Rekor mapping and the exact trust statement.

Layout (inside one cache layer):

```
<cache>/log/entries/00000000.sexpr       one generation, exact bytes
<cache>/log/entries/00000000.sexpr.sig   SSHSIG over those bytes
<cache>/log/checkpoint.sexpr             signed tree head (size, root, head, generation)
<cache>/log/checkpoint.sexpr.sig         SSHSIG over the checkpoint
```

`<witness>` is a separate file (normally outside the cache) holding the last checkpoint a
monitor accepted. The log is append-only by construction: a new entry names the SHA-256 of
the previous entry's bytes in `prev`, and `append` refuses a generation that is not newer
than the logged one or that does not descend from the logged root.
-/

import Wiz.Cache

namespace Wiz.Cache

/-! ## File names and small helpers -/

/-- Directory holding a layer's transparency log. -/
def logDirName : String := "log"

/-- Entries are one file per index, under `log/entries`. -/
def logEntriesName : String := "entries"

/-- The SSHSIG namespace of log entries and checkpoints. Changing it invalidates every
existing log signature. -/
def transparencyNamespace : String := "wiz-cache-transparency"

/-- The leaf domain of a log entry (RFC 6962 leaf separation, with a Wiz label). -/
def logEntryDomain : String := "wiz-log-entry-v1"

def logDir (dir : System.FilePath) : System.FilePath := dir / logDirName
def logEntriesDir (dir : System.FilePath) : System.FilePath := logDir dir / logEntriesName
def checkpointFile (dir : System.FilePath) : System.FilePath := logDir dir / "checkpoint.sexpr"
def checkpointSigFile (dir : System.FilePath) : System.FilePath :=
  System.FilePath.mk ((checkpointFile dir).toString ++ ".sig")

/-- Zero-pad an index to eight digits, so file-name order is index order. -/
def padIndex (n : Nat) : String :=
  let s := toString n
  let k := 8 - s.length
  String.ofList (List.replicate (if k > 0 then k else 0) '0') ++ s

/-- The entry file for index `i`. -/
def entryFile (dir : System.FilePath) (i : Nat) : System.FilePath :=
  logEntriesDir dir / s!"{padIndex i}.sexpr"

/-- The signature file of entry `i` (written by `ssh-keygen -Y sign` beside its payload). -/
def entrySigFile (dir : System.FilePath) (i : Nat) : System.FilePath :=
  System.FilePath.mk ((entryFile dir i).toString ++ ".sig")

/-- Parse a hexadecimal digest (64 hex digits for SHA-256). Used by inclusion proofs, which
store digests as text in an S-expression. -/
def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

partial def hexToBytes? (s : String) : Option ByteArray :=
  let rec go (cs : List Char) (acc : ByteArray) : Option ByteArray :=
    match cs with
    | [] => some acc
    | a :: b :: rest => do
        let x ← hexDigit? a
        let y ← hexDigit? b
        go rest (acc.push (UInt8.ofNat (16 * x + y)))
    | _ => none
  go s.toList .empty

/-- Lower-case hexadecimal, for digests computed by `nodeHash` (which returns raw bytes). -/
def hexOfBytes (bytes : ByteArray) : String := Id.run do
  let digit (n : Nat) : Char := "0123456789abcdef".toList[n]!
  let mut out := ""
  for byte in bytes do
    out := out.push (digit (byte.toNat >>> 4)) |>.push (digit (byte.toNat % 16))
  pure out

/-- Sign `payload` in `namespace`, leaving `payload.sig` beside it (OpenSSH's behaviour).
Nothing is written when `ssh-keygen` fails; the caller decides whether to remove a payload
whose signature could not be made. -/
def signDetachedFile (payload key : System.FilePath) (ns : String) :
    IO (Except String System.FilePath) := do
  let sig := System.FilePath.mk (payload.toString ++ ".sig")
  removeQuietly sig
  let o ← try
      IO.Process.output { cmd := "ssh-keygen", args := #["-Y", "sign", "-q", "-f", key.toString, "-n", ns, payload.toString] }
    catch e => return .error s!"ssh-keygen: {e}"
  if o.exitCode != 0 then
    return .error s!"ssh-keygen -Y sign failed: {o.stderr.trimAscii.toString}"
  unless ← sig.pathExists do
    return .error "ssh-keygen wrote no signature file"
  pure (.ok sig)

/-- Verify `sig` over the exact bytes of `payload` with an OpenSSH `allowed_signers` file.
With no `keyId`, every listed principal is tried; a `SHA256:` principal must also be the
actual fingerprint of its line's key. This is `verifySignatureWith` with the payload,
signature and namespace made explicit (the generation index is one caller of it; log
entries and the checkpoint are others). -/
def verifyDetachedFile (payload sig signers : System.FilePath) (ns : String)
    (keyId : Option String) : IO (Except String (String × String)) := do
  let payloadText ← IO.FS.readFile payload
  let keys ← readSigners signers
  let mut detail := ""
  for s in keys do
    for id in s.identities do
      if keyId.isNone || keyId == some id then
        let fpOk ← if id.startsWith "SHA256:" then
            match ← sshPublicFingerprint s.keyType s.key with
            | some fp => pure (fp == id)
            | none => pure false
          else pure true
        if fpOk then
          let o ← IO.Process.output { cmd := "ssh-keygen", args := #["-Y", "verify", "-f", signers.toString, "-I", id, "-n", ns, "-s", sig.toString] } (some payloadText)
          if o.exitCode == 0 then
            let fp ← sshPublicFingerprint s.keyType s.key
            return .ok (id, fp.getD "")
          else
            detail := o.stderr.trimAscii.toString
  pure (.error (if detail.isEmpty then s!"no allowlisted key verified {sig}" else detail))

/-! ## Log entries -/

/-- One generation, as it enters the log. `prev` is the SHA-256 of the previous entry's
exact bytes (`""` for the first entry), so the entries form a hash chain. `manifest` and
`manifestSig` are the SHA-256 digests of the signed generation index and its signature;
`root` is the index's own Merkle root, which the next generation's `prev` must name. -/
structure LogEntry where
  format : Nat := 1
  index : Nat := 0
  prev : String := ""
  generation : Nat := 0
  root : String := ""
  manifest : String := ""
  manifestSig : String := ""
  validUntil : Nat := 0
  timestamp : Nat := 0
  deriving Repr, Inhabited

def LogEntry.toSx (e : LogEntry) : Sx :=
  node "log-entry" [
    node "format" [nat e.format],
    node "index" [nat e.index],
    node "prev" [str e.prev],
    node "generation" [nat e.generation],
    node "root" [str e.root],
    node "manifest" [str e.manifest],
    node "manifest-sig" [str e.manifestSig],
    node "valid-until" [nat e.validUntil],
    node "timestamp" [nat e.timestamp]]

def LogEntry.ofSx? (x : Sx) : Option LogEntry := do
  let v ← sxField? "format" x
  let format ← (← atom? v).toNat?
  let v ← sxField? "index" x
  let index ← (← atom? v).toNat?
  let prev ← match ← sxField? "prev" x with | .a s => pure s | _ => pure ""
  let v ← sxField? "generation" x
  let generation ← (← atom? v).toNat?
  let v ← sxField? "root" x
  let root ← atom? v
  let v ← sxField? "manifest" x
  let manifest ← atom? v
  let manifestSig ← match ← sxField? "manifest-sig" x with | .a s => pure s | _ => pure ""
  let validUntil ← match ← sxField? "valid-until" x with
    | .a s => pure (s.toNat?.getD 0) | _ => pure 0
  let timestamp ← match ← sxField? "timestamp" x with
    | .a s => pure (s.toNat?.getD 0) | _ => pure 0
  pure { format, index, prev, generation, root, manifest, manifestSig, validUntil, timestamp }

/-- The exact bytes of an entry: canonical S-expression and a newline. The hash chain and
the Merkle leaf both cover these bytes, so no re-serialization happens during verification. -/
def LogEntry.text (e : LogEntry) : String := e.toSx.render ++ "\n"

def LogEntry.bytes (e : LogEntry) : ByteArray := e.text.toUTF8

/-- The RFC 6962 leaf hash of an entry's bytes. -/
def logLeaf (bytes : ByteArray) : ByteArray := leafHash logEntryDomain bytes

/-- One entry as read from disk, with the exact bytes the digest names. -/
structure LogFile where
  index : Nat := 0
  bytes : ByteArray := .empty
  entry : LogEntry := {}
  deriving Inhabited

/-- Read every entry of a layer's log in index order. A gap, an unparsable entry, or a file
whose own `index` is not its position is an error (never silently skipped). -/
def readLogFiles (dir : System.FilePath) : IO (Except String (Array LogFile)) := do
  let d := logEntriesDir dir
  if !(← d.pathExists) then return .ok #[]
  let es ← d.readDir
  let names := (es.filter (fun e => e.fileName.endsWith ".sexpr")).qsort
    (fun a b => a.fileName < b.fileName)
  let mut out := #[]
  let mut pos := 0
  for e in names do
    let bytes ← try pure (← IO.FS.readBinFile e.path)
      catch err => return .error s!"log entry {e.fileName}: {err}"
    let text := (String.fromUTF8? bytes).getD ""
    let some entry := (Sx.parse text).bind LogEntry.ofSx?
      | return .error s!"log entry {e.fileName}: not a log entry"
    if entry.format != 1 then
      return .error s!"log entry {e.fileName}: unsupported format {entry.format}"
    if entry.index != pos then
      return .error s!"log entry {e.fileName}: index {entry.index} at position {pos}"
    out := out.push { index := pos, bytes, entry }
    pos := pos + 1
  pure (.ok out)

/-- Check the `prev` chain and the generation monotonicity of a sequence of entries. The
first entry must name the genesis (`prev = ""`); every later entry must name the SHA-256 of
its predecessor's exact bytes, and its generation must be strictly larger. -/
def checkChain (fs : Array LogFile) : Except String Unit := do
  for i in [0:fs.size] do
    let f := fs[i]!
    if i == 0 then
      unless f.entry.prev == "" do
        throw s!"entry 0: prev is not the genesis ({f.entry.prev})"
    else
      let p := fs[i - 1]!
      let want := Smt.Sha256.hexBytes p.bytes
      unless f.entry.prev == want do
        throw s!"entry {i}: prev does not name entry {i - 1}"
      unless p.entry.generation < f.entry.generation do
        throw s!"entry {i}: generation {f.entry.generation} is not newer than {p.entry.generation}"

/-- The Merkle root over the log entries (RFC 6962 shapes). -/
def logRoot (fs : Array LogFile) : String :=
  Smt.Sha256.hexBytes (merkleRoot (fs.map fun f => logLeaf f.bytes))

/-- The SHA-256 of the last entry's bytes (`""` for an empty log); this is the value the
next entry's `prev` and the witness record. -/
def logHead (fs : Array LogFile) : String :=
  match fs.back? with
  | some f => Smt.Sha256.hexBytes f.bytes
  | none => ""

/-! ## The signed checkpoint (tree head) -/

/-- A signed tree head over the log: its size, Merkle root, the hash of its last entry,
and the latest cache generation it names. One signature over this value is enough to pin
the whole history. -/
structure Checkpoint where
  format : Nat := 1
  size : Nat := 0
  root : String := ""
  head : String := ""
  generation : Nat := 0
  timestamp : Nat := 0
  deriving Repr, Inhabited

def Checkpoint.toSx (c : Checkpoint) : Sx :=
  node "checkpoint" [
    node "format" [nat c.format],
    node "size" [nat c.size],
    node "root" [str c.root],
    node "head" [str c.head],
    node "generation" [nat c.generation],
    node "timestamp" [nat c.timestamp]]

def Checkpoint.ofSx? (x : Sx) : Option Checkpoint := do
  let v ← sxField? "format" x
  let format ← (← atom? v).toNat?
  let v ← sxField? "size" x
  let size ← (← atom? v).toNat?
  let v ← sxField? "root" x
  let root ← atom? v
  let head ← match ← sxField? "head" x with | .a s => pure s | _ => pure ""
  let v ← sxField? "generation" x
  let generation ← (← atom? v).toNat?
  let timestamp ← match ← sxField? "timestamp" x with
    | .a s => pure (s.toNat?.getD 0) | _ => pure 0
  pure { format, size, root, head, generation, timestamp }

def Checkpoint.text (c : Checkpoint) : String := c.toSx.render ++ "\n"

/-- The checkpoint that commits to `fs`. -/
def Checkpoint.ofLog (fs : Array LogFile) (timestamp : Nat) : Checkpoint :=
  { size := fs.size
    root := logRoot fs
    head := logHead fs
    generation := (fs.back?).map (·.entry.generation) |>.getD 0
    timestamp }

def readCheckpoint (dir : System.FilePath) : IO (Option Checkpoint) := do
  let f := checkpointFile dir
  if ← f.pathExists then
    try
      match (Sx.parse (← IO.FS.readFile f)).bind Checkpoint.ofSx? with
      | some c => pure (if c.format == 1 then some c else none)
      | none => pure none
    catch _ => pure none
  else pure none

/-- What `wiz cache log append` did. -/
structure AppendResult where
  index : Nat := 0
  entries : Nat := 0
  generation : Nat := 0
  root : String := ""
  checkpoint : System.FilePath := ""
  deriving Repr, Inhabited

/-- Append the layer's current signed generation index to its log, sign the new entry and
the new checkpoint, and leave the log ready for the next generation.

The preconditions are the rollback checks: the index must exist and be signed, its
generation must be strictly newer than the logged one, and its `prev` must name the last
logged index root (a re-sealed index that descends from a different history is refused).
`--signers` also re-verifies the index signature before logging it. The log is written to
the layer it is given; only a writable layer should be passed here. -/
def appendEntry (dir : System.FilePath) (key : System.FilePath)
    (keyId : Option String := none) (signers : Option System.FilePath := none) :
    IO (Except String AppendResult) := do
  let genF := generationFile dir
  unless ← genF.pathExists do
    return .error s!"no {genF} (run 'wiz cache manifest' first)"
  let some g ← readGeneration dir
    | return .error s!"{genF} is not a self-consistent generation index"
  let sigF := signatureFile dir
  unless ← sigF.pathExists do
    return .error "the generation index is not signed (run 'wiz cache sign' first)"
  if let some signers := signers then
    let r ← try verifyDetachedFile genF sigF signers signatureNamespace keyId
      catch e => pure (.error s!"{e}")
    match r with
    | .error e => return .error s!"manifest signature: {e}"
    | .ok _ => pure ()
  let logRes ← readLogFiles dir
  let fs ← match logRes with
    | .ok fs => pure fs
    | .error e => return .error e
  match checkChain fs with
  | .error e => return .error e
  | .ok () => pure ()
  if let some last := fs.back? then
    if g.generation <= last.entry.generation then
      return .error s!"generation {g.generation} is not newer than logged generation {last.entry.generation}"
    unless g.prev == last.entry.root do
      return .error (s!"the generation index does not descend from the logged head: " ++
        s!"prev {g.prev} is not {last.entry.root} (fork or rollback)")
  let index := fs.size
  let gbytes ← try pure (← IO.FS.readBinFile genF) catch e => return .error s!"{genF}: {e}"
  let sbytes ← try pure (← IO.FS.readBinFile sigF) catch e => return .error s!"{sigF}: {e}"
  let entry : LogEntry := {
    index
    prev := if let some last := fs.back? then Smt.Sha256.hexBytes last.bytes else ""
    generation := g.generation
    root := g.root
    manifest := Smt.Sha256.hexBytes gbytes
    manifestSig := Smt.Sha256.hexBytes sbytes
    validUntil := g.validUntil
    timestamp := ← unixNow }
  let ef := entryFile dir index
  IO.FS.createDirAll (logEntriesDir dir)
  writeAtomic ef entry.text
  match ← signDetachedFile ef key transparencyNamespace with
  | .error e => removeQuietly ef; return .error e
  | .ok _ => pure ()
  let fs' := fs.push { index, bytes := entry.bytes, entry }
  let cp := Checkpoint.ofLog fs' (← unixNow)
  let cpRes : Except String Unit ← try
      IO.FS.createDirAll (logDir dir)
      writeAtomic (checkpointFile dir) cp.text
      match ← signDetachedFile (checkpointFile dir) key transparencyNamespace with
      | .error e => pure (.error e)
      | .ok _ => pure (.ok ())
    catch e => pure (.error s!"{e}")
  match cpRes with
  | .ok () => pure ()
  | .error e =>
    -- (the checkpoint is what commits the entry; an uncommitted entry must not stay,
    -- or a retry would look like a duplicate generation)
    removeQuietly ef
    removeQuietly (entrySigFile dir index)
    removeQuietly (checkpointFile dir)
    removeQuietly (checkpointSigFile dir)
    return .error s!"entry {index} was rolled back: the checkpoint could not be signed: {e}"
  pure (.ok { index, entries := fs'.size, generation := g.generation, root := g.root,
              checkpoint := checkpointFile dir })

/-! ## Inclusion proofs -/

/-- An RFC 6962 audit path for one leaf. `leaf` is the leaf hash; each path element is a
sibling digest and whether that sibling is on the left. -/
structure InclusionProof where
  format : Nat := 1
  index : Nat := 0
  size : Nat := 0
  leaf : String := ""
  path : Array (Bool × String) := #[]
  deriving Repr, Inhabited

def InclusionProof.toSx (p : InclusionProof) : Sx :=
  node "inclusion-proof" [
    node "format" [nat p.format],
    node "index" [nat p.index],
    node "size" [nat p.size],
    node "leaf" [str p.leaf],
    node "path" [list (p.path.toList.map fun (left, h) =>
      node (if left then "left" else "right") [str h])]]

def InclusionProof.ofSx? (x : Sx) : Option InclusionProof := do
  let v ← sxField? "format" x
  let format ← (← atom? v).toNat?
  let v ← sxField? "index" x
  let index ← (← atom? v).toNat?
  let v ← sxField? "size" x
  let size ← (← atom? v).toNat?
  let v ← sxField? "leaf" x
  let leaf ← atom? v
  let path ← match ← sxField? "path" x with
    | .l xs => xs.filterMapM fun y => do
        let ys ← items? y
        match ys.toList with
        | .a tag :: .a h :: _ =>
          if tag == "left" then pure (true, h)
          else if tag == "right" then pure (false, h)
          else none
        | _ => none
    | _ => pure #[]
  pure { format, index, size, leaf, path }

def parseInclusionProof (text : String) : Option InclusionProof :=
  (Sx.parse text).bind InclusionProof.ofSx?

/-- The audit path of leaf `i`, siblings ordered from the leaf to the root. `partial`: the
recursion follows the RFC 6962 split, not a structural subterm. -/
partial def auditPath (hs : Array ByteArray) (i : Nat) : Array (Bool × String) :=
  if hs.size ≤ 1 then #[]
  else
    let k := largestPow2Lt hs.size
    if i < k then
      (auditPath (hs.extract 0 k) i).push
        (false, hexOfBytes (merkleRoot (hs.extract k hs.size)))
    else
      (auditPath (hs.extract k hs.size) (i - k)).push
        (true, hexOfBytes (merkleRoot (hs.extract 0 k)))

/-- Recompute the root named by a proof. `none` when a digest is not 64 hex digits. -/
def InclusionProof.computeRoot (p : InclusionProof) : Option String := do
  let leaf ← hexToBytes? p.leaf
  let rec go (h : ByteArray) (ps : List (Bool × String)) : Option ByteArray :=
    match ps with
    | [] => some h
    | (left, sib) :: rest => do
        let s ← hexToBytes? sib
        go (if left then nodeHash s h else nodeHash h s) rest
  pure (Smt.Sha256.hexBytes (← go leaf p.path.toList))

/-- Verify that `entryBytes` is leaf `p.index` of the tree whose signed checkpoint is
`cp`. A proof whose recomputed root is not the checkpoint's root, or whose leaf is not the
entry's leaf hash, is rejected. -/
def verifyInclusion (p : InclusionProof) (cp : Checkpoint) (entryBytes : ByteArray) :
    Except String Unit := do
  unless p.format == 1 do throw s!"unsupported proof format {p.format}"
  unless p.index < p.size do throw s!"proof index {p.index} is not below size {p.size}"
  unless p.size == cp.size do throw s!"proof size {p.size} does not match checkpoint size {cp.size}"
  let leaf := hexOfBytes (logLeaf entryBytes)
  unless p.leaf == leaf do throw "proof leaf does not name the entry"
  let some root := p.computeRoot | throw "proof contains a malformed digest"
  unless root == cp.root do throw s!"proof root {root} does not match checkpoint root {cp.root}"

/-- Build the inclusion proof for entry `index` of a layer's log. -/
def proveLog (dir : System.FilePath) (index : Nat) :
    IO (Except String InclusionProof) := do
  match ← readLogFiles dir with
  | .error e => pure (.error e)
  | .ok fs =>
    if index >= fs.size then
      return .error s!"no entry {index} (the log has {fs.size})"
    let leaf := hexOfBytes (logLeaf fs[index]!.bytes)
    pure (.ok { index, size := fs.size, leaf, path := auditPath (fs.map (fun f => logLeaf f.bytes)) index })

/-! ## Verifying a log -/

/-- What `checkLog` found. `errors` empty means the chain, every entry signature, the
checkpoint and (when the layer has one) the signed generation index are consistent.
`current` says the generation index is the latest logged one; `behind` says it is newer, so
`wiz cache log append` has not run yet. -/
structure LogStatus where
  entries : Nat := 0
  generation : Nat := 0
  root : String := ""
  head : String := ""
  checkpointKey : String := ""
  behind : Bool := false
  current : Bool := false
  errors : Array String := #[]
  deriving Repr, Inhabited

def LogStatus.ok (s : LogStatus) : Bool := s.errors.isEmpty && !s.behind

/-- Verify a layer's transparency log offline: entry order and `prev` chain, every entry
signature under `allowed_signers`, the checkpoint against the entries and its signature,
and that the layer's current signed generation index is exactly the latest entry. -/
def checkLog (dir : System.FilePath) (signers : System.FilePath)
    (keyId : Option String := none) : IO LogStatus := do
  match ← readLogFiles dir with
  | .error e => pure { errors := #[e] }
  | .ok fs =>
    if fs.isEmpty then
      return { errors := #["the log has no entries"] }
    let last := fs.back!
    let mut st : LogStatus := { entries := fs.size, generation := last.entry.generation,
                                root := logRoot fs, head := logHead fs }
    let mut errors : Array String := #[]
    match checkChain fs with
    | .error e => errors := errors.push e
    | .ok () => pure ()
    -- (every entry is signed; the signature is over the exact bytes on disk)
    for i in [0:fs.size] do
      let sp := entrySigFile dir i
      if !(← sp.pathExists) then
        errors := errors.push s!"entry {i}: no signature ({sp})"
      else
        let r ← try verifyDetachedFile (entryFile dir i) sp signers transparencyNamespace keyId
          catch e => pure (.error s!"{e}")
        match r with
        | .error e => errors := errors.push s!"entry {i}: {e}"
        | .ok (id, _) => if i == fs.size - 1 then st := { st with checkpointKey := id }
    -- (the checkpoint must name exactly these entries, and be signed)
    match ← readCheckpoint dir with
    | none => errors := errors.push "no checkpoint (missing or unparsable)"
    | some cp =>
      let want := Checkpoint.ofLog fs cp.timestamp
      unless cp.size == want.size && cp.root == want.root && cp.head == want.head &&
          cp.generation == want.generation do
        errors := errors.push "checkpoint does not match the log entries"
      let sp := checkpointSigFile dir
      if !(← sp.pathExists) then
        errors := errors.push s!"checkpoint: no signature ({sp})"
      else
        let r ← try verifyDetachedFile (checkpointFile dir) sp signers transparencyNamespace keyId
          catch e => pure (.error s!"{e}")
        match r with
        | .error e => errors := errors.push s!"checkpoint: {e}"
        | .ok (id, _) => st := { st with checkpointKey := id }
    -- (the current generation index is the latest logged one, or is newer: not yet appended)
    match ← readGeneration dir with
    | none => errors := errors.push "no manifest.sexpr (the layer has no generation index)"
    | some g =>
      if g.generation < last.entry.generation then
        errors := errors.push s!"generation rollback: index generation {g.generation} is older than logged {last.entry.generation}"
      else if g.generation > last.entry.generation then
        st := { st with behind := true }
      else
        unless g.root == last.entry.root do
          errors := errors.push "the generation index root is not the logged root"
        let gbytes ← try pure (← IO.FS.readBinFile (generationFile dir)) catch _ => pure .empty
        unless Smt.Sha256.hexBytes gbytes == last.entry.manifest do
          errors := errors.push "manifest.sexpr bytes do not match the logged digest"
        let sp := signatureFile dir
        if !(← sp.pathExists) then
          errors := errors.push "manifest.sexpr has no signature"
        else
          let sbytes ← try pure (← IO.FS.readBinFile sp) catch _ => pure .empty
          unless Smt.Sha256.hexBytes sbytes == last.entry.manifestSig do
            errors := errors.push "manifest.sexpr.sig bytes do not match the logged digest"
          let r ← try verifyDetachedFile (generationFile dir) sp signers signatureNamespace keyId
            catch e => pure (.error s!"{e}")
          match r with
          | .error e => errors := errors.push s!"manifest signature: {e}"
          | .ok _ => pure ()
          if errors.isEmpty then st := { st with current := true }
    pure { st with errors }

/-! ## The witness and the offline monitor -/

/-- A monitor's pinned view of a log: the last checkpoint it accepted. It is local state,
not a signed object; an attacker who can rewrite it can defeat the monitor, so keep it
outside the cache and, for a real deployment, on a different machine. -/
structure Witness where
  format : Nat := 1
  size : Nat := 0
  root : String := ""
  head : String := ""
  generation : Nat := 0
  updated : Nat := 0
  deriving Repr, Inhabited

def Witness.ofCheckpoint (cp : Checkpoint) (timestamp : Nat) : Witness :=
  { size := cp.size, root := cp.root, head := cp.head, generation := cp.generation,
    updated := timestamp }

def Witness.toSx (w : Witness) : Sx :=
  node "witness" [
    node "format" [nat w.format],
    node "size" [nat w.size],
    node "root" [str w.root],
    node "head" [str w.head],
    node "generation" [nat w.generation],
    node "updated" [nat w.updated]]

def Witness.ofSx? (x : Sx) : Option Witness := do
  let v ← sxField? "format" x
  let format ← (← atom? v).toNat?
  let v ← sxField? "size" x
  let size ← (← atom? v).toNat?
  let v ← sxField? "root" x
  let root ← atom? v
  let head ← match ← sxField? "head" x with | .a s => pure s | _ => pure ""
  let v ← sxField? "generation" x
  let generation ← (← atom? v).toNat?
  let updated ← match ← sxField? "updated" x with
    | .a s => pure (s.toNat?.getD 0) | _ => pure 0
  pure { format, size, root, head, generation, updated }

def readWitness (file : System.FilePath) : IO (Except String (Option Witness)) := do
  if !(← file.pathExists) then return .ok none
  try
    let text ← IO.FS.readFile file
    match (Sx.parse text).bind Witness.ofSx? with
    | some w => pure (.ok (some w))
    | none => pure (.error s!"{file} is not a witness; refusing to reset the monitor state")
  catch e => pure (.error s!"{file}: {e}")

def writeWitness (file : System.FilePath) (w : Witness) : IO Unit := do
  if let some d := file.parent then IO.FS.createDirAll d
  writeAtomic file (w.toSx.render ++ "\n")

/-- What the offline monitor found. `status` is `new`, `ok`, `behind`, `rollback`, `fork`
or `tamper`; only `new` and `ok` are accepted and update the witness. -/
structure MonitorResult where
  status : String := "ok"
  entries : Nat := 0
  generation : Nat := 0
  root : String := ""
  detail : String := ""
  witness : Witness := {}
  updated : Bool := false
  deriving Repr, Inhabited

/-- Verify a layer's log and compare it with a local witness, then advance the witness if
the log extends it. Rollback (a shorter log, or a lower generation), a fork (the witnessed
head or root no longer prefixes the log), and any tampered entry are refused and leave the
witness untouched. The whole check is offline: no network, no public log. -/
def monitorLog (dir : System.FilePath) (signers : System.FilePath)
    (witnessFile : System.FilePath) (keyId : Option String := none) :
    IO MonitorResult := do
  let st ← checkLog dir signers keyId
  if !st.errors.isEmpty then
    return { status := "tamper", entries := st.entries, generation := st.generation,
             root := st.root, detail := "; ".intercalate st.errors.toList }
  if st.behind then
    return { status := "behind", entries := st.entries, generation := st.generation,
             root := st.root,
             detail := "the generation index is newer than the log; run 'wiz cache log append'" }
  let some cp ← readCheckpoint dir
    | return { status := "tamper", detail := "no checkpoint" }
  match ← readWitness witnessFile with
  | .error e => pure { status := "tamper", entries := st.entries, generation := st.generation,
                       root := st.root, detail := e }
  | .ok none =>
    let w := Witness.ofCheckpoint cp (← unixNow)
    writeWitness witnessFile w
    pure { status := "new", entries := st.entries, generation := st.generation,
           root := st.root, witness := w, updated := true }
  | .ok (some w) =>
    match ← readLogFiles dir with
    | .error e => pure { status := "tamper", detail := e }
    | .ok fs =>
      if cp.size < w.size || cp.generation < w.generation then
        pure { status := "rollback", entries := st.entries, generation := st.generation,
               root := st.root, witness := w,
               detail := s!"the log has {cp.size} entries and generation {cp.generation}; " ++
                 s!"the witness has {w.size} and {w.generation}" }
      else if w.size > 0 then
        let pref := fs.extract 0 w.size
        let prefixRoot := logRoot pref
        let prefixHead := logHead pref
        if prefixHead != w.head || prefixRoot != w.root then
          pure { status := "fork", entries := st.entries, generation := st.generation,
                 root := st.root, witness := w,
                 detail := "the witnessed head is not a prefix of this log" }
        else if cp.size == w.size && cp.root == w.root && cp.head == w.head &&
            cp.generation == w.generation then
          pure { status := "ok", entries := st.entries, generation := st.generation,
                 root := st.root, witness := w }
        else
          let w' := Witness.ofCheckpoint cp (← unixNow)
          writeWitness witnessFile w'
          pure { status := "ok", entries := st.entries, generation := st.generation,
                 root := st.root, witness := w', updated := true }
      else
        let w' := Witness.ofCheckpoint cp (← unixNow)
        writeWitness witnessFile w'
        pure { status := "ok", entries := st.entries, generation := st.generation,
               root := st.root, witness := w', updated := true }

end Wiz.Cache
