import Wiz.Lint
import Wiz.Version

/-!
# SARIF 2.1.0 output for `wiz lint`

`wiz lint --format sarif` (`Wiz.Sarif.toJson` / `Wiz.Sarif.render`) renders the
diagnostics of `Wiz.Lint` as one [SARIF 2.1.0] log, so that a code-scanning service or a
CI job can consume them without parsing the human text.

The shape follows the SARIF writer of the scry analysis (`Scry.Sarif`): a `$schema`, a
`version` and one `run` whose `tool.driver` names the tool and whose `results` carry the
findings. `wiz lint` does not depend on the scry package; the renderer is host-side Lean
and uses only `Lean.Data.Json`.

[SARIF 2.1.0]: https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html

## Rule IDs

Every lint rule has a **namespaced** SARIF id (`wizlint/<category>/<rule>`), so lint
findings do not collide with CodeQL, Semgrep or scry findings in an aggregated
dashboard. The text output keeps the short name in `[RULE]`.

| short name (`Diag.rule`) | SARIF `ruleId` |
|---|---|
| `style.tabs` | `wizlint/style/tabs` |
| `style.trailing-whitespace` | `wizlint/style/trailing-whitespace` |
| `style.crlf` | `wizlint/style/crlf` |
| `style.line-length` | `wizlint/style/line-length` |
| `sorry` | `wizlint/hygiene/sorry` |
| `axiom` | `wizlint/hygiene/axiom` |
| `shadowed-binder` | `wizlint/hygiene/shadowed-binder` |
| `unused-import` | `wizlint/imports/unused-import` |
| `duplicate-import` | `wizlint/imports/duplicate-import` |

An elaborator diagnostic (a file that does not check) keeps its own code: its id is
`wizlint/elaborator/<code>` (`unknown-identifier`, `parse-error`, …, or
`wizlint/elaborator/other` when the message has no code). A descriptor is added for each
such id a run reports, after the fixed table above. The descriptor's `name` is a short
human name, not the id.

The SARIF level of a result is `error` for an error, `warning` for a warning and `note`
for an informational message (Wiz calls the last one `info`).

## Locations and fingerprints

`artifactLocation.uri` is relative to the working directory of the invocation (an
absolute path under it is shortened; one outside it gets `..` components; standard
input is `-`). It carries `uriBaseId: "%SRCROOT%"`, as GitHub code scanning expects, and
`runs[0].artifacts` lists the same location. `region` is 1-based and its end is
exclusive; columns are **UTF-16 code units** (`columnKind` is declared on the run), not
raw code points. A position-only finding gets a one-character region when it is not at
the end of its line.

`partialFingerprints` has two entries:

* `primaryLocationLineHash`: FNV-1a over the rule id and the normalized primary line
  (leading and trailing whitespace stripped, internal whitespace collapsed). It does
  not include the line number, so a line move keeps the finding and a content change
  creates a new one. GitHub code scanning uses this one.
* `wizlint/v1`: the composite fingerprint, FNV-1a over the rule id, the normalized
  relative path and the normalized primary line. Versioning the key means a change to
  its inputs can be a new key.

Both hashes are FNV-1a over code points, not `Hashable.hash`: they do not depend on the
Lean build, and the same inputs always give the same digest.
-/

namespace Wiz.Sarif

open Wiz.Lint

/-! ## Rule metadata -/

/-- A lint rule's SARIF reporting descriptor. `rule` is the short name `Diag.rule`
carries; `id` is the namespaced SARIF rule id; `name` is the short human name. `level`
is its default configuration. -/
structure RuleMeta where
  rule : String
  id : String
  name : String
  level : String
  description : String
  deriving Repr, Inhabited

/-- The lint rules, in a fixed order (the order `tool.driver.rules` lists them). -/
def ruleTable : Array RuleMeta := #[
  { rule := "style.tabs", id := "wizlint/style/tabs", name := "tab", level := "warning",
    description := "a tab in indentation or alignment" },
  { rule := "style.trailing-whitespace", id := "wizlint/style/trailing-whitespace",
    name := "trailing-whitespace", level := "warning",
    description := "spaces or tabs at the end of a line" },
  { rule := "style.crlf", id := "wizlint/style/crlf", name := "crlf", level := "warning",
    description := "a CRLF line ending" },
  { rule := "style.line-length", id := "wizlint/style/line-length",
    name := "line-length", level := "warning",
    description := "a line longer than the configured maximum" },
  { rule := "sorry", id := "wizlint/hygiene/sorry", name := "sorry", level := "warning",
    description := "the identifier sorry or admit (Wiz does not check it)" },
  { rule := "axiom", id := "wizlint/hygiene/axiom", name := "axiom", level := "warning",
    description := "an axiom declared in this file" },
  { rule := "shadowed-binder", id := "wizlint/hygiene/shadowed-binder",
    name := "shadowed-binder", level := "warning",
    description := "a binder that shadows an enclosing binder or a visible global" },
  { rule := "unused-import", id := "wizlint/imports/unused-import",
    name := "unused-import", level := "warning",
    description := "an import that nothing in this file needs" },
  { rule := "duplicate-import", id := "wizlint/imports/duplicate-import",
    name := "duplicate-import", level := "warning",
    description := "the same module imported twice" }
]

/-- SARIF's `level`: Wiz's `info` is SARIF's `note`. -/
def level : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .info => "note"

/-! ## JSON helpers -/

private def jstr (s : String) : Lean.Json := Lean.Json.str s

private def jnat (n : Nat) : Lean.Json := Lean.Json.num (Lean.JsonNumber.fromNat n)

private def jarr (xs : Array Lean.Json) : Lean.Json := Lean.Json.arr xs

private def jobj (xs : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj xs

/-! ## Rule descriptors -/

/-- The rule ids (`Diag.rule`, the short names) a run reports, in first-appearance
order. -/
def reportedRules (diags : Array Diag) : Array String :=
  diags.foldl (fun acc d => if acc.contains d.rule then acc else acc.push d.rule) #[]

/-- The descriptor of a rule a run reports: a table entry for a lint rule, or an
elaborator descriptor (`wizlint/elaborator/<code>`) for an error. -/
def descriptor (diags : Array Diag) (rule : String) : RuleMeta :=
  match ruleTable.find? (·.rule == rule) with
  | some r => r
  | none =>
    let id := if rule == "elaborator" || rule.isEmpty then "wizlint/elaborator/other"
      else s!"wizlint/elaborator/{rule}"
    let lvl := match diags.find? (·.rule == rule) with
      | some d => level d.severity
      | none => "warning"
    { rule, id, name := (if rule.isEmpty then "elaborator" else rule), level := lvl,
      description := s!"a diagnostic from the elaborator ({id})" }

/-- The descriptors of a run: the lint table, then a descriptor for each elaborator
rule id the run reports (in first-appearance order). -/
def rulesFor (diags : Array Diag) : Array RuleMeta :=
  (reportedRules diags).foldl (fun rs rule =>
    if rs.any (·.rule == rule) then rs else rs.push (descriptor diags rule)) ruleTable

/-- A rule's index in `tool.driver.rules` (its `ruleIndex`), or 0. -/
def ruleIndex (rs : Array RuleMeta) (rule : String) : Nat :=
  match rs.findIdx? (·.rule == rule) with
  | some i => i
  | none => 0

def ruleJson (r : RuleMeta) : Lean.Json :=
  jobj [
    ("id", jstr r.id),
    ("name", jstr r.name),
    ("shortDescription", jobj [("text", jstr r.description)]),
    ("defaultConfiguration", jobj [("level", jstr r.level)])]

/-! ## Spans -/

/-- The text of the line that contains `pos`, without its line ending. -/
def lineTextAt (text : String) (pos : Nat) : String := Id.run do
  let chars := text.toList.toArray
  let mut start := 0
  let mut i := 0
  while i < chars.size && i < pos do
    if chars[i]! == '\n' then start := i + 1
    i := i + 1
  let mut stop := start
  while stop < chars.size && chars[stop]! != '\n' do stop := stop + 1
  String.ofList (chars.extract start stop).toList

/-- The UTF-16 code units in a string: two for a supplementary-plane code point, one
otherwise. -/
def utf16Units (s : String) : Nat :=
  s.toList.foldl (fun n c => n + (if c.toNat > 0xFFFF then 2 else 1)) 0

/-- The 1-based UTF-16 column of a 0-based character column in `line`. -/
def utf16Column (line : String) (charCol : Nat) : Nat :=
  utf16Units (String.ofList (line.toList.take charCol)) + 1

/-- The `region` of a diagnostic: 1-based, end exclusive, columns in UTF-16 code units
(the run declares `columnKind`). A position-only finding is given a one-character
region when its position is not the end of the line, so that it names a character. -/
def regionJson (text : String) (d : Diag) : Lean.Json :=
  let (l, c) := lineCol text d.info.start
  let stop := max d.info.stop d.info.start
  let (l₂, c₂) := lineCol text stop
  let startLineText := lineTextAt text d.info.start
  let endLineText := lineTextAt text stop
  let endCol :=
    if l₂ == l && c₂ <= c then
      if c < startLineText.toList.length then c + 1 else c
    else c₂
  jobj [
    ("startLine", jnat (l + 1)),
    ("startColumn", jnat (utf16Column startLineText c)),
    ("endLine", jnat (l₂ + 1)),
    ("endColumn", jnat (utf16Column endLineText endCol))]

/-! ## Locations and artifacts -/

/-- GitHub code scanning's base id for paths relative to the repository root; `wiz`
runs from the invocation's working directory. -/
def uriBaseId : String := "%SRCROOT%"

def artifactLocationJson (uri : String) : Lean.Json :=
  jobj [("uri", jstr uri), ("uriBaseId", jstr uriBaseId)]

def locationJson (uri text : String) (d : Diag) : Lean.Json :=
  jobj [
    ("physicalLocation", jobj [
      ("artifactLocation", artifactLocationJson uri),
      ("region", regionJson text d)])]

/-- The `artifacts` entry for the linted file. -/
def artifactJson (uri : String) : Lean.Json :=
  jobj [("location", artifactLocationJson uri)]

/-! ## Fingerprints -/

/-- FNV-1a over a string's code points: cheap, deterministic and independent of the
Lean build (a hash of `Hashable` could change with the toolchain). -/
def fnv1a (s : String) : UInt64 :=
  s.toList.foldl (fun h c => (h ^^^ c.toNat.toUInt64) * 1099511628211) 14695981039346656037

/-- A `UInt64` as 16 lowercase hex digits. -/
def hex16 (n : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 n.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The fingerprint key GitHub code scanning reads. -/
def fingerprintKey : String := "primaryLocationLineHash"

/-- The versioned composite fingerprint's key. -/
def compositeFingerprintKey : String := "wizlint/v1"

/-- A primary line with leading and trailing whitespace stripped and internal
whitespace runs collapsed, so whitespace-only edits keep a finding. -/
def normalizeLine (s : String) : String := Id.run do
  let mut out : String := ""
  let mut pending := false
  for c in s.toList do
    if c == ' ' || c == '\t' || c == '\r' || c == '\n' then
      if !out.isEmpty then pending := true
    else
      if pending then
        out := out.push ' '
        pending := false
      out := out.push c
  out

/-- `primaryLocationLineHash`: the rule id and the normalized primary line, no line
number. -/
def primaryLocationLineHash (rule line : String) : String :=
  hex16 (fnv1a s!"{rule}\u0000{normalizeLine line}")

/-- `wizlint/v1`: the rule id, the normalized relative path and the normalized primary
line. -/
def compositeFingerprint (rule uri line : String) : String :=
  hex16 (fnv1a s!"{rule}\u0000{uri}\u0000{normalizeLine line}")

def fingerprintsJson (rule uri text : String) (d : Diag) : Lean.Json :=
  let line := lineTextAt text d.info.start
  jobj [
    (fingerprintKey, jstr (primaryLocationLineHash rule line)),
    (compositeFingerprintKey, jstr (compositeFingerprint rule uri line))]

/-! ## The log -/

def resultJson (rs : Array RuleMeta) (uri text : String) (d : Diag) : Lean.Json :=
  let r := match rs.find? (·.rule == d.rule) with
    | some r => r
    | none => descriptor #[d] d.rule
  jobj [
    ("ruleId", jstr r.id),
    ("ruleIndex", jnat (ruleIndex rs d.rule)),
    ("level", jstr (level d.severity)),
    ("message", jobj [("text", jstr d.message)]),
    ("locations", jarr #[locationJson uri text d]),
    ("partialFingerprints", fingerprintsJson r.id uri text d)]

def driverJson (rs : Array RuleMeta) : Lean.Json :=
  jobj [
    ("name", jstr "wiz"),
    ("version", jstr Wiz.version),
    ("informationUri", jstr "https://github.com/wiz-pl/wiz"),
    ("rules", jarr (rs.map ruleJson))]

/-- The SARIF log for `diags`, with `uri` as the artifact location. -/
def toJson (uri text : String) (diags : Array Diag) : Lean.Json :=
  let rs := rulesFor diags
  jobj [
    ("$schema",
      jstr "https://docs.oasis-open.org/sarif/sarif/v2.1.0/os/schemas/sarif-schema-2.1.0.json"),
    ("version", jstr "2.1.0"),
    ("runs", jarr #[jobj [
      ("tool", jobj [("driver", driverJson rs)]),
      ("artifacts", jarr #[artifactJson uri]),
      ("columnKind", jstr "utf16CodeUnits"),
      ("results", jarr (diags.map (resultJson rs uri text)))]])]

/-- The SARIF log as one line of compact JSON. -/
def render (uri text : String) (diags : Array Diag) : String :=
  (toJson uri text diags).compress

/-! ## Paths -/

/-- `s` with the characters that would break a relative URI reference escaped. -/
def uriEscape (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == ' ' then "%20"
    else if c == '%' then "%25"
    else if c == '#' then "%23"
    else if c == '?' then "%3F"
    else String.singleton c)

/-- `path` relative to the current working directory, for `artifactLocation.uri`.
Standard input (`-`) stays `-`. -/
def artifactUri (path : String) : IO String := do
  if path == "-" || path == "<stdin>" then return "-"
  let parts (p : System.FilePath) : List String :=
    (p.normalize.components).filter fun s => s != "" && s != "."
  let p := System.FilePath.mk path
  if p.isRelative then
    let ps := parts p
    return uriEscape (if ps.isEmpty then "." else "/".intercalate ps)
  let cwd ← IO.currentDir
  let cs := parts cwd
  let ps := parts p
  let rec shared : List String → List String → Nat
    | a :: as, b :: bs => if a == b then 1 + shared as bs else 0
    | _, _ => 0
  let k := shared cs ps
  let ups := (List.range (cs.length - k)).map fun _ => ".."
  let rel := ups ++ ps.drop k
  return uriEscape (if rel.isEmpty then "." else "/".intercalate rel)

end Wiz.Sarif
