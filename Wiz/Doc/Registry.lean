import Wiz.Doc.Highlight

/-!
# The external language registry (`wiz doc --languages`)

`schema wiz.doc.languages/1` (`docs-highlighting.md` §4.2). A package ships a versioned
JSON file of `Spec`s; `wiz doc` merges it after the built-ins. This module is the only
place that reads it.

The checks are the design's, and they fail the run rather than produce a partial page:

* the schema must be exactly `wiz.doc.languages/1`; unknown fields are refused (a typo
  should not be silently ignored);
* a name must be non-empty and `[A-Za-z][A-Za-z0-9_+-]*`; names and aliases are matched
  case-insensitively;
* a duplicate name within one file is an error; a name (or alias) that already exists is
  an error unless the entry says `"override": true`, which replaces the built-in;
* `wiz` is reserved and can never be replaced;
* a class must be one of the fixed eight (`kw com str num op const var sort`).

No package code runs here and no package class name is accepted: a registry entry is
data, and the HTML class is always `Wiz.Doc.Highlight.className`.
-/

namespace Wiz.Doc

open Lean (Json)

/-- The keys of a JSON object (`[]` for any other value). -/
def objKeys : Json → List String
  | .obj kvs => kvs.keys
  | _ => []

/-- The keys of `j` that are not in `allowed`. -/
def unknownKeys (allowed : List String) (j : Json) : List String :=
  (objKeys j).filter fun k => !allowed.contains k

def strOpt (j : Json) (k : String) : Option String :=
  (j.getObjVal? k).toOption.bind fun v => (Json.getStr? v).toOption

def boolOpt (j : Json) (k : String) : Bool :=
  ((j.getObjVal? k).toOption.bind fun v => (Json.getBool? v).toOption).getD false

def arrOpt (j : Json) (k : String) : Option (Array Json) :=
  (j.getObjVal? k).toOption.bind fun v => (Json.getArr? v).toOption

def arrOf (j : Json) (k : String) : Array Json := (arrOpt j k).getD #[]

def listStr (j : Json) (k : String) : List String :=
  (arrOf j k).toList.filterMap fun v => (Json.getStr? v).toOption

/-- A language name's shape: `[A-Za-z][A-Za-z0-9_+-]*`. -/
def nameOk (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => c.isAlpha && cs.all fun x => x.isAlphanum || x == '_' || x == '+' || x == '-'

namespace Highlight

/-- A string rule from JSON: `{open, close, escape?, multiline?}`. -/
def StringRule.ofJson (j : Json) : Except String StringRule := do
  let unk := unknownKeys ["open", "close", "escape", "multiline"] j
  if !unk.isEmpty then throw s!"unknown field(s) in a string rule: {unk}"
  let opener ← Json.getStr? (← j.getObjVal? "open")
  let closer ← Json.getStr? (← j.getObjVal? "close")
  if opener.isEmpty || closer.isEmpty then throw "a string rule needs non-empty open and close"
  pure { opener, closer, escape := (strOpt j "escape").getD "\\",
         multiline := boolOpt j "multiline" }

/-- A spec from JSON: the fields of `Spec` (at the top level of a language entry). -/
def Spec.ofJson (j : Json) : Except String Spec := do
  let strings ← (arrOf j "strings").toList.mapM StringRule.ofJson
  let blockComment ← match (j.getObjVal? "blockComment").toOption with
    | none => pure none
    | some .null => pure none
    | some b => do
      let unk := unknownKeys ["open", "close", "nested"] b
      if !unk.isEmpty then throw s!"unknown field(s) in blockComment: {unk}"
      let opener ← Json.getStr? (← b.getObjVal? "open")
      let closer ← Json.getStr? (← b.getObjVal? "close")
      if opener.isEmpty || closer.isEmpty then throw "a block comment needs non-empty open and close"
      pure (some (opener, closer, boolOpt b "nested"))
  pure { lineComment := listStr j "lineComment", blockComment, strings,
         keywords := listStr j "keywords", numberPrefix := listStr j "numberPrefix",
         operators := listStr j "operators", caseFold := boolOpt j "caseFold" }

/-- A language from JSON: `{name, aliases?, lexer?: "wiz"|"spec", classes?, spec
fields…, override?}`. -/
def Lang.ofJson (j : Json) : Except String Lang := do
  let specFields := ["lineComment", "blockComment", "strings", "keywords",
    "numberPrefix", "operators", "caseFold"]
  let unk := unknownKeys (["name", "aliases", "lexer", "classes", "override"] ++ specFields) j
  if !unk.isEmpty then throw s!"unknown field(s): {unk}"
  let name ← Json.getStr? (← j.getObjVal? "name")
  if !nameOk name then throw s!"bad language name {name}"
  let aliases := listStr j "aliases"
  aliases.forM fun a => do
    if !nameOk a then throw s!"bad alias {a} for {name}"
  let classes ← match arrOpt j "classes" with
    | none => pure [Class.kw, Class.com, Class.str, Class.num]
    | some xs => xs.toList.mapM fun v => do
      let s ← Json.getStr? v
      match Class.ofName? s with
      | some c => pure c
      | none => throw s!"unknown class {s}"
  let lexerName := (strOpt j "lexer").getD "spec"
  let lexer ← if lexerName == "wiz" then pure (Lexer.wiz)
    else if lexerName == "spec" then Lexer.spec <$> Spec.ofJson j
    else throw s!"unknown lexer {lexerName} (wiz or spec)"
  pure { name, aliases, lexer, classes, override := boolOpt j "override" }

/-- A registry from JSON. -/
def Registry.ofJson (j : Json) : Except String Registry := do
  let unk := unknownKeys ["schema", "languages"] j
  if !unk.isEmpty then throw s!"unknown field(s): {unk}"
  let schema ← Json.getStr? (← j.getObjVal? "schema")
  if schema != "wiz.doc.languages/1" then throw s!"unknown schema {schema}"
  let entries ← match arrOpt j "languages" with
    | some xs => xs.toList.mapM Lang.ofJson
    | none => throw "languages must be an array"
  let names := entries.map (·.name.toLower)
  match names.find? fun n => (names.filter (· == n)).length > 1 with
  | some n => throw s!"duplicate language {n}"
  | none => pure { langs := entries }

/-- Merge an external registry after `base`. Names and aliases match case-insensitively;
`override` replaces an existing name (`wiz` is never replaceable). -/
def Registry.merge (base : Registry) (extra : Registry) : Except String Registry :=
  extra.langs.foldlM (fun reg l => do
    if l.name.toLower == "wiz" then throw "the wiz language is reserved"
    if let some old := reg.find? l.name then
      if !l.override then throw s!"language {l.name} already exists (as {old.name})"
    l.aliases.forM fun a => do
      if let some old := reg.find? a then
        if old.name.toLower != l.name.toLower then
          throw s!"alias {a} of {l.name} already belongs to {old.name}"
    match reg.find? l.name with
    | some _ =>
      pure { reg with langs := reg.langs.map fun x =>
        if x.name.toLower == l.name.toLower then l else x }
    | none => pure { reg with langs := reg.langs ++ [l] }) base

end Highlight

/-- Read one registry file; a parse or validation error names the file and the message. -/
def Registry.loadFile (path : System.FilePath) : IO Highlight.Registry := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok j => match Highlight.Registry.ofJson j with
    | .error e => throw (IO.userError s!"{path}: {e}")
    | .ok r => pure r

/-- Merge the registry files after the built-ins, in order (the first failure stops). -/
def Registry.loadFiles (paths : List System.FilePath) : IO Highlight.Registry :=
  paths.foldlM (fun reg p => do
    let r ← Registry.loadFile p
    match Highlight.Registry.merge reg r with
    | .error e => throw (IO.userError s!"{p}: {e}")
    | .ok reg => pure reg) Highlight.Registry.builtins

/-- The `WIZ_DOC_LANGUAGES` hook: a colon-separated list of registry files. The `wiz
doc`/`grail doc` flag is the explicit path; this environment variable is the host-side
hook until the flag is parsed (see the lane's report). -/
def Registry.envFiles : IO (List System.FilePath) := do
  match ← IO.getEnv "WIZ_DOC_LANGUAGES" with
  | some s => pure ((List.map System.FilePath.mk) ((s.splitOn ":").filter fun x => !x.isEmpty))
  | none => pure []

end Wiz.Doc
