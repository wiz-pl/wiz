/-
# `--target bpf`: the P0 facade

Two entry points:

* `compileSourceFile` / `Wiz/Compiler/Bpf/Adapter.lean` — the CLI path for a `.wiz`
  source: the elaborated `Term R` is adapted to the typed surface, the restriction pass
  (`Bpf.Lower`) and checker run, and the flat C is printed. `compileManifest` remains the
  fixture path: a manifest naming a `bpf-core/1` file (or with no `source`) is read by
  `Bpf.Sexp`, so the tests keep a serialised-core case.
* `buildCmd` — `wiz build flow.wiz -o flow.c --target bpf` (a sibling `flow.toml`/`bpf.toml`
  supplies the section, licence, version and maps; a manifest with `source = "flow.wiz"`
  works too).

Deliberately absent (recorded as needing a queue slot, not guessed):

* invoking `clang -target bpf` and reading the object back for the post-`clang` checks
  (`r10 - N`, undefined symbols, relocations, the 100k instruction count);
* the ELF reader / ubpf harness and the hosted (`BPF_HOSTED`) map implementation;
* the privileged verifier CI (§8.4), which is the long pole and must not be run here.
-/
import Wiz.Compiler.Bpf.Sexp
import Wiz.Compiler.Bpf.C
import Wiz.Compiler.Bpf.Lower
import Wiz.Compiler.Bpf.Adapter
import Wiz.Rig.Instances

namespace Wiz.Compiler.Bpf

/-! ## The manifest (§5.1) -/

structure ProgramSpec where
  name : String
  entry : String
  sectionName : String
  kind : ProgKind
  license : String
  version : Nat
  /-- the `bpf-core/1` file, relative to the manifest; default `<entry>.bpfcore` -/
  core : Option String := none
  /-- the `.wiz` source, relative to the manifest. A source build goes through the
  elaborator adapter; a `core` build stays as the P0 fixture path. -/
  wizSource : Option String := none

structure Manifest where
  program : ProgramSpec
  maps : Array MapDecl

structure Sect where
  name : String
  entries : Array (String × String)

def findEntry (s : Sect) (k : String) : Option String :=
  (s.entries.find? fun (k', _) => k' == k).map fun (_, v) => v

def reqEntry (s : Sect) (k : String) : Except String String :=
  match findEntry s k with
  | some v => pure v
  | none => .error s!"bpf.toml: `[{s.name}]` needs `{k}`"

def unquote (v : String) : String :=
  if v.length >= 2 && v.startsWith "\"" && v.endsWith "\"" then
    (v.drop 1).dropEnd 1 |>.toString
  else v

/-- Strip a section prefix (`program.` / `map.`) and return the rest, or an error. -/
def sectionSuffix (pfx : String) (s : Sect) : Except String String :=
  if s.name.startsWith pfx then
    pure (s.name.drop pfx.length).toString
  else
    .error s!"bpf.toml: `[{s.name}]` is not a `{pfx}` section"

partial def sections (lines : List String) (cur : Option Sect) (acc : List Sect) :
    Except String (List Sect) :=
  match lines with
  | [] =>
    match cur with
    | some s => pure (s :: acc).reverse
    | none => pure acc.reverse
  | line :: rest =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then
      sections rest cur acc
    else if line.startsWith "[" && line.endsWith "]" then
      let name := ((line.drop 1).dropEnd 1).trimAscii.toString
      let acc := match cur with | some s => s :: acc | none => acc
      sections rest (some { name, entries := #[] }) acc
    else
      match cur with
      | none => .error s!"bpf.toml: `{line}` is outside a section"
      | some s =>
        match line.splitOn "=" with
        | [k, v] =>
          sections rest (some { s with
            entries := s.entries.push (k.trimAscii.toString, unquote (v.trimAscii.toString)) }) acc
        | _ => .error s!"bpf.toml: expected `key = value`, got `{line}`"

/-- P0 map keys and values are scalars: the manifest names a type, it does not parse the
core grammar. Struct keys and BTF layouts are P2. -/
def parseScalarTy (s : String) : Except String Ty :=
  match s with
  | "u8" => pure .u8
  | "u16" => pure .u16
  | "u32" => pure .u32
  | "u64" => pure .u64
  | "i8" => pure .i8
  | "i16" => pure .i16
  | "i32" => pure .i32
  | "i64" => pure .i64
  | "bool" => pure .bool
  | _ =>
    .error s!"bpf.toml: the map key/value `{s}` is not a scalar. P0 maps are scalar-keyed; \
struct keys and BTF layouts arrive with the P2 map declarations."

def parseProgramSect (s : Sect) : Except String ProgramSpec := do
  let name ← sectionSuffix "program." s
  let entry ← reqEntry s "entry"
  let sectionName ← reqEntry s "section"
  let typ ← reqEntry s "type"
  let license ← reqEntry s "license"
  let versionS ← reqEntry s "version"
  let version ← match versionS.toNat? with
    | some n => pure n
    | none => .error s!"bpf.toml: `version = {versionS}` is not a number"
  let kind ← match typ with
    | "xdp" => pure .xdp
    | "tc" => pure .tc
    | other => .error s!"bpf.toml: `type = \"{other}\"` (choose \"xdp\" or \"tc\"; tracing \
is outside the packet subset)"
  match ProgKind.ofSection? sectionName with
  | none => .error s!"bpf.toml: unknown section `{sectionName}` (choose \"xdp\", \"tc\" or \
\"classifier\")"
  | some k =>
    if k != kind then
      .error s!"bpf.toml: the section `{sectionName}` is {k.describe}, but `type` is \
{kind.describe}"
    else pure ()
  pure (ProgramSpec.mk name entry sectionName kind license version
    (findEntry s "core") (findEntry s "source"))

def parseMapSect (s : Sect) : Except String MapDecl := do
  let name ← sectionSuffix "map." s
  let kindS ← reqEntry s "kind"
  let kind ← Sexp.parseMapKind kindS
  let keyS ← reqEntry s "key"
  let key ← parseScalarTy keyS
  let valueS ← reqEntry s "value"
  let value ← parseScalarTy valueS
  let maxS ← reqEntry s "max_entries"
  let maxEntries ← match maxS.toNat? with
    | some n => pure n
    | none => .error s!"bpf.toml: `max_entries = {maxS}` is not a number"
  pure { name, kind, key, value, maxEntries }

/-- Parse `bpf.toml`. One `[program.NAME]`, zero or more `[map.NAME]`. Unknown keys are
ignored so a newer manifest is readable, but a missing required key is an error. -/
def parseManifest (input : String) : Except String Manifest := do
  let secs ← sections (input.splitOn "\n") none []
  let programs := secs.filter fun s => s.name.startsWith "program."
  let maps := secs.filter fun s => s.name.startsWith "map."
  match programs with
  | [p] =>
    let program ← parseProgramSect p
    let maps ← maps.mapM parseMapSect
    pure { program, maps := maps.toArray }
  | [] => .error "bpf.toml: no `[program.NAME]` section"
  | _ => .error "bpf.toml: P0 declares exactly one `[program.NAME]`"

/-! ## Compiling a manifest -/

def coreFileName (p : ProgramSpec) : String :=
  p.core.getD (p.entry ++ ".bpfcore")

/-- The manifest's scalar map types as the surface's types. -/
def tyToSTy : Ty → STy
  | .unit => .unit
  | .bool => .bool
  | .u8 => .uint 8
  | .u16 => .uint 16
  | .u32 => .uint 32
  | .u64 => .uint 64
  | .i8 => .int 8
  | .i16 => .int 16
  | .i32 => .int 32
  | .i64 => .int 64
  | .enum n => .enum n
  | .struct fs => .struct (fs.map tyToSTy)
  | .option t => .option (tyToSTy t)
  | .packet => .packet
  | .ctx k => .ctx k
  | .map k v kind => .map (tyToSTy k) (tyToSTy v) kind

/-- The map declarations the manifest adds to the surface program. -/
def surfaceMaps (maps : Array MapDecl) : Array SMapDecl :=
  maps.map fun m =>
    { name := m.name, kind := m.kind, key := tyToSTy m.key, value := tyToSTy m.value
      maxEntries := m.maxEntries }

/-- Read a `bpf-core/1` fixture manifest and emit its C. This is the fixture path; the
CLI's source path is `compileSourceFile` below. -/
def compileManifest (manifestPath : System.FilePath) : IO (Except String String) := do
  let text ← IO.FS.readFile manifestPath
  match parseManifest text with
  | .error e => pure (.error e)
  | .ok m =>
    let dir := manifestPath.parent.getD "."
    let corePath := dir / coreFileName m.program
    let present ← corePath.pathExists
    if !present then
      pure (.error s!"bpf: `{manifestPath}` needs a typed core `{corePath}` (a \
`bpf-core/1` file) or a `source = \"file.wiz\"` key.")
    else
      let coreText ← IO.FS.readFile corePath
      match Sexp.parseCore coreText with
      | .error e => pure (.error e)
      | .ok core =>
        let prog : Program :=
          { entry := m.program.entry
            sectionName := m.program.sectionName
            kind := m.program.kind
            license := m.program.license
            version := m.program.version
            maps := m.maps
            decls := core.decls
            ret := core.ret }
        pure (emitProgram prog)

/-- Elaborate a `.wiz` file and return its state and text. The CLI supplies this (the
frontend needs the toolchain's module roots, headers and cache); the adapter and the
manifest parser stay pure. -/
abbrev Elaborator := String → IO (Except String (CommandState ZeroOneMany × String))

/-- Lower an elaborated `.wiz` source with the manifest's metadata and maps. -/
def compileSourceFile (elaborate : Elaborator) (sourcePath : System.FilePath)
    (m : Manifest) : IO (Except String String) := do
  match ← elaborate sourcePath.toString with
  | .error e => pure (.error e)
  | .ok (state, text) =>
    let src : Source ZeroOneMany := { state, path := sourcePath.toString, text }
    pure (compileSource src
      { entry := m.program.entry
        sectionName := m.program.sectionName
        kind := m.program.kind
        license := m.program.license
        version := m.program.version
        maps := surfaceMaps m.maps })

/-- A source file with no manifest: the file's stem is the entry, an XDP program with a
GPL licence and no maps. A manifest is needed for a TC program or a map. -/
def defaultManifest (sourcePath : System.FilePath) : Manifest :=
  let name := sourcePath.fileStem.getD "flow"
  { program :=
      { name, entry := name, sectionName := "xdp", kind := .xdp, license := "GPL", version := 1 }
    maps := #[] }

/-- The manifest beside a `.wiz` file: `<stem>.toml`, or `bpf.toml`. -/
def companionManifest (sourcePath : System.FilePath) : IO (Option System.FilePath) := do
  let dir := sourcePath.parent.getD "."
  let stem := sourcePath.withExtension "toml"
  if ← stem.pathExists then pure (some stem)
  else
    let bpf := dir / "bpf.toml"
    if ← bpf.pathExists then pure (some bpf) else pure none

/-- A source path from the manifest, relative to the manifest's directory. -/
def manifestSource? (m : Manifest) (manifestPath : System.FilePath) : Option System.FilePath :=
  m.program.wizSource.map fun s =>
    if System.FilePath.isAbsolute (System.FilePath.mk s) then System.FilePath.mk s
    else manifestPath.parent.getD "." / s

def buildCmd (elaborate : Elaborator) (path out : String) (lib noMain : Bool) (split : Nat) :
    IO UInt32 := do
  if lib || noMain || split != 0 then do
    IO.eprintln "wiz build --target bpf: the backend builds one freestanding object; \
`--lib`, `--no-main` and `--split` do not apply"
    pure 2
  else
    let p := System.FilePath.mk path
    let ext := p.extension
    if ext != some "wiz" && ext != some "toml" then do
      IO.eprintln "wiz build --target bpf: takes a `.wiz` source (with an optional \
sibling `bpf.toml`) or a manifest (`bpf.toml`) naming a `source` or a `bpf-core/1` file"
      pure 2
    else
      let (manifestPath?, sourceArg?) ←
        if ext == some "wiz" then do
          pure (← companionManifest p, some p)
        else pure (some p, none)
      let manifest ←
        match manifestPath? with
        | none => pure (.ok (defaultManifest p))
        | some mp => do
          let text ← IO.FS.readFile mp
          pure (parseManifest text)
      match manifest with
      | .error e => do IO.eprintln e; pure 1
      | .ok m =>
        let manifestDir := match manifestPath? with
          | some mp => mp.parent.getD "."
          | none => p.parent.getD "."
        let source? :=
          match sourceArg? with
          | some s => some s
          | none => manifestSource? m (manifestPath?.getD p)
        let corePath := manifestDir / coreFileName m.program
        let result ←
          match source? with
          | some src => compileSourceFile elaborate src m
          | none =>
            if ← corePath.pathExists then
              match manifestPath? with
              | some mp => compileManifest mp
              | none => pure (.error "bpf: internal: a core build has no manifest")
            else
              -- a manifest with neither `source` nor a core: try `<stem>.wiz`
              let guess := manifestDir / (m.program.entry ++ ".wiz")
              if ← guess.pathExists then compileSourceFile elaborate guess m
              else pure (.error s!"bpf: `{path}` has no `source = \"file.wiz\"` and no \
`{corePath}`. Add `source = \"file.wiz\"` to the manifest, or pass the `.wiz` directly.")
        match result with
        | .error e => do IO.eprintln e; pure 1
        | .ok c =>
          let outPath : String :=
            if out.endsWith ".c" then out
            else ((System.FilePath.mk out).withExtension "c").toString
          let outFile := System.FilePath.mk outPath
          let dir := outFile.parent.getD "."
          let hdr := dir / "bpf_rt.h"
          IO.FS.writeFile outFile c
          IO.FS.writeFile hdr header
          IO.println s!"bpf: wrote {outPath} and {hdr}"
          IO.eprintln "bpf: the C is verifier-shaped; `clang -target bpf` and the post-clang \
checks (stack, undefined symbols, relocations, instruction budget) are the next P0 step."
          pure 0

end Wiz.Compiler.Bpf
