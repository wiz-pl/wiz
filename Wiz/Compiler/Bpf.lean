/-
# `--target bpf`: the P0 facade

Two entry points:

* `compileManifest` — the CLI path. P0 consumes a **manifest** (`bpf.toml`, §5.1) and the
  typed core it names (`bpf-core/1`, `Wiz/Compiler/Bpf/Sexp.lean`), checks the result and
  prints the flat C. The Wiz-source restriction pass is `Wiz/Compiler/Bpf/Lower.lean`;
  its adapter from the elaborator's `Term R` is the one piece P0 cannot write without a
  build, because the IR is untyped (§1.2) and the elaborated term's types and spans are
  what the diagnostics need.
* `buildCmd` — `wiz build bpf.toml -o flow.c --target bpf`.

Deliberately absent (recorded as needing a queue slot, not guessed):

* invoking `clang -target bpf` and reading the object back for the post-`clang` checks
  (`r10 - N`, undefined symbols, relocations, the 100k instruction count);
* the ELF reader / ubpf harness and the hosted (`BPF_HOSTED`) map implementation;
* the privileged verifier CI (§8.4), which is the long pole and must not be run here.
-/
import Wiz.Compiler.Bpf.Sexp
import Wiz.Compiler.Bpf.C
import Wiz.Compiler.Bpf.Lower

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
  pure { name, entry, sectionName, kind, license, version, core := findEntry s "core" }

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

/-- Read the manifest and its typed core, lower nothing (the core *is* the lowered term),
check it, and return the C text. -/
def compileManifest (manifestPath : System.FilePath) : IO (Except String String) := do
  let text ← IO.FS.readFile manifestPath
  match parseManifest text with
  | .error e => pure (.error e)
  | .ok m =>
    let dir := manifestPath.parent.getD "."
    let corePath := dir / coreFileName m.program
    let present ← corePath.pathExists
    if !present then
      pure (.error s!"bpf: `{manifestPath}` needs the typed core `{corePath}` (a \
`bpf-core/1` file). P0 cannot read Wiz source: the compiler IR is untyped, so the \
restriction pass needs the elaborated types and is not wired yet (see \
Wiz/Compiler/Bpf/Lower.lean).")
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

def buildCmd (path out : String) (lib noMain : Bool) (split : Nat) : IO UInt32 := do
  if lib || noMain || split != 0 then do
    IO.eprintln "wiz build --target bpf: the backend builds one freestanding object; \
`--lib`, `--no-main` and `--split` do not apply"
    pure 2
  else if !path.endsWith ".toml" then do
    IO.eprintln "wiz build --target bpf: P0 consumes a manifest (`bpf.toml`) and a \
`bpf-core/1` file. A `.wiz` source needs the restriction pass, which needs the elaborated \
types; it is not wired yet (see Wiz/Compiler/Bpf/Lower.lean)."
    pure 2
  else
    match ← compileManifest (System.FilePath.mk path) with
    | .error e => IO.eprintln e; pure 1
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
