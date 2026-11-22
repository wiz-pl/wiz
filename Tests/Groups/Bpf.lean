import Tests.Elab

open Wiz
open Wiz.Compiler.Bpf

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# `bpf`: the eBPF subset's rejection corpus and P0 fixture

**Run (2026-11-22)** — the whole group is green (22/22), including
the manifest and `bpf-core/1` fixture through the checker and C emitter. The cases are
pure (`Bpf.Lower`, `Bpf.Check`, `Bpf.Sexp`, `Bpf.C`; no `clang`, no privileges), so they
run in every PR. The first build/run found and fixed the fixture's atom-type spelling
and the `call` argument-list shape; a failure now is a P0 correctness bug.

There is no source-level `.wiz` corpus here. An earlier P0 lane wrote 20
`Tests/fixtures/bpf/{reject,accept}/*.wiz` + `.expected` files, but nothing could run
them: `bpf_program`/`BpfM` are not in `lib/`, and the elaborator → `STm` adapter that
would lower a `.wiz` file is still the P0 roadblock (`docs/stages/08-backend/bpf.md`).
They were `-- [UNRUN]` documentation with no consumer, so they were removed rather than
left asserting nothing. The rejection/acceptance contract they described is held by the
`STm` cases below, and by the manifest + `bpf-core/1` fixture through the real pipeline.

The two halves mirror §8.6 (both on `STm`, not on `.wiz` source):

* `reject`: each case asserts the stable `bpf:` prefix and the message fragment of §4.4
  (or the edge case of §2.6: `BitVec` width, signed division with `INT_MIN / -1`, a
  shift count at or past the width);
* `accept`: a neighbour for each rejection, so the corpus cannot be gamed by rejecting
  everything (a `BitVec 32`, a `Nat` literal offset, `IntN` arithmetic, `k = 63`).

The fixture test runs the whole P0 path: manifest + `bpf-core/1` → check → C text. It
does not run `clang` (that is the post-emission half, and it needs a queue slot).
-/

namespace Tests.BpfGroup

/-- Assert a rejection: `Except.error` with the stable prefix and a fragment. -/
def expectReject {α : Type} (r : Except String α) (fragment : String) : IO Unit :=
  match r with
  | .error e => do
    check (e.startsWith "bpf:") s!"not a `bpf:` diagnostic: {e}"
    check ((e.splitOn fragment).length > 1) s!"the message does not mention `{fragment}`: {e}"
  | .ok _ => throw (IO.userError s!"accepted; expected a diagnostic mentioning `{fragment}`")

/-- The entry declaration of a minimal XDP program (`flow : XdpContext → ret`). -/
def entry (body : STm) (ret : STy := .enum 5) : SDecl :=
  { name := "flow", params := #[.ctx .xdp], ret, body }

def program (decls : Array SDecl) (maps : Array SMapDecl := #[]) (ret : STy := .enum 5) :
    SProgram :=
  { entry := "flow"
    sectionName := "xdp"
    kind := .xdp
    license := "GPL"
    version := 1
    maps
    decls
    ret }

/-- A `flow` that returns `XdpAction.pass`. -/
def passProgram (maps : Array SMapDecl := #[]) : SProgram :=
  program #[entry (.ret (.enumLit 5 2))] maps

def lowerTyCase (ty : STy) (fragment : String) : Case :=
  { name := s!"`{fragment}` is rejected", run := fun _ =>
      expectReject (lowerTy {} ty) fragment }

def group : Group where
  name := "bpf"
  exercise := "Exercise 8.7 (eBPF): the verifier-shaped subset"
  parallel := true
  shard := "library"
  cases := [
    -- §2.6/§4.1 type edge cases
    lowerTyCase (.bitvec 12) "BitVec 12",
    lowerTyCase (.uint 128) "`UIntN 128`",
    lowerTyCase .nat "`Nat` is not representable",
    lowerTyCase .string "`String` is a heap object",
    lowerTyCase (.list (.uint 32)) "`List` is a recursive heap object",
    lowerTyCase .closure "a closure has no eBPF representation",
    lowerTyCase (.array (.uint 32)) "`Array` allocates",
    lowerTyCase (.ref (.uint 32)) "`Ref` is mutable heap state",
    lowerTyCase .float64 "no floating-point instructions",
    lowerTyCase (.io .unit) "`IO` — a kernel program has no world",

    -- accepted widths: the neighbours that make the width rejection meaningful
    { name := "`BitVec 32` is a register width", run := fun _ =>
        match lowerTy {} (.bitvec 32) with
        | .ok .u32 => pure ()
        | .ok other => throw (IO.userError s!"expected UIntN 32, got {other.describe}")
        | .error e => throw (IO.userError e) },

    -- §2.6 signed division: rejected with the INT_MIN / -1 edge named
    { name := "signed division (INT_MIN / -1)", run := fun _ =>
        expectReject
          (lowerProgram (program #[
            entry (.ret (.intOp 32 .div (.intLit 32 2147483648) (.intLit 32 4294967295)))
              (.int 32)] (ret := .int 32)))
          "`INT_MIN / -1`" },

    { name := "signed arithmetic is accepted", run := fun _ =>
        match lowerTm #[] #[] #[.i32] {}
            (.intOp 32 .add (.var 0) (.intLit 32 4294967295)) with
        | .ok tm => check (tm.ty == .i32) s!"wrong type {tm.ty.describe}"
        | .error e => throw (IO.userError e) },

    -- §2.6 shifts: the ISA masks by 63/31, Wiz says `k >= w` is 0
    { name := "a 64-bit shift by 64 is rejected", run := fun _ =>
        expectReject
          (lowerTm #[] #[] #[.u64] {} (.shift 64 true (.var 0) 64))
          "the shift amount must be a literal below the width" },
    { name := "a 64-bit shift by 65 is rejected", run := fun _ =>
        expectReject
          (lowerTm #[] #[] #[.u64] {} (.shift 64 false (.var 0) 65))
          "the shift amount must be a literal below the width" },
    { name := "a 64-bit shift by 63 is accepted", run := fun _ =>
        match lowerTm #[] #[] #[.u64] {} (.shift 64 true (.var 0) 63) with
        | .ok _ => pure ()
        | .error e => throw (IO.userError e) },

    -- §5.2 the result is an action enum
    { name := "a `UIntN 32` result is not an action", run := fun _ =>
        expectReject
          (lowerProgram (program #[
            entry (.ret (.uintLit 32 2)) (.uint 32)] #[] (.uint 32)))
          "must be an action enum" },

    -- §2.1 no recursion
    { name := "a call cycle is rejected", run := fun _ =>
        let recDecl : SDecl :=
          { name := "f", params := #[.ctx .xdp], ret := .enum 5
            body := .ret (.call "f" #[.var 0]) }
        expectReject
          (lowerProgram (program #[
            entry (.ret (.call "f" #[.var 0]))
              (.enum 5), recDecl]))
          "the call graph is cyclic" },

    -- §2.7 map values are POD
    { name := "a Packet map value is rejected", run := fun _ =>
        expectReject
          (lowerProgram (passProgram #[
            { name := "m", kind := .hash, key := .uint 32, value := .packet, maxEntries := 16 }]))
          "plain old data" },

    -- §4.4 `partial` is rejected by declaration
    { name := "`partial` is rejected", run := fun _ =>
        expectReject
          (lowerProgram (program #[
            { name := "flow", params := #[.ctx .xdp], ret := .enum 5, isPartial := true
              body := .ret (.enumLit 5 2) }]))
          "has a witness, not a termination measure" },

    -- the whole P0 path, from the checked-in fixture
    { name := "the IPv4 allow-list fixture emits verifier-shaped C", run := fun _ => do
        let text ← IO.FS.readFile "Tests/fixtures/bpf/allow.bpfcore"
        match Wiz.Compiler.Bpf.Sexp.parseCore text with
        | .error e => throw (IO.userError e)
        | .ok core =>
          let maps : Array MapDecl := #[
            { name := "allow", kind := .hash, key := .u32, value := .u8, maxEntries := 4096 },
            { name := "hits", kind := .percpuArray, key := .u32, value := .u64,
              maxEntries := 256 }]
          let prog : Program :=
            { entry := "flow", sectionName := "xdp", kind := .xdp, license := "GPL",
              version := 1, maps, decls := core.decls, ret := core.ret }
          match Wiz.Compiler.Bpf.emitProgram prog with
          | .error e => throw (IO.userError s!"the P0 fixture was rejected: {e}")
          | .ok c => do
            check ((c.splitOn "SEC(\"xdp\")").length > 1) "no SEC(\"xdp\") entry in the C"
            check ((c.splitOn "bpf_map_lookup_elem").length > 1) "no map lookup in the C"
            check ((c.splitOn "pkt_load32be").length > 1) "no checked packet load in the C"
            check ((c.splitOn "__sync_fetch_and_add").length > 1) "no atomic Map.add in the C"
            check ((c.splitOn "#line").length > 1) "no #line directive for the verifier log"
            check ((c.splitOn "static __always_inline").length > 1) "a declaration was not inlined" },

    -- §5.1 the manifest
    { name := "the manifest parses", run := fun _ => do
        let text ← IO.FS.readFile "Tests/fixtures/bpf/allow.toml"
        match parseManifest text with
        | .error e => throw (IO.userError e)
        | .ok m => do
          checkEq "flow" m.program.entry
          checkEq 2 m.maps.size
          match m.maps.find? fun x => x.name == "hits" with
          | some m => checkEq 256 m.maxEntries
          | none => throw (IO.userError "the `hits` map did not parse") }
  ]

builtin_initialize registerGroup group

end Tests.BpfGroup
