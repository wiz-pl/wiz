import Wiz.Compiler.IR
import Wiz.Compiler.Run

/-!
# A WebAssembly target (prototype)

`Wiz.Wasm.program decls` emits a binary WebAssembly module for the IR of an IO-less
`main`. It is **additive**: the C (`Compiler/C.lean`) and LLVM (`Compiler/LLVM.lean`)
backends are unchanged, and `wiz build FILE -o OUT --wasm` selects this one.

The module is self-contained except for a small **JS host** (`web/wasm-host.mjs`), which
provides

* big integers (`Nat` values above 62 bits) through `BigInt`; every other value,
  closure, constructor and array lives in the module's linear memory;
* the decoder that prints a result in the same generic tree syntax as the C runtime
  (`(tag fields…)`, a number, `<fn>`), so `wiz run`'s readback works unchanged.

The representation is the C runtime's: a value is an `i64`; scalars (small numbers, tags,
`◾`) have bit 0 set, objects are pointers into linear memory with a header `{rc, tag,
size, class}` (16 bytes) and `i64` fields. The reference counts the IR's `dup`/`drop`
insert are maintained: the last `drop` releases an object's fields and returns its block
to a **segregated free list**, so peak memory is the peak *live* set, not the total
allocated. `reset`/`reuse` keep and refill a unique cell, as the C runtime does.

Limits and the reason for them are in `docs/stages/08-backend/wasm.md`.
-/

namespace Wiz.Wasm

open IR

/-! ## Bytes, LEB128 and opcodes -/

abbrev Code := Array UInt8

/-- Unsigned LEB128. -/
def uleb (n : Nat) : Code := Id.run do
  let mut n := n
  let mut out : Code := #[]
  let mut more := true
  while more do
    let b := n % 128
    n := n / 128
    if n == 0 then
      out := out.push (UInt8.ofNat b)
      more := false
    else
      out := out.push (UInt8.ofNat (b + 128))
  return out

/-- Signed LEB128 of a non-negative number (all constants this backend emits are). -/
def sleb (n : Nat) : Code := Id.run do
  let mut n := n
  let mut out : Code := #[]
  let mut more := true
  while more do
    let b := n % 128
    n := n / 128
    if n == 0 && b < 64 then
      out := out.push (UInt8.ofNat b)
      more := false
    else
      out := out.push (UInt8.ofNat (b + 128))
  return out

/-- Signed LEB128 (for `i32.const`, whose tags are written as 32-bit signed values). -/
def slebInt (n : Int) : Code := Id.run do
  let mut n := n
  let mut out : Code := #[]
  let mut more := true
  while more do
    let b := n % 128
    n := n / 128
    if (n == 0 && b < 64) || (n == -1 && b >= 64) then
      out := out.push (UInt8.ofNat b.toNat)
      more := false
    else
      out := out.push (UInt8.ofNat (b.toNat + 128))
  return out

def strBytes (s : String) : Code := s.toUTF8.data

def nameBytes (s : String) : Code := uleb s.utf8ByteSize ++ strBytes s

/-- Value types. -/
inductive VT where
  | i32
  | i64
  deriving Repr, BEq, Inhabited

def VT.byte : VT → UInt8
  | .i32 => 0x7F
  | .i64 => 0x7E

/-- A function signature. -/
structure FnSig where
  params : Array VT
  results : Array VT
  deriving Repr, BEq, Inhabited

/-! ### Instructions (the subset this backend uses) -/

def unreachable : Code := #[0x00]
def nop : Code := #[0x01]
def block : Code := #[0x02, 0x40]
def loop : Code := #[0x03, 0x40]
def if_ : Code := #[0x04, 0x40]
def else_ : Code := #[0x05]
def end_ : Code := #[0x0B]
def br (d : Nat) : Code := #[0x0C] ++ uleb d
def brIf (d : Nat) : Code := #[0x0D] ++ uleb d
def ret : Code := #[0x0F]
def call (i : Nat) : Code := #[0x10] ++ uleb i
def callIndirect (ty table : Nat) : Code := #[0x11] ++ uleb ty ++ uleb table
def drop : Code := #[0x1A]
def select : Code := #[0x1B]
def lg (i : Nat) : Code := #[0x20] ++ uleb i
def ls (i : Nat) : Code := #[0x21] ++ uleb i
def lt (i : Nat) : Code := #[0x22] ++ uleb i
def gg (i : Nat) : Code := #[0x23] ++ uleb i
def gs (i : Nat) : Code := #[0x24] ++ uleb i
def gg0 : Code := gg 0
def gs0 : Code := gs 0
/-- `i32.const`, wrapping a tag (such as `0xFFFF0000`) to its signed 32-bit value. -/
def i32c (n : Nat) : Code :=
  #[0x41] ++ slebInt (if n < 2 ^ 31 then Int.ofNat n else Int.ofNat n - 2 ^ 32)
def i64c (n : Nat) : Code := #[0x42] ++ sleb n
def i32Load (align off : Nat) : Code := #[0x28] ++ uleb align ++ uleb off
def i64Load (align off : Nat) : Code := #[0x29] ++ uleb align ++ uleb off
def i32Store (align off : Nat) : Code := #[0x36] ++ uleb align ++ uleb off
def i64Store (align off : Nat) : Code := #[0x37] ++ uleb align ++ uleb off

def i32Eqz : Code := #[0x45]
def i32Eq : Code := #[0x46]
def i32Ne : Code := #[0x47]
def i32LtS : Code := #[0x48]
def i32LtU : Code := #[0x49]
def i32GtS : Code := #[0x4A]
def i32GtU : Code := #[0x4B]
def i32LeU : Code := #[0x4D]
def i32GeU : Code := #[0x4F]
def i32Clz : Code := #[0x67]
def i32Add : Code := #[0x6A]
def i32Sub : Code := #[0x6B]
def i32Mul : Code := #[0x6C]
def i32DivU : Code := #[0x6E]
def i32RemU : Code := #[0x70]
def i32And : Code := #[0x71]
def i32Or : Code := #[0x72]
def i32Xor : Code := #[0x73]
def i32Shl : Code := #[0x74]
def i32ShrU : Code := #[0x76]

def i64Eqz : Code := #[0x50]
def i64Eq : Code := #[0x51]
def i64Ne : Code := #[0x52]
def i64LtU : Code := #[0x54]
def i64GtU : Code := #[0x56]
def i64LeU : Code := #[0x58]
def i64GeU : Code := #[0x5A]
def i64Add : Code := #[0x7C]
def i64Sub : Code := #[0x7D]
def i64Mul : Code := #[0x7E]
def i64DivU : Code := #[0x80]
def i64RemU : Code := #[0x82]
def i64And : Code := #[0x83]
def i64Or : Code := #[0x84]
def i64Xor : Code := #[0x85]
def i64Shl : Code := #[0x86]
def i64ShrU : Code := #[0x88]
def i64Clz : Code := #[0x79]
def i64ExtendI32U : Code := #[0xAD]
def i32WrapI64 : Code := #[0xA7]

def memSize : Code := #[0x3F, 0x00]
def memGrow : Code := #[0x40, 0x00]

/-! ## Layout constants -/

/-- Scratch memory for `pap`/`ap` arguments: 8 + 256 × 8 bytes, below the data. -/
def scratchBase : Nat := 8
def maxCallArgs : Nat := 256
/-- Big literals' decimal text starts here. -/
def dataBase : Nat := 4096
/-- The free lists' heads: one `i32` per size class, just above the argument scratch. -/
def bucketBase : Nat := scratchBase + 8 * maxCallArgs
/-- The global holding the head of the release work list (global 0 is the bump pointer). -/
def deadHeadGlobal : Nat := 1
/-- The tag of a closure (as in `runtime/wiz_rt.h`). -/
def tagClo : Nat := 0xFFFF0000
def tagBig : Nat := 0xFFFF0001
def tagArray : Nat := 0xFFFF0005
def tagThunk : Nat := 0xFFFF0008
/-- `2^62 - 1`, the largest small `Nat`. -/
def maxSmall : Nat := 2 ^ 62 - 1

/-! ## Host imports -/

/-- The JS host's imports, in function-index order. -/
def hostSigs : Array (String × FnSig) := #[
  ("big_of_dec", { params := #[.i32, .i32], results := #[.i64] }),
  ("big_op", { params := #[.i32, .i64, .i64, .i64, .i64], results := #[.i64] }),
  ("big_cmp", { params := #[.i64, .i64, .i64, .i64], results := #[.i32] }),
  ("big_log2", { params := #[.i64, .i64], results := #[.i64] }),
  ("big_to_dec", { params := #[.i64, .i32], results := #[.i32] })
]

def hostIndex (name : String) : Nat := (hostSigs.findIdx? (·.1 == name)).getD 0
def iBigOfDec : Nat := hostIndex "big_of_dec"
def iBigOp : Nat := hostIndex "big_op"
def iBigCmp : Nat := hostIndex "big_cmp"
def iBigLog2 : Nat := hostIndex "big_log2"
def iBigToDec : Nat := hostIndex "big_to_dec"

/-! ## The runtime, in Wasm

Each function has a comment naming its locals (by index) and mirrors the C runtime's
behaviour (`runtime/rt_*.inc`), minus reference counting. -/

structure FnDef where
  name : String
  params : Array VT := #[]
  results : Array VT := #[.i64]
  locals : Array VT := #[]
  code : Code := #[]

/-- `boxI32`: an `i32` on the stack as a Wiz scalar. -/
def boxI32 : Code := i64ExtendI32U ++ i64c 1 ++ i64Shl ++ i64c 1 ++ i64Or

/-- `boxI64`: a (small) `i64` on the stack as a Wiz scalar. -/
def boxI64 : Code := i64c 1 ++ i64Shl ++ i64c 1 ++ i64Or

/-- The runtime functions, in function-index order (right after the five imports). -/
def runtimeNames : Array String := #[
  "wiz_alloc_raw", "wiz_alloc_obj", "wiz_free_raw", "wiz_claim", "wiz_drain",
  "wiz_ctor_new", "wiz_set", "wiz_tag", "wiz_proj", "wiz_inc", "wiz_dec", "wiz_reset",
  "wiz_reuse", "wiz_drop_moved", "wiz_clo_new", "wiz_apply",
  "wiz_memo", "wiz_lazy_tag", "wiz_lazy_set", "wiz_tag_of", "wiz_nat_tag",
  "wiz_field_at", "wiz_mk_obj", "wiz_nat_norm", "wiz_big_handle", "wiz_big_small",
  "wiz_nat_add", "wiz_nat_sub", "wiz_nat_mul", "wiz_nat_div", "wiz_nat_mod",
  "wiz_nat_land", "wiz_nat_lor", "wiz_nat_xor", "wiz_nat_shiftLeft",
  "wiz_nat_shiftRight", "wiz_nat_pow", "wiz_nat_log2", "wiz_nat_beq", "wiz_nat_blt",
  "wiz_array_new", "wiz_array_empty", "wiz_array_push", "wiz_array_size",
  "wiz_array_get", "wiz_array_set", "wiz_big_to_string", "wiz_big_digits"
]

def rtIdx (name : String) : Nat :=
  hostSigs.size + ((runtimeNames.findIdx? (· == name)).getD 0)

def runtimeSigs : Array FnSig := #[
  { params := #[.i32], results := #[.i32] },                          -- alloc_raw
  { params := #[.i32, .i32], results := #[.i32] },                    -- alloc_obj
  { params := #[.i32], results := #[] },                              -- free_raw
  { params := #[.i32], results := #[] },                              -- claim
  { params := #[], results := #[] },                                  -- drain
  { params := #[.i32, .i32], results := #[.i64] },                    -- ctor_new
  { params := #[.i64, .i32, .i64], results := #[] },                  -- set
  { params := #[.i64], results := #[.i32] },                          -- tag
  { params := #[.i64, .i32], results := #[.i64] },                    -- proj
  { params := #[.i64], results := #[] },                              -- inc
  { params := #[.i64], results := #[] },                              -- dec
  { params := #[.i64], results := #[.i64] },                          -- reset
  { params := #[.i64, .i32, .i32], results := #[.i64] },              -- reuse
  { params := #[.i64, .i64], results := #[.i64] },                    -- drop_moved
  { params := #[.i32, .i32, .i32, .i32], results := #[.i64] },        -- clo_new
  { params := #[.i64, .i32, .i32], results := #[.i64] },              -- apply
  { params := #[.i64, .i64], results := #[.i64] },                    -- memo
  { params := #[.i64], results := #[.i64] },                          -- lazy_tag
  { params := #[.i64, .i64], results := #[.i64] },                    -- lazy_set
  { params := #[.i64], results := #[.i64] },                          -- tag_of
  { params := #[.i64], results := #[.i64] },                          -- nat_tag
  { params := #[.i64, .i64], results := #[.i64] },                    -- field_at
  { params := #[.i64, .i64], results := #[.i64] },                    -- mk_obj
  { params := #[.i64], results := #[.i64] },                          -- nat_norm
  { params := #[.i64], results := #[.i64] },                          -- big_handle
  { params := #[.i64], results := #[.i64] },                          -- big_small
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_add
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_sub
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_mul
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_div
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_mod
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_land
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_lor
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_xor
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_shiftLeft
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_shiftRight
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_pow
  { params := #[.i64], results := #[.i64] },                          -- nat_log2
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_beq
  { params := #[.i64, .i64], results := #[.i64] },                    -- nat_blt
  { params := #[.i32], results := #[.i64] },                          -- array_new
  { params := #[], results := #[.i64] },                              -- array_empty
  { params := #[.i64, .i64], results := #[.i64] },                    -- array_push
  { params := #[.i64], results := #[.i64] },                          -- array_size
  { params := #[.i64, .i64, .i64], results := #[.i64] },              -- array_get
  { params := #[.i64, .i64, .i64], results := #[.i64] },              -- array_set
  { params := #[.i64, .i32], results := #[.i32] },                    -- big_to_string
  { params := #[.i64], results := #[.i64] }                           -- big_digits
]

def runtimeSig (name : String) : FnSig :=
  runtimeSigs.getD ((runtimeNames.findIdx? (· == name)).getD 0) { params := #[], results := #[] }

/-- The runtime's function bodies.

Every object is reference counted: a header `{rc, tag, size, class}` (the fourth word is
the block's size class while it is live, and the next pointer while it is free) and `i64`
fields. `dup`/`drop` are `wiz_inc`/`wiz_dec`; the last drop releases the object's fields
and returns its block to a segregated free list, so memory is bounded by the peak live
set, not by the total allocated. -/
def runtimeDefs (boxedType : Nat) : Array FnDef := Id.run do
  let mut out : Array FnDef := #[]
  let rt := rtIdx
  -- `wiz_alloc_raw(bytes)`: a block of at least `bytes` bytes, from the free list of its
  -- size class or from the bump pointer. The block's class is kept at offset 12.
  out := out.push {
    name := "wiz_alloc_raw", params := #[.i32], results := #[.i32]
    locals := #[.i32, .i32, .i32, .i32, .i32]
    code :=
      -- locals: need=1, k=2, p=3, cap=4, grew=5
      lg 0 ++ i32c 7 ++ i32Add ++ i32c 0xFFFFFFF8 ++ i32And ++ ls 1 ++
      lg 1 ++ i32c 16 ++ i32LtU ++ if_ ++ i32c 16 ++ ls 1 ++ end_ ++
      -- (a single block is at most 1 GiB: beyond that the module traps, it does not
      -- silently wrap the class index)
      lg 1 ++ i32c 0x40000000 ++ i32GtU ++ if_ ++ unreachable ++ end_ ++
      -- k: fields 0..63 are exact sizes (16+8k bytes), then powers of two from 1 KiB
      lg 1 ++ i32c 521 ++ i32LtU ++ if_
        ++ lg 1 ++ i32c 16 ++ i32Sub ++ i32c 3 ++ i32ShrU ++ ls 2
        ++ else_ ++ lg 1 ++ i32c 1 ++ i32Sub ++ i32Clz ++ i32c 86 ++ i32Sub ++ ls 2 ++ end_ ++
      -- p = free[k]
      lg 2 ++ i32c 4 ++ i32Mul ++ i32c bucketBase ++ i32Add ++ i32Load 2 0 ++ ls 3 ++
      lg 3 ++ if_
        ++ -- pop: free[k] = p.next
        lg 2 ++ i32c 4 ++ i32Mul ++ i32c bucketBase ++ i32Add ++
           lg 3 ++ i32Load 2 12 ++ i32Store 2 0
        ++ else_ ++
        -- bump: p = top; cap = cap(k); top += cap
        gg0 ++ ls 3 ++
        lg 2 ++ i32c 63 ++ i32LeU ++ if_
          ++ lg 2 ++ i32c 8 ++ i32Mul ++ i32c 16 ++ i32Add ++ ls 4
          ++ else_ ++ i32c 1 ++ lg 2 ++ i32c 54 ++ i32Sub ++ i32Shl ++ ls 4 ++ end_ ++
        block ++ loop ++
          memSize ++ i32c 65536 ++ i32Mul ++ lg 3 ++ lg 4 ++ i32Add ++ i32GeU ++ brIf 1 ++
          i32c 1 ++ memGrow ++ ls 5 ++
          -- (a failed grow is a trap, not a spin: the engine's limit is reached)
          lg 5 ++ i32c 0xFFFFFFFF ++ i32Eq ++ if_ ++ unreachable ++ end_ ++
          br 0 ++
        end_ ++ end_ ++
        lg 3 ++ lg 4 ++ i32Add ++ gs0
        ++ end_ ++
      -- p.class = k
      lg 3 ++ lg 2 ++ i32Store 2 12 ++
      lg 3 ++ ret }
  -- `wiz_alloc_obj(tag, n)`: a header (rc 1) and `n` fields (16 bytes, 8-aligned).
  out := out.push {
    name := "wiz_alloc_obj", params := #[.i32, .i32], results := #[.i32], locals := #[.i32, .i32]
    code :=
      -- locals: bytes=2, p=3
      i32c 16 ++ lg 1 ++ i32c 8 ++ i32Mul ++ i32Add ++ ls 2 ++
      lg 2 ++ call (rt "wiz_alloc_raw") ++ ls 3 ++
      lg 3 ++ i32c 1 ++ i32Store 2 0 ++
      lg 3 ++ lg 0 ++ i32Store 2 4 ++
      lg 3 ++ lg 1 ++ i32Store 2 8 ++
      lg 3 ++ ret }
  -- `wiz_free_raw(p)`: the block of `p` back to its class's free list (no fields are
  -- released: the caller did that, or there are none).
  out := out.push {
    name := "wiz_free_raw", params := #[.i32], results := #[], locals := #[.i32]
    code :=
      -- locals: k=1
      lg 0 ++ i32Load 2 12 ++ ls 1 ++
      lg 0 ++ lg 1 ++ i32c 4 ++ i32Mul ++ i32c bucketBase ++ i32Add ++ i32Load 2 0
        ++ i32Store 2 12 ++
      lg 1 ++ i32c 4 ++ i32Mul ++ i32c bucketBase ++ i32Add ++ lg 0 ++ i32Store 2 0 ++
      ret }
  -- `wiz_claim(p)`: `p`'s count has reached 0: mark it dead (a negative count) and thread
  -- it on the release work list of the global at index 1, so a long chain is freed
  -- iteratively, not on the engine's stack.
  out := out.push {
    name := "wiz_claim", params := #[.i32], results := #[], locals := #[.i32]
    code :=
      -- locals: k=1
      lg 0 ++ i32Load 2 12 ++ ls 1 ++
      lg 0 ++ i32c 0xFFFFFFFF ++ lg 1 ++ i32Sub ++ i32Store 2 0 ++
      lg 0 ++ gg deadHeadGlobal ++ i32Store 2 12 ++
      lg 0 ++ gs deadHeadGlobal ++
      ret }
  -- `wiz_drain()`: free every object on the work list: release its fields (claiming each
  -- child whose count drops to 0) and put its block back in its size class's free list.
  out := out.push {
    name := "wiz_drain", params := #[], results := #[]
    locals := #[.i32, .i32, .i32, .i32, .i32, .i32, .i64, .i32, .i32]
    code :=
      -- locals: q=0, k=1, i=2, last=3, n=4, tag=5, c=6, cp=7, rc=8
      block ++ loop ++
        gg deadHeadGlobal ++ i32Eqz ++ brIf 1 ++
        gg deadHeadGlobal ++ ls 0 ++
        lg 0 ++ i32Load 2 12 ++ gs deadHeadGlobal ++
        -- k was stored as `-(k+1)` in the count of a dead object
        i32c 0xFFFFFFFF ++ lg 0 ++ i32Load 2 0 ++ i32Sub ++ ls 1 ++
        lg 0 ++ i32Load 2 8 ++ ls 4 ++
        lg 0 ++ i32Load 2 4 ++ ls 5 ++
        -- the fields that hold references: a closure's skip its table and arity, an
        -- array's are its live elements only, a big number's one field is a host handle
        i32c 0 ++ ls 2 ++ lg 4 ++ ls 3 ++
        lg 5 ++ i32c tagClo ++ i32Eq ++ if_ ++ i32c 2 ++ ls 2 ++ end_ ++
        lg 5 ++ i32c tagArray ++ i32Eq ++ if_
          ++ lg 0 ++ i64Load 3 16 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ i32c 2 ++ i32Add ++ ls 3
          ++ end_ ++
        lg 5 ++ i32c tagBig ++ i32Eq ++ if_ ++ i32c 0 ++ ls 3 ++ end_ ++
        block ++ loop ++
          lg 2 ++ lg 3 ++ i32GeU ++ brIf 1 ++
          lg 0 ++ i32c 16 ++ i32Add ++ lg 2 ++ i32c 8 ++ i32Mul ++ i32Add ++ i64Load 3 0 ++ ls 6 ++
          lg 6 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
            ++ lg 6 ++ i32WrapI64 ++ ls 7 ++
               lg 7 ++ i32Load 2 0 ++ ls 8 ++
               lg 8 ++ i32c 1 ++ i32GtU ++ if_
                 ++ lg 7 ++ lg 8 ++ i32c 1 ++ i32Sub ++ i32Store 2 0
                 ++ else_ ++ lg 8 ++ i32c 1 ++ i32Eq ++ if_
                    ++ lg 7 ++ call (rt "wiz_claim") ++ end_
                 ++ end_
            ++ end_ ++
          lg 2 ++ i32c 1 ++ i32Add ++ ls 2 ++ br 0 ++
        end_ ++ end_ ++
        -- put q's block back in the free list of its class
        lg 0 ++ lg 1 ++ i32c 4 ++ i32Mul ++ i32c bucketBase ++ i32Add ++ i32Load 2 0
          ++ i32Store 2 12 ++
        lg 1 ++ i32c 4 ++ i32Mul ++ i32c bucketBase ++ i32Add ++ lg 0 ++ i32Store 2 0 ++
        br 0 ++
      end_ ++ end_ ++
      ret }
  -- `wiz_ctor_new(tag, n)`: the fields start as `◾` (owned by nobody yet).
  out := out.push {
    name := "wiz_ctor_new", params := #[.i32, .i32], results := #[.i64], locals := #[.i32, .i32]
    code :=
      -- locals: p=2, i=3
      lg 0 ++ lg 1 ++ call (rt "wiz_alloc_obj") ++ ls 2 ++
      i32c 0 ++ ls 3 ++
      block ++ loop ++
        lg 3 ++ lg 1 ++ i32GeU ++ brIf 1 ++
        lg 2 ++ i32c 16 ++ i32Add ++ lg 3 ++ i32c 8 ++ i32Mul ++ i32Add ++ i64c 1 ++ i64Store 3 0 ++
        lg 3 ++ i32c 1 ++ i32Add ++ ls 3 ++ br 0 ++
      end_ ++ end_ ++
      lg 2 ++ i64ExtendI32U ++ ret }
  -- `wiz_set(o, i, v)`: the field of a fresh cell (its old value is `◾`).
  out := out.push {
    name := "wiz_set", params := #[.i64, .i32, .i64], results := #[]
    code :=
      lg 0 ++ i32WrapI64 ++ i32c 16 ++ i32Add ++ lg 1 ++ i32c 8 ++ i32Mul ++ i32Add ++
      lg 2 ++ i64Store 3 0 ++ ret }
  -- `wiz_tag(v)`: a scalar's value, or an object's tag (borrows `v`).
  out := out.push {
    name := "wiz_tag", params := #[.i64], results := #[.i32], locals := #[.i32]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ i32Load 2 4 ++ ls 1
        ++ else_ ++ lg 0 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 1
        ++ end_ ++ lg 1 ++ ret }
  -- `wiz_proj(v, i)`: borrowed field access (a number's field 0 is its unary tag).
  out := out.push {
    name := "wiz_proj", params := #[.i64, .i32], results := #[.i64], locals := #[.i64, .i32]
    code :=
      -- locals: r=2, tag=3
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ i32Load 2 4 ++ ls 3 ++
        lg 3 ++ i32c tagBig ++ i32Eq ++ if_
          ++ -- (a number's unary view: 0 for zero, 1 otherwise)
          lg 1 ++ i32Eqz ++ if_ ++ i64c 3 ++ ret ++ else_ ++ unreachable ++ end_
          ++ end_ ++
        lg 0 ++ i32WrapI64 ++ lg 1 ++ i32c 8 ++ i32Mul ++ i32Add ++ i64Load 3 16 ++ ret
        ++ else_ ++
        lg 0 ++ i64c 1 ++ i64Eq ++ if_ ++ i64c 1 ++ ret ++ end_ ++
        lg 1 ++ i32Eqz ++ if_
          ++ lg 0 ++ i64c 1 ++ i64ShrU ++ i64Eqz ++ if_
            ++ i64c 1 ++ ls 2 ++ else_ ++ i64c 3 ++ ls 2 ++ end_ ++ lg 2 ++ ret
          ++ else_ ++ unreachable ++ end_
        ++ end_ }
  -- `wiz_inc(v)`: one more reference to `v` (a scalar is free).
  out := out.push {
    name := "wiz_inc", params := #[.i64], results := #[], locals := #[.i32, .i32]
    code :=
      -- locals: p=1, rc=2
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ ls 1 ++
           lg 1 ++ i32Load 2 0 ++ ls 2 ++
           lg 2 ++ i32c 0 ++ i32GtU ++ if_
             ++ lg 1 ++ lg 2 ++ i32c 1 ++ i32Add ++ i32Store 2 0
           ++ end_
        ++ end_ ++ ret }
  -- `wiz_dec(v)`: drop a reference; the last one releases the object.
  out := out.push {
    name := "wiz_dec", params := #[.i64], results := #[], locals := #[.i32, .i32]
    code :=
      -- locals: p=1, rc=2
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ ls 1 ++
           lg 1 ++ i32Load 2 0 ++ ls 2 ++
           lg 2 ++ i32c 1 ++ i32GtU ++ if_
             ++ lg 1 ++ lg 2 ++ i32c 1 ++ i32Sub ++ i32Store 2 0
             ++ else_ ++ lg 2 ++ i32c 1 ++ i32Eq ++ if_
               ++ lg 1 ++ call (rt "wiz_claim") ++ call (rt "wiz_drain")
               ++ end_
             ++ end_
        ++ end_ ++ ret }
  -- `wiz_reset(x)`: drop `x`, keeping its cell as a token when it is a unique
  -- constructor (its fields are released here; `reuse` refills it).
  out := out.push {
    name := "wiz_reset", params := #[.i64], results := #[.i64]
    locals := #[.i32, .i32, .i32, .i32, .i32]
    code :=
      -- locals: p=1, rc=2, tag=3, n=4, i=5
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ ls 1 ++
           lg 1 ++ i32Load 2 0 ++ ls 2 ++
           lg 1 ++ i32Load 2 4 ++ ls 3 ++
           lg 2 ++ i32c 1 ++ i32Eq ++ lg 3 ++ i32c tagClo ++ i32LtU ++ i32And ++ if_
             ++ lg 1 ++ i32Load 2 8 ++ ls 4 ++
                i32c 0 ++ ls 5 ++
                block ++ loop ++
                  lg 5 ++ lg 4 ++ i32GeU ++ brIf 1 ++
                  lg 1 ++ i32c 16 ++ i32Add ++ lg 5 ++ i32c 8 ++ i32Mul ++ i32Add ++
                  i64Load 3 0 ++ call (rt "wiz_dec") ++
                  lg 5 ++ i32c 1 ++ i32Add ++ ls 5 ++ br 0 ++
                end_ ++ end_ ++
                lg 0 ++ ret
             ++ else_ ++ lg 0 ++ call (rt "wiz_dec") ++ i64c 1 ++ ret ++ end_
        ++ end_ ++
      i64c 1 ++ ret }
  -- `wiz_reuse(tok, tag, n)`: `ctor tag n`, in the token's cell when its size matches.
  out := out.push {
    name := "wiz_reuse", params := #[.i64, .i32, .i32], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ i32Load 2 8 ++ lg 2 ++ i32Eq ++ if_
          ++ lg 0 ++ i32WrapI64 ++ lg 1 ++ i32Store 2 4 ++ lg 0 ++ ret
          ++ else_ ++ lg 0 ++ i32WrapI64 ++ call (rt "wiz_free_raw") ++ end_
        ++ end_ ++
      lg 2 ++ i32Eqz ++ if_ ++ lg 1 ++ boxI32 ++ ret ++ end_ ++
      lg 1 ++ lg 2 ++ call (rt "wiz_ctor_new") ++ ret }
  -- `wiz_drop_moved(x, mask)`: drop `x`, whose fields in `mask` moved out (a unique
  -- cell's others are released and the cell freed; a shared one lends them a reference).
  out := out.push {
    name := "wiz_drop_moved", params := #[.i64, .i64], results := #[.i64]
    locals := #[.i32, .i32, .i32, .i32, .i32, .i64, .i32]
    code :=
      -- locals: p=2, tag=3, rc=4, n=5, i=6, m=7, keep=8
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ ls 2 ++
           lg 2 ++ i32Load 2 4 ++ ls 3 ++
           lg 3 ++ i32c tagClo ++ i32GeU ++ if_
             ++ lg 0 ++ call (rt "wiz_dec")
             ++ else_ ++
                lg 2 ++ i32Load 2 0 ++ ls 4 ++
                lg 2 ++ i32Load 2 8 ++ ls 5 ++
                lg 1 ++ i64c 1 ++ i64ShrU ++ ls 7 ++
                lg 4 ++ i32c 1 ++ i32Eq ++ if_
                  ++ i32c 0 ++ ls 6 ++
                     block ++ loop ++
                       lg 6 ++ lg 5 ++ i32GeU ++ brIf 1 ++
                       i32c 0 ++ ls 8 ++
                       lg 6 ++ i32c 62 ++ i32LtU ++ if_
                         ++ lg 7 ++ lg 6 ++ i64ExtendI32U ++ i64ShrU ++ i64c 1 ++
                            i64And ++ i32WrapI64 ++ ls 8
                         ++ end_ ++
                       lg 8 ++ i32Eqz ++ if_
                         ++ lg 2 ++ i32c 16 ++ i32Add ++ lg 6 ++ i32c 8 ++ i32Mul ++
                            i32Add ++ i64Load 3 0 ++ call (rt "wiz_dec")
                         ++ end_ ++
                       lg 6 ++ i32c 1 ++ i32Add ++ ls 6 ++ br 0 ++
                     end_ ++ end_ ++
                     lg 2 ++ call (rt "wiz_free_raw")
                  ++ else_ ++
                     i32c 0 ++ ls 6 ++
                     block ++ loop ++
                       lg 6 ++ lg 5 ++ i32GeU ++ brIf 1 ++
                       i32c 0 ++ ls 8 ++
                       lg 6 ++ i32c 62 ++ i32LtU ++ if_
                         ++ lg 7 ++ lg 6 ++ i64ExtendI32U ++ i64ShrU ++ i64c 1 ++
                            i64And ++ i32WrapI64 ++ ls 8
                         ++ end_ ++
                       lg 8 ++ if_
                         ++ lg 2 ++ i32c 16 ++ i32Add ++ lg 6 ++ i32c 8 ++ i32Mul ++
                            i32Add ++ i64Load 3 0 ++ call (rt "wiz_inc")
                         ++ end_ ++
                       lg 6 ++ i32c 1 ++ i32Add ++ ls 6 ++ br 0 ++
                     end_ ++ end_ ++
                     lg 0 ++ call (rt "wiz_dec")
                  ++ end_
             ++ end_
        ++ end_ ++
      i64c 1 ++ ret }
  -- `wiz_clo_new(table, arity, n, args)`: a closure owning the `n` arguments.
  out := out.push {
    name := "wiz_clo_new", params := #[.i32, .i32, .i32, .i32], results := #[.i64], locals := #[.i64, .i32]
    code :=
      -- locals: p=4, i=5
      i32c tagClo ++ lg 2 ++ i32c 2 ++ i32Add ++ call (rt "wiz_ctor_new") ++ ls 4 ++
      lg 4 ++ i32WrapI64 ++ lg 0 ++ boxI32 ++ i64Store 3 16 ++
      lg 4 ++ i32WrapI64 ++ lg 1 ++ boxI32 ++ i64Store 3 24 ++
      i32c 0 ++ ls 5 ++
      block ++ loop ++
        lg 5 ++ lg 2 ++ i32GeU ++ brIf 1 ++
        lg 4 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 5 ++ i32c 8 ++ i32Mul ++ i32Add ++
        lg 3 ++ lg 5 ++ i32c 8 ++ i32Mul ++ i32Add ++ i64Load 3 0 ++ i64Store 3 0 ++
        lg 5 ++ i32c 1 ++ i32Add ++ ls 5 ++ br 0 ++
      end_ ++ end_ ++ lg 4 ++ ret }
  -- `wiz_apply(f, n, args)`: apply (owned) `f` to `n` (owned) arguments: force a thunk,
  -- combine with a closure's captured arguments, then call, partially apply, or apply the
  -- result again. The argument buffers are returned to the free list.
  out := out.push {
    name := "wiz_apply", params := #[.i64, .i32, .i32], results := #[.i64]
    locals := #[.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i64, .i64, .i32, .i32]
    code :=
      -- locals: buf=3, i=4, tag=5, m=6, arity=7, total=8, buf2=9, r=10, fn=11,
      --         table=12, rc=13
      lg 1 ++ i32c 8 ++ i32Mul ++ call (rt "wiz_alloc_raw") ++ ls 3 ++
      i32c 0 ++ ls 4 ++
      block ++ loop ++
        lg 4 ++ lg 1 ++ i32GeU ++ brIf 1 ++
        lg 3 ++ lg 4 ++ i32c 8 ++ i32Mul ++ i32Add ++
        lg 2 ++ lg 4 ++ i32c 8 ++ i32Mul ++ i32Add ++ i64Load 3 0 ++ i64Store 3 0 ++
        lg 4 ++ i32c 1 ++ i32Add ++ ls 4 ++ br 0 ++
      end_ ++ end_ ++
      lg 0 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ -- a scalar: `◾` applied is `◾` (its arguments are dropped)
        lg 0 ++ i64c 1 ++ i64Eq ++ if_
          ++ lg 3 ++ call (rt "wiz_free_raw") ++ i64c 1 ++ ret
          ++ end_ ++
        unreachable
        ++ else_ ++
        lg 0 ++ i32WrapI64 ++ i32Load 2 4 ++ ls 5 ++
        lg 5 ++ i32c tagThunk ++ i32Eq ++ if_
          ++ -- a thunk: force it, store the value, and hand out a reference
          lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ ls 11 ++
          lg 11 ++ i64c 1 ++ i64Eq ++ if_
            ++ -- already forced: the first argument (the unit) is dropped
            lg 3 ++ i64Load 3 0 ++ call (rt "wiz_dec") ++
            lg 0 ++ i32WrapI64 ++ i64Load 3 24 ++ ls 10
            ++ else_ ++
            -- blackhole while forcing (a recursive thunk re-enters its body, as before)
            lg 0 ++ i32WrapI64 ++ i64c 1 ++ i64Store 3 16 ++
            lg 11 ++ i32c 1 ++ lg 3 ++ call (rt "wiz_apply") ++ ls 10 ++
            lg 0 ++ i32WrapI64 ++ lg 10 ++ i64Store 3 24
            ++ end_ ++
          lg 10 ++ call (rt "wiz_inc") ++
          lg 0 ++ call (rt "wiz_dec") ++
          lg 1 ++ i32c 1 ++ i32GtU ++ if_
            ++ lg 10 ++ lg 1 ++ i32c 1 ++ i32Sub ++ lg 3 ++ i32c 8 ++ i32Add ++
               call (rt "wiz_apply") ++ ls 10
            ++ end_ ++
          lg 3 ++ call (rt "wiz_free_raw") ++
          lg 10 ++ ret
          ++ else_ ++
          lg 5 ++ i32c tagClo ++ i32Ne ++ if_ ++ unreachable ++ end_ ++
          lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 12 ++
          lg 0 ++ i32WrapI64 ++ i64Load 3 24 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 7 ++
          lg 0 ++ i32WrapI64 ++ i32Load 2 8 ++ i32c 2 ++ i32Sub ++ ls 6 ++
          lg 6 ++ lg 1 ++ i32Add ++ ls 8 ++
          lg 8 ++ i32c 8 ++ i32Mul ++ call (rt "wiz_alloc_raw") ++ ls 9 ++
          -- the captured arguments
          i32c 0 ++ ls 4 ++
          block ++ loop ++
            lg 4 ++ lg 6 ++ i32GeU ++ brIf 1 ++
            lg 9 ++ lg 4 ++ i32c 8 ++ i32Mul ++ i32Add ++
            lg 0 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 4 ++ i32c 8 ++ i32Mul ++ i32Add ++
            i64Load 3 0 ++ i64Store 3 0 ++
            lg 4 ++ i32c 1 ++ i32Add ++ ls 4 ++ br 0 ++
          end_ ++ end_ ++
          -- the given arguments
          i32c 0 ++ ls 4 ++
          block ++ loop ++
            lg 4 ++ lg 1 ++ i32GeU ++ brIf 1 ++
            lg 9 ++ lg 6 ++ lg 4 ++ i32Add ++ i32c 8 ++ i32Mul ++ i32Add ++
            lg 3 ++ lg 4 ++ i32c 8 ++ i32Mul ++ i32Add ++ i64Load 3 0 ++ i64Store 3 0 ++
            lg 4 ++ i32c 1 ++ i32Add ++ ls 4 ++ br 0 ++
          end_ ++ end_ ++
          -- the closure itself: a unique one's arguments move into `buf2`, a shared
          -- one's are shared and the closure is dropped
          lg 0 ++ i32WrapI64 ++ i32Load 2 0 ++ ls 13 ++
          lg 13 ++ i32c 1 ++ i32Eq ++ if_
            ++ lg 0 ++ i32WrapI64 ++ call (rt "wiz_free_raw")
            ++ else_ ++
               i32c 0 ++ ls 4 ++
               block ++ loop ++
                 lg 4 ++ lg 6 ++ i32GeU ++ brIf 1 ++
                 lg 9 ++ lg 4 ++ i32c 8 ++ i32Mul ++ i32Add ++ i64Load 3 0 ++
                 call (rt "wiz_inc") ++
                 lg 4 ++ i32c 1 ++ i32Add ++ ls 4 ++ br 0 ++
               end_ ++ end_ ++
               lg 0 ++ call (rt "wiz_dec")
            ++ end_ ++
          lg 8 ++ lg 7 ++ i32LtU ++ if_
            ++ lg 12 ++ lg 7 ++ lg 8 ++ lg 9 ++ call (rt "wiz_clo_new") ++ ls 10
            ++ else_ ++
               lg 9 ++ lg 12 ++ callIndirect boxedType 0 ++ ls 10 ++
               lg 8 ++ lg 7 ++ i32GtU ++ if_
                 ++ lg 10 ++ lg 8 ++ lg 7 ++ i32Sub ++
                    lg 9 ++ lg 7 ++ i32c 8 ++ i32Mul ++ i32Add ++
                    call (rt "wiz_apply") ++ ls 10
                 ++ end_
            ++ end_ ++
          lg 3 ++ call (rt "wiz_free_raw") ++
          lg 9 ++ call (rt "wiz_free_raw") ++
          lg 10 ++ ret
          ++ end_
        ++ end_ }
  -- `wiz_memo(ty, f)`: a fresh, unforced suspension that owns `f`.
  out := out.push {
    name := "wiz_memo", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      lg 0 ++ call (rt "wiz_dec") ++
      i32c tagThunk ++ i32c 2 ++ call (rt "wiz_ctor_new") ++ ls 2 ++
      lg 2 ++ i32WrapI64 ++ lg 1 ++ i64Store 3 16 ++
      lg 2 ++ i32WrapI64 ++ i64c 1 ++ i64Store 3 24 ++
      lg 2 ++ ret }
  -- `wiz_lazy_tag(v)`: the observation of a codata value (it consumes `v`).
  out := out.push {
    name := "wiz_lazy_tag", params := #[.i64], results := #[.i64], locals := #[.i32, .i64]
    code :=
      -- locals: tag=1, r=2
      i32c 0 ++ ls 1 ++
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ i32Load 2 4 ++ ls 1 ++ end_ ++
      lg 0 ++ call (rt "wiz_dec") ++
      i64c 1 ++ ls 2 ++
      lg 1 ++ i32c 1000 ++ i32Eq ++ if_ ++ i64c 3 ++ ls 2 ++ end_ ++
      lg 1 ++ i32c 1001 ++ i32Eq ++ if_ ++ i64c 5 ++ ls 2 ++ end_ ++
      lg 1 ++ i32c 1002 ++ i32Eq ++ if_ ++ i64c 7 ++ ls 2 ++ end_ ++
      lg 2 ++ ret }
  -- `wiz_lazy_set(x, p)`: a shared cell is overwritten with ⟨1002 p⟩, so its other
  -- references do not unfold it again; `x` and `p` are consumed.
  out := out.push {
    name := "wiz_lazy_set", params := #[.i64, .i64], results := #[.i64]
    locals := #[.i32, .i32, .i32, .i32]
    code :=
      -- locals: rc=2, tag=3, n=4, i=5
      lg 0 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ ret ++ end_ ++
      lg 0 ++ i32WrapI64 ++ i32Load 2 0 ++ ls 2 ++
      lg 0 ++ i32WrapI64 ++ i32Load 2 4 ++ ls 3 ++
      lg 2 ++ i32c 1 ++ i32LeU ++ if_
        ++ lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ ret ++ end_ ++
      lg 3 ++ i32c 1000 ++ i32Eq ++ lg 3 ++ i32c 1001 ++ i32Eq ++ i32Or ++ i32Eqz ++ if_
        ++ lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ ret ++ end_ ++
      lg 0 ++ i32WrapI64 ++ i32Load 2 8 ++ ls 4 ++
      i32c 0 ++ ls 5 ++
      block ++ loop ++
        lg 5 ++ lg 4 ++ i32GeU ++ brIf 1 ++
        lg 0 ++ i32WrapI64 ++ i32c 16 ++ i32Add ++ lg 5 ++ i32c 8 ++ i32Mul ++ i32Add ++
        i64Load 3 0 ++ call (rt "wiz_dec") ++
        lg 5 ++ i32c 1 ++ i32Add ++ ls 5 ++ br 0 ++
      end_ ++ end_ ++
      lg 0 ++ i32WrapI64 ++ i32c 1002 ++ i32Store 2 4 ++
      lg 0 ++ i32WrapI64 ++ i32c 1 ++ i32Store 2 8 ++
      lg 1 ++ call (rt "wiz_inc") ++
      lg 0 ++ i32WrapI64 ++ lg 1 ++ i64Store 3 16 ++
      lg 0 ++ i32WrapI64 ++ lg 2 ++ i32c 1 ++ i32Sub ++ i32Store 2 0 ++
      lg 1 ++ ret }
  -- `wiz_tag_of(v)`: the tag as a scalar (it consumes `v`).
  out := out.push {
    name := "wiz_tag_of", params := #[.i64], results := #[.i64], locals := #[.i32]
    code :=
      lg 0 ++ call (rt "wiz_tag") ++ ls 1 ++
      lg 0 ++ call (rt "wiz_dec") ++
      lg 1 ++ boxI32 ++ ret }
  out := out.push {
    name := "wiz_nat_tag", params := #[.i64], results := #[.i64], locals := #[.i32]
    code :=
      -- locals: z=1
      i32c 1 ++ ls 1 ++
      lg 0 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ i64Eqz ++ if_ ++ i32c 0 ++ ls 1 ++ end_
        ++ end_ ++
      lg 0 ++ call (rt "wiz_dec") ++
      lg 1 ++ boxI32 ++ ret }
  out := out.push {
    name := "wiz_field_at", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      -- locals: f=2
      lg 0 ++ i32WrapI64 ++ i32c 16 ++ i32Add ++
      lg 1 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ i32c 8 ++ i32Mul ++ i32Add ++
      i64Load 3 0 ++ ls 2 ++
      lg 2 ++ call (rt "wiz_inc") ++
      lg 0 ++ call (rt "wiz_dec") ++
      lg 2 ++ ret }
  -- `wiz_mk_obj(t, l)`: an object with the tag of `t` and the fields of nested pairs.
  out := out.push {
    name := "wiz_mk_obj", params := #[.i64, .i64], results := #[.i64]
    locals := #[.i64, .i32, .i32, .i64, .i32, .i64]
    code :=
      -- locals: p=2, tag=3, n=4, c=5, i=6, f=7
      lg 0 ++ call (rt "wiz_tag") ++ ls 3 ++
      i32c 0 ++ ls 4 ++ lg 1 ++ ls 5 ++
      block ++ loop ++
        -- (a nested pair is an object: continue while the list cell is not a scalar)
        lg 5 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ brIf 1 ++
        lg 4 ++ i32c 1 ++ i32Add ++ ls 4 ++
        lg 5 ++ i32WrapI64 ++ i64Load 3 24 ++ ls 5 ++ br 0 ++
      end_ ++ end_ ++
      lg 0 ++ call (rt "wiz_dec") ++
      lg 4 ++ i32Eqz ++ if_ ++ lg 1 ++ call (rt "wiz_dec") ++ lg 3 ++ boxI32 ++ ret ++ end_ ++
      lg 3 ++ lg 4 ++ call (rt "wiz_ctor_new") ++ ls 2 ++
      i32c 0 ++ ls 6 ++ lg 1 ++ ls 5 ++
      block ++ loop ++
        lg 5 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ brIf 1 ++
        lg 5 ++ i32WrapI64 ++ i64Load 3 16 ++ ls 7 ++
        lg 2 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 6 ++ i32c 8 ++ i32Mul ++ i32Add ++
        lg 7 ++ i64Store 3 0 ++
        lg 7 ++ call (rt "wiz_inc") ++
        lg 5 ++ i32WrapI64 ++ i64Load 3 24 ++ ls 5 ++
        lg 6 ++ i32c 1 ++ i32Add ++ ls 6 ++ br 0 ++
      end_ ++ end_ ++
      lg 1 ++ call (rt "wiz_dec") ++ lg 2 ++ ret }
  -- `wiz_nat_norm(r)`: a host result (scalar or handle) as a Wiz value.
  out := out.push {
    name := "wiz_nat_norm", params := #[.i64], results := #[.i64], locals := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ i32c tagBig ++ i32c 1 ++ call (rt "wiz_ctor_new") ++ ls 1 ++
        lg 1 ++ i32WrapI64 ++ lg 0 ++ i64Store 3 16 ++ lg 1 ++ ret
        ++ else_ ++ lg 0 ++ ret ++ end_ }
  out := out.push {
    name := "wiz_big_handle", params := #[.i64], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ ret
        ++ else_ ++ i64c 0 ++ ret ++ end_ }
  out := out.push {
    name := "wiz_big_small", params := #[.i64], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ i64Eqz ++ if_
        ++ i64c 0 ++ ret
        ++ else_ ++ lg 0 ++ i64c 1 ++ i64ShrU ++ ret ++ end_ }
  -- Nat operations: a fast path on small scalars, then the host's `BigInt`. Every
  -- operation except the comparisons consumes its arguments (as in `runtime/rt_num.inc`).
  out := out.push {
    name := "wiz_nat_add", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      -- locals: s=2
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64Add ++ ls 2 ++
        lg 2 ++ i64c maxSmall ++ i64LeU ++ if_ ++ lg 2 ++ boxI64 ++ ret ++ end_
        ++ end_ ++
      i32c 0 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_sub", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      -- locals: x=2
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ ls 2 ++
        lg 2 ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64GtU ++ if_
          ++ lg 2 ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64Sub ++ boxI64 ++ ret
          ++ else_ ++ i64c 1 ++ ret ++ end_
        ++ end_ ++
      i32c 1 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_mul", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      -- locals: x=2
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ ls 2 ++
        lg 1 ++ i64c 1 ++ i64ShrU ++ i64Eqz ++ if_
          ++ i64c 1 ++ ret
          ++ else_ ++
          lg 2 ++ i64c maxSmall ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64DivU ++ i64LeU ++ if_
            ++ lg 2 ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64Mul ++ boxI64 ++ ret
            ++ end_
          ++ end_
        ++ end_ ++
      i32c 2 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_div", params := #[.i64, .i64], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64Eqz ++ if_
          ++ i64c 1 ++ ret
          ++ else_ ++ lg 0 ++ i64c 1 ++ i64ShrU ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64DivU ++ boxI64 ++ ret
          ++ end_
        ++ end_ ++
      i32c 3 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_mod", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      -- locals: a=2
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ ls 2 ++
        lg 1 ++ i64c 1 ++ i64ShrU ++ i64Eqz ++ if_
          ++ lg 2 ++ boxI64 ++ ret
          ++ else_ ++ lg 2 ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64RemU ++ boxI64 ++ ret
          ++ end_
        ++ end_ ++
      i32c 4 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_land", params := #[.i64, .i64], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64And ++ boxI64 ++ ret
        ++ end_ ++
      i32c 5 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_lor", params := #[.i64, .i64], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64Or ++ boxI64 ++ ret
        ++ end_ ++
      i32c 6 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_xor", params := #[.i64, .i64], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64Xor ++ boxI64 ++ ret
        ++ end_ ++
      i32c 7 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_shiftLeft", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      -- locals: k=2
      -- 0 shifted is 0, whatever the shift (which is dropped)
      lg 0 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++
      lg 0 ++ i64c 1 ++ i64ShrU ++ i64Eqz ++ i32And ++ if_
        ++ lg 1 ++ call (rt "wiz_dec") ++ lg 0 ++ ret ++ end_ ++
      -- a big shift of a nonzero number has no representation (as the C runtime panics)
      lg 1 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ i32Eqz ++ if_ ++ unreachable ++ end_ ++
      lg 1 ++ i64c 1 ++ i64ShrU ++ ls 2 ++
      lg 0 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++
      lg 2 ++ i64c 62 ++ i64LtU ++ i32And ++
      lg 0 ++ i64c 1 ++ i64ShrU ++ i64c maxSmall ++ lg 2 ++ i64ShrU ++ i64LeU ++ i32And ++
      if_ ++ lg 0 ++ i64c 1 ++ i64ShrU ++ lg 2 ++ i64Shl ++ boxI64 ++ ret ++ end_ ++
      i32c 8 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_shiftRight", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      -- locals: k=2
      lg 1 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ i32Eqz ++ if_
        ++ lg 0 ++ call (rt "wiz_dec") ++ lg 1 ++ call (rt "wiz_dec") ++ i64c 1 ++ ret
        ++ end_ ++
      lg 1 ++ i64c 1 ++ i64ShrU ++ ls 2 ++
      lg 0 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 2 ++ i64c 64 ++ i64GeU ++ if_ ++ i64c 1 ++ ret ++ end_ ++
        lg 0 ++ i64c 1 ++ i64ShrU ++ lg 2 ++ i64ShrU ++ boxI64 ++ ret
        ++ end_ ++
      i32c 9 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_pow", params := #[.i64, .i64], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++
      lg 0 ++ i64c 1 ++ i64ShrU ++ i64c 1 ++ i64LeU ++ i32And ++ if_
        ++ lg 1 ++ i64c 1 ++ i64ShrU ++ i64Eqz ++ if_
          ++ lg 1 ++ call (rt "wiz_dec") ++ i64c 3 ++ ret
          ++ else_ ++ lg 1 ++ call (rt "wiz_dec") ++ lg 0 ++ ret ++ end_
        ++ end_ ++
      lg 1 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ i32Eqz ++ if_ ++ unreachable ++ end_ ++
      i32c 10 ++ lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
      lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
      lg 0 ++ call (rt "wiz_dec") ++
      call iBigOp ++ call (rt "wiz_nat_norm") ++ ret }
  out := out.push {
    name := "wiz_nat_log2", params := #[.i64], results := #[.i64], locals := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ i64c 1 ++ i64ShrU ++ ls 1 ++
        lg 1 ++ i64Eqz ++ if_ ++ i64c 1 ++ ret ++ end_ ++
        i64c 63 ++ lg 1 ++ i64Clz ++ i64Sub ++ boxI64 ++ ret
        ++ else_ ++
        lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
        lg 0 ++ call (rt "wiz_dec") ++
        call iBigLog2 ++ ret
        ++ end_ }
  out := out.push {
    name := "wiz_nat_beq", params := #[.i64, .i64], results := #[.i64], locals := #[.i64]
    code :=
      -- (the comparisons borrow their arguments: the caller keeps its references)
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ lg 1 ++ i64Eq ++ if_ ++ i64c 3 ++ ret ++ else_ ++ i64c 1 ++ ret ++ end_
        ++ else_ ++
        lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
        lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
        call iBigCmp ++ i32Eqz ++ if_ ++ i64c 3 ++ ret ++ else_ ++ i64c 1 ++ ret ++ end_
        ++ end_ }
  out := out.push {
    name := "wiz_nat_blt", params := #[.i64, .i64], results := #[.i64]
    code :=
      lg 0 ++ i64c 1 ++ i64And ++ lg 1 ++ i64c 1 ++ i64And ++ i64And ++ i64c 1 ++ i64Eq ++ if_
        ++ lg 0 ++ lg 1 ++ i64LtU ++ if_ ++ i64c 3 ++ ret ++ else_ ++ i64c 1 ++ ret ++ end_
        ++ else_ ++
        lg 0 ++ call (rt "wiz_big_handle") ++ lg 0 ++ call (rt "wiz_big_small") ++
        lg 1 ++ call (rt "wiz_big_handle") ++ lg 1 ++ call (rt "wiz_big_small") ++
        call iBigCmp ++ i32c 0 ++ i32LtS
        ++ if_ ++ i64c 3 ++ ret ++ else_ ++ i64c 1 ++ ret ++ end_
        ++ end_ }
  -- arrays: fields [0] = length, [1] = capacity, then the elements (owned).
  out := out.push {
    name := "wiz_array_new", params := #[.i32], results := #[.i64], locals := #[.i64]
    code :=
      i32c tagArray ++ lg 0 ++ i32c 2 ++ i32Add ++ call (rt "wiz_ctor_new") ++ ls 1 ++
      lg 1 ++ i32WrapI64 ++ i64c 1 ++ i64Store 3 16 ++
      lg 1 ++ i32WrapI64 ++ lg 0 ++ boxI32 ++ i64Store 3 24 ++
      lg 1 ++ ret }
  out := out.push {
    name := "wiz_array_empty", params := #[], results := #[.i64]
    code := i32c 0 ++ call (rt "wiz_array_new") ++ ret }
  out := out.push {
    name := "wiz_array_push", params := #[.i64, .i64], results := #[.i64]
    locals := #[.i32, .i32, .i32, .i64, .i32, .i64]
    code :=
      -- locals: len=2, cap=3, newcap=4, p=5, i=6, f=7
      lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 2 ++
      lg 0 ++ i32WrapI64 ++ i64Load 3 24 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 3 ++
      lg 2 ++ lg 3 ++ i32LtU ++
      lg 0 ++ i32WrapI64 ++ i32Load 2 0 ++ i32c 1 ++ i32Eq ++ i32And ++ if_
        ++ lg 0 ++ ls 5
        ++ else_ ++
        lg 2 ++ lg 3 ++ i32LtU ++ if_
          ++ lg 3 ++ ls 4
          ++ else_ ++ lg 3 ++ i32c 2 ++ i32Mul ++ i32c 8 ++ i32Add ++ ls 4 ++ end_ ++
        lg 4 ++ call (rt "wiz_array_new") ++ ls 5 ++
        i32c 0 ++ ls 6 ++
        block ++ loop ++
          lg 6 ++ lg 2 ++ i32GeU ++ brIf 1 ++
          lg 0 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 6 ++ i32c 8 ++ i32Mul ++ i32Add ++
          i64Load 3 0 ++ ls 7 ++
          lg 7 ++ call (rt "wiz_inc") ++
          lg 5 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 6 ++ i32c 8 ++ i32Mul ++ i32Add ++
          lg 7 ++ i64Store 3 0 ++
          lg 6 ++ i32c 1 ++ i32Add ++ ls 6 ++ br 0 ++
        end_ ++ end_ ++
        lg 5 ++ i32WrapI64 ++ lg 2 ++ boxI32 ++ i64Store 3 16 ++
        lg 0 ++ call (rt "wiz_dec")
        ++ end_ ++
      lg 5 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 2 ++ i32c 8 ++ i32Mul ++ i32Add ++
      lg 1 ++ i64Store 3 0 ++
      lg 5 ++ i32WrapI64 ++ lg 2 ++ i32c 1 ++ i32Add ++ boxI32 ++ i64Store 3 16 ++
      lg 5 ++ ret }
  out := out.push {
    name := "wiz_array_size", params := #[.i64], results := #[.i64], locals := #[.i64]
    code :=
      -- locals: n=1
      lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ ls 1 ++
      lg 0 ++ call (rt "wiz_dec") ++
      lg 1 ++ ret }
  out := out.push {
    name := "wiz_array_get", params := #[.i64, .i64, .i64], results := #[.i64]
    locals := #[.i32, .i32, .i64]
    code :=
      -- locals: i=3, len=4, r=5
      lg 1 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 3 ++
      lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 4 ++
      lg 3 ++ lg 4 ++ i32LtU ++ if_
        ++ lg 0 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 3 ++ i32c 8 ++ i32Mul ++ i32Add ++
           i64Load 3 0 ++ ls 5 ++
           lg 5 ++ call (rt "wiz_inc") ++
           lg 2 ++ call (rt "wiz_dec")
        ++ else_ ++ lg 2 ++ ls 5 ++ end_ ++
      lg 0 ++ call (rt "wiz_dec") ++
      lg 5 ++ ret }
  out := out.push {
    name := "wiz_array_set", params := #[.i64, .i64, .i64], results := #[.i64]
    locals := #[.i32, .i32, .i32, .i64, .i32, .i64]
    code :=
      -- locals: i=3, len=4, cap=5, p=6, k=7, f=8
      lg 1 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 3 ++
      lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 4 ++
      lg 3 ++ lg 4 ++ i32GeU ++ if_ ++ lg 2 ++ call (rt "wiz_dec") ++ lg 0 ++ ret ++ end_ ++
      lg 0 ++ i32WrapI64 ++ i64Load 3 24 ++ i64c 1 ++ i64ShrU ++ i32WrapI64 ++ ls 5 ++
      lg 0 ++ i32WrapI64 ++ i32Load 2 0 ++ i32c 1 ++ i32Eq ++ if_
        ++ lg 0 ++ ls 6
        ++ else_ ++
        lg 5 ++ call (rt "wiz_array_new") ++ ls 6 ++
        i32c 0 ++ ls 7 ++
        block ++ loop ++
          lg 7 ++ lg 4 ++ i32GeU ++ brIf 1 ++
          lg 0 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 7 ++ i32c 8 ++ i32Mul ++ i32Add ++
          i64Load 3 0 ++ ls 8 ++
          lg 8 ++ call (rt "wiz_inc") ++
          lg 6 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 7 ++ i32c 8 ++ i32Mul ++ i32Add ++
          lg 8 ++ i64Store 3 0 ++
          lg 7 ++ i32c 1 ++ i32Add ++ ls 7 ++ br 0 ++
        end_ ++ end_ ++
        lg 6 ++ i32WrapI64 ++ lg 4 ++ boxI32 ++ i64Store 3 16 ++
        lg 0 ++ call (rt "wiz_dec")
        ++ end_ ++
      lg 6 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 3 ++ i32c 8 ++ i32Mul ++ i32Add ++
      i64Load 3 0 ++ call (rt "wiz_dec") ++
      lg 6 ++ i32WrapI64 ++ i32c 32 ++ i32Add ++ lg 3 ++ i32c 8 ++ i32Mul ++ i32Add ++
      lg 2 ++ i64Store 3 0 ++
      lg 6 ++ ret }
  out := out.push {
    name := "wiz_big_to_string", params := #[.i64, .i32], results := #[.i32]
    code := lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ lg 1 ++ call iBigToDec ++ ret }
  out := out.push {
    name := "wiz_big_digits", params := #[.i64], results := #[.i64], locals := #[.i32, .i32]
    code :=
      -- locals: ptr=1, len=2
      i32c 8192 ++ call (rt "wiz_alloc_raw") ++ ls 1 ++
      lg 0 ++ i32WrapI64 ++ i64Load 3 16 ++ lg 1 ++ call iBigToDec ++ ls 2 ++
      lg 1 ++ i64ExtendI32U ++ i64c 32 ++ i64Shl ++ lg 2 ++ i64ExtendI32U ++ i64Or ++ ret }
  return out
/-! ## Collecting a program -/

/-- The variables a body binds (as `C.bound`). -/
partial def bound (b : Body) (acc : Array Var := #[]) : Array Var :=
  match b with
  | .vdecl x _ b => bound b (acc.push x)
  | .case _ alts => alts.foldl (fun acc a => bound a acc) acc
  | .jdecl _ ps body k => bound k (bound body (acc ++ ps))
  | .dup _ b | .drop _ b => bound b acc
  | _ => acc

def dedup (xs : Array Nat) : Array Nat :=
  let init : Std.HashSet Nat × Array Nat := ({}, #[])
  (xs.foldl (fun (st : Std.HashSet Nat × Array Nat) x =>
    if st.1.contains x then st else (st.1.insert x, st.2.push x)) init).2

structure JoinDef where
  owner : Name
  id : JoinId
  params : Array Var
  body : Body

partial def joinsOf (owner : Name) : Body → Array JoinDef
  | .jdecl j ps jb k => joinsOf owner jb ++ joinsOf owner k ++ #[{ owner, id := j, params := ps, body := jb }]
  | .vdecl _ _ b | .dup _ b | .drop _ b => joinsOf owner b
  | .case _ alts => alts.foldl (fun acc a => acc ++ joinsOf owner a) #[]
  | _ => #[]

/-- The big literals of a body, in order. -/
partial def bigLitsOf : Body → Array Nat → Array Nat
  | .vdecl _ (.lit n) b, acc => bigLitsOf b (if n ≥ 2 ^ 62 then acc.push n else acc)
  | .vdecl _ _ b, acc | .dup _ b, acc | .drop _ b, acc => bigLitsOf b acc
  | .case _ alts, acc => alts.foldl (fun acc a => bigLitsOf a acc) acc
  | .jdecl _ _ jb k, acc => bigLitsOf k (bigLitsOf jb acc)
  | _, acc => acc

def arrayFn (cname : String) : Option String :=
  match cname with
  | "wiz_array_empty" => some "wiz_array_empty"
  | "wiz_array_push" => some "wiz_array_push"
  | "wiz_array_size" => some "wiz_array_size"
  | "wiz_array_get" => some "wiz_array_get"
  | "wiz_array_set" => some "wiz_array_set"
  | _ => none

def natPrimFn (op : String) : Option String :=
  match op with
  | "nat.succ" => some "wiz_nat_add"
  | "nat.pred" => some "wiz_nat_sub"
  | "nat.add" => some "wiz_nat_add"
  | "nat.sub" => some "wiz_nat_sub"
  | "nat.mul" => some "wiz_nat_mul"
  | "nat.div" => some "wiz_nat_div"
  | "nat.mod" => some "wiz_nat_mod"
  | "nat.pow" => some "wiz_nat_pow"
  | "nat.land" => some "wiz_nat_land"
  | "nat.lor" => some "wiz_nat_lor"
  | "nat.xor" => some "wiz_nat_xor"
  | "nat.shiftLeft" => some "wiz_nat_shiftLeft"
  | "nat.shiftRight" => some "wiz_nat_shiftRight"
  | "nat.log2" => some "wiz_nat_log2"
  | "nat.beq" => some "wiz_nat_beq"
  | "nat.blt" => some "wiz_nat_blt"
  | "lazyTag" => some "wiz_lazy_tag"
  | "lazySet" => some "wiz_lazy_set"
  | "memo" => some "wiz_memo"
  | "tag" => some "wiz_tag_of"
  | "natTag" => some "wiz_nat_tag"
  | "fieldAt" => some "wiz_field_at"
  | "mkObj" => some "wiz_mk_obj"
  | "dropMoved" => some "wiz_drop_moved"
  | _ => none

/-- The runtime function of a prim, if the Wasm backend supports it. -/
def primFn (op : String) : Option String :=
  match natPrimFn op with
  | some f => some f
  | none =>
    match RVal.ExternSig.ofKey? op with
    | some sig => if sig.io then none else (arrayFn sig.cname)
    | none => none

/-- A human-readable reason a prim is unsupported. -/
def unsupportedPrim (op : String) : String :=
  match RVal.ExternSig.ofKey? op with
  | some sig => s!"the foreign function `{sig.cname}` is not supported by the Wasm backend (its arrays are)"
  | none => s!"the primitive `{op}` is not supported by the Wasm backend"

partial def checkBody : Body → Except String Unit
  | .vdecl _ (.prim op _) b => if primFn op |>.isSome then checkBody b else .error (unsupportedPrim op)
  | .vdecl _ (.pap f as) b | .vdecl _ (.ap f as) b =>
    if as.size > maxCallArgs then
      .error s!"the Wasm backend holds at most {maxCallArgs} call arguments (calling `{f}` with {as.size})"
    else checkBody b
  | .vdecl _ (.ctor t _) b | .vdecl _ (.reuse _ t _) b =>
    -- Tags are written as `i32`; a tag that does not fit would be silently truncated.
    if t ≥ 2 ^ 32 then
      .error s!"the Wasm backend writes a constructor tag as an `i32` (tag {t} is too large)"
    else checkBody b
  | .vdecl _ _ b | .dup _ b | .drop _ b => checkBody b
  | .case _ alts => alts.foldl (fun r a => r.bind fun _ => checkBody a) (.ok ())
  | .jdecl _ _ jb k => checkBody jb >>= fun _ => checkBody k
  | _ => .ok ()

/-- Every direct call and closure names a declaration in this module, and its arity
matches (a direct call is full application; a `pap` may be partial). Without this a
wrong arity would be emitted as a `call` with the wrong number of operands. -/
partial def checkCalls (names : Std.HashSet Name) (arities : Std.HashMap Name Nat) :
    Body → Except String Unit
  | .vdecl _ (.fap f as) b =>
    if !names.contains f then .error s!"the Wasm backend has no function `{f}` (an unresolved call)"
    else if as.size != arities.getD f 0 then
      .error s!"the Wasm backend calls `{f}` with {as.size} arguments, but it takes {arities.getD f 0}"
    else checkCalls names arities b
  | .vdecl _ (.pap f as) b =>
    if !names.contains f then .error s!"the Wasm backend has no function `{f}` (an unresolved call)"
    else if as.size > arities.getD f 0 then
      .error s!"the Wasm backend partially applies `{f}` with {as.size} arguments, but it takes {arities.getD f 0}"
    else checkCalls names arities b
  | .vdecl _ _ b | .dup _ b | .drop _ b => checkCalls names arities b
  | .case _ alts => alts.foldl (fun r a => r.bind fun _ => checkCalls names arities a) (.ok ())
  | .jdecl _ _ jb k => checkCalls names arities jb >>= fun _ => checkCalls names arities k
  | _ => .ok ()

/-- Every variable a body uses is one of its parameters or is bound in it. A variable
outside that scope would silently read Wiz local 0 in `Ctx.var`. -/
def checkScope (params : Array Var) (b : Body) : Except String Unit := do
  let allowed : Std.HashSet Var :=
    (bound b).foldl (fun s x => s.insert x) (params.foldl (fun s x => s.insert x) {})
  for x in b.freeVars.toArray do
    unless allowed.contains x do
      throw s!"the Wasm backend cannot find Wiz local x{x} (an out-of-scope variable)"

/-- Every `jmp` names a join point in scope. -/
partial def checkJumps (known : Std.HashSet JoinId) : Body → Except String Unit
  | .jdecl j _ jb k =>
    checkJumps (known.insert j) jb >>= fun _ => checkJumps (known.insert j) k
  | .jmp j _ =>
    if known.contains j then .ok () else .error s!"the Wasm backend has no join point j{j}"
  | .vdecl _ _ b | .dup _ b | .drop _ b => checkJumps known b
  | .case _ alts => alts.foldl (fun r a => r.bind fun _ => checkJumps known a) (.ok ())
  | _ => .ok ()

/-- An unsupported prim (or too many call arguments, an unresolved call, an out-of-scope
variable or a missing join point) anywhere in the program, as an error. -/
def check (decls : Array IR.Decl) : Except String Unit :=
  let names : Std.HashSet Name := decls.foldl (fun s d => s.insert d.name) {}
  let arities : Std.HashMap Name Nat :=
    decls.foldl (fun m d => m.insert d.name d.params.size) {}
  decls.foldl (fun r d => r.bind fun _ =>
    checkBody d.body >>= fun _ =>
    checkCalls names arities d.body >>= fun _ =>
    checkScope d.params d.body >>= fun _ =>
    checkJumps {} d.body >>= fun _ =>
    -- a join body is compiled as a function of its parameters and its own locals; it
    -- may not read an outer variable
    (joinsOf d.name d.body).foldl (fun r j => r.bind fun _ =>
      checkScope j.params j.body) (.ok ())) (.ok ())

/-! ## Code generation -/

structure Ctx where
  owner : Name
  declIdx : Std.HashMap Name Nat
  joinIdx : Std.HashMap (Name × Nat) Nat
  /-- a join's parameters (for the unreachable fall-through path) -/
  joinParams : Std.HashMap (Name × Nat) (Array Var)
  tableIdx : Std.HashMap Name Nat
  arities : Std.HashMap Name Nat
  lits : Std.HashMap Nat (Nat × Nat)
  locals : Std.HashMap Var Nat
  tmp : Nat

def Ctx.var (c : Ctx) (x : Var) : Nat := c.locals.getD x 0

/-- `value` on the stack as an object pointer; then `local.get x`'s field. -/
def storeField (x : Nat) (i : Nat) : Code :=
  lg x ++ i32WrapI64 ++ i32c (16 + 8 * i) ++ i32Add

def boxNat (n : Nat) : Nat := 2 * n + 1

mutual

partial def emitExpr (c : Ctx) (x : Var) : Expr → Code
  | .erased => i64c 1 ++ ls (c.var x)
  | .lit n =>
    if n < 2 ^ 62 then i64c (boxNat n) ++ ls (c.var x)
    else match c.lits.get? n with
      | some (off, len) =>
        i32c (dataBase + off) ++ i32c len ++ call iBigOfDec ++ call (rtIdx "wiz_nat_norm") ++ ls (c.var x)
      | none => unreachable
  | .ctor t as =>
    if as.isEmpty then i64c (boxNat t) ++ ls (c.var x)
    else
      i32c t ++ i32c as.size ++ call (rtIdx "wiz_ctor_new") ++ ls (c.var x) ++
      as.toList.zipIdx.foldl (fun (code : Code) (a, i) =>
        code ++ storeField (c.var x) i ++ lg (c.var a) ++ i64Store 3 0) #[]
  | .proj i y => lg (c.var y) ++ i32c i ++ call (rtIdx "wiz_proj") ++ ls (c.var x)
  | .fap f as =>
    as.foldl (fun (code : Code) a => code ++ lg (c.var a)) #[] ++ call (c.declIdx.getD f 0) ++ ls (c.var x)
  | .pap f as =>
    as.toList.zipIdx.foldl (fun (code : Code) (a, i) =>
      code ++ i32c (scratchBase + 8 * i) ++ lg (c.var a) ++ i64Store 3 0) #[] ++
    i32c (c.tableIdx.getD f 0) ++ i32c (c.arities.getD f 0) ++ i32c as.size ++
    i32c scratchBase ++ call (rtIdx "wiz_clo_new") ++ ls (c.var x)
  | .ap f as =>
    as.toList.zipIdx.foldl (fun (code : Code) (a, i) =>
      code ++ i32c (scratchBase + 8 * i) ++ lg (c.var a) ++ i64Store 3 0) #[] ++
    lg (c.var f) ++ i32c as.size ++ i32c scratchBase ++ call (rtIdx "wiz_apply") ++ ls (c.var x)
  | .reset y => lg (c.var y) ++ call (rtIdx "wiz_reset") ++ ls (c.var x)
  | .reuse tok t as =>
    if as.isEmpty then
      -- (a token with no fields frees its cell; the value is the scalar tag)
      lg (c.var tok) ++ call (rtIdx "wiz_dec") ++ i64c (boxNat t) ++ ls (c.var x)
    else
      lg (c.var tok) ++ i32c t ++ i32c as.size ++ call (rtIdx "wiz_reuse") ++ ls (c.var x) ++
      as.toList.zipIdx.foldl (fun (code : Code) (a, i) =>
        code ++ storeField (c.var x) i ++ lg (c.var a) ++ i64Store 3 0) #[]
  | .prim op as => emitPrim c x op as

partial def emitPrim (c : Ctx) (x : Var) (op : String) (as : Array Var) : Code :=
  match natPrimFn op with
  | some f =>
    match op, as.toList with
    | "nat.succ", [a] => lg (c.var a) ++ i64c 3 ++ call (rtIdx "wiz_nat_add") ++ ls (c.var x)
    | "nat.pred", [a] => lg (c.var a) ++ i64c 3 ++ call (rtIdx "wiz_nat_sub") ++ ls (c.var x)
    | _, _ => as.foldl (fun (code : Code) a => code ++ lg (c.var a)) #[] ++
              call (rtIdx f) ++ ls (c.var x)
  | none =>
    match RVal.ExternSig.ofKey? op with
    | some sig =>
      match arrayFn sig.cname with
      | some f =>
        -- skip erased (type) arguments; the runtime takes Wiz values
        let keep := as.toList.zip (sig.params ++ List.replicate (as.size - sig.params.length) (RVal.FKind.k 'e'))
          |>.filterMap fun (a, k) => if k == RVal.FKind.k 'e' then none else some a
        keep.foldl (fun (code : Code) a => code ++ lg (c.var a)) #[] ++
        call (rtIdx f) ++ ls (c.var x)
      | none => unreachable
    | none => unreachable

partial def emitBody (c : Ctx) : Body → Code
  | .vdecl x e rest => emitExpr c x e ++ emitBody c rest
  | .case x alts =>
    lg (c.var x) ++ call (rtIdx "wiz_tag") ++ ls c.tmp ++ emitAlts c alts 0
  | .ret x => lg (c.var x) ++ ret
  | .jdecl j _ _ k =>
    let i := (c.joinIdx.get? (c.owner, j)).getD 0
    -- the fall-through path (the IR never takes it, but the C backend has it)
    emitBody c k ++
      ((c.joinParams.getD (c.owner, j) #[]).foldl
        (fun (code : Code) p => code ++ lg (c.var p)) #[]) ++ call i ++ ret
  | .jmp j as =>
    as.foldl (fun (code : Code) a => code ++ lg (c.var a)) #[] ++
    call ((c.joinIdx.get? (c.owner, j)).getD 0) ++ ret
  | .dup x b => lg (c.var x) ++ call (rtIdx "wiz_inc") ++ emitBody c b
  | .drop x b => lg (c.var x) ++ call (rtIdx "wiz_dec") ++ emitBody c b
  | .unreachable => unreachable

partial def emitAlts (c : Ctx) (alts : Array Body) (i : Nat) : Code :=
  if h : i < alts.size then
    lg c.tmp ++ i32c i ++ i32Eq ++ if_ ++ emitBody c alts[i] ++ else_ ++ emitAlts c alts (i + 1) ++ end_
  else unreachable

end

/-! ## Assembling the module -/

structure Built where
  types : Array FnSig
  funcs : Array FnDef
  tableSize : Nat
  heapStart : Nat
  data : Array (Nat × String)
  entry : Nat

def typeIndex (types : Array FnSig) (s : FnSig) : Nat := (types.findIdx? (· == s)).getD 0

def align8 (n : Nat) : Nat := (n + 7) / 8 * 8

/-- The literal table: `n ↦ (offset in the data area, length)`, first use in order. -/
def litTable (ls : Array Nat) : Std.HashMap Nat (Nat × Nat) × Nat := Id.run do
  let mut m : Std.HashMap Nat (Nat × Nat) := {}
  let mut off := 0
  for n in ls do
    if m.contains n then continue
    let s := toString n
    m := m.insert n (off, s.utf8ByteSize)
    off := off + s.utf8ByteSize
  return (m, off)

def wasmSection (id : Nat) (body : Code) : Code := #[UInt8.ofNat id] ++ uleb body.size ++ body

def vec (xs : Array Code) : Code := uleb xs.size ++ xs.foldl (· ++ ·) #[]

def encodeFn (f : FnDef) : Code :=
  let groups := f.locals.foldl (fun (acc : Code) t => acc ++ uleb 1 ++ #[t.byte]) #[]
  -- (a fall-through traps: every IR body returns or is unreachable, and the runtime's
  -- own paths all return; the extra instruction only satisfies the validator)
  let body := uleb f.locals.size ++ groups ++ f.code ++ #[0x00, 0x0B]
  uleb body.size ++ body

def moduleBytes (b : Built) : ByteArray := Id.run do
  -- types
  let typeSec := wasmSection 1 (vec (b.types.map fun s =>
    #[0x60] ++ vec (s.params.map fun t => #[t.byte]) ++ vec (s.results.map fun t => #[t.byte])))
  -- imports
  let importSec := wasmSection 2 (uleb hostSigs.size ++ hostSigs.foldl (fun (acc : Code) (name, sig) =>
    acc ++ nameBytes "env" ++ nameBytes name ++ #[0x00] ++ uleb (typeIndex b.types sig)) #[])
  -- functions
  let fnSec := wasmSection 3 (vec (b.funcs.map fun f => uleb (typeIndex b.types { params := f.params, results := f.results })))
  -- table (one funcref per boxed wrapper)
  let tableSec := wasmSection 4 (uleb 1 ++ #[0x70, 0x00] ++ uleb b.tableSize)
  -- memory (one page; the allocator grows it)
  let minPages := max 1 ((b.heapStart + 65535) / 65536)
  let memSec := wasmSection 5 (uleb 1 ++ #[0x00] ++ uleb minPages)
  -- globals: the bump pointer, and the release work list's head
  let globSec := wasmSection 6 (uleb 2 ++
    #[0x7F, 0x01] ++ i32c b.heapStart ++ #[0x0B] ++
    #[0x7F, 0x01] ++ i32c 0 ++ #[0x0B])
  -- exports
  let exports : Array (String × Nat × Nat) :=
    #[("memory", 2, 0), ("wiz_main", 0, b.entry), ("wiz_value_tag", 0, rtIdx "wiz_tag"),
      ("wiz_value_field", 0, rtIdx "wiz_proj"), ("wiz_big_digits", 0, rtIdx "wiz_big_digits")]
  let exportSec := wasmSection 7 (vec (exports.map fun (n, kind, idx) =>
    nameBytes n ++ #[UInt8.ofNat kind] ++ uleb idx))
  -- element section: the table is exactly the boxed wrappers, from index 0
  let firstBoxed := hostSigs.size + runtimeNames.size + b.tableSize
  let elemSec := wasmSection 9 (uleb 1 ++ #[0x00] ++ i32c 0 ++ #[0x0B] ++
    uleb b.tableSize ++ (List.range b.tableSize).foldl (fun (acc : Code) i => acc ++ uleb (firstBoxed + i)) #[])
  -- code
  let codeSec := wasmSection 10 (vec (b.funcs.map encodeFn))
  -- data
  let dataSec := wasmSection 11 (uleb b.data.size ++ b.data.foldl (fun (acc : Code) (off, s) =>
    acc ++ #[0x00] ++ i32c (dataBase + off) ++ #[0x0B] ++ nameBytes s) #[])
  let magic : Code := #[0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]
  return ByteArray.mk (magic ++ typeSec ++ importSec ++ fnSec ++ tableSec ++ memSec ++ globSec ++
    exportSec ++ elemSec ++ codeSec ++ dataSec)

/-- Emit a WebAssembly module for the IR of an IO-less `main`. -/
def program (decls : Array IR.Decl) (io : Bool := false) : Except String ByteArray := do
  if io then throw "the Wasm backend runs only IO-less `main`"
  check decls
  match decls.find? (·.name == "wiz.entry") with
  | none => throw "the Wasm backend needs the `wiz.entry` function (no `main`?)"
  | some d =>
    if !d.params.isEmpty then
      throw "the Wasm backend's `main` must not take arguments (it is called with none)"
  let lits := dedup (decls.foldl (fun acc d => bigLitsOf d.body acc) #[])
  let (litTab, dataSize) := litTable lits
  let heapStart := align8 (dataBase + dataSize)
  let declIdx : Std.HashMap Name Nat := Id.run do
    let mut m : Std.HashMap Name Nat := {}
    for d in decls, i in [0:decls.size] do
      m := m.insert d.name (hostSigs.size + runtimeNames.size + i)
    return m
  let joinList := decls.foldl (fun acc d => acc ++ joinsOf d.name d.body) #[]
  let joinBase := hostSigs.size + runtimeNames.size + 2 * decls.size
  let joinIdx : Std.HashMap (Name × Nat) Nat := Id.run do
    let mut m : Std.HashMap (Name × Nat) Nat := {}
    for j in joinList, i in [0:joinList.size] do
      m := m.insert (j.owner, j.id) (joinBase + i)
    return m
  let joinParams : Std.HashMap (Name × Nat) (Array Var) := Id.run do
    let mut m : Std.HashMap (Name × Nat) (Array Var) := {}
    for j in joinList do
      m := m.insert (j.owner, j.id) j.params
    return m
  let tableIdx : Std.HashMap Name Nat := Id.run do
    let mut m : Std.HashMap Name Nat := {}
    for d in decls, i in [0:decls.size] do
      m := m.insert d.name i
    return m
  let arities : Std.HashMap Name Nat := decls.foldl (fun m d => m.insert d.name d.params.size) {}
  -- the boxed-wrapper signature is used by `call_indirect`
  let boxedSig : FnSig := { params := #[.i32], results := #[.i64] }
  let allSigs : Array FnSig :=
    (hostSigs.map (·.2)) ++
    (runtimeNames.map runtimeSig) ++
    (decls.map fun d => { params := d.params.map fun _ => .i64, results := #[.i64] }) ++
    (decls.map fun _ => boxedSig) ++
    (joinList.map fun j => { params := j.params.map fun _ => .i64, results := #[.i64] })
  let types := allSigs.foldl (fun (acc : Array FnSig) s => if acc.contains s then acc else acc.push s) #[]
  let boxedType := typeIndex types boxedSig
  let declFns := decls.map fun d =>
    let extra := dedup ((bound d.body).filter (!d.params.contains ·))
    let locals := extra.map fun _ => VT.i64
    let nParams := d.params.size
    let env : Std.HashMap Var Nat := Id.run do
      let mut m : Std.HashMap Var Nat := {}
      for p in d.params, i in [0:nParams] do m := m.insert p i
      for x in extra, i in [0:extra.size] do m := m.insert x (nParams + i)
      return m
    let c : Ctx := {
      owner := d.name, declIdx, joinIdx, joinParams, tableIdx, arities, lits := litTab, locals := env,
      tmp := nParams + extra.size }
    { name := d.name, params := d.params.map fun _ => .i64, results := #[.i64],
      locals := locals ++ #[.i32], code := emitBody c d.body }
  let boxedFns := decls.map fun d =>
    let n := d.params.size
    let loads := (List.range n).foldl (fun (acc : Code) i =>
      acc ++ lg 0 ++ i64Load 3 (8 * i)) #[]
    { name := d.name ++ "_boxed", params := #[.i32], results := #[.i64], code :=
      loads ++ call (declIdx.getD d.name 0) ++ ret }
  let joinFns := joinList.map fun j =>
    let extra := dedup ((bound j.body).filter (!j.params.contains ·))
    let nParams := j.params.size
    let env : Std.HashMap Var Nat := Id.run do
      let mut m : Std.HashMap Var Nat := {}
      for p in j.params, i in [0:nParams] do m := m.insert p i
      for x in extra, i in [0:extra.size] do m := m.insert x (nParams + i)
      return m
    let c : Ctx := {
      owner := j.owner, declIdx, joinIdx, joinParams, tableIdx, arities, lits := litTab, locals := env,
      tmp := nParams + extra.size }
    { name := s!"{j.owner}.j{j.id}", params := j.params.map fun _ => .i64, results := #[.i64],
      locals := (extra.map fun _ => VT.i64).push VT.i32, code := emitBody c j.body }
  let funcs := runtimeDefs boxedType ++ declFns ++ boxedFns ++ joinFns
  let entry := declIdx.getD "wiz.entry" 0
  let data := (lits.map fun n => match litTab.get? n with
    | some (off, _) => (off, toString n) | none => (0, "")).toList.toArray
  pure (moduleBytes { types, funcs, tableSize := decls.size, heapStart, data, entry })

end Wiz.Wasm
