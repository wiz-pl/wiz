/-!
# SHA-256 (FIPS 180-4), for the trusted `smt` answer cache (stage 28a)

The cache of solver answers is in `smt`'s trusted base: an answer replayed from it closes
a goal. So its key is a cryptographic digest of the query (Lean's `hash` is a 64-bit
non-cryptographic hash: a colliding query could be crafted), and each entry also stores the
query it answers, which is compared on every read.
-/

namespace Wiz.Smt.Sha256

private def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-! The compression function is written as tail-recursive loops over unboxed `UInt32`
arguments, with one message-schedule array reused (updated in place) for every block:
a `for` loop with eight mutable words packs them into a tuple per iteration, and that
allocation, not the arithmetic, dominated (hashing the 170 MB `wiz` executable for the
cache's toolchain tag took about 4 s). -/

/-- The working state: eight words. -/
private structure St where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
  deriving Inhabited

private def St.init : St :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- `w[0..16)` := the big-endian words of `b[off..off+64)`. -/
private partial def load (b : ByteArray) (off : Nat) (w : Array UInt32) (i : Nat) : Array UInt32 :=
  if i < 16 then
    let o := off + 4 * i
    let x := ((b.get! o).toUInt32 <<< 24) ||| ((b.get! (o + 1)).toUInt32 <<< 16) |||
      ((b.get! (o + 2)).toUInt32 <<< 8) ||| (b.get! (o + 3)).toUInt32
    load b off (w.set! i x) (i + 1)
  else w

/-- `w[16..64)`: the message schedule. -/
private partial def sched (w : Array UInt32) (i : Nat) : Array UInt32 :=
  if i < 64 then
    let x15 := w[i-15]!; let x2 := w[i-2]!
    let s0 := rotr x15 7 ^^^ rotr x15 18 ^^^ (x15 >>> 3)
    let s1 := rotr x2 17 ^^^ rotr x2 19 ^^^ (x2 >>> 10)
    sched (w.set! i (w[i-16]! + s0 + w[i-7]! + s1)) (i + 1)
  else w

/-- The 64 rounds, from round `i`. -/
private partial def rounds (w : Array UInt32) (i : Nat) (a b c d e f g h : UInt32) : St :=
  if i < 64 then
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := h + S1 + ch + k[i]! + w[i]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    rounds w (i + 1) (t1 + S0 + maj) a b c (d + t1) e f g
  else ⟨a, b, c, d, e, f, g, h⟩

/-- Compress the blocks of `b` at offsets `off, off + 64, …` below `stop`. -/
private partial def blocks (b : ByteArray) (off stop : Nat) (st : St) (w : Array UInt32) :
    St × Array UInt32 :=
  if off + 64 ≤ stop then
    let w := sched (load b off w 0) 16
    let r := rounds w 0 st.a st.b st.c st.d st.e st.f st.g st.h
    blocks b (off + 64) stop
      ⟨st.a + r.a, st.b + r.b, st.c + r.c, st.d + r.d, st.e + r.e, st.f + r.f, st.g + r.g, st.h + r.h⟩ w
  else (st, w)

/-- The SHA-256 digest of `msg`, as its 32 raw bytes. -/
def bytes (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let full := len / 64 * 64
  let (st, w) := blocks msg 0 full St.init (Array.replicate 64 0)
  -- (only the tail is copied: the last partial block, the padding and the length)
  let mut t := (msg.extract full len).push 0x80
  while t.size % 64 != 56 do t := t.push 0
  let bits := len * 8
  for i in [0:8] do t := t.push (UInt8.ofNat (bits >>> (8 * (7 - i)) % 256))
  let (st, _) := blocks t 0 t.size st w
  let mut out : ByteArray := .emptyWithCapacity 32
  for x in [st.a, st.b, st.c, st.d, st.e, st.f, st.g, st.h] do
    for j in [0:4] do out := out.push (UInt8.ofNat ((x.toNat >>> (8 * (3 - j))) % 256))
  pure out

/-- `n` as eight big-endian bytes (the framing length in `framed`). -/
private def be64 (n : Nat) : ByteArray :=
  ByteArray.mk #[ UInt8.ofNat ((n >>> 56) % 256), UInt8.ofNat ((n >>> 48) % 256),
                  UInt8.ofNat ((n >>> 40) % 256), UInt8.ofNat ((n >>> 32) % 256),
                  UInt8.ofNat ((n >>> 24) % 256), UInt8.ofNat ((n >>> 16) % 256),
                  UInt8.ofNat ((n >>> 8) % 256), UInt8.ofNat (n % 256) ]

/-- SHA-256 over a **domain label** and a list of byte fields, each length-prefixed with
eight big-endian bytes. This is the canonical way to turn structured inputs into a key:
without the lengths, `["ab", "c"]` and `["a", "bc"]` would have the same preimage, and
without the domain, a module key could be replayed as a toolchain id or a manifest entry.
The domain is itself length-prefixed, so no label is a prefix of another. -/
def framed (domain : String) (fields : List ByteArray) : ByteArray := Id.run do
  let d := domain.toUTF8
  let mut b := be64 d.size ++ d
  for f in fields do
    b := b ++ be64 f.size ++ f
  pure (bytes b)

/-- `msg`'s SHA-256 digest as 64 hexadecimal digits. -/
def hexBytes (msg : ByteArray) : String := Id.run do
  let digit (n : Nat) : Char := "0123456789abcdef".toList[n]!
  let mut out := ""
  for byte in bytes msg do
    out := out.push (digit (byte.toNat >>> 4)) |>.push (digit (byte.toNat % 16))
  pure out

/-- The SHA-256 digest of `s`'s UTF-8 bytes, as 64 hexadecimal digits. -/
def hex (s : String) : String := hexBytes s.toUTF8

/-- The digest of a domain-separated, length-framed list of string fields, as 64
hexadecimal digits. -/
def hexFramed (domain : String) (fields : List String) : String :=
  hexBytes (framed domain (fields.map String.toUTF8))

end Wiz.Smt.Sha256
