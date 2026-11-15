/-!
# LSP position encodings

LSP 3.17 lets a client offer the position encodings it understands
(`general.positionEncodings`) and the server pick one (`capabilities.positionEncoding`).
UTF-16 is the protocol's default when the client says nothing; UTF-8 is the other
encoding this server supports.

A position's `character` is counted from the start of its line in the **negotiated
encoding**: UTF-16 code units or UTF-8 bytes. Offsets inside this tree are character
(Unicode scalar value) offsets, so the language server converts at its LSP boundary
(`Wiz/LSP.lean`) and semantic tokens convert again (`Wiz/Semantic.lean`). The two agree
for the Basic Multilingual Plane; they differ for astral characters (one character, two
UTF-16 code units, four UTF-8 bytes).
-/

namespace Wiz

/-- How an LSP position counts the characters of a line. -/
inductive PositionEncoding where
  | utf16
  | utf8
  deriving DecidableEq, Repr, Inhabited

namespace PositionEncoding

/-- The encoding's name in the protocol (`general.positionEncodings`,
`capabilities.positionEncoding`). -/
def toString : PositionEncoding → String
  | .utf16 => "utf-16"
  | .utf8 => "utf-8"

instance : ToString PositionEncoding := ⟨toString⟩

/-- The encoding a protocol name means, if this server supports it. -/
def ofString? : String → Option PositionEncoding
  | "utf-16" => some .utf16
  | "utf-8" => some .utf8
  | _ => none

/-- The encoding to use from the client's `general.positionEncodings`, in the client's
order; UTF-16 if it omitted the capability or offered nothing this server knows. -/
def negotiate (offered : List String) : PositionEncoding :=
  (offered.findSome? ofString?).getD .utf16

/-- The width of a character in the encoding: UTF-16 code units or UTF-8 bytes. -/
def width (enc : PositionEncoding) (c : Char) : Nat :=
  match enc with
  | .utf16 => if c.toNat < 0x10000 then 1 else 2
  | .utf8 => c.utf8Size

/-- The width of some characters in the encoding. -/
def widths (enc : PositionEncoding) (cs : List Char) : Nat :=
  cs.foldl (fun n c => n + width enc c) 0

end PositionEncoding

end Wiz
