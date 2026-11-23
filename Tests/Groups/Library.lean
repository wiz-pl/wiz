import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/Sha.wiz` and `lib/Encoding.wiz` (new): pure, so `#eval` runs them. The SHA-256
cases are the FIPS 180-4 vectors; the encodings are checked in both directions, and every
invalid input must come back as an `error`, never as a shorter result. -/
def libraryGroup : Group where
  name := "library"
  exercise := "lib/Sha.wiz, lib/Encoding.wiz (pure)"
  parallel := true
  shard := "library"
  cases := [
    { name := "sha256: the empty message, \"abc\", the 448-bit message, 64 bytes (FIPS 180-4)", run := fun _ =>
        let src := r#"import Sha
def toBytes : List Char → List U8
  | .nil => .nil
  | .cons c cs => .cons (U8.ofNat (Char.code c)) (toBytes cs)
def b (s : String) : List U8 := toBytes (String.chars s)
#eval Sha.sha256Hex .nil
#eval Sha.sha256Hex (b "abc")
#eval Sha.sha256Hex (b "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
#eval Sha.sha256Hex (b "The quick brown fox jumps over the lazy dog")
#eval Sha.sha256Hex (b "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
#eval List.length (Sha.sha256 (b "abc"))
"#
        okLibs src [
          "\"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\"",
          "\"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad\"",
          "\"248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1\"",
          "\"d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592\"",
          "\"ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb\"",
          "32"] },
    { name := "encoding: hex and base64 both ways; every invalid input is an error", run := fun _ =>
        let src := r#"import Encoding
def showDec (r : Except String (List U8)) : String := match r with
  | .ok bs => Encoding.hexEncode bs
  | .error e => e
#eval Encoding.hexEncode .nil
#eval Encoding.hexEncode (.cons 0xDE (.cons 0xAD (.cons 0xBE (.cons 0xEF .nil))))
#eval showDec (Encoding.hexDecode "DeAdBeEf")
#eval showDec (Encoding.hexDecode "")
#eval showDec (Encoding.hexDecode "D")
#eval showDec (Encoding.hexDecode "Dz")
#eval Encoding.base64Encode .nil
#eval Encoding.base64Encode (.cons 0x66 .nil)
#eval Encoding.base64Encode (.cons 0x66 (.cons 0x6F .nil))
#eval Encoding.base64Encode (.cons 0x66 (.cons 0x6F (.cons 0x6F .nil)))
#eval Encoding.base64Encode (.cons 0x66 (.cons 0x6F (.cons 0x6F (.cons 0x62 (.cons 0x61 (.cons 0x72 .nil))))))
#eval Encoding.base64Encode (.cons 0xFB (.cons 0xFF .nil))
#eval showDec (Encoding.base64Decode "Zm9vYmFy")
#eval showDec (Encoding.base64Decode "Zg==")
#eval showDec (Encoding.base64Decode "Zm8=")
#eval showDec (Encoding.base64Decode "AAAA")
#eval showDec (Encoding.base64Decode "")
#eval showDec (Encoding.base64Decode "Zg")
#eval showDec (Encoding.base64Decode "Zg==Zg==")
#eval showDec (Encoding.base64Decode "Z===")
#eval showDec (Encoding.base64Decode "Zm9v!")
#eval showDec (Encoding.base64Decode "====")
"#
        okLibs src [
          "\"\"",
          "\"deadbeef\"",
          "\"deadbeef\"",
          "\"\"",
          "\"hex: odd number of digits\"",
          "\"hex: not a hex digit\"",
          "\"\"",
          "\"Zg==\"",
          "\"Zm8=\"",
          "\"Zm9v\"",
          "\"Zm9vYmFy\"",
          "\"+/8=\"",
          "\"666f6f626172\"",
          "\"66\"",
          "\"666f\"",
          "\"000000\"",
          "\"\"",
          "\"base64: length is not a multiple of 4\"",
          "\"base64: data after padding\"",
          "\"base64: misplaced padding\"",
          "\"base64: invalid character\"",
          "\"base64: misplaced padding\""] }
  ]

builtin_initialize registerGroup libraryGroup

end Tests.Elab
