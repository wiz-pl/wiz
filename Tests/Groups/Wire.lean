import Tests.Groups.Loom

open Wiz

set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Web.Wire: the P0 wire constants and the adopt hash (lib/Web/Wire.wiz)

The JavaScript half of the wire and the adopt contract is `web/framework/wire.js` and
`web/framework/adopt.js`; its browser-free test is `web/framework/wire_test.mjs`. These
cases pin the two values that must agree across the boundary: the exact envelope version
and the `data-wiz-ssr` hash. The hash is FNV-1a 32 over the UTF-8 bytes; the expected
digits below are the vectors `wire_test.mjs` uses, so a change to one side fails both.

The full Wiz monitor, protocol values and call/reply handlers are P1. The model and the
single validation table are `docs/notes/loom-wire-protocol.md`. -/

def wirePrelude : String := "import Web.Wire\n"

def wireGroup : Group where
  name := "wire"
  exercise := "lib/Web/Wire.wiz (wire version + adopt hash)"
  cases := [
    { name := "version: the exact envelope version both sides use", run := fun _ =>
        okLoom (wirePrelude ++ "#eval Wire.version")
          [r#""wiz.loom.wire/1""#] },
    { name := "adopt hash: FNV-1a 32 over UTF-8 (the JS wire_test vectors)", run := fun _ =>
        okLoom (wirePrelude ++
          "#eval Wire.ssrHash \"\"\n" ++
          "#eval Wire.ssrHash \"<div class=\\\"x\\\">a</div>\"\n" ++
          "#eval Wire.ssrHash \"héllo ☃ 𝄞\"\n" ++
          "#eval Wire.ssrHash \"<div><textarea id=\\\"editor\\\">x</textarea></div>\"")
          [r#""811c9dc5""#, r#""c7574f58""#, r#""04ec678c""#, r#""0dc601d0""#] },
    { name := "adopt hash: class attributes are part of the hash", run := fun _ =>
        okLoom (wirePrelude ++
          "#eval String.eq (Wire.ssrHash \"<div class=\\\"a\\\">x</div>\") (Wire.ssrHash \"<div class=\\\"b\\\">x</div>\")\n" ++
          "#eval String.eq (Wire.ssrHash \"<div class=\\\"a\\\">x</div>\") (Wire.ssrHash \"<div class=\\\"a\\\">x</div>\")")
          [".false", ".true"] }
  ]

builtin_initialize registerGroup wireGroup

end Tests.Elab
