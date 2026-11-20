import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/Anim.wiz`: animation as a pure function of time, the `seq`/`par`/`stagger`/
`loop`/`retime` algebra, easing, morphing and the `wiz.widget/1` payload. The Wiz
sources live in `Tests/data/anim/` (they are read as files, like the golden SVGs);
`examples/anim-unwind.wiz` and `examples/anim-sine.wiz` are compared byte for byte with
`Tests/data/anim/*.svg`, so a diff there means the library changed the picture (or
stopped being deterministic). -/

def animEasingExpected : List String := [
  ".true", ".true", ".true", ".true", ".true",
  "\"0.25\"", "\"0.75\"", "\"0.0625\"", "\"0\"", "\"1\"", ".true", ".true"]

def animLawsExpected : List String := [
  ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true",
  ".true", ".true", ".true", ".true", ".true", "\"1\"", ".true", ".true", ".true",
  ".true", ".true", ".true", ".true", ".true", "\"3\"", "\"2\"", "\"0.5\"", "\"3\"",
  "\"2\"", ".true", ".true", ".true", ".true", "\"0.5\"", "\"1\"", "\"0\"", "\"1\"",
  ".true", ".true", ".true", ".false"]

def animMorphExpected : List String := [
  ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true",
  ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true", ".true",
  ".true"]

def animPayloadExpected : List String := [
  "\"wiz.widget/1\"", "\"anim\"", "\"image/svg+xml\"", "\"Demo\"",
  "\"animation: 2 s, 120x80 px, 24 sampled frames\"", "120", "80", "\"2\"", "24",
  "24", "4", "\"0\"", "\"2\"", "\"play\"", "\"slider\"", "\"2\"", "\"4\"",
  "\"animation\"", ".true", ".false", ".false", ".true", ".true", ".true", ".true",
  ".true", ".true", ".true", ".true", ".true", "\"2\""]

def animRuntimeExpected : List String := [
  ".false", ".true", "\"1\"", "\"1.5\"", "\"1\"", "\"1\"", "\"0\"", "\"2\"",
  ".false", "\"1.25\"", "\"-0.5\"", "\"4\"", "\"none\"", "\"none\"", "\"none\"",
  "\"2.5\"", ".true", ".true", ".true", ".true", ".true", ".true", ".false"]

/-- `#anim` and `#animate` each emit one widget display value. -/
def animCommandSrc : String := r##"import Anim

def dot : Anim :=
  Anim.hold 1 (Anim.scene 200 120 [Anim.dot (Anim.pt 60 60) 8])

#anim dot
#animate dot
"##

def animGroup : Group where
  name := "anim"
  exercise := "lib/Anim.wiz"
  parallel := true
  cases := [
    { name := "easing: endpoints, monotone on a grid, symmetric, exact fixed values", run := fun _ => do
        okLibs (← IO.FS.readFile "Tests/data/anim/easing.wiz") animEasingExpected },
    { name := "time: zero duration, clamping, eased progress, sampled endpoints and counts; frame determinism", run := fun _ => do
        okLibs (← IO.FS.readFile "Tests/data/anim/laws.wiz") animLawsExpected },
    { name := "morph: point/segment/polyline/circle/arc, undefined morphs hold the start; move, rotate, scale, fade", run := fun _ => do
        okLibs (← IO.FS.readFile "Tests/data/anim/morph.wiz") animMorphExpected },
    { name := "payload: wiz.widget/1 anim, 24 sampled frames, runtime and controls, no script or link", run := fun _ => do
        okLibs (← IO.FS.readFile "Tests/data/anim/payload.wiz") animPayloadExpected },
    { name := "runtime: play/pause/scrub/rate/tick are pure transitions; decimal events parse exactly", run := fun _ => do
        okLibs (← IO.FS.readFile "Tests/data/anim/runtime.wiz") animRuntimeExpected },
    { name := "#anim and #animate emit one WIZ_WIDGET: anim message each (schema, kind, SVG, no script)", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) animCommandSrc
          { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render animCommandSrc
        unless errs.isEmpty do
          throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
        let texts := s.messages.toList.map (·.text)
        check (texts.length == 2) s!"#anim: expected two messages, got {texts.length}"
        for t in texts do
          check (t.startsWith "WIZ_WIDGET:") s!"#anim: no WIZ_WIDGET: prefix: {t.take 40}"
          check ((t.splitOn "\"schema\":\"wiz.widget/1\"").length > 1) "#anim: no widget schema"
          check ((t.splitOn "\"kind\":\"anim\"").length > 1) "#anim: not an anim widget"
          check ((t.splitOn "\"mimeType\":\"image/svg+xml\"").length > 1) "#anim: no SVG mime type"
          check ((t.splitOn "<svg").length > 1) "#anim: no SVG document"
          check (!((t.splitOn "<script").length > 1)) "#anim: the payload contains a script"
          check (!((t.splitOn "href").length > 1)) "#anim: the payload has an external reference" },
    { name := "#anim without Anim is one error saying to import Anim", run := fun _ =>
        failsLibs "#anim (fun (A : Type) => A)\n" "#anim: import Anim first" },
    { name := "golden frames: examples/anim-unwind.wiz (t = 0, 1.5, 3), byte for byte", run := fun _ => do
        let u0 ← IO.FS.readFile "Tests/data/anim/unwind-t0.svg"
        let u1 ← IO.FS.readFile "Tests/data/anim/unwind-t1.svg"
        let u2 ← IO.FS.readFile "Tests/data/anim/unwind-t2.svg"
        cRunLibs (← IO.FS.readFile "examples/anim-unwind.wiz")
          (String.intercalate "\n@@\n" [u0, u1, u2]) },
    { name := "golden frames: examples/anim-sine.wiz (t = 0, 2, 4), byte for byte", run := fun _ => do
        let s0 ← IO.FS.readFile "Tests/data/anim/sine-t0.svg"
        let s1 ← IO.FS.readFile "Tests/data/anim/sine-t1.svg"
        let s2 ← IO.FS.readFile "Tests/data/anim/sine-t2.svg"
        cRunLibs (← IO.FS.readFile "examples/anim-sine.wiz")
          (String.intercalate "\n@@\n" [s0, s1, s2]) }
  ]

builtin_initialize registerGroup animGroup

end Tests.Elab
