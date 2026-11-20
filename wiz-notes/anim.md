# Anim — design note (2026-11-20, branch `anim`)

`lib/Anim.wiz` is a math-animation library for the infoview and notebooks. This note
records the decisions, the algebra and what the widget host still has to supply. The
user-facing version is `docs/anim.md`; the tests are `Tests/Groups/Anim.lean` with the
Wiz sources in `Tests/data/anim/`.

## Why a pure function of time

The brief's testability requirement decides the representation. `Anim` is

```
structure Anim where
  title : String
  duration : Q
  at : Q → Scene
```

and the sampler is `Anim.frame a t = a.at (clamp t 0 a.duration)`. There is no clock, no
mutable state, no randomness and no host time inside the library. A golden test compares
`Anim.svg (Anim.frame a t)` at fixed exact rational `t`; two calls are byte-identical.
The host owns the clock and the runtime state (`Anim.Runtime`); the library only supplies
the pure transition.

Exact rationals (`Q`) rather than `Float64`: `Float64` is an axiom in `lib/IO.wiz`
(opaque to the kernel and `#eval`), and a frame that used it could not be checked or
compared byte for byte. Everything (time, progress, easing, coordinates, angles) is a
`Q`; `Plot.qRound` rounds each coordinate once to an integer pixel. Trigonometry is a
fixed-point integer Taylor series (`Anim.sinFixed`, six decimals) so arcs and rotation do
not call the host's `libm`.

## Scene model

`Scene = (width, height, background, [Item])`; `Item = (Shape, Style)`. Shapes are
`point`, `segment`, `polyline`, `circle`, `arc` (centre, radius, start, sweep in degrees,
clockwise on screen) and `text` (position, string, size, anchor). Styles are `stroke`,
`fill` (`"none"` allowed), `width`, `opacity`, `dash`.

Coordinates are SVG pixels, `y` down. `Anim.Plane` is the math-coordinate adapter: origin
at a pixel, `sx`/`sy` pixels per unit, `y` up (`cy − y·sy`). The examples use it.

`Scene.overlay` is list append with size union and a background rule (`"none"` means the
empty scene) so `Scene.empty` is a two-sided identity. Painting order is observable, so
`overlay` is deliberately not commutative.

Transformations are shape-level (`translate`, `scaleAbout`, `rotateAbout`) and scene-level
(`mapShape`, `mapStyle`, `fade`). `Anim.tween d ease f s` is the one place time becomes a
`[0, 1]` parameter; `move`, `rotateOver`, `scaleOver`, `fade`, `morph`, `morphWith` and
`morphItem` are its convenience forms.

Morphing is defined only where it is continuous: same constructor (and same polyline
length; same text string/anchor). `Shape.morphSome` returns `Option`; `morphOr` is the
total fallback used by animations — hold the start until `u = 1`, then the target, so
`morphOr a b 1 = b` unconditionally.

## The algebra and its laws

Two monoids over `Anim` and one over `Scene`:

* `(Anim, seq, empty)`: `seq` is associative, `empty` is two-sided identity.
* `(Anim, par, empty)`: associative, two-sided identity; not commutative (paint order).
* `(Scene, overlay, Scene.empty)`: associative, two-sided identity; not commutative.

`seq` samples `a` on `[0, a.duration]` and `b` on `[0, b.duration]`; the seam shows
`a`'s final frame. A zero-duration side is skipped explicitly, which is what makes the
identity hold at the seam (`seq a empty` at `t = duration` shows `a`'s final frame, not
`empty`).

Derived operations and laws:

```
stagger g a b = par a (delay g b)
stagger 0 a b = par a b
delay 0 a = a
delay g (seq a b) = seq (delay g a) b

reverse (reverse a) = a
duration (reverse a) = duration a
reverse empty = empty
reverse (seq a b) = seq (reverse b) (reverse a)      -- continuous composition

speed 1 a = a
speed (m·n) a = speed m (speed n a)
speed k (seq a b) = seq (speed k a) (speed k b)
duration (speed k a) = duration a / k
retime id (duration a) a = a

loop 0 a = empty
loop 1 a = a                                    -- for a positive duration
loop (m+n) a = seq (loop m a) (loop n a)             -- seamless a (first = final)
duration (loop n a) = n · duration a
```

The reverse anti-composition and the loop-splitting law are stated for **continuous**
compositions. A discontinuous `seq` has a jump at its seam (the seam shows the first
piece's final frame); reversing moves that jump to the boundary between the reversed
pieces, so the two sides can differ at that one instant. The tests use continuous pieces
(`move` segments that meet) and a constant animation for `loop`, and sample a grid that
includes the seams.

Easing: every curve clamps to `[0, 1]`, has `e 0 = 0`, `e 1 = 1`, and is monotone on the
grid; `easeInOut` and `easeInOutCubic` are symmetric. Tested for `linear`, `easeIn`,
`easeOut`, `easeInOut`, the three cubic variants and `holdEase`.

Equality in the tests is equality of the rendered SVG at a fixed time grid, not
structural equality of `Q` fractions (unreduced fractions can differ as terms while being
the same number; the renderer rounds them to the same pixel). This is the right notion for
the deliverable and is what the golden frames check too.

## Widget payload and interactivity

`Anim.payload a` is a `wiz.widget/1` bundle: `kind: "anim"`, `mimeType:
"image/svg+xml"`, `title`, `summary`, `width`, `height`, frame-0 `svg`/`html`, `duration`,
`frameCount` (24), `frames` (24 `{t, svg}` documents, both ends included), `runtime`,
`controls`, `count`.

Controls are **data**: `{name, kind, event, value|min/max/step}` for play, pause, scrub
and speed. There is no DOM code, no id and no script in the library or the payload. The
runtime is a record `{playing, time, rate, loop}` and the library supplies:

* `Anim.initial` (paused, time 0, rate 1, looping),
* `Anim.handle a r event value : Runtime` for `play`, `pause`, `toggle`, `scrub`, `rate`
  and `tick`; decimal values are parsed exactly (`Anim.parseQ`), and `scrub`/`tick` wrap
  when looping and clamp otherwise,
* `Anim.step a r dt`, `Anim.frameAtRuntime`, `Anim.payloadAt`, `Anim.widgetAt`.

### What the host still has to do

1. **Static frames.** Render `html` (or `svg`) and step through `frames` with a timer,
   using `runtime`/`controls` for the UI. This needs nothing from Wiz and is fully
   deterministic; frame 0 is also the `image/svg+xml` fallback and the static picture.
2. **Exact re-render.** Persist the `Runtime` host-side, forward `{event, value}`, ask the
   session to evaluate `Anim.handle a r event value` and then `Anim.htmlAt a r.time` (or
   `Anim.widgetAt a r`), and replace the figure. `#anim` is a message, not a comm, so the
   host must keep the runtime between messages; the natural extension is a comm for anim
   output, like `lib/Web/Widget.wiz`'s `Widget.handle` (the kernel re-enters the session
   and returns a new payload). A host with its own clock can use `Anim.step` instead of
   a `tick` event.

The payload is self-contained: no `href`/`src`, no `url(…)`, no `<script>`, no ids and no
timestamps. The browser infoview's existing `WIZ_WIDGET:` path already treats any widget
message as a widget item and uses `summary` as its title, so `#anim` needs no host
change to be shown; only live controls need the protocol above.

## Command

`#anim expr` and `#animate expr` are builtin commands in `Wiz/Parser/Builtin.lean` and
`Wiz/Elab/Command.lean`, cloned from `#plot`: elaborate the term, apply `Anim.widget` and
report the string as one command message. They are listed in `Wiz/Cache.lean`'s
`cacheable` set, and `selfhost/Tables.wiz` was regenerated (the self-hosted front end
still reports them as unsupported commands, like `#plot`; the Lean front end implements
them).

## Limits

3D, clipping, Bézier paths, text metrics (labels use fixed offsets), colour interpolation
in a morph (the style switches at the end), a client-side runtime and audio are not in
the library. Colour spaces stay the fixed sRGB hex strings of `Plot.colour`; the scene
model is intentionally small so payloads stay self-contained.
