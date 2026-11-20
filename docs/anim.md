# Animation: math scenes as a pure function of time (`lib/Anim.wiz`)

`import Anim` is a small math-animation library. An animation is a **pure function of
time**: a title, an exact duration in seconds, and `at : Q → Scene`. The public sampler
is `Anim.frame a t`, which clamps `t` into `[0, a.duration]`. There is no clock, no
mutable state and no randomness in the library: the host owns the clock, so a golden
test can compare `frame t` for a fixed `t` and two calls return the same bytes.

```
import Anim

def dot : Anim :=
  Anim.hold 1 (Anim.scene 200 120 [Anim.dot (Anim.pt 60 60) 8])

#eval Anim.svg (Anim.frame dot (1 : Q))   -- one deterministic SVG document
#eval Json.render (Anim.render dot)       -- a Jupyter mime bundle
#anim dot                                 -- a WIZ_WIDGET: anim payload (frame 0)
```

**Arithmetic.** Time, easing, coordinates, radii and angles are exact rationals (`Q`,
`lib/Rat.wiz`). Rendering rounds each coordinate once to an integer pixel
(`Plot.qRound`), so the SVG is byte-stable and the library is checkable and `#eval`-able.
Sine and cosine (for arcs and rotation) are an integer fixed-point algorithm
(`Anim.sinDeg`/`Anim.cosDeg`, six decimals), not the host's `libm`.

## The scene model

A `Scene` is a fixed pixel canvas (`width`, `height`, a background colour) and a list of
painted `Item`s, back to front. An `Item` is a `Shape` and a `Style`.

| shape | fields |
|-------|--------|
| `point` | centre, radius |
| `segment` | two endpoints |
| `polyline` | a list of points |
| `circle` | centre, radius |
| `arc` | centre, radius, start angle, sweep (degrees, clockwise on screen) |
| `text` | position, string, font size, anchor (`start`/`middle`/`end`) |

Coordinates are CSS pixels with `y` down, exactly as SVG draws them. For ordinary math
coordinates (`y` up) use `Anim.Plane`: `Anim.plane width height sx sy` puts the origin at
the centre and scales by `sx`/`sy` pixels per unit; `Plane.map`/`Plane.pt` convert.

A `Style` is `stroke`, `fill` (`"none"` for no fill), `width`, `opacity` and `dash` (an
SVG `stroke-dasharray`). `Anim.style` is a 2 px blue stroke with no fill;
`strokeColour`, `fillColour`, `lineWidth`, `withOpacity` and `dashed` change one field,
and `itemStroke`, `itemFill`, `itemWidth`, `itemOpacity`, `itemDashed` do the same to an
item.

Scenes compose with `Scene.overlay`, which takes the union of the canvases, the left
background (unless it is the empty scene's `"none"`) and appends the item lists. It is
associative and `Scene.empty` is its two-sided identity. It is **not commutative**:
painting order is observable.

## Transformations over time

Transformations are functions on shapes and scenes:

* `Shape.translate d`
* `Shape.scaleAbout c k` (radii and font sizes scale by `|k|`)
* `Shape.rotateAbout c deg` (clockwise on screen, fixed-point trigonometry)
* `Scene.mapShape f`, `Scene.mapStyle f`, `Scene.fade k`

A `Tween` turns time into a `[0, 1]` parameter and applies one of these:
`Anim.tween d ease f s`. The convenience forms are

```
Anim.move from to d ease s          -- translate by the lerped vector
Anim.rotateOver from to about d ease s
Anim.scaleOver from to about d ease s
Anim.fade from to d ease s          -- multiply every item's opacity
Anim.morph from to d ease s         -- morph a shape on top of s
Anim.morphWith style from to d ease s
Anim.morphItem from to d ease s
```

**Morphing** is defined shape by shape in `Shape.morphSome` (an `Option`):
point↔point, segment↔segment, circle↔circle and arc↔arc lerp their points and radii
(an arc also lerps its start and sweep); polyline↔polyline needs the same number of
points; text↔text needs the same string and anchor. Everything else is not a continuous
morph. `Shape.morphOr` is the total version used by the animations: an undefined morph
holds the start shape until the end and then shows the target, so `morph a b 1 = b`
always. `morphSome a a u = some a` for every defined shape.

## Easing

`Ease` is `Q → Q`, from progress to progress. All curves are exact, clamp their input to
`[0, 1]`, satisfy `e 0 = 0` and `e 1 = 1`, and are monotone: `linear`, `easeIn` (`u²`),
`easeOut` (`1 − (1−u)²`), `easeInOut` (smoothstep `3u² − 2u³`), `easeInCubic`,
`easeOutCubic`, `easeInOutCubic`, and `holdEase` (0 until 1). `easeInOut` and
`easeInOutCubic` are symmetric: `e (1−u) = 1 − e u`.

## Time arithmetic

* `duration` is in seconds, an exact `Q`. `frame a t` clamps `t` to `[0, duration]`, so
  sampling outside the interval returns the first/final frame rather than extrapolating.
* `Anim.eased d ease t = ease (clamp01 (t / d))`; a zero-length interval is already over,
  so it returns `ease 1`.
* `Anim.frameTime a i n = duration · i / (n−1)` for the `n` sampled times
  (`0, …, duration`); `sampleTimes a n` lists them, and `n = 1` is time 0.
* `seq` samples `a` on `[0, a.duration]` and `b` on `[0, b.duration]`; the seam shows
  `a`'s final frame. A composition whose pieces meet (`a.final = b.first`) has no visible
  jump; if they do not, `b`'s first frame is not shown at the seam.
* `delay g a` waits `g` seconds (showing the empty scene) and then plays `a`.
* `speed k a` scales time by `k` (`k ≥ 1`; `speed 0` is the identity so the function is
  total), `slow k` divides it, and `reverse a` samples `a` at `duration − t`.

## The combinator DSL

```haskell
seq      : Anim → Anim → Anim   -- a, then b
par      : Anim → Anim → Anim   -- both at once, b painted over a
stagger  : Q → Anim → Anim → Anim  -- a at 0, b at g
delay    : Q → Anim → Anim
loop     : Nat → Anim → Anim
retime   : (Q → Q) → Q → Anim → Anim
speed    : Nat → Anim → Anim
slow     : Nat → Anim → Anim
reverse  : Anim → Anim
empty    : Anim
hold     : Q → Scene → Anim
```

`stagger g a b` is defined as `par a (delay g b)`. `retime f d a` is the general form of
`speed`/`reverse`: sample `a` at `f t` for `t ∈ [0, d]`; the caller promises `f` maps
that interval into `[0, a.duration]`.

### Laws

The tests compare animations by the SVG of `frame` on a fixed grid of times that
includes every seam and both endpoints. Where a law involves a seam, the composition is
**continuous** (`a.final = b.first`); a discontinuous composition has a jump at the seam,
and the two sides can differ only there.

**Scenes** — `(Scene, overlay, Scene.empty)` is a monoid:

* `overlay (overlay a b) c = overlay a (overlay b c)`
* `overlay Scene.empty a = a = overlay a Scene.empty`
* `overlay a b ≠ overlay b a` in general (paint order).

**Animations** — `(Anim, seq, empty)` and `(Anim, par, empty)` are monoids:

* `seq (seq a b) c = seq a (seq b c)` and `par (par a b) c = par a (par b c)`
* `seq empty a = a = seq a empty` and `par empty a = a = par a empty`
* `par` is not commutative (it paints `b` over `a`).

**Sequencing and delaying**

* `stagger 0 a b = par a b`
* `stagger g a b = par a (delay g b)` (definition)
* `delay 0 a = a`
* `delay g (seq a b) = seq (delay g a) b`

**Reversal**

* `reverse (reverse a) = a`
* `duration (reverse a) = duration a`
* `reverse empty = empty`
* `reverse (seq a b) = seq (reverse b) (reverse a)` for a continuous composition (the
  seam is where the two sides could differ otherwise).

**Speed and retiming**

* `speed 1 a = a`
* `speed (m·n) a = speed m (speed n a)` (for `m, n ≥ 1`)
* `speed k (seq a b) = seq (speed k a) (speed k b)`
* `duration (speed k a) = duration a / k`
* `retime id (duration a) a = a`

**Repetition**

* `loop 0 a = empty`
* `loop 1 a = a` (for a positive duration; a zero-length animation has no frames to repeat)
* `loop (m+n) a = seq (loop m a) (loop n a)` when `a.first = a.final` (a seamless loop);
  otherwise the two sides differ only at the seam, by the seam convention above.
* `duration (loop n a) = n · duration a`.

**Morph**

* `morphSome a a u = some a` when `a` has a morph with itself (all shapes do)
* `morphOr a b 1 = b`
* `morphOr a b u = a` for `u < 1` when no continuous morph exists.

**Easing**

* `e 0 = 0`, `e 1 = 1`, and `e u ≤ e v` for `u ≤ v` on `[0, 1]`, for every curve above.
* `easeInOut (1−u) = 1 − easeInOut u` (and the same for `easeInOutCubic`).

## SVG and widgets

`Anim.svg` writes one deterministic document: coordinates rounded once, a fixed
attribute order, no ids, timestamps, scripts, `href`/`src` or `url(…)`. `Anim.svgAt a t`
is the SVG of one frame; `Anim.htmlAt` wraps it in a `<figure class="wiz-anim">` with the
title as a `<figcaption>`. `Anim.html` and `Anim.svgAt a 0` are the static fallback
(frame 0).

`#anim expr` (also `#animate expr`) is the command: it evaluates an `Anim`, calls
`Anim.widget`, and emits one `WIZ_WIDGET:` message, exactly as `#plot` does. The payload
is:

```json
{
  "schema": "wiz.widget/1",
  "kind": "anim",
  "mimeType": "image/svg+xml",
  "title": "A circle unwinding to a line",
  "summary": "animation: 3 s, 640x260 px, 24 sampled frames",
  "width": 640, "height": 260,
  "svg": "<svg …>", "html": "<figure …>",
  "duration": "3", "frameCount": 24,
  "frames": [{"t": "0", "svg": "<svg …>"}, …],
  "runtime": {"playing": false, "time": "0", "rate": "1", "loop": true},
  "controls": [
    {"name": "play", "kind": "button", "event": "click", "value": "play", "label": "Play"},
    {"name": "pause", "kind": "button", "event": "click", "value": "pause", "label": "Pause"},
    {"name": "scrub", "kind": "slider", "event": "input", "min": "0", "max": "3", "step": "0.01", "value": "0"},
    {"name": "speed", "kind": "slider", "event": "input", "min": "0.25", "max": "4", "step": "0.25", "value": "1"}
  ],
  "count": 1
}
```

`frames` holds `frameCount` evenly spaced frames (both ends included), so a host can
animate with no callback at all by flipping through them. `runtime` and `controls` are
the **interactive protocol**, expressed as data, not DOM code: the library's half is the
pure transition `Anim.handle a runtime event value : Runtime`
(`play`, `pause`, `toggle`, `scrub`, `rate`, `tick`; a decimal `value` is parsed exactly
by `Anim.parseQ`), plus `Anim.step a runtime dt` and
`Anim.frameAtRuntime`. `Anim.payloadAt a runtime` and `Anim.widgetAt` are the same
payload at a runtime state, with the current frame as the fallback.

`Anim.render a` is a Jupyter mime bundle (`text/plain`, `image/svg+xml`, `text/html`) in
the shape `Plot.render` uses.

### What the host still has to do

The library is pure; a host has two supported ways to animate, and may mix them.

1. **Static `frames`.** Render `html` (or `svg`) and advance through `frames` with a
   timer, holding `runtime`/`controls` for the UI. Nothing else is needed, and every
   frame is a fixed document from the payload.
2. **Exact re-render.** Keep the `Runtime` in the host, forward a control event
   (`{event, value}`) to the session, evaluate
   `Anim.handle a runtime event value` and then `Anim.htmlAt a runtime.time` (or
   `Anim.widgetAt a runtime`), and replace the figure. This needs the same kind of
   session re-entry as `Widget.handle` (`lib/Web/Widget.wiz`); `#anim` itself is a
   message, not a comm, so the host must persist the runtime between messages. A host
   with its own clock can call `Anim.step a runtime dt` instead of sending `tick`.

Not yet in the library: a DOM/JS runtime, smooth interpolation between sampled frames,
clipping and Bézier paths, text metrics, colour interpolation in a morph (the style
switches at the end), stacked timelines, and audio. The scene model is deliberately
small so that the payload stays self-contained and every frame is reproducible.

## Worked examples

* `examples/anim-unwind.wiz` — a circle of radius 55 peeling into a line of length
  `2πr`; three golden frames at `t = 0, 1.5, 3`.
* `examples/anim-sine.wiz` — `(x, sin x)` traced from `0` to `2π` with guide lines;
  three golden frames at `t = 0, 2, 4`.

Both are run by the `anim` test group (`lake test -- '=anim'`), which also checks the
combinator laws, easing monotonicity, the frame determinism, the payload schema and the
`#anim`/`#animate` command.
