import Wiz.Compiler.Erase

/-!
# The generic eliminators, as code

The interpreter implements `ind`, `Desc.elim` and `out` natively (`Run.lean`). The
backend instead compiles these definitions, written in the erased language, like any
other code. They walk the description at runtime, exactly as the interpreter does
(see its module docstring). A description is `⟨0 i⟩` (ret), `⟨1 ◾ F⟩` (arg; `⟨4 ◾ F⟩`
for a tag), `⟨2 j D⟩` (rec) or `⟨3 ◾ j D⟩` (hrec); `⟨5 D⟩` marks the description of
numbers. Lazy codata is `⟨1000 D step i s⟩` (`coit`) or `⟨1001 f i a⟩` (`scofix`).

Data is flat (`Erase.lean`); `pack` and `unpack` convert between flat objects and
payloads of nested pairs, which `ind` and `map` walk.
-/

namespace Wiz.PrimCode

open ETerm

private def v (i : Nat) : ETerm := .var i
private def g (n : Name) : ETerm := .global n
private def p (i : Nat) (t : ETerm) : ETerm := .proj i t
private def lams (xs : List Name) (b : ETerm) : ETerm := xs.foldr .lam b

/-- The description inside the mark of numbers. -/
private def unwrap (d : ETerm) : ETerm := .case d #[d, d, d, d, d, p 0 d]

/-- `ind D m i x = m i u (hyps D m D u)` with `u = unpack D x` -/
def ind : ETerm :=
  -- x0 i1 m2 D3; then u0 x1 i2 m3 D4
  lams ["D", "m", "i", "x"] (.letE "u" (.prim .unpack #[v 3, v 0])
    (apps (v 3) [v 2, v 0, apps (g "wiz.hyps") [v 4, v 3, unwrap (v 4), v 0]]))

/-- The induction hypotheses: `ind` at every recursive field. -/
def hyps : ETerm :=
  -- xs0 d1 m2 D3
  let arg := apps (g "wiz.hyps") [v 3, v 2, .app (p 1 (v 1)) (p 0 (v 0)), p 1 (v 0)]
  lams ["D", "m", "d", "xs"] (.case (v 1) #[
    .erased,
    arg,
    .obj 0 #[apps (g "wiz.ind") [v 3, v 2, p 0 (v 1), p 0 (v 0)],
             apps (g "wiz.hyps") [v 3, v 2, p 1 (v 1), p 1 (v 0)]],
    -- h0 xs1 d2 m3 D4
    .obj 0 #[.lam "h" (apps (g "wiz.ind") [v 4, v 3, .app (p 1 (v 2)) (v 0), .app (p 0 (v 1)) (v 0)]),
             apps (g "wiz.hyps") [v 3, v 2, p 2 (v 1), p 1 (v 0)]],
    arg])

/-- `unpack D v`: the payload of a flat object (or a number). -/
def unpack : ETerm :=
  -- v0 D1
  lams ["D", "v"] (.case (v 1) #[
    apps (g "wiz.unpackAt") [v 1, v 0, .natLit 0],
    apps (g "wiz.unpackAt") [v 1, v 0, .natLit 0],
    apps (g "wiz.unpackAt") [v 1, v 0, .natLit 0],
    apps (g "wiz.unpackAt") [v 1, v 0, .natLit 0],
    -- t0 v1 D2
    .letE "t" (.prim .tag #[v 0])
      (.obj 0 #[v 0, apps (g "wiz.unpackAt") [.app (p 1 (v 2)) (v 0), v 1, .natLit 0]]),
    -- a number: `0 ↦ ⟨⟨0⟩ ⟨◾ ◾⟩⟩`, `n+1 ↦ ⟨⟨1⟩ ⟨n ⟨◾ ◾⟩⟩⟩`
    .case (.prim .natTag #[v 0]) #[
      .obj 0 #[.obj 0 #[], .obj 0 #[.erased, .erased]],
      .obj 0 #[.obj 1 #[], .obj 0 #[.prim .natPred #[v 0], .obj 0 #[.erased, .erased]]]]])

/-- `unpackAt d v n`: the rest of the payload, from field `n` of `v`, along `d`. -/
def unpackAt : ETerm :=
  -- n0 v1 d2; then f0 n1 v2 d3
  let next (d' : ETerm) := apps (g "wiz.unpackAt") [d', v 1, .prim .natSucc #[v 0]]
  let arg := .letE "f" (.prim .fieldAt #[v 1, v 0])
    (.obj 0 #[v 0, apps (g "wiz.unpackAt") [.app (p 1 (v 3)) (v 0), v 2, .prim .natSucc #[v 1]]])
  lams ["d", "v", "n"] (.case (v 2) #[
    .obj 0 #[.erased, .erased],
    arg,
    .obj 0 #[.prim .fieldAt #[v 1, v 0], next (p 1 (v 2))],
    .obj 0 #[.prim .fieldAt #[v 1, v 0], next (p 2 (v 2))],
    arg])

/-- `pack D x`: a payload as a flat object (or a number). -/
def pack : ETerm :=
  -- x0 D1
  lams ["D", "x"] (.case (v 1) #[
    .prim .mkObj #[.obj 0 #[], apps (g "wiz.fields") [v 1, v 0]],
    .prim .mkObj #[.obj 0 #[], apps (g "wiz.fields") [v 1, v 0]],
    .prim .mkObj #[.obj 0 #[], apps (g "wiz.fields") [v 1, v 0]],
    .prim .mkObj #[.obj 0 #[], apps (g "wiz.fields") [v 1, v 0]],
    .prim .mkObj #[p 0 (v 0), apps (g "wiz.fields") [.app (p 1 (v 1)) (p 0 (v 0)), p 1 (v 0)]],
    .case (p 0 (v 0)) #[.natLit 0, .prim .natSucc #[p 0 (p 1 (v 0))]]])

/-- `fields d x`: the fields of a payload, as a list of nested pairs ending in `◾`. -/
def fields : ETerm :=
  -- x0 d1
  let arg := .obj 0 #[p 0 (v 0), apps (g "wiz.fields") [.app (p 1 (v 1)) (p 0 (v 0)), p 1 (v 0)]]
  lams ["d", "x"] (.case (v 1) #[
    .erased,
    arg,
    .obj 0 #[p 0 (v 0), apps (g "wiz.fields") [p 1 (v 1), p 1 (v 0)]],
    .obj 0 #[p 0 (v 0), apps (g "wiz.fields") [p 2 (v 1), p 1 (v 0)]],
    arg])

/-- `Desc.elim mret marg mrec mhrec D` -/
def delim : ETerm :=
  -- D0 mhrec1 mrec2 marg3 mret4
  -- s0 D1 mhrec2 mrec3 marg4 mret5
  let arg := apps (v 3) [.erased, .erased, p 1 (v 0),
    .lam "s" (apps (g "wiz.delim") [v 5, v 4, v 3, v 2, .app (p 1 (v 1)) (v 0)])]
  lams ["mret", "marg", "mrec", "mhrec", "D"] (.case (v 0) #[
    .app (v 4) (p 0 (v 0)),
    arg,
    apps (v 2) [.erased, p 0 (v 0), p 1 (v 0), apps (g "wiz.delim") [v 4, v 3, v 2, v 1, p 1 (v 0)]],
    apps (v 1) [.erased, .erased, p 1 (v 0), p 2 (v 0), apps (g "wiz.delim") [v 4, v 3, v 2, v 1, p 2 (v 0)]],
    arg])

/-- `map D f xs`: apply `f` to the recursive positions of a payload. -/
def map : ETerm :=
  -- xs0 f1 d2
  let arg := .obj 0 #[p 0 (v 0), apps (g "wiz.map") [.app (p 1 (v 2)) (p 0 (v 0)), v 1, p 1 (v 0)]]
  lams ["d", "f", "xs"] (.case (v 2) #[
    v 0,
    arg,
    .obj 0 #[apps (v 1) [p 0 (v 2), p 0 (v 0)], apps (g "wiz.map") [p 1 (v 2), v 1, p 1 (v 0)]],
    -- h0 xs1 f2 d3
    .obj 0 #[.lam "h" (apps (v 2) [.app (p 1 (v 3)) (v 0), .app (p 0 (v 1)) (v 0)]),
             apps (g "wiz.map") [p 2 (v 2), v 1, p 1 (v 0)]],
    arg])

/-- `out x`: run one step of a lazy coinductive value, and remember it: `lazySet`
overwrites a shared cell with the payload (`⟨1002 p⟩`, lazy tag 3), which later
observations return. -/
def out : ETerm :=
  lams ["x"] (.case (.prim .lazyTag #[v 0]) #[
    v 0,
    -- coit D step i s: map D (fun j s => coit D step j s) (step i s);  inside: s0 j1 x2
    .prim .lazySet #[v 0, apps (g "wiz.map") [p 0 (v 0),
      lams ["j", "s"] (.prim .coit #[p 0 (v 2), p 1 (v 2), v 1, v 0]),
      apps (p 1 (v 0)) [p 2 (v 0), p 3 (v 0)]]],
    -- scofix f i a: out (f ◾ (fun i a => scofix f i a) i a);  inside: a0 i1 f2
    .prim .lazySet #[v 0, .app (g "wiz.out") (apps (p 0 (v 0)) [.erased,
      lams ["i", "a"] (.prim .scofix #[p 0 (v 2), v 1, v 0]), p 1 (v 0), p 2 (v 0)])],
    -- observed: the payload
    p 0 (v 0)])

def all : List (Name × ETerm) :=
  [("wiz.ind", ind), ("wiz.hyps", hyps), ("wiz.delim", delim), ("wiz.map", map), ("wiz.out", out),
   ("wiz.unpack", unpack), ("wiz.unpackAt", unpackAt), ("wiz.pack", pack), ("wiz.fields", fields)]

end Wiz.PrimCode
