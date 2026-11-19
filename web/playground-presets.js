// (11ab) The playground's examples. They are plain source text: the page puts one in
// the editor and the self-hosted checker runs it exactly as if it had been typed. Each
// preset is also checked by web/playground_test.mjs, so an example never rots.
"use strict";

export const presets = Object.freeze([
  {
    id: "basics",
    title: "Basics",
    code: `import Prelude

-- Everything here runs in the page: the self-hosted Wiz frontend and kernel
-- (selfhost/*.wiz, stage 11ab), compiled to WebAssembly by web/build-playground.sh.
def twice (n : Nat) : Nat := n + n

#check twice
#eval twice 21
`,
  },
  {
    id: "arithmetic",
    title: "Arithmetic",
    code: `import Prelude

def square (n : Nat) : Nat := n * n

#check square
#eval square 12
#eval Nat.mod 100 7
#eval Nat.beq (Nat.add 20 22) 42
`,
  },
  {
    id: "data",
    title: "Inductive data",
    code: `import Prelude

inductive Colour where
  | red
  | green
  | blue

def favourite : Colour := Colour.green

#check Colour
#check favourite
#eval favourite
`,
  },
  {
    id: "patterns",
    title: "Pattern matching",
    code: `import Prelude

def negate : Bool → Bool
  | .true => .false
  | .false => .true

def even : Nat → Bool
  | .zero => .true
  | .succ n => negate (even n)

#check even
#eval even 10
#eval even 7
`,
  },
  {
    id: "structures",
    title: "Structures",
    code: `import Prelude

structure Point where
  x : Nat
  y : Nat

def origin : Point := Point.mk 0 0
def shift (p : Point) : Point := Point.mk (p.x + 1) (p.y + 1)

#check Point
#check shift
#eval (shift origin).x
`,
  },
  {
    id: "lists",
    title: "Lists",
    code: `import Prelude

def numbers : List Nat := .cons 1 (.cons 2 (.cons 3 .nil))
def double (n : Nat) : Nat := n + n

def mapList {A B : Type} (f : A → B) : List A → List B
  | .nil => .nil
  | .cons x xs => .cons (f x) (mapList f xs)

#check mapList
#eval mapList double numbers
`,
  },
  {
    id: "tour",
    title: "Wiz in Y minutes",
    // The tour from the sample-page branch (`web/playground-tour.wiz` there), kept as an
    // example now that the page's first program is this menu's default.
    code: `import Prelude

-- Wiz in Y minutes: \`--\` starts a comment; commands begin at column 0, and
-- layout (indentation) only matters inside \`where\` and \`match\`. The page runs
-- this with the self-hosted frontend (selfhost/*.wiz) in WebAssembly; docs/tour.md is longer.

-- Literals; \`#check\` gives a type, \`#eval\` the kernel's normal form.
#check 42
#eval 6 * 7

-- Functions curry: \`add3 1 2\` waits for one more argument.
def add3 (a b c : Nat) : Nat := a + b + c

#eval add3 1 2 3

-- \`let\` binds an intermediate value; \`if\` is a two-branch match on Bool.
def parity (n : Nat) : Nat :=
  let r := Nat.mod n 2; if Nat.beq r 0 then 0 else 1

#eval parity 7

-- An inductive type, and a function by pattern-matching equations.
inductive Shape where
  | circle (r : Nat)
  | square (s : Nat)

def area : Shape → Nat
  | .circle r => 3 * r * r
  | .square s => s * s

-- Lists, recursion, and a function passed to \`List.map\`.
def total : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + total xs

#eval total (.cons 1 (.cons 2 (.cons 3 .nil)))
#eval List.map (fun n => n + 1) (.cons 1 (.cons 2 .nil))

-- A structure's fields are projections: \`p.x\`.
structure Point where
  x : Nat
  y : Nat

#eval (Point.mk 2 3).x

-- A class and its instance; the dictionary comes from instance search.
class Describe (A : Type) where
  describe : A → Nat
instance instDescribeNat : Describe Nat where
  describe := fun n => n + 1

#eval Describe.describe 41

-- A dependent type: \`Vec A n\` has \`n\` elements, so \`head\` needs a default.
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (Nat.succ n)

def head {A : Type} {n : Nat} (d : A) (v : Vec A n) : A := match v with
  | .cons _ x _ => x
  | .nil => d

#eval head 0 (Vec.cons 0 7 Vec.nil)

def twoPlusTwo : 2 + 2 = 4 := rfl   -- \`rfl\` closes a definitional equality

-- Answers from a built-in, a recursion and a pattern match.
#eval String.length "Wiz"
#eval total (List.map (fun n => n + 1) (.cons 2 (.cons 3 .nil)))
#eval area (.square 5)
`,
  },
]);

export const defaultPresetId = "basics";

export function findPreset(id) {
  return presets.find((p) => p.id === id) || null;
}

export function defaultPreset() {
  return findPreset(defaultPresetId);
}

export function presetOf(code) {
  return presets.find((p) => p.code === code) || null;
}
