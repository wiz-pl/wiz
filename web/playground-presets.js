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
