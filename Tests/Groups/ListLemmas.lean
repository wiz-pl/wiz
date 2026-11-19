import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/Data/ListLemmas.wiz` (issue #255): the list lemma set, membership with `∈` and
`∀ x ∈ l`, and the Boolean algebra of `lib/Logic.wiz`. -/
def listLemmasGroup : Group where
  name := "list-lemmas"
  exercise := "Issue #255"
  cases := [
    { name := "the library checks, also next to Json, Vec and Functor", run := fun _ => do
        okLibs "import Data.ListLemmas"
        okLibs ("import Json\nimport Vec\nimport Functor\nimport Data.ListLemmas\n" ++
          "#eval Nat.repr 42") ["\"42\""] },
    { name := "membership, the binder notation and evals (#check/#eval)", run := fun _ =>
        okLibs ("import Data.ListLemmas\n" ++
          "#check List.map_map\n" ++
          "#check List.mem_append\n" ++
          "#check List.all_eq_true\n" ++
          "#check (fun (x : Nat) (l : List Nat) => ∀ y ∈ l, x ∈ l)\n" ++
          "#eval List.map Nat.succ [1, 2, 3]\n" ++
          "#eval List.filter (fun x => Nat.lt x 3) [1, 2, 3]\n" ++
          "#eval List.reverse [1, 2, 3]\n" ++
          "#eval List.any (fun x => Nat.beq x 2) [1, 2, 3]\n" ++
          "#eval List.all (fun x => Nat.beq x 2) [1, 2, 3]\n" ++
          "#eval Bool.not (Bool.and .true .false)\n" ++
          "#eval Bool.or (Bool.not .true) .false\n" ++
          "#check Bool.and_eq_true\n")
          [
            "List.map_map : {A : Type} → {B : Type} → {C : Type} → (g : B → C) → (f : A → B) → (l : List A) → List.map B C g (List.map A B f l) = List.map A C (fun x => g (f x)) l",
            "List.mem_append : {A : Type} → (x : A) → (l : List A) → (m : List A) → (x ∈ List.append A l m ↔ x ∈ l ∨ x ∈ m)",
            "List.all_eq_true : {A : Type} → (p : A → Bool) → (l : List A) → (List.all A p l = .true ↔ (x : A) → x ∈ l → p x = .true)",
            "fun x l => (y : Nat) → y ∈ l → x ∈ l : Nat → List Nat → Prop",
            ".cons 2 (.cons 3 (.cons 4 .nil))",
            ".cons 1 (.cons 2 .nil)",
            ".cons 3 (.cons 2 (.cons 1 .nil))",
            ".true",
            ".false",
            ".true",
            ".false",
            "Bool.and_eq_true : (a : Bool) → (b : Bool) → (Bool.and a b = .true ↔ a = .true ∧ b = .true)"
          ] },
    { name := "map fusion, append and length in proofs", run := fun _ =>
        okLibs ("import Data.ListLemmas\n" ++
          "def fusion {A B C : Type} (f : B → C) (g : A → B) (l : List A) :\n" ++
          "    List.map f (List.map g l) = List.map (fun x => f (g x)) l :=\n" ++
          "  List.map_map f g l\n" ++
          "def fusionTwice {A B C D : Type} (f : C → D) (g : B → C) (h : A → B) (l : List A) :\n" ++
          "    List.map f (List.map g (List.map h l)) = List.map (fun x => f (g (h x))) l :=\n" ++
          "  Eq.trans (List.map_map f g (List.map h l))\n" ++
          "    (List.map_map (fun x => f (g x)) h l)\n" ++
          "def appendAssoc {A : Type} (l m n : List A) :\n" ++
          "    List.append (List.append l m) n = List.append l (List.append m n) :=\n" ++
          "  List.append_assoc l m n\n" ++
          "def appendNil {A : Type} (l : List A) : List.append l List.nil = l :=\n" ++
          "  List.append_nil l\n" ++
          "def mapAppend {A B : Type} (f : A → B) (l m : List A) :\n" ++
          "    List.map f (List.append l m) = List.append (List.map f l) (List.map f m) :=\n" ++
          "  List.map_append f l m\n" ++
          "def lengthReverse {A : Type} (l : List A) : List.length (List.reverse l) = List.length l :=\n" ++
          "  List.length_reverse l") },
    { name := "filter is sound and complete", run := fun _ =>
        okLibs ("import Data.ListLemmas\n" ++
          "def filteredSound {A : Type} (p : A → Bool) (x : A) (l : List A)\n" ++
          "    (h : x ∈ List.filter p l) : p x = .true :=\n" ++
          "  (List.filter_sound p x l h).2\n" ++
          "def filteredIn {A : Type} (p : A → Bool) (x : A) (l : List A)\n" ++
          "    (h : x ∈ List.filter p l) : x ∈ l :=\n" ++
          "  (List.filter_sound p x l h).1\n" ++
          "def filteredBack {A : Type} (p : A → Bool) (x : A) (l : List A)\n" ++
          "    (hx : x ∈ l) (hp : p x = .true) : x ∈ List.filter p l :=\n" ++
          "  List.filter_complete p x l hx hp\n" ++
          "def filteredAll {A : Type} (p : A → Bool) (l : List A)\n" ++
          "    (h : List.all p (List.filter p l) = .true) : ∀ x ∈ List.filter p l, p x = .true :=\n" ++
          "  (List.all_eq_true p (List.filter p l)).1 h") },
    { name := "any/all, append and the Boolean bridge", run := fun _ =>
        okLibs ("import Data.ListLemmas\n" ++
          "def anyWitness {A : Type} (p : A → Bool) (l : List A)\n" ++
          "    (h : List.any p l = .true) : ∃ x, x ∈ l ∧ p x = .true :=\n" ++
          "  (List.any_eq_true p l).1 h\n" ++
          "def allHolds {A : Type} (p : A → Bool) (l : List A)\n" ++
          "    (h : List.all p l = .true) : ∀ x ∈ l, p x = .true :=\n" ++
          "  (List.all_eq_true p l).1 h\n" ++
          "def anyAppend {A : Type} (p : A → Bool) (l m : List A)\n" ++
          "    (h : List.any p (List.append l m) = .true) :\n" ++
          "    List.any p l = .true ∨ List.any p m = .true :=\n" ++
          "  (Bool.or_eq_true (List.any p l) (List.any p m)).1\n" ++
          "    (@Eq.mp' Bool (List.any p (List.append l m))\n" ++
          "      (Bool.or (List.any p l) (List.any p m)) (fun t => t = .true)\n" ++
          "      (List.any_append p l m) h)\n" ++
          "def allAppend {A : Type} (p : A → Bool) (l m : List A)\n" ++
          "    (h : List.all p (List.append l m) = .true) :\n" ++
          "    List.all p l = .true ∧ List.all p m = .true :=\n" ++
          "  (Bool.and_eq_true (List.all p l) (List.all p m)).1\n" ++
          "    (@Eq.mp' Bool (List.all p (List.append l m))\n" ++
          "      (Bool.and (List.all p l) (List.all p m)) (fun t => t = .true)\n" ++
          "      (List.all_append p l m) h)") },
    { name := "reverse, membership and the Boolean laws", run := fun _ =>
        okLibs ("import Data.ListLemmas\n" ++
          "def reverseAppend {A : Type} (l m : List A) :\n" ++
          "    List.reverse (List.append l m) = List.append (List.reverse m) (List.reverse l) :=\n" ++
          "  List.reverse_append l m\n" ++
          "def reverseReverse {A : Type} (l : List A) : List.reverse (List.reverse l) = l :=\n" ++
          "  List.reverse_reverse l\n" ++
          "def memReverse {A : Type} (x : A) (l : List A) : (x ∈ List.reverse l) ↔ x ∈ l :=\n" ++
          "  List.mem_reverse x l\n" ++
          "def memAppend {A : Type} (x : A) (l m : List A) :\n" ++
          "    (x ∈ List.append l m) ↔ (x ∈ l ∨ x ∈ m) :=\n" ++
          "  List.mem_append x l m\n" ++
          "def deMorgan (a b : Bool) :\n" ++
          "    Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) :=\n" ++
          "  Bool.not_and a b\n" ++
          "def andBridge (a b : Bool) (h : Bool.and a b = .true) : a = .true :=\n" ++
          "  ((Bool.and_eq_true a b).1 h).1\n" ++
          "def absorption (a b : Bool) : Bool.and a (Bool.or a b) = a :=\n" ++
          "  Bool.and_absorb a b\n" ++
          "def notBridge (a : Bool) : (Bool.not a = .true) ↔ a = .false :=\n" ++
          "  Bool.not_eq_true a") }
  ]

builtin_initialize registerGroup listLemmasGroup

end Tests.Elab
