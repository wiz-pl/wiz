import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Linear-case stage 2 (K1: `scase` at a quantity, `T.casesOn1`; the unit eliminator
`let () := u; b`): the M4 acceptance probes of `wiz-notes/cohesion-resources.md` §7, the
negatives of the soundness argument (docs/CoreSpec.md §10.2, §10.2a): a linear variable is
never used twice, nor dropped, an erased one never used at run time; and linear-review's
counterexamples to the withdrawn K2a. -/
def linearCaseHeader : String :=
  "import Prelude\naxiom Tok : Type\naxiom use : (1 t : Tok) → Nat\n" ++
  "inductive Res1 (A : Type) where\n  | ok (1 a : A)\n  | err (e : Nat) (1 back : A)\n"

/-- At least one error, and the first mentions `fragment` (with every library importable):
for programs whose later declarations use a rejected one. -/
def rejectsLibs (input : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  let some e := errs[0]? | throw (IO.userError "expected an error, got none")
  unless (e.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{e}")

/-- linear-review's stash: a linear `t` hidden in a closure `(0 e : T = Unit) → Unit`. -/
def stashDef : String :=
  "def stash {T : Type} (1 t : T) : (0 e : T = Unit) → Unit := fun e => Eq.subst (fun (X : Type) => X) e t\n"

/-- A lock in C, a non-recursive mutex: `c_acquire` locks it (a second `c_acquire` without
a `c_release` in between would wait forever) and hands out a ticket number; `c_release`
(in IO) unlocks and counts. `c_poly` is a polymorphic foreign function that counts its
calls (for erasure's defence in depth). -/
def relHelper : String := "#include <stdint.h>
#include <pthread.h>
typedef uintptr_t wiz_val;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static uint64_t released = 0, next = 0, polys = 0;
uint64_t c_acquire(void) { pthread_mutex_lock(&mu); return next++; }
void c_release(uint64_t n) { (void)n; released++; pthread_mutex_unlock(&mu); }
uint64_t c_count(void) { return released; }
wiz_val c_poly(uint64_t n) { (void)n; polys++; return (wiz_val)1; }
uint64_t c_polys(void) { return polys; }
"

/-- A linear ticket for `relHelper`'s lock: acquired and released in IO (side effects live
in the world), released through `casesOn1`. -/
def ticketHeader : String :=
  "import IO\nextern \"c_acquire\" cAcquire : IO Nat\nextern \"c_release\" cRelease : Nat → IO Unit\n" ++
  "extern \"c_count\" cCount : IO Nat\n" ++
  "inductive Ticket where\n  | mk (n : Nat)\n" ++
  "def Ticket.release (1 t : Ticket) : IO Unit := match t with\n  | .mk n => cRelease n\n" ++
  "def withTicket {B : Type} (1 k : (1 t : Ticket) → IO B) : IO B :=\n  fun w => let 1 (n, w') := cAcquire w; k (Ticket.mk n) w'\n"

def ticketSrc : String := ticketHeader ++
  "def main : IO Unit :=\n  IO.bind (withTicket (fun t => IO.then1 (Ticket.release t) (IO.println \"first\")))\n" ++
  "    (fun _ => IO.bind (withTicket (fun t => IO.then1 (Ticket.release t) (IO.println \"second\")))\n" ++
  "      (fun _ => IO.bind cCount (fun c => IO.println (Nat.toString c))))\n"

def linearCaseGroup : Group where
  name := "linear-case"
  exercise := "docs/CoreSpec.md §10.2 (K1), §10.2a (the unit eliminator)"
  cases := [
    { name := "a2: a linear field matched out of a linear scrutinee, handed back in both alternatives (D8)", run := fun _ =>
        okLibs (linearCaseHeader ++ "def rebuild (1 r : Res1 Tok) : Res1 Tok := match r with\n  | .ok t => .ok t\n  | .err e t => .err e t\n") },
    { name := "n1: the resource dropped in one alternative is rejected", run := fun _ =>
        failsLibs (linearCaseHeader ++ "def drop (1 r : Res1 Tok) : Nat := match r with\n  | .ok t => 0\n  | .err e t => e\n") "quantity 1 but used 0" },
    { name := "n2: the resource duplicated is rejected", run := fun _ =>
        failsLibs (linearCaseHeader ++ "def dup (1 r : Res1 Tok) : Res1 Tok × Res1 Tok := match r with\n  | .ok t => (.ok t, .ok t)\n  | .err e t => (.err e t, .err e t)\n") "used ω" },
    { name := "the scrutinee used again after a linear match is rejected", run := fun _ =>
        failsLibs (linearCaseHeader ++ "def again (1 r : Res1 Tok) : Res1 Tok × Res1 Tok := (match r with\n  | .ok t => .ok t\n  | .err e t => .err e t, r)\n") "used ω" },
    { name := "a field at 0 is erased in a linear match: used at run time rejected, in an erased position accepted", run := fun _ => do
        let h := linearCaseHeader ++ "inductive R0 where\n  | mk (0 n : Nat) (1 t : Tok)\n"
        failsLibs (h ++ "axiom use0 : (n : Nat) → (1 t : Tok) → Nat\ndef f (1 r : R0) : Nat := match r with\n  | .mk n t => use0 n t\n") "quantity 0 but used ω"
        okLibs (h ++ "axiom use0 : (0 n : Nat) → (1 t : Tok) → Nat\ndef f (1 r : R0) : Nat := match r with\n  | .mk n t => use0 n t\n") },
    { name := "a linear match on an indexed family (the index equation at 0, a cast)", run := fun _ =>
        okLibs (linearCaseHeader ++ "inductive V : Nat → Type where\n  | nil : V .zero\n  | one (1 t : Tok) : V (.succ .zero)\n" ++
          "def f {n : Nat} (1 v : V n) : Nat := match v with\n  | .nil => 0\n  | .one t => use t\n") },
    { name := "nested linear matches: a linear field is matched again with casesOn1", run := fun _ =>
        okLibs (linearCaseHeader ++ "def flat (1 r : Res1 (Res1 Tok)) : Res1 Tok := match r with\n" ++
          "  | .ok s => (match s with\n    | .ok t => .ok t\n    | .err e t => .err e t)\n  | .err e s => (match s with\n    | .ok t => .err e t\n    | .err e' t => .err e' t)\n") },
    { name := "a3: a borrow scope over a linear handle, a one-constructor inductive `H | mk (1 val : S)`", run := fun _ =>
        okLibs ("import Region\ninductive Res1 (A : Type) where\n  | ok (1 a : A)\n  | err (e : Error) (1 back : A)\n" ++
          "inductive H (ρ : Region) (S : Type) where\n  | mk (1 val : S)\n" ++
          "def borrow1 {S B : Type} (0 σ : Region) (1 s : S)\n    (1 body : (0 ρ : Region) → (1 r : H ρ S) → Res1 ((ω b : B) × H ρ S)) : Res1 ((ω b : B) × S) :=\n" ++
          "  match body σ (H.mk s) with\n  | .ok p => let 1 (b, r) := p; (match r with\n    | .mk v => .ok (b, v))\n" ++
          "  | .err e p => let 1 (b, r) := p; (match r with\n    | .mk v => .err e (b, v))\n") },
    { name := "a3 as a structure: an ω field holding a linear value is a usage error, and a linear structure has no destructuring form", run := fun _ => do
        let pre (fld : String) := "import Region\ninductive Res1 (A : Type) where\n  | ok (1 a : A)\n  | err (e : Error) (1 back : A)\n" ++
          s!"structure H (ρ : Region) (S : Type) where\n  {fld}\n" ++
          "def borrow1 {S B : Type} (0 σ : Region) (1 s : S)\n    (1 body : (0 ρ : Region) → (1 r : H ρ S) → Res1 ((ω b : B) × H ρ S)) : Res1 ((ω b : B) × S) :=\n" ++
          "  match body σ (H.mk s) with\n  | .ok p => let 1 (b, r) := p; let 1 ⟨v⟩ := r; .ok (b, v)\n  | .err e p => let 1 (b, r) := p; let 1 ⟨v⟩ := r; .err e (b, v)\n"
        failsLibs (pre "val : S") "cannot take a value of the structure H apart at quantity 1"
        failsLibs (pre "1 val : S") "cannot take a value of the structure H apart at quantity 1" },
    { name := "a linear one-constructor type: a field dropped is rejected", run := fun _ =>
        failsLibs (linearCaseHeader ++ "inductive G where\n  | mk (n : Nat) (1 t : Tok)\n" ++
          "def g (1 x : G) : Nat := match x with\n  | .mk n t => n\n") "quantity 1 but used 0" },
    { name := "a linear Unit must be consumed: unused is rejected, `let () := u` consumes it once", run := fun _ => do
        failsLibs "import Prelude\ndef f (1 u : Unit) : Nat := 0\n" "used 0"
        failsLibs "import Prelude\ndef g (1 k : (0 n : Nat) → Unit) : Nat := 0\n" "used 0"
        okLibs "import Prelude\ndef f (1 u : Unit) : Nat := let () := u; 0\n"
        failsLibs "import Prelude\ndef f (1 u : Unit) : Nat := let () := u; let () := u; 0\n" "used ω"
        failsLibs "import Prelude\ndef f (0 u : Unit) : Nat := let () := u; 0\n" "quantity 0"
        failsLibs "import Prelude\ndef f (1 k : (0 n : Nat) → Unit) : Nat := let () := k; 0\n" "mismatch" },
    { name := "a token is not droppable, whether an axiom, a definition of Unit or a field-less structure", run := fun _ => do
        failsLibs "import Prelude\naxiom Tok : Type\ndef drop (1 t : Tok) : Nat := 0\n" "used 0"
        failsLibs "import Prelude\ndef Tok : Type := Unit\ndef drop (1 t : Tok) : Nat := 0\n" "used 0"
        failsLibs "import Prelude\nstructure Tok where\ndef drop (1 t : Tok) : Nat := 0\n" "used 0" },
    { name := "linear-review: a token hidden in a closure into Unit can't be dropped (leak1–4, 6)", run := fun _ => do
        let h := linearCaseHeader
        let subst := "fun e => Eq.subst (fun (X : Type) => X) e t"
        failsLibs (h ++ s!"def drop (1 t : Tok) : Nat :=\n  let 1 g : (0 e : Tok = Unit) → Unit := {subst}\n  0\n") "used 0"
        rejectsLibs (h ++ s!"def dropU (1 t : Tok) : Unit := let 1 g : (0 e : Tok = Unit) → Unit := {subst}; ()\n" ++
          "def drop (1 t : Tok) : Nat := let 1 u : Unit := dropU t; 0\n") "used 0"
        rejectsLibs (h ++ stashDef ++ "def drop (1 t : Tok) : Nat := let 1 g := stash t; 0\n") "used 0"
        failsLibs (h ++ s!"def drop (1 t : Tok) : Nat := (fun (1 g : (0 e : Tok = Unit) → Unit) => 0) ({subst})\n") "used 0"
        failsLibs (h ++ s!"def drop (1 t : Tok) : Nat :=\n  let 1 p : Nat × ((0 e : Tok = Unit) → Unit) := (0, {subst})\n  let 1 (n, g) := p\n  n\n") "used 0"
        -- (n_closurefield) the closure as a linear constructor field, matched and dropped
        failsLibs (h ++ "inductive C where\n  | mk (1 f : (0 e : Tok = Unit) → Unit)\n" ++
          s!"def stash (1 t : Tok) : C := .mk ({subst})\n" ++ "def drop (1 c : C) : Nat := match c with\n  | .mk f => 0\n") "used 0"
        -- and the closure can't be "consumed" by the unit eliminator: it is not a Unit
        failsLibs (h ++ s!"def drop (1 t : Tok) : Nat :=\n  let 1 g : (0 e : Tok = Unit) → Unit := {subst}\n  let () := g; 0\n") "mismatch" },
    { name := "linear-review: a unit-valued consumer's result must be consumed (leak5)", run := fun _ => do
        let h := linearCaseHeader ++ "axiom useU : (1 t : Tok) → Unit\n"
        failsLibs (h ++ "def drop (1 t : Tok) : Nat := (fun (1 u : Unit) => 0) (useU t)\n") "used 0"
        okLibs (h ++ "def fin (1 t : Tok) : Nat := let () := useU t; 0\n") },
    { name := "linear-review: a token stashed in a structure's tail can't be dropped (tail3)", run := fun _ => do
        failsLibs (linearCaseHeader ++ "inductive PL (P : Prop) : Type where\n  | up (h : P)\n" ++
          "def PL.down {P : Prop} (b : PL P) : P := match b with | .up h => h\n" ++
          "structure S (A : Type) where\n  n : Nat\n" ++
          "def mk (1 t : Tok) : S (PL (Tok = Unit)) := (0, fun b m => Eq.subst (fun (X : Type) => X) (PL.down b) t)\n" ++
          "def drop (1 t : Tok) : Nat := let 1 ⟨n⟩ := mk t; n\n") "cannot take a value of the structure S apart" },
    { name := "linear-review: a lock guard can't be forgotten (the deadlock repro is rejected)", run := fun _ =>
        rejectsLibs ("import IO\nimport MVar\n" ++ stashDef ++
          "def forget {T B : Type} (1 t : T) (1 k : IO B) : IO B := let 1 g := stash t; k\n" ++
          "def main : IO Unit :=\n  IO.bind Lock.new (fun l =>\n" ++
          "    IO.bind (Lock.acquire l (fun g => forget g (IO.println \"first acquire; guard forgotten\")))\n" ++
          "      (fun _ => Lock.acquire l (fun g => Lock.release l g (IO.println \"second acquire\"))))\n") "variable g declared with quantity 1 but used 0" },
    { name := "the linear match runs, compiled", run := fun _ =>
        ioRun ("import IO\ninductive Res1 (A : Type) where\n  | ok (1 a : A)\n  | err (e : Nat) (1 back : A)\n" ++
          "def get (1 r : Res1 Nat) : Nat := match r with\n  | .ok n => n\n  | .err e n => n\n" ++
          "def main : IO Unit := do\n  IO.println (Nat.toString (get (.ok 3)));\n  IO.println (Nat.toString (get (.err 4 5)))\n") "3\n5\n" },
    { name := "a linear lock ticket released in IO runs exactly once, compiled (C and LLVM)", run := fun _ =>
        -- (if the release were skipped, the second `c_acquire` would wait forever; if it
        -- ran twice, the count would be off)
        ioRunC ticketSrc relHelper "first\nsecond\n2\n" },
    { name := "side effects live in IO: an extern or implementation whose result has no runtime content is rejected", run := fun _ => do
        -- linear-review's stashes of a pure Unit-valued release (t_stash2, t_stash, t_res)
        -- start with the extern itself, which is now refused; so do the bypasses b1 (a
        -- named unit) and b3 (a proposition), and an erased function into Unit. The check
        -- is semantic (after whnf, erasure's own `erasable`)
        let m := "must carry something at run time"
        failsLibs "import IO\nextern \"c_release\" cRelease : Nat → Unit\n" m
        failsLibs "import IO\nextern \"c_release\" cRelease : (1 n : Nat) → Unit\n" m
        failsLibs "import IO\ndef Tk : Type := Unit\nextern \"c_release\" cRelease : Nat → Tk\n" m
        failsLibs "import IO\ndef P : Prop := True\nextern \"c_release\" cRelease : Nat → P\n" m
        failsLibs "import IO\nextern \"c_release\" cRelease : Nat → (0 k : Nat) → Unit\n" m
        failsLibs ("import IO\ndef rel (n : Nat) : Unit := ()\ndef relImpl (n : Nat) : Unit := ()\n" ++
          "attribute [implemented_by relImpl] rel\n") "has no runtime content"
        failsLibs ("import IO\ndef Tk : Type := Unit\ndef rel (n : Nat) : Tk := ()\ndef relImpl (n : Nat) : Tk := ()\n" ++
          "attribute [implemented_by relImpl] rel\n") "has no runtime content"
        -- an implementation at a proposition is a proof, erased too: allowed (externs are not)
        okLibs ("import IO\ndef pf (n : Nat) : n = n := refl n\ndef pfImpl (n : Nat) : n = n := refl n\n" ++
          "attribute [implemented_by pfImpl] pf\n")
        okLibs "import IO\nextern \"c_release\" cRelease : Nat → IO Unit\nextern \"c_sq\" cSq : Nat → Nat\n" },
    { name := "linear-review's erased-position stashes: with the release in IO there is no Unit to hide it in", run := fun _ => do
        -- (the same shapes, with the IO release: `t` must reach an IO action that is run;
        -- hiding it in an erasable value is a quantity error, or leaves a World unconsumed)
        let h := ticketHeader
        failsLibs (h ++ "def hide (1 t : Ticket) : (0 k : Nat) → Unit := fun k => ()\n") "used 0"
        failsLibs (h ++ "def hide (1 t : Ticket) : (0 k : Nat) → IO Unit := fun k => Ticket.release t\n" ++
          "def drop (1 t : Ticket) : Nat := let 1 g := hide t; 0\n") "used 0" },
    { name := "defence in depth: an extern call is kept where its type is erasable (C and LLVM)", run := fun _ =>
        ioRunC ("import IO\nextern \"c_poly\" cPoly : {A : Type} → Nat → A\nextern \"c_polys\" cPolys : IO Nat\n" ++
          "def main : IO Unit :=\n  let g : (0 k : Nat) → Unit := cPoly 5\n  IO.bind cPolys (fun c => IO.println (Nat.toString c))\n")
          relHelper "1\n" }
  ]

builtin_initialize registerGroup linearCaseGroup

end Tests.Elab
