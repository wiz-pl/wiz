import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## M0.0 triage: definitional regularity (D1) and sizes (D2)

The experiments of `wiz-notes/stc-m0-triage.md`, kept as regressions. They pin what the
kernels currently do; they do **not** claim a contradiction:

* **D1.** Abel–Coquand's box program (the closest faithful encoding: Wiz's `cast` at a
  proposition is the equivalence, so their literal term is not expressible) checks in
  every mode, and forcing the proof (the box's cast) terminates with a *stuck* cast — the
  evaluator never applies regularity. `--regularity full` is a rule of conversion only,
  and `--eager-proofs` (P2 off) still terminates. If a future change makes regularity a
  rule of evaluation, the `#reduce` below is the reproducer that times out.
* **D2.** `∞ : Size< ∞` is rejected by both kernels, so Agda's `∞ < ∞` (#3026) cannot be
  replayed. The known residual is `g ∞ Nat.zero`: its type is `(0 k : Size< ∞) × Unit`,
  but it reduces to `(∞, ())`, and the reduct is not usable as a `Size< ∞` (the size
  checker decides `<` on the value, not on the type). The probes below pin both halves.

The commands, results and the decision input are in `wiz-notes/stc-m0-triage.md`. -/

/-- The Abel–Coquand box program with `#reduce Omega` appended: checking must finish, and
the read-back of the proof must not loop. `triageTerminates` runs this in a child process
with a timeout, so a regression is a failure, not a hang. -/
def triageAcForced : String := abelCoquand ++ "#reduce Omega\n"

/-- The sized-types residual: `g ∞ Nat.zero` has the type `(0 k : Size< ∞) × Unit` and
reduces to `(∞, ())`, but nothing may use the reduct's first component as a `Size< ∞`. -/
def triageSized : String :=
  "inductive Nat where\n  | zero\n  | succ (n : Nat)\n" ++
  "def NatAt (s : Size) : Type := Nat^s\n" ++
  "def g {s : Size} (x : Nat^s) : (0 k : Size< s) × Unit :=\n" ++
  "  Nat.scasesOn (s := s) (fun _ => (0 k : Size< s) × Unit) (fun j => (j, ())) (fun j n => (j, ())) x\n"

/-- `checkTerminates` (the copy of `Tests/Groups/Ott.lean`'s helper, which is in this
namespace but another module): `input` under `mode` finishes, without errors, in `secs`. -/
def triageTerminates (input mode : String) (secs : Nat := 10) : IO Unit := do
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "input.wiz") input
  let self ← IO.appPath
  let out ← IO.Process.output { cmd := "sh", cwd := dir, args := #["-c",
    s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --check {mode} input.wiz", self.toString] }
  unless out.exitCode == 0 do
    throw (IO.userError s!"expected success, got exit code {out.exitCode}: {out.stderr.take 1000}")

def stcTriageGroup : Group where
  name := "stc-triage"
  exercise := "M0.0: D1 (definitional regularity) and D2 (sizes)"
  cases := [
    -- D1: the program checks in every mode, including full regularity with proofs
    -- evaluated; and forcing the proof terminates (the evaluator leaves the cast stuck)
    { name := "D1 (Abel–Coquand): the box program checks in every mode, and forcing the proof terminates", run := fun _ => do
        ok (abelCoquand)
        okWith .full (abelCoquand)
        for mode in ["off", "full", "off+eager", "full+eager"] do
          triageTerminates triageAcForced mode },
    -- D1: the read-back is a stuck cast, not a loop. (If this ever becomes a value, a
    -- regularity-as-reduction change has landed.)
    { name := "D1 (Abel–Coquand): the forced proof reads back as a value with a stuck cast", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) triageAcForced
        let infos := s.messages.toList.map (·.text)
        unless infos.any (fun t => t.contains "cast") do
          throw (IO.userError s!"expected a stuck cast in the normal form, got:\n{infos}")
        unless (s.messages.filter (·.severity == .error)).isEmpty do
          throw (IO.userError "the program has an error") },
    -- D2: the surface rule. `∞` is not a `Size< ∞` (and not a `Size< ↑∞`).
    { name := "D2: ∞ is not a size below itself", run := fun _ => do
        fails "def bad : Size< ∞ := ∞" "mismatch"
        fails "def bad : Size< ↑∞ := ∞" "mismatch" },
    -- D2: the residual subject-reduction gap. The reduct exists, but `<` is never taken
    -- from a type: `(g ∞ zero).1` is rejected as a `Size< ∞`, and the pair `(∞, ())` is
    -- rejected at the Σ type. The harmless conversion at `Nat^{∞}` is accepted.
    { name := "D2: the scase reduct of a closed term is (∞, ()) but is not a Size< ∞", run := fun _ => do
        ok (triageSized ++ "#reduce g (s := ∞) Nat.zero") ["(∞, ())"]
        fails (triageSized ++ "def direct : (0 k : Size< ∞) × Unit := (∞, ())") "type mismatch"
        fails (triageSized ++ "def k0 : Size< ∞ := (g (s := ∞) Nat.zero).1") "not below"
        ok (triageSized ++ "def coerce (x : Nat) : NatAt (g (s := ∞) Nat.zero).1 := x") },
    -- D2: Agda #3026's well-founded route needs a closed `Size< ∞` (to build `Acc ∞`).
    -- The `Acc` family is definable as a raw description, but its constructor needs
    -- `(h : Size< ∞) → Acc h`; `(∞, ())` is not that, and no closed inhabitant exists.
    { name := "D2: Acc ∞ has no closed inhabitant, so the #3026 replay has no base", run := fun _ => do
        ok ("def AccD : Desc Size := Desc.arg ω Size (fun s => Desc.hrec ω (Size< s) (fun h => h) (Desc.ret s))\n" ++
          "def Acc (s : Size) : Type := μ AccD s\n")
        fails ("def AccD : Desc Size := Desc.arg ω Size (fun s => Desc.hrec ω (Size< s) (fun h => h) (Desc.ret s))\n" ++
          "def Acc (s : Size) : Type := μ AccD s\n" ++
          "def noBase : Acc ∞ := con (∞, ())") "type mismatch" }
  ]

builtin_initialize registerGroup stcTriageGroup

end Tests.Elab
