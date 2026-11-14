# Stage 28: solvers

Automated solvers decide goals that are tedious to prove by hand: linear arithmetic side
conditions, Boolean identities, bit-vector facts. Wiz uses them in three ways, which
differ in what is trusted (design and survey: `wiz-notes/smt.md`):

* **`smt`** (28a) asks an SMT solver (Z3) and believes it: an axiom per
  use, behind a flag, as `native_refl` (stage 27) does for compiled evaluation;
* **`sat_decide`** (28b) asks a SAT solver (CaDiCaL) for a *proof*, an LRAT certificate,
  which a checker written in Wiz and proved sound checks in the kernel: nothing new is
  trusted, as with Lean's `bv_decide` (which runs its checker compiled, trusting the
  compiler) or Coq's SMTCoq;
* **`sat_decide_native`** (28e) is `sat_decide` with that check run compiled instead of
  by the kernel: an axiom per check, behind `--trust-native`, as 27a and 28a do.

## 28a: `smt` and `--trust-smt`

    def trans (a b c : Nat) (h₁ : Nat.lt a b = .true) (h₂ : Nat.lt b c = .true) :
        Nat.lt a c = .true := by smt
    def nn (x : UIntN 8) : UIntN.not (UIntN.not x) = x := by smt

`smt` is a tactic (lib/Prelude.wiz, over the request `Tac.smt`). It is accepted only

* with **`--trust-smt`** (`wiz check/build/run/lsp`, grail), off by default, a flag
  only (not a setting): "SMT solving is not enabled …" otherwise. `--smt-solver CMD`
  (default `z3`) and `--solver-timeout MS` (default 10 000) choose the solver; all flags only, never settings
  of a grail file;
* in the body of a `def` (the axiom is named after it, and takes its universe
  parameters).

**How.** The host translates the goal and its context to SMT-LIB 2 (`Wiz/Smt/Translate.lean`),
asserts the hypotheses and the negated goal, and runs the solver
(`Wiz/Smt/Process.lean`: a process call behind an `opaque`, as the module cache does;
answers are kept in `<cache>/smt` in a file named by the SHA-256 of the solver's identity
and the query, which the entry stores and every read compares; only a definite `sat` or
`unsat` is kept, never a timeout or a crash). `unsat`: the goal is closed by a new axiom
**`X.smt✝N⟨z3 5.1.0⟩ : Π ctx, goal`** (the goal over its context, with erased binders,
named after the definition, the use and the solver), applied to the context. `sat`: the
tactic fails with the solver's model, in the user's names. The definition gets a warning;
`#print axioms` lists the axiom, with a note, for it and everything that uses it.

**Constructors by position.** A constant of a fragment's sort is read by its tag's
*position* in the library type (`Bool` is `false | true`, `Nat` is `zero | succ`), never
by its label: types are structural, so `inductive Flip | true | false` is convertible
with `Bool` and `Flip.true` *is* `Bool.false`. Reading the label made `smt` prove
`b = (Flip.true : Bool) → b = .true`, and from it `Empty` (smt-review B1; group *smt*
keeps the case). Only names declared in lib/ (Prelude, Word, Logic, Int) are read as
SMT operations or sorts.

**The fragment.** Propositions (`→`, `¬`, `∧`, `∨`, `↔`, `True`, `False`, equations),
`Bool` (`Bool.and/or/not/xor`, comparisons), `Nat` as integers `≥ 0` (`+ *`, `succ`,
`pred`, `max`, truncated `-`, and `/`, `%` with Wiz's `x / 0 = 0`, `x % 0 = x`), and words
`UIntN w` with a numeral width as `(_ BitVec w)` (arithmetic, bitwise operations, shifts and
`testBit` by numerals, comparisons, `ofNat`, `toNat`). A subterm outside it becomes an
*atom* (a fresh constant; equal terms are the same constant): sound, since a formula valid
for an arbitrary value is valid for this one. Hypotheses outside it are dropped.

**Words are bit vectors because they are in range.** Mapping `UIntN w` to `(_ BitVec w)`
is sound only if every value is below `2^w`, where Word's definitions are the bit-vector
operations. Since 22l the constructor carries that proof. Before it, the kernel's
`UIntN 8` had values like `ofBitsTrusted 300`, on which `UIntN.not (UIntN.not x) = x`
is false (the kernel refuted it), so the prototype required a range hypothesis per word.

**What is trusted**: the solver (named in the axiom), the translation (one Lean file,
reviewed), the process plumbing (only the exact answer `unsat` closes a goal) and the
answer cache (named by a SHA-256 digest, each entry checked against the query it stores;
the command and module cache keys include the solver's version). Not trusted: whatever
built the goal (the axiom's statement is the goal itself, checked by the kernel as a
type). The flag and the solver settings are in the cache keys (commands, modules, grail's
jobs), so an acceptance is never replayed without the flag. `lib/` never uses `smt`
(group *smt* greps it).

**The self-hosted toolchain** has no `smt`: the request is the Lean host's.

## 28b: `sat_decide`: certified, with LRAT

    import SatTactic
    def demorgan (a b : Bool) : Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) := by sat_decide

`#print axioms demorgan`: none. The pieces (lib/Sat.wiz, lib/SatTactic.wiz):

* **An LRAT checker**, `Sat.lratCheck cnf proof`, with literals `Sat.Lit.mk v pos`, a
  clause database as an association list and RUP along the hints (deletions are accepted
  and ignored), and its **soundness theorem**
  `Sat.lratCheck_sound : lratCheck cnf proof = .true → ∀ τ, Cnf.eval τ cnf = .true → False`
  (invariant: an assignment that satisfies the database satisfies each added clause).
* **Formulas and the Tseitin translation**: `Sat.BForm` (variables, constants, `not and
  or xor iff`) and a circuit of nodes `mk id t a b`, one per distinct subformula. A node's
  variable stands for its subformula, so the satisfying assignment in the proof is just
  "evaluate it" (no fresh-name bookkeeping): `Sat.decide_sound : IsTrue (checkAll f nodes
  out proof) → ∀ σ, BForm.eval σ f = .true`, where `checkAll` checks the nodes' ids and
  runs the LRAT checker on the circuit's clauses plus the negated output.
* **The tactic** introduces the goal's `∀`s, reads `e = .true` or `e₁ = e₂` at `Bool`
  (`TacticM.eqView`: equations are opaque to `Expr`), reflects `e` (other Bool subterms
  are atoms, `σ := Sat.envOf [t₀, …]`), builds the circuit, asks the SAT solver
  (`TacticM.satSolve`: DIMACS out, LRAT back; `--sat-solver CMD`, default `cadical`, and
  `--solver-timeout MS`; flags only, so a grail file can't name a program to run;
  answers are kept in `<cache>/smt`, crashes and timeouts not) and
  closes the goal with `Sat.decide_sound f nodes out proof Sat.trivial σ`. The kernel
  checks `Sat.trivial : IsTrue .true` against `IsTrue (checkAll …)` by running the checker,
  and `BForm.eval σ f = .true` against the goal by conversion. A model is shown as a
  counterexample.

**The solver.** Release tarballs ship CaDiCaL in `share/wiz/cc/bin/cadical` (the Lean
toolchain's copy, which Lean ships for `bv_decide`; scripts/bundle-cc.sh), and a bundled
toolchain uses it by default. A checkout finds `cadical` on PATH (the Nix dev shell has
it). Z3 is not shipped (tens of MB, and `smt` is opt-in): `--smt-solver` finds it.

**Trusted**: nothing new. The solver, the tactic, the DIMACS/LRAT plumbing can only make
`sat_decide` fail. The kernel runs the checker, which is slow for big proofs (kernel
evaluation); 28e runs the same check compiled, for a trust extension.

**Limits of the prototype.** Reflection follows the goal as a tree, so a circuit with
fan-out written as nested calls (`maj` uses the carry twice) grows exponentially once
unfolded: an 8-bit carry chain checks, a 16-bit one goes over 2 GB. The fix is to reflect
shared subterms (`let`s, or a circuit given as nodes, as the HDL builds them) as one node
each. A stuck `a && b` is a `match`, not `Bool.and`, so it is an atom (write `Bool.and`).

**Not yet** (at 28b): bit vectors; 28d bit-blasts them, with the lemmas 28b expected.

## 28c: sharing

    def maj (a b c : Bool) : Bool := Bool.or (Bool.or (Bool.and a b) (Bool.and a c)) (Bool.and b c)
    def eq4 … : Bool.xor (Bool.xor a3 b3) (carry a2 b2 (carry a1 b1 …)) = Bool.xor … (maj b2 a2 (maj …)) := by sat_decide

28b's formulas are trees: `maj` uses its last argument twice, so a carry chain unfolded is
exponential (a 16-bit one went over 2 GB). Now the goal becomes a **circuit of nodes**
(`Sat.GNode`: a node number and a gate over other nodes), one per distinct subterm, and
**a node's value is the goal's own subterm**: `σ v` is that subterm, so no formula is
ever rebuilt. What the circuit claims is checked by the kernel, node by node:
`Sat.allHold σ nodes` is the conjunction of `σ v = op (σ a) (σ b)`, each proved by `refl`
at the subterm (`Sat.eqRefl`), which the kernel compares with its operands *folded* (both
sides are the same subterms). Then `Sat.dag_sound`: an LRAT refutation of the gates'
clauses and `¬ σ out` gives `σ out = .true`, with no Tseitin bookkeeping at all (the
clauses hold under `σ` itself). No axioms.

* **Head-only unfolding.** An application of a definition (`maj x y z`) is unfolded at
  its head only: the definition applied to variables is unfolded (`TacticM.unfold` under
  `fun`s) and the arguments put back (`TacticM.instantiate`), so they stay folded, and are
  nodes already. A definition that does not unfold to a connective is an input.
* **`TacticM.define`** (a new request): a definition in the goal's context, added before
  the definition being elaborated and checked by the kernel like any other (it is not an
  axiom: `#print axioms` does not list it). The proof uses two, `σ` and the node list,
  instead of repeating them in every node's proof.
* **`TacticM.assignLate`** (a new request): `assign` without the kernel's check of the
  term at that moment. `assign` type-checks the term with the kernel and the declaration
  is checked again at the end, so a big proof cost twice (on an 8-bit carry chain: 13 s
  in `assign`, 14 s at the end); `sat_decide`'s proof is only checked at the end. An
  ill-typed term is still refused, at the declaration.
* **Where the time goes** (probes, not measurements): of the remaining check, about half
  is the gates (`allHold`: each `refl` compared by conversion) and half the LRAT check run
  by the kernel's evaluator over association lists. Running the check compiled and then
  *stating* its result costs as much as the check (the kernel compares the stated
  certificate with the expected type, evaluating both); 28e avoids that by stating it as
  an axiom, at the price of trusting the run. Faster for `sat_decide`: a checker for the
  kernel's evaluator (arrays or maps for the clause database).

## 28d: `bv_decide`: words, bit-blasted (a fragment: bitwise, `+ -`, shifts, `<ᵤ ≤ᵤ`)

    import BvDecide
    def t (x y z : UIntN 8) : UIntN.land x (UIntN.lor y z) = UIntN.lor (UIntN.land x y) (UIntN.land x z) := by bv_decide

An equation of words `UIntN w` / `BitVec w` (`w` a numeral) becomes 28c's circuit: bit `i`
of a word expression `e` is the node whose value is `Bits.bit (UIntN.toNat e) i`, an
operation's bit is a gate over its operands' bits, and **the node's proof is the
operation's lemma** (`Bits.wland_bit x y i : bit (land x y) i = bit x i && bit y i`), which
the kernel checks like any gate. Other words are inputs; closed words (numerals) are
constants, their bits computed (`refl`). The output node is `Bits.eqUpTo (toNat lhs)
(toNat rhs) w`, and `Bits.word_ext` turns it into `lhs = rhs` (two numbers below `2^w`
with the same bits are equal; the range comes from 22l). No axioms: `#print axioms` lists
only `UIntN`'s seal and its natives, as for any use of words.

lib/BitBlast.wiz has the lemmas, all at any width: `n = 2 (half n) + odd n`, `Nat.div n 2
= half n` and `Nat.isOdd n = odd n` (through `Nat.divGo`'s fuel), the bits of
`Nat.bitwise` (so `land`, `lor`, `xor`), `land a b ≤ a` (Word's `land` keeps the smaller),
and extensionality. `Bits.bit` itself runs on the native `Nat.isOdd`/`Nat.div`, so the bits
of a numeral compute fast.

**Arithmetic.** `x + y` is a ripple-carry adder: bit `i` of the sum is `a_i ^^ b_i ^^ c_i`,
where the carry `c_i` is the node `Bits.carry i false A B` (`c_{i+1} = maj a_i b_i c_i`,
`Bits.carry_step`, by `refl` on the numeral `i`), proved by `Bits.wadd_bit` from `(x + y)
mod 2^w`'s low bits. `x - y` is `x + ~~~y + 1` (`Bits.wsub_bit`, carry in `true`, over
`2^w - 1 - y`'s bits, `Bits.compl_bit`); `-x` is `0 - x`; `~~~x` is `Bits.wnot_bit`.
Shifts by a numeral `k` move bits (`Bits.wshl_hi`/`wshr_in`) and fill with `false`
(`wshl_lo`/`wshr_out`). Each lemma's side condition `i < w` is a closed comparison of
numerals, which the kernel computes, so the tactic passes `Sat.trivial`.

**Comparisons.** A goal may also be an equation of booleans (as for `sat_decide`) that
compares words: `UIntN.lt/le` (`BitVec.ult/ule`) become a chain from the low bit up,
`Bits.ltc c A B (i+1) = (¬a_i ∧ b_i) ∨ (a_i = b_i ∧ ltc c A B i)`, and
`Bits.wlt_bits`/`wle_bits` (by induction on the width, through `n = 2 (half n) + odd n`)
say the chain is `<` (`c = false`) or `≤` (`c = true`) of numbers below `2^w`. The
comparisons become nodes first, and `sat_decide`'s reflection of the connectives finds them.

    def c (x : UIntN 8) : UIntN.lt x (UIntN.add x (UIntN.ofNat 8 1)) = Bool.not (UIntN.le (UIntN.ofNat 8 255) x) := by bv_decide

**Fragment**: `land/lor/xor/not/add/sub/neg`, `shiftLeft/shiftRight` by numerals,
`lt/le`, under their `BitVec` names too, and closed words. Not yet: `*`, `/`, `%`, signed
comparisons, shifts by a word. This is the whole claim: outside it an operation the tactic
does not know is an uninterpreted word (or, in a Boolean goal, an atom), so the goal is
proved only if it holds for every value of that word, and the counterexample shown names
that reading (it need not be a real one). A numeral shift amount `k` may be any numeral,
including `k ≥ w` (all bits `false`).

**Only Boolean goals with a word variable.** A closed *Boolean* goal is not supported: a
true one is already `True` when the tactic sees it (`rfl` closes it), and a false one's
closed `Bool` values are constructor payloads (`('true, refl (), ())`), not `Bool.true`, so
there is no equation of `Bool` to bit-blast. A closed *word* equation is fine (its
numerals are bits, computed by `refl`).

**Tests.** The group *smt* keeps the cases: bitwise goals, arithmetic and shifts at widths
1, 3 and 4 (both the `UIntN` and the `BitVec` names, and the shift boundaries `k = 0`
and `k = w`), and comparisons in Boolean goals; `#print axioms` checks that a proof rests
only on `UIntN`'s seal and its natives, never on `smt`'s axiom or a `sorry`.

**Kernel cost** (light probes, noise-level; distributivity of `&&&` over `|||`, three
words, over the time to import the libraries): 4 bits ≈ 2 s, 8 bits ≈ 10 s, 16 bits ≈ 58 s.
It grows faster than the circuit (3w inputs, ~5w gates): each kernel step costs
~0.1–1 ms (wiz-notes/smt.md §10), so wide words are slow until the evaluator is faster.
Arithmetic and comparisons add gates per bit (a carry or comparison chain), so the same
width costs more than a bitwise goal.

## 28e: `sat_decide_native`: the check run compiled, on trust

    import SatTactic
    def demorgan (a b : Bool) : Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) := by sat_decide_native

With `--trust-native`, `#print axioms demorgan` lists `[demorgan.sat3.native✝]`; without
it the tactic refuses with the 27a message ("native evaluation is not enabled … run with
`--trust-native`"). `sat_decide_native` is `sat_decide` with one difference: the premise
that the LRAT check passes.

`sat_decide` closes with `Sat.dag_sound nodes out proof Sat.trivial σ …`; `Sat.trivial :
IsTrue .true` is checked against `IsTrue (lratCheck (dagFull nodes out) proof)` by the
kernel running the checker (`SatT.solveDag`'s `h`). `sat_decide_native` instead has the
tactic add an axiom for that premise, after running the check compiled (the evaluator of
27a, `Native.decideNative`), and the command decides the axiom by running it before it is
added:

    X.satK.native✝ : Sat.IsTrue (Sat.lratCheck (Sat.dagFull nodes out) proof)

`K` numbers the declaration's side declarations: the proof's `σ` and node list are two
definitions, so the first check's axiom is normally `sat3.native✝`.

* **An axiom per check, listed by `#print axioms`.** The definition and everything that
  uses it depend on it, and `#print axioms` names it with the note about `.native✝`
  ("a closed proposition decided by running it … trusted are erasure, the interpreter and
  the native implementations listed"). The solver, the translation and the DIMACS/LRAT
  plumbing are still not trusted: they can only make the tactic fail. `lib/` never uses
  `sat_decide_native` (group *native*).
* **Stated as `IsTrue e`, not `e = .true`.** An equation type computes both sides when
  the kernel evaluates it (`wiz-notes/kernel-eval.md`, F5), so every use of the axiom
  would run the check again. `IsTrue e` is a definition too, but the use's expected type
  is the same term, so the constant rule compares its arguments, not the check. An
  axiom's type is checked as a type, not against a value, so adding it does not run the
  check either.
* **The node list is a closed definition.** The nodes are the circuit's structure (ids
  and gates); the goal's variables appear only in `σ`'s *values*. `TacticM.define` now
  defines a closed value as it is (not as a function over the goal's context), so the
  axiom's `nodes` is the same closed constant `Sat.dag_sound` is instantiated with. A
  value that does mention variables (such as `σ`) is still defined over the context.
* **The flag.** `--trust-native` (27a), only in a `def`'s body (the axiom is named after
  it), a flag and not a grail setting. The command and module cache keys include it, so
  an acceptance is never replayed for a run without it. The tactic itself is
  `SatT.run .true` (`SatT.checkProof` picks the axiom; `.false` is `sat_decide`).
* **The fragment is `sat_decide`'s.** The same reflection, circuit, sharing, solver and
  limits (28b–28c); only the check's premise differs. Parameters are fine (their values
  are in `σ`, not in the check's closed term); a false goal is still the solver's
  counterexample, and a goal that is not an equation of booleans is refused before the
  solver.

**Tests.** The group *sat* keeps the cases: refused without the flag; accepted with it,
with the axiom that `#print axioms` lists (for the definition and for a use); a 4-bit
carry chain over definitions (the same goal as 28c, with the check run compiled instead
of by the kernel); and a false goal, still the solver's counterexample.
