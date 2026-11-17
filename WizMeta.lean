import WizMeta.Level
import WizMeta.Syntax
import WizMeta.Templates
import WizMeta.Reducts
import WizMeta.Spec.Fragments
import WizMeta.Spec.Laws
import WizMeta.Spec.Weakening
import WizMeta.Spec.Substitution
import WizMeta.Checker
import WizMeta.Translate

/-!
# WizMeta: a declarative spec of the Wiz core theory, and a reference checker

Milestone M1c of the metatheory plan. The rules are data, and the checker is written
from them; `Tests/Meta.lean` compares it with the Lean kernel on the terms it can
translate. Two open design questions are kept as switchable rule files: Π/Σ type
equality across levels (`Spec/EqTyCross` or `Spec/EqTyLevelled`) and equality of
constructor payloads (`Spec/PayloadKernel`, `PayloadStuck`, `PayloadUniform`).

* `Syntax`, `Level`: the spec's own terms and levels.
* `Spec/`: the rules, one file per former; `Spec/Fragments.lean`: T0, T1, Tprog.
* `Reducts`, `Templates`: the terms the rules build, shared by rules and checker.
* `Checker`: the reference checker. Total; unverified.
* `Translate`: from `Wiz.Term`; fails outside the fragment.

Not a default Lake target: only `Tests/Meta.lean` imports it.
-/
