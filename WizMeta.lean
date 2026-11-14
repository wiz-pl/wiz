import WizMeta.Level
import WizMeta.Syntax
import WizMeta.Templates
import WizMeta.Reducts
import WizMeta.Spec.Fragments
import WizMeta.Spec.Laws
import WizMeta.Spec.Weakening
import WizMeta.Spec.Substitution
import WizMeta.Spec.DescCommute
import WizMeta.Spec.SubstitutionProg
import WizMeta.Spec.LevelSubstitution
import WizMeta.Checker
import WizMeta.Translate

/-!
# WizMeta: a declarative spec of the Wiz core theory, and a reference checker

Milestone M1c of the metatheory plan. Design, the differences from the kernels, and
what is not done: `/workspace/wiz-notes/wiz-meta.md`.

* `Syntax`, `Level`: the spec's own terms and levels.
* `Spec/`: the rules, one file per former; `Spec/Fragments.lean`: T0, T1, Tprog.
* `Spec/{Weakening,Substitution,SubstitutionProg,LevelSubstitution}.lean`: the first
  metatheory lemmas — renaming, substitution and level instantiation for T0, T1 and Tprog,
  and `DescEq_subst` (plan O4–O7). `Spec/DescCommute.lean` is the bookkeeping that lets the
  description formers be renamed/substituted/instantiated.
* `Reducts`, `Templates`: the terms the rules build, shared by rules and checker.
* `Checker`: the reference checker. Total; unverified.
* `Translate`: from `Wiz.Term`; fails outside the fragment.

Not a default Lake target: only `Tests/Meta.lean` imports it.
-/
