# Lowering-fuzz seeds

Small, hand-written C inputs that steer the generator at the Wiz side of the
front end (not at tree-sitter: `scry/fuzz/run.py` owns the shim target). They
are loaded by `scry/scripts/fuzz-lower.py` in addition to `bench/corpus`,
`tests/fixtures` and `corpus`.

| file | shape |
|---|---|
| `deep-paren.c` | nested parenthesised expression |
| `declarator.c` | pointer-declarator chain |
| `nested-control.c` | nested `while`/`if` blocks |
| `big-literal.c` | large integer literal |
| `unterminated-comment.c` | recovery tree from an unterminated comment |

The generator scales these classes from 128 to 131 072 levels and adds mutated
corpus files, random bytes, pathological sizes and small syntactically valid
programs. A seed is a starting point, not a regression test; the minimised
findings live in `scry/tests/fixtures/fuzz-regression/`.
