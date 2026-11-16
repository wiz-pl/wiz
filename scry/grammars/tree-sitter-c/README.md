# tree-sitter-c `node-types.json` (named-node excerpt)

The schema generator reads this file (`scry-schema grammars/tree-sitter-c/node-types.json`).
It is the 132 **named** entries of tree-sitter-c's generated `node-types.json`, from
tree-sitter-c v0.24.2 (`b780e47fc780ddc8da13afa35a3f4ed5c157823d`), MIT licensed;
the grammar's full `src/node-types.json` (named and anonymous tokens) and its LICENSE
are in the fetched tree, `../../native/tree-sitter-c/` (a Nix out-link,
`../../native/README.md`).

Only named entries matter here: `C.Kind` is one constructor per concrete named node
kind, and the anonymous tokens in a tree (`(`, `,`, `;`, …) are reported by the shim's
kind table but have no constructor. `tests/codegen.wiz` fails if
`scry/gen/C/Schema.wiz` is not exactly this file's generated output.
