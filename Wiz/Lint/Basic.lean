/-!
# The lint registry's data vocabulary

The enums a lint rule's metadata is made of. They live in their own module so that both
the elaborator (`Wiz/Elab/Command.lean`, which records a package lint module's `lint`
commands) and the rule registry (`Wiz/Lint.lean`) can name them without an import cycle.

The stable `W` code blocks are documented in `docs/error-codes.md`: core owns
`W001`–`W499`, a package owns `W500`–`W999`.
-/

namespace Wiz
namespace Lint

/-- The stable category of a rule. The `W` block allocates codes by category:
`W1xx` correctness, `W2xx` performance, `W3xx` API/style, `W4xx` maintainability,
`W5xx` package sets. -/
inductive Category where
  | correctness
  | performance
  | api
  | maintainability
  | ecosystem
  deriving BEq, Repr, Inhabited

/-- The default severity of a rule. `off` means the rule is registered but does not
run unless a repository enables it. `hint` maps to the messages' `info` severity. -/
inductive Severity where
  | off
  | hint
  | warning
  | error
  deriving BEq, Repr, Inhabited

/-- What a rule sees: a command's declarations, or the whole module for a module-scope
rule. A source range is the primary span; the anchor is stable across a reindent (`f#2`
is the second parameter of `f`). -/
inductive Scope where
  | declaration
  | module
  | workspace
  deriving BEq, Repr, Inhabited

/-- The capability a rule declares. The registry builds exactly the declared view; a
package rule may read only the **stable** capabilities (`decl`, `spans`, `imports`,
`globals`, `messages`, `facts`). The unstable ones (`info`, `tactics`, `kernelTerm`,
`sourceText`) are refused for a package set (a core rule, or a future `abi`-pinned set,
may use them). -/
inductive Capability where
  | decl
  | spans
  | imports
  | globals
  | messages
  | facts
  | info
  | tactics
  | kernelTerm
  | sourceText
  deriving BEq, Repr, Inhabited

/-- The spelling a rule and a view use for a capability. -/
def Capability.key : Capability → String
  | .decl => "decl"
  | .spans => "spans"
  | .imports => "imports"
  | .globals => "globals"
  | .messages => "messages"
  | .facts => "facts"
  | .info => "info"
  | .tactics => "tactics"
  | .kernelTerm => "kernelTerm"
  | .sourceText => "sourceText"

def Capability.ofKey? : String → Option Capability
  | "decl" => some .decl
  | "spans" => some .spans
  | "imports" => some .imports
  | "globals" => some .globals
  | "messages" => some .messages
  | "facts" => some .facts
  | "info" => some .info
  | "tactics" => some .tactics
  | "kernelTerm" => some .kernelTerm
  | "sourceText" => some .sourceText
  | _ => none

/-- The capabilities a package rule set may declare. The unstable views are not part of
the P1 package ABI: a rule that needs `info` or the raw term asks for a toolchain
extension, not a capability the loader can honour. -/
def packageCapability : Capability → Bool
  | .decl => true
  | .spans => true
  | .imports => true
  | .globals => true
  | .messages => true
  | .facts => true
  | .info => false
  | .tactics => false
  | .kernelTerm => false
  | .sourceText => false

def Category.key : Category → String
  | .correctness => "correctness"
  | .performance => "performance"
  | .api => "api"
  | .maintainability => "maintainability"
  | .ecosystem => "ecosystem"

def Category.ofKey? : String → Option Category
  | "correctness" => some .correctness
  | "performance" => some .performance
  | "api" => some .api
  | "maintainability" => some .maintainability
  | "ecosystem" => some .ecosystem
  | _ => none

def Severity.key : Severity → String
  | .off => "off"
  | .hint => "hint"
  | .warning => "warning"
  | .error => "error"

def Severity.ofKey? : String → Option Severity
  | "off" => some .off
  | "hint" => some .hint
  | "warning" => some .warning
  | "error" => some .error
  | _ => none

def Scope.key : Scope → String
  | .declaration => "declaration"
  | .module => "module"
  | .workspace => "workspace"

def Scope.ofKey? : String → Option Scope
  | "declaration" => some .declaration
  | "module" => some .module
  | "workspace" => some .workspace
  | _ => none

end Lint
end Wiz
