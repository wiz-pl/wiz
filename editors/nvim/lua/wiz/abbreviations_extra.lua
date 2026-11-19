-- Wiz's additions to Lean's abbreviation table (keys without the leader).
--
-- Lean gives most single letters a meaning (\a α, \b β, \l ←, \r →, \x ×, \t ▸, ...);
-- those stay. The nine letters Lean leaves free become Greek letters, following the
-- Greek keyboard layout where it has one. The rest are symbols the Wiz sources and
-- docs use that Lean's table has no abbreviation for.
return {
  f = 'φ',
  h = 'η',
  j = 'ξ',
  k = 'κ',
  q = 'θ',
  s = 'σ',
  w = 'ω',
  y = 'υ',
  z = 'ζ',
  ['++'] = '⧺', -- selfhost/Backend.wiz: Doc concatenation
  done = '✅', -- the docs' "done" mark
  cross = '✗', -- grail's failure mark
  cmd = '⌘', -- lib/Web/Editor.wiz: the editor hint's Command key (Ctrl/⌘+Enter runs)
  hat = '\u{0302}', -- combining circumflex: x\hat → x̂ (docs/CoreSpec.md)
  vec = '\u{20D7}', -- combining arrow above: v\vec → v⃗
}
