import Init.Data.String.Search
import Init.Data.Nat.ToString

/-!
# Decimal numerals and `Nat`

The two conversions between a decimal digit string and a `Nat`, with the cost of the
multiplications or divisions they do rather than one bignum operation per digit.

* `ofDecimalDigits?` reads a numeral. `String.toNat?` folds `n * 10 + d` over the
  digits and copies the whole (GMP) bignum each time, so an `n`-digit numeral costs
  `O(n²)`; 1 MiB of digits took minutes in `wiz check`. Here the digits are grouped
  into base-10^9 limbs (linear) and the limbs are combined as a balanced tree, which
  costs the multiplications of a product tree.
* `decimalString` prints one. `Nat.toString` (Lean core) divides by 10 once per digit
  and appends, so it is quadratic too; the cache serialises every `natLit` with it.
  Here the number is split at `10^(9·2^j)` with one division per level, so the cost is
  that of the divisions in the tree.

Neither changes a value: a numeral is read and written as its exact decimal string, and
the cache format (decimal atoms) is unchanged. Numerals below 10^9 are a single limb and
use the core functions directly, so the common case does no extra work.
-/

namespace Wiz

namespace NatString

/-- The base of the limbs: `10^9`, which fits a machine word. -/
def limbBase : Nat := 1000000000

/-- The base-10^9 limbs of a decimal numeral, least significant first, or `none` if it
is not a natural number. Accepted like `String.toNat?`: only ASCII digits, with `_` as a
separator between digits (`1_000`); empty and all-underscore strings are not numerals. -/
def limbs (s : String) : Option (Array Nat) :=
  let rec go (cs : List Char) (limb place count : Nat) (lastDigit : Bool)
      (acc : Array Nat) : Option (Array Nat) :=
    match cs with
    | [] =>
      if !lastDigit then none
      else if count > 0 then some (acc.push limb)
      else if acc.isEmpty then none else some acc
    | c :: rest =>
      if c == '_' then
        if lastDigit then go rest limb place count false acc else none
      else if c.isDigit then
        let limb := limb + (c.toNat - '0'.toNat) * place
        if count + 1 == 9 then go rest 0 1 0 true (acc.push limb)
        else go rest limb (place * 10) (count + 1) true acc
      else none
  go s.toList.reverse 0 1 0 false #[]

/-- The value of the limbs `ls[lo:hi]` (least significant first) and `10^(9*(hi-lo))`. -/
private partial def foldLimbs (ls : Array Nat) (lo hi : Nat) : Nat × Nat :=
  if hi ≤ lo + 1 then
    (if hi ≤ lo then 0 else ls[lo]!, limbBase)
  else
    let mid := lo + (hi - lo) / 2
    let (vlo, plo) := foldLimbs ls lo mid
    let (vhi, phi) := foldLimbs ls mid hi
    (vhi * plo + vlo, phi * plo)

/-- A decimal numeral as a `Nat`, in time near-linear in its length. -/
def ofDecimalDigits? (s : String) : Option Nat :=
  if s.utf8ByteSize ≤ 18 then s.toNat?
  else
    match limbs s with
    | some ls => some (foldLimbs ls 0 ls.size).1
    | none => none

/-- `P[i] = 10^(9·2^i)`, up to the first one above `n`. -/
private def powerTable (n : Nat) : Array Nat := Id.run do
  let mut ps := #[limbBase]
  while ps.back! ≤ n do ps := ps.push (ps.back! * ps.back!)
  return ps

/-- `9·2^j`: the number of digits of a limb group at level `j`. -/
private def width (j : Nat) : Nat := 9 * 2 ^ j

private def padLeft (w : Nat) (s : String) : String :=
  if s.length ≥ w then s else String.ofList (List.replicate (w - s.length) '0') ++ s

/-- Print `n < P[j]`: split at `P[j-1]` and pad the low half to its width. -/
private partial def go (ps : Array Nat) (j : Nat) (n : Nat) : String :=
  if j == 0 then toString n
  else if n < ps[j - 1]! then go ps (j - 1) n
  else
    let q := ps[j - 1]!
    let hi := go ps (j - 1) (n / q)
    let lo := padLeft (width (j - 1)) (go ps (j - 1) (n % q))
    hi ++ lo

/-- `n` in decimal, in time near-linear in the number of digits. -/
def decimalString (n : Nat) : String :=
  if n < limbBase then toString n
  else
    let ps := powerTable n
    go ps (ps.size - 1) n

end NatString

end Wiz
