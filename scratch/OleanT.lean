def double (n : Nat) : Nat := n + n
def xs : List Nat := List.range 100
theorem double_zero : double 0 = 0 := rfl
