import Wiz
open Wiz

def show1 (tag : String) (st : CommandState ZeroOneMany) : IO Unit := do
  let errs := st.messages.filter (·.severity == .error)
  IO.println s!"{tag}: {(errs.toList.map (·.text.take 60))}"

def main : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let loader : Name → Option String := fun m => if m == "Prelude" then some prelude else none
  let lst := (List.range 5).foldr (fun i acc => s!"(List.cons {i} {acc})") "List.nil"
  let src := s!"import Prelude\ndef L : List Nat := {lst}\ndef bad (h : L = L) : Nat := h\n"
  let order := (← IO.getEnv "ORDER").getD "le"
  for c in order.toList do
    let st := runFrontend (R := ZeroOneMany) src { loader, globals := { lazyEqs := c == 'l' } }
    show1 (toString c) st
