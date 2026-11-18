import Wiz

open Wiz

set_option compiler.extract_closed false

/-- Time the phases of `addDeclSorted` on the recursors of a wide inductive, after
elaborating it once (the frontend run pays everything once; each phase is then timed
again on the stored declarations). -/
def main : IO Unit := do
  let n := 500
  let src := "inductive T where\n" ++ String.join ((List.range n).map fun i => s!"  | c{i} : T\n")
  let t0 ← IO.monoMsNow
  let s : CommandState ZeroOneMany := runFrontend src
  let t1 ← IO.monoMsNow
  IO.println s!"frontend: {t1 - t0} ms, {s.globals.decls.size} decls"
  let g := s.globals
  for (dn, d) in g.decls.toList do
    if dn.startsWith "T." then
      let full := d.type.hasHole || d.value.any (·.hasHole) ||
        d.impl.any (·.hasHole) || d.witness.any (·.hasHole)
      let a0 ← IO.monoMsNow
      let _ ← pure (Decl.withTopMarks g d)
      let a1 ← IO.monoMsNow
      let b0 ← IO.monoMsNow
      let ctx : Ctx ZeroOneMany := { globals := g }
      let _ ← pure (ctx.eval d.type)
      let b1 ← IO.monoMsNow
      let c0 ← IO.monoMsNow
      let r := addDecl g { d with name := dn ++ "✝probe" }
      let c1 ← IO.monoMsNow
      IO.println s!"{dn}: holes={full} withTopMarks={a1 - a0}ms evalType={b1 - b0}ms kernel={c1 - c0}ms ok={r.isOk}"
