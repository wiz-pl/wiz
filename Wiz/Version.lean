/-! The toolchain's version, for `wiz --version`, `grail --version` and `tower --version`.
No imports: tower uses it without depending on the rest of Wiz. -/

namespace Wiz

/-- The release this tree is, or leads up to (`-dev` until the commit that is tagged).
Keep it in step with `version` in lakefile.lean and flake.nix, and with the copy in
the self-hosted tower (`tower/Tower/Cli.wiz`, `--version`). -/
def version : String := "0.1.0-dev"

/-- The commit a release toolchain was built from: the file `REVISION` that the release
tarball and tower's installs write next to the toolchain's library
(`share/wiz/REVISION`, four directories above `share/wiz/.lake/build/bin/wiz`). None
in a checkout. -/
def revision? : IO (Option String) := do
  let exe ← IO.appPath
  let some dir := ((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)
    | return none
  let f := dir / "REVISION"
  unless ← f.pathExists do return none
  let r := (← IO.FS.readFile f).trimAscii.toString
  return if r.isEmpty then none else some r

/-- `TOOL VERSION`, with ` (COMMIT)` when the toolchain knows its commit. -/
def versionLine (tool : String) : IO String := do
  match ← revision? with
  | some r => return s!"{tool} {version} ({r})"
  | none => return s!"{tool} {version}"

end Wiz
