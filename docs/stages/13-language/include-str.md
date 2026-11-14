# `include_str`: a file's text, as a string literal

`include_str "relative/path.txt"` is a **term of type `String`** whose value is the
contents of a text file. It is the Wiz equivalent of Rust's `include_str!` and Lean's
`include_str`, without a build script:

```wiz
import Prelude

def nodeTypes : String := include_str "node-types.json"

#eval String.length nodeTypes
```

The path is a string literal: the parser produces `term.includeStr` (`include_str` and
the literal), and the driver replaces the node with an ordinary `term.str` literal
before the command is elaborated. Macros therefore stay **pure**: no macro, tactic or
elaborator step ever reads a file, and a macro that receives or produces the node still
sees a string literal.

The literal is an ordinary string (`String.mk [Char.mk n, …]`), one term node per
character: files of a few KB are fine; a multi-MB file would want a future `Str`/`Bytes`
primitive with a native literal.

## Where the file is read

The frontend (`runFrontend`, `ElabM`, `MacroM`) is pure, so file IO happens in the
drivers, which already read imports, C headers and `link_c` files:

* `wiz` (`Main.elaborate`) and grail (`Grail.Elab.load`) scan a source text with
  `Module.includesOf`, read every `include_str` file it names with `Module.includeTable`,
  and put the result in `CommandState.includes`.
* `Elab.Command.resolveIncludes` runs at the top of `elabCommand`, looks each node up by
  `(module, path as written)` and substitutes the literal (or an empty literal plus an
  error at the include). This is the one hook in elaboration.

A frontend with no include table (the language server today) reports "the file was not
read" at each `include_str`; see "Language server" below.

## Path rules

* The path is **relative to the `.wiz` file that contains the `include_str`**, never the
  current directory. Each module's own directory is used for its includes.
* Absolute paths are errors.
* `.` and `..` are normalised; a path that climbs above the including file's directory
  (`../x`) is an error, so included data must live next to the source or below it.
* A missing file, a directory, and a file that is not valid UTF-8 are errors reported at
  the path literal, with the source position (e.g.
  `2:22: error: include_str: no file nowhere.txt (paths are relative to the .wiz file)`).
* The path must be written literally in the source. A path a macro computes during term
  expansion is not in the table; the include is reported as unresolvable. (No file is
  read during macro expansion; that is the point.)

Include paths are found by a scan of the text (`Module.includesOf`), like `link_c` paths:
a mention in a comment or ordinary string is read too (harmless: an extra file in the
table), but an identifier such as `my_include_str` is not.

## Cache keys

Included content is part of the key that decides what a module or command elaborates
to, so editing an included file re-elaborates its users and a content-addressed entry
never serves stale text:

* `Module.includesKey` hashes every included file's contents (or the resolution error).
* `Cache.moduleKeys`/`moduleKey` mix it into each module's key, so importers of a module
  that includes a file are invalidated too.
* `Cache.elaborateWith` mixes the main file's includes into `key₀`; `Query.elaborate`
  (the language server's per-command memo) does the same.
* `Frontend.isoKey` (the per-process isolated-module cache) does the same, and the
  pristine-import path now carries `CommandState.includes` over from the importer: the
  cached isolated state is keyed by content, not by the resolver function.

An edit invalidates the whole including file (and its importers), not only the commands
after the include. That is coarser than the command chain could be, but deterministic
and cheap; the content hash is already computed once per run.

## Language server

`include_str` needs a resolver; without one it is an error. The LSP's `elabText` is pure
and does not know the document's URI, so wiring it up means passing the document's
directory (from the `textDocument/didOpen`/`didChange` URI) through `elabText` and
building a table in IO, cached by the file's modification time. Until then an editor
reports each include as unread; the command line is the supported path.

## Tests

`ffi` (the group that also holds `link_c`): the text is a `String` through `#eval` and
`#run`; a compiled program prints it; a module's file is relative to the module; a
missing file, a non-UTF-8 file, an absolute path and a `..` path are errors at the
include; and editing the included file invalidates the cache (the `#eval` command is
re-elaborated, the imported Prelude still hits).
