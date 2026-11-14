/-!
# The C runtime, as text

The runtime embedded in the compiler (`Wiz.C.program` pastes it at the top of every C
program). It is split into the ABI header `runtime/wiz_rt.h` (value representation, tags,
object layouts, and — below a marker — prototypes for embedders) and six area files,
in the order of the old `runtime/wiz.c`:

* `rt_core.inc` — leaks, allocation, reference counting, immortality, CAFs;
* `rt_num.inc` — numbers (small scalars and GMP);
* `rt_words.inc` — flat values (`pack`/`unpack`, fields, lazy cells), closures and
  application, reuse, the FFI's raw words and machine words;
* `rt_data.inc` — constructors, `String`, the C ABI, `Bytes`/`Array`/`Str`/maps/`Intern`,
  the library helpers and the proof budget;
* `rt_sys.inc` — POSIX: environment, files, processes, descriptors, output;
* `rt_con.inc` — threads, channels, `MVar`s, locks, and the entry points.

`runtime` is the header's representation part followed by the parts, in that order —
byte for byte what `wiz.c` used to be, so every generated C program is unchanged.
The header's prototypes (after the marker) are not inlined: a translation unit includes
the header instead (`scripts/test-runtime.sh`), which is also the ABI of the object mode
in `wiz-notes/runtime-in-wiz.md`.

This module is a library of its own, `WizRuntime` in `lakefile.lean`, whose `needs` names
these files as input files: Lake mixes their content hashes into this module's trace, so
editing one rebuilds this module (and its importers) and nothing else, and Lake's artifact
cache never serves a stale one.
-/

namespace Wiz.C

/-- The prototypes in `wiz_rt.h` start at this line; everything above is inlined into
the generated C. -/
def headerMarker : String := "/* ---- declarations for embedders"

/-- The header's representation part, without the prototypes. -/
def inlineHeader : String :=
  match (include_str "wiz_rt.h").splitOn headerMarker with
  | [header, _] => header
  | _ => panic! "runtime/wiz_rt.h: the 'declarations for embedders' marker is missing"

/-- The runtime, as it is pasted at the top of every generated C program: the header's
representation part, then the six area files in the old order. (Each `include_str` is
parenthesized: unparenthesized, its argument runs to the end of the expression.) -/
def runtime : String :=
  inlineHeader ++
    (include_str "rt_core.inc") ++
    (include_str "rt_num.inc") ++
    (include_str "rt_words.inc") ++
    (include_str "rt_data.inc") ++
    (include_str "rt_sys.inc") ++
    (include_str "rt_con.inc")

end Wiz.C
