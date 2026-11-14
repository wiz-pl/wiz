import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (9i) A header of our own: structs by value (nested, with a string and a byte array),
an opaque pointer type with a constructor and a finalizer, and a buffer function. -/
def pointHeader : String := "#ifndef WIZ_POINT_H
#define WIZ_POINT_H
#include <stdio.h>
#include <stddef.h>
struct point { double x; double y; };
typedef struct { struct point lo; struct point hi; const char *name; unsigned char tag[4]; int flags; } box;
struct packed { unsigned a : 3; unsigned b : 5; };
static inline struct point point_add(struct point a, struct point b) { struct point r = { a.x + b.x, a.y + b.y }; return r; }
static inline double box_area(box b) { return (b.hi.x - b.lo.x) * (b.hi.y - b.lo.y); }
static inline box box_make(struct point lo, struct point hi) {
  box b; b.lo = lo; b.hi = hi; b.name = \"made in C\"; b.tag[0] = 'w'; b.tag[1] = 'i'; b.tag[2] = 'z'; b.tag[3] = '!'; b.flags = 7; return b;
}
static inline size_t box_name_len(box b) { size_t n = 0; while (b.name[n]) n++; return n + b.tag[0]; }
static inline int packed_sum(struct packed p) { return p.a + p.b; }
typedef struct counter counter;
struct counter { int n; };
static struct counter wiz_the_counter;
static inline counter *counter_new(void) { wiz_the_counter.n = 0; return &wiz_the_counter; }
static inline int counter_bump(counter *c) { return ++c->n; }
static inline void counter_free(counter *c) { printf(\"freed at %d\\n\", c->n); fflush(stdout); }
static inline size_t sum_bytes(const void *buf, size_t n) { const unsigned char *p = buf; size_t s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
#endif
"

/-- Write `pointHeader` to a fresh directory; its absolute path. -/
def writePointHeader : IO String := do
  let dir ← IO.FS.createTempDir
  let h := dir / "wiz_point.h"
  IO.FS.writeFile h pointHeader
  pure h.toString

/-- The errors of a program that imports headers (preprocessed like `ioRun` does). -/
def ffiErrors (src : String) : IO (Array String) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else none
  let headers ← Build.preprocessHeaders (← toolchain) src
  let s := runFrontend (R := ZeroOneMany) src { loader, cHeaders := (headers[·]?) }
  pure ((s.messages.filter (·.severity == .error)).map fun m => m.render src)

def divSrc : String :=
  "import IO\nc_struct \"div_t\" (header := \"stdlib.h\") DivT where\n  quot : Nat\n  rem : Nat\n" ++
  "extern \"div\" (header := \"stdlib.h\") cdiv : Nat → Nat → DivT\n" ++
  "def main : IO Unit := do\n  let d := cdiv 17 5;\n  IO.println (Nat.toString d.quot);\n  IO.println (Nat.toString d.rem)"

def ffiStructGroup : Group where
  name := "ffi-structs"
  exercise := "Stage 9i"
  cases := [
    { name := "a C struct by value: div_t from div()", run := fun _ => ioRun divSrc "3\n2\n" },
    { name := "a C struct by value, LLVM backend", run := fun _ => ioRun divSrc "3\n2\n" (llvm := true) },
    { name := "a struct argument: inet_ntoa (struct in_addr)", run := fun _ =>
        ioRun ("import IO\nc_struct \"struct in_addr\" (header := \"arpa/inet.h\") InAddr where\n  s_addr : Nat\n" ++
          "extern \"inet_ntoa\" (header := \"arpa/inet.h\") ntoa : InAddr → String\n" ++
          "def main : IO Unit := IO.println (ntoa (InAddr.mk 16777343))") "127.0.0.1\n" },
    { name := "struct timespec from clock_gettime, through glue", run := fun _ =>
        ioRun ("import IO\nimport_c \"time.h\"\nc_struct \"struct timespec\" (header := \"time.h\") Timespec where\n  tv_sec : Nat\n  tv_nsec : Nat\n" ++
          "glue monotonic : IO Timespec := \"struct timespec t; clock_gettime(1, &t); return t;\"\n" ++
          "def showB : Bool → String\n  | .true => \"true\"\n  | .false => \"false\"\nglue later (t : Timespec) : Timespec := \"t.tv_sec = t.tv_sec + 1; return t;\"\n" ++
          "def main : IO Unit := do\n  t ← monotonic;\n  let u := later t;\n" ++
          "  IO.println (showB (Nat.lt t.tv_nsec 1000000000));\n" ++
          "  IO.println (Nat.toString (u.tv_sec - t.tv_sec))") "true\n1\n" },
    { name := "a struct defined in Wiz (generated C definition)", run := fun _ =>
        ioRun ("import IO\nc_struct \"struct pair\" Pair where\n  a : Nat\n  b : Float64\n  ok : Bool\n" ++
          "def showB : Bool → String\n  | .true => \"true\"\n  | .false => \"false\"\nglue bump (p : Pair) : Pair := \"p.a = p.a + 1; p.b = p.b * 2; p.ok = !p.ok; return p;\"\n" ++
          "def main : IO Unit := do\n  let p := bump (Pair.mk 41 (Float64.ofNat 3) .false);\n" ++
          "  IO.println (Nat.toString p.a);\n  IO.println (Float64.toString p.b);\n" ++
          "  IO.println (showB p.ok)") "42\n6\ntrue\n" },
    { name := "import_c binds functions on structs: div, ldiv", run := fun _ =>
        ioRun ("import IO\nimport_c \"stdlib.h\" (pure)\n" ++
          "def main : IO Unit := do\n  let d := C.div 100 7;\n  IO.println (Nat.toString d.quot);\n" ++
          "  IO.println (Nat.toString (C.ldiv 100 7).rem)") "14\n2\n" },
    { name := "a header's structs: nested, strings, byte arrays, pointers, buffers", run := fun _ => do
        let h ← writePointHeader
        ioRun (s!"import IO\nimport_c \"{h}\"\n" ++
          "def pt (x y : Nat) : C.struct_point := C.struct_point.mk (Float64.ofNat x) (Float64.ofNat y)\n" ++
          "def main : IO Unit := do\n  p ← C.point_add (pt 1 2) (pt 10 20);\n" ++
          "  IO.println (Float64.toString p.x);\n  IO.println (Float64.toString p.y);\n" ++
          "  b ← C.box_make (pt 0 0) (pt 3 4);\n  a ← C.box_area b;\n  IO.println (Float64.toString a);\n" ++
          "  IO.println b.name;\n  IO.println (Bytes.toString b.tag);\n  IO.println (Nat.toString b.flags);\n" ++
          "  n ← C.box_name_len (C.box.mk (pt 0 0) (pt 1 1) \"four\" (Bytes.ofString \"A\") 0);\n  IO.println (Nat.toString n);\n" ++
          "  c ← C.counter_new;\n  k ← C.counter_bump c;\n  k ← C.counter_bump c;\n  IO.println (Nat.toString k);\n" ++
          "  s ← C.sum_bytes (Bytes.ofString \"AB\");\n  IO.println (Nat.toString s)")
          "11\n22\n12\nmade in C\nwiz!\n7\n69\n2\n131\n" },
    { name := "foreign_type (c := …) takes over a header's pointer type, with a finalizer", run := fun _ => do
        let h ← writePointHeader
        ioRun (s!"import IO\nforeign_type Counter (finalizer := \"counter_free\") (c := \"counter\")\nimport_c \"{h}\"\n" ++
          "def main : IO Unit := do\n  c ← C.counter_new;\n  k ← C.counter_bump c;\n  k ← C.counter_bump c;\n  k ← C.counter_bump c;\n" ++
          "  IO.println (Nat.toString k)") "freed at 3\n3\n" },
    { name := "c_struct takes over a header's struct (only the fields it names)", run := fun _ => do
        let h ← writePointHeader
        ioRun (s!"import IO\nc_struct \"box\" (header := \"{h}\") Box where\n  name : String\n  flags : Nat\nimport_c \"{h}\"\n" ++
          "def main : IO Unit := do\n  b ← C.box_make (C.struct_point.mk (Float64.ofNat 0) (Float64.ofNat 0)) (C.struct_point.mk (Float64.ofNat 1) (Float64.ofNat 1));\n" ++
          "  IO.println b.name;\n  IO.println (Nat.toString b.flags)") "made in C\n7\n" },
    { name := "opt-outs: no_auto and skip", run := fun _ => do
        let h ← writePointHeader
        let errs ← ffiErrors s!"import IO\nimport_c \"{h}\" (no_auto)\n#check C.point_add"
        check (errs.size == 1) s!"{errs}"
        let errs ← ffiErrors s!"import IO\nimport_c \"{h}\" (skip := \"counter box_area\")\n#check C.counter_new\n#check C.box_area\n#check C.point_add"
        check (errs.size == 2) s!"{errs}"
        -- a struct with bit fields isn't mapped
        let errs ← ffiErrors s!"import IO\nimport_c \"{h}\"\n#check C.packed_sum"
        check (errs.size == 1) s!"{errs}" },
    { name := "glue: struct addresses only for struct pointer parameters", run := fun _ => do
        let errs ← ffiErrors ("import IO\nimport_c \"time.h\"\nc_struct \"struct timespec\" (header := \"time.h\") Timespec where\n  tv_sec : Nat\n  tv_nsec : Nat\n" ++
          "glue bad (n : Nat) : Nat := \"return clock_gettime(1, &n);\"")
        check (errs.size == 1 && (errs[0]!.splitOn "struct variable").length > 1) s!"{errs}"
        let errs ← ffiErrors ("import IO\nimport_c \"string.h\"\nc_struct \"struct timespec\" (header := \"time.h\") Timespec where\n  tv_sec : Nat\n  tv_nsec : Nat\n" ++
          "glue bad (n : Nat) : Nat := \"struct timespec t; return strlen(&t);\"")
        check (errs.size == 1 && (errs[0]!.splitOn "address").length > 1) s!"{errs}"
        let errs ← ffiErrors ("import IO\nc_struct \"struct named\" Named where\n  s : String\n" ++
          "glue bad (n : Nat) : Named := \"struct named t; return t;\"")
        check (errs.size == 1 && (errs[0]!.splitOn "initialised").length > 1) s!"{errs}" },
    { name := "c_struct fields are checked", run := fun _ =>
        ioFails "import IO\nc_struct Bad where\n  f : Nat → Nat" "c_struct field f" },
    { name := "the C subset parser reads struct definitions", run := fun _ => do
        let (_, sts) := FFI.parseHeaderFull "struct a { int x; double y[3]; char n[8]; };\ntypedef struct { struct a in; const char *s; } b_t;\ntypedef struct a a_t;\nstruct c { unsigned f : 1; };\nstruct d;"
        checkEq "[struct a, b_t, struct c]" (toString (sts.toList.map (·.spelling)))
        checkEq "[a_t]" (toString (sts[0]!.aliases))
        checkEq "true" (toString (sts[2]!.fields.isNone))
        checkEq "true" (toString ((sts[0]!.fields.getD []).map (·.2) == [.int "int", .array (.float "double") (some 3), .array (.int "char") (some 8)])) }
  ]

builtin_initialize registerGroup ffiStructGroup

end Tests.Elab
