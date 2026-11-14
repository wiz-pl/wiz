# Stage 9: the C FFI

## 9a: IO, machine types, foreign functions

```
import IO
extern "strlen" (header := "string.h") strlen : String → Nat
def main : IO Unit := do
  IO.println "hello from Wiz";
  IO.println (Nat.toString (strlen "hello"))
```

* `lib/IO.wiz`: `IO A := (1 w : World) → A × World`. The world is a **linear token**:
  QTT's usage checking makes sure every action takes it and gives it back exactly
  once, so effects are ordered and nothing else is impure. (`let 1 (a, w') := …`
  splits linearly; `match` can't, because `ind` uses its methods ω times, and the
  projections `.1`/`.2` can't either: they need an unrestricted pair, see 9e.) `Monad IO`
  makes `do` work.
* `extern "cname" (header := "h.h")? name : T` declares an axiom implemented by a C
  function. Marshalling follows `T`: `Nat` and `UInt64` ↔ `uint64_t`, `Float64` ↔
  `double`, `String` ↔ UTF-8 `char*`, `Bool` ↔ `int`, `Unit` ↔ `void`; a result in `IO`
  takes and returns the world. The backends emit a C wrapper per foreign function.
  A foreign function outside `IO` must be pure (no observable effect): compiled code may
  drop or duplicate such a call. Its result must have runtime content: `Unit`, a
  proposition, a type, or an erased function into those (after unfolding) is refused.
  An effect belongs in `IO` (`… → IO Unit`). (4h; CoreSpec §10.2a.)
  A foreign function outside `IO` must be pure (no observable effect): compiled code may
  drop or duplicate such a call. Its result must have runtime content: `Unit`, a
  proposition, a type or an erased function into those (after unfolding) is refused;
  an effect belongs in `IO` (`… → IO Unit`). (4h; CoreSpec §10.2a.)
  Without a header, a prototype is generated from the Wiz type.
* `UInt64` and `Float64` are axioms whose operations are runtime functions, bound
  with `extern` (boxed raw words at runtime). The kernel doesn't compute with them.
* `wiz run` on `main : IO A` runs it. Foreign functions only run in compiled code
  (`#eval`/`#run` report them).

## 9b: importing C headers

```
import IO
import_c "string.h"            -- C.strlen : String → IO Nat, …
import_c "math.h" (pure)       -- C.pow : Float64 → Float64 → Float64, …
```

`import_c "h"` binds every function of a header whose types can be marshalled, as
`C.name`, in `IO` unless the import is marked `pure`. The command line tool (and the
tests) run the header through `cc -E -P` first, since the frontend is pure. A parser
for a small C subset (`FFI/CParse.lean`) reads the prototypes and the typedefs they
use, and skips struct bodies, inline function bodies and GNU extensions. Variadic
functions and functions taking pointers other than `char*` (or function pointers,
or structs by value) are skipped. On glibc, `string.h` gives 66 prototypes and
`math.h` gives 620.

| #   | Where              | What                                              |
|-----|--------------------|---------------------------------------------------|
| 9.1 | `FFI/CParse.lean`  | `declarator`: pointers, names, parameter lists    |

## 9c: checked C glue

```
import_c "string.h"
glue sumTo (n : Nat) : Nat := "uint64_t s = 0; for (uint64_t i = 0; i < n; i++) s += i; return s;"
glue twiceLen (s : String) : Nat := "return strlen(s) * 2;"
```

A `glue` function's body is C, in a **checked subset** (`FFI/CGlue.lean`): scalar
locals, assignments, `if`/`while`/`for`/`return`, arithmetic and logic on integers and
doubles, strings passed around, and calls to functions from imported headers (with
their types checked). Pointer dereference, address-of, casts, indexing, member access,
`goto`, `asm` and `sizeof` are rejected, so glue can't corrupt memory by itself. The
checked code is emitted into the program, with its headers, and bound like an
`extern`.

| #   | Where              | What                                     |
|-----|--------------------|------------------------------------------|
| 9.2 | `FFI/CGlue.lean`   | `expr`: types of glue expressions        |

## 9d: foreign pointers, finalizers, buffers

```
foreign_type FILE (finalizer := "fclose")
extern "fopen" (header := "stdio.h") fopen : String → String → IO FILE
extern "fputs" (header := "stdio.h") fputs : String → FILE → IO Nat
```

* `foreign_type T (finalizer := "f")` declares an opaque type of C pointers. A pointer
  returned by a foreign function is wrapped in a reference-counted object, and `f` runs
  when the last reference goes. An argument is borrowed during the call and released
  after it. Glue code can pass foreign pointers on but not look inside them.
* `Bytes` (in `lib/IO.wiz`) is a byte buffer whose `push` updates in place when the
  buffer is unique (the same idea as Perceus reuse). It has `IO.readFile` for input.
  Runtime helpers like these take Wiz values as they are (the `w` marshalling kind).

Later sections: callbacks and exported functions (C calling Wiz) are 9g; structs by
value and more of a header's pointer types are 9i.

## 9e: linear sequencing

```
axiom Tok : Type
axiom Tok.close : (1 t : Tok) → IO Unit
def finish (1 t : Tok) : IO Nat := do1
  IO.println "closing";
  Tok.close t;
  IO.pure 3
```

* `IO.bind` takes its action and its continuation **at quantity 1** (both are used
  once), so an action that consumes a linear value can be sequenced, and the
  continuation may capture one. Unrestricted arguments pass as before. `IO.then1 x y`
  runs `x`, drops its result, then `y`.
* `class Monad1 m` has `bind1 : (1 x : m A) → (1 f : A → m B) → m B`, and **`do1`** is
  `do` notation over it (`x ← e;`, `e;`, `let x := e;`). `do` stays on `Monad.bind`,
  whose continuation is unrestricted: the same block written with `do` is rejected
  when a later step uses a linear variable. Bound results are unrestricted in both.
* **An action's result is split, never projected.** `x w : A × World` holds the next
  world as its second component, so it is taken apart with `let 1 (a, w') := x w; …`
  (as `IO.bind` and `IO.then1` do). `(x w).1` would run the action and drop the world
  it returns; the kernel rejects it, because a projection uses its pair, here the
  expression `x w` and so `w`, ω times (stage 4b; CoreSpec §7.1, R1). The same goes for
  every function that hands a resource back in a pair (`B × Uniq ρ S` in
  `lib/Region.wiz`): a caller holding the pair linearly must split it.
  ```
  def peek {A : Type} (1 x : IO A) (1 w : World) : A := (x w).1
  -- error: cannot project (x w).1: a projection needs an unrestricted pair …,
  -- but this one uses w, which has quantity 1; take the pair apart with
  -- `let 1 (x, y) := x w; …` instead
  ```
* Transport for linear values: `Eq.cast (0 e : A = B) (1 a : A) : B`, `Eq.subst P e`
  and `Eq.substBack P e` take the transported value at 1 (the kernel's `cast` already
  passes its argument's usage through), e.g. `Chan (dual (dual p))` to `Chan p` given
  a proof (Prelude; plan L4).

## 9f: C source files and libraries

```
link_c "term.c"                       -- relative to this .wiz file
link_lib "m"                          -- -lm
extern "iv_term_open" Term.open : IO Nat
```

* `link_c "f.c"` names a C file to compile and link with any program that imports the
  module (or is the file). The path is relative to the `.wiz` file that says it (a
  module's to the module's file), or absolute. It is the **unchecked** counterpart of
  `glue`: the file may use pointers, structs, system headers and static helpers; Wiz
  sees only the functions it binds with `extern`. A file named twice is linked once.
* `link_lib "m"` links a library (`-lm`), after the toolchain's `--libs`.
* `wiz build`/`wiz run` compile the files with the program, with the same compiler and
  `--cflags` (`-O2 -w`, like the generated C), through either backend (with `--llvm` the
  linking step compiles them). The frontend is pure, so the command line resolves the
  paths first (`Module.cSourceTable`, like the headers of `import_c`); a file that
  doesn't exist is an error at its `link_c`. The commands aren't cached (they rerun on
  every elaboration; they are cheap), so a file deleted later is still noticed. In the
  language server the paths aren't checked.
* grail (stage 23): `c F` lists the files and libraries in `link.txt` beside `main.c`;
  `link E` compiles and links them, and its key covers their paths, their contents and
  the `cflags`, so editing a C file reruns only the link (and the `run` tests that use
  the program). Which of the files exist enters `check F`'s key, so a deleted file is
  reported by the check.
* `--gmp "…"` (a toolchain field, default `-lgmp`; also `gmp` in `grail.local.wiz`) says
  how GMP is linked. For WebAssembly it is mini-gmp's C file, so `web/build.sh` is one
  `wiz --cc emcc --gmp ".../mini-gmp.c" build web/Web.wiz -o wiz-infoview.mjs`, with
  `web/js.c` (Emscripten's `EM_JS`) from `link_c "js.c"`. The terminal infoview links
  `infoview/term.c` (termios, poll, sockets) the same way.

Not done: `pkg-config` names (`link_pkg "gtk+-3.0"`) — for now, give their flags with
`--cflags`/`--ldflags`.

## 9g: callbacks and exported functions

```
import IO
-- C calls Wiz: a symbol for a definition
def greet (who : String) : String := String.append "hello, " who
export "wiz_greet" greet                  -- char *wiz_greet(const char *)

-- a Wiz closure passed to C: a function pointer and a context
extern "sort_some" sortSome : (Nat → Nat → Bool) → String
--   const char *sort_some(int (*lt)(void *, uint64_t, uint64_t), void *ctx)
extern "on_tick" onTick : Callback (Nat → IO Unit) → IO Unit
--   void on_tick(void (*f)(void *, uint64_t), void *ctx)   -- keeps ctx; wiz_release(ctx)
```

* `export "c_name" f (: T)?` gives a closed definition a C symbol. The wrapper is the
  reverse of an `extern`'s: C values come in (`Nat`/`UInt64` from `uint64_t`, `Float64`
  from `double`, `String` from a `const char *` that Wiz copies, `Bool` from `int`, a
  foreign pointer lent without a finalizer, a Wiz data type as a `wiz_val`), the
  closure is applied, and the result goes out (a `String` as a `malloc`ed `char *` the
  caller `free`s; `Unit` as `void`). A result in `IO` is run: the wrapper passes the
  world (a scalar) and drops it after. The optional type must be the definition's.
  Universe-polymorphic definitions and erased parameters can't be exported, nor
  functions taking functions.
* **Handles.** A Wiz value of a data type crosses as `wiz_val` (a word), and the C
  side **owns** the reference it gets: passing it back to an export hands that
  reference over (so `s = step(s, ev)` threads a state), `wiz_retain(v)` makes another
  one first (to keep `v` across a call), and `wiz_release(v)` gives one back. The
  runtime's `wiz_live_objects()` counts live objects, for leak checks in C tests.
* **Callbacks.** A foreign function's parameter of function type becomes two C
  arguments: a function pointer whose first parameter is the context, then the
  context (`void *`, the closure). The function is a *trampoline* generated per
  signature (`wiz_cb_nn_b` for `Nat → Nat → Bool`), which marshals like an export and
  applies the closure. Ownership: a plain `A → B` parameter is **borrowed** for the
  call (the wrapper drops the closure when the C function returns, so C must not keep
  it); `Callback (A → B)` (`lib/IO.wiz`, a transparent definition) hands C a
  reference, kept alive until C calls `wiz_release(ctx)` (a stored callback C never
  releases shows up in the leak check at exit). A callback whose result is in `IO`
  may run effects; the foreign function taking it must be in `IO` too, so they happen
  during that call, in order.
* `wiz build FILE -o OUT.o --lib [--llvm]` compiles the exports (no `main`) to an object
  file with the runtime, and writes `OUT.h` with their prototypes and the handle
  functions; a C program links it with `-lgmp` (and with the file's `link_c` sources
  and `link_lib` libraries, 9f, which an object file doesn't carry).
  `wiz build FILE -o OUT --no-main` links the exports like a program, `link_c` files
  included, but without a `main`: what that makes is the toolchain's business (with
  `--cc emcc --ldflags "--no-entry …"`, a Wasm module). A program with a `main` exports its
  functions too (C code linked with it, here through `--libs`, can call them).
  Exported functions run on the caller's thread and stack (not `main`'s big stack);
  a handle is used from the thread that got it (only 25a's shared objects cross
  threads), and `wiz_live_objects()` counts the calling thread's objects.
* The keys: an export is `export:cname:kinds:result:io` in the builtins (cached with
  them); a callback parameter is `k[<params>/<result>]` (`K` for `Callback`, `!` before
  a result in `IO`) in an `extern:` key (`RVal.ExternSig`). An export's code is an IR
  function `wiz.export.<cname>` giving `f`'s closure (so borrowed parameters and owned
  wrappers stay the compiler's business), which the C wrapper applies with `wiz_apply`;
  for LLVM it is not `internal`, and the wrappers are C compiled with the runtime.
* **The web infoview** (`web/Web.wiz`, 11n) is now a library: it exports
  `wiz_web_init : WSt` and `wiz_web_step : WSt → String → IO WSt` (State → Event →
  State, the actions — messages to the server, HTML for the page — done through the
  `js_send`/`js_set_html` imports during the step). `web/infoview.js` keeps the state
  and calls the step on every event, so there is no Wasm main loop waiting in
  `js_next_event` and the build (`wiz --cc emcc … build web/Web.wiz --no-main`, with
  `web/js.c` by `link_c`) no longer needs Asyncify.

Known limits: a project built by grail doesn't get its export wrappers yet (only
`wiz build` and `wiz run` emit them); a callback's or an export's signature can't
contain a `c_struct` (9i) or another callback. The self-hosted compiler has exports,
callbacks, libraries and the handle functions too (stages 21o, 21q, 21s).

Tests: `callbacks` (qsort with Wiz comparators, a closure kept by C and called later
in `IO`, the leak when it isn't released, C calling an export from a program, a C
program linked with a `--lib` build, both backends), `web/test.sh`.

## 9h: system interfaces: processes, environment, files

```
import Sys
def main : IO Unit := EIO.toIO (do
  o ← Process.output "cat" .nil "piped through cat\n";
  EIO.lift (IO.print o.stdout);
  Env.set "GREETING" "hi";
  d ← FS.createTempDir;
  FS.writeFile (Path.join d "a.txt") "alpha\n";
  names ← FS.listDir d;
  FS.removeAll d)
```

`lib/Sys.wiz` binds the POSIX interfaces a program needs to drive other programs
(what the toolchain manager and grail need, see stages 23 and 26), with C in the
runtime's section "system interfaces" (`runtime/`, so both backends have it).

* **Errors.** Anything that can fail returns `EIO A := IO (Except String A)`, a monad of
  its own, so a `do` block stops at the first error; `EIO.lift` runs an `IO` action in
  it and `EIO.toIO` runs it as `main`, printing the error to stderr and exiting with 1.
  An error reads `"<path or call>: <strerror(errno)>"`. Underneath there are two
  shapes of foreign function: a call that only succeeds or fails returns the errno
  (0 for success, `Sys.lift`), and a call that returns a value records its errno per
  thread, read back by `Sys.errno` right after it (`Sys.check`; the linear world
  token keeps the two calls together and in order). Results that are lists (directory
  entries, the environment, a `stat`) are built by the runtime as Wiz lists.
* **Environment.** `Env.get : String → IO (Option String)`, `Env.set`, `Env.unset`,
  `Env.list : IO (List (String × String))` (sorted by name). Setting variables isn't
  thread-safe in C: set them before starting threads.
* **Files and directories** (`FS.`). `currentDir`, `setCurrentDir`, `createDir`,
  `removeDir`, `removeFile`, `removeAll` (recursive, doesn't follow links), `rename`,
  `symlink target link`, `readLink`, `setMode`, `listDir` (sorted, without `.` and
  `..`), `stat` and `linkStat` (a `FileStat`: kind, size, modification time, mode),
  `exists`, `isDir`, `isFile`, `tempRoot` (`$TMPDIR` or `/tmp`), `createTempDir`
  (`mkdtemp`), and whole files: `readFile`, `writeFile`, `appendFile`, and `readBytes`,
  `writeBytes` for binary data (text stops at a NUL byte). `Path.join` puts a `/`
  between two paths.
* **File handles.** `foreign_type File` (closed by its finalizer, or `File.close`):
  `File.open path mode` (`fopen` modes), `File.stdin`/`stdout`/`stderr`,
  `readLine` (`none` at the end), `readAll`, `write`, `flush`. `IO.ePrintln` prints
  to stderr.
* **Processes.** `Process.spawn cmd args stdin stdout stderr` starts `cmd` (searched in
  `PATH`, `posix_spawnp`) with each stream `.inherit`, `.piped` or `.null`, giving a
  `Child` (a foreign type: its pipes close and a finished child is reaped when it
  goes). `Child.write`, `closeStdin`, `readStdout`/`readStderr` (to the end),
  `communicate input` (writes stdin while collecting stdout and stderr with `poll`, so
  a child that fills one pipe doesn't deadlock), `wait` (an `ExitStatus`: `exited code`
  or `signaled n`), `kill`, `pid`. `Process.output cmd args input` runs a command to the
  end and returns its status and output; `Process.run` runs one with this program's
  streams; `Process.exec` replaces the program; `Process.exit`, `Process.id`. The
  runtime ignores `SIGPIPE` once a child has been started (a write to a closed pipe is
  then an `EPIPE` error), and the pipes are close-on-exec, so other children don't keep
  them open.
* `#eval` and `#run` can't do any of this (they are pure and can't call C): there are
  no models for system calls, since a model of the file system or of processes would
  give answers the real program wouldn't. The pure helpers (`Path.join`,
  `ExitStatus.ofNat`, `FS.statOf`, `Env.pairs`) run anywhere.

Tests: the `sys` group (spawning `echo`, a pipe through `cat`, exit codes and spawn
errors, the environment, a temporary directory's life: files, links, stat, listing,
removal, handles), on both backends.

Binary data on handles, descriptors with time limits, spawn options and serial ports
came later: 9k.

## 9i: C structs by value; header pointer types as foreign types

```
import IO
c_struct "div_t" (header := "stdlib.h") DivT where
  quot : Nat
  rem : Nat
extern "div" (header := "stdlib.h") cdiv : Nat → Nat → DivT

import_c "time.h"
c_struct "struct timespec" (header := "time.h") Timespec where
  tv_sec : Nat
  tv_nsec : Nat
glue monotonic : IO Timespec := "struct timespec t; clock_gettime(1, &t); return t;"

c_struct "struct pair" Pair where     -- no header: the C definition is generated
  a : Nat
  b : Float64
```

* `c_struct ["ctype"] [(header := "h")] T where fields` declares a Wiz structure `T`
  (an ordinary one: `T.mk`, `t.field`, `deriving`) that stands for the C struct `ctype`.
  Externs and glue functions take and return it **by value**. A field is `Nat`,
  `UInt64`, `Float64`, `String`, `Bool`, a foreign type, another `c_struct` (nested),
  `Bytes` for a byte array `char f[N]` (copied; cut or zero-padded to `N`), or a `0`
  field (not in C). Fields can't depend on each other.
* **With a header**, the header's definition is the layout: fields are assigned by name,
  the C compiler converts the numbers, and only the named fields are marshalled (a
  `c_struct` may name a subset; the rest are zero going in and dropped coming out).
  **Without**, the definition is generated from the fields (`uint64_t`, `double`, `int`
  for `Bool`, `const char *`, `void *`), as `struct t { … };` for a name `struct t` or a
  `typedef` otherwise (the default name is `wiz_s_T`), so C code (glue, linked sources)
  can use it.
* **Marshalling** (`C.lean`, `structHelpers`): for each struct the glue gets
  `wiz_sin_N(&c, v)` (fill `c` from the structure, which is borrowed: it is nested pairs
  with the last pair unboxed, 22i), `wiz_sfree_N` (free the strings that made) and
  `wiz_sout_N(c)` (build the structure; strings are copied, a NULL one becomes `""`; a
  pointer field coming back has no finalizer). The extern key carries the layout,
  `<ctype|header|f=k,…>`, so the wrappers need nothing else.
* **LLVM backend**: the foreign wrappers are C in both backends (the LLVM module calls
  `wiz_ext_…` on `wiz_val`s), so a by-value struct is lowered by the C compiler, which
  follows the x86-64 SysV ABI (registers or memory, by size and class). The LLVM IR never
  sees a C struct; no ABI lowering of our own.
* **Glue** may take and return structs, declare struct locals (`struct timespec t;`, or a
  typedef name; one with string or pointer fields must be initialised), read and assign
  fields (`t.tv_sec = t.tv_sec + 1;`), and take `&t` of a struct variable, but only as
  the argument of a C function whose parameter is a pointer to that struct. The checker
  knows the fields of `c_struct`s and of imported headers' structs.

**`import_c`** now also maps (unless opted out):

| C type in a prototype        | Wiz type                                          |
|------------------------------|---------------------------------------------------|
| `struct foo` / `foo_t` by value | a structure `C.struct_foo` / `C.foo_t`, made with `c_struct` from the header's definition (every field must map: numbers, `char *`, `char f[N]` → `Bytes`, nested structs); a struct with bit fields or anonymous members is left out |
| `struct foo *`, `FILE *`     | a foreign type `C.struct_foo` / `C.FILE` (no finalizer) |
| `const void *buf, size_t n`  | one `Bytes` argument (the pointer and the length come from the buffer; only when the length parameter right after is named `n`, `len`, `nbytes` or `length`, with or without `__`) |

`const char *` stays `String`; other pointers (`int *`, `void *`, output buffers) are
still skipped. The C subset parser (`FFI/CParse.lean`, `parseHeaderFull`) reads struct
bodies, array lengths, typedef names of structs and parameter names for this.

Opt-outs:

* `import_c "h" (no_auto)`: only the 9b mappings (numbers, strings).
* `import_c "h" (skip := "FILE div_t fopen")`: leave out these C types (struct spellings
  or typedef names; functions using them are skipped) and functions.
* `foreign_type File (finalizer := "fclose") (c := "FILE")`: a header's `FILE *` is this
  type, with its finalizer, instead of an automatic one.
* `c_struct "div_t" (header := "stdlib.h") DivT where …` before the import: the header's
  `div_t` is this structure (with the fields it names).

Caveats: an automatic foreign type has no finalizer, so nothing is freed for it; a C
function may keep a pointer it was given (`&t` or a foreign pointer) beyond the call,
which the checker can't see. Tests: the `ffi-structs` group (`div`, `ldiv`, `inet_ntoa`
with `struct in_addr`, `clock_gettime` with `struct timespec`, a header of our own with
nested structs, strings, byte arrays, an opaque pointer type and a buffer function, the
opt-outs, and the glue checks).

## 9k: bytes on handles, time limits, spawn options, serial ports

```
import Serial
def main : IO Unit := EIO.toIO (do
  port ← Serial.open "/dev/ttyUSB1" (SerialConfig.raw8N1 .b115200);
  Fd.write port (Bytes.range 256);                      -- every byte value, NUL included
  r ← Fd.readExactlyWithin port 2 (Duration.seconds 2);
  match r with
  | .all b => EIO.lift (IO.println (Bytes.show b))
  | .eof b => EIO.fail "the port went away"
  | .timeout b => EIO.fail "no answer in time")
```

Additions to `lib/IO.wiz` (`Bytes`) and `lib/Sys.wiz` (one block at the end; nothing
before it changed), and a new module `lib/Serial.wiz` with its C shim `lib/serial.c`
(`link_c`). Written for a host test of an FPGA board over a UART
(wiz-icestick-uart's FINDINGS.md, G13), which had to run `stty` and send only bytes
1 … 127.

* **Text and bytes.** A `String` crossing the FFI is UTF-8 and ends at the first NUL:
  `File.write`, `Child.write` and every other `String` argument write the characters'
  UTF-8 and stop at code point 0; `readLine`, `readAll` and other `String` results
  decode UTF-8 without checking (bytes that aren't UTF-8 become wrong characters, not
  an error) and stop at a NUL byte. So binary data goes as `Bytes`, and text and bytes
  meet only through a named encoding: `Bytes.ofUtf8 : String → Bytes` (every string,
  NUL included; a code point that isn't a scalar value becomes U+FFFD),
  `Bytes.toUtf8 : Bytes → Except String String` (checked: overlong forms, surrogates,
  truncated sequences are `"invalid UTF-8 at byte k"`), `Bytes.ofLatin1 : String →
  Except String Bytes` (fails on a character above 255) and `Bytes.toLatin1` (total).
  `Bytes.ofString`/`toString` (9d) still go through a C string.
* **Bytes** also got `slice b start len`, `take`, `drop`, `append` (in place when the
  first is unique), `eq`, `isEmpty`, `at : Bytes → Nat → Option Nat` (`get` past the end
  is 0), `ofList`/`toList` (`List Nat`, each mod 256), `singleton`, `range n` (0 … n-1)
  and `show` (`[1, 2, 255]`). A byte is a `Nat`; `import WordBytes` adds
  `Bytes.ofU8s`/`toU8s` (`List U8`, lib/Word.wiz), kept out of IO and Sys because
  `Hdl.Core` users define their own `U8`.
* **Bytes on a `File`** (stdio, buffered, so they mix with `readLine`):
  `File.readBytes f n : EIO (Option Bytes)` (up to `n`, fewer only at the end; `none`
  at the end), `File.writeBytes`, `File.seek f to : EIO Nat` with
  `SeekFrom = start n | forward n | back n | fromEnd n` (the result is the new offset;
  `.forward 0` asks where it is). `File.flush` was there already.
* **Descriptors.** `foreign_type Fd`: an unbuffered POSIX descriptor, for terminals,
  pipes and devices, where a buffer would hide from `poll` what is waiting.
  `Fd.open path access flags` (`Access = read | write | readWrite`; `OpenFlags` with
  `create`, `truncate`, `append`, `exclusive`, `noControllingTty`, `nonBlockingOpen`;
  `OpenFlags.none`, `.createNew`, `.device`), `Fd.stdin`/`stdout`/`stderr`, `Fd.pipe :
  EIO (Fd × Fd)`, `Child.takePipe c i` (a child's pipe as an `Fd`), `Fd.close`,
  `Fd.seek`, and:

  | read | result |
  |---|---|
  | `Fd.read f n` | `Option Bytes`: one `read(2)`, 1 … n bytes, `none` at the end |
  | `Fd.readWithin f n d` | `Timed (Option Bytes)`: the same, or `.timedOut` when nothing came within `d` |
  | `Fd.readExactly f n` | `Got .false`: `.all b`, or `.eof b` with what came before the end |
  | `Fd.readExactlyWithin f n d` | `Got .true`: also `.timeout b`, with what came in time (`d` is for the whole read) |

  `Got : Bool → Type` is indexed by whether the read had a time limit, and `.timeout`
  only exists at `Got .true`, so a match on what `readExactly` returned needs no
  timeout case (the coverage check knows). `Fd.write f b` writes all of `b` (waiting
  while a non-blocking descriptor is full), `Fd.writeUtf8`; `Fd.readableWithin f d`,
  `Fd.writableWithin`; `Fd.poll (fds : List (Fd × Interest)) d : EIO (List Readiness)`
  (each ready one's position, `readable`, `writable`, `hangup`; empty when the time ran
  out) and `Fd.pollForever`. Time limits are measured on the monotonic clock and
  survive `EINTR`.
* **Handles are not linear.** `Fd`, like `File` and `Child`, is a reference-counted
  foreign pointer: closed by its finalizer when the last reference goes, or by `close`.
  Linear handles would need every `do` block that uses one to be a `do1` block threading
  it, and `EIO`'s `bind` takes its continuation at ω, so a linear handle could not cross
  a `←` in an ordinary `EIO` block (stage 9e). What keeps it sound instead: a closed
  handle's number is forgotten, so a second `close` or a read after `close` is the error
  "Bad file descriptor", never an operation on a number another open has since reused.
  Two things follow from closing at the last use. A handle whose last use comes early
  is closed early: a pseudo-terminal's controller that the program stops using is
  closed, and the terminal side then reads the end of the file, so keep using it (or
  `Fd.close` it at the end). And a bare number from `Fd.raw` outlives its handle: C
  shims get it through `Fd.withRaw f (fun n => …)`, which keeps `f` open until the
  shim returns.
* **Spawn options**, next to `Process.spawn` (whose signature is unchanged; it is
  `spawnWith` with `SpawnOptions.default`): `SpawnOptions` (the three `Stdio`s, `cwd :
  Option String`, `clearEnv`, `env : List EnvChange` with `set k v | unset k` applied
  in order, `group : ProcessGroup = inherit | newGroup | newSession`), built as
  `SpawnOptions.default |> SpawnOptions.inDir d |> SpawnOptions.setEnv k v`;
  `Process.spawnWith`, `outputWith`, `runWith`. `PATH` lookup uses this program's
  `PATH`. `Child.tryWait : Child → EIO (Option ExitStatus)` doesn't block;
  `Child.killGroup c sig` signals the group a `.newGroup`/`.newSession` child leads.
* **Paths, clocks.** `FS.realPath`, `IO.appPath` (the running program: `/proc/self/exe`
  on Linux, `_NSGetExecutablePath` on macOS, an error elsewhere). `Duration` (a number
  of nanoseconds: `Duration.millis 200`, `seconds`, …, `add`, `sub`, `lt`),
  `Clock.monotonic`, `Clock.wall` (since the epoch), `Clock.sleep`.
* **Serial ports** (`import Serial`). Typed configuration: `Baud` is an enumeration of
  the standard rates (`.b9600` … `.b3000000`; `Baud.ofBitsPerSecond 115200` finds one),
  `SerialConfig` has `DataBits`, `Parity`, `StopBits`, `FlowControl` (`none | rtsCts |
  xonXoff`), and `SerialConfig.raw8N1 b` is the usual one. `Serial.open path cfg`
  opens for reading and writing (no controlling terminal, without waiting for a
  carrier), configures and discards what was queued; `Serial.withPort` closes again.
  `Serial.configure` always sets raw mode (no echo, line editing, CR/LF translation or
  signals; a read waits for one byte, time limits are `Fd`'s) and reads the settings
  back: a device that didn't keep them is an error. `Serial.settings` reads them as a
  `SerialSettings` (also VMIN/VTIME and whether the terminal is raw),
  `SerialSettings.matches`, `Serial.discard f (input | output | both)` (`tcflush`),
  `Serial.drain` (`tcdrain`), `Serial.isTty`.
* **Pseudo-terminals.** `Pty.open : EIO Pty` (`posix_openpt`): `controller : Fd` is
  the device's side, `path` the terminal side another program opens like a serial port.
  Once nothing has the terminal side open, reading the controller is the end of the file
  (Linux reports EIO there; a controller from `Pty.open` turns that into the end).
  A Linux pseudo-terminal always has 8 data bits and no parity (configuring 7E1 on one
  is the error above); rates, stop bits and flow control are kept, though nothing is
  slowed down.
* `lib/serial.c` is compiled with every program that imports `Serial` (9f); `Sys` itself
  needs nothing new outside the runtime. The self-hosted toolchain's runtime
  (`selfhost/rt.c`) has its own FFI and none of `lib/Sys`: parity would need the
  `wiz_bytes_*` and `wiz_sys_*` functions there (or the runtime's system section shared
  with it) and `link_c` in the self-hosted frontend.

Tests: six more cases in the `sys` group (bytes and encodings; all 256 byte values
through a pipe, the end of a file, a time limit that fires, double close; file bytes and
seek; spawn options, process groups, try-wait; poll and a child's pipe; paths and
clocks) and the new `serial` group (a pseudo-terminal: all 256 values both ways and
the raw settings read back; a terminal that doesn't answer in time and a discarded
input queue; every rate, stop bits and flow control read back, and the errors), on both
backends, no hardware needed.
