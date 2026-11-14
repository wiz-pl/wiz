# Stage 29: native data structures

Three structures that Wiz programs need once they handle a lot of data: unboxed arrays
of machine words, maps from 64-bit words, and interned strings. Stage S0 of the code
analysis design (`wiz-notes/code-analysis-design.md`, §3 and §6) asked for them, and
they also help compilers and checkers written in Wiz. Each one follows the 22b/22d
pattern:

* a **model** in plain Wiz data. A `sealed inductive` (22k) with a private constructor
  around a list, every operation defined on that list. The kernel computes with the
  definitions and proofs see them. `#eval` and `#run` run them too, so the
  interpreters give a reference implementation for free;
* **natives** for compiled code (`runtime/`). `attribute [implemented_by mk get]`
  on the constructor gives the type a native representation, and `implemented_by` on
  each operation runs a C function instead of the definition. Both backends call them
  through the usual extern wrappers, so the LLVM backend needed no changes;
* **laws** proved on the model where that is cheap;
* a **trust story**. The natives are trusted to agree with the definitions, as
  `UIntN.add` is. `#print axioms` lists each one, marked `native` (22f). The C code is
  small (about 490 lines for all three), and the tests run every program both ways.

Tests: group `natives` (in CI's `library` shard). Its differential programs are
`examples/wordarray.wiz`, `examples/wordmap.wiz` and `examples/intern.wiz`. Benchmark:
`examples/natives-bench.wiz` (`wiz-tools/bench/natives`).

## 29a: unboxed word arrays (`lib/WordArray.wiz`)

`U8Array`, `U32Array` and `U64Array`, with `empty`, `ofList`/`toList`, `size`,
`get`/`getD`, `set`, `push`, `pop`, `slice` (`[start, start + n)`, cut at the end),
`append`, `replicate` and `foldl`. In the model a `U32Array` is
`mk (toList : List U32)`. Out-of-range indices behave as they do there: `getD` gives
the default (`get` gives 0) and `set` changes nothing.

* **Compiled.** An array is a header plus one C array of `uint8_t`, `uint32_t` or
  `uint64_t`, with its length and capacity (`wiz_warray`, tag `WIZ_TAG_WARRAY`). No
  element is a Wiz object, so reference counting never visits the elements and freeing
  the array is one `free`. A million `U32`s take 4 MB. As an `Array U32` they take 8 MB
  of `wiz_val`s, and a `List U32` needs 24 MB of cells. Elements leave and enter as
  words (22d): scalars, plus a raw box for a `U64` of 2^63 or more.
* **In place when unique.** As with `Array`, `set`, `push`, `pop` and `append` change
  the array itself when its count is 1. Otherwise they copy it first, so old versions
  stay valid. A slice of a unique array starting at 0 truncates in place; any other
  slice copies.
* **For C.** Code in a `link_c` file or a `glue` block that takes a word array (an
  extern parameter of type `U32Array` arrives as the Wiz value and is owned by the
  callee) reads it with `void *wiz_warray_data(wiz_val)` and
  `size_t wiz_warray_len(wiz_val)`. The pointer is borrowed: it is valid while the
  caller holds the array and doesn't update it. `wiz_warray_of_c(width, ptr, n)` makes
  a new array from C memory. Like `wiz_release`, these three are part of the C
  interface whatever `WIZ_API` is.
* **Laws** (proved, through list lemmas `List.length_snoc`, `List.getD_setAt` and
  others): `size_empty`, `size_push`, `getD_push` (the pushed element is at index
  `size a`), `size_set`, `getD_set` (`getD (set a i x) i d = x` when `i < size a`),
  `size_append` and `ofList_toList`, for each width.
* `replicate`, `pushN` and `foldl` are Wiz loops over the natives, not natives of their
  own. They are definitions, so nothing more is trusted.

## 29b: maps from 64-bit words (`lib/WordMap.wiz`)

`U64Map V`, with `empty`, `insert`, `erase`, `find` (an `Option`), `findD`,
`contains`, `size`, `toList`, `ofList`, `foldl` and `keys`. Other word types, typed ids
(22e) and interned strings go through `U64`.

* **The model** is `mk (entries : List (U64 × V))` with the keys strictly increasing.
  The module keeps this invariant: the constructor is private and `insertL` and
  `eraseL` preserve sortedness. So every map has exactly one model, and `toList` and
  `foldl` see the entries by increasing key in the kernel, in the interpreters and in
  compiled code alike. That is the reason a general `HashMap K V` with a `Hashable`
  class is not here. Its iteration order would depend on the hash, so either the model
  would be unfaithful or every traversal would need an order on `K` too. A `U64Map` is
  the case scry and the compilers need.
* **Compiled** (`wiz_wmap`): open addressing over `uint64_t` keys and Wiz values, with
  linear probing at most half full, the murmur3 finaliser as the hash, and deletion by
  backward shift, so there are no tombstones. An empty slot is a zero value, since no
  Wiz value is 0. `insert`, `find`, `erase` and `contains` take expected constant time.
  `toList`, `foldl` and `keys` sort the entries, O(n log n), which is the price of a
  canonical model. An update copies a shared table and changes a unique one in place.
* **Laws** (proved): `find_empty`, and `find_insert`
  (`find (insert m k v) k = some v`). `find` after `erase`, and `insert` at another key,
  rest on the sorted-keys invariant. They are tested (the random operations in
  `examples/wordmap.wiz`), not proved yet.

## 29c: interned strings (`lib/Intern.wiz`)

`InternTable`, with `empty`, `intern` (the table with the string, and the string's
id), `internAll`, `find`, `lookup`, `size` and `toList`. An id is a `U32`, so ids
compare and hash as words. Ids are stable (a string keeps its id) and handed out in
order 0, 1, 2, … A table is a functional value that is updated in place when unique.
It is not a global pool: a global pool can't have a model in pure Wiz, since its ids
would depend on the history of the whole program. Keep one table per program or per
analysis, threaded through like a `StrMap`.

* **The model** is `mk (strs : List String)`, the strings by id, all distinct (a
  module invariant).
* **Compiled** (`wiz_itab`): the `String` values by id, kept as they are, so `lookup`
  copies nothing, plus a hash index from a string to its id + 1. Strings are hashed
  (FNV-1a) and compared by code point, walking the `String.mk (List Char)` cells.
  `intern` and `find` take time proportional to the string's length, and `lookup`
  takes constant time. An extern passes the `String` as a Wiz value through
  `StringObj` (`def StringObj : Type := String`, as `NatObj` does for numbers), not as
  a C string.
* **Laws:** `size_empty` and `find_empty`. That `lookup` returns the interned string
  needs `String.eq` to be equality, which `lib/Text.wiz` doesn't prove yet, and fewer
  than 2^32 strings. It is tested, not proved.
* **Where model and natives part:** a table with 2^32 − 1 strings. The model's ids
  wrap around there and the native aborts.

## Reference counting and threads

All three follow the runtime's rules (stage 8, 25a). Each native consumes its
arguments and returns owned values. In-place updates need a count of exactly 1, which
an object shared between threads (`rc < 0`) never has, so a shared structure is
always copied before it changes. `wiz_mark_mt` visits a map's values and a table's
strings. It skips an array's elements, which are not objects. The case "shared between
threads" in group `natives` forks a thread that captures an array and a map. Both
threads update their own copies, and the program checks that nothing leaks, in C and
LLVM.

## The trust story

What is trusted, beyond the compiler: each native computes its definition on the
native representation, and the representation's `get` (`toList`) gives back the
model. For the map and the intern table this relies on the module invariant (sorted
keys, distinct strings), which the module's own definitions keep. Natives abort
instead of answering when memory runs out, when an intern table is full, or on a word
above 64 bits, which the types rule out. The interpreters and the kernel never run
them. Every program in the tests runs under `#eval`, `#run`, C and LLVM, and the
results are compared.

## The self-hosted toolchain

The self-hosted toolchain doesn't use these structures yet, and this stage doesn't
change it. It could use them for:

* the lexer's input (`Array Nat` of code points in `selfhost/Lex.wiz`), as a
  `U32Array`;
* names (`StrMap` keyed by global names in `Frontend.wiz` and `Backend.wiz`):
  interned once, with tables then indexed by id (a `U64Map` or a `U32Array`);
* the metavariable store (`Array MetaInfo`): no change, since its elements are
  objects.

The obstacle is its backend. `selfhost/Backend.wiz` knows the runtime's natives by name
(`nativeNames`: `Array.*`, `StrMap.*`) and supports neither `implemented_by` (22b) nor
native representations (22d). Self-compiled code would run the list models, with O(n)
`get`. Before the self-hosted sources can use these structures, the backend needs the
attribute, or these names in `nativeNames` and their functions in `selfhost/rt.c`.

## Not yet

Arrays of other widths (`U16`, `I32`; each takes about 60 lines), slices that share
storage, sorting, and `U8Array` ↔ `Bytes`. Passing a word array to an `import_c`
function as a pointer and a length directly (as `Bytes` is, kind `y`, 9i) instead of
through `wiz_warray_data`. A general `HashMap` (see 29b). Union-find and bitsets, the
other structures §3 of the design asks for.
