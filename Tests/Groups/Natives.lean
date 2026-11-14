import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (S0) A differential test of a native structure: `examples/NAME.wiz`'s `main` gives the
same value under `#eval` and `#run` (the model) and compiled, C and LLVM (the natives). -/
def nativesSame (name expected : String) : IO Unit := do
  let src ← IO.FS.readFile s!"examples/{name}.wiz"
  okLibs (src ++ "\n#eval main\n#run main\n") [expected, expected]
  cRunLibs src expected
  cRunLibs src expected (llvm := true)

/-- C code reading a `U32Array` and making a `U64Array` (`wiz_warray_*`, runtime/). -/
def warrayHelper : String := "#include <stdint.h>
#include <stdlib.h>
typedef uintptr_t wiz_val;
void *wiz_warray_data(wiz_val v);
size_t wiz_warray_len(wiz_val v);
wiz_val wiz_warray_of_c(uint32_t width, const void *p, size_t n);
void wiz_release(void *v);
uint64_t weighted_sum(wiz_val a) {
  const uint32_t *p = (const uint32_t *)wiz_warray_data(a);
  uint64_t s = 0;
  for (size_t i = 0; i < wiz_warray_len(a); i++) s += (uint64_t)p[i] * (i + 1);
  wiz_release((void *)a);
  return s;
}
wiz_val squares(uint64_t n) {
  uint64_t *p = (uint64_t *)malloc((n ? n : 1) * sizeof(uint64_t));
  for (uint64_t i = 0; i < n; i++) p[i] = i * i;
  wiz_val r = wiz_warray_of_c(8, p, n);
  free(p);
  return r;
}
"

/-- Two threads share a word array and a word map (25a: marked shared when the closure
crosses), each updates its own copy. -/
def nativesThreads : String := "import IO
import Session
import MVar
import WordArray
import WordMap
def fill : Nat → U32Array → U32Array
  | .zero, a => a
  | .succ n, a => U32Array.push (fill n a) (U32.ofNat n)
def mfill : Nat → U64Map Nat → U64Map Nat
  | .zero, m => m
  | .succ n, m => mfill n (U64Map.insert m (U64.ofNat n) n)
def total (a : U32Array) (m : U64Map Nat) : Nat :=
  U32Array.foldl (fun s x => s + x.toNat) 0 a + U64Map.foldl (fun s k v => s + v) 0 m
def main : IO Unit := IO.bind (MVar.new (A := Nat)) (fun r =>
  let a := fill 1000 U32Array.empty;
  let m := mfill 500 U64Map.empty;
  Chan.fork Proto.done (fun c => Chan.close c (MVar.put r (total (U32Array.set a 0 (U32.ofNat 100000)) (U64Map.erase m (U64.ofNat 1)))))
    (fun c => Chan.close c (IO.bind (MVar.take r) (fun x =>
      IO.println (Nat.toString (x + 1000000 * total (U32Array.push a (U32.ofNat 1)) (U64Map.insert m (U64.ofNat 1) 0)))))))
"

def nativesGroup : Group where
  name := "natives"
  exercise := "S0: lib/WordArray.wiz, lib/WordMap.wiz, lib/Intern.wiz (docs/stages/29-natives.md)"
  cases := [
    { name := "word arrays: the model (#eval, #run) and the natives (C, LLVM) agree", run := fun _ =>
        nativesSame "wordarray" "24057236113" },
    { name := "word maps: the model and the natives agree (growing, erasing, keys above 2^63)", run := fun _ =>
        nativesSame "wordmap" "6735556925" },
    { name := "intern tables: the model and the natives agree", run := fun _ =>
        nativesSame "intern" "3120451233" },
    { name := "compiled code calls the natives: no list in the IR", run := fun _ => do
        let src := "import WordArray\nimport WordMap\nimport Intern\n" ++
          "def f (a : U32Array) (i : Nat) : U32Array := U32Array.push (U32Array.set a i (U32Array.get a 0)) (U32.ofNat 3)\n" ++
          "def g (m : U64Map Nat) (k : U64) : Nat := U64Map.findD (U64Map.insert (U64Map.erase m k) k 1) k 0\n" ++
          "def h (t : InternTable) (s : String) : U32 := (InternTable.intern t s).2\n#ir f\n#ir g\n#ir h"
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        for n in ["wiz_warray_push", "wiz_warray_set", "wiz_warray_get", "wiz_wmap_find_d", "wiz_wmap_insert",
            "wiz_wmap_erase", "wiz_itab_intern"] do
          check ((out.splitOn n).length > 1) s!"no call of {n} in:\n{out}"
        check ((out.splitOn "to_list").length == 1 && (out.splitOn "ctor").length == 1) s!"a list in:\n{out}" },
    { name := "the laws are proved on the model; #print axioms lists the natives", run := fun _ => do
        okLibs "import WordArray\nimport WordMap\n#check U32Array.getD_set\n#check U64Map.find_insert"
          ["U32Array.getD_set : (a : U32Array) → (i : Nat) → (x : U32) → (d : U32) → Nat.lt i (U32Array.size a) = .true → U32Array.getD (U32Array.set a i x) i d = x",
           "U64Map.find_insert : {V : Type} → (m : U64Map V) → (k : U64) → (v : V) → U64Map.find V (U64Map.insert V m k v) k = .some v"]
        let src := "import WordArray\ndef len (a : U8Array) : Nat := U8Array.size (U8Array.push a (U8.ofNat 1))\n#print axioms len"
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        for a in ["native U8Array.size := U8Array.sizeNative", "native U8Array.push := U8Array.pushNative",
            "native U8Array := U8Array.ofListNative/U8Array.toListNative", "U8Array.seal✝"] do
          check ((out.splitOn a).length > 1) s!"{a} not listed:\n{out}" },
    { name := "a unique array or map is updated in place (200k updates each, linear)", run := fun _ =>
        cRunLibs ("import WordArray\nimport WordMap\ndef fill : Nat → U32Array → U32Array\n  | .zero, a => a\n" ++
          "  | .succ n, a => fill n (U32Array.set (U32Array.push a (U32.ofNat n)) 0 (U32.ofNat n))\n" ++
          "def mfill : Nat → U64Map Nat → U64Map Nat\n  | .zero, m => m\n  | .succ n, m => mfill n (U64Map.insert m (U64.ofNat (Nat.mod n 1000)) n)\n" ++
          "def main : Nat := U32Array.size (fill 200000 U32Array.empty) + U64Map.size (mfill 200000 U64Map.empty)") "201000" },
    { name := "C code reads a word array and makes one (wiz_warray_data/len/of_c), C and LLVM", run := fun _ => do
        let src := "import WordArray\nextern \"weighted_sum\" weightedSum : U32Array → Nat\nextern \"squares\" squares : Nat → U64Array\n" ++
          "def main : Nat := weightedSum (U32Array.ofList [U32.ofNat 3, U32.ofNat 4, U32.ofNat 4294967295]) + " ++
          "1000000000000000 * U64Array.foldl (fun s x => s + x.toNat) 0 (squares 10)"
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
        for llvm in [false, true] do
          let dir ← IO.FS.createTempDir
          IO.FS.writeFile (dir / "helper.c") warrayHelper
          let tc ← toolchain
          match ← Build.runGlobal { tc with libs := tc.libs ++ [(dir / "helper.c").toString] } s "main" dir llvm (timeout := some 120) with
          | .ok v => checkEq "285000012884901896" v
          | .error e =>
            if ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1 then skip "no toolchain"
            else throw (IO.userError s!"{if llvm then "(llvm) " else ""}{e}") },
    { name := "shared between threads: each thread's update copies, nothing leaks (C, LLVM)", run := fun _ => do
        cRunLibs nativesThreads "624250724249\n"
        cRunLibs nativesThreads "624250724249\n" (llvm := true) }
  ]

builtin_initialize registerGroup nativesGroup

end Tests.Elab
