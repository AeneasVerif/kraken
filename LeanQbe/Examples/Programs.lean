module

public import LeanQbe.Examples.LitmusProgs
public import LeanQbe.Examples.UnionFind
public import LeanQbe.Examples.LratTrim
public import LeanQbe.Examples.LratBytes

/-!
# The program table

The built-in programs: every litmus function and every multi-function module that the command-line
driver (`LeanQbe.Driver`) can print, on every target. This is the only table: the executables
`leanqbe` (x64) and `leanqbe-arm64` list and compile exactly these, and the test, benchmark and tool
scripts ask the executables by name.

Three groupings of the union-find functions have a name each, because three users need them:

* `uf`: `find` and `union` (which calls `find` twice), the module of the litmus harness
  `test/uf_main.c` and of the end-to-end theorems;
* `unionfind`: `find` and `unionInline` (no call), the module of `test/arm64/unionfind_main.c`;
* `uf_bench`: all three in one module, as `bench/uf_bench.c` links them.
-/

@[expose] public section

namespace LeanQbe

/-- Built-in programs and multi-function modules: name, functions (callees first). -/
def programs : List (String × List Fn) :=
  let find : Fn := ⟨"find", UnionFind.find⟩
  let union : Fn := ⟨"union", UnionFind.union⟩
  let unionInline : Fn := ⟨"unionInline", UnionFind.unionInline⟩
  ([Litmus.tracer, Litmus.ifelse, Litmus.sumto, Litmus.evenodd, Litmus.nested, Litmus.swap,
    Litmus.spill10].map fun f => (f.name, [f])) ++
  [("callinc", [Litmus.inc, Litmus.callinc]),
   ("twice", [Litmus.check, Litmus.twice]),
   ("sumcall", [Litmus.inc, Litmus.sumcall]),
   ("uf", [find, union]),
   ("unionfind", [find, unionInline]),
   ("uf_bench", [find, union, unionInline]),
   ("lrat_trim", LratTrim.lratTrimFns),
   ("lrat_bytes", LratBytes.lratBytesFns)]

end LeanQbe
