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

The three union-find names (`uf` for `test/uf_main.c`, `unionfind` for
`test/arm64/unionfind_main.c`, and `uf_bench` for `bench/uf_bench.c`) all compile the unified
three-function module `UnionFind.ufFns` (`find`, `union`, `unionInline`), matching the single
compiled record in `Amd64.UnionFind` and `Arm64.UnionFind`.
-/

@[expose] public section

namespace LeanQbe

/-- Built-in programs and multi-function modules: name, functions (callees first). -/
def programs : List (String × List Fn) :=
  ([Litmus.tracer, Litmus.ifelse, Litmus.sumto, Litmus.evenodd, Litmus.nested, Litmus.swap,
    Litmus.spill10].map fun f => (f.name, [f])) ++
  [("callinc", [Litmus.inc, Litmus.callinc]),
   ("twice", [Litmus.check, Litmus.twice]),
   ("sumcall", [Litmus.inc, Litmus.sumcall]),
   ("uf", UnionFind.ufFns),
   ("unionfind", UnionFind.ufFns),
   ("uf_bench", UnionFind.ufFns),
   ("lrat_trim", LratTrim.lratTrimFns),
   ("lrat_bytes", LratBytes.lratBytesFns)]

end LeanQbe
