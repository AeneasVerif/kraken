/-! Native Lean 4 oracle for P5 coverage tests (`test/lcnf/run.sh`). -/

set_option autoImplicit false

open LeanQbe.T.LeanLCNF.Coverage

def main (args : List String) : IO Unit := do
  let quick := args == ["quick"]
  for n in [0, 1, 7, 42, 123456789] do
    IO.println s!"STR n={n} lit={strLitTest n}"
  for n in [0, 1, 15, 64, 600] do
    if quick && n > 100 then continue
    IO.println s!"SBLD n={n} r={strBuildBench n}"
  for n in [0, 1, 5, 19] do
    IO.println s!"BNAT n={n} r={bigNatBench n}"
  for n in [2, 10, 80, 150] do
    if quick && n > 80 then continue
    IO.println s!"ARR n={n} bench={arrBench n} lin={arrLinear n 20} sh={arrShared n 10}"
  for n in [1, 10, 100, 600] do
    if quick && n > 100 then continue
    IO.println s!"BA n={n} r={byteArrBench n}"
  for n in [0, 1, 7, 42] do
    IO.println s!"FLT n={n} r={floatBench n}"
  for n in [0, 1, 5, 977] do
    if quick && n > 5 then continue
    IO.println s!"INT n={n} r={intBench n}"
  for n in [0, 1, 7, 42, 89, 1000] do
    IO.println s!"BVI n={n} r={bitVecIntBench n}"
  for n in [0, 1, 7, 123456789] do
    IO.println s!"I64 n={n} r={int64Bench n} ubv={uintBvBench n} sh={shapeBench (n % 100)}"
  for n in [0, 9, 4294967296] do
    IO.println s!"MISC n={n} us={usizeBench n} sha={shaMix n}"
