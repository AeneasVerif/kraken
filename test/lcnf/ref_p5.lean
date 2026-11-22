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
