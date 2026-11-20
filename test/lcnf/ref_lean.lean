/-! Native Lean 4 oracle for `test/lcnf/run.sh`.

`run.sh` prepends the demo source extracted verbatim from `LeanQbe/T/LeanLCNF/Demo.lean`
(between the `BEGIN`/`END LCNF DEMO` markers, wrapped in `namespace LeanQbe.T.LeanLCNF.Demo`),
then compiles the result with `lean -c` + `leanc -O2`.  The output format matches
`test/lcnf/lcnf_main.c` line for line. -/

open LeanQbe.T.LeanLCNF.Demo

def rbNs : List Nat := [0, 1, 2, 3, 7, 10, 64, 100, 500, 1000, 2000]
def sortNs : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 3), (3, 9), (10, 4), (100, 5), (500, 6), (1000, 7), (2000, 8)]
def sats : List (Nat × Nat × Nat × Nat) :=
  [(0, 2, 1, 0), (0, 3, 2, 0), (0, 3, 3, 0), (0, 4, 3, 0), (0, 4, 4, 0), (0, 5, 4, 0),
   (1, 10, 30, 1), (1, 10, 50, 2), (1, 12, 70, 9), (1, 15, 60, 3), (1, 16, 90, 10),
   (1, 20, 80, 4), (1, 20, 91, 5), (1, 25, 100, 6), (1, 30, 120, 7), (1, 30, 150, 8)]
def vms : List (Nat × Nat × Nat) :=
  [(0, 0, 1), (1, 1, 1), (10, 3, 2), (100, 5, 3), (1000, 8, 4), (3000, 10, 5)]

def runTests (quick : Bool) : IO Unit := do
  for n in rbNs do
    if quick && n > 200 then continue
    IO.println s!"RB n={n} bench={rbBench n} persist={rbPersist n} linear={rbLinear n 3} \
      shared={rbShared n 3}"
  for (n, seed) in sortNs do
    if quick && n > 200 then continue
    IO.println s!"SORT n={n} seed={seed} r={sortBench n seed}"
  for (k, a, b, s) in sats do
    if quick && k == 0 && a > 4 then continue
    let r := satSolve k a b s
    IO.println s!"SAT kind={k} a={a} b={b} seed={s} sat={r % 2} nodes={r / 2}"
  for (n, d, s) in vms do
    if quick && n > 100 then continue
    IO.println s!"VM n={n} depth={d} seed={s} r={vmBench n d s}"

/-- Time one workload (inputs depend on `k` so nothing is hoisted into a closed term). -/
def bench (name : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := f ()
  if r == 1234567890123 then IO.println "-"  -- forces `r` before the second clock read
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0).toFloat / 1.0e6
  IO.println s!"BENCH {name} {ms} {r}"

def runBench (k : Nat) : IO Unit := do
  bench "rbmap" fun _ => rbBench (200000 + k)
  bench "rbmap_fbip" fun _ => rbLinear (100000 + k) 20
  bench "mergesort" fun _ => sortBench (50000 + k) 42
  bench "dpll_php87" fun _ => satSolve 0 (8 + k) 7 0
  bench "dpll_rand" fun _ => satSolve 1 (70 + k) 298 11
  bench "exprvm" fun _ => (vmBench (30000 + k) 10 77).toNat

def main (args : List String) : IO Unit := do
  match args with
  | ["bench"] => runBench (args.length - 1)
  | ["quick"] => runTests true
  | _ => runTests false
