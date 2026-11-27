/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Full
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S0Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5Rows
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.Src.Full
meta import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep13S0Rows
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Rows
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2Rows
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Rows
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4Rows
meta import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5Rows
meta import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Kissat `Src.Full` Step-13 `S0..S5` `418`-Fn AST Parity & Zero-Dead-Code Test

Verifies exact `reifyFunc` / `Fn` equality between the flattened `418`-function
`LeanQbe.T.Examples.Kissat.Src.Full.kissatModule` and the live functions from landed
`FullFidelityAssemblyStep12` + `FullFidelityStep13S0..S5` (`0` `PatchModule` layers,
`checkAcyclic = true`, `0` dead functions reachable from `kissat_solve_bytes` /
`kissat_solve_bytes_seeded`, `<= std3` axioms).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.KissatSrcStep13ParityTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.PatchModule

public section

/-- Combined `S0..S5` replacement functions (`101` fns across `S0..S5`). -/
def step13Repls : List Fn :=
  FullFidelityStep13S0.fidStep13S0Repls ++
  FullFidelityStep13S1.fidStep13S1Repls ++
  FullFidelityStep13S2.fidStep13S2Repls ++
  FullFidelityStep13S3.fidStep13S3Repls ++
  FullFidelityStep13S4.fidStep13S4Repls ++
  FullFidelityStep13S5.fidStep13S5Repls

/-- Combined `S0..S5` newly added helper functions (`29` fns across `S0..S5`). -/
def step13Adds : List Fn :=
  FullFidelityStep13S0.fidStep13S0AddFns ++
  FullFidelityStep13S1.fidStep13S1Adds ++
  FullFidelityStep13S2.fidStep13S2Befores.flatMap Prod.snd ++
  FullFidelityStep13S3.fidStep13S3Befores.flatMap Prod.snd ++
  FullFidelityStep13S4.fidStep13S4Befores.flatMap Prod.snd ++
  FullFidelityStep13S5.fidStep13S5Befores.flatMap Prod.snd

/-- Full Step-13 ground-truth function pool (`546` total = `517` Step-12 + `29` S0..S5 adds). -/
def step13AllFns : List Fn :=
  spliceFns step13Repls FullFidelityAssemblyStep12.fidStep12Fns ++ step13Adds

/-- Ground-truth Step-13 `Module` pool used as the reference RHS for `derive_reuse_bridge!`. -/
def step13PoolModule : LeanQbe.T.Module :=
  { fns := step13AllFns, externs := [], exits := [] }

derive_reuse_bridge! step13Bridge Src.Full.kissatModule step13PoolModule

private def exprCallees {rs : List Ty} : Expr (fun _ => Unit) (fun _ => Unit) rs → List Sym
  | .let_ _ k => exprCallees (k (Tup.units _))
  | .load _ _ k => exprCallees (k ())
  | .store _ _ k => exprCallees k
  | .call f (bs := bs) _ k => f :: exprCallees (k (Tup.units bs))
  | .jnz _ t e => exprCallees t ++ exprCallees e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => []
  | .group (sig := sig) bodies k =>
    blocksCallees (bodies (Tup.units sig)) ++ exprCallees (k (Tup.units sig))
where
  blocksCallees : {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → List Sym
    | _, .nil => []
    | _, .cons b bs => exprCallees (b (Tup.units _)) ++ blocksCallees bs

private def fnCallees (fn : Fn) : List Sym :=
  (exprCallees (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))).eraseDups

private def reachCount (fns : List Fn) (roots : List Sym) : Nat :=
  let adj : Std.HashMap Sym (List Sym) :=
    fns.foldl (fun acc f => acc.insert f.name (fnCallees f)) {}
  let rec go : Nat → List Sym → Std.HashSet Sym → Nat
    | 0, _, vis => vis.size
    | _ + 1, [], vis => vis.size
    | n + 1, u :: rest, vis =>
      if vis.contains u then go n rest vis
      else
        let cs := adj.getD u []
        go n (rest ++ cs.filter (!vis.contains ·)) (vis.insert u)
  go (fns.length * fns.length + 1) roots {}

end

#guard step13Repls.length == 101
#guard step13Adds.length == 29
#guard step13PoolModule.fns.length == 546
#guard Src.Full.kissatModule.fns.length == 418
#guard (Src.Full.kissatModule.fns.map Fn.name).eraseDups.length == 418
#guard Src.Full.kissatModule.checkAcyclic == true
#guard Src.Full.kissatModule.externs.isEmpty && Src.Full.kissatModule.exits.isEmpty

-- Contiguous LHS slice coverage across all `418` `Src.Full` slots (`0..417`, `0` gaps)
#guard
  (step13Bridge_runs.foldl (fun (ok, exp) (a, _, len) => (ok && a == exp, a + len)) (true, 0)) ==
    (true, 418)

-- Distinct RHS slots matched in `step13PoolModule` (`418` distinct live functions)
#guard
  (step13Bridge_runs.map (fun (_, b, len) => (List.range len).map (b + ·))).flatten.eraseDups.length
    == 418

-- Explicit `reifyFunc` + `tflatBeq` verification on every matched pair
#guard
  (step13Bridge_lhsSlices.flatten.zip step13Bridge_rhsSlices.flatten).all fun (f, g) =>
    fnStructBeq f g

-- Zero dead/unreachable functions in `Src.Full` (`418` reachable == `418` total), matching Step-13
#guard
  reachCount Src.Full.kissatModule.fns ["kissat_solve_bytes", "kissat_solve_bytes_seeded"] == 418
#guard
  reachCount step13PoolModule.fns ["kissat_solve_bytes", "kissat_solve_bytes_seeded"] == 418

public section

/-- Kernel `Eq.refl` witness equating all `418` functions in `Src.Full.kissatModule`
(partitioned into contiguous slices) with landed Step-13 `S0..S5` live functions. -/
theorem src_step13_parity_eq : step13Bridge_lhsSlices = step13Bridge_rhsSlices :=
  step13Bridge_eq

/-- Flattened `418`-function `List Fn` equality (`reifyFunc` identical by `rfl`). -/
theorem src_step13_fns_flat_eq :
    step13Bridge_lhsSlices.flatten = step13Bridge_rhsSlices.flatten :=
  congrArg List.flatten step13Bridge_eq

/-- Every function in `Src.Full.kissatModule` is PHOAS well-formed (`Func.Wf`). -/
theorem src_full_wf : ∀ f ∈ Src.Full.kissatModule.fns, f.Wf :=
  Src.Full.kissatModule_wf

end

end LeanQbeTest.T.KissatSrcStep13ParityTest

#print axioms LeanQbeTest.T.KissatSrcStep13ParityTest.step13Bridge_eq
#print axioms LeanQbeTest.T.KissatSrcStep13ParityTest.src_step13_parity_eq
#print axioms LeanQbeTest.T.KissatSrcStep13ParityTest.src_step13_fns_flat_eq
#print axioms LeanQbeTest.T.KissatSrcStep13ParityTest.src_full_wf
