/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Kissat.Src.Header
public import LeanQbe.T.Examples.Kissat.Src.Dimacs
public import LeanQbe.T.Examples.Kissat.Src.Limits
public import LeanQbe.T.Examples.Kissat.Src.Arena
public import LeanQbe.T.Examples.Kissat.Src.Watch
public import LeanQbe.T.Examples.Kissat.Src.Heap
public import LeanQbe.T.Examples.Kissat.Src.Backtrack
public import LeanQbe.T.Examples.Kissat.Src.Clause
public import LeanQbe.T.Examples.Kissat.Src.Tiers
public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Examples.Kissat.Src.Internal
public import LeanQbe.T.Examples.Kissat.Src.PropSearch
public import LeanQbe.T.Examples.Kissat.Src.Parse
public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Src.Reduce
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Examples.Kissat.Src.Learn
public import LeanQbe.T.Examples.Kissat.Src.Analyze
public import LeanQbe.T.Examples.Kissat.Src.Decide
public import LeanQbe.T.Examples.Kissat.Src.Walk
public import LeanQbe.T.Examples.Kissat.Src.Restart
public import LeanQbe.T.Examples.Kissat.Src.Extend
public import LeanQbe.T.Examples.Kissat.Src.Lucky
public import LeanQbe.T.Examples.Kissat.Src.Vivify
public import LeanQbe.T.Examples.Kissat.Src.Backbone
public import LeanQbe.T.Examples.Kissat.Src.Transitive
public import LeanQbe.T.Examples.Kissat.Src.Substitute
public import LeanQbe.T.Examples.Kissat.Src.Dense
public import LeanQbe.T.Examples.Kissat.Src.Congruence
public import LeanQbe.T.Examples.Kissat.Src.Kitten
public import LeanQbe.T.Examples.Kissat.Src.Sweep
public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Examples.Kissat.Src.Gates
public import LeanQbe.T.Examples.Kissat.Src.Definition
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Examples.Kissat.Src.Reorder
public import LeanQbe.T.Examples.Kissat.Src.Probe
public import LeanQbe.T.Examples.Kissat.Src.Search
meta import LeanQbe.T.Module
meta import LeanQbe.T.Examples.Kissat.Src.Dimacs
meta import LeanQbe.T.Examples.Kissat.Src.Limits
meta import LeanQbe.T.Examples.Kissat.Src.Arena
meta import LeanQbe.T.Examples.Kissat.Src.Watch
meta import LeanQbe.T.Examples.Kissat.Src.Heap
meta import LeanQbe.T.Examples.Kissat.Src.Backtrack
meta import LeanQbe.T.Examples.Kissat.Src.Clause
meta import LeanQbe.T.Examples.Kissat.Src.Tiers
meta import LeanQbe.T.Examples.Kissat.Src.Bump
meta import LeanQbe.T.Examples.Kissat.Src.Internal
meta import LeanQbe.T.Examples.Kissat.Src.PropSearch
meta import LeanQbe.T.Examples.Kissat.Src.Parse
meta import LeanQbe.T.Examples.Kissat.Src.Collect
meta import LeanQbe.T.Examples.Kissat.Src.Reduce
meta import LeanQbe.T.Examples.Kissat.Src.Deduce
meta import LeanQbe.T.Examples.Kissat.Src.Minimize
meta import LeanQbe.T.Examples.Kissat.Src.Learn
meta import LeanQbe.T.Examples.Kissat.Src.Analyze
meta import LeanQbe.T.Examples.Kissat.Src.Decide
meta import LeanQbe.T.Examples.Kissat.Src.Walk
meta import LeanQbe.T.Examples.Kissat.Src.Restart
meta import LeanQbe.T.Examples.Kissat.Src.Extend
meta import LeanQbe.T.Examples.Kissat.Src.Lucky
meta import LeanQbe.T.Examples.Kissat.Src.Vivify
meta import LeanQbe.T.Examples.Kissat.Src.Backbone
meta import LeanQbe.T.Examples.Kissat.Src.Transitive
meta import LeanQbe.T.Examples.Kissat.Src.Substitute
meta import LeanQbe.T.Examples.Kissat.Src.Dense
meta import LeanQbe.T.Examples.Kissat.Src.Congruence
meta import LeanQbe.T.Examples.Kissat.Src.Kitten
meta import LeanQbe.T.Examples.Kissat.Src.Sweep
meta import LeanQbe.T.Examples.Kissat.Src.Forward
meta import LeanQbe.T.Examples.Kissat.Src.Gates
meta import LeanQbe.T.Examples.Kissat.Src.Definition
meta import LeanQbe.T.Examples.Kissat.Src.Eliminate
meta import LeanQbe.T.Examples.Kissat.Src.Factor
meta import LeanQbe.T.Examples.Kissat.Src.Compact
meta import LeanQbe.T.Examples.Kissat.Src.Reorder
meta import LeanQbe.T.Examples.Kissat.Src.Probe
meta import LeanQbe.T.Examples.Kissat.Src.Search

/-!
# Flat `410`-Function Kissat 4.0.4 Full Solver Module (`Src/Full.lean`)

Direct acyclic list concatenation of all `40` upstream-mirrored `Src/*.lean` C0 modules
(`Dimacs.fns ++ Limits.fns ++ ... ++ Search.fns`) with:
- **`0` `PatchModule` / `patchFns` / `spliceFns` / `befores` / `renameFuncCalls`**
- **`0` dead function slots** (`410` live functions, `0` externs, `0` exits)
- **`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`*Audit*`/`Amd64`/`Arm64`/`Kraken` imports**
- Kernel-verified `kissatModule_wf : ∀ f ∈ kissatModule.fns, f.Wf` (`<= std3` axioms).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Full

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

/-- Flat `410`-function topological concatenation of all `40` upstream-mirrored `Src/*.lean`
modules (`0` dead slots, `0` back-edges). -/
def kissatFns : List Fn :=
  Dimacs.fns
  ++ Limits.fns
  ++ Arena.fns
  ++ Watch.fns
  ++ Heap.fns
  ++ Backtrack.fns
  ++ Clause.fns
  ++ Tiers.fns
  ++ Bump.fns
  ++ Internal.fns
  ++ PropSearch.fns
  ++ Parse.fns
  ++ Collect.fns
  ++ Reduce.fns
  ++ Deduce.fns
  ++ Minimize.fns
  ++ Learn.fns
  ++ Analyze.fns
  ++ Decide.fns
  ++ Walk.fns
  ++ Restart.fns
  ++ Extend.fns
  ++ Lucky.fns
  ++ Vivify.fns
  ++ Backbone.fns
  ++ Transitive.fns
  ++ Substitute.fns
  ++ Dense.fns
  ++ Congruence.fns
  ++ Kitten.fns
  ++ Sweep.fns
  ++ Forward.fns
  ++ Gates.fns
  ++ Definition.fns
  ++ Eliminate.fns
  ++ Factor.fns
  ++ Compact.fns
  ++ Reorder.fns
  ++ Probe.fns
  ++ Search.fns

/-- Closed `410`-function Kissat 4.0.4 `LeanQbe.T.Module` (`0` externs, `0` exits). -/
def kissatModule : LeanQbe.T.Module :=
  { fns := kissatFns, externs := [], exits := [] }

end

#guard kissatModule.fns.length == 410
#guard (kissatModule.fns.map Fn.name).eraseDups.length == 410
#guard kissatModule.checkAcyclic == true
#guard kissatModule.externs.isEmpty && kissatModule.exits.isEmpty

public section

theorem kissatModule_fns : kissatModule.fns = kissatFns := rfl

theorem kissatModule_noExterns : kissatModule.externs = [] := rfl

theorem kissatModule_noExit : kissatModule.exits = [] := rfl

private theorem append_wf {xs ys : List Fn}
    (hx : ∀ f ∈ xs, f.Wf) (hy : ∀ f ∈ ys, f.Wf) :
    ∀ f ∈ xs ++ ys, f.Wf := fun f hf =>
  (List.mem_append.mp hf).elim (hx f) (hy f)

/-- Every function in `kissatModule` is PHOAS well-formed (`Func.Wf`). -/
theorem kissatModule_wf : ∀ f ∈ kissatModule.fns, f.Wf := by
  have h := append_wf Dimacs.fns_wf Limits.fns_wf
  have h := append_wf h Arena.fns_wf
  have h := append_wf h Watch.fns_wf
  have h := append_wf h Heap.fns_wf
  have h := append_wf h Backtrack.fns_wf
  have h := append_wf h Clause.fns_wf
  have h := append_wf h Tiers.fns_wf
  have h := append_wf h Bump.fns_wf
  have h := append_wf h Internal.fns_wf
  have h := append_wf h PropSearch.fns_wf
  have h := append_wf h Parse.fns_wf
  have h := append_wf h Collect.fns_wf
  have h := append_wf h Reduce.fns_wf
  have h := append_wf h Deduce.fns_wf
  have h := append_wf h Minimize.fns_wf
  have h := append_wf h Learn.fns_wf
  have h := append_wf h Analyze.fns_wf
  have h := append_wf h Decide.fns_wf
  have h := append_wf h Walk.fns_wf
  have h := append_wf h Restart.fns_wf
  have h := append_wf h Extend.fns_wf
  have h := append_wf h Lucky.fns_wf
  have h := append_wf h Vivify.fns_wf
  have h := append_wf h Backbone.fns_wf
  have h := append_wf h Transitive.fns_wf
  have h := append_wf h Substitute.fns_wf
  have h := append_wf h Dense.fns_wf
  have h := append_wf h Congruence.fns_wf
  have h := append_wf h Kitten.fns_wf
  have h := append_wf h Sweep.fns_wf
  have h := append_wf h Forward.fns_wf
  have h := append_wf h Gates.fns_wf
  have h := append_wf h Definition.fns_wf
  have h := append_wf h Eliminate.fns_wf
  have h := append_wf h Factor.fns_wf
  have h := append_wf h Compact.fns_wf
  have h := append_wf h Reorder.fns_wf
  have h := append_wf h Probe.fns_wf
  exact append_wf h Search.fns_wf

end

end LeanQbe.T.Examples.Kissat.Src.Full
