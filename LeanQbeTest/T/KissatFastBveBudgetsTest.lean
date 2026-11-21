module

public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
meta import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for `FullFastBveBudgets` (M2 Tier-A)

1. Executable `#guard` checks on `fastBveBudgets_fns` (`7` upgraded functions), names & signatures,
   `fastBveBudgetsExterns` (`21` externs), `fastBveBudgetsModule.checkAcyclic`, and the `28`-row
   `fastBveBudgetsSpecTable`.
2. Single-line `#print axioms` audit (`<= 100` cols) on all exported `Func.Wf`, acyclicity, gate
   soundness, UNSAT-only `Func.wp`, `SpecEntry.Impl`, `ModuleOk`, and concrete `Mem 64` UNSAT
   non-vacuity theorems (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatFastBveBudgetsTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets

/-! ## 1. Executable `#guard` sanity checks -/

#guard fastBveBudgets_fns.length == 7
#guard fastBveBudgetsExterns.length == 21
#guard fastBveBudgetsModule.checkAcyclic == true
#guard fastBveBudgetsSpecTable.length == 28
#guard fastBveBudgets_fns.map Fn.name ==
  [ "full_init_hdr", "full_probe_run", "full_transitive", "full_vivify",
    "full_tarjan_scc", "full_forward_sub", "full_bve_var" ]
#guard (fastBveBudgets_fns.map fun f => (f.name, f.as.length, f.rs.length)) ==
  [ ("full_init_hdr", 4, 0), ("full_probe_run", 2, 1), ("full_transitive", 2, 1),
    ("full_vivify", 3, 1), ("full_tarjan_scc", 1, 1), ("full_forward_sub", 2, 1),
    ("full_bve_var", 2, 1) ]
#guard (fastBveBudgetsSpecTable.all fun e => e.noExit) == true

/-! ## 2. Single-line `#print axioms` audit -/

#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fastBveBudgets_fns_wf
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fastBveBudgets_acyclic
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.bve_gate_pg_ng_unsat_iff
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.bve_gate_pg_ng_extUnsatSound
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_init_hdr_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_init_hdr_canon_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_probe_run_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_transitive_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_vivify_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_tarjan_scc_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_tarjan_scc_canon_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_forward_sub_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_bve_var_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fast_bve_var_def_wp
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fastBveBudgetsEnv_noExit
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.fastBveBudgets_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_init_hdr
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_probe_run
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_transitive
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_vivify
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_tarjan_scc
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_forward_sub
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_forward_sub_unsat20
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_bve_var
#print axioms LeanQbe.T.Examples.Kissat.FullFastBveBudgets.nv_fast_bve_var_def

end LeanQbeTest.T.KissatFastBveBudgetsTest
