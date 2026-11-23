module

public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7BveGates
meta import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Checks, and Axiom Audit for Kissat `FullM7BveGates` Tail

1. Executable `#guard` checks on `m7BveGatesModule` (`39` owned `_m7` fns + `23` externs),
   `43`-row `m7BveAllFns`, `checkAcyclic = true`, `PrintCpp`, `PrintQbe`, and `Fn.legal`
   across `aarch64`, `scalar64`, and `x64AVX2`.
2. Short root-namespace audit theorems covering `full_k6_solve_m7_wp`,
   `full_bve_def_k6_m7_wp`, `full_bve_gates_m7_wp`, unconditional `43`-row `m7BveAll_tableImpl`,
   `M7BveAllTblSpecs`, UNSAT soundness, and concrete `100060`-byte `Mem 64` UNSAT non-vacuity
   (`XPost := False`, `0` SAT model-finding proofs).
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7BveGatesTailTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.FullM7BveGates

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m7BveGatesModule.checkAcyclic == true
#guard m7BveGatesModule.exits.isEmpty
#guard m7BveGates_fns.length == 39
#guard m7BveGatesExterns.length == 23
#guard m7BveAllFns.length == 43
#guard m7BveAllSpecTable.length == 43
#guard m7BveClosedSpecTable.length == 66
#guard m7BveAllFns.map Fn.name ==
  [ "full_dense_prop_unit_m7", "full_dense_flush_units_m7", "full_fwd_flush_large_m7",
    "full_fwd_reconnect_irred_m7", "full_fwd_scan_lit_m7", "full_fwd_check_cl_m7",
    "full_fwd_connect_subsumer_m7", "full_fwd_collect_sort_m7", "full_forward_sub_m7",
    "full_bve_collect_m7", "full_forward_sub", "full_bve_collect", "full_bve_mark_and_m7",
    "full_bve_find_equiv_m7", "full_bve_find_and_m7", "full_bve_get_tern_m7",
    "full_bve_match_tern_m7", "full_bve_find_ite_side_m7", "full_bve_find_ite_m7",
    "full_bve_xor_pat_m7", "full_bve_find_xor_m7", "full_k6_watch_m7",
    "full_k6_assign_m7", "full_k6_mtf_m7", "full_k6_backtrack_m7", "full_k6_prop_m7",
    "full_k6_ana_cl_m7", "full_k6_analyze_m7", "full_k6_solve_m7", "full_k6_core_m7",
    "full_bve_def_k6_m7", "full_bve_gates_m7", "full_bve_var_m7", "full_bve_var",
    "full_bve_var_key_m7", "full_bve_heap_up_m7", "full_bve_heap_down_m7",
    "full_bve_heap_push_m7", "full_bve_heap_pop_m7", "full_bve_collect_nbrs_m7",
    "full_elim_bve_m7", "full_eliminate_m7", "full_eliminate_m6" ]
#guard (ppTModule m7BveGatesModule).isOk
#guard (PrintQbe.module m7BveGatesModule).isOk
#guard (ppModule (m7BveAllFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7BveAllFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7BveAllFns.map (Fn.legal .x64AVX2))).isOk

end LeanQbeTest.T.KissatM7BveGatesTailTest

/-! ## 2. Short Root-Namespace Audit Theorems & Single-Line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM7BveGates

theorem tBveWf : AllFns Fn.Wf m7BveAllFns :=
  m7BveAllFns_wf

theorem tBveAcyc : m7BveGatesModule.checkAcyclic = true :=
  m7BveGatesModule_acyclic

theorem tBveSigs :
    m7BveAllSpecTable.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig :=
  m7BveAllSpecTable_sigs

theorem tBveSolveWp (Γ : Env)
    (hProp : ∀ a m Q X, fullK6PropM7Spec a m Q X →
      Γ "full_k6_prop_m7" [i64] [i32] a m Q X)
    (hAssign : ∀ a m Q X, fullK6AssignM7Spec a m Q X →
      Γ "full_k6_assign_m7" [i64, i32, i32] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullK6BacktrackM7Spec a m Q X →
      Γ "full_k6_backtrack_m7" [i64, i32] [] a m Q X)
    (hAnalyze : ∀ a m Q X, fullK6AnalyzeM7Spec a m Q X →
      Γ "full_k6_analyze_m7" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullK6SolveM7Spec a m Q X →
      Func.wp Γ full_k6_solve_m7_body a m Q X :=
  full_k6_solve_m7_wp Γ hProp hAssign hBacktrack hAnalyze

theorem tBveDefK6Wp (Γ : Env)
    (hWatch : ∀ a m Q X, fullK6WatchM7Spec a m Q X →
      Γ "full_k6_watch_m7" [i64, i32, i32, i32, i32] [] a m Q X)
    (hSolve : ∀ a m Q X, fullK6SolveM7Spec a m Q X →
      Γ "full_k6_solve_m7" [i64, i64, i32] [i64] a m Q X)
    (hCore : ∀ a m Q X, fullK6CoreM7Spec a m Q X →
      Γ "full_k6_core_m7" [i64] [] a m Q X) :
    ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Func.wp Γ full_bve_def_k6_m7_body a m Q X :=
  full_bve_def_k6_m7_wp Γ hWatch hSolve hCore

theorem tBveGatesWp (Γ : Env)
    (hEquiv : ∀ a m Q X, fullBveFindEquivM7Spec a m Q X →
      Γ "full_bve_find_equiv_m7" [i64, i32, i32] [.bool] a m Q X)
    (hAnd : ∀ a m Q X, fullBveFindAndM7Spec a m Q X →
      Γ "full_bve_find_and_m7" [i64, i32, i32, i32] [.bool] a m Q X)
    (hIte : ∀ a m Q X, fullBveFindIteM7Spec a m Q X →
      Γ "full_bve_find_ite_m7" [i64, i32, i32, i32] [.bool] a m Q X)
    (hXor : ∀ a m Q X, fullBveFindXorM7Spec a m Q X →
      Γ "full_bve_find_xor_m7" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefK6 : ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Γ "full_bve_def_k6_m7" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Func.wp Γ full_bve_gates_m7_body a m Q X :=
  full_bve_gates_m7_wp Γ hEquiv hAnd hIte hXor hDefK6

theorem tBveAllImpl {tbl : List SpecEntry}
    (hNodup : (tbl.map SpecEntry.name).Nodup)
    (hSub : ∀ e ∈ m7BveClosedSpecTable, e ∈ tbl) :
    TableImpl (Env.ofTable tbl) m7BveAllFns m7BveAllSpecTable :=
  m7BveAll_tableImpl hNodup hSub

theorem tBveElimSound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {initial : Bool} {m : Mem 64}
    (hinv : FullSparseInv c F0 s) (hlvl : s.core.cur_level = 0) (hm : (FullMem c s ⋆ R) m) :
    Func.wp m7BveAllEnv full_eliminate_m7_body (c.hdr, initial, ()) m
      (fun (r, ()) m' => ∃ s',
        FullSparseInv c F0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → F0.Unsat) ∧ (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  full_eliminate_m7_unsat_sound hinv hlvl hm

theorem tBveNvSolve :
    Func.wp m7BveAllEnv full_k6_solve_m7_body
      (FullM4Sweep.nvM4SweepCfg.hdr, FullM4Sweep.nvM4SweepCfg.pScratchBuf + 1096#64 * 4#64,
        10#32, ())
      FullM4Sweep.nvM4SweepMem
      (fun (_, ()) m' => ∃ (hdr' : List (BitVec 64)) (kbuf' : List (BitVec 32)),
        K6BufOk kbuf' ∧ nvOneLitF0.Unsat ∧
        ∃ R', (array64 (FullM4Sweep.nvM4SweepCfg.hdr + 32) hdr' ⋆
          array (t := i32) (FullM4Sweep.nvM4SweepCfg.pScratchBuf + 1096#64 * 4#64) kbuf' ⋆ R') m')
      (fun _ _ _ _ => False) :=
  nv_m7_k6_solve

theorem tBveNvDefK6 :
    Func.wp m7BveAllEnv full_bve_def_k6_m7_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, 0#32, 0#32, ()) FullM4Sweep.nvM4SweepMem
      (fun () m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_bve_def_k6

theorem tBveNvGates :
    Func.wp m7BveAllEnv full_bve_gates_m7_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, 0#32, 0#32, ()) FullM4Sweep.nvM4SweepMem
      (fun () m' => ∃ s',
        FullDenseInvW FullM4Sweep.nvM4SweepCfg nvOneLitF0 [[0], [1]] s' ∧
        TmkZero s' ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_bve_gates

theorem tBveNvVar :
    Func.wp m7BveAllEnv full_bve_var_m7_body (FullM4Sweep.nvM4SweepCfg.hdr, 0#32, ())
      FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_bve_var

theorem tBveNvElim :
    Func.wp m7BveAllEnv full_eliminate_m7_body (FullM4Sweep.nvM4SweepCfg.hdr, true, ())
      FullM4Sweep.nvM4SweepSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_eliminate

#print axioms tBveWf
#print axioms tBveAcyc
#print axioms tBveSigs
#print axioms tBveSolveWp
#print axioms tBveDefK6Wp
#print axioms tBveGatesWp
#print axioms tBveAllImpl
#print axioms tBveElimSound
#print axioms tBveNvSolve
#print axioms tBveNvDefK6
#print axioms tBveNvGates
#print axioms tBveNvVar
#print axioms tBveNvElim

end AxiomAudit
