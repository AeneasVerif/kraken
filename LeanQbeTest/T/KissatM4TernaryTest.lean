module

public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
meta import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for `FullM4Ternary` (`14/14`)

1. Executable `#guard` checks on `full_m4_ternary_fns` (`14` functions), `fullM4TernaryExterns`
   (`6` externs), `fullM4TernaryModule.checkAcyclic`, `m4TernarySpecTable` (`20` rows, all
   `noExit = true`), and `nvM4TernaryBytes.length == nvM4TernaryCfg.avail` (`2128`).
2. Short root-namespace `m4t_*` audit theorems + single-line `#print axioms` audit.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM4TernaryTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM4Ternary

/-! ## 1. Executable `#guard` sanity checks -/

#guard full_m4_ternary_fns.length == 14
#guard fullM4TernaryModule.externs.length == 6
#guard fullM4TernaryModule.checkAcyclic == true
#guard m4TernarySpecTable.length == 20
#guard (m4TernarySpecTable.all fun e => e.noExit) == true
#guard full_m4_ternary_fns.map Fn.name ==
  [ "full_compute_lbd", "full_promote_clause", "full_promote_reasons",
    "full_score_sift", "full_reorder_queue", "full_reorder_heap",
    "full_tumble_clause", "full_tumble_clauses", "full_reorder",
    "full_ternary_match_bin", "full_ternary_collect", "full_ternary_resolve_bin",
    "full_ternary_round", "full_ternary" ]
#guard (full_m4_ternary_fns.map fun f => (f.name, f.as.length, f.rs.length)) ==
  [ ("full_compute_lbd", 2, 1), ("full_promote_clause", 2, 1),
    ("full_promote_reasons", 1, 1), ("full_score_sift", 3, 0),
    ("full_reorder_queue", 1, 1), ("full_reorder_heap", 1, 1),
    ("full_tumble_clause", 2, 1), ("full_tumble_clauses", 2, 1),
    ("full_reorder", 2, 1), ("full_ternary_match_bin", 6, 1),
    ("full_ternary_collect", 2, 1), ("full_ternary_resolve_bin", 3, 1),
    ("full_ternary_round", 3, 1), ("full_ternary", 3, 1) ]
#guard nvM4TernaryBytes.length == nvM4TernaryCfg.avail

end LeanQbeTest.T.KissatM4TernaryTest

/-! ## 2. Short root-namespace audit theorems & single-line `#print axioms` -/

section AxiomAudit

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Ternary

theorem m4t_fns_wf : ∀ f ∈ full_m4_ternary_fns, f.Wf := full_m4_ternary_fns_wf
theorem m4t_acyclic : fullM4TernaryModule.checkAcyclic = true := fullM4Ternary_acyclic
theorem m4t_noExit : ∀ e ∈ m4TernarySpecTable, e.noExit = true := m4TernarySpecTable_noExit
theorem m4t_sigs :
    (m4TernarySpecTable.take 14).map (fun e => (e.name, e.as, e.rs)) =
      full_m4_ternary_fns.map (fun f => (f.name, f.as, f.rs)) :=
  m4TernarySpecTable_sigs
theorem m4t_ext_sigs :
    (m4TernarySpecTable.drop 14).map (fun e => ⟨e.name, e.as, e.rs⟩) = fullM4TernaryExterns :=
  m4TernarySpecTable_ext_sigs

theorem m4t_lbd_wp (Γ : Env) :
    ∀ a m Q X, fullComputeLbdSpec a m Q X → Func.wp Γ full_compute_lbd_body a m Q X :=
  full_compute_lbd_wp Γ

theorem m4t_prom_cl_wp (Γ : Env) (hL : EnvSpec Γ "full_compute_lbd" fullComputeLbdSpec) :
    ∀ a m Q X, fullPromoteClauseSpec a m Q X → Func.wp Γ full_promote_clause_body a m Q X :=
  full_promote_clause_wp Γ hL

theorem m4t_prom_rsn_wp (Γ : Env) (hP : EnvSpec Γ "full_promote_clause" fullPromoteClauseSpec) :
    ∀ a m Q X, fullPromoteReasonsSpec a m Q X → Func.wp Γ full_promote_reasons_body a m Q X :=
  full_promote_reasons_wp Γ hP

theorem m4t_sift_wp (Γ : Env) :
    ∀ a m Q X, fullScoreSiftSpec a m Q X → Func.wp Γ full_score_sift_body a m Q X :=
  full_score_sift_wp Γ

theorem m4t_reord_q_wp (Γ : Env) (hS : EnvSpec Γ "full_score_sift" fullScoreSiftSpec) :
    ∀ a m Q X, fullReorderQueueSpec a m Q X → Func.wp Γ full_reorder_queue_body a m Q X :=
  full_reorder_queue_wp Γ hS

theorem m4t_reord_h_wp (Γ : Env) (hP : EnvSpec Γ "full_heap_push" Full.fullHeapPushSpec) :
    ∀ a m Q X, fullReorderHeapSpec a m Q X → Func.wp Γ full_reorder_heap_body a m Q X :=
  full_reorder_heap_wp Γ hP

theorem m4t_tumble_cl_wp (Γ : Env) (hR : EnvSpec Γ "full_rng_next" Full.fullRngNextSpec) :
    ∀ a m Q X, fullTumbleClauseSpec a m Q X → Func.wp Γ full_tumble_clause_body a m Q X :=
  full_tumble_clause_wp Γ hR

theorem m4t_tumble_all_wp (Γ : Env)
    (hN : EnvSpec Γ "full_arena_next" Full.fullArenaNextSpec)
    (hT : EnvSpec Γ "full_tumble_clause" fullTumbleClauseSpec) :
    ∀ a m Q X, fullTumbleClausesSpec a m Q X → Func.wp Γ full_tumble_clauses_body a m Q X :=
  full_tumble_clauses_wp Γ hN hT

theorem m4t_reord_wp (Γ : Env)
    (hQ : EnvSpec Γ "full_reorder_queue" fullReorderQueueSpec)
    (hH : EnvSpec Γ "full_reorder_heap" fullReorderHeapSpec)
    (hT : EnvSpec Γ "full_tumble_clauses" fullTumbleClausesSpec) :
    ∀ a m Q X, fullReorderSpec a m Q X → Func.wp Γ full_reorder_body a m Q X :=
  full_reorder_wp Γ hQ hH hT

theorem m4t_match_wp (Γ : Env) :
    ∀ a m Q X, fullTernaryMatchBinSpec a m Q X → Func.wp Γ full_ternary_match_bin_body a m Q X :=
  full_ternary_match_bin_wp Γ

theorem m4t_collect_wp (Γ : Env) (hN : EnvSpec Γ "full_arena_next" Full.fullArenaNextSpec) :
    ∀ a m Q X, fullTernaryCollectSpec a m Q X → Func.wp Γ full_ternary_collect_body a m Q X :=
  full_ternary_collect_wp Γ hN

theorem m4t_resolve_wp (Γ : Env)
    (hM : EnvSpec Γ "full_ternary_match_bin" fullTernaryMatchBinSpec)
    (hB : EnvSpec Γ "full_add_bin" Full.fullAddBinSpec) :
    ∀ a m Q X, fullTernaryResolveBinSpec a m Q X →
      Func.wp Γ full_ternary_resolve_bin_body a m Q X :=
  full_ternary_resolve_bin_wp Γ hM hB

theorem m4t_round_wp (Γ : Env)
    (hR : EnvSpec Γ "full_ternary_resolve_bin" fullTernaryResolveBinSpec)
    (hP : EnvSpec Γ "full_propagate" Full.fullPropagateSpec) :
    ∀ a m Q X, fullTernaryRoundSpec a m Q X → Func.wp Γ full_ternary_round_body a m Q X :=
  full_ternary_round_wp Γ hR hP

theorem m4t_ternary_wp (Γ : Env)
    (hB : EnvSpec Γ "full_backtrack" Full.fullBacktrackSpec)
    (hP : EnvSpec Γ "full_propagate" Full.fullPropagateSpec)
    (hC : EnvSpec Γ "full_ternary_collect" fullTernaryCollectSpec)
    (hR : EnvSpec Γ "full_ternary_round" fullTernaryRoundSpec) :
    ∀ a m Q X, fullTernarySpec a m Q X → Func.wp Γ full_ternary_body a m Q X :=
  full_ternary_wp Γ hB hP hC hR

theorem m4t_env_noExit :
    ∀ f as bs xs m Q X X',
      m4TernaryEnv f as bs xs m Q X → m4TernaryEnv f as bs xs m Q X' :=
  m4TernaryEnv_noExit

theorem m4t_moduleOk : ModuleOk m4TernaryEnv fullM4TernaryModule := m4TernaryEnv_moduleOk

theorem m4t_nv_mem_ok : FullMem nvM4TernaryCfg nvM4TernaryState nvM4TernaryMem :=
  nvM4TernaryMem_ok

theorem m4t_nv_prom_cl :
    Func.wp m4TernaryEnv full_promote_clause_body (nvM4TernaryCfg.hdr, 0#32, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ ar' ws2' gu',
        let s' : FullState :=
          { core := { nvM4TernaryState.core with arena := ar' }
            scratch := { nvM4TernaryState.scratch with work_stk2 := ws2', glue_used := gu' } }
        FullSparseInvW nvM4TernaryCfg nvM4TernaryF0 nvM4TernaryClauses s' ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_promote_clause

theorem m4t_nv_prom_rsn :
    Func.wp m4TernaryEnv full_promote_reasons_body (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ ar' ws2' gu',
        let s' : FullState :=
          { core := { nvM4TernaryState.core with arena := ar' }
            scratch := { nvM4TernaryState.scratch with work_stk2 := ws2', glue_used := gu' } }
        FullSparseInv nvM4TernaryCfg nvM4TernaryF0 s' ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_promote_reasons

theorem m4t_nv_reord :
    Func.wp m4TernaryEnv full_reorder_body (nvM4TernaryCfg.hdr, 10#64, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ s',
        FullSparseInv nvM4TernaryCfg nvM4TernaryF0 s' ∧
        FullArenaPermEq nvM4TernaryState.core s'.core ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_reorder

theorem m4t_nv_resolve :
    Func.wp m4TernaryEnv full_ternary_resolve_bin_body
      (nvM4TernaryCfg.hdr, 0#32, 6#32, ()) nvM4TernaryMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM4TernaryCfg nvM4TernaryF0 nvM4TernaryClauses s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_ternary_resolve_bin

theorem m4t_nv_ternary :
    Func.wp m4TernaryEnv full_ternary_body (nvM4TernaryCfg.hdr, 2#64, 16#64, ()) nvM4TernaryMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM4TernaryCfg nvM4TernaryF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_ternary

#print axioms m4t_fns_wf
#print axioms m4t_acyclic
#print axioms m4t_noExit
#print axioms m4t_sigs
#print axioms m4t_ext_sigs
#print axioms m4t_lbd_wp
#print axioms m4t_prom_cl_wp
#print axioms m4t_prom_rsn_wp
#print axioms m4t_sift_wp
#print axioms m4t_reord_q_wp
#print axioms m4t_reord_h_wp
#print axioms m4t_tumble_cl_wp
#print axioms m4t_tumble_all_wp
#print axioms m4t_reord_wp
#print axioms m4t_match_wp
#print axioms m4t_collect_wp
#print axioms m4t_resolve_wp
#print axioms m4t_round_wp
#print axioms m4t_ternary_wp
#print axioms m4t_env_noExit
#print axioms m4t_moduleOk
#print axioms m4t_nv_mem_ok
#print axioms m4t_nv_prom_cl
#print axioms m4t_nv_prom_rsn
#print axioms m4t_nv_reord
#print axioms m4t_nv_resolve
#print axioms m4t_nv_ternary

end AxiomAudit
