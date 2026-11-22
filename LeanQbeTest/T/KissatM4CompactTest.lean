/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM4CompactProof
meta import LeanQbe.T.Examples.Kissat.FullM4CompactProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for `FullM4Compact` (`13/13`)

1. Executable `#guard` checks on `compact_fns` (`13` functions), `fullM4CompactExterns`
   (`7` externs), `compactModule.checkAcyclic`, `compactSpecTable` (`20` rows, all
   `noExit = true`), and `nvCompactBytes.length == nvCompactCfg.avail` (`1972`).
2. Short root-namespace `kmc_*` audit theorems + single-line `#print axioms` (`<= 100` cols,
   every `depends on axioms: [...]` output `< 115` chars on one line).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM4CompactTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM4Compact

/-! ## 1. Executable `#guard` sanity checks -/

#guard compact_fns.length == 13
#guard compactModule.externs.length == 7
#guard compactModule.checkAcyclic == true
#guard compactSpecTable.length == 20
#guard (compactSpecTable.all fun e => e.noExit) == true
#guard compact_fns.map Fn.name ==
  [ "full_compact_needed", "full_compact_flush", "full_compact_mark_live",
    "full_compact_assign_map", "full_compact_record_ext", "full_compact_bins",
    "full_compact_arena", "full_compact_vars", "full_compact_sift_q",
    "full_compact_vmtf", "full_compact_sift_h", "full_compact_heap", "full_compact" ]
#guard (compact_fns.map fun f => (f.name, f.as.length, f.rs.length)) ==
  [ ("full_compact_needed", 1, 1), ("full_compact_flush", 1, 1),
    ("full_compact_mark_live", 1, 0), ("full_compact_assign_map", 1, 1),
    ("full_compact_record_ext", 3, 0), ("full_compact_bins", 3, 0),
    ("full_compact_arena", 2, 1), ("full_compact_vars", 3, 0),
    ("full_compact_sift_q", 4, 0), ("full_compact_vmtf", 2, 0),
    ("full_compact_sift_h", 5, 0), ("full_compact_heap", 2, 0),
    ("full_compact", 1, 1) ]
#guard nvCompactBytes.length == nvCompactCfg.avail

end LeanQbeTest.T.KissatM4CompactTest

/-! ## 2. Short root-namespace audit theorems & single-line `#print axioms` -/

section AxiomAudit

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Compact

theorem kmc_fns_wf : ∀ f ∈ compact_fns, f.Wf := compact_fns_wf

theorem kmc_acyclic : compactModule.checkAcyclic = true := compactModule_acyclic

theorem kmc_noExit : ∀ e ∈ compactSpecTable, e.noExit = true := compactSpecTable_noExit

theorem kmc_sigs :
    (compactSpecTable.take 13).map (fun e => (e.name, e.as, e.rs)) =
      compact_fns.map (fun f => (f.name, f.as, f.rs)) :=
  compactSpecTable_sigs

theorem kmc_ext_sigs :
    (compactSpecTable.drop 13).map (fun e => ⟨e.name, e.as, e.rs⟩) = fullM4CompactExterns :=
  compactSpecTable_ext_sigs

theorem kmc_needed_wp (Γ : Env) :
    ∀ a m Q X, fullCompactNeededSpec a m Q X → Func.wp Γ full_compact_needed_body a m Q X :=
  full_compact_needed_wp Γ

theorem kmc_flush_wp (Γ : Env)
    (hbt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hprop : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hsweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCompactFlushSpec a m Q X → Func.wp Γ full_compact_flush_body a m Q X :=
  full_compact_flush_wp Γ hbt hprop hsweep

theorem kmc_mark_live_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullCompactMarkLiveSpec a m Q X →
      Func.wp Γ full_compact_mark_live_body a m Q X :=
  full_compact_mark_live_wp Γ hnext

theorem kmc_assign_map_wp (Γ : Env) :
    ∀ a m Q X, fullCompactAssignMapSpec a m Q X →
      Func.wp Γ full_compact_assign_map_body a m Q X :=
  full_compact_assign_map_wp Γ

theorem kmc_record_ext_wp (Γ : Env) :
    ∀ a m Q X, fullCompactRecordExtSpec a m Q X →
      Func.wp Γ full_compact_record_ext_body a m Q X :=
  full_compact_record_ext_wp Γ

theorem kmc_bins_wp (Γ : Env) :
    ∀ a m Q X, fullCompactBinsSpec a m Q X → Func.wp Γ full_compact_bins_body a m Q X :=
  full_compact_bins_wp Γ

theorem kmc_arena_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullCompactArenaSpec a m Q X → Func.wp Γ full_compact_arena_body a m Q X :=
  full_compact_arena_wp Γ hnext hpush

theorem kmc_vars_wp (Γ : Env) :
    ∀ a m Q X, fullCompactVarsSpec a m Q X → Func.wp Γ full_compact_vars_body a m Q X :=
  full_compact_vars_wp Γ

theorem kmc_sift_q_wp (Γ : Env) :
    ∀ a m Q X, fullCompactSiftQSpec a m Q X → Func.wp Γ full_compact_sift_q_body a m Q X :=
  full_compact_sift_q_wp Γ

theorem kmc_vmtf_wp (Γ : Env)
    (hsift : ∀ a m Q X, fullCompactSiftQSpec a m Q X →
      Γ "full_compact_sift_q" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullCompactVmtfSpec a m Q X → Func.wp Γ full_compact_vmtf_body a m Q X :=
  full_compact_vmtf_wp Γ hsift

theorem kmc_sift_h_wp (Γ : Env) :
    ∀ a m Q X, fullCompactSiftHSpec a m Q X → Func.wp Γ full_compact_sift_h_body a m Q X :=
  full_compact_sift_h_wp Γ

theorem kmc_heap_wp (Γ : Env)
    (hsift : ∀ a m Q X, fullCompactSiftHSpec a m Q X →
      Γ "full_compact_sift_h" [i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullCompactHeapSpec a m Q X → Func.wp Γ full_compact_heap_body a m Q X :=
  full_compact_heap_wp Γ hsift

theorem kmc_full_compact_wp (Γ : Env)
    (hfl : ∀ a m Q X, fullCompactFlushSpec a m Q X → Γ "full_compact_flush" [i64] [i64] a m Q X)
    (hmk : ∀ a m Q X, fullCompactMarkLiveSpec a m Q X → Γ "full_compact_mark_live" [i64] [] a m Q X)
    (hmp : ∀ a m Q X, fullCompactAssignMapSpec a m Q X →
      Γ "full_compact_assign_map" [i64] [i64] a m Q X)
    (hre : ∀ a m Q X, fullCompactRecordExtSpec a m Q X →
      Γ "full_compact_record_ext" [i64, i64, i64] [] a m Q X)
    (hbn : ∀ a m Q X, fullCompactBinsSpec a m Q X →
      Γ "full_compact_bins" [i64, i64, i64] [] a m Q X)
    (hdf : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X)
    (har : ∀ a m Q X, fullCompactArenaSpec a m Q X →
      Γ "full_compact_arena" [i64, i64] [i64] a m Q X)
    (hvr : ∀ a m Q X, fullCompactVarsSpec a m Q X →
      Γ "full_compact_vars" [i64, i64, i64] [] a m Q X)
    (hvm : ∀ a m Q X, fullCompactVmtfSpec a m Q X → Γ "full_compact_vmtf" [i64, i64] [] a m Q X)
    (hhp : ∀ a m Q X, fullCompactHeapSpec a m Q X → Γ "full_compact_heap" [i64, i64] [] a m Q X)
    (hrw : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Γ "full_rewatch_arena" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullCompactSpec a m Q X → Func.wp Γ full_compact_body a m Q X :=
  full_compact_wp Γ hfl hmk hmp hre hbn hdf har hvr hvm hhp hrw

theorem kmc_env_noExit :
    ∀ f as bs xs m Q X X',
      compactEnv f as bs xs m Q X → compactEnv f as bs xs m Q X' :=
  compactEnv_noExit

theorem kmc_moduleOk : ModuleOk compactEnv compactModule := compact_moduleOk

theorem kmc_nv_mem_ok : FullMem nvCompactCfg nvCompactState nvCompactMem := nvCompactMem_ok

theorem kmc_nv_compact :
    Func.wp compactEnv full_compact_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (r, ()) m' => ∃ c' s',
        FullCfgCompat nvCompactCfg c' ∧ FullSparseInv c' nvCompactF0 s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧ nvCompactF0.Unsat ∧ FullMem c' s' m')
      (fun _ _ _ _ => False) :=
  nv_full_compact

theorem kmc_nv_canary10 :
    Func.wp compactEnv full_compact_assign_map_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (ncv, ()) m' => ∃ s',
        ncv.toNat < nvCompactCfg.mv ∧ ncv.toNat ≤ 1 ∧
        CompactBijOk nvCompactState.core.cur_vars ncv.toNat nvCompactState.core.vals
          s'.scratch.work_stk1 s'.scratch.work_stk2 ∧
        FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_compact_canary10

#print axioms kmc_fns_wf
#print axioms kmc_acyclic
#print axioms kmc_noExit
#print axioms kmc_sigs
#print axioms kmc_ext_sigs
#print axioms kmc_needed_wp
#print axioms kmc_flush_wp
#print axioms kmc_mark_live_wp
#print axioms kmc_assign_map_wp
#print axioms kmc_record_ext_wp
#print axioms kmc_bins_wp
#print axioms kmc_arena_wp
#print axioms kmc_vars_wp
#print axioms kmc_sift_q_wp
#print axioms kmc_vmtf_wp
#print axioms kmc_sift_h_wp
#print axioms kmc_heap_wp
#print axioms kmc_full_compact_wp
#print axioms kmc_env_noExit
#print axioms kmc_moduleOk
#print axioms kmc_nv_mem_ok
#print axioms kmc_nv_compact
#print axioms kmc_nv_canary10

end AxiomAudit
