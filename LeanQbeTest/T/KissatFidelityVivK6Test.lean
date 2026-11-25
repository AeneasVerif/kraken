/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0a
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof1a
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof1b
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof2
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
meta import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for `FullFidelityVivK6`

Covers `GAP-VIV-01/02` (dynamic vivify schedule cap + active-tier budget normalization),
`G1-P2.1b` (alignment-safe `u64`/`u32` copy loops in `full_unwatch_large_fid` &
`full_bva_commit_fid`), and `G1-P2.1c` (cached 8-pointer Kitten state in `full_k6_propagate_fid`
& `full_k6_core_m8_fid`):
1. Executable `#guard` checks on `fidVivK6Module` (`10` fns, `17` externs, `0` exits),
   `fidVivK6SplicedModule` (`473` fns, `0` externs, `0` exits),
   `fidVivK6NoBvaCommitSplicedModule` (`473` fns, `0` externs, `0` exits), `PrintCpp`, `PrintQbe`,
   and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Restated headline theorems covering all `10` parametric `Func.wp` proofs, closed `473/473`
   `TableImpl`/`ModuleOk`, UNSAT soundness + host frame lift (`XPost := False`), and genuine
   non-bailout concrete `Mem 64` UNSAT non-vacuity witnesses (`nv_fid_unwatch_large`,
   `nv_fid_vivify_delayed_irr`, `nv_fid_k6_propagate`, `nv_fid_k6_core_m8`, `*_unsat_nv`).
3. Single-line `<= 100`c `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityVivK6Test

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullM4Bva
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.PatchModule
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard fidVivK6Fns.length == 10
#guard fidVivHelpers.length == 4
#guard fidVivK6Repls.length == 6
#guard fidVivK6NoBvaCommitRepls.length == 5
#guard fidVivK6Module.fns.length == 10
#guard fidVivK6Module.externs.length == 17
#guard fidVivK6Module.exits.isEmpty == true
#guard fidVivK6Module.checkAcyclic == true
#guard fidVivK6SplicedFns.length == 473
#guard (fidVivK6SplicedFns.map Fn.name).eraseDups.length == 473
#guard fidVivK6SplicedModule.checkAcyclic == true
#guard fidVivK6SplicedModule.externs.isEmpty == true
#guard fidVivK6SplicedModule.exits.isEmpty == true
#guard fidVivK6NoBvaCommitSplicedFns.length == 473
#guard (fidVivK6NoBvaCommitSplicedFns.map Fn.name).eraseDups.length == 473
#guard fidVivK6NoBvaCommitSplicedModule.checkAcyclic == true
#guard fidVivK6NoBvaCommitSplicedModule.externs.isEmpty == true
#guard fidVivK6NoBvaCommitSplicedModule.exits.isEmpty == true
#guard fidVivK6SpecTable.length == 473
#guard fidVivK6NoBvaCommitSpecTable.length == 473
#guard fidVivK6Bundle.frontTable.length == 10
#guard fidVivK6SpecTable.all (·.noExit) == true
#guard fidVivK6NoBvaCommitSpecTable.all (·.noExit) == true
#guard (ppTModule fidVivK6Module).isOk
#guard (PrintQbe.module fidVivK6Module).isOk
#guard (ppTModule fidVivK6SplicedModule).isOk
#guard (ppTModule fidVivK6NoBvaCommitSplicedModule).isOk
#guard (ppModule (fidVivK6Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidVivK6Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidVivK6Fns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (fidVivK6Fns.map (Fn.legal .x64AVX512))).isOk
#guard fidVivK6Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidVivK6Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidVivK6Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidVivK6Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem fvk_repls_wf : ∀ r ∈ fidVivK6Repls, r.Wf := fidVivK6Repls_wf
theorem fvk_nb_repls_wf : ∀ r ∈ fidVivK6NoBvaCommitRepls, r.Wf := fidVivK6NoBvaCommitRepls_wf
theorem fvk_helpers_wf : ∀ h ∈ fidVivHelpers, h.Wf := fidVivHelpers_wf
theorem fvk_fns_wf : ∀ f ∈ fidVivK6Fns, f.Wf := fidVivK6Fns_wf
theorem fvk_acyc : fidVivK6Module.checkAcyclic = true := fidVivK6_acyclic
theorem fvk_spl_len : fidVivK6SplicedModule.fns.length = 473 := fidVivK6Spliced_length
theorem fvk_spl_wf : ∀ f ∈ fidVivK6SplicedModule.fns, f.Wf := fidVivK6Spliced_wf
theorem fvk_spl_no_exit : fidVivK6SplicedModule.exits = [] := fidVivK6Spliced_noExit
theorem fvk_spl_acyc : fidVivK6SplicedModule.checkAcyclic = true := fidVivK6Spliced_acyclic
theorem fvk_nb_len : fidVivK6NoBvaCommitSplicedModule.fns.length = 473 :=
  fidVivK6NoBvaCommitSpliced_length
theorem fvk_nb_wf : ∀ f ∈ fidVivK6NoBvaCommitSplicedModule.fns, f.Wf :=
  fidVivK6NoBvaCommit_wf
theorem fvk_nb_no_exit : fidVivK6NoBvaCommitSplicedModule.exits = [] :=
  fidVivK6NoBvaCommitSpliced_noExit
theorem fvk_nb_acyc : fidVivK6NoBvaCommitSplicedModule.checkAcyclic = true :=
  fidVivK6NoBvaCommit_acyclic

theorem fvk_unwatch_large_wp (Γ : Env) :
    ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Func.wp Γ full_unwatch_large_fid_body a m Q X :=
  full_unwatch_large_fid_wp Γ

theorem fvk_bva_commit_wp (Γ : Env)
    (hDef : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hInit : ∀ a m Q X, fullInitFreshVarHeapSpec a m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] a m Q X)
    (hBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWatch : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDel : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, m4BvaCommitSpec a m Q X → Func.wp Γ full_bva_commit_fid_body a m Q X :=
  full_bva_commit_fid_wp Γ hDef hInit hBin hAlloc hWatch hDel hUnw

theorem fvk_viv_collect_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hMatch : ∀ a m Q X, fullVivTierMatchM6Spec a m Q X →
      Γ "full_viv_tier_match_m6" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullVivCollectFidSpec a m Q X → Func.wp Γ full_viv_collect_fid_body a m Q X :=
  full_viv_collect_fid_wp Γ hNext hMatch

theorem fvk_viv_count_wp (Γ : Env) :
    ∀ a m Q X, fullVivCountFidSpec a m Q X → Func.wp Γ full_viv_count_fid_body a m Q X :=
  full_viv_count_fid_wp Γ

theorem fvk_viv_sort2_wp (Γ : Env) :
    ∀ a m Q X, fullVivSort2FidSpec a m Q X → Func.wp Γ full_viv_sort2_fid_body a m Q X :=
  full_viv_sort2_fid_wp Γ

theorem fvk_viv_sort_wp (Γ : Env)
    (hS2 : ∀ a m Q X, fullVivSort2FidSpec a m Q X →
      Γ "full_viv_sort2_fid" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullVivSortFidSpec a m Q X → Func.wp Γ full_viv_sort_fid_body a m Q X :=
  full_viv_sort_fid_wp Γ hS2

theorem fvk_vivify_tier_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCol : ∀ a m Q X, fullVivCollectFidSpec a m Q X →
      Γ "full_viv_collect_fid" [i64, i64] [i64] a m Q X)
    (hCnt : ∀ a m Q X, fullVivCountFidSpec a m Q X →
      Γ "full_viv_count_fid" [i64, i64] [] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortFidSpec a m Q X →
      Γ "full_viv_sort_fid" [i64, i64] [] a m Q X)
    (hCl : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hClr : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Func.wp Γ full_vivify_tier_m6_hdr_fid_body a m Q X :=
  full_vivify_tier_m6_hdr_fid_wp Γ hBt hCol hCnt hSort hCl hProp hClr

theorem fvk_vivify_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hDel : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hTier : ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X)
    (hBmp : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hRed : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6aVivifySpec a m Q X → Func.wp Γ full_vivify_m6_hdr_fid_body a m Q X :=
  full_vivify_m6_hdr_fid_wp Γ hBt hSync hDel hWm hTier hBmp hRed

theorem fvk_k6_prop_wp (Γ : Env) :
    ∀ a m Q X, k6PropagateSpec a m Q X → Func.wp Γ full_k6_propagate_fid_body a m Q X :=
  full_k6_propagate_fid_wp Γ

theorem fvk_k6_core_wp (Γ : Env) :
    ∀ a m Q X, m8K6CoreSpec a m Q X → Func.wp Γ full_k6_core_m8_fid_body a m Q X :=
  full_k6_core_m8_fid_wp Γ

theorem fvk_spl_tbl : TableImpl fidVivK6Env fidVivK6SplicedFns fidVivK6SpecTable :=
  fidVivK6Spliced_tableImpl

theorem fvk_spl_mod_ok : ModuleOk fidVivK6Env fidVivK6SplicedModule :=
  fidVivK6Spliced_moduleOk

theorem fvk_nb_tbl :
    TableImpl fidVivK6NoBvaCommitEnv fidVivK6NoBvaCommitSplicedFns fidVivK6NoBvaCommitSpecTable :=
  fidVivK6NoBvaCommit_tableImpl

theorem fvk_nb_mod_ok :
    ModuleOk fidVivK6NoBvaCommitEnv fidVivK6NoBvaCommitSplicedModule :=
  fidVivK6NoBvaCommit_moduleOk

theorem fvk_spl_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidVivK6Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidVivK6Spliced_solve_bytes_sound hcfit hwfit hm

theorem fvk_spl_solve_host
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {m_dmem : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) m_dmem) :
    ∃ m0, (Eq m0 ⋆ F_host) m_dmem ∧
      Func.wp fidVivK6Env FullM6Orch.kissat_solve_bytes_body
        (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m0
        (fun rs m' =>
          match rs with
          | (r, ()) => ∀ st_dmem, (Eq m' ⋆ F_host) st_dmem →
            (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
            (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem)
        (fun _ _ _ _ => False) :=
  fidVivK6Spliced_solve_bytes_host_sound hcfit hwfit hm

theorem fvk_nb_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidVivK6NoBvaCommitEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidVivK6NoBvaCommit_solve_bytes_sound hcfit hwfit hm

theorem fvk_nb_solve_host
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {m_dmem : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) m_dmem) :
    ∃ m0, (Eq m0 ⋆ F_host) m_dmem ∧
      Func.wp fidVivK6NoBvaCommitEnv FullM6Orch.kissat_solve_bytes_body
        (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m0
        (fun rs m' =>
          match rs with
          | (r, ()) => ∀ st_dmem, (Eq m' ⋆ F_host) st_dmem →
            (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
            (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem)
        (fun _ _ _ _ => False) :=
  fidVivK6NoBvaCommit_solve_bytes_host_sound hcfit hwfit hm

theorem fvk_spl_unsat_nv :
    Func.wp fidVivK6Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidVivK6Spliced_unsat_nv

theorem fvk_nb_unsat_nv :
    Func.wp fidVivK6NoBvaCommitEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidVivK6NoBvaCommit_unsat_nv

theorem fvk_nv_unwatch :
    Func.wp fidVivK6Env full_unwatch_large_fid_body (nvUwCfg.hdr, 0#32, 42#32, ()) nvUwMem
      (fun _ m' => ∃ s', s'.LengthsOk nvUwCfg ∧ WatchStackLayout s'.core ∧
        s'.core.cur_vars = 4 ∧ FullMem nvUwCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_unwatch_large

theorem fvk_nv_viv_irr :
    Func.wp fidVivK6Env full_vivify_m6_hdr_fid_body (nvM6Cfg.hdr, ()) nvFidVivMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ (r = 1#64 ∨ r = 20#64) ∧
        FullSparseInv nvM6Cfg nvM6F0 s' ∧ nvM6F0.Unsat ∧ FullM6HdrMem nvM6Cfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_vivify_delayed_irr

theorem fvk_nv_k6_prop :
    Func.wp fidVivK6Env full_k6_propagate_fid_body (8192#64, ()) nvK6PropMem
      (fun (confl, ()) m' => ∃ ks', confl = 4294967295#32 ∧ K6Inv nvM6K6Layout nvK6PropP ks' ∧
        K6TrailSynced ks' ∧ ks'.prop = ks'.trl_end ∧ 1 ≤ ks'.trl_end.toNat ∧
        K6Mem nvM6K6Layout 8192#64 ks' m')
      (fun _ _ _ _ => False) :=
  nv_fid_k6_propagate

theorem fvk_nv_k6_core :
    Func.wp fidVivK6Env full_k6_core_m8_fid_body (nvM4SweepCfg.hdr, ()) nvFidK6CoreMem
      (fun _ m' => ∃ scr', scr'.length = nvM4SweepCfg.scratch_cap ∧ M8K6BufOk scr' ∧
        FullMem nvM4SweepCfg
          { nvM6SweepState with scratch := { nvM6SweepState.scratch with scratch_buf := scr' } }
          m')
      (fun _ _ _ _ => False) :=
  nv_fid_k6_core_m8

end LeanQbeTest.T.KissatFidelityVivK6Test

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev fvk_t_rwf := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_repls_wf
abbrev fvk_t_nbr := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_repls_wf
abbrev fvk_t_hwf := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_helpers_wf
abbrev fvk_t_fwf := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_fns_wf
abbrev fvk_t_acyc := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_acyc
abbrev fvk_t_slen := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_len
abbrev fvk_t_swf := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_wf
abbrev fvk_t_sno := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_no_exit
abbrev fvk_t_sacyc := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_acyc
abbrev fvk_t_nblen := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_len
abbrev fvk_t_nbwf := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_wf
abbrev fvk_t_nbno := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_no_exit
abbrev fvk_t_nbacyc := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_acyc
abbrev fvk_t_unw := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_unwatch_large_wp
abbrev fvk_t_bva := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_bva_commit_wp
abbrev fvk_t_col := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_viv_collect_wp
abbrev fvk_t_cnt := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_viv_count_wp
abbrev fvk_t_s2 := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_viv_sort2_wp
abbrev fvk_t_srt := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_viv_sort_wp
abbrev fvk_t_tier := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_vivify_tier_wp
abbrev fvk_t_viv := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_vivify_wp
abbrev fvk_t_k6p := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_k6_prop_wp
abbrev fvk_t_k6c := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_k6_core_wp
abbrev fvk_t_stbl := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_tbl
abbrev fvk_t_smod := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_mod_ok
abbrev fvk_t_nbtbl := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_tbl
abbrev fvk_t_nbmod := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_mod_ok
abbrev fvk_t_sb := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_solve_sound
abbrev fvk_t_host := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_solve_host
abbrev fvk_t_nbsb := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_solve_sound
abbrev fvk_t_nbhost := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_solve_host
abbrev fvk_t_nv := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_spl_unsat_nv
abbrev fvk_t_nbnv := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nb_unsat_nv
abbrev fvk_t_nv_unw := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nv_unwatch
abbrev fvk_t_nv_viv := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nv_viv_irr
abbrev fvk_t_nv_k6p := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nv_k6_prop
abbrev fvk_t_nv_k6c := @LeanQbeTest.T.KissatFidelityVivK6Test.fvk_nv_k6_core

#print axioms fvk_t_rwf
#print axioms fvk_t_nbr
#print axioms fvk_t_hwf
#print axioms fvk_t_fwf
#print axioms fvk_t_acyc
#print axioms fvk_t_slen
#print axioms fvk_t_swf
#print axioms fvk_t_sno
#print axioms fvk_t_sacyc
#print axioms fvk_t_nblen
#print axioms fvk_t_nbwf
#print axioms fvk_t_nbno
#print axioms fvk_t_nbacyc
#print axioms fvk_t_unw
#print axioms fvk_t_bva
#print axioms fvk_t_col
#print axioms fvk_t_cnt
#print axioms fvk_t_s2
#print axioms fvk_t_srt
#print axioms fvk_t_tier
#print axioms fvk_t_viv
#print axioms fvk_t_k6p
#print axioms fvk_t_k6c
#print axioms fvk_t_stbl
#print axioms fvk_t_smod
#print axioms fvk_t_nbtbl
#print axioms fvk_t_nbmod
#print axioms fvk_t_sb
#print axioms fvk_t_host
#print axioms fvk_t_nbsb
#print axioms fvk_t_nbhost
#print axioms fvk_t_nv
#print axioms fvk_t_nbnv
#print axioms fvk_t_nv_unw
#print axioms fvk_t_nv_viv
#print axioms fvk_t_nv_k6p
#print axioms fvk_t_nv_k6c
