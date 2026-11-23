/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, Splice & Axiom Audit for `FullM7FidelitySearch`

1. Executable `#guard` checks on standalone `fidSearchModule` (`4` fns, `22` externs, `0` exits)
   and `fidSearchSplicedModule` (`411 = 410 + 1` fns spliced onto `FullM7.m7Module`), executable
   equivalence with `FullM7Splice.patchFns`, `PrintCpp`, `PrintQbe`, and 4-ISA legalization.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, all `4` `Func.wp`
   contracts, closed `26`-row `fidSearch_tableImpl` / `fidSearch_moduleOk`, `4`-fn patch
   `TableImpl`, `411`-fn `fidSearchSpliced_moduleOk` / `fidSearchSpliced_solve_bytes_sound` /
   `fidSearchSpliced_unsat_nv`, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`).
3. Single-line `< 115c` `#print axioms` checks (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7FidelitySearchTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen, Legalization & `FullM7` Splice Checks -/

#guard fidSearchFns.length == 4
#guard fidSearchExterns.length == 22
#guard fidSearchModule.exits.isEmpty == true
#guard fidSearchModule.checkAcyclic == true
#guard fidSearchSpecTable.length == 26
#guard fidSearchSpecTable.all (·.noExit) == true
#guard fidSearchSpecTable.map (fun e => (e.name, e.as, e.rs)) == fidSearchModule.sigs
#guard fidBumpAnalyzedFn.name == "full_bump_analyzed_m6_hdr"
#guard fidSwitchModeFn.name == "full_switch_mode_m7"
#guard fidHdrDecideFn.name == "m6_hdr_decide_fid"
#guard fidSearchM6Fn.name == "full_search_m6"
#guard fidSearchPatchRepls.length == 3
#guard fidSearchPatchBefores.length == 1
#guard fidSearchPatchFns.length == 4
#guard fidSearchPatchRows.length == 4
#guard fidSearchPatchRows.all (·.noExit) == true
#guard fidSearchPatchRows.map (fun e => (e.name, e.as, e.rs)) == fidSearchPatchFns.map Fn.sig
#guard (ppTModule fidSearchModule).isOk
#guard (PrintQbe.module fidSearchModule).isOk
#guard (ppModule (fidSearchFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidSearchFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidSearchFns.map (Fn.legal .x64AVX2))).isOk
#guard fidSearchFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidSearchFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidSearchFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidSearchFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

#guard fidSearchSplicedFns.length == FullM7.m7Fns.length + 1
#guard fidSearchSplicedFns.map Fn.sig ==
  (FullM7Splice.patchFns fidSearchPatchRepls fidSearchPatchBefores FullM7.m7Fns).map Fn.sig
#guard (fidSearchSplicedFns.map Fn.name).eraseDups.length == fidSearchSplicedFns.length
#guard fidSearchSplicedModule.exits.isEmpty == true
#guard fidSearchSplicedModule.externs.isEmpty == true
#guard fidSearchSplicedModule.checkAcyclic == true
#guard (ppTModule fidSearchSplicedModule).isOk
#guard (PrintQbe.module fidSearchSplicedModule).isOk
#guard fidSearchSplicedFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidSearchSplicedFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidSearchSplicedFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidSearchSplicedFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem fs_fns_wf : ∀ f ∈ fidSearchFns, f.Wf := fidSearch_fns_wf
theorem fs_acyc : fidSearchModule.checkAcyclic = true := fidSearch_acyclic
theorem fs_tbl_len : fidSearchSpecTable.length = 26 := fidSearchSpecTable_length
theorem fs_tbl_impl : TableImpl fidSearchEnv fidSearchFns fidSearchSpecTable :=
  fidSearch_tableImpl
theorem fs_mod_ok : ModuleOk fidSearchEnv fidSearchModule := fidSearch_moduleOk
theorem fs_patch_sigs :
    fidSearchPatchRows.map (fun e => (e.name, e.as, e.rs)) = fidSearchPatchFns.map Fn.sig :=
  fidSearchPatchRows_sigs
theorem fs_patch_impl : TableImpl fidSearchEnv fidSearchPatchFns fidSearchPatchRows :=
  fidSearchPatch_tableImpl

theorem fs_bump_analyzed_wp (Γ : Env)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hSortAna : ∀ a m Q X, m6SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hQueueMtf : ∀ a m Q X, Full.fullQueueMtfSpec a m Q X →
      Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hBumpVar : ∀ a m Q X, Full.fullBumpVarSpec a m Q X →
      Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hBumpDecay : ∀ a m Q X, Full.fullBumpDecaySpec a m Q X →
      Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, m6aBumpAnalyzedSpec a m Q X →
      Func.wp Γ full_bump_analyzed_fid_body a m Q X :=
  full_bump_analyzed_fid_wp Γ hDrAllow hSortAna hQueueMtf hBumpVar hBumpDecay

theorem fs_switch_mode_wp (Γ : Env)
    (hIlog : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hHeapDown : ∀ a m Q X, Full.fullHeapDownSpec a m Q X →
      Γ "full_heap_down" [i64, i32] [] a m Q X)
    (hEmaSwap : ∀ a m Q X, m7EmaSwapSpec a m Q X →
      Γ "full_ema_swap_m7" [i64, i64, i64] [] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m7Set64Spec a m Q X →
      Γ "full_m7_set64" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m7SwitchModeSpec a m Q X → Func.wp Γ full_switch_mode_fid_body a m Q X :=
  full_switch_mode_fid_wp Γ hIlog hHeapDown hEmaSwap hLog10 hSet64

theorem fs_hdr_decide_wp (Γ : Env)
    (hDecide : ∀ a m Q X, m7DecideSpec a m Q X → Γ "full_decide_m7" [i64] [i64] a m Q X)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDecideSpec a m Q X → Func.wp Γ m6_hdr_decide_fid_body a m Q X :=
  m6_hdr_decide_fid_wp Γ hDecide hDrInit

theorem fs_search_wp (Γ : Env)
    (hLuckyLate : ∀ a m Q X, m7LuckyLateSpec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, m7SwitchModeSpec a m Q X →
      Γ "full_switch_mode_m7" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m7RephaseSpec a m Q X → Γ "full_rephase" [i64] [] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, m6HdrDecideSpec a m Q X →
      Γ "m6_hdr_decide_fid" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SearchSpec a m Q X →
      Func.wp Γ full_search_fid_body a m Q X :=
  full_search_fid_wp Γ hLuckyLate hProp hAnalyze hReduce hSwitch hRstDue hRst hReorder hRephase
    hSimplify hDecide

theorem fs_patch_impl_of (Γ : Env)
    (hDrAllow : EnvSpec Γ "m6_hdr_dr_allow" m6HdrDrAllowSpec)
    (hSortAna : EnvSpec Γ "full_sort_ana_qs_m6" m6SortAnaQsSpec)
    (hQueueMtf : EnvSpec Γ "full_queue_mtf" Full.fullQueueMtfSpec)
    (hBumpVar : EnvSpec Γ "full_bump_var" Full.fullBumpVarSpec)
    (hBumpDecay : EnvSpec Γ "full_bump_decay" Full.fullBumpDecaySpec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hIlog : EnvSpec Γ "full_ilog10" Full.fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" Full.fullHeapDownSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hDecideM7 : EnvSpec Γ "full_decide_m7" m7DecideSpec)
    (hDrInit : EnvSpec Γ "m6_hdr_dr_init" m6HdrDrMutSpec)
    (hLuckyLate : EnvSpec Γ "full_lucky_late_m7" m7LuckyLateSpec)
    (hProp : EnvSpec Γ "full_propagate" Full.fullPropagateSpec)
    (hAnalyze : EnvSpec Γ "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hReduce : EnvSpec Γ "full_reduce_m6" m6ReduceSpec)
    (hSwitch : EnvSpec Γ "full_switch_mode_m7" m7SwitchModeSpec)
    (hRstDue : EnvSpec Γ "full_restart_due" Full.fullRestartDueSpec)
    (hRst : EnvSpec Γ "full_restart" Full.fullRestartSpec)
    (hReorder : EnvSpec Γ "full_reorder_m6" FullM4.m4ReorderSpec)
    (hRephase : EnvSpec Γ "full_rephase" m7RephaseSpec)
    (hSimplify : EnvSpec Γ "full_simplify_m6" fullM6SimplifySpec)
    (hDecideFid : EnvSpec Γ "m6_hdr_decide_fid" m6HdrDecideSpec) :
    TableImpl Γ fidSearchPatchFns fidSearchPatchRows :=
  fidSearchPatch_tableImpl_of Γ hDrAllow hSortAna hQueueMtf hBumpVar hBumpDecay hSet64 hEmaSwap
    hIlog hHeapDown hLog10 hDecideM7 hDrInit hLuckyLate hProp hAnalyze hReduce hSwitch hRstDue hRst
    hReorder hRephase hSimplify hDecideFid

theorem fs_spliced_acyc : fidSearchSplicedModule.checkAcyclic = true := fidSearchSpliced_acyclic
theorem fs_spliced_nodup : (fidSearchSplicedFns.map Fn.name).Nodup := fidSearchSpliced_names_nodup

theorem fs_spliced_sigs (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (fidSearchSplicedTable tBve solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      fidSearchSplicedFns.map Fn.sig :=
  fidSearchSplicedTable_sigs tBve solveSpec hBveSigs

theorem fs_spliced_mod_ok (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true) (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve)
    (hHost : M7FidSearchHostRows (m7SpecTable tBve solveSpec)) :
    ModuleOk (fidSearchSplicedEnv tBve solveSpec) fidSearchSplicedModule :=
  fidSearchSpliced_moduleOk tBve solveSpec hWeaken hSolveMonoX hBveSigs hBveNoExit hBveSpecs
    hBveOk hHost

theorem fs_spliced_sound (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true) (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    (hHost : M7FidSearchHostRows (m7SpecTable tBve fullM6SolveBytesSpec))
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (fidSearchSplicedEnv tBve fullM6SolveBytesSpec)
      FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidSearchSpliced_solve_bytes_sound tBve hBveSigs hBveNoExit hBveSpecs hBveOk hHost hcfit hwfit hm

theorem fs_spliced_unsat_nv (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true) (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve)
    (hHost : M7FidSearchHostRows (m7SpecTable tBve fullM6SolveBytesCoreModelSpec)) :
    Func.wp (fidSearchSplicedEnv tBve fullM6SolveBytesCoreModelSpec)
      FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidSearchSpliced_unsat_nv tBve hBveSigs hBveNoExit hBveSpecs hBveOk hHost

theorem fs_nv_bump_analyzed :
    Func.wp fidSearchEnv full_bump_analyzed_fid_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ mrk' mcl' sc' ext',
        let c' : FullCoreState :=
          { nvOneLitState.core with mrk := mrk', min_clr_len := mcl' }
        let s' : FullState := { nvOneLitState with core := c', scratch := sc' }
        s'.LengthsOk nvOneLitCfg ∧ FullAnaMarksCov nvOneLitCfg s' ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bump_analyzed

theorem fs_nv_switch_mode :
    Func.wp fidSearchEnv full_switch_mode_fid_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s' : FullState,
        s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        FullProbeScratchPres nvOneLitState s' ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_switch_mode

theorem fs_nv_hdr_decide :
    Func.wp fidSearchEnv m6_hdr_decide_fid_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl'
          sc' ext',
        let s' : FullState :=
          { core := { nvOneLitState.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
              cur_level := cl', unassigned := unass', unflushed := unfl' }
            scratch := sc' }
        FullM6HdrCoreInv nvOneLitCfg nvOneLitF0 ext' s' ∧ (r = 0#64 ∨ r = 1#64) ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_hdr_decide

theorem fs_nv_search :
    Func.wp fidSearchEnv full_search_fid_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ c' ext' s',
        FullCfgCompat nvOneLitCfg c' ∧ s'.LengthsOk c' ∧
        FullM6HdrCfgOk c' ∧ M6HdrExtOk ext' ∧ (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧ FullM6HdrMem c' ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_search

end LeanQbeTest.T.KissatM7FidelitySearchTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev fs_ax_wf := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_fns_wf
abbrev fs_ax_acyc := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_acyc
abbrev fs_ax_tlen := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_tbl_len
abbrev fs_ax_tbl := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_tbl_impl
abbrev fs_ax_mod := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_mod_ok
abbrev fs_ax_psig := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_patch_sigs
abbrev fs_ax_pimpl := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_patch_impl
abbrev fs_ax_bump := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_bump_analyzed_wp
abbrev fs_ax_sw := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_switch_mode_wp
abbrev fs_ax_dec := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_hdr_decide_wp
abbrev fs_ax_srch := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_search_wp
abbrev fs_ax_pof := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_patch_impl_of
abbrev fs_ax_sacyc := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_spliced_acyc
abbrev fs_ax_snd := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_spliced_nodup
abbrev fs_ax_ssig := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_spliced_sigs
abbrev fs_ax_smod := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_spliced_mod_ok
abbrev fs_ax_ssnd := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_spliced_sound
abbrev fs_ax_snv := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_spliced_unsat_nv
abbrev fs_ax_nv_b := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_nv_bump_analyzed
abbrev fs_ax_nv_sw := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_nv_switch_mode
abbrev fs_ax_nv_d := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_nv_hdr_decide
abbrev fs_ax_nv_s := @LeanQbeTest.T.KissatM7FidelitySearchTest.fs_nv_search

#print axioms fs_ax_wf
#print axioms fs_ax_acyc
#print axioms fs_ax_tlen
#print axioms fs_ax_tbl
#print axioms fs_ax_mod
#print axioms fs_ax_psig
#print axioms fs_ax_pimpl
#print axioms fs_ax_bump
#print axioms fs_ax_sw
#print axioms fs_ax_dec
#print axioms fs_ax_srch
#print axioms fs_ax_pof
#print axioms fs_ax_sacyc
#print axioms fs_ax_snd
#print axioms fs_ax_ssig
#print axioms fs_ax_smod
#print axioms fs_ax_ssnd
#print axioms fs_ax_snv
#print axioms fs_ax_nv_b
#print axioms fs_ax_nv_sw
#print axioms fs_ax_nv_d
#print axioms fs_ax_nv_s
