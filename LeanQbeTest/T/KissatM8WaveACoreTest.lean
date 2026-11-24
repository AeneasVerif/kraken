module

public import LeanQbe.T.Examples.Kissat.FullM8WaveACore
public import LeanQbe.T.Examples.Kissat.FullM8WaveACoreProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM8WaveACore
meta import LeanQbe.T.Examples.Kissat.FullM8WaveACoreProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Codegen Guards, and Axiom Audit for Kissat M8 `FullM8WaveACore`

1. Executable `#guard` checks on `waveACoreModule` (`11` fns, `22` externs, `0` exits),
   `waveACoreSpecTable` (`33` rows, `noExit = true`), `waveACoreRepls`/`waveACoreBefores`,
   `PatchModule.patchFns`, `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`,
   `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Restated headline theorems covering `Func.Wf`, `checkAcyclic`, all `11` parametric `Func.wp`
   theorems, closed `TableImpl` / `ModuleOk`, `PatchModule` bridges, and concrete `Mem 64` UNSAT
   non-vacuity (`XPost := False`, covering AE-bump Q16 `tanh` / rescale paths and M8 delay slots).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM8WaveACoreTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.PatchModule
open LeanQbe.T.Examples.Kissat.FullM8WaveACore
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard waveACoreFns.length == 11
#guard waveACoreRepls.length == 10
#guard waveACoreBefores.length == 1
#guard waveACoreModule.externs.length == 22
#guard waveACoreModule.exits.isEmpty == true
#guard waveACoreModule.checkAcyclic == true
#guard waveACoreSpecTable.length == 33
#guard waveACoreSpecTable.all (·.noExit) == true
#guard waveACoreSpecTable.map (fun e => (e.name, e.as, e.rs)) ==
  waveACoreModule.fns.map Fn.sig ++ waveACoreModule.externs.map Extern.sig
#guard waveACorePatchRows.map (fun e => (e.name, e.as, e.rs)) == waveACoreRepls.map Fn.sig
#guard waveACoreBeforeRows.map (fun e => (e.name, e.as, e.rs)) == [m8Log2Q16Fn].map Fn.sig
#guard waveACorePatchRows.all (·.noExit) == true
#guard waveACoreBeforeRows.all (·.noExit) == true
#guard (ppTModule waveACoreModule).isOk
#guard (PrintQbe.module waveACoreModule).isOk
#guard (ppModule (waveACoreFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (waveACoreFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (waveACoreFns.map (Fn.legal .x64AVX2))).isOk
#guard waveACoreFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem wac_fns_wf : ∀ f ∈ waveACoreFns, f.Wf := waveACoreFns_wf
theorem wac_repls_wf : ∀ f ∈ waveACoreRepls, f.Wf := waveACoreRepls_wf
theorem wac_acyc : waveACoreModule.checkAcyclic = true := waveACore_acyclic
theorem wac_tbl_len : waveACoreSpecTable.length = 33 := waveACoreSpecTable_length

theorem wac_noExit :
    ∀ f as bs xs m Q X X',
      waveACoreEnv f as bs xs m Q X → waveACoreEnv f as bs xs m Q X' :=
  waveACoreEnv_noExit

theorem wac_log2_wp (Γ : Env) :
    ∀ a m Q X, m8Log2Q16Spec a m Q X → Func.wp Γ m8_log2_q16_body a m Q X :=
  m8_log2_q16_wp Γ

theorem wac_bump_decay_wp (Γ : Env)
    (hLog2 : ∀ a m Q X, m8Log2Q16Spec a m Q X → Γ "m8_log2_q16" [i64] [i64] a m Q X)
    (hRes : ∀ a m Q X, Full.fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullBumpDecaySpec a m Q X →
      Func.wp Γ m8_ae_bump_decay_body a m Q X :=
  m8_ae_bump_decay_wp Γ hLog2 hRes

theorem wac_recompute_tiers_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m8_hdr_recompute_tiers_mode_body a m Q X :=
  m8_hdr_recompute_tiers_mode_wp Γ hEnsure hSync

theorem wac_record_used_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m8_hdr_record_used_body a m Q X :=
  m8_hdr_record_used_wp Γ hEnsure

theorem wac_delaying_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Func.wp Γ FullM8WaveACore.m6_hdr_delaying_body a m Q X :=
  m6_hdr_delaying_wp Γ hEnsure

theorem wac_bump_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ FullM8WaveACore.m6_hdr_bump_delay_body a m Q X :=
  m6_hdr_bump_delay_wp Γ hEnsure

theorem wac_reduce_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ FullM8WaveACore.m6_hdr_reduce_delay_body a m Q X :=
  m6_hdr_reduce_delay_wp Γ hEnsure

theorem wac_viv_tier_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m8VivifyTierSpec a m Q X →
      Func.wp Γ FullM8WaveACore.full_vivify_tier_m6_hdr_body a m Q X :=
  full_vivify_tier_m6_hdr_wp Γ hBacktrack hCollect hCount hKeys hSortSched
    hVivClause hProp hClearTier

theorem wac_vivify_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hVivTier : ∀ a m Q X, m8VivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6aVivifySpec a m Q X →
      Func.wp Γ FullM8WaveACore.full_vivify_m6_hdr_body a m Q X :=
  full_vivify_m6_hdr_wp Γ hBacktrack hSync hGetWm hDelaying hBumpDelay hReduceDelay hVivTier

theorem wac_elim_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X → Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, m8EliminateSpec a m Q X → Func.wp Γ m8_eliminate_m6_body a m Q X :=
  m8_eliminate_m6_wp Γ hDticks hLog10 hScale hEnter hMin hFwd hBve hReb

theorem wac_probe_tail_wp (Γ : Env)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hBackbone : ∀ a m Q X, fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Func.wp Γ FullM8WaveACore.full_probe_tail_m6_body a m Q X :=
  full_probe_tail_m6_wp Γ hDelaying hBackbone hBumpDelay hReduceDelay hTrans

theorem wac_tbl_impl : TableImpl waveACoreEnv waveACoreFns waveACoreSpecTable :=
  waveACore_tableImpl

theorem wac_mod_ok : ModuleOk waveACoreEnv waveACoreModule :=
  waveACore_moduleOk

theorem wac_patch_tbl_impl : TableImpl waveACoreEnv waveACoreRepls waveACorePatchRows :=
  waveACorePatch_tableImpl

theorem wac_before_tbl_of (Γ : Env) :
    TableImpl Γ [m8Log2Q16Fn] waveACoreBeforeRows :=
  waveACoreBefore_tableImpl_of Γ

theorem wac_patch_sigs :
    waveACorePatchRows.map (fun e => (e.name, e.as, e.rs)) = waveACoreRepls.map Fn.sig :=
  waveACorePatchRows_sigs

theorem wac_before_sigs :
    waveACoreBeforeRows.map (fun e => (e.name, e.as, e.rs)) = [m8Log2Q16Fn].map Fn.sig :=
  waveACoreBeforeRows_sigs

theorem wac_nv_log2 :
    Func.wp waveACoreEnv m8_log2_q16_body (1#64 <<< 44, ()) nvOneLitMem
      (fun (r, ()) m' => 44 * 65536 ≤ r.toNat ∧ r.toNat < 45 * 65536 ∧ m' = nvOneLitMem)
      (fun _ _ _ _ => False) :=
  nv_m8_log2_q16_pow44

theorem wac_nv_tanh :
    Func.wp waveACoreEnv m8_ae_bump_decay_body (nvOneLitCfg.hdr, ()) nvAeTanhMem
      (fun () m' => ∃ s', PreservesCoreSlice FullState.core nvAeTanhState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvAeTanhState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_bump_decay_tanh

theorem wac_nv_rescale :
    Func.wp waveACoreEnv m8_ae_bump_decay_body (nvOneLitCfg.hdr, ()) nvAeRescaleMem
      (fun () m' => ∃ s', PreservesCoreSlice FullState.core nvAeRescaleState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvAeRescaleState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_bump_decay_rescale

theorem wac_nv_tiers :
    Func.wp waveACoreEnv m8_hdr_recompute_tiers_mode_body (nvOneLitCfg.hdr, 0#64, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_recompute_tiers_mode

theorem wac_nv_rec_used :
    Func.wp waveACoreEnv m8_hdr_record_used_body (nvOneLitCfg.hdr, 80#64, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_record_used_clamp64

theorem wac_nv_del6 :
    Func.wp waveACoreEnv FullM8WaveACore.m6_hdr_delaying_body (nvOneLitCfg.hdr, 6#64, ())
      nvM8DelayMem
      (fun (b, ()) m' => ∃ ext' s', (b = true ∨ b = false) ∧ s'.LengthsOk nvOneLitCfg ∧
        M6HdrExtOk ext' ∧ nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_delay_slot6_delaying

theorem wac_nv_bump4 :
    Func.wp waveACoreEnv FullM8WaveACore.m6_hdr_bump_delay_body (nvOneLitCfg.hdr, 4#64, ())
      nvM8DelayMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_delay_slot4_bump

theorem wac_nv_red6 :
    Func.wp waveACoreEnv FullM8WaveACore.m6_hdr_reduce_delay_body (nvOneLitCfg.hdr, 6#64, ())
      nvM8DelayMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_delay_slot6_reduce

theorem wac_nv_viv_tier :
    Func.wp waveACoreEnv FullM8WaveACore.full_vivify_tier_m6_hdr_body
      (nvOneLitCfg.hdr, 0#64, 1#64, 100#64, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_vivify_tier

theorem wac_nv_viv :
    Func.wp waveACoreEnv FullM8WaveACore.full_vivify_m6_hdr_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_vivify

theorem wac_nv_elim_i :
    Func.wp waveACoreEnv m8_eliminate_m6_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_eliminate_init

theorem wac_nv_elim_p :
    Func.wp waveACoreEnv m8_eliminate_m6_body (nvOneLitCfg.hdr, false, ()) nvM8DelayMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_eliminate_post

theorem wac_nv_ptail6 :
    Func.wp waveACoreEnv FullM8WaveACore.full_probe_tail_m6_body
      (nvOneLitCfg.hdr, 100#64, ()) nvM8ProbeTailMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_probe_tail_delay6

end LeanQbeTest.T.KissatM8WaveACoreTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m8wac_fns_wf := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_fns_wf
abbrev m8wac_rep_wf := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_repls_wf
abbrev m8wac_acyc := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_acyc
abbrev m8wac_tbl_len := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_tbl_len
abbrev m8wac_nx := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_noExit
abbrev m8wac_log2_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_log2_wp
abbrev m8wac_decay_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_bump_decay_wp
abbrev m8wac_tiers_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_recompute_tiers_wp
abbrev m8wac_used_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_record_used_wp
abbrev m8wac_del_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_delaying_wp
abbrev m8wac_bmp_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_bump_delay_wp
abbrev m8wac_red_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_reduce_delay_wp
abbrev m8wac_vivt_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_viv_tier_wp
abbrev m8wac_viv_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_vivify_wp
abbrev m8wac_elim_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_elim_wp
abbrev m8wac_ptail_wp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_probe_tail_wp
abbrev m8wac_tbl := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_tbl_impl
abbrev m8wac_mod := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_mod_ok
abbrev m8wac_ptbl := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_patch_tbl_impl
abbrev m8wac_btbl := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_before_tbl_of
abbrev m8wac_psigs := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_patch_sigs
abbrev m8wac_bsigs := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_before_sigs
abbrev m8wac_nv_log2 := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_log2
abbrev m8wac_nv_tanh := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_tanh
abbrev m8wac_nv_res := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_rescale
abbrev m8wac_nv_tier := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_tiers
abbrev m8wac_nv_used := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_rec_used
abbrev m8wac_nv_del6 := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_del6
abbrev m8wac_nv_bmp4 := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_bump4
abbrev m8wac_nv_red6 := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_red6
abbrev m8wac_nv_vivt := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_viv_tier
abbrev m8wac_nv_viv := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_viv
abbrev m8wac_nv_eli := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_elim_i
abbrev m8wac_nv_elp := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_elim_p
abbrev m8wac_nv_ptl6 := @LeanQbeTest.T.KissatM8WaveACoreTest.wac_nv_ptail6

#print axioms m8wac_fns_wf
#print axioms m8wac_rep_wf
#print axioms m8wac_acyc
#print axioms m8wac_tbl_len
#print axioms m8wac_nx
#print axioms m8wac_log2_wp
#print axioms m8wac_decay_wp
#print axioms m8wac_tiers_wp
#print axioms m8wac_used_wp
#print axioms m8wac_del_wp
#print axioms m8wac_bmp_wp
#print axioms m8wac_red_wp
#print axioms m8wac_vivt_wp
#print axioms m8wac_viv_wp
#print axioms m8wac_elim_wp
#print axioms m8wac_ptail_wp
#print axioms m8wac_tbl
#print axioms m8wac_mod
#print axioms m8wac_ptbl
#print axioms m8wac_btbl
#print axioms m8wac_psigs
#print axioms m8wac_bsigs
#print axioms m8wac_nv_log2
#print axioms m8wac_nv_tanh
#print axioms m8wac_nv_res
#print axioms m8wac_nv_tier
#print axioms m8wac_nv_used
#print axioms m8wac_nv_del6
#print axioms m8wac_nv_bmp4
#print axioms m8wac_nv_red6
#print axioms m8wac_nv_vivt
#print axioms m8wac_nv_viv
#print axioms m8wac_nv_eli
#print axioms m8wac_nv_elp
#print axioms m8wac_nv_ptl6
