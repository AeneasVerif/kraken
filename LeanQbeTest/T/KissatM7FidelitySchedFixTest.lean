/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import Kraken.Mem
import Kraken.Separation

/-!
# Verification, Splice Guards & Axiom Audit (`FullM7FidelitySchedFix`)

1. Executable `#guard` checks on standalone `fidSchedFixModule` (`5` fns, `32` externs, `37` spec
   rows, `0` exits), upstream-fix structural call-set invariants (`fastel = 0`, `full_factor`
   dropped from eliminate, `full_probe_run` dropped, `full_vivify_m6_hdr` in `full_probe_m6`, Q16
   arithmetic), `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` / `isLegal` across `.aarch64`,
   `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Executable `#guard` checks on `410`-function spliced `m7FidSchedFixModule` (`checkAcyclic`, empty
   externs/exits, preserved signatures, `PrintCpp`, `PrintQbe`, 4-ISA legalization).
3. Audit-ready restated headline theorems (`Wf`, `checkAcyclic`, parametric `Func.wp` contracts,
   `fidSchedFix_moduleOk`, concrete `Mem 64` UNSAT NV `XPost := False`, `m7FidSchedFix_moduleOk`,
   `m7FidSchedFix_solve_bytes_sound`, `m7FidSchedFix_unsat_nv`).
4. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7FidelitySchedFixTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
open Kraken.Bedrock2.Test

/-! ## 1. Standalone Module, Upstream Fix Structure, Codegen & 4-ISA Legalization Guards -/

#guard fidSchedFixModule.checkAcyclic == true
#guard fidSchedFixModule.exits.isEmpty == true
#guard fidSchedFixFns.length == 5
#guard fidSchedFixExterns.length == 32
#guard fidSchedFixSpecTable.length == 37
#guard fidSchedFixSpecTable.all (·.noExit) == true
#guard fidSchedFixSpecTable.map (fun e => (e.name, e.as, e.rs)) ==
  fidSchedFixModule.fns.map Fn.sig ++ fidSchedFixModule.externs.map Extern.sig
#guard fidSchedFixFns.map Fn.name ==
  [ "full_reduce_m6", "full_eliminate_m6", "full_probe_tail_m6", "full_probe_m6"
  , "full_preprocess_m6" ]
#guard fidSchedFixPatchFns.map Fn.sig == fidSchedFixFns.map Fn.sig
#guard fidSchedFixPatchBefores.isEmpty == true
#guard fidSchedFixPatchRows.length == 5
#guard fidSchedFixPatchInsRows.isEmpty == true
#guard fid2EliminateM6Fn.checkCallsOk
    [ ("full_elim_dticks", [i64, .bool], [i64]), ("full_log10_q16_m7", [i64], [i64])
    , ("full_scale_delta", [i64, i64], [i64]), ("full_enter_dense", [i64], [.bool])
    , ("full_min_u64", [i64, i64], [i64]), ("full_forward_sub", [i64, i64], [i64])
    , ("full_elim_bve_m7", [i64, i64], [i64]), ("full_rebuild_watches", [i64], [i64]) ] []
#guard fid2ProbeTailM6Fn.checkCallsOk
    [ ("full_backbone_m6", [i64, i64], [i64])
    , ("full_transitive_m6", [i64, i64], [i64]) ] []
#guard fid2PreprocessM6Fn.checkCallsOk
    [ ("full_propagate", [i64], [i64]), ("full_arena_sweep", [i64], [i64])
    , ("full_lucky", [i64], [i64]), ("full_compact_needed", [i64], [.bool])
    , ("full_compact", [i64], [i64]), ("full_scale_delta_m5", [i64, i64], [i64])
    , ("full_probe_m6", [i64, .bool], [i64]) ] []
#guard 900 - (400 <<< 16) / 65536 == 500
#guard 900 - (400 <<< 16) / (2 * 65536) == 700
#guard (ppTModule fidSchedFixModule).isOk
#guard match ppTModule fidSchedFixModule with
  | .ok s => (s.splitOn "full_probe_run").length == 1 &&
      (s.splitOn "full_vivify_m6_hdr").length > 1 &&
      (s.splitOn "full_log10_q16_m7").length > 1 &&
      (s.splitOn "full_reduce_m6").length > 1 &&
      (s.splitOn "full_eliminate_m6").length > 1 &&
      (s.splitOn "full_probe_tail_m6").length > 1 &&
      (s.splitOn "full_probe_m6").length > 1 &&
      (s.splitOn "full_preprocess_m6").length > 1
  | .error _ => false
#guard (PrintQbe.module fidSchedFixModule).isOk
#guard (ppModule (fidSchedFixFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidSchedFixFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidSchedFixFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (fidSchedFixFns.map (Fn.legal .x64AVX512))).isOk
#guard fidSchedFixFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidSchedFixFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidSchedFixFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidSchedFixFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. `410`-Function `m7FidSchedFixModule` Splice, Codegen & 4-ISA Legalization Guards -/

#guard m7FidSchedFixFns.length == 410
#guard m7FidSchedFixModule.checkAcyclic == true
#guard m7FidSchedFixModule.exits.isEmpty && m7FidSchedFixModule.externs.isEmpty
#guard m7FidSchedFixFns.map Fn.sig == m7Fns.map Fn.sig
#guard (ppTModule m7FidSchedFixModule).isOk
#guard (PrintQbe.module m7FidSchedFixModule).isOk
#guard (ppModule (m7FidSchedFixFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7FidSchedFixFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7FidSchedFixFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (m7FidSchedFixFns.map (Fn.legal .x64AVX512))).isOk
#guard m7FidSchedFixFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7FidSchedFixFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7FidSchedFixFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard m7FidSchedFixFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 3. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem f2_fns_wf : ∀ f ∈ fidSchedFixFns, f.Wf := fidSchedFix_fns_wf
theorem f2_acyc : fidSchedFixModule.checkAcyclic = true := fidSchedFix_acyclic
theorem f2_nd : (fidSchedFixSpecTable.map SpecEntry.name).Nodup := fidSchedFixSpecTable_nodup

theorem f2_no_exit :
    ∀ f as bs xs m Q X X',
      fidSchedFixEnv f as bs xs m Q X → fidSchedFixEnv f as bs xs m Q X' :=
  fidSchedFixEnv_noExit

theorem f2_reduce_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hMark : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSort : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ReduceSpec a m Q X → Func.wp Γ full_reduce_fid2_body a m Q X :=
  full_reduce_fid2_wp Γ hIsqrt hLog10 hNext hRecomp hWm hMark hSort hBack hProp hSweep

theorem f2_elim_wp (Γ : Env)
    (hDt : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnt : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X → Func.wp Γ full_eliminate_fid2_body a m Q X :=
  full_eliminate_fid2_wp Γ hDt hLog10 hScale hEnt hMin hFwd hBve hReb

theorem f2_tail_wp (Γ : Env)
    (hBone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeTailSpec a m Q X → Func.wp Γ full_probe_tail_fid2_body a m Q X :=
  full_probe_tail_fid2_wp Γ hBone hTrans

theorem f2_probe_wp (Γ : Env)
    (hDt : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X)
    (hEnt : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDel : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSw : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFac : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X → Func.wp Γ full_probe_fid2_body a m Q X :=
  full_probe_fid2_wp Γ hDt hLog10 hScale hViv hEnt hDel hCong hReb hWm hRedD hBumpD
    hSw hSub hTail hBone hMin hFac

theorem f2_pre_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hCn : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCmp : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X → Func.wp Γ full_preprocess_fid2_body a m Q X :=
  full_preprocess_fid2_wp Γ hProp hSw hLucky hCn hCmp hScale hProbe

theorem f2_mod_ok : ModuleOk fidSchedFixEnv fidSchedFixModule := fidSchedFix_moduleOk

theorem f2_nv_reduce :
    Func.wp fidSchedFixEnv full_reduce_fid2_body (nvOneLitCfg.hdr, false, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s',
        FullM6HdrInvW nvOneLitCfg nvOneLitF0 [[0], [1]] ext' s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid2_reduce

theorem f2_nv_elim :
    Func.wp fidSchedFixEnv full_eliminate_fid2_body (nvOneLitCfg.hdr, true, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s', FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid2_eliminate

theorem f2_nv_tail :
    Func.wp fidSchedFixEnv full_probe_tail_fid2_body (nvOneLitCfg.hdr, 0#64, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid2_probe_tail

theorem f2_nv_probe :
    Func.wp fidSchedFixEnv full_probe_fid2_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid2_probe

theorem f2_nv_pre :
    Func.wp fidSchedFixEnv full_preprocess_fid2_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ c' ext' s',
        FullM4Compact.FullCfgCompat nvOneLitCfg c' ∧ s'.LengthsOk c' ∧
        FullM6HdrCfgOk c' ∧ M6HdrExtOk ext' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv c' nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem c' ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid2_preprocess

theorem f2_m7_sigs (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (patchRows fidSchedFixPatchRows fidSchedFixPatchInsRows (m7SpecTable tBve s)).map
        (fun e => (e.name, e.as, e.rs)) =
      m7FidSchedFixFns.map Fn.sig :=
  m7FidSchedFix_patched_rows_sigs tBve s hBS

theorem f2_m7_acyc : m7FidSchedFixModule.checkAcyclic = true := m7FidSchedFix_acyclic

theorem f2_m7_mod_ok (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (hW : ∀ a m Q X, s a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hX : ∀ a m Q X X', s a m Q X → s a m Q X')
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hEB : (⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :
      SpecEntry) ∈ tBve)
    (hED : (⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve s)
    (hSD : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64],
      FullDefSweep.fullSweepDenseSpec, true⟩ : SpecEntry) ∈ m7SpecTable tBve s)
    (hPT : (⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve s)
    (hPr : (⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve s)
    (hBO : TableImpl (mkM7Env tBve s) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tBve s) m7FidSchedFixModule :=
  m7FidSchedFix_moduleOk tBve s hW hX hBS hBN hBP hEB hED hSD hPT hPr hBO

theorem f2_m7_sound (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hEB : (⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :
      SpecEntry) ∈ tBve)
    (hED : (⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesSpec)
    (hSD : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64],
      FullDefSweep.fullSweepDenseSpec, true⟩ : SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesSpec)
    (hPT : (⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesSpec)
    (hPr : (⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesSpec)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
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
  m7FidSchedFix_solve_bytes_sound tBve hBS hBN hBP hEB hED hSD hPT hPr hBO hcfit hwfit hm

theorem f2_m7_nv (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hEB : (⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ :
      SpecEntry) ∈ tBve)
    (hED : (⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesCoreModelSpec)
    (hSD : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64],
      FullDefSweep.fullSweepDenseSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesCoreModelSpec)
    (hPT : (⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesCoreModelSpec)
    (hPr : (⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :
      SpecEntry) ∈ m7SpecTable tBve fullM6SolveBytesCoreModelSpec)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tBve fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m7FidSchedFix_unsat_nv tBve hBS hBN hBP hEB hED hSD hPT hPr hBO

end AuditSpec

end LeanQbeTest.T.KissatM7FidelitySchedFixTest

/-! ## 4. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7f2_wf := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_fns_wf
abbrev m7f2_acyc := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_acyc
abbrev m7f2_nd := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_nd
abbrev m7f2_nx := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_no_exit
abbrev m7f2_rd := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_reduce_wp
abbrev m7f2_el := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_elim_wp
abbrev m7f2_tl := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_tail_wp
abbrev m7f2_pr := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_probe_wp
abbrev m7f2_pp := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_pre_wp
abbrev m7f2_ok := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_mod_ok
abbrev m7f2_nv1 := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_nv_reduce
abbrev m7f2_nv2 := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_nv_elim
abbrev m7f2_nv3 := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_nv_tail
abbrev m7f2_nv4 := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_nv_probe
abbrev m7f2_nv5 := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_nv_pre
abbrev m7f2_m7s := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_m7_sigs
abbrev m7f2_m7a := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_m7_acyc
abbrev m7f2_m7o := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_m7_mod_ok
abbrev m7f2_m7w := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_m7_sound
abbrev m7f2_m7n := @LeanQbeTest.T.KissatM7FidelitySchedFixTest.f2_m7_nv

#print axioms m7f2_wf
#print axioms m7f2_acyc
#print axioms m7f2_nd
#print axioms m7f2_nx
#print axioms m7f2_rd
#print axioms m7f2_el
#print axioms m7f2_tl
#print axioms m7f2_pr
#print axioms m7f2_pp
#print axioms m7f2_ok
#print axioms m7f2_nv1
#print axioms m7f2_nv2
#print axioms m7f2_nv3
#print axioms m7f2_nv4
#print axioms m7f2_nv5
#print axioms m7f2_m7s
#print axioms m7f2_m7a
#print axioms m7f2_m7o
#print axioms m7f2_m7w
#print axioms m7f2_m7n

end
