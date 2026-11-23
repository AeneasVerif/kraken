module

public import LeanQbe.T.Examples.Kissat.FullM7FidelitySched
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedProof
public import LeanQbe.T.Examples.Kissat.Full1
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySched
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedProof
meta import LeanQbe.T.Examples.Kissat.Full1
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Reference Checks, Codegen Guards & Axiom Audit (`FullM7FidelitySched`)

1. Executable `#guard` checks on `fidSchedModule` (`7` fns, `31` externs, `38` spec rows,
   `0` exits), `checkAcyclic = true`, drop-in `Fn` handles, `PrintCpp`, `PrintQbe`, and 4-ISA
   `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, `.x64AVX512`.
2. Upstream reference checks comparing `full_ilog10_fid` (`P1-4`), `full_nlogpown_fid`
   (`NLOGN`/`NLOG2N`/`NLOG3N`), and `full_calc_max_v_fid` vs `Full1.full_calc_max_v`.
3. Audit-ready restated headline theorems (`Wf`, `checkAcyclic`, parametric `Func.wp` contracts,
   closed `fidSched_moduleOk`, concrete `Mem 64` UNSAT non-vacuity `XPost := False`).
4. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7FidelitySchedTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM7FidelitySched
open Kraken.Bedrock2.Test

/-! ## 1. Module Structure, Codegen, 4-ISA Legalization & Upstream Reference Guards -/

#guard fidSchedModule.checkAcyclic == true
#guard fidSchedModule.exits.isEmpty == true
#guard fidSchedFns.length == 7
#guard fidSchedExterns.length == 31
#guard fidSchedSpecTable.length == 38
#guard fidSchedSpecTable.all (·.noExit) == true
#guard fidSchedSpecTable.map (fun e => (e.name, e.as, e.rs)) ==
  fidSchedModule.fns.map Fn.sig ++ fidSchedModule.externs.map Extern.sig
#guard fidSchedFns.map Fn.name ==
  [ "full_ilog10_fid", "full_nlogpown_fid", "full_calc_max_v_fid", "full_reduce_fid"
  , "full_probe_fid", "full_eliminate_fid", "full_preprocess_fid" ]
#guard fidIlog10Fn.name == "full_ilog10"
#guard fidNlogpownFn.name == "full_nlogpown"
#guard fidCalcMaxVFn.name == "full_calc_max_v"
#guard fidReduceFn.name == "full_reduce"
#guard fidReduceM6Fn.name == "full_reduce_m6"
#guard fidProbeFn.name == "full_probe"
#guard fidProbeM6Fn.name == "full_probe_m6"
#guard fidEliminateFn.name == "full_eliminate"
#guard fidEliminateM7Fn.name == "full_eliminate_m7"
#guard fidPreprocessFn.name == "full_preprocess"
#guard fidPreprocessM6Fn.name == "full_preprocess_m6"
#guard (ppTModule fidSchedModule).isOk
#guard match ppTModule fidSchedModule with
  | .ok s => (s.splitOn "full_ilog10_fid").length > 1 &&
      (s.splitOn "full_nlogpown_fid").length > 1 &&
      (s.splitOn "full_reduce_fid").length > 1 &&
      (s.splitOn "full_probe_fid").length > 1 &&
      (s.splitOn "full_eliminate_fid").length > 1 &&
      (s.splitOn "full_preprocess_fid").length > 1
  | .error _ => false
#guard (PrintQbe.module fidSchedModule).isOk
#guard (ppModule (fidSchedFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidSchedFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidSchedFns.map (Fn.legal .x64AVX2))).isOk
#guard fidSchedFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

private def refIlog10Go (x r p fuel : Nat) : Nat :=
  match fuel with
  | 0 => r
  | k + 1 => if p ≤ x / 10 ∧ r < 19 then refIlog10Go x (r + 1) (p * 10) k else r

private def refIlog10 (x : Nat) : Nat := refIlog10Go x 1 10 20

private def refNlogpown (base count exp : Nat) : Nat :=
  let arg := min (count + 9) (2 ^ 64 - 1)
  let lg := refIlog10 arg
  min base 10000 * min count 100000000 * lg ^ min exp 3

private def refFixedBytes (mv : Nat) : Nat := mv * 1000

private def refCalcMaxVFid (avail mv nc f0 : Nat) : Nat :=
  let rem0 := avail - f0
  let bva :=
    if 2 ≤ mv ∧ nc * 48 + 8192 < rem0 then
      min 4096 ((rem0 - nc * 48 - 4096) / 2688)
    else 0
  let max_v := mv + bva
  let fixed := refFixedBytes max_v
  if avail < fixed ∨ avail - fixed < nc * 40 + 136 then mv else max_v

private def refCalcMaxVFull1 (avail mv nc f0 : Nat) : Nat :=
  let rem0 := avail - f0
  let bva :=
    if 2 ≤ mv ∧ nc * 48 + 8192 < rem0 then
      min (min (mv / 2 + 16) 4096) ((rem0 - nc * 48 - 4096) / 2688)
    else 0
  let max_v := mv + bva
  let fixed := refFixedBytes max_v
  if avail < fixed ∨ avail - fixed < nc * 40 + 136 then mv else max_v

#guard refIlog10 0 == 1
#guard refIlog10 10 == 1
#guard refIlog10 99 == 1
#guard refIlog10 100 == 2
#guard refIlog10 999 == 2
#guard refIlog10 1000 == 3
#guard refNlogpown 100 1 1 == 100
#guard refNlogpown 100 91 1 == 18200
#guard refNlogpown 500 1 2 == 500
#guard refNlogpown 500 91 2 == 182000
#guard refNlogpown 10 91 3 == 7280
#guard 900 - 400 / refIlog10 (1 + 9) == 500
#guard refCalcMaxVFid 32000000 572 1000 (refFixedBytes 572) == 572 + 4096
#guard refCalcMaxVFull1 32000000 572 1000 (refFixedBytes 572) == 572 + 302
#guard refCalcMaxVFid 32000000 10000 1000 (refFixedBytes 10000) ==
  refCalcMaxVFull1 32000000 10000 1000 (refFixedBytes 10000)
#guard (full1_fns.find? (·.name == "full_calc_max_v")).map Fn.sig == some fidCalcMaxVFn.sig
#guard (full1_fns.find? (·.name == "full_ilog10")).map Fn.sig == some fidIlog10Fn.sig
#guard fidCalcMaxVFn.sig == ("full_calc_max_v", [i64, i64, i64, i64], [i64])
#guard fidIlog10Fn.sig == ("full_ilog10", [i64], [i64])

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem fs_fns_wf : ∀ f ∈ fidSchedFns, f.Wf := fidSched_fns_wf
theorem fs_acyc : fidSchedModule.checkAcyclic = true := fidSched_acyclic
theorem fs_nd : (fidSchedSpecTable.map SpecEntry.name).Nodup := fidSchedSpecTable_nodup

theorem fs_no_exit :
    ∀ f as bs xs m Q X X', fidSchedEnv f as bs xs m Q X → fidSchedEnv f as bs xs m Q X' :=
  fidSchedEnv_noExit

theorem fs_ilog_ex_wp (Γ : Env) :
    ∀ a m Q X, fidIlog10ExactSpec a m Q X → Func.wp Γ full_ilog10_fid_body a m Q X :=
  full_ilog10_fid_exact_wp Γ

theorem fs_ilog_wp (Γ : Env) :
    ∀ a m Q X, fullIlog10Spec a m Q X → Func.wp Γ full_ilog10_fid_body a m Q X :=
  full_ilog10_fid_wp Γ

theorem fs_nlog_wp (Γ : Env)
    (hIlog : ∀ a m Q X, fidIlog10ExactSpec a m Q X →
      Γ "full_ilog10_fid" [i64] [i64] a m Q X) :
    ∀ a m Q X, fidNlogpownSpec a m Q X → Func.wp Γ full_nlogpown_fid_body a m Q X :=
  full_nlogpown_fid_wp Γ hIlog

theorem fs_cmax_wp (Γ : Env)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_fid_body a m Q X :=
  full_calc_max_v_fid_wp Γ hFixed

theorem fs_reduce_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X →
      Γ "full_ilog10_fid" [i64] [i64] a m Q X)
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
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ReduceSpec a m Q X → Func.wp Γ full_reduce_fid_body a m Q X :=
  full_reduce_fid_wp Γ hIsqrt hIlog hNext hRecomp hWm hMark hSort hBack hProp hSweep

theorem fs_probe_wp (Γ : Env)
    (hDt : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hNlog : ∀ a m Q X, fidNlogpownSpec a m Q X →
      Γ "full_nlogpown_fid" [i64, i64, i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnt : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDel : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullDefSweep.fullCongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSw : ∀ a m Q X, FullM3CongBva.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hTail : ∀ a m Q X, fidProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hBone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFac : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fidProbeSpec a m Q X → Func.wp Γ full_probe_fid_body a m Q X :=
  full_probe_fid_wp Γ hDt hNlog hScale hEnt hDel hCong hReb hRedD hBumpD hSw hSub hWm
    hTail hBone hMin hFac

theorem fs_elim_wp (Γ : Env)
    (hDt : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hNlog : ∀ a m Q X, fidNlogpownSpec a m Q X →
      Γ "full_nlogpown_fid" [i64, i64, i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnt : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m7" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hFac : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_fid_body a m Q X :=
  full_eliminate_fid_wp Γ hDt hNlog hScale hEnt hMin hFwd hBve hFac hReb

theorem fs_pre_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hCn : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCmp : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, fidProbeSpec a m Q X →
      Γ "full_probe_fid" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Γ "full_eliminate_fid" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ full_preprocess_fid_body a m Q X :=
  full_preprocess_fid_wp Γ hProp hSw hLucky hCn hCmp hScale hProbe hElim

theorem fs_mod_ok : ModuleOk fidSchedEnv fidSchedModule := fidSched_moduleOk

theorem fs_nv_ilog :
    Func.wp fidSchedEnv full_ilog10_fid_body (10#64, ()) nvOneLitMem
      (fun (r, ()) m' => r = 1#64 ∧ FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_fid_ilog10

theorem fs_nv_nlog :
    Func.wp fidSchedEnv full_nlogpown_fid_body (500#64, 1#64, 2#64, ()) nvOneLitMem
      (fun (r, ()) m' => r = 500#64 ∧ FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_fid_nlogpown

theorem fs_nv_cmax :
    Func.wp fidSchedEnv full_calc_max_v_fid_body
      (65536#64, 1#64, 2#64, BitVec.ofNat 64 (fullFixedBytes 1), ()) nvOneLitMem
      (fun (r, ()) m' =>
        1 ≤ r.toNat ∧ r.toNat < 2 * dimacsBound ∧
        fullFixedBytes r.toNat + 2 * 40 + 136 ≤ 65536 ∧
        FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_fid_calc_max_v

theorem fs_nv_reduce :
    Func.wp fidSchedEnv full_reduce_fid_body (nvOneLitCfg.hdr, false, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s',
        FullM6HdrInvW nvOneLitCfg nvOneLitF0 [[0], [1]] ext' s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_reduce

theorem fs_nv_probe :
    Func.wp fidSchedEnv full_probe_fid_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s',
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_probe

theorem fs_nv_elim :
    Func.wp fidSchedEnv full_eliminate_fid_body (nvOneLitCfg.hdr, true, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_eliminate

theorem fs_nv_pre :
    Func.wp fidSchedEnv full_preprocess_fid_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ c' ext' s',
        FullM4Compact.FullCfgCompat nvOneLitCfg c' ∧ s'.LengthsOk c' ∧
        FullM6HdrCfgOk c' ∧ M6HdrExtOk ext' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv c' nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem c' ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_preprocess

end AuditSpec

end LeanQbeTest.T.KissatM7FidelitySchedTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7fs_wf := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_fns_wf
abbrev m7fs_acyc := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_acyc
abbrev m7fs_nd := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nd
abbrev m7fs_nx := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_no_exit
abbrev m7fs_ilx := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_ilog_ex_wp
abbrev m7fs_il := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_ilog_wp
abbrev m7fs_nl := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nlog_wp
abbrev m7fs_cm := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_cmax_wp
abbrev m7fs_rd := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_reduce_wp
abbrev m7fs_pr := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_probe_wp
abbrev m7fs_el := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_elim_wp
abbrev m7fs_pp := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_pre_wp
abbrev m7fs_ok := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_mod_ok
abbrev m7fs_nv1 := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nv_ilog
abbrev m7fs_nv2 := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nv_nlog
abbrev m7fs_nv3 := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nv_cmax
abbrev m7fs_nv4 := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nv_reduce
abbrev m7fs_nv5 := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nv_probe
abbrev m7fs_nv6 := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nv_elim
abbrev m7fs_nv7 := @LeanQbeTest.T.KissatM7FidelitySchedTest.fs_nv_pre

#print axioms m7fs_wf
#print axioms m7fs_acyc
#print axioms m7fs_nd
#print axioms m7fs_nx
#print axioms m7fs_ilx
#print axioms m7fs_il
#print axioms m7fs_nl
#print axioms m7fs_cm
#print axioms m7fs_rd
#print axioms m7fs_pr
#print axioms m7fs_el
#print axioms m7fs_pp
#print axioms m7fs_ok
#print axioms m7fs_nv1
#print axioms m7fs_nv2
#print axioms m7fs_nv3
#print axioms m7fs_nv4
#print axioms m7fs_nv5
#print axioms m7fs_nv6
#print axioms m7fs_nv7
