module

public import LeanQbe.T.Examples.Kissat.FullM6Hdr
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6Hdr
meta import LeanQbe.T.Examples.Kissat.FullM6HdrProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Backend Compilation Guards, and Axiom Audit for Kissat M6 Header (`FullM6Hdr`)

1. Executable `#guard` checks on `FullM6Hdr` layout (`144 + 288 = 432` words = `3,456 B`,
   disjoint decision-rate words `1..7` & tier/watermark words `8..287`), `m6HdrModule` (`27` fns +
   `5` externs, `0` exits), `checkAcyclic = true`, M6 drop-in handles (`m6HdrDecideFn`,
   `m6HdrAnalyzeRsnFn`, `m6HdrAnalyzeFn`, etc.), `PrintCpp`, `PrintQbe`, and `Fn.legal` across
   `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems for `m6Hdr_fns_wf`, `m6Hdr_acyclic`, automatic framing
   over frozen `FullMem`, all `27` parametric UNSAT-only `Func.wp` proofs, closed `32`-row
   `m6Hdr_moduleOk`, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeLegacyTest.KissatM6HdrTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open Kraken.Bedrock2.Test

/-! ## 1. Static Layout Checks, Module Guards & 4-ISA Backend Compilation Guards -/

#guard fullM6HdrBaseWords == 144
#guard fullM6HdrBaseBytes == 1152
#guard fullM6ExtWords == 288
#guard fullM6ExtBytes == 2304
#guard fullM6HdrTotalWords == 432
#guard fullM6HdrTotalBytes == 3456
#guard m6WMagic == 0
#guard m6WDrState == 1
#guard m6WDrPrev == 2
#guard m6WDrSb == 4
#guard m6WDrSe == 6
#guard m6WTier1 == 8
#guard m6WTier2 == 10
#guard m6WGlueNext == 12
#guard m6WGlueInterval == 13
#guard m6WTotalUsed == 14
#guard m6WDelayCnt == 16
#guard m6WDelayCur == 20
#guard m6WWmBase == 24
#guard m6WUsed0 == 32
#guard m6WUsed1 == 160
#guard m6WUsed1 + fullM6HdrGlueBins == fullM6ExtWords

#guard m6HdrModule.checkAcyclic == true
#guard m6HdrModule.exits.isEmpty == true
#guard m6Hdr_fns.length == 27
#guard m6HdrExterns.length == 5
#guard m6HdrSpecTable.length == 32
#guard m6HdrSpecTable.all (·.noExit) == true
#guard m6HdrExtReadyFn.name == "full_m6_ext_ready"
#guard m6HdrRecomputeTiersFn.name == "full_recompute_tiers_m6"
#guard m6HdrDrInitFn.name == "full_dr_init_m6"
#guard m6HdrDrUpdateFn.name == "full_dr_update_m6"
#guard m6HdrDrAllowFn.name == "full_dr_allow_m6"
#guard m6HdrDecideFn.name == "full_decide"
#guard m6HdrAnalyzeRsnFn.name == "full_analyze_rsn"
#guard m6HdrAnalyzeFn.name == "full_analyze"
#guard (ppTModule m6HdrModule).isOk
#guard (PrintQbe.module m6HdrModule).isOk
#guard (ppModule (m6Hdr_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6Hdr_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6Hdr_fns.map (Fn.legal .x64AVX2))).isOk
#guard m6Hdr_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m6h_wf : ∀ f ∈ m6Hdr_fns, f.Wf := m6Hdr_fns_wf
theorem m6h_acyc : m6HdrModule.checkAcyclic = true := m6Hdr_acyclic
theorem m6h_spec_len : m6HdrSpecTable.length = 32 := m6HdrSpecTable_length
theorem m6h_spec_no_exit : m6HdrSpecTable.all (·.noExit) = true := m6HdrSpecTable_allNoExit

theorem m6h_to_region {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {m : Mem 64}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : FullM6HdrMem c ext s m) :
    region (m6ExtAddr c.hdr) (fullM6ExtBytes + c.avail) m :=
  fullM6HdrMem_to_region hcfg hext hlen hm

theorem m6h_frame_full {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {P : (FullState → Mem 64 → Prop) → Prop}
    (hfn : ∀ F : Mem 64 → Prop, (FullMem c s ⋆ F) m → P (fun s' m' => (FullMem c s' ⋆ F) m'))
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    P (fun s' m' => (FullM6HdrMem c ext s' ⋆ R) m') :=
  fullM6Hdr_frame_full hfn hm

theorem m6h_hdr_sizeof_wp (Γ : Env) :
    ∀ a m Q X, m6HdrSizeofSpec a m Q X → Func.wp Γ full_m6_hdr_sizeof_body a m Q X :=
  full_m6_hdr_sizeof_wp Γ

theorem m6h_ext_sizeof_wp (Γ : Env) :
    ∀ a m Q X, m6ExtSizeofSpec a m Q X → Func.wp Γ full_m6_ext_sizeof_body a m Q X :=
  full_m6_ext_sizeof_wp Γ

theorem m6h_init_wp (Γ : Env) :
    ∀ a m Q X, m6HdrInitSpec a m Q X → Func.wp Γ m6_hdr_init_body a m Q X :=
  m6_hdr_init_wp Γ

theorem m6h_reset_wp (Γ : Env)
    (hInit : ∀ a m Q X, m6HdrInitSpec a m Q X → Γ "m6_hdr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrResetSpec a m Q X → Func.wp Γ m6_hdr_reset_body a m Q X :=
  m6_hdr_reset_wp Γ hInit

theorem m6h_ensure_wp (Γ : Env)
    (hInit : ∀ a m Q X, m6HdrInitSpec a m Q X → Γ "m6_hdr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6ExtEnsureInitSpec a m Q X → Func.wp Γ m6_ext_ensure_init_body a m Q X :=
  m6_ext_ensure_init_wp Γ hInit

theorem m6h_ready_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrExtReadySpec a m Q X → Func.wp Γ m6_hdr_ext_ready_body a m Q X :=
  m6_hdr_ext_ready_wp Γ hEnsure

theorem m6h_mem_init_wp (Γ : Env)
    (hInitState : ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hHdrInit : ∀ a m Q X, m6HdrInitSpec a m Q X → Γ "m6_hdr_init" [i64] [] a m Q X) :
    ∀ a m Q X, fullM6MemInitSpec a m Q X → Func.wp Γ full_m6_mem_init_body a m Q X :=
  full_m6_mem_init_wp Γ hInitState hHdrInit

theorem m6h_sync_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ m6_hdr_sync_legacy_tiers_body a m Q X :=
  m6_hdr_sync_legacy_tiers_wp Γ hEnsure

theorem m6h_recomp_mode_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_recompute_tiers_mode_body a m Q X :=
  m6_hdr_recompute_tiers_mode_wp Γ hEnsure hSync

theorem m6h_recomp_wp (Γ : Env)
    (hMode : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_recompute_tiers_mode" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ m6_hdr_recompute_tiers_body a m Q X :=
  m6_hdr_recompute_tiers_wp Γ hMode

theorem m6h_upd_tiers_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ m6_hdr_update_tier_limits_body a m Q X :=
  m6_hdr_update_tier_limits_wp Γ hEnsure hRecomp

theorem m6h_rec_used_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_record_used_body a m Q X :=
  m6_hdr_record_used_wp Γ hEnsure

theorem m6h_get_t1_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp Γ m6_hdr_get_tier1_body a m Q X :=
  m6_hdr_get_tier1_wp Γ hEnsure

theorem m6h_get_t2_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Func.wp Γ m6_hdr_get_tier2_body a m Q X :=
  m6_hdr_get_tier2_wp Γ hEnsure

theorem m6h_delaying_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Func.wp Γ m6_hdr_delaying_body a m Q X :=
  m6_hdr_delaying_wp Γ hEnsure

theorem m6h_bump_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_bump_delay_body a m Q X :=
  m6_hdr_bump_delay_wp Γ hEnsure

theorem m6h_reduce_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_reduce_delay_body a m Q X :=
  m6_hdr_reduce_delay_wp Γ hEnsure

theorem m6h_reset_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_reset_delay_body a m Q X :=
  m6_hdr_reset_delay_wp Γ hEnsure

theorem m6h_get_wm_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Func.wp Γ m6_hdr_get_watermark_body a m Q X :=
  m6_hdr_get_watermark_wp Γ hEnsure

theorem m6h_set_wm_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Func.wp Γ m6_hdr_set_watermark_body a m Q X :=
  m6_hdr_set_watermark_wp Γ hEnsure

theorem m6h_add_ticks_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_add_ticks_body a m Q X :=
  m6_hdr_add_ticks_wp Γ hEnsure

theorem m6h_dr_init_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X → Func.wp Γ m6_hdr_dr_init_body a m Q X :=
  m6_hdr_dr_init_wp Γ hEnsure

theorem m6h_dr_upd_wp (Γ : Env)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X → Func.wp Γ m6_hdr_dr_update_body a m Q X :=
  m6_hdr_dr_update_wp Γ hDrInit

theorem m6h_dr_allow_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrAllowSpec a m Q X → Func.wp Γ m6_hdr_dr_allow_body a m Q X :=
  m6_hdr_dr_allow_wp Γ hEnsure

theorem m6h_decide_wp (Γ : Env)
    (hNextDec : ∀ a m Q X, Full.fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDecideSpec a m Q X → Func.wp Γ m6_hdr_decide_body a m Q X :=
  m6_hdr_decide_wp Γ hNextDec hAssign hDrInit

theorem m6h_ana_rsn_wp (Γ : Env)
    (hRecUsed : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_record_used" [i64, i64] [] a m Q X)
    (hAnaRsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m6HdrAnalyzeRsnSpec a m Q X → Func.wp Γ m6_hdr_analyze_rsn_body a m Q X :=
  m6_hdr_analyze_rsn_wp Γ hRecUsed hAnaRsn

theorem m6h_ana_wp (Γ : Env)
    (hUpd : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_update_tier_limits" [i64] [] a m Q X)
    (hDrUpd : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_update" [i64] [] a m Q X)
    (hAna : ∀ a m Q X, Full.fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6HdrAnalyzeSpec a m Q X → Func.wp Γ m6_hdr_analyze_body a m Q X :=
  m6_hdr_analyze_wp Γ hUpd hDrUpd hAna

theorem m6h_mod_ok : ModuleOk m6HdrEnv m6HdrModule := m6Hdr_moduleOk

theorem m6h_nv_hdr_sz :
    Func.wp m6HdrEnv full_m6_hdr_sizeof_body () nvM6HdrMem
      (fun (r, ()) m' => r = 3456#64 ∧ FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_full_m6_hdr_sizeof

theorem m6h_nv_ext_sz :
    Func.wp m6HdrEnv full_m6_ext_sizeof_body () nvM6HdrMem
      (fun (r, ()) m' => r = 2304#64 ∧ FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_full_m6_ext_sizeof

theorem m6h_nv_init :
    Func.wp m6HdrEnv m6_hdr_init_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext', M6HdrExtInitOk ext' ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_m6_hdr_init

theorem m6h_nv_reset :
    Func.wp m6HdrEnv m6_hdr_reset_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', M6HdrExtInitOk ext' ∧ s'.scratch.tier1 = 2#64 ∧
        s'.scratch.tier2 = 6#64 ∧ nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_hdr_reset

theorem m6h_nv_recomp :
    Func.wp m6HdrEnv m6_hdr_recompute_tiers_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        M6HdrBaseDelayedPres nvOneLitState s' ∧ M6HdrExtOk ext' ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_hdr_recompute_tiers

theorem m6h_nv_dr_upd :
    Func.wp m6HdrEnv m6_hdr_dr_update_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext', M6HdrExtInitOk ext' ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_m6_hdr_dr_update

theorem m6h_nv_dr_alw :
    Func.wp m6HdrEnv m6_hdr_dr_allow_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext', (r = true ∨ r = false) ∧ M6HdrExtInitOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_m6_hdr_dr_allow

theorem m6h_nv_ana :
    Func.wp m6HdrEnv m6_hdr_analyze_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', r = 20#64 ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m6_hdr_analyze

theorem m6h_nv_tiny :
    Func.wp m6HdrEnv full_m6_mem_init_body
      (0x2000#64, 0x2000#64 + BitVec.ofNat 64 nvTinyCnfBytes.length,
       0x2000#64 + BitVec.ofNat 64 nvTinyCnfBytes.length, 1000#64, 100#64, ())
      nvTinyInitMem
      (fun (r, ()) m' => r = 0#64 ∧
        (bytes 0x2000#64 nvTinyCnfBytes ⋆
          region (0x2000#64 + BitVec.ofNat 64 nvTinyCnfBytes.length) 1000) m')
      (fun _ _ _ _ => False) :=
  nv_full_m6_mem_init_tiny

end AuditSpec

end LeanQbeLegacyTest.KissatM6HdrTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m6h_a_wf := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_wf
abbrev m6h_a_acyc := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_acyc
abbrev m6h_a_reg := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_to_region
abbrev m6h_a_frm := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_frame_full
abbrev m6h_a_init := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_init_wp
abbrev m6h_a_rst := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_reset_wp
abbrev m6h_a_ens := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_ensure_wp
abbrev m6h_a_rdy := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_ready_wp
abbrev m6h_a_minit := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_mem_init_wp
abbrev m6h_a_sync := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_sync_wp
abbrev m6h_a_rcm := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_recomp_mode_wp
abbrev m6h_a_rc := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_recomp_wp
abbrev m6h_a_upd := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_upd_tiers_wp
abbrev m6h_a_rec := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_rec_used_wp
abbrev m6h_a_gt1 := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_get_t1_wp
abbrev m6h_a_gt2 := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_get_t2_wp
abbrev m6h_a_dly := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_delaying_wp
abbrev m6h_a_bdl := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_bump_delay_wp
abbrev m6h_a_rdl := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_reduce_delay_wp
abbrev m6h_a_zdl := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_reset_delay_wp
abbrev m6h_a_gwm := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_get_wm_wp
abbrev m6h_a_swm := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_set_wm_wp
abbrev m6h_a_tks := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_add_ticks_wp
abbrev m6h_a_dri := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_dr_init_wp
abbrev m6h_a_dru := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_dr_upd_wp
abbrev m6h_a_dra := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_dr_allow_wp
abbrev m6h_a_dec := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_decide_wp
abbrev m6h_a_arsn := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_ana_rsn_wp
abbrev m6h_a_ana := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_ana_wp
abbrev m6h_a_mod := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_mod_ok
abbrev m6h_a_nv_i := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_nv_init
abbrev m6h_a_nv_r := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_nv_reset
abbrev m6h_a_nv_t := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_nv_recomp
abbrev m6h_a_nv_u := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_nv_dr_upd
abbrev m6h_a_nv_d := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_nv_dr_alw
abbrev m6h_a_nv_a := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_nv_ana
abbrev m6h_a_nv_z := @LeanQbeLegacyTest.KissatM6HdrTest.m6h_nv_tiny

#print axioms m6h_a_wf
#print axioms m6h_a_acyc
#print axioms m6h_a_reg
#print axioms m6h_a_frm
#print axioms m6h_a_init
#print axioms m6h_a_rst
#print axioms m6h_a_ens
#print axioms m6h_a_rdy
#print axioms m6h_a_minit
#print axioms m6h_a_sync
#print axioms m6h_a_rcm
#print axioms m6h_a_rc
#print axioms m6h_a_upd
#print axioms m6h_a_rec
#print axioms m6h_a_gt1
#print axioms m6h_a_gt2
#print axioms m6h_a_dly
#print axioms m6h_a_bdl
#print axioms m6h_a_rdl
#print axioms m6h_a_zdl
#print axioms m6h_a_gwm
#print axioms m6h_a_swm
#print axioms m6h_a_tks
#print axioms m6h_a_dri
#print axioms m6h_a_dru
#print axioms m6h_a_dra
#print axioms m6h_a_dec
#print axioms m6h_a_arsn
#print axioms m6h_a_ana
#print axioms m6h_a_mod
#print axioms m6h_a_nv_i
#print axioms m6h_a_nv_r
#print axioms m6h_a_nv_t
#print axioms m6h_a_nv_u
#print axioms m6h_a_nv_d
#print axioms m6h_a_nv_a
#print axioms m6h_a_nv_z
