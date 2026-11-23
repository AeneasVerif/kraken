module

public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiersProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
meta import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiersProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat M7 `FullM7ParityVivTiers`

No blanket expose attributes, no local attributes, no unrestricted imports, UNSAT-only:
1. Executable `#guard` checks on `m7ParityVivTiersModule` (`4` fns, `12` externs, `0` exits),
   `m7ParityVivTiersSpecTable` (`16` rows, `noExit = true`), `m7ParityVivTiersPatchFns` /
   `m7ParityVivTiersPatchRows` (`5` rows), `m7ParityVivTiersSplicedModule` (`410` fns, `0` exits),
   `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and
   `.x64AVX512`.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, standalone `ModuleOk`,
   `4` parametric `Func.wp` contracts + `"full_propagate_ignore"` canonical bridge, `410`-fn
   spliced `checkAcyclic` / `ModuleOk` / `patchRows_{sigs,noExit}` / `solve_bytes_sound` /
   `unsat_nv`, and all `4` concrete `Mem 64` UNSAT non-vacuity theorems.
3. Single-line `< 115c` `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7ParityVivTiersTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard m7ParityVivTiers_fns.length == 4
#guard m7ParityVivTiersExterns.length == 12
#guard m7ParityVivTiersModule.checkAcyclic == true
#guard m7ParityVivTiersModule.exits.isEmpty == true
#guard m7ParityVivTiersSpecTable.length == 16
#guard m7ParityVivTiersSpecTable.all (·.noExit) == true
#guard m7ParityVivTiersSpecTable.map (fun e => (e.name, e.as, e.rs)) ==
  m7ParityVivTiersModule.sigs
#guard m7ParityVivTiers_fns.map Fn.name ==
  [ "m6_hdr_sync_legacy_tiers", "full_propagate_ignore_hot"
  , "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr" ]
#guard m7ParityVivTiersPatchFns.length == 5
#guard m7ParityVivTiersPatchFns.map Fn.name ==
  [ "m6_hdr_sync_legacy_tiers", "full_propagate_ignore_hot", "full_propagate_ignore"
  , "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr" ]
#guard m7ParityVivTiersPatchRows.map (fun e => (e.name, e.as, e.rs)) ==
  m7ParityVivTiersPatchFns.map Fn.sig
#guard m7ParityVivTiersPatchRows.all (·.noExit) == true
#guard m7ParityVivTiersSplicedFns.length == 410
#guard m7ParityVivTiersSplicedModule.exits.isEmpty == true
#guard (ppTModule m7ParityVivTiersModule).isOk
#guard (PrintQbe.module m7ParityVivTiersModule).isOk
#guard (ppModule (m7ParityVivTiers_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7ParityVivTiers_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7ParityVivTiers_fns.map (Fn.legal .x64AVX2))).isOk
#guard m7ParityVivTiers_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem fvt_sync_wf : Func.Wf FullM7ParityVivTiers.m6_hdr_sync_legacy_tiers_body :=
  m6_hdr_sync_legacy_tiers_wf
theorem fvt_prop_wf : Func.Wf FullM7ParityVivTiers.full_propagate_ignore_hot_body :=
  full_propagate_ignore_hot_wf
theorem fvt_vt_wf : Func.Wf FullM7ParityVivTiers.full_vivify_tier_m6_hdr_body :=
  full_vivify_tier_m6_hdr_wf
theorem fvt_viv_wf : Func.Wf FullM7ParityVivTiers.full_vivify_m6_hdr_body :=
  full_vivify_m6_hdr_wf
theorem fvt_fns_wf : ∀ f ∈ m7ParityVivTiersFns, f.Wf := m7ParityVivTiers_fns_wf
theorem fvt_patch_wf : ∀ f ∈ m7ParityVivTiersPatchFns, f.Wf := m7ParityVivTiersPatchFns_wf
theorem fvt_acyc : m7ParityVivTiersModule.checkAcyclic = true := m7ParityVivTiers_acyclic
theorem fvt_spliced_acyc : m7ParityVivTiersSplicedModule.checkAcyclic = true :=
  m7ParityVivTiers_spliced_checkAcyclic
theorem fvt_tbl_len : m7ParityVivTiersSpecTable.length = 16 := m7ParityVivTiersSpecTable_length

theorem fvt_noExit :
    ∀ f as bs xs m Q X X',
      m7ParityVivTiersEnv f as bs xs m Q X → m7ParityVivTiersEnv f as bs xs m Q X' :=
  m7ParityVivTiersEnv_noExit

theorem fvt_sync_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ FullM7ParityVivTiers.m6_hdr_sync_legacy_tiers_body a m Q X :=
  FullM7ParityVivTiers.m6_hdr_sync_legacy_tiers_wp Γ hEnsure

theorem fvt_prop_wp (Γ : Env)
    (hOvf : ∀ a m Q X, FullM7BcpHot.fullPropLitOvfHotSpec a m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] a m Q X)
    (hChrono : ∀ a m Q X, FullM7BcpHot.fullPropChronoHotSpec a m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.FullPropDecSpecs.fullPropagateIgnoreSpec a m Q X →
      Func.wp Γ FullM7ParityVivTiers.full_propagate_ignore_hot_body a m Q X :=
  FullM7ParityVivTiers.full_propagate_ignore_hot_wp Γ hOvf hChrono

theorem fvt_prop_canon_wp (Γ : Env)
    (hOvf : ∀ a m Q X, FullM7BcpHot.fullPropLitOvfHotSpec a m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] a m Q X)
    (hChrono : ∀ a m Q X, FullM7BcpHot.fullPropChronoHotSpec a m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Func.wp Γ FullM7ParityVivTiers.full_propagate_ignore_hot_body a m Q X :=
  full_propagate_ignore_canon_hot_wp Γ hOvf hChrono

theorem fvt_vt_wp (Γ : Env)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCol : ∀ a m Q X, FullM6VivBackbone.fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCnt : ∀ a m Q X, FullM6VivBackbone.fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, FullM6VivBackbone.fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSort : ∀ a m Q X, FullM6VivBackbone.fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hCls : ∀ a m Q X, FullM6VivBackbone.fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClr : ∀ a m Q X, FullM6VivBackbone.fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Func.wp Γ FullM7ParityVivTiers.full_vivify_tier_m6_hdr_body a m Q X :=
  FullM7ParityVivTiers.full_vivify_tier_m6_hdr_wp Γ hBt hCol hCnt hKeys hSort hCls hProp hClr

theorem fvt_viv_wp (Γ : Env)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVt : ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6aVivifySpec a m Q X →
      Func.wp Γ FullM7ParityVivTiers.full_vivify_m6_hdr_body a m Q X :=
  FullM7ParityVivTiers.full_vivify_m6_hdr_wp Γ hBt hSync hGetWm hVt

theorem fvt_tbl_impl :
    TableImpl m7ParityVivTiersEnv m7ParityVivTiersModule.fns m7ParityVivTiersSpecTable :=
  m7ParityVivTiers_tableImpl

theorem fvt_mod_ok : ModuleOk m7ParityVivTiersEnv m7ParityVivTiersModule :=
  m7ParityVivTiers_moduleOk

theorem fvt_patch_sigs
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (patchRows m7ParityVivTiersPatchRows [] (m7SpecTable tBve solveSpec)).map
        (fun e => (e.name, e.as, e.rs)) =
      m7ParityVivTiersSplicedFns.map Fn.sig :=
  m7ParityVivTiers_patchRows_sigs tBve solveSpec hBveSigs

theorem fvt_patch_noExit
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveNoExit : tBve.all SpecEntry.noExit = true) :
    (patchRows m7ParityVivTiersPatchRows [] (m7SpecTable tBve solveSpec)).all
        SpecEntry.noExit = true :=
  m7ParityVivTiers_patchRows_noExit tBve solveSpec hBveNoExit

theorem fvt_spliced_mod_ok
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve) :
    ModuleOk (M7pHotEnv (mkM7Env tBve solveSpec)) m7ParityVivTiersSplicedModule :=
  m7ParityVivTiers_spliced_moduleOk tBve solveSpec hWeaken hSolveMonoX
    hBveSigs hBveNoExit hBveSpecs hBveOk

theorem fvt_spliced_solve_sound
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (M7pHotEnv (mkM7Env tBve fullM6SolveBytesSpec)) FullM6Orch.kissat_solve_bytes_body
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
  m7ParityVivTiers_spliced_solve_bytes_sound tBve hBveSigs hBveNoExit hBveSpecs hBveOk
    hcfit hwfit hm

theorem fvt_spliced_unsat_nv
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (M7pHotEnv (mkM7Env tBve fullM6SolveBytesCoreModelSpec))
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
  m7ParityVivTiers_spliced_unsat_nv tBve hBveSigs hBveNoExit hBveSpecs hBveOk

theorem fvt_nv_sync :
    Func.wp m7ParityVivTiersEnv FullM7ParityVivTiers.m6_hdr_sync_legacy_tiers_body
      (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        M6HdrExtOk ext' ∧ nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m7p_sync_legacy_tiers

theorem fvt_nv_prop :
    Func.wp m7ParityVivTiersEnv full_propagate_ignore_hot_body
      (FastCore.nvFastPropCfg.hdr, 0xFFFFFFFF#64, ()) FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧ (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', FullMem FastCore.nvFastPropCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7p_propagate_ignore_hot

theorem fvt_nv_vt :
    Func.wp m7ParityVivTiersEnv FullM7ParityVivTiers.full_vivify_tier_m6_hdr_body
      (nvOneLitCfg.hdr, 0#64, 1#64, 100#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s', FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7p_vivify_tier

theorem fvt_nv_viv :
    Func.wp m7ParityVivTiersEnv FullM7ParityVivTiers.full_vivify_m6_hdr_body
      (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_m7p_vivify

end LeanQbeTest.T.KissatM7ParityVivTiersTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7pvt_wf_s := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_sync_wf
abbrev m7pvt_wf_p := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_prop_wf
abbrev m7pvt_wf_t := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_vt_wf
abbrev m7pvt_wf_v := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_viv_wf
abbrev m7pvt_wf_all := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_fns_wf
abbrev m7pvt_wf_pat := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_patch_wf
abbrev m7pvt_acyc := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_acyc
abbrev m7pvt_sp_acyc := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_spliced_acyc
abbrev m7pvt_tbl_len := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_tbl_len
abbrev m7pvt_nx := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_noExit
abbrev m7pvt_wp_s := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_sync_wp
abbrev m7pvt_wp_p := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_prop_wp
abbrev m7pvt_wp_pc := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_prop_canon_wp
abbrev m7pvt_wp_t := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_vt_wp
abbrev m7pvt_wp_v := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_viv_wp
abbrev m7pvt_tbl := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_tbl_impl
abbrev m7pvt_mod := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_mod_ok
abbrev m7pvt_pat_s := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_patch_sigs
abbrev m7pvt_pat_nx := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_patch_noExit
abbrev m7pvt_sp_mod := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_spliced_mod_ok
abbrev m7pvt_sp_sb := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_spliced_solve_sound
abbrev m7pvt_sp_nv := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_spliced_unsat_nv
abbrev m7pvt_nv_s := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_nv_sync
abbrev m7pvt_nv_p := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_nv_prop
abbrev m7pvt_nv_t := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_nv_vt
abbrev m7pvt_nv_v := @LeanQbeTest.T.KissatM7ParityVivTiersTest.fvt_nv_viv

#print axioms m7pvt_wf_s
#print axioms m7pvt_wf_p
#print axioms m7pvt_wf_t
#print axioms m7pvt_wf_v
#print axioms m7pvt_wf_all
#print axioms m7pvt_wf_pat
#print axioms m7pvt_acyc
#print axioms m7pvt_sp_acyc
#print axioms m7pvt_tbl_len
#print axioms m7pvt_nx
#print axioms m7pvt_wp_s
#print axioms m7pvt_wp_p
#print axioms m7pvt_wp_pc
#print axioms m7pvt_wp_t
#print axioms m7pvt_wp_v
#print axioms m7pvt_tbl
#print axioms m7pvt_mod
#print axioms m7pvt_pat_s
#print axioms m7pvt_pat_nx
#print axioms m7pvt_sp_mod
#print axioms m7pvt_sp_sb
#print axioms m7pvt_sp_nv
#print axioms m7pvt_nv_s
#print axioms m7pvt_nv_p
#print axioms m7pvt_nv_t
#print axioms m7pvt_nv_v
