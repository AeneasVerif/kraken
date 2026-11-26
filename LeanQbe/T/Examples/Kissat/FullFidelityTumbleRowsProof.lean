/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleRows
public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
public import LeanQbe.T.Examples.Kissat.PatchModule
import LeanQbe.T.Examples.Kissat.FullFidelityTumbleProofAct
import LeanQbe.T.Examples.Kissat.FullFidelityTumbleProofIngest
import LeanQbe.T.Examples.Kissat.FullFidelityTumbleProofParse
import LeanQbe.T.Examples.Kissat.FullFidelityTumbleProofSat
import LeanQbe.T.Examples.Kissat.FullFidelityTumbleProofLucky

/-!
# Kissat Fidelity Step 11 PR 2 Proof Rows & `Impl` Barrel (`FullFidelityTumbleRowsProof`)

Companion proof barrel for `FullFidelityTumbleRows.lean` (keeping `FullFidelityTumbleRows`
strictly data-pure for `check_firewall.py --require-isa --data-proof`).

Exports:
1. `fidStep11TumReplRows : List SpecEntry` (`6` rows matching `fidStep11TumRepls`).
2. `fidStep11TumBeforeRows : List SpecEntry` (`5` rows matching `fidStep11TumBefores`).
3. `checkCallsOk` certificates and `SpecEntry.Impl` proofs for all `11` PR 2 functions, ready
   for direct plug-in to `FullFidelityAssemblyStep11Proof.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityTumble

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] public section

/-! ## 1. `SpecEntry` Row Tables -/

/-- The `6` replacement specification rows matching `fidStep11TumRepls` in exact order. -/
def fidStep11TumReplRows : List SpecEntry :=
  [ ⟨"full_zero_tables2", [i64], [], Full.fullZeroTables2Spec, true⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClTumSpec, true⟩
  , ⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  , ⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩
  , ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], Full.fullLuckyScanSpec, true⟩ ]

/-- The `5` inserted helper specification rows matching `fidStep11TumBefores` in exact order. -/
def fidStep11TumBeforeRows : List SpecEntry :=
  [ ⟨"full_activate_lit_fid", [i64, i32], [], fullActivateLitFidSpec, true⟩
  , ⟨"full_tumble_finish_fid", [i64], [], fullTumbleFinishFidSpec, true⟩
  , ⟨"full_extend_core_fid", [i64], [], Full.fullExtendSpec, true⟩
  , ⟨"full_unperm_fid", [i64], [], fullUnpermFidSpec, true⟩
  , ⟨"full_lucky_ord_fid", [i64], [i64], fullLuckyOrdFidSpec, true⟩ ]

end

public section

theorem fidStep11TumReplRows_map_name :
    fidStep11TumReplRows.map SpecEntry.name = fidStep11TumReplNames :=
  rfl

theorem fidStep11TumBeforeRows_map_name :
    fidStep11TumBeforeRows.map SpecEntry.name = fidStep11TumBeforeNames :=
  rfl

/-! ## 2. Per-Function `checkCallsOk` Certificates (`11/11`) -/

theorem fidStep11ZeroTables2_callsOk :
    fidStep11ZeroTables2Fn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem fidStep11InitHdr_callsOk :
    fidStep11InitHdrFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem fidStep11ActivateLit_callsOk :
    fidStep11ActivateLitFn.checkCallsOk
      [ ("full_heap_push", [i64, i32], []) ] [] = true := by
  t_kernel_rfl

theorem fidStep11IngestCl_callsOk :
    fidStep11IngestClFn.checkCallsOk
      [ ("kissat_next_lit", [i64, i64], [i64])
      , ("full_activate_lit_fid", [i64, i32], [])
      , ("full_assign_lvl", [i64, i32, i32, i32], [])
      , ("full_add_clause", [i64, i32, i32, .bool], [i64]) ] [] = true := by
  t_kernel_rfl

theorem fidStep11TumbleFinish_callsOk :
    fidStep11TumbleFinishFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem fidStep11ParseBodyM6_callsOk :
    fidStep11ParseBodyM6Fn.checkCallsOk
      [ ("kissat_skip_ws_comments", [i64, i64], [i64])
      , ("full_skip_cl", [i64, i64], [.bool])
      , ("full_ingest_cl", [i64, i64], [i64])
      , ("full_propagate", [i64], [i64])
      , ("full_tumble_finish_fid", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem fidStep11ExtendCore_callsOk :
    fidStep11ExtendCoreFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem fidStep11Unperm_callsOk :
    fidStep11UnpermFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem fidStep11Extend_callsOk :
    fidStep11ExtendFn.checkCallsOk
      [ ("full_extend_core_fid", [i64], [])
      , ("full_unperm_fid", [i64], []) ] [] = true := by
  t_kernel_rfl

theorem fidStep11LuckyOrd_callsOk :
    fidStep11LuckyOrdFn.checkCallsOk [] [] = true := by
  t_kernel_rfl

theorem fidStep11LuckyScan_callsOk :
    fidStep11LuckyScanFn.checkCallsOk
      [ ("full_lucky_ord_fid", [i64], [i64])
      , ("full_assign", [i64, i32, i32], [])
      , ("full_propagate", [i64], [i64])
      , ("full_backtrack", [i64, i64], [])
      , ("full_analyze", [i64], [i64]) ] [] = true := by
  t_kernel_rfl

/-! ## 3. Parametric `Fn.wp` / `Impl` Lemmas (`11/11`) -/

theorem fidStep11ZeroTables2_impl (Γ : Env) :
    ∀ a m Q X, Full.fullZeroTables2Spec a m Q X →
      Func.wp Γ fidStep11ZeroTables2Fn.body a m Q X :=
  full_zero_tables2_fid_wp Γ

theorem fidStep11InitHdr_impl (Γ : Env) :
    ∀ a m Q X, Full.fullInitHdrSpec a m Q X →
      Func.wp Γ fidStep11InitHdrFn.body a m Q X :=
  full_init_hdr_fid_wp Γ

theorem fidStep11ActivateLit_impl (Γ : Env)
    (hHeapPush : ∀ a m Q X, Full.fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullActivateLitFidSpec a m Q X →
      Func.wp Γ fidStep11ActivateLitFn.body a m Q X :=
  full_activate_lit_fid_wp Γ hHeapPush

theorem fidStep11IngestCl_impl (Γ : Env)
    (hLit : ∀ a m Q X, kissatNextLitSpec a m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] a m Q X)
    (hAct : ∀ a m Q X, fullActivateLitFidSpec a m Q X →
      Γ "full_activate_lit_fid" [i64, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hAddCl : ∀ a m Q X, Full.fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullIngestClTumSpec a m Q X →
      Func.wp Γ fidStep11IngestClFn.body a m Q X :=
  full_ingest_cl_tum_wp Γ hLit hAct hAssign hAddCl

theorem fidStep11TumbleFinish_impl (Γ : Env) :
    ∀ a m Q X, fullTumbleFinishFidSpec a m Q X →
      Func.wp Γ fidStep11TumbleFinishFn.body a m Q X :=
  full_tumble_finish_fid_wp Γ

theorem fidStep11ParseBodyM6_impl (Γ : Env)
    (hSkip : ∀ a m Q X, Full.fullSkipClSpec a m Q X →
      Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, fullIngestClTumSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X)
    (hFinish : ∀ a m Q X, fullTumbleFinishFidSpec a m Q X →
      Γ "full_tumble_finish_fid" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Func.wp Γ fidStep11ParseBodyM6Fn.body a m Q X :=
  full_parse_body_tum_wp Γ hSkip hIngest hProp hSwc hFinish

theorem fidStep11ExtendCore_impl (Γ : Env) :
    ∀ a m Q X, Full.fullExtendSpec a m Q X →
      Func.wp Γ fidStep11ExtendCoreFn.body a m Q X :=
  full_extend_core_fid_wp Γ

theorem fidStep11Unperm_impl (Γ : Env) :
    ∀ a m Q X, fullUnpermFidSpec a m Q X →
      Func.wp Γ fidStep11UnpermFn.body a m Q X :=
  full_unperm_fid_wp Γ

theorem fidStep11Extend_impl (Γ : Env)
    (hCore : ∀ a m Q X, Full.fullExtendSpec a m Q X →
      Γ "full_extend_core_fid" [i64] [] a m Q X)
    (hUnperm : ∀ a m Q X, fullUnpermFidSpec a m Q X →
      Γ "full_unperm_fid" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullExtendSpec a m Q X →
      Func.wp Γ fidStep11ExtendFn.body a m Q X :=
  full_extend_tum_wp Γ hCore hUnperm

theorem fidStep11LuckyOrd_impl (Γ : Env) :
    ∀ a m Q X, fullLuckyOrdFidSpec a m Q X →
      Func.wp Γ fidStep11LuckyOrdFn.body a m Q X :=
  full_lucky_ord_fid_wp Γ

theorem fidStep11LuckyScan_impl (Γ : Env)
    (hOrd : ∀ a m Q X, fullLuckyOrdFidSpec a m Q X →
      Γ "full_lucky_ord_fid" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAna : ∀ a m Q X, Full.fullAnalyzeSpec a m Q X →
      Γ "full_analyze" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullLuckyScanSpec a m Q X →
      Func.wp Γ fidStep11LuckyScanFn.body a m Q X :=
  full_lucky_scan_tum_wp Γ hOrd hAssign hBt hProp hAna

end

end LeanQbe.T.Examples.Kissat.FullFidelityTumble
