/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5Otfs
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5Otfs
meta import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, Backend Compilation Guards, & Axiom Audit for M5 (`FullM5Otfs`)

1. Executable `#guard` checks on `m5OtfsModule` (`8` fns + `11` externs, `0` exits),
   `checkAcyclic = true`, `m5OtfsSpecTable` (`19` rows), `PrintCpp`, `PrintQbe`, and `Fn.legal`
   across `.aarch64`, `.scalar64`, and `.x64AVX2`.
2. Restated audit theorems covering `m5Otfs_fns_wf`, `m5Otfs_acyclic`, all `8` parametric
   `Func.wp` proofs against canonical `FullSpec2` contracts, `m5Otfs_moduleOk`, and
   concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT model proofs).
3. Single-line `#print axioms` audit across all exported theorems
   (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeLegacyTest.KissatM5OtfsTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open Kraken.Bedrock2.Test

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m5OtfsModule.checkAcyclic == true
#guard m5OtfsModule.exits.isEmpty
#guard m5Otfs_fns.length == 8
#guard m5Otfs_fns.map Fn.name ==
  ["full_unwatch_large", "full_otfs_large", "full_otfs_bin_m5",
   "full_deduce_1uip_m5", "full_one_lit_confl_m5", "full_prop_lit_chrono",
   "full_prop_lit", "full_propagate_ignore"]
#guard m5OtfsExterns.length == 11
#guard m5OtfsSpecTable.length == 19
#guard m5OtfsSpecTable.map (fun e => (e.name, e.as, e.rs)) ==
  (m5Otfs_fns.map (fun f => (f.name, f.as, f.rs)) ++
   m5OtfsExterns.map (fun x => (x.name, x.as, x.rs)))
#guard (ppTModule m5OtfsModule).isOk
#guard (PrintQbe.module m5OtfsModule).isOk
#guard (ppModule (m5Otfs_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5Otfs_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5Otfs_fns.map (Fn.legal .x64AVX2))).isOk

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m5o_wf : ∀ f ∈ m5Otfs_fns, f.Wf :=
  m5Otfs_fns_wf

theorem m5o_acyc : m5OtfsModule.checkAcyclic = true :=
  m5Otfs_acyclic

theorem m5o_unwatch_wp (Γ : Env) :
    ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Func.wp Γ FullM5Otfs.full_unwatch_large_body a m Q X :=
  FullM5Otfs.full_unwatch_large_wp Γ

theorem m5o_otfs_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Func.wp Γ FullM5Otfs.full_otfs_large_body a m Q X :=
  FullM5Otfs.full_otfs_large_wp Γ hDefrag hUnw hPush

theorem m5o_otfs_bin_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Func.wp Γ FullM5Otfs.full_otfs_bin_m5_body a m Q X :=
  FullM5Otfs.full_otfs_bin_m5_wp Γ hNext hDefrag hUnw hPush

theorem m5o_deduce_1uip_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin_m5" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
      Func.wp Γ FullM5Otfs.full_deduce_1uip_m5_body a m Q X :=
  FullM5Otfs.full_deduce_1uip_m5_wp Γ hAlit hArsn hClear hOtfsLarge hOtfsBin hOtfsSub

theorem m5o_one_lit_confl_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hDet : ∀ args m Q X, Full.fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hUnw : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullOneLitConflSpec args m Q X →
      Func.wp Γ FullM5Otfs.full_one_lit_confl_m5_body args m Q X :=
  FullM5Otfs.full_one_lit_confl_m5_wp Γ hDefrag hDet hBt hAss hUnw hPush

theorem m5o_prop_chrono_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hRaw : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Func.wp Γ FullM5Otfs.full_prop_lit_chrono_body a m Q X :=
  FullM5Otfs.full_prop_lit_chrono_wp Γ hDefrag hUnw hRaw hPush

theorem m5o_prop_lit_wp (Γ : Env)
    (hChrono : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_chrono" [i64, i32, i64] [.bool] a m Q X)
    (hRaw : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Func.wp Γ FullM5Otfs.full_prop_lit_body a m Q X :=
  FullM5Otfs.full_prop_lit_wp Γ hChrono hRaw

theorem m5o_prop_ign_wp (Γ : Env)
    (hChrono : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_chrono" [i64, i32, i64] [.bool] a m Q X)
    (hRaw : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Func.wp Γ FullM5Otfs.full_propagate_ignore_body a m Q X :=
  FullM5Otfs.full_propagate_ignore_wp Γ hChrono hRaw

theorem m5o_mod_ok : ModuleOk m5OtfsEnv m5OtfsModule :=
  m5Otfs_moduleOk

theorem m5o_nv_prop_ign :
    Func.wp m5OtfsEnv FullM5Otfs.full_propagate_ignore_body
      (FastCore.nvFastPropCfg.hdr, 0xFFFFFFFF#64, ()) FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_m5_propagate_ignore_sound

theorem m5o_nv_prop_lit :
    Func.wp m5OtfsEnv FullM5Otfs.full_prop_lit_body
      (FastCore.nvFastPropCfg.hdr, 0#32, 0xFFFFFFFF#64, ()) FastCore.nvFastPropMem
      (fun (ok, ()) m' =>
        ∃ s', (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m' ∧
          (ok = false → s'.core.oom ≠ 0#64 ∨ Full.nvOneLitF0.Unsat))
      (fun _ _ _ _ => False) :=
  nv_m5_prop_lit_sound

theorem m5o_nv_unwatch :
    Func.wp m5OtfsEnv FullM5Otfs.full_unwatch_large_body
      (FastCore.nvFastPropCfg.hdr, 1#32, 0#32, ()) FastCore.nvFastPropMem
      (fun () m' =>
        ∃ s', s'.LengthsOk FastCore.nvFastPropCfg ∧
          Full.WatchStackLayout s'.core ∧ Full.ModeWatchesInv [[0], [1]] s'.core ∧
          (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_m5_unwatch_large_ok

theorem m5o_nv_one_lit :
    Func.wp m5OtfsEnv FullM5Otfs.full_one_lit_confl_m5_body
      (Full.nvOneLitCfg.hdr, ()) Full.nvOneLitMem
      (fun (r, ()) m' =>
        r = 20#64 ∧ Full.nvOneLitF0.Unsat ∧ FullMem Full.nvOneLitCfg Full.nvOneLitState m')
      (fun _ _ _ _ => False) :=
  nv_m5_one_lit_confl_sound

end AuditSpec

end LeanQbeLegacyTest.KissatM5OtfsTest

/-! ## 3. Single-line `#print axioms` audit across all exported theorems -/

abbrev m5o_ax_wf := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_wf
abbrev m5o_ax_acyc := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_acyc
abbrev m5o_ax_unw := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_unwatch_wp
abbrev m5o_ax_otfs := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_otfs_wp
abbrev m5o_ax_bin := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_otfs_bin_wp
abbrev m5o_ax_ded := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_deduce_1uip_wp
abbrev m5o_ax_ol := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_one_lit_confl_wp
abbrev m5o_ax_chr := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_prop_chrono_wp
abbrev m5o_ax_pl := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_prop_lit_wp
abbrev m5o_ax_pi := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_prop_ign_wp
abbrev m5o_ax_noex := @LeanQbe.T.Examples.Kissat.FullM5Otfs.m5Otfs_noExit
abbrev m5o_ax_tbl := @LeanQbe.T.Examples.Kissat.FullM5Otfs.m5Otfs_tableImpl
abbrev m5o_ax_mod := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_mod_ok
abbrev m5o_ax_nv_pi := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_nv_prop_ign
abbrev m5o_ax_nv_pl := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_nv_prop_lit
abbrev m5o_ax_nv_unw := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_nv_unwatch
abbrev m5o_ax_nv_ol := @LeanQbeLegacyTest.KissatM5OtfsTest.m5o_nv_one_lit

#print axioms m5o_ax_wf
#print axioms m5o_ax_acyc
#print axioms m5o_ax_unw
#print axioms m5o_ax_otfs
#print axioms m5o_ax_bin
#print axioms m5o_ax_ded
#print axioms m5o_ax_ol
#print axioms m5o_ax_chr
#print axioms m5o_ax_pl
#print axioms m5o_ax_pi
#print axioms m5o_ax_noex
#print axioms m5o_ax_tbl
#print axioms m5o_ax_mod
#print axioms m5o_ax_nv_pi
#print axioms m5o_ax_nv_pl
#print axioms m5o_ax_nv_unw
#print axioms m5o_ax_nv_ol
