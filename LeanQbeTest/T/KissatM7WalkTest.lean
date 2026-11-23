module

public import LeanQbe.T.Examples.Kissat.FullM7Walk
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7Walk
meta import LeanQbe.T.Examples.Kissat.FullM7WalkProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit (`FullM7Walk`)

1. Executable `#guard` checks on `m7WalkModule` (`13` fns, `6` externs, `19` spec rows, `0` exits),
   `checkAcyclic = true`, `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` checks (`.aarch64`,
   `.scalar64`, `.x64AVX2`, `.x64AVX512`).
2. Audit-ready restated headline theorems for `m7WalkFns_wf`, `m7Walk_acyclic`, `m7WalkEnv_noExit`,
   all `13` parametric WP contracts (`full_walk_*_m7_wp`, `full_warmup_m7_wp`,
   `full_walk_warmup_m7_wp`), `m7Walk_tableImpl`, `m7Walk_moduleOk`, and concrete `Mem 64` UNSAT
   non-vacuity (`nv_m7_walk`, `nv_m7_warmup` with `XPost := False`).
3. Single-line `< 100`-col `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7WalkTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7Walk
open Kraken.Bedrock2.Test

/-! ## 1. Module Structure, C++/QBE Emission, and 4-ISA Legalization Guards -/

#guard m7WalkModule.checkAcyclic == true
#guard m7WalkModule.exits.isEmpty == true
#guard m7WalkFns.length == 13
#guard m7WalkExterns.length == 6
#guard m7WalkSpecTable.length == 19
#guard m7WalkSpecTable.all (·.noExit) == true
#guard m7WalkSpecTable.map (fun e => (e.name, e.as, e.rs)) == m7WalkModule.sigs
#guard m7WalkFns.map Fn.name ==
  [ "full_walk_cb_inv_m7", "full_walk_init_table_m7", "full_walk_effort_m7",
    "full_walk_init_vals_m7", "full_walk_collect_m7", "full_walk_build_occ_m7",
    "full_walk_break_m7", "full_walk_pick_m7", "full_walk_flip_m7",
    "full_walk_save_min_m7", "full_walk_m7", "full_warmup_m7", "full_walk_warmup_m7" ]
#guard (m7WalkExterns.map Extern.name) ==
  [ "full_rng_next", "full_arena_next", "full_next_dec_var",
    "full_assign", "full_propagate", "full_backtrack" ]
#guard (ppTModule m7WalkModule).isOk
#guard match ppTModule m7WalkModule with
  | .ok s => (s.splitOn "full_walk_cb_inv_m7").length > 1 &&
      (s.splitOn "full_walk_m7").length > 1 &&
      (s.splitOn "full_warmup_m7").length > 1 &&
      (s.splitOn "full_walk_warmup_m7").length > 1
  | .error _ => false
#guard (PrintQbe.module m7WalkModule).isOk
#guard (ppModule (m7WalkFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7WalkFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7WalkFns.map (Fn.legal .x64AVX2))).isOk
#guard m7WalkFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

section AuditSpec

theorem m7w_fns_wf : ∀ f ∈ m7WalkFns, f.Wf := m7WalkFns_wf
theorem m7w_acyc : m7WalkModule.checkAcyclic = true := m7Walk_acyclic

theorem m7w_no_exit :
    ∀ f as bs xs m Q X X', m7WalkEnv f as bs xs m Q X → m7WalkEnv f as bs xs m Q X' :=
  m7WalkEnv_noExit

theorem m7w_cb_inv_wp (Γ : Env) :
    ∀ a m Q X, m7CbInvSpec a m Q X → Func.wp Γ full_walk_cb_inv_m7_body a m Q X :=
  full_walk_cb_inv_m7_wp Γ

theorem m7w_init_table_wp (Γ : Env) :
    ∀ a m Q X, m7InitTableSpec a m Q X → Func.wp Γ full_walk_init_table_m7_body a m Q X :=
  full_walk_init_table_m7_wp Γ

theorem m7w_init_table_mono_wp (Γ : Env) :
    ∀ a m Q X, m7InitTableMonoSpec a m Q X →
      Func.wp Γ full_walk_init_table_m7_body a m Q X :=
  full_walk_init_table_m7_mono_wp Γ

theorem m7w_effort_wp (Γ : Env) :
    ∀ a m Q X, m7EffortSpec a m Q X → Func.wp Γ full_walk_effort_m7_body a m Q X :=
  full_walk_effort_m7_wp Γ

theorem m7w_init_vals_wp (Γ : Env) :
    ∀ a m Q X, m7InitValsSpec a m Q X → Func.wp Γ full_walk_init_vals_m7_body a m Q X :=
  full_walk_init_vals_m7_wp Γ

theorem m7w_collect_wp (Γ : Env)
    (hArenaNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X) :
    ∀ a m Q X, m7CollectSpec a m Q X → Func.wp Γ full_walk_collect_m7_body a m Q X :=
  full_walk_collect_m7_wp Γ hArenaNext

theorem m7w_build_occ_wp (Γ : Env) :
    ∀ a m Q X, m7BuildOccSpec a m Q X → Func.wp Γ full_walk_build_occ_m7_body a m Q X :=
  full_walk_build_occ_m7_wp Γ

theorem m7w_break_wp (Γ : Env) :
    ∀ a m Q X, m7BreakSpec a m Q X → Func.wp Γ full_walk_break_m7_body a m Q X :=
  full_walk_break_m7_wp Γ

theorem m7w_pick_wp (Γ : Env)
    (hBrk : ∀ a m Q X, m7BreakSpec a m Q X →
      Γ "full_walk_break_m7" [i64, i32, i64] [i32] a m Q X)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X →
      Γ "full_rng_next" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7PickSpec a m Q X → Func.wp Γ full_walk_pick_m7_body a m Q X :=
  full_walk_pick_m7_wp Γ hBrk hRng

theorem m7w_flip_wp (Γ : Env) :
    ∀ a m Q X, m7FlipSpec a m Q X → Func.wp Γ full_walk_flip_m7_body a m Q X :=
  full_walk_flip_m7_wp Γ

theorem m7w_save_min_wp (Γ : Env) :
    ∀ a m Q X, m7SaveMinSpec a m Q X → Func.wp Γ full_walk_save_min_m7_body a m Q X :=
  full_walk_save_min_m7_wp Γ

theorem m7w_walk_wp (Γ : Env)
    (hInitVals : ∀ a m Q X, m7InitValsSpec a m Q X →
      Γ "full_walk_init_vals_m7" [i64] [] a m Q X)
    (hCollect : ∀ a m Q X, m7CollectSpec a m Q X →
      Γ "full_walk_collect_m7" [i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X, m7CbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    (hInitTable : ∀ a m Q X, m7InitTableSpec a m Q X →
      Γ "full_walk_init_table_m7" [i64, i64] [] a m Q X)
    (hBuildOcc : ∀ a m Q X, m7BuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    (hEffort : ∀ a m Q X, m7EffortSpec a m Q X →
      Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, m7PickSpec a m Q X →
      Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    (hFlip : ∀ a m Q X, m7FlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hSaveMin : ∀ a m Q X, m7SaveMinSpec a m Q X →
      Γ "full_walk_save_min_m7" [i64, i64, Ty.bool] [] a m Q X) :
    ∀ a m Q X, fullWalkSpec a m Q X → Func.wp Γ full_walk_m7_body a m Q X :=
  full_walk_m7_wp Γ hInitVals hCollect hCbInv hInitTable hBuildOcc hEffort hPick hFlip hSaveMin

theorem m7w_warmup_wp (Γ : Env)
    (hNDV : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWarmupSpec a m Q X → Func.wp Γ full_warmup_m7_body a m Q X :=
  full_warmup_m7_wp Γ hNDV hAssign hProp hBT

theorem m7w_walk_warmup_wp (Γ : Env)
    (hWarmup : ∀ a m Q X, fullWarmupSpec a m Q X →
      Γ "full_warmup_m7" [i64] [] a m Q X)
    (hWalk : ∀ a m Q X, fullWalkSpec a m Q X →
      Γ "full_walk_m7" [i64] [] a m Q X) :
    ∀ a m Q X, fullWarmupSpec a m Q X → Func.wp Γ full_walk_warmup_m7_body a m Q X :=
  full_walk_warmup_m7_wp Γ hWarmup hWalk

theorem m7w_tbl_impl : TableImpl m7WalkEnv m7WalkModule.fns m7WalkSpecTable :=
  m7Walk_tableImpl

theorem m7w_mod_ok : ModuleOk m7WalkEnv m7WalkModule :=
  m7Walk_moduleOk

theorem m7w_nv_walk :
    Func.wp m7WalkEnv full_walk_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun _ m' => ∃ s' : FullState, s'.LengthsOk nvOneLitCfg ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_walk

theorem m7w_nv_warmup :
    Func.wp m7WalkEnv full_warmup_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun _ m' => ∃ s' : FullState, FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.probing = 0#64 ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_warmup

end AuditSpec

end LeanQbeTest.T.KissatM7WalkTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev m7w_a_wf := @LeanQbeTest.T.KissatM7WalkTest.m7w_fns_wf
abbrev m7w_a_acyc := @LeanQbeTest.T.KissatM7WalkTest.m7w_acyc
abbrev m7w_a_nx := @LeanQbeTest.T.KissatM7WalkTest.m7w_no_exit
abbrev m7w_a_cb := @LeanQbeTest.T.KissatM7WalkTest.m7w_cb_inv_wp
abbrev m7w_a_it := @LeanQbeTest.T.KissatM7WalkTest.m7w_init_table_wp
abbrev m7w_a_itm := @LeanQbeTest.T.KissatM7WalkTest.m7w_init_table_mono_wp
abbrev m7w_a_eff := @LeanQbeTest.T.KissatM7WalkTest.m7w_effort_wp
abbrev m7w_a_iv := @LeanQbeTest.T.KissatM7WalkTest.m7w_init_vals_wp
abbrev m7w_a_col := @LeanQbeTest.T.KissatM7WalkTest.m7w_collect_wp
abbrev m7w_a_occ := @LeanQbeTest.T.KissatM7WalkTest.m7w_build_occ_wp
abbrev m7w_a_brk := @LeanQbeTest.T.KissatM7WalkTest.m7w_break_wp
abbrev m7w_a_pck := @LeanQbeTest.T.KissatM7WalkTest.m7w_pick_wp
abbrev m7w_a_flp := @LeanQbeTest.T.KissatM7WalkTest.m7w_flip_wp
abbrev m7w_a_sav := @LeanQbeTest.T.KissatM7WalkTest.m7w_save_min_wp
abbrev m7w_a_wlk := @LeanQbeTest.T.KissatM7WalkTest.m7w_walk_wp
abbrev m7w_a_wrm := @LeanQbeTest.T.KissatM7WalkTest.m7w_warmup_wp
abbrev m7w_a_ww := @LeanQbeTest.T.KissatM7WalkTest.m7w_walk_warmup_wp
abbrev m7w_a_tbl := @LeanQbeTest.T.KissatM7WalkTest.m7w_tbl_impl
abbrev m7w_a_mod := @LeanQbeTest.T.KissatM7WalkTest.m7w_mod_ok
abbrev m7w_a_nv_wlk := @LeanQbeTest.T.KissatM7WalkTest.m7w_nv_walk
abbrev m7w_a_nv_wrm := @LeanQbeTest.T.KissatM7WalkTest.m7w_nv_warmup

#print axioms m7w_a_wf
#print axioms m7w_a_acyc
#print axioms m7w_a_nx
#print axioms m7w_a_cb
#print axioms m7w_a_it
#print axioms m7w_a_itm
#print axioms m7w_a_eff
#print axioms m7w_a_iv
#print axioms m7w_a_col
#print axioms m7w_a_occ
#print axioms m7w_a_brk
#print axioms m7w_a_pck
#print axioms m7w_a_flp
#print axioms m7w_a_sav
#print axioms m7w_a_wlk
#print axioms m7w_a_wrm
#print axioms m7w_a_ww
#print axioms m7w_a_tbl
#print axioms m7w_a_mod
#print axioms m7w_a_nv_wlk
#print axioms m7w_a_nv_wrm
