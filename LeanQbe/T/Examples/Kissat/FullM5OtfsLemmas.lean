/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5Otfs
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas2
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas3
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas4a
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas4b
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M5 Hub: `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity (`FullM5OtfsLemmas`)

Zero `import all LeanQbe.*`. Re-exports all `8` canonical `FullSpec2` `Func.wp` proofs from
`FullM5OtfsLemmas{1,2,3,4a,4b}`, builds the aligned `19`-row `m5OtfsSpecTable` / `m5OtfsEnv`,
proves closed `m5Otfs_tableImpl` and `m5Otfs_moduleOk`, and certifies `4` concrete `Mem 64`
UNSAT non-vacuity theorems (`XPost := False`, zero SAT/model proofs).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Otfs

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_unwatch_large_body full_unwatch_large_wf
  full_otfs_large_body full_otfs_large_wf full_otfs_large_wp full_otfs_large_wp_weak
  full_prop_lit_body full_prop_lit_wf
  full_propagate_ignore_body full_propagate_ignore_wf

/-! ## 1. Closed `19`-Row `m5OtfsSpecTable`, `m5OtfsEnv`, & `ModuleOk` -/

/-- Canonical `FullSpec2` specification table for `m5OtfsModule` (`8` fns + `11` externs). -/
def m5OtfsSpecTable : List SpecEntry :=
  [ ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩
  , ⟨"full_otfs_bin_m5", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩
  , ⟨"full_deduce_1uip_m5", [i64], [i64], Full.fullDeduce1uipSpec, true⟩
  , ⟨"full_one_lit_confl_m5", [i64], [i64], Full.fullOneLitConflSpec, true⟩
  , ⟨"full_prop_lit_chrono", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  , ⟨"full_prop_lit", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_det_new_level", [i64, i64], [i64], Full.fullDetNewLevelSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  , ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩
  , ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  , ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩
  , ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  ]

/-- Specification environment induced by `m5OtfsSpecTable`. -/
def m5OtfsEnv : Env := Env.ofTable m5OtfsSpecTable

theorem m5OtfsSpecTable_noExit : ∀ e ∈ m5OtfsSpecTable, e.noExit = true := by
  intro e he
  have hall : m5OtfsSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m5OtfsSpecTable_sigs :
    m5OtfsSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      (m5Otfs_fns.map (fun f => (f.name, f.as, f.rs)) ++
        m5OtfsExterns.map (fun x => (x.name, x.as, x.rs))) := by
  t_kernel_rfl

theorem m5Otfs_noExit :
    ∀ f as bs xs m Q X X',
      m5OtfsEnv f as bs xs m Q X → m5OtfsEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m5OtfsSpecTable_noExit

private theorem m5OtfsSpecTable_nodup :
    (m5OtfsSpecTable.map SpecEntry.name).Nodup := by
  show (["full_unwatch_large", "full_otfs_large", "full_otfs_bin_m5",
    "full_deduce_1uip_m5", "full_one_lit_confl_m5", "full_prop_lit_chrono",
    "full_prop_lit", "full_propagate_ignore", "full_arena_next",
    "full_wstack_defrag", "full_watch_push", "full_backtrack",
    "full_det_new_level", "full_assign_lvl", "full_analyze_lit",
    "full_analyze_rsn", "full_clear_ana", "full_otfs_subsume",
    "full_prop_lit_raw"] : List String).Nodup
  decide

private theorem m5OtfsEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m5OtfsSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m5OtfsEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m5OtfsSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m5Otfs_fns` against `m5OtfsSpecTable`. -/
theorem m5Otfs_tableImpl :
    TableImpl m5OtfsEnv m5Otfs_fns m5OtfsSpecTable := by
  let hUnw := m5OtfsEnv_row_at 0
    ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩
  let hOtfsLarge := m5OtfsEnv_row_at 1
    ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩
  let hOtfsBin := m5OtfsEnv_row_at 2
    ⟨"full_otfs_bin_m5", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩
  let hChrono := m5OtfsEnv_row_at 5
    ⟨"full_prop_lit_chrono", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  let hNext := m5OtfsEnv_row_at 8
    ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  let hDefrag := m5OtfsEnv_row_at 9
    ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩
  let hPush := m5OtfsEnv_row_at 10
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hBt := m5OtfsEnv_row_at 11
    ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  let hDet := m5OtfsEnv_row_at 12
    ⟨"full_det_new_level", [i64, i64], [i64], Full.fullDetNewLevelSpec, true⟩
  let hAss := m5OtfsEnv_row_at 13
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  let hAlit := m5OtfsEnv_row_at 14
    ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩
  let hArsn := m5OtfsEnv_row_at 15
    ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩
  let hClear := m5OtfsEnv_row_at 16
    ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩
  let hOtfsSub := m5OtfsEnv_row_at 17
    ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩
  let hRaw := m5OtfsEnv_row_at 18
    ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  exact ⟨.of (full_unwatch_large_wp m5OtfsEnv),
    ⟨.of (full_otfs_large_wp m5OtfsEnv hDefrag hUnw hPush),
    ⟨.of (full_otfs_bin_m5_wp m5OtfsEnv hNext hDefrag hUnw hPush),
    ⟨.of (full_deduce_1uip_m5_wp m5OtfsEnv hAlit hArsn hClear hOtfsLarge hOtfsBin hOtfsSub),
    ⟨.of (full_one_lit_confl_m5_wp m5OtfsEnv hDefrag hDet hBt hAss hUnw hPush),
    ⟨.of (full_prop_lit_chrono_wp m5OtfsEnv hDefrag hUnw hRaw hPush),
    ⟨.of (full_prop_lit_wp m5OtfsEnv hChrono hRaw),
    ⟨.of (full_propagate_ignore_wp m5OtfsEnv hChrono hRaw), trivial⟩⟩⟩⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` certifying all `8` M5 functions under canonical `m5OtfsEnv`. -/
theorem m5Otfs_moduleOk : ModuleOk m5OtfsEnv m5OtfsModule :=
  Env.ofTable_moduleOk m5Otfs_acyclic
    ⟨full_unwatch_large_wf, full_otfs_large_wf, full_otfs_bin_m5_wf,
     full_deduce_1uip_m5_wf, full_one_lit_confl_m5_wf, full_prop_lit_chrono_wf,
     full_prop_lit_wf, full_propagate_ignore_wf, trivial⟩
    m5Otfs_tableImpl

/-! ## 2. Concrete `Mem 64` UNSAT Soundness & Non-Vacuity (`XPost := False`) -/

private theorem m5_conflictOkW_to_confl {F_cur : List (List Nat)} {s : FullState}
    (h : Full.FullConflictOkW F_cur s) : FullPropDecSpecs.FullConflOkW F_cur s.core := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | hr
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr hr

/-- Concrete `Mem 64` UNSAT soundness/non-vacuity (`XPost := False`) for
`full_propagate_ignore_body` under `m5OtfsEnv`: derives `nvOneLitF0.Unsat` on conflict. -/
theorem nv_m5_propagate_ignore_sound :
    Func.wp m5OtfsEnv full_propagate_ignore_body
      (FastCore.nvFastPropCfg.hdr, 0xFFFFFFFF#64, ()) FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let hChrono := m5OtfsEnv_row_at 5
    ⟨"full_prop_lit_chrono", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  let hRaw := m5OtfsEnv_row_at 18
    ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  apply full_propagate_ignore_wp m5OtfsEnv hChrono hRaw
  refine ⟨FastCore.nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], FastCore.nvFastPropState, emp,
    rfl, FastCore.nvFastProp_lengths, FastCore.nvFastProp_witness, rfl,
    by rw [sep_emp]; exact FastCore.nvFastPropMem_ok, ?_⟩
  intro r _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _prop' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _fuel' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' m' s' _hlen' hwf' _htr' _hperm' _hfl' hr _hr0 hr1 _hr2 _hnoop hm'
  refine ⟨hr, fun h1 => ?_, s', hm'⟩
  subst h1
  exact hwf'.level0_unsat_of_conflOkW rfl (m5_conflictOkW_to_confl (hr1 rfl).2.2.1)

/-- Concrete `Mem 64` UNSAT soundness/non-vacuity (`XPost := False`) for `full_prop_lit_body`
under `m5OtfsEnv`: derives `nvOneLitF0.Unsat` on non-OOM conflict (`ok = false`). -/
theorem nv_m5_prop_lit_sound :
    Func.wp m5OtfsEnv full_prop_lit_body
      (FastCore.nvFastPropCfg.hdr, 0#32, 0xFFFFFFFF#64, ()) FastCore.nvFastPropMem
      (fun (ok, ()) m' =>
        ∃ s', (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m' ∧
          (ok = false → s'.core.oom ≠ 0#64 ∨ Full.nvOneLitF0.Unsat))
      (fun _ _ _ _ => False) := by
  let hChrono := m5OtfsEnv_row_at 5
    ⟨"full_prop_lit_chrono", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  let hRaw := m5OtfsEnv_row_at 18
    ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  apply full_prop_lit_wp m5OtfsEnv hChrono hRaw
  refine ⟨FastCore.nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], FastCore.nvFastPropState, emp,
    rfl, FastCore.nvFastProp_lengths, FastCore.nvFastProp_witness, rfl, rfl,
    by rw [sep_emp]; exact FastCore.nvFastPropMem_ok, ?_⟩
  intro ok _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' m' s' _hlen' hwf' _htr' _hperm' hcf _hokT hm'
  refine ⟨s', hm', fun hf => ?_⟩
  rcases hcf hf with hoom | ⟨hconfl, _⟩
  · exact Or.inl hoom
  · exact Or.inr (hwf'.level0_unsat_of_conflOkW rfl (m5_conflictOkW_to_confl hconfl))

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `full_unwatch_large_body` under
`m5OtfsEnv`: preserves `LengthsOk`, `WatchStackLayout`, and `ModeWatchesInv` on
`FastCore.nvFastPropMem`. -/
theorem nv_m5_unwatch_large_ok :
    Func.wp m5OtfsEnv full_unwatch_large_body
      (FastCore.nvFastPropCfg.hdr, 1#32, 0#32, ()) FastCore.nvFastPropMem
      (fun () m' =>
        ∃ s', s'.LengthsOk FastCore.nvFastPropCfg ∧
          Full.WatchStackLayout s'.core ∧ Full.ModeWatchesInv [[0], [1]] s'.core ∧
          (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  apply full_unwatch_large_wp m5OtfsEnv
  refine ⟨FastCore.nvFastPropCfg, FastCore.nvFastPropState, emp,
    rfl, FastCore.nvFastProp_lengths, FastCore.nvFastProp_witness.watches.layout,
    by rw [sep_emp]; exact FastCore.nvFastPropMem_ok, ?_⟩
  intro wvec' wstk' wu' m' s' hlen' hlay' hmw' hm'
  exact ⟨s', hlen', hlay', hmw' [[0], [1]] FastCore.nvFastProp_witness.watches, hm'⟩

private theorem m5_nvOneLit_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem m5_nvOneLit_entails_11 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨lit, hm, heq⟩ := h1
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

private theorem m5_nvOneLit_witness :
    Full.FullWitnessInv Full.nvOneLitCfg Full.nvOneLitF0 [[0], [1]] Full.nvOneLitState.core := by
  have hrefs : fullArenaClauseRefsCore Full.nvOneLitState.core = [] := rfl
  have hcv : Full.nvOneLitState.core.cur_vars = 1 := rfl
  have hte : Full.nvOneLitState.core.trail_end = 1 := rfl
  have hcl : Full.nvOneLitState.core.cur_level = 0 := rfl
  have hdm : Full.nvOneLitState.core.dense_mode = 0#64 := rfl
  have hwat : Full.ModeWatchesInv [[0], [1]] Full.nvOneLitState.core := by
    unfold Full.ModeWatchesInv; rw [ite_eq_left hdm]
    refine Full.WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, Full.nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, Full.nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact Full.WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [Full.nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun L h1 h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact m5_nvOneLit_entails_0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

/-- Concrete `Mem 64` UNSAT soundness/non-vacuity (`XPost := False`) for
`full_one_lit_confl_m5_body` under `m5OtfsEnv`: returns `20#64` on level-0 conflict. -/
theorem nv_m5_one_lit_confl_sound :
    Func.wp m5OtfsEnv full_one_lit_confl_m5_body
      (Full.nvOneLitCfg.hdr, ()) Full.nvOneLitMem
      (fun (r, ()) m' =>
        r = 20#64 ∧ Full.nvOneLitF0.Unsat ∧ FullMem Full.nvOneLitCfg Full.nvOneLitState m')
      (fun _ _ _ _ => False) := by
  let hBt := m5OtfsEnv_row_at 11
    ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  let hDet := m5OtfsEnv_row_at 12
    ⟨"full_det_new_level", [i64, i64], [i64], Full.fullDetNewLevelSpec, true⟩
  let hAss := m5OtfsEnv_row_at 13
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  have hmv : Full.nvOneLitCfg.max_vars = 1 := rfl
  have hcl : Full.nvOneLitState.core.cur_level = 0 := rfl
  have hconflW : Full.FullConflictOkW [[0], [1]] Full.nvOneLitState :=
    Or.inl ⟨rfl, by decide, by decide, rfl, rfl, m5_nvOneLit_entails_11⟩
  have hmarks : Full.FullLitMarksClear Full.nvOneLitCfg Full.nvOneLitState := by
    refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
    · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  have hnd : Full.FullArenaVarsNodup Full.nvOneLitState := fun r hr => by
    have : fullArenaClauseRefs Full.nvOneLitState = [] := rfl
    simp [this] at hr
  have hext : Full.FullExtScratchOk Full.nvOneLitCfg Full.nvOneLitState :=
    ⟨Full.FullLastLearnedWf.of_cleared fun i hi => by
      simp only [Full.nvOneLitState, Full.nvOneLitScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩
  have hm : (FullMem Full.nvOneLitCfg Full.nvOneLitState ⋆ emp) Full.nvOneLitMem := by
    rw [sep_emp]; exact Full.nvOneLitMem_ok
  refine m5_oneLit_bin_branch_wp m5OtfsEnv hDet hBt hAss Full.nvOneLit_lengths rfl
    m5_nvOneLit_witness.toCut hmarks hnd hext (Nat.le_refl _)
    (hconflW.toCut m5_nvOneLit_witness) rfl hm ?_
  intro r s' m' _ hr _ _ _ _ _ _ _ _ hnb h20 h1 _ h0 hm'
  rw [sep_emp] at hm'
  rcases hr with rfl | rfl | rfl | rfl
  · obtain ⟨_, _, _, hpos, _, _⟩ := h0 rfl
    omega
  · obtain ⟨_, hlt⟩ := h1 rfl
    rw [hcl] at hlt; omega
  · exact absurd rfl (hnb rfl)
  · obtain ⟨hu, rfl⟩ := h20 rfl
    exact ⟨rfl, hu, hm'⟩

end LeanQbe.T.Examples.Kissat.FullM5Otfs
