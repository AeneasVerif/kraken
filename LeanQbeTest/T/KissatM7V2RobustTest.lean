/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7V2Robust
public import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullSpec
import Kraken.Separation
meta import LeanQbe.T.Examples.Kissat.FullM7V2Robust
meta import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, UNSAT Non-Vacuity & Axiom Audit (`FullM7V2Robust`)

1. Executable `#guard` checks on `v2RobustModule` (`5` fns, `12` externs, `0` exits),
   `m7FidV2RobustModule` (`415` fns), `m7PlusV2RobustModule` (`412` fns), exposed `patchFns`
   equalities, `PrintCpp`, `PrintQbe`, and 4-ISA `Fn.legal` legality.
2. Audit-ready restated headline theorems covering `Wf`, `checkAcyclic`, all `5` parametric
   `Func.wp` proofs, closed `v2Robust_moduleOk`, `patchModule_moduleOk`, and the `m7Fidelity` /
   `m7Plus` spliced UNSAT soundness bridges.
3. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, zero SAT model proofs):
   - `nv_v2r_reduce_purge_unsat`: executes `full_reduce_purge_c0_body` under closed `v2RobustEnv`
     on concrete `1,756 B` `nvOneLitMem` (`nvOneLitF0.Unsat`).
   - `nv_v2r_add_clause_oom`: executes `full_add_clause_body` under closed `v2RobustEnv` on
     concrete `nvOneLitMem`, returning `0xFFFFFFFF#64` cleanly.
   - `nv_v2r_m7fid_unsat_of` & `nv_v2r_m7plus_unsat_of`: concrete `8 KiB` `nvM6UnsatInitMem`
     `r = 20#64 ∧ nvM6UnsatCnf.Unsat` lifts through `V2RobustCallees`.
4. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7V2RobustTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM7V2Robust

/-! ## 1. Executable `#guard` Codegen, ABI & Legalization Checks -/

#guard v2Robust_fns.length == 5
#guard v2RobustExterns.length == 12
#guard v2RobustModule.checkAcyclic == true
#guard v2RobustModule.exits.isEmpty == true
#guard v2rWatchPopFn.sig == ("full_watch_pop_c0", [i64, i32, i32], [])
#guard v2rAddClauseFn.sig == ("full_add_clause", [i64, i32, i32, .bool], [i64])
#guard v2rSweepCopyFn.sig == ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64])
#guard v2rReducePurgeFn.sig == ("full_reduce_purge_c0", [i64], [i64])
#guard v2rLearnClauseFn.sig == ("full_learn_clause", [i64, i64], [i64])
#guard m7FidV2RobustFns.length == 415
#guard m7PlusV2RobustFns.length == 412
#guard m7FidV2RobustModule.checkAcyclic == true
#guard m7PlusV2RobustModule.checkAcyclic == true
#guard m7FidV2RobustModule.externs.isEmpty && m7PlusV2RobustModule.externs.isEmpty
#guard m7FidV2RobustModule.exits.isEmpty && m7PlusV2RobustModule.exits.isEmpty
#guard (patchFns v2RobustRepls v2RobustBefores FullM7Fidelity.m7FidelityFns).length == 415
#guard (patchFns v2RobustRepls v2RobustBefores FullM7Plus.m7PlusFns).length == 412
#guard (ppTModule v2RobustModule).isOk
#guard (PrintQbe.module v2RobustModule).isOk
#guard (ppModule (v2Robust_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (v2Robust_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (v2Robust_fns.map (Fn.legal .x64AVX2))).isOk
#guard v2Robust_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem v2r_fns_wf : ∀ f ∈ v2Robust_fns, f.Wf :=
  v2Robust_fns_wf

theorem v2r_fid_wf : ∀ f ∈ m7FidV2RobustFns, f.Wf :=
  m7FidV2RobustFns_wf

theorem v2r_plus_wf : ∀ f ∈ m7PlusV2RobustFns, f.Wf :=
  m7PlusV2RobustFns_wf

theorem v2r_standalone_acyc : v2RobustModule.checkAcyclic = true :=
  v2Robust_checkAcyclic

theorem v2r_fid_acyc : m7FidV2RobustModule.checkAcyclic = true :=
  m7FidV2Robust_checkAcyclic

theorem v2r_plus_acyc : m7PlusV2RobustModule.checkAcyclic = true :=
  m7PlusV2Robust_checkAcyclic

theorem v2r_patchFns_fid :
    patchFns v2RobustRepls v2RobustBefores FullM7Fidelity.m7FidelityFns = m7FidV2RobustFns :=
  patchFns_eq_fid

theorem v2r_patchFns_plus :
    patchFns v2RobustRepls v2RobustBefores FullM7Plus.m7PlusFns = m7PlusV2RobustFns :=
  patchFns_eq_plus

theorem v2r_watch_pop_wp (Γ : Env) :
    ∀ a m Q X, fullWatchPopC0Spec a m Q X → Func.wp Γ full_watch_pop_c0_body a m Q X :=
  full_watch_pop_c0_wp Γ

theorem v2r_add_clause_wp (Γ : Env)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hPop : ∀ a m Q X, fullWatchPopC0Spec a m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullAddClauseSpec a m Q X →
      Func.wp Γ FullM7V2Robust.full_add_clause_body a m Q X :=
  full_add_clause_wp Γ hAlloc hPush hPop

theorem v2r_sweep_copy_wp (Γ : Env)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hPop : ∀ a m Q X, fullWatchPopC0Spec a m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullSweepCopySpec a m Q X →
      Func.wp Γ FullM7V2Robust.full_sweep_copy_body a m Q X :=
  full_sweep_copy_wp Γ hAsgn hPush hPop

theorem v2r_reduce_purge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hMrk : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hSwp : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullReducePurgeC0Spec a m Q X → Func.wp Γ full_reduce_purge_c0_body a m Q X :=
  full_reduce_purge_c0_wp Γ hBt hProp hMrk hNext hSwp

theorem v2r_learn_clause_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X →
      Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hRedPurge : ∀ a m Q X, fullReducePurgeC0Spec a m Q X →
      Γ "full_reduce_purge_c0" [i64] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullLearnClauseSpec a m Q X →
      Func.wp Γ FullM7V2Robust.full_learn_clause_body a m Q X :=
  full_learn_clause_wp Γ hBt hAsgn hDnl hDefrag hRed hRedPurge hAddCl hEsub

theorem v2r_standalone_noExit : ∀ f as bs xs m Q X X',
    v2RobustEnv f as bs xs m Q X → v2RobustEnv f as bs xs m Q X' :=
  v2RobustEnv_noExit

theorem v2r_standalone_modOk : ModuleOk v2RobustEnv v2RobustModule :=
  v2Robust_moduleOk

theorem v2r_patch_modOk {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M)
    (hchk : ({ M with fns := patchFns v2RobustRepls v2RobustBefores M.fns } :
      LeanQbe.T.Module).checkAcyclic = true)
    (hNotFns : M.fns.all (fun fn =>
      fn.name != "full_watch_pop_c0" && fn.name != "full_reduce_purge_c0") = true)
    (hNotExts : M.externs.all (fun ex =>
      ex.name != "full_watch_pop_c0" && ex.name != "full_reduce_purge_c0") = true)
    (hc : V2RobustCallees Γ) :
    ModuleOk (V2RobustEnv Γ) { M with fns := patchFns v2RobustRepls v2RobustBefores M.fns } :=
  patchModule_moduleOk hM hchk hNotFns hNotExts hc

theorem v2r_fid_modOk_of (hc : V2RobustCallees FullM7Fidelity.m7FidelityEnv) :
    ModuleOk m7FidV2RobustEnv m7FidV2RobustModule :=
  m7FidV2Robust_moduleOk_of hc

theorem v2r_plus_modOk_of (hc : V2RobustCallees FullM7Plus.m7PlusEnv) :
    ModuleOk m7PlusV2RobustEnv m7PlusV2RobustModule :=
  m7PlusV2Robust_moduleOk_of hc

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT) -/

private theorem nv_v2r_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nv_v2r_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nv_v2r_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core := by
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun _ hr => by simp [hrefs] at hr,
        fun _ hr => by simp [hrefs] at hr, fun _ hr => by simp [hrefs] at hr,
        fun _ hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [nvOneLitState]
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
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nv_v2r_entails_0
      trail_pos_inv := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT): executes
`full_reduce_purge_c0_body` inside closed `v2RobustEnv` / `v2RobustModule` on `1,756 B`
`nvOneLitMem`, certifying `nvOneLitF0.Unsat`, `r ∈ {0, 1, 20}`, and restored invariants. -/
theorem nv_v2r_reduce_purge_unsat :
    Func.wp v2RobustEnv v2rReducePurgeFn.body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (r, ()) m' =>
        nvOneLitF0.Unsat ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧
        ∃ s' : FullState, FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
          FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hmem : v2rReducePurgeFn ∈ v2RobustModule.fns := by
    simp only [v2RobustModule, v2Robust_fns, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hfn := (v2Robust_moduleOk.fnsOk pre _ post hsplit).2.2
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hmarks : FullLitMarksClear nvOneLitCfg nvOneLitState := by
    refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
    · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  have hnd : FullArenaVarsNodup nvOneLitState := fun r hr => by
    have : fullArenaClauseRefs nvOneLitState = [] := rfl
    simp [this] at hr
  have hext : FullExtScratchOk nvOneLitCfg nvOneLitState :=
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩
  have hsp0 : FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState :=
    ⟨nvOneLit_lengths, nv_v2r_witness, hmarks, hnd, hext, rfl⟩
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [Std.ExtHashMap.sep_emp]; exact nvOneLitMem_ok
  refine hfn _ nvOneLitMem _ (fun _ _ _ _ => False) (v2RobustEnv_reducePurge_of_full
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState, emp, rfl, hsp0, hm, ?_⟩)
  intro r s' m' hspW hr _ _ _ _ _ _ h20 _ _ hm'
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨nv_v2r_unsat, hr, h20, s', hspW, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT): executes
`full_add_clause_body` inside closed `v2RobustEnv` / `v2RobustModule` on `1,756 B`
`nvOneLitMem`, returning `0xFFFFFFFF#64` cleanly and restoring `FullMem`. -/
theorem nv_v2r_add_clause_oom :
    Func.wp v2RobustEnv v2rAddClauseFn.body
      (nvOneLitCfg.hdr, 0#32, 0#32, true, ()) nvOneLitMem
      (fun (r, ()) m' =>
        nvOneLitF0.Unsat ∧ r = 0xFFFFFFFF#64 ∧ FullMem nvOneLitCfg nvOneLitState m')
      (fun _ _ _ _ => False) := by
  have hmem : v2rAddClauseFn ∈ v2RobustModule.fns := by
    simp only [v2RobustModule, v2Robust_fns, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inl rfl)
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hfn := (v2Robust_moduleOk.fnsOk pre _ post hsplit).2.2
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [Std.ExtHashMap.sep_emp]; exact nvOneLitMem_ok
  refine hfn _ nvOneLitMem _ (fun _ _ _ _ => False) (v2RobustEnv_addClause
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState, emp, rfl, nvOneLit_lengths,
      nv_v2r_witness, rfl, (by decide), (fun h => by cases h), hm, ?_⟩)
  rw [ite_eq_left (by decide)]
  rw [Std.ExtHashMap.sep_emp] at hm
  exact ⟨nv_v2r_unsat, rfl, hm⟩

/-- Concrete `8 KiB` UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`m7FidV2RobustModule` (`415` fns) given `V2RobustCallees m7FidelityEnv`. -/
theorem nv_v2r_m7fid_unsat_of (hc : V2RobustCallees FullM7Fidelity.m7FidelityEnv) :
    Func.wp m7FidV2RobustEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m7FidV2Robust_unsat_nv_of hc

/-- Concrete `8 KiB` UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`m7PlusV2RobustModule` (`412` fns) given `V2RobustCallees m7PlusEnv`. -/
theorem nv_v2r_m7plus_unsat_of (hc : V2RobustCallees FullM7Plus.m7PlusEnv) :
    Func.wp m7PlusV2RobustEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m7PlusV2Robust_unsat_nv_of hc

end LeanQbeTest.T.KissatM7V2RobustTest

/-! ## 4. Single-Line `#print axioms` Audit (`std3` Only) -/

abbrev v2r_ax_fns_wf := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_fns_wf
abbrev v2r_ax_fid_wf := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_fid_wf
abbrev v2r_ax_plus_wf := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_plus_wf
abbrev v2r_ax_acyc := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_standalone_acyc
abbrev v2r_ax_fid_acyc := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_fid_acyc
abbrev v2r_ax_plus_acyc := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_plus_acyc
abbrev v2r_ax_patch_fid := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_patchFns_fid
abbrev v2r_ax_patch_plus := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_patchFns_plus
abbrev v2r_ax_pop_wp := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_watch_pop_wp
abbrev v2r_ax_add_wp := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_add_clause_wp
abbrev v2r_ax_swp_wp := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_sweep_copy_wp
abbrev v2r_ax_red_wp := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_reduce_purge_wp
abbrev v2r_ax_lrn_wp := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_learn_clause_wp
abbrev v2r_ax_noExit := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_standalone_noExit
abbrev v2r_ax_modOk := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_standalone_modOk
abbrev v2r_ax_patchOk := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_patch_modOk
abbrev v2r_ax_fid_modOk := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_fid_modOk_of
abbrev v2r_ax_plus_modOk := @LeanQbeTest.T.KissatM7V2RobustTest.v2r_plus_modOk_of
abbrev v2r_ax_nv_red := @LeanQbeTest.T.KissatM7V2RobustTest.nv_v2r_reduce_purge_unsat
abbrev v2r_ax_nv_add := @LeanQbeTest.T.KissatM7V2RobustTest.nv_v2r_add_clause_oom
abbrev v2r_ax_nv_fid := @LeanQbeTest.T.KissatM7V2RobustTest.nv_v2r_m7fid_unsat_of
abbrev v2r_ax_nv_plus := @LeanQbeTest.T.KissatM7V2RobustTest.nv_v2r_m7plus_unsat_of

#print axioms v2r_ax_fns_wf
#print axioms v2r_ax_fid_wf
#print axioms v2r_ax_plus_wf
#print axioms v2r_ax_acyc
#print axioms v2r_ax_fid_acyc
#print axioms v2r_ax_plus_acyc
#print axioms v2r_ax_patch_fid
#print axioms v2r_ax_patch_plus
#print axioms v2r_ax_pop_wp
#print axioms v2r_ax_add_wp
#print axioms v2r_ax_swp_wp
#print axioms v2r_ax_red_wp
#print axioms v2r_ax_lrn_wp
#print axioms v2r_ax_noExit
#print axioms v2r_ax_modOk
#print axioms v2r_ax_patchOk
#print axioms v2r_ax_fid_modOk
#print axioms v2r_ax_plus_modOk
#print axioms v2r_ax_nv_red
#print axioms v2r_ax_nv_add
#print axioms v2r_ax_nv_fid
#print axioms v2r_ax_nv_plus

end
