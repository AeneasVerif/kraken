/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofMin2
import LeanQbe.T.Examples.Kissat.FullMinLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Rank #5 Min-Shrink Proof (`FullM8CoreParityProofMin`)

UNSAT-only `Func.wp` proof (`public section`, `0` `@[expose]`, `0` `@[local]`, `XPost := False`,
`0` `maxHeartbeats`, `0` `sorry`) for `full_min_shrink_m6_m8_wp` (`m8MinShrinkSpec`), re-exporting
all Rank #5 helpers via `FullM8CoreParityProofMin2`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  FullMinMarkInv fullMinMarkCore fullMinMarkState fullMinMarkSpec
  fullMinLitSpec fullShrinkLowerSpec fullShrinkBlkSpec fullMinShrinkSpec
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

/-! ## 4. `full_min_shrink_m6` M8 Soundness (`m8MinShrinkSpec`) -/

private theorem m8ListTakeSuccSet {α : Type _} {xs : List α} {i : Nat} (v : α)
    (hi : i < xs.length) :
    (xs.set i v).take (i + 1) = xs.take i ++ [v] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i => simp [List.set, List.take_succ_cons, ih (by simpa using hi)]

private theorem m8ListFilterNeEqSelf {xs : List (BitVec 32)} {k : Nat}
    (hk : k ≤ xs.length)
    (hne : ∀ j < k, xs[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    (xs.take k).filter (· ≠ 0xFFFFFFFF#32) = xs.take k := by
  rw [List.filter_eq_self]; intro b hb
  rw [List.mem_iff_getElem] at hb; obtain ⟨j, hj, rfl⟩ := hb
  rw [List.length_take] at hj; rw [List.getElem_take]
  have h1 := hne j (by omega)
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
  exact decide_eq_true h1

private theorem m8MinMarkInvMrkNeZeroIff {k : FullCoreState} {keep : List Nat}
    (hmin : FullMinMarkInv k keep) (hno8 : ∀ v < k.cur_vars, (k.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    {v : Nat} (hv : v < k.cur_vars) :
    k.mrk[v]?.getD 0#8 ≠ 0#8 ↔ (k.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
  have hd := hmin.mrk_dom v hv; have h8 := hno8 v hv
  generalize k.mrk[v]?.getD 0#8 = b at hd h8 ⊢; revert b hd h8; decide

private theorem m8MinShrinkScratchOk {c : FullCfg} {sc : FullScratch} (hok : sc.LengthsOk c)
    {sstk' wsort' : List (BitVec 32)} {conf' llits' mrem' ticks' : BitVec 64}
    (hsstk : sstk'.length = c.max_vars) (hws : wsort'.length = 2 * c.max_vars) :
    ({ sc with
      conflicts := conf', learned_lits := llits', min_removed := mrem',
      shrink_stk := sstk', wsort := wsort', search_ticks := ticks' } : FullScratch).LengthsOk c :=
  { hok with shrink_stk_len := hsstk, wsort_len := hws }

private theorem m8OtfsCoreInvWithMinTmpTl {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullOtfsCoreInv c F0 s) {tmp' : List (BitVec 32)} {tl' : Nat}
    {mrk' : List (BitVec 8)} {mclr' sstk' wsort' : List (BitVec 32)} {mcl' : Nat}
    {mcf' conf' llits' mrem' ticks' : BitVec 64}
    (htl : tl' ≤ s.core.cur_vars) (htmp : tmp'.length = c.max_vars)
    (hmrk : mrk'.length = c.max_vars) (hmclr : mclr'.length = c.max_vars) (hmcl : mcl' ≤ c.max_vars)
    (hsstk : sstk'.length = c.max_vars) (hws : wsort'.length = 2 * c.max_vars) :
    FullOtfsCoreInv c F0
      (m8MinShrinkRes s tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' conf' llits' mrem' ticks') := by
  have h1 : FullOtfsCoreInv c F0 (minLitState s mrk' s.core.min_stk mclr' mcl' mcf') :=
    fullOtfsCoreInv_with_min h hmrk h.1.core_ok.min_stk_len hmclr hmcl
  have h2 := fullOtfsCoreInv_with_min_tmp (mcf1 := mcf') h1 htmp
    (le_trans htl h.1.core_ok.cur_vars_le) hmrk h.1.core_ok.min_stk_len hmclr hmcl
    (m8MinShrinkScratchOk h.1.scratch_ok hsstk hws
      (conf' := conf') (llits' := llits') (mrem' := mrem') (ticks' := ticks'))
  obtain ⟨hlo, F_cur, hw⟩ := h2
  exact ⟨⟨{ hlo.core_ok with tmp_len_le := le_trans htl h.1.core_ok.cur_vars_le }, hlo.scratch_ok⟩,
    ⟨F_cur, { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩⟩

private theorem m8MinShrinkPostSort {c : FullCfg} {s : FullState}
    (htl1 : 1 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars) (htmp_len : s.core.tmp.length = c.max_vars)
    (htmp_vals : ∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (htmp_lvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    {tmp1 : List (BitVec 32)} (ht1_len : tmp1.length = c.max_vars)
    (ht1_0 : 1 ≤ s.core.tmp_len → tmp1[0]? = s.core.tmp[0]?)
    (ht1_r : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp1[k]? = s.core.tmp[i]?)
    (ht1_l : ∀ i, 1 ≤ i → i < s.core.tmp_len →
      ∃ k, 1 ≤ k ∧ k < s.core.tmp_len ∧ s.core.tmp[i]? = tmp1[k]?) :
    let keep0 := ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    keep0 = (tmp1.take s.core.tmp_len).map BitVec.toNat ∧
    (∀ F_cur, (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause keep0)) ∧
    (∀ k < s.core.tmp_len, tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      (tmp1[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp1[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 ∧
      (tmp1[k]?.getD 0#32).toNat ∈ keep0) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl
  have hlt1 : ∀ k < s.core.tmp_len, (tmp1[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp1[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := fun k hk => by
    cases k with
    | zero => rw [ht1_0 htl1]; exact htmp_vals 0 hk
    | succ k' =>
      obtain ⟨i, _, hi2, heq⟩ := ht1_r (k' + 1) (by omega) hk
      rw [heq]; exact htmp_vals i hi2
  have hkeep_eq : ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat =
      (tmp1.take s.core.tmp_len).map BitVec.toNat := by
    rw [m8ListFilterNeEqSelf (by omega) fun j hj => by
      have h1 := (hlt1 j hj).1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1 ⊢
      intro heq; have hto := congrArg BitVec.toNat heq; rw [hff] at hto; omega]
  refine ⟨hkeep_eq, ?_, ?_, fun k hk1 hk2 => by
      obtain ⟨i, hi1, hi2, heq⟩ := ht1_r k hk1 hk2; rw [heq]; exact htmp_lvls i hi1 hi2⟩
  · intro F_cur hEnt0; rw [hkeep_eq]; rw [CNF.entails_clause_def] at hEnt0 ⊢
    intro α hα; obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hEnt0 α hα)
    refine (clause_sat_cnfClause_iff α _).mpr ⟨l, ?_, hsat⟩
    rw [List.mem_map] at hl ⊢; obtain ⟨b, hb, rfl⟩ := hl
    rw [List.mem_iff_getElem] at hb; obtain ⟨i, hi, rfl⟩ := hb
    rw [List.length_take] at hi; rw [List.getElem_take]
    obtain ⟨j, hj, heq⟩ : ∃ j < s.core.tmp_len, s.core.tmp[i]? = tmp1[j]? := by
      cases i with
      | zero => exact ⟨0, htl1, (ht1_0 htl1).symm⟩
      | succ i' =>
        obtain ⟨j, _, hj2, heq⟩ := ht1_l (i' + 1) (by omega) (by omega)
        exact ⟨j, hj2, heq⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
    exact ⟨tmp1[j]'(by omega), List.mem_iff_getElem.mpr ⟨j, by rw [List.length_take]; omega,
      by rw [List.getElem_take]⟩, by rw [Option.some.inj heq]⟩
  · intro k hk; have hkv := hlt1 k hk
    have hk_ne : tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; intro heq
      have hto := congrArg BitVec.toNat heq; have h1' := hkv.1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1'
      rw [hff] at hto; omega
    have hk_mem : (tmp1[k]?.getD 0#32).toNat ∈
        ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
      rw [hkeep_eq, List.mem_map]
      exact ⟨tmp1[k]'(by omega), List.mem_iff_getElem.mpr ⟨k, by rw [List.length_take]; omega,
        by rw [List.getElem_take]⟩, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
    exact ⟨hk_ne, hkv.1, hkv.2, hk_mem⟩

private theorem m8MinLitStepState {c : FullCfg} {F0 : CNF Nat} {s_orig cur : FullState}
    {keepLen idx : Nat} (hidx_kl : idx < keepLen) (hkl_cv : keepLen ≤ cur.core.cur_vars)
    (hcore : FullOtfsCoreInv c F0 cur)
    (_hmin : FullMinMarkInv cur.core
      (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hent : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s_orig.core →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s_orig.core.tmp.take s_orig.core.tmp_len).map BitVec.toNat)) →
      FullOtfsWitnessInv c F0 F_cur cur.core ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)))
    (hnd : ((s_orig.core.tmp.take s_orig.core.tmp_len).map fun x => x.toNat / 2).Nodup →
      (∀ k, 1 ≤ k → k < s_orig.core.tmp_len →
        (s_orig.core.lvl[(s_orig.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
        (s_orig.core.lvl[(s_orig.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
        fun x => x.toNat / 2).Nodup)
    (hab : ∀ v, cur.core.cur_vars ≤ v → cur.core.mrk[v]? = s_orig.core.mrk[v]?)
    (hno8 : ∀ v < cur.core.cur_vars, (cur.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hrem : ∀ k < keepLen, cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (cur.core.tmp[k]?.getD 0#32).toNat
      l < 2 * cur.core.cur_vars ∧ cur.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (cur.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {root_lit : BitVec 32} (hroot_eq : cur.core.tmp[idx]? = some root_lit)
    (hroot_ne : root_lit ≠ 0xFFFFFFFF#32)
    {ok : Bool} {mrk' : List (BitVec 8)} {wsort' mclr' : List (BitVec 32)}
    {mcl' : Nat} {mcf' ticks' : BitVec 64}
    (hlen' : (m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks').LengthsOk c)
    (hab' : ∀ v, cur.core.cur_vars ≤ v → mrk'[v]? = cur.core.mrk[v]?)
    (hmono2 : ∀ v < cur.core.cur_vars,
      (cur.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8 : ∀ v < cur.core.cur_vars,
      (mrk'[v]?.getD 0#8 &&& 8#8) = (cur.core.mrk[v]?.getD 0#8 &&& 8#8))
    (hmin' : FullMinMarkInv (m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks').core
      (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hok_true : ok = true →
      (∀ keep', (∀ l ∈ (((cur.core.tmp.take keepLen).filter
            (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep') →
        FullMinMarkInv (m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks').core keep') ∧
      FullMinMarkInv (fullMinMarkCore
          (m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks').core
          (root_lit.toNat / 2) 2#8)
        (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) :
    let tmp_n := if ok then cur.core.tmp.set idx 0xFFFFFFFF#32 else cur.core.tmp
    let st_n : FullState := m8BlkState cur tmp_n mrk' mclr' cur.scratch.shrink_stk wsort'
      mcl' mcf' ticks'
    FullOtfsCoreInv c F0 st_n ∧
    FullMinMarkInv st_n.core
      (((tmp_n.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
    (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s_orig.core →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s_orig.core.tmp.take s_orig.core.tmp_len).map BitVec.toNat)) →
      FullOtfsWitnessInv c F0 F_cur st_n.core ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        (((tmp_n.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) ∧
    (((s_orig.core.tmp.take s_orig.core.tmp_len).map fun x => x.toNat / 2).Nodup →
      (∀ k, 1 ≤ k → k < s_orig.core.tmp_len →
        (s_orig.core.lvl[(s_orig.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
        (s_orig.core.lvl[(s_orig.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (((tmp_n.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
        fun x => x.toNat / 2).Nodup) ∧
    (∀ v, cur.core.cur_vars ≤ v → mrk'[v]? = s_orig.core.mrk[v]?) ∧
    (∀ v < cur.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (∀ k < keepLen, tmp_n[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (tmp_n[k]?.getD 0#32).toNat
      l < 2 * cur.core.cur_vars ∧ cur.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
    (∀ k, idx < k → k < keepLen → tmp_n[k]? = cur.core.tmp[k]?) := by
  have hrm_b : cur.core.tmp[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    rw [hroot_eq, Option.getD_some]; exact hroot_ne
  have hrb := hrem idx hidx_kl hrm_b
  have hr_nat : (cur.core.tmp[idx]?.getD 0#32).toNat = root_lit.toNat := by
    rw [hroot_eq, Option.getD_some]
  have hcur_w : cur.scratch.shrink_stk.length = c.max_vars := hcore.1.scratch_ok.shrink_stk_len
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨m8CoreInv_blk hcore hcore.1.core_ok.tmp_len_arr hlen'.core_ok.mrk_len
        hlen'.core_ok.min_clr_len_arr hlen'.core_ok.min_clr_len_le hcur_w
        hlen'.scratch_ok.wsort_len,
      hmin', fun F_cur hw hEnt0 =>
        let ⟨hwc, hEc⟩ := hent F_cur hw hEnt0
        ⟨m8Witness_shrinkBlk hwc (sstk1 := cur.scratch.shrink_stk)
          (wsort1 := wsort') (ticks1 := ticks'), hEc⟩,
      hnd, fun v hv => (hab' v hv).trans (hab v hv),
      fun v hv => by rw [hbit8 v hv]; exact hno8 v hv,
      fun k hk hne => by
        have hrk := hrem k hk hne
        exact ⟨hrk.1, hrk.2.1,
          hmono2 ((cur.core.tmp[k]?.getD 0#32).toNat / 2) (by omega) hrk.2.2⟩,
      fun _ _ _ => trivial⟩
  | true =>
    simp only [↓reduceIte]; let tmp_n := cur.core.tmp.set idx 0xFFFFFFFF#32
    let st_base := m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks'
    let st_n : FullState :=
      m8BlkState cur tmp_n mrk' mclr' cur.scratch.shrink_stk wsort' mcl' mcf' ticks'
    have htl_n : tmp_n.length = c.max_vars := by
      dsimp only [tmp_n]; rw [List.length_set, hcore.1.core_ok.tmp_len_arr]
    have hcore_n : FullOtfsCoreInv c F0 st_n :=
      m8CoreInv_blk hcore htl_n hlen'.core_ok.mrk_len hlen'.core_ok.min_clr_len_arr
        hlen'.core_ok.min_clr_len_le hcur_w hlen'.scratch_ok.wsort_len
    let keep' := ((tmp_n.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    have hsub : ∀ l ∈ (((cur.core.tmp.take keepLen).filter
        (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep' := by
      intro l hl; rw [mem_filter_map_toNat_take] at hl; obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
      by_cases hke : k = idx
      · subst k; rw [hkb] at hroot_eq; left; exact congrArg BitVec.toNat (Option.some.inj hroot_eq)
      · right; exact mem_filter_map_toNat_take.mpr ⟨k,
          by dsimp only [tmp_n]; rw [List.length_set]; exact hk, b,
          by dsimp only [tmp_n]; rw [List.getElem?_set_ne (Ne.symm hke)]; exact hkb, hne, rfl⟩
    have hmin_base : FullMinMarkInv st_base.core keep' := (hok_true rfl).1 keep' hsub
    have hmin_n : FullMinMarkInv st_n.core keep' :=
      ⟨hmin_base.mrk_dom, hmin_base.clr_cov, hmin_base.rem_sound⟩
    have hent_n : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s_orig.core →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s_orig.core.tmp.take s_orig.core.tmp_len).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur st_n.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause keep') := by
      intro F_cur hw hEnt0; obtain ⟨hwc, hEc⟩ := hent F_cur hw hEnt0
      have hwb : FullOtfsWitnessInv c F0 F_cur st_base.core :=
        { hwc with
          arena := { hwc.arena with len_ok := hwc.arena.len_ok }
          watches := hwc.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
      refine ⟨m8Witness_shrinkBlk hwc, fullMinMark_entails hwb hmin_base hEc fun l hl => ?_⟩
      rw [mem_filter_map_toNat_take] at hl; obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
      have hrk := hrem k (lt_of_lt_of_le hk (Nat.min_le_left _ _))
        (by rw [hkb, Option.getD_some]; exact hne)
      have hbk : (cur.core.tmp[k]?.getD 0#32).toNat = b.toNat := by rw [hkb, Option.getD_some]
      rw [hbk] at hrk
      refine ⟨hrk.1, hrk.2.1, ?_⟩
      rcases hsub b.toNat (mem_filter_map_toNat_take.mpr ⟨k, hk, b, hkb, hne, rfl⟩) with
        heqb | hin
      · right; rw [heqb, ← hr_nat]; exact hmono2 _ (by omega) hrb.2.2
      · exact Or.inl hin
    have hkl_lt_c : keepLen ≤ cur.core.tmp.length := by
      rw [hcore.1.core_ok.tmp_len_arr]; exact le_trans hkl_cv hcore.1.core_ok.cur_vars_le
    have hidx_lt' : idx < cur.core.tmp.length := lt_of_lt_of_le hidx_kl hkl_lt_c
    have hnb : ∀ k, tmp_n[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 → k ≠ idx := fun k hk => by
      rintro rfl; exact hk (by dsimp only [tmp_n]; rw [List.getElem?_set_self hidx_lt']; rfl)
    refine ⟨hcore_n, hmin_n, hent_n,
      fun hnd0 hne0 => nodup_filter_set_sent hkl_lt_c hidx_kl (hnd hnd0 hne0),
      fun v hv => (hab' v hv).trans (hab v hv),
      fun v hv => by rw [hbit8 v hv]; exact hno8 v hv,
      fun k hk hne => ?_,
      fun _ _ _ => by rw [List.getElem?_set_ne (by omega)]⟩
    · have hke := Ne.symm (hnb k hne)
      rw [List.getElem?_set_ne hke] at hne ⊢; have hrk := hrem k hk hne
      exact ⟨hrk.1, hrk.2.1, hmono2 ((cur.core.tmp[k]?.getD 0#32).toNat / 2) (by omega) hrk.2.2⟩

private def m8MinMarkInitExpr {V : Ty → Type} {C : List Ty → Type} (p orig_tlen pTmp : V i64)
    (K : Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Js => .cons (fun p_14 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_14.fst, .var orig_tlen, ())) fun p_15 =>
    .jnz (.var p_15.fst)
      (.let_ (op64 (.mul i64) (.var p_14.fst) (.imm 4)) fun p_16 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p_16.fst)) fun p_17 =>
       .load i32 (.var p_17.fst) fun ld =>
       .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun p_18 =>
       .let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun p_19 =>
       .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
         (.var p, .var p_18.fst, .var p_19.fst, ()) fun _ =>
       .let_ (op64 (.add i64) (.var p_14.fst) (.imm 1)) fun p =>
       .jump Js.fst (.var p.fst, ()))
      K) .nil)
    (fun Js => .jump Js.fst (.imm 0, ()))

private def m8MinCompactLoopExpr {V : Ty → Type} {C : List Ty → Type} (bound pTmp : V i64)
    (K : V i64 → Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64]]) (fun Js => .cons (fun p_18 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_18.snd.fst, .var bound, ())) fun p_19 =>
    .jnz (.var p_19.fst)
      (.group (sig := [[i64]]) (fun _Js_1 => .cons (fun p =>
        .let_ (op64 (.add i64) (.var p_18.snd.fst) (.imm 1)) fun p_20 =>
        .jump Js.fst (.var p.fst, .var p_20.fst, ())) .nil) fun Js =>
       .let_ (op64 (.mul i64) (.var p_18.snd.fst) (.imm 4)) fun p =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
       .load i32 (.var p.fst) fun ld =>
       .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var ld, .imm 4294967295, ())) fun p =>
       .jnz (.var p.fst)
         (.let_ (op64 (.mul i64) (.var p_18.fst) (.imm 4)) fun p =>
          .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
          .let_ (op64 (.mul i64) (.var p_18.snd.fst) (.imm 4)) fun p_20 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var p_20.fst)) fun p_21 =>
          .load i32 (.var p_21.fst) fun ld =>
          .store (.var ld) (.var p.fst)
            (.let_ (op64 (.add i64) (.var p_18.fst) (.imm 1)) fun p =>
             .jump Js.fst (.var p.fst, ())))
         (.jump Js.fst (.var p_18.fst, ())))
      (K p_18.fst)) .nil)
    (fun Js => .jump Js.fst (.imm 1, .imm 1, ()))

private def m8MinCleanExpr {V : Ty → Type} {C : List Ty → Type}
    (p cv orig_tlen pMark keep : V i64) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _Js => .cons (fun _ =>
    .let_ (op64 (.add i64) (.var p) (.imm 272)) fun p_22 =>
    .store (t := i64) (.imm 0) (.var p_22.fst)
      (.let_ (op64 (.add i64) (.var p) (.imm 280)) fun p_23 =>
       .store (t := i64) (.imm 0) (.var p_23.fst)
         (.let_ (op64 (.add i64) (.var p) (.imm 192)) fun p_24 =>
          .store (.var keep) (.var p_24.fst)
            (.let_ (op64 (.add i64) (.var p) (.imm 352)) fun p_25 =>
             .load i64 (.var p_25.fst) fun ld =>
             .let_ (op64 (.sub i64) (.var orig_tlen) (.var keep)) fun p_26 =>
             .let_ (op64 (.add i64) (.var ld) (.var p_26.fst)) fun p_27 =>
             .let_ (op64 (.add i64) (.var p) (.imm 352)) fun p_28 =>
             .store (.var p_27.fst) (.var p_28.fst)
               (.let_ (op64 (.add i64) (.var p) (.imm 344)) fun p_29 =>
                .load i64 (.var p_29.fst) fun ld =>
                .let_ (op64 (.add i64) (.var ld) (.var keep)) fun p_30 =>
                .let_ (op64 (.add i64) (.var p) (.imm 344)) fun p =>
                .store (.var p_30.fst) (.var p.fst) (.ret ())))))) .nil)
    (fun Js =>
      .let_ (op64 (.add i64) (.var p) (.imm 280)) fun p_21 =>
      .load i64 (.var p_21.fst) fun ld_7 =>
      .let_ (Op.mk (.cmp .ne i64 .bool rfl) (.var ld_7, .imm 0, ())) fun p_22 =>
      .jnz (.var p_22.fst)
        (.group (sig := [[i64]]) (fun Js_1 => .cons (fun p =>
          .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var cv, ())) fun p_23 =>
          .jnz (.var p_23.fst)
            (.let_ (op64 (.add i64) (.var pMark) (.var p.fst)) fun p_24 =>
             .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p_25 =>
             .store (.var p_25.fst) (.var p_24.fst)
               (.let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun p =>
                .jump Js_1.fst (.var p.fst, ())))
            (.jump Js.fst ())) .nil)
          (fun Js => .jump Js.fst (.imm 0, ())))
        (.let_ (op64 (.add i64) (.var p) (.imm 240)) fun p_23 =>
         .load i64 (.var p_23.fst) fun ld_8 =>
         .group (sig := [[i64]]) (fun Js_1 => .cons (fun p_24 =>
           .let_ (op64 (.add i64) (.var p) (.imm 272)) fun p =>
           .load i64 (.var p.fst) fun ld_9 =>
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_24.fst, .var ld_9, ())) fun p =>
           .jnz (.var p.fst)
             (.let_ (op64 (.mul i64) (.var p_24.fst) (.imm 4)) fun p =>
              .let_ (op64 (.add i64) (.var ld_8) (.var p.fst)) fun p =>
              .load i32 (.var p.fst) fun ld_10 =>
              .group (sig := [[]]) (fun _ => .cons (fun _ =>
                .let_ (op64 (.add i64) (.var p_24.fst) (.imm 1)) fun p =>
                .jump Js_1.fst (.var p.fst, ())) .nil) fun Js =>
              .let_ (Op.mk (.zext 32 64) (.var ld_10, ())) fun p =>
              .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var cv, ())) fun p =>
              .jnz (.var p.fst)
                (.let_ (Op.mk (.zext 32 64) (.var ld_10, ())) fun p =>
                 .let_ (op64 (.add i64) (.var pMark) (.var p.fst)) fun p =>
                 .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p_25 =>
                 .store (.var p_25.fst) (.var p.fst) (.jump Js.fst ()))
                (.jump Js.fst ()))
             (.jump Js.fst ())) .nil)
           (fun Js => .jump Js.fst (.imm 0, ()))))

private def m8MinBlkLoopExpr {V : Ty → Type} {C : List Ty → Type}
    (p cv orig_tlen pTmp pLvl pTpos tlen : V i64) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Js => .cons (fun p_34 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_34.fst, .var tlen, ())) fun p_35 =>
    .jnz (.var p_35.fst)
      (.let_ (op64 (.mul i64) (.var p_34.fst) (.imm 4)) fun p_36 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p_36.fst)) fun p_37 =>
       .load i32 (.var p_37.fst) fun ld =>
       .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun p_38 =>
       .let_ (Op.mk (.zext 32 64) (.var p_38.fst, ())) fun p_39 =>
       .let_ (op64 (.mul i64) (.var p_39.fst) (.imm 4)) fun p_40 =>
       .let_ (op64 (.add i64) (.var pLvl) (.var p_40.fst)) fun p_41 =>
       .load i32 (.var p_41.fst) fun ld =>
       .let_ (op64 (.mul i64) (.var p_34.fst) (.imm 4)) fun p_42 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p_42.fst)) fun p_43 =>
       .load i32 (.var p_43.fst) fun ld_9 =>
       .let_ (Op.mk (.lshr i32) (.var ld_9, .imm 1, ())) fun p_44 =>
       .let_ (Op.mk (.zext 32 64) (.var p_44.fst, ())) fun p_45 =>
       .let_ (op64 (.mul i64) (.var p_45.fst) (.imm 4)) fun p_46 =>
       .let_ (op64 (.add i64) (.var pTpos) (.var p_46.fst)) fun p_47 =>
       .load i32 (.var p_47.fst) fun ld_10 =>
       .let_ (Op.mk (.zext 32 64) (.var ld_10, ())) fun p_48 =>
       .let_ (op64 (.add i64) (.var p_34.fst) (.imm 1)) fun p_49 =>
       .group (sig := [[i64, i64]]) (fun Js_1 => .cons (fun p_50 =>
         .group (sig := [[]]) (fun _ => .cons (fun _ =>
           .group (sig := [[]]) (fun _ => .cons (fun _ =>
             .jump Js.fst (.var p_50.snd.fst, ())) .nil) fun Js =>
           .let_ (op64 (.sub i64) (.var p_50.snd.fst) (.var p_34.fst)) fun p_52 =>
           .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var p_52.fst, .imm 2, ())) fun p_53 =>
           .jnz (.var p_53.fst)
             (.group (sig := [[]]) (fun _ => .cons (fun _ => .jump Js.fst ()) .nil) fun Js =>
              .call "full_shrink_blk_bool_m8" (as := [i64, i64, i64, i32, i64]) (bs := [.bool])
                (.var p, .var p_34.fst, .var p_50.snd.fst, .var ld, .var p_50.fst, ())
                fun p_54 =>
              .jnz (.var p_54.fst) (.jump Js.fst ())
                (.group (sig := [[i64]]) (fun Js_3 => .cons (fun p_55 =>
                   .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                     (.var p_55.fst, .var p_50.snd.fst, ())) fun p_56 =>
                   .jnz (.var p_56.fst)
                     (.group (sig := [[]]) (fun _ => .cons (fun _ =>
                        .let_ (op64 (.add i64) (.var p_55.fst) (.imm 1)) fun p =>
                        .jump Js_3.fst (.var p.fst, ())) .nil) fun Js =>
                      .let_ (op64 (.mul i64) (.var p_55.fst) (.imm 4)) fun p_57 =>
                      .let_ (op64 (.add i64) (.var pTmp) (.var p_57.fst)) fun p_58 =>
                      .load i32 (.var p_58.fst) fun ld =>
                      .call "full_min_lit_dfs_m8" (as := [i64, i32, .bool, .bool]) (bs := [.bool])
                        (.var p, .var ld, .imm false, .imm false, ()) fun p =>
                      .jnz (.var p.fst)
                        (.let_ (op64 (.mul i64) (.var p_55.fst) (.imm 4)) fun p =>
                         .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
                         .store (t := i32) (.imm 4294967295) (.var p.fst) (.jump Js.fst ()))
                        (.jump Js.fst ()))
                     (.jump Js.fst ())) .nil)
                   fun Js => .jump Js.fst (.var p_34.fst, ())))
             (.jump Js.fst ())) .nil) fun Js =>
         .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_50.snd.fst, .var tlen, ())) fun p =>
         .jnz (.var p.fst)
           (.let_ (op64 (.mul i64) (.var p_50.snd.fst) (.imm 4)) fun p =>
            .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
            .load i32 (.var p.fst) fun ld_11 =>
            .let_ (Op.mk (.lshr i32) (.var ld_11, .imm 1, ())) fun p =>
            .let_ (Op.mk (.zext 32 64) (.var p.fst, ())) fun p =>
            .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
            .let_ (op64 (.add i64) (.var pLvl) (.var p.fst)) fun p =>
            .load i32 (.var p.fst) fun ld_12 =>
            .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld_12, .var ld, ())) fun p =>
            .jnz (.var p.fst)
              (.let_ (op64 (.mul i64) (.var p_50.snd.fst) (.imm 4)) fun p =>
               .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
               .load i32 (.var p.fst) fun ld =>
               .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun p =>
               .let_ (Op.mk (.zext 32 64) (.var p.fst, ())) fun p =>
               .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
               .let_ (op64 (.add i64) (.var pTpos) (.var p.fst)) fun p =>
               .load i32 (.var p.fst) fun ld =>
               .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p =>
               .group (sig := [[i64]]) (fun _ => .cons (fun p =>
                 .let_ (op64 (.add i64) (.var p_50.snd.fst) (.imm 1)) fun p_51 =>
                 .jump Js_1.fst (.var p.fst, .var p_51.fst, ())) .nil) fun Js =>
               .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var p.fst, .var p_50.fst, ())) fun p_51 =>
               .jnz (.var p_51.fst) (.jump Js.fst (.var p.fst, ()))
                 (.jump Js.fst (.var p_50.fst, ())))
              (.jump Js.fst ()))
           (.jump Js.fst ())) .nil)
         fun Js => .jump Js.fst (.var p_48.fst, .var p_49.fst, ()))
      (m8MinCompactLoopExpr tlen pTmp fun keep =>
        .let_ (op64 (.add i64) (.var p) (.imm 72)) fun p_38 =>
        .load i64 (.var p_38.fst) fun ld_9 =>
        m8MinCleanExpr p cv orig_tlen ld_9 keep)) .nil)
    fun Js => .jump Js.fst (.imm 1, ())

private theorem m8_min_shrink_m6_body_eq :
    full_min_shrink_m6_body = fun V _ p =>
      let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
      .let_ (op64 (.add i64) (.var p.fst) (.imm 776)) fun p_1 =>
      .load i64 (.var p_1.fst) fun ld =>
      .let_ (op64 (.add i64) (.var p.fst) (.imm 192)) fun p_2 =>
      .load i64 (.var p_2.fst) fun ld_1 =>
      .let_ (op64 (.add i64) (.var p.fst) (.imm 336)) fun p_3 =>
      .load i64 (.var p_3.fst) fun ld_2 =>
      .let_ (op64 (.add i64) (.var ld_2) (.imm 1)) fun p_4 =>
      .let_ (op64 (.add i64) (.var p.fst) (.imm 336)) fun p_5 =>
      .store (.var p_4.fst) (.var p_5.fst)
        (.group (sig := [[]]) (fun _Js => .cons (fun _ =>
          .let_ (op64 (.add i64) (.var p.fst) (.imm 344)) fun p_7 =>
          .load i64 (.var p_7.fst) fun ld =>
          .let_ (op64 (.add i64) (.var ld) (.var ld_1)) fun p_8 =>
          .let_ (op64 (.add i64) (.var p.fst) (.imm 344)) fun p =>
          .store (.var p_8.fst) (.var p.fst) (.ret ())) .nil) fun Js =>
        .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var ld_1, .imm 1, ())) fun p_6 =>
        .jnz (.var p_6.fst) (.jump Js.fst ())
          (.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var ld_1, .var ld, ())) fun p_7 =>
           .jnz (.var p_7.fst) (.jump Js.fst ())
             (.call "full_sort_tmp" (as := [i64]) (bs := []) (.var p.fst, ()) fun _ =>
              .let_ (op64 (.add i64) (.var p.fst) (.imm 136)) fun p_9 =>
              .load i64 (.var p_9.fst) fun ld_3 =>
              .let_ (op64 (.add i64) (.var p.fst) (.imm 80)) fun p_10 =>
              .load i64 (.var p_10.fst) fun ld_4 =>
              .let_ (op64 (.add i64) (.var p.fst) (.imm 360)) fun p_11 =>
              .load i64 (.var p_11.fst) fun ld_5 =>
              .let_ (op64 (.add i64) (.var p.fst) (.imm 272)) fun p_12 =>
              .store (t := i64) (.imm 0) (.var p_12.fst)
                (.let_ (op64 (.add i64) (.var p.fst) (.imm 280)) fun p_13 =>
                 .store (t := i64) (.imm 0) (.var p_13.fst)
                   (m8MinMarkInitExpr p.fst ld_1 ld_3
                     (m8MinBlkLoopExpr p.fst ld ld_1 ld_3 ld_4 ld_5 ld_1)))))) := by
  funext V C p; rfl

private theorem m8_min_shrink_compact_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {tlen : Nat} {tlen_bv : BitVec 64} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (ht1 : 1 ≤ tlen) (ht_cv : tlen ≤ s.core.cur_vars)
    (htlen_eq : tlen_bv.toNat = tlen)
    (h0ne : s.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hvals : ∀ k < tlen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlvls : ∀ k, 1 ≤ k → k < tlen → s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    (hsort : ∀ i j, 1 ≤ i → i ≤ j → j < tlen →
      s.core.tmp[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(s.core.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m)
    {K : Val i64 → Expr Val Cont []}
    (hK : ∀ (keep_bv : Val i64) (tmp_c : List (BitVec 32)) (mc : Mem 64),
      let s_c : FullState := { s with core := { s.core with tmp := tmp_c } }
      let keep := keep_bv.toNat
      tmp_c.length = c.max_vars → 1 ≤ keep → keep ≤ tlen → tmp_c[0]? = s.core.tmp[0]? →
      (tmp_c.take keep).map BitVec.toNat =
        ((s.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat →
      (∀ k < keep, tmp_c[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      (∀ j, 1 ≤ j → j < keep →
        let l := (tmp_c[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp_c[keep - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (∀ i j, 1 ≤ i → i ≤ j → j < keep →
        (s.core.lvl[(tmp_c[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp_c[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c s_c ⋆ R) mc → wp Γ Q X (K keep_bv) mc) :
    wp Γ Q X (m8MinCompactLoopExpr tlen_bv c.pTmp K) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen := hcore.1.core_ok; have hcv := hlen.cur_vars_le
  have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
  dsimp only [m8MinCompactLoopExpr]
  refine wp_loop_group (ts := [i64, i64]) (fun n (keep_bv, k_bv, ()) mk =>
      n = tlen - k_bv.toNat ∧ 1 ≤ keep_bv.toNat ∧ keep_bv.toNat ≤ k_bv.toNat ∧ k_bv.toNat ≤ tlen ∧
      ∃ (tmp_k : List (BitVec 32)),
        let st_k : FullState := { s with core := { s.core with tmp := tmp_k } }
        tmp_k.length = c.max_vars ∧ tmp_k[0]? = s.core.tmp[0]? ∧
        (∀ j, k_bv.toNat ≤ j → j < tlen → tmp_k[j]? = s.core.tmp[j]?) ∧
        (∀ i, 1 ≤ i → i < keep_bv.toNat →
          ∃ k', 1 ≤ k' ∧ k' < k_bv.toNat ∧ tmp_k[i]? = s.core.tmp[k']?) ∧
        (tmp_k.take keep_bv.toNat).map BitVec.toNat =
          ((s.core.tmp.take k_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat ∧
        (∀ j < keep_bv.toNat, tmp_k[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
        (∀ j, 1 ≤ j → j < keep_bv.toNat →
          let l := (tmp_k[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
          lv < s.core.cur_level) ∧
        (∀ i j, 1 ≤ i → i ≤ j → j < keep_bv.toNat →
          (s.core.lvl[(tmp_k[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp_k[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
        (FullMem c st_k ⋆ R) mk) ?_
    (fun Js hJs => by
      ml_lets
      have h0tl : 0 < s.core.tmp.length := by rw [hlen.tmp_len_arr]; omega
      have htk1 : s.core.tmp.take 1 = [s.core.tmp[0]'h0tl] := by
        generalize hxs : s.core.tmp = xs at h0tl ⊢
        cases xs with
        | nil => simp at h0tl
        | cons _ _ => rfl
      have h0ne' : (s.core.tmp[0]'h0tl ≠ 0xFFFFFFFF#32) := by
        rwa [List.getElem?_eq_getElem h0tl, Option.getD_some] at h0ne
      have hkf0 : (s.core.tmp.take (1#64).toNat).map BitVec.toNat =
          ((s.core.tmp.take (1#64).toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
        rw [h1v, htk1]; simp [h0ne']
      have hk_ne : ∀ j < (1#64).toNat,
          s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun j hj => by
        rw [h1v] at hj
        have hj0 : j = 0 := by omega
        subst hj0; exact h0ne
      have hk_ok : ∀ j, 1 ≤ j → j < (1#64).toNat →
          let l := (s.core.tmp[j]?.getD 0#32).toNat
          let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
          lv < s.core.cur_level := fun j hj1 hj2 => by rw [h1v] at hj2; omega
      have hk_sort : ∀ i j, 1 ≤ i → i ≤ j → j < (1#64).toNat →
          (s.core.lvl[(s.core.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
        fun i j hi hij hj => by rw [h1v] at hj; omega
      exact hJs (tlen - 1) (1#64, 1#64, ()) m
        ⟨by rw [h1v], by rw [h1v]; exact le_refl _, by rw [h1v]; exact le_refl _,
          by rw [h1v]; exact ht1, s.core.tmp, hlen.tmp_len_arr, rfl, (fun _ _ _ => rfl),
          (fun i hi1 hi2 => by rw [h1v] at hi2; omega),
          hkf0, hk_ne, hk_ok, hk_sort, hm⟩)
  rintro Js n ⟨keep_bv, k_bv, ⟨⟩⟩ mk hJs ⟨rfl, hkp1, hkp_k, hk_tl, tmp_k, htk_len, htk0, htail,
    hsrc, hf_eq, hkp_ne, hkp_ok, hkp_sort, hmk⟩
  let st_k : FullState := { s with core := { s.core with tmp := tmp_k } }
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hk_lt => ?_, fun hk_ge => ?_⟩
  · have hkx : k_bv.toNat < tlen := by
      rw [BitVec.ult, decide_eq_true_eq, htlen_eq] at hk_lt; exact hk_lt
    have hk_arr : k_bv.toNat < st_k.core.tmp.length := by dsimp only [st_k]; rw [htk_len]; omega
    have hk1 : (k_bv + 1).toNat = k_bv.toNat + 1 := min_bv64_add1 (by omega)
    refine wp_join_group (ts := [i64]) (fun (keep_n, ()) m_n =>
        1 ≤ keep_n.toNat ∧ keep_n.toNat ≤ k_bv.toNat + 1 ∧
        ∃ tmp_n,
          let st_n : FullState := { s with core := { s.core with tmp := tmp_n } }
          tmp_n.length = c.max_vars ∧ tmp_n[0]? = s.core.tmp[0]? ∧
          (∀ j, k_bv.toNat + 1 ≤ j → j < tlen → tmp_n[j]? = s.core.tmp[j]?) ∧
          (∀ i, 1 ≤ i → i < keep_n.toNat →
            ∃ k', 1 ≤ k' ∧ k' < k_bv.toNat + 1 ∧ tmp_n[i]? = s.core.tmp[k']?) ∧
          (tmp_n.take keep_n.toNat).map BitVec.toNat =
            ((s.core.tmp.take (k_bv.toNat + 1)).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat ∧
          (∀ j < keep_n.toNat, tmp_n[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
          (∀ j, 1 ≤ j → j < keep_n.toNat →
            let l := (tmp_n[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
            l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
            lv < s.core.cur_level) ∧
          (∀ i j, 1 ≤ i → i ≤ j → j < keep_n.toNat →
            (s.core.lvl[(tmp_n[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            (s.core.lvl[(tmp_n[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
          (FullMem c st_n ⋆ R) m_n)
      (fun _ ⟨keep_n, ⟨⟩⟩ m_n ⟨hkn1, hkn_le, tmp_n, htn_len, htn0, hntail, hnsrc, hnf_eq, hkn_ne,
          hkn_ok, hkn_sort, hmn⟩ => by
        rw [Blocks.get_here]; ml_lets
        exact hJs (tlen - (k_bv + 1).toNat) (keep_n, k_bv + 1, ()) m_n (by omega)
          ⟨rfl, hkn1, by rw [hk1]; exact hkn_le, by rw [hk1]; exact hkx,
            tmp_n, htn_len, htn0, fun j hj1 hj2 => hntail j (by rw [hk1] at hj1; exact hj1) hj2,
            fun i hi1 hi2 => let ⟨k', hk'1, hk'2, heq⟩ := hnsrc i hi1 hi2
              ⟨k', hk'1, by rw [hk1]; exact hk'2, heq⟩,
            by rw [hk1]; exact hnf_eq, hkn_ne, hkn_ok, hkn_sort, hmn⟩) ?_
    rintro Jkp hJkp
    ml_ld c0_load_full_tmp (s := st_k) (i := k_bv) hk_arr hmk
    let v_k := st_k.core.tmp[k_bv.toNat]'hk_arr
    have hvk_orig : tmp_k[k_bv.toNat]? = s.core.tmp[k_bv.toNat]? := htail k_bv.toNat (le_refl _) hkx
    have htake_k1 : s.core.tmp.take (k_bv.toNat + 1) =
        s.core.tmp.take k_bv.toNat ++ [v_k] := by
      rw [List.take_add_one, ← hvk_orig, List.getElem?_eq_getElem hk_arr]; rfl
    ml_lets; ml_jnz; refine ⟨fun hne => ?_, fun heq => ?_⟩
    · have hvk_ne : v_k ≠ 0xFFFFFFFF#32 := by c0_cond hne; exact hne
      have hvk_ne' : s.core.tmp[k_bv.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [← hvk_orig, List.getElem?_eq_getElem hk_arr, Option.getD_some]; exact hvk_ne
      have hk_keep : keep_bv.toNat < st_k.core.tmp.length := by
        dsimp only [st_k]; rw [htk_len]; omega
      ml_ld c0_load_full_tmp (s := st_k) (i := k_bv) hk_arr hmk
      ml_st mk', hmk' := c0_store_full_tmp (s := st_k) (i := keep_bv) v_k hk_keep hmk
      let tmp_n := tmp_k.set keep_bv.toNat v_k
      have hkp1_nat : (keep_bv + 1).toNat = keep_bv.toNat + 1 := min_bv64_add1 (by omega)
      have hv_orig_get : (s.core.tmp[k_bv.toNat]?.getD 0#32).toNat = v_k.toNat := by
        rw [← hvk_orig, List.getElem?_eq_getElem hk_arr, Option.getD_some]
      have hvk_vals := hvals k_bv.toNat hkx hvk_ne'
      have hvk_lvls : 0 < (s.core.lvl[v_k.toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[v_k.toNat / 2]?.getD 0#32).toNat < s.core.cur_level := by
        rw [← hv_orig_get]; exact hlvls k_bv.toNat (by omega) hkx hvk_ne'
      have hlast_le : ∀ i, 1 ≤ i → i < keep_bv.toNat →
          (s.core.lvl[(tmp_k[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[v_k.toNat / 2]?.getD 0#32).toNat := fun i hi1 hi2 => by
        obtain ⟨k', hk'1, hk'2, hk'eq⟩ := hsrc i hi1 hi2
        have hk'_ne : s.core.tmp[k']?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
          rw [← hk'eq]; exact hkp_ne i (by omega)
        rw [hk'eq, ← hv_orig_get]
        exact hsort k' k_bv.toNat hk'1 (by omega) hkx hk'_ne hvk_ne'
      ml_lets
      refine hJkp (keep_bv + 1, ()) mk' ⟨by rw [hkp1_nat]; omega, by rw [hkp1_nat]; omega,
        tmp_n, by simp [tmp_n, htk_len], by rw [List.getElem?_set_ne (by omega)]; exact htk0,
        fun j hj1 hj2 => by rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2,
        fun i hi1 hi2 => ?_, ?_, fun j hj => ?_, fun j hj1 hj2 => ?_, fun i j hi1 hij hj2 => ?_,
        hmk'⟩
      · rw [hkp1_nat] at hi2; by_cases hik : i = keep_bv.toNat
        · subst i; refine ⟨k_bv.toNat, by omega, by omega, ?_⟩
          rw [List.getElem?_set_self (by rw [htk_len]; omega), ← hvk_orig,
            List.getElem?_eq_getElem hk_arr]
        · obtain ⟨k', hk'1, hk'2, hk'eq⟩ := hsrc i hi1 (by omega)
          exact ⟨k', hk'1, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hk'eq⟩
      · rw [hkp1_nat, m8ListTakeSuccSet _ (by rw [htk_len]; omega), List.map_append, hf_eq,
          htake_k1, List.filter_append, List.filter_cons, decide_eq_true hvk_ne]
        simp
      · rw [hkp1_nat] at hj; by_cases hjk : j = keep_bv.toNat
        · subst j; rw [List.getElem?_set_self (by rw [htk_len]; omega), Option.getD_some]
          exact hvk_ne
        · rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hkp_ne j (by omega)
      · rw [hkp1_nat] at hj2; by_cases hjk : j = keep_bv.toNat
        · subst j; rw [List.getElem?_set_self (by rw [htk_len]; omega), Option.getD_some]
          rw [hv_orig_get] at hvk_vals
          exact ⟨hvk_vals.1, hvk_vals.2, hvk_lvls.1, hvk_lvls.2⟩
        · rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hkp_ok j hj1 (by omega)
      · rw [hkp1_nat] at hj2; by_cases hjk : j = keep_bv.toNat
        · subst j; rw [List.getElem?_set_self (by rw [htk_len]; omega), Option.getD_some]
          by_cases hik : i = keep_bv.toNat
          · subst i; rw [List.getElem?_set_self (by rw [htk_len]; omega), Option.getD_some]
            exact le_refl _
          · rw [List.getElem?_set_ne (Ne.symm hik)]; exact hlast_le i hi1 (by omega)
        · rw [List.getElem?_set_ne (Ne.symm hjk), List.getElem?_set_ne (by omega)]
          exact hkp_sort i j hi1 hij (by omega)
    · have hvk_eq : v_k = 0xFFFFFFFF#32 := by c0_cond heq; exact heq
      refine hJkp (keep_bv, ()) mk ⟨hkp1, by omega, tmp_k, htk_len, htk0,
        fun j hj1 hj2 => htail j (by omega) hj2,
        fun i hi1 hi2 => let ⟨k', hk'1, hk'2, hk'eq⟩ := hsrc i hi1 hi2
          ⟨k', hk'1, by omega, hk'eq⟩,
        ?_, hkp_ne, hkp_ok, hkp_sort, hmk⟩
      rw [hf_eq, htake_k1, List.filter_append, List.filter_cons,
        decide_eq_false (by simpa using hvk_eq)]
      simp
  · c0_cond hk_ge
    have hk_eq : k_bv.toNat = tlen := by rw [htlen_eq] at hk_ge; omega
    subst hk_eq
    refine hK keep_bv tmp_k mk htk_len hkp1 hkp_k htk0 hf_eq hkp_ne (fun j hj1 hj2 => ?_)
      hkp_sort hmk
    have ho := hkp_ok j hj1 hj2
    exact ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2, hkp_sort j (keep_bv.toNat - 1) hj1 (by omega)
      (by omega)⟩

private theorem m8_min_shrink_clean_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep_bv orig_tlen_bv : Val i64} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (_htl_cv : keep_bv.toNat ≤ s.core.cur_vars)
    (_hkeep_le : keep_bv.toNat ≤ orig_tlen_bv.toNat)
    (_horig_le : orig_tlen_bv.toNat ≤ s.core.cur_vars)
    (hmin : FullMinMarkInv s.core
      (((s.core.tmp.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8 : ∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m)
    (hpost : ∀ (mrk' : List (BitVec 8)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with tmp_len := keep_bv.toNat, mrk := mrk', min_clr_len := 0,
                                min_clr_full := 0#64 }
          scratch := { s.scratch with
            min_removed := s.scratch.min_removed + (orig_tlen_bv - keep_bv),
            learned_lits := s.scratch.learned_lits + keep_bv } }
      mrk'.length = c.max_vars → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      FullMarksClear s' → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (m8MinCleanExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars) orig_tlen_bv c.pMark
      keep_bv) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen := hcore.1.core_ok; have hcv := hlen.cur_vars_le
  have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
  have hz8 : (0 : BitVec 32).setWidth 8 = 0#8 := rfl
  have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    Nat.mod_eq_of_lt (by omega)
  dsimp only [m8MinCleanExpr]
  refine wp_join_group (ts := []) (fun _ m' =>
      ∃ (mrk' : List (BitVec 8)), mrk'.length = c.max_vars ∧
        (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) ∧
        (∀ v < s.core.cur_vars, mrk'[v]?.getD 0#8 = 0#8) ∧
        (FullMem c { s with core := { s.core with mrk := mrk' } } ⋆ R) m') ?_ ?_
  · rintro _ ⟨⟩ mf ⟨mrk', hml', hab', hmc', hmf⟩
    rw [Blocks.get_here]; ml_lets
    ml_st m1, hm1 := store_full_min_clr_len (s := { s with core := { s.core with mrk := mrk' } })
      0 (Nat.zero_lt_succ _) hmf
    ml_st m2, hm2 := store_full_min_clr_full
      (s := { s with core := { s.core with mrk := mrk', min_clr_len := 0 } }) 0#64 hm1
    ml_st m3, hm3 := c0_store_full_tmp_len
      (s := { s with core := { s.core with mrk := mrk', min_clr_len := 0, min_clr_full := 0#64 } })
      keep_bv hm2
    ml_ld load_full_min_removed
      (s := { s with core := { s.core with tmp_len := keep_bv.toNat, mrk := mrk',
                                           min_clr_len := 0, min_clr_full := 0#64 } }) hm3
    ml_lets
    ml_st m4, hm4 := store_full_min_removed
      (s := { s with core := { s.core with tmp_len := keep_bv.toNat, mrk := mrk',
                                           min_clr_len := 0, min_clr_full := 0#64 } })
      (s.scratch.min_removed + (orig_tlen_bv - keep_bv)) hm3
    ml_ld load_full_learned_lits
      (s := { s with core := { s.core with tmp_len := keep_bv.toNat, mrk := mrk',
                                           min_clr_len := 0, min_clr_full := 0#64 }
                     scratch := { s.scratch with
                       min_removed := s.scratch.min_removed + (orig_tlen_bv - keep_bv) } }) hm4
    ml_lets
    ml_st m5, hm5 := store_full_learned_lits
      (s := { s with core := { s.core with tmp_len := keep_bv.toNat, mrk := mrk',
                                           min_clr_len := 0, min_clr_full := 0#64 }
                     scratch := { s.scratch with
                       min_removed := s.scratch.min_removed + (orig_tlen_bv - keep_bv) } })
      (s.scratch.learned_lits + keep_bv) hm4
    rw [wp]; exact hpost mrk' m5 hml' hab' hmc' hm5
  rintro Js hJs; ml_ld load_full_min_clr_full hm; ml_lets; ml_jnz
  refine ⟨fun hnf => ?_, fun hf => ?_⟩
  · refine wp_loop_group (ts := [i64]) (fun n (v, ()) mv =>
        n = s.core.cur_vars - v.toNat ∧ v.toNat ≤ s.core.cur_vars ∧
        ∃ mrk_v : List (BitVec 8), mrk_v.length = c.max_vars ∧
          (∀ w, s.core.cur_vars ≤ w → mrk_v[w]? = s.core.mrk[w]?) ∧
          (∀ w < v.toNat, mrk_v[w]?.getD 0#8 = 0#8) ∧
          (FullMem c { s with core := { s.core with mrk := mrk_v } } ⋆ R) mv) ?_
      (fun J1 hJ1 => by
        ml_lets; exact hJ1 s.core.cur_vars (0#64, ()) m ⟨by rw [h0v]; omega,
          by rw [h0v]; exact Nat.zero_le _, s.core.mrk, hlen.mrk_len, fun _ _ => rfl,
          fun _ h => by rw [h0v] at h; omega, hm⟩)
    rintro J1 n ⟨v, ⟨⟩⟩ mv hJ1 ⟨rfl, hv_le, mrk_v, hml_v, hab_v, hzero_v, hm_v⟩
    let st_v : FullState := { s with core := { s.core with mrk := mrk_v } }
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hvx : v.toNat < s.core.cur_vars := by
        rw [BitVec.ult, decide_eq_true_eq, hcv_bv] at hlt; exact hlt
      have hvm : v.toNat < st_v.core.mrk.length := by dsimp only [st_v]; rw [hml_v]; omega
      ml_lets
      ml_st mn, hmn := c0_store_full_mrk (s := st_v) (i := v) ((0 : BitVec 32).setWidth 8) hvm hm_v
      rw [hz8] at hmn
      have hv1 : (v + 1).toNat = v.toNat + 1 := min_bv64_add1 (by omega)
      ml_lets
      refine hJ1 (s.core.cur_vars - (v + 1).toNat) (v + 1, ()) mn (by omega)
        ⟨by rw [hv1], by rw [hv1]; omega, mrk_v.set v.toNat 0#8, by rw [List.length_set, hml_v],
          fun w hw => by rw [List.getElem?_set_ne (by omega)]; exact hab_v w hw,
          fun w hw => by
            rw [hv1] at hw; by_cases hwe : w = v.toNat
            · subst w; rw [List.getElem?_set_self (by rw [hml_v]; omega), Option.getD_some]
            · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hzero_v w (by omega),
          hmn⟩
    · have hve : v.toNat = s.core.cur_vars := by
        rw [BitVec.ult, decide_eq_false_iff_not, hcv_bv] at hge; omega
      exact hJs () mv ⟨mrk_v, hml_v, hab_v, fun w hw => hzero_v w (by omega), hm_v⟩
  · have hnf' : s.core.min_clr_full = 0#64 := by c0_cond hf; exact hf
    ml_ld load_full_min_clr_ptr hm; ml_lets
    refine wp_loop_group (ts := [i64]) (fun n (z, ()) mz =>
        n = s.core.min_clr_len - z.toNat ∧ z.toNat ≤ s.core.min_clr_len ∧
        ∃ mrk_z : List (BitVec 8), mrk_z.length = c.max_vars ∧
          (∀ w, s.core.cur_vars ≤ w → mrk_z[w]? = s.core.mrk[w]?) ∧
          (∀ w < s.core.cur_vars, mrk_z[w]?.getD 0#8 ≠ 0#8 →
            ∃ k, z.toNat ≤ k ∧ k < s.core.min_clr_len ∧ (s.core.min_clr[k]?.getD 0#32).toNat = w) ∧
          (FullMem c { s with core := { s.core with mrk := mrk_z } } ⋆ R) mz) ?_
      (fun J2 hJ2 => by
        ml_lets; refine hJ2 s.core.min_clr_len (0#64, ()) m
          ⟨by rw [h0v]; omega, by rw [h0v]; exact Nat.zero_le _, s.core.mrk, hlen.mrk_len,
            fun _ _ => rfl, fun w hw hnz => ?_, hm⟩
        obtain ⟨k, hk, hke⟩ :=
          hmin.clr_cov hnf' w hw ((m8MinMarkInvMrkNeZeroIff hmin hno8 hw).mp hnz)
        exact ⟨k, by rw [h0v]; exact Nat.zero_le _, hk, hke⟩)
    rintro J2 n ⟨z, ⟨⟩⟩ mz hJ2 ⟨rfl, hzle, mrk_z, hml_z, hab_z, hcov_z, hm_z⟩
    let st_z : FullState := { s with core := { s.core with mrk := mrk_z } }
    rw [Blocks.get_here]; ml_ld load_full_min_clr_len (s := st_z) hm_z; ml_lets; ml_jnz
    have hmcl_bv : (BitVec.ofNat 64 s.core.min_clr_len).toNat = s.core.min_clr_len :=
      Nat.mod_eq_of_lt (by have := hlen.min_clr_len_le; omega)
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hzm : z.toNat < s.core.min_clr_len := by
        rw [BitVec.ult, decide_eq_true_eq, hmcl_bv] at hlt; exact hlt
      have hzl : z.toNat < st_z.core.min_clr.length := by
        dsimp only [st_z]; rw [hlen.min_clr_len_arr]; have := hlen.min_clr_len_le; omega
      have hz1 : (z + 1).toNat = z.toNat + 1 :=
        min_bv64_add1 (by have := hlen.min_clr_len_le; omega)
      ml_ld c0_load_full_min_clr (s := st_z) (i := z) hzl hm_z
      let v32 := st_z.core.min_clr[z.toNat]'hzl
      refine wp_join_group (ts := []) (fun _ mn =>
          ∃ mrk_n : List (BitVec 8), mrk_n.length = c.max_vars ∧
            (∀ w, s.core.cur_vars ≤ w → mrk_n[w]? = s.core.mrk[w]?) ∧
            (∀ w < s.core.cur_vars, mrk_n[w]?.getD 0#8 ≠ 0#8 →
              ∃ k, z.toNat + 1 ≤ k ∧ k < s.core.min_clr_len ∧
                (s.core.min_clr[k]?.getD 0#32).toNat = w) ∧
            (FullMem c { s with core := { s.core with mrk := mrk_n } } ⋆ R) mn)
        (fun _ ⟨⟩ mn ⟨mrk_n, hml_n, hab_n, hcov_n, hm_n⟩ => by
          rw [Blocks.get_here]; ml_lets
          exact hJ2 (s.core.min_clr_len - (z + 1).toNat) (z + 1, ()) mn (by omega)
            ⟨by rw [hz1], by rw [hz1]; omega, mrk_n, hml_n, hab_n,
              by simpa only [hz1] using hcov_n, hm_n⟩) ?_
      rintro Jstep hJstep
      ml_lets; ml_jnz; refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
      · have hv_lt : v32.toNat < s.core.cur_vars := by
          rw [BitVec.ult, decide_eq_true_eq, bv_c0_zext32_64, hcv_bv] at hvlt; exact hvlt
        have hvm : (v32.setWidth 64).toNat < st_z.core.mrk.length := by
          dsimp only [st_z]; rw [hml_z, bv_c0_zext32_64]; omega
        ml_lets; ml_st mn, hmn := c0_store_full_mrk (s := st_z) (i := v32.setWidth 64)
          ((0 : BitVec 32).setWidth 8) hvm hm_z
        rw [hz8, bv_c0_zext32_64] at hmn
        refine hJstep () mn ⟨mrk_z.set v32.toNat 0#8, by rw [List.length_set, hml_z],
          fun w hw => by rw [List.getElem?_set_ne (by omega)]; exact hab_z w hw,
          fun w hw hnz => ?_, hmn⟩
        have hwne : w ≠ v32.toNat := by
          rintro rfl; rw [List.getElem?_set_self (by rw [hml_z]; omega)] at hnz; exact hnz rfl
        rw [List.getElem?_set_ne (Ne.symm hwne)] at hnz
        obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
        have hknz : k ≠ z.toNat := by
          rintro rfl; rw [List.getElem?_eq_getElem hzl, Option.getD_some] at hke
          exact hwne hke.symm
        exact ⟨k, by omega, hk2, hke⟩
      · have hvx : s.core.cur_vars ≤ v32.toNat := by
          rw [BitVec.ult, decide_eq_false_iff_not, not_lt, bv_c0_zext32_64, hcv_bv] at hvge
          exact hvge
        refine hJstep () mz ⟨mrk_z, hml_z, hab_z, fun w hw hnz => ?_, hm_z⟩
        obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
        have hknz : k ≠ z.toNat := by
          rintro rfl; dsimp only [v32] at hvx
          rw [show st_z.core.min_clr[z.toNat]'hzl =
                (some (st_z.core.min_clr[z.toNat]'hzl)).getD 0#32 from rfl,
            ← List.getElem?_eq_getElem hzl, hke] at hvx
          omega
        exact ⟨k, by omega, hk2, hke⟩
    · have hze : z.toNat = s.core.min_clr_len := by
        rw [BitVec.ult, decide_eq_false_iff_not, hmcl_bv] at hge; omega
      exact hJs () mz ⟨mrk_z, hml_z, hab_z, fun w hw => by
        by_cases hz : mrk_z[w]?.getD 0#8 = 0#8; · exact hz
        exfalso; obtain ⟨k, hk1, hk2, _⟩ := hcov_z w hw hz; omega, hm_z⟩

private structure M8BlkLoopInv (c : FullCfg) (F0 : CNF Nat) (s s_c1 : FullState)
    (tlen beg : Nat) (cur : FullState) : Prop where
  core : FullOtfsCoreInv c F0 cur
  min_inv : FullMinMarkInv cur.core
    (((cur.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)
  entails : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
    FullOtfsWitnessInv c F0 F_cur cur.core ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      (((cur.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
  nodup : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
    (((cur.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map
      fun x => x.toNat / 2).Nodup
  mrk_above : ∀ v, s.core.cur_vars ≤ v → cur.core.mrk[v]? = s.core.mrk[v]?
  no8 : ∀ v < s.core.cur_vars, (cur.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8
  cv_eq : cur.core.cur_vars = s.core.cur_vars
  tl_eq : cur.core.tmp_len = s.core.tmp_len
  lvl_eq : cur.core.lvl = s.core.lvl
  vals_eq : cur.core.vals = s.core.vals
  clvl_eq : cur.core.cur_level = s.core.cur_level
  tpos_eq : cur.core.trail_pos = s.core.trail_pos
  zero_eq : cur.core.tmp[0]? = s_c1.core.tmp[0]?
  tail_eq : ∀ k, beg ≤ k → k < tlen → cur.core.tmp[k]? = s_c1.core.tmp[k]?
  beg_bnd : 1 < beg → beg < tlen →
    (s.core.lvl[(s_c1.core.tmp[beg - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
    (s.core.lvl[(s_c1.core.tmp[beg]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  rem_mrk : ∀ k < tlen, cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (cur.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    (cur.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8
  post_lvls : ∀ k, 1 ≤ k → k < tlen →
    cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
    (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

private theorem m8_min_shrink_blk_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s_c1 : FullState} {tlen : Nat} {tlen_bv : BitVec 64} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost}
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X)
    (htlen_eq : tlen_bv.toNat = tlen) (ht1 : 1 ≤ tlen) (ht_cv : tlen ≤ s.core.cur_vars)
    (ht_tl : tlen ≤ s.core.tmp_len)
    (hc1_inv : M8BlkLoopInv c F0 s s_c1 tlen 1 s_c1)
    (hc1_0eq : s_c1.core.tmp[0]? = s.core.tmp[0]?)
    (hc1_0ne : s_c1.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hc1_0lv : (s.core.lvl[(s_c1.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      s.core.cur_level)
    (hc1_ne : ∀ k < tlen, s_c1.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hc1_lvls : ∀ k, 1 ≤ k → k < tlen →
      let lv := (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    (hc1_sort : ∀ i j, 1 ≤ i → i ≤ j → j < tlen →
      (s.core.lvl[(s_c1.core.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s_c1.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {m : Mem 64} (hm_in : (FullMem c s_c1 ⋆ R) m)
    (hpost : ∀ (tmp' : List (BitVec 32)) (tl' : Nat) (mrk' : List (BitVec 8))
        (mclr' sstk' wsort' : List (BitVec 32)) (mcl' : Nat)
        (mcf' llits' mrem' ticks' : BitVec 64) (m' : Mem 64),
      let s' := m8MinShrinkRes s_c1 tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf'
        s_c1.scratch.conflicts llits' mrem' ticks'
      tmp'.length = c.max_vars → mrk'.length = c.max_vars → mclr'.length = c.max_vars →
      mcl' ≤ c.max_vars → sstk'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) → FullMarksClear s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      (((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
        (∀ k, 1 ≤ k → k < s.core.tmp_len →
          (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
          (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup) →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
        lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (m8MinBlkLoopExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      tlen_bv c.pTmp c.pLevel c.pTrailPos tlen_bv) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hc1_inv.core.1.core_ok.cur_vars_le; rw [hc1_inv.cv_eq] at hcv
  have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
  dsimp only [m8MinBlkLoopExpr]
  refine wp_loop_group (ts := [i64]) (fun n (beg, ()) mb =>
      n = tlen - beg.toNat ∧ 1 ≤ beg.toNat ∧ beg.toNat ≤ tlen ∧
      ∃ (mrk_b : List (BitVec 8)) (tmp_b mclr_b sstk_b wsort_b : List (BitVec 32))
        (mcl_b : Nat) (mcf_b ticks_b : BitVec 64),
      let cur := m8BlkState s_c1 tmp_b mrk_b mclr_b sstk_b wsort_b mcl_b mcf_b ticks_b
      M8BlkLoopInv c F0 s s_c1 tlen beg.toNat cur ∧ (FullMem c cur ⋆ R) mb) ?_
    (fun Js hJs => by
      ml_lets; exact hJs (tlen - 1) (1#64, ()) m
        ⟨by rw [h1v], by rw [h1v]; exact le_refl _, by rw [h1v]; exact ht1,
         s_c1.core.mrk, s_c1.core.tmp, s_c1.core.min_clr, s_c1.scratch.shrink_stk,
         s_c1.scratch.wsort, s_c1.core.min_clr_len, s_c1.core.min_clr_full,
         s_c1.scratch.search_ticks, by rw [h1v]; exact hc1_inv, hm_in⟩)
  rintro Js n ⟨beg, ⟨⟩⟩ mb hJs
    ⟨rfl, hbeg1, hbeg_tl, mrk_b, tmp_b, mclr_b, sstk_b, wsort_b, mcl_b, mcf_b, ticks_b,
      hb, hm_b⟩
  let cur := m8BlkState s_c1 tmp_b mrk_b mclr_b sstk_b wsort_b mcl_b mcf_b ticks_b
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have hbx : beg.toNat < tlen := by
      rw [BitVec.ult, decide_eq_true_eq, htlen_eq] at hlt; exact hlt
    have hbg_tl : beg.toNat < cur.core.tmp.length := by
      dsimp only [cur]; rw [hb.core.1.core_ok.tmp_len_arr]; omega
    ml_ld c0_load_full_tmp (s := cur) (i := beg) hbg_tl hm_b
    let lit_b := cur.core.tmp[beg.toNat]'hbg_tl
    have hbt1 : cur.core.tmp[beg.toNat]? = s_c1.core.tmp[beg.toNat]? :=
      hb.tail_eq beg.toNat (le_refl _) hbx
    have hne_b : cur.core.tmp[beg.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [hbt1]; exact hc1_ne beg.toNat hbx
    have hr_b := hb.rem_mrk beg.toNat hbx hne_b
    rw [List.getElem?_eq_getElem hbg_tl, Option.getD_some] at hr_b
    have hr_b1 : lit_b.toNat < 2 * s.core.cur_vars := hr_b.1
    have hbv_lt : (lit_b >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr_1]; omega
    have hblvl_l : ((lit_b >>> 1).setWidth 64).toNat < cur.core.lvl.length := by
      rw [hb.core.1.core_ok.lvl_len, bv_c0_zext32_64]; omega
    ml_lets; ml_ld c0_load_full_lvl (s := cur) (i := (lit_b >>> 1).setWidth 64) hblvl_l hm_b
    let blvl := cur.core.lvl[((lit_b >>> 1).setWidth 64).toNat]'hblvl_l
    ml_ld c0_load_full_tmp (s := cur) (i := beg) hbg_tl hm_b
    let lit_b' := cur.core.tmp[beg.toNat]'hbg_tl
    have hbt_len : cur.core.trail_pos.length = c.max_vars := hb.core.1.core_ok.trail_pos_len
    have hbtp_l : ((lit_b' >>> 1).setWidth 64).toNat < cur.core.trail_pos.length := by
      rw [hbt_len, bv_c0_zext32_64]; change (lit_b >>> 1).toNat < _; omega
    ml_lets; ml_ld c0_load_full_trail_pos (s := cur) (i := (lit_b' >>> 1).setWidth 64) hbtp_l hm_b
    let tp0 := cur.core.trail_pos[((lit_b' >>> 1).setWidth 64).toNat]'hbtp_l
    have hlit_b_eq : lit_b.toNat = (s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat := by
      dsimp only [lit_b]; rw [← hbt1, List.getElem?_eq_getElem hbg_tl, Option.getD_some]
    have hblv_nat : blvl.toNat =
        (s.core.lvl[(s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
      dsimp only [blvl]
      rw [show cur.core.lvl[((lit_b >>> 1).setWidth 64).toNat]'hblvl_l =
            (some (cur.core.lvl[((lit_b >>> 1).setWidth 64).toNat]'hblvl_l)).getD 0#32 from rfl,
        ← List.getElem?_eq_getElem hblvl_l, bv_c0_zext32_64, bv32_lshr_1, hb.lvl_eq, hlit_b_eq]
    have hblv_ok : 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level := by
      rw [hblv_nat]; exact hc1_lvls beg.toNat hbeg1 hbx
    have htp0_nat : (tp0.setWidth 64).toNat =
        (s.core.trail_pos[(s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
      rw [bv_c0_zext32_64]; dsimp only [tp0, lit_b']
      rw [show cur.core.trail_pos[((lit_b' >>> 1).setWidth 64).toNat]'hbtp_l =
            (some (cur.core.trail_pos[((lit_b' >>> 1).setWidth 64).toNat]'hbtp_l)).getD 0#32
            from rfl,
        ← List.getElem?_eq_getElem hbtp_l, bv_c0_zext32_64, bv32_lshr_1, hb.tpos_eq]
      rw [show lit_b'.toNat = lit_b.toNat from rfl, hlit_b_eq]
    have hbeg1_nat : (beg + 1).toNat = beg.toNat + 1 := min_bv64_add1 (by omega)
    ml_lets
    refine wp_loop_group (ts := [i64, i64]) (fun n (max_tr, end_b, ()) m_w =>
        n = tlen - end_b.toNat ∧ m_w = mb ∧ beg.toNat < end_b.toNat ∧ end_b.toNat ≤ tlen ∧
        (∀ k, beg.toNat ≤ k → k < end_b.toNat →
          (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
          (s.core.trail_pos[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            max_tr.toNat)) ?_
      (fun Js_1 hJs_1 => by
        ml_lets; exact hJs_1 (tlen - (beg.toNat + 1)) (tp0.setWidth 64, beg + 1, ()) mb
          ⟨by rw [hbeg1_nat], rfl, by rw [hbeg1_nat]; omega, by rw [hbeg1_nat]; omega,
            fun k hk1 hk2 => by
              rw [hbeg1_nat] at hk2; have hke : k = beg.toNat := by omega
              subst k; exact ⟨hblv_nat.symm, by rw [htp0_nat]; exact le_refl _⟩⟩)
    rintro Js_1 n_w ⟨max_tr, end_b, ⟨⟩⟩ m_w hJs_1 ⟨rfl, hmw_eq, hbeg_end, hend_tl, hblk_in⟩
    subst m_w
    rw [Blocks.get_here]
    refine wp_join_group (ts := []) (fun () m_end =>
        m_end = mb ∧ (end_b.toNat < tlen → blvl.toNat <
          (s.core.lvl[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)) ?_ ?_
    · rintro J_ex ⟨⟩ m_end ⟨hm_end_eq, hstep_end⟩; subst m_end; rw [Blocks.get_here]
      refine wp_join_group (ts := []) (fun () m_next =>
          ∃ mrk_n tmp_n mclr_n sstk_n wsort_n mcl_n mcf_n ticks_n,
            let cur_n := m8BlkState s_c1 tmp_n mrk_n mclr_n sstk_n wsort_n mcl_n mcf_n ticks_n
            M8BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_n ∧ (FullMem c cur_n ⋆ R) m_next)
        (fun _ ⟨⟩ m_next ⟨mrk_n, tmp_n, mclr_n, sstk_n, wsort_n, mcl_n, mcf_n, ticks_n,
            hn, hm_n⟩ => by
          rw [Blocks.get_here]; ml_lets
          exact hJs (tlen - end_b.toNat) (end_b, ()) m_next (by omega)
            ⟨rfl, by omega, hend_tl, mrk_n, tmp_n, mclr_n, sstk_n, wsort_n, mcl_n, mcf_n,
              ticks_n, hn, hm_n⟩) ?_
      rintro J_nb hJ_nb; ml_lets; ml_jnz; refine ⟨fun hge2 => ?_, fun hlt2 => ?_⟩
      · have h2le : 2 ≤ end_b.toNat - beg.toNat := by
          c0_cond hge2
          have h1 := beg.isLt; have h2 := end_b.isLt
          have hmod : (2 ^ 64 - beg.toNat + end_b.toNat) % 2 ^ 64 = end_b.toNat - beg.toNat := by
            rw [show 2 ^ 64 - beg.toNat + end_b.toNat = 2 ^ 64 + (end_b.toNat - beg.toNat)
                  from by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          rw [hmod] at hge2; exact hge2
        refine wp_join_group (ts := []) (fun () m_done =>
            ∃ mrk_n tmp_n mclr_n sstk_n wsort_n mcl_n mcf_n ticks_n,
              let cur_n := m8BlkState s_c1 tmp_n mrk_n mclr_n sstk_n wsort_n mcl_n mcf_n ticks_n
              M8BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_n ∧ (FullMem c cur_n ⋆ R) m_done)
          (fun _ ⟨⟩ m_done hdone => by rw [Blocks.get_here]; exact hJ_nb () m_done hdone) ?_
        rintro J_bd hJ_bd
        have hblk_cur : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
            let l := (cur.core.tmp[k]?.getD 0#32).toNat
            l < 2 * cur.core.cur_vars ∧ cur.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
            (cur.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
            (cur.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat := fun k hk1 hk2 => by
          have hk_t : k < tlen := Nat.lt_of_lt_of_le hk2 hend_tl
          have htk := hb.tail_eq k (by omega) hk_t
          have hne_k : cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            rw [htk]; exact hc1_ne k hk_t
          have hrm := hb.rem_mrk k hk_t hne_k
          have hbi := hblk_in k hk1 hk2
          dsimp only; rw [hb.cv_eq, hb.vals_eq, hb.lvl_eq, hb.tpos_eq]
          refine ⟨hrm.1, hrm.2.1, ?_, ?_⟩
          · rw [htk]; exact hbi.1
          · rw [htk]; exact hbi.2
        have hkeep_cur : ∀ k < tlen, cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
            let l := (cur.core.tmp[k]?.getD 0#32).toNat
            l < 2 * cur.core.cur_vars ∧ cur.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
            (cur.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun k hk hne => by
          have hrm := hb.rem_mrk k hk hne; rw [hb.cv_eq, hb.vals_eq]; exact hrm
        apply wp_call_of_spec; apply hSb
        dsimp only [vals, Arg.val]
        refine m8ShrinkBlkBoolSpec_of hb.core (m8_toFullMinInv hb.min_inv)
          (fun v hv => hb.no8 v (hb.cv_eq ▸ hv)) hbeg1 hbeg_end hend_tl
          (by rw [hb.cv_eq]; exact ht_cv) hblv_ok.1 (by rw [hb.clvl_eq]; exact hblv_ok.2)
          hblk_cur hkeep_cur hm_b ?_
        intro ok_s tmp_s mrk_s mclr_s sstk_s wsort_s mcl_s mcf_s ticks_s m_s
          hcore_s hmin_sf hab_s h8_s hmono2_s hfl_s hoth_s hlvl_s hnd_s hEnt_s hrem_s hm_s
        have hmin_s := m8_toSpecsMinInv hmin_sf
        let st_s := m8BlkState cur tmp_s mrk_s mclr_s sstk_s wsort_s mcl_s mcf_s ticks_s
        have hst_s_eq : st_s =
            m8BlkState s_c1 tmp_s mrk_s mclr_s sstk_s wsort_s mcl_s mcf_s ticks_s := rfl
        have hinv_s' : M8BlkLoopInv c F0 s s_c1 tlen end_b.toNat st_s := by
          refine ⟨hcore_s, hmin_s, fun F_cur hw hEnt0 => ?_, fun hnd0 hne0 => ?_,
            fun v hv => (hab_s v (hb.cv_eq ▸ hv)).trans (hb.mrk_above v hv),
            fun v hv => h8_s v (hb.cv_eq ▸ hv),
            hb.cv_eq, hb.tl_eq, hb.lvl_eq, hb.vals_eq, hb.clvl_eq, hb.tpos_eq,
            ?_, fun k hk1 hk2 => ?_, ?_, fun k hk hne => ?_, fun k hk1 hk2 hne => ?_⟩
          · obtain ⟨hw1, he1⟩ := hb.entails F_cur hw hEnt0
            have ⟨hw2, he2⟩ := hEnt_s F_cur hw1 he1
            exact ⟨hw2, he2⟩
          · refine hnd_s (hb.nodup hnd0 hne0) fun k hk hkb hne => ?_
            intro heq
            have heq_s : (s.core.lvl[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                blvl.toNat :=
              (congrArg (fun lv => (lv[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
                hb.lvl_eq.symm).trans heq
            by_cases hk0 : k = 0
            · subst k; rw [hb.zero_eq] at heq_s
              have heq' : (s.core.lvl[(s_c1.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  blvl.toNat := heq_s
              rw [hc1_0lv] at heq'; exact absurd heq' (Nat.ne_of_gt hblv_ok.2)
            · rw [hb.post_lvls k (Nat.pos_of_ne_zero hk0) hk hne] at heq_s
              rcases hkb with hlt_b | hge_e
              · have hc := hb.beg_bnd (by omega) hbx
                have hs1 := hc1_sort k (beg.toNat - 1) (Nat.pos_of_ne_zero hk0) (by omega)
                  (by omega)
                omega
              · have he1 := hstep_end (by omega)
                have hs1 := hc1_sort end_b.toNat k (Nat.le_trans hbeg1 (le_of_lt hbeg_end)) hge_e hk
                omega
          · have h0 := hoth_s 0 (by omega) (Or.inl (by omega)); rw [h0]; exact hb.zero_eq
          · rw [hoth_s k hk2 (Or.inr hk1)]; exact hb.tail_eq k (by omega) hk2
          · intro _ hend_lt
            have := (hblk_in (end_b.toNat - 1) (by omega) (by omega)).1
            have := hstep_end hend_lt; omega
          · have hr := hrem_s k hk hne
            rw [hb.cv_eq, hb.vals_eq] at hr; exact hr
          · by_cases hk_in : beg.toNat ≤ k ∧ k < end_b.toNat
            · have hl1 := hlvl_s k hk_in.1 hk_in.2 hne
              have hl2 := (hblk_in k hk_in.1 hk_in.2).1
              have hl1' : (s.core.lvl[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  blvl.toNat :=
                (congrArg (fun lv => (lv[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
                  hb.lvl_eq.symm).trans hl1
              rw [hl1', hl2]
            · have hkb : k < beg.toNat ∨ end_b.toNat ≤ k := by omega
              have hne' := hne; rw [hoth_s k (by omega) hkb] at hne'
              rw [hoth_s k (by omega) hkb]; exact hb.post_lvls k hk1 hk2 hne'
        ml_lets; ml_jnz; refine ⟨fun hok_t => ?_, fun hok_f => ?_⟩
        · exact hJ_bd () m_s ⟨mrk_s, tmp_s, mclr_s, sstk_s, wsort_s, mcl_s, mcf_s, ticks_s,
            hinv_s', hst_s_eq ▸ hm_s⟩
        · have hf_s : ok_s = false := by c0_cond hok_f; exact hok_f
          have htmp_s_eq : tmp_s = cur.core.tmp := hfl_s hf_s
          refine wp_loop_group (ts := [i64]) (fun n_d (mk2, ()) md =>
              n_d = end_b.toNat - mk2.toNat ∧ beg.toNat ≤ mk2.toNat ∧ mk2.toNat ≤ end_b.toNat ∧
              ∃ (mrk_d : List (BitVec 8)) (tmp_d mclr_d wsort_d : List (BitVec 32))
                (mcl_d : Nat) (mcf_d ticks_d : BitVec 64),
                let cur_d := m8BlkState s_c1 tmp_d mrk_d mclr_d sstk_s wsort_d mcl_d mcf_d ticks_d
                M8BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_d ∧
                (∀ k, beg.toNat ≤ k → k < end_b.toNat → mk2.toNat ≤ k →
                  cur_d.core.tmp[k]? = tmp_s[k]?) ∧
                (FullMem c cur_d ⋆ R) md) ?_
            (fun Js_3 hJs_3 => by
              ml_lets; exact hJs_3 (end_b.toNat - beg.toNat) (beg, ()) m_s
                ⟨rfl, le_refl _, le_of_lt hbeg_end, mrk_s, tmp_s, mclr_s, wsort_s,
                  mcl_s, mcf_s, ticks_s, hinv_s', fun _ _ _ _ => rfl, hst_s_eq ▸ hm_s⟩)
          rintro Js_3 n_d ⟨mk2, ⟨⟩⟩ md hJs_3 ⟨rfl, hmk2_lb, hmk2_ub, mrk_d, tmp_d, mclr_d,
            wsort_d, mcl_d, mcf_d, ticks_d, hd, hd_tail, hm_d⟩
          let cur_d := m8BlkState s_c1 tmp_d mrk_d mclr_d sstk_s wsort_d mcl_d mcf_d ticks_d
          rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hmk2_lt => ?_, fun hmk2_done => ?_⟩
          · c0_cond hmk2_lt
            have hmk2_t : mk2.toNat < tlen := Nat.lt_of_lt_of_le hmk2_lt hend_tl
            have hmk2_tl : mk2.toNat < cur_d.core.tmp.length := by
              dsimp only [cur_d]; rw [hd.core.1.core_ok.tmp_len_arr]; omega
            have hmk2_1 : (mk2 + 1).toNat = mk2.toNat + 1 := min_bv64_add1 (by omega)
            refine wp_join_group (ts := []) (fun _ md_n =>
                ∃ (mrk_n : List (BitVec 8)) (tmp_n mclr_n wsort_n : List (BitVec 32))
                  (mcl_n : Nat) (mcf_n ticks_n : BitVec 64),
                  let cur_n := m8BlkState s_c1 tmp_n mrk_n mclr_n sstk_s wsort_n mcl_n mcf_n ticks_n
                  M8BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_n ∧
                  (∀ k, beg.toNat ≤ k → k < end_b.toNat → mk2.toNat + 1 ≤ k →
                    cur_n.core.tmp[k]? = tmp_s[k]?) ∧
                  (FullMem c cur_n ⋆ R) md_n)
              (fun _ ⟨⟩ md_n ⟨mrk_n, tmp_n, mclr_n, wsort_n, mcl_n, mcf_n, ticks_n,
                  hn, hnt, hm_n⟩ => by
                rw [Blocks.get_here]; ml_lets
                exact hJs_3 (end_b.toNat - (mk2 + 1).toNat) (mk2 + 1, ()) md_n (by omega)
                  ⟨rfl, by rw [hmk2_1]; omega, by rw [hmk2_1]; omega,
                    mrk_n, tmp_n, mclr_n, wsort_n, mcl_n, mcf_n, ticks_n, hn,
                    by simpa only [hmk2_1] using hnt, hm_n⟩) ?_
            rintro Jnext hJnext
            ml_ld c0_load_full_tmp (s := cur_d) (i := mk2) hmk2_tl hm_d
            let root_lit := cur_d.core.tmp[mk2.toNat]'hmk2_tl
            have hrl_eq : cur_d.core.tmp[mk2.toNat]? = some root_lit :=
              List.getElem?_eq_getElem hmk2_tl
            have hrl_orig : cur_d.core.tmp[mk2.toNat]? = s_c1.core.tmp[mk2.toNat]? := by
              rw [hd_tail mk2.toNat hmk2_lb hmk2_lt (le_refl _), htmp_s_eq]
              exact hb.tail_eq mk2.toNat hmk2_lb hmk2_t
            have hrl_ne : root_lit ≠ 0xFFFFFFFF#32 := by
              have := hc1_ne mk2.toNat hmk2_t
              rwa [← hrl_orig, hrl_eq, Option.getD_some] at this
            have hrl_rm := hd.rem_mrk mk2.toNat hmk2_t (by rwa [hrl_eq, Option.getD_some])
            rw [hrl_eq, Option.getD_some] at hrl_rm
            have hrl_lvl : (cur_d.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat <
                cur_d.core.cur_level := by
              rw [hd.lvl_eq, hd.clvl_eq]
              have hrn : root_lit.toNat = (s_c1.core.tmp[mk2.toNat]?.getD 0#32).toNat := by
                rw [← hrl_orig, hrl_eq, Option.getD_some]
              rw [hrn]; exact (hc1_lvls mk2.toNat (by omega) hmk2_t).2
            ml_lets; apply wp_call_of_spec; apply hDfs
            dsimp only [vals, Arg.val]
            refine m8MinLitDfsSpec_of hd.core (m8_toFullMinInv hd.min_inv)
              (by rw [hd.cv_eq]; exact hrl_rm.1) (by rw [hd.vals_eq]; exact hrl_rm.2.1) hrl_lvl
              (fun v hv _ => hd.no8 v (hd.cv_eq ▸ hv)) hm_d ?_
            intro ok_d mrk_n wsort_n mclr_n mcl_n mcf_n ticks_n m_dn _s_dn
              hlen_dn hab_dn hmono2_dn hbit8_dn hmin_df hok_dn hm_dn
            have hmin_dn := m8_toSpecsMinInv hmin_df
            have hok_dn' : ok_d = true →
                (∀ keep', (∀ l ∈ (((cur_d.core.tmp.take tlen).filter
                      (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep') →
                  FullMinMarkInv (m8MinLitDfsState cur_d mrk_n wsort_n mclr_n
                    mcl_n mcf_n ticks_n).core keep') ∧
                FullMinMarkInv (fullMinMarkCore (m8MinLitDfsState cur_d mrk_n wsort_n mclr_n
                    mcl_n mcf_n ticks_n).core (root_lit.toNat / 2) 2#8)
                  (((cur_d.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) :=
              fun h => let ⟨h1, h2⟩ := hok_dn h
                ⟨fun keep' hs => m8_toSpecsMinInv (h1 keep' hs), m8_toSpecsMinInv h2⟩
            obtain ⟨hcore_n, hmin_n, hent_n, hnd_n, hab_n, hno8_n, hrem_n, hpost_k⟩ :=
              m8MinLitStepState hmk2_t (by rw [hd.cv_eq]; exact ht_cv) hd.core
                hd.min_inv hd.entails hd.nodup
                (fun v hv => hd.mrk_above v (hd.cv_eq ▸ hv))
                (fun v hv => hd.no8 v (hd.cv_eq ▸ hv))
                (fun k hk hne => by
                  have h := hd.rem_mrk k hk hne; rw [← hd.cv_eq, ← hd.vals_eq] at h; exact h)
                hrl_eq hrl_ne hlen_dn
                hab_dn hmono2_dn hbit8_dn hmin_dn hok_dn'
            let tmp_n := if ok_d then cur_d.core.tmp.set mk2.toNat 0xFFFFFFFF#32 else cur_d.core.tmp
            let cur_n : FullState := m8BlkState s_c1 tmp_n mrk_n mclr_n sstk_s wsort_n
              mcl_n mcf_n ticks_n
            have hcur_n_eq : cur_n = m8BlkState cur_d tmp_n mrk_n mclr_n
                cur_d.scratch.shrink_stk wsort_n mcl_n mcf_n ticks_n := rfl
            have hzero_n : cur_n.core.tmp[0]? = s_c1.core.tmp[0]? := by
              rw [← hd.zero_eq]; dsimp only [cur_n, m8BlkState, m8ShrinkBlkBoolState, tmp_n]
              cases ok_d <;> simp only [Bool.false_eq_true, ↓reduceIte]
              · rfl
              · exact List.getElem?_set_ne (by omega)
            have htail_n : ∀ k, end_b.toNat ≤ k → k < tlen →
                cur_n.core.tmp[k]? = s_c1.core.tmp[k]? := fun k hk1 hk2 => by
              dsimp only [cur_n, m8BlkState, m8ShrinkBlkBoolState, tmp_n]
              have hdt : cur_d.core.tmp[k]? = s_c1.core.tmp[k]? := hd.tail_eq k hk1 hk2
              cases ok_d <;> simp only [Bool.false_eq_true, ↓reduceIte]
              · exact hdt
              · rw [List.getElem?_set_ne (by omega)]; exact hdt
            have hinv_n : M8BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur_n :=
              ⟨hcur_n_eq ▸ hcore_n, hcur_n_eq ▸ hmin_n, fun F_cur hw hEnt0 => by
                  have h := hcur_n_eq ▸ hent_n F_cur hw hEnt0; exact h,
                fun hnd0 hne0 => hcur_n_eq ▸ hnd_n hnd0 hne0,
                fun v hv => hcur_n_eq ▸ hab_n v (hd.cv_eq ▸ hv),
                fun v hv => hcur_n_eq ▸ hno8_n v (hd.cv_eq ▸ hv),
                hd.cv_eq, hd.tl_eq, hd.lvl_eq, hd.vals_eq, hd.clvl_eq, hd.tpos_eq,
                hzero_n, htail_n, hd.beg_bnd, fun k hk hne => by
                  have hne' : (m8BlkState cur_d tmp_n mrk_n mclr_n cur_d.scratch.shrink_stk
                      wsort_n mcl_n mcf_n ticks_n).core.tmp[k]?.getD 0xFFFFFFFF#32 ≠
                      0xFFFFFFFF#32 := by
                    rw [← hcur_n_eq]; exact hne
                  have hr := hrem_n k hk hne'
                  dsimp only [cur_n, m8BlkState, m8ShrinkBlkBoolState, tmp_n] at hr ⊢
                  have hcv_c : (m8BlkState s_c1 tmp_d mrk_d mclr_d sstk_s wsort_d
                      mcl_d mcf_d ticks_d).core.cur_vars = s.core.cur_vars := hd.cv_eq
                  have hvals_c : (m8BlkState s_c1 tmp_d mrk_d mclr_d sstk_s wsort_d
                      mcl_d mcf_d ticks_d).core.vals = s.core.vals := hd.vals_eq
                  rw [hcv_c, hvals_c] at hr; exact hr,
                fun k hk1 hk2 hne => by
                  dsimp only [cur_n, m8BlkState, m8ShrinkBlkBoolState, tmp_n] at hne ⊢
                  cases ok_d <;> simp only [Bool.false_eq_true, ↓reduceIte] at hne ⊢
                  · exact hd.post_lvls k hk1 hk2 hne
                  · by_cases hkm : k = mk2.toNat
                    · subst k; exfalso; apply hne
                      rw [List.getElem?_set_self hmk2_tl]; rfl
                    · rw [List.getElem?_set_ne (Ne.symm hkm)] at hne ⊢
                      exact hd.post_lvls k hk1 hk2 hne⟩
            have hnt : ∀ k, beg.toNat ≤ k → k < end_b.toNat → mk2.toNat + 1 ≤ k →
                cur_n.core.tmp[k]? = tmp_s[k]? := fun k hk1 hk2 hk3 => by
              have hdt := hd_tail k hk1 hk2 (by omega)
              dsimp only [cur_n, m8BlkState, m8ShrinkBlkBoolState, tmp_n]
              cases ok_d <;> simp only [Bool.false_eq_true, ↓reduceIte]
              · exact hdt
              · rw [List.getElem?_set_ne (by omega)]; exact hdt
            ml_lets; ml_jnz; refine ⟨fun hok_t => ?_, fun hok_f => ?_⟩
            · have hok_d : ok_d = true := by c0_cond hok_t; exact hok_t
              have hmk2_set : mk2.toNat < cur_d.core.tmp.length := hmk2_tl
              ml_st md_n, hmd_n := c0_store_full_tmp (s := m8MinLitDfsState cur_d mrk_n wsort_n
                mclr_n mcl_n mcf_n ticks_n) (i := mk2) 0xFFFFFFFF#32 hmk2_set hm_dn
              have hmd_n' : (FullMem c cur_n ⋆ R) md_n := by
                dsimp only [cur_n, m8BlkState, m8ShrinkBlkBoolState, m8MinLitDfsState,
                  tmp_n] at hmd_n ⊢
                rw [hok_d]; simp only [↓reduceIte] at hmd_n ⊢; exact hmd_n
              exact hJnext () md_n ⟨mrk_n, tmp_n, mclr_n, wsort_n, mcl_n, mcf_n, ticks_n,
                hinv_n, hnt, hmd_n'⟩
            · have hok_d : ok_d = false := by c0_cond hok_f; exact hok_f
              have hmd_n' : (FullMem c cur_n ⋆ R) m_dn := by
                dsimp only [cur_n, m8BlkState, m8ShrinkBlkBoolState, m8MinLitDfsState,
                  tmp_n] at hm_dn ⊢
                rw [hok_d]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hm_dn
              exact hJnext () m_dn ⟨mrk_n, tmp_n, mclr_n, wsort_n, mcl_n, mcf_n, ticks_n,
                hinv_n, hnt, hmd_n'⟩
          · c0_cond hmk2_done
            exact hJ_bd () md ⟨mrk_d, tmp_d, mclr_d, sstk_s, wsort_d, mcl_d, mcf_d, ticks_d,
              hd, hm_d⟩
      · have h2lt : end_b.toNat - beg.toNat = 1 := by
          c0_cond hlt2
          have h1 := beg.isLt; have h2 := end_b.isLt
          have hmod : (2 ^ 64 - beg.toNat + end_b.toNat) % 2 ^ 64 = end_b.toNat - beg.toNat := by
            rw [show 2 ^ 64 - beg.toNat + end_b.toNat = 2 ^ 64 + (end_b.toNat - beg.toNat)
                  from by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          have h2v : (2 : BitVec 64).toNat = 2 := rfl
          rw [hmod, h2v] at hlt2; omega
        have hinv_next : M8BlkLoopInv c F0 s s_c1 tlen end_b.toNat cur :=
          { hb with
            tail_eq := fun k hk1 hk2 => hb.tail_eq k (by omega) hk2
            beg_bnd := fun _ hend_lt => by
              have := (hblk_in (end_b.toNat - 1) (by omega) (by omega)).1
              have := hstep_end hend_lt; omega }
        exact hJ_nb () mb ⟨mrk_b, tmp_b, mclr_b, sstk_b, wsort_b, mcl_b, mcf_b, ticks_b,
          hinv_next, hm_b⟩
    rintro J_ex hJ_ex; ml_lets; ml_jnz; refine ⟨fun hlt_tl => ?_, fun hge_tl => ?_⟩
    · have hend_x : end_b.toNat < tlen := by
        rw [BitVec.ult, decide_eq_true_eq, htlen_eq] at hlt_tl; exact hlt_tl
      have hend_arr : end_b.toNat < cur.core.tmp.length := by
        dsimp only [cur]; rw [hb.core.1.core_ok.tmp_len_arr]; omega
      ml_ld c0_load_full_tmp (s := cur) (i := end_b) hend_arr hm_b
      let lit_e := cur.core.tmp[end_b.toNat]'hend_arr
      have het1 : cur.core.tmp[end_b.toNat]? = s_c1.core.tmp[end_b.toNat]? :=
        hb.tail_eq end_b.toNat (by omega) hend_x
      have hne_e : cur.core.tmp[end_b.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [het1]; exact hc1_ne end_b.toNat hend_x
      have hr_e := hb.rem_mrk end_b.toNat hend_x hne_e
      rw [List.getElem?_eq_getElem hend_arr, Option.getD_some] at hr_e
      have hev_lt : (lit_e >>> 1).toNat < s.core.cur_vars := by
        rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hr_e.1
      have helvl_l : ((lit_e >>> 1).setWidth 64).toNat < cur.core.lvl.length := by
        rw [hb.core.1.core_ok.lvl_len, bv_c0_zext32_64]; omega
      ml_lets; ml_ld c0_load_full_lvl (s := cur) (i := (lit_e >>> 1).setWidth 64) helvl_l hm_b
      let elvl := cur.core.lvl[((lit_e >>> 1).setWidth 64).toNat]'helvl_l
      have hlit_e_eq : lit_e.toNat = (s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat := by
        dsimp only [lit_e]; rw [← het1, List.getElem?_eq_getElem hend_arr, Option.getD_some]
      have helv_nat : elvl.toNat =
          (s.core.lvl[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        dsimp only [elvl]
        rw [show cur.core.lvl[((lit_e >>> 1).setWidth 64).toNat]'helvl_l =
              (some (cur.core.lvl[((lit_e >>> 1).setWidth 64).toNat]'helvl_l)).getD 0#32 from rfl,
          ← List.getElem?_eq_getElem helvl_l, bv_c0_zext32_64, bv32_lshr_1, hb.lvl_eq, hlit_e_eq]
      ml_lets; ml_jnz; refine ⟨fun heq_lv => ?_, fun hne_lv => ?_⟩
      · have helv_eq : elvl.toNat = blvl.toNat := by
          c0_cond heq_lv; exact congrArg BitVec.toNat heq_lv
        ml_ld c0_load_full_tmp (s := cur) (i := end_b) hend_arr hm_b
        have hetp_l : ((lit_e >>> 1).setWidth 64).toNat < cur.core.trail_pos.length := by
          rw [hbt_len, bv_c0_zext32_64]; omega
        ml_lets
        ml_ld c0_load_full_trail_pos (s := cur) (i := (lit_e >>> 1).setWidth 64) hetp_l hm_b
        let tpe := cur.core.trail_pos[((lit_e >>> 1).setWidth 64).toNat]'hetp_l
        have htpe_nat : (tpe.setWidth 64).toNat =
            (s.core.trail_pos[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD
              0#32).toNat := by
          rw [bv_c0_zext32_64]; dsimp only [tpe]
          rw [show cur.core.trail_pos[((lit_e >>> 1).setWidth 64).toNat]'hetp_l =
                (some (cur.core.trail_pos[((lit_e >>> 1).setWidth 64).toNat]'hetp_l)).getD 0#32
                from rfl,
            ← List.getElem?_eq_getElem hetp_l, bv_c0_zext32_64, bv32_lshr_1, hb.tpos_eq, hlit_e_eq]
        have hend1 : (end_b + 1).toNat = end_b.toNat + 1 := min_bv64_add1 (by omega)
        ml_lets
        refine wp_join_group (ts := [i64]) (fun (m_tr', ()) mw' =>
            mw' = mb ∧ max_tr.toNat ≤ m_tr'.toNat ∧
            (s.core.trail_pos[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              m_tr'.toNat)
          (fun _ ⟨m_tr', ⟨⟩⟩ mw' ⟨hmw_eq, hmt1, hmt2⟩ => by
            subst mw'; rw [Blocks.get_here]; ml_lets
            exact hJs_1 (tlen - (end_b + 1).toNat) (m_tr', end_b + 1, ()) mb (by omega)
              ⟨by rw [hend1], rfl, by rw [hend1]; omega, by rw [hend1]; exact hend_x,
                fun k hk1 hk2 => by
                  rw [hend1] at hk2; by_cases hke : k = end_b.toNat
                  · subst k; exact ⟨helv_nat ▸ helv_eq, hmt2⟩
                  · have hi := hblk_in k hk1 (by omega); exact ⟨hi.1, le_trans hi.2 hmt1⟩⟩) ?_
        rintro Jtp hJtp; ml_lets; ml_jnz; refine ⟨fun hgt => ?_, fun hle => ?_⟩
        · c0_cond hgt
          exact hJtp (tpe.setWidth 64, ()) mb ⟨rfl, le_of_lt hgt, by rw [htpe_nat]; exact le_refl _⟩
        · have hle' : (tpe.setWidth 64).toNat ≤ max_tr.toNat := by
            c0_cond hle; dsimp only [tpe]
            simp only [bv_c0_zext32_64, bv32_lshr_1] at hle ⊢; omega
          exact hJtp (max_tr, ()) mb ⟨rfl, le_refl _, by rw [htpe_nat] at hle'; exact hle'⟩
      · have helv_ne : elvl.toNat ≠ blvl.toNat := by
          c0_cond hne_lv; intro heq; apply hne_lv; exact BitVec.eq_of_toNat_eq heq
        have hlt_b := hc1_sort beg.toNat end_b.toNat hbeg1 (le_of_lt hbeg_end) hend_x
        have hb0 := (hblk_in beg.toNat (le_refl _) hbeg_end).1
        exact hJ_ex () mb ⟨rfl, fun _ => by rw [← helv_nat]; omega⟩
    · exact hJ_ex () mb ⟨rfl, fun h => by
        rw [BitVec.ult, decide_eq_false_iff_not, htlen_eq] at hge_tl; omega⟩
  · c0_cond hge
    have hbeg_e : beg.toNat = tlen := by rw [htlen_eq] at hge; omega
    subst hbeg_e
    ml_lets
    refine m8_min_shrink_compact_loop_wp hb.core ht1 (by rw [hb.cv_eq]; exact ht_cv) htlen_eq
      (by rw [hb.zero_eq]; exact hc1_0ne)
      (fun k hk hne => by
        rw [hb.cv_eq, hb.vals_eq]; have hr := hb.rem_mrk k hk hne; exact ⟨hr.1, hr.2.1⟩)
      (fun k hk1 hk2 hne => by
        rw [hb.lvl_eq, hb.clvl_eq, hb.post_lvls k hk1 hk2 hne]; exact hc1_lvls k hk1 hk2)
      (fun i j hi1 hij hj hni hnj => by
        rw [hb.lvl_eq, hb.post_lvls i hi1 (lt_of_le_of_lt hij hj) hni,
          hb.post_lvls j (by omega) hj hnj]
        exact hc1_sort i j hi1 hij hj) hm_b
      (fun keep_bv tmp_c mc htc_len hkp1 hkp_tl htc0 htake_eq htc_ne htc_ok htc_sort hm_c => by
        ml_ld load_full_mark_ptr (s := { cur with core := { cur.core with tmp := tmp_c } }) hm_c
        ml_lets
        have hcv_c : ({ cur with core := { cur.core with tmp := tmp_c } } :
            FullState).core.cur_vars =
            s.core.cur_vars := hb.cv_eq
        have hcore_c : FullOtfsCoreInv c F0 { cur with core := { cur.core with tmp := tmp_c } } :=
          m8CoreInv_blk hb.core htc_len hb.core.1.core_ok.mrk_len
            hb.core.1.core_ok.min_clr_len_arr hb.core.1.core_ok.min_clr_len_le
            hb.core.1.scratch_ok.shrink_stk_len hb.core.1.scratch_ok.wsort_len
        have hmin_c : FullMinMarkInv ({ cur with core := { cur.core with tmp := tmp_c } } :
            FullState).core
            (((tmp_c.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
          have hmf := m8ListFilterNeEqSelf (k := keep_bv.toNat)
            (by rw [htc_len]; exact le_trans hkp_tl (le_trans ht_cv hcv)) htc_ne
          have hma : ((tmp_c.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat =
              ((cur.core.tmp.take beg.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
            rw [hmf, htake_eq]
          exact ⟨fun v hv => hb.min_inv.mrk_dom v hv,
            fun hnf w hw h6 => hb.min_inv.clr_cov hnf w hw h6,
            fun idx hi h2 => by rw [hma]; exact hb.min_inv.rem_sound idx hi h2⟩
        rw [show BitVec.ofNat 64 s.core.cur_vars =
            BitVec.ofNat 64
              ({ cur with core := { cur.core with tmp := tmp_c } } : FullState).core.cur_vars
            from congrArg (BitVec.ofNat 64) hcv_c.symm]
        exact m8_min_shrink_clean_wp hcore_c
          (by rw [hcv_c]; exact le_trans hkp_tl ht_cv) (by rw [htlen_eq]; exact hkp_tl)
          (by rw [htlen_eq, hcv_c]; exact ht_cv) hmin_c
          (fun v hv => hb.no8 v (by rw [← hcv_c]; exact hv)) hm_c
          fun mrk_f mf hml_f hab_f hmc_f hm_f => by
            have htc0' : tmp_c[0]? = s.core.tmp[0]? := htc0.trans (hb.zero_eq.trans hc1_0eq)
            exact hpost tmp_c keep_bv.toNat mrk_f mclr_b sstk_b wsort_b 0 0#64
              (s_c1.scratch.learned_lits + keep_bv)
              (s_c1.scratch.min_removed + (tlen_bv - keep_bv)) ticks_b mf
              htc_len hml_f hb.core.1.core_ok.min_clr_len_arr (Nat.zero_le _)
              hb.core.1.scratch_ok.shrink_stk_len hb.core.1.scratch_ok.wsort_len
              (fun v hv => (hab_f v (by rw [hcv_c]; exact hv)).trans (hb.mrk_above v hv))
              hmc_f hkp1 (le_trans hkp_tl ht_tl) htc0'
              (fun hnd0 hne0 => by
                have htake_div : (tmp_c.take keep_bv.toNat).map (fun x => x.toNat / 2) =
                    ((cur.core.tmp.take beg.toNat).filter (· ≠ 0xFFFFFFFF#32)).map
                      (fun x => x.toNat / 2) := by
                  have h1 := congrArg (List.map (· / 2)) htake_eq
                  simpa only [List.map_map, Function.comp_def] using h1
                rw [htake_div]; exact hb.nodup hnd0 hne0)
              (fun j hj1 hj2 => by
                have ho := htc_ok j hj1 hj2
                rw [hb.cv_eq, hb.vals_eq, hb.lvl_eq, hb.clvl_eq] at ho
                exact ho)
              (fun F_cur hw hEnt0 => by
                obtain ⟨hwc, hec⟩ := hb.entails F_cur hw hEnt0
                rw [← htake_eq] at hec
                exact ⟨m8Witness_minTmp hwc, hec⟩)
              (by dsimp only [m8MinShrinkRes, m8MinShrinkState]; exact hm_f))

/-- Level-only `sort_tmp` specification for Step 7 (`≤ 32` threshold, no tie-break needed). -/
def step7SortTmpSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.tmp_len ≤ c.max_vars ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' wsort' m',
      let s' : FullState :=
        { core := { s.core with tmp := tmp' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 32 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      Full.FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem step7SortTmpSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : step7SortTmpSpec xs m Q X) : step7SortTmpSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step7SortTmpSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (htl : s.core.tmp_len ≤ c.max_vars)
    (hbd : ∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ tmp' wsort' m',
      let s' : FullState :=
        { core := { s.core with tmp := tmp' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 32 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      Full.FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m') :
    step7SortTmpSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, htl, hbd, hm, hQ⟩

private theorem full_min_shrink_m6_m8_wp_core (Γ : Env)
    (hStCore : ∀ {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
      {Q : Post []} {X : XPost},
      s.LengthsOk c → s.core.tmp_len ≤ c.max_vars →
      (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) →
      (FullMem c s ⋆ R) m →
      (∀ tmp' wsort' m',
        let s' : FullState :=
          { core := { s.core with tmp := tmp' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → tmp'.length = c.max_vars →
        (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
        (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
        (∀ j, 1 ≤ j → j < s.core.tmp_len →
          ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
        (∀ i, 1 ≤ i → i < s.core.tmp_len →
          ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
        (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
          (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
        (FullMem c s' ⋆ R) m' → Q () m') →
      Γ "full_sort_tmp" [i64] [] (c.hdr, ()) m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, m8MinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_m6_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur, s, R, ha, hlen0, hw0, hlm0, htl1, htl_cv, hnd0, hEnt0,
    htmp_vals, htmp_lvls, h0_lvl, hm, hQ⟩ := m8MinShrinkSpec_elim hspec
  obtain rfl : h = c.hdr := ha
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hlen0.core_ok.cur_vars_le
  have hmc0 : FullMarksClear s := hlm0.toFullMarksClear hlen0
  rw [Func.wp, m8_min_shrink_m6_body_eq]; ml_lets
  ml_ld load_full_cur_vars hm; ml_lets
  ml_ld load_full_tmp_len hm; ml_lets
  ml_ld load_full_conflicts hm; ml_lets
  ml_st m0, hm0 := store_full_conflicts (s.scratch.conflicts + 1) hm
  let s0 : FullState :=
    { s with scratch := { s.scratch with conflicts := s.scratch.conflicts + 1 } }
  have hs0_core : FullOtfsCoreInv c F0 s0 :=
    ⟨⟨hlen0.core_ok, m8MinShrinkScratchOk hlen0.scratch_ok hlen0.scratch_ok.shrink_stk_len
      hlen0.scratch_ok.wsort_len⟩, F_cur, hw0⟩
  refine wp_join_group (ts := []) (fun () mq => s.core.tmp_len = 1 ∧ mq = m0)
    (fun _ ⟨⟩ mq ⟨htl_eq1, rfl⟩ => by
      rw [Blocks.get_here]
      ml_ld load_full_learned_lits (s := s0) hm0; ml_lets
      ml_st m_e, hm_e := store_full_learned_lits (s := s0)
        (s0.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len) hm0
      rw [wp]
      have hce_eq :
          m8MinShrinkState s s.core.tmp s.core.tmp_len s.core.mrk s.core.min_clr
            s.scratch.shrink_stk s.scratch.wsort s.core.min_clr_len s.core.min_clr_full
            (s.scratch.conflicts + 1)
            (s.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len) s.scratch.min_removed
            s.scratch.search_ticks =
          { s0 with scratch := { s0.scratch with
            learned_lits := s0.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len } } := rfl
      exact hQ s.core.tmp s.core.tmp_len s.core.mrk s.core.min_clr
        s.scratch.shrink_stk s.scratch.wsort s.core.min_clr_len s.core.min_clr_full
        (s.scratch.conflicts + 1)
        (s.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len) s.scratch.min_removed
        s.scratch.search_ticks m_e
        ⟨hlen0.core_ok, m8MinShrinkScratchOk hlen0.scratch_ok hlen0.scratch_ok.shrink_stk_len
          hlen0.scratch_ok.wsort_len⟩
        hw0 hlm0 htl1 (le_refl _) rfl hnd0 (fun j hj1 hj2 => by omega) hEnt0 (hce_eq ▸ hm_e)) ?_
  rintro J_early hJ_early; ml_lets; ml_jnz
  refine ⟨fun hle1 => ?_, fun hgt1 => ?_⟩
  · have htl_eq1 : s.core.tmp_len = 1 := by c0_cond hle1; bv_omega
    ml_lets; exact hJ_early () m0 ⟨htl_eq1, rfl⟩
  · c0_cond hgt1; have h2lt : 2 ≤ s.core.tmp_len := by bv_omega
    ml_lets; ml_jnz; refine ⟨fun hoob => by exfalso; c0_cond hoob; bv_omega, fun _ => ?_⟩
    ml_lets; apply wp_call_of_spec; dsimp only [vals, Arg.val]
    refine hStCore hs0_core.1 (by dsimp only [s0]; omega)
      (fun k _ hk2 => by dsimp only [s0] at hk2 ⊢; have := (htmp_vals k (by omega)).1; omega)
      hm0
      (fun tmp1 wsort1 m1 hlen1 ht1_len ht1_perm ht1_0 ht1_r ht1_l ht1_sort hm1 => ?_)
    obtain ⟨hkeep_eq, hEnt1, htmp1_vals, htmp1_lvls⟩ := m8MinShrinkPostSort
      htl1 htl_cv hcv hlen0.core_ok.tmp_len_arr htmp_vals htmp_lvls ht1_len ht1_0 ht1_r ht1_l
    let s1 : FullState :=
      { s0 with core := { s0.core with tmp := tmp1 }
                scratch := { s0.scratch with wsort := wsort1 } }
    ml_ld load_full_tmp_lits_ptr (s := s1) hm1; ml_ld load_full_level_ptr (s := s1) hm1
    ml_ld load_full_trail_pos_ptr (s := s1) hm1
    ml_st m2, hm2 := store_full_min_clr_len (s := s1) 0 (Nat.zero_lt_succ _) hm1
    ml_st m3, hm3 :=
      store_full_min_clr_full (s := { s1 with core := { s1.core with min_clr_len := 0 } }) 0#64 hm2
    let s2 : FullState :=
      { s1 with core := { s1.core with min_clr_len := 0, min_clr_full := 0#64 } }
    have hs2_core : FullOtfsCoreInv c F0 s2 := fullOtfsCoreInv_with_min_tmp hs0_core ht1_len
      hlen0.core_ok.tmp_len_le hlen0.core_ok.mrk_len hlen0.core_ok.min_stk_len
      hlen0.core_ok.min_clr_len_arr (Nat.zero_le _) hlen1.scratch_ok
    let keep0 := ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    have hmin2_init : FullMinMarkInv s2.core keep0 := fullMinMarkInv_init hs2_core hmc0 keep0
    clear hm hm0 hm1 m1 hm2 m2 hs0_core
    have htl_bv : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len :=
      Nat.mod_eq_of_lt (by omega)
    dsimp only [m8MinMarkInitExpr]
    refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) mi =>
        n = s.core.tmp_len - i_bv.toNat ∧ i_bv.toNat ≤ s.core.tmp_len ∧
        ∃ (mrk_i : List (BitVec 8)) (mclr_i : List (BitVec 32)) (mcl_i : Nat) (mcf_i : BitVec 64),
          let st_i := m8BlkState s2 tmp1 mrk_i mclr_i s2.scratch.shrink_stk wsort1 mcl_i mcf_i
            s2.scratch.search_ticks
          mrk_i.length = c.max_vars ∧ mclr_i.length = c.max_vars ∧ mcl_i ≤ c.max_vars ∧
          (∀ v, s.core.cur_vars ≤ v → mrk_i[v]? = s.core.mrk[v]?) ∧
          (∀ v < s.core.cur_vars, (mrk_i[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
          FullMinMarkInv st_i.core keep0 ∧
          (∀ k < i_bv.toNat, (mrk_i[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
          (FullMem c st_i ⋆ R) mi) ?_
      (fun Jinit hJinit => by
        have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
        ml_lets; exact hJinit s.core.tmp_len (0#64, ()) m3
          ⟨by rw [h0v]; exact Nat.sub_zero _, by rw [h0v]; exact Nat.zero_le _, s2.core.mrk,
            s2.core.min_clr, s2.core.min_clr_len, s2.core.min_clr_full, hlen0.core_ok.mrk_len,
            hlen0.core_ok.min_clr_len_arr, Nat.zero_le _, fun _ _ => rfl, fun v hv => by
              change (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8
              rw [hmc0 v hv]; rfl,
            hmin2_init, fun _ h => by rw [h0v] at h; omega, hm3⟩)
    rintro Jinit n ⟨i_bv, ⟨⟩⟩ mi hJinit
      ⟨rfl, hi_le, mrk_i, mclr_i, mcl_i, mcf_i, hmr_len, hmcl_len, hmcl_le,
        hab_i, hno8_i, hmin_i, hmarked_i, hm_i⟩
    let st_i := m8BlkState s2 tmp1 mrk_i mclr_i s2.scratch.shrink_stk wsort1 mcl_i mcf_i
      s2.scratch.search_ticks
    have hcore_i := m8CoreInv_blk hs2_core ht1_len hmr_len hmcl_len hmcl_le
      hlen1.scratch_ok.shrink_stk_len hlen1.scratch_ok.wsort_len
      (mcf1 := mcf_i) (ticks1 := s2.scratch.search_ticks)
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt_i => ?_, fun hge_i => ?_⟩
    · have hi_lt : i_bv.toNat < s.core.tmp_len := by
        rw [BitVec.ult, decide_eq_true_eq, htl_bv] at hlt_i; exact hlt_i
      have hi_arr : i_bv.toNat < st_i.core.tmp.length := by
        dsimp only [st_i, m8BlkState, m8ShrinkBlkBoolState]; rw [ht1_len]; omega
      ml_ld c0_load_full_tmp (s := st_i) (i := i_bv) hi_arr hm_i
      let lit_i := st_i.core.tmp[i_bv.toNat]'hi_arr
      have hl_get : lit_i.toNat = (tmp1[i_bv.toNat]?.getD 0#32).toNat := by
        dsimp only [lit_i]
        rw [show st_i.core.tmp[i_bv.toNat]'hi_arr =
              (some (st_i.core.tmp[i_bv.toNat]'hi_arr)).getD 0#32 from rfl,
          ← List.getElem?_eq_getElem hi_arr]
      have hli_v := htmp1_vals i_bv.toNat hi_lt
      have hli_lit_lt : lit_i.toNat < 2 * st_i.core.cur_vars := by
        rw [hl_get]; exact hli_v.2.1
      have hli_lt : (lit_i >>> 1).toNat < s.core.cur_vars := by
        rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hli_lit_lt
      ml_lets; apply wp_call_of_spec; apply hMm; refine m8_fullMinMarkSpec_of_specs ?_
      refine fullMinMarkSpec_step hcore_i.1 hm_i (lit_i >>> 1) hli_lt
        ((2 : BitVec 32).setWidth 8) fun mn hmn => ?_
      have h2eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
      rw [h2eq] at hmn
      let st_n := fullMinMarkStepState st_i (lit_i >>> 1).toNat 2#8
      have hlen_n := fullMinMarkStepState_lengths hcore_i.1 (lit_i >>> 1).toNat 2#8
      have hno8_v : (st_i.core.mrk[(lit_i >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8 :=
        hno8_i _ hli_lt
      have hab_n := fullMinMarkStepState_mrk_above (s := st_i) hli_lt 2#8
      obtain ⟨h8_n, hmono_n⟩ := fullMinMarkStepState_bit8_mono2 hcore_i.1 hli_lt (Or.inl rfl) hno8_v
      have hli_mem : lit_i.toNat ∈ keep0 := by
        rw [hl_get]; exact hli_v.2.2.2
      have hli_val : st_i.core.vals[lit_i.toNat]?.getD 0#8 = 0xFF#8 := by
        rw [hl_get]; exact hli_v.2.2.1
      have hmin_n : FullMinMarkInv st_n.core keep0 := by
        have h1 := fullMinMarkInv_step_keep hcore_i hmin_i hli_lit_lt hli_mem hli_val
          (by simpa only [bv32_lshr_1] using hno8_v)
        simpa only [st_n, bv32_lshr_1] using h1
      have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := min_bv64_add1 (by omega)
      have hm_n' : (FullMem c (m8BlkState s2 tmp1 st_n.core.mrk st_n.core.min_clr
          s2.scratch.shrink_stk wsort1 st_n.core.min_clr_len st_n.core.min_clr_full
          s2.scratch.search_ticks) ⋆ R) mn := by
        dsimp only [st_n] at hmn ⊢; rw [m8Blk_step]; exact hmn
      have hmin_n' : FullMinMarkInv (m8BlkState s2 tmp1 st_n.core.mrk st_n.core.min_clr
          s2.scratch.shrink_stk wsort1 st_n.core.min_clr_len st_n.core.min_clr_full
          s2.scratch.search_ticks).core keep0 := by
        have hc_f : ¬ st_i.core.cur_vars ≤ (lit_i >>> 1).toNat := Nat.not_le.mpr hli_lt
        dsimp only [st_n, fullMinMarkStepState, fullMinMarkStepCore, st_i, m8BlkState,
          m8ShrinkBlkBoolState] at hmin_n ⊢
        have hc_f' : ¬ s2.core.cur_vars ≤ (lit_i >>> 1).toNat := hc_f
        simp only [eq_false hc_f'] at hmin_n ⊢
        by_cases hcond : (mrk_i[(lit_i >>> 1).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8
        · simp only [false_or, eq_true hcond, ↓reduceIte] at hmin_n ⊢; exact hmin_n
        · simp only [false_or, eq_false hcond, ↓reduceIte] at hmin_n ⊢
          dsimp only [fullMinMarkCore] at hmin_n ⊢; exact hmin_n
      refine hJinit (s.core.tmp_len - (i_bv + 1).toNat) (i_bv + 1, ()) mn (by omega)
        ⟨by rw [hi1], by rw [hi1]; omega, st_n.core.mrk, st_n.core.min_clr, st_n.core.min_clr_len,
          st_n.core.min_clr_full, hlen_n.core_ok.mrk_len, hlen_n.core_ok.min_clr_len_arr,
          hlen_n.core_ok.min_clr_len_le, fun v hv => (hab_n v hv).trans (hab_i v hv),
          fun v hv => by rw [h8_n v hv]; exact hno8_i v hv, hmin_n', fun k hk => ?_, hm_n'⟩
      rw [hi1] at hk; by_cases hki : k = i_bv.toNat
      · subst k
        dsimp only [st_n, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore]
        split
        · rename_i hc
          simpa only [bv32_lshr_1, hl_get] using hc.resolve_left (Nat.not_le.mpr hli_lt)
        · dsimp only [lit_i, st_i, m8BlkState, m8ShrinkBlkBoolState]
          rw [bv32_lshr_1, hl_get,
            List.getElem?_set_self (by rw [hmr_len, ← hl_get, ← bv32_lshr_1]; omega),
            Option.getD_some]
          exact bv8_and2_of_or2 _
      · exact hmono_n _ (Nat.div_lt_of_lt_mul (htmp1_vals k (by omega)).2.1)
          (hmarked_i k (by omega))
    · have hi_eq : i_bv.toNat = s.core.tmp_len := by
        rw [BitVec.ult, decide_eq_false_iff_not, htl_bv] at hge_i; omega
      rw [hi_eq] at hmarked_i
      have hc1_inv : M8BlkLoopInv c F0 s st_i s.core.tmp_len 1 st_i :=
        ⟨hcore_i, hmin_i,
          fun F_cur' hw' hEnt' =>
            ⟨m8Witness_shrinkBlk (sstk1 := s2.scratch.shrink_stk) (wsort1 := wsort1)
              (ticks1 := s2.scratch.search_ticks) hw', hEnt1 F_cur' hEnt'⟩,
          fun hnd _ => by
            have hmf := m8ListFilterNeEqSelf (by rw [ht1_len]; exact le_trans htl_cv hcv)
              (fun j hj => (htmp1_vals j hj).1)
            change (((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map
              fun x => x.toNat / 2).Nodup
            rw [hmf]
            exact (ht1_perm.map (fun x => x.toNat / 2)).nodup_iff.mpr hnd,
          hab_i, hno8_i, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl,
          fun h _ => by omega,
          fun k hk _ => ⟨(htmp1_vals k hk).2.1, (htmp1_vals k hk).2.2.1, hmarked_i k hk⟩,
          fun _ _ _ _ => rfl⟩
      refine m8_min_shrink_blk_loop_wp hDfs hSb htl_bv htl1 htl_cv (le_refl _) hc1_inv
        (ht1_0 (Nat.lt_of_lt_of_le Nat.zero_lt_one htl1)) (htmp1_vals 0 htl1).1
        (by change (s.core.lvl[(tmp1[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level
            rw [ht1_0 (Nat.lt_of_lt_of_le Nat.zero_lt_one htl1)]; exact h0_lvl)
        (fun k hk => (htmp1_vals k hk).1) htmp1_lvls ht1_sort hm_i ?_
      intro tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' llits' mrem' ticks' mf _s'
        htmp'_len hmrk'_len hmclr'_len hmcl'_le hsstk'_len hws'_len hab' hmc'
        htl'_1 htl'_le ht'_0 hnd'_fn hlv'_fn hEnt'_fn hm'
      have hnd_out : ((tmp'.take tl').map fun x => x.toNat / 2).Nodup :=
        hnd'_fn hnd0 fun k hk1 hk2 => by
          have hl := (htmp_lvls k hk1 hk2).2
          change (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ _
          rw [h0_lvl]; omega
      obtain ⟨hw', hEnt'⟩ := hEnt'_fn F_cur hw0 hEnt0
      have hlen' : FullState.LengthsOk c (m8MinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' mcl'
          mcf' (s.scratch.conflicts + 1) llits' mrem' ticks') :=
        ⟨{ hlen0.core_ok with
            tmp_len_arr := htmp'_len, tmp_len_le := le_trans htl'_le hlen0.core_ok.tmp_len_le,
            mrk_len := hmrk'_len, min_clr_len_arr := hmclr'_len, min_clr_len_le := hmcl'_le },
          m8MinShrinkScratchOk hlen0.scratch_ok hsstk'_len hws'_len⟩
      exact hQ tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' (s.scratch.conflicts + 1) llits' mrem'
        ticks' mf hlen' hw' (m8_mrk_above_zero hlm0 rfl hmc' hab' rfl)
        htl'_1 htl'_le ht'_0 hnd_out hlv'_fn hEnt' hm'

/-- `Func.wp` soundness theorem for `full_min_shrink_m6` (`m8MinShrinkSpec`). -/
theorem full_min_shrink_m6_m8_wp (Γ : Env)
    (hSt : ∀ args m Q X, m7SortTmpSpec args m Q X →
      Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, m8MinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_m6_body args m Q X :=
  full_min_shrink_m6_m8_wp_core Γ
    (fun {_c _s _R _m _Q _X} hlen htl hbd hm hcont =>
      hSt _ _ _ _ (m7SortTmpSpec_of hlen htl hbd hm
        fun tmp' wsort' m' hlen' ht' _ hperm h0 hr hl _ hlvl _ hm' =>
          hcont tmp' wsort' m' hlen' ht' hperm h0 hr hl hlvl hm'))
    hMm hDfs hSb

/-- Level-only `step7SortTmpSpec` soundness theorem for `full_min_shrink_m6`. -/
theorem full_min_shrink_m6_m8_wp_lvl (Γ : Env)
    (hSt : ∀ args m Q X, step7SortTmpSpec args m Q X →
      Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m8MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m8" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m8" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, m8MinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_m6_body args m Q X :=
  full_min_shrink_m6_m8_wp_core Γ
    (fun {_c _s _R _m _Q _X} hlen htl hbd hm hcont =>
      hSt _ _ _ _ ⟨_, _, _, rfl, hlen, htl, hbd, hm,
        fun tmp' wsort' m' hlen' ht' _ hperm h0 hr hl hlvl _ hm' =>
          hcont tmp' wsort' m' hlen' ht' hperm h0 hr hl hlvl hm'⟩)
    hMm hDfs hSb
