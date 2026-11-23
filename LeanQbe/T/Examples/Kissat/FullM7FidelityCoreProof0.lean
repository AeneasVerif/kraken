module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullM7SpecBridges1
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof2a
import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof2b
import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof0
import LeanQbe.T.Examples.Kissat.FullMinLemmas3
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.SolverArena
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `FullM7Fidelity` Core Proofs — Part 0 (`MinShrink`)

M1-clean UNSAT-only proofs (`public section`, `0` `@[expose]`, `0` `@[local]`, `0` `import all`,
`XPost := False`, `0` SAT proofs) for `full_min_shrink_fid_wp`: certifies canonical
`FullM7SpecBridges.m7MinShrinkSpec` (`shrink=3`, skips Pass 1 DFS so `mrk | 4` never
cross-contaminates `full_shrink_lower_m6`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat

/-! ## 1. `full_min_shrink_fid` (`FullM7SpecBridges.m7MinShrinkSpec`) -/

section MinShrinkProof

open LeanQbe.T.Examples.Kissat.Full hiding
  FullMinMarkInv fullMinMarkCore fullMinMarkState fullMinMarkSpec
  fullMinLitSpec fullShrinkLowerSpec fullShrinkBlkSpec fullMinShrinkSpec
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
open LeanQbe.T.Examples.Kissat.FullM7SpecBridges

private theorem fidToSpecsMinInv {k : FullCoreState} {keep : List Nat}
    (h : Full.FullMinMarkInv k keep) : FullMinMarkInv k keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

private theorem fidToFullMinInv {k : FullCoreState} {keep : List Nat}
    (h : FullMinMarkInv k keep) : Full.FullMinMarkInv k keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

private theorem fidSpecsMinMarkSpecOfFull {args m Q X}
    (h : fullMinMarkSpec args m Q X) : Full.fullMinMarkSpec args m Q X := by
  rcases args with ⟨h0, v, tag, ⟨⟩⟩
  rcases h with ⟨c, s, R, rfl, hlen, hm, hrest⟩
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  dsimp only at hrest ⊢
  split
  · simpa only [↓reduceIte, ite_eq_left ‹_›] using hrest
  · rename_i hneg
    simp only [ite_eq_right hneg] at hrest ⊢
    intro m' hm'
    dsimp only [Full.fullMinMarkState, Full.fullMinMarkCore] at hm'
    by_cases hcz : s.core.mrk[v.toNat]?.getD 0#8 = 0#8
    · by_cases hlt : s.core.min_clr_len < s.core.cur_vars
      · simp only [hcz, hlt, ↓reduceIte, not_true_eq_false, and_self, and_false,
          bv_ofNat_toNat_eq] at hrest hm'
        exact hrest m' hm'
      · simp only [hcz, hlt, ↓reduceIte, not_false_eq_true, and_self, and_false] at hrest hm'
        exact hrest m' hm'
    · simp only [hcz, ↓reduceIte, ne_eq, not_false_eq_true, false_and] at hrest hm'
      exact hrest m' hm'

private theorem fidListTakeSuccSet {α : Type _} {xs : List α} {i : Nat} (v : α)
    (hi : i < xs.length) : (xs.set i v).take (i + 1) = xs.take i ++ [v] := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_set, List.length_append, List.length_take]
    simp only [List.length_singleton]; omega
  · intro j hj1 _; rw [List.getElem_take]
    by_cases hjl : j < min i xs.length
    · rw [List.getElem_append_left (by rw [List.length_take]; exact hjl),
        List.getElem_take, List.getElem_set_ne (by omega)]
    · have hje : j = i := by rw [List.length_take, List.length_set] at hj1; omega
      subst hje
      rw [List.getElem_set_self (by rw [List.length_set]; exact hi),
        List.getElem_append_right (by rw [List.length_take]; omega)]
      simp [List.length_take_of_le (Nat.le_of_lt hi)]

private theorem fidListFilterNeEqSelf {xs : List (BitVec 32)} {k : Nat}
    (hk : k ≤ xs.length) (h : ∀ j < k, (xs[j]?.getD 0#32).toNat < 2 ^ 31) :
    (xs.take k).filter (· ≠ 0xFFFFFFFF#32) = xs.take k := by
  rw [List.filter_eq_self]; intro x hx; rw [List.mem_iff_getElem] at hx
  obtain ⟨j, hj, rfl⟩ := hx; rw [List.length_take] at hj
  have hlt := h j (by omega); rw [List.getElem_take]
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hlt
  rw [decide_eq_true_eq]; intro heq; have := congrArg BitVec.toNat heq
  have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega

private theorem fidMinMarkInvMrkNeZeroIff {k : FullCoreState} {keep : List Nat}
    (hmin : FullMinMarkInv k keep) (hno8 : ∀ v < k.cur_vars, (k.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    {v : Nat} (hv : v < k.cur_vars) :
    k.mrk[v]?.getD 0#8 ≠ 0#8 ↔ (k.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
  have hd := hmin.mrk_dom v hv; have h8 := hno8 v hv
  generalize k.mrk[v]?.getD 0#8 = b at hd h8 ⊢; revert b hd h8; decide

private theorem fidMinShrinkScratchOk {c : FullCfg} {sc : FullScratch} (hok : sc.LengthsOk c)
    {cf ll mr : BitVec 64} {sstk : List (BitVec 32)} (hsstk : sstk.length = c.max_vars) :
    ({ sc with conflicts := cf, learned_lits := ll, min_removed := mr,
               shrink_stk := sstk } : FullScratch).LengthsOk c :=
  { hok with shrink_stk_len := hsstk }

private theorem fidOtfsCoreInvWithMinTmpTl {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullOtfsCoreInv c F0 s) {tmp' : List (BitVec 32)} {tl' : Nat}
    {mrk' : List (BitVec 8)} {mstk' mclr' : List (BitVec 32)} {mcl' : Nat} {mcf' : BitVec 64}
    {sc' : FullScratch} (htmp : tmp'.length = c.max_vars) (htl : tl' ≤ s.core.cur_vars)
    (hmrk : mrk'.length = c.max_vars) (hmstk : mstk'.length = 2 * c.minDepth)
    (hmclr : mclr'.length = c.max_vars) (hmcl : mcl' ≤ c.max_vars) (hsc : sc'.LengthsOk c) :
    FullOtfsCoreInv c F0
      { core := { s.core with tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk',
                              min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }
        scratch := sc' } := by
  refine ⟨⟨{ h.1.core_ok with
      tmp_len_arr := htmp, tmp_len_le := le_trans htl h.1.core_ok.cur_vars_le, mrk_len := hmrk,
      min_stk_len := hmstk, min_clr_len_arr := hmclr, min_clr_len_le := hmcl }, hsc⟩, ?_⟩
  obtain ⟨F_cur, hw⟩ := h.2
  exact ⟨F_cur, fullOtfsWitness_with_min hw⟩

private theorem fidMinShrinkPostSort {c : FullCfg} {s : FullState}
    (htl1 : 1 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars) (hlen_tmp : s.core.tmp.length = c.max_vars)
    (htmp_vals : ∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (htmp_lvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    {tmp1 : List (BitVec 32)} (ht1_len : tmp1.length = c.max_vars)
    (ht1_0 : 0 < s.core.tmp_len → tmp1[0]? = s.core.tmp[0]?)
    (ht1_r : ∀ j, 1 ≤ j → j < s.core.tmp_len →
      ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp1[j]? = s.core.tmp[i]?)
    (ht1_l : ∀ i, 1 ≤ i → i < s.core.tmp_len →
      ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp1[j]?) :
    let keep0 := ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    keep0 = (tmp1.take s.core.tmp_len).map BitVec.toNat ∧
    (∀ F_cur, (cnfOfClauses F_cur).EntailsClause (cnfClause
        ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause keep0)) ∧
    (∀ k < s.core.tmp_len, let l := (tmp1[k]?.getD 0#32).toNat
      tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ l ∈ keep0) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlt1 : ∀ k < s.core.tmp_len, (tmp1[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp1[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
    intro k hk; cases k with
    | zero => rw [ht1_0 htl1]; exact htmp_vals 0 hk
    | succ k' =>
      obtain ⟨i, _, hi2, heq⟩ := ht1_r (k' + 1) (by omega) hk
      rw [heq]; exact htmp_vals i hi2
  have hkeep_eq : ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat =
      (tmp1.take s.core.tmp_len).map BitVec.toNat := by
    rw [fidListFilterNeEqSelf (by omega) fun j hj => by have := (hlt1 j hj).1; omega]
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
      have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    have hk_mem : (tmp1[k]?.getD 0#32).toNat ∈
        ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
      rw [hkeep_eq, List.mem_map]
      exact ⟨tmp1[k]'(by omega), List.mem_iff_getElem.mpr ⟨k, by rw [List.length_take]; omega,
        by rw [List.getElem_take]⟩, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
    exact ⟨hk_ne, hkv.1, hkv.2, hk_mem⟩

private theorem fidMinLitStepState {c : FullCfg} {F0 : CNF Nat} {s_orig cur : FullState}
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
    {ok : Bool} {mrk' : List (BitVec 8)} {mstk' mclr' : List (BitVec 32)}
    {mcl' : Nat} {mcf' : BitVec 64}
    (hlen' : (minLitState cur mrk' mstk' mclr' mcl' mcf').LengthsOk c)
    (hab' : ∀ v, cur.core.cur_vars ≤ v → mrk'[v]? = cur.core.mrk[v]?)
    (hmono2 : ∀ v < cur.core.cur_vars,
      (cur.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8 : ∀ v < cur.core.cur_vars,
      (mrk'[v]?.getD 0#8 &&& 8#8) = (cur.core.mrk[v]?.getD 0#8 &&& 8#8))
    (hmin' : FullMinMarkInv (minLitState cur mrk' mstk' mclr' mcl' mcf').core
      (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hok_true : ok = true →
      (∀ keep', (∀ l ∈ (((cur.core.tmp.take keepLen).filter
            (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep') →
        FullMinMarkInv (minLitState cur mrk' mstk' mclr' mcl' mcf').core keep') ∧
      FullMinMarkInv (fullMinMarkState (minLitState cur mrk' mstk' mclr' mcl' mcf')
          (root_lit.toNat / 2) 2#8).core
        (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) :
    let tmp_n := if ok then cur.core.tmp.set idx 0xFFFFFFFF#32 else cur.core.tmp
    let st_n : FullState := { cur with core := { cur.core with
      tmp := tmp_n, mrk := mrk', min_stk := mstk', min_clr := mclr',
      min_clr_len := mcl', min_clr_full := mcf' } }
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
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨fullOtfsCoreInv_with_min hcore hlen'.core_ok.mrk_len hlen'.core_ok.min_stk_len
        hlen'.core_ok.min_clr_len_arr hlen'.core_ok.min_clr_len_le,
      hmin', fun F_cur hw hEnt0 =>
        let ⟨hwc, hEc⟩ := hent F_cur hw hEnt0; ⟨fullOtfsWitness_with_min hwc, hEc⟩,
      hnd, fun v hv => (hab' v hv).trans (hab v hv),
      fun v hv => by rw [hbit8 v hv]; exact hno8 v hv,
      fun k hk hne => by
        have hrk := hrem k hk hne
        exact ⟨hrk.1, hrk.2.1,
          hmono2 ((cur.core.tmp[k]?.getD 0#32).toNat / 2) (by omega) hrk.2.2⟩,
      fun _ _ _ => trivial⟩
  | true =>
    simp only [↓reduceIte]; let tmp_n := cur.core.tmp.set idx 0xFFFFFFFF#32
    let st_base := minLitState cur mrk' mstk' mclr' mcl' mcf'
    let st_n : FullState := { st_base with core := { st_base.core with tmp := tmp_n } }
    have htl_n : tmp_n.length = c.max_vars := by
      dsimp only [tmp_n]; rw [List.length_set, hcore.1.core_ok.tmp_len_arr]
    have hcore_n : FullOtfsCoreInv c F0 st_n := fullOtfsCoreInv_with_min_tmp hcore htl_n
      hcore.1.core_ok.tmp_len_le hlen'.core_ok.mrk_len hlen'.core_ok.min_stk_len
      hlen'.core_ok.min_clr_len_arr hlen'.core_ok.min_clr_len_le hcore.1.scratch_ok
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
      have hwb : FullOtfsWitnessInv c F0 F_cur st_base.core := fullOtfsWitness_with_min hwc
      refine ⟨fullOtfsWitness_with_min hwc, fullMinMark_entails hwb hmin_base hEc fun l hl => ?_⟩
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

private def fidMinMarkInitExpr {V : Ty → Type} {C : List Ty → Type} (p orig_tlen pTmp : V i64)
    (cont : Expr V C []) : Expr V C [] :=
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
      cont) .nil)
    fun Js => .jump Js.fst (.imm 0, ())

private def fidMinCompactLoopExpr {V : Ty → Type} {C : List Ty → Type} (bound pTmp : V i64)
    (after : V i64 → Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64]]) (fun Js => .cons (fun p_32 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_32.snd.fst, .var bound, ())) fun p_33 =>
    .jnz (.var p_33.fst)
      (.group (sig := [[i64]]) (fun _ => .cons (fun p =>
         .let_ (op64 (.add i64) (.var p_32.snd.fst) (.imm 1)) fun p_34 =>
         .jump Js.fst (.var p.fst, .var p_34.fst, ())) .nil) fun Js =>
       .let_ (op64 (.mul i64) (.var p_32.snd.fst) (.imm 4)) fun p =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
       .load i32 (.var p.fst) fun ld =>
       .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var ld, .imm 4294967295, ())) fun p =>
       .jnz (.var p.fst)
         (.let_ (op64 (.mul i64) (.var p_32.fst) (.imm 4)) fun p =>
          .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
          .let_ (op64 (.mul i64) (.var p_32.snd.fst) (.imm 4)) fun p_34 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var p_34.fst)) fun p_35 =>
          .load i32 (.var p_35.fst) fun ld =>
          .store (.var ld) (.var p.fst)
            (.let_ (op64 (.add i64) (.var p_32.fst) (.imm 1)) fun p =>
             .jump Js.fst (.var p.fst, ())))
         (.jump Js.fst (.var p_32.fst, ())))
      (after p_32.fst)) .nil)
    fun Js => .jump Js.fst (.imm 1, .imm 1, ())

private def fidMinCleanExpr {V : Ty → Type} {C : List Ty → Type}
    (p cv orig_tlen pMark keep : V i64) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _ => .cons (fun _ =>
    .let_ (op64 (.add i64) (.var p) (.imm 272)) fun p_40 =>
    .store (t := i64) (.imm 0) (.var p_40.fst)
      (.let_ (op64 (.add i64) (.var p) (.imm 280)) fun p_41 =>
       .store (t := i64) (.imm 0) (.var p_41.fst)
         (.let_ (op64 (.add i64) (.var p) (.imm 192)) fun p_42 =>
          .store (.var keep) (.var p_42.fst)
            (.let_ (op64 (.add i64) (.var p) (.imm 352)) fun p_43 =>
             .load i64 (.var p_43.fst) fun ld =>
             .let_ (op64 (.sub i64) (.var orig_tlen) (.var keep)) fun p_44 =>
             .let_ (op64 (.add i64) (.var ld) (.var p_44.fst)) fun p_45 =>
             .let_ (op64 (.add i64) (.var p) (.imm 352)) fun p_46 =>
             .store (.var p_45.fst) (.var p_46.fst)
               (.let_ (op64 (.add i64) (.var p) (.imm 344)) fun p_47 =>
                .load i64 (.var p_47.fst) fun ld =>
                .let_ (op64 (.add i64) (.var ld) (.var keep)) fun p_48 =>
                .let_ (op64 (.add i64) (.var p) (.imm 344)) fun p =>
                .store (.var p_48.fst) (.var p.fst) (.ret ())))))) .nil)
    fun Js =>
    .let_ (op64 (.add i64) (.var p) (.imm 280)) fun p_39 =>
    .load i64 (.var p_39.fst) fun ld_10 =>
    .let_ (Op.mk (.cmp .ne i64 .bool rfl) (.var ld_10, .imm 0, ())) fun p_40 =>
    .jnz (.var p_40.fst)
      (.group (sig := [[i64]]) (fun Js_1 => .cons (fun p =>
        .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var cv, ())) fun p_41 =>
        .jnz (.var p_41.fst)
          (.let_ (op64 (.add i64) (.var pMark) (.var p.fst)) fun p_42 =>
           .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun p_43 =>
           .store (.var p_43.fst) (.var p_42.fst)
             (.let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun p =>
              .jump Js_1.fst (.var p.fst, ())))
          (.jump Js.fst ())) .nil) fun Js => .jump Js.fst (.imm 0, ()))
      (.let_ (op64 (.add i64) (.var p) (.imm 240)) fun p_41 =>
       .load i64 (.var p_41.fst) fun ld_11 =>
       .group (sig := [[i64]]) (fun Js_1 => .cons (fun p_42 =>
         .let_ (op64 (.add i64) (.var p) (.imm 272)) fun p =>
         .load i64 (.var p.fst) fun ld_12 =>
         .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_42.fst, .var ld_12, ())) fun p =>
         .jnz (.var p.fst)
           (.let_ (op64 (.mul i64) (.var p_42.fst) (.imm 4)) fun p =>
            .let_ (op64 (.add i64) (.var ld_11) (.var p.fst)) fun p =>
            .load i32 (.var p.fst) fun ld_13 =>
            .group (sig := [[]]) (fun _ => .cons (fun _ =>
              .let_ (op64 (.add i64) (.var p_42.fst) (.imm 1)) fun p =>
              .jump Js_1.fst (.var p.fst, ())) .nil) fun Js =>
            .let_ (Op.mk (.zext 32 64) (.var ld_13, ())) fun p =>
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var cv, ())) fun p =>
            .jnz (.var p.fst)
              (.let_ (Op.mk (.zext 32 64) (.var ld_13, ())) fun p =>
               .let_ (op64 (.add i64) (.var pMark) (.var p.fst)) fun p =>
               .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun p_43 =>
               .store (.var p_43.fst) (.var p.fst) (.jump Js.fst ()))
              (.jump Js.fst ()))
           (.jump Js.fst ())) .nil) fun Js => .jump Js.fst (.imm 0, ()))

private def fidMinBlkLoopExpr {V : Ty → Type} {C : List Ty → Type}
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
              .call "full_shrink_blk_bool_m6" (as := [i64, i64, i64, i32, i64]) (bs := [.bool])
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
                      .call "full_min_lit_dfs_m6" (as := [i64, i32, .bool, .bool]) (bs := [.bool])
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
      (fidMinCompactLoopExpr tlen pTmp fun keep =>
        .let_ (op64 (.add i64) (.var p) (.imm 72)) fun p_38 =>
        .load i64 (.var p_38.fst) fun ld_9 =>
        fidMinCleanExpr p cv orig_tlen ld_9 keep)) .nil)
    fun Js => .jump Js.fst (.imm 1, ())

private theorem fid_min_shrink_fid_body_eq :
    full_min_shrink_fid_body = fun V _ p =>
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
        (.group (sig := [[]]) (fun _ => .cons (fun _ =>
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
                    (fidMinMarkInitExpr p.fst ld_1 ld_3
                      (fidMinBlkLoopExpr p.fst ld ld_1 ld_3 ld_4 ld_5 ld_1)))))) := by
  rfl

private theorem fid_min_shrink_compact_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {bound_bv : BitVec 64} {bound_n : Nat} {after : Val i64 → Expr Val Cont []}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} (hcore : FullOtfsCoreInv c F0 s)
    (hbd_eq : bound_bv.toNat = bound_n) (hbd1 : 1 ≤ bound_n) (hbd_cv : bound_n ≤ s.core.cur_vars)
    (h0_ok : s.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (h0_val : let l0 := (s.core.tmp[0]?.getD 0#32).toNat
      l0 < 2 * s.core.cur_vars ∧ s.core.vals[l0]?.getD 0#8 = 0xFF#8 ∧
      (s.core.mrk[l0 / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hns_ok : ∀ k, 1 ≤ k → k < bound_n → s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hns_sort : ∀ i j, 1 ≤ i → i ≤ j → j < bound_n →
      s.core.tmp[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(s.core.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {m : Mem 64} (hm_in : (FullMem c s ⋆ R) m)
    (hpost : ∀ (tmp' : List (BitVec 32)) (kp_bv : BitVec 64) (m' : Mem 64),
      let kp := kp_bv.toNat
      tmp'.length = c.max_vars → 1 ≤ kp → kp ≤ bound_n → tmp'[0]? = s.core.tmp[0]? →
      tmp'.take kp = (s.core.tmp.take bound_n).filter (· ≠ 0xFFFFFFFF#32) →
      (∀ k < kp, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      (∀ k < kp, let l := (tmp'[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ j, 1 ≤ j → j < kp →
        let l := (tmp'[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
        lv < s.core.cur_level ∧ (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ a b, 1 ≤ a → a ≤ b → b < kp →
        (s.core.lvl[(tmp'[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' →
      wp Γ Q X (after kp_bv) m') :
    wp Γ Q X (fidMinCompactLoopExpr bound_bv c.pTmp after) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen := hcore.1.core_ok; have hcv := hlen.cur_vars_le
  have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
  dsimp only [fidMinCompactLoopExpr]
  refine wp_loop_group (ts := [i64, i64]) (fun n (kp, k, ()) mk =>
      n = bound_n - k.toNat ∧ 1 ≤ kp.toNat ∧ kp.toNat ≤ k.toNat ∧ k.toNat ≤ bound_n ∧
      ∃ tmp_k, tmp_k.length = c.max_vars ∧ tmp_k[0]? = s.core.tmp[0]? ∧
      tmp_k.take kp.toNat = (s.core.tmp.take k.toNat).filter (· ≠ 0xFFFFFFFF#32) ∧
      (∀ j, k.toNat ≤ j → j < bound_n → tmp_k[j]? = s.core.tmp[j]?) ∧
      (∀ j, 1 ≤ j → j < kp.toNat →
        let l := (tmp_k[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
        lv < s.core.cur_level ∧ (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (∀ a b, 1 ≤ a → a ≤ b → b < kp.toNat →
        (s.core.lvl[(tmp_k[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp_k[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (∀ a, 1 ≤ a → a < kp.toNat → ∀ j, k.toNat ≤ j → j < bound_n →
        s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.core.lvl[(tmp_k[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (FullMem c { s with core := { s.core with tmp := tmp_k } } ⋆ R) mk) ?_
    (fun Js hJs => by
      ml_lets; have h0lt : 0 < s.core.tmp.length := by rw [hlen.tmp_len_arr]; omega
      have htake1 : s.core.tmp.take 1 = [s.core.tmp[0]'h0lt] := by
        simpa using List.take_succ_eq_append_getElem (i := 0) h0lt
      have h0ne : (s.core.tmp[0]'h0lt) ≠ 0xFFFFFFFF#32 := by
        rwa [List.getElem?_eq_getElem h0lt, Option.getD_some] at h0_ok
      exact hJs (bound_n - 1) (1#64, 1#64, ()) m
        ⟨by rw [h1v], by rw [h1v]; exact le_refl _, by rw [h1v]; exact le_refl _, hbd1,
         s.core.tmp, hlen.tmp_len_arr, rfl, by rw [h1v, htake1]; simp [h0ne], fun _ _ _ => rfl,
         fun _ h1 h2 => by rw [h1v] at h2; omega, fun _ _ _ _ h => by rw [h1v] at h; omega,
         fun _ _ h => by rw [h1v] at h; omega, hm_in⟩)
  rintro Js n ⟨kp, k, ⟨⟩⟩ mk hJs
    ⟨rfl, hkp1, hkpk, hkle, tmp_k, htkl, htk0, htk_f, htk_r, htk_l, htk_s, htk_c, hm_k⟩
  let st_k : FullState := { s with core := { s.core with tmp := tmp_k } }
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have hkx : k.toNat < bound_n := by
      rw [BitVec.ult, decide_eq_true_eq, hbd_eq] at hlt; exact hlt
    have hk_tl : k.toNat < st_k.core.tmp.length := by dsimp only [st_k]; rw [htkl]; omega
    have hkp_tl : kp.toNat < st_k.core.tmp.length := by dsimp only [st_k]; rw [htkl]; omega
    have hk_eq : tmp_k[k.toNat]? = s.core.tmp[k.toNat]? := htk_r k.toNat (le_refl _) hkx
    have hk1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
    have htake_k : s.core.tmp.take (k.toNat + 1) = s.core.tmp.take k.toNat ++
        [s.core.tmp[k.toNat]'(by rw [hlen.tmp_len_arr]; omega)] :=
      List.take_succ_eq_append_getElem (by rw [hlen.tmp_len_arr]; omega)
    refine wp_join_group (ts := [i64]) (fun (kp', ()) mk' =>
        1 ≤ kp'.toNat ∧ kp'.toNat ≤ k.toNat + 1 ∧ ∃ tmp_n, tmp_n.length = c.max_vars ∧
        tmp_n[0]? = s.core.tmp[0]? ∧
        tmp_n.take kp'.toNat = (s.core.tmp.take (k.toNat + 1)).filter (· ≠ 0xFFFFFFFF#32) ∧
        (∀ j, k.toNat + 1 ≤ j → j < bound_n → tmp_n[j]? = s.core.tmp[j]?) ∧
        (∀ j, 1 ≤ j → j < kp'.toNat →
          let l := (tmp_n[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
          lv < s.core.cur_level ∧ (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ a b, 1 ≤ a → a ≤ b → b < kp'.toNat →
          (s.core.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp_n[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
        (∀ a, 1 ≤ a → a < kp'.toNat → ∀ j, k.toNat + 1 ≤ j → j < bound_n →
          s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
        (FullMem c { s with core := { s.core with tmp := tmp_n } } ⋆ R) mk')
      (fun _ ⟨kp', ⟨⟩⟩ mk'
          ⟨hkp'1, hkp'k, tmp_n, htnl, htn0, htn_f, htn_r, htn_l, htn_s, htn_c, hm_n⟩ => by
        rw [Blocks.get_here]; ml_lets
        exact hJs (bound_n - (k + 1).toNat) (kp', k + 1, ()) mk' (by omega)
          ⟨rfl, hkp'1, by omega, by omega, tmp_n, htnl, htn0, by rw [hk1]; exact htn_f,
           fun j hj => htn_r j (by omega), htn_l, htn_s,
           fun a ha1 ha2 j hj => htn_c a ha1 ha2 j (by omega), hm_n⟩) ?_
    rintro J1 hJ1; ml_ld c0_load_full_tmp (s := st_k) (i := k) hk_tl hm_k; ml_lets; ml_jnz
    refine ⟨fun hne => ?_, fun heq => ?_⟩
    · have hne' : tmp_k[k.toNat]'hk_tl ≠ 0xFFFFFFFF#32 := bne_iff_ne.mp hne
      ml_ld c0_load_full_tmp (s := st_k) (i := k) hk_tl hm_k; ml_lets
      ml_st m_n, hm_n := c0_store_full_tmp (s := st_k) (i := kp) (tmp_k[k.toNat]'hk_tl)
        hkp_tl hm_k
      have hkp1' : (kp + 1).toNat = kp.toNat + 1 := by bv_omega
      have hkne : s.core.tmp[k.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [← hk_eq, List.getElem?_eq_getElem hk_tl, Option.getD_some]; exact hne'
      have hktl : k.toNat < s.core.tmp.length := by rw [hlen.tmp_len_arr]; omega
      have hk_get : s.core.tmp[k.toNat]?.getD 0#32 = s.core.tmp[k.toNat]'hktl := by
        rw [List.getElem?_eq_getElem hktl, Option.getD_some]
      have hval_k := hns_ok k.toNat (by omega) hkx hkne
      have hkv_eq : tmp_k[k.toNat]'hk_tl = s.core.tmp[k.toNat]'hktl := by
        rw [List.getElem?_eq_getElem hk_tl, List.getElem?_eq_getElem hktl] at hk_eq
        exact Option.some.inj hk_eq
      let tmp_n := tmp_k.set kp.toNat (tmp_k[k.toNat]'hk_tl)
      have hset_k : tmp_n[kp.toNat]?.getD 0#32 = s.core.tmp[k.toNat]?.getD 0#32 := by
        dsimp only [tmp_n]; rw [List.getElem?_set_self (by rw [htkl]; omega),
          Option.getD_some, hkv_eq, hk_get]
      have htn_l : ∀ j, 1 ≤ j → j < (kp + 1).toNat →
          let l := (tmp_n[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
          lv < s.core.cur_level ∧ (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
        intro j hj1 hj2; dsimp only [tmp_n]; rw [hkp1'] at hj2; by_cases hje : j = kp.toNat
        · subst j; simpa [tmp_n, hset_k] using hval_k
        · rw [List.getElem?_set_ne (Ne.symm hje)]; exact htk_l j hj1 (by omega)
      have htn_s : ∀ a b, 1 ≤ a → a ≤ b → b < (kp + 1).toNat →
          (s.core.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp_n[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        intro a b ha1 hab hb2; dsimp only [tmp_n]; rw [hkp1'] at hb2; by_cases hbe : b = kp.toNat
        · subst b; by_cases hae : a = kp.toNat
          · subst a; exact le_refl _
          · have h1 := htk_c a ha1 (by omega) k.toNat (le_refl _) hkx hkne
            rw [List.getElem?_set_ne (Ne.symm hae)]; simpa [tmp_n, hset_k] using h1
        · rw [List.getElem?_set_ne (Ne.symm hbe), List.getElem?_set_ne (by omega)]
          exact htk_s a b ha1 hab (by omega)
      have htn_c : ∀ a, 1 ≤ a → a < (kp + 1).toNat → ∀ j, k.toNat + 1 ≤ j → j < bound_n →
          s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        intro a ha1 ha2 j hj1 hj2 hjne; dsimp only [tmp_n]; rw [hkp1'] at ha2
        by_cases hae : a = kp.toNat
        · subst a; simpa [tmp_n, hset_k] using
            hns_sort k.toNat j (by omega) (by omega) hj2 hkne hjne
        · rw [List.getElem?_set_ne (Ne.symm hae)]
          exact htk_c a ha1 (by omega) j (by omega) hj2 hjne
      ml_lets; have hne_s : s.core.tmp[k.toNat]'hktl ≠ 0xFFFFFFFF#32 := hkv_eq ▸ hne'
      refine hJ1 (kp + 1, ()) m_n ⟨by omega, by omega, tmp_n, by rw [List.length_set, htkl],
        by rw [List.getElem?_set_ne (by omega)]; exact htk0, ?_, ?_, htn_l, htn_s, htn_c, hm_n⟩
      · rw [hkp1', htake_k, List.filter_append, fidListTakeSuccSet _ (by omega), htk_f, hkv_eq]
        simp [hne_s]
      · intro j hj1 hj2; dsimp only [tmp_n]
        rw [List.getElem?_set_ne (by omega)]; exact htk_r j (by omega) hj2
    · ml_lets; have heq' : tmp_k[k.toNat]'hk_tl = 0xFFFFFFFF#32 := bne_eq_false_iff_eq.mp heq
      have hkeq : s.core.tmp[k.toNat]'(by rw [hlen.tmp_len_arr]; omega) = 0xFFFFFFFF#32 := by
        rw [List.getElem?_eq_getElem hk_tl,
          List.getElem?_eq_getElem (by rw [hlen.tmp_len_arr]; omega)] at hk_eq
        exact (Option.some.inj hk_eq) ▸ heq'
      refine hJ1 (kp, ()) mk ⟨hkp1, by omega, tmp_k, htkl, htk0, ?_, ?_, htk_l, htk_s, ?_, hm_k⟩
      · rw [htake_k, List.filter_append, htk_f]; simp [hkeq]
      · intro j hj1 hj2; exact htk_r j (by omega) hj2
      · intro a ha1 ha2 j hj1 hj2 hjne; exact htk_c a ha1 ha2 j (by omega) hj2 hjne
  · have hke : k.toNat = bound_n := by
      rw [BitVec.ult, decide_eq_false_iff_not, hbd_eq] at hge; omega
    rw [hke] at htk_f hkpk
    refine hpost tmp_k kp mk htkl hkp1 hkpk htk0 htk_f (fun j hj => ?_) (fun j hj => ?_)
      htk_l htk_s hm_k
    · have hmem : tmp_k[j]'(by omega) ∈ tmp_k.take kp.toNat :=
        List.mem_iff_getElem.mpr ⟨j, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
      rw [htk_f, List.mem_filter] at hmem
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact of_decide_eq_true hmem.2
    · rcases Nat.eq_zero_or_pos j with rfl | hj1
      · simpa [htk0] using h0_val
      · have := htk_l j hj1 hj; exact ⟨this.1, this.2.1, this.2.2.2.2⟩

private theorem fid_min_shrink_clean_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} (hcore : FullOtfsCoreInv c F0 s)
    {keep_bv : BitVec 64} {m : Mem 64} (hm_in : (FullMem c s ⋆ R) m)
    (hmin : FullMinMarkInv s.core
      (((s.core.tmp.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8 : ∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hpost : ∀ (mrk' : List (BitVec 8)) (m' : Mem 64),
      let sc' := { s.scratch with
        min_removed := s.scratch.min_removed + (BitVec.ofNat 64 s.core.tmp_len - keep_bv),
        learned_lits := s.scratch.learned_lits + keep_bv }
      let s' : FullState := {
        core := { s.core with mrk := mrk', min_clr_len := 0, min_clr_full := 0#64,
                              tmp_len := keep_bv.toNat }
        scratch := sc' }
      mrk'.length = c.max_vars → (∀ w, s.core.cur_vars ≤ w → mrk'[w]? = s.core.mrk[w]?) →
      FullMarksClear s' → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (fidMinCleanExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 s.core.tmp_len) c.pMark keep_bv) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen := hcore.1.core_ok; have hcv := hlen.cur_vars_le
  have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
  have hz8 : (0 : BitVec 32).setWidth 8 = 0#8 := rfl
  have hmcl_le := hlen.min_clr_len_le; have hmcl_arr := hlen.min_clr_len_arr
  have hmcl_bv : (BitVec.ofNat 64 s.core.min_clr_len).toNat = s.core.min_clr_len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only [fidMinCleanExpr]
  refine wp_join_group (ts := []) (fun () mc => ∃ mrk',
      mrk'.length = c.max_vars ∧ (∀ w, s.core.cur_vars ≤ w → mrk'[w]? = s.core.mrk[w]?) ∧
      (∀ v < s.core.cur_vars, mrk'[v]?.getD 0#8 = 0#8) ∧
      (FullMem c { s with core := { s.core with mrk := mrk' } } ⋆ R) mc) ?_ ?_
  · rintro Js ⟨⟩ mc ⟨mrk', hml, hab, hmc, hm_c⟩; rw [Blocks.get_here]; ml_lets
    let sc0 : FullState := { s with core := { s.core with mrk := mrk' } }
    ml_st m1, hm1 := store_full_min_clr_len (s := sc0) 0 (Nat.zero_lt_succ _) hm_c; ml_lets
    let sc0b : FullState := { sc0 with core := { sc0.core with min_clr_len := 0 } }
    ml_st m2, hm2 := store_full_min_clr_full (s := sc0b) 0#64 hm1; ml_lets
    ml_st m3, hm3 := c0_store_full_tmp_len
      (s := { sc0b with core := { sc0b.core with min_clr_full := 0#64 } }) keep_bv hm2
    let sc1 : FullState := { s with core := { s.core with
      mrk := mrk', min_clr_len := 0, min_clr_full := 0#64, tmp_len := keep_bv.toNat } }
    ml_ld load_full_min_removed (s := sc1) hm3; ml_lets
    ml_st m4, hm4 := store_full_min_removed (s := sc1)
      (s.scratch.min_removed + (BitVec.ofNat 64 s.core.tmp_len - keep_bv)) hm3
    let sc2 : FullState := { sc1 with scratch := { sc1.scratch with
      min_removed := s.scratch.min_removed + (BitVec.ofNat 64 s.core.tmp_len - keep_bv) } }
    ml_ld load_full_learned_lits (s := sc2) hm4; ml_lets
    ml_st m5, hm5 := store_full_learned_lits (s := sc2) (s.scratch.learned_lits + keep_bv) hm4
    rw [wp]; exact hpost mrk' m5 hml hab hmc hm5
  rintro Js hJs; ml_ld load_full_min_clr_full hm_in; ml_lets; ml_jnz
  refine ⟨fun _ => ?_, fun hnf => ?_⟩
  · refine wp_loop_group (ts := [i64]) (fun n (z, ()) mz =>
        n = s.core.cur_vars - z.toNat ∧ z.toNat ≤ s.core.cur_vars ∧ ∃ mrk_z,
        mrk_z.length = c.max_vars ∧ (∀ w, s.core.cur_vars ≤ w → mrk_z[w]? = s.core.mrk[w]?) ∧
        (∀ w < z.toNat, mrk_z[w]?.getD 0#8 = 0#8) ∧
        (FullMem c { s with core := { s.core with mrk := mrk_z } } ⋆ R) mz) ?_
      (fun J1 hJ1 => by
        ml_lets; exact hJ1 (s.core.cur_vars - 0) (0#64, ()) m
          ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s.core.mrk, hlen.mrk_len,
           fun _ _ => rfl, fun _ h => by rw [h0v] at h; omega, hm_in⟩)
    rintro J1 n ⟨z, ⟨⟩⟩ mz hJ1 ⟨rfl, hzle, mrk_z, hml_z, hab_z, hz0, hm_z⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · c0_cond hlt; have hzx : z.toNat < s.core.cur_vars := by bv_omega
      have hzm : z.toNat < ({ s with core := { s.core with mrk := mrk_z } } :
          FullState).core.mrk.length := by dsimp only; rw [hml_z]; omega
      ml_lets; ml_st m_z', hm_z' := c0_store_full_mrk (s := { s with core := { s.core with
        mrk := mrk_z } }) (i := z) ((0 : BitVec 32).setWidth 8) hzm hm_z
      have hz1 : (z + 1).toNat = z.toNat + 1 := by bv_omega
      rw [hz8] at hm_z'; ml_lets
      refine hJ1 (s.core.cur_vars - (z + 1).toNat) (z + 1, ()) m_z' (by omega)
        ⟨rfl, by omega, mrk_z.set z.toNat 0#8, by rw [List.length_set, hml_z],
         fun w hw => by rw [List.getElem?_set_ne (by omega)]; exact hab_z w hw,
         fun w hw => ?_, hm_z'⟩
      by_cases hwe : w = z.toNat
      · subst w; rw [List.getElem?_set_self (by omega)]; rfl
      · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hz0 w (by omega)
    · c0_cond hge; have hze : z.toNat = s.core.cur_vars := by bv_omega; ml_lets
      exact hJs () mz ⟨mrk_z, hml_z, hab_z, fun w hw => hz0 w (hze ▸ hw), hm_z⟩
  · c0_cond hnf; have hnf' : s.core.min_clr_full = 0#64 := hnf; ml_ld load_full_min_clr_ptr hm_in
    refine wp_loop_group (ts := [i64]) (fun n (z, ()) mz =>
        n = s.core.min_clr_len - z.toNat ∧ z.toNat ≤ s.core.min_clr_len ∧ ∃ mrk_z,
        mrk_z.length = c.max_vars ∧ (∀ w, s.core.cur_vars ≤ w → mrk_z[w]? = s.core.mrk[w]?) ∧
        (∀ w < s.core.cur_vars, mrk_z[w]?.getD 0#8 ≠ 0#8 →
          ∃ k, z.toNat ≤ k ∧ k < s.core.min_clr_len ∧ (s.core.min_clr[k]?.getD 0#32).toNat = w) ∧
        (FullMem c { s with core := { s.core with mrk := mrk_z } } ⋆ R) mz) ?_
      (fun J1 hJ1 => by
        ml_lets; refine hJ1 (s.core.min_clr_len - 0) (0#64, ()) m
          ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s.core.mrk, hlen.mrk_len,
           fun _ _ => rfl, fun w hw hnz => ?_, hm_in⟩
        obtain ⟨k, hk, hke⟩ :=
          hmin.clr_cov hnf' w hw ((fidMinMarkInvMrkNeZeroIff hmin hno8 hw).mp hnz)
        exact ⟨k, by rw [h0v]; exact Nat.zero_le _, hk, hke⟩)
    rintro J1 n ⟨z, ⟨⟩⟩ mz hJ1 ⟨rfl, hzle, mrk_z, hml_z, hab_z, hcov_z, hm_z⟩
    let st_z : FullState := { s with core := { s.core with mrk := mrk_z } }
    rw [Blocks.get_here]; ml_ld load_full_min_clr_len (s := st_z) hm_z; ml_lets; ml_jnz
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hzm : z.toNat < s.core.min_clr_len := by
        rw [BitVec.ult, decide_eq_true_eq, hmcl_bv] at hlt; exact hlt
      have hzl : z.toNat < st_z.core.min_clr.length := by
        dsimp only [st_z]; rw [hmcl_arr]; exact lt_of_lt_of_le hzm hmcl_le
      ml_ld c0_load_full_min_clr (s := st_z) (i := z) hzl hm_z
      let v32 := s.core.min_clr[z.toNat]'hzl
      have hz1 : (z + 1).toNat = z.toNat + 1 := by bv_omega
      refine wp_join_group (ts := []) (fun () mn => ∃ mrk_n,
          mrk_n.length = c.max_vars ∧ (∀ w, s.core.cur_vars ≤ w → mrk_n[w]? = s.core.mrk[w]?) ∧
          (∀ w < s.core.cur_vars, mrk_n[w]?.getD 0#8 ≠ 0#8 → ∃ k, z.toNat + 1 ≤ k ∧
            k < s.core.min_clr_len ∧ (s.core.min_clr[k]?.getD 0#32).toNat = w) ∧
          (FullMem c { s with core := { s.core with mrk := mrk_n } } ⋆ R) mn)
        (fun _ ⟨⟩ mn ⟨mrk_n, hml_n, hab_n, hcov_n, hm_n⟩ => by
          rw [Blocks.get_here]; ml_lets
          exact hJ1 (s.core.min_clr_len - (z + 1).toNat) (z + 1, ()) mn (by omega)
            ⟨rfl, by omega, mrk_n, hml_n, hab_n,
             fun w hw hnz => by rw [hz1]; exact hcov_n w hw hnz, hm_n⟩) ?_
      rintro J2 hJ2; ml_lets; ml_jnz; refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
      · have hvx : (v32.setWidth 64).toNat < s.core.cur_vars := by
          rw [BitVec.ult, decide_eq_true_eq, hcv_bv] at hvlt; exact hvlt
        have hvx' : v32.toNat < s.core.cur_vars := by rwa [bv_c0_zext32_64] at hvx
        have hvm : (v32.setWidth 64).toNat < st_z.core.mrk.length := by
          dsimp only [st_z]; rw [hml_z]; omega
        ml_lets; ml_st mn, hmn := c0_store_full_mrk (s := st_z) (i := v32.setWidth 64)
          ((0 : BitVec 32).setWidth 8) hvm hm_z
        rw [hz8, bv_c0_zext32_64] at hmn; ml_lets
        refine hJ2 () mn ⟨mrk_z.set v32.toNat 0#8, by rw [List.length_set, hml_z],
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
        ml_lets; refine hJ2 () mz ⟨mrk_z, hml_z, hab_z, fun w hw hnz => ?_, hm_z⟩
        obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
        have hknz : k ≠ z.toNat := by
          rintro rfl; dsimp only [v32] at hvx
          rw [List.getElem?_eq_getElem hzl, Option.getD_some] at hke; dsimp only [st_z] at hke
          omega
        exact ⟨k, by omega, hk2, hke⟩
    · have hze : z.toNat = s.core.min_clr_len := by
        rw [BitVec.ult, decide_eq_false_iff_not, hmcl_bv] at hge; omega
      ml_lets; refine hJs () mz ⟨mrk_z, hml_z, hab_z, fun w hw => ?_, hm_z⟩
      by_cases hz : mrk_z[w]?.getD 0#8 = 0#8; · exact hz
      exfalso; obtain ⟨k, hk1, hk2, _⟩ := hcov_z w hw hz; omega

private abbrev fidBlkState (s : FullState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (mstk mclr sstk : List (BitVec 32)) (mcl : Nat) (mcf : BitVec 64) : FullState :=
  { core := { s.core with
      tmp, mrk, min_stk := mstk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with shrink_stk := sstk } }

private abbrev fidMinShrinkRes (s : FullState) (tmp : List (BitVec 32)) (tl : Nat)
    (mrk : List (BitVec 8)) (mstk mclr sstk : List (BitVec 32)) (mcl : Nat)
    (mcf conf llits mrem : BitVec 64) : FullState :=
  { core := { s.core with
      tmp, tmp_len := tl, mrk, min_stk := mstk, min_clr := mclr,
      min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      conflicts := conf, learned_lits := llits, min_removed := mrem, shrink_stk := sstk } }

private structure FidBlkLoopInv (c : FullCfg) (F0 : CNF Nat) (s s_c1 : FullState)
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

private theorem fid_min_shrink_blk_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s s_c1 : FullState} {tlen : Nat} {tlen_bv : BitVec 64} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost}
    (hDfs : ∀ args m Q X, m6MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m6ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m6" [i64, i64, i64, i32, i64] [.bool] args m Q X)
    (htlen_eq : tlen_bv.toNat = tlen) (ht1 : 1 ≤ tlen) (ht_cv : tlen ≤ s.core.cur_vars)
    (ht_tl : tlen ≤ s.core.tmp_len)
    (hc1_inv : FidBlkLoopInv c F0 s s_c1 tlen 1 s_c1)
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
        (mstk' mclr' sstk' : List (BitVec 32)) (mcl' : Nat) (mcf' llits' mrem' : BitVec 64)
        (m' : Mem 64),
      let s' := fidMinShrinkRes s_c1 tmp' tl' mrk' mstk' mclr' sstk' mcl' mcf'
        s_c1.scratch.conflicts llits' mrem'
      tmp'.length = c.max_vars → mrk'.length = c.max_vars → mstk'.length = 2 * c.minDepth →
      mclr'.length = c.max_vars → mcl' ≤ c.max_vars → sstk'.length = c.max_vars →
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
      (∀ i j, 1 ≤ i → i ≤ j → j < tl' →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (fidMinBlkLoopExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pTrailPos tlen_bv) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hc1_inv.core.1.core_ok.cur_vars_le; rw [hc1_inv.cv_eq] at hcv
  have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
  dsimp only [fidMinBlkLoopExpr]
  refine wp_loop_group (ts := [i64]) (fun n (beg, ()) mb =>
      n = tlen - beg.toNat ∧ 1 ≤ beg.toNat ∧ beg.toNat ≤ tlen ∧
      ∃ (mrk_b : List (BitVec 8)) (tmp_b mstk_b mclr_b sstk_b : List (BitVec 32))
        (mcl_b : Nat) (mcf_b : BitVec 64),
      let cur := fidBlkState s_c1 tmp_b mrk_b mstk_b mclr_b sstk_b mcl_b mcf_b
      FidBlkLoopInv c F0 s s_c1 tlen beg.toNat cur ∧ (FullMem c cur ⋆ R) mb) ?_
    (fun Js hJs => by
      ml_lets; exact hJs (tlen - 1) (1#64, ()) m
        ⟨by rw [h1v], by rw [h1v]; exact le_refl _, by rw [h1v]; exact ht1,
         s_c1.core.mrk, s_c1.core.tmp, s_c1.core.min_stk, s_c1.core.min_clr,
         s_c1.scratch.shrink_stk, s_c1.core.min_clr_len, s_c1.core.min_clr_full,
         by rw [h1v]; exact hc1_inv, hm_in⟩)
  rintro Js n ⟨beg, ⟨⟩⟩ mb hJs
    ⟨rfl, hbeg1, hbeg_tl, mrk_b, tmp_b, mstk_b, mclr_b, sstk_b, mcl_b, mcf_b, hb, hm_b⟩
  let cur := fidBlkState s_c1 tmp_b mrk_b mstk_b mclr_b sstk_b mcl_b mcf_b
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
    have hbtp_l : ((lit_b >>> 1).setWidth 64).toNat < cur.core.trail_pos.length := by
      rw [hb.core.1.core_ok.trail_pos_len, bv_c0_zext32_64]; omega
    ml_lets
    ml_ld c0_load_full_trail_pos (s := cur) (i := (lit_b >>> 1).setWidth 64) hbtp_l hm_b
    let tp0_32 := cur.core.trail_pos[((lit_b >>> 1).setWidth 64).toNat]'hbtp_l
    let tp0 := tp0_32.setWidth 64
    have hlitb_c1 : (s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat = lit_b.toNat := by
      rw [← hbt1, List.getElem?_eq_getElem hbg_tl, Option.getD_some]
    have hblvl_eq :
        (s.core.lvl[(s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        blvl.toNat := by
      have hl_get : s.core.lvl[((lit_b >>> 1).setWidth 64).toNat]? = some blvl := by
        rw [← hb.lvl_eq]; exact List.getElem?_eq_getElem hblvl_l
      rw [hlitb_c1, ← bv32_lshr_1 lit_b, ← bv_c0_zext32_64 (lit_b >>> 1), hl_get,
        Option.getD_some]
    have hblvl_bounds : 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level := by
      rw [← hblvl_eq]; exact hc1_lvls beg.toNat hbeg1 hbx
    have htp0_eq :
        (s.core.trail_pos[(s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        tp0.toNat := by
      have htp_get : s.core.trail_pos[((lit_b >>> 1).setWidth 64).toNat]? = some tp0_32 := by
        rw [← hb.tpos_eq]; exact List.getElem?_eq_getElem hbtp_l
      dsimp only [tp0]
      rw [hlitb_c1, bv_c0_zext32_64, ← bv32_lshr_1 lit_b, ← bv_c0_zext32_64 (lit_b >>> 1),
        htp_get, Option.getD_some]
    have hbg_p1 : (beg + 1).toNat = beg.toNat + 1 := min_bv64_add1 (by omega)
    ml_lets
    refine wp_loop_group (ts := [i64, i64]) (fun n1 (max_tr', end_b, ()) ms =>
        n1 = tlen - end_b.toNat ∧ ms = mb ∧ beg.toNat < end_b.toNat ∧ end_b.toNat ≤ tlen ∧
        ∀ k, beg.toNat ≤ k → k < end_b.toNat →
          (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
          (s.core.trail_pos[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            max_tr'.toNat) ?_
      (fun Js_1 hJs_1 => by
        exact hJs_1 (tlen - (beg + 1).toNat) (tp0, beg + 1, ()) mb
          ⟨by rw [hbg_p1], rfl, by omega, by omega, fun k hk1 hk2 => by
            have hke : k = beg.toNat := by omega
            subst k; exact ⟨hblvl_eq, le_of_eq htp0_eq⟩⟩)
    rintro Js_1 n1 ⟨max_tr', end_b, ⟨⟩⟩ ms hJs_1 ⟨rfl, hms, hbg_end, hend_tl, hscan⟩
    subst ms
    rw [Blocks.get_here]
    refine wp_join_group (ts := []) (fun () ms' =>
        ms' = mb ∧ (end_b.toNat < tlen →
          (s.core.lvl[(s_c1.core.tmp[beg.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
          (s.core.lvl[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat))
      ?_ ?_
    · rintro J_2 ⟨⟩ ms' ⟨hms', hnxt⟩; subst ms'
      rw [Blocks.get_here]
      refine wp_join_group (ts := []) (fun () mf =>
          ∃ (mrk_f : List (BitVec 8)) (tmp_f mstk_f mclr_f sstk_f : List (BitVec 32))
            (mcl_f : Nat) (mcf_f : BitVec 64),
          let cf := fidBlkState s_c1 tmp_f mrk_f mstk_f mclr_f sstk_f mcl_f mcf_f
          FidBlkLoopInv c F0 s s_c1 tlen end_b.toNat cf ∧ (FullMem c cf ⋆ R) mf)
        (fun _ ⟨⟩ mf ⟨mrk_f, tmp_f, mstk_f, mclr_f, sstk_f, mcl_f, mcf_f, hbf, hmf⟩ => by
          rw [Blocks.get_here]
          exact hJs (tlen - end_b.toNat) (end_b, ()) mf (by omega)
            ⟨rfl, by omega, hend_tl, mrk_f, tmp_f, mstk_f, mclr_f, sstk_f, mcl_f, mcf_f,
             hbf, hmf⟩) ?_
      rintro J_3 hJ_3
      have hnxt_bnd : 1 < end_b.toNat → end_b.toNat < tlen →
          (s.core.lvl[(s_c1.core.tmp[end_b.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
          (s.core.lvl[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        intro _ hlt'; have hs1 := hscan (end_b.toNat - 1) (by omega) (by omega)
        have hlt1 := hnxt hlt'; rw [hblvl_eq] at hlt1; omega
      have hskip_inv : FidBlkLoopInv c F0 s s_c1 tlen end_b.toNat cur :=
        { hb with
          tail_eq := fun k hk1 hk2 => hb.tail_eq k (by omega) hk2,
          beg_bnd := hnxt_bnd }
      ml_lets; ml_jnz; refine ⟨fun hge2 => ?_, fun _ => by
        ml_lets
        exact hJ_3 () mb ⟨mrk_b, tmp_b, mstk_b, mclr_b, sstk_b, mcl_b, mcf_b, hskip_inv, hm_b⟩⟩
      have hbg_end2 : beg.toNat + 2 ≤ end_b.toNat := by c0_cond hge2; bv_omega
      refine wp_join_group (ts := []) (fun () mf =>
          ∃ (mrk_f : List (BitVec 8)) (tmp_f mstk_f mclr_f sstk_f : List (BitVec 32))
            (mcl_f : Nat) (mcf_f : BitVec 64),
          let cf := fidBlkState s_c1 tmp_f mrk_f mstk_f mclr_f sstk_f mcl_f mcf_f
          FidBlkLoopInv c F0 s s_c1 tlen end_b.toNat cf ∧ (FullMem c cf ⋆ R) mf)
        (fun _ ⟨⟩ mf ⟨mrk_f, tmp_f, mstk_f, mclr_f, sstk_f, mcl_f, mcf_f, hbf, hmf⟩ => by
          rw [Blocks.get_here]
          exact hJ_3 () mf ⟨mrk_f, tmp_f, mstk_f, mclr_f, sstk_f, mcl_f, mcf_f, hbf, hmf⟩) ?_
      rintro J_4 hJ_4
      ml_lets; apply wp_call_of_spec; apply hSb; dsimp only [vals, Arg.val]
      have hmin_cur : Full.FullMinMarkInv cur.core (((cur.core.tmp.take tlen).filter
          (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := fidToFullMinInv hb.min_inv
      have hblvl_cur_lt : blvl.toNat < cur.core.cur_level := by
        rw [hb.clvl_eq]; exact hblvl_bounds.2
      refine m6ShrinkBlkBoolSpec_of (keepLen := tlen) hb.core hmin_cur
        (fun v hv => hb.no8 v (by rw [← hb.cv_eq]; exact hv))
        hbeg1 hbg_end hend_tl (by rw [hb.cv_eq]; exact ht_cv)
        hblvl_bounds.1 hblvl_cur_lt ?_ ?_ hm_b
        fun ok tmp_f mrk_f mstk_f mclr_f mcl_f mcf_f sstk_f m_f hcore_f hmin_f hab_f hno8_f
          _hmono2_f hfl_f hother_f hlvl_f hnodup_f hent_f hrem_f hm_f => ?_
      · intro k hk1 hk2; change beg.toNat ≤ k at hk1; change k < end_b.toNat at hk2
        have hpk : cur.core.tmp[k]? = s_c1.core.tmp[k]? := hb.tail_eq k hk1 (by omega)
        have hkne : cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
          rw [hpk]; exact hc1_ne k (by omega)
        have hrk := hb.rem_mrk k (by omega) hkne; have hsc := hscan k hk1 hk2; rw [hpk] at hrk ⊢
        have hlv_s := hsc.1; rw [← hb.lvl_eq] at hlv_s
        have htp_s := hsc.2; rw [← hb.tpos_eq] at htp_s
        exact ⟨by rw [hb.cv_eq]; exact hrk.1, by rw [hb.vals_eq]; exact hrk.2.1, hlv_s, htp_s⟩
      · intro k hk hne; have hrk := hb.rem_mrk k hk hne
        exact ⟨by rw [hb.cv_eq]; exact hrk.1, by rw [hb.vals_eq]; exact hrk.2.1, hrk.2.2⟩
      · let cf := fidBlkState s_c1 tmp_f mrk_f mstk_f mclr_f sstk_f mcl_f mcf_f
        have hcf_eq :
            ({ cur with
                core := { cur.core with
                  tmp := tmp_f, mrk := mrk_f, min_stk := mstk_f,
                  min_clr := mclr_f, min_clr_len := mcl_f, min_clr_full := mcf_f },
                scratch := { cur.scratch with shrink_stk := sstk_f } } : FullState) = cf :=
          rfl
        rw [hcf_eq] at hcore_f hmin_f hrem_f hm_f
        have hent_cf : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
            FullOtfsWitnessInv c F0 F_cur cf.core ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause (((tmp_f.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) := by
          intro F_cur hw hEnt0
          obtain ⟨hwc, hEc⟩ := hb.entails F_cur hw hEnt0
          simpa only [hcf_eq] using hent_f F_cur hwc hEc
        have hnd_cf : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
            (∀ k, 1 ≤ k → k < s.core.tmp_len →
              (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
              (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
            (((tmp_f.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup := by
          intro hnd0 hne0
          refine hnodup_f (hb.nodup hnd0 hne0) fun k hk_tl h_out hkne => ?_
          change (cur.core.lvl[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
            blvl.toNat
          rw [hb.lvl_eq]; rcases Nat.eq_zero_or_pos k with rfl | hk1
          · rw [hb.zero_eq, hc1_0lv]; exact Nat.ne_of_gt hblvl_bounds.2
          · have hpk := hb.post_lvls k hk1 hk_tl hkne
            rw [hpk]
            rcases h_out with hlt_b | hge_e
            · have hle := hc1_sort k (beg.toNat - 1) hk1 (by omega) (by omega)
              have hlt := hb.beg_bnd (by omega) hbx; rw [hblvl_eq] at hlt; omega
            · have hgt := hnxt (by omega); have hle := hc1_sort end_b.toNat k (by omega) hge_e hk_tl
              rw [hblvl_eq] at hgt; omega
        have hab_cf : ∀ v, s.core.cur_vars ≤ v → mrk_f[v]? = s.core.mrk[v]? := fun v hv =>
          (hab_f v (by rw [hb.cv_eq]; exact hv)).trans (hb.mrk_above v hv)
        have hno8_cf : ∀ v < s.core.cur_vars, (mrk_f[v]?.getD 0#8 &&& 8#8) = 0#8 :=
          fun v hv => hno8_f v (by rw [hb.cv_eq]; exact hv)
        have hzero_cf : tmp_f[0]? = s_c1.core.tmp[0]? :=
          (hother_f 0 ht1 (Or.inl (Nat.zero_lt_of_lt hbeg1))).trans hb.zero_eq
        have hrem_cf : ∀ k < tlen, tmp_f[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
            let l := (tmp_f[k]?.getD 0#32).toNat
            l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
            (mrk_f[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
          intro k hk hne; have := hrem_f k hk hne
          exact ⟨by rw [← hb.cv_eq]; exact this.1,
            by rw [← hb.vals_eq]; exact this.2.1, this.2.2⟩
        have hpost_lvls_cf : ∀ k, 1 ≤ k → k < tlen →
            tmp_f[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
            (s.core.lvl[(tmp_f[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
            (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          intro k hk1 hk2 hne
          by_cases hmid : beg.toNat ≤ k ∧ k < end_b.toNat
          · have hlv := hlvl_f k hmid.1 hmid.2 hne
            have hsc := (hscan k hmid.1 hmid.2).1
            have hlv_s : (s.core.lvl[(tmp_f[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                blvl.toNat := by
              have hcl := congrArg
                (fun arr => (arr[(tmp_f[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
                hb.lvl_eq
              exact hcl.symm.trans hlv
            exact hlv_s.trans hsc.symm
          · have hoth := hother_f k hk2 (by omega)
            rw [hoth]; exact hb.post_lvls k hk1 hk2 (by rwa [← hoth])
        ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hfalse => ?_⟩
        · have hbf : FidBlkLoopInv c F0 s s_c1 tlen end_b.toNat cf :=
            ⟨hcore_f, fidToSpecsMinInv hmin_f, hent_cf, hnd_cf, hab_cf, hno8_cf,
             hb.cv_eq, hb.tl_eq, hb.lvl_eq, hb.vals_eq, hb.clvl_eq, hb.tpos_eq, hzero_cf,
             fun k hk1 hk2 => (hother_f k hk2 (Or.inr hk1)).trans (hb.tail_eq k (by omega) hk2),
             hnxt_bnd, hrem_cf, hpost_lvls_cf⟩
          exact hJ_4 () m_f ⟨mrk_f, tmp_f, mstk_f, mclr_f, sstk_f, mcl_f, mcf_f, hbf, hm_f⟩
        · have htmp_eq_fb : tmp_f = cur.core.tmp := hfl_f hfalse
          subst tmp_f
          refine wp_loop_group (ts := [i64]) (fun n2 (mk2, ()) mm =>
              n2 = end_b.toNat - mk2.toNat ∧ beg.toNat ≤ mk2.toNat ∧ mk2.toNat ≤ end_b.toNat ∧
              ∃ (tmp_m : List (BitVec 32)) (mrk_m : List (BitVec 8))
                (mstk_m mclr_m : List (BitVec 32)) (mcl_m : Nat) (mcf_m : BitVec 64),
              let cm := fidBlkState s_c1 tmp_m mrk_m mstk_m mclr_m sstk_f mcl_m mcf_m
              FullOtfsCoreInv c F0 cm ∧
              FullMinMarkInv cm.core
                (((tmp_m.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
              (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
                (cnfOfClauses F_cur).EntailsClause
                  (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
                FullOtfsWitnessInv c F0 F_cur cm.core ∧
                (cnfOfClauses F_cur).EntailsClause (cnfClause
                  (((tmp_m.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) ∧
              (((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
                (∀ k, 1 ≤ k → k < s.core.tmp_len →
                  (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
                  (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
                (((tmp_m.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map
                  fun x => x.toNat / 2).Nodup) ∧
              (∀ v, s.core.cur_vars ≤ v → mrk_m[v]? = s.core.mrk[v]?) ∧
              (∀ v < s.core.cur_vars, (mrk_m[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
              (tmp_m[0]? = s_c1.core.tmp[0]?) ∧
              (∀ k < tlen, tmp_m[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
                let l := (tmp_m[k]?.getD 0#32).toNat
                l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
                (mrk_m[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
              (∀ k, mk2.toNat ≤ k → k < tlen → tmp_m[k]? = s_c1.core.tmp[k]?) ∧
              (∀ k, 1 ≤ k → k < tlen → tmp_m[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
                (s.core.lvl[(tmp_m[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
              (FullMem c cm ⋆ R) mm) ?_
            (fun Js_3 hJs_3 => by
              ml_lets
              exact hJs_3 (end_b.toNat - beg.toNat) (beg, ()) m_f
                ⟨rfl, le_refl _, le_of_lt hbg_end, tmp_b, mrk_f, mstk_f, mclr_f, mcl_f, mcf_f,
                 hcore_f, fidToSpecsMinInv hmin_f, hent_cf, hnd_cf, hab_cf, hno8_cf, hzero_cf,
                 hrem_cf, hb.tail_eq, hpost_lvls_cf, hm_f⟩)
          rintro Js_3 n2 ⟨mk2, ⟨⟩⟩ mm hJs_3
            ⟨rfl, hbm2, hm2_e, tmp_m, mrk_m, mstk_m, mclr_m, mcl_m, mcf_m,
             hcore_m, hmin_m, hent_m, hnd_m, hab_m, hno8_m, h0_m, hrem_m, htail_m, hplvl_m, hm_m⟩
          let cm := fidBlkState s_c1 tmp_m mrk_m mstk_m mclr_m sstk_f mcl_m mcf_m
          rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt_m => ?_, fun hge_m => ?_⟩
          · have hmx2 : mk2.toNat < end_b.toNat := by c0_cond hlt_m; exact hlt_m
            have hmk_tl : mk2.toNat < cm.core.tmp.length := by
              dsimp only [cm]; rw [hcore_m.1.core_ok.tmp_len_arr]; omega
            have hmk_p1 : (mk2 + 1).toNat = mk2.toNat + 1 := min_bv64_add1 (by omega)
            refine wp_join_group (ts := []) (fun () mn =>
                ∃ (tmp_n : List (BitVec 32)) (mrk_n : List (BitVec 8))
                  (mstk_n mclr_n : List (BitVec 32)) (mcl_n : Nat) (mcf_n : BitVec 64),
                let cn := fidBlkState s_c1 tmp_n mrk_n mstk_n mclr_n sstk_f mcl_n mcf_n
                FullOtfsCoreInv c F0 cn ∧
                FullMinMarkInv cn.core
                  (((tmp_n.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
                (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
                  (cnfOfClauses F_cur).EntailsClause
                    (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
                  FullOtfsWitnessInv c F0 F_cur cn.core ∧
                  (cnfOfClauses F_cur).EntailsClause (cnfClause
                    (((tmp_n.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) ∧
                (((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
                  (∀ k, 1 ≤ k → k < s.core.tmp_len →
                    (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
                    (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
                  (((tmp_n.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map
                    fun x => x.toNat / 2).Nodup) ∧
                (∀ v, s.core.cur_vars ≤ v → mrk_n[v]? = s.core.mrk[v]?) ∧
                (∀ v < s.core.cur_vars, (mrk_n[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
                (tmp_n[0]? = s_c1.core.tmp[0]?) ∧
                (∀ k < tlen, tmp_n[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
                  let l := (tmp_n[k]?.getD 0#32).toNat
                  l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
                  (mrk_n[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
                (∀ k, mk2.toNat + 1 ≤ k → k < tlen → tmp_n[k]? = s_c1.core.tmp[k]?) ∧
                (∀ k, 1 ≤ k → k < tlen → tmp_n[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
                  (s.core.lvl[(tmp_n[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
                (FullMem c cn ⋆ R) mn)
              (fun _ ⟨⟩ mn ⟨tmp_n, mrk_n, mstk_n, mclr_n, mcl_n, mcf_n,
                  hcn, hmn, henn, hndn, habn, h8n, h0n, hrmn, htn, hpln, hmmn⟩ => by
                rw [Blocks.get_here]; ml_lets
                exact hJs_3 (end_b.toNat - (mk2 + 1).toNat) (mk2 + 1, ()) mn (by omega)
                  ⟨rfl, by omega, by omega, tmp_n, mrk_n, mstk_n, mclr_n, mcl_n, mcf_n,
                   hcn, hmn, henn, hndn, habn, h8n, h0n, hrmn,
                   fun k hk => htn k (by omega), hpln, hmmn⟩) ?_
            rintro J_m hJ_m; ml_ld c0_load_full_tmp (s := cm) (i := mk2) hmk_tl hm_m
            let lit_m := cm.core.tmp[mk2.toNat]'hmk_tl
            have hm_t1 : cm.core.tmp[mk2.toNat]? = s_c1.core.tmp[mk2.toNat]? :=
              htail_m mk2.toNat (le_refl _) (by omega)
            have hne_m : lit_m ≠ 0xFFFFFFFF#32 := by
              intro heq; apply hc1_ne mk2.toNat (by omega)
              rw [← hm_t1, List.getElem?_eq_getElem hmk_tl, Option.getD_some]; exact heq
            have hrem_m0 : cm.core.tmp[mk2.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem hmk_tl, Option.getD_some]; exact hne_m
            have hrm := hrem_m mk2.toNat (by omega) hrem_m0
            rw [List.getElem?_eq_getElem hmk_tl, Option.getD_some] at hrm
            have hmlv := hc1_lvls mk2.toNat (by omega) (by omega)
            rw [← hm_t1, List.getElem?_eq_getElem hmk_tl, Option.getD_some] at hmlv
            ml_lets; apply wp_call_of_spec; apply hDfs; dsimp only [vals, Arg.val]
            apply m6MinLitDfsSpec_of; dsimp only [Full.fullMinLitSpec]
            let keep_m := (((cm.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)
            refine ⟨c, F0, cm, keep_m, R, rfl, hcore_m, fidToFullMinInv hmin_m,
              by dsimp only [cm]; rw [hc1_inv.cv_eq]; exact hrm.1,
              by dsimp only [cm]; rw [hc1_inv.vals_eq]; exact hrm.2.1,
              by dsimp only [cm]; rw [hc1_inv.lvl_eq, hc1_inv.clvl_eq]; exact hmlv.2,
              fun v hv _ => hno8_m v (by dsimp only [cm] at hv; rw [hc1_inv.cv_eq] at hv; exact hv),
              hm_m,
              fun ok mrk' mstk' mclr' mcl' mcf' m' hlen' hab' hmono2' hbit8' hmin' hok_t hm' => ?_⟩
            have hst := fidMinLitStepState (s_orig := s) (cur := cm) (keepLen := tlen)
              (by omega) (by dsimp only [cm]; rw [hc1_inv.cv_eq]; exact ht_cv) hcore_m hmin_m
              hent_m hnd_m
              (fun v hv => hab_m v (by dsimp only [cm] at hv; rw [hc1_inv.cv_eq] at hv; exact hv))
              (fun v hv => hno8_m v (by dsimp only [cm] at hv; rw [hc1_inv.cv_eq] at hv; exact hv))
              (fun k hk hne => by
                have := hrem_m k hk hne
                exact ⟨by dsimp only [cm]; rw [hc1_inv.cv_eq]; exact this.1,
                  by dsimp only [cm]; rw [hc1_inv.vals_eq]; exact this.2.1, this.2.2⟩)
              (List.getElem?_eq_getElem hmk_tl) hne_m hlen' hab' hmono2' hbit8'
              (fidToSpecsMinInv hmin') fun hok =>
                let ⟨hk1, hk2⟩ := hok_t hok
                ⟨fun k' hk' => fidToSpecsMinInv (hk1 k' hk'), fidToSpecsMinInv hk2⟩
            rcases hst with ⟨hcore_st, hmin_st, hent_st, hnd_st, hab_st, hno8_st, hrem_st, htail_st⟩
            ml_lets; ml_jnz; refine ⟨fun htrue => ?_, fun hfalse => ?_⟩
            · ml_st m_n, hm_n := c0_store_full_tmp
                (s := minLitState cm mrk' mstk' mclr' mcl' mcf') (i := mk2) 0xFFFFFFFF#32
                (by dsimp only [minLitState]; exact hmk_tl) hm'
              rw [htrue] at hcore_st hmin_st hent_st hnd_st hrem_st htail_st
              simp only [↓reduceIte] at hcore_st hmin_st hent_st hnd_st hrem_st htail_st
              have hrem_n : ∀ k < tlen,
                  (tmp_m.set mk2.toNat 0xFFFFFFFF#32)[k]?.getD 0xFFFFFFFF#32 ≠
                    0xFFFFFFFF#32 →
                  let l := ((tmp_m.set mk2.toNat 0xFFFFFFFF#32)[k]?.getD 0#32).toNat
                  l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
                  (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun k hk hne => by
                have := hrem_st k hk hne
                exact ⟨by dsimp only [cm] at this; rw [hc1_inv.cv_eq] at this; exact this.1,
                  by dsimp only [cm] at this; rw [hc1_inv.vals_eq] at this; exact this.2.1,
                  this.2.2⟩
              have hplvl_n : ∀ k, 1 ≤ k → k < tlen →
                  (tmp_m.set mk2.toNat 0xFFFFFFFF#32)[k]?.getD 0xFFFFFFFF#32 ≠
                    0xFFFFFFFF#32 →
                  (s.core.lvl[((tmp_m.set mk2.toNat 0xFFFFFFFF#32)[k]?.getD 0#32).toNat /
                    2]?.getD 0#32).toNat =
                  (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
                fun k hk1 hk2 hne => by
                  have hkn : k ≠ mk2.toNat := by
                    rintro rfl
                    have hmk_tl' : mk2.toNat < tmp_m.length := hmk_tl
                    rw [List.getElem?_set_self hmk_tl', Option.getD_some] at hne
                    exact hne rfl
                  rw [List.getElem?_set_ne (Ne.symm hkn)] at hne ⊢
                  exact hplvl_m k hk1 hk2 hne
              ml_lets
              exact hJ_m () m_n ⟨tmp_m.set mk2.toNat 0xFFFFFFFF#32, mrk', mstk', mclr', mcl',
                mcf', hcore_st, hmin_st, hent_st, hnd_st,
                fun v hv => hab_st v (by dsimp only [cm]; rw [hc1_inv.cv_eq]; exact hv),
                fun v hv => hno8_st v (by dsimp only [cm]; rw [hc1_inv.cv_eq]; exact hv),
                by rw [List.getElem?_set_ne (by omega)]; exact h0_m, hrem_n,
                fun k hk1 hk2 => (htail_st k hk1 hk2).trans (htail_m k (by omega) hk2),
                hplvl_n, by simpa [cm, minLitState, fidBlkState] using hm_n⟩
            · rw [hfalse] at hcore_st hmin_st hent_st hnd_st hrem_st htail_st
              simp only [Bool.false_eq_true, ↓reduceIte] at hcore_st hmin_st hent_st hnd_st
              simp only [Bool.false_eq_true, ↓reduceIte] at hrem_st htail_st
              ml_lets
              refine hJ_m () m' ⟨tmp_m, mrk', mstk', mclr', mcl', mcf',
                hcore_st, hmin_st, hent_st, hnd_st,
                fun v hv => hab_st v (by dsimp only [cm]; rw [hc1_inv.cv_eq]; exact hv),
                fun v hv => hno8_st v (by dsimp only [cm]; rw [hc1_inv.cv_eq]; exact hv),
                h0_m,
                fun k hk hne => by
                  have := hrem_st k hk hne
                  exact ⟨by dsimp only [cm] at this; rw [hc1_inv.cv_eq] at this; exact this.1,
                    by dsimp only [cm] at this; rw [hc1_inv.vals_eq] at this; exact this.2.1,
                    this.2.2⟩,
                fun k hk1 hk2 => htail_m k (by omega) hk2, hplvl_m,
                by simpa [cm, minLitState, fidBlkState] using hm'⟩
          · have hme : mk2.toNat = end_b.toNat := by c0_cond hge_m; bv_omega
            ml_lets
            have hbf_end : FidBlkLoopInv c F0 s s_c1 tlen end_b.toNat cm :=
              ⟨hcore_m, hmin_m, hent_m, hnd_m, hab_m, hno8_m, hc1_inv.cv_eq, hc1_inv.tl_eq,
               hc1_inv.lvl_eq, hc1_inv.vals_eq, hc1_inv.clvl_eq, hc1_inv.tpos_eq,
               h0_m, fun k hk => htail_m k (by rw [hme]; exact hk), hnxt_bnd, hrem_m, hplvl_m⟩
            exact hJ_4 () mm ⟨mrk_m, tmp_m, mstk_m, mclr_m, sstk_f, mcl_m, mcf_m, hbf_end, hm_m⟩
    · rintro J_2 hJ_2; ml_lets; ml_jnz
      refine ⟨fun hlt_e => ?_, fun hge_e => by
        exact hJ_2 () mb ⟨rfl, fun hlt => by
          have : ¬ (end_b.toNat < tlen) := by
            rw [BitVec.ult, decide_eq_false_iff_not, htlen_eq] at hge_e; exact hge_e
          exact absurd hlt this⟩⟩
      have hex : end_b.toNat < tlen := by
        rw [BitVec.ult, decide_eq_true_eq, htlen_eq] at hlt_e; exact hlt_e
      have he_tl : end_b.toNat < cur.core.tmp.length := by
        dsimp only [cur]; rw [hb.core.1.core_ok.tmp_len_arr]; omega
      ml_ld c0_load_full_tmp (s := cur) (i := end_b) he_tl hm_b
      let lit_e := cur.core.tmp[end_b.toNat]'he_tl
      have het1 : cur.core.tmp[end_b.toNat]? = s_c1.core.tmp[end_b.toNat]? :=
        hb.tail_eq end_b.toNat (le_of_lt hbg_end) hex
      have hne_e : cur.core.tmp[end_b.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [het1]; exact hc1_ne end_b.toNat hex
      have hr_e := hb.rem_mrk end_b.toNat hex hne_e
      rw [List.getElem?_eq_getElem he_tl, Option.getD_some] at hr_e
      have hr_e1 : lit_e.toNat < 2 * s.core.cur_vars := hr_e.1
      have hev_lt : (lit_e >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr_1]; omega
      have he_lvl_l : ((lit_e >>> 1).setWidth 64).toNat < cur.core.lvl.length := by
        rw [hb.core.1.core_ok.lvl_len, bv_c0_zext32_64]; omega
      ml_lets; ml_ld c0_load_full_lvl (s := cur) (i := (lit_e >>> 1).setWidth 64) he_lvl_l hm_b
      let elvl := cur.core.lvl[((lit_e >>> 1).setWidth 64).toNat]'he_lvl_l
      have hlit_e_c1 : (s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat = lit_e.toNat := by
        rw [← het1, List.getElem?_eq_getElem he_tl, Option.getD_some]
      have helvl_eq :
          (s.core.lvl[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          elvl.toNat := by
        have hl_get : s.core.lvl[((lit_e >>> 1).setWidth 64).toNat]? = some elvl := by
          rw [← hb.lvl_eq]; exact List.getElem?_eq_getElem he_lvl_l
        rw [hlit_e_c1, ← bv32_lshr_1 lit_e, ← bv_c0_zext32_64 (lit_e >>> 1), hl_get,
          Option.getD_some]
      ml_lets; ml_jnz; refine ⟨fun heq_l => ?_, fun hne_l => ?_⟩
      · have hle_eq : elvl.toNat = blvl.toNat := congrArg BitVec.toNat (beq_iff_eq.mp heq_l)
        ml_ld c0_load_full_tmp (s := cur) (i := end_b) he_tl hm_b
        have he_tp_l : ((lit_e >>> 1).setWidth 64).toNat < cur.core.trail_pos.length := by
          rw [hb.core.1.core_ok.trail_pos_len, bv_c0_zext32_64]; omega
        ml_lets
        ml_ld c0_load_full_trail_pos (s := cur) (i := (lit_e >>> 1).setWidth 64) he_tp_l hm_b
        let tp_e_32 := cur.core.trail_pos[((lit_e >>> 1).setWidth 64).toNat]'he_tp_l
        let tp_e := tp_e_32.setWidth 64
        have htp_e_eq :
            (s.core.trail_pos[(s_c1.core.tmp[end_b.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
            = tp_e.toNat := by
          have htp_get : s.core.trail_pos[((lit_e >>> 1).setWidth 64).toNat]? = some tp_e_32 := by
            rw [← hb.tpos_eq]; exact List.getElem?_eq_getElem he_tp_l
          dsimp only [tp_e]
          rw [hlit_e_c1, bv_c0_zext32_64, ← bv32_lshr_1 lit_e, ← bv_c0_zext32_64 (lit_e >>> 1),
            htp_get, Option.getD_some]
        have he1 : (end_b + 1).toNat = end_b.toNat + 1 := min_bv64_add1 (by omega)
        ml_lets; refine wp_join_group (ts := [i64]) (fun (mx, ()) mn =>
            mn = mb ∧ max_tr'.toNat ≤ mx.toNat ∧ tp_e.toNat ≤ mx.toNat)
          (fun _ ⟨mx, ⟨⟩⟩ mn ⟨rfl, hmx1, hmx2⟩ => by
            rw [Blocks.get_here]; ml_lets
            refine hJs_1 (tlen - (end_b + 1).toNat) (mx, end_b + 1, ()) mn (by omega)
              ⟨rfl, rfl, by omega, by omega, fun k hk1 hk2 => ?_⟩
            by_cases hke : k = end_b.toNat
            · subst k; exact ⟨helvl_eq.trans hle_eq, by rw [htp_e_eq]; exact hmx2⟩
            · have hsc := hscan k hk1 (by omega); exact ⟨hsc.1, le_trans hsc.2 hmx1⟩) ?_
        rintro J_m hJ_m; ml_lets; ml_jnz; refine ⟨fun hmgt => ?_, fun hmle => ?_⟩
        · rw [BitVec.ult, decide_eq_true_eq] at hmgt
          exact hJ_m (tp_e, ()) mb ⟨rfl, le_of_lt hmgt, le_refl _⟩
        · rw [BitVec.ult, decide_eq_false_iff_not] at hmle
          exact hJ_m (max_tr', ()) mb ⟨rfl, le_refl _, Nat.le_of_not_lt hmle⟩
      · have hne_nat : elvl.toNat ≠ blvl.toNat :=
          fun h => (beq_eq_false_iff_ne.mp hne_l) (BitVec.eq_of_toNat_eq h)
        have hle_b := hc1_sort beg.toNat end_b.toNat hbeg1 (le_of_lt hbg_end) hex
        ml_lets; exact hJ_2 () mb ⟨rfl, fun _ => by rw [hblvl_eq, helvl_eq]; omega⟩
  · have hbe : beg.toNat = tlen := by
      rw [BitVec.ult, decide_eq_false_iff_not, htlen_eq] at hge; omega
    have h0_cur : cur.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [hb.zero_eq]; exact hc1_0ne
    have h0_val_cur : let l0 := (cur.core.tmp[0]?.getD 0#32).toNat
        l0 < 2 * cur.core.cur_vars ∧ cur.core.vals[l0]?.getD 0#8 = 0xFF#8 ∧
        (cur.core.mrk[l0 / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
      have h0r := hb.rem_mrk 0 ht1 h0_cur
      rw [hb.cv_eq, hb.vals_eq]; exact h0r
    refine fid_min_shrink_compact_loop_wp hb.core htlen_eq ht1 (by rw [hb.cv_eq]; exact ht_cv)
      h0_cur h0_val_cur ?_ ?_ hm_b
      fun tmp_c2 kp_bv m_c2 htl_c2 hkp1 hkp_tl h0_c2 htake_c2 hne_c2 hval_c2 hns_c2 hsort_c2
        hm_c2 => ?_
    · intro k hk1 hk2 hne; have hrk := hb.rem_mrk k hk2 hne
      have hpk := hb.post_lvls k hk1 hk2 hne; have hlvk := hc1_lvls k hk1 hk2
      rw [hb.cv_eq, hb.vals_eq, hb.lvl_eq, hb.clvl_eq]
      exact ⟨hrk.1, hrk.2.1, hpk ▸ hlvk.1, hpk ▸ hlvk.2, hrk.2.2⟩
    · intro i j hi1 hij hj hne_i hne_j
      have hpi := hb.post_lvls i hi1 (by omega) hne_i
      have hpj := hb.post_lvls j (by omega) hj hne_j
      rw [hb.lvl_eq, hpi, hpj]; exact hc1_sort i j hi1 hij hj
    · let cur_c2 : FullState := { cur with core := { cur.core with tmp := tmp_c2 } }
      ml_ld load_full_mark_ptr (s := cur_c2) hm_c2
      have hcore_c2 : FullOtfsCoreInv c F0 cur_c2 :=
        fullOtfsCoreInv_with_min_tmp hb.core htl_c2 hb.core.1.core_ok.tmp_len_le
          hb.core.1.core_ok.mrk_len hb.core.1.core_ok.min_stk_len
          hb.core.1.core_ok.min_clr_len_arr hb.core.1.core_ok.min_clr_len_le hb.core.1.scratch_ok
      have hflt_c2 : (tmp_c2.take kp_bv.toNat).filter (· ≠ 0xFFFFFFFF#32) =
          tmp_c2.take kp_bv.toNat := by
        rw [List.filter_eq_self]; intro x hx; rw [List.mem_iff_getElem] at hx
        obtain ⟨j, hj, rfl⟩ := hx; rw [List.length_take] at hj
        have hne := hne_c2 j (by omega); rw [List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hne
        exact decide_eq_true hne
      have hmin_c2 : FullMinMarkInv cur_c2.core
          (((tmp_c2.take kp_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
        rw [hflt_c2, htake_c2]
        exact ⟨hb.min_inv.mrk_dom, hb.min_inv.clr_cov, hb.min_inv.rem_sound⟩
      have hcv_c2 : cur_c2.core.cur_vars = s.core.cur_vars := hb.cv_eq
      have htl_c2' : cur_c2.core.tmp_len = s.core.tmp_len := hb.tl_eq
      rw [← hcv_c2, ← htl_c2']
      refine fid_min_shrink_clean_wp hcore_c2 hm_c2 hmin_c2
        (fun v hv => hb.no8 v (by rw [← hb.cv_eq]; exact hv))
        fun mrk' m' hml hab hmc hm' => ?_
      have htl_orig : kp_bv.toNat ≤ s.core.tmp_len := le_trans hkp_tl ht_tl
      have h0_fin : tmp_c2[0]? = s.core.tmp[0]? :=
        h0_c2.trans (hb.zero_eq.trans hc1_0eq)
      have hnd_fin : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
          (∀ k, 1 ≤ k → k < s.core.tmp_len →
            (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
            (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
          ((tmp_c2.take kp_bv.toNat).map fun x => x.toNat / 2).Nodup := fun hnd0 hne0 => by
        rw [htake_c2]; exact hb.nodup hnd0 hne0
      have hent_fin : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
          FullOtfsWitnessInv c F0 F_cur (fidMinShrinkRes s_c1 tmp_c2 kp_bv.toNat mrk' mstk_b mclr_b
            sstk_b 0 0#64 s_c1.scratch.conflicts (cur.scratch.learned_lits + kp_bv)
            (cur.scratch.min_removed +
              (BitVec.ofNat 64 s.core.tmp_len - kp_bv))).core ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((tmp_c2.take kp_bv.toNat).map BitVec.toNat)) := fun F_cur hw hE => by
        obtain ⟨hwc, hEc⟩ := hb.entails F_cur hw hE
        exact ⟨fullOtfsWitness_with_min hwc, by rw [htake_c2]; exact hEc⟩
      have hns_fin : ∀ j, 1 ≤ j → j < kp_bv.toNat →
          let l := (tmp_c2[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
          lv < s.core.cur_level ∧
          lv ≤ (s.core.lvl[(tmp_c2[kp_bv.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        intro j hj1 hj2; have hjv := hns_c2 j hj1 hj2
        have hle := hsort_c2 j (kp_bv.toNat - 1) hj1 (by omega) (by omega)
        rw [hb.cv_eq, hb.vals_eq, hb.lvl_eq, hb.clvl_eq] at hjv
        rw [hb.lvl_eq] at hle
        exact ⟨hjv.1, hjv.2.1, hjv.2.2.1, hjv.2.2.2.1, hle⟩
      have hsort_fin : ∀ i j, 1 ≤ i → i ≤ j → j < kp_bv.toNat →
          (s.core.lvl[(tmp_c2[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp_c2[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := fun i j hi1 hij hj =>
        by rw [← hb.lvl_eq]; exact hsort_c2 i j hi1 hij hj
      refine hpost tmp_c2 kp_bv.toNat mrk' mstk_b mclr_b sstk_b 0 0#64
        (cur.scratch.learned_lits + kp_bv)
        (cur.scratch.min_removed + (BitVec.ofNat 64 cur.core.tmp_len - kp_bv)) m'
        htl_c2 hml hb.core.1.core_ok.min_stk_len hb.core.1.core_ok.min_clr_len_arr (Nat.zero_le _)
        hb.core.1.scratch_ok.shrink_stk_len
        (fun v hv => (hab v (hcv_c2 ▸ hv)).trans (hb.mrk_above v hv))
        hmc hkp1 htl_orig h0_fin hnd_fin hns_fin hsort_fin hent_fin ?_
      have hst_eq :
          ({ core := { cur_c2.core with
               mrk := mrk', min_clr_len := 0, min_clr_full := 0#64, tmp_len := kp_bv.toNat },
             scratch := { cur_c2.scratch with
               min_removed := cur_c2.scratch.min_removed +
                 (BitVec.ofNat 64 cur_c2.core.tmp_len - kp_bv),
               learned_lits := cur_c2.scratch.learned_lits + kp_bv } } : FullState) =
          fidMinShrinkRes s_c1 tmp_c2 kp_bv.toNat mrk' mstk_b mclr_b sstk_b 0 0#64
            s_c1.scratch.conflicts (cur.scratch.learned_lits + kp_bv)
            (cur.scratch.min_removed + (BitVec.ofNat 64 cur.core.tmp_len - kp_bv)) := rfl
      exact hst_eq ▸ hm'

/-- Upstream Kissat `shrink=3` clause minimization/shrinking contract (`full_min_shrink_fid`):
skips Pass-1 literal-by-literal DFS and calls `full_shrink_blk_bool_m6` / `full_min_lit_dfs_m6`
directly, certifying canonical `FullM7SpecBridges.m7MinShrinkSpec`. -/
theorem full_min_shrink_fid_wp (Γ : Env)
    (hSt : ∀ args m Q X, m7SortTmpSpec args m Q X →
      Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hDfs : ∀ args m Q X, m6MinLitDfsSpec args m Q X →
      Γ "full_min_lit_dfs_m6" [i64, i32, .bool, .bool] [.bool] args m Q X)
    (hSb : ∀ args m Q X, m6ShrinkBlkBoolSpec args m Q X →
      Γ "full_shrink_blk_bool_m6" [i64, i64, i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, m7MinShrinkSpec args m Q X →
      Func.wp Γ full_min_shrink_fid_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur, s, R, ha, hlen0, hw0, hlm0, htl1, htl_cv, hnd0, hEnt0,
    htmp_vals, htmp_lvls, h0_lvl, hm, hQ⟩ := m7MinShrinkSpec_elim hspec
  obtain rfl : h = c.hdr := congrArg Prod.fst ha
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hlen0.core_ok.cur_vars_le
  have hmc0 : FullMarksClear s := hlm0.toFullMarksClear hlen0
  have hne0 : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := fun k hk1 hk2 => by
    have := (htmp_lvls k hk1 hk2).2; omega
  rw [Func.wp, fid_min_shrink_fid_body_eq]; ml_lets
  ml_ld load_full_cur_vars hm; ml_lets
  ml_ld load_full_tmp_len hm; ml_lets
  ml_ld load_full_conflicts hm; ml_lets
  ml_st m0, hm0 := store_full_conflicts (s.scratch.conflicts + 1) hm
  let s0 : FullState :=
    { s with scratch := { s.scratch with conflicts := s.scratch.conflicts + 1 } }
  have hs0_core : FullOtfsCoreInv c F0 s0 :=
    ⟨⟨hlen0.core_ok, fidMinShrinkScratchOk hlen0.scratch_ok hlen0.scratch_ok.shrink_stk_len⟩,
     F_cur, hw0⟩
  refine wp_join_group (ts := []) (fun () mq => s.core.tmp_len = 1 ∧ mq = m0)
    (fun _ ⟨⟩ mq ⟨htl_eq1, rfl⟩ => by
      rw [Blocks.get_here]
      ml_ld load_full_learned_lits (s := s0) hm0; ml_lets
      ml_st m_e, hm_e := store_full_learned_lits (s := s0)
        (s0.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len) hm0
      rw [wp]
      have hce_eq :
          ({ s with
              core := { s.core with
                tmp := s.core.tmp, tmp_len := s.core.tmp_len, mrk := s.core.mrk,
                min_stk := s.core.min_stk, min_clr := s.core.min_clr,
                min_clr_len := s.core.min_clr_len, min_clr_full := s.core.min_clr_full },
              scratch := { s.scratch with
                conflicts := s.scratch.conflicts + 1,
                learned_lits := s.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len,
                min_removed := s.scratch.min_removed,
                shrink_stk := s.scratch.shrink_stk,
                wsort := s.scratch.wsort } } : FullState) =
          { s0 with scratch := { s0.scratch with
            learned_lits := s0.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len } } := rfl
      exact hQ s.core.tmp s.core.tmp_len s.core.mrk s.core.min_stk s.core.min_clr
        s.core.min_clr_len s.core.min_clr_full (s.scratch.conflicts + 1)
        (s.scratch.learned_lits + BitVec.ofNat 64 s.core.tmp_len) s.scratch.min_removed
        s.scratch.shrink_stk s.scratch.wsort m_e
        ⟨hlen0.core_ok, fidMinShrinkScratchOk hlen0.scratch_ok hlen0.scratch_ok.shrink_stk_len⟩
        hw0 hlm0 htl1 (le_refl _) rfl hnd0 (fun j hj1 hj2 => by omega) hEnt0 (fun _ => rfl)
        (hce_eq ▸ hm_e)) ?_
  rintro J_early hJ_early; ml_lets; ml_jnz
  refine ⟨fun hle1 => ?_, fun hgt1 => ?_⟩
  · have htl_eq1 : s.core.tmp_len = 1 := by c0_cond hle1; bv_omega
    ml_lets; exact hJ_early () m0 ⟨htl_eq1, rfl⟩
  · c0_cond hgt1; have h2lt : 2 ≤ s.core.tmp_len := by bv_omega
    ml_lets; ml_jnz; refine ⟨fun hoob => by exfalso; c0_cond hoob; bv_omega, fun _ => ?_⟩
    ml_lets; apply wp_call_of_spec; apply hSt; dsimp only [vals, Arg.val]
    refine m7SortTmpSpec_of hs0_core.1 (by dsimp only [s0]; omega)
      (fun k _ hk2 => by dsimp only [s0] at hk2 ⊢; have := (htmp_vals k (by omega)).1; omega)
      hm0
      (fun tmp1 wsort1 m1 hlen1 ht1_len hw1_16 ht1_perm ht1_0 ht1_r ht1_l _ ht1_sort _ hm1 => ?_)
    obtain ⟨hkeep_eq, hEnt1, htmp1_vals, htmp1_lvls⟩ := fidMinShrinkPostSort
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
    clear hm hm0 hm1 m1 hm2 m2 hs0_core hkeep_eq
    dsimp only [fidMinMarkInitExpr]
    refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) mi =>
        n = s.core.tmp_len - i_bv.toNat ∧ i_bv.toNat ≤ s.core.tmp_len ∧
        ∃ (mrk_i : List (BitVec 8)) (mclr_i : List (BitVec 32)) (mcl_i : Nat) (mcf_i : BitVec 64),
        let cur : FullState := { s2 with core := { s2.core with
          mrk := mrk_i, min_clr := mclr_i, min_clr_len := mcl_i, min_clr_full := mcf_i } }
        mrk_i.length = c.max_vars ∧ mclr_i.length = c.max_vars ∧ mcl_i ≤ c.max_vars ∧
        (∀ v, s.core.cur_vars ≤ v → mrk_i[v]? = s.core.mrk[v]?) ∧
        FullMinMarkInv cur.core keep0 ∧
        (∀ v < s.core.cur_vars, (mrk_i[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
        (∀ j < i_bv.toNat, (mrk_i[(tmp1[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (FullMem c cur ⋆ R) mi) ?_
      (fun Jm hJm => by
        ml_lets; have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
        exact hJm (s.core.tmp_len - 0) (0#64, ()) m3
          ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s2.core.mrk, s2.core.min_clr,
           s2.core.min_clr_len, s2.core.min_clr_full, hs2_core.1.core_ok.mrk_len,
           hs2_core.1.core_ok.min_clr_len_arr, hs2_core.1.core_ok.min_clr_len_le, fun _ _ => rfl,
           hmin2_init, fun v hv => by dsimp only [s2, s1, s0]; rw [hmc0 v hv]; decide,
           fun _ h => by rw [h0v] at h; omega, hm3⟩)
    rintro Jm n ⟨i_bv, ⟨⟩⟩ mi hJm
      ⟨rfl, hile, mrk_i, mclr_i, mcl_i, mcf_i, hmrkl, hmclrl, hmcll, hab_i, hmin_i, hno8_i,
        hmark_i, hm_i⟩
    let cur : FullState := { s2 with core := { s2.core with
      mrk := mrk_i, min_clr := mclr_i, min_clr_len := mcl_i, min_clr_full := mcf_i } }
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · c0_cond hlt; have hix : i_bv.toNat < s.core.tmp_len := by bv_omega
      have hi_tl : i_bv.toNat < cur.core.tmp.length := by dsimp only [cur, s2]; rw [ht1_len]; omega
      ml_ld c0_load_full_tmp (s := cur) (i := i_bv) hi_tl hm_i
      let lit_i := tmp1[i_bv.toNat]'(by rw [ht1_len]; omega)
      have hl_i := htmp1_vals i_bv.toNat hix
      rw [List.getElem?_eq_getElem (by rw [ht1_len]; omega), Option.getD_some] at hl_i
      have hlit_lt : lit_i.toNat < 2 * s.core.cur_vars := hl_i.2.1
      have hv_i : (lit_i >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr_1]; omega
      have hv_i' : lit_i.toNat / 2 < s.core.cur_vars := by omega
      have hcore_i : FullOtfsCoreInv c F0 cur :=
        fullOtfsCoreInv_with_min hs2_core hmrkl hs2_core.1.core_ok.min_stk_len hmclrl hmcll
      ml_lets; apply wp_call_of_spec
      refine hMm _ _ _ _ (fidSpecsMinMarkSpecOfFull (fullMinMarkSpec_step hcore_i.1 hm_i
        (lit_i >>> 1) hv_i ((2 : BitVec 32).setWidth 8) fun m_n hm_n => ?_))
      have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl; rw [h2_eq, bv32_lshr_1] at hm_n
      let nxt := fullMinMarkStepState cur (lit_i.toNat / 2) 2#8
      have hnxt_eq : { s2 with core := { s2.core with
          mrk := nxt.core.mrk, min_clr := nxt.core.min_clr,
          min_clr_len := nxt.core.min_clr_len, min_clr_full := nxt.core.min_clr_full } } = nxt := by
        dsimp only [nxt, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, cur]
        split <;> rfl
      have hlen_n := fullMinMarkStepState_lengths hcore_i.1 (lit_i.toNat / 2) 2#8
      have hmin_n := fullMinMarkInv_step_keep hcore_i hmin_i hlit_lt hl_i.2.2.2 hl_i.2.2.1
        (hno8_i _ hv_i')
      obtain ⟨hbit8_n, hmono2_n⟩ :=
        fullMinMarkStepState_bit8_mono2 hcore_i.1 hv_i' (Or.inl rfl) (hno8_i _ hv_i')
      have hab_n : ∀ v, s.core.cur_vars ≤ v → nxt.core.mrk[v]? = s.core.mrk[v]? := fun v hv =>
        (fullMinMarkStepState_mrk_above (s := cur) hv_i' 2#8 v hv).trans (hab_i v hv)
      have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := by bv_omega; ml_lets
      refine hJm (s.core.tmp_len - (i_bv + 1).toNat) (i_bv + 1, ()) m_n (by omega)
        ⟨rfl, by omega, nxt.core.mrk, nxt.core.min_clr, nxt.core.min_clr_len, nxt.core.min_clr_full,
         hlen_n.core_ok.mrk_len, hlen_n.core_ok.min_clr_len_arr, hlen_n.core_ok.min_clr_len_le,
         hab_n, by rw [hnxt_eq]; exact hmin_n,
         fun v hv => by rw [hbit8_n v hv]; exact hno8_i v hv, fun j hj => ?_,
         by rw [hnxt_eq]; exact hm_n⟩
      rw [hi1] at hj; by_cases hje : j = i_bv.toNat
      · subst j
        have hti : tmp1[i_bv.toNat]?.getD 0#32 = lit_i := by
          rw [List.getElem?_eq_getElem (by rw [ht1_len]; omega), Option.getD_some]
        rw [hti]; dsimp only [nxt, fullMinMarkStepState, fullMinMarkStepCore]; split
        · rename_i hc; exact hc.resolve_left (Nat.not_le.mpr hv_i')
        · dsimp only [fullMinMarkCore]
          rw [List.getElem?_set_self (hmrkl ▸ lt_of_lt_of_le hv_i' hcv), Option.getD_some]
          exact bv8_and2_of_or2 _
      · have hjlt : (tmp1[j]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
          have := (htmp1_vals j (by omega)).2.1; omega
        exact hmono2_n _ hjlt (hmark_i j (by omega))
    · c0_cond hge; have hie : i_bv.toNat = s.core.tmp_len := by bv_omega
      have hcore_i : FullOtfsCoreInv c F0 cur :=
        fullOtfsCoreInv_with_min hs2_core hmrkl hs2_core.1.core_ok.min_stk_len hmclrl hmcll
      have hflt_i : (tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32) =
          tmp1.take s.core.tmp_len :=
        fidListFilterNeEqSelf (by rw [ht1_len]; omega) fun j hj => by
          have := (htmp1_vals j hj).2.1; omega
      have htl_bv : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hc1_inv : FidBlkLoopInv c F0 s cur s.core.tmp_len 1 cur :=
        ⟨hcore_i, hmin_i,
         fun F_c hw hE => ⟨fullOtfsWitness_with_min hw, hEnt1 F_c hE⟩,
         fun hnd _ => by
           dsimp only [cur, s2, s1, s0]
           rw [hflt_i]
           exact nodup_take_map_div2_of_perm ht1_perm hnd,
         hab_i, hno8_i, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl,
         fun h1 _ => absurd h1 (by omega),
         fun k hk _ => let hkv := htmp1_vals k hk; ⟨hkv.2.1, hkv.2.2.1, hmark_i k (hie ▸ hk)⟩,
         fun _ _ _ _ => rfl⟩
      have h0eq : cur.core.tmp[0]? = s.core.tmp[0]? := ht1_0 htl1
      have h0_ne : cur.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := (htmp1_vals 0 htl1).1
      have h0lv :
          (s.core.lvl[(cur.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s.core.cur_level := by
        rw [h0eq]; exact h0_lvl
      refine fid_min_shrink_blk_loop_wp hDfs hSb htl_bv htl1 htl_cv (le_refl _) hc1_inv
        h0eq h0_ne h0lv (fun k hk => (htmp1_vals k hk).1)
        (fun k hk1 hk2 => htmp1_lvls k hk1 hk2) ht1_sort hm_i
        fun tmp' tl' mrk' mstk' mclr' sstk' mcl' mcf' llits' mrem' m'
          htlf hmlf hmstkf hmclrf hmclf hsstkf habf hmcf h1f htl_lef h0f hndf hnsf _
          hentf hm' => ?_
      let sf := { s with
        core := { s.core with tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk',
                              min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' },
        scratch := { s.scratch with conflicts := s.scratch.conflicts + 1,
                                    learned_lits := llits', min_removed := mrem',
                                    shrink_stk := sstk', wsort := wsort1 } }
      have hlen_f : sf.LengthsOk c :=
        ⟨{ hlen0.core_ok with
            tmp_len_arr := htlf, tmp_len_le := le_trans (le_trans htl_lef htl_cv) hcv,
            mrk_len := hmlf, min_stk_len := hmstkf, min_clr_len_arr := hmclrf,
            min_clr_len_le := hmclf },
         fidMinShrinkScratchOk hlen1.scratch_ok hsstkf⟩
      obtain ⟨hw', hEc'⟩ := hentf F_cur hw0 hEnt0
      have hlm' : FullLitMarksClear c sf := fullLitMarksClear_of_clear hlm0 rfl hmcf habf rfl
      exact hQ tmp' tl' mrk' mstk' mclr' mcl' mcf' (s.scratch.conflicts + 1) llits' mrem'
        sstk' wsort1 m' hlen_f hw' hlm' h1f htl_lef h0f (hndf hnd0 hne0) hnsf
        hEc' hw1_16 (by simpa [sf, fidMinShrinkRes, cur, s2, s1, s0] using hm')

end MinShrinkProof

end LeanQbe.T.Examples.Kissat.FullM7FidelityCore
