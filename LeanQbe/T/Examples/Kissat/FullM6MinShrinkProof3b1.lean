module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3a
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Minimization/Shrink Proof Shard 3b1 (`m6AnaFailedLitSpec` & Helpers)

Defines `m6AnaFailedLitSpec`, `FailedStateOk`, `FailedMarkedCut`, `flIdxs`, `flLits`, and proves
the pure CNF resolution, trail implication, marking, assignment, and arena indexing lemmas used
by `FullM6MinShrinkProof3b.lean` (`full_ana_failed_lit_m6_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullLearnAnaSpecs
open LeanQbe.T.Examples.Kissat.Full.FullLearnAnaHelpers
open Kraken.Bedrock2.Test

/-! ## 1. Specification & Bridge for `full_ana_failed_lit_m6` -/

/-- Level-1 failed-literal / multi-UIP conflict analysis contract. -/
def m6AnaFailedLitSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ Full.FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧
    Full.FullConflictOkCut F_cur cut s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem m6AnaFailedLitSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcut : Full.FullCutInvW c F0 F_cur cut s) (hcl : 0 < s.core.cur_level)
    (hc : Full.FullConflictOkCut F_cur cut s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m6AnaFailedLitSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, cut, s, R, rfl, hcut, hcl, hc, hm, hQ⟩

theorem m6AnaFailedLitSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6AnaFailedLitSpec xs m Q X) : m6AnaFailedLitSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem m6AnaFailedLitSpec_elim {P : Prop} {a : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hspec : m6AnaFailedLitSpec a m Q X)
    (hK : ∀ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
      (s : FullState) (R : Mem 64 → Prop),
      a = (c.hdr, ()) → Full.FullCutInvW c F0 F_cur cut s → 0 < s.core.cur_level →
      Full.FullConflictOkCut F_cur cut s → (FullMem c s ⋆ R) m →
      (∀ r s' m',
        s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
        (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
        (r = 1#64 → Full.FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m') → P) : P := by
  rcases a with ⟨h0, ⟨⟩⟩
  rcases hspec with ⟨c, F0, F_cur, cut, s, R, rfl, hcut, hcl, hc, hm, hQ⟩
  exact hK c F0 F_cur cut s R rfl hcut hcl hc hm hQ

/-! ## 2. Arithmetic, CNF Resolution, Mark/Trail, and Arena Helpers -/

theorem fl_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

theorem fl_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 :=
  bv32_xor_1 x

theorem fl_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

theorem fl_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  simpa [litVar, litNeg] using litVar_litNeg l

theorem fl_i8_slt0_neg_iff {v : BitVec 8}
    (hv : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : BitVec.slt (v.signExtend 32) ((0#32 : BitVec 32).truncate 8 |>.signExtend 32)) :
    v = 0xFF#8 := by
  rcases hv with rfl | rfl | rfl <;> first | rfl | exact absurd h (by decide)

theorem fl_i8_pos_of_not_sle {v : BitVec 8}
    (hv : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : ¬ BitVec.sle (v.signExtend 32) ((0#32 : BitVec 32).truncate 8 |>.signExtend 32)) :
    v = 1#8 := by
  rcases hv with rfl | rfl | rfl <;> first | rfl | exact absurd (by decide) h

private theorem fl_bv8_zext_eq0 {x : BitVec 8} (h : BitVec.setWidth 32 x = 0#32) : x = 0#8 := by
  revert x h; decide

private theorem fl_bv8_zext_ne0 {x : BitVec 8} (h : BitVec.setWidth 32 x ≠ 0#32) : x ≠ 0#8 :=
  fun hx => h (by subst hx; rfl)

theorem fl_i8_sext32_eq0_iff {v : BitVec 8} :
    v.signExtend 32 = ((0#32 : BitVec 32).truncate 8 |>.signExtend 32) ↔ v = 0#8 := by
  revert v; decide

theorem fl_bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem fl_bv64_sub1_toNat {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx := x.isLt; bv_omega

theorem fl_bv32_add1_toNat {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem fl_nodup_getElem_inj {α : Type} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (heq : xs[i] = xs[j]) : i = j := by
  have hp := List.pairwise_iff_getElem.mp hnd
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact absurd heq (hp i j hi hj h)
  · rfl
  · exact absurd heq.symm (hp j i hj hi h)

private theorem fl_nodup_of_getElem_ne {α : Type} :
    ∀ {xs : List α},
      (∀ i j (hi : i < xs.length) (hj : j < xs.length), i < j → xs[i] ≠ xs[j]) → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, fl_nodup_of_getElem_ne fun i j hi hj hij =>
      h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ hij)⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    exact h 0 (k + 1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hk) (Nat.zero_lt_succ _) hget.symm

private theorem fl_nodup_map_take_append {xs : List (BitVec 32)} {n : Nat} {v : BitVec 32}
    (hn : n < xs.length) (hnd : ((xs.take n).map BitVec.toNat).Nodup)
    (hmiss : ∀ k < n, (xs[k]?.getD 0#32).toNat ≠ v.toNat) :
    (((xs.set n v).take (n + 1)).map BitVec.toNat).Nodup := by
  refine fl_nodup_of_getElem_ne fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_take, List.length_set] at hi hj
  simp only [List.getElem_map, List.getElem_take]
  have hi_n : i < n := by omega
  rw [List.getElem_set_ne (by omega)]
  by_cases hj_n : j = n
  · subst hj_n; rw [List.getElem_set_self (by rw [List.length_set]; exact hn)]
    have hm := hmiss i hi_n
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hm
  · rw [List.getElem_set_ne (by omega)]
    have hi_t : i < ((xs.take n).map BitVec.toNat).length := by
      simp only [List.length_map, List.length_take]; omega
    have hj_t : j < ((xs.take n).map BitVec.toNat).length := by
      simp only [List.length_map, List.length_take]; omega
    intro heq
    have hne := List.pairwise_iff_getElem.mp hnd i j hi_t hj_t hij
    simp only [List.getElem_map, List.getElem_take] at hne
    exact hne heq

private theorem fl_nodup_mcl_lt_cv {c : FullCfg} {s : FullState}
    (hcov : Full.FullAnaMarksCov c s) (hwsl : s.core.min_clr_len ≤ s.scratch.work_stk1.length)
    {v : Nat} (hv : v < s.core.cur_vars)
    (hmrk0 : s.core.mrk[v]?.getD 0#8 = 0#8) : s.core.min_clr_len < s.core.cur_vars :=
  inj_lt_of_missing (fun i => (s.scratch.work_stk1[i]?.getD 0#32).toNat)
    (fun i j hi hj heq => by
      have hi_t : i < ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat).length := by
        rw [List.length_map, List.length_take]; omega
      have hj_t : j < ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat).length := by
        rw [List.length_map, List.length_take]; omega
      have hget : ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat)[i]'hi_t =
          ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat)[j]'hj_t := by
        simp only [List.getElem_map, List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
          List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
        exact heq
      exact fl_nodup_getElem_inj hcov.2.1 hi_t hj_t hget)
    (fun i hi => (hcov.2.2.1 i hi).1) hv
    fun i hi heq => (hcov.2.2.1 i hi).2 (by rwa [heq])

private theorem fl_sat_false_of_xor1 {α : Nat → Bool} {q : Nat}
    (h : (cnfClause [q ^^^ 1]).Sat α) : ¬ (cnfClause [q]).Sat α :=
  (sat_cnfClause_litNeg_iff α q).mp h

theorem fl_unsat_of_unit_pair {F_cur : List (List Nat)} {u : Nat}
    (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u]))
    (h2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u ^^^ 1])) :
    (cnfOfClauses F_cur).Unsat := by
  refine unsat_of_entails_nil (CNF.entails_clause_def.mpr fun α hα => ?_)
  exact absurd (CNF.entails_clause_def.mp h1 α hα)
    (fl_sat_false_of_xor1 (CNF.entails_clause_def.mp h2 α hα))

private theorem fl_sat_taut {α : Nat → Bool} (x : Nat) : (cnfClause [x ^^^ 1, x]).Sat α := by
  rw [clause_sat_cnfClause_iff]
  by_cases hx : α (litVar x) = !(litSign x)
  · exact ⟨x, by simp, hx⟩
  · have hneg := (sat_cnfClause_litNeg_iff α x).mpr (by rwa [sat_cnfClause_singleton])
    exact ⟨x ^^^ 1, by simp, (sat_cnfClause_singleton α (x ^^^ 1)).mp hneg⟩

private theorem fl_sat_not_pair {α : Nat → Bool} {a b : Nat}
    (h1 : (cnfClause [a, b]).Sat α) (ha : ¬ (cnfClause [a]).Sat α) :
    (cnfClause [b]).Sat α := by
  obtain ⟨x, hx, hxt⟩ := (clause_sat_cnfClause_iff α [a, b]).mp h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact absurd ((sat_cnfClause_singleton α x).mpr hxt) ha
  · exact (sat_cnfClause_singleton α x).mpr hxt

private theorem fl_sat_not_pair_snd {α : Nat → Bool} {a b : Nat}
    (h1 : (cnfClause [a, b]).Sat α) (hb : ¬ (cnfClause [b]).Sat α) :
    (cnfClause [a]).Sat α := by
  obtain ⟨x, hx, hxt⟩ := (clause_sat_cnfClause_iff α [a, b]).mp h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact (sat_cnfClause_singleton α x).mpr hxt
  · exact absurd ((sat_cnfClause_singleton α x).mpr hxt) hb

private theorem fl_entails_weakening {F : CNF Nat} {a b : Nat}
    (h : F.EntailsClause (cnfClause [b])) : F.EntailsClause (cnfClause [a, b]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have hb := (sat_cnfClause_singleton α b).mp (CNF.entails_clause_def.mp h α hα)
  exact (clause_sat_cnfClause_iff α [a, b]).mpr ⟨b, by simp, hb⟩

theorem failedLit_trail_imp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : Full.FullWitnessCutInv c F0 F_cur cut k)
    (hcl1 : k.cur_level = 1) {failed : Nat}
    (hval : k.vals[failed]?.getD 0#8 = 1#8) (hf_lt : failed < 2 * k.cur_vars)
    (hlvl : (k.lvl[failed / 2]?.getD 0#32).toNat = 1)
    (hrsn : k.rsns[failed / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    ∀ j < cut, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [failed ^^^ 1, (k.trl[j]?.getD 0#32).toNat]) := by
  obtain ⟨idx_d, hid_lt, hid_eq⟩ := (hw.vals_true_iff failed hf_lt).mp hval
  intro j
  refine @Nat.strongRecOn (fun j => j < cut → (cnfOfClauses F_cur).EntailsClause
    (cnfClause [failed ^^^ 1, (k.trl[j]?.getD 0#32).toNat])) j fun j ih hj => by
    have hj_te : j < k.trail_end := Nat.lt_of_lt_of_le hj hw.cut_le
    let p := (k.trl[j]?.getD 0#32).toNat
    have hp_lvl_le : (k.lvl[p / 2]?.getD 0#32).toNat ≤ 1 := by
      rw [← hcl1]; exact hw.lvl_le j hj_te
    rcases Nat.lt_or_eq_of_le hp_lvl_le with hp0 | hp1
    · dsimp only [p] at hp0
      exact fl_entails_weakening (hw.level0_sound j hj_te (by omega))
    · have hd_le : idx_d ≤ j := hw.dec_earliest j idx_d hj_te hid_lt
        (by rw [hid_eq, hp1, hlvl]) (by rw [hid_eq]; exact ⟨by omega, hrsn⟩)
      rcases Nat.eq_or_lt_of_le hd_le with rfl | hgt
      · rw [CNF.entails_clause_def]; intro α _
        simpa only [p, hid_eq] using fl_sat_taut (α := α) failed
      · have hrsn_ne : k.rsns[p / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
          intro hnil
          dsimp only [p] at hp1
          have hrev := hw.dec_earliest idx_d j hid_lt hj_te
            (by rw [hid_eq, hlvl, hp1]) ⟨by omega, hnil⟩
          omega
        have hri := hw.reason_inv_cut j hj hrsn_ne
        dsimp only at hri
        by_cases hbin : (k.rsns[p / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hri
          obtain ⟨_, hent, m, hm_lt, hm_eq, _⟩ := hri
          have ihm := ih m hm_lt (by omega)
          rw [CNF.entails_clause_def] at hent ihm ⊢
          intro α hα
          have h_imp := ihm α hα
          have h_rsn := hent α hα
          by_cases hnf : (cnfClause [failed ^^^ 1]).Sat α
          · exact (clause_sat_cnfClause_iff α [failed ^^^ 1, p]).mpr
              ⟨failed ^^^ 1, by simp, (sat_cnfClause_singleton α (failed ^^^ 1)).mp hnf⟩
          · have hot_neg : (cnfClause [(k.rsns[p / 2]?.getD 0xFFFFFFFF#32 &&&
                0x7FFFFFFF#32).toNat ^^^ 1]).Sat α := by
              have hsat := fl_sat_not_pair h_imp hnf
              rwa [← hm_eq]
            have hot_f := fl_sat_false_of_xor1 hot_neg
            have hp_sat := fl_sat_not_pair_snd h_rsn hot_f
            exact (clause_sat_cnfClause_iff α [failed ^^^ 1, p]).mpr
              ⟨p, by simp, (sat_cnfClause_singleton α p).mp hp_sat⟩
        · rw [ite_eq_right hbin] at hri
          obtain ⟨href, hng, hall⟩ := hri
          have hent := hw.arena.entails _ href hng
          rw [CNF.entails_clause_def] at hent ⊢
          intro α hα
          by_cases hnf : (cnfClause [failed ^^^ 1]).Sat α
          · exact (clause_sat_cnfClause_iff α [failed ^^^ 1, p]).mpr
              ⟨failed ^^^ 1, by simp, (sat_cnfClause_singleton α (failed ^^^ 1)).mp hnf⟩
          · obtain ⟨q, hqm, hqt⟩ :=
              (clause_sat_cnfClause_iff α (Full.fullArenaClauseLitsCore k _)).mp (hent α hα)
            rcases hall q hqm with rfl | ⟨m, hm_lt, hm_eq, _⟩
            · exact (clause_sat_cnfClause_iff α [failed ^^^ 1, p]).mpr ⟨p, by simp, hqt⟩
            · have ihm := ih m hm_lt (by omega)
              have h_imp := CNF.entails_clause_def.mp ihm α hα
              have hq_neg : (cnfClause [q ^^^ 1]).Sat α := by
                have hsat := fl_sat_not_pair h_imp hnf
                rwa [← hm_eq]
              exact absurd ((sat_cnfClause_singleton α q).mpr hqt)
                (fl_sat_false_of_xor1 hq_neg)

private theorem fl_falsified_not_failed_false {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : Full.FullWitnessCutInv c F0 F_cur cut k) (hcl1 : k.cur_level = 1) {failed l : Nat}
    (himp : ∀ j < cut, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [failed ^^^ 1, (k.trl[j]?.getD 0#32).toNat]))
    (hl : l < 2 * k.cur_vars) (hfl : k.vals[l]?.getD 0#8 = 0xFF#8)
    (hcut_or0 : (k.lvl[l / 2]?.getD 0#32).toNat = k.cur_level →
      ∃ m < cut, (k.trl[m]?.getD 0#32).toNat = l ^^^ 1)
    {α : Nat → Bool} (hα : (cnfOfClauses F_cur).Sat α)
    (hnf : ¬ (cnfClause [failed ^^^ 1]).Sat α) :
    ¬ (cnfClause [l]).Sat α := by
  obtain ⟨m_t, hm_te, hm_teq⟩ := (hw.vals_false_iff l hl).mp hfl
  have hm_lv_le := hw.lvl_le m_t hm_te
  rcases Nat.eq_zero_or_pos (k.lvl[(k.trl[m_t]?.getD 0#32).toNat / 2]?.getD 0#32).toNat with
    hz | hp
  · have hs := hw.level0_sound m_t hm_te hz
    rw [hm_teq] at hs
    exact fl_sat_false_of_xor1 (CNF.entails_clause_def.mp hs α hα)
  · have hlv1 : (k.lvl[l / 2]?.getD 0#32).toNat = k.cur_level := by
      rw [hm_teq, fl_xor1_div2] at hm_lv_le hp; omega
    obtain ⟨m, hm_cut, hm_eq⟩ := hcut_or0 hlv1
    have hcl := fl_sat_not_pair (CNF.entails_clause_def.mp (himp m hm_cut) α hα) hnf
    rw [hm_eq] at hcl
    exact fl_sat_false_of_xor1 hcl

theorem failedLit_not_failed_of_confl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (hw : Full.FullWitnessCutInv c F0 F_cur cut s.core) (hcl1 : s.core.cur_level = 1)
    (hc : Full.FullConflictOkCut F_cur cut s) {failed : Nat}
    (himp : ∀ j < cut, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [failed ^^^ 1, (s.core.trl[j]?.getD 0#32).toNat])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [failed ^^^ 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  by_cases hnf : (cnfClause [failed ^^^ 1]).Sat α
  · exact hnf
  · exfalso
    rcases hc with ⟨hcw, hcc⟩
    by_cases hct : s.core.confl_type = 1#64
    · rw [ite_eq_left hct] at hcc
      rcases hcw with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨hne, _⟩
      · obtain ⟨l, hl_mem, hl_t⟩ :=
          (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hent α hα)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl_mem
        rcases hl_mem with rfl | rfl
        · exact fl_falsified_not_failed_false hw hcl1 himp h0lt hf0 hcc.1 hα hnf
            ((sat_cnfClause_singleton α _).mpr hl_t)
        · exact fl_falsified_not_failed_false hw hcl1 himp h1lt hf1 hcc.2 hα hnf
            ((sat_cnfClause_singleton α _).mpr hl_t)
      · exact absurd (hct.symm.trans hne) (by decide)
    · rw [ite_eq_right hct] at hcc
      rcases hcw with ⟨h1, _⟩ | ⟨_, href, hng, hfals⟩
      · exact absurd h1 hct
      · obtain ⟨l, hl_mem, hl_t⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp (hw.arena.entails _ href hng) α hα)
        have hlt := hw.arena.lits_lt _ href hng l hl_mem
        exact fl_falsified_not_failed_false hw hcl1 himp hlt (hfals l hl_mem)
          (hcc l hl_mem) hα hnf ((sat_cnfClause_singleton α _).mpr hl_t)

def flIdxs (k : FullCoreState) (mrk : List (BitVec 8)) (t : Nat) : List Nat :=
  (List.range t).filter fun j =>
    decide (mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)

def flLits (k : FullCoreState) (mrk : List (BitVec 8)) (t : Nat) : List Nat :=
  (flIdxs k mrk t).map fun j => (k.trl[j]?.getD 0#32).toNat ^^^ 1

def FailedMarkedCut (s0 : FullState) (mrk : List (BitVec 8)) (cut : Nat) : Prop :=
  ∀ v < s0.core.cur_vars, mrk[v]?.getD 0#8 ≠ 0#8 →
    (s0.core.lvl[v]?.getD 0#32).toNat = 1 ∧
    ∃ m < cut, (s0.core.trl[m]?.getD 0#32).toNat / 2 = v

theorem fl_mb_empty {s0 : FullState} {mrk : List (BitVec 8)} {cut : Nat}
    (hz : ∀ v < s0.core.cur_vars, mrk[v]?.getD 0#8 = 0#8) : FailedMarkedCut s0 mrk cut :=
  fun v hv hnz => absurd (hz v hv) hnz

theorem fl_mb_get {s0 : FullState} {mrk : List (BitVec 8)} {cut : Nat}
    (h : FailedMarkedCut s0 mrk cut) {v : Nat} (hv : v < s0.core.cur_vars)
    (hnz : mrk[v]?.getD 0#8 ≠ 0#8) :
    (s0.core.lvl[v]?.getD 0#32).toNat = 1 ∧
    ∃ m < cut, (s0.core.trl[m]?.getD 0#32).toNat / 2 = v :=
  h v hv hnz

theorem flIdxs_length_le {k : FullCoreState} {mrk : List (BitVec 8)} {t : Nat} :
    (flIdxs k mrk t).length ≤ t := by
  unfold flIdxs
  exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_range]; exact Nat.le_refl _)

theorem flIdxs_eq_nil_of_zero {k : FullCoreState} {mrk : List (BitVec 8)} {t : Nat}
    (hz : ∀ j < t, mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    flIdxs k mrk t = [] := by
  unfold flIdxs; rw [List.filter_eq_nil_iff]
  intro j hj; rw [List.mem_range] at hj; simp [hz j hj]

theorem flLits_congr_idxs {k : FullCoreState} {mrk : List (BitVec 8)} {t1 t2 : Nat}
    (h : flIdxs k mrk t1 = flIdxs k mrk t2) : flLits k mrk t1 = flLits k mrk t2 := by
  unfold flLits; rw [h]

theorem flIdxs_eq_of_unmarked_above {k : FullCoreState} {mrk : List (BitVec 8)}
    {t' t : Nat} (hle : t' ≤ t)
    (hun : ∀ j, t' ≤ j → j < t → mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    flIdxs k mrk t = flIdxs k mrk t' := by
  induction t with
  | zero =>
    have : t' = 0 := by omega
    subst this; rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · rfl
    · have hm := hun m (by omega) (Nat.lt_succ_self m)
      have hsub : flIdxs k mrk (m + 1) = flIdxs k mrk m := by
        simp [flIdxs, List.range_succ, List.filter_append, hm]
      exact hsub.trans (ih (by omega) fun j hj1 hj2 => hun j hj1 (by omega))

theorem flIdxs_succ_marked {k : FullCoreState} {mrk : List (BitVec 8)} {t' : Nat}
    (hm : mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    flIdxs k mrk (t' + 1) = flIdxs k mrk t' ++ [t'] := by
  simp [flIdxs, List.range_succ, List.filter_append, hm]

private theorem flLits_succ_marked {k : FullCoreState} {mrk : List (BitVec 8)} {t' : Nat}
    (hm : mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    flLits k mrk (t' + 1) = flLits k mrk t' ++ [(k.trl[t']?.getD 0#32).toNat ^^^ 1] := by
  unfold flLits; rw [flIdxs_succ_marked hm, List.map_append, List.map_singleton]

theorem flLits_eq_singleton_of_len1 {k : FullCoreState} {mrk : List (BitVec 8)} {t' : Nat}
    (hm : mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hlen1 : (flIdxs k mrk (t' + 1)).length = 1) :
    flLits k mrk (t' + 1) = [(k.trl[t']?.getD 0#32).toNat ^^^ 1] := by
  rw [flIdxs_succ_marked hm, List.length_append, List.length_singleton] at hlen1
  have hnil : flIdxs k mrk t' = [] := List.eq_nil_of_length_eq_zero (by omega)
  unfold flLits; rw [flIdxs_succ_marked hm, hnil, List.nil_append, List.map_singleton]

private theorem flIdxs_set_of_ne {k : FullCoreState} {mrk : List (BitVec 8)} {t ov : Nat}
    (hne : ∀ j < t, (k.trl[j]?.getD 0#32).toNat / 2 ≠ ov) :
    flIdxs k (mrk.set ov 1#8) t = flIdxs k mrk t := by
  unfold flIdxs
  refine List.filter_congr fun j hj => ?_
  rw [List.mem_range] at hj
  rw [List.getElem?_set_ne (Ne.symm (hne j hj))]

private theorem flIdxs_set_marked {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : Full.FullWitnessCutInv c F0 F_cur cut k)
    {mrk : List (BitVec 8)} {t ov : Nat} (ht : t ≤ k.trail_end) (hov_len : ov < mrk.length)
    (hmrk0 : mrk[ov]?.getD 0#8 = 0#8)
    (hm : ∃ m < t, (k.trl[m]?.getD 0#32).toNat / 2 = ov) :
    (flIdxs k (mrk.set ov 1#8) t).length = (flIdxs k mrk t).length + 1 ∧
    (∀ j ∈ flIdxs k mrk t, j ∈ flIdxs k (mrk.set ov 1#8) t) ∧
    (∀ l ∈ flLits k mrk t, l ∈ flLits k (mrk.set ov 1#8) t) ∧
    (∀ m < t, (k.trl[m]?.getD 0#32).toNat / 2 = ov →
      ((k.trl[m]?.getD 0#32).toNat ^^^ 1) ∈ flLits k (mrk.set ov 1#8) t) := by
  have hmem_pres : ∀ {mrk : List (BitVec 8)} {t : Nat}, ov < mrk.length →
      ∀ j ∈ flIdxs k mrk t, j ∈ flIdxs k (mrk.set ov 1#8) t := by
    intro mrk t hml j hj
    unfold flIdxs at hj ⊢
    rw [List.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    by_cases heq : (k.trl[j]?.getD 0#32).toNat / 2 = ov
    · simp only [decide_eq_true_eq] at hj ⊢; rw [heq, List.getElem?_set_self hml]; decide
    · simp only [decide_eq_true_eq] at hj ⊢; rw [List.getElem?_set_ne (Ne.symm heq)]; exact hj.2
  have hlen : (flIdxs k (mrk.set ov 1#8) t).length = (flIdxs k mrk t).length + 1 := by
    induction t with
    | zero => obtain ⟨m, hm0, _⟩ := hm; omega
    | succ t' ih =>
      by_cases heq : (k.trl[t']?.getD 0#32).toNat / 2 = ov
      · have hne : ∀ j < t', (k.trl[j]?.getD 0#32).toNat / 2 ≠ ov := fun j hj hje =>
          absurd (hw.trail_vars_nodup j t' (by omega) (by omega) (hje.trans heq.symm)) (by omega)
        rw [flIdxs_succ_marked (by rw [heq, List.getElem?_set_self hov_len]; decide)]
        have h0 : mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 := by
          rw [heq]; exact hmrk0
        have hsub : flIdxs k mrk (t' + 1) = flIdxs k mrk t' := by
          simp [flIdxs, List.range_succ, List.filter_append, h0]
        rw [List.length_append, List.length_singleton, hsub, flIdxs_set_of_ne hne]
      · obtain ⟨m, hm_lt, hm_eq⟩ := hm
        have hm' : ∃ m < t', (k.trl[m]?.getD 0#32).toNat / 2 = ov := by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm_lt) with hlt | rfl
          · exact ⟨m, hlt, hm_eq⟩
          · exact absurd hm_eq heq
        have ih' := ih (by omega) hm'
        have hiff :
            decide ((mrk.set ov 1#8)[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) =
            decide (mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) := by
          rw [List.getElem?_set_ne (Ne.symm heq)]
        have hflt : [t'].filter (fun j =>
            decide ((mrk.set ov 1#8)[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)) =
          [t'].filter (fun j =>
            decide (mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)) := by
          simp only [List.filter_cons, hiff]; split <;> rfl
        simp only [flIdxs, List.range_succ, List.filter_append, List.length_append] at ih' ⊢
        rw [ih', hflt]; omega
  refine ⟨hlen, hmem_pres hov_len, ?_, fun m hmt hmv => ?_⟩
  · intro l hl; rw [flLits, List.mem_map] at hl ⊢
    obtain ⟨j, hj, rfl⟩ := hl; exact ⟨j, hmem_pres hov_len j hj, rfl⟩
  · unfold flLits; rw [List.mem_map]
    refine ⟨m, ?_, rfl⟩
    unfold flIdxs; rw [List.mem_filter, List.mem_range]
    exact ⟨hmt, by simp [hmv, List.getElem?_set_self hov_len]⟩

private theorem flLits_mem_already_marked {k : FullCoreState} {mrk : List (BitVec 8)}
    {t m : Nat} (hm : m < t)
    (hmrk : mrk[(k.trl[m]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    ((k.trl[m]?.getD 0#32).toNat ^^^ 1) ∈ flLits k mrk t := by
  unfold flLits; rw [List.mem_map]
  refine ⟨m, ?_, rfl⟩
  unfold flIdxs; rw [List.mem_filter, List.mem_range]
  exact ⟨hm, by simp [hmrk]⟩

theorem fl_resolve_step {F_cur : List (List Nat)} {k : FullCoreState}
    {mrk mrk' : List (BitVec 8)} {t' : Nat} {R_lits : List Nat}
    (hPop : mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hEnt : (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits k mrk (t' + 1))))
    (hPres : ∀ l ∈ flLits k mrk t', l ∈ flLits k mrk' t')
    (hRsnEnt : (cnfOfClauses F_cur).EntailsClause (cnfClause R_lits))
    (hRsnIn : ∀ q ∈ R_lits,
      q = (k.trl[t']?.getD 0#32).toNat ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨ q ∈ flLits k mrk' t') :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits k mrk' t')) := by
  rw [CNF.entails_clause_def]; intro α hα
  by_cases hp : (cnfClause [(k.trl[t']?.getD 0#32).toNat ^^^ 1]).Sat α
  · have hpf : ¬ (cnfClause [(k.trl[t']?.getD 0#32).toNat]).Sat α := by
      have hxor : ((k.trl[t']?.getD 0#32).toNat ^^^ 1) ^^^ 1 =
          (k.trl[t']?.getD 0#32).toNat := litNeg_litNeg _
      refine fl_sat_false_of_xor1 ?_
      simpa only [hxor] using hp
    obtain ⟨q, hqm, hqt⟩ :=
      (clause_sat_cnfClause_iff α R_lits).mp (CNF.entails_clause_def.mp hRsnEnt α hα)
    rcases hRsnIn q hqm with rfl | hq0 | hq_fl
    · exact absurd ((sat_cnfClause_singleton α _).mpr hqt) hpf
    · exact absurd ((sat_cnfClause_singleton α _).mpr hqt)
        (fl_sat_false_of_xor1 (CNF.entails_clause_def.mp hq0 α hα))
    · exact (clause_sat_cnfClause_iff α _).mpr ⟨q, hq_fl, hqt⟩
  · have hact := hEnt
    rw [flLits_succ_marked hPop] at hact
    obtain ⟨x, hx, hxt⟩ :=
      (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hact α hα)
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx_fl | rfl
    · exact (clause_sat_cnfClause_iff α _).mpr ⟨x, hPres x hx_fl, hxt⟩
    · exact absurd ((sat_cnfClause_singleton α _).mpr hxt) hp

private theorem fl_entails_step_falsified {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : Full.FullWitnessCutInv c F0 F_cur cut k)
    {s1 : FullState} {t : Nat} (_ht : t ≤ k.trail_end)
    {q : Nat} (hq_lvl0 : (k.lvl[q / 2]?.getD 0#32).toNat = 0 →
      ∃ m < k.trail_end, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1)
    (hq_marked : 0 < (k.lvl[q / 2]?.getD 0#32).toNat →
      s1.core.mrk[q / 2]?.getD 0#8 ≠ 0#8 ∧ ∃ m < t, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
      q ∈ flLits k s1.core.mrk t := by
  rcases Nat.eq_zero_or_pos (k.lvl[q / 2]?.getD 0#32).toNat with hz | hp
  · left; obtain ⟨m, hm_te, hm_eq⟩ := hq_lvl0 hz
    have hms := hw.level0_sound m hm_te (by rw [hm_eq, fl_xor1_div2]; exact hz)
    rwa [hm_eq] at hms
  · right; obtain ⟨hmrk, m, hm_t, hm_eq⟩ := hq_marked hp
    have hmem := flLits_mem_already_marked (k := k) (mrk := s1.core.mrk) hm_t
      (by rwa [hm_eq, fl_xor1_div2])
    rwa [hm_eq, show (q ^^^ 1) ^^^ 1 = q from litNeg_litNeg q] at hmem

structure FailedStateOk (c : FullCfg) (s s1 : FullState) (cut : Nat) : Prop where
  len : s1.LengthsOk c
  core : s1.core =
    { s.core with mrk := s1.core.mrk, min_clr_len := s1.core.min_clr_len,
                  tmp := s1.core.tmp, tmp_len := s1.core.tmp_len }
  scr : s1.scratch = { s.scratch with work_stk1 := s1.scratch.work_stk1 }
  cov : Full.FullAnaMarksCov c s1
  mb : FailedMarkedCut s s1.core.mrk cut

private theorem fl_push_mrk_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState}
    (_hw : Full.FullWitnessCutInv c F0 F_cur cut s.core)
    (hok : FailedStateOk c s s1 cut) {ov : Nat}
    (hov_lt : ov < s.core.cur_vars) (hmrk0 : s1.core.mrk[ov]?.getD 0#8 = 0#8)
    (hmcl_lt : s1.core.min_clr_len < s.core.cur_vars)
    (hlvl1 : (s.core.lvl[ov]?.getD 0#32).toNat = 1)
    (hm_cut : ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat / 2 = ov) :
    let ov32 := BitVec.ofNat 32 ov
    let s2 : FullState :=
      { core := { s1.core with mrk := s1.core.mrk.set ov 1#8,
                               min_clr_len := s1.core.min_clr_len + 1 }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov32 } }
    FailedStateOk c s s2 cut := by
  intro ov32 s2
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le := hok.len.core_ok.cur_vars_le
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
  have hmrl1 : s1.core.mrk.length = c.max_vars := hok.len.core_ok.mrk_len
  have hwsl1 : s1.scratch.work_stk1.length = 2 * c.max_vars := hok.len.scratch_ok.work_stk1_len
  have hov_max : ov < c.max_vars := by omega
  have hov32_toNat : ov32.toNat = ov := bv32_ofNat_toNat (by omega)
  have hmcl_ws : s1.core.min_clr_len < s1.scratch.work_stk1.length := by rw [hwsl1]; omega
  have hov_mrk : ov < s1.core.mrk.length := by rw [hmrl1]; omega
  rcases hok.cov with ⟨hmcl_c1, hnd1, helem1, hcov1⟩
  refine ⟨⟨{ hok.len.core_ok with
      mrk_len := by simp [s2, hmrl1]
      min_clr_len_le := by dsimp only [s2]; omega },
    { hok.len.scratch_ok with work_stk1_len := by simp [s2, hwsl1] }⟩,
    by dsimp only [s2]; rw [hok.core], by dsimp only [s2]; rw [hok.scr], ?_, ?_⟩
  · refine ⟨by dsimp only [s2]; rw [hcv1]; omega, ?_, fun k hk => ?_, fun v hv hnz => ?_⟩
    · exact fl_nodup_map_take_append hmcl_ws hnd1 fun k hk he =>
        (helem1 k hk).2 (by rw [he, hov32_toNat]; exact hmrk0)
    · dsimp only [s2] at hk ⊢
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
      · rw [List.getElem?_set_ne (by omega)]
        have hne : (s1.scratch.work_stk1[k]?.getD 0#32).toNat ≠ ov := fun he =>
          (helem1 k hlt).2 (he ▸ hmrk0)
        exact ⟨(helem1 k hlt).1,
          by rw [List.getElem?_set_ne (Ne.symm hne)]; exact (helem1 k hlt).2⟩
      · rw [List.getElem?_set_self hmcl_ws, Option.getD_some, hov32_toNat,
          List.getElem?_set_self hov_mrk, Option.getD_some]
        exact ⟨by rw [hcv1]; exact hov_lt, by decide⟩
    · by_cases hveq : v = ov
      · subst v; refine ⟨s1.core.min_clr_len, by dsimp only [s2]; omega, ?_⟩
        dsimp only [s2]; rw [List.getElem?_set_self hmcl_ws, Option.getD_some, hov32_toNat]
      · have hnz1 : s1.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
          dsimp only [s2] at hnz; rwa [List.getElem?_set_ne (Ne.symm hveq)] at hnz
        obtain ⟨k, hk, hkeq⟩ := hcov1 v hv hnz1
        exact ⟨k, by dsimp only [s2]; omega, by
          dsimp only [s2]; rw [List.getElem?_set_ne (by omega)]; exact hkeq⟩
  · intro v hv hnz; dsimp only [s2] at hnz
    by_cases hveq : v = ov
    · subst v; exact ⟨hlvl1, hm_cut⟩
    · rw [List.getElem?_set_ne (Ne.symm hveq)] at hnz
      exact hok.mb v hv hnz

theorem fl_failedStateOk_with_tmp {c : FullCfg} {s s1 : FullState} {cut : Nat}
    (hok : FailedStateOk c s s1 cut) {tmp' : List (BitVec 32)}
    (htlen : tmp'.length = c.max_vars) :
    FailedStateOk c s { s1 with core := { s1.core with tmp := tmp' } } cut :=
  ⟨⟨{ hok.len.core_ok with tmp_len_arr := htlen }, hok.len.scratch_ok⟩,
   by dsimp only; rw [hok.core], hok.scr, hok.cov, hok.mb⟩

theorem fl_otfsInvW_of_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState}
    (hcut : Full.FullCutInvW c F0 F_cur cut s) (hok : FailedStateOk c s s1 cut)
    (hmrk0 : ∀ v < c.max_vars, s1.core.mrk[v]?.getD 0#8 = 0#8) :
    Full.FullOtfsInvW c F0 F_cur s1 := by
  have hwt_s1 : Full.FullWitnessCutInv c F0 F_cur cut
      { s.core with mrk := s1.core.mrk, tmp := s1.core.tmp, tmp_cnt := s.core.tmp_cnt,
                    tmp_len := s1.core.tmp_len, min_clr_len := s1.core.min_clr_len } :=
    Full.deduce_same_core_cut hcut.2.1 s1.core.mrk s1.core.tmp s.core.tmp_cnt
      s1.core.tmp_len s1.core.min_clr_len
  have hs1_eq : s1.core = { s.core with
      mrk := s1.core.mrk, tmp := s1.core.tmp, tmp_cnt := s.core.tmp_cnt,
      tmp_len := s1.core.tmp_len, min_clr_len := s1.core.min_clr_len } := by
    rw [hok.core]
  have hw_clr : Full.FullOtfsWitnessInv c F0 F_cur s1.core :=
    hs1_eq ▸ hwt_s1.toFullOtfsWitnessInv
  have hlm_clr : Full.FullLitMarksClear c s1 :=
    ⟨hmrk0, fun l hl => by rw [hok.core]; exact hcut.2.2.1.2 l hl⟩
  have hnd_clr : Full.FullArenaVarsNodup s1 := by
    unfold Full.FullArenaVarsNodup Full.fullArenaClauseRefs Full.fullArenaClauseRefsCore
      Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore Full.fullArenaClauseLits
      Full.fullArenaClauseLitsCore Full.fullArenaClauseSizeCore Full.fullArenaHdrCore
    rw [hok.core]; exact hcut.2.2.2.1
  have hext_clr : Full.FullExtScratchOk c s1 :=
    ⟨fun i hi => by
      dsimp only [Full.FullLastLearnedWf]
      change (let cr := s1.scratch.last_learned[i]?.getD 0xFFFFFFFF#32; _)
      have hll : s1.scratch.last_learned = s.scratch.last_learned := by rw [hok.scr]
      have hrefs : Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s := by
        unfold Full.fullArenaClauseRefs Full.fullArenaClauseRefsCore; rw [hok.core]
      rw [hll, hrefs]; exact hcut.2.2.2.2.1.1 i hi,
     by rw [hok.scr]; exact hcut.2.2.2.2.1.2⟩
  exact ⟨hok.len, hw_clr, hlm_clr, hnd_clr, hext_clr, by rw [hok.core]; exact hcut.2.2.2.2.2⟩

theorem fl_mark_zero_eq {s1 s : FullState} {c : FullCfg} {cut : Nat}
    (hok : FailedStateOk c s s1 cut) {ov : Nat} (hov : ov < s.core.cur_vars)
    (heq0 : BitVec.setWidth 32 (s1.core.mrk[ov]'(by
      rw [hok.len.core_ok.mrk_len]
      have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
      have := hok.len.core_ok.cur_vars_le; omega)) = 0#32) :
    s1.core.mrk[ov]?.getD 0#8 = 0#8 := by
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
  have hml : ov < s1.core.mrk.length := by
    rw [hok.len.core_ok.mrk_len]; have := hok.len.core_ok.cur_vars_le; omega
  rw [List.getElem?_eq_getElem hml, Option.getD_some]
  exact fl_bv8_zext_eq0 heq0

theorem fl_mark_nz_eq {s1 s : FullState} {c : FullCfg} {cut : Nat}
    (hok : FailedStateOk c s s1 cut) {ov : Nat} (hov : ov < s.core.cur_vars)
    (hne0 : BitVec.setWidth 32 (s1.core.mrk[ov]'(by
      rw [hok.len.core_ok.mrk_len]
      have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
      have := hok.len.core_ok.cur_vars_le; omega)) ≠ 0#32) :
    s1.core.mrk[ov]?.getD 0#8 ≠ 0#8 := by
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
  have hml : ov < s1.core.mrk.length := by
    rw [hok.len.core_ok.mrk_len]; have := hok.len.core_ok.cur_vars_le; omega
  rw [List.getElem?_eq_getElem hml, Option.getD_some]
  exact fl_bv8_zext_ne0 hne0

theorem fl_entails_of_clause {F_cur : List (List Nat)} {C L : List Nat}
    (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hIn : ∀ q ∈ C, (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨ q ∈ L) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause L) := by
  rw [CNF.entails_clause_def]; intro α hα
  obtain ⟨q, hqm, hqt⟩ := (clause_sat_cnfClause_iff α C).mp (CNF.entails_clause_def.mp hC α hα)
  rcases hIn q hqm with hq0 | hql
  · exact absurd ((sat_cnfClause_singleton α q).mpr hqt)
      (fl_sat_false_of_xor1 (CNF.entails_clause_def.mp hq0 α hα))
  · exact (clause_sat_cnfClause_iff α L).mpr ⟨q, hql, hqt⟩

theorem fl_mark_lit_push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState}
    (hw : Full.FullWitnessCutInv c F0 F_cur cut s.core) (hcl1 : s.core.cur_level = 1)
    (hok : FailedStateOk c s s1 cut) {t q : Nat}
    (ht_le : t ≤ s.core.trail_end) (hq_lt : q < 2 * s.core.cur_vars)
    (hmrk0 : s1.core.mrk[q / 2]?.getD 0#8 = 0#8)
    (hlvl_pos : 0 < (s.core.lvl[q / 2]?.getD 0#32).toNat)
    (hq_t : ∃ m < t, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1)
    (hq_cut : ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1) :
    let ov := q / 2
    let ov32 := BitVec.ofNat 32 ov
    let s2 : FullState :=
      { core := { s1.core with mrk := s1.core.mrk.set ov 1#8,
                               min_clr_len := s1.core.min_clr_len + 1 }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov32 } }
    s1.core.min_clr_len < s.core.cur_vars ∧
    FailedStateOk c s s2 cut ∧
    (flIdxs s.core s2.core.mrk t).length = (flIdxs s.core s1.core.mrk t).length + 1 ∧
    (∀ l ∈ flLits s.core s1.core.mrk t, l ∈ flLits s.core s2.core.mrk t) ∧
    ((cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
      q ∈ flLits s.core s2.core.mrk t) := by
  intro ov ov32 s2
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
  have hov_lt : ov < s.core.cur_vars := Nat.div_lt_of_lt_mul hq_lt
  have hov_lt1 : ov < s1.core.cur_vars := by rw [hcv1]; exact hov_lt
  have hmcl_ws : s1.core.min_clr_len ≤ s1.scratch.work_stk1.length := by
    have := hok.len.core_ok.min_clr_len_le
    have := hok.len.scratch_ok.work_stk1_len
    omega
  have hmcl_lt : s1.core.min_clr_len < s.core.cur_vars := by
    have := fl_nodup_mcl_lt_cv hok.cov hmcl_ws hov_lt1 hmrk0
    omega
  obtain ⟨mt, hmt_t, hmt_eq⟩ := hq_t
  obtain ⟨mc, hmc_cut, hmc_eq⟩ := hq_cut
  have hlvl1 : (s.core.lvl[ov]?.getD 0#32).toNat = 1 := by
    have hle := hw.lvl_le mc (Nat.lt_of_lt_of_le hmc_cut hw.cut_le)
    rw [hmc_eq, fl_xor1_div2, hcl1] at hle
    exact le_antisymm hle hlvl_pos
  have hok2 := fl_push_mrk_inv hw hok hov_lt hmrk0 hmcl_lt hlvl1
    ⟨mc, hmc_cut, by rw [hmc_eq, fl_xor1_div2]⟩
  have hov_mrk : ov < s1.core.mrk.length := by
    rw [hok.len.core_ok.mrk_len]; have := hok.len.core_ok.cur_vars_le; omega
  have hidx := flIdxs_set_marked hw ht_le hov_mrk hmrk0
    ⟨mt, hmt_t, by rw [hmt_eq, fl_xor1_div2]⟩
  have hmem := hidx.2.2.2 mt hmt_t (by rw [hmt_eq, fl_xor1_div2])
  rw [hmt_eq, show (q ^^^ 1) ^^^ 1 = q from litNeg_litNeg q] at hmem
  exact ⟨hmcl_lt, hok2, hidx.1, hidx.2.2.1, Or.inr hmem⟩

theorem fl_mark_lit_skip {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState}
    (hw : Full.FullWitnessCutInv c F0 F_cur cut s.core) (_hcl1 : s.core.cur_level = 1)
    {t q : Nat} (ht_le : t ≤ s.core.trail_end)
    (hq_lvl0 : (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 →
      ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1)
    (hq_pos : 0 < (s.core.lvl[q / 2]?.getD 0#32).toNat →
      s1.core.mrk[q / 2]?.getD 0#8 ≠ 0#8 ∧ ∃ m < t, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
      q ∈ flLits s.core s1.core.mrk t :=
  fl_entails_step_falsified hw ht_le hq_lvl0 hq_pos

theorem fl_assign0_preserves_sparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hs : Full.FullSparseInvW c F0 F_cur s) (_hcl0 : s.core.cur_level = 0)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hl0 : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    {flags' : List (BitVec 32)} {unass' unflushed' : BitVec 64} {phases' : List (BitVec 8)}
    (hfll : flags'.length = c.max_vars) (hphl : phases'.length = c.max_vars) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v 0#32, rsns := s.core.rsns.set v 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            trail_end := s.core.trail_end + 1
            unassigned := unass', unflushed := unflushed' }
        scratch := { s.scratch with phases := phases' } }
    Full.FullSparseInvW c F0 F_cur s' := by
  intro v s'
  have hsc' : ({ s.scratch with phases := phases' } : FullScratch).LengthsOk c :=
    { hs.1.scratch_ok with phases_len := hphl }
  obtain ⟨hlen', hw'⟩ := chronoAssign_preserves_fullWitness hs.2.1 hs.1
    (lit := lit) (rsn := 0xFFFFFFFF#32) (alvl := 0) (flags' := flags') (unassigned' := unass')
    (unflushed' := unflushed') (scratch' := { s.scratch with phases := phases' })
    hsc' hfll hlit hun (Nat.zero_le _) (fun h => by omega) (fun _ => hl0)
    (fun h => by omega) (fun h => by omega)
  have hnd' : Full.FullArenaVarsNodup s' := by
    unfold Full.FullArenaVarsNodup Full.fullArenaClauseRefs Full.fullArenaClauseRefsCore
      Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore Full.fullArenaClauseLits
      Full.fullArenaClauseLitsCore Full.fullArenaClauseSizeCore Full.fullArenaHdrCore
    exact hs.2.2.2.1
  have hext' := Full.FullExtScratchOk.of_pres hs.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr)
  have hbv0 : BitVec.ofNat 32 0 = 0#32 := rfl
  rw [hbv0] at hlen' hw'
  exact ⟨hlen', hw', hs.2.2.1, hnd', hext', hs.2.2.2.2.2⟩

theorem fl_take_succ_forall {α : Type} (xs : List α) {i : Nat} (hi : i < xs.length)
    (P : α → Prop) (hprev : ∀ q ∈ xs.take i, P q) (hcur : P (xs[i]'hi)) :
    ∀ q ∈ xs.take (i + 1), P q := by
  intro q hq
  rw [List.mem_iff_getElem] at hq
  obtain ⟨m, hm, rfl⟩ := hq
  rw [List.length_take] at hm
  have hm_lt : m < i + 1 := by omega
  rw [List.getElem_take]
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm_lt) with hlt | rfl
  · refine hprev _ ?_
    rw [List.mem_iff_getElem]
    exact ⟨m, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
  · exact hcur

theorem fl_arenaClauseLitsCore_length {k : FullCoreState} {cref : Nat}
    (h : cref + 3 + Full.fullArenaClauseSizeCore k cref ≤ k.arena.length) :
    (Full.fullArenaClauseLitsCore k cref).length = Full.fullArenaClauseSizeCore k cref := by
  unfold Full.fullArenaClauseLitsCore
  rw [List.length_map, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]

theorem fl_arenaClauseLitsCore_getElem {k : FullCoreState} {cref j : Nat}
    (_hbd : cref + 3 + Full.fullArenaClauseSizeCore k cref ≤ k.arena.length)
    (_hj : j < Full.fullArenaClauseSizeCore k cref)
    (hj_len : j < (Full.fullArenaClauseLitsCore k cref).length := by
      rw [fl_arenaClauseLitsCore_length _hbd]; exact _hj)
    (hk_ar : cref + 3 + j < k.arena.length := by omega) :
    (Full.fullArenaClauseLitsCore k cref)[j]'hj_len = (k.arena[cref + 3 + j]'hk_ar).toNat := by
  simp only [Full.fullArenaClauseLitsCore, List.getElem_map, List.getElem_take, List.getElem_drop]

end LeanQbe.T.Examples.Kissat.FullM6MinShrink
