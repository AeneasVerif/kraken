/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Shared Theory & Helpers for `full_ana_failed_lit_m6_hdr` (`Proof.Analyze.WpFailedLitBase`)

Provides failed-literal trail resolution theory, marking invariants (`FailedMarkedCut`,
`FailedStateOk`), and Step-13 OTFS/clear bridge lemmas built on canonical `Analyze.Helpers`
(`0` legacy `Full*` imports, `0` `@[expose]` on theorems/sections, `<= 100` cols).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. BitVec, List & Arena Indexing Helpers -/

theorem fl_bv64_sub1_toNat {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hle : (1#64 : BitVec 64) ≤ x := BitVec.le_def.mpr h
  rw [BitVec.toNat_sub_of_le hle]; rfl

theorem fl_bv32_0_add (x : BitVec 32) : 0#32 + x = x := by simp

theorem fl_sext32_64_1 : BitVec.signExtend 64 (1#32 : BitVec 32) = 1#64 := rfl

theorem p2_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

theorem p2_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

theorem p2_bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem fl_bv8_zext_eq0 {x : BitVec 8} (h : BitVec.setWidth 32 x = 0#32) : x = 0#8 := by
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
    show (0#32 : BitVec 32).toNat = 0 from rfl] at ht
  exact BitVec.eq_of_toNat_eq ht

theorem fl_bv8_zext_ne0 {x : BitVec 8} (h : BitVec.setWidth 32 x ≠ 0#32) : x ≠ 0#8 :=
  fun hx => h (by subst hx; rfl)

theorem fl_take_succ_forall_pure {α : Type} [Inhabited α] {xs : List α} {P : α → Prop}
    {k : Nat} (_hk : k < xs.length) (hpre : ∀ j < k, P (xs[j]?.getD default))
    (hkP : P (xs[k]?.getD default)) : ∀ j < k + 1, P (xs[j]?.getD default) := by
  intro j hj
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
  · exact hpre j hlt
  · exact hkP

theorem fl_arenaClauseLitsCore_length {k : FullCoreState} {cref : Nat}
    (h : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length) :
    (fullArenaClauseLitsCore k cref).length = fullArenaClauseSizeCore k cref := by
  unfold fullArenaClauseLitsCore
  rw [List.length_map, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]

theorem fl_arenaClauseLitsCore_getElem {k : FullCoreState} {cref j : Nat}
    (_hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length)
    (_hj : j < fullArenaClauseSizeCore k cref)
    (hj_len : j < (fullArenaClauseLitsCore k cref).length := by
      rw [fl_arenaClauseLitsCore_length _hbd]; exact _hj)
    (hk_ar : cref + 3 + j < k.arena.length := by omega) :
    (fullArenaClauseLitsCore k cref)[j]'hj_len = (k.arena[cref + 3 + j]'hk_ar).toNat := by
  unfold fullArenaClauseLitsCore
  simp [List.getElem_take, List.getElem_drop]

theorem p2_arena_clause_lit {c : FullCfg} {s sj : FullState}
    (_hcl : s.LengthsOk c) (_hlj : sj.LengthsOk c) (hcore : sj.core.arena = s.core.arena)
    {r32 j : BitVec 32} {cref : Nat} (hr_eq : r32.toNat = cref)
    (hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length)
    (hj_lt : j.toNat < fullArenaClauseSizeCore s.core cref) :
    let idx := (r32.setWidth 64 + 3#64 + j.setWidth 64).toNat
    ∃ (hlt_ar : idx < sj.core.arena.length)
      (hlen_lits : j.toNat < (fullArenaClauseLitsCore s.core cref).length),
      (fullArenaClauseLitsCore s.core cref)[j.toNat]'hlen_lits =
        (sj.core.arena[idx]'hlt_ar).toNat ∧
      (sj.core.arena[idx]'hlt_ar).toNat ∈ fullArenaClauseLitsCore s.core cref := by
  intro idx
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hlen_eq : sj.core.arena.length = s.core.arena.length := by rw [hcore]
  have har_s : s.core.arena.length = c.arena_cap := _hcl.core_ok.arena_len_arr
  have h3_add : r32.toNat + 3 < 2 ^ 64 := by omega
  have hj_add : r32.toNat + 3 + j.toNat < 2 ^ 64 := by omega
  have hidx_eq : idx = cref + 3 + j.toNat := by
    dsimp only [idx]
    rw [BitVec.toNat_add, BitVec.toNat_add, fl_bv32_setWidth64, fl_bv32_setWidth64,
      show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt h3_add, Nat.mod_eq_of_lt hj_add, hr_eq]
  have hlt_ar : idx < sj.core.arena.length := by rw [hlen_eq, hidx_eq]; omega
  have hlen_lits : j.toNat < (fullArenaClauseLitsCore s.core cref).length := by
    rw [fl_arenaClauseLitsCore_length hbd]; exact hj_lt
  have hget : (fullArenaClauseLitsCore s.core cref)[j.toNat]'hlen_lits =
      (sj.core.arena[idx]'hlt_ar).toNat := by
    rw [fl_arenaClauseLitsCore_getElem hbd hj_lt hlen_lits (by omega)]
    exact congrArg BitVec.toNat (p2_getElem_congr_list hcore.symm hidx_eq.symm)
  exact ⟨hlt_ar, hlen_lits, hget, by rw [← hget]; exact List.getElem_mem _⟩

/-! ## 2. Failed-Literal SAT & Implication Theory -/

theorem fl_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l :=
  litNeg_litNeg l

theorem fl_sat_false_of_xor1 {α : Nat → Bool} {q : Nat} (hq : (cnfClause [q]).Sat α) :
    ¬ (cnfClause [q ^^^ 1]).Sat α :=
  fun hqf => (sat_cnfClause_litNeg_iff α q).mp hqf hq

theorem fl_sat_taut {α : Nat → Bool} (x : Nat) : (cnfClause [x ^^^ 1, x]).Sat α := by
  rw [clause_sat_cnfClause_iff]
  by_cases hx : (cnfClause [x]).Sat α
  · exact ⟨x, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl),
      (sat_cnfClause_singleton α x).mp hx⟩
  · exact ⟨x ^^^ 1, List.mem_cons_self,
      (sat_cnfClause_singleton α _).mp ((sat_cnfClause_litNeg_iff α x).mpr hx)⟩

theorem fl_sat_not_pair {α : Nat → Bool} {a b : Nat}
    (hb : ¬ (cnfClause [b]).Sat α) (hab : (cnfClause [a, b]).Sat α) :
    (cnfClause [a]).Sat α := by
  obtain ⟨l, hl, hlt⟩ := (clause_sat_cnfClause_iff α [a, b]).mp hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact (sat_cnfClause_singleton α _).mpr hlt
  · exact absurd ((sat_cnfClause_singleton α _).mpr hlt) hb

theorem fl_sat_not_pair_snd {α : Nat → Bool} {a b : Nat}
    (ha : ¬ (cnfClause [a]).Sat α) (hab : (cnfClause [a, b]).Sat α) :
    (cnfClause [b]).Sat α := by
  obtain ⟨l, hl, hlt⟩ := (clause_sat_cnfClause_iff α [a, b]).mp hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact absurd ((sat_cnfClause_singleton α _).mpr hlt) ha
  · exact (sat_cnfClause_singleton α _).mpr hlt

theorem fl_entails_weakening {F : CNF Nat} {a b : Nat}
    (h : F.EntailsClause (cnfClause [b])) : F.EntailsClause (cnfClause [a, b]) := by
  rw [CNF.entails_clause_def]; intro α hα
  rw [clause_sat_cnfClause_iff]
  exact ⟨b, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl),
    (sat_cnfClause_singleton α b).mp (CNF.entails_clause_def.mp h α hα)⟩

theorem fl_entails_of_clause {F_cur : List (List Nat)} {C L : List Nat}
    (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hIn : ∀ q ∈ C, (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨ q ∈ L) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause L) := by
  rw [CNF.entails_clause_def]; intro α hα
  obtain ⟨q, hqm, hqt⟩ := (clause_sat_cnfClause_iff α C).mp (CNF.entails_clause_def.mp hC α hα)
  rcases hIn q hqm with hq0 | hql
  · have hnf := fl_sat_false_of_xor1 (CNF.entails_clause_def.mp hq0 α hα)
    rw [fl_xor1_xor1] at hnf
    exact absurd ((sat_cnfClause_singleton α q).mpr hqt) hnf
  · exact (clause_sat_cnfClause_iff α L).mpr ⟨q, hql, hqt⟩

/-- At level 1 with decision literal `failed` at level 1, every trail literal below `cut`
is entailed conditioned on `failed ^^^ 1`. -/
theorem fl_trail_imp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
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
    by_cases hl0 : (k.lvl[p / 2]?.getD 0#32).toNat = 0
    · exact fl_entails_weakening (hw.level0_sound j hj_te hl0)
    · have hl_pos : 0 < (k.lvl[p / 2]?.getD 0#32).toNat := Nat.pos_of_ne_zero hl0
      have hl_1 : (k.lvl[p / 2]?.getD 0#32).toNat = 1 := by
        have hle := hw.lvl_le j hj_te; rw [hcl1] at hle; exact Nat.le_antisymm hle hl_pos
      by_cases hrsn_none : k.rsns[p / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
      · have hle1 := hw.dec_earliest j idx_d hj_te hid_lt
          (by rw [hid_eq]; exact hl_1.trans hlvl.symm)
          ⟨by rw [hid_eq, hlvl]; omega, by rw [hid_eq]; exact hrsn⟩
        have hle2 := hw.dec_earliest idx_d j hid_lt hj_te
          (by rw [hid_eq]; exact hlvl.trans hl_1.symm) ⟨hl_pos, hrsn_none⟩
        have hji : j = idx_d := by omega
        have hp_eq : p = failed := by dsimp only [p]; rw [hji, hid_eq]
        rw [show (k.trl[j]?.getD 0#32).toNat = p from rfl, hp_eq]
        rw [CNF.entails_clause_def]; intro α _; exact fl_sat_taut failed
      · have hr := hw.reason_inv_cut j hj hrsn_none
        dsimp only at hr
        by_cases hbin : (k.rsns[p / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hr
          obtain ⟨_, hent_bin, m, hm_j, hm_eq, _⟩ := hr
          have hm_cut : m < cut := by omega
          have hm_imp := ih m hm_j hm_cut
          rw [CNF.entails_clause_def]; intro α hα
          by_cases hfn : (cnfClause [failed ^^^ 1]).Sat α
          · exact (clause_sat_cnfClause_iff α _).mpr ⟨failed ^^^ 1, List.mem_cons_self,
              (sat_cnfClause_singleton α _).mp hfn⟩
          · have hot_neg := fl_sat_not_pair_snd hfn (CNF.entails_clause_def.mp hm_imp α hα)
            rw [hm_eq] at hot_neg
            have hot_false := fl_sat_false_of_xor1 hot_neg
            rw [fl_xor1_xor1] at hot_false
            exact (clause_sat_cnfClause_iff α _).mpr
              ⟨p, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl),
                (sat_cnfClause_singleton α p).mp
                  (fl_sat_not_pair hot_false (CNF.entails_clause_def.mp hent_bin α hα))⟩
        · rw [ite_eq_right hbin] at hr
          obtain ⟨href, hng, hall⟩ := hr
          have hent_lg := hw.arena.entails _ href hng
          rw [CNF.entails_clause_def]; intro α hα
          by_cases hfn : (cnfClause [failed ^^^ 1]).Sat α
          · exact (clause_sat_cnfClause_iff α _).mpr ⟨failed ^^^ 1, List.mem_cons_self,
              (sat_cnfClause_singleton α _).mp hfn⟩
          · obtain ⟨q, hqm, hqt⟩ :=
              (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hent_lg α hα)
            rcases hall q hqm with hqp | ⟨m, hm_j, hm_eq, _⟩
            · exact (clause_sat_cnfClause_iff α _).mpr
                ⟨p, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl),
                  by dsimp only [p]; rw [← hqp]; exact hqt⟩
            · have hm_imp := ih m hm_j (by omega)
              have hqn := fl_sat_not_pair_snd hfn (CNF.entails_clause_def.mp hm_imp α hα)
              rw [hm_eq] at hqn
              have hqf := fl_sat_false_of_xor1 hqn
              rw [fl_xor1_xor1] at hqf
              exact absurd ((sat_cnfClause_singleton α q).mpr hqt) hqf

private theorem fl_falsified_not_failed_false {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hcl1 : s.core.cur_level = 1)
    {failed l : Nat}
    (himp : ∀ j < cut, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [failed ^^^ 1, (s.core.trl[j]?.getD 0#32).toNat]))
    (hl_lt : l < 2 * s.core.cur_vars) (hfals : s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hcut_m : (s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level →
      ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)
    {α : Nat → Bool} (hα : (cnfOfClauses F_cur).Sat α)
    (hnf : ¬ (cnfClause [failed ^^^ 1]).Sat α) :
    (cnfClause [l]).Sat α → False := fun hl_sat => by
  obtain ⟨i, hi_te, hi_eq⟩ := (hw.vals_false_iff l hl_lt).mp hfals
  have hl_div : (l ^^^ 1) / 2 = l / 2 := fl_xor1_div2 l
  by_cases hl0 : (s.core.lvl[l / 2]?.getD 0#32).toNat = 0
  · have hl0i : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      rw [hi_eq, hl_div]; exact hl0
    have hent_op := hw.level0_sound i hi_te hl0i
    rw [hi_eq] at hent_op
    have hnf_l := fl_sat_false_of_xor1 hl_sat
    exact hnf_l (CNF.entails_clause_def.mp hent_op α hα)
  · have hl_cl : (s.core.lvl[l / 2]?.getD 0#32).toNat = s.core.cur_level := by
      have hi_lvl := hw.lvl_le i hi_te
      rw [hi_eq, hl_div, hcl1] at hi_lvl
      rw [hcl1]
      omega
    obtain ⟨m, hm_cut, hm_eq⟩ := hcut_m hl_cl
    have hsat_neg := fl_sat_not_pair_snd hnf (CNF.entails_clause_def.mp (himp m hm_cut) α hα)
    rw [hm_eq] at hsat_neg
    exact fl_sat_false_of_xor1 hl_sat hsat_neg

theorem failedLit_not_failed_of_confl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hcl1 : s.core.cur_level = 1)
    (hc : FullConflictOkCut F_cur cut s) {failed : Nat}
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
      · exact absurd hct (by rw [hne]; decide)
    · rw [ite_eq_right hct] at hcc
      rcases hcw with ⟨h1, _⟩ | ⟨_, href, hng, hfals⟩
      · exact absurd h1 hct
      · obtain ⟨l, hl_mem, hl_t⟩ :=
          (clause_sat_cnfClause_iff α _).mp
            (CNF.entails_clause_def.mp (hw.arena.entails _ href hng) α hα)
        exact fl_falsified_not_failed_false hw hcl1 himp (hw.arena.lits_lt _ href hng l hl_mem)
          (hfals l hl_mem) (hcc l hl_mem) hα hnf ((sat_cnfClause_singleton α _).mpr hl_t)

/-! ## 3. Marked-Trail Cut Invariants & `Helpers.flIdxs`/`flLits` Lemmas -/

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

theorem flLits_succ_marked {mrk : List (BitVec 8)} {trl : List (BitVec 32)} {t' : Nat}
    (hm : mrk[(trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    flLits mrk trl (t' + 1) = ((trl[t']?.getD 0#32).toNat ^^^ 1) :: flLits mrk trl t' := by
  unfold flLits
  rw [flIdxs_succ_marked hm, List.map_cons]

theorem flLits_eq_singleton_of_len1 {mrk : List (BitVec 8)} {trl : List (BitVec 32)} {t' : Nat}
    (hm : mrk[(trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (h1 : (flIdxs mrk trl (t' + 1)).length = 1) :
    flLits mrk trl (t' + 1) = [(trl[t']?.getD 0#32).toNat ^^^ 1] := by
  have hlen0 : (flIdxs mrk trl t').length = 0 := by
    rw [flIdxs_succ_marked hm, List.length_cons] at h1; omega
  have hnil : flIdxs mrk trl t' = [] := List.length_eq_zero_iff.mp hlen0
  rw [flLits_succ_marked hm, show flLits mrk trl t' = [] from by unfold flLits; rw [hnil]; rfl]

theorem flIdxs_mem_iff {mrk : List (BitVec 8)} {trl : List (BitVec 32)} {t j : Nat} :
    j ∈ flIdxs mrk trl t ↔ j < t ∧ mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
  induction t with
  | zero => simp [flIdxs]
  | succ i ih =>
    rw [flIdxs]
    by_cases hm : mrk[(trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8
    · rw [ite_eq_left hm, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hj, hjm⟩)
        · exact ⟨Nat.lt_succ_self _, hm⟩
        · exact ⟨Nat.lt_succ_of_lt hj, hjm⟩
      · rintro ⟨hj, hjm⟩
        by_cases hji : j = i
        · exact Or.inl hji
        · exact Or.inr ⟨by omega, hjm⟩
    · rw [ite_eq_right hm, ih]
      constructor
      · rintro ⟨hj, hjm⟩; exact ⟨Nat.lt_succ_of_lt hj, hjm⟩
      · rintro ⟨hj, hjm⟩
        have hne : j ≠ i := fun hji => hm (by rw [← hji]; exact hjm)
        exact ⟨by omega, hjm⟩

theorem flLits_mem_already_marked {mrk : List (BitVec 8)} {trl : List (BitVec 32)}
    {t m : Nat} (hm : m < t)
    (hmrk : mrk[(trl[m]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    ((trl[m]?.getD 0#32).toNat ^^^ 1) ∈ flLits mrk trl t := by
  unfold flLits; rw [List.mem_map]
  exact ⟨m, flIdxs_mem_iff.mpr ⟨hm, hmrk⟩, rfl⟩

theorem flIdxs_set_of_ne {mrk : List (BitVec 8)} {trl : List (BitVec 32)} {t ov : Nat}
    (hmiss : ∀ j < t, (trl[j]?.getD 0#32).toNat / 2 ≠ ov) :
    flIdxs (mrk.set ov 1#8) trl t = flIdxs mrk trl t :=
  flIdxs_congr fun j hj => by rw [List.getElem?_set_ne (Ne.symm (hmiss j hj))]

theorem flIdxs_set_marked {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    {mrk : List (BitVec 8)} {t ov : Nat} (ht : t ≤ k.trail_end) (hov_len : ov < mrk.length)
    (hmrk0 : mrk[ov]?.getD 0#8 = 0#8)
    (hm : ∃ m < t, (k.trl[m]?.getD 0#32).toNat / 2 = ov) :
    (flIdxs (mrk.set ov 1#8) k.trl t).length = (flIdxs mrk k.trl t).length + 1 ∧
    (∀ j ∈ flIdxs mrk k.trl t, j ∈ flIdxs (mrk.set ov 1#8) k.trl t) ∧
    (∀ l ∈ flLits mrk k.trl t, l ∈ flLits (mrk.set ov 1#8) k.trl t) ∧
    (∀ m < t, (k.trl[m]?.getD 0#32).toNat / 2 = ov →
      ((k.trl[m]?.getD 0#32).toNat ^^^ 1) ∈ flLits (mrk.set ov 1#8) k.trl t) := by
  have hlen_set : (flIdxs (mrk.set ov 1#8) k.trl t).length = (flIdxs mrk k.trl t).length + 1 := by
    induction t with
    | zero => obtain ⟨m, hm0, _⟩ := hm; omega
    | succ t' ih =>
      rw [flIdxs, flIdxs]
      have ht'_lt : t' < k.trail_end := by omega
      by_cases hov : (k.trl[t']?.getD 0#32).toNat / 2 = ov
      · have hmiss : ∀ j < t', (k.trl[j]?.getD 0#32).toNat / 2 ≠ ov := fun j hj heq => by
          have hij := hw.trail_vars_nodup t' j ht'_lt (by omega) (hov.trans heq.symm)
          omega
        have hm_set : (mrk.set ov 1#8)[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
          rw [hov, List.getElem?_set_self hov_len]; decide
        have hm_old : mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 := by
          rw [hov]; exact hmrk0
        rw [ite_eq_left hm_set, ite_eq_right (fun hn => absurd hm_old hn), List.length_cons,
          flIdxs_set_of_ne hmiss]
      · obtain ⟨m, hm_lt, hm_eq⟩ := hm
        have hm_t' : m < t' := by
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm_lt) with hlt | rfl
          · exact hlt
          · exact absurd hm_eq hov
        have hmrk_eq : (mrk.set ov 1#8)[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 =
            mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 := by
          rw [List.getElem?_set_ne (Ne.symm hov)]
        have ih_t' := ih (by omega) ⟨m, hm_t', hm_eq⟩
        by_cases hm_old : mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8
        · have hm_new : (mrk.set ov 1#8)[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
            rw [hmrk_eq]; exact hm_old
          rw [ite_eq_left hm_new, ite_eq_left hm_old, List.length_cons, List.length_cons, ih_t']
        · have hm_new : ¬ (mrk.set ov 1#8)[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
            rw [hmrk_eq]; exact hm_old
          rw [ite_eq_right hm_new, ite_eq_right hm_old, ih_t']
  have hmem_pres : ∀ j ∈ flIdxs mrk k.trl t, j ∈ flIdxs (mrk.set ov 1#8) k.trl t := fun j hj => by
    obtain ⟨hj_lt, hj_nz⟩ := flIdxs_mem_iff.mp hj
    refine flIdxs_mem_iff.mpr ⟨hj_lt, ?_⟩
    by_cases heq : (k.trl[j]?.getD 0#32).toNat / 2 = ov
    · rw [heq, List.getElem?_set_self hov_len]; decide
    · rwa [List.getElem?_set_ne (Ne.symm heq)]
  refine ⟨hlen_set, hmem_pres, fun l hl => ?_, fun m hm_lt hm_eq => ?_⟩
  · unfold flLits at hl ⊢; rw [List.mem_map] at hl ⊢
    obtain ⟨j, hj, rfl⟩ := hl
    exact ⟨j, hmem_pres j hj, rfl⟩
  · refine flLits_mem_already_marked hm_lt ?_
    rw [hm_eq, List.getElem?_set_self hov_len]; decide

theorem fl_resolve_step {F_cur : List (List Nat)} {k : FullCoreState}
    {mrk mrk' : List (BitVec 8)} {t' : Nat} {R_lits : List Nat}
    (hPop : mrk[(k.trl[t']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hEnt : (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits mrk k.trl (t' + 1))))
    (hPres : ∀ l ∈ flLits mrk k.trl t', l ∈ flLits mrk' k.trl t')
    (hRsnEnt : (cnfOfClauses F_cur).EntailsClause (cnfClause R_lits))
    (hRsnIn : ∀ q ∈ R_lits,
      q = (k.trl[t']?.getD 0#32).toNat ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
      q ∈ flLits mrk' k.trl t') :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (flLits mrk' k.trl t')) := by
  rw [CNF.entails_clause_def]; intro α hα
  by_cases hp : (cnfClause [(k.trl[t']?.getD 0#32).toNat ^^^ 1]).Sat α
  · have hpf : ¬ (cnfClause [(k.trl[t']?.getD 0#32).toNat]).Sat α := by
      simpa only [fl_xor1_xor1] using fl_sat_false_of_xor1 hp
    obtain ⟨q, hqm, hqt⟩ :=
      (clause_sat_cnfClause_iff α R_lits).mp (CNF.entails_clause_def.mp hRsnEnt α hα)
    rcases hRsnIn q hqm with hqp | hq0 | hq_in
    · rw [hqp] at hqt; exact absurd ((sat_cnfClause_singleton α _).mpr hqt) hpf
    · have hnf := fl_sat_false_of_xor1 (CNF.entails_clause_def.mp hq0 α hα)
      rw [fl_xor1_xor1] at hnf
      exact absurd ((sat_cnfClause_singleton α q).mpr hqt) hnf
    · exact (clause_sat_cnfClause_iff α _).mpr ⟨q, hq_in, hqt⟩
  · have hfl := CNF.entails_clause_def.mp hEnt α hα
    rw [flLits_succ_marked hPop, clause_sat_cnfClause_iff] at hfl
    obtain ⟨l, hl_mem, hlt⟩ := hfl
    rw [List.mem_cons] at hl_mem
    rcases hl_mem with rfl | hl_tail
    · exact absurd ((sat_cnfClause_singleton α _).mpr hlt) hp
    · exact (clause_sat_cnfClause_iff α _).mpr ⟨l, hPres l hl_tail, hlt⟩

theorem fl_entails_step_falsified {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    {mrk : List (BitVec 8)} {t q : Nat} (_ht_le : t ≤ k.trail_end)
    (hq_lvl0 : (k.lvl[q / 2]?.getD 0#32).toNat = 0 →
      ∃ m < k.trail_end, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1)
    (hq_pos : 0 < (k.lvl[q / 2]?.getD 0#32).toNat →
      mrk[q / 2]?.getD 0#8 ≠ 0#8 ∧ ∃ m < t, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨ q ∈ flLits mrk k.trl t := by
  by_cases hl0 : (k.lvl[q / 2]?.getD 0#32).toNat = 0
  · left
    obtain ⟨m, hm_te, hm_eq⟩ := hq_lvl0 hl0
    have hl0m : (k.lvl[(k.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      rw [hm_eq, fl_xor1_div2]; exact hl0
    simpa [hm_eq] using hw.level0_sound m hm_te hl0m
  · right
    obtain ⟨hmrk, m, hm_t, hm_eq⟩ := hq_pos (Nat.pos_of_ne_zero hl0)
    have hmrk' : mrk[(k.trl[m]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
      rw [hm_eq, fl_xor1_div2]; exact hmrk
    have hmem := flLits_mem_already_marked hm_t hmrk'
    rwa [hm_eq, fl_xor1_xor1] at hmem

/-! ## 4. Failed-Literal Analysis State Invariant & Step Bridges -/

structure FailedStateOk (c : FullCfg) (s s1 : FullState) (cut : Nat) : Prop where
  len : s1.LengthsOk c
  core : s1.core =
    { s.core with mrk := s1.core.mrk, min_clr_len := s1.core.min_clr_len,
                  tmp := s1.core.tmp, tmp_len := s1.core.tmp_len }
  scr : s1.scratch = { s.scratch with work_stk1 := s1.scratch.work_stk1 }
  cov : FullAnaMarksCov c s1
  mb : FailedMarkedCut s s1.core.mrk cut

theorem fl_witnessCut_with_ana {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k)
    {mrk' : List (BitVec 8)} {mcl' tl' tc' : Nat} {tmp' repr' : List (BitVec 32)} :
    FullWitnessCutInv c F0 F_cur cut
      { k with mrk := mrk', min_clr_len := mcl', tmp := tmp',
               tmp_len := tl', tmp_cnt := tc', repr := repr' } :=
  ⟨⟨h.ext_sound, h.inconsistent_sound,
    { h.arena with len_ok := h.arena.len_ok },
    h.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r),
    h.cur_level_le, h.trail_lits_lt, h.trail_vars_nodup, h.vals_domain, h.vals_true_iff,
    h.vals_false_iff, h.lvl_le, h.dec_earliest, h.levels_inhabited, h.level0_sound,
    h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt, h.frame_trail_mono,
    h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below, h.reason_lit_mem_below⟩,
   h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

theorem fl_push_mrk_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState}
    (_hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hok : FailedStateOk c s s1 cut) {ov : Nat}
    (hov_lt : ov < s.core.cur_vars) (hmrk0 : s1.core.mrk[ov]?.getD 0#8 = 0#8)
    (_hmcl_lt : s1.core.min_clr_len < s.core.cur_vars)
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
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
  have hcov' := s13b_push_marksCov_gen hok.len hok.cov (hcv1.symm ▸ hov_lt) hmrk0
    (by decide : (1#8 : BitVec 8) ≠ 0#8)
  have hcv_le := hok.len.core_ok.cur_vars_le
  have hmcl_le2 : s1.core.min_clr_len + 1 ≤ c.max_vars := by
    have hcov_le := hcov'.1
    change s1.core.min_clr_len + 1 ≤ s1.core.cur_vars at hcov_le
    omega
  have hlen' : s2.LengthsOk c :=
    ⟨{ hok.len.core_ok with
        mrk_len := by simp [s2, List.length_set, hok.len.core_ok.mrk_len]
        min_clr_len_le := hmcl_le2 },
     { hok.len.scratch_ok with
       work_stk1_len := by simp [s2, List.length_set, hok.len.scratch_ok.work_stk1_len] }⟩
  have hmb' : FailedMarkedCut s s2.core.mrk cut := fun v hv hnz => by
    by_cases hv_ov : v = ov
    · subst hv_ov; exact ⟨hlvl1, hm_cut⟩
    · have hnz' : s1.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
        simpa [s2, List.getElem?_set_ne (Ne.symm hv_ov)] using hnz
      exact fl_mb_get hok.mb hv hnz'
  exact ⟨hlen', by dsimp only [s2]; rw [hok.core], by dsimp only [s2]; rw [hok.scr], hcov', hmb'⟩

theorem fl_failedStateOk_with_tmp {c : FullCfg} {s s1 : FullState} {cut : Nat}
    (hok : FailedStateOk c s s1 cut) {tmp' : List (BitVec 32)}
    (htlen : tmp'.length = c.max_vars) :
    FailedStateOk c s { s1 with core := { s1.core with tmp := tmp' } } cut :=
  ⟨⟨{ hok.len.core_ok with tmp_len_arr := htlen }, hok.len.scratch_ok⟩,
   by dsimp only; rw [hok.core], hok.scr, hok.cov, hok.mb⟩

theorem fl_otfsInvW_of_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState}
    (hcut : FullCutInvW c F0 F_cur cut s) (hok : FailedStateOk c s s1 cut)
    (hmrk0 : ∀ v < c.max_vars, s1.core.mrk[v]?.getD 0#8 = 0#8) :
    FullOtfsInvW c F0 F_cur s1 := by
  have hwt_s1 := fl_witnessCut_with_ana hcut.2.1 (mrk' := s1.core.mrk)
    (mcl' := s1.core.min_clr_len) (tl' := s1.core.tmp_len) (tc' := s.core.tmp_cnt)
    (tmp' := s1.core.tmp) (repr' := s.core.repr)
  have hs1_eq : s1.core = { s.core with
      mrk := s1.core.mrk, min_clr_len := s1.core.min_clr_len, tmp := s1.core.tmp,
      tmp_len := s1.core.tmp_len, tmp_cnt := s.core.tmp_cnt, repr := s.core.repr } := by
    rw [hok.core]
  have hw_clr : FullOtfsWitnessInv c F0 F_cur s1.core :=
    hs1_eq ▸ hwt_s1.toFullOtfsWitnessInv
  have hlm_clr : FullLitMarksClear c s1 :=
    ⟨hmrk0, fun l hl => by rw [hok.core]; exact hcut.2.2.1.2 l hl⟩
  have hnd_clr : FullArenaVarsNodup s1 := by
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hok.core]; exact hcut.2.2.2.1
  have hpres_s1 : FullExtScratchPres s s1 := by
    unfold FullExtScratchPres; rw [hok.scr]; exact ⟨rfl, rfl⟩
  have hext_clr : FullExtScratchOk c s1 :=
    FullExtScratchOk.of_pres hcut.2.2.2.2.1 hpres_s1
      fun r hr => by unfold fullArenaClauseRefs; rwa [hok.core]
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

theorem fl_mark_lit_push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hcl1 : s.core.cur_level = 1)
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
    (flIdxs s2.core.mrk s.core.trl t).length = (flIdxs s1.core.mrk s.core.trl t).length + 1 ∧
    (∀ l ∈ flLits s1.core.mrk s.core.trl t, l ∈ flLits s2.core.mrk s.core.trl t) ∧
    ((cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
      q ∈ flLits s2.core.mrk s.core.trl t) := by
  intro ov ov32 s2
  have hov_lt : ov < s.core.cur_vars := by omega
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
  have hmcl_lt : s1.core.min_clr_len < s.core.cur_vars := by
    obtain ⟨hmcl_le, hnd, hent, _⟩ := hok.cov
    rw [hcv1] at hmcl_le hent
    refine inj_lt_of_missing (fun i => (s1.scratch.work_stk1[i]?.getD 0#32).toNat) ?_
      (fun i hi => (hent i hi).1) hov_lt fun i hi heq => ?_
    · intro i j hi hj hij_eq
      by_cases hij : i = j
      · exact hij
      · have hwlen : s1.core.min_clr_len ≤ s1.scratch.work_stk1.length := by
          rw [hok.len.scratch_ok.work_stk1_len]; have := hok.len.core_ok.cur_vars_le; omega
        have htk_len : (s1.scratch.work_stk1.take s1.core.min_clr_len).length =
            s1.core.min_clr_len := by rw [List.length_take, Nat.min_eq_left hwlen]
        have hmap_len : ((s1.scratch.work_stk1.take s1.core.min_clr_len).map BitVec.toNat).length =
            s1.core.min_clr_len := by rw [List.length_map, htk_len]
        have hpw := List.pairwise_iff_getElem.mp hnd
        have hi_stk : i < s1.scratch.work_stk1.length := Nat.lt_of_lt_of_le hi hwlen
        have hj_stk : j < s1.scratch.work_stk1.length := Nat.lt_of_lt_of_le hj hwlen
        rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
        · have hne := hpw i j (by rw [hmap_len]; exact hi) (by rw [hmap_len]; exact hj) hlt
          simp [List.getElem_take, List.getElem?_eq_getElem hi_stk,
            List.getElem?_eq_getElem hj_stk] at hij_eq hne
          exact absurd hij_eq hne
        · have hne := hpw j i (by rw [hmap_len]; exact hj) (by rw [hmap_len]; exact hi) hgt
          simp [List.getElem_take, List.getElem?_eq_getElem hi_stk,
            List.getElem?_eq_getElem hj_stk] at hij_eq hne
          exact absurd hij_eq.symm hne
    · have hmnz := (hok.cov.2.2.1 i hi).2
      rw [heq] at hmnz; exact hmnz hmrk0
  obtain ⟨mc, hmc_cut, hmc_eq⟩ := hq_cut
  obtain ⟨mt, hmt_t, hmt_eq⟩ := hq_t
  have hmc_te : mc < s.core.trail_end := Nat.lt_of_lt_of_le hmc_cut hw.cut_le
  have hlvl1 : (s.core.lvl[ov]?.getD 0#32).toNat = 1 := by
    have hlv_le := hw.lvl_le mc hmc_te
    rw [hmc_eq, fl_xor1_div2, hcl1] at hlv_le
    have hlv_pos : 0 < (s.core.lvl[ov]?.getD 0#32).toNat := by simpa [ov] using hlvl_pos
    exact Nat.le_antisymm hlv_le hlv_pos
  have hok2 := fl_push_mrk_inv hw hok hov_lt hmrk0 hmcl_lt hlvl1
    ⟨mc, hmc_cut, by rw [hmc_eq, fl_xor1_div2]⟩
  have hov_mrk : ov < s1.core.mrk.length := by
    rw [hok.len.core_ok.mrk_len]; have := hok.len.core_ok.cur_vars_le; omega
  have hidx := flIdxs_set_marked hw ht_le hov_mrk hmrk0
    ⟨mt, hmt_t, by rw [hmt_eq, fl_xor1_div2]⟩
  have hmem := hidx.2.2.2 mt hmt_t (by rw [hmt_eq, fl_xor1_div2])
  rw [hmt_eq, fl_xor1_xor1] at hmem
  exact ⟨hmcl_lt, hok2, hidx.1, hidx.2.2.1, Or.inr hmem⟩

theorem fl_mark_lit_skip {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (_hcl1 : s.core.cur_level = 1)
    {t q : Nat} (ht_le : t ≤ s.core.trail_end)
    (hq_lvl0 : (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 →
      ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1)
    (hq_pos : 0 < (s.core.lvl[q / 2]?.getD 0#32).toNat →
      s1.core.mrk[q / 2]?.getD 0#8 ≠ 0#8 ∧ ∃ m < t, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1]) ∨
      q ∈ flLits s1.core.mrk s.core.trl t :=
  fl_entails_step_falsified hw ht_le hq_lvl0 hq_pos

theorem s13_fl_post_otfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s s_t : FullState} {ucnt_f : Nat}
    (hcut : FullCutInvW c F0 F_cur cut s) (hcl1 : s.core.cur_level = 1)
    (hok_t : FailedStateOk c s s_t cut) (ht_tmp : s_t.core.tmp_len = ucnt_f + 1)
    {mrk_b : List (BitVec 8)} {mcl_b : Nat} {repr_b : List (BitVec 32)} {sc_b : FullScratch}
    (hlen_b : FullState.LengthsOk c
      { s_t with
        core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b, repr := repr_b },
        scratch := sc_b })
    (hcov_b : FullAnaMarksCov c
      { s_t with
        core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b, repr := repr_b },
        scratch := sc_b })
    (hpres_b : FullExtScratchPres s_t
      { s_t with
        core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b, repr := repr_b },
        scratch := sc_b })
    (hws2_b : sc_b.work_stk2 = s_t.scratch.work_stk2)
    {mrk_c : List (BitVec 8)} (hml_c : mrk_c.length = c.max_vars)
    (hclr_c : FullAnaMarksCov c
        { s_t with
          core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b, repr := repr_b },
          scratch := sc_b } →
      ∀ v < c.max_vars, mrk_c[v]?.getD 0#8 = 0#8) :
    let s_b : FullState :=
      { s_t with
        core := { s_t.core with mrk := mrk_b, min_clr_len := mcl_b, repr := repr_b },
        scratch := sc_b }
    let s_c : FullState := { s_b with core := { s_b.core with mrk := mrk_c, min_clr_len := 0 } }
    s_c.LengthsOk c ∧ FullOtfsInvW c F0 F_cur s_c ∧ FullOtfsWitnessInv c F0 F_cur s_c.core ∧
    s_c.core.cur_level = 1 ∧ s_c.core.cur_vars = s.core.cur_vars ∧
    s_c.core.fuel = s.core.fuel ∧ s_c.core.dense_mode = s.core.dense_mode ∧
    s_c.scratch.work_stk2 = s.scratch.work_stk2 ∧ s_c.core.tmp = s_t.core.tmp := by
  intro s_b s_c
  obtain ⟨_, hw0, hlm0, hnd0, hext0, hdm0⟩ := hcut
  have hwt_c := fl_witnessCut_with_ana hw0 (mrk' := mrk_c) (mcl' := 0) (tl' := ucnt_f + 1)
    (tc' := s.core.tmp_cnt) (tmp' := s_t.core.tmp) (repr' := repr_b)
  have hsc_eq : s_c.core = { s.core with
      mrk := mrk_c, min_clr_len := 0, tmp := s_t.core.tmp, tmp_len := ucnt_f + 1,
      tmp_cnt := s.core.tmp_cnt, repr := repr_b } := by
    dsimp only [s_c, s_b]; rw [hok_t.core, ht_tmp]
  have hlen_c : s_c.LengthsOk c :=
    ⟨{ hlen_b.core_ok with mrk_len := hml_c, min_clr_len_le := Nat.zero_le _ },
     hlen_b.scratch_ok⟩
  have hpres_t : FullExtScratchPres s s_t := by
    unfold FullExtScratchPres; rw [hok_t.scr]; exact ⟨rfl, rfl⟩
  have hpres_c : FullExtScratchPres s s_c :=
    ⟨by dsimp only [s_c, s_b]; exact hpres_b.1.trans hpres_t.1,
     by dsimp only [s_c, s_b]; exact hpres_b.2.trans hpres_t.2⟩
  have hw_c : FullOtfsWitnessInv c F0 F_cur s_c.core := hsc_eq ▸ hwt_c.toFullOtfsWitnessInv
  have hlm_c : FullLitMarksClear c s_c :=
    ⟨hclr_c hcov_b, fun l hl => by rw [hsc_eq]; exact hlm0.2 l hl⟩
  have hnd_c : FullArenaVarsNodup s_c := by
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hsc_eq]; exact hnd0
  have hext_c : FullExtScratchOk c s_c :=
    FullExtScratchOk.of_pres hext0 hpres_c fun r hr => by
      unfold fullArenaClauseRefs; rwa [hsc_eq]
  have hsc_otfs : FullOtfsInvW c F0 F_cur s_c :=
    ⟨hlen_c, hw_c, hlm_c, hnd_c, hext_c, by rw [hsc_eq]; exact hdm0⟩
  exact ⟨hlen_c, hsc_otfs, hw_c, by rw [hsc_eq]; exact hcl1, by rw [hsc_eq],
    by rw [hsc_eq], by rw [hsc_eq], by dsimp only [s_c, s_b]; rw [hws2_b, hok_t.scr],
    by rw [hsc_eq]⟩

theorem fl_bv64_add1_eq {x : Nat} (hx : x + 1 < 2 ^ 64) :
    BitVec.ofNat 64 x + 1 = BitVec.ofNat 64 (x + 1) :=
  BitVec.eq_of_toNat_eq (by
    have hx0 : x < 2 ^ 64 := by omega
    rw [show (1 : BitVec 64) = 1#64 from rfl, BitVec.toNat_add,
      p2_bv64_ofNat_toNat hx0, p2_bv64_ofNat_toNat hx,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx])

theorem fl_bv64_sub1_eq {x : Nat} (hpos : 0 < x) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x - 1 = BitVec.ofNat 64 (x - 1) :=
  BitVec.eq_of_toNat_eq (by
    rw [show (1 : BitVec 64) = 1#64 from rfl,
      fl_bv64_sub1_toNat (by rw [p2_bv64_ofNat_toNat hx]; omega),
      p2_bv64_ofNat_toNat hx, p2_bv64_ofNat_toNat (by omega)])

theorem p2_bv32_lshr_eq {q : BitVec 32} :
    BitVec.ofNat 32 (q.toNat / 2) = q >>> 1 :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show q >>> 1 = q >>> 1#32 from rfl, fl_bv32_lshr1])

theorem fl_take_succ_list {α : Type} (xs : List α) {i : Nat} (hi : i < xs.length)
    (P : α → Prop) (hpre : ∀ q ∈ xs.take i, P q) (hiP : P (xs[i]'hi)) :
    ∀ q ∈ xs.take (i + 1), P q := by
  intro q hq
  rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hpre q hq
  · exact hiP

theorem p2_clear_ok {c : FullCfg} {s s_f : FullState} {cut : Nat}
    (hok : FailedStateOk c s s_f cut) {mrk' : List (BitVec 8)}
    (hml : mrk'.length = c.max_vars)
    (hmrk0 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) :
    let s_c : FullState := { s_f with core := { s_f.core with mrk := mrk', min_clr_len := 0 } }
    FailedStateOk c s s_c cut := by
  intro s_c
  refine ⟨⟨{ hok.len.core_ok with mrk_len := hml, min_clr_len_le := Nat.zero_le _ },
    hok.len.scratch_ok⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only [s_c]; rw [hok.core]
  · dsimp only [s_c]; rw [hok.scr]
  · exact ⟨Nat.zero_le _, by simp [s_c], fun _ hk => absurd hk (Nat.not_lt_zero _),
      fun v hv hnz => absurd (hmrk0 v hv) hnz⟩
  · have hcv_le := hok.len.core_ok.cur_vars_le
    have hcv_eq : s_f.core.cur_vars = s.core.cur_vars := by rw [hok.core]
    exact fl_mb_empty (fun v hv => hmrk0 v (by omega))

theorem p2_bt_sp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s_c : FullState}
    (hsc_otfs : FullOtfsInvW c F0 F_cur s_c) (hcl_c : s_c.core.cur_level = 1)
    (hcv_c : s_c.core.cur_vars = s.core.cur_vars) (hfu_c : s_c.core.fuel = s.core.fuel)
    (hdm_c : s_c.core.dense_mode = s.core.dense_mode)
    (hws2_c : s_c.scratch.work_stk2 = s.scratch.work_stk2)
    {vals_bt : List (BitVec 8)} {lvl_bt rsns_bt trl_bt tp_bt : List (BitVec 32)}
    {te_bt prop_bt cl_bt : Nat} {unass_bt : BitVec 64} {sc_bt : FullScratch}
    (hbt_len : FullState.LengthsOk c
      { s_c with
        core := { s_c.core with
          vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
          trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
          cur_level := cl_bt, unassigned := unass_bt },
        scratch := sc_bt })
    (hbt_cl : cl_bt = Nat.min s_c.core.cur_level 0)
    (hbt_pres : FullProbeScratchPres s_c
      { s_c with
        core := { s_c.core with
          vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
          trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
          cur_level := cl_bt, unassigned := unass_bt },
        scratch := sc_bt })
    (hbt_wo : ∀ F0' F_cur', FullOtfsWitnessInv c F0' F_cur' s_c.core → 0 < s_c.core.cur_level →
      FullWitnessInv c F0' F_cur' { s_c.core with
        vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
        trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
        cur_level := cl_bt, unassigned := unass_bt }) :
    let s_bt : FullState :=
      { s_c with
        core := { s_c.core with
          vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt, trl := trl_bt,
          trail_pos := tp_bt, trail_end := te_bt, propagated := prop_bt,
          cur_level := cl_bt, unassigned := unass_bt },
        scratch := sc_bt }
    FullSparseInvW c F0 F_cur s_bt ∧ s_bt.core.cur_level = 0 ∧
    s_bt.core.cur_vars = s.core.cur_vars ∧ s_bt.core.fuel = s.core.fuel ∧
    s_bt.core.dense_mode = s.core.dense_mode ∧ s_bt.scratch.work_stk2 = s.scratch.work_stk2 ∧
    s_bt.core.tmp = s_c.core.tmp := by
  intro s_bt
  have hw_bt := hbt_wo F0 F_cur hsc_otfs.2.1 (by omega)
  have hsp : FullSparseInvW c F0 F_cur s_bt := by
    refine ⟨hbt_len, hw_bt, hsc_otfs.2.2.1, ?_,
      FullExtScratchOk.of_pres hsc_otfs.2.2.2.2.1 hbt_pres.1
        (fun _ h => by unfold fullArenaClauseRefs fullArenaClauseRefsCore at h ⊢; exact h),
      hsc_otfs.2.2.2.2.2⟩
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
      fullArenaClauseGarb fullArenaClauseGarbCore fullArenaClauseLits
      fullArenaClauseLitsCore fullArenaClauseSizeCore fullArenaHdrCore
    exact hsc_otfs.2.2.2.1
  exact ⟨hsp, by dsimp only [s_bt]; rw [hbt_cl]; exact Nat.min_zero _,
    hcv_c, hfu_c, hdm_c, hbt_pres.2.2.1.trans hws2_c, rfl⟩

theorem p2_lvl_pos_of_lt {c : FullCfg} {s s1 : FullState} {cut v : Nat}
    (hok : FailedStateOk c s s1 cut) (hv_lt : v < s1.core.lvl.length)
    (hpos : (0#32).toNat < (s1.core.lvl[v]'hv_lt).toNat) :
    0 < (s.core.lvl[v]?.getD 0#32).toNat := by
  have heql : s1.core.lvl[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 := by rw [hok.core]
  rw [← heql, List.getElem?_eq_getElem hv_lt, Option.getD_some]
  exact hpos

theorem p2_lvl0_of_nlt {c : FullCfg} {s s1 : FullState} {cut v : Nat}
    (hok : FailedStateOk c s s1 cut) (hv_lt : v < s1.core.lvl.length)
    (hno : ¬ (0#32).toNat < (s1.core.lvl[v]'hv_lt).toNat) :
    (s.core.lvl[v]?.getD 0#32).toNat = 0 := by
  have heql : s1.core.lvl[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 := by rw [hok.core]
  rw [← heql, List.getElem?_eq_getElem hv_lt, Option.getD_some]
  have h0 : (0#32 : BitVec 32).toNat = 0 := rfl
  omega

theorem p2_push_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut t : Nat}
    {s s1 : FullState} {q : BitVec 32}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hcl1 : s.core.cur_level = 1)
    (hok : FailedStateOk c s s1 cut) (ht_le : t ≤ s.core.trail_end)
    (hq_lt : q.toNat < 2 * s.core.cur_vars)
    (hmrk0 : s1.core.mrk[q.toNat / 2]?.getD 0#8 = 0#8)
    (hlvl_pos : 0 < (s.core.lvl[q.toNat / 2]?.getD 0#32).toNat)
    (hq_t : ∃ m < t, (s.core.trl[m]?.getD 0#32).toNat = q.toNat ^^^ 1)
    (hq_cut : ∃ m < cut, (s.core.trl[m]?.getD 0#32).toNat = q.toNat ^^^ 1) :
    let ov := q.toNat / 2
    let s2 : FullState :=
      { core := { s1.core with mrk := s1.core.mrk.set ov 1#8,
                               min_clr_len := s1.core.min_clr_len + 1 }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len (q >>> 1) } }
    s1.core.min_clr_len < s.core.cur_vars ∧
    s1.core.min_clr_len < 2 ^ 64 ∧
    (BitVec.ofNat 64 s1.core.min_clr_len).toNat < s1.scratch.work_stk1.length ∧
    (BitVec.ofNat 64 s1.core.min_clr_len + 1).toNat = s1.core.min_clr_len + 1 ∧
    FailedStateOk c s s2 cut ∧
    (flIdxs s2.core.mrk s.core.trl t).length = (flIdxs s1.core.mrk s.core.trl t).length + 1 ∧
    (∀ l ∈ flLits s1.core.mrk s.core.trl t, l ∈ flLits s2.core.mrk s.core.trl t) ∧
    ((cnfOfClauses F_cur).EntailsClause (cnfClause [q.toNat ^^^ 1]) ∨
      q.toNat ∈ flLits s2.core.mrk s.core.trl t) := by
  intro ov s2
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hok.len.core_ok.cur_vars_le
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hok.core]
  obtain ⟨hmcl_lt, hok2, hlen2, hpres2, hin2⟩ :=
    fl_mark_lit_push hw hcl1 hok ht_le hq_lt hmrk0 hlvl_pos hq_t hq_cut
  have hmcl_eq : BitVec.ofNat 32 ov = q >>> 1 := p2_bv32_lshr_eq
  have hmcl64 : s1.core.min_clr_len < 2 ^ 64 := by omega
  have hws_lt : (BitVec.ofNat 64 s1.core.min_clr_len).toNat < s1.scratch.work_stk1.length := by
    rw [p2_bv64_ofNat_toNat hmcl64, hok.len.scratch_ok.work_stk1_len]; omega
  have hmcl1 : (BitVec.ofNat 64 s1.core.min_clr_len + 1).toNat = s1.core.min_clr_len + 1 := by
    rw [fl_bv64_add1_eq (by omega), p2_bv64_ofNat_toNat (by omega)]
  refine ⟨hmcl_lt, hmcl64, hws_lt, hmcl1,
    by simpa only [s2, ov, hmcl_eq] using hok2,
    by simpa only [s2, ov, hmcl_eq] using hlen2,
    by simpa only [s2, ov, hmcl_eq] using hpres2,
    by simpa only [s2, ov, hmcl_eq] using hin2⟩

theorem p2_arena_clause_sz {c : FullCfg} {s s1 : FullState}
    (hcl : s.LengthsOk c) (hl1 : s1.LengthsOk c) (hcore : s1.core.arena = s.core.arena)
    (_hal_eq : s1.core.arena_len = s.core.arena_len) {r32 : BitVec 32} {cref : Nat}
    (hr_eq : r32.toNat = cref)
    (hwf : cref + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core cref ∧
      cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena_len ∧
      s.core.arena_len ≤ c.arena_cap ∧ c.arena_cap = s.core.arena.length) :
    let rsz := s1.core.arena[(r32.setWidth 64 + 2#64).toNat]'(by
      have := c.harena; unfold dimacsBound at this
      rw [hl1.core_ok.arena_len_arr, BitVec.toNat_add, fl_bv32_setWidth64,
        show (2#64 : BitVec 64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega : r32.toNat + 2 < 2 ^ 64)]
      have := hcl.core_ok.arena_len_le; omega)
    (r32.setWidth 64 + 2#64).toNat < s1.core.arena.length ∧
    rsz.toNat = fullArenaClauseSizeCore s.core r32.toNat ∧
    cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length ∧
    (fullArenaClauseLitsCore s.core cref).length = rsz.toNat := by
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hal_le := hl1.core_ok.arena_len_le
  have hadd2 : (r32.setWidth 64 + 2#64).toNat < s1.core.arena.length := by
    rw [hl1.core_ok.arena_len_arr, BitVec.toNat_add, fl_bv32_setWidth64,
      show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega : r32.toNat + 2 < 2 ^ 64)]
    omega
  have hrsz_eq : (s1.core.arena[(r32.setWidth 64 + 2#64).toNat]'hadd2).toNat =
      fullArenaClauseSizeCore s.core r32.toNat := by
    rw [hr_eq]; unfold fullArenaClauseSizeCore
    have hidx : cref + 2 < s.core.arena.length := by omega
    have hget : s1.core.arena[(r32.setWidth 64 + 2#64).toNat]'hadd2 =
        s.core.arena[cref + 2]'hidx := by
      refine p2_getElem_congr_list hcore ?_
      rw [BitVec.toNat_add, fl_bv32_setWidth64, show (2#64 : BitVec 64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega : r32.toNat + 2 < 2 ^ 64), hr_eq]
    rw [hget, List.getElem?_eq_getElem hidx, Option.getD_some]
  refine ⟨hadd2, hrsz_eq, by omega, ?_⟩
  rw [hrsz_eq, hr_eq]; exact fl_arenaClauseLitsCore_length (by omega)

end

end LeanQbe.T.Examples.Kissat.Proof.Analyze.WpFailedLit
