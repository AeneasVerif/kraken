module

public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas2

/-!
# Kissat `D-Full` `full_hbr_dom` & `full_probe_prop_lit` Proofs (`Stage 4`, Part 3)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullProbeTransSpecs FullProbeTransHelpers

section HbrDomProofHelpers

private theorem u8_zext32_eq0_iff (v : BitVec 8) :
    (BitVec.setWidth 32 v = 0#32) ↔ v = 0#8 := by revert v; decide

private theorem hbrDom_mark_hlvl1 {cv ov : Nat} {lvl : List (BitVec 32)}
    {mrk : List (BitVec 8)}
    (hl1 : ∀ w < cv, mrk[w]?.getD 0#8 ≠ 0#8 → (lvl[w]?.getD 0#32).toNat = 1)
    (hov : (lvl[ov]?.getD 0#32).toNat = 1) :
    ∀ w < cv, (mrk.set ov 1#8)[w]?.getD 0#8 ≠ 0#8 → (lvl[w]?.getD 0#32).toNat = 1 := by
  intro w hw hne
  by_cases hwv : w = ov
  · rwa [hwv]
  · rw [List.getElem?_set_ne (Ne.symm hwv)] at hne; exact hl1 w hw hne

private theorem hbrDom_mark_cov {n ov base : Nat} (P : Nat → Prop) {ar lvl : List (BitVec 32)}
    {mrk : List (BitVec 8)}
    (hcov : ∀ k < n, let l := (ar[base + k]?.getD 0#32).toNat
      P l → (lvl[l / 2]?.getD 0#32).toNat = 1 → mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hget : (ar[base + n]?.getD 0#32).toNat / 2 = ov) (hov : ov < mrk.length) :
    ∀ k < n + 1, let l := (ar[base + k]?.getD 0#32).toNat
      P l → (lvl[l / 2]?.getD 0#32).toNat = 1 → (mrk.set ov 1#8)[l / 2]?.getD 0#8 ≠ 0#8 := by
  intro k hk l hp hlv1
  by_cases hkn : k = n
  · subst hkn; dsimp only [l]; rw [hget, List.getElem?_set_self hov, Option.getD_some]; decide
  · have prev := hcov k (by omega) hp hlv1
    by_cases heqv : (ar[base + k]?.getD 0#32).toNat / 2 = ov
    · dsimp only [l]; rw [heqv, List.getElem?_set_self hov, Option.getD_some]; decide
    · dsimp only [l]; rw [List.getElem?_set_ne (Ne.symm heqv)]; exact prev

private theorem hbrDom_mono_set {cv ov : Nat} {mrk0 mrk : List (BitVec 8)}
    (hm : ∀ w < cv, mrk0[w]?.getD 0#8 ≠ 0#8 → mrk[w]?.getD 0#8 ≠ 0#8)
    (hov : ov < mrk.length) :
    ∀ w < cv, mrk0[w]?.getD 0#8 ≠ 0#8 → (mrk.set ov 1#8)[w]?.getD 0#8 ≠ 0#8 := by
  intro w hw hne
  by_cases hwv : w = ov
  · rw [hwv, List.getElem?_set_self hov, Option.getD_some]; decide
  · rw [List.getElem?_set_ne (Ne.symm hwv)]; exact hm w hw hne

private theorem hbrDom_step_same {n base ex : Nat} {ar lvl : List (BitVec 32)}
    {mrk : List (BitVec 8)}
    (hcov : ∀ k < n, let l := (ar[base + k]?.getD 0#32).toNat
      l ≠ ex → (lvl[l / 2]?.getD 0#32).toNat = 1 → mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hln : (ar[base + n]?.getD 0#32).toNat = ex ∨
      (lvl[(ar[base + n]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ 1 ∨
      mrk[(ar[base + n]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    ∀ k < n + 1, let l := (ar[base + k]?.getD 0#32).toNat
      l ≠ ex → (lvl[l / 2]?.getD 0#32).toNat = 1 → mrk[l / 2]?.getD 0#8 ≠ 0#8 := by
  intro k hk l hneq hlv1
  by_cases hkn : k = n
  · subst hkn; rcases hln with h | h | h; exact absurd h hneq; exact absurd hlv1 h; exact h
  · exact hcov k (by omega) hneq hlv1

private theorem hbrDom_clear_step_cov {cv k clen ov : Nat} {mrkk : List (BitVec 8)}
    {clr : List (BitVec 32)} (hov_eq : (clr[k]?.getD 0#32).toNat = ov)
    (hov_lt : ov < mrkk.length)
    (hcovk : ∀ w < cv, mrkk[w]?.getD 0#8 ≠ 0#8 →
      ∃ t, k ≤ t ∧ t < clen ∧ (clr[t]?.getD 0#32).toNat = w) :
    ∀ w < cv, (mrkk.set ov 0#8)[w]?.getD 0#8 ≠ 0#8 →
      ∃ t, k + 1 ≤ t ∧ t < clen ∧ (clr[t]?.getD 0#32).toNat = w := by
  intro w hw hne
  by_cases hwe : w = ov
  · rw [hwe, List.getElem?_set_self hov_lt, Option.getD_some] at hne; exact absurd rfl hne
  · rw [List.getElem?_set_ne (Ne.symm hwe)] at hne
    obtain ⟨t, htk, htcl, hteq⟩ := hcovk w hw hne
    refine ⟨t, ?_, htcl, hteq⟩
    by_cases htk0 : t = k
    · subst htk0; rw [hov_eq] at hteq; exact absurd hteq.symm hwe
    · omega

private theorem hbrDom_clear_fin {c : FullCfg} {mrk0 mrkk : List (BitVec 8)}
    {clr' : List (BitVec 32)} {cv clen : Nat}
    (hm0 : ∀ v < c.max_vars, mrk0[v]?.getD 0#8 = 0#8)
    (_hcv_le : cv ≤ c.max_vars) (hml0 : mrk0.length = c.max_vars) (hmkl : mrkk.length = c.max_vars)
    (hout : ∀ w, cv ≤ w → w < c.max_vars → mrkk[w]? = mrk0[w]?)
    (hcov : ∀ w < cv, mrkk[w]?.getD 0#8 ≠ 0#8 →
      ∃ t, clen ≤ t ∧ t < clen ∧ (clr'[t]?.getD 0#32).toNat = w) :
    mrkk = mrk0 := by
  apply List.ext_getElem (hmkl.trans hml0.symm)
  intro w hw1 hw2
  by_cases hwv : w < cv
  · have hz : mrkk[w]?.getD 0#8 = 0#8 := by
      by_cases hne : mrkk[w]?.getD 0#8 = 0#8
      · exact hne
      · obtain ⟨t, ht1, ht2, _⟩ := hcov w hwv hne; omega
    have hz0 := hm0 w (by omega)
    rw [List.getElem?_eq_getElem hw1, Option.getD_some] at hz
    rw [List.getElem?_eq_getElem hw2, Option.getD_some] at hz0
    exact hz.trans hz0.symm
  · have hopt := hout w (by omega) (by omega)
    rw [List.getElem?_eq_getElem hw1, List.getElem?_eq_getElem hw2, Option.some.injEq] at hopt
    exact hopt

private theorem hbrDom_sat_lvl1_of_false_trl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hcl1 : s.core.cur_level = 1) {t l : Nat} (ht : t < s.core.trail_end)
    (htrl : (s.core.trl[t]?.getD 0#32).toNat = l ^^^ 1)
    {α : Nat → Bool} (hα : (cnfOfClauses F_cur).Sat α)
    (hsat : α (litVar l) = !(litSign l)) :
    (s.core.lvl[l / 2]?.getD 0#32).toNat = 1 := by
  have hle := hw.lvl_le
  have hl0 := hw.level0_sound
  dsimp only [withEmptyModeWatches] at hle hl0
  have hle1 : (s.core.lvl[(s.core.trl[t]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ 1 := by
    have := hle t ht; omega
  rw [htrl, fullInv_var_xor1] at hle1
  by_cases hz : (s.core.lvl[l / 2]?.getD 0#32).toNat = 0
  · exfalso
    have he0 := hl0 t ht (by rwa [htrl, fullInv_var_xor1])
    rw [htrl] at he0
    have hs0 := (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp he0 α hα)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    obtain ⟨q, rfl, hqsat⟩ := hs0
    change α (litVar (litNeg l)) = !(litSign (litNeg l)) at hqsat
    rw [litVar_litNeg, litSign_litNeg, Bool.not_not] at hqsat
    cases litSign l <;> simp_all
  · omega

private theorem hbrDom_sat_neg_trl {q : Nat} {trl_val : Nat} (htrl : trl_val = q ^^^ 1)
    {α : Nat → Bool} (hsat : α (litVar q) = !(litSign q)) :
    α (litVar trl_val) = litSign trl_val := by
  rw [htrl]
  change α (litVar (litNeg q)) = litSign (litNeg q)
  rw [litVar_litNeg, litSign_litNeg]
  exact hsat

private theorem hbrDom_init_reach {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hcl1 : s.core.cur_level = 1) {cref : Nat} (hcref : cref ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref = false)
    (hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length)
    {implied : Nat} {mrk : List (BitVec 8)}
    (hfal : ∀ l ∈ fullArenaClauseLits s cref, l ≠ implied → s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hcov : ∀ k < fullArenaClauseSize s cref,
      let l := (s.core.arena[cref + 3 + k]?.getD 0#32).toNat
      l ≠ implied → (s.core.lvl[l / 2]?.getD 0#32).toNat = 1 → mrk[l / 2]?.getD 0#8 ≠ 0#8) :
    ∀ α, (cnfOfClauses F_cur).Sat α → α (litVar implied) = litSign implied →
      domReach s.core mrk s.core.trail_end α := by
  intro α hα himf
  have hent := hw.arena.entails cref hcref hng
  have hcl_sat := (CNF.entails_clause_def.mp hent) α hα
  obtain ⟨l, hl_mem, hl_sat⟩ := (clause_sat_cnfClause_iff α _).mp hcl_sat
  have hl_ne : l ≠ implied := by
    intro heq; rw [heq] at hl_sat
    cases hl_s : litSign implied <;> simp_all
  have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt cref hcref hng l hl_mem
  have hvf := hw.vals_false_iff l hl_lt
  dsimp only [withEmptyModeWatches] at hvf
  obtain ⟨t, ht, htrl⟩ := hvf.mp (hfal l hl_mem hl_ne)
  have hl_lvl1 := hbrDom_sat_lvl1_of_false_trl hw hcl1 ht htrl hα hl_sat
  obtain ⟨k, hk, hgetk⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl_mem
  have hk' : k < fullArenaClauseSize s cref := hk
  have hgetk' : (s.core.arena[cref + 3 + k]?.getD 0#32).toNat = l := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hgetk
  have hmk_l := hcov k hk' (by rwa [hgetk']) (by rwa [hgetk'])
  rw [hgetk'] at hmk_l
  exact ⟨t, ht, by rwa [htrl, fullInv_var_xor1], hbrDom_sat_neg_trl htrl hl_sat⟩

private theorem hbrDom_bin_false {F_cur : List (List Nat)} {p ot : Nat}
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]))
    {α : Nat → Bool} (hα : (cnfOfClauses F_cur).Sat α)
    (hfp : α (litVar p) = litSign p) : α (litVar ot) = !(litSign ot) := by
  obtain ⟨q, hq, hq_sat⟩ :=
    (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hent α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exfalso; cases hls : litSign q <;> simp_all
  · exact hq_sat

private theorem hbrDom_bin_no_add_reach {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hcl1 : s.core.cur_level = 1) {mrk : List (BitVec 8)} {idx implied ot : Nat}
    (_hidx_lt : idx < s.core.trail_end) (_hot_lt : ot < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(s.core.trl[idx]?.getD 0#32).toNat, ot]))
    {m_w : Nat} (hm_w : m_w < idx) (hmw_eq : (s.core.trl[m_w]?.getD 0#32).toNat = ot ^^^ 1)
    (_hmw_lvl : (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hreach : ∀ α, (cnfOfClauses F_cur).Sat α → α (litVar implied) = litSign implied →
      domReach s.core mrk (idx + 1) α)
    (hcase : mrk[ot / 2]?.getD 0#8 ≠ 0#8 ∨ (s.core.lvl[ot / 2]?.getD 0#32).toNat ≠ 1) :
    ∀ α, (cnfOfClauses F_cur).Sat α → α (litVar implied) = litSign implied →
      domReach s.core mrk idx α := by
  intro α hα himf
  obtain ⟨t, ht, hmt, hfal_t⟩ := hreach α hα himf
  by_cases hteq : t = idx
  · subst hteq
    have hot_sat := hbrDom_bin_false hent hα hfal_t
    rcases hcase with hm_ne | hlv_ne
    · refine ⟨m_w, hm_w, by rwa [hmw_eq, fullInv_var_xor1], hbrDom_sat_neg_trl hmw_eq hot_sat⟩
    · exfalso
      exact hlv_ne (hbrDom_sat_lvl1_of_false_trl hw hcl1 (by omega : m_w < s.core.trail_end)
        hmw_eq hα hot_sat)
  · exact ⟨t, by omega, hmt, hfal_t⟩

private theorem hbrDom_bin_add_reach {F_cur : List (List Nat)} {k : FullCoreState}
    {mrk : List (BitVec 8)} {idx implied ot ov m_w : Nat}
    (hov_eq : ov = ot / 2) (hov_lt : ov < mrk.length) (hm_w : m_w < idx)
    (hmw_eq : (k.trl[m_w]?.getD 0#32).toNat = ot ^^^ 1)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(k.trl[idx]?.getD 0#32).toNat, ot]))
    (hreach : ∀ α, (cnfOfClauses F_cur).Sat α → α (litVar implied) = litSign implied →
      domReach k mrk (idx + 1) α) :
    ∀ α, (cnfOfClauses F_cur).Sat α → α (litVar implied) = litSign implied →
      domReach k (mrk.set ov 1#8) idx α := by
  intro α hα himf
  obtain ⟨t, ht, hmt, hfal_t⟩ := hreach α hα himf
  by_cases hteq : t = idx
  · subst hteq
    refine ⟨m_w, hm_w, ?_, hbrDom_sat_neg_trl hmw_eq (hbrDom_bin_false hent hα hfal_t)⟩
    rw [hmw_eq, fullInv_var_xor1, ← hov_eq, List.getElem?_set_self hov_lt, Option.getD_some]
    decide
  · refine ⟨t, by omega, ?_, hfal_t⟩
    by_cases htv : (k.trl[t]?.getD 0#32).toNat / 2 = ov
    · rw [htv, List.getElem?_set_self hov_lt, Option.getD_some]; decide
    · rw [List.getElem?_set_ne (Ne.symm htv)]; exact hmt

private theorem hbrDom_large_finish_reach {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hcl1 : s.core.cur_level = 1) {mrk mrk_j : List (BitVec 8)} {idx implied rsn : Nat}
    (hidx_lt : idx < s.core.trail_end) (hrsn_ref : rsn ∈ fullArenaClauseRefs s)
    (hrsn_ng : fullArenaClauseGarb s rsn = false)
    (hbd : rsn + 3 + fullArenaClauseSize s rsn ≤ s.core.arena.length)
    (hrsn_lits : ∀ q ∈ fullArenaClauseLits s rsn,
      q = (s.core.trl[idx]?.getD 0#32).toNat ∨
      ∃ m < idx, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hmono : ∀ w < s.core.cur_vars, mrk[w]?.getD 0#8 ≠ 0#8 → mrk_j[w]?.getD 0#8 ≠ 0#8)
    (hcov : ∀ k < fullArenaClauseSize s rsn,
      let q := (s.core.arena[rsn + 3 + k]?.getD 0#32).toNat
      q / 2 ≠ (s.core.trl[idx]?.getD 0#32).toNat / 2 →
      (s.core.lvl[q / 2]?.getD 0#32).toNat = 1 → mrk_j[q / 2]?.getD 0#8 ≠ 0#8)
    (hreach : ∀ α, (cnfOfClauses F_cur).Sat α → α (litVar implied) = litSign implied →
      domReach s.core mrk (idx + 1) α) :
    ∀ α, (cnfOfClauses F_cur).Sat α → α (litVar implied) = litSign implied →
      domReach s.core mrk_j idx α := by
  have hnod := hw.trail_vars_nodup
  have htl := hw.trail_lits_lt
  dsimp only [withEmptyModeWatches] at hnod htl
  intro α hα himf
  obtain ⟨t, ht, hmt, hfal_t⟩ := hreach α hα himf
  by_cases hteq : t = idx
  · subst hteq
    have hent_r := hw.arena.entails rsn hrsn_ref hrsn_ng
    obtain ⟨q, hq_mem, hq_sat⟩ :=
      (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hent_r α hα)
    have hq_ne_p : q ≠ (s.core.trl[t]?.getD 0#32).toNat := by
      intro heq; subst heq; cases hls : litSign (s.core.trl[t]?.getD 0#32).toNat <;> simp_all
    obtain ⟨m_q, hm_q, hmq_eq, _⟩ := (hrsn_lits q hq_mem).resolve_left hq_ne_p
    have hq_var_ne : q / 2 ≠ (s.core.trl[t]?.getD 0#32).toNat / 2 := by
      intro hve
      have hvn : (s.core.trl[m_q]?.getD 0#32).toNat / 2 =
          (s.core.trl[t]?.getD 0#32).toNat / 2 := by
        rw [hmq_eq, fullInv_var_xor1]; exact hve
      have := hnod m_q t (by omega) hidx_lt hvn; omega
    have hq_lvl1 := hbrDom_sat_lvl1_of_false_trl hw hcl1 (by omega : m_q < s.core.trail_end)
      hmq_eq hα hq_sat
    obtain ⟨kq, hkq, hget_kq⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hq_mem
    have hkq' : kq < fullArenaClauseSize s rsn := hkq
    have hget_kq' : (s.core.arena[rsn + 3 + kq]?.getD 0#32).toNat = q := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget_kq
    have hmk_q := hcov kq hkq' (by rwa [hget_kq']) (by rwa [hget_kq'])
    rw [hget_kq'] at hmk_q
    exact ⟨m_q, hm_q, by rwa [hmq_eq, fullInv_var_xor1], hbrDom_sat_neg_trl hmq_eq hq_sat⟩
  · have ht_lt := htl t (by omega)
    exact ⟨t, by omega, hmono _ (by omega) hmt, hfal_t⟩

private abbrev hbrState (s : FullState) (mrk : List (BitVec 8))
    (clr : List (BitVec 32)) : FullState :=
  { s with core := { s.core with mrk := mrk, min_clr := clr } }

private structure HbrMarkBase (c : FullCfg) (s : FullState) (clen : Nat)
    (mrk : List (BitVec 8)) (clr : List (BitVec 32)) : Prop where
  clen_le : clen ≤ s.core.cur_vars
  mrk_len : mrk.length = c.max_vars
  clr_len : clr.length = c.max_vars
  mark_inv : hbrMarkInv s.core.cur_vars clen s.core.mrk mrk clr
  lvl1 : ∀ w < s.core.cur_vars, mrk[w]?.getD 0#8 ≠ 0#8 → (s.core.lvl[w]?.getD 0#32).toNat = 1

private def hbrLoop1Inv (c : FullCfg) (s : FullState) (cref implied i clen open_c : Nat)
    (mrk : List (BitVec 8)) (clr : List (BitVec 32)) : Prop :=
  HbrMarkBase c s clen mrk clr ∧
  i ≤ fullArenaClauseSize s cref ∧
  open_c = clen ∧
  markedTrailCount mrk s.core.trl s.core.trail_end = clen ∧
  ∀ k < i, let l := (s.core.arena[cref + 3 + k]?.getD 0#32).toNat
    l ≠ implied → (s.core.lvl[l / 2]?.getD 0#32).toNat = 1 → mrk[l / 2]?.getD 0#8 ≠ 0#8

private def hbrOutInv (c : FullCfg) (s : FullState) (F_cur : List (List Nat))
    (implied clen : Nat) (dom : BitVec 32) (mrk : List (BitVec 8))
    (clr : List (BitVec 32)) : Prop :=
  HbrMarkBase c s clen mrk clr ∧
  (dom = 0xFFFFFFFF#32 ∨ (dom.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [dom.toNat ^^^ 1, implied])))

private def hbrLoop2Inv (c : FullCfg) (s : FullState) (F_cur : List (List Nat))
    (implied clen open_c idx : Nat) (mrk : List (BitVec 8))
    (clr : List (BitVec 32)) : Prop :=
  HbrMarkBase c s clen mrk clr ∧
  open_c ≤ s.core.trail_end ∧
  idx ≤ s.core.trail_end ∧
  markedTrailCount mrk s.core.trl idx = open_c ∧
  ∀ α, (cnfOfClauses F_cur).Sat α → α (litVar implied) = litSign implied →
    domReach s.core mrk idx α

private def hbrInnerInv (c : FullCfg) (s : FullState) (rsn idx_pred j clen open_c : Nat)
    (mrk mrk_j : List (BitVec 8)) (clr_j : List (BitVec 32)) : Prop :=
  HbrMarkBase c s clen mrk_j clr_j ∧
  j ≤ fullArenaClauseSize s rsn ∧
  open_c ≤ s.core.trail_end ∧
  (∀ w < s.core.cur_vars, mrk[w]?.getD 0#8 ≠ 0#8 → mrk_j[w]?.getD 0#8 ≠ 0#8) ∧
  markedTrailCount mrk_j s.core.trl idx_pred = open_c ∧
  ∀ k < j, let q := (s.core.arena[rsn + 3 + k]?.getD 0#32).toNat
    q / 2 ≠ (s.core.trl[idx_pred]?.getD 0#32).toNat / 2 →
    (s.core.lvl[q / 2]?.getD 0#32).toNat = 1 → mrk_j[q / 2]?.getD 0#8 ≠ 0#8

private def hbrLoop3Inv (c : FullCfg) (s : FullState) (k clen : Nat)
    (mrkk : List (BitVec 8)) (clr : List (BitVec 32)) : Prop :=
  k ≤ clen ∧ mrkk.length = c.max_vars ∧
  (∀ w, s.core.cur_vars ≤ w → w < c.max_vars → mrkk[w]? = s.core.mrk[w]?) ∧
  ∀ w < s.core.cur_vars, mrkk[w]?.getD 0#8 ≠ 0#8 →
    ∃ t, k ≤ t ∧ t < clen ∧ (clr[t]?.getD 0#32).toNat = w

private theorem hbrLoop1_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hmrk0 : FullMrkZero c s) {cref implied : Nat} :
    hbrLoop1Inv c s cref implied 0 0 0 s.core.mrk s.core.min_clr := by
  have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le
  have htrl_lt := hw.trail_lits_lt
  dsimp only [withEmptyModeWatches] at htrl_lt
  refine ⟨⟨Nat.zero_le _, hcl.mrk_len, hcl.min_clr_len_arr,
    hbrMarkInv_init fun v hv => hmrk0 v (by omega),
    fun w hw0 hne => absurd (hmrk0 w (by omega)) hne⟩, Nat.zero_le _, rfl, ?_,
    fun _ hk => by simp at hk⟩
  have h0 : ¬ 0 < markedTrailCount s.core.mrk s.core.trl s.core.trail_end := by
    intro hp
    obtain ⟨t, ht⟩ := List.length_pos_iff_exists_mem.mp hp
    have hf := List.mem_filter.mp ht
    have htlt := htrl_lt t (List.mem_range.mp hf.1)
    exact absurd (hmrk0 _ (by omega)) (of_decide_eq_true hf.2)
  exact Nat.eq_zero_of_not_pos h0

private theorem hbrLoop1_step_mark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    {cref implied i clen open_c : Nat} {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop1Inv c s cref implied i clen open_c mrk clr)
    (hcref : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false)
    (hfal : ∀ l ∈ fullArenaClauseLits s cref, l ≠ implied → s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length)
    (hi_lt : i < fullArenaClauseSize s cref)
    {ov : BitVec 32} (hov_eq : ov = s.core.arena[cref + 3 + i]'(by omega) >>> (1 : Nat))
    (hneq_imp : (s.core.arena[cref + 3 + i]'(by omega)).toNat ≠ implied)
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hlvl1 : (s.core.lvl[ov.toNat]?.getD 0#32).toNat = 1)
    (hm0 : mrk[ov.toNat]?.getD 0#8 = 0#8) :
    hbrLoop1Inv c s cref implied (i + 1) (clen + 1) (open_c + 1)
      (mrk.set ov.toNat 1#8) (clr.set clen ov) := by
  have hbase := h.1
  have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le
  have hmv := fullInv_max_vars_lt32 c
  have hcv32 : s.core.cur_vars < 2 ^ 32 := by omega
  have hnod := hw.trail_vars_nodup
  dsimp only [withEmptyModeWatches] at hnod
  have hcl_lt : clen < s.core.cur_vars :=
    hbrMarkInv_clen_lt hbase.mark_inv (by rw [hbase.clr_len]; exact hcv_le) hov_lt hm0
  have hbd_core : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := hbd
  have hmem_l : (s.core.arena[cref + 3 + i]'(by omega)).toNat ∈ fullArenaClauseLits s cref :=
    (mem_fullArenaClauseLitsCore_iff hbd_core).mpr ⟨i, hi_lt, rfl⟩
  have hl_lt : (s.core.arena[cref + 3 + i]'(by omega)).toNat < 2 * s.core.cur_vars :=
    hw.arena.lits_lt cref hcref hng _ hmem_l
  have hvf := hw.vals_false_iff _ hl_lt
  dsimp only [withEmptyModeWatches] at hvf
  obtain ⟨t_w, ht_w, htrl_w⟩ := hvf.mp (hfal _ hmem_l hneq_imp)
  have ht_var : (s.core.trl[t_w]?.getD 0#32).toNat / 2 = ov.toNat := by
    rw [htrl_w, fullInv_var_xor1, hov_eq, bv32_toNat_lshr1]
  have hset_mk := hbrMarkInv_set hbase.mark_inv (by rw [hbase.clr_len]; exact hcv_le)
    (by rw [hcl.mrk_len]; exact hcv_le) hcv32 hov_lt hm0
  have hov_bv : BitVec.ofNat 32 ov.toNat = ov := BitVec.eq_of_toNat_eq (by simp)
  rw [hov_bv] at hset_mk
  have hset_cnt : markedTrailCount (mrk.set ov.toNat 1#8) s.core.trl s.core.trail_end =
      clen + 1 := by
    rw [markedTrailCount_set (Nat.le_refl _) (by rw [hbase.mrk_len]; omega) hm0 hnod, h.2.2.2.1]
    have hex : ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat / 2 = ov.toNat :=
      ⟨t_w, ht_w, ht_var⟩
    simp only [hex, ↓reduceIte]
  have hop_eq := h.2.2.1
  refine ⟨⟨hcl_lt, by rw [List.length_set]; exact hbase.mrk_len,
    by rw [List.length_set]; exact hbase.clr_len, hset_mk,
    hbrDom_mark_hlvl1 hbase.lvl1 hlvl1⟩, hi_lt, by omega, hset_cnt,
    hbrDom_mark_cov (fun l => l ≠ implied) h.2.2.2.2 (by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← bv32_toNat_lshr1, ← hov_eq])
      (by rw [hbase.mrk_len]; omega)⟩

private theorem hbrLoop1_step_same {c : FullCfg} {s : FullState}
    {cref implied i clen open_c : Nat} {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop1Inv c s cref implied i clen open_c mrk clr)
    (hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length)
    (hi_lt : i < fullArenaClauseSize s cref)
    (hcase : (s.core.arena[cref + 3 + i]'(by omega)).toNat = implied ∨
      (s.core.lvl[(s.core.arena[cref + 3 + i]'(by omega)).toNat / 2]?.getD 0#32).toNat ≠ 1 ∨
      mrk[(s.core.arena[cref + 3 + i]'(by omega)).toNat / 2]?.getD 0#8 ≠ 0#8) :
    hbrLoop1Inv c s cref implied (i + 1) clen open_c mrk clr := by
  refine ⟨h.1, hi_lt, h.2.2.1, h.2.2.2.1, hbrDom_step_same h.2.2.2.2 ?_⟩
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hcase

private theorem hbrLoop2_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hcl1 : s.core.cur_level = 1) {cref implied clen open_c : Nat}
    (hcref : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false)
    (hbd : cref + 3 + fullArenaClauseSize s cref ≤ s.core.arena.length)
    (hfal : ∀ l ∈ fullArenaClauseLits s cref, l ≠ implied → s.core.vals[l]?.getD 0#8 = 0xFF#8)
    {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop1Inv c s cref implied (fullArenaClauseSize s cref) clen open_c mrk clr) :
    hbrLoop2Inv c s F_cur implied clen open_c s.core.trail_end mrk clr := by
  have hle := markedTrailCount_le mrk s.core.trl s.core.trail_end
  have := h.2.2.1; have := h.2.2.2.1
  refine ⟨h.1, by omega, Nat.le_refl _, by rw [h.2.2.2.1, h.2.2.1],
    hbrDom_init_reach hw hcl1 hcref hng hbd hfal h.2.2.2.2⟩

private theorem hbrLoop2_skip {c : FullCfg} {s : FullState} {F_cur : List (List Nat)}
    {implied clen open_c idx_pred : Nat} {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop2Inv c s F_cur implied clen open_c (idx_pred + 1) mrk clr)
    (hm0 : mrk[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    hbrLoop2Inv c s F_cur implied clen open_c idx_pred mrk clr := by
  have hsc := markedTrailCount_succ mrk s.core.trl idx_pred
  rw [h.2.2.2.1, hm0] at hsc
  have := h.2.2.1
  refine ⟨h.1, h.2.1, by omega, by simp at hsc; exact hsc.symm, fun α hα himf => ?_⟩
  obtain ⟨t, ht, hmt, hfal_t⟩ := h.2.2.2.2 α hα himf
  refine ⟨t, ?_, hmt, hfal_t⟩
  by_cases hteq : t = idx_pred
  · subst hteq; exact absurd hm0 hmt
  · omega

private theorem hbrLoop2_consume {c : FullCfg} {s : FullState} {F_cur : List (List Nat)}
    {implied clen open_c idx_pred : Nat} {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop2Inv c s F_cur implied clen open_c (idx_pred + 1) mrk clr)
    (hm_nz : mrk[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    markedTrailCount mrk s.core.trl idx_pred = open_c - 1 := by
  have hsc := markedTrailCount_succ mrk s.core.trl idx_pred
  rw [h.2.2.2.1, ite_eq_left hm_nz] at hsc; omega

private theorem hbrLoop2_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    {implied clen idx_pred : Nat} {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop2Inv c s F_cur implied clen 1 (idx_pred + 1) mrk clr)
    (hidx_lt : idx_pred < s.core.trail_end)
    (hm_nz : mrk[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    hbrOutInv c s F_cur implied clen
      (s.core.trl[idx_pred]'(by
        have := hlen.core_ok.trail_end_le; have := hlen.core_ok.trl_len
        have := hlen.core_ok.cur_vars_le; omega)) mrk clr := by
  have htl := hw.trail_lits_lt
  dsimp only [withEmptyModeWatches] at htl
  have hcnt0 : markedTrailCount mrk s.core.trl idx_pred = 0 := by
    have := hbrLoop2_consume h hm_nz; omega
  have hplt := htl idx_pred hidx_lt
  have hte_le := hlen.core_ok.trail_end_le; have htrl_len := hlen.core_ok.trl_len
  have hcv_le := hlen.core_ok.cur_vars_le
  have htrl_get : s.core.trl[idx_pred]? = some (s.core.trl[idx_pred]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  rw [htrl_get, Option.getD_some] at hplt
  refine ⟨h.1, Or.inr ⟨hplt, ?_⟩⟩
  have hent := entails_bin_hbr_of_domReach hcnt0 h.2.2.2.2
  rw [htrl_get, Option.getD_some] at hent
  exact hent

private theorem hbrLoop2_bin_skip {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hcl1 : s.core.cur_level = 1) {implied clen open_c idx_pred ot : Nat}
    {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop2Inv c s F_cur implied clen open_c (idx_pred + 1) mrk clr)
    (hidx_lt : idx_pred < s.core.trail_end) (hop_pos : 0 < open_c)
    (hm_nz : mrk[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hot_lt : ot < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(s.core.trl[idx_pred]?.getD 0#32).toNat, ot]))
    {m_w : Nat} (hm_w : m_w < idx_pred)
    (hmw_eq : (s.core.trl[m_w]?.getD 0#32).toNat = ot ^^^ 1)
    (hmw_lvl : (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hcase : mrk[ot / 2]?.getD 0#8 ≠ 0#8 ∨ (s.core.lvl[ot / 2]?.getD 0#32).toNat ≠ 1) :
    hbrLoop2Inv c s F_cur implied clen (open_c - 1) idx_pred mrk clr :=
  have := h.2.1; have := h.2.2.1
  ⟨h.1, by omega, by omega, hbrLoop2_consume h hm_nz,
    hbrDom_bin_no_add_reach hw hcl1 hidx_lt hot_lt hent hm_w hmw_eq hmw_lvl h.2.2.2.2 hcase⟩

private theorem hbrLoop2_bin_mark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    {implied clen open_c idx_pred ot : Nat} {ov : BitVec 32}
    {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop2Inv c s F_cur implied clen open_c (idx_pred + 1) mrk clr)
    (hidx_lt : idx_pred < s.core.trail_end) (hop_pos : 0 < open_c)
    (hm_nz : mrk[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hov_eq : ov.toNat = ot / 2) (hov_lt : ov.toNat < s.core.cur_vars)
    (hlvl1 : (s.core.lvl[ov.toNat]?.getD 0#32).toNat = 1)
    (hm0 : mrk[ov.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(s.core.trl[idx_pred]?.getD 0#32).toNat, ot]))
    {m_w : Nat} (hm_w : m_w < idx_pred)
    (hmw_eq : (s.core.trl[m_w]?.getD 0#32).toNat = ot ^^^ 1) :
    hbrLoop2Inv c s F_cur implied (clen + 1) open_c idx_pred
      (mrk.set ov.toNat 1#8) (clr.set clen ov) := by
  have hbase := h.1
  have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le
  have hmv := fullInv_max_vars_lt32 c
  have hcv32 : s.core.cur_vars < 2 ^ 32 := by omega
  have hnod := hw.trail_vars_nodup
  dsimp only [withEmptyModeWatches] at hnod
  have hcl_lt : clen < s.core.cur_vars :=
    hbrMarkInv_clen_lt hbase.mark_inv (by rw [hbase.clr_len]; exact hcv_le) hov_lt hm0
  have hset_mk := hbrMarkInv_set hbase.mark_inv (by rw [hbase.clr_len]; exact hcv_le)
    (by rw [hcl.mrk_len]; exact hcv_le) hcv32 hov_lt hm0
  have hov_bv : BitVec.ofNat 32 ov.toNat = ov := BitVec.eq_of_toNat_eq (by simp)
  rw [hov_bv] at hset_mk
  have hcnt_pred := hbrLoop2_consume h hm_nz
  have hmw_var : (s.core.trl[m_w]?.getD 0#32).toNat / 2 = ov.toNat := by
    rw [hmw_eq, fullInv_var_xor1, hov_eq]
  have hset_cnt : markedTrailCount (mrk.set ov.toNat 1#8) s.core.trl idx_pred = open_c := by
    rw [markedTrailCount_set (by omega) (by rw [hbase.mrk_len]; omega) hm0 hnod, hcnt_pred]
    have hex : ∃ m < idx_pred, (s.core.trl[m]?.getD 0#32).toNat / 2 = ov.toNat :=
      ⟨m_w, hm_w, hmw_var⟩
    simp only [hex, ↓reduceIte]; omega
  have := h.2.2.1
  refine ⟨⟨hcl_lt, by rw [List.length_set]; exact hbase.mrk_len,
    by rw [List.length_set]; exact hbase.clr_len, hset_mk,
    hbrDom_mark_hlvl1 hbase.lvl1 hlvl1⟩, h.2.1, by omega, hset_cnt,
    hbrDom_bin_add_reach hov_eq (by rw [hbase.mrk_len]; omega) hm_w hmw_eq hent h.2.2.2.2⟩

private theorem hbrInner_init {c : FullCfg} {s : FullState} {F_cur : List (List Nat)}
    {implied clen open_c idx_pred rsn : Nat} {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (h : hbrLoop2Inv c s F_cur implied clen open_c (idx_pred + 1) mrk clr)
    (hm_nz : mrk[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    hbrInnerInv c s rsn idx_pred 0 clen (open_c - 1) mrk mrk clr :=
  have := h.2.1
  ⟨h.1, Nat.zero_le _, by omega, fun _ _ hx => hx, hbrLoop2_consume h hm_nz,
    fun _ hk => by simp at hk⟩

private theorem hbrInner_step_mark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    {rsn idx_pred j clen open_c : Nat} {mrk mrk_j : List (BitVec 8)} {clr_j : List (BitVec 32)}
    (h : hbrInnerInv c s rsn idx_pred j clen open_c mrk mrk_j clr_j)
    (_hrsn_ref : rsn ∈ fullArenaClauseRefs s) (_hrsn_ng : fullArenaClauseGarb s rsn = false)
    (hbd : rsn + 3 + fullArenaClauseSize s rsn ≤ s.core.arena.length)
    (hj_lt : j < fullArenaClauseSize s rsn)
    (_hidx_lt : idx_pred < s.core.trail_end)
    (hrsn_lits : ∀ q ∈ fullArenaClauseLits s rsn,
      q = (s.core.trl[idx_pred]?.getD 0#32).toNat ∨
      ∃ m < idx_pred, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {ov : BitVec 32} (hov_eq : ov = s.core.arena[rsn + 3 + j]'(by omega) >>> (1 : Nat))
    (hov_ne : ov.toNat ≠ (s.core.trl[idx_pred]?.getD 0#32).toNat / 2)
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hlvl1 : (s.core.lvl[ov.toNat]?.getD 0#32).toNat = 1)
    (hm0 : mrk_j[ov.toNat]?.getD 0#8 = 0#8) :
    hbrInnerInv c s rsn idx_pred (j + 1) (clen + 1) (open_c + 1)
      mrk (mrk_j.set ov.toNat 1#8) (clr_j.set clen ov) := by
  have hbase := h.1
  have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le
  have hmv := fullInv_max_vars_lt32 c
  have hcv32 : s.core.cur_vars < 2 ^ 32 := by omega
  have hnod := hw.trail_vars_nodup
  dsimp only [withEmptyModeWatches] at hnod
  have hclj_lt : clen < s.core.cur_vars :=
    hbrMarkInv_clen_lt hbase.mark_inv (by rw [hbase.clr_len]; exact hcv_le) hov_lt hm0
  have hbd_core : rsn + 3 + fullArenaClauseSizeCore s.core rsn ≤ s.core.arena.length := hbd
  have hmem_q : (s.core.arena[rsn + 3 + j]'(by omega)).toNat ∈ fullArenaClauseLits s rsn :=
    (mem_fullArenaClauseLitsCore_iff hbd_core).mpr ⟨j, hj_lt, rfl⟩
  have hq_ne_p : (s.core.arena[rsn + 3 + j]'(by omega)).toNat ≠
      (s.core.trl[idx_pred]?.getD 0#32).toNat := by
    intro heq
    apply hov_ne
    rw [hov_eq, bv32_toNat_lshr1, heq]
  obtain ⟨m_q, hm_q, hmq_eq, _⟩ := (hrsn_lits _ hmem_q).resolve_left hq_ne_p
  have hmq_var : (s.core.trl[m_q]?.getD 0#32).toNat / 2 = ov.toNat := by
    rw [hmq_eq, fullInv_var_xor1, hov_eq, bv32_toNat_lshr1]
  have hset_mk := hbrMarkInv_set hbase.mark_inv (by rw [hbase.clr_len]; exact hcv_le)
    (by rw [hcl.mrk_len]; exact hcv_le) hcv32 hov_lt hm0
  have hov_bv : BitVec.ofNat 32 ov.toNat = ov := BitVec.eq_of_toNat_eq (by simp)
  rw [hov_bv] at hset_mk
  have hset_cnt : markedTrailCount (mrk_j.set ov.toNat 1#8) s.core.trl idx_pred = open_c + 1 := by
    rw [markedTrailCount_set (by omega) (by rw [hbase.mrk_len]; omega) hm0 hnod, h.2.2.2.2.1]
    have hex : ∃ m < idx_pred, (s.core.trl[m]?.getD 0#32).toNat / 2 = ov.toNat :=
      ⟨m_q, hm_q, hmq_var⟩
    simp only [hex, ↓reduceIte]
  have hop_le : open_c + 1 ≤ s.core.trail_end := by
    have := markedTrailCount_le (mrk_j.set ov.toNat 1#8) s.core.trl idx_pred; omega
  refine ⟨⟨hclj_lt, by rw [List.length_set]; exact hbase.mrk_len,
    by rw [List.length_set]; exact hbase.clr_len, hset_mk,
    hbrDom_mark_hlvl1 hbase.lvl1 hlvl1⟩, hj_lt, hop_le,
    hbrDom_mono_set h.2.2.2.1 (by rw [hbase.mrk_len]; omega), hset_cnt,
    hbrDom_mark_cov (fun q => q / 2 ≠ (s.core.trl[idx_pred]?.getD 0#32).toNat / 2) h.2.2.2.2.2 (by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← bv32_toNat_lshr1, ← hov_eq])
      (by rw [hbase.mrk_len]; omega)⟩

private theorem hbrInner_step_same {c : FullCfg} {s : FullState}
    {rsn idx_pred j clen open_c : Nat} {mrk mrk_j : List (BitVec 8)} {clr_j : List (BitVec 32)}
    (h : hbrInnerInv c s rsn idx_pred j clen open_c mrk mrk_j clr_j)
    (hbd : rsn + 3 + fullArenaClauseSize s rsn ≤ s.core.arena.length)
    (hj_lt : j < fullArenaClauseSize s rsn)
    (hcase : (s.core.arena[rsn + 3 + j]'(by omega)).toNat / 2 =
        (s.core.trl[idx_pred]?.getD 0#32).toNat / 2 ∨
      (s.core.lvl[(s.core.arena[rsn + 3 + j]'(by omega)).toNat / 2]?.getD 0#32).toNat ≠ 1 ∨
      mrk_j[(s.core.arena[rsn + 3 + j]'(by omega)).toNat / 2]?.getD 0#8 ≠ 0#8) :
    hbrInnerInv c s rsn idx_pred (j + 1) clen open_c mrk mrk_j clr_j := by
  refine ⟨h.1, hj_lt, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun k hk hne hlv1 => ?_⟩
  by_cases hkj : k = j
  · simp only [hkj] at hne hlv1 ⊢
    have har_get : s.core.arena[rsn + 3 + j]? = some (s.core.arena[rsn + 3 + j]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [har_get, Option.getD_some] at hne hlv1 ⊢
    rcases hcase with h1 | h1 | h1
    · exact absurd h1 hne
    · exact absurd hlv1 h1
    · exact h1
  · exact h.2.2.2.2.2 k (by omega) hne hlv1

private theorem hbrLoop2_large_finish {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hcl1 : s.core.cur_level = 1) {implied clen open_c clen_j open_j idx_pred rsn : Nat}
    {mrk mrk_j : List (BitVec 8)} {clr clr_j : List (BitVec 32)}
    (h2 : hbrLoop2Inv c s F_cur implied clen open_c (idx_pred + 1) mrk clr)
    (hj : hbrInnerInv c s rsn idx_pred (fullArenaClauseSize s rsn) clen_j open_j mrk mrk_j clr_j)
    (hidx_lt : idx_pred < s.core.trail_end) (hrsn_ref : rsn ∈ fullArenaClauseRefs s)
    (hrsn_ng : fullArenaClauseGarb s rsn = false)
    (hbd : rsn + 3 + fullArenaClauseSize s rsn ≤ s.core.arena.length)
    (hrsn_lits : ∀ q ∈ fullArenaClauseLits s rsn,
      q = (s.core.trl[idx_pred]?.getD 0#32).toNat ∨
      ∃ m < idx_pred, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[idx_pred]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) :
    hbrLoop2Inv c s F_cur implied clen_j open_j idx_pred mrk_j clr_j :=
  ⟨hj.1, hj.2.2.1, by omega, hj.2.2.2.2.1,
    hbrDom_large_finish_reach hw hcl1 hidx_lt hrsn_ref hrsn_ng hbd hrsn_lits
      hj.2.2.2.1 hj.2.2.2.2.2 h2.2.2.2.2⟩

private theorem hbrLoop3_init {c : FullCfg} {s : FullState} {F_cur : List (List Nat)}
    {implied clen : Nat} {dom : BitVec 32} {mrk : List (BitVec 8)} {clr : List (BitVec 32)}
    (hlen : s.LengthsOk c) (h : hbrOutInv c s F_cur implied clen dom mrk clr) :
    hbrLoop3Inv c s 0 clen mrk clr :=
  ⟨Nat.zero_le _, h.1.mrk_len,
    fun w hw1 hw2 => h.1.mark_inv.2.2.1 w hw1 (by rw [hlen.core_ok.mrk_len]; exact hw2),
    fun w hw hne => by
      obtain ⟨t, ht, hteq⟩ := (h.1.mark_inv.2.2.2.2.2 w hw).mp hne
      exact ⟨t, Nat.zero_le _, ht, hteq⟩⟩

private theorem hbrLoop3_step {c : FullCfg} {s : FullState} {F_cur : List (List Nat)}
    {implied k clen : Nat} {dom : BitVec 32} {mrk mrkk : List (BitVec 8)}
    {clr : List (BitVec 32)}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hout : hbrOutInv c s F_cur implied clen dom mrk clr)
    (h : hbrLoop3Inv c s k clen mrkk clr) (hk_lt : k < clen) :
    have hck_lt : (clr[k]'(by rw [hout.1.clr_len]; have := hout.1.clen_le; omega)).toNat <
        s.core.cur_vars := by
      have hcl := hout.1.mark_inv.2.2.2.2.1 k hk_lt
      rw [List.getElem?_eq_getElem (by rw [hout.1.clr_len]; have := hout.1.clen_le; omega),
        Option.getD_some] at hcl
      exact hcl
    hbrLoop3Inv c s (k + 1) clen
      (mrkk.set (clr[k]'(by rw [hout.1.clr_len]; have := hout.1.clen_le; omega)).toNat 0#8)
      clr := by
  intro hck_lt
  refine ⟨by omega, by rw [List.length_set]; exact h.2.1, fun w hw1 hw2 => ?_, ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact h.2.2.1 w hw1 hw2
  · exact hbrDom_clear_step_cov
      (by rw [List.getElem?_eq_getElem (by rw [hout.1.clr_len]; have := hout.1.clen_le; omega),
        Option.getD_some]) (by rw [h.2.1]; omega) h.2.2.2

private theorem hbrLoop3_fin {c : FullCfg} {s : FullState} {F_cur : List (List Nat)}
    {implied clen : Nat} {dom : BitVec 32} {mrk mrkk : List (BitVec 8)}
    {clr : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hmrk0 : FullMrkZero c s)
    (hout : hbrOutInv c s F_cur implied clen dom mrk clr)
    (h : hbrLoop3Inv c s clen clen mrkk clr) :
    mrkk = s.core.mrk ∧
    ({ s with core := { s.core with mrk := s.core.mrk, min_clr := clr } } :
      FullState).LengthsOk c :=
  ⟨hbrDom_clear_fin hmrk0 hlen.core_ok.cur_vars_le hlen.core_ok.mrk_len h.2.1 h.2.2.1 h.2.2.2,
    { core_ok := { hlen.core_ok with min_clr_len_arr := hout.1.clr_len },
      scratch_ok := hlen.scratch_ok }⟩

private theorem mrk_getD_eq0 {mrk : List (BitVec 8)} {v : Nat} (hv : v < mrk.length)
    (h : BitVec.setWidth 32 (mrk[v]'hv) = 0#32) : mrk[v]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hv, Option.getD_some]; exact (u8_zext32_eq0_iff _).mp h

private theorem mrk_getD_ne0 {mrk : List (BitVec 8)} {v : Nat} (hv : v < mrk.length)
    (h : ¬ BitVec.setWidth 32 (mrk[v]'hv) = 0#32) : mrk[v]?.getD 0#8 ≠ 0#8 := by
  rw [List.getElem?_eq_getElem hv, Option.getD_some]
  intro h0; exact h ((u8_zext32_eq0_iff _).mpr h0)

private theorem lvl_toNat_eq1 {lvl : List (BitVec 32)} {v : Nat} (hv : v < lvl.length)
    (h : lvl[v]'hv = 1#32) : (lvl[v]?.getD 0#32).toNat = 1 := by
  rw [List.getElem?_eq_getElem hv, Option.getD_some, h]; rfl

private theorem lvl_toNat_ne1 {lvl : List (BitVec 32)} {v : Nat} (hv : v < lvl.length)
    (h : ¬ lvl[v]'hv = 1#32) : (lvl[v]?.getD 0#32).toNat ≠ 1 := by
  rw [List.getElem?_eq_getElem hv, Option.getD_some]
  intro heq; exact h (BitVec.eq_of_toNat_eq (by simpa using heq))

end HbrDomProofHelpers

section HbrDomProof

open scoped FullArenaTactics FullProbeTransTactics

private def hbrInnerExpr (h_arg pArena pMark pLevel pClr cv clen0 open_m1 : Val i64)
    (trl_pv rsn_v rsz : Val i32) (J2 : Cont [i64, i64]) : Expr Val Cont [i32] :=
  .group (sig := [[i64, i64, i32]]) (fun Js => Blocks.cons (fun p =>
    .let_ ⟨.cmp .ult i32, (.var p.snd.snd.fst, .var rsz, ())⟩ fun p_1 => .jnz (.var p_1.fst)
      (.let_ ⟨.zext 32 64, (.var rsn_v, ())⟩ fun p_2 =>
       .let_ ⟨.add i64, (.var p_2.fst, .imm 3, ())⟩ fun p_3 =>
       .let_ ⟨.zext 32 64, (.var rsz, ())⟩ fun p_4 =>
       .let_ ⟨.add i64, (.var p_3.fst, .var p_4.fst, ())⟩ fun p_5 =>
       .let_ ⟨.add i64, (.var h_arg, .imm 48, ())⟩ fun p_6 => .load i64 (.var p_6.fst) fun ld =>
       .let_ ⟨.cmp .ule i64, (.var p_5.fst, .var ld, ())⟩ fun p_7 => .jnz (.var p_7.fst)
         (.let_ ⟨.zext 32 64, (.var rsn_v, ())⟩ fun p_8 =>
          .let_ ⟨.add i64, (.var p_8.fst, .imm 3, ())⟩ fun p_9 =>
          .let_ ⟨.zext 32 64, (.var p.snd.snd.fst, ())⟩ fun p_10 =>
          .let_ ⟨.add i64, (.var p_9.fst, .var p_10.fst, ())⟩ fun p_11 =>
          .let_ ⟨.mul i64, (.var p_11.fst, .imm 4, ())⟩ fun p_12 =>
          .let_ ⟨.add i64, (.var pArena, .var p_12.fst, ())⟩ fun p_13 =>
          .load i32 (.var p_13.fst) fun ld => .let_ ⟨.lshr i32, (.var ld, .imm 1, ())⟩ fun p_14 =>
          .group (sig := [[i64, i64]]) (fun _ => Blocks.cons (fun p_15 =>
            .let_ ⟨.add i32, (.var p.snd.snd.fst, .imm 1, ())⟩ fun p_16 =>
            .jump Js.fst (.var p_15.fst, .var p_15.snd.fst, .var p_16.fst, ())) .nil) fun Js_c =>
          .let_ ⟨.cmp .ne i32, (.var p_14.fst, .var trl_pv, ())⟩ fun p_15 => .jnz (.var p_15.fst)
            (.let_ ⟨.zext 32 64, (.var p_14.fst, ())⟩ fun p_16 =>
             .let_ ⟨.cmp .ult i64, (.var p_16.fst, .var cv, ())⟩ fun p_17 => .jnz (.var p_17.fst)
               (.let_ ⟨.zext 32 64, (.var p_14.fst, ())⟩ fun p_18 =>
                .let_ ⟨.mul i64, (.var p_18.fst, .imm 4, ())⟩ fun p_19 =>
                .let_ ⟨.add i64, (.var pLevel, .var p_19.fst, ())⟩ fun p_20 =>
                .load i32 (.var p_20.fst) fun ld =>
                .let_ ⟨.cmp .eq i32, (.var ld, .imm 1, ())⟩ fun p_21 => .jnz (.var p_21.fst)
                  (.let_ ⟨.zext 32 64, (.var p_14.fst, ())⟩ fun p_22 =>
                   .let_ ⟨.add i64, (.var pMark, .var p_22.fst, ())⟩ fun p_23 =>
                   .load i8 (.var p_23.fst) fun ld => .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p_24 =>
                   .let_ ⟨.zext 8 32, (.var ld, ())⟩ fun p_25 =>
                   .let_ ⟨.zext 8 32, (.var p_24.fst, ())⟩ fun p_26 =>
                   .let_ ⟨.cmp .eq i32, (.var p_25.fst, .var p_26.fst, ())⟩ fun p_27 =>
                   .jnz (.var p_27.fst)
                     (.let_ ⟨.cmp .ult i64, (.var p.fst, .var cv, ())⟩ fun p_28 =>
                     .jnz (.var p_28.fst) (.let_ ⟨.zext 32 64, (.var p_14.fst, ())⟩ fun p_29 =>
                       .let_ ⟨.add i64, (.var pMark, .var p_29.fst, ())⟩ fun p_30 =>
                       .let_ ⟨.trunc 32 8, (.imm 1, ())⟩ fun p_31 =>
                       .store (.var p_31.fst) (.var p_30.fst)
                         (.let_ ⟨.mul i64, (.var p.fst, .imm 4, ())⟩ fun p_32 =>
                          .let_ ⟨.add i64, (.var pClr, .var p_32.fst, ())⟩ fun p_33 =>
                          .store (.var p_14.fst) (.var p_33.fst)
                            (.let_ ⟨.add i64, (.var p.fst, .imm 1, ())⟩ fun p_34 =>
                             .let_ ⟨.add i64, (.var p.snd.fst, .imm 1, ())⟩ fun p_35 =>
                             .jump Js_c.fst (.var p_34.fst, .var p_35.fst, ()))))
                       (.jump Js_c.fst (.var p.fst, .var p.snd.fst, ())))
                     (.jump Js_c.fst (.var p.fst, .var p.snd.fst, ())))
                  (.jump Js_c.fst (.var p.fst, .var p.snd.fst, ())))
               (.jump Js_c.fst (.var p.fst, .var p.snd.fst, ())))
            (.jump Js_c.fst (.var p.fst, .var p.snd.fst, ())))
         (.jump J2 (.var p.fst, .var p.snd.fst, ())))
      (.jump J2 (.var p.fst, .var p.snd.fst, ()))) .nil)
  fun Js => .jump Js.fst (.var clen0, .var open_m1, .imm 0, ())

private theorem hbrInnerLoop_wp {Γ : Env} {Q : Post [i32]} {X : XPost} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hcl1 : s.core.cur_level = 1) {implied : Nat} {clen' open_c' idx : Val i64}
    {mrk' : List (BitVec 8)} {clr' : List (BitVec 32)} {ml' : Mem 64} {rsn_v : BitVec 32}
    {h_arg pArena pMark pLevel pClr cv clen0 open_m1 : Val i64}
    {trl_pv rsn_arg rsz : Val i32} {J : Cont [i64, i64]}
    (hh : h_arg = c.hdr) (hpa : pArena = c.pArena) (hpm : pMark = c.pMark)
    (hpl : pLevel = c.pLevel) (hpc : pClr = c.pMinClr) (hcl_eq : clen0 = clen')
    (hcv_eq : cv = BitVec.ofNat 64 s.core.cur_vars) (hop_eq : open_m1 = open_c' - 1#64)
    (htrl_i : (idx - 1#64).toNat < s.core.trl.length)
    (htrl_eq : trl_pv = s.core.trl[(idx - 1#64).toNat]'htrl_i >>> (1 : Nat))
    (hrsn_eq : rsn_arg = rsn_v) (hrsn2_lt : rsn_v.toNat + 2 < s.core.arena.length)
    (hrsn2_mod : (rsn_v.toNat + 2) % 18446744073709551616 < s.core.arena.length)
    (hrsz_val : rsz = s.core.arena[(rsn_v.toNat + 2) % 18446744073709551616]'hrsn2_mod)
    (hidx_lt : (idx - 1#64).toNat < s.core.trail_end)
    (hidx_succ : idx.toNat = (idx - 1#64).toNat + 1)
    (hop_sub : (open_c' - 1#64).toNat = open_c'.toNat - 1)
    (hrsn_ref : rsn_v.toNat ∈ fullArenaClauseRefs s)
    (hrsn_ng : fullArenaClauseGarb s rsn_v.toNat = false)
    (hrsn_le : rsn_v.toNat + 3 + fullArenaClauseSize s rsn_v.toNat ≤ s.core.arena_len)
    (hrsz_eq : (s.core.arena[rsn_v.toNat + 2]'hrsn2_lt).toNat = fullArenaClauseSize s rsn_v.toNat)
    (hrsz_mod : (s.core.arena[(rsn_v.toNat + 2) % 18446744073709551616]'hrsn2_mod).toNat =
      fullArenaClauseSize s rsn_v.toNat)
    (hrsn_bd_core : rsn_v.toNat + 3 + fullArenaClauseSizeCore s.core rsn_v.toNat ≤
      s.core.arena.length)
    (hrsn_lits' : ∀ q ∈ fullArenaClauseLits s rsn_v.toNat,
      q = (s.core.trl[(idx - 1#64).toNat]?.getD 0#32).toNat ∨
      ∃ m < (idx - 1#64).toNat, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[(idx - 1#64).toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hl2 : hbrLoop2Inv c s F_cur implied clen'.toNat open_c'.toNat idx.toNat mrk' clr')
    (hm_nz : mrk'[(s.core.trl[(idx - 1#64).toNat]'(by omega)).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hm' : (FullMem c (hbrState s mrk' clr') ⋆ R) ml')
    (hJ : ∀ (cl_j op_j : Val i64) (mj : Mem 64), ∀ mrk_j clr_j,
      hbrLoop2Inv c s F_cur implied cl_j.toNat op_j.toNat (idx - 1#64).toNat mrk_j clr_j →
      (FullMem c (hbrState s mrk_j clr_j) ⋆ R) mj → J (cl_j, op_j, ()) mj) :
    wp Γ Q X (hbrInnerExpr h_arg pArena pMark pLevel pClr cv clen0 open_m1 trl_pv rsn_arg rsz J)
      ml' := by
  rw [hh, hpa, hpm, hpl, hpc, hcv_eq, hcl_eq, hop_eq, htrl_eq, hrsn_eq, hrsz_val]
  clear hh hpa hpm hpl hpc hcv_eq hcl_eq hop_eq htrl_eq hrsn_eq hrsz_val
  have hcl := hlen.core_ok
  have hmv := fullInv_max_vars_lt32 c
  have hcv_le := hcl.cur_vars_le
  have har_len_le := hcl.arena_len_le
  have har_arr := hcl.arena_len_arr
  have hlvl_len := hcl.lvl_len
  have hrsn32 : rsn_v.toNat < 2 ^ 32 := rsn_v.isLt
  have hcv_c0 : s.core.cur_vars % 18446744073709551616 = s.core.cur_vars :=
    Nat.mod_eq_of_lt (by omega)
  unfold hbrInnerExpr
  refine wp_loop_inv
    (fun (clen_j, open_j, j, ()) mj => ∃ mrk_j clr_j,
      hbrInnerInv c s rsn_v.toNat (idx - 1#64).toNat j.toNat clen_j.toNat open_j.toNat
        mrk' mrk_j clr_j ∧
      (FullMem c (hbrState s mrk_j clr_j) ⋆ R) mj)
    (fun (_clen_j, _open_j, j, ()) _ => fullArenaClauseSize s rsn_v.toNat - j.toNat)
    (fun Jj_l hLj => ?_)
    (fun Jj_l (clen_j, open_j, j, ()) mj ⟨mrk_j, clr_j, hj_inv, hmj⟩ hLj => ?_)
  · refine hLj (clen', open_c' - 1#64, 0#32, ()) ml' ⟨mrk', clr', ?_, hm'⟩
    rw [hop_sub]
    exact hbrInner_init (hidx_succ ▸ hl2) (by
      rwa [List.getElem?_eq_getElem (l := s.core.trl) htrl_i, Option.getD_some])
  · pt_steps_nogrp
    · have hj_lt : j.toNat < fullArenaClauseSize s rsn_v.toNat := by
        pt_clear_big; simp only [hrsz_mod] at hc; pt_bound
      have hj32 : j.toNat + 1 < 2 ^ 32 := by omega
      have hqidx : rsn_v.toNat + 3 + j.toNat < s.core.arena.length := by omega
      have hqmod : (rsn_v.toNat + 3 + j.toNat) % 18446744073709551616 =
          rsn_v.toNat + 3 + j.toNat := Nat.mod_eq_of_lt (by omega)
      have hmem_q : (s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx).toNat ∈
          fullArenaClauseLits s rsn_v.toNat :=
        (mem_fullArenaClauseLitsCore_iff hrsn_bd_core).mpr ⟨j.toNat, hj_lt, rfl⟩
      have hq_lt : (s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx).toNat < 2 * s.core.cur_vars :=
        hw.arena.lits_lt rsn_v.toNat hrsn_ref hrsn_ng _ hmem_q
      have hovj_lt : (s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx >>>
          (1 : Nat)).toNat < s.core.cur_vars := by rw [bv32_toNat_lshr1]; omega
      pt_steps_nogrp
      refine wp_join_group
        (fun (clen_j', open_j', ()) mj' => ∃ mrk_j' clr_j',
          hbrInnerInv c s rsn_v.toNat (idx - 1#64).toNat (j.toNat + 1)
            clen_j'.toNat open_j'.toNat mrk' mrk_j' clr_j' ∧
          (FullMem c (hbrState s mrk_j' clr_j') ⋆ R) mj')
        (fun _ (clen_j', open_j', ()) mj' ⟨mrk_j', clr_j', hj', hmj'⟩ => ?_) ?_
      · pt_steps_nogrp
        refine hLj (clen_j', open_j', j + 1#32, ()) mj'
          (by dsimp only; rw [bv32_add1_toNat hj32]; omega)
          ⟨mrk_j', clr_j', by rw [bv32_add1_toNat hj32]; exact hj', hmj'⟩
      · intro Jjb hJjb
        have hmrkj_len := hj_inv.1.mrk_len; have hclrj_len := hj_inv.1.clr_len
        have hclj_le := hj_inv.1.clen_le
        have hj_bd : rsn_v.toNat + 3 + fullArenaClauseSize s rsn_v.toNat ≤
            s.core.arena.length := by omega
        have hovj_lvl : (s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx).toNat / 2 <
            s.core.lvl.length := by rw [hlvl_len]; rw [bv32_toNat_lshr1] at hovj_lt; omega
        have hovj_mrk : (s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx).toNat / 2 <
            mrk_j.length := by rw [hmrkj_len]; rw [bv32_toNat_lshr1] at hovj_lt; omega
        pt_steps_nogrp
        · have hovj_ne : (s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx >>> (1 : Nat)).toNat ≠
              (s.core.trl[(idx - 1#64).toNat]?.getD 0#32).toNat / 2 := by
            pt_clear_big
            rw [bv32_toNat_lshr1, List.getElem?_eq_getElem htrl_i, Option.getD_some]
            simp only [hqmod] at *
            intro heq
            have hne : ¬ s.core.arena[rsn_v.toNat + 3 + j.toNat] >>> 1 =
                s.core.trl[(idx - 1#64).toNat] >>> 1 := by assumption
            apply hne; apply BitVec.eq_of_toNat_eq
            rw [bv32_toNat_lshr1, bv32_toNat_lshr1]; exact heq
          refine wp_load_of (FullArenaTactics.c0_load_full_lvl ?_ hmj) ?_
          · simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat, hqmod]
            exact hovj_lvl
          pt_steps_nogrp
          · have hlvl1j : (s.core.lvl[(s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx >>>
                (1 : Nat)).toNat]?.getD 0#32).toNat = 1 := by
              pt_clear_big; rw [bv32_toNat_lshr1]; simp only [hqmod] at hc
              exact lvl_toNat_eq1 hovj_lvl hc
            refine wp_load_of (FullArenaTactics.c0_load_full_mrk ?_ hmj) ?_
            · simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat, hqmod]
              exact hovj_mrk
            pt_steps_nogrp
            · have hm0j : mrk_j[(s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx >>>
                  (1 : Nat)).toNat]?.getD 0#8 = 0#8 := by
                pt_clear_big; rw [bv32_toNat_lshr1]
                simp only [bv_c0, Nat.reducePow, hqmod] at *
                exact mrk_getD_eq0 hovj_mrk (by assumption)
              have hstepj := hbrInner_step_mark hlen hw hj_inv hrsn_ref hrsn_ng
                (by omega) hj_lt hidx_lt hrsn_lits' rfl hovj_ne hovj_lt hlvl1j hm0j
              have hclj_lt := hstepj.1.clen_le
              refine wp_store_sep (FullArenaTactics.c0_store_full_mrk _ ?_ hmj) fun m1 hm1 => ?_
              · simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat, hqmod]; exact hovj_mrk
              pt_steps_nogrp
              refine wp_store_sep (FullArenaTactics.c0_store_full_min_clr _
                (by rw [hclrj_len]; omega) hm1) fun m hm => ?_
              pt_steps_nogrp
              have hcl1j_eq : (clen_j + 1#64).toNat = clen_j.toNat + 1 := bv64_add1_toNat (by omega)
              have hop1j_eq : (open_j + 1#64).toNat = open_j.toNat + 1 := by
                have := hstepj.2.2.1; have := hcl.trail_end_le; exact bv64_add1_toNat (by omega)
              refine hJjb (clen_j + 1#64, open_j + 1#64, ()) m ⟨_, _,
                by rw [hcl1j_eq, hop1j_eq]; exact hstepj, ?_⟩
              simp only [Arg.val_var, bv_c0, Nat.reducePow, BitVec.reduceToNat,
                bv32_toNat_lshr1, hqmod] at hm
              simpa only [← bv32_toNat_lshr1] using hm
            · clear hw hlen hrsn_lits' hrsn_ref hrsn_ng
              have hm0j : mrk_j[(s.core.arena[rsn_v.toNat + 3 + j.toNat]'hqidx >>>
                  (1 : Nat)).toNat]?.getD 0#8 = 0#8 := by
                pt_clear_big; rw [bv32_toNat_lshr1]
                simp only [bv_c0, Nat.reducePow, hqmod] at *
                exact mrk_getD_eq0 hovj_mrk (by assumption)
              have hclj_lt := hbrMarkInv_clen_lt hj_inv.1.mark_inv
                (by rw [hclrj_len]; exact hcv_le) hovj_lt hm0j
              exfalso; rw [hcv_c0] at hc; omega
            · clear hw hlen hrsn_lits' hrsn_ref hrsn_ng
              simp only [hqmod] at hc
              exact hJjb (clen_j, open_j, ()) mj ⟨mrk_j, clr_j,
                hbrInner_step_same hj_inv hj_bd hj_lt
                  (Or.inr (Or.inr (mrk_getD_ne0 hovj_mrk hc))), hmj⟩
          · clear hw hlen hrsn_lits' hrsn_ref hrsn_ng
            simp only [hqmod] at hc
            exact hJjb (clen_j, open_j, ()) mj ⟨mrk_j, clr_j,
              hbrInner_step_same hj_inv hj_bd hj_lt
                (Or.inr (Or.inl (lvl_toNat_ne1 hovj_lvl hc))), hmj⟩
        · clear hw hlen hrsn_lits' hrsn_ref hrsn_ng
          exfalso; pt_clear_big; simp only [hqmod] at hc; rw [hcv_c0] at hc
          exact hc (by rw [← bv32_toNat_lshr1]; exact hovj_lt)
        · clear hw hlen hrsn_lits' hrsn_ref hrsn_ng
          simp only [hqmod] at hc
          exact hJjb (clen_j, open_j, ()) mj ⟨mrk_j, clr_j,
            hbrInner_step_same hj_inv hj_bd hj_lt (Or.inl (by
              pt_clear_big
              rw [List.getElem?_eq_getElem htrl_i, Option.getD_some]
              have hto := congrArg BitVec.toNat hc
              simp only [bv32_toNat_lshr1] at hto; exact hto)), hmj⟩
    · exfalso
      have ha64 : s.core.arena_len < 18446744073709551616 :=
        Nat.lt_of_le_of_lt har_len_le (by have := c.harena; unfold dimacsBound at this; omega)
      pt_clear_big; simp only [hrsz_mod] at hc
      have h64 : rsn_v.toNat + 3 + fullArenaClauseSize s rsn_v.toNat <
          18446744073709551616 := by
        have : fullArenaClauseSize s rsn_v.toNat < 2 ^ 32 := by
          rw [← hrsz_eq]; exact BitVec.isLt _
        omega
      simp only [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt ha64] at hc
      omega
    · have hj_le := hj_inv.2.1
      have hj_eq : j.toNat = fullArenaClauseSize s rsn_v.toNat := by
        simp only [hrsz_mod] at hc; omega
      exact hJ clen_j open_j mj mrk_j clr_j
        (hbrLoop2_large_finish hw hcl1 (hidx_succ ▸ hl2) (hj_eq ▸ hj_inv)
          hidx_lt hrsn_ref hrsn_ng (by omega) hrsn_lits') hmj

theorem full_hbr_dom_wp (Γ : Env) :
    ∀ args m Q X, fullHbrDomSpec args m Q X → Func.wp Γ full_hbr_dom_body args m Q X := by
  rintro ⟨h, cref, implied, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, ⟨wv, ws, wl, hw_raw⟩, hmrk0, hcl1, hcref, hng,
      _him_mem_raw, hfal, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmv := fullInv_max_vars_lt32 c
  have hcv_le := hcl.cur_vars_le
  have hw : FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core :=
    fullWitnessInv_replace_watches hw_raw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      { hcl with wvec_len := by simp, wlen_le := Nat.zero_le _ }
      (modeWatchesInv_empty c F_cur s hcv_le)
  clear hw_raw
  have ⟨_hsz3, har_le⟩ : 3 ≤ fullArenaClauseSize s cref.toNat ∧
      cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ s.core.arena_len := by
    have hwf_cref := hw.arena.refs_wf cref.toNat hcref
    exact ⟨hwf_cref.2.1, Nat.le_trans hwf_cref.2.2.1 hwf_cref.2.2.2.1⟩
  have har_len_le := hcl.arena_len_le
  have har_arr := hcl.arena_len_arr
  have hcref32 : cref.toNat < 2 ^ 32 := cref.isLt
  have hsz_eq : s.core.arena[cref.toNat + 2].toNat = fullArenaClauseSize s cref.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsz_eq_mod : s.core.arena[(cref.toNat + 2) % 18446744073709551616].toNat =
      fullArenaClauseSize s cref.toNat := by
    simp only [Nat.mod_eq_of_lt (by omega : cref.toNat + 2 < 18446744073709551616), hsz_eq]
  pt_steps
  refine wp_loop_inv
    (fun (clen, open_c, i, ()) ml => ∃ mrk clr,
      hbrLoop1Inv c s cref.toNat implied.toNat i.toNat clen.toNat open_c.toNat mrk clr ∧
      (FullMem c (hbrState s mrk clr) ⋆ R) ml)
    (fun (_clen, _open_c, i, ()) _ => fullArenaClauseSize s cref.toNat - i.toNat)
    (fun J hLoop => ?_)
    (fun J (clen, open_c, i, ()) ml ⟨mrk, clr, hl1, hml⟩ hLoop => ?_)
  · pt_steps
    exact hLoop (0#64, 0#64, 0#32, ()) m
      ⟨s.core.mrk, s.core.min_clr, hbrLoop1_init hlen hw hmrk0, hm⟩
  · pt_steps_nogrp
    · have hi_lt : i.toNat < fullArenaClauseSize s cref.toNat := by pt_bound
      have hi_32 : i.toNat + 1 < 2 ^ 32 := by omega
      have hidx_lt : cref.toNat + 3 + i.toNat < s.core.arena.length := by omega
      have hidx_mod : (cref.toNat + 3 + i.toNat) % 18446744073709551616 =
          cref.toNat + 3 + i.toNat := Nat.mod_eq_of_lt (by omega)
      have hbd_core : cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤
          s.core.arena.length := by
        change cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ s.core.arena.length; omega
      have hmem_l : (s.core.arena[cref.toNat + 3 + i.toNat]'hidx_lt).toNat ∈
          fullArenaClauseLits s cref.toNat :=
        (mem_fullArenaClauseLitsCore_iff hbd_core).mpr ⟨i.toNat, hi_lt, rfl⟩
      have hl_lt : (s.core.arena[cref.toNat + 3 + i.toNat]'hidx_lt).toNat <
          2 * s.core.cur_vars := hw.arena.lits_lt cref.toNat hcref hng _ hmem_l
      pt_steps_nogrp
      refine wp_join_group
        (fun (clen', open', ()) ml' => ∃ mrk' clr',
          hbrLoop1Inv c s cref.toNat implied.toNat (i.toNat + 1) clen'.toNat open'.toNat
            mrk' clr' ∧
          (FullMem c (hbrState s mrk' clr') ⋆ R) ml')
        (fun _ (clen', open', ()) ml' ⟨mrk', clr', hjn, hm'⟩ => ?_) ?_
      · pt_steps_nogrp
        refine hLoop (clen', open', i + 1#32, ()) ml'
          (by dsimp only; rw [bv32_add1_toNat hi_32]; omega)
          ⟨mrk', clr', by rw [bv32_add1_toNat hi_32]; exact hjn, hm'⟩
      · intro Jj hJj
        have hmrk_len' : mrk.length = c.max_vars := hl1.1.mrk_len
        have hclr_len' : clr.length = c.max_vars := hl1.1.clr_len
        have hlvl_len : s.core.lvl.length = c.max_vars := hcl.lvl_len
        have hcl_le' : clen.toNat ≤ s.core.cur_vars := hl1.1.clen_le
        have hv_lt : (s.core.arena[cref.toNat + 3 + i.toNat]'hidx_lt >>> (1 : Nat)).toNat <
            s.core.cur_vars := by rw [bv32_toNat_lshr1]; omega
        pt_steps_nogrp
        · refine wp_load_of (FullArenaTactics.c0_load_full_lvl ?_ hml) ?_
          · simp only [bv_c0, hidx_mod, Nat.reducePow, BitVec.reduceToNat]
            rw [bv32_toNat_lshr1] at hv_lt; omega
          pt_steps_nogrp
          · have hc_imp : (s.core.arena[cref.toNat + 3 + i.toNat]'hidx_lt).toNat ≠
                implied.toNat := by
              pt_clear_big; intro heq; simp only [hidx_mod] at *
              have hne : ¬ s.core.arena[cref.toNat + 3 + i.toNat] = implied := by assumption
              exact hne (BitVec.eq_of_toNat_eq heq)
            have hc_lvl : (s.core.lvl[(s.core.arena[cref.toNat + 3 + i.toNat]'hidx_lt >>>
                (1 : Nat)).toNat]?.getD 0#32).toNat = 1 := by
              pt_clear_big; rw [bv32_toNat_lshr1]; simp only [hidx_mod] at *
              exact lvl_toNat_eq1 (by omega) (by assumption)
            have hm0v : mrk[(s.core.arena[cref.toNat + 3 + i.toNat]'hidx_lt >>>
                (1 : Nat)).toNat]?.getD 0#8 = 0#8 := by
              pt_clear_big; rw [bv32_toNat_lshr1]; simp only [hidx_mod] at *
              exact mrk_getD_eq0 (by omega) (by assumption)
            have hstep := hbrLoop1_step_mark hlen hw hl1 hcref hng hfal (by omega) hi_lt
              rfl hc_imp hv_lt hc_lvl hm0v
            have hcl_lt := hstep.1.clen_le
            refine wp_store_sep (FullArenaTactics.c0_store_full_min_clr _
              (by change clen.toNat < clr.length; omega) hm) fun m hm => ?_
            pt_steps_nogrp
            have hcl1_eq : (clen + 1#64).toNat = clen.toNat + 1 := bv64_add1_toNat (by omega)
            have hop1_eq : (open_c + 1#64).toNat = open_c.toNat + 1 := by
              have := hl1.2.2.1; exact bv64_add1_toNat (by omega)
            have hidx_w : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 i).toNat =
                cref.toNat + 3 + i.toNat := by bv_omega
            have hmrk_idx : (BitVec.setWidth 64 (s.core.arena[(BitVec.setWidth 64 cref + 3 +
                BitVec.setWidth 64 i).toNat]'(by omega) >>> 1)).toNat =
                (s.core.arena[cref.toNat + 3 + i.toNat]'hidx_lt >>> (1 : Nat)).toNat := by
              have hlt64 : (s.core.arena[(BitVec.setWidth 64 cref + 3 +
                  BitVec.setWidth 64 i).toNat]'(by omega) >>> (1 : Nat)).toNat < 2 ^ 64 := by
                rw [bv32_toNat_lshr1]; omega
              simp only [bv_c0, hidx_w]
            refine hJj (clen + 1#64, open_c + 1#64, ()) m ⟨_, _,
              by rw [hcl1_eq, hop1_eq]; exact hstep, ?_⟩
            simpa only [Arg.val_var, bv_c0, hidx_mod, hidx_w, hmrk_idx] using hm
          · simp only [hidx_mod] at hc
            exact hJj (clen, open_c, ()) ml ⟨mrk, clr,
              hbrLoop1_step_same hl1 (by omega) hi_lt
                (Or.inr (Or.inr (mrk_getD_ne0 (by omega) hc))), hml⟩
          · simp only [hidx_mod] at hc
            exact hJj (clen, open_c, ()) ml ⟨mrk, clr,
              hbrLoop1_step_same hl1 (by omega) hi_lt
                (Or.inr (Or.inl (lvl_toNat_ne1 (by omega) hc))), hml⟩
        · exfalso
          have hcm := Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 18446744073709551616)
          simp only [hidx_mod, hcm] at hc
          exact hc (by rw [← bv32_toNat_lshr1]; exact hv_lt)
        · simp only [hidx_mod] at hc
          exact hJj (clen, open_c, ()) ml ⟨mrk, clr,
            hbrLoop1_step_same hl1 (by omega) hi_lt
              (Or.inl (congrArg BitVec.toNat hc)), hml⟩
    · have hi_eq : i.toNat = fullArenaClauseSize s cref.toNat := by
        rw [hsz_eq_mod] at hc; have := hl1.2.1; omega
      refine wp_join_group
        (fun (clen', _open_c', dom, ()) ml' => ∃ mrk' clr',
          hbrOutInv c s F_cur implied.toNat clen'.toNat dom mrk' clr' ∧
          (FullMem c (hbrState s mrk' clr') ⋆ R) ml')
        (fun _ (clen', _open_c', dom, ()) ml' ⟨mrk', clr', hout, hm'⟩ => ?_) ?_
      · clear hw hfal hcref hng
        pt_steps_nogrp
        refine wp_loop_inv
          (fun (k, ()) mk => ∃ mrkk,
            hbrLoop3Inv c s k.toNat clen'.toNat mrkk clr' ∧
            (FullMem c (hbrState s mrkk clr') ⋆ R) mk)
          (fun (k, ()) _ => clen'.toNat - k.toNat)
          (fun Jk hLk => ?_)
          (fun Jk (k, ()) mk ⟨mrkk, hk3, hmk⟩ hLk => ?_)
        · pt_steps_nogrp
          exact hLk (0#64, ()) ml' ⟨mrk', hbrLoop3_init hlen hout, hm'⟩
        · pt_steps_nogrp
          · have hk_lt : k.toNat < clen'.toNat := by pt_bound
            have hclr_len' : clr'.length = c.max_vars := hout.1.clr_len
            have hcl_le' : clen'.toNat ≤ s.core.cur_vars := hout.1.clen_le
            have hmrkk_len : mrkk.length = c.max_vars := hk3.2.1
            have hck_lt : (clr'[k.toNat]'(by omega)).toNat < s.core.cur_vars := by
              have hcl0 := hout.1.mark_inv.2.2.2.2.1 k.toNat hk_lt
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hcl0
            pt_steps_nogrp
            have hk1_eq : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
            refine hLk (k + 1#64, ()) m (by dsimp only; rw [hk1_eq]; omega)
              ⟨_, by rw [hk1_eq]; exact hbrLoop3_step hcv_le hout hk3 hk_lt, hm⟩
          · have hk_eq : k.toNat = clen'.toNat := by have := hk3.1; omega
            obtain ⟨hmrk_eq, hlen_fin⟩ := hbrLoop3_fin hlen hmrk0 hout (hk_eq ▸ hk3)
            rw [hmrk_eq] at hmk
            refine hQ dom s.core.mrk clr' mk hlen_fin hmrk0 hout.2 ?_
            exact hmk
      · intro Jout hJout
        pt_steps_nogrp
        · refine wp_join_group
            (fun (clen', _open_c', dom, _idx, ()) ml' => ∃ mrk' clr',
              hbrOutInv c s F_cur implied.toNat clen'.toNat dom mrk' clr' ∧
              (FullMem c (hbrState s mrk' clr') ⋆ R) ml')
            (fun _ (clen', _open_c', dom, _idx, ()) ml' hjn => by
              pt_steps_nogrp; exact hJout (clen', _open_c', dom, ()) ml' hjn)
            (fun J2e hJ2e => ?_)
          pt_steps_nogrp
          refine wp_loop_inv
            (fun (clen', open_c', idx, ()) ml' => ∃ mrk' clr',
              hbrLoop2Inv c s F_cur implied.toNat clen'.toNat open_c'.toNat idx.toNat
                mrk' clr' ∧
              (FullMem c (hbrState s mrk' clr') ⋆ R) ml')
            (fun (_clen', _open_c', idx, ()) _ => idx.toNat)
            (fun J2 hL2 => ?_)
            (fun J2 (clen', open_c', idx, ()) ml' ⟨mrk', clr', hl2, hm'⟩ hL2 => ?_)
          · pt_steps_nogrp
            have hte_le := hcl.trail_end_le
            have hte32 : s.core.trail_end < 2 ^ 64 := by omega
            refine hL2 (clen, open_c, BitVec.ofNat 64 s.core.trail_end, ()) ml
              ⟨mrk, clr, ?_, hml⟩
            rw [bv64_ofNat_toNat hte32]
            exact hbrLoop2_init hw hcl1 hcref hng (by omega) hfal (hi_eq ▸ hl1)
          · clear hJout hLoop _him_mem_raw hml hl1 hcref hng hm hmrk0 hcref32 hfal
            pt_steps_nogrp
            · have hop_pos : 0 < open_c'.toNat := by pt_bound
              have hidx_pos : 0 < idx.toNat := by pt_bound
              have hidx_pred : (idx - 1#64).toNat = idx.toNat - 1 :=
                bv64_sub1_toNat (fun heq => by subst heq; simp at hidx_pos)
              have hte_le := hcl.trail_end_le; have htrl_len := hcl.trl_len
              have hlvl_len := hcl.lvl_len; have hrsn_len := hcl.rsns_len
              have hmrk_len' := hl2.1.mrk_len; have hclr_len' := hl2.1.clr_len
              have hcl_le' := hl2.1.clen_le
              have hidx_lt : (idx - 1#64).toNat < s.core.trail_end := by
                have := hl2.2.2.1; omega
              have hidx_succ : idx.toNat = (idx - 1#64).toNat + 1 := by omega
              have hp_lt : (s.core.trl[(idx - 1#64).toNat]'(by omega)).toNat <
                  2 * s.core.cur_vars := by
                have := hw.trail_lits_lt (idx - 1#64).toNat hidx_lt
                dsimp only [withEmptyModeWatches] at this
                rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
              have hpv_lt : (s.core.trl[(idx - 1#64).toNat]'(by omega) >>> (1 : Nat)).toNat <
                  s.core.cur_vars := by rw [bv32_toNat_lshr1]; omega
              have hidx_c0 : (18446744073709551616 - 1 + idx.toNat) % 18446744073709551616 =
                  idx.toNat - 1 := by omega
              have hcv_c0 : s.core.cur_vars % 18446744073709551616 = s.core.cur_vars :=
                Nat.mod_eq_of_lt (by omega)
              have hop_sub : (open_c' - 1#64).toNat = open_c'.toNat - 1 :=
                bv64_sub1_toNat (fun heq => by subst heq; simp at hop_pos)
              pt_steps_nogrp
              · simp only [hidx_c0, ← hidx_pred, hcv_c0] at hc
                rw [bv32_toNat_lshr1] at hpv_lt; exfalso; omega
              · refine hL2 (clen', open_c', idx - 1#64, ()) ml' (by dsimp only; omega)
                  ⟨mrk', clr', hbrLoop2_skip (hidx_succ ▸ hl2) (by
                    rw [List.getElem?_eq_getElem (l := s.core.trl) (by omega), Option.getD_some]
                    by_cases hm0 : mrk'[(s.core.trl[(idx - 1#64).toNat]'(by omega)).toNat /
                        2]?.getD 0#8 = 0#8
                    · exact hm0
                    · exfalso
                      have hlv1 := hl2.1.lvl1 _ (by rw [← bv32_toNat_lshr1]; exact hpv_lt) hm0
                      simp only [hidx_c0, ← hidx_pred] at hc
                      exact lvl_toNat_ne1 (by omega) hc hlv1), hm'⟩
              · simp only [hidx_c0, ← hidx_pred] at hc
                refine hL2 (clen', open_c', idx - 1#64, ()) ml' (by dsimp only; omega)
                  ⟨mrk', clr', hbrLoop2_skip (hidx_succ ▸ hl2) (by
                    rw [List.getElem?_eq_getElem (l := s.core.trl) (by omega), Option.getD_some]
                    exact mrk_getD_eq0 (by omega) hc), hm'⟩
              · have hm_nz : mrk'[(s.core.trl[(idx - 1#64).toNat]'(by omega)).toNat / 2]?.getD
                    0#8 ≠ 0#8 := by
                  pt_clear_big; simp only [hidx_c0, ← hidx_pred] at *
                  exact mrk_getD_ne0 (by omega) (by assumption)
                have hop1 : open_c'.toNat = 1 := by
                  have h0 := congrArg BitVec.toNat hc
                  change (open_c' - 1#64).toNat = 0 at h0; omega
                have hl2' := hl2; rw [hop1, hidx_succ] at hl2'
                refine hJ2e (clen', open_c' - 1#64,
                  s.core.trl[(idx - 1#64).toNat]'(by omega), idx - 1#64, ()) ml'
                  ⟨mrk', clr', hbrLoop2_root hlen hw hl2' hidx_lt (by
                    rwa [List.getElem?_eq_getElem (l := s.core.trl) (by omega),
                      Option.getD_some]), hm'⟩
              · exact hJ2e (clen', open_c' - 1#64, 0xFFFFFFFF#32, idx - 1#64, ()) ml'
                  ⟨mrk', clr', ⟨hl2.1, Or.inl rfl⟩, hm'⟩
              · have hm_nz : mrk'[(s.core.trl[(idx - 1#64).toNat]'(by omega)).toNat / 2]?.getD
                    0#8 ≠ 0#8 := by
                  pt_clear_big; simp only [hidx_c0, ← hidx_pred] at *
                  exact mrk_getD_ne0 (by omega) (by assumption)
                have htrl_i : (idx - 1#64).toNat < s.core.trl.length := by omega
                have hrsn_i : (s.core.trl[(idx - 1#64).toNat]'htrl_i).toNat / 2 <
                    s.core.rsns.length := by omega
                have hrsn_ne : s.core.rsns[(s.core.trl[(idx - 1#64).toNat]'htrl_i).toNat /
                    2]'hrsn_i ≠ 0xFFFFFFFF#32 := by
                  simp only [hidx_c0, ← hidx_pred] at hc; exact hc
                have hrsn_inv := hw.reason_inv (idx - 1#64).toNat hidx_lt
                dsimp only [withEmptyModeWatches] at hrsn_inv
                rw [List.getElem?_eq_getElem htrl_i, Option.getD_some,
                  List.getElem?_eq_getElem hrsn_i, Option.getD_some] at hrsn_inv
                have hrsn_inv' := hrsn_inv hrsn_ne
                pt_step
                pt_steps_nogrp
                · have hbf : (s.core.rsns[(s.core.trl[(idx - 1#64).toNat]'htrl_i).toNat /
                        2]'hrsn_i &&& 0x80000000#32) ≠ 0#32 := by
                    simp only [hidx_c0, ← hidx_pred] at hc; exact hc
                  rw [ite_eq_left hbf] at hrsn_inv'
                  obtain ⟨hot_lt, hent_b, m_w, hm_w, hmw_eq, hmw_lvl⟩ := hrsn_inv'
                  let ov := (s.core.rsns[(s.core.trl[(idx - 1#64).toNat]'htrl_i).toNat /
                    2]'hrsn_i &&& 0x7FFFFFFF#32) >>> (1 : Nat)
                  have hov_eq : ov.toNat = ((s.core.rsns[(s.core.trl[(idx - 1#64).toNat]'
                      htrl_i).toNat / 2]'hrsn_i &&& 0x7FFFFFFF#32).toNat) / 2 :=
                    bv32_toNat_lshr1 _
                  have hov_lt : ov.toNat < s.core.cur_vars := by omega
                  have hent_b' : (cnfOfClauses F_cur).EntailsClause (cnfClause [
                      (s.core.trl[(idx - 1#64).toNat]?.getD 0#32).toNat,
                      (s.core.rsns[(s.core.trl[(idx - 1#64).toNat]'htrl_i).toNat /
                        2]'hrsn_i &&& 0x7FFFFFFF#32).toNat]) := by
                    rwa [List.getElem?_eq_getElem htrl_i, Option.getD_some]
                  pt_step
                  pt_steps_nogrp
                  · have hm0 : mrk'[ov.toNat]?.getD 0#8 = 0#8 := by
                      pt_clear_big; simp only [hov_eq, hidx_c0, ← hidx_pred] at *
                      exact mrk_getD_eq0 (by omega) (by assumption)
                    have hlvl1 : (s.core.lvl[ov.toNat]?.getD 0#32).toNat = 1 := by
                      pt_clear_big; simp only [hov_eq, hidx_c0, ← hidx_pred] at *
                      exact lvl_toNat_eq1 (by omega) (by assumption)
                    have hstep := hbrLoop2_bin_mark hlen hw (hidx_succ ▸ hl2) hidx_lt hop_pos
                      (by rwa [List.getElem?_eq_getElem (l := s.core.trl) (by omega),
                        Option.getD_some])
                      hov_eq hov_lt hlvl1 hm0 hent_b' hm_w hmw_eq
                    have hcl_lt := hstep.1.clen_le
                    pt_steps_nogrp
                    have hcl1_eq : (clen' + 1#64).toNat = clen'.toNat + 1 :=
                      bv64_add1_toNat (by omega)
                    refine hL2 (clen' + 1#64, (open_c' - 1#64) + 1#64, idx - 1#64, ()) m
                      (by dsimp only; omega)
                      ⟨mrk'.set ov.toNat 1#8, clr'.set clen'.toNat ov, ?_, ?_⟩
                    · rw [hcl1_eq, bv64_add1_toNat (by omega), hop_sub,
                        show open_c'.toNat - 1 + 1 = open_c'.toNat by omega]
                      exact hstep
                    · have hidx_c0b : (18446744073709551615 + idx.toNat) % 18446744073709551616 =
                          idx.toNat - 1 := by omega
                      have hov_c : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
                      have h1_c : (1 : BitVec 64).toNat = 1 := rfl
                      dsimp only [ov]
                      simpa only [bv_c0, Nat.reducePow, h1_c, hov_c, hidx_c0, hidx_c0b,
                        hidx_pred] using hm
                  · exfalso
                    have hm0 : mrk'[ov.toNat]?.getD 0#8 = 0#8 := by
                      pt_clear_big; simp only [hov_eq, hidx_c0, ← hidx_pred] at *
                      exact mrk_getD_eq0 (by omega) (by assumption)
                    have hcl_lt := hbrMarkInv_clen_lt hl2.1.mark_inv
                      (by rw [hclr_len']; exact hcv_le) hov_lt hm0
                    rw [hcv_c0] at hc; omega
                  · simp only [hidx_c0, ← hidx_pred] at hc
                    refine hL2 (clen', open_c' - 1#64, idx - 1#64, ()) ml' (by dsimp only; omega)
                      ⟨mrk', clr', ?_, hm'⟩
                    rw [hop_sub]
                    exact hbrLoop2_bin_skip hw hcl1 (hidx_succ ▸ hl2) hidx_lt hop_pos
                      (by rwa [List.getElem?_eq_getElem (l := s.core.trl) (by omega),
                        Option.getD_some])
                      hot_lt hent_b' hm_w hmw_eq
                      (by rwa [List.getElem?_eq_getElem (l := s.core.trl) (by omega),
                        Option.getD_some])
                      (Or.inl (mrk_getD_ne0 (by omega) hc))
                  · simp only [hidx_c0, ← hidx_pred] at hc
                    refine hL2 (clen', open_c' - 1#64, idx - 1#64, ()) ml' (by dsimp only; omega)
                      ⟨mrk', clr', ?_, hm'⟩
                    rw [hop_sub]
                    exact hbrLoop2_bin_skip hw hcl1 (hidx_succ ▸ hl2) hidx_lt hop_pos
                      (by rwa [List.getElem?_eq_getElem (l := s.core.trl) (by omega),
                        Option.getD_some])
                      hot_lt hent_b' hm_w hmw_eq
                      (by rwa [List.getElem?_eq_getElem (l := s.core.trl) (by omega),
                        Option.getD_some])
                      (Or.inr (lvl_toNat_ne1 (by omega) hc))
                  · exfalso
                    pt_clear_big
                    rw [hcv_c0, show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] at hc
                    simp only [hidx_c0, ← hidx_pred, ← hov_eq] at hc
                    exact hc hov_lt
                · have hbf : (s.core.rsns[(s.core.trl[(idx - 1#64).toNat]'htrl_i).toNat /
                        2]'hrsn_i &&& 0x80000000#32) = 0#32 := by
                    simp only [hidx_c0, ← hidx_pred] at hc; exact hc
                  have hbf' : ¬ (s.core.rsns[(s.core.trl[(idx - 1#64).toNat]'htrl_i).toNat /
                      2]'hrsn_i &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hbf h
                  rw [ite_eq_right hbf'] at hrsn_inv'
                  obtain ⟨rsn_v, hrsn_v_eq⟩ : ∃ rv : BitVec 32,
                      rv = s.core.rsns[(s.core.trl[(idx - 1#64).toNat]'htrl_i).toNat /
                        2]'hrsn_i := ⟨_, rfl⟩
                  rw [← hrsn_v_eq] at hrsn_inv'
                  obtain ⟨hrsn_ref, hrsn_ng, hrsn_lits⟩ := hrsn_inv'
                  clear hrsn_inv hrsn_ne hbf hbf'
                  have ⟨_hrsz3, hrsn_le⟩ : 3 ≤ fullArenaClauseSize s rsn_v.toNat ∧
                      rsn_v.toNat + 3 + fullArenaClauseSize s rsn_v.toNat ≤ s.core.arena_len := by
                    have hwf_rsn := hw.arena.refs_wf rsn_v.toNat hrsn_ref
                    exact ⟨hwf_rsn.2.1, Nat.le_trans hwf_rsn.2.2.1 hwf_rsn.2.2.2.1⟩
                  have hrsn32 : rsn_v.toNat < 2 ^ 32 := rsn_v.isLt
                  have hrsn2_lt : rsn_v.toNat + 2 < s.core.arena.length := by omega
                  have hrsz_eq : (s.core.arena[rsn_v.toNat + 2]'hrsn2_lt).toNat =
                      fullArenaClauseSize s rsn_v.toNat := by
                    unfold fullArenaClauseSize fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem hrsn2_lt, Option.getD_some]
                  have hrsn2_mod : (rsn_v.toNat + 2) % 18446744073709551616 < s.core.arena.length :=
                    Nat.lt_of_le_of_lt (Nat.mod_le _ _) hrsn2_lt
                  have hrsz_mod : (s.core.arena[(rsn_v.toNat + 2) %
                      18446744073709551616]'hrsn2_mod).toNat =
                      fullArenaClauseSize s rsn_v.toNat := by
                    simp only [Nat.mod_eq_of_lt (by omega : rsn_v.toNat + 2 < 18446744073709551616),
                      hrsz_eq]
                  have hrsn_bd_core : rsn_v.toNat + 3 + fullArenaClauseSizeCore s.core rsn_v.toNat ≤
                      s.core.arena.length := by
                    change rsn_v.toNat + 3 + fullArenaClauseSize s rsn_v.toNat ≤ _ ; omega
                  have hrsn_lits' : ∀ q ∈ fullArenaClauseLits s rsn_v.toNat,
                      q = (s.core.trl[(idx - 1#64).toNat]?.getD 0#32).toNat ∨
                      ∃ m < (idx - 1#64).toNat, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ (s.core.lvl[(s.core.trl[(idx -
                          1#64).toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                    intro q hq
                    have hgt := List.getElem?_eq_getElem (l := s.core.trl)
                      (i := (idx - 1#64).toNat) (by omega)
                    simpa only [hgt, Option.getD_some] using hrsn_lits q hq
                  clear hrsn_lits
                  pt_step
                  pt_steps_nogrp
                  · refine hbrInnerLoop_wp hlen hw hcl1 rfl rfl rfl rfl rfl rfl rfl rfl htrl_i rfl
                      (by simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                          simp only [hidx_c0]; simp only [← hidx_pred, ← hrsn_v_eq])
                      hrsn2_lt hrsn2_mod
                      (by simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                          simp only [hidx_c0]; simp only [← hidx_pred, ← hrsn_v_eq])
                      hidx_lt hidx_succ hop_sub hrsn_ref hrsn_ng hrsn_le hrsz_eq hrsz_mod
                      hrsn_bd_core hrsn_lits' hl2 hm_nz hm'
                      (fun cl_j op_j mj mrk_j clr_j hnext hmj => by
                        pt_steps_nogrp
                        exact hL2 (cl_j, op_j, idx - 1#64, ()) mj (by dsimp only; omega)
                          ⟨mrk_j, clr_j, hnext, hmj⟩)
                  · exfalso
                    have ha64 : s.core.arena_len < 18446744073709551616 := by
                      have := c.harena; unfold dimacsBound at this; omega
                    pt_clear_big
                    simp only [hidx_c0, ← hidx_pred, ← hrsn_v_eq] at hc
                    have h64 : rsn_v.toNat + 3 < 18446744073709551616 := by omega
                    simp only [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt ha64] at hc
                    omega
            · have heq0 : idx = 0#64 := by pt_bound
              exact hJ2e (clen', open_c', 0xFFFFFFFF#32, idx, ()) ml'
                ⟨mrk', clr', ⟨hl2.1, Or.inl rfl⟩, hm'⟩
            · have heq0 : open_c' = 0#64 := by pt_bound
              exact hJ2e (clen', open_c', 0xFFFFFFFF#32, idx, ()) ml'
                ⟨mrk', clr', ⟨hl2.1, Or.inl rfl⟩, hm'⟩
        · exact hJout (clen, open_c, 0xFFFFFFFF#32, ()) ml ⟨mrk, clr, ⟨hl1.1, Or.inl rfl⟩, hml⟩

end HbrDomProof

end LeanQbe.T.Examples.Kissat.Full