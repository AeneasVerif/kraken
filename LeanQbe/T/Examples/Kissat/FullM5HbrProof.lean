module

public import LeanQbe.T.Examples.Kissat.FullM5Hbr
public import LeanQbe.T.Examples.Kissat.FullSpec3
import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas2
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` M5 Budgeted `full_hbr_dom_m5` Proof (`FullM5HbrProof`)

Proves `Func.wp Γ full_hbr_dom_m5_body` against the exact unchanged `Full.fullHbrDomSpec`
(`FullSpec3.lean:452`) for the `steps < 128` marked-level-1 expansion budgeted
`full_hbr_dom_m5` in `FullM5Hbr`, plus closed `m5Hbr_moduleOk` (`M1`-clean `.olean`, zero
`@[expose]`, zero `import all`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5Hbr

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding full_hbr_dom_body full_hbr_dom_wf
open FullProbeTransSpecs hiding fullHbrDomSpec FullMrkZero
open FullProbeTransHelpers

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

theorem full_hbr_dom_m5_wp (Γ : Env) :
    ∀ args m Q X, fullHbrDomSpec args m Q X → Func.wp Γ full_hbr_dom_m5_body args m Q X := by
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
            (fun (clen', _open_c', dom, _idx, _steps, ()) ml' => ∃ mrk' clr',
              hbrOutInv c s F_cur implied.toNat clen'.toNat dom mrk' clr' ∧
              (FullMem c (hbrState s mrk' clr') ⋆ R) ml')
            (fun _ (clen', _open_c', dom, _idx, _steps, ()) ml' hjn => by
              pt_steps_nogrp; exact hJout (clen', _open_c', dom, ()) ml' hjn)
            (fun J2e hJ2e => ?_)
          pt_steps_nogrp
          refine wp_loop_inv
            (fun (clen', open_c', idx, _steps, ()) ml' => ∃ mrk' clr',
              hbrLoop2Inv c s F_cur implied.toNat clen'.toNat open_c'.toNat idx.toNat
                mrk' clr' ∧
              (FullMem c (hbrState s mrk' clr') ⋆ R) ml')
            (fun (_clen', _open_c', idx, _steps, ()) _ => idx.toNat)
            (fun J2 hL2 => ?_)
            (fun J2 (clen', open_c', idx, steps, ()) ml' ⟨mrk', clr', hl2, hm'⟩ hL2 => ?_)
          · pt_steps_nogrp
            have hte_le := hcl.trail_end_le
            have hte32 : s.core.trail_end < 2 ^ 64 := by omega
            refine hL2 (clen, open_c, BitVec.ofNat 64 s.core.trail_end, 0#64, ()) ml
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
              · refine hL2 (clen', open_c', idx - 1#64, steps, ()) ml' (by dsimp only; omega)
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
                refine hL2 (clen', open_c', idx - 1#64, steps, ()) ml' (by dsimp only; omega)
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
                  s.core.trl[(idx - 1#64).toNat]'(by omega), idx - 1#64, steps + 1#64, ()) ml'
                  ⟨mrk', clr', hbrLoop2_root hlen hw hl2' hidx_lt (by
                    rwa [List.getElem?_eq_getElem (l := s.core.trl) (by omega),
                      Option.getD_some]), hm'⟩
              · exact hJ2e (clen', open_c' - 1#64, 0xFFFFFFFF#32, idx - 1#64, steps + 1#64, ()) ml'
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
                    refine hL2
                      (clen' + 1#64, (open_c' - 1#64) + 1#64, idx - 1#64, steps + 1#64, ()) m
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
                    refine hL2 (clen', open_c' - 1#64, idx - 1#64, steps + 1#64, ()) ml'
                      (by dsimp only; omega)
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
                    refine hL2 (clen', open_c' - 1#64, idx - 1#64, steps + 1#64, ()) ml'
                      (by dsimp only; omega)
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
                        exact hL2 (cl_j, op_j, idx - 1#64, steps + 1#64, ()) mj
                          (by dsimp only; omega)
                          ⟨mrk_j, clr_j, hnext, hmj⟩)
                  · exfalso
                    have ha64 : s.core.arena_len < 18446744073709551616 := by
                      have := c.harena; unfold dimacsBound at this; omega
                    pt_clear_big
                    simp only [hidx_c0, ← hidx_pred, ← hrsn_v_eq] at hc
                    have h64 : rsn_v.toNat + 3 < 18446744073709551616 := by omega
                    simp only [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt ha64] at hc
                    omega
            · exact hJ2e (clen', open_c', 0xFFFFFFFF#32, idx, steps, ()) ml'
                ⟨mrk', clr', ⟨hl2.1, Or.inl rfl⟩, hm'⟩
            · exact hJ2e (clen', open_c', 0xFFFFFFFF#32, idx, steps, ()) ml'
                ⟨mrk', clr', ⟨hl2.1, Or.inl rfl⟩, hm'⟩
            · exact hJ2e (clen', open_c', 0xFFFFFFFF#32, idx, steps, ()) ml'
                ⟨mrk', clr', ⟨hl2.1, Or.inl rfl⟩, hm'⟩
        · exact hJout (clen, open_c, 0xFFFFFFFF#32, ()) ml ⟨mrk, clr, ⟨hl1.1, Or.inl rfl⟩, hml⟩


end HbrDomProof

/-! ## 2. Closed Standalone `m5HbrModule` `ModuleOk` -/

/-- Specification table aligned 1-to-1 with `FullM5Hbr.m5Hbr_fns` (`1` row). -/
def m5HbrSpecTable : List SpecEntry :=
  [ ⟨"full_hbr_dom_m5", [i64, i32, i32], [i32], Full.fullHbrDomSpec, true⟩ ]

/-- Specification environment induced by `m5HbrSpecTable`. -/
def m5HbrEnv : Env := Env.ofTable m5HbrSpecTable

theorem m5HbrSpecTable_noExit : ∀ e ∈ m5HbrSpecTable, e.noExit = true := by
  intro e he
  have hall : m5HbrSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m5HbrSpecTable_sigs :
    m5HbrSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m5Hbr_fns.map (fun f => (f.name, f.as, f.rs)) := by
  t_kernel_rfl

theorem m5HbrSpecTable_length : m5HbrSpecTable.length = 1 := by
  t_kernel_rfl

theorem m5Hbr_noExit :
    ∀ f as bs xs m Q X X',
      m5HbrEnv f as bs xs m Q X → m5HbrEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m5HbrSpecTable_noExit

/-- Row-by-row `TableImpl` for `m5Hbr_fns` against `m5HbrSpecTable`. -/
theorem m5Hbr_tableImpl : TableImpl m5HbrEnv m5Hbr_fns m5HbrSpecTable :=
  ⟨.of (full_hbr_dom_m5_wp m5HbrEnv), trivial⟩

/-- Closed `ModuleOk` for standalone `m5HbrModule` under `m5HbrEnv`. -/
theorem m5Hbr_moduleOk : ModuleOk m5HbrEnv m5HbrModule :=
  Env.ofTable_moduleOk m5Hbr_acyclic ⟨full_hbr_dom_m5_wf, trivial⟩ m5Hbr_tableImpl

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`) -/

def nvHbrCfg : FullCfg where
  hdr := 0x1000#64
  avail := 2588
  mv := 3
  max_vars := 3
  bva_cap := 0
  nc := 2
  arena_cap := 6
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 128
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

private def nvHbrScratch : FullScratch where
  heap_len := 0
  scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64
  learned_lits := 0#64; min_removed := 0#64; delayed_len := 0; stable := 0#64
  switched := 0#64; mode_count := 0#64; mode_confl_lim := 0#64; mode_tick_lim := 0#64
  mode_saved_ticks := 0#64; search_ticks := 0#64; q_first := 0#64; q_last := 0#64
  q_search_idx := 0#64; q_search_stamp := 0#64; q_cur_stamp := 0#64
  target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64; rephased := 0#64
  reduce_limit := 0#64; reductions := 0#64; tier1 := 2#64; tier2 := 6#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64
  subst_cnt := 0#64; cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64
  bce_cnt := 0#64; bva_cnt := 0#64; walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 6 0#8
  phases := List.replicate 3 0#8
  phases_target := List.replicate 3 0#8
  phases_best := List.replicate 3 0#8
  walk_best := List.replicate 3 0#8
  heap := List.replicate 3 0#32
  pos := List.replicate 3 0#32
  shrink_stk := List.replicate 3 0#32
  q_prev := List.replicate 3 0#32
  q_next := List.replicate 3 0#32
  q_stamp := List.replicate 3 0#32
  wsort := List.replicate 6 0#32
  work_stk1 := List.replicate 6 0#32
  work_stk2 := List.replicate 6 0#32
  tarjan_mark := List.replicate 6 0#32
  tarjan_reach := List.replicate 6 0#32
  score := List.replicate 3 0#64
  sim_sig := List.replicate 3 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := List.replicate 128 0#32

def nvHbrState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 3, unassigned := 1#64
      arena_len := 6, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 1#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 2, propagated := 2
      cur_level := 1, fuel := 1#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64
      confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := 0#64
      vals := [0xFF#8, 1#8, 0xFF#8, 1#8, 0#8, 0#8]
      lit_mark := List.replicate 6 0#8
      mrk := [0#8, 0#8, 0#8]
      flags := [1#32, 1#32, 1#32]
      lvl := [0#32, 1#32, 0#32]
      rsns := [0xFFFFFFFF#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32]
      trl := [1#32, 3#32, 0#32]
      trail_pos := [0#32, 1#32, 0#32]
      tmp := [0#32, 0#32, 0#32]
      min_clr := [0#32, 0#32, 0#32]
      frame_trail := [0#32, 1#32, 0#32, 0#32]
      frame_dec := [0#32, 3#32, 0#32, 0#32]
      wvec := List.replicate 12 0#32
      repr := List.replicate 6 0#32
      min_stk := List.replicate 8 0#32
      arena := [0x00400000#32, 0#32, 3#32, 0#32, 2#32, 4#32]
      wstk := [0#32] }
  scratch := nvHbrScratch

def nvHbrF0 : CNF Nat := cnfOfClauses [[0], [1]]

private def nvHbrBlockHdr : List UInt8 :=
  bytes64 [3#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvHbrCfg nvHbrState)

private def nvHbrBlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvHbrState.core.vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvHbrState.scratch.walk_vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvHbrState.core.lit_mark ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvHbrState.core.mrk ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvHbrState.scratch.phases ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvHbrState.scratch.phases_target ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvHbrState.scratch.phases_best ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvHbrState.scratch.walk_best ++ List.replicate 5 0)

private def nvHbrBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvHbrState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.core.trail_pos ++ List.replicate 4 0)

private def nvHbrBlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvHbrState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.scratch.shrink_stk ++ List.replicate 4 0)

private def nvHbrBlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvHbrState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvHbrState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvHbrState.core.frame_dec ++ List.replicate 0 0)

private def nvHbrBlockWvec : List UInt8 :=
  bytesOf (t := i32) nvHbrState.core.wvec ++
  bytesOf (t := i32) nvHbrState.core.repr ++
  bytesOf (t := i32) nvHbrState.scratch.wsort ++
  bytesOf (t := i32) nvHbrState.scratch.work_stk1 ++
  bytesOf (t := i32) nvHbrState.scratch.work_stk2 ++
  bytesOf (t := i32) nvHbrState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvHbrState.scratch.tarjan_reach ++
  bytes64 nvHbrState.scratch.score ++
  bytes64 nvHbrState.scratch.sim_sig

private def nvHbrBlockTail : List UInt8 :=
  bytesOf (t := i32) nvHbrState.core.min_stk ++
  bytesOf (t := i32) nvHbrState.scratch.glue_used ++
  bytesOf (t := i32) nvHbrState.scratch.last_learned ++
  bytesOf (t := i32) nvHbrState.core.arena ++
  bytesOf (t := i32) nvHbrState.core.wstk ++
  bytesOf (t := i32) nvHbrState.scratch.delayed ++
  bytesOf (t := i32) nvHbrState.scratch.red_refs ++
  bytesOf (t := i32) nvHbrState.scratch.extend_stk ++
  bytesOf (t := i32) nvHbrState.scratch.scratch_buf ++
  List.replicate 0 0

private def nvHbrBytes : List UInt8 :=
  nvHbrBlockHdr ++ nvHbrBlockBytes ++ nvHbrBlockU32A ++ nvHbrBlockU32B ++
  nvHbrBlockU32C ++ nvHbrBlockWvec ++ nvHbrBlockTail

def nvHbrMem : Mem 64 := nvHbrBytes.At nvHbrCfg.hdr

private theorem nvHbrMem_ok : FullMem nvHbrCfg nvHbrState nvHbrMem := by
  let c := nvHbrCfg; let s := nvHbrState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 2 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 5 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv3 : BitVec.ofNat 64 c.max_vars = 3#64 := rfl
  have hmv6 : BitVec.ofNat 64 (2 * c.max_vars) = 6#64 := rfl
  have hmv12 : BitVec.ofNat 64 (4 * c.max_vars) = 12#64 := rfl
  have hmv16 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 16#64 := rfl
  have hHdr : nvHbrBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvHbrBlockHdr.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [3#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvHbrBlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvHbrBlockBytes.At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 6 2 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 6 2 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 6 2 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 3 5 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 3 5 rfl
      (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 3 5
      rfl (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 3 5 rfl
      (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 3 5 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 6#64) 2 ⋆ region (c.pWalkVals + 6#64) 2 ⋆
      region (c.pLitMark + 6#64) 2 ⋆ region (c.pMark + 3#64) 5
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => nv_zip4 hm
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by
      have hfin := nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv6, hmv3]; simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvHbrBlockU32A.length = 80 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvHbrBlockU32A.At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 12 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 12 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 12 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 12 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 12 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv12]; exact sep_ac hm
  have hU32B : nvHbrBlockU32B.length = 80 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvHbrBlockU32B.At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 12 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 12 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 12 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 12 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 12 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv12]; exact sep_ac hm
  have hU32C : nvHbrBlockU32C.length = 80 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvHbrBlockU32C.At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 12 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 12 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 12 4 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 16 0 rfl
      (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 16 0 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv12, hmv16]; exact sep_ac hm
  have hWvec : nvHbrBlockWvec.length = 240 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvHbrBlockWvec.At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 48 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 24 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 24 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 24 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 24 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 24 rfl
      (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 24 rfl
      (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 24 rfl (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 24 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvHbrBlockTail.length = 892 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvHbrBlockTail.At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 32 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 24 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 512 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := nv_join_pair h12345678 h9 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := nv_join_pair h04 hWvec (by decide) (by decide)
  exact (nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

private theorem nvHbr_lengths : nvHbrState.LengthsOk nvHbrCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvHbr_entails_024 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0, 2, 4]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 ⊢
  obtain ⟨lit, hm, heq⟩ := h0
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

private theorem nvHbr_entails_1 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvHbrF0_unsat : nvHbrF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvHbrF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvHbrF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1 <;> first
    | omega
    | (rcases (by omega : v0 = 0) with rfl; rcases (by omega : v1 = 0) with rfl;
       exact Bool.noConfusion (he0.symm.trans he1))

private theorem nvHbr_witness :
    FullWitnessInv nvHbrCfg nvHbrF0 [[0], [1]] nvHbrState.core := by
  let k := nvHbrState.core
  have hrefs : fullArenaClauseRefsCore k = [0] := by
    unfold fullArenaClauseRefsCore; dsimp only [k]; decide
  have hte : k.trail_end = 2 := rfl
  have hcl : k.cur_level = 1 := rfl
  have hwat : ModeWatchesInv [[0], [1]] k := by
    unfold ModeWatchesInv
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · dsimp only [k, nvHbrState] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · dsimp only [k, nvHbrState] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fullWatchSizeCore, k, nvHbrState] at hp
    · dsimp only [k, nvHbrState] at h1
      rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fullWatchSizeCore, k, nvHbrState] at hp
    · dsimp only [k, nvHbrState] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 3 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inr (by decide),
        fun r hr => by rw [hrefs, List.mem_singleton] at hr; subst hr; exact ⟨by decide, by decide,
          by decide, by decide, Or.inl (by decide)⟩,
        fun r hr hsh => by rw [hrefs, List.mem_singleton] at hr; subst hr; exact absurd rfl hsh,
        fun r hr _ l hl => by
          rw [hrefs, List.mem_singleton] at hr; subst hr
          have hlits : fullArenaClauseLitsCore k 0 = [0, 2, 4] := rfl
          rw [hlits] at hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl | rfl <;> decide,
        fun r hr _ => by
          rw [hrefs, List.mem_singleton] at hr; subst hr
          have hlits : fullArenaClauseLitsCore k 0 = [0, 2, 4] := rfl
          rw [hlits]; exact nvHbr_entails_024⟩
      watches := hwat
      cur_level_le := by decide
      trail_lits_lt := fun i hi => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      trail_vars_nodup := fun i j hi hj hne => by
        rw [hte] at hi hj
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · rfl
        · exfalso; revert hne; decide
        · exfalso; revert hne; decide
        · rfl
      vals_domain := fun l hl => by
        dsimp only [nvHbrState] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
      vals_true_iff := fun l hl => by
        dsimp only [nvHbrState] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> intro h
        · cases h
        · rcases h with ⟨i, hi, heq⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases heq
        · exact ⟨0, by decide, rfl⟩
        · rfl
        · cases h
        · rcases h with ⟨i, hi, heq⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases heq
        · exact ⟨1, by decide, rfl⟩
        · rfl
        · cases h
        · rcases h with ⟨i, hi, heq⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases heq
        · cases h
        · rcases h with ⟨i, hi, heq⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases heq
      vals_false_iff := fun l hl => by
        dsimp only [nvHbrState] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> intro h
        · exact ⟨0, by decide, rfl⟩
        · rfl
        · cases h
        · rcases h with ⟨i, hi, heq⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases heq
        · exact ⟨1, by decide, rfl⟩
        · rfl
        · cases h
        · rcases h with ⟨i, hi, heq⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases heq
        · cases h
        · rcases h with ⟨i, hi, heq⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases heq
        · cases h
        · rcases h with ⟨i, hi, heq⟩; rw [hte] at hi
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases heq
      lvl_le := fun i hi => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      dec_earliest := fun i j hi hj heq _ => by
        rw [hte] at hi hj
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · decide
        · exfalso; revert heq; decide
        · decide
        · decide
      levels_inhabited := fun L hL1 hL2 => by
        rw [hcl] at hL2; obtain rfl : L = 1 := by omega
        exact ⟨1, by decide, rfl⟩
      level0_sound := fun i hi hl0 => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact nvHbr_entails_1
        · cases hl0
      trail_pos_inv := fun i hi => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
      level0_rsn_none := fun i hi _ => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; rcases (by omega : L = 0 ∨ L = 1) with rfl | rfl <;> decide
      frame_trail_mono := fun L1 L2 h12 h2 => by
        rw [hcl] at h2
        rcases (by omega : L1 = 0 ∨ L1 = 1) with rfl | rfl <;>
          rcases (by omega : L2 = 0 ∨ L2 = 1) with rfl | rfl <;>
          first | decide | omega
      frame_trail_before_lt := fun L h1 h2 i hi => by
        rw [hcl] at h2; obtain rfl : L = 1 := by omega
        have hft : (nvHbrState.core.frame_trail[1]?.getD 0#32).toNat = 1 := rfl
        rw [hft] at hi; obtain rfl : i = 0 := (by omega)
        decide
      frame_dec_lt := fun L h1 h2 => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega)
        decide
      reason_inv := fun i hi hne => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> exact absurd rfl hne }

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_hbr_dom_m5_body` under `m5HbrEnv`
(`XPost := False`): preserves `FullMrkZero`, returns `0xFFFFFFFF#32` or a valid dominating literal,
and certifies `nvHbrF0.Unsat`. -/
theorem nv_m5_hbr_dom :
    Func.wp m5HbrEnv full_hbr_dom_m5_body (nvHbrCfg.hdr, 0#32, 4#32, ()) nvHbrMem
      (fun (dom, ()) m' =>
        nvHbrF0.Unsat ∧
        (dom = 0xFFFFFFFF#32 ∨ dom.toNat < 2 * nvHbrState.core.cur_vars) ∧
        ∃ mrk' mclr',
          FullMem nvHbrCfg { nvHbrState with core := { nvHbrState.core with
            mrk := mrk', min_clr := mclr' } } m')
      (fun _ _ _ _ => False) := by
  apply full_hbr_dom_m5_wp m5HbrEnv
  have hmv3 : nvHbrCfg.max_vars = 3 := rfl
  refine ⟨nvHbrCfg, nvHbrF0, [[0], [1]], nvHbrState, emp, rfl, nvHbr_lengths,
    ⟨nvHbrState.core.wvec, nvHbrState.core.wstk, nvHbrState.core.wlen, nvHbr_witness⟩,
    (fun w hw => by
      rw [hmv3] at hw
      rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2) with rfl | rfl | rfl <;> rfl),
    rfl, by decide, by decide, by decide,
    (fun l hl hne => by
      have hlits : fullArenaClauseLits nvHbrState 0 = [0, 2, 4] := rfl
      change l ∈ fullArenaClauseLits nvHbrState 0 at hl
      change l ≠ 4 at hne
      rw [hlits] at hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · rfl
      · rfl
      · exact absurd rfl hne),
    (by rw [sep_emp]; exact nvHbrMem_ok), ?_⟩
  intro dom mrk' mclr' m' s' _ _ hdom hm'
  rw [sep_emp] at hm'
  exact ⟨nvHbrF0_unsat, hdom.imp id And.left, mrk', mclr', hm'⟩

end LeanQbe.T.Examples.Kissat.FullM5Hbr
