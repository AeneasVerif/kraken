module

public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3b1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M6.0` Orchestrator Adapter Proofs — Part 1 (`FullM6OrchAdaptersProof1`)

Proves `full_restore_bump_ana_m6_hdr_wp` (`m6aRestoreBumpAnaSpec`, calling `m6aBumpAnalyzedSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6OrchAdapters

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

/-! ## 1. Pure Helpers (`FullAnaMarksCov` & BitVec Arithmetic) -/

section Helpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem p1_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem p1_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 :=
  fl_bv32_xor1 x

private theorem p1_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  fl_bv32_setWidth64 x

private theorem p1_sext32_64_1 : BitVec.signExtend 64 (1#32 : BitVec 32) = 1#64 := rfl

private theorem p1_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem p1_bv32_0_add (x : BitVec 32) : 0#32 + x = x := by simp

attribute [local bv_c0] p1_bv32_lshr1 p1_bv32_xor1 p1_bv32_setWidth64
  p1_sext32_64_1 p1_bv32_lshr_nat1 p1_bv32_0_add

private theorem p1_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

private theorem p1_bv8_zext32_eq0_iff {x : BitVec 8} :
    BitVec.setWidth 32 x = 0#32 ↔ x = 0#8 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      show (0#32 : BitVec 32).toNat = 0 from rfl] at ht
    exact BitVec.eq_of_toNat_eq ht
  · rintro rfl; rfl

private theorem p1_bv64_ult_iff {a b : BitVec 64} : a.ult b = true ↔ a.toNat < b.toNat := by
  simp [BitVec.ult]

private theorem p1_bv32_ult_iff {a b : BitVec 32} : a.ult b = true ↔ a.toNat < b.toNat := by
  simp [BitVec.ult]

private theorem p1_nodup_of_getElem_ne {α : Type} :
    ∀ (xs : List α),
      (∀ i j (hi : i < xs.length) (hj : j < xs.length), i < j → xs[i] ≠ xs[j]) → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, p1_nodup_of_getElem_ne _ fun i j hi hj hij =>
      h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ hij)⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    exact h 0 (k + 1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hk) (Nat.zero_lt_succ _) hget.symm

private theorem p1_nodup_map_take_append {xs : List (BitVec 32)} {n : Nat} {v : BitVec 32}
    (hn : n < xs.length) (hnd : ((xs.take n).map BitVec.toNat).Nodup)
    (hmiss : ∀ k < n, (xs[k]?.getD 0#32).toNat ≠ v.toNat) :
    (((xs.set n v).take (n + 1)).map BitVec.toNat).Nodup := by
  refine p1_nodup_of_getElem_ne _ fun i j hi hj hij => ?_
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

private theorem p1_nodup_take_pred {xs : List (BitVec 32)} {n : Nat}
    (hpos : 0 < n) (hnd : ((xs.take n).map BitVec.toNat).Nodup) :
    ((xs.take (n - 1)).map BitVec.toNat).Nodup := by
  refine p1_nodup_of_getElem_ne _ fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_take] at hi hj
  have hi_t : i < ((xs.take n).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take]; omega
  have hj_t : j < ((xs.take n).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take]; omega
  have hne := List.pairwise_iff_getElem.mp hnd i j hi_t hj_t hij
  simpa only [List.getElem_map, List.getElem_take] using hne

private abbrev mkBumpState (s : FullState) (mrk : List (BitVec 8)) (mcl : Nat)
    (ws1 : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with mrk := mrk, min_clr_len := mcl }
    scratch := { s.scratch with work_stk1 := ws1 } }

private theorem mkBumpState_lengths {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hmcl : mcl ≤ c.max_vars) :
    (mkBumpState s mrk mcl ws1).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, min_clr_len_le := hmcl },
   { hlen.scratch_ok with work_stk1_len := hws1 }⟩

private theorem bump_zero_marksCov {c : FullCfg} {s : FullState}
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c (mkBumpState s s.core.mrk 0 s.scratch.work_stk1) :=
  ⟨Nat.zero_le _, by simp, fun _ hk => absurd hk (Nat.not_lt_zero _),
    fun v hv hnz => absurd (hmrk0 v hv) hnz⟩

private theorem bump_push_marksCov {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {ov : BitVec 32}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (mkBumpState s mrk mcl ws1))
    (hov_cv : ov.toNat < s.core.cur_vars) (hmcl_cv : mcl < s.core.cur_vars)
    (hmrk0 : mrk[ov.toNat]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c (mkBumpState s (mrk.set ov.toNat 1#8) (mcl + 1) (ws1.set mcl ov)) := by
  obtain ⟨hmcl_cv0, hnd, hfwd, hbak⟩ := hcov
  dsimp only [mkBumpState] at hnd hfwd hbak
  have hmcl_ws : mcl < ws1.length := by rw [hws1]; omega
  refine ⟨hmcl_cv, p1_nodup_map_take_append hmcl_ws hnd (fun k hk heq => ?_),
    fun k hk => ?_, fun v hv hnz => ?_⟩
  · exact (hfwd k hk).2 (by simpa [heq] using hmrk0)
  · dsimp only [mkBumpState] at hk ⊢
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
    · have hk_cov := hfwd k hlt
      have hne : (ws1[k]?.getD 0#32).toNat ≠ ov.toNat := fun heq => by
        rw [heq] at hk_cov; exact hk_cov.2 hmrk0
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne hne.symm]
      exact hk_cov
    · rw [List.getElem?_set_self hmcl_ws, Option.getD_some,
        List.getElem?_set_self (by rw [hmrk]; omega), Option.getD_some]
      exact ⟨hov_cv, by decide⟩
  · dsimp only [mkBumpState] at hnz ⊢
    by_cases hveq : v = ov.toNat
    · refine ⟨mcl, Nat.lt_succ_self _, ?_⟩
      subst hveq
      rw [List.getElem?_set_self hmcl_ws, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hveq)] at hnz
      obtain ⟨i, hi, hieq⟩ := hbak v hv hnz
      refine ⟨i, Nat.lt_succ_of_lt hi, ?_⟩
      rwa [List.getElem?_set_ne (by omega)]

private theorem bump_pop_marksCov {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (mkBumpState s mrk mcl ws1)) (hpos : 0 < mcl) :
    let hmcl_ws : mcl - 1 < ws1.length := by
      have hm1 := hcov.1; dsimp only [mkBumpState] at hm1; rw [hws1]; omega
    let rv := ws1[mcl - 1]'hmcl_ws
    FullAnaMarksCov c (mkBumpState s (mrk.set rv.toNat 0#8) (mcl - 1) ws1) := by
  intro hmcl_ws rv
  obtain ⟨hmcl_cv0, hnd, hfwd, hbak⟩ := hcov
  dsimp only [mkBumpState] at hmcl_cv0 hnd hfwd hbak
  have hrv_lt : rv.toNat < s.core.cur_vars := by
    have := (hfwd (mcl - 1) (by omega)).1
    simpa [rv, List.getElem?_eq_getElem hmcl_ws] using this
  dsimp only [FullAnaMarksCov, mkBumpState]
  refine ⟨by omega, p1_nodup_take_pred hpos hnd, fun k hk => ?_, fun v hv hnz => ?_⟩
  · have hk_cov := hfwd k (by omega)
    have hne : (ws1[k]?.getD 0#32).toNat ≠ rv.toNat := by
      have hk_t : k < ((ws1.take mcl).map BitVec.toNat).length := by
        simp only [List.length_map, List.length_take]; omega
      have hr_t : mcl - 1 < ((ws1.take mcl).map BitVec.toNat).length := by
        simp only [List.length_map, List.length_take]; omega
      have hdiff := List.pairwise_iff_getElem.mp hnd k (mcl - 1) hk_t hr_t (by omega)
      simp only [List.getElem_map, List.getElem_take] at hdiff
      rw [List.getElem?_eq_getElem (by omega : k < ws1.length), Option.getD_some]
      exact hdiff
    rw [List.getElem?_set_ne hne.symm]
    exact hk_cov
  · have hvne : v ≠ rv.toNat := fun hveq => by
      subst hveq
      rw [List.getElem?_set_self (by rw [hmrk]; omega), Option.getD_some] at hnz
      exact hnz rfl
    rw [List.getElem?_set_ne hvne.symm] at hnz
    obtain ⟨i, hi, hieq⟩ := hbak v hv hnz
    rcases Nat.lt_or_eq_of_le (Nat.le_pred_of_lt hi) with hlt | rfl
    · exact ⟨i, hlt, hieq⟩
    · exfalso; apply hvne; rw [← hieq]
      simp [rv, List.getElem?_eq_getElem hmcl_ws]

private theorem bump_perm_marksCov {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {cnt : Nat} {ws1 ws' : List (BitVec 32)}
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hws1 : ws1.length = 2 * c.max_vars) (hws' : ws'.length = 2 * c.max_vars)
    (hcov : FullAnaMarksCov c (mkBumpState s mrk cnt ws1))
    (hperm : (ws'.take cnt).Perm (ws1.take cnt)) :
    FullAnaMarksCov c (mkBumpState s mrk cnt ws') := by
  obtain ⟨hcnt_cv, hnd, hfwd, hbak⟩ := hcov
  dsimp only [mkBumpState] at hcnt_cv hnd hfwd hbak
  have hcnt_ws1 : cnt ≤ ws1.length := by rw [hws1]; omega
  have hcnt_ws' : cnt ≤ ws'.length := by rw [hws']; omega
  refine ⟨hcnt_cv, (hperm.map BitVec.toNat).nodup_iff.mpr hnd, fun k hk => ?_,
    fun v hv hnz => ?_⟩
  · dsimp only [mkBumpState] at hk ⊢
    have hmem : ws'[k]'(by omega) ∈ ws1.take cnt := by
      rw [← hperm.mem_iff]
      have hk_t : k < (ws'.take cnt).length := by rw [List.length_take]; omega
      simpa [List.getElem_take] using List.getElem_mem hk_t
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_take] at hj
    have hj_lt : j < cnt := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
    rw [List.getElem_take] at hjeq
    have hcov_j := hfwd j hj_lt
    rw [List.getElem?_eq_getElem (by omega : k < ws'.length), Option.getD_some, ← hjeq]
    rwa [List.getElem?_eq_getElem (by omega : j < ws1.length), Option.getD_some] at hcov_j
  · dsimp only [mkBumpState] at hnz ⊢
    obtain ⟨j, hj, hjeq⟩ := hbak v hv hnz
    have hmem : ws1[j]'(by omega) ∈ ws'.take cnt := by
      rw [hperm.mem_iff]
      have hj_t : j < (ws1.take cnt).length := by rw [List.length_take]; omega
      simpa [List.getElem_take] using List.getElem_mem hj_t
    obtain ⟨i, hi, hieq⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_take] at hi
    have hi_lt : i < cnt := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    rw [List.getElem_take] at hieq
    refine ⟨i, hi_lt, ?_⟩
    rw [List.getElem?_eq_getElem (by omega : i < ws'.length), Option.getD_some, hieq]
    rwa [List.getElem?_eq_getElem (by omega : j < ws1.length), Option.getD_some] at hjeq

end Helpers

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "c0_hcall " h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev BumpSt := List (BitVec 8) × Nat × List (BitVec 32)

/-! ## 2. `full_restore_bump_ana_m6_hdr` (`m6aRestoreBumpAnaSpec`) -/

theorem full_restore_bump_ana_m6_hdr_wp (Γ : Env)
    (hBumpAna : ∀ a m Q X, m6aBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed_m6_hdr" [i64] [] a m Q X)
    (hClearAna : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    ∀ a m Q X, m6aRestoreBumpAnaSpec a m Q X →
      Func.wp Γ full_restore_bump_ana_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩ := m6aRestoreBumpAnaSpec_elim hs
  have hmaxv := c.hmaxv; unfold LratBytes.dimacsBound at hmaxv
  have hco := hlen.core_ok; have hso := hlen.scratch_ok
  have hcv_le := hco.cur_vars_le
  have hmrk0_len := hco.mrk_len
  have hws10_len := hso.work_stk1_len
  unfold Func.wp full_restore_bump_ana_m6_hdr_body
  rw [fullM6HdrMem_iff] at hm
  c0_hsteps_nogrp
  · exact hQ s.core.mrk s.core.min_clr_len s.scratch ext m hlen hmrk0
      (fun hp => absurd hp (by assumption))
      (fun _ => rfl) ⟨rfl, rfl⟩ rfl hext (fun hi => ⟨hi, rfl⟩)
      ((fullM6HdrMem_iff ..).mpr hm)
  · have hprob0 : s.core.probing = 0#64 := by assumption
    let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext ⋆ R
    have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
    c0_hsteps_nogrp
    refine wp_join_state1 (t := i64) (α := Nat) (proj := BitVec.ofNat 64)
      (Inv := fun ana_n m1 => ana_n ≤ s.core.cur_vars ∧ m1 = m)
      (fun Ja ana_n m1 ⟨hana_le, hm1⟩ => ?_) (fun Ja hJa => ?_)
    · rcases hm1.symm with rfl; rw [Blocks.get_here]; dsimp only
      have hana_bv : (BitVec.ofNat 64 ana_n).toNat = ana_n := bv64_ofNat_toNat (by omega)
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i64, i64]) (α := Nat × Nat × BumpSt)
        (proj := fun st => (BitVec.ofNat 64 st.2.1, BitVec.ofNat 64 st.1, ()))
        (μ := fun st => ana_n - st.1)
        (Inv := fun st mk =>
          st.2.1 ≤ st.1 ∧ st.1 ≤ ana_n ∧
          st.2.2.1.length = c.max_vars ∧ st.2.2.2.2.length = 2 * c.max_vars ∧
          FullAnaMarksCov c (mkBumpState s st.2.2.1 st.2.1 st.2.2.2.2) ∧
          (FullMem c (mkBumpState s st.2.2.1 s.core.min_clr_len st.2.2.2.2) ⋆ R_hdr) mk)
        (fun Jk hJk => ?_)
        (fun Jk (k, w, mrk_k, mcl_k, ws_k) mk
          ⟨hwk, hka, hmrk_k, hws_k, hcov_k, hmk⟩ ihk => ?_)
      · c0_hsteps
        exact hJk (0, 0, s.core.mrk, 0, s.scratch.work_stk1) m
          ⟨Nat.le_refl _, Nat.zero_le _, hmrk0_len, hws10_len,
            bump_zero_marksCov hmrk0, hm⟩
      dsimp only at hwk hka hmrk_k hws_k hcov_k hmk ihk
      rw [Blocks.get_here]; dsimp only
      let sk := mkBumpState s mrk_k s.core.min_clr_len ws_k
      c0_hsteps_nogrp
      · have hk_lt : k < ana_n := by
          have hlt : k % 2 ^ 64 < ana_n % 2 ^ 64 := by
            simpa [BitVec.toNat_ofNat] using (by assumption : _)
          rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : ana_n < 2 ^ 64)] at hlt
        have hk_ws : k < ws_k.length := by rw [hws_k]; omega
        let av := ws_k[(BitVec.ofNat 64 k).toNat]'(by rw [bv64_ofNat_toNat (by omega)]; exact hk_ws)
        have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
          BitVec.eq_of_toNat_eq (by
            rw [show (1 : BitVec 64) = 1#64 from rfl,
              fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
              bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i64]) (α := Nat × BumpSt)
          (proj := fun st => (BitVec.ofNat 64 st.1, ()))
          (Inv := fun st mk' =>
            st.1 ≤ k + 1 ∧ st.2.1.length = c.max_vars ∧ st.2.2.2.length = 2 * c.max_vars ∧
            FullAnaMarksCov c (mkBumpState s st.2.1 st.1 st.2.2.2) ∧
            (FullMem c (mkBumpState s st.2.1 s.core.min_clr_len st.2.2.2) ⋆ R_hdr) mk')
          (fun _ (w', mrk', mcl', ws') mk' ⟨hw', hmrk', hws', hcov', hmk'⟩ => by
            rw [Blocks.get_here]; dsimp only
            c0_hsteps; rw [hk1_bv]
            exact ihk (k + 1, w', mrk', mcl', ws') mk' (by dsimp only; omega)
              ⟨hw', by omega, hmrk', hws', hcov', hmk'⟩)
          (fun Jks hJks => ?_)
        c0_hsteps_nogrp
        · have hav_cv : av.toNat < s.core.cur_vars := by dsimp only [av]; c0_bound
          have hw_cv : w < s.core.cur_vars := by omega
          have hmrk_z : mrk_k[av.toNat]?.getD 0#8 = 0#8 := by
            rw [List.getElem?_eq_getElem (by rw [hmrk_k]; omega), Option.getD_some]
            exact p1_bv8_zext32_eq0_iff.mp (by simpa [av] using (by assumption : _))
          have hcov' := bump_push_marksCov hmrk_k hws_k hcv_le hcov_k hav_cv hw_cv hmrk_z
          have hw1_bv : (BitVec.ofNat 64 w + 1).toNat = w + 1 := by
            rw [show (1 : BitVec 64) = 1#64 from rfl,
              fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
              bv64_ofNat_toNat (by omega)]
          have hav_lt64 : (ws_k[k]'(by omega)).toNat < 2 ^ 64 := by
            have := (ws_k[k]'(by omega)).isLt; omega
          rw [show BitVec.ofNat 64 w + 1 = BitVec.ofNat 64 (w + 1) from
            BitVec.eq_of_toNat_eq (by rw [hw1_bv, bv64_ofNat_toNat (by omega)])]
          exact hJks (w + 1, mrk_k.set av.toNat 1#8, 0, ws_k.set w av) _
            ⟨by omega, by simp [hmrk_k], by simp [hws_k], hcov', by
              simpa [mkBumpState, av, p1_bv32_setWidth64,
                bv64_ofNat_toNat (by omega : w < 2 ^ 64),
                bv64_ofNat_toNat (by omega : k < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : w < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
                Nat.mod_eq_of_lt hav_lt64,
                show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
        · exact hJks (w, mrk_k, 0, ws_k) mk ⟨by omega, hmrk_k, hws_k, hcov_k, hmk⟩
        · exact hJks (w, mrk_k, 0, ws_k) mk ⟨by omega, hmrk_k, hws_k, hcov_k, hmk⟩
      · -- Loop 2 (`if (tlen <= cv)`) + `min_clr_len = w` + `if (w > 0)`
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i64) (α := Nat × BumpSt)
          (proj := fun st => BitVec.ofNat 64 st.1)
          (Inv := fun st m2 =>
            st.1 ≤ s.core.cur_vars ∧ st.2.1.length = c.max_vars ∧ st.2.2.2.length = 2 * c.max_vars ∧
            FullAnaMarksCov c (mkBumpState s st.2.1 st.1 st.2.2.2) ∧
            (FullMem c (mkBumpState s st.2.1 s.core.min_clr_len st.2.2.2) ⋆ R_hdr) m2)
          (fun Jw (wf, mrkf, mclf, wsf) m2 ⟨hwf_le, hmrkf, hwsf, hcovf, hm2⟩ => ?_)
          (fun Jw hJw => ?_)
        · dsimp only at hwf_le hmrkf hwsf hcovf hm2
          rw [Blocks.get_here]; dsimp only
          let s_pre := mkBumpState s mrkf wf wsf
          have hlen_pre : s_pre.LengthsOk c := mkBumpState_lengths hlen hmrkf hwsf (by omega)
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun () m_out => ∃ (mrk_o : List (BitVec 8)) (sc_o : FullScratch)
              (ext_o : List (BitVec 64)),
              let s_o : FullState :=
                { s with core := { s.core with mrk := mrk_o, min_clr_len := 0 }, scratch := sc_o }
              s_o.LengthsOk c ∧ (∀ v < c.max_vars, mrk_o[v]?.getD 0#8 = 0#8) ∧
              FullExtScratchPres s s_o ∧ sc_o.work_stk2 = s.scratch.work_stk2 ∧
              M6HdrExtOk ext_o ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext_o ∧ ext_o = ext) ∧
              (FullM6HdrMem c ext_o s_o ⋆ R) m_out)
            (fun _ () m_out ⟨mrk_o, sc_o, ext_o, hlo, hmo, hpo, hw2o, hext_o, hinit_o, hm_o⟩ => by
              rw [Blocks.get_here]; c0_hsteps
              exact hQ mrk_o 0 sc_o ext_o m_out hlo hmo (fun _ => rfl)
                (fun hp => absurd hprob0 hp) hpo hw2o hext_o hinit_o hm_o)
            (fun Jret hJret => ?_)
          c0_hsteps_nogrp
          · m6h_call hBumpAna
            refine m6aBumpAnalyzedSpec_of hcfg hext hlen_pre hcovf ((fullM6HdrMem_iff ..).mpr (by
                simpa [R_hdr, s_pre, mkBumpState, bv64_ofNat_toNat (by omega : wf < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : wf < 2 ^ 64)] using hm))
              fun mrk_b mcl_b sc_b ext' m_b hlen_b hcov_b hpre_b hws2_b hext_b hinit_b hm_b => ?_
            rw [fullM6HdrMem_iff] at hm_b
            c0_hsteps_nogrp
            c0_hcall hClearAna
            let s_b : FullState :=
              { s_pre with
                core := { s_pre.core with mrk := mrk_b, min_clr_len := mcl_b }
                scratch := sc_b }
            refine ⟨c, s_b, array64 (c.hdr - 2304) ext' ⋆ R, rfl, hlen_b, hm_b,
              fun mrk' m' hmrk' _ _ hclr' hm' => ?_⟩
            have hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8 := hclr' hcov_b
            c0_hsteps
            exact hJret () m' ⟨mrk', sc_b, ext',
              mkBumpState_lengths hlen_b hmrk' hlen_b.scratch_ok.work_stk1_len (Nat.zero_le _),
              hmrk0', hpre_b, hws2_b, hext_b, hinit_b,
              (fullM6HdrMem_iff ..).mpr (by simpa [s_b, s_pre, mkBumpState] using hm')⟩
          · have hwf0 : wf = 0 := by
              have h0 : ¬ (0 : Nat) < wf % 2 ^ 64 := hc
              rw [Nat.mod_eq_of_lt (by omega)] at h0; omega
            subst hwf0
            have hmrk0' : ∀ v < c.max_vars, mrkf[v]?.getD 0#8 = 0#8 := fun v hv => by
              if hnz : mrkf[v]?.getD 0#8 = 0#8 then exact hnz else
                exfalso; obtain ⟨i, hi, _⟩ := hcovf.2.2.2 v hv hnz
                dsimp only [mkBumpState] at hi; omega
            have hm2' : (FullMem c (mkBumpState s mrkf 0 wsf) ⋆ R_hdr) m := by
              simpa [mkBumpState, show (BitVec.ofNat 64 0).toNat = 0 from rfl] using hm
            c0_hsteps
            exact hJret () m ⟨mrkf, (mkBumpState s mrkf 0 wsf).scratch, ext,
              mkBumpState_lengths hlen hmrkf hwsf (Nat.zero_le _), hmrk0', ⟨rfl, rfl⟩, rfl,
              hext, fun hi => ⟨hi, rfl⟩, (fullM6HdrMem_iff ..).mpr hm2'⟩
        · c0_hsteps_nogrp
          · have htl_le : s.core.tmp_len ≤ s.core.cur_vars := by
              have htl64 : s.core.tmp_len < 2 ^ 64 := by have := hco.tmp_len_le; omega
              have hle : ¬ s.core.cur_vars % 2 ^ 64 < s.core.tmp_len % 2 ^ 64 := by omega
              rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt htl64] at hle; omega
            refine wp_while_state (ts := [i64, i64]) (α := Nat × Nat × BumpSt)
              (proj := fun st => (BitVec.ofNat 64 st.2.1, BitVec.ofNat 64 st.1, ()))
              (μ := fun st => s.core.tmp_len - st.1)
              (Inv := fun st mt =>
                st.1 ≤ s.core.tmp_len ∧ st.2.1 ≤ s.core.cur_vars ∧
                st.2.2.1.length = c.max_vars ∧ st.2.2.2.2.length = 2 * c.max_vars ∧
                FullAnaMarksCov c (mkBumpState s st.2.2.1 st.2.1 st.2.2.2.2) ∧
                (FullMem c (mkBumpState s st.2.2.1 s.core.min_clr_len st.2.2.2.2) ⋆ R_hdr) mt)
              (fun Jt hJt => by
                c0_hsteps; exact hJt (0, w, mrk_k, 0, ws_k) mk
                  ⟨Nat.zero_le _, by dsimp only; omega, hmrk_k, hws_k, hcov_k, hmk⟩)
              (fun Jt (ti, wt, mrk_t, mcl_t, ws_t) mt
                ⟨hti_le, hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩ iht => ?_)
            dsimp only at hti_le hwt_le hmrk_t hws_t hcov_t hmt iht
            rw [Blocks.get_here]; dsimp only
            let st := mkBumpState s mrk_t s.core.min_clr_len ws_t
            c0_hsteps_nogrp
            · have hti_lt : ti < s.core.tmp_len := by
                have htl64 : s.core.tmp_len < 2 ^ 64 := by omega
                have hlt : ti % 2 ^ 64 < s.core.tmp_len % 2 ^ 64 := by
                  simpa [BitVec.toNat_ofNat] using (by assumption : _)
                rwa [Nat.mod_eq_of_lt (by omega : ti < 2 ^ 64), Nat.mod_eq_of_lt htl64] at hlt
              have hti_tmp : ti < st.core.tmp.length := by
                rw [show st.core.tmp = s.core.tmp from rfl, hco.tmp_len_arr]; omega
              have hti_tmp_bv : (BitVec.ofNat 64 ti).toNat <
                  (mkBumpState s mrk_t s.core.min_clr_len ws_t).core.tmp.length := by
                rw [bv64_ofNat_toNat (by omega)]; exact hti_tmp
              have hti1_bv : BitVec.ofNat 64 ti + 1 = BitVec.ofNat 64 (ti + 1) :=
                BitVec.eq_of_toNat_eq (by
                  rw [show (1 : BitVec 64) = 1#64 from rfl,
                    fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                    bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
              let tv := (st.core.tmp[(BitVec.ofNat 64 ti).toNat]'hti_tmp_bv) >>> 1#32
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i64]) (α := Nat × BumpSt)
                (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                (Inv := fun st mt' =>
                  st.1 ≤ s.core.cur_vars ∧ st.2.1.length = c.max_vars ∧
                  st.2.2.2.length = 2 * c.max_vars ∧
                  FullAnaMarksCov c (mkBumpState s st.2.1 st.1 st.2.2.2) ∧
                  (FullMem c (mkBumpState s st.2.1 s.core.min_clr_len st.2.2.2) ⋆ R_hdr) mt')
                (fun _ (wt', mrk', mcl', ws') mt' ⟨hwt', hmrk', hws', hcov', hmt'⟩ => by
                  rw [Blocks.get_here]; dsimp only
                  c0_hsteps; rw [hti1_bv]
                  exact iht (ti + 1, wt', mrk', mcl', ws') mt' (by dsimp only; omega)
                    ⟨by omega, hwt', hmrk', hws', hcov', hmt'⟩)
                (fun Jts hJts => ?_)
              c0_hsteps_nogrp
              · have htv_cv : tv.toNat < s.core.cur_vars := by
                  dsimp only [tv, st, mkBumpState]
                  simp only [bv64_ofNat_toNat (by omega : ti < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : ti < 2 ^ 64),
                    Nat.mod_eq_of_lt hcv_lt64] at *
                  c0_bound
                have htv_lvl : (tv.setWidth 64).toNat < st.core.lvl.length := by
                  rw [p1_bv32_setWidth64, show st.core.lvl = s.core.lvl from rfl, hco.lvl_len]
                  omega
                have htv_mrk : (tv.setWidth 64).toNat < mrk_t.length := by
                  rw [p1_bv32_setWidth64, hmrk_t]
                  omega
                c0_hsteps_nogrp
                · have hwt_cv : wt < s.core.cur_vars := by c0_bound
                  have hmrk_z : mrk_t[tv.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem (by rw [hmrk_t]; omega), Option.getD_some]
                    exact p1_bv8_zext32_eq0_iff.mp (by simpa [tv] using (by assumption : _))
                  have hcov' := bump_push_marksCov hmrk_t hws_t hcv_le hcov_t htv_cv hwt_cv hmrk_z
                  have hwt1_bv : (BitVec.ofNat 64 wt + 1).toNat = wt + 1 := by
                    rw [show (1 : BitVec 64) = 1#64 from rfl,
                      fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                      bv64_ofNat_toNat (by omega)]
                  have hwt_ws : (BitVec.ofNat 64 wt).toNat < ws_t.length := by
                    rw [bv64_ofNat_toNat (by omega), hws_t]; omega
                  have htmp_lt64 : (s.core.tmp[ti]'(by rw [hco.tmp_len_arr]; omega)).toNat <
                      2 ^ 64 := by
                    have := (s.core.tmp[ti]'(by rw [hco.tmp_len_arr]; omega)).isLt; omega
                  c0_hsteps
                  rw [show BitVec.ofNat 64 wt + 1 = BitVec.ofNat 64 (wt + 1) from
                    BitVec.eq_of_toNat_eq (by rw [hwt1_bv, bv64_ofNat_toNat (by omega)])]
                  exact hJts (wt + 1, mrk_t.set tv.toNat 1#8, 0, ws_t.set wt tv) _
                    ⟨by omega, by simp [hmrk_t], by simp [hws_t], hcov', by
                      simpa [st, mkBumpState, tv, p1_bv32_setWidth64, p1_bv32_lshr_nat1,
                        bv64_ofNat_toNat (by omega : wt < 2 ^ 64),
                        bv64_ofNat_toNat (by omega : ti < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : wt < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : ti < 2 ^ 64),
                        Nat.mod_eq_of_lt htmp_lt64,
                        show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
                · exact hJts (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
                · exact hJts (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
                · exact hJts (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
              · exact hJts (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
            · exact hJw (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
          · exact hJw (w, mrk_k, 0, ws_k) mk ⟨by omega, hmrk_k, hws_k, hcov_k, hmk⟩
    · c0_hsteps
      · exact hJa s.core.cur_vars m ⟨Nat.le_refl _, rfl⟩
      · have hle : s.scratch.res_sz.toNat ≤ s.core.cur_vars := by
          have hcv64 : s.core.cur_vars < 2 ^ 64 := hcv_lt64
          have hng : ¬ s.core.cur_vars % 2 ^ 64 < s.scratch.res_sz.toNat := by assumption
          rw [Nat.mod_eq_of_lt hcv64] at hng; omega
        have hres_bv : BitVec.ofNat 64 s.scratch.res_sz.toNat = s.scratch.res_sz :=
          BitVec.eq_of_toNat_eq (bv64_ofNat_toNat (by omega))
        simpa [hres_bv] using hJa s.scratch.res_sz.toNat m ⟨hle, rfl⟩

end LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
