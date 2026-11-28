module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Src.Eliminate

import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open FullArenaTactics
open EliminateTactics

private def ws1St (s : FullState) (ws1 : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with work_stk1 := ws1 } }

private def ss1St (s : FullState) (ss1 : List (BitVec 64)) : FullState :=
  { s with scratch := { s.scratch with sim_sig := ss1 } }

private def nbrsSt (s : FullState) (mclr : List (BitVec 32)) (ws2 : List (BitVec 32)) :
    FullState :=
  { s with
    core := { s.core with min_clr := mclr }
    scratch := { s.scratch with work_stk2 := ws2 } }

private theorem ws1St_len (s : FullState) (ws1 : List (BitVec 32)) :
    (ws1St s ws1).scratch.work_stk1.length = ws1.length := rfl

private theorem ws1St_lengthsOk {c : FullCfg} {s : FullState} {ws1 : List (BitVec 32)}
    (hs : s.LengthsOk c) (hws1 : ws1.length = 2 * c.max_vars) :
    (ws1St s ws1).LengthsOk c :=
  { core_ok := hs.core_ok
    scratch_ok := { hs.scratch_ok with work_stk1_len := hws1 } }

private theorem ss1St_lengthsOk {c : FullCfg} {s : FullState} {ss1 : List (BitVec 64)}
    (hs : s.LengthsOk c) (hss1 : ss1.length = c.max_vars) :
    (ss1St s ss1).LengthsOk c :=
  { core_ok := hs.core_ok
    scratch_ok := { hs.scratch_ok with sim_sig_len := hss1 } }

private theorem nbrsSt_lengthsOk {c : FullCfg} {s : FullState}
    {mclr : List (BitVec 32)} {ws2 : List (BitVec 32)}
    (hs : s.LengthsOk c) (hmclr : mclr.length = c.max_vars)
    (hws2 : ws2.length = 2 * c.max_vars) :
    (nbrsSt s mclr ws2).LengthsOk c :=
  { core_ok := { hs.core_ok with min_clr_len_arr := hmclr }
    scratch_ok := { hs.scratch_ok with work_stk2_len := hws2 } }

private theorem mv_lt_bound (c : FullCfg) : c.max_vars < 2 ^ 30 := by
  have h := c.hmaxv
  unfold LeanQbe.T.Examples.Kissat.Ref.dimacsBound at h
  omega

private theorem cv_lt_2p30 {c : FullCfg} {s : FullState} (hs : s.LengthsOk c) :
    s.core.cur_vars < 2 ^ 30 :=
  Nat.lt_of_le_of_lt hs.core_ok.cur_vars_le (mv_lt_bound c)

private theorem bv32_lit0_toNat {v : BitVec 32} (hv : v.toNat < 2 ^ 30) :
    (v <<< 1#32).toNat = 2 * v.toNat := by
  change (v <<< 1).toNat = 2 * v.toNat
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

private theorem bv32_lit1_toNat {v : BitVec 32} (hv : v.toNat < 2 ^ 30) :
    ((v <<< 1#32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hsh : (v <<< 1#32).toNat = 2 * v.toNat := bv32_lit0_toNat hv
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, hsh]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  | succ k =>
    simp only [Nat.testBit_or]
    have hpow : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (Nat.succ_ne_zero k)
    have h1 : Nat.testBit 1 (k + 1) = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hpow]
    rw [h1, Bool.or_false, Nat.testBit, Nat.testBit,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have hdiv : (2 * v.toNat) / 2 ^ (k + 1) = (2 * v.toNat + 1) / 2 ^ (k + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2,
        ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      congr 1
      omega
    rw [hdiv]

private theorem mv_add_zext_lt {c : FullCfg} {s : FullState} (hs : s.LengthsOk c)
    {u : BitVec 32} (hu : u.toNat < s.core.cur_vars) :
    (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 u).toNat < 2 * c.max_vars := by
  have hmv := mv_lt_bound c
  have hcv := hs.core_ok.cur_vars_le
  have hu32 : u.toNat < 2 ^ 32 := u.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

private theorem par_lt {p : BitVec 64} (hp0 : 0 < p.toNat) :
    ((p - 1#64) >>> 1#64).toNat < p.toNat := by
  have h1 : 1#64 ≤ p := by rw [BitVec.le_def]; exact hp0
  change ((p - 1#64) >>> 1).toNat < p.toNat
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le h1, Nat.shiftRight_eq_div_pow]
  omega

private theorem bv64_shl1_add1 {p : BitVec 64} (hp : p.toNat < 2 ^ 30) :
    ((p <<< 1#64) + 1#64).toNat = 2 * p.toNat + 1 := by
  change ((p <<< 1) + 1#64).toNat = 2 * p.toNat + 1
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

public theorem full_bve_var_key_m7_wp (Γ : Env)
    (hDenseOcc : ∀ a m Q X,
      Dense.Spec.fullDenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    (hF64u : ∀ a m Q X,
      Float64.Spec.f64uPure1Spec a m Q X →
      Γ "f64u_to_u64" [i64] [i64] a m Q X) :
    ∀ a m Q X, Spec.fullBveVarKeyM7Spec a m Q X →
      Func.wp Γ Src.Eliminate.full_bve_var_key_m7_body a m Q X := by
  intro ⟨h, v, ⟨⟩⟩ m Q X hPre
  rcases hPre with ⟨c, s0, R, rfl, hs0, hwl0, hm0, hQ⟩
  have hcv_le := hs0.core_ok.cur_vars_le
  unfold Func.wp Src.Eliminate.full_bve_var_key_m7_body
  elim_steps_nogrp
  · exact hQ 0#64
  · have hcv30 : s0.core.cur_vars < 2 ^ 30 := cv_lt_2p30 hs0
    have hv_lt : v.toNat < s0.core.cur_vars := by omega
    have hv_mv : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcv_le
    have hv_ss : (BitVec.setWidth 64 v).toNat < s0.scratch.sim_sig.length := by
      rw [hs0.scratch_ok.sim_sig_len]; simp only [BitVec.toNat_setWidth]; omega
    have hv_sc : (BitVec.setWidth 64 v).toNat < s0.scratch.score.length := by
      rw [hs0.scratch_ok.score_len]; simp only [BitVec.toNat_setWidth]; omega
    have hv_qs : (BitVec.setWidth 64 v).toNat < s0.scratch.q_stamp.length := by
      rw [hs0.scratch_ok.q_stamp_len]; simp only [BitVec.toNat_setWidth]; omega
    have hpos_lt : (v <<< 1#32).toNat < 2 * s0.core.cur_vars := by
      rw [bv32_lit0_toNat (by omega)]; omega
    elim_call hDenseOcc
    · refine ⟨c, s0, R, rfl, hs0, hwl0, hpos_lt, hm0, ?_⟩
      intro p
      elim_steps_nogrp
      have hneg_lt : ((v <<< 1#32) ||| 1#32).toNat < 2 * s0.core.cur_vars := by
        rw [bv32_lit1_toNat (by omega)]; omega
      elim_call hDenseOcc
      · refine ⟨c, s0, R, rfl, hs0, hwl0, hneg_lt, hm0, ?_⟩
        intro n
        apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun _ mj => m = mj)
        · intro _Jp p' mj rfl
          elim_steps_nogrp
          apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun _ mk => m = mk)
          · intro _Jn n' mk rfl
            elim_steps_nogrp
            apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun _ ml => m = ml)
            · intro _Jr rel ml rfl
              elim_steps_nogrp
              apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun _ mn => m = mn)
              · intro _Jr2 rel' mn rfl
                elim_steps_nogrp
                exact hQ _
              · intro Jr2 hJr2
                elim_steps_nogrp
                · exact hJr2 _ m rfl
                · exact hJr2 _ m rfl
            · intro Jr hJr
              elim_steps_nogrp
              · elim_steps_nogrp
                elim_call hF64u
                · intro r
                  apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun _ mn => m = mn)
                  · intro _Jr1 rel' mn rfl
                    elim_steps_nogrp
                    exact hJr rel' m rfl
                  · intro Jr1 hJr1
                    elim_steps_nogrp
                    · exact hJr1 _ m rfl
                    · exact hJr1 _ m rfl
              · elim_steps_nogrp
                exact hJr _ m rfl
          · intro Jn hJn
            elim_steps_nogrp
            · exact hJn _ m rfl
            · exact hJn _ m rfl
        · intro Jp hJp
          elim_steps_nogrp
          · exact hJp _ m rfl
          · exact hJp _ m rfl

public theorem full_bve_heap_up_m7_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullBveHeapUpM7Spec a m Q X →
      Func.wp Γ Src.Eliminate.full_bve_heap_up_m7_body a m Q X := by
  intro ⟨h, hlen, v, ⟨⟩⟩ m Q X hPre
  rcases hPre with ⟨c, s0, R, rfl, hs0, hm0, hQ⟩
  have hcv_le := hs0.core_ok.cur_vars_le
  unfold Func.wp Src.Eliminate.full_bve_heap_up_m7_body
  elim_steps_nogrp
  · exact hQ s0.scratch.work_stk1 m hs0.scratch_ok.work_stk1_len hm0
  · exact hQ s0.scratch.work_stk1 m hs0.scratch_ok.work_stk1_len hm0
  · rename_i hc1
    have hcv30 : s0.core.cur_vars < 2 ^ 30 := cv_lt_2p30 hs0
    have hv_lt : v.toNat < s0.core.cur_vars := by omega
    have hv_mv : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcv_le
    have hlen_le : hlen.toNat ≤ s0.core.cur_vars := by omega
    have hmv_v : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat <
        s0.scratch.work_stk1.length := by
      rw [hs0.scratch_ok.work_stk1_len]; exact mv_add_zext_lt hs0 hv_lt
    have hv_ss : (BitVec.setWidth 64 v).toNat < s0.scratch.sim_sig.length := by
      rw [hs0.scratch_ok.sim_sig_len]; simp only [BitVec.toNat_setWidth]; omega
    elim_steps_nogrp
    · exact hQ s0.scratch.work_stk1 m hs0.scratch_ok.work_stk1_len hm0
    · rename_i hp_lt
      apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun p' mj =>
        ∃ ws1, ws1.length = 2 * c.max_vars ∧ p'.toNat < c.max_vars ∧
          (FullMem c (ws1St s0 ws1) ⋆ R) mj)
      · intro _Jp p' mj ⟨ws1, hws1, hp'lt, hmj⟩
        have hp'_ws1 : p'.toNat < (ws1St s0 ws1).scratch.work_stk1.length := by
          rw [ws1St_len, hws1]; omega
        have hmv_v' : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat <
            ((ws1St s0 ws1).scratch.work_stk1.set p'.toNat v).length := by
          rw [List.length_set, ws1St_len, hws1]; exact mv_add_zext_lt hs0 hv_lt
        elim_steps_nogrp
        refine hQ _ _ ?_ (by simpa [ws1St] using hm)
        rw [List.length_set, List.length_set, hws1]
      · intro Jp hJp
        refine wp_loop_group
          (fun n (p', _) mi =>
            ∃ ws1, ws1.length = 2 * c.max_vars ∧ p'.toNat = n ∧ p'.toNat < hlen.toNat ∧
              (FullMem c (ws1St s0 ws1) ⋆ R) mi)
          ?_ ?_
        · intro J n ⟨p', ⟨⟩⟩ mi ih ⟨ws1, hws1, hn_eq, hp'lt, hmi⟩
          elim_steps_nogrp
          · have hp0' : 0 < p'.toNat := by simpa using hc
            have hpar_lt : ((p' - 1#64) >>> 1#64).toNat < p'.toNat := par_lt hp0'
            have hpar_ws1 : ((p' - 1#64) >>> 1#64).toNat <
                (ws1St s0 ws1).scratch.work_stk1.length := by
              rw [ws1St_len, hws1]; omega
            elim_steps_nogrp
            · exact hJp p' mi ⟨ws1, hws1, by omega, hmi⟩
            · dsimp only [ws1St] at hc
              have hpv_lt : ws1[((p' - 1#64) >>> 1#64).toNat].toNat < s0.core.cur_vars := by
                change ¬s0.core.cur_vars % 2 ^ 64 ≤
                  ws1[((p' - 1#64) >>> 1#64).toNat].toNat at hc
                omega
              have hpv_ss : (BitVec.setWidth 64
                  ws1[((p' - 1#64) >>> 1#64).toNat]).toNat <
                  (ws1St s0 ws1).scratch.sim_sig.length := by
                simp only [ws1St, hs0.scratch_ok.sim_sig_len, BitVec.toNat_setWidth]
                have := (ws1[((p' - 1#64) >>> 1#64).toNat]).isLt
                omega
              elim_steps_nogrp
              · exact hJp p' mi ⟨ws1, hws1, by omega, hmi⟩
              · have hp'_ws1 : p'.toNat < (ws1St s0 ws1).scratch.work_stk1.length := by
                  rw [ws1St_len, hws1]; omega
                have hmv_pv : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64
                    ws1[((p' - 1#64) >>> 1#64).toNat]).toNat <
                    ((ws1St s0 ws1).scratch.work_stk1.set p'.toNat
                      ws1[((p' - 1#64) >>> 1#64).toNat]).length := by
                  rw [List.length_set, ws1St_len, hws1]; exact mv_add_zext_lt hs0 hpv_lt
                elim_steps_nogrp
                refine ih ((p' - 1#64) >>> 1#64).toNat ((p' - 1#64) >>> 1#64, ()) _
                  (by omega) ⟨_, ?_, rfl, by omega, by simpa [ws1St] using hm⟩
                rw [List.length_set, List.length_set, hws1]
          · exact hJp p' mi ⟨ws1, hws1, by omega, hmi⟩
        · intro J hJ
          elim_steps_nogrp
          refine hJ _ _ _ ⟨s0.scratch.work_stk1, hs0.scratch_ok.work_stk1_len, rfl, ?_, hm0⟩
          have hmv_eq : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat =
              (c.max_vars + v.toNat) % 2 ^ 64 := by
            simp [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
          simp only [hmv_eq, BitVec.toNat_setWidth]
          omega

public theorem full_bve_heap_down_m7_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullBveHeapDownM7Spec a m Q X →
      Func.wp Γ Src.Eliminate.full_bve_heap_down_m7_body a m Q X := by
  intro ⟨h, hlen, v, ⟨⟩⟩ m Q X hPre
  rcases hPre with ⟨c, s0, R, rfl, hs0, hm0, hQ⟩
  have hcv_le := hs0.core_ok.cur_vars_le
  unfold Func.wp Src.Eliminate.full_bve_heap_down_m7_body
  elim_steps_nogrp
  · exact hQ s0.scratch.work_stk1 m hs0.scratch_ok.work_stk1_len hm0
  · exact hQ s0.scratch.work_stk1 m hs0.scratch_ok.work_stk1_len hm0
  · rename_i hc1
    have hcv30 : s0.core.cur_vars < 2 ^ 30 := cv_lt_2p30 hs0
    have hv_lt : v.toNat < s0.core.cur_vars := by omega
    have hv_mv : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcv_le
    have hlen_le : hlen.toNat ≤ s0.core.cur_vars := by omega
    have hmv_v : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat <
        s0.scratch.work_stk1.length := by
      rw [hs0.scratch_ok.work_stk1_len]; exact mv_add_zext_lt hs0 hv_lt
    have hv_ss : (BitVec.setWidth 64 v).toNat < s0.scratch.sim_sig.length := by
      rw [hs0.scratch_ok.sim_sig_len]; simp only [BitVec.toNat_setWidth]; omega
    elim_steps_nogrp
    · exact hQ s0.scratch.work_stk1 m hs0.scratch_ok.work_stk1_len hm0
    · rename_i hp_lt
      apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun p' mj =>
        ∃ ws1, ws1.length = 2 * c.max_vars ∧ p'.toNat < c.max_vars ∧
          (FullMem c (ws1St s0 ws1) ⋆ R) mj)
      · intro _Jp p' mj ⟨ws1, hws1, hp'lt, hmj⟩
        have hp'_ws1 : p'.toNat < (ws1St s0 ws1).scratch.work_stk1.length := by
          rw [ws1St_len, hws1]; omega
        have hmv_v' : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat <
            ((ws1St s0 ws1).scratch.work_stk1.set p'.toNat v).length := by
          rw [List.length_set, ws1St_len, hws1]; exact mv_add_zext_lt hs0 hv_lt
        elim_steps_nogrp
        refine hQ _ _ ?_ (by simpa [ws1St] using hm)
        rw [List.length_set, List.length_set, hws1]
      · intro Jp hJp
        refine wp_loop_group
          (fun n (p', _) mi =>
            ∃ ws1, ws1.length = 2 * c.max_vars ∧ hlen.toNat - p'.toNat = n ∧
              p'.toNat < hlen.toNat ∧ (FullMem c (ws1St s0 ws1) ⋆ R) mi)
          ?_ ?_
        · intro J n ⟨p', ⟨⟩⟩ mi ih ⟨ws1, hws1, hn_eq, hp'lt, hmi⟩
          elim_steps_nogrp
          · exact hJp p' mi ⟨ws1, hws1, by omega, hmi⟩
          · have hl_eq : ((p' <<< 1#64) + 1#64).toNat = 2 * p'.toNat + 1 :=
              bv64_shl1_add1 (by omega)
            have hl_ws1 : ((p' <<< 1#64) + 1#64).toNat <
                (ws1St s0 ws1).scratch.work_stk1.length := by
              rw [ws1St_len, hws1]; omega
            elim_steps_nogrp
            · exact hJp p' mi ⟨ws1, hws1, by omega, hmi⟩
            · dsimp only [ws1St] at hc
              have h1_64 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
              have hbv_idx : (2 * p'.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                  ((p' <<< 1#64) + 1#64).toNat := by
                rw [h1_64, hl_eq]; omega
              have hbv_lt : ws1[((p' <<< 1#64) + 1#64).toNat].toNat < s0.core.cur_vars := by
                simp only [hbv_idx] at hc
                omega
              have hbv_ss : (BitVec.setWidth 64
                  ws1[((p' <<< 1#64) + 1#64).toNat]).toNat <
                  (ws1St s0 ws1).scratch.sim_sig.length := by
                simp only [ws1St, hs0.scratch_ok.sim_sig_len, BitVec.toNat_setWidth]
                omega
              elim_steps_nogrp
              apply wp_join_state
                (fun x : BitVec 32 × BitVec 64 × BitVec 64 => (x.1, x.2.1, x.2.2, ()))
                (fun x mj => mi = mj ∧ x.1.toNat < s0.core.cur_vars ∧
                  p'.toNat < x.2.2.toNat ∧ x.2.2.toNat < hlen.toNat)
              · intro _J50 x mj ⟨rfl, hbv'lt, hlt1, hlt2⟩
                elim_steps_nogrp
                · exact hJp p' mi ⟨ws1, hws1, by omega, hmi⟩
                · have hp'_ws1 : p'.toNat < (ws1St s0 ws1).scratch.work_stk1.length := by
                    rw [ws1St_len, hws1]; omega
                  have hmv_bv' : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 x.1).toNat <
                      ((ws1St s0 ws1).scratch.work_stk1.set p'.toNat x.1).length := by
                    rw [List.length_set, ws1St_len, hws1]; exact mv_add_zext_lt hs0 hbv'lt
                  elim_steps_nogrp
                  refine ih (hlen.toNat - x.2.2.toNat) (x.2.2, ()) _ (by omega)
                    ⟨_, ?_, rfl, hlt2, by simpa [ws1St] using hm⟩
                  rw [List.length_set, List.length_set, hws1]
              · intro J50 hJ50
                elim_steps_nogrp
                · have hr_eq : (((p' <<< 1#64) + 1#64) + 1#64).toNat =
                      ((p' <<< 1#64) + 1#64).toNat + 1 := by
                    have : ((p' <<< 1#64) + 1#64).toNat < 2 ^ 31 := by omega
                    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                    omega
                  have hr_ws1 : (((p' <<< 1#64) + 1#64) + 1#64).toNat <
                      (ws1St s0 ws1).scratch.work_stk1.length := by
                    rw [ws1St_len, hws1]; omega
                  elim_steps_nogrp
                  apply wp_join_state
                    (fun x : BitVec 32 × BitVec 64 × BitVec 64 => (x.1, x.2.1, x.2.2, ()))
                    (fun x mj => mi = mj ∧ x.1.toNat < s0.core.cur_vars ∧
                      p'.toNat < x.2.2.toNat ∧ x.2.2.toNat < hlen.toNat)
                  · intro _J64 x mj hinv
                    elim_steps_nogrp
                    exact hJ50 x mj hinv
                  · intro J64 hJ64
                    elim_steps_nogrp
                    · dsimp only [ws1St] at hc
                      have hrv_idx :
                          (2 * p'.toNat + BitVec.toNat (1 : BitVec 64) +
                            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                            (((p' <<< 1#64) + 1#64) + 1#64).toNat := by
                        rw [h1_64, hr_eq, hl_eq]; omega
                      have hrv_lt : ws1[(((p' <<< 1#64) + 1#64) + 1#64).toNat].toNat <
                          s0.core.cur_vars := by
                        simp only [hrv_idx] at hc
                        omega
                      have hrv_ss : (BitVec.setWidth 64
                          ws1[(((p' <<< 1#64) + 1#64) + 1#64).toNat]).toNat <
                          (ws1St s0 ws1).scratch.sim_sig.length := by
                        simp only [ws1St, hs0.scratch_ok.sim_sig_len, BitVec.toNat_setWidth]
                        omega
                      elim_steps_nogrp
                      · exact hJ64 (_, _, _) mi ⟨rfl, hrv_lt,
                          by change p'.toNat < (((p' <<< 1#64) + 1#64) + 1#64).toNat; omega,
                          by change (((p' <<< 1#64) + 1#64) + 1#64).toNat < hlen.toNat; omega⟩
                      · exact hJ64 (_, _, _) mi ⟨rfl, hbv_lt,
                          by change p'.toNat < ((p' <<< 1#64) + 1#64).toNat; omega,
                          by change ((p' <<< 1#64) + 1#64).toNat < hlen.toNat; omega⟩
                    · exact hJ64 (_, _, _) mi ⟨rfl, hbv_lt,
                        by change p'.toNat < ((p' <<< 1#64) + 1#64).toNat; omega,
                        by change ((p' <<< 1#64) + 1#64).toNat < hlen.toNat; omega⟩
                · exact hJ50 (_, _, _) mi ⟨rfl, hbv_lt,
                    by change p'.toNat < ((p' <<< 1#64) + 1#64).toNat; omega,
                    by change ((p' <<< 1#64) + 1#64).toNat < hlen.toNat; omega⟩
          · exact hJp p' mi ⟨ws1, hws1, by omega, hmi⟩
        · intro J hJ
          elim_steps_nogrp
          refine hJ _ _ _ ⟨s0.scratch.work_stk1, hs0.scratch_ok.work_stk1_len, rfl, ?_, hm0⟩
          have hmv_eq : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat =
              (c.max_vars + v.toNat) % 2 ^ 64 := by
            simp [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
          simp only [hmv_eq, BitVec.toNat_setWidth]
          omega

public theorem full_bve_heap_push_m7_wp (Γ : Env)
    (hVarKey : ∀ a m Q X,
      Spec.fullBveVarKeyM7Spec a m Q X →
      Γ "full_bve_var_key_m7" [i64, i32] [i64] a m Q X)
    (hHeapUp : ∀ a m Q X,
      Spec.fullBveHeapUpM7Spec a m Q X →
      Γ "full_bve_heap_up_m7" [i64, i64, i32] [] a m Q X)
    (hHeapDown : ∀ a m Q X,
      Spec.fullBveHeapDownM7Spec a m Q X →
      Γ "full_bve_heap_down_m7" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, Spec.fullBveHeapPushM7Spec a m Q X →
      Func.wp Γ Src.Eliminate.full_bve_heap_push_m7_body a m Q X := by
  intro ⟨h, hlen, v, ⟨⟩⟩ m Q X hPre
  rcases hPre with ⟨c, s0, R, rfl, hs0, hwl0, hm0, hQ⟩
  have hcv_le := hs0.core_ok.cur_vars_le
  unfold Func.wp Src.Eliminate.full_bve_heap_push_m7_body
  elim_steps_nogrp
  · exact hQ hlen s0.scratch.work_stk1 s0.scratch.sim_sig m
      hs0.scratch_ok.work_stk1_len hs0.scratch_ok.sim_sig_len id hm0
  · exact hQ hlen s0.scratch.work_stk1 s0.scratch.sim_sig m
      hs0.scratch_ok.work_stk1_len hs0.scratch_ok.sim_sig_len id hm0
  · rename_i hc1
    have hcv30 : s0.core.cur_vars < 2 ^ 30 := cv_lt_2p30 hs0
    have hv_lt : v.toNat < s0.core.cur_vars := by omega
    have hv_mv : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcv_le
    have hlen_le : hlen.toNat ≤ s0.core.cur_vars := by omega
    have hmv_v : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat <
        s0.scratch.work_stk1.length := by
      rw [hs0.scratch_ok.work_stk1_len]; exact mv_add_zext_lt hs0 hv_lt
    have hv_ss : (BitVec.setWidth 64 v).toNat < s0.scratch.sim_sig.length := by
      rw [hs0.scratch_ok.sim_sig_len]; simp only [BitVec.toNat_setWidth]; omega
    elim_call hVarKey
    · refine ⟨c, s0, R, rfl, hs0, hwl0, hm0, ?_⟩
      intro nk
      elim_steps_nogrp
      · let ss1 := s0.scratch.sim_sig.set (BitVec.setWidth 64 v).toNat nk
        let s1 := ss1St s0 ss1
        have hss1 : ss1.length = c.max_vars := by simp [ss1, hs0.scratch_ok.sim_sig_len]
        have hs1 : s1.LengthsOk c := ss1St_lengthsOk hs0 hss1
        apply wp_join0 (fun mj =>
          ∃ ws1', ws1'.length = 2 * c.max_vars ∧ (FullMem c (ws1St s1 ws1') ⋆ R) mj)
        · intro _J29 mj ⟨ws1', hws1', hmj⟩
          elim_steps_nogrp
          exact hQ hlen ws1' ss1 mj hws1' hss1 (fun _ => hlen_le)
            (by simpa [ws1St, s1, ss1St] using hmj)
        · intro J29 hJ29
          elim_steps_nogrp
          · elim_call hHeapUp
            · refine ⟨c, s1, R, rfl, hs1,
                by simpa [s1, ss1St, ss1, BitVec.toNat_setWidth] using hm, ?_⟩
              intro ws1' m' hws1' hm'
              elim_steps_nogrp
              exact hJ29 m' ⟨ws1', hws1', by simpa [ws1St] using hm'⟩
          · apply wp_join0 (fun mj =>
              ∃ ws1', ws1'.length = 2 * c.max_vars ∧ (FullMem c (ws1St s1 ws1') ⋆ R) mj)
            · intro _J32 mj ⟨ws1', hws1', hmj⟩
              elim_steps_nogrp
              exact hJ29 mj ⟨ws1', hws1', hmj⟩
            · intro J32 hJ32
              elim_steps_nogrp
              · elim_call hHeapDown
                · refine ⟨c, s1, R, rfl, hs1,
                    by simpa [s1, ss1St, ss1, BitVec.toNat_setWidth] using hm, ?_⟩
                  intro ws1' m' hws1' hm'
                  elim_steps_nogrp
                  exact hJ32 m' ⟨ws1', hws1', by simpa [ws1St] using hm'⟩
              · exact hJ32 _ ⟨s0.scratch.work_stk1, hs0.scratch_ok.work_stk1_len,
                  by simpa [ws1St, s1, ss1St, ss1, BitVec.toNat_setWidth] using hm⟩
      · let ss1 := s0.scratch.sim_sig.set (BitVec.setWidth 64 v).toNat nk
        let s1 := ss1St s0 ss1
        have hss1 : ss1.length = c.max_vars := by simp [ss1, hs0.scratch_ok.sim_sig_len]
        exact hQ hlen s1.scratch.work_stk1 ss1 _ hs0.scratch_ok.work_stk1_len hss1
          (fun _ => hlen_le) (by simpa [s1, ss1St, ss1, BitVec.toNat_setWidth] using hm)
      · let ss1 := s0.scratch.sim_sig.set (BitVec.setWidth 64 v).toNat nk
        let s1 := ss1St s0 ss1
        have hss1 : ss1.length = c.max_vars := by simp [ss1, hs0.scratch_ok.sim_sig_len]
        have hs1 : s1.LengthsOk c := ss1St_lengthsOk hs0 hss1
        have hlen_lt : hlen.toNat < s0.core.cur_vars := by omega
        have hlen_ws0 : hlen.toNat < s0.scratch.work_stk1.length := by
          rw [hs0.scratch_ok.work_stk1_len]; omega
        have hmv_v_set : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat <
            (s0.scratch.work_stk1.set hlen.toNat v).length := by
          rw [List.length_set]; exact hmv_v
        have hnlen_le : (hlen + 1#64).toNat ≤ s0.core.cur_vars := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        elim_steps_nogrp
        let ws1_2 := (s0.scratch.work_stk1.set hlen.toNat v).set
          (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 v).toNat (hlen.setWidth 32)
        have hws1_2 : ws1_2.length = 2 * c.max_vars := by
          simp [ws1_2, hs0.scratch_ok.work_stk1_len]
        let s2 := ws1St s1 ws1_2
        have hs2 : s2.LengthsOk c := ws1St_lengthsOk hs1 hws1_2
        elim_call hHeapUp
        · refine ⟨c, s2, R, rfl, hs2, ?_, ?_⟩
          · dsimp only [s2, s1, ws1St, ss1St, ws1_2, ss1]
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth] at hm ⊢
            exact hm
          · intro ws1' m' hws1' hm'
            elim_steps_nogrp
            exact hQ (hlen + 1#64) ws1' ss1 m' hws1' hss1 (fun _ => hnlen_le)
              (by simpa [s2, ws1St, s1, ss1St] using hm')

public theorem full_bve_heap_pop_m7_wp (Γ : Env)
    (hHeapDown : ∀ a m Q X,
      Spec.fullBveHeapDownM7Spec a m Q X →
      Γ "full_bve_heap_down_m7" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, Spec.fullBveHeapPopM7Spec a m Q X →
      Func.wp Γ Src.Eliminate.full_bve_heap_pop_m7_body a m Q X := by
  intro ⟨h, hlen, ⟨⟩⟩ m Q X hPre
  rcases hPre with ⟨c, s0, R, rfl, hs0, hm0, hQ⟩
  have hcv_le := hs0.core_ok.cur_vars_le
  unfold Func.wp Src.Eliminate.full_bve_heap_pop_m7_body
  elim_steps_nogrp
  · exact hQ 0xFFFFFFFF#32 s0.scratch.work_stk1 m hs0.scratch_ok.work_stk1_len hm0
  · exact hQ 0xFFFFFFFF#32 s0.scratch.work_stk1 m hs0.scratch_ok.work_stk1_len hm0
  · rename_i hne0
    have hcv30 : s0.core.cur_vars < 2 ^ 30 := cv_lt_2p30 hs0
    have hlen_pos : 0 < hlen.toNat :=
      Nat.pos_of_ne_zero fun h0 => hne0 (BitVec.eq_of_toNat_eq h0)
    have hlen_le : hlen.toNat ≤ s0.core.cur_vars := by omega
    have h0_lt : (BitVec.ofNat 64 0).toNat < s0.scratch.work_stk1.length := by
      rw [hs0.scratch_ok.work_stk1_len]
      simp only [BitVec.toNat_ofNat]
      omega
    elim_steps_nogrp
    apply wp_join0 (fun mj =>
      ∃ ws1, ws1.length = 2 * c.max_vars ∧ (FullMem c (ws1St s0 ws1) ⋆ R) mj)
    · intro _J14 mj ⟨ws1, hws1, hmj⟩
      elim_steps_nogrp
      have hnlen_lt : (hlen - 1#64).toNat < c.max_vars := by
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      have hnlen_ws1 : (hlen - 1#64).toNat < (ws1St s0 ws1).scratch.work_stk1.length := by
        rw [ws1St_len, hws1]; omega
      have h0_ws1 : (BitVec.ofNat 64 0).toNat < (ws1St s0 ws1).scratch.work_stk1.length := by
        rw [ws1St_len, hws1]; simp only [BitVec.toNat_ofNat]; omega
      apply wp_join0 (fun mk =>
        ∃ ws1', ws1'.length = 2 * c.max_vars ∧ (FullMem c (ws1St s0 ws1') ⋆ R) mk)
      · intro _J17 mk ⟨ws1', hws1', hmk⟩
        apply wp_join_state (fun x : BitVec 32 => (x, ())) (fun _ ml => mk = ml)
        · intro _J19 r ml rfl
          elim_steps_nogrp
          exact hQ r ws1' mk hws1' (by simpa [ws1St] using hmk)
        · intro J19 hJ19
          elim_steps_nogrp
          · exact hJ19 _ mk rfl
          · exact hJ19 _ mk rfl
      · intro J17 hJ17
        elim_steps_nogrp
        · apply wp_join0 (fun mk =>
            ∃ ws1', ws1'.length = 2 * c.max_vars ∧ (FullMem c (ws1St s0 ws1') ⋆ R) mk)
          · intro _J30 mk ⟨ws1', hws1', hmk⟩
            elim_steps_nogrp
            exact hJ17 mk ⟨ws1', hws1', hmk⟩
          · intro J30 hJ30
            elim_steps_nogrp
            · dsimp only [ws1St] at hc
              have hlast_idx :
                  (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + hlen.toNat) % 2 ^ 64 =
                    (hlen - 1#64).toNat := by
                have h1_64 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                rw [h1_64, BitVec.toNat_sub, BitVec.toNat_ofNat]
              have hlast_lt : ws1[(hlen - 1#64).toNat].toNat < s0.core.cur_vars := by
                simp only [hlast_idx] at hc
                omega
              have hmv_last : (BitVec.ofNat 64 c.max_vars +
                  BitVec.setWidth 64 ws1[(hlen - 1#64).toNat]).toNat <
                  (ws1.set (BitVec.ofNat 64 0).toNat ws1[(hlen - 1#64).toNat]).length := by
                rw [List.length_set, hws1]; exact mv_add_zext_lt hs0 hlast_lt
              elim_steps_nogrp
              let ws1' := (ws1.set (BitVec.ofNat 64 0).toNat ws1[(hlen - 1#64).toNat]).set
                (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 ws1[(hlen - 1#64).toNat]).toNat
                0#32
              have hws1' : ws1'.length = 2 * c.max_vars := by
                simp [ws1', hws1]
              let s1 := ws1St s0 ws1'
              have hs1 : s1.LengthsOk c := ws1St_lengthsOk hs0 hws1'
              elim_call hHeapDown
              · refine ⟨c, s1, R, rfl, hs1, by simpa [s1, ws1St, ws1'] using hm, ?_⟩
                intro ws1'' m' hws1'' hm'
                elim_steps_nogrp
                exact hJ30 m' ⟨ws1'', hws1'', by simpa [s1, ws1St] using hm'⟩
            · refine hJ30 _ ⟨_, ?_, by simpa [ws1St] using hm⟩
              rw [List.length_set, hws1]
        · exact hJ17 mj ⟨ws1, hws1, hmj⟩
    · intro J14 hJ14
      elim_steps_nogrp
      · have h0eq : (BitVec.ofNat 64 0).toNat = OfNat.ofNat 0 % 2 ^ 64 := rfl
        have htop_lt : s0.scratch.work_stk1[(BitVec.ofNat 64 0).toNat].toNat <
            s0.core.cur_vars := by
          simp only [h0eq]
          omega
        have hmv_top : (BitVec.ofNat 64 c.max_vars +
            BitVec.setWidth 64 s0.scratch.work_stk1[(BitVec.ofNat 64 0).toNat]).toNat <
            s0.scratch.work_stk1.length := by
          rw [hs0.scratch_ok.work_stk1_len]; exact mv_add_zext_lt hs0 htop_lt
        elim_steps_nogrp
        refine hJ14 _ ⟨_, ?_, by simpa [ws1St] using hm⟩
        rw [List.length_set, hs0.scratch_ok.work_stk1_len]
      · exact hJ14 _ ⟨s0.scratch.work_stk1, hs0.scratch_ok.work_stk1_len, hm0⟩

private theorem list_getElem_of_eq {α : Type} {xs : List α} {i j : Nat} {v : α}
    (hij : i = j) (hget : xs[j]? = some v) (hi : i < xs.length) :
    xs[i]'hi = v := by
  have hg := List.getElem?_eq_getElem hi
  have hij_get : xs[i]? = some v := by rw [hij]; exact hget
  rw [hij_get] at hg; exact Option.some.inj hg.symm

private theorem nbrs_u_lt {s0 : FullState} (hcv30 : s0.core.cur_vars < 2 ^ 30)
    (w : BitVec 32) (h : (w >>> (1 : BitVec 32)).toNat < s0.core.cur_vars % 2 ^ 64) :
    (w >>> 1#32).toNat < s0.core.cur_vars := by
  change (w >>> (1 : BitVec 32)).toNat < s0.core.cur_vars % 2 ^ 64 at h
  change (w >>> (1 : BitVec 32)).toNat < s0.core.cur_vars
  omega

private theorem nbrs_u_fl {c : FullCfg} {s0 : FullState} (hs0 : s0.LengthsOk c)
    {u : BitVec 32} (hu : u.toNat < s0.core.cur_vars) (hcv30 : s0.core.cur_vars < 2 ^ 30) :
    (BitVec.setWidth 64 u).toNat < s0.core.flags.length := by
  rw [hs0.core_ok.flags_len, BitVec.toNat_setWidth]; have := hs0.core_ok.cur_vars_le; omega

private theorem nbrs_u_vals {c : FullCfg} {s0 : FullState} (hs0 : s0.LengthsOk c)
    {u : BitVec 32} (hu : u.toNat < s0.core.cur_vars) (hcv30 : s0.core.cur_vars < 2 ^ 30) :
    (BitVec.setWidth 64 u <<< 1#64).toNat < s0.core.vals.length := by
  change (BitVec.setWidth 64 u <<< 1).toNat < s0.core.vals.length
  rw [hs0.core_ok.vals_len, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  have := hs0.core_ok.cur_vars_le; omega

private theorem nbrs_u_mc {c : FullCfg} {mclr : List (BitVec 32)}
    (hmclr : mclr.length = c.max_vars) {s0 : FullState} (hs0 : s0.LengthsOk c)
    {u : BitVec 32} (hu : u.toNat < s0.core.cur_vars) (hcv30 : s0.core.cur_vars < 2 ^ 30) :
    (BitVec.setWidth 64 u).toNat < mclr.length := by
  rw [hmclr, BitVec.toNat_setWidth]; have := hs0.core_ok.cur_vars_le; omega

private theorem nbrs_ws2_set_b {c : FullCfg} {s0 : FullState} {ws2 : List (BitVec 32)}
    (hws2 : ws2.length = 2 * c.max_vars) (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    {nn : BitVec 64} (hnn : nn.toNat < s0.core.cur_vars)
    (hws2_b : ∀ i < nn.toNat, (ws2[i]?.getD 0#32).toNat < s0.core.cur_vars)
    {u : BitVec 32} (hu : u.toNat < s0.core.cur_vars) :
    ∀ i < (nn + 1#64).toNat, ((ws2.set nn.toNat u)[i]?.getD 0#32).toNat < s0.core.cur_vars := by
  have hnn1 : (nn + 1#64).toNat = nn.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := mv_lt_bound c; omega
  intro i hi
  by_cases hieq : i = nn.toNat
  · subst hieq
    rw [List.getElem?_set_self (by rw [hws2]; omega), Option.getD_some]; exact hu
  · rw [List.getElem?_set_ne (Ne.symm hieq)]; exact hws2_b i (by omega)

private theorem nbrs_wvec0_lt {c : FullCfg} {s0 : FullState} (hs0 : s0.LengthsOk c)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * s0.core.cur_vars)
    (hcv30 : s0.core.cur_vars < 2 ^ 30) :
    (lit.setWidth 64 <<< 1#64).toNat < s0.core.wvec.length := by
  change (lit.setWidth 64 <<< 1).toNat < s0.core.wvec.length
  rw [hs0.core_ok.wvec_len, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  have := hs0.core_ok.cur_vars_le; have := mv_lt_bound c; have := lit.isLt; omega

private theorem nbrs_wvec1_lt {c : FullCfg} {s0 : FullState} (hs0 : s0.LengthsOk c)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * s0.core.cur_vars)
    (hcv30 : s0.core.cur_vars < 2 ^ 30) :
    ((lit.setWidth 64 <<< 1#64) + 1#64).toNat < s0.core.wvec.length := by
  change ((lit.setWidth 64 <<< 1) + 1#64).toNat < s0.core.wvec.length
  rw [hs0.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have := hs0.core_ok.cur_vars_le; have := mv_lt_bound c; have := lit.isLt; omega

private theorem nbrs_hend_hc {c : FullCfg} {s0 : FullState} (hs0 : s0.LengthsOk c)
    (hwl : WatchStackLayout s0.core) {lit : BitVec 32} (hlit : lit.toNat < 2 * s0.core.cur_vars)
    (hcv30 : s0.core.cur_vars < 2 ^ 30)
    (h0 : 2 * lit.toNat % 2 ^ 64 < s0.core.wvec.length)
    (h1 : (2 * lit.toNat + 1) % 2 ^ 64 < s0.core.wvec.length) :
    ((s0.core.wvec[2 * lit.toNat % 2 ^ 64]'h0).toNat +
      (s0.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64]'h1).toNat) % 2 ^ 64 =
      fullWatchOffCore s0.core lit.toNat + fullWatchSizeCore s0.core lit.toNat := by
  have hwbd := hwl.bounds lit.toNat hlit
  have hwcap_lt : c.wcap < 2 ^ 31 := by
    have := c.hwcap; unfold LeanQbe.T.Examples.Kissat.Ref.dimacsBound at *; omega
  have hwlen_le := hs0.core_ok.wlen_le
  have hget : ∀ i (hi : i < s0.core.wvec.length),
      s0.core.wvec[i]'hi = s0.core.wvec[i]?.getD 0#32 :=
    fun i hi => by simp [List.getElem?_eq_getElem hi]
  have hm0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := by omega
  have hm1 : (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 := by omega
  rw [hget _ h0, hget _ h1, hm0, hm1]
  change (fullWatchOffCore s0.core lit.toNat + fullWatchSizeCore s0.core lit.toNat) % 2 ^ 64 = _
  omega

private theorem nbrs_occ_ar_lt {c : FullCfg} {F : List (List Nat)} {s0 : FullState}
    (hs0 : s0.LengthsOk c) (harena : FullArenaClausesInv c F s0.core) {cref : BitVec 32}
    (hmem : cref.toNat ∈ fullArenaClauseRefsCore s0.core) :
    cref.toNat + 3 + fullArenaClauseSizeCore s0.core cref.toNat ≤ c.arena_cap ∧
      c.arena_cap < 2 ^ 31 := by
  have hwf := harena.refs_wf cref.toNat hmem
  have har_lt : c.arena_cap < 2 ^ 31 := by
    have := c.harena; unfold LeanQbe.T.Examples.Kissat.Ref.dimacsBound at *; omega
  have := hs0.core_ok.arena_len_le
  omega

private theorem nbrs_occ_sz {c : FullCfg} {F : List (List Nat)} {s0 : FullState}
    (hs0 : s0.LengthsOk c) (harena : FullArenaClausesInv c F s0.core) {p : BitVec 64}
    {cref : BitVec 32} (hmem : cref.toNat ∈ fullArenaClauseRefsCore s0.core)
    (hp1_w : s0.core.wstk[p.toNat + 1]? = some cref) (hp_bd : p.toNat + 1 < 2 ^ 64)
    (hp1 : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 < s0.core.wstk.length)
    (ha2 : (s0.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64].toNat +
      (2 : BitVec 64).toNat) % 2 ^ 64 < s0.core.arena.length) :
    (s0.core.arena[(s0.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64].toNat +
      (2 : BitVec 64).toNat) % 2 ^ 64]'ha2).toNat =
      fullArenaClauseSizeCore s0.core cref.toNat := by
  have ⟨hcr_bd, _⟩ := nbrs_occ_ar_lt hs0 harena hmem
  have hp1m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 := by
    change (p.toNat + 1) % 2 ^ 64 = p.toNat + 1; omega
  have hce := list_getElem_of_eq hp1m hp1_w hp1
  have har2m : (s0.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64].toNat +
      (2 : BitVec 64).toNat) % 2 ^ 64 = cref.toNat + 2 := by
    rw [hce]; change (cref.toNat + 2) % 2 ^ 64 = cref.toNat + 2; omega
  unfold fullArenaClauseSizeCore
  have hg2 := List.getElem?_eq_getElem ha2
  have h2eq : s0.core.arena[cref.toNat + 2]? = some (s0.core.arena[(s0.core.wstk[(p.toNat +
      (1 : BitVec 64).toNat) % 2 ^ 64].toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'ha2) := by
    rw [← har2m]; exact hg2
  rw [h2eq, Option.getD_some]

private theorem nbrs_occ_k_ar {c : FullCfg} {F : List (List Nat)} {s0 : FullState}
    (hs0 : s0.LengthsOk c) (harena : FullArenaClausesInv c F s0.core) {p : BitVec 64}
    {cref k : BitVec 32}
    (hmem : cref.toNat ∈ fullArenaClauseRefsCore s0.core)
    (hp1_w : s0.core.wstk[p.toNat + 1]? = some cref) (hp1_eq : (p + 1#64).toNat = p.toNat + 1)
    (hp1_s0 : (p + 1#64).toNat < s0.core.wstk.length)
    (hk : k.toNat < fullArenaClauseSizeCore s0.core cref.toNat) :
    ((BitVec.setWidth 64 (s0.core.wstk[(p + 1#64).toNat]'hp1_s0) + 3#64) +
      BitVec.setWidth 64 k).toNat < s0.core.arena.length := by
  have ⟨hcr_bd, _⟩ := nbrs_occ_ar_lt hs0 harena hmem
  have hce := list_getElem_of_eq hp1_eq hp1_w hp1_s0
  rw [hs0.core_ok.arena_len_arr, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, hce]
  omega

private theorem nbrs_occ_u_lt {c : FullCfg} {F : List (List Nat)} {s0 : FullState}
    (hs0 : s0.LengthsOk c) (harena : FullArenaClausesInv c F s0.core)
    (hcv30 : s0.core.cur_vars < 2 ^ 30) {p : BitVec 64} {cref k : BitVec 32}
    (hmem : cref.toNat ∈ fullArenaClauseRefsCore s0.core)
    (hp1_w : s0.core.wstk[p.toNat + 1]? = some cref) (hp1_eq : (p + 1#64).toNat = p.toNat + 1)
    (hp1_s0 : (p + 1#64).toNat < s0.core.wstk.length)
    (hk : k.toNat < fullArenaClauseSizeCore s0.core cref.toNat)
    (hp1m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 < s0.core.wstk.length)
    (har : ((s0.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'hp1m).toNat +
      (3 : BitVec 64).toNat + k.toNat) % 2 ^ 64 < s0.core.arena.length)
    (hc : (s0.core.arena[((s0.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'hp1m).toNat +
      (3 : BitVec 64).toNat + k.toNat) % 2 ^ 64]'har).toNat / 2 < s0.core.cur_vars % 2 ^ 64) :
    (s0.core.arena[((BitVec.setWidth 64 (s0.core.wstk[(p + 1#64).toNat]'hp1_s0) + 3#64) +
      BitVec.setWidth 64 k).toNat]'(nbrs_occ_k_ar hs0 harena hmem hp1_w hp1_eq hp1_s0 hk) >>>
        1#32).toNat < s0.core.cur_vars := by
  have ⟨hcr_bd, _⟩ := nbrs_occ_ar_lt hs0 harena hmem
  have hp1m_eq : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 := by
    have := (p + 1#64).isLt; change (p.toNat + 1) % 2 ^ 64 = p.toNat + 1; omega
  have hce1 := list_getElem_of_eq hp1m_eq hp1_w hp1m
  have hce2 := list_getElem_of_eq hp1_eq hp1_w hp1_s0
  have hi_eq : ((s0.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'hp1m).toNat +
      (3 : BitVec 64).toNat + k.toNat) % 2 ^ 64 =
      ((BitVec.setWidth 64 (s0.core.wstk[(p + 1#64).toNat]'hp1_s0) + 3#64) +
        BitVec.setWidth 64 k).toNat := by
    rw [hce1, hce2, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change (cref.toNat + 3 + k.toNat) % 2 ^ 64 = _
    omega
  have hcongr : ∀ {a b : Nat} (hab : a = b) (ha : a < s0.core.arena.length)
      (hb : b < s0.core.arena.length), s0.core.arena[a]'ha = s0.core.arena[b]'hb := by
    rintro _ _ rfl _ _; rfl
  rw [hcongr hi_eq har (nbrs_occ_k_ar hs0 harena hmem hp1_w hp1_eq hp1_s0 hk)] at hc
  change BitVec.toNat ((_ : BitVec 32) >>> (1 : Nat)) < s0.core.cur_vars
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

public theorem full_bve_collect_nbrs_m7_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullBveCollectNbrsM7Spec a m Q X →
      Func.wp Γ Src.Eliminate.full_bve_collect_nbrs_m7_body a m Q X := by
  intro ⟨h, v, ⟨⟩⟩ m Q X hPre
  rcases hPre with ⟨c, F0, s0, R, rfl, hden0, htmk0, hm0, hQ⟩
  obtain ⟨F_cur, hdw0⟩ := hden0.exists_witness
  have hdw_s0 : DenseWatchesInv F_cur s0.core := denseWatchesInv_of_w hdw0
  have hwl_s0 : WatchStackLayout s0.core := watchLayout_of_denseInv hden0
  have hs0 : s0.LengthsOk c := hdw0.1
  have hcv_le := hs0.core_ok.cur_vars_le
  have hcv30 : s0.core.cur_vars < 2 ^ 30 := cv_lt_2p30 hs0
  unfold Func.wp Src.Eliminate.full_bve_collect_nbrs_m7_body
  c0_hfast_nogrp_nobound
  refine wp_loop_group
    (fun n (nn, side, _) mi =>
      ∃ mclr ws2, 2 - side.toNat = n ∧ side.toNat ≤ 2 ∧ mclr.length = c.max_vars ∧
        ws2.length = 2 * c.max_vars ∧ nn.toNat ≤ s0.core.cur_vars ∧
        (∀ i < nn.toNat, (ws2[i]?.getD 0#32).toNat < s0.core.cur_vars) ∧
        (FullMem c (nbrsSt s0 mclr ws2) ⋆ R) mi)
    ?_ ?_
  · intro J n ⟨nn, side, ⟨⟩⟩ mi ih ⟨mclr, ws2, hn_eq, hside, hmclr, hws2, hnn, hws2_b, hmi⟩
    c0_hfast_nogrp_nobound
    · have hside_lt2 : side.toNat < 2 := by simpa using hc
      apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun nn' mj =>
        ∃ mclr' ws2', mclr'.length = c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
          nn'.toNat ≤ s0.core.cur_vars ∧
          (∀ i < nn'.toNat, (ws2'[i]?.getD 0#32).toNat < s0.core.cur_vars) ∧
          (FullMem c (nbrsSt s0 mclr' ws2') ⋆ R) mj)
      · intro _J23 nn' mj ⟨mclr', ws2', hmclr', hws2', hnn', hws2'_b, hmj⟩
        c0_hfast_nogrp_nobound
        have hside1 : (side + 1#32).toNat = side.toNat + 1 := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        exact ih (2 - (side + 1#32).toNat) (nn', side + 1#32, ()) _ (by omega)
          ⟨mclr', ws2', rfl, by omega, hmclr', hws2', hnn', hws2'_b, hmj⟩
      · intro J23 hJ23
        c0_hfast_nogrp_nobound
        · have hlit_lt : ((v <<< 1#32) ||| side).toNat < 2 * s0.core.cur_vars := by
            change ((v <<< OfNat.ofNat 1) ||| side).toNat < 2 * s0.core.cur_vars; omega
          have hlit0 : ((((v <<< 1#32) ||| side).setWidth 64) <<< 1#64).toNat <
              (nbrsSt s0 mclr ws2).core.wvec.length :=
            nbrs_wvec0_lt hs0 hlit_lt hcv30
          have hlit1 : (((((v <<< 1#32) ||| side).setWidth 64) <<< 1#64) + 1#64).toNat <
              (nbrsSt s0 mclr ws2).core.wvec.length :=
            nbrs_wvec1_lt hs0 hlit_lt hcv30
          c0_hfast_nogrp_nobound
          let lit := (v <<< 1#32) ||| side
          let off : Nat := fullWatchOffCore s0.core lit.toNat
          let sz : Nat := fullWatchSizeCore s0.core lit.toNat
          let endOff : Nat := off + sz
          have hlit_bd : lit.toNat < 2 * s0.core.cur_vars := hlit_lt
          have hlit_wvec0 : (lit.setWidth 64 <<< 1#64).toNat = 2 * lit.toNat := by
            change (lit.setWidth 64 <<< 1).toNat = 2 * lit.toNat
            rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
            have := lit.isLt; omega
          have hwlen_bd : endOff ≤ s0.core.wlen := hwl_s0.bounds lit.toNat hlit_bd
          have hwcap_lt : c.wcap < 2 ^ 31 := by
            have := c.hwcap; unfold LeanQbe.T.Examples.Kissat.Ref.dimacsBound at *; omega
          have hwlen_le := hs0.core_ok.wlen_le
          have hvec0_bd : 2 * lit.toNat % 2 ^ 64 < s0.core.wvec.length := by
            rw [hs0.core_ok.wvec_len]; omega
          have hvec1_bd : (2 * lit.toNat + 1) % 2 ^ 64 < s0.core.wvec.length := by
            rw [hs0.core_ok.wvec_len]; omega
          have hoff_get : ∀ h, (s0.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'h).toNat = off :=
            fun h => by
              dsimp only [off, fullWatchOffCore]
              have hget : s0.core.wvec[2 * lit.toNat]? =
                  some (s0.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'h) := by
                rw [← hlit_wvec0]; exact List.getElem?_eq_getElem h
              rw [hget, Option.getD_some]
          have hend_hc := fun h0 h1 => nbrs_hend_hc hs0 hwl_s0 hlit_bd hcv30 h0 h1
          apply wp_join_state (fun x : BitVec 64 × BitVec 64 => (x.1, x.2, ())) (fun x mj =>
            ∃ mclr' ws2', mclr'.length = c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
              x.1.toNat ≤ s0.core.cur_vars ∧
              (∀ i < x.1.toNat, (ws2'[i]?.getD 0#32).toNat < s0.core.cur_vars) ∧
              (FullMem c (nbrsSt s0 mclr' ws2') ⋆ R) mj)
          · intro _J46 x mj hinv; c0_hfast_nogrp_nobound; exact hJ23 x.1 mj hinv
          · intro J46 hJ46
            refine wp_loop_group
              (fun n' (nn_p, p, _) mk =>
                ∃ mclr' ws2', endOff - p.toNat = n' ∧ off ≤ p.toNat ∧ p.toNat ≤ endOff ∧
                  DenseWatchSliceOk F_cur s0.core lit.toNat p.toNat (endOff - p.toNat) ∧
                  mclr'.length = c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
                  nn_p.toNat ≤ s0.core.cur_vars ∧
                  (∀ i < nn_p.toNat, (ws2'[i]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                  (FullMem c (nbrsSt s0 mclr' ws2') ⋆ R) mk)
              ?_ ?_
            · intro J48 n' ⟨nn_p, p, ⟨⟩⟩ mk ih48
                ⟨mclr', ws2', hn48, hp_lo, hp_hi, hslice, hmclr', hws2', hnn_p, hws2'_b, hmk⟩
              c0_hfast_nogrp_nobound
              · have hp_end : p.toNat < endOff := by
                  dsimp only [nbrsSt] at hc
                  change p.toNat <
                    (((s0.core.wvec[2 * lit.toNat % 2 ^ 64]'hvec0_bd).toNat +
                      (s0.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64]'hvec1_bd).toNat) % 2 ^ 64)
                      at hc
                  rw [hend_hc] at hc
                  exact hc
                have hp_wstk : p.toNat < (nbrsSt s0 mclr' ws2').core.wstk.length := by
                  change p.toNat < s0.core.wstk.length
                  rw [hs0.core_ok.wstk_len_arr]; omega
                c0_hfast_nogrp_nobound
                · have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by
                    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
                  have hrem : ∃ rem', endOff - p.toNat = rem' + 1 :=
                    ⟨endOff - p.toNat - 1, by omega⟩
                  rcases hrem with ⟨rem', hrem_eq⟩
                  rw [hrem_eq] at hslice
                  cases hslice with
                  | @occ _ _ w0' _ hp_w0 _ hflag _ _ _ _ =>
                    exfalso
                    dsimp only [nbrsSt] at hc
                    have hget_p :
                        s0.core.wstk[p.toNat]? = some (s0.core.wstk[p.toNat]'hp_wstk) :=
                      List.getElem?_eq_getElem hp_wstk
                    rw [hget_p] at hp_w0; injection hp_w0 with hw0; subst hw0; exact hc hflag
                  | @bin _ _ w0' hp_w0 hflag _ hbin_lt _ hrest =>
                    apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun nn'' ml =>
                      ∃ mclr'' ws2'', mclr''.length = c.max_vars ∧
                        ws2''.length = 2 * c.max_vars ∧ nn''.toNat ≤ s0.core.cur_vars ∧
                        (∀ i < nn''.toNat, (ws2''[i]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                        (FullMem c (nbrsSt s0 mclr'' ws2'') ⋆ R) ml)
                    · intro _J59 nn'' ml ⟨mclr'', ws2'', hmclr'', hws2'', hnn'', hws2''_b, hml⟩
                      c0_hfast_nogrp_nobound
                      refine ih48 (endOff - (p + 1#64).toNat) (nn'', p + 1#64, ()) _ (by omega)
                        ⟨mclr'', ws2'', rfl, by omega, by omega, ?_,
                          hmclr'', hws2'', hnn'', hws2''_b, hml⟩
                      rw [hp1_eq, show endOff - (p.toNat + 1) = rem' from by omega]
                      exact hrest
                    · intro J59 hJ59
                      c0_hfast_nogrp_nobound
                      · have hp_s0 : p.toNat < s0.core.wstk.length := hp_wstk
                        let u_lit := s0.core.wstk[p.toNat]'hp_s0 &&& 0x7FFFFFFF#32
                        let u := u_lit >>> 1#32
                        have hu_lt : u.toNat < s0.core.cur_vars := by
                          dsimp only [nbrsSt] at hc
                          exact nbrs_u_lt hcv30 u_lit hc
                        have hu_fl : (BitVec.setWidth 64 u).toNat <
                            (nbrsSt s0 mclr' ws2').core.flags.length := by
                          change _ < s0.core.flags.length; exact nbrs_u_fl hs0 hu_lt hcv30
                        c0_hfast_nogrp_nobound
                        · have hu_vals : (BitVec.setWidth 64 u <<< 1#64).toNat <
                              (nbrsSt s0 mclr' ws2').core.vals.length := by
                            change _ < s0.core.vals.length; exact nbrs_u_vals hs0 hu_lt hcv30
                          c0_hfast_nogrp_nobound
                          · have hu_mc : (BitVec.setWidth 64 u).toNat <
                                (nbrsSt s0 mclr' ws2').core.min_clr.length := by
                              change _ < mclr'.length; exact nbrs_u_mc hmclr' hs0 hu_lt hcv30
                            c0_hfast_nogrp_nobound
                            · have hnn_lt : nn_p.toNat < s0.core.cur_vars := by omega
                              have hnn_ws2 : nn_p.toNat <
                                  (nbrsSt s0 mclr' ws2').scratch.work_stk2.length := by
                                change nn_p.toNat < ws2'.length; rw [hws2']; omega
                              have hnn1_eq : (nn_p + 1#64).toNat = nn_p.toNat + 1 := by
                                rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
                              c0_hfast_nogrp_nobound
                              refine hJ59 (nn_p + 1#64) _
                                ⟨mclr'.set (BitVec.setWidth 64 u).toNat 1#32, ws2'.set nn_p.toNat u,
                                  by rw [List.length_set, hmclr'], by rw [List.length_set, hws2'],
                                  by omega, nbrs_ws2_set_b hws2' hcv_le hnn_lt hws2'_b hu_lt,
                                  by dsimp only [nbrsSt, u, u_lit] at hm ⊢; exact hm⟩
                            · exact hJ59 nn_p mk ⟨mclr', ws2', hmclr', hws2', hnn_p, hws2'_b, hmk⟩
                            · exact hJ59 nn_p mk ⟨mclr', ws2', hmclr', hws2', hnn_p, hws2'_b, hmk⟩
                          · exact hJ59 nn_p mk ⟨mclr', ws2', hmclr', hws2', hnn_p, hws2'_b, hmk⟩
                        · exact hJ59 nn_p mk ⟨mclr', ws2', hmclr', hws2', hnn_p, hws2'_b, hmk⟩
                      · exact hJ59 nn_p mk ⟨mclr', ws2', hmclr', hws2', hnn_p, hws2'_b, hmk⟩
                      · exact hJ59 nn_p mk ⟨mclr', ws2', hmclr', hws2', hnn_p, hws2'_b, hmk⟩
                · exact hJ46 (nn_p, p + 1#64) mk
                    ⟨mclr', ws2', hmclr', hws2', hnn_p, hws2'_b, hmk⟩
                · have hp1_end : (p + 1#64).toNat < endOff := by
                    dsimp only [nbrsSt] at hc
                    change ¬((s0.core.wvec[2 * lit.toNat % 2 ^ 64]'hvec0_bd).toNat +
                      (s0.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64]'hvec1_bd).toNat) % 2 ^ 64 ≤
                        (p.toNat + BitVec.toNat (1#64)) % 2 ^ 64 at hc
                    rw [hend_hc] at hc
                    have h1eq : (p + 1#64).toNat = (p.toNat + BitVec.toNat (1#64)) % 2 ^ 64 :=
                      BitVec.toNat_add _ _
                    have : BitVec.toNat (1#64) = 1 := rfl
                    dsimp only [endOff, off, sz, lit] at hc ⊢
                    omega
                  have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by
                    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
                  have hp2_eq : ((p + 1#64) + 1#64).toNat = p.toNat + 2 := by
                    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hp1_eq]; omega
                  have hp1_s0 : (p + 1#64).toNat < s0.core.wstk.length := by
                    rw [hs0.core_ok.wstk_len_arr]; omega
                  have hp1_wstk :
                      (p + 1#64).toNat < (nbrsSt s0 mclr' ws2').core.wstk.length := hp1_s0
                  have hzero : (s0.core.wstk[p.toNat]'hp_wstk &&& 0x80000000#32) = 0#32 := by
                    dsimp only [nbrsSt] at *; assumption
                  have hrem : ∃ rem', endOff - p.toNat = rem' + 2 := by
                    have hne1 : endOff - p.toNat ≠ 1 := by
                      intro h1
                      rw [h1] at hslice
                      cases hslice with
                      | @bin _ _ w0' hp_w0 hflag =>
                        have hw0 := list_getElem_of_eq rfl hp_w0 hp_wstk
                        rw [hw0] at hzero; exact hflag hzero
                    exact ⟨endOff - p.toNat - 2, by omega⟩
                  rcases hrem with ⟨rem', hrem_eq⟩
                  rw [hrem_eq] at hslice
                  cases hslice with
                  | @bin _ _ w0' hp_w0 hflag =>
                    exfalso
                    have hw0 := list_getElem_of_eq rfl hp_w0 hp_wstk
                    rw [hw0] at hzero; exact hflag hzero
                  | @occ _ _ w0' cref' hp_w0 hp_w1 _ _ _ hcref_mem hrest =>
                    have ⟨hcr_bd, hcap_lt⟩ := nbrs_occ_ar_lt hs0 hdw0.2.1.arena hcref_mem
                    have hce := list_getElem_of_eq hp1_eq hp_w1 hp1_s0
                    have hcref_ar : (BitVec.setWidth 64
                        (s0.core.wstk[(p + 1#64).toNat]'hp1_s0)).toNat <
                        (nbrsSt s0 mclr' ws2').core.arena.length := by
                      change _ < s0.core.arena.length
                      rw [hs0.core_ok.arena_len_arr, BitVec.toNat_setWidth, hce]; omega
                    have hcref2_ar : ((BitVec.setWidth 64
                        (s0.core.wstk[(p + 1#64).toNat]'hp1_s0)) + 2#64).toNat <
                        (nbrsSt s0 mclr' ws2').core.arena.length := by
                      change _ < s0.core.arena.length
                      rw [hs0.core_ok.arena_len_arr, BitVec.toNat_add, BitVec.toNat_setWidth,
                        BitVec.toNat_ofNat, hce]; omega
                    c0_hfast_nogrp_nobound
                    · refine ih48 (endOff - ((p + 1#64) + 1#64).toNat)
                        (nn_p, (p + 1#64) + 1#64, ()) _ (by omega)
                        ⟨mclr', ws2', rfl, by omega, by omega, ?_,
                          hmclr', hws2', hnn_p, hws2'_b, hmk⟩
                      rw [hp2_eq, show endOff - (p.toNat + 2) = rem' from by omega]
                      exact hrest
                    · refine wp_loop_group
                        (fun n_k (nn_k, k, _) mk' =>
                          ∃ mclr'' ws2'',
                            fullArenaClauseSizeCore s0.core cref'.toNat - k.toNat = n_k ∧
                            k.toNat ≤ fullArenaClauseSizeCore s0.core cref'.toNat ∧
                            mclr''.length = c.max_vars ∧ ws2''.length = 2 * c.max_vars ∧
                            nn_k.toNat ≤ s0.core.cur_vars ∧
                            (∀ i < nn_k.toNat, (ws2''[i]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                            (FullMem c (nbrsSt s0 mclr'' ws2'') ⋆ R) mk')
                        ?_ ?_
                      · intro J108 n_k ⟨nn_k, k, ⟨⟩⟩ mk' ih108
                          ⟨mclr'', ws2'', hnk, hk_le, hmclr'', hws2'', hnn_k, hws2''_b, hmk'⟩
                        c0_hfast_nogrp_nobound
                        · have hk_lt : k.toNat < fullArenaClauseSizeCore s0.core cref'.toNat := by
                            have hp1m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 <
                                s0.core.wstk.length := by
                              change (p.toNat + 1) % 2 ^ 64 < s0.core.wstk.length
                              rw [hs0.core_ok.wstk_len_arr]; omega
                            have har2m :
                                ((s0.core.wstk[(p.toNat +
                                    (1 : BitVec 64).toNat) % 2 ^ 64]'hp1m).toNat +
                                  (2 : BitVec 64).toNat) % 2 ^ 64 < s0.core.arena.length := by
                              have hce := list_getElem_of_eq
                                (by change (p.toNat + 1) % 2 ^ 64 = p.toNat + 1; omega) hp_w1 hp1m
                              rw [hs0.core_ok.arena_len_arr, hce]
                              change (cref'.toNat + 2) % 2 ^ 64 < c.arena_cap; omega
                            have hc' : k.toNat <
                                (s0.core.arena[((s0.core.wstk[(p.toNat +
                                    (1 : BitVec 64).toNat) % 2 ^ 64]'hp1m).toNat +
                                  (2 : BitVec 64).toNat) % 2 ^ 64]'har2m).toNat := hc
                            rw [nbrs_occ_sz hs0 hdw0.2.1.arena hcref_mem hp_w1
                              (by omega) hp1m har2m] at hc'
                            exact hc'
                          have hk_ar_s0 :=
                            nbrs_occ_k_ar hs0 hdw0.2.1.arena hcref_mem hp_w1 hp1_eq hp1_s0 hk_lt
                          have hk_ar : ((BitVec.setWidth 64
                              (s0.core.wstk[(p + 1#64).toNat]'hp1_s0) + 3#64) +
                              BitVec.setWidth 64 k).toNat <
                              (nbrsSt s0 mclr'' ws2'').core.arena.length := hk_ar_s0
                          c0_hfast_nogrp_nobound
                          apply wp_join_state (fun x : BitVec 64 => (x, ())) (fun nn'' ml =>
                            ∃ mclr3 ws2_3, mclr3.length = c.max_vars ∧
                              ws2_3.length = 2 * c.max_vars ∧ nn''.toNat ≤ s0.core.cur_vars ∧
                              (∀ i < nn''.toNat, (ws2_3[i]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                              (FullMem c (nbrsSt s0 mclr3 ws2_3) ⋆ R) ml)
                          · intro _J119 nn'' ml ⟨mclr3, ws2_3, hmclr3, hws2_3, hnn3, hws2_3_b, hml⟩
                            c0_hfast_nogrp_nobound
                            have hk1_eq : (k + 1#32).toNat = k.toNat + 1 := by
                              rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
                            exact ih108
                              (fullArenaClauseSizeCore s0.core cref'.toNat - (k + 1#32).toNat)
                              (nn'', k + 1#32, ()) _ (by omega)
                              ⟨mclr3, ws2_3, rfl, by omega, hmclr3, hws2_3, hnn3, hws2_3_b, hml⟩
                          · intro J119 hJ119
                            let u_lit := s0.core.arena[((BitVec.setWidth 64
                              (s0.core.wstk[(p + 1#64).toNat]'hp1_s0) + 3#64) +
                              BitVec.setWidth 64 k).toNat]'hk_ar_s0
                            let u := u_lit >>> 1#32
                            c0_hfast_nogrp_nobound
                            · have hp1m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 <
                                  s0.core.wstk.length := by
                                change (p.toNat + 1) % 2 ^ 64 < s0.core.wstk.length
                                rw [hs0.core_ok.wstk_len_arr]; omega
                              have har_k : ((s0.core.wstk[(p.toNat +
                                    (1 : BitVec 64).toNat) % 2 ^ 64]'hp1m).toNat +
                                  (3 : BitVec 64).toNat + k.toNat) % 2 ^ 64 <
                                  s0.core.arena.length := by
                                have hce1 := list_getElem_of_eq
                                  (by change (p.toNat + 1) % 2 ^ 64 = p.toNat + 1; omega)
                                  hp_w1 hp1m
                                rw [hs0.core_ok.arena_len_arr, hce1]
                                change (cref'.toNat + 3 + k.toNat) % 2 ^ 64 < c.arena_cap; omega
                              have hu_lt : u.toNat < s0.core.cur_vars :=
                                nbrs_occ_u_lt hs0 hdw0.2.1.arena hcv30 hcref_mem hp_w1 hp1_eq
                                  hp1_s0 hk_lt hp1m har_k hc
                              have hu_fl : (BitVec.setWidth 64 u).toNat <
                                  (nbrsSt s0 mclr'' ws2'').core.flags.length := by
                                change _ < s0.core.flags.length; exact nbrs_u_fl hs0 hu_lt hcv30
                              c0_hfast_nogrp_nobound
                              · have hu_vals : (BitVec.setWidth 64 u <<< 1#64).toNat <
                                    (nbrsSt s0 mclr'' ws2'').core.vals.length := by
                                  change _ < s0.core.vals.length; exact nbrs_u_vals hs0 hu_lt hcv30
                                c0_hfast_nogrp_nobound
                                · have hu_mc : (BitVec.setWidth 64 u).toNat <
                                      (nbrsSt s0 mclr'' ws2'').core.min_clr.length := by
                                    change _ < mclr''.length
                                    exact nbrs_u_mc hmclr'' hs0 hu_lt hcv30
                                  c0_hfast_nogrp_nobound
                                  · have hnn_lt : nn_k.toNat < s0.core.cur_vars := by omega
                                    have hnn_ws2 : nn_k.toNat <
                                        (nbrsSt s0 mclr'' ws2'').scratch.work_stk2.length := by
                                      change nn_k.toNat < ws2''.length; rw [hws2'']; omega
                                    have hnn1_eq : (nn_k + 1#64).toNat = nn_k.toNat + 1 := by
                                      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
                                    c0_hfast_nogrp_nobound
                                    refine hJ119 (nn_k + 1#64) _
                                      ⟨mclr''.set (BitVec.setWidth 64 u).toNat 1#32,
                                        ws2''.set nn_k.toNat u,
                                        by rw [List.length_set, hmclr''],
                                        by rw [List.length_set, hws2''],
                                        by omega,
                                        nbrs_ws2_set_b hws2'' hcv_le hnn_lt hws2''_b hu_lt,
                                        by dsimp only [nbrsSt, u, u_lit] at hm ⊢; exact hm⟩
                                  · exact hJ119 nn_k mk'
                                      ⟨mclr'', ws2'', hmclr'', hws2'', hnn_k, hws2''_b, hmk'⟩
                                  · exact hJ119 nn_k mk'
                                      ⟨mclr'', ws2'', hmclr'', hws2'', hnn_k, hws2''_b, hmk'⟩
                                · exact hJ119 nn_k mk'
                                    ⟨mclr'', ws2'', hmclr'', hws2'', hnn_k, hws2''_b, hmk'⟩
                              · exact hJ119 nn_k mk'
                                  ⟨mclr'', ws2'', hmclr'', hws2'', hnn_k, hws2''_b, hmk'⟩
                            · exact hJ119 nn_k mk'
                                ⟨mclr'', ws2'', hmclr'', hws2'', hnn_k, hws2''_b, hmk'⟩
                            · exact hJ119 nn_k mk'
                                ⟨mclr'', ws2'', hmclr'', hws2'', hnn_k, hws2''_b, hmk'⟩
                        · refine ih48 (endOff - ((p + 1#64) + 1#64).toNat)
                            (nn_k, (p + 1#64) + 1#64, ()) _ (by omega)
                            ⟨mclr'', ws2'', rfl, by omega, by omega, ?_,
                              hmclr'', hws2'', hnn_k, hws2''_b, hmk'⟩
                          rw [hp2_eq, show endOff - (p.toNat + 2) = rem' from by omega]
                          exact hrest
                      · intro J108 hJ108
                        c0_hfast_nogrp_nobound
                        exact hJ108 _ (nn_p, 0#32, ()) mk
                          ⟨mclr', ws2', rfl, Nat.zero_le _, hmclr', hws2', hnn_p, hws2'_b, hmk⟩
              · exact hJ46 (nn_p, p) mk ⟨mclr', ws2', hmclr', hws2', hnn_p, hws2'_b, hmk⟩
            · intro J48 hJ48
              c0_hfast_nogrp_nobound
              have hp0_eq : (BitVec.setWidth 64
                  (s0.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'hlit0)).toNat = off := by
                rw [BitVec.toNat_setWidth, hoff_get hlit0]
                have := (s0.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'hlit0).isLt
                omega
              refine hJ48 _ (nn, _, ()) _
                ⟨mclr, ws2, rfl, ?_, ?_, ?_, hmclr, hws2, hnn, hws2_b, hmi⟩
              · change off ≤ (BitVec.setWidth 64
                  (s0.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'hlit0)).toNat
                rw [hp0_eq]; exact Nat.le_refl _
              · change (BitVec.setWidth 64
                  (s0.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'hlit0)).toNat ≤ endOff
                rw [hp0_eq]; omega
              · change DenseWatchSliceOk F_cur s0.core lit.toNat
                  (BitVec.setWidth 64
                    (s0.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'hlit0)).toNat
                  (endOff - (BitVec.setWidth 64
                    (s0.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'hlit0)).toNat)
                rw [hp0_eq]
                dsimp only [off, sz, endOff]
                rw [Nat.add_sub_cancel_left]
                exact hdw_s0.slices lit.toNat hlit_lt
        · exact hJ23 nn mi ⟨mclr, ws2, hmclr, hws2, hnn, hws2_b, hmi⟩
    · refine wp_loop_group
        (fun n' (ci, _) mj =>
          ∃ mclr', nn.toNat - ci.toNat = n' ∧ ci.toNat ≤ nn.toNat ∧
            mclr'.length = c.max_vars ∧ (FullMem c (nbrsSt s0 mclr' ws2) ⋆ R) mj)
        ?_ ?_
      · intro Jc n' ⟨ci, ⟨⟩⟩ mj ihc ⟨mclr', hnc_eq, hci, hmclr', hmj⟩
        c0_hfast_nogrp_nobound
        · have hci_ws2 : ci.toNat < (nbrsSt s0 mclr' ws2).scratch.work_stk2.length := by
            change ci.toNat < ws2.length
            rw [hws2]; omega
          have hu_lt : (ws2[ci.toNat]?.getD 0#32).toNat < s0.core.cur_vars :=
            hws2_b ci.toNat (by omega)
          have hci_len : ci.toNat < ws2.length := hci_ws2
          have hu_mclr : (BitVec.setWidth 64 ws2[ci.toNat]).toNat <
              (nbrsSt s0 mclr' ws2).core.min_clr.length := by
            have hget : ws2[ci.toNat]'hci_len = ws2[ci.toNat]?.getD 0#32 := by
              simp [List.getElem?_eq_getElem hci_len]
            change (BitVec.setWidth 64 (ws2[ci.toNat]'hci_len)).toNat < mclr'.length
            rw [hmclr', BitVec.toNat_setWidth, hget]
            have := (ws2[ci.toNat]?.getD 0#32).isLt
            omega
          c0_hfast_nogrp_nobound
          have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by
            have : ci.toNat < 2 ^ 30 := by omega
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
            omega
          refine ihc (nn.toNat - (ci + 1#64).toNat) (ci + 1#64, ()) _ (by omega)
            ⟨_, rfl, by omega, ?_, by simpa [nbrsSt] using hm⟩
          rw [List.length_set, hmclr']
        · refine hQ nn mclr' ws2 mj (nbrsSt_lengthsOk hs0 hmclr' hws2) hnn hws2_b ?_
          simpa [nbrsSt] using hmj
      · intro Jc hJc
        c0_hfast_nogrp_nobound
        exact hJc _ _ _ ⟨mclr, rfl, Nat.zero_le _, hmclr, hmi⟩
  · intro J hJ
    c0_hfast_nogrp_nobound
    have h0_le : (0#32).toNat ≤ 2 := by decide
    exact hJ _ _ _ ⟨s0.core.min_clr, s0.scratch.work_stk2, rfl, h0_le,
      hs0.core_ok.min_clr_len_arr, hs0.scratch_ok.work_stk2_len, Nat.zero_le _,
      fun _ h => absurd h (Nat.not_lt_zero _), hm0⟩

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
