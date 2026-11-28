/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Variable Enqueue WP Proof (`enq_var`)

Canonical `Func.wp` proof for `full_cong_enq_var` (`Spec.fullCongEnqVarSpec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

private theorem bv64_add_ofNat_toNat {a : BitVec 64} {k cap : Nat}
    (ha : a.toNat + k ≤ cap) (hcap : cap < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem bv32_and_sub1_eq_mod {x : BitVec 32} {occ : Nat}
    (hpow : ∃ p, 1 ≤ p ∧ p ≤ 20 ∧ occ = 2 ^ p) :
    (x &&& (BitVec.ofNat 32 occ - 1#32)).toNat = x.toNat % occ := by
  rcases hpow with ⟨p, hp1, hp20, rfl⟩
  have hpow_lt : 2 ^ p < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ p := Nat.pow_pos (by decide)
  have h1 : (BitVec.ofNat 32 (2 ^ p) - 1#32).toNat = 2 ^ p - 1 := by
    have hbv : (BitVec.ofNat 32 (2 ^ p)).toNat = 2 ^ p := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpow_lt]
    bv_omega
  have hmask : BitVec.ofNat 32 (2 ^ p) - 1#32 = BitVec.ofNat 32 (2 ^ p - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hmask, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat p

private theorem bv32_and_sub1_lt {x m : BitVec 32} {occ : Nat}
    (hpow : ∃ p, 1 ≤ p ∧ p ≤ 20 ∧ occ = 2 ^ p) (hm : m = BitVec.ofNat 32 occ) :
    (x &&& (m - 1#32)).toNat < occ := by
  subst hm; rw [bv32_and_sub1_eq_mod hpow]
  rcases hpow with ⟨p, _, _, rfl⟩
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

private theorem enq_var_unchanged {c : FullCfg} {s : FullState}
    {g_len ctrl_off ht_off ht_sz : Nat} {m : Mem 64} {R : Mem 64 → Prop} {Q : Post []}
    (hscrl : s.scratch.scratch_buf.length = c.scratch_cap)
    (hqctx : CongQueueCtx c s.scratch.scratch_buf g_len ctrl_off ht_off ht_sz)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      CongQueueCtx c scr' g_len ctrl_off ht_off ht_sz →
      (ctrl_off = c.scratch_cap → scr' = s.scratch.scratch_buf) →
      (∀ occ_bkt bkt_off inq_off q_off,
        CongCtrlLayout c s.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off q_off
          ht_off ht_sz →
        scr'[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
        scr'[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
        scr'[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
        scr'[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
        scr'[ctrl_off + 4]? = s.scratch.scratch_buf[ctrl_off + 4]? ∧
        scr'[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
        scr'[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
        ∀ idx, idx ≠ ctrl_off + 5 →
          ¬(q_off ≤ idx ∧ idx < q_off + occ_bkt) →
          ¬(inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q () m') : Q () m := by
  refine hQ s.scratch.scratch_buf m hscrl hqctx (fun _ => rfl) (fun occ bkt inq q hlay => ?_) hm
  rcases hlay with ⟨_, h8, _, _, hs0, hs1, hs2, hs3, hs6, hs7, _⟩
  exact ⟨getElem?_eq_some_of_getD (by omega) hs0, getElem?_eq_some_of_getD (by omega) hs1,
    getElem?_eq_some_of_getD (by omega) hs2, getElem?_eq_some_of_getD (by omega) hs3,
    rfl, getElem?_eq_some_of_getD (by omega) hs6, getElem?_eq_some_of_getD (by omega) hs7,
    fun _ _ _ _ => rfl⟩

public section

/-- Canonical `Func.wp` proof for `full_cong_enq_var`. -/
theorem full_cong_enq_var_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullCongEnqVarSpec args m Q X →
      Func.wp Γ full_cong_enq_var_body args m Q X := by
  rintro ⟨h, ctrl_off, v, ⟨⟩⟩ m0 Q X ⟨c, s, g_len, ht_off, ht_sz, R, rfl, hlen, hqctx, hm0, hQ⟩
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hcap_lt : c.scratch_cap < 2 ^ 32 := by
    have := c.hscr; unfold dimacsBound at this; omega
  have hcv_lt : s.core.cur_vars < 2 ^ 64 := by
    have := hlen.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
  unfold Func.wp full_cong_enq_var_body
  c0_hsplit
  · c0_hsteps!
    exact enq_var_unchanged hscrl hqctx hm0 hQ
  · have hctrl_lt : ctrl_off.toNat < c.scratch_cap := by omega
    clear hc
    c0_hsplit
    · c0_hsteps!
      exact enq_var_unchanged hscrl hqctx hm0 hQ
    · clear hc
      have hlay : ∃ occ_bkt bkt_off inq_off q_off,
          CongCtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off inq_off
            q_off ht_off ht_sz := by
        rcases hqctx with hcap | hex
        · omega
        · exact hex
      rcases hlay with ⟨occ_bkt, bkt_off, inq_off, q_off, hlay⟩
      have hlay_orig := hlay
      rcases hlay with ⟨_, hctrl8, _, _, hs0, hs1, hs2, hs3, hs6, hs7, hocc_pos, hocc_max,
        hpow, hht_pos, hq8, hqinq, hinqb, hbht, hhtcap, hqh_lt, hql_le, hq_vals⟩
      have ha0 : ctrl_off.toNat < s.scratch.scratch_buf.length := by omega
      have ha2_n : (ctrl_off + 2#64).toNat = ctrl_off.toNat + 2 :=
        bv64_add_ofNat_toNat (k := 2) (cap := c.scratch_cap) (by omega) (by omega)
      have ha3_n : (ctrl_off + 3#64).toNat = ctrl_off.toNat + 3 :=
        bv64_add_ofNat_toNat (k := 3) (cap := c.scratch_cap) (by omega) (by omega)
      have ha4_n : (ctrl_off + 4#64).toNat = ctrl_off.toNat + 4 :=
        bv64_add_ofNat_toNat (k := 4) (cap := c.scratch_cap) (by omega) (by omega)
      have ha5_n : (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5 :=
        bv64_add_ofNat_toNat (k := 5) (cap := c.scratch_cap) (by omega) (by omega)
      have ha2 : (ctrl_off + 2#64).toNat < s.scratch.scratch_buf.length := by omega
      have ha3 : (ctrl_off + 3#64).toNat < s.scratch.scratch_buf.length := by omega
      have ha4 : (ctrl_off + 4#64).toNat < s.scratch.scratch_buf.length := by omega
      have ha5 : (ctrl_off + 5#64).toNat < s.scratch.scratch_buf.length := by omega
      have hocc_bv : s.scratch.scratch_buf[ctrl_off.toNat]'ha0 = BitVec.ofNat 32 occ_bkt := by
        have := hs0; rw [List.getElem?_eq_getElem ha0, Option.getD_some] at this; exact this
      have hinq_bv : s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'ha2 =
          BitVec.ofNat 32 inq_off := by
        rw [list_getElem_congr ha2_n ha2 (by omega)]
        have := hs2; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; exact this
      have hq_bv : s.scratch.scratch_buf[(ctrl_off + 3#64).toNat]'ha3 =
          BitVec.ofNat 32 q_off := by
        rw [list_getElem_congr ha3_n ha3 (by omega)]
        have := hs3; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; exact this
      let bkt := v &&& (s.scratch.scratch_buf[ctrl_off.toNat]'ha0 - 1#32)
      have hbkt_lt : bkt.toNat < occ_bkt := bv32_and_sub1_lt hpow hocc_bv
      have hinq_bkt_n : ((s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'ha2).setWidth 64 +
          bkt.setWidth 64).toNat = inq_off + bkt.toNat := by
        rw [hinq_bv, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hinq_arr : ((s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'ha2).setWidth 64 +
          bkt.setWidth 64).toNat < s.scratch.scratch_buf.length := by omega
      let qh := s.scratch.scratch_buf[(ctrl_off + 4#64).toNat]'ha4
      let ql := s.scratch.scratch_buf[(ctrl_off + 5#64).toNat]'ha5
      let qidx := (qh + ql) &&& (s.scratch.scratch_buf[ctrl_off.toNat]'ha0 - 1#32)
      have hqidx_lt : qidx.toNat < occ_bkt := bv32_and_sub1_lt hpow hocc_bv
      have hq_pos_n : (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 3#64).toNat] +
          BitVec.setWidth 64 (s.scratch.scratch_buf[(ctrl_off + 4#64).toNat] +
            s.scratch.scratch_buf[(ctrl_off + 5#64).toNat] &&&
            s.scratch.scratch_buf[BitVec.toNat ctrl_off] - 1#32)).toNat = q_off + qidx.toNat := by
        dsimp only [qidx, qh, ql]
        rw [hq_bv, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hq_pos_arr : (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 3#64).toNat] +
          BitVec.setWidth 64 (s.scratch.scratch_buf[(ctrl_off + 4#64).toNat] +
            s.scratch.scratch_buf[(ctrl_off + 5#64).toNat] &&&
            s.scratch.scratch_buf[BitVec.toNat ctrl_off] - 1#32)).toNat <
          s.scratch.scratch_buf.length := by rw [hq_pos_n]; omega
      c0_hstraight!
      refine wp_join_group (ts := []) (fun () m' => ∃ scr' : List (BitVec 32),
        scr'.length = c.scratch_cap ∧ CongQueueCtx c scr' g_len ctrl_off.toNat ht_off ht_sz ∧
        (∀ o1 b1 i1 q1,
          CongCtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat o1 b1 i1 q1 ht_off ht_sz →
          scr'[ctrl_off.toNat]? = some (BitVec.ofNat 32 o1) ∧
          scr'[ctrl_off.toNat + 1]? = some (BitVec.ofNat 32 b1) ∧
          scr'[ctrl_off.toNat + 2]? = some (BitVec.ofNat 32 i1) ∧
          scr'[ctrl_off.toNat + 3]? = some (BitVec.ofNat 32 q1) ∧
          scr'[ctrl_off.toNat + 4]? = s.scratch.scratch_buf[ctrl_off.toNat + 4]? ∧
          scr'[ctrl_off.toNat + 6]? = some (BitVec.ofNat 32 ht_off) ∧
          scr'[ctrl_off.toNat + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
          ∀ idx, idx ≠ ctrl_off.toNat + 5 →
            ¬(q1 ≤ idx ∧ idx < q1 + o1) → ¬(i1 ≤ idx ∧ idx < i1 + o1) →
            scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m')
        (fun _ ⟨⟩ mf ⟨scr', hlen', hq', hfr', hmf⟩ => by
          c0_hstraight!
          exact hQ scr' mf hlen' hq' (fun h => by omega) hfr' hmf)
        ?_
      intro J hJ
      c0_hsplit
      · c0_hstraight!
        refine wp_join_group (ts := []) (fun () m' => ∃ scr' : List (BitVec 32),
          scr'.length = c.scratch_cap ∧ CongQueueCtx c scr' g_len ctrl_off.toNat ht_off ht_sz ∧
          (∀ o1 b1 i1 q1,
            CongCtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat o1 b1 i1 q1 ht_off ht_sz →
            scr'[ctrl_off.toNat]? = some (BitVec.ofNat 32 o1) ∧
            scr'[ctrl_off.toNat + 1]? = some (BitVec.ofNat 32 b1) ∧
            scr'[ctrl_off.toNat + 2]? = some (BitVec.ofNat 32 i1) ∧
            scr'[ctrl_off.toNat + 3]? = some (BitVec.ofNat 32 q1) ∧
            scr'[ctrl_off.toNat + 4]? = s.scratch.scratch_buf[ctrl_off.toNat + 4]? ∧
            scr'[ctrl_off.toNat + 6]? = some (BitVec.ofNat 32 ht_off) ∧
            scr'[ctrl_off.toNat + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
            ∀ idx, idx ≠ ctrl_off.toNat + 5 →
              ¬(q1 ≤ idx ∧ idx < q1 + o1) → ¬(i1 ≤ idx ∧ idx < i1 + o1) →
              scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m')
          (fun _ ⟨⟩ mf ⟨scr', hlen', hq', hfr', hmf⟩ => by
            c0_hstraight!
            exact hJ () mf ⟨scr', hlen', hq', hfr', hmf⟩)
          ?_
        intro J2 hJ2
        c0_hsplit
        · have hql_hc := hc; clear hc
          have hql_lt : ql.toNat < occ_bkt := by
            have h5_bv : (5 : BitVec 64) = 5#64 := rfl
            have h5_idx : (BitVec.toNat ctrl_off + BitVec.toNat (5 : BitVec 64)) % 2 ^ 64 =
                (ctrl_off + 5#64).toNat := by
              rw [h5_bv, ha5_n, show BitVec.toNat 5#64 = 5 from rfl, Nat.mod_eq_of_lt (by omega)]
            have hql_eq_hc : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
                BitVec.toNat (5 : BitVec 64)) % 2 ^ 64]'(by rw [h5_idx]; exact ha5) = ql :=
              list_getElem_congr h5_idx (by rw [h5_idx]; exact ha5) ha5
            have hc' : ql.toNat < (s.scratch.scratch_buf[BitVec.toNat ctrl_off]'ha0).toNat := by
              simpa only [← hql_eq_hc] using hql_hc
            rw [hocc_bv, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold congOccBktMax at hocc_max; omega)] at hc'
            exact hc'
          have hqh_lt' : qh.toNat < occ_bkt := by
            have := hqh_lt; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
            dsimp only [qh]; rwa [list_getElem_congr ha4_n ha4 (by omega)]
          have hqidx_mod : qidx.toNat = (qh.toNat + ql.toNat) % occ_bkt := by
            dsimp only [qidx]; rw [hocc_bv, bv32_and_sub1_eq_mod hpow]
            congr 1; unfold congOccBktMax at hocc_max; bv_omega
          have hql1_n : (ql + 1#32).toNat = ql.toNat + 1 := by
            unfold congOccBktMax at hocc_max; bv_omega
          c0_hstraight!
          let scr1 := ((s.scratch.scratch_buf.set (inq_off + bkt.toNat) 1#32).set
            (q_off + qidx.toNat) bkt).set (ctrl_off.toNat + 5) (ql + 1#32)
          have hscr1_len : scr1.length = c.scratch_cap := by simp [scr1, hscrl]
          have hlay1 : CongCtrlLayout c scr1 g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off
              ht_off ht_sz := by
            refine congCtrlLayout_same_tail hlay_orig (by simp [scr1]) ?_ ?_ ?_
            · rw [show scr1[ctrl_off.toNat + 5]? = some (ql + 1#32) from
                List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]
              omega
            · intro i hi hne
              dsimp only [scr1]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)]
            · intro k hk
              have hmod_k : (qh.toNat + k) % occ_bkt < occ_bkt := Nat.mod_lt _ hocc_pos
              have hq1_e : (scr1[ctrl_off.toNat + 5]?.getD 0#32).toNat = ql.toNat + 1 := by
                rw [show scr1[ctrl_off.toNat + 5]? = some (ql + 1#32) from
                  List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some, hql1_n]
              have hqh1_e : (scr1[ctrl_off.toNat + 4]?.getD 0#32).toNat = qh.toNat := by
                dsimp only [scr1, qh]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega),
                  list_getElem_congr ha4_n ha4 (by omega),
                  List.getElem?_eq_getElem (by omega), Option.getD_some]
              rw [hqh1_e]
              by_cases hkl : k = ql.toNat
              · subst hkl; rw [← hqidx_mod]
                dsimp only [scr1]
                rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_self (by simp [hscrl]; omega), Option.getD_some]
                exact hbkt_lt
              · have hne_idx : q_off + (qh.toNat + k) % occ_bkt ≠ q_off + qidx.toNat := by
                  rw [hqidx_mod]
                  intro heq
                  have hmod : (qh.toNat + k) % occ_bkt = (qh.toNat + ql.toNat) % occ_bkt := by
                    omega
                  have hlt : k < ql.toNat := by omega
                  by_cases c1 : qh.toNat + k < occ_bkt <;>
                    by_cases c2 : qh.toNat + ql.toNat < occ_bkt
                  · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hmod; omega
                  · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega),
                      Nat.mod_eq_of_lt (by omega)] at hmod; omega
                  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_of_lt c2] at hmod; omega
                  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
                dsimp only [scr1]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne hne_idx.symm,
                  List.getElem?_set_ne (by omega)]
                have hqh0 :
                    (s.scratch.scratch_buf[ctrl_off.toNat + 4]?.getD 0#32).toNat = qh.toNat := by
                  dsimp only [qh]
                  rw [list_getElem_congr ha4_n ha4 (by omega), List.getElem?_eq_getElem (by omega),
                    Option.getD_some]
                have hql0 :
                    (s.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat = ql.toNat := by
                  dsimp only [ql]
                  rw [list_getElem_congr ha5_n ha5 (by omega), List.getElem?_eq_getElem (by omega),
                    Option.getD_some]
                rw [← hqh0]; exact hq_vals k (by omega)
          have h2_bv : (2 : BitVec 64) = 2#64 := rfl
          have h3_bv : (3 : BitVec 64) = 3#64 := rfl
          have h4_bv : (4 : BitVec 64) = 4#64 := rfl
          have h5_bv : (5 : BitVec 64) = 5#64 := rfl
          have h1_32 : (1 : BitVec 32) = 1#32 := rfl
          have h5_eq : (ctrl_off + (5 : BitVec 64)).toNat = ctrl_off.toNat + 5 := by
            rw [h5_bv, ha5_n]
          have hm_rw : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R)
              m := by
            dsimp only [scr1]
            have hm' := hm
            simp only [h2_bv, h3_bv, h4_bv, h5_bv, h1_32] at hm'
            dsimp only [bkt, qidx, qh, ql] at hinq_bkt_n hq_pos_n ⊢
            rw [hinq_bkt_n, hq_pos_n] at hm'
            rw [← ha5_n]
            exact hm'
          exact hJ2 () m ⟨scr1, hscr1_len, Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay1⟩,
            fun o1 b1 i1 q1 hl1 => by
              obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := congCtrlLayout_unique hl1 hlay_orig
              exact ⟨by dsimp [scr1]; rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  getElem?_eq_some_of_getD (by omega) hs0],
                by dsimp [scr1]; rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  getElem?_eq_some_of_getD (by omega) hs1],
                by dsimp [scr1]; rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  getElem?_eq_some_of_getD (by omega) hs2],
                by dsimp [scr1]; rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  getElem?_eq_some_of_getD (by omega) hs3],
                by dsimp [scr1]; rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
                by dsimp [scr1]; rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  getElem?_eq_some_of_getD (by omega) hs6],
                by dsimp [scr1]; rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  getElem?_eq_some_of_getD (by omega) hs7],
                fun idx h5 hq_out hinq_out => by
                  dsimp only [scr1]
                  rw [List.getElem?_set_ne h5.symm,
                    List.getElem?_set_ne (fun h => hq_out ⟨by omega, by omega⟩),
                    List.getElem?_set_ne (fun h => hinq_out ⟨by omega, by omega⟩)]⟩,
            hm_rw⟩
        · c0_hstraight!
          exact hJ2 () m0 ⟨s.scratch.scratch_buf, hscrl, hqctx, fun o1 b1 i1 q1 hl1 => by
            obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := congCtrlLayout_unique hl1 hlay_orig
            exact ⟨getElem?_eq_some_of_getD (by omega) hs0,
              getElem?_eq_some_of_getD (by omega) hs1,
              getElem?_eq_some_of_getD (by omega) hs2,
              getElem?_eq_some_of_getD (by omega) hs3,
              rfl, getElem?_eq_some_of_getD (by omega) hs6,
              getElem?_eq_some_of_getD (by omega) hs7, fun _ _ _ _ => rfl⟩,
            hm0⟩
      · c0_hstraight!
        exact hJ () m0 ⟨s.scratch.scratch_buf, hscrl, hqctx, fun o1 b1 i1 q1 hl1 => by
          obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := congCtrlLayout_unique hl1 hlay_orig
          exact ⟨getElem?_eq_some_of_getD (by omega) hs0,
            getElem?_eq_some_of_getD (by omega) hs1,
            getElem?_eq_some_of_getD (by omega) hs2,
            getElem?_eq_some_of_getD (by omega) hs3,
            rfl, getElem?_eq_some_of_getD (by omega) hs6,
            getElem?_eq_some_of_getD (by omega) hs7, fun _ _ _ _ => rfl⟩,
          hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
