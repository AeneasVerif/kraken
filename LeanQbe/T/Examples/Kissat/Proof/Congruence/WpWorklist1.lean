/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpWorklist0
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Worklist WP Proof (`full_cong_worklist`)

Canonical `Func.wp` proof for `full_cong_worklist` (`Spec.fullCongWorklistSpec`) over
dynamic power-of-2 occurrence buckets (`occ_bkt ≤ 1,048,576`), 3-word occurrence nodes
`(g, raw_lit, nxt)`, and growing/flushing hash table (`ht_sz ≤ 1,048,576`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

/-! ## 2. Sub-Expression WP Helpers -/

private def wl_pushsExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reprPtr scrPtr : V i64) (occ_u : V i32) (bkt_64 occ_end0 g : V i64) (arity : V i32)
    (Jocc : L [i64]) : Expr V L rs :=
  .group (sig := [[i64, i32]]) (fun Js => .cons (fun p =>
    .let_ ⟨.cmp .ult i32 .bool rfl, (.var p.snd.fst, (.var arity, ()))⟩ fun p_72 =>
    .jnz (.var p_72.fst) (
      .let_ ⟨.add i64, (.var g, (.imm 2, ()))⟩ fun p1 =>
      .let_ ⟨.zext 32 64, (.var p.snd.fst, ())⟩ fun p2 =>
      .let_ ⟨.add i64, (.var p1.fst, (.var p2.fst, ()))⟩ fun p3 =>
      .let_ ⟨.mul i64, (.var p3.fst, (.imm 4, ()))⟩ fun p4 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var p4.fst, ()))⟩ fun p5 =>
      .load i32 (.var p5.fst) fun ld_12 =>
      .call (as := [i64, i32]) (bs := [i32]) "full_cong_find" (.var reprPtr, (.var ld_12, ()))
        fun p_78 =>
      .let_ ⟨.lshr i32, (.var p_78.fst, (.imm 1, ()))⟩ fun p_79 =>
      .let_ ⟨.sub i32, (.var occ_u, (.imm 1, ()))⟩ fun p_80 =>
      .let_ ⟨.and i32, (.var p_79.fst, (.var p_80.fst, ()))⟩ fun p_81 =>
      .let_ ⟨.mul i64, (.var p.fst, (.imm 4, ()))⟩ fun q1 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var q1.fst, ()))⟩ fun q2 =>
      .let_ ⟨.trunc 64 32, (.var g, ())⟩ fun q3 =>
      .store (t := i32) (.var q3.fst) (.var q2.fst) (
      .let_ ⟨.add i64, (.var p.fst, (.imm 1, ()))⟩ fun q4 =>
      .let_ ⟨.mul i64, (.var q4.fst, (.imm 4, ()))⟩ fun q5 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var q5.fst, ()))⟩ fun q6 =>
      .store (t := i32) (.var ld_12) (.var q6.fst) (
      .let_ ⟨.add i64, (.var p.fst, (.imm 2, ()))⟩ fun r1 =>
      .let_ ⟨.mul i64, (.var r1.fst, (.imm 4, ()))⟩ fun r2 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var r2.fst, ()))⟩ fun r3 =>
      .let_ ⟨.zext 32 64, (.var p_81.fst, ())⟩ fun r4 =>
      .let_ ⟨.add i64, (.var bkt_64, (.var r4.fst, ()))⟩ fun r5 =>
      .let_ ⟨.mul i64, (.var r5.fst, (.imm 4, ()))⟩ fun r6 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var r6.fst, ()))⟩ fun r7 =>
      .load i32 (.var r7.fst) fun ld_13 => .store (t := i32) (.var ld_13) (.var r3.fst) (
      .let_ ⟨.zext 32 64, (.var p_81.fst, ())⟩ fun s1 =>
      .let_ ⟨.add i64, (.var bkt_64, (.var s1.fst, ()))⟩ fun s2 =>
      .let_ ⟨.mul i64, (.var s2.fst, (.imm 4, ()))⟩ fun s3 =>
      .let_ ⟨.add i64, (.var scrPtr, (.var s3.fst, ()))⟩ fun s4 =>
      .let_ ⟨.trunc 64 32, (.var p.fst, ())⟩ fun s5 =>
      .store (t := i32) (.var s5.fst) (.var s4.fst) (
      .let_ ⟨.add i64, (.var p.fst, (.imm 3, ()))⟩ fun t1 =>
      .let_ ⟨.add i32, (.var p.snd.fst, (.imm 1, ()))⟩ fun t2 =>
      .jump Js.fst (.var t1.fst, (.var t2.fst, ()))))))
    ) (.jump Jocc (.var p.fst, ()))
  ) .nil) fun Js => .jump Js.fst (.var occ_end0, (.imm 0, ()))

private theorem wl_pushs_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st_p0 : FullState} {m_p0 : Mem 64} {occ_end g : BitVec 64}
    {mw1 : BitVec 32} {R : Mem 64 → Prop} {Jocc : Cont [i64]} {Q : Post [i64]} {X : XPost}
    (hc_cap : ctrl_off < c.scratch_cap)
    (ho_pos : 0 < occ_bkt) (hopow : ∃ p, 1 ≤ p ∧ p ≤ 20 ∧ occ_bkt = 2 ^ p)
    (hg_lt : g.toNat < g_len) (hgat : CongGateAt congAndArityMax F_cur cv0 scr0 g_len g.toNat)
    (hscr0_g1 : scr0[g.toNat + 1]? = some mw1)
    (hocc_fit : occ_end.toNat + (1 + congGateArity mw1) * 3 ≤ ctrl_off)
    (hoe_lo : g_len ≤ occ_end.toNat) (hoe_m3 : (occ_end.toNat - g_len) % 3 = 0)
    (hoe3_n : (occ_end + 3#64).toNat = occ_end.toNat + 3)
    (hok_p0 : WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz (occ_end.toNat + 3) scr0 st_p0)
    (hm_p0 : (FullMem c st_p0 ⋆ R) m_p0)
    (hJocc : ∀ (occ_e' : BitVec 64) me,
      (∃ se : FullState, g_len ≤ occ_e'.toNat ∧ occ_e'.toNat ≤ ctrl_off ∧
        (occ_e'.toNat - g_len) % 3 = 0 ∧
        WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
          ht_off ht_sz occ_e'.toNat scr0 se ∧ (FullMem c se ⋆ R) me) → Jocc (occ_e', ()) me) :
    wp Γ Q X (wl_pushsExpr c.pRepr c.pScratchBuf (BitVec.ofNat 32 occ_bkt)
      (BitVec.ofNat 64 bkt_off) (occ_end + 3#64) g
      (BitVec.ofNat 32 (congGateArity mw1)) Jocc) m_p0 := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ⟨_, mword, _, hg1, _, hbd_g, _, _, hrhs, _⟩ := hgat
  have hmw : mword = mw1 := Option.some.inj (hg1.symm.trans hscr0_g1)
  let arity := BitVec.ofNat 32 (congGateArity mw1)
  have har_n : arity.toNat = congGateArity mw1 :=
    bv32_ofNat_toNat_lt (by have := hbd_g; rw [← hmw]; omega)
  unfold wl_pushsExpr; c0_hsteps_nogrp
  refine wp_loop_inv
    (Inv := fun (occ_s, s_i, ()) ms => ∃ st_s : FullState,
      s_i.toNat ≤ arity.toNat ∧ g_len ≤ occ_s.toNat ∧
      occ_s.toNat + 3 * (arity.toNat - s_i.toNat) ≤ ctrl_off ∧
      (occ_s.toNat - g_len) % 3 = 0 ∧
      WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
        ht_off ht_sz occ_s.toNat scr0 st_s ∧ (FullMem c st_s ⋆ R) ms)
    (μ := fun (_, s_i, ()) _ => arity.toNat - s_i.toNat)
    (fun Js hJs => by
      c0_hsteps!; exact hJs (occ_end + 3#64, 0#32, ()) m_p0 ⟨_, Nat.zero_le _, by omega,
        by rw [hoe3_n, har_n]; omega, by rw [hoe3_n]; omega, hoe3_n ▸ hok_p0, hm_p0⟩)
    (fun Js ⟨occ_s, s_i, ⟨⟩⟩ ms ⟨st_s, hs_le, hoes_lo, hoes_cap, hoes_m3, hok_s, hms⟩ ihs => ?_)
  have ⟨hdw_s, hcv_s, hfl_s, hrepr_s, hlay_s, hpref_s, hht_s, hocc_s⟩ := hok_s
  have hscrl_s := hdw_s.1.scratch_ok.scratch_buf_len; have hg_co := hlay_s.2.2.1
  c0_hsteps_nogrp; c0_hsplit
  · have hs_lt : s_i.toNat < arity.toNat := hc
    have hsi_mw : s_i.toNat < congGateArity mword := by rw [hmw, ← har_n]; exact hs_lt
    obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs s_i.toNat hsi_mw
    have hg2s_n : (g + (2 : BitVec 64) + BitVec.setWidth 64 s_i).toNat =
        g.toNat + 2 + s_i.toNat := by bv_omega
    have hg2s_arr : (g + (2 : BitVec 64) + BitVec.setWidth 64 s_i).toNat <
        st_s.scratch.scratch_buf.length := by rw [hg2s_n, hscrl_s]; omega
    have hs_g2s : st_s.scratch.scratch_buf[(g + (2 : BitVec 64) +
        BitVec.setWidth 64 s_i).toNat]'hg2s_arr = rv := by
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem hg2s_arr, hg2s_n, hpref_s _ (by omega), hrv_get]
    c0_hsteps!; c0_hcall hFind
    refine ⟨F_cur, 2 * cv0, st_s.core.repr, ArrayField.repr.rest c st_s ⋆ R,
      hcv_s ▸ hrepr_s, by rw [hs_g2s]; exact hrv_lt, focus_full_repr hms,
      fun rr repr_r mr hrl_r hrepr_r _ _ _ hmr => ?_⟩
    let st_r : FullState := { st_s with core := { st_s.core with repr := repr_r } }
    have hmr' : (FullMem c st_r ⋆ R) mr := unfocus_full_repr hmr
    have hokr := wlStOk_with_repr hok_s (hrl_r.trans hdw_s.1.core_ok.repr_len) hrepr_r
    let bs := (rr >>> (1 : BitVec 32)) &&& (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))
    have hbs_lt : bs.toNat < occ_bkt := by
      dsimp only [bs]; rw [show (1 : BitVec 32) = 1#32 from rfl,
        cong_and_sub1_u32_eq_mod hopow]; exact Nat.mod_lt _ ho_pos
    have hlay_r := hlay_s; rcases hlay_r with ⟨_, _, _, _, _, _, _, _, _, _, _, ho_max, _, _,
      hcq, hqi, hib, hbh, hht_cap, _⟩
    unfold congOccBktMax at ho_max
    have hbs_n : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 bs).toNat = bkt_off + bs.toNat := by
      bv_omega
    have hoes1_n : (occ_s + (1 : BitVec 64)).toNat = occ_s.toNat + 1 := by bv_omega
    have hoes2_n : (occ_s + (2 : BitVec 64)).toNat = occ_s.toNat + 2 := by bv_omega
    have hoes3_n : (occ_s + (3 : BitVec 64)).toNat = occ_s.toNat + 3 := by bv_omega
    have hs1_n : (s_i + (1 : BitVec 32)).toNat = s_i.toNat + 1 := by bv_omega
    have hgn_32 : (BitVec.setWidth 32 g).toNat = g.toNat := by bv_omega
    have hocc_32 : (BitVec.setWidth 32 occ_s).toNat = occ_s.toNat := by bv_omega
    have hpres := wl_push3_pres hlay_s hscrl_s hpref_s (hcv_s ▸ hht_s) hocc_s
      (by omega) hbs_lt (hgn_32 ▸ hg_lt) (hgn_32 ▸ hgat) hrv_lt
    have ho0_arr : occ_s.toNat < st_r.scratch.scratch_buf.length := by
      change _ < st_s.scratch.scratch_buf.length; rw [hscrl_s]; omega
    have ho1_arr : (occ_s + (1 : BitVec 64)).toNat <
        (st_r.scratch.scratch_buf.set occ_s.toNat (BitVec.setWidth 32 g)).length := by
      rw [List.length_set, hoes1_n]; change _ < st_s.scratch.scratch_buf.length; rw [hscrl_s]; omega
    have ho2_arr : (occ_s + (2 : BitVec 64)).toNat <
        ((st_r.scratch.scratch_buf.set occ_s.toNat (BitVec.setWidth 32 g)).set
          (occ_s + (1 : BitVec 64)).toNat rv).length := by
      simp only [List.length_set]; rw [hoes2_n]
      change _ < st_s.scratch.scratch_buf.length; rw [hscrl_s]; omega
    have hbs_r_arr : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 bs).toNat <
        ((st_r.scratch.scratch_buf.set occ_s.toNat (BitVec.setWidth 32 g)).set
          (occ_s + (1 : BitVec 64)).toNat rv).length := by
      simp only [List.length_set]; rw [hbs_n]
      change _ < st_s.scratch.scratch_buf.length; rw [hscrl_s]; omega
    have hbs_arr : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 bs).toNat <
        (((st_r.scratch.scratch_buf.set occ_s.toNat (BitVec.setWidth 32 g)).set
          (occ_s + (1 : BitVec 64)).toNat rv).set (occ_s + (2 : BitVec 64)).toNat
          (((st_r.scratch.scratch_buf.set occ_s.toNat (BitVec.setWidth 32 g)).set
            (occ_s + (1 : BitVec 64)).toNat rv)[
              (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 bs).toNat]'hbs_r_arr)).length := by
      simp only [List.length_set]; rw [hbs_n]
      change _ < st_s.scratch.scratch_buf.length; rw [hscrl_s]; omega
    rw [hs_g2s]
    have hmr_scr := focus_full_scratch_buf hmr'; c0_hsteps!
    have hhm : (array (t := i32) c.pScratchBuf
        ((((st_s.scratch.scratch_buf.set occ_s.toNat (BitVec.ofNat 32 g.toNat)).set
          (occ_s.toNat + 1) rv).set (occ_s.toNat + 2)
          (st_s.scratch.scratch_buf[bkt_off + bs.toNat]?.getD 0xFFFFFFFF#32)).set
          (bkt_off + bs.toNat) (BitVec.ofNat 32 occ_s.toNat)) ⋆
        (ArrayField.scratch_buf.rest c st_r ⋆ R)) m := by
      have hbs_eq' : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64
          (rr >>> OfNat.ofNat 1 &&& BitVec.ofNat 32 occ_bkt - 1)).toNat =
          bkt_off + bs.toNat := hbs_n
      have h_arr' : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64
          (rr >>> OfNat.ofNat 1 &&& BitVec.ofNat 32 occ_bkt - 1)).toNat <
          ((st_r.scratch.scratch_buf.set occ_s.toNat (BitVec.setWidth 32 g)).set
            (occ_s + (1 : BitVec 64)).toNat rv).length := by
        simp only [List.length_set]; rw [hbs_eq', hscrl_s]; omega
      have hb_get : (((st_r.scratch.scratch_buf.set occ_s.toNat
          (BitVec.setWidth 32 g)).set (occ_s + (1 : BitVec 64)).toNat rv)[
            (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64
              (rr >>> OfNat.ofNat 1 &&& BitVec.ofNat 32 occ_bkt - 1)).toNat]'h_arr') =
          st_s.scratch.scratch_buf[bkt_off + bs.toNat]?.getD 0xFFFFFFFF#32 := by
        rw [List.getElem_set_ne (by rw [hbs_eq', hoes1_n]; omega),
          List.getElem_set_ne (by rw [hbs_eq']; omega),
          list_getElem_congr hbs_eq' _ (by rw [hscrl_s]; omega),
          List.getElem?_eq_getElem (by rw [hscrl_s]; omega), Option.getD_some]
      have hg_32 : BitVec.setWidth 32 g = BitVec.ofNat 32 g.toNat := by bv_omega
      have hb_32 : BitVec.setWidth 32 occ_s = BitVec.ofNat 32 occ_s.toNat := by bv_omega
      rw [hb_get] at hm; rw [hbs_eq', hoes1_n, hoes2_n, hg_32, hb_32] at hm; exact hm
    have hok_ps := wlStOk_with_scr hokr hpres.1 hpres.2.1 hpres.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2
    exact ihs (occ_s + (3 : BitVec 64), s_i + (1 : BitVec 32), ()) m
      (by dsimp only; omega) ⟨_, by rw [hs1_n]; omega, by rw [hoes3_n]; omega,
        by rw [hoes3_n, hs1_n]; omega, by rw [hoes3_n]; omega,
        by rw [hoes3_n]; exact hok_ps, unfocus_full_scratch_buf hhm⟩
  · c0_hsteps!; exact hJocc occ_s ms ⟨st_s, hoes_lo, by omega, hoes_m3, hok_s, hms⟩

private def wl_push_gateExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reprPtr scrPtr : V i64) (occ_u : V i32) (bkt_64 occ_end g : V i64) (arity : V i32)
    (Jocc : L [i64]) : Expr V L rs :=
  .let_ ⟨.mul i64, (.var g, (.imm 4, ()))⟩ fun p1 =>
  .let_ ⟨.add i64, (.var scrPtr, (.var p1.fst, ()))⟩ fun p2 =>
  .load i32 (.var p2.fst) fun raw_l =>
  .call (as := [i64, i32]) (bs := [i32]) "full_cong_find" (.var reprPtr, (.var raw_l, ()))
    fun rl =>
  .let_ ⟨.lshr i32, (.var rl.fst, (.imm 1, ()))⟩ fun p3 =>
  .let_ ⟨.sub i32, (.var occ_u, (.imm 1, ()))⟩ fun p4 =>
  .let_ ⟨.and i32, (.var p3.fst, (.var p4.fst, ()))⟩ fun b0 =>
  .let_ ⟨.mul i64, (.var occ_end, (.imm 4, ()))⟩ fun q1 =>
  .let_ ⟨.add i64, (.var scrPtr, (.var q1.fst, ()))⟩ fun q2 =>
  .let_ ⟨.trunc 64 32, (.var g, ())⟩ fun q3 =>
  .store (t := i32) (.var q3.fst) (.var q2.fst) (
  .let_ ⟨.add i64, (.var occ_end, (.imm 1, ()))⟩ fun q4 =>
  .let_ ⟨.mul i64, (.var q4.fst, (.imm 4, ()))⟩ fun q5 =>
  .let_ ⟨.add i64, (.var scrPtr, (.var q5.fst, ()))⟩ fun q6 =>
  .store (t := i32) (.var raw_l) (.var q6.fst) (
  .let_ ⟨.add i64, (.var occ_end, (.imm 2, ()))⟩ fun r1 =>
  .let_ ⟨.mul i64, (.var r1.fst, (.imm 4, ()))⟩ fun r2 =>
  .let_ ⟨.add i64, (.var scrPtr, (.var r2.fst, ()))⟩ fun r3 =>
  .let_ ⟨.zext 32 64, (.var b0.fst, ())⟩ fun r4 =>
  .let_ ⟨.add i64, (.var bkt_64, (.var r4.fst, ()))⟩ fun r5 =>
  .let_ ⟨.mul i64, (.var r5.fst, (.imm 4, ()))⟩ fun r6 =>
  .let_ ⟨.add i64, (.var scrPtr, (.var r6.fst, ()))⟩ fun r7 =>
  .load i32 (.var r7.fst) fun ld => .store (t := i32) (.var ld) (.var r3.fst) (
  .let_ ⟨.zext 32 64, (.var b0.fst, ())⟩ fun s1 =>
  .let_ ⟨.add i64, (.var bkt_64, (.var s1.fst, ()))⟩ fun s2 =>
  .let_ ⟨.mul i64, (.var s2.fst, (.imm 4, ()))⟩ fun s3 =>
  .let_ ⟨.add i64, (.var scrPtr, (.var s3.fst, ()))⟩ fun s4 =>
  .let_ ⟨.trunc 64 32, (.var occ_end, ())⟩ fun s5 =>
  .store (t := i32) (.var s5.fst) (.var s4.fst) (
  .let_ ⟨.add i64, (.var occ_end, (.imm 3, ()))⟩ fun t1 =>
  wl_pushsExpr reprPtr scrPtr occ_u bkt_64 t1.fst g arity Jocc))))

private theorem wl_push_gate_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {sj : FullState} {mj : Mem 64} {occ_end g : BitVec 64}
    {arity mw1 : BitVec 32} {R : Mem 64 → Prop} {Jocc : Cont [i64]} {Q : Post [i64]} {X : XPost}
    (hc_cap : ctrl_off < c.scratch_cap)
    (ho_pos : 0 < occ_bkt) (hopow : ∃ p, 1 ≤ p ∧ p ≤ 20 ∧ occ_bkt = 2 ^ p)
    (hg_lt : g.toNat < g_len) (hgat : CongGateAt congAndArityMax F_cur cv0 scr0 g_len g.toNat)
    (hscr0_g1 : scr0[g.toNat + 1]? = some mw1) (har_eq : arity.toNat = congGateArity mw1)
    (hfit : occ_end.toNat + (1 + arity.toNat) * 3 ≤ ctrl_off)
    (hoe_lo : g_len ≤ occ_end.toNat) (hoe_m3 : (occ_end.toNat - g_len) % 3 = 0)
    (hokj : WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end.toNat scr0 sj)
    (hmj : (FullMem c sj ⋆ R) mj)
    (hJocc : ∀ (occ_e' : BitVec 64) me,
      (∃ se : FullState, g_len ≤ occ_e'.toNat ∧ occ_e'.toNat ≤ ctrl_off ∧
        (occ_e'.toNat - g_len) % 3 = 0 ∧
        WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
          ht_off ht_sz occ_e'.toNat scr0 se ∧ (FullMem c se ⋆ R) me) → Jocc (occ_e', ()) me) :
    wp Γ Q X (wl_push_gateExpr c.pRepr c.pScratchBuf (BitVec.ofNat 32 occ_bkt)
      (BitVec.ofNat 64 bkt_off) occ_end g arity Jocc) mj := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ⟨hdwj, hcvj, hflj, hreprj, hlay_j, hprefj, hhtj, hocc_j⟩ := hokj
  have hscrl_j := hdwj.1.scratch_ok.scratch_buf_len; have hg_co := hlay_j.2.2.1
  have ⟨lhs0, _, hscr0_g, _, hlhs0_lt, _, _, _, _, _⟩ := hgat
  have hg_arr_j : g.toNat < sj.scratch.scratch_buf.length := by omega
  have hs_g_j : sj.scratch.scratch_buf[g.toNat]'hg_arr_j = lhs0 := by
    apply Option.some.inj; rw [← List.getElem?_eq_getElem hg_arr_j, hprefj _ hg_lt, hscr0_g]
  unfold wl_push_gateExpr; c0_hsteps!; c0_hcall hFind
  refine ⟨F_cur, 2 * cv0, sj.core.repr, ArrayField.repr.rest c sj ⋆ R,
    hcvj ▸ hreprj, by rw [hs_g_j]; exact hlhs0_lt,
    focus_full_repr hmj, fun rl repr_r mi hrl_r hrepr_r _ _ _ hmi => ?_⟩
  let st_r : FullState := { sj with core := { sj.core with repr := repr_r } }
  have hmi' : (FullMem c st_r ⋆ R) mi := unfocus_full_repr hmi
  have hokr := wlStOk_with_repr hokj (hrl_r.trans hdwj.1.core_ok.repr_len) hrepr_r
  let b0 := (rl >>> (1 : BitVec 32)) &&& (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))
  have hb0_lt : b0.toNat < occ_bkt := by
    dsimp only [b0]; rw [show (1 : BitVec 32) = 1#32 from rfl, cong_and_sub1_u32_eq_mod hopow]
    exact Nat.mod_lt _ ho_pos
  have hlay_r := hlay_j; rcases hlay_r with ⟨_, _, _, _, _, _, _, _, _, _, _, ho_max, _, _,
    hcq, hqi, hib, hbh, hht_cap, _⟩
  unfold congOccBktMax at ho_max
  have hoe1_n : (occ_end + (1 : BitVec 64)).toNat = occ_end.toNat + 1 := by bv_omega
  have hoe2_n : (occ_end + (2 : BitVec 64)).toNat = occ_end.toNat + 2 := by bv_omega
  have hoe3_n : (occ_end + 3#64).toNat = occ_end.toNat + 3 := by bv_omega
  have hb0_n : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 b0).toNat = bkt_off + b0.toNat := by
    bv_omega
  have hgn_32 : (BitVec.setWidth 32 g).toNat = g.toNat := by bv_omega
  have hpres := wl_push3_pres hlay_j hscrl_j hprefj (hcvj ▸ hhtj) hocc_j (by omega) hb0_lt
    (hgn_32 ▸ hg_lt) (hgn_32 ▸ hgat) hlhs0_lt
  have ho0_arr : occ_end.toNat < st_r.scratch.scratch_buf.length := by
    change _ < sj.scratch.scratch_buf.length; rw [hscrl_j]; omega
  have ho1_arr : (occ_end + (1 : BitVec 64)).toNat <
      (st_r.scratch.scratch_buf.set occ_end.toNat (BitVec.setWidth 32 g)).length := by
    rw [List.length_set, hoe1_n]; change _ < sj.scratch.scratch_buf.length; rw [hscrl_j]; omega
  have ho2_arr : (occ_end + (2 : BitVec 64)).toNat <
      ((st_r.scratch.scratch_buf.set occ_end.toNat (BitVec.setWidth 32 g)).set
        (occ_end + (1 : BitVec 64)).toNat lhs0).length := by
    simp only [List.length_set]; rw [hoe2_n]
    change _ < sj.scratch.scratch_buf.length; rw [hscrl_j]; omega
  have hb0_r_arr : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 b0).toNat <
      ((st_r.scratch.scratch_buf.set occ_end.toNat (BitVec.setWidth 32 g)).set
        (occ_end + (1 : BitVec 64)).toNat lhs0).length := by
    simp only [List.length_set]; rw [hb0_n]
    change _ < sj.scratch.scratch_buf.length; rw [hscrl_j]; omega
  have hb0_arr : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 b0).toNat <
      (((st_r.scratch.scratch_buf.set occ_end.toNat (BitVec.setWidth 32 g)).set
        (occ_end + (1 : BitVec 64)).toNat lhs0).set (occ_end + (2 : BitVec 64)).toNat
        (((st_r.scratch.scratch_buf.set occ_end.toNat (BitVec.setWidth 32 g)).set
          (occ_end + (1 : BitVec 64)).toNat lhs0)[
            (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 b0).toNat]'hb0_r_arr)).length := by
    simp only [List.length_set]; rw [hb0_n]
    change _ < sj.scratch.scratch_buf.length; rw [hscrl_j]; omega
  rw [hs_g_j]
  have hmi_scr := focus_full_scratch_buf hmi'; c0_hsteps!
  have hhm : (array (t := i32) c.pScratchBuf
      ((((sj.scratch.scratch_buf.set occ_end.toNat
        (BitVec.ofNat 32 g.toNat)).set (occ_end.toNat + 1) lhs0).set
        (occ_end.toNat + 2) (sj.scratch.scratch_buf[bkt_off + b0.toNat]?.getD 0xFFFFFFFF#32)).set
        (bkt_off + b0.toNat) (BitVec.ofNat 32 occ_end.toNat)) ⋆
      (ArrayField.scratch_buf.rest c st_r ⋆ R)) m := by
    have hb0_eq' : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64
        (rl >>> OfNat.ofNat 1 &&& BitVec.ofNat 32 occ_bkt - 1)).toNat =
        bkt_off + b0.toNat := hb0_n
    have h_arr' : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64
        (rl >>> OfNat.ofNat 1 &&& BitVec.ofNat 32 occ_bkt - 1)).toNat <
        ((st_r.scratch.scratch_buf.set occ_end.toNat (BitVec.setWidth 32 g)).set
          (occ_end + (1 : BitVec 64)).toNat lhs0).length := by
      simp only [List.length_set]; rw [hb0_eq']
      change _ < sj.scratch.scratch_buf.length; rw [hscrl_j]; omega
    have hb_get : (((st_r.scratch.scratch_buf.set occ_end.toNat
        (BitVec.setWidth 32 g)).set (occ_end + (1 : BitVec 64)).toNat lhs0)[
          (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64
            (rl >>> OfNat.ofNat 1 &&& BitVec.ofNat 32 occ_bkt - 1)).toNat]'h_arr') =
        sj.scratch.scratch_buf[bkt_off + b0.toNat]?.getD 0xFFFFFFFF#32 := by
      rw [List.getElem_set_ne (by rw [hb0_eq', hoe1_n]; omega),
        List.getElem_set_ne (by rw [hb0_eq']; omega),
        list_getElem_congr hb0_eq' _ (by rw [hscrl_j]; omega),
        List.getElem?_eq_getElem (by rw [hscrl_j]; omega), Option.getD_some]
    have hg_32 : BitVec.setWidth 32 g = BitVec.ofNat 32 g.toNat := by bv_omega
    have hoe_32 : BitVec.setWidth 32 occ_end = BitVec.ofNat 32 occ_end.toNat := by bv_omega
    rw [hb_get] at hm; rw [hb0_eq', hoe1_n, hoe2_n, hg_32, hoe_32] at hm; exact hm
  have hok_p0 := wlStOk_with_scr hokr hpres.1 hpres.2.1 hpres.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2
  have har_32 : arity = BitVec.ofNat 32 (congGateArity mw1) := by bv_omega
  rw [har_32]
  exact wl_pushs_wp Γ hFind hc_cap ho_pos hopow hg_lt hgat hscr0_g1 (by rw [← har_eq]; exact hfit)
    hoe_lo hoe_m3 hoe3_n (hoe3_n ▸ hok_p0) (unfocus_full_scratch_buf hhm) hJocc

private def wl_rehashExpr {V : Ty → Type} {L : List Ty → Type}
    (h scrPtr tlim htOff htSz gLen ctrlOff rehashes ticks_n : V i64) (ep : V i32) (dg : V .bool)
    (Jreh : L [i64, i64, i64, i64, i64]) : Expr V L [i64] :=
  .group (sig := [[i64, i64]]) (fun _Js_7 => .cons (fun p_83 =>
    .group (sig := [[i64]]) (fun Js_8 => .cons (fun p_84 =>
      .let_ ⟨.cmp .ult i64 .bool rfl, (.var p_84.fst, (.var p_83.fst, ()))⟩ fun p_85 =>
      .jnz (.var p_85.fst) (
        .let_ ⟨.add i64, (.var htOff, (.var p_84.fst, ()))⟩ fun p1 =>
        .let_ ⟨.mul i64, (.var p1.fst, (.imm 4, ()))⟩ fun p2 =>
        .let_ ⟨.add i64, (.var scrPtr, (.var p2.fst, ()))⟩ fun p3 =>
        .store (t := i32) (.imm 4294967295) (.var p3.fst) (
        .let_ ⟨.add i64, (.var p_84.fst, (.imm 1, ()))⟩ fun p4 => .jump Js_8.fst (.var p4.fst, ()))
      ) (
        .let_ ⟨.add i64, (.var h, (.imm 1144, ()))⟩ fun p_86 =>
        .store (t := i64) (.imm 0) (.var p_86.fst) (
        .group (sig := [[i64, i64]]) (fun Js_9 => .cons (fun p_87 =>
          .let_ ⟨.cmp .ult i64 .bool rfl, (.var p_87.snd.fst, (.var gLen, ()))⟩ fun p_88 =>
          .jnz (.var p_88.fst) (
            .let_ ⟨.add i64, (.var h, (.imm 1024, ()))⟩ fun p_89 =>
            .load i64 (.var p_89.fst) fun ld_14 =>
            .let_ ⟨.cmp .eq i64 .bool rfl, (.var ld_14, (.imm 0, ()))⟩ fun p_90 =>
            .jnz (.var p_90.fst) (
              .let_ ⟨.cmp .ult i64 .bool rfl, (.var p_87.fst, (.var tlim, ()))⟩ fun p_91 =>
              .jnz (.var p_91.fst) (
                .let_ ⟨.add i64, (.var p_87.snd.fst, (.imm 1, ()))⟩ fun p1 =>
                .let_ ⟨.mul i64, (.var p1.fst, (.imm 4, ()))⟩ fun p2 =>
                .let_ ⟨.add i64, (.var scrPtr, (.var p2.fst, ()))⟩ fun p3 =>
                .load i32 (.var p3.fst) fun ld =>
                .group (sig := [[i32]]) (fun _Js => .cons (fun p_95 =>
                  .let_ ⟨.add i64, (.var p_87.fst, (.imm 1, ()))⟩ fun p_96 =>
                  .call (as := [i64, i64, i64, i64, i32, i64]) (bs := [i64]) "full_cong_eval_gate"
                    (.var h, (.var p_87.snd.fst, (.var htOff, (.var p_83.fst,
                      (.var ep, (.var ctrlOff, ())))))) fun p =>
                  .let_ ⟨.and i64, (.var p.fst, (.imm 2, ()))⟩ fun p =>
                  .let_ ⟨.cmp .ne i64 .bool rfl, (.var p.fst, (.imm 0, ()))⟩ fun p =>
                  .jnz (.var p.fst) (.ret (.imm 20, ())) (
                    .let_ ⟨.add i64, (.var p_87.snd.fst, (.imm 2, ()))⟩ fun p =>
                    .let_ ⟨.zext 32 64, (.var p_95.fst, ())⟩ fun p_97 =>
                    .let_ ⟨.add i64, (.var p.fst, (.var p_97.fst, ()))⟩ fun p =>
                    .jump Js_9.fst (.var p_96.fst, (.var p.fst, ())))
                ) .nil) fun Js =>
                .let_ ⟨.lshr i32, (.var ld, (.imm 28, ()))⟩ fun p =>
                .let_ ⟨.cmp .eq i32 .bool rfl, (.var p.fst, (.imm 3, ()))⟩ fun p =>
                .jnz (.var p.fst)
                  (.let_ ⟨.and i32, (.var ld, (.imm 268435455, ()))⟩ fun p =>
                    .jump Js.fst (.var p.fst, ()))
                  (.let_ ⟨.and i32, (.var ld, (.imm 255, ()))⟩ fun p =>
                    .jump Js.fst (.var p.fst, ()))
              ) (.jump Jreh (.var p_83.fst, (.var p_84.fst, (.var p_87.fst,
                  (.var p_83.snd.fst, (.var p_87.snd.fst, ()))))))
            ) (.jump Jreh (.var p_83.fst, (.var p_84.fst, (.var p_87.fst,
                (.var p_83.snd.fst, (.var p_87.snd.fst, ()))))))
          ) (.jump Jreh (.var p_83.fst, (.var p_84.fst, (.var p_87.fst,
              (.var p_83.snd.fst, (.var p_87.snd.fst, ()))))))
        ) .nil) fun Js => .jump Js.fst (.var ticks_n, (.imm 0, ())))
      )
    ) .nil) fun Js => .jump Js.fst (.imm 0, ())
  ) .nil) fun Js => .jnz (.var dg) (
    .let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_83 =>
    .let_ ⟨.shl i64, (.var htSz, (.var p_83.fst, ()))⟩ fun p_84 =>
    .let_ ⟨.add i64, (.var ctrlOff, (.imm 7, ()))⟩ fun p =>
    .let_ ⟨.mul i64, (.var p.fst, (.imm 4, ()))⟩ fun p =>
    .let_ ⟨.add i64, (.var scrPtr, (.var p.fst, ()))⟩ fun p =>
    .let_ ⟨.trunc 64 32, (.var p_84.fst, ())⟩ fun p_85 =>
    .store (t := i32) (.var p_85.fst) (.var p.fst)
      (.jump Js.fst (.var p_84.fst, (.var rehashes, ())))
  ) (.let_ ⟨.add i64, (.var rehashes, (.imm 1, ()))⟩ fun p =>
     .jump Js.fst (.var htSz, (.var p.fst, ())))

private theorem wl_rehash_wp (Γ : Env)
    (hEval : Γ.Has "full_cong_eval_gate" Spec.fullCongEvalGateSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 occ_bkt bkt_off inq_off q_off ht_off occ_end : Nat}
    {ht_sz_o g_len ctrl_off tlim ticks_o rehashes_o ticks_n : BitVec 64} {ql ep : BitVec 32}
    {dg : Bool} {scr0 : List (BitVec 32)} {sa : FullState} {ma : Mem 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {Jreh : Cont [i64, i64, i64, i64, i64]}
    (hg_pos : 0 < g_len.toNat) (hht_pos : 0 < ht_sz_o.toNat)
    (hht_bnd : ht_sz_o.toNat < 2 ^ 30) (hht_max : ht_sz_o.toNat ≤ 2 * congHashMaxSz)
    (hg_ht_le : g_len.toNat ≤ ht_off) (hht_cap : ht_off + ht_sz_o.toNat ≤ c.scratch_cap)
    (hc_cap : ctrl_off.toNat < c.scratch_cap) (htlim_le : tlim.toNat ≤ 2 ^ 63 - 1)
    (htn_lt : ticks_n.toNat < tlim.toNat) (hta_lo : ticks_o.toNat ≤ ticks_n.toNat)
    (hta_eq : ticks_o.toNat = ticks_n.toNat → sa.core.inconsistent = 0#64 ∧
      (sa.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat)
    (hdg : dg = true →
      ht_sz_o.toNat < 1048576 ∧ ht_off + (ht_sz_o <<< 1#64).toNat ≤ c.scratch_cap)
    (hdf : dg = false → rehashes_o.toNat < 4) (hreh_le : rehashes_o.toNat ≤ 4)
    (hseq0 : CongGateSeqOk congAndArityMax F_cur cv0 scr0 g_len.toNat 0)
    (hoka : WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
      q_off ht_off ht_sz_o.toNat occ_end scr0 sa)
    (hma : (FullMem c sa ⋆ R) ma)
    (hQ : ∀ r s' m', FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = cv0 →
      s'.core.fuel = fuel0 → FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJreh : ∀ ys mb,
      (match ys with
        | (ht_sz_b, _i_b, ticks_b, reh_b, _g_b, ()) => ∃ sb : FullState,
          0 < ht_sz_b.toNat ∧ ht_sz_b.toNat ≤ 2 * congHashMaxSz ∧ ht_sz_b.toNat < 2 ^ 30 ∧
          ht_off + ht_sz_b.toNat ≤ c.scratch_cap ∧ reh_b.toNat ≤ 4 ∧
          ticks_o.toNat ≤ ticks_b.toNat ∧ ticks_b.toNat ≤ tlim.toNat ∧
          (ticks_o.toNat < ticks_b.toNat ∨ (sb.core.inconsistent = 0#64 ∧
            (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat)) ∧
          WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
            q_off ht_off ht_sz_b.toNat occ_end scr0 sb ∧ (FullMem c sb ⋆ R) mb) → Jreh ys mb) :
    wp Γ Q X (wl_rehashExpr c.hdr c.pScratchBuf tlim (BitVec.ofNat 64 ht_off)
      ht_sz_o g_len ctrl_off rehashes_o ticks_n ep dg Jreh) ma := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl_a := hoka.1.1.scratch_ok.scratch_buf_len
  have hho_n : (BitVec.ofNat 64 ht_off).toNat = ht_off := by bv_omega
  unfold wl_rehashExpr; c0_hsteps_nogrp
  refine wp_join_group
    (fun (ht_sz_c, reh_c, ()) m_c => ∃ sc : FullState,
      0 < ht_sz_c.toNat ∧ ht_sz_c.toNat ≤ 2 * congHashMaxSz ∧ ht_sz_c.toNat < 2 ^ 30 ∧
      ht_off + ht_sz_c.toNat ≤ c.scratch_cap ∧ reh_c.toNat ≤ 4 ∧
      FullDenseInvW c F0 F_cur sc ∧ sc.core.cur_vars = cv0 ∧ sc.core.fuel = fuel0 ∧
      FullCongReprInv F_cur (2 * cv0) sc.core.repr ∧
      CongCtrlLayout c sc.scratch.scratch_buf g_len.toNat ctrl_off.toNat occ_bkt bkt_off
        inq_off q_off ht_off ht_sz_c.toNat ∧
      (∀ idx < g_len.toNat, sc.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      CongOccNodesOk F_cur cv0 g_len.toNat occ_end ctrl_off.toNat bkt_off occ_bkt scr0
        sc.scratch.scratch_buf ∧
      (ticks_o.toNat = ticks_n.toNat → sc.core.inconsistent = 0#64 ∧
        (sc.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
      (FullMem c sc ⋆ R) m_c)
    (fun Js_7 ⟨ht_sz_c, reh_c, ⟨⟩⟩ m_c
      ⟨sc, hht_pos_c, hht_max_c, hht_bnd_c, hht_cap_c, hreh_c, hdw_c, hcv_c, hfl_c,
        hrepr_c, hlay_c, hpref_c, hocc_c, hta_c, hm_c⟩ => ?_)
    (fun Js_7 hJs_7 => ?_)
  · c0_hsteps_nogrp
    refine wp_loop_inv
      (Inv := fun (ih, ()) mh => ∃ sh : FullState,
        ih.toNat ≤ ht_sz_c.toNat ∧
        sh = { sc with scratch := { sc.scratch with scratch_buf := sh.scratch.scratch_buf } } ∧
        sh.scratch.scratch_buf.length = c.scratch_cap ∧
        CongCtrlLayout c sh.scratch.scratch_buf g_len.toNat ctrl_off.toNat occ_bkt bkt_off
          inq_off q_off ht_off ht_sz_c.toNat ∧
        (∀ idx < g_len.toNat, sh.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
        (∀ k < ih.toNat, sh.scratch.scratch_buf[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
        CongOccNodesOk F_cur cv0 g_len.toNat occ_end ctrl_off.toNat bkt_off occ_bkt scr0
          sh.scratch.scratch_buf ∧
        (ticks_o.toNat = ticks_n.toNat →
          (sh.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
        (FullMem c sh ⋆ R) mh)
      (μ := fun (ih, ()) _ => ht_sz_c.toNat - ih.toNat)
      (fun Js_8 hJs_8 => by
        c0_hsteps!; exact hJs_8 (0#64, ()) m_c ⟨sc, Nat.zero_le _, rfl,
          hdw_c.1.scratch_ok.scratch_buf_len, hlay_c, hpref_c,
          fun _ h => absurd h (Nat.not_lt_zero _), hocc_c, fun h => (hta_c h).2, hm_c⟩)
      (fun Js_8 ⟨ih, ⟨⟩⟩ mh
        ⟨sh, hih_le, hsh_eq, hscrl_h, hlay_h, hpref_h, hht_h, hocc_h, hql_h, hm_h⟩ ihs => ?_)
    c0_hsteps_nogrp; c0_hsplit_nobound
    · have hih_lt : ih.toNat < ht_sz_c.toNat := hc
      have hstep := wl_rehash_clear_step hlay_h hscrl_h hpref_h hht_h hocc_h hih_lt
      have hidx_arr : (BitVec.ofNat 64 ht_off + ih).toNat < sh.scratch.scratch_buf.length := by
        rw [hstep.1]; omega
      clear hc; c0_hsteps!; rw [hstep.1] at hm
      exact ihs (ih + 1#64, ()) m (by dsimp only; rw [hstep.2.2.1]; omega)
        ⟨_, by rw [hstep.2.2.1]; omega, by rw [hsh_eq], hstep.2.2.2.1, hstep.2.2.2.2.1,
         hstep.2.2.2.2.2.1, by rw [hstep.2.2.1]; exact hstep.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2,
         fun heq => by
           rw [List.getElem?_set_ne (by
             rcases hlay_h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4, _⟩
             omega)]
           exact hql_h heq, hm⟩
    · have hih_eq : ih.toNat = ht_sz_c.toNat := by omega
      have hht_clr : CongHtInv congAndArityMax F_cur cv0 scr0 sh.scratch.scratch_buf
          g_len.toNat ht_off ht_sz_c.toNat := fun k hk =>
        Or.inl (by rw [← hih_eq] at hk; exact hht_h k hk)
      have hdw_h : FullDenseInvW c F0 F_cur sh := by
        rw [hsh_eq]; exact fullDenseInvW_with_scr hdw_c hscrl_h
      have hcor_h : sh.core = sc.core := by rw [hsh_eq]
      have hok_clr : WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off
          inq_off q_off ht_off ht_sz_c.toNat occ_end scr0
          { sh with scratch := { sh.scratch with res_sz := 0#64 } } :=
        ⟨fullDenseInvW_with_rsz hdw_h 0#64, hcor_h ▸ hcv_c, hcor_h ▸ hfl_c,
         hcor_h ▸ hrepr_c, hlay_h, hpref_h, hht_clr, hocc_h⟩
      clear hc ihs; c0_hsteps_nogrp
      refine wp_loop_inv
        (Inv := fun (tk, gh, ()) mg => ∃ sg : FullState,
          ticks_o.toNat ≤ tk.toNat ∧ tk.toNat ≤ tlim.toNat ∧
          (ticks_o.toNat < tk.toNat ∨ (sg.core.inconsistent = 0#64 ∧
            (sg.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat)) ∧
          CongGateSeqOk congAndArityMax F_cur cv0 scr0 g_len.toNat gh.toNat ∧
          WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
            q_off ht_off ht_sz_c.toNat occ_end scr0 sg ∧ (FullMem c sg ⋆ R) mg)
        (μ := fun (_, gh, ()) _ => g_len.toNat - gh.toNat)
        (fun Js_9 hJs_9 => by
          c0_hsteps!
          refine hJs_9 (ticks_n, 0#64, ()) m ⟨_, hta_lo, by omega, ?_, hseq0, hok_clr, hm⟩
          rcases Nat.lt_or_eq_of_le hta_lo with hlt | heq
          · exact Or.inl hlt
          · exact Or.inr ⟨hcor_h ▸ (hta_c heq).1, hql_h heq⟩)
        (fun Js_9 ⟨tk, gh, ⟨⟩⟩ mg ⟨sg, htk_lo, htk_le, hstep_g, hseq_g, hok_g, hmg⟩ ihg => ?_)
      c0_hstraight; c0_hsplit_nobound
      · have hg_lt : gh.toNat < g_len.toNat := hc
        have hscrl_g := hok_g.1.1.scratch_ok.scratch_buf_len
        have hg1_n : (gh + (1 : BitVec 64)).toNat = gh.toNat + 1 := by bv_omega
        have hg1_arr : (gh + (1 : BitVec 64)).toNat < sg.scratch.scratch_buf.length := by
          rw [hg1_n]; omega
        clear hc; c0_hstraight; c0_hsplit_nobound
        · have hinc0 : sg.core.inconsistent = 0#64 := hc
          clear hc; c0_hstraight; c0_hsplit_nobound
          · have htk_lt : tk.toNat < tlim.toNat := hc
            obtain ⟨hgat_g, hseq_next⟩ := congGateSeqOk_inv_lt hseq_g hg_lt
            have ⟨_, mw, _, hscr0_g1, _, hbd_g, _, _, _, _⟩ := hgat_g
            have hsg_g1 : sg.scratch.scratch_buf[(gh + (1 : BitVec 64)).toNat]'hg1_arr = mw := by
              apply Option.some.inj
              rw [← List.getElem?_eq_getElem hg1_arr, hg1_n, hok_g.2.2.2.2.2.1 _ (by omega),
                hscr0_g1]
            have hsg_g1' : sg.scratch.scratch_buf[
                (gh.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [show (gh.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                  (gh + (1 : BitVec 64)).toNat from by bv_omega]; exact hg1_arr) = mw := hsg_g1
            clear hc; c0_hsteps_nogrp
            refine wp_join_group
              (fun (arity, ()) ma_g => ma_g = mg ∧
                arity.toNat = congGateArity mw ∧ arity.toNat ≤ g_len.toNat)
              (fun _ ⟨arity, ⟨⟩⟩ ma_g ⟨hma_g, har_eq, har_le⟩ => ?_)
              (fun _ hJa => by
                c0_hsplit
                · rw [hsg_g1'] at hc; c0_hsteps!
                  have h_g1' : sg.scratch.scratch_buf[(gh + 1).toNat]'hg1_arr = mw := hsg_g1
                  rw [h_g1']
                  exact hJa (mw &&& 0x0FFFFFFF#32, ()) mg ⟨rfl,
                    by rw [congGateArity_of_eq3 hc],
                    by rw [congGateArity_of_eq3 hc] at hbd_g; omega⟩
                · rw [hsg_g1'] at hc; c0_hsteps!
                  have h_g1' : sg.scratch.scratch_buf[(gh + 1).toNat]'hg1_arr = mw := hsg_g1
                  rw [h_g1']
                  exact hJa (mw &&& 0xFF#32, ()) mg ⟨rfl,
                    by rw [congGateArity_of_ne3 hc],
                    by rw [congGateArity_of_ne3 hc] at hbd_g; omega⟩)
            subst ma_g
            have htk1 : (tk + 1#64).toNat = tk.toNat + 1 := by bv_omega
            have hng : (gh + 2#64 + BitVec.setWidth 64 arity).toNat =
                gh.toNat + 2 + arity.toNat := by bv_omega
            have hseq_next' : CongGateSeqOk congAndArityMax F_cur cv0 scr0 g_len.toNat
                (gh + 2#64 + BitVec.setWidth 64 arity).toNat := by
              rw [hng, har_eq]; simpa [hscr0_g1] using hseq_next
            c0_hsteps!; c0_hcall hEval
            refine ⟨congAndArityMax, c, F0, F_cur, sg, scr0, g_len.toNat, R,
              Nat.le_refl _, rfl, hok_g.1, hok_g.2.1 ▸ hok_g.2.2.2.1, hht_pos_c, hht_bnd_c, hg_lt,
              by rw [hho_n]; exact hg_ht_le, by rw [hho_n]; exact hht_cap_c, hok_g.2.2.2.2.2.1,
              hok_g.2.1 ▸ hgat_g, by rw [hho_n]; exact hok_g.2.1 ▸ hok_g.2.2.2.2.2.2.1,
              Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, by rw [hho_n]; exact hok_g.2.2.2.2.1⟩,
              hmg, fun er sj mj hdwj hcvj hflj _ _ hreprj hprefj hhtj hqj hfrj he2u hmj => ?_⟩
            c0_hsplit
            · c0_hsteps!; exact hQ 20#64 sj mj hdwj (hcvj.trans hok_g.2.1) (hflj.trans hok_g.2.2.1)
                ((hcvj.trans hok_g.2.1) ▸ hreprj) (Or.inr rfl) (fun _ => he2u hc) hmj
            · have hokj := wlStOk_of_eval hok_g hc_cap hdwj hcvj hflj hreprj hprefj
                (by rw [hho_n] at hhtj; exact hhtj) (by rw [hho_n] at hqj; exact hqj)
                fun idx h1 h2 => ⟨(hfrj (by simpa using hc) idx h1 (by rw [hho_n]; exact h2)).1,
                  fun o b i q hl => (hfrj (by simpa using hc) idx h1
                    (by rw [hho_n]; exact h2)).2 o b i q (by rw [hho_n]; exact hl)⟩
              clear hc; c0_hsteps!
              exact ihg (tk + 1#64, gh + 2#64 + BitVec.setWidth 64 arity, ()) mj
                (by dsimp only; rw [hng]; omega) ⟨sj, by rw [htk1]; omega, by rw [htk1]; omega,
                 Or.inl (by rw [htk1]; omega), hseq_next', hokj, hmj⟩
          · c0_hsteps!; exact hJreh (ht_sz_c, ih, tk, reh_c, gh, ()) mg ⟨sg, hht_pos_c, hht_max_c,
              hht_bnd_c, hht_cap_c, hreh_c, htk_lo, htk_le, hstep_g, hok_g, hmg⟩
        · c0_hsteps!; exact hJreh (ht_sz_c, ih, tk, reh_c, gh, ()) mg ⟨sg, hht_pos_c, hht_max_c,
            hht_bnd_c, hht_cap_c, hreh_c, htk_lo, htk_le, hstep_g, hok_g, hmg⟩
      · c0_hsteps!; exact hJreh (ht_sz_c, ih, tk, reh_c, gh, ()) mg ⟨sg, hht_pos_c, hht_max_c,
          hht_bnd_c, hht_cap_c, hreh_c, htk_lo, htk_le, hstep_g, hok_g, hmg⟩
  · c0_hsplit
    · have hdg_t : dg = true := hc; have hct := wl_do_grow_ctrl hoka.2.2.2.2.1 hscrl_a (hdg hdg_t)
      have hc7_n : (ctrl_off + (7 : BitVec 64)).toNat = ctrl_off.toNat + 7 := by
        have := hoka.2.2.2.2.1.2.1; bv_omega
      have hc7_arr : (ctrl_off + (7 : BitVec 64)).toNat < sa.scratch.scratch_buf.length := by
        rw [hc7_n, hscrl_a]; have := hoka.2.2.2.2.1.2.1; omega
      have hm_sh := focus_full_scratch_buf hma; clear hc; c0_hsteps!; rw [hc7_n] at hm
      have hm' := unfocus_full_scratch_buf hm
      have hno7 : ∀ idx, idx ≠ ctrl_off.toNat + 7 → (sa.scratch.scratch_buf.set (ctrl_off.toNat + 7)
          (BitVec.setWidth 32 (ht_sz_o <<< 1#64)))[idx]? = sa.scratch.scratch_buf[idx]? :=
        fun idx hne => List.getElem?_set_ne (Ne.symm hne)
      exact hJs_7 (ht_sz_o <<< 1#64, rehashes_o, ()) m ⟨_, hct.1, hct.2.1, hct.2.2.1, hct.2.2.2.1,
        hreh_le, fullDenseInvW_with_scr hoka.1 hct.2.2.2.2.1, hoka.2.1, hoka.2.2.1, hoka.2.2.2.1,
        hct.2.2.2.2.2, fun idx hidx => by
          rw [hno7 idx (by have := hoka.2.2.2.2.1.2.2.1; omega)]; exact hoka.2.2.2.2.2.1 idx hidx,
        ⟨hoka.2.2.2.2.2.2.2.1, hoka.2.2.2.2.2.2.2.2.1, hoka.2.2.2.2.2.2.2.2.2.1,
         fun b hb => by
           rcases hoka.2.2.2.2.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, _⟩
           rw [hno7 _ (by omega)]; exact hoka.2.2.2.2.2.2.2.2.2.2.1 b hb,
         fun nd hn1 hn2 hm3 => by
           have := hoka.2.2.2.2.2.2.2.2.1
           rw [hno7 nd (by omega), hno7 (nd + 1) (by omega), hno7 (nd + 2) (by omega)]
           exact hoka.2.2.2.2.2.2.2.2.2.2.2 nd hn1 hn2 hm3⟩,
        fun heq => ⟨(hta_eq heq).1,
          by rw [hno7 (ctrl_off.toNat + 5) (by omega)]; exact (hta_eq heq).2⟩, hm'⟩
    · have hdg_f : dg = false := by cases dg <;> first | rfl | cases hc
      have hrf := hdf hdg_f
      have hr1_n : (rehashes_o + 1#64).toNat = rehashes_o.toNat + 1 := by bv_omega
      clear hc; c0_hsteps!; exact hJs_7 (ht_sz_o, rehashes_o + 1#64, ()) ma
        ⟨sa, hht_pos, hht_max, hht_bnd, hht_cap, by rw [hr1_n]; omega, hoka.1, hoka.2.1, hoka.2.2.1,
         hoka.2.2.2.1, hoka.2.2.2.2.1, hoka.2.2.2.2.2.1, hoka.2.2.2.2.2.2.2, hta_eq, hma⟩

private theorem wl_relink_step (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {fuel0 : BitVec 64}
    {cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz occ_end : Nat}
    {scr0 : List (BitVec 32)} {sj : FullState} {mj : Mem 64} {nd raw_lit : BitVec 32}
    {R : Mem 64 → Prop} (ho_pos : 0 < occ_bkt) (hopow : ∃ p, 1 ≤ p ∧ p ≤ 20 ∧ occ_bkt = 2 ^ p)
    (hnd_lo : g_len ≤ nd.toNat) (hnd2 : nd.toNat + 2 < occ_end)
    (hm3 : (nd.toNat - g_len) % 3 = 0) (hrl_lt : raw_lit.toNat < 2 * cv0)
    (hokj : WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end scr0 sj)
    (hmj : (FullMem c sj ⋆ R) mj) :
    ∀ {Q : Post [i64]} {X : XPost} {J : Cont []},
      (∀ m', (∃ st' : FullState, WlStOk c F0 F_cur fuel0 cv0 g_len ctrl_off occ_bkt
        bkt_off inq_off q_off ht_off ht_sz occ_end scr0 st' ∧ (FullMem c st' ⋆ R) m') → J () m') →
      wp Γ Q X
        (.call (as := [i64, i32]) (bs := [i32]) "full_cong_find"
          (.var c.pRepr, (.var raw_lit, ())) fun p =>
         .let_ ⟨.lshr i32, (.var p.fst, (.imm 1, ()))⟩ fun p =>
         .let_ ⟨.sub i32, (.var (BitVec.ofNat 32 occ_bkt), (.imm 1, ()))⟩ fun q1 =>
         .let_ ⟨.and i32, (.var p.fst, (.var q1.fst, ()))⟩ fun p =>
         .let_ ⟨.zext 32 64, (.var nd, ())⟩ fun q2 =>
         .let_ ⟨.add i64, (.var q2.fst, (.imm 2, ()))⟩ fun q3 =>
         .let_ ⟨.mul i64, (.var q3.fst, (.imm 4, ()))⟩ fun q4 =>
         .let_ ⟨.add i64, (.var c.pScratchBuf, (.var q4.fst, ()))⟩ fun q5 =>
         .let_ ⟨.zext 32 64, (.var p.fst, ())⟩ fun q6 =>
         .let_ ⟨.add i64, (.var (BitVec.ofNat 64 bkt_off), (.var q6.fst, ()))⟩ fun q7 =>
         .let_ ⟨.mul i64, (.var q7.fst, (.imm 4, ()))⟩ fun q8 =>
         .let_ ⟨.add i64, (.var c.pScratchBuf, (.var q8.fst, ()))⟩ fun q9 =>
         .load i32 (.var q9.fst) fun ld => .store (t := i32) (.var ld) (.var q5.fst) (
         .let_ ⟨.zext 32 64, (.var p.fst, ())⟩ fun p =>
         .let_ ⟨.add i64, (.var (BitVec.ofNat 64 bkt_off), (.var p.fst, ()))⟩ fun p =>
         .let_ ⟨.mul i64, (.var p.fst, (.imm 4, ()))⟩ fun p =>
         .let_ ⟨.add i64, (.var c.pScratchBuf, (.var p.fst, ()))⟩ fun p =>
         .store (t := i32) (.var nd) (.var p.fst) (.jump J ()))) mj := by
  intro Q X J hJ; have hsc := c.hscr; unfold dimacsBound at hsc
  have ⟨hdwj, hcvj, hflj, hreprj, hlay_j, hpref_j, hht_j, hocc_j⟩ := hokj
  have hscrl_j := hdwj.1.scratch_ok.scratch_buf_len; c0_hsteps!; c0_hcall hFind
  refine ⟨F_cur, 2 * cv0, sj.core.repr, ArrayField.repr.rest c sj ⋆ R, hcvj ▸ hreprj, hrl_lt,
    focus_full_repr hmj, fun dst repr_r mr hrl_r hrepr_r _ _ _ hmr => ?_⟩
  let st_r : FullState := { sj with core := { sj.core with repr := repr_r } }
  have hmr' : (FullMem c st_r ⋆ R) mr := unfocus_full_repr hmr
  have hokr := wlStOk_with_repr hokj (hrl_r.trans hdwj.1.core_ok.repr_len) hrepr_r
  let b_dst := (dst >>> (1 : BitVec 32)) &&& (BitVec.ofNat 32 occ_bkt - (1 : BitVec 32))
  have hbd_lt : b_dst.toNat < occ_bkt := by
    dsimp only [b_dst]; rw [show (1 : BitVec 32) = 1#32 from rfl,
      cong_and_sub1_u32_eq_mod hopow]; exact Nat.mod_lt _ ho_pos
  have hlay_r := hlay_j; rcases hlay_r with ⟨_, _, _, _, _, _, _, _, _, _, _, ho_max, _, _,
    hcq, hqi, hib, hbh, hht_cap, _⟩
  unfold congOccBktMax at ho_max; have hocc_c := hocc_j.2.1; have hco_cap := hlay_j.1
  have hnd2_n : (BitVec.setWidth 64 nd + (2 : BitVec 64)).toNat = nd.toNat + 2 := by bv_omega
  have hbd_n : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 b_dst).toNat =
      bkt_off + b_dst.toNat := by bv_omega
  have hpres := wl_relink_pres hlay_j hscrl_j hpref_j (hcvj ▸ hht_j) hocc_j hnd_lo hnd2 hm3 hbd_lt
  have hbd_arr : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 b_dst).toNat <
      st_r.scratch.scratch_buf.length := by rw [hbd_n, hscrl_j]; omega
  have hnd2_arr : (BitVec.setWidth 64 nd + (2 : BitVec 64)).toNat <
      st_r.scratch.scratch_buf.length := by rw [hnd2_n, hscrl_j]; omega
  have hbd_arr2 : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 b_dst).toNat <
      (st_r.scratch.scratch_buf.set (BitVec.setWidth 64 nd + (2 : BitVec 64)).toNat
        (st_r.scratch.scratch_buf[(BitVec.ofNat 64 bkt_off +
          BitVec.setWidth 64 b_dst).toNat]'hbd_arr)).length := by
    rw [List.length_set]; exact hbd_arr
  have hmr_scr := focus_full_scratch_buf hmr'; c0_hsteps!
  have hhm : (array (t := i32) c.pScratchBuf
      ((sj.scratch.scratch_buf.set (nd.toNat + 2)
        (sj.scratch.scratch_buf[bkt_off + b_dst.toNat]?.getD 0xFFFFFFFF#32)).set
        (bkt_off + b_dst.toNat) (BitVec.ofNat 32 nd.toNat)) ⋆
      (ArrayField.scratch_buf.rest c st_r ⋆ R)) m := by
    have hb_get : st_r.scratch.scratch_buf[(BitVec.ofNat 64 bkt_off +
        BitVec.setWidth 64 (dst >>> OfNat.ofNat 1 &&& BitVec.ofNat 32 occ_bkt - 1)).toNat]'
          hbd_arr = sj.scratch.scratch_buf[bkt_off + b_dst.toNat]?.getD 0xFFFFFFFF#32 := by
      change sj.scratch.scratch_buf[(BitVec.ofNat 64 bkt_off +
        BitVec.setWidth 64 b_dst).toNat]'(by rw [hscrl_j, hbd_n]; omega) = _
      rw [list_getElem_congr hbd_n _ (by rw [hscrl_j]; omega),
        List.getElem?_eq_getElem (by rw [hscrl_j]; omega), Option.getD_some]
    have hbd_eq' : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64
        (dst >>> OfNat.ofNat 1 &&& BitVec.ofNat 32 occ_bkt - 1)).toNat =
        bkt_off + b_dst.toNat := hbd_n
    have hnd_32 : BitVec.ofNat 32 nd.toNat = nd := by bv_omega
    rw [hb_get, hnd2_n, hbd_eq'] at hm; rw [hnd_32]; exact hm
  exact hJ m ⟨_, wlStOk_with_scr hokr hpres.1 hpres.2.1 hpres.2.2.1 hpres.2.2.2.1
    hpres.2.2.2.2, unfocus_full_scratch_buf hhm⟩

private theorem wl_pop_bounds {c : FullCfg} {so : FullState} {ctrl_off : BitVec 64}
    {g_len occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hlay : CongCtrlLayout c so.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off
      inq_off q_off ht_off ht_sz)
    (hscrl : so.scratch.scratch_buf.length = c.scratch_cap)
    (hc4_n : (ctrl_off + 4#64).toNat = ctrl_off.toNat + 4)
    (hc5_n : (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5)
    (hql_pos : 0 < (so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat) :
    ∃ (hc4 : (ctrl_off + 4).toNat < so.scratch.scratch_buf.length)
      (hq_arr : (BitVec.ofNat 64 q_off + BitVec.setWidth 64
        (so.scratch.scratch_buf[(ctrl_off + 4).toNat]'hc4)).toNat <
        so.scratch.scratch_buf.length),
      (so.scratch.scratch_buf[(BitVec.ofNat 64 q_off + BitVec.setWidth 64
        (so.scratch.scratch_buf[(ctrl_off + 4).toNat]'hc4)).toNat]'hq_arr).toNat < occ_bkt ∧
      (let scr := so.scratch.scratch_buf
       let qh := scr[ctrl_off.toNat + 4]?.getD 0#32
       let ql := scr[ctrl_off.toNat + 5]?.getD 0#32
       let b := scr[q_off + qh.toNat]?.getD 0#32
       let qidx := (BitVec.ofNat 64 q_off +
         BitVec.setWidth 64 (scr[(ctrl_off + 4).toNat]'hc4)).toNat
       let bv := scr[qidx]'hq_arr
       let scr3 := ((scr.set (ctrl_off + 4).toNat
           (scr[(ctrl_off + 4).toNat]'hc4 + 1 &&& BitVec.ofNat 32 occ_bkt - 1)).set
           (ctrl_off + 5).toNat (scr[(ctrl_off + 5).toNat]'(by
             rw [show (ctrl_off + 5).toNat = ctrl_off.toNat + 5 from hc5_n, hscrl]
             have := hlay.2.1; omega) - 1)).set
           (BitVec.ofNat 64 inq_off + BitVec.setWidth 64 bv).toNat 0
       scr3.set (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 bv).toNat 4294967295 =
       (((scr.set (ctrl_off.toNat + 4)
           ((qh + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32))).set
           (ctrl_off.toNat + 5) (ql - 1#32)).set (inq_off + b.toNat) 0#32).set
           (bkt_off + b.toNat) 0xFFFFFFFF#32 ∧
       (∀ h3 : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 bv).toNat < scr3.length,
         scr3[(BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 bv).toNat]'h3 =
           scr[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32)) := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ⟨_, hc8, _, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, hhc, hqh_lt, hqok⟩ :=
    hlay
  let qh := so.scratch.scratch_buf[ctrl_off.toNat + 4]?.getD 0#32
  let ql := so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32
  let b := so.scratch.scratch_buf[q_off + qh.toNat]?.getD 0#32
  have hc4_n' : (ctrl_off + 4).toNat = ctrl_off.toNat + 4 := hc4_n
  have hc5_n' : (ctrl_off + 5).toNat = ctrl_off.toNat + 5 := hc5_n
  have hc4 : (ctrl_off + 4).toNat < so.scratch.scratch_buf.length := by
    rw [hc4_n', hscrl]; omega
  have hc4' : ctrl_off.toNat + 4 < so.scratch.scratch_buf.length := by rw [hscrl]; omega
  have hc5' : ctrl_off.toNat + 5 < so.scratch.scratch_buf.length := by rw [hscrl]; omega
  have hqhe : so.scratch.scratch_buf[(ctrl_off + 4).toNat]'hc4 = qh := by
    dsimp only [qh]
    rw [list_getElem_congr hc4_n' hc4 hc4', List.getElem?_eq_getElem hc4', Option.getD_some]
  have hqle : so.scratch.scratch_buf[(ctrl_off + 5).toNat]'(by rw [hc5_n']; exact hc5') = ql := by
    dsimp only [ql]
    rw [list_getElem_congr hc5_n' _ hc5', List.getElem?_eq_getElem hc5', Option.getD_some]
  have hqh_v : qh.toNat < occ_bkt := by
    simpa [qh, List.getElem?_eq_getElem hc4'] using hqh_lt
  have hidx : (BitVec.ofNat 64 q_off + BitVec.setWidth 64
      (so.scratch.scratch_buf[(ctrl_off + 4).toNat]'hc4)).toNat = q_off + qh.toNat := by
    rw [hqhe]; bv_omega
  have hq_arr : (BitVec.ofNat 64 q_off + BitVec.setWidth 64
      (so.scratch.scratch_buf[(ctrl_off + 4).toNat]'hc4)).toNat <
      so.scratch.scratch_buf.length := by rw [hidx, hscrl]; omega
  have hql0 := hqok.2 0 hql_pos
  rw [Nat.add_zero, Nat.mod_eq_of_lt hqh_v] at hql0
  have hq_arr' : q_off + qh.toNat < so.scratch.scratch_buf.length := by rw [← hidx]; exact hq_arr
  have hb_v : (so.scratch.scratch_buf[(BitVec.ofNat 64 q_off + BitVec.setWidth 64
      (so.scratch.scratch_buf[(ctrl_off + 4).toNat]'hc4)).toNat]'hq_arr).toNat < occ_bkt := by
    rw [list_getElem_congr hidx hq_arr hq_arr']
    simpa [List.getElem?_eq_getElem hq_arr'] using hql0
  have hbe : so.scratch.scratch_buf[(BitVec.ofNat 64 q_off + BitVec.setWidth 64
      (so.scratch.scratch_buf[(ctrl_off + 4).toNat]'hc4)).toNat]'hq_arr = b := by
    dsimp only [b]; rw [list_getElem_congr hidx hq_arr hq_arr', List.getElem?_eq_getElem hq_arr',
      Option.getD_some]
  have hinqb_n : (BitVec.ofNat 64 inq_off + BitVec.setWidth 64 b).toNat = inq_off + b.toNat := by
    rw [hbe] at hb_v; bv_omega
  have hbktb_n : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64 b).toNat = bkt_off + b.toNat := by
    rw [hbe] at hb_v; bv_omega
  refine ⟨hc4, hq_arr, hb_v, ?_, fun h3 => ?_⟩
  · rw [hbe, hqhe, hqle, hc4_n', hc5_n', hinqb_n, hbktb_n]; rfl
  · have hb_lt : b.toNat < occ_bkt := hbe ▸ hb_v
    have hb_arr : bkt_off + b.toNat < so.scratch.scratch_buf.length := by rw [hscrl]; omega
    have hidx2 : (BitVec.ofNat 64 bkt_off + BitVec.setWidth 64
        (so.scratch.scratch_buf[(BitVec.ofNat 64 q_off + BitVec.setWidth 64
          (so.scratch.scratch_buf[(ctrl_off + 4).toNat]'hc4)).toNat]'hq_arr)).toNat =
        bkt_off + b.toNat := by rw [hbe, hbktb_n]
    rw [list_getElem_congr hidx2 h3 (by simp [hscrl]; omega)]
    rw [List.getElem_set_ne (by rw [hbe, hinqb_n]; omega),
      List.getElem_set_ne (by rw [hc5_n']; omega), List.getElem_set_ne (by rw [hc4_n']; omega),
      List.getElem?_eq_getElem hb_arr, Option.getD_some]

private theorem wl_nd_read {scr : List (BitVec 32)} {k : BitVec 64} {n : Nat} (d : BitVec 32)
    (hk : k.toNat = n) (hlt : n < scr.length) :
    scr[k.toNat]'(hk ▸ hlt) = scr[n]?.getD d := by
  rw [list_getElem_congr hk (hk ▸ hlt) hlt, List.getElem?_eq_getElem hlt, Option.getD_some]

private theorem wl_exit_ret_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 : Nat} {fuel0 : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {Γ : Env} {sout : FullState} {mout : Mem 64}
    (hdw : FullDenseInvW c F0 F_cur sout) (hcv : sout.core.cur_vars = cv0)
    (hfl : sout.core.fuel = fuel0) (hrepr : FullCongReprInv F_cur (2 * cv0) sout.core.repr)
    (hmout : (FullMem c sout ⋆ R) mout)
    (hQ : ∀ r s' m', FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = cv0 →
      s'.core.fuel = fuel0 → FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (.group (sig := [[i64]]) (fun _Js => .cons (fun p => .ret (.var p.fst, ())) .nil)
      fun Js => .let_ ⟨.add i64, (.var c.hdr, (.imm 1024, ()))⟩ fun p =>
        .load i64 (.var p.fst) fun ld =>
        .let_ ⟨.cmp .ne i64 .bool rfl, (.var ld, (.imm 0, ()))⟩ fun p =>
        .jnz (.var p.fst) (.jump Js.fst (.imm 20, ())) (.jump Js.fst (.imm 1, ()))) mout := by
  c0_hsteps_nogrp
  refine wp_join_group (fun (r, ()) mret =>
    mret = mout ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
    (fun _ ⟨r, ⟨⟩⟩ mret ⟨hmret, hr, huns⟩ => by
      subst hmret; c0_hsteps!; exact hQ r sout mret hdw hcv hfl (hcv ▸ hrepr) hr huns hmout)
    (fun _ hJret => by
      c0_hsteps_nogrp; c0_hsplit
      · c0_hsteps!; exact hJret (20#64, ()) mout ⟨rfl, Or.inr rfl, fun _ =>
          unsat_of_inconsistent_w hdw.2.1 hc⟩
      · c0_hsteps!; exact hJret (1#64, ()) mout ⟨rfl, Or.inl rfl, fun h => by cases h⟩)

/-! ## 3. Main Theorem (`full_cong_worklist_wp`) -/

public section

/-- Canonical `Func.wp` proof for `full_cong_worklist`. -/
theorem full_cong_worklist_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hEval : Γ.Has "full_cong_eval_gate" Spec.fullCongEvalGateSpec) :
    ∀ args m Q X, Spec.fullCongWorklistSpec args m Q X →
      Func.wp Γ full_cong_worklist_body args m Q X := by
  rintro ⟨h, g_len, ctrl_off, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, scr0, occ_bkt, bkt_off, inq_off, q_off, ht_off, ht_sz, R,
     rfl, hdw0, hrepr0, hg_pos, hht_bnd, hlay0, hseq0, hpref0, hht0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  have ⟨hc_cap, hc_8, hg_co, hg_24, _, _, _, _, _, _,
    ho_pos, ho_max, hopow, hht_pos, hcq, hqi, hib, hbh, hht_cap, _, _, _⟩ := hlay0
  have hg_ht_le : g_len.toNat ≤ ht_off := by omega
  unfold congOccBktMax at ho_max; unfold congHashMaxSz at hht_bnd
  have hscrl0 := hdw0.1.scratch_ok.scratch_buf_len
  dsimp only [Func.wp, full_cong_worklist_body]; c0_hsteps_nogrp
  refine wp_join_group (fun (tlim, ()) mt => mt = m0 ∧ tlim.toNat ≤ 2 ^ 63 - 1)
    (fun _ ⟨tlim, ⟨⟩⟩ mt ⟨hmt, htlim_le⟩ => ?_)
    (fun _ hJt => by
      c0_hsplit
      · c0_hsteps!; exact hJt (0x7FFFFFFFFFFFFFFF#64, ()) m0 ⟨rfl, by decide⟩
      · have h9 : (9223372036854775807 : BitVec 64).toNat = 2 ^ 63 - 1 := by decide
        have hnot : ¬ (9223372036854775807 : BitVec 64).toNat < tick_lim.toNat := hc
        c0_hsteps!; exact hJt (tick_lim, ()) m0 ⟨rfl, by omega⟩)
  subst mt
  obtain ⟨hc0_a, hc1_a, hc2_a, hc3_a, hc6_a, hc7_a, hc4_n, hc5_n, hho_n, hhs_n,
    hbkt64_n, hinq64_n, hq64_n, hocc_eq, hbkt_eq, hinq_eq, hq_eq, hho_eq, hhs_eq⟩ :=
    wl_ctrl_eqs (by omega) hscrl0 hlay0
  have hbkt_eq' : BitVec.setWidth 64 (s0.scratch.scratch_buf[(ctrl_off + 1).toNat]'hc1_a) =
      BitVec.ofNat 64 bkt_off := hbkt_eq
  have hinq_eq' : BitVec.setWidth 64 (s0.scratch.scratch_buf[(ctrl_off + 2).toNat]'hc2_a) =
      BitVec.ofNat 64 inq_off := hinq_eq
  have hq_eq' : BitVec.setWidth 64 (s0.scratch.scratch_buf[(ctrl_off + 3).toNat]'hc3_a) =
      BitVec.ofNat 64 q_off := hq_eq
  have hho_eq' : BitVec.setWidth 64 (s0.scratch.scratch_buf[(ctrl_off + 6).toNat]'hc6_a) =
      BitVec.ofNat 64 ht_off := hho_eq
  have hhs_eq' : BitVec.setWidth 64 (s0.scratch.scratch_buf[(ctrl_off + 7).toNat]'hc7_a) =
      BitVec.ofNat 64 ht_sz := hhs_eq
  c0_hsteps_nogrp; dsimp only; rw [hocc_eq, hbkt_eq', hinq_eq']
  refine wp_loop_inv
    (Inv := fun (i, ()) mi => ∃ si : FullState, i.toNat ≤ occ_bkt ∧
      FullDenseInvW c F0 F_cur si ∧ si.core.cur_vars = cv0 ∧ si.core.fuel = fuel0 ∧
      FullCongReprInv F_cur (2 * cv0) si.core.repr ∧
      CongCtrlLayout c si.scratch.scratch_buf g_len.toNat ctrl_off.toNat occ_bkt bkt_off
        inq_off q_off ht_off ht_sz ∧
      (∀ idx < g_len.toNat, si.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      CongHtInv congAndArityMax F_cur cv0 scr0 si.scratch.scratch_buf g_len.toNat ht_off ht_sz ∧
      (∀ b < i.toNat, si.scratch.scratch_buf[bkt_off + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
      (FullMem c si ⋆ R) mi)
    (μ := fun (i, ()) _ => occ_bkt - i.toNat)
    (fun _ hJi => by
      c0_hsteps!; exact hJi (0#64, ()) m0 ⟨s0, Nat.zero_le _, hdw0, rfl, rfl, hrepr0, hlay0,
        hpref0, hht0, fun _ hb => absurd hb (Nat.not_lt_zero _), hm0⟩)
    (fun _ ⟨i, ⟨⟩⟩ mi ⟨si, hi_le, hdw_i, hcv_i, hfl_i, hrepr_i, hlay_i, hpref_i, hht_i,
      hbkt_i, hmi⟩ ihi => ?_)
  c0_hstraight; c0_hsplit_nobound
  · have hi_lt : i.toNat < occ_bkt := by rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hscrl_i := hdw_i.1.scratch_ok.scratch_buf_len
    have hst := wl_phase0_clear_step hlay_i hscrl_i hpref_i hht_i hbkt_i hi_lt
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcq_i, hqi_i, hib_i, hbh_i, hhc_i, _⟩ := hlay_i
    have hb_arr : (BitVec.ofNat 64 bkt_off + i).toNat < si.scratch.scratch_buf.length := by
      rw [hst.1, hscrl_i]; omega
    have hi_arr : (BitVec.ofNat 64 inq_off + i).toNat <
        (si.scratch.scratch_buf.set (BitVec.ofNat 64 bkt_off + i).toNat 4294967295).length := by
      rw [List.length_set, hst.2.1, hscrl_i]; omega
    have hm_sh := focus_full_scratch_buf hmi; clear hc; c0_hsteps!; rw [hst.1, hst.2.1] at hm
    exact ihi (i + 1#64, ()) m (by dsimp only; rw [hst.2.2.1]; omega)
      ⟨_, by rw [hst.2.2.1]; omega, fullDenseInvW_with_scr hdw_i hst.2.2.2.1, hcv_i, hfl_i,
       hrepr_i, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1,
       by rw [hst.2.2.1]; exact hst.2.2.2.2.2.2.2, unfocus_full_scratch_buf hm⟩
  have hi_eq : i.toNat = occ_bkt := by rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
  have hscrl_i := hdw_i.1.scratch_ok.scratch_buf_len
  have hfin := wl_phase0_finalize hlay_i hscrl_i hpref_i hht_i (hi_eq ▸ hbkt_i)
  have hc4_arr : (ctrl_off + 4#64).toNat < si.scratch.scratch_buf.length := by
    rw [hc4_n, hscrl_i]; have := hlay_i.2.1; omega
  have hc5_arr : (ctrl_off + 5#64).toNat <
      (si.scratch.scratch_buf.set (ctrl_off + 4#64).toNat 0).length := by
    rw [List.length_set, hc5_n, hscrl_i]; have := hlay_i.2.1; omega
  have hm_sh := focus_full_scratch_buf hmi; clear hc ihi; c0_hsteps!
  rw [show (ctrl_off + 4).toNat = ctrl_off.toNat + 4 from hc4_n,
    show (ctrl_off + 5).toNat = ctrl_off.toNat + 5 from hc5_n] at hm
  let scr_f :=
    (si.scratch.scratch_buf.set (ctrl_off.toNat + 4) 0#32).set (ctrl_off.toNat + 5) 0#32
  let sf : FullState := { si with scratch := { si.scratch with scratch_buf := scr_f } }
  have hok_f : WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
      q_off ht_off ht_sz g_len.toNat scr0 sf :=
    ⟨fullDenseInvW_with_scr hdw_i hfin.1, hcv_i, hfl_i, hrepr_i, hfin.2.1, hfin.2.2.1,
     hfin.2.2.2.1, hfin.2.2.2.2⟩
  have hmf : (FullMem c sf ⋆ R) m := unfocus_full_scratch_buf hm
  clear hc4_arr hc5_arr; c0_hsteps_nogrp
  let Inv1 : Tup Val [i64, i64, i64] → Mem 64 → Prop := fun (occ_end, ticks, g, ()) m1 =>
    ∃ s1 : FullState, g.toNat ≤ g_len.toNat ∧ g_len.toNat ≤ occ_end.toNat ∧
      occ_end.toNat ≤ ctrl_off.toNat ∧ (occ_end.toNat - g_len.toNat) % 3 = 0 ∧
      ticks.toNat ≤ tlim.toNat + 1 ∧
      CongGateSeqOk congAndArityMax F_cur cv0 scr0 g_len.toNat g.toNat ∧
      WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off q_off
        ht_off ht_sz occ_end.toNat scr0 s1 ∧ (FullMem c s1 ⋆ R) m1
  refine wp_loop_inv Inv1 (fun (_, _, g, ()) _ => g_len.toNat - g.toNat) ?_
    (fun _ ⟨occ_end, ticks, g, ⟨⟩⟩ m1
      ⟨s1, hg_le, hoe_lo, hoe_hi, hoe_m3, htk_le, hseq_1, hok_1, hm1⟩ ih1 => ?_)
  · intro J1 hJ1; c0_hsteps!; exact hJ1 (g_len, 0#64, 0#64, ()) m
      ⟨sf, Nat.zero_le _, Nat.le_refl _, hg_co, by simp, Nat.zero_le _, hseq0, hok_f, hmf⟩
  have ⟨hdw_1, hcv_1, hfl_1, hrepr_1, hlay_1, hpref_1, hht_1, hocc_1⟩ := hok_1
  clear hm m hmf hok_f sf scr_f hfin hbkt_i hht_i hpref_i hlay_i hrepr_i hfl_i hcv_i hdw_i hscrl_i
    hi_eq hi_le si hdw0 hrepr0 hlay0 hpref0 hht0 hm0
  have hscrl_1 := hdw_1.1.scratch_ok.scratch_buf_len; c0_hsteps_nogrp
  refine wp_join_group (fun () m2 => ∃ s2 : FullState,
    WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off q_off
      ht_off ht_sz occ_end.toNat scr0 s2 ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ ⟨⟩ m2 ⟨s2, hok_2, hm2⟩ => ?_) (fun _ hJp2 => ?_)
  · c0_hsteps_nogrp
    let Inv2 : Tup Val [i64, i64, i64, i64, i64, i32] → Mem 64 → Prop :=
      fun (ht_sz_o, _io, ticks_o, rehashes_o, _go, ep, ()) mo => ∃ so : FullState,
        0 < ht_sz_o.toNat ∧ ht_sz_o.toNat ≤ 2 * congHashMaxSz ∧ ht_sz_o.toNat < 2 ^ 30 ∧
        ht_off + ht_sz_o.toNat ≤ c.scratch_cap ∧
        rehashes_o.toNat ≤ 4 ∧ ticks_o.toNat ≤ tlim.toNat + 2 ∧
        WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
          q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 so ∧ (FullMem c so ⋆ R) mo
    refine wp_loop_inv Inv2
      (fun (_, _, ticks_o, _, _, _, ()) mo =>
        (tlim.toNat - ticks_o.toNat) * (occ_bkt + 1) +
          ((loadVal mo i32 (c.pScratchBuf + ctrl_off * 4 + 20)).getD 0#32).toNat)
      ?_
      (fun _ ⟨ht_sz_o, _io, ticks_o, rehashes_o, _go, ep, ⟨⟩⟩ mo
        ⟨so, hho_pos, hho_max, hho_bnd, hho_cap, hreh_o, hto_le, hok_o, hmo⟩ iho => ?_)
    · intro Jo hJo; c0_hsteps!; rw [hhs_eq']
      exact hJo (BitVec.ofNat 64 ht_sz, i, ticks, 0#64, g, 3#32, ()) m2
        ⟨s2, by rw [hhs_n]; exact hht_pos, by rw [hhs_n]; unfold congHashMaxSz; omega,
         by rw [hhs_n]; omega, by rw [hhs_n]; exact hht_cap, Nat.zero_le _,
         by omega, by rw [hhs_n]; exact hok_2, hm2⟩
    have ⟨hdw_o, hcv_o, hfl_o, hrepr_o, hlay_o, hpref_o, hht_o, hocc_o⟩ := hok_o
    have hscrl_o := hdw_o.1.scratch_ok.scratch_buf_len
    have hql_le_o := hlay_o.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; c0_hsteps_nogrp
    refine wp_join_group (fun () mout => ∃ sout : FullState,
      WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off q_off
        ht_off ht_sz_o.toNat occ_end.toNat scr0 sout ∧ (FullMem c sout ⋆ R) mout)
      (fun _ ⟨⟩ mout ⟨sout, hok_out, hmout⟩ => by
        c0_hsteps_nogrp; exact wl_exit_ret_wp hok_out.1 hok_out.2.1 hok_out.2.2.1
          (hok_out.2.1 ▸ hok_out.2.2.2.1) hmout hQ)
      (fun _ hjout => ?_)
    c0_hsplit
    · have ⟨_, hc8_o, _, _, _, _, _, _, _, _, _, _, _, _, hcq_o, hqi_o, hib_o, hbh_o, hhc_o, _⟩ :=
        hlay_o
      have hc5_arr : (ctrl_off + 5#64).toNat < so.scratch.scratch_buf.length := by
        rw [hc5_n, hscrl_o]; omega
      have hc5' : ctrl_off.toNat + 5 < so.scratch.scratch_buf.length := by rw [hscrl_o]; omega
      have hql_pos : 0 < (so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem hc5', Option.getD_some,
          ← list_getElem_congr hc5_n hc5_arr hc5']
        exact hc
      clear hc; c0_hsplit
      · have hinc0 : so.core.inconsistent = 0#64 := hc
        clear hc; c0_hsplit
        · have hto_lt : ticks_o.toNat < tlim.toNat := hc
          have hpop := wl_pop_pres hlay_o hscrl_o hpref_o (hcv_o ▸ hht_o) hocc_o hql_pos
          rcases hpop with ⟨hb_lt, hnqh_lt, hscrl_p, hlay_p, hpref_p, hht_p,
            hnd_ptr, hocc_p, hql_dec⟩
          let qh := so.scratch.scratch_buf[ctrl_off.toNat + 4]?.getD 0#32
          let ql := so.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32
          let b := so.scratch.scratch_buf[q_off + qh.toNat]?.getD 0#32
          obtain ⟨hc4_a, hq_arr, hb_v, hscr_eq, hnd_eq⟩ :=
            wl_pop_bounds hlay_o hscrl_o hc4_n hc5_n hql_pos
          have hld_mo : (loadVal mo i32 (c.pScratchBuf + ctrl_off * 4 + 20)).getD 0#32 = ql := by
            rw [wl_load_c5 hc5_n hc5_arr hmo]
          have hm_sh := focus_full_scratch_buf hmo
          clear hc; simp only [hq_eq']; c0_hsteps!; rw [hscr_eq] at hm
          have hhm_pop := unfocus_full_scratch_buf hm
          let scr_p := (((so.scratch.scratch_buf.set (ctrl_off.toNat + 4)
            ((qh + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32))).set
            (ctrl_off.toNat + 5) (ql - 1#32)).set (inq_off + b.toNat) 0#32).set
            (bkt_off + b.toNat) 0xFFFFFFFF#32
          let sp : FullState := { so with scratch := { so.scratch with scratch_buf := scr_p } }
          have hok_p := wlStOk_with_scr hok_o hscrl_p hlay_p hpref_p (hcv_o ▸ hht_p) hocc_p
          c0_hsteps_nogrp
          refine wp_loop_inv
            (Inv := fun (ticks_n, nd, ()) mn => ∃ sn : FullState,
              ticks_o.toNat ≤ ticks_n.toNat ∧ ticks_n.toNat ≤ tlim.toNat + 2 ∧
              (ticks_o.toNat = ticks_n.toNat → sn.core.inconsistent = 0#64 ∧
                (sn.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
              WlNodePtrOk g_len.toNat occ_end.toNat nd ∧
              WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
                q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 sn ∧ (FullMem c sn ⋆ R) mn)
            (μ := fun (ticks_n, _, ()) _ => tlim.toNat + 2 - ticks_n.toNat)
            (fun _ hJn => by
              c0_hsteps!; rw [hnd_eq]; exact hJn (ticks_o,
                so.scratch.scratch_buf[bkt_off + b.toNat]?.getD 0xFFFFFFFF#32, ()) m
                ⟨sp, Nat.le_refl _, by omega, fun _ => ⟨hinc0, hql_dec⟩, hnd_ptr, hok_p, hhm_pop⟩)
            (fun _ ⟨ticks_n, nd, ⟨⟩⟩ mn ⟨sn, htn_lo, htn_hi, htn_eq, hnd_p, hok_n, hmn⟩ ihn => ?_)
          have ⟨hdw_n, hcv_n, hfl_n, hrepr_n, hlay_n, hpref_n, hht_n, hocc_n⟩ := hok_n
          clear hhm_pop hok_p sp scr_p hscr_eq hnd_eq
          have hscrl_n := hdw_n.1.scratch_ok.scratch_buf_len; c0_hfast_nogrp
          refine wp_join_group (fun () ma => ∃ sa : FullState,
            ticks_o.toNat ≤ ticks_n.toNat ∧ ticks_n.toNat ≤ tlim.toNat + 2 ∧
            (ticks_o.toNat = ticks_n.toNat → sa.core.inconsistent = 0#64 ∧
              (sa.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat) ∧
            WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
              q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 sa ∧ (FullMem c sa ⋆ R) ma)
            (fun _ ⟨⟩ ma ⟨sa, hta_lo, hta_hi, hta_eq, hok_a, hma⟩ => ?_) (fun _ hJnd => ?_)
          · rw [hho_eq']; c0_hsteps_nogrp
            refine wp_join_group (fun (dg, ()) mdg => mdg = ma ∧
              (dg = true → ht_sz_o.toNat < 1048576 ∧
                ht_off + (ht_sz_o <<< 1#64).toNat ≤ c.scratch_cap))
              (fun _ ⟨dg, ⟨⟩⟩ mdg ⟨hmdg, hdg_ok⟩ => ?_)
              (fun _ hJdg => by
                c0_hsplit
                · clear hc; c0_hsplit
                  · have hlt : ht_sz_o.toNat < 1048576 := hc; clear hc; c0_hsplit
                    · have hle : ht_off + (ht_sz_o <<< 1#64).toNat ≤ c.scratch_cap := by
                        rw [bv64_shl1_lt (by omega)]
                        simpa [hho_n,
                          Nat.mod_eq_of_lt (by omega : ht_off + 2 * ht_sz_o.toNat < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] using hc
                      c0_hsteps!; exact hJdg (true, ()) ma ⟨rfl, fun _ => ⟨hlt, hle⟩⟩
                    all_goals (c0_hsteps!; exact hJdg (false, ()) ma ⟨rfl, fun h => by cases h⟩)
                  all_goals (c0_hsteps!; exact hJdg (false, ()) ma ⟨rfl, fun h => by cases h⟩)
                all_goals (c0_hsteps!; exact hJdg (false, ()) ma ⟨rfl, fun h => by cases h⟩))
            subst mdg; c0_hsteps_nogrp
            refine wp_join_group (fun (df, ()) mdf => mdf = ma ∧
              (df = true → dg = false ∧ rehashes_o.toNat < 4))
              (fun _ ⟨df, ⟨⟩⟩ mdf ⟨hmdf, hdf_ok⟩ => ?_)
              (fun _ hJdf => by
                c0_hsplit
                · c0_hsteps!; exact hJdf (false, ()) ma ⟨rfl, fun h => by cases h⟩
                · have hdg_f : dg = false := by cases dg <;> first | rfl | cases hc
                  clear hc; c0_hsplit
                  · clear hc; c0_hsplit
                    · have hr4 : rehashes_o.toNat < 4 := hc
                      c0_hsteps!; exact hJdf (true, ()) ma ⟨rfl, fun _ => ⟨hdg_f, hr4⟩⟩
                    all_goals (c0_hsteps!; exact hJdf (false, ()) ma ⟨rfl, fun h => by cases h⟩)
                  all_goals (c0_hsteps!; exact hJdf (false, ()) ma ⟨rfl, fun h => by cases h⟩))
            subst mdf; c0_hsteps_nogrp
            refine wp_join_group (fun (ht_sz_b, _ib, ticks_b, reh_b, _gb, ()) mb =>
              ∃ sb : FullState, 0 < ht_sz_b.toNat ∧ ht_sz_b.toNat ≤ 2 * congHashMaxSz ∧
                ht_sz_b.toNat < 2 ^ 30 ∧ ht_off + ht_sz_b.toNat ≤ c.scratch_cap ∧
                reh_b.toNat ≤ 4 ∧ ticks_o.toNat ≤ ticks_b.toNat ∧
                ticks_b.toNat ≤ tlim.toNat + 2 ∧
                (ticks_o.toNat < ticks_b.toNat ∨ (sb.core.inconsistent = 0#64 ∧
                  (sb.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat < ql.toNat)) ∧
                WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
                  q_off ht_off ht_sz_b.toNat occ_end.toNat scr0 sb ∧ (FullMem c sb ⋆ R) mb)
              (fun _ ⟨ht_sz_b, _ib, ticks_b, reh_b, _gb, ⟨⟩⟩ mb ⟨sb, hhb_pos, hhb_max, hhb_bnd,
                  hhb_cap, hreh_b, htb_lo, htb_le, hstep_b, hok_b, hmb⟩ => by
                have hlay_b := hok_b.2.2.2.2.1; have hscrl_b := hok_b.1.1.scratch_ok.scratch_buf_len
                have hco5_b : (ctrl_off + 5#64).toNat < sb.scratch.scratch_buf.length := by
                  rw [hc5_n, hscrl_b]; have := hlay_b.2.1; omega
                have hdec := wl_measure_dec hc5_n hco5_b hld_mo hmb hto_lt
                  hlay_b.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hstep_b htb_lo
                c0_hsteps!; exact iho (ht_sz_b, _ib, ticks_b, reh_b, _gb, ep + 1#32, ()) mb hdec
                  ⟨sb, hhb_pos, hhb_max, hhb_bnd, hhb_cap, hreh_b, by omega, hok_b, hmb⟩)
              (fun _ hJreh => by
                have hskip : ∀ {m' : Mem 64}, m' = ma → _ := fun {m'} hm' =>
                  hJreh (ht_sz_o, _io, ticks_n, rehashes_o, _go, ()) m'
                    ⟨sa, hho_pos, hho_max, hho_bnd, hho_cap, hreh_o, hta_lo, by omega,
                     (by rcases Nat.lt_or_eq_of_le hta_lo with h | heq
                         · exact Or.inl h
                         · exact Or.inr (hta_eq heq)), hok_a, hm' ▸ hma⟩
                c0_hsteps_nogrp
                refine wp_join_group (fun () mchk => mchk = ma ∧ (dg = true ∨ df = true))
                  (fun _ ⟨⟩ mchk ⟨hmchk, hdo⟩ => by
                    c0_hsplit
                    · have htn_lt : ticks_n.toNat < tlim.toNat := hc
                      have hdf_r : dg = false → rehashes_o.toNat < 4 := fun hdg_f => by
                        rcases hdo with h | h; cases hdg_f ▸ h; exact (hdf_ok h).2
                      c0_hsteps_nogrp; subst hmchk
                      exact wl_rehash_wp Γ hEval hg_pos hho_pos hho_bnd hho_max hg_ht_le
                        hho_cap hc_cap htlim_le htn_lt hta_lo hta_eq hdg_ok hdf_r hreh_o hseq0
                        hok_a hma hQ fun ys mb ⟨sb, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ =>
                          hJreh ys mb ⟨sb, a1, a2, a3, a4, a5, a6, by omega, a8, a9, a10⟩
                    · c0_hsteps!; exact hskip hmchk)
                  (fun _ hJor => by
                    c0_hsplit
                    · c0_hsteps!; exact hJor () ma ⟨rfl, Or.inl hc⟩
                    · have hdg_f : dg = false := by cases dg <;> first | rfl | cases hc
                      clear hc; c0_hsplit
                      · c0_hsteps!; exact hJor () ma ⟨rfl, Or.inr hc⟩
                      · c0_hsteps!; exact hskip rfl))
          · c0_hsplit
            · have hnd_ne : nd ≠ 0xFFFFFFFF#32 := hc
              clear hc; c0_hsplit
              · clear hc; c0_hsplit
                · have htn_lt : ticks_n.toNat < tlim.toNat := hc
                  rcases hnd_p with rfl | ⟨hnd_lo, hnd_2, hnd_m3⟩; · exact absurd rfl hnd_ne
                  obtain ⟨hgn_lt, hgat_gn, hrl_lt, hnxt_p⟩ :=
                    hocc_n.2.2.2.2 nd.toNat hnd_lo hnd_2 hnd_m3
                  have hnd0_n : (BitVec.setWidth 64 nd).toNat = nd.toNat := bv_zext32_toNat nd
                  have hnd1_n : (BitVec.setWidth 64 nd + 1).toNat = nd.toNat + 1 := by bv_omega
                  have hnd2_n : (BitVec.setWidth 64 nd + 2).toNat = nd.toNat + 2 := by bv_omega
                  have htn2_n : (ticks_n + 2).toNat = ticks_n.toNat + 2 := by bv_omega
                  let gn := sn.scratch.scratch_buf[nd.toNat]?.getD 0#32
                  let raw_lit := sn.scratch.scratch_buf[nd.toNat + 1]?.getD 0#32
                  let nxt := sn.scratch.scratch_buf[nd.toNat + 2]?.getD 0xFFFFFFFF#32
                  have hnd_len : nd.toNat + 2 < sn.scratch.scratch_buf.length := by
                    rw [hscrl_n]; have := hlay_n.2.2.1; omega
                  have hnd_e := wl_nd_read (scr := sn.scratch.scratch_buf) 0#32 hnd0_n
                    (by omega : nd.toNat < sn.scratch.scratch_buf.length)
                  have hnd1_e := wl_nd_read (scr := sn.scratch.scratch_buf) 0#32 hnd1_n
                    (by omega : nd.toNat + 1 < sn.scratch.scratch_buf.length)
                  have hnd2_e := wl_nd_read (scr := sn.scratch.scratch_buf) 0xFFFFFFFF#32 hnd2_n
                    hnd_len
                  clear hc; rw [hho_eq']; c0_hsteps!; c0_hcall hEval
                  refine ⟨congAndArityMax, c, F0, F_cur, sn, scr0, g_len.toNat, R,
                    Nat.le_refl _, rfl, hdw_n, hcv_n ▸ hrepr_n, hho_pos, hho_bnd,
                    by rw [hnd_e]; exact hgn_lt, by rw [hho_n]; exact hg_ht_le,
                    by rw [hho_n]; exact hho_cap, hpref_n, by rw [hnd_e]; exact hcv_n ▸ hgat_gn,
                    by rw [hho_n]; exact hcv_n ▸ hht_n,
                    Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, by rw [hho_n]; exact hlay_n⟩, hmn,
                    fun er sj mj hdwj hcvj hflj _ _ hreprj hprefj hhtj hqj hfrj he2u hmj => ?_⟩
                  c0_hsplit
                  · c0_hsteps!; exact hQ 20#64 sj mj hdwj (hcvj.trans hcv_n) (hflj.trans hfl_n)
                      ((hcvj.trans hcv_n) ▸ hreprj) (Or.inr rfl) (fun _ => he2u hc) hmj
                  · rw [hho_n] at hhtj hqj hfrj
                    have hokj := wlStOk_of_eval hok_n hc_cap hdwj hcvj hflj hreprj hprefj hhtj hqj
                      (fun idx h1 h2 => hfrj (by simpa using hc) idx h1 h2)
                    clear hc; c0_hfast_nogrp
                    refine wp_join_group (fun () m_nd => ∃ snd : FullState,
                      WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off
                        inq_off q_off ht_off ht_sz_o.toNat occ_end.toNat scr0 snd ∧
                      (FullMem c snd ⋆ R) m_nd)
                      (fun _ ⟨⟩ m_nd ⟨snd, hok_nd, hm_nd⟩ => ?_)
                      (fun _ hJrel => ?_)
                    · c0_hsteps!; rw [hnd2_e]; exact ihn (ticks_n + 2, nxt, ()) m_nd
                        (by dsimp only; rw [htn2_n]; omega) ⟨snd, by rw [htn2_n]; omega,
                          by rw [htn2_n]; omega, fun h => by rw [htn2_n] at h; omega,
                          hnxt_p, hok_nd, hm_nd⟩
                    · c0_hsplit
                      · clear hc; c0_hfast_nogrp; rw [hnd1_e]
                        exact wl_relink_step Γ hFind ho_pos hopow hnd_lo hnd_2 hnd_m3 hrl_lt
                          hokj hmj (fun m' hm' => hJrel () m' hm')
                      · c0_hsteps!; exact hJrel () mj ⟨sj, hokj, hmj⟩
                all_goals (c0_hsteps!; exact hJnd () mn ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩)
              all_goals (c0_hsteps!; exact hJnd () mn ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩)
            all_goals (c0_hsteps!; exact hJnd () mn ⟨sn, htn_lo, htn_hi, htn_eq, hok_n, hmn⟩)
        all_goals (c0_hsteps!; exact hjout () mo ⟨so, hok_o, hmo⟩)
      all_goals (c0_hsteps!; exact hjout () mo ⟨so, hok_o, hmo⟩)
    all_goals (c0_hsteps!; exact hjout () mo ⟨so, hok_o, hmo⟩)
  · clear hseq0
    c0_hsteps_nogrp; c0_hsplit
    · have htk_lt : ticks.toNat < tlim.toNat := hc; clear hc; c0_hsteps_nogrp; c0_hsplit
      · clear hc; c0_hsteps_nogrp; c0_hsplit
        · have hg_lt : g.toNat < g_len.toNat := hc
          obtain ⟨hgat_1, hseq_next⟩ := congGateSeqOk_inv_lt hseq_1 hg_lt
          have ⟨lhs0, mw1, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, _, _, hrhs_1, _⟩ := hgat_1
          have hg1_mod : (g + 1).toNat = g.toNat + 1 := by
            rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]
            exact Nat.mod_eq_of_lt (by omega)
          have hg1_arr : (g + 1).toNat < s1.scratch.scratch_buf.length := by rw [hg1_mod]; omega
          have hs1_g1 : s1.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mw1 := by
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem hg1_arr, hg1_mod, hpref_1 _ (by omega), hscr0_g1]
          have hs1_g1' : s1.scratch.scratch_buf[(g.toNat + 1) % 18446744073709551616]'(by
              rw [Nat.mod_eq_of_lt (by omega : g.toNat + 1 < 18446744073709551616)]; omega) =
              mw1 := by
            have hmod : (g.toNat + 1) % 18446744073709551616 = (g + 1).toNat := by
              rw [hg1_mod, Nat.mod_eq_of_lt (by omega)]
            rw [list_getElem_congr hmod _ hg1_arr]; exact hs1_g1
          c0_hsteps_nogrp
          refine wp_join_group
            (fun (arity, ()) ma_1 => ma_1 = m1 ∧
              arity.toNat = congGateArity mw1 ∧ arity.toNat ≤ g_len.toNat)
            (fun _ ⟨arity, ⟨⟩⟩ ma_1 ⟨hma_1, har_eq, har_le⟩ => ?_)
            (fun _ hJa => by
              c0_hsplit
              · have ht3 : (mw1 >>> 28) = 3#32 := by simpa [hs1_g1'] using hc
                c0_hsteps!; rw [hs1_g1]; exact hJa (mw1 &&& 0x0FFFFFFF#32, ()) m1
                  ⟨rfl, (congGateArity_of_eq3 ht3).symm,
                    by rw [congGateArity_of_eq3 ht3] at hbd_g; omega⟩
              · have hne3 : (mw1 >>> 28) ≠ 3#32 := fun h => hc (by simpa [hs1_g1'] using h)
                c0_hsteps!; rw [hs1_g1]; exact hJa (mw1 &&& 0xFF#32, ()) m1
                  ⟨rfl, (congGateArity_of_ne3 hne3).symm,
                    by rw [congGateArity_of_ne3 hne3] at hbd_g; omega⟩)
          subst ma_1
          have htk_63 : ticks.toNat < 2 ^ 63 - 1 := Nat.lt_of_lt_of_le htk_lt htlim_le
          have htk2_n : (ticks + 2#64).toNat = ticks.toNat + 2 := by
            rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl]
            exact Nat.mod_eq_of_lt (by omega)
          have hng : (g + 2#64 + BitVec.setWidth 64 arity).toNat =
              g.toNat + 2 + arity.toNat := by
            rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
              show (2#64 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega : g.toNat + 2 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : g.toNat + 2 + arity.toNat < 2 ^ 64)]
          have hseq_next' : CongGateSeqOk congAndArityMax F_cur cv0 scr0 g_len.toNat
              (g + 2#64 + BitVec.setWidth 64 arity).toNat := by
            rw [hng, har_eq]; simpa [hscr0_g1] using hseq_next
          rw [hho_eq', hhs_eq']; c0_hsteps!; c0_hcall hEval
          refine ⟨congAndArityMax, c, F0, F_cur, s1, scr0, g_len.toNat, R,
            Nat.le_refl _, rfl, hdw_1, hcv_1 ▸ hrepr_1, by rw [hhs_n]; exact hht_pos,
            by rw [hhs_n]; exact Nat.lt_of_le_of_lt hht_bnd (by decide), hg_lt,
            by rw [hho_n]; exact hg_ht_le,
            by rw [hho_n, hhs_n]; exact hht_cap, hpref_1, hcv_1 ▸ hgat_1,
            by rw [hho_n, hhs_n]; exact hcv_1 ▸ hht_1,
            Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, by rw [hho_n, hhs_n]; exact hlay_1⟩, hm1,
            fun er sj mj hdwj hcvj hflj _ _ hreprj hprefj hhtj hqj hfrj he2u hmj => ?_⟩
          c0_hsplit
          · c0_hsteps!; exact hQ 20#64 sj mj hdwj (hcvj.trans hcv_1) (hflj.trans hfl_1)
              ((hcvj.trans hcv_1) ▸ hreprj) (Or.inr rfl) (fun _ => he2u hc) hmj
          · rw [hho_n, hhs_n] at hhtj hqj hfrj
            have hokj := wlStOk_of_eval hok_1 hc_cap hdwj hcvj hflj hreprj hprefj hhtj hqj
              (fun idx h1 h2 => hfrj (by simpa using hc) idx h1 h2)
            have hscrl_j := hdwj.1.scratch_ok.scratch_buf_len; clear hc; c0_hsteps_nogrp
            refine wp_join_group
              (fun (occ_e', ()) me => ∃ se : FullState, g_len.toNat ≤ occ_e'.toNat ∧
                occ_e'.toNat ≤ ctrl_off.toNat ∧ (occ_e'.toNat - g_len.toNat) % 3 = 0 ∧
                WlStOk c F0 F_cur fuel0 cv0 g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
                  q_off ht_off ht_sz occ_e'.toNat scr0 se ∧ (FullMem c se ⋆ R) me)
              (fun _ ⟨occ_e', ⟨⟩⟩ me ⟨se, hoe_lo', hoe_hi', hoe_m3', hoke', hme'⟩ => by
                c0_hsteps!; exact ih1 (occ_e', ticks + 2#64, g + 2#64 + BitVec.setWidth 64 arity,
                  ()) me (by dsimp only; rw [hng, har_eq]; exact Nat.sub_lt_sub_left hg_lt (by
                    have := har_eq ▸ hbd_g; omega))
                  ⟨se, by rw [hng, har_eq]; exact hbd_g, hoe_lo', hoe_hi', hoe_m3',
                    by rw [htk2_n]; omega, hseq_next', hoke', hme'⟩)
              (fun _ hJocc => ?_)
            c0_hsplit
            · clear hc; c0_hsplit
              · have hfit : occ_end.toNat + (1 + arity.toNat) * 3 ≤ ctrl_off.toNat := by
                  rw [show (1 : BitVec 64).toNat = 1 from rfl,
                    show (3 : BitVec 64).toNat = 3 from rfl,
                    Nat.mod_eq_of_lt (by omega : 1 + arity.toNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : occ_end.toNat + (1 + arity.toNat) * 3 < 2 ^ 64)]
                    at hc
                  exact hc
                clear hc
                exact wl_push_gate_wp Γ hFind hc_cap ho_pos hopow hg_lt hgat_1 hscr0_g1 har_eq
                  hfit hoe_lo hoe_m3 hokj hmj (fun occ_e' me h => hJocc (occ_e', ()) me h)
              all_goals
                (c0_hsteps!; exact hJocc (occ_end, ()) mj ⟨sj, hoe_lo, hoe_hi, hoe_m3, hokj, hmj⟩)
            all_goals
              (c0_hsteps!; exact hJocc (occ_end, ()) mj ⟨sj, hoe_lo, hoe_hi, hoe_m3, hokj, hmj⟩)
        all_goals (c0_hsteps!; exact hJp2 () m1 ⟨s1, hok_1, hm1⟩)
      all_goals (c0_hsteps!; exact hJp2 () m1 ⟨s1, hok_1, hm1⟩)
    all_goals (c0_hsteps!; exact hJp2 () m1 ⟨s1, hok_1, hm1⟩)

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
