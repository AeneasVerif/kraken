module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2b

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Proofs — Part 2b2

Builds on `FullM6CongSubstProof2b` to prove the parametric `(Γ : Env)` `Func.wp` contract for:
19. `full_cong_eval_gate` (`full_cong_eval_gate_wp`, `m6CongEvalGateSpec`)

All proofs operate within the UNSAT-only `FullDenseInvW` / `M6CongHtInv` / `M6QueueCtx`
invariants (`0 sorry`, `0 maxHeartbeats`, `≤ 100` cols/line).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullCongTactics M6bHeadTactics

section EvalGateProof

private theorem c0_load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

private theorem c0_load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h1 : 1 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'h1) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 1#64) (by simpa using h1) hm

private theorem c0_load_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h2 : 2 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 8#64) = some (s.core.tmp[2]'h2) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 2#64) (by simpa using h2) hm

private theorem c0_store_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h0 : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 0#64) v (by simpa using h0) hm

private theorem c0_store_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h1 : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 1#64) v (by simpa using h1) hm

private theorem c0_store_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h2 : 2 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 8#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 2 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 8#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 2#64) v (by simpa using h2) hm

attribute [local c0_load] c0_load_full_tmp0 c0_load_full_tmp1 c0_load_full_tmp2
attribute [local c0_store] c0_store_full_tmp0 c0_store_full_tmp1 c0_store_full_tmp2

theorem full_cong_eval_gate_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullSortU32Spec a m Q X →
      Γ "full_sort_u32" [i64, i32] [] a m Q X)
    (hUnit : ∀ a m Q X, m3CongUnitFoldSpec a m Q X →
      Γ "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X)
    (hEquiv : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X)
    (hAndMatch : ∀ a m Q X, m6CongAndMatchSpec a m Q X →
      Γ "full_cong_and_match" [i64, i32, i32] [.bool] a m Q X)
    (hXorMatch : ∀ a m Q X, m6CongXorMatchSpec a m Q X →
      Γ "full_cong_xor_match" [i64, i32, i32] [i32] a m Q X)
    (hEnq : ∀ a m Q X, m6CongEnqVarSpec a m Q X →
      Γ "full_cong_enq_var" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, m6CongEvalGateSpec a m Q X →
      Func.wp Γ full_cong_eval_gate_body a m Q X := by
  rintro ⟨h, g, ht_off, ht_sz, next_ep, ctrl_off, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, scr0, g_len, R, rfl, hdw0, hrepr0, hht_pos, hht_bnd, hg_lt,
     hg_le_ht, hht_le, hpref0, hgat_g0, hht0, hq0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  let ar0 := s0.core.arena; let alen0 := s0.core.arena_len
  let scr_init := s0.scratch.scratch_buf
  let ctx : M6EvCtx :=
    ⟨c, F0, F_cur, fuel0, ar0, alen0, cv0, g_len, ht_off.toNat, ht_sz.toNat,
     ctrl_off.toNat, scr0, scr_init, R⟩
  have hok0 : M6EvStOk ctx s0 :=
    ⟨hdw0, rfl, rfl, rfl, rfl, hrepr0, hht0, hq0, m6ScrFrame_refl hdw0.1.scratch_ok.scratch_buf_len⟩
  have hexit : M6EvOutCtx ctx s0 Q :=
    ⟨rfl, rfl, rfl, rfl, rfl, hg_le_ht, hht_le, hpref0, hq0, hQ⟩
  have hlen0 := hdw0.1; have hw0 := hdw0.2.1; have hcl0 := hdw0.2.2.2.2.2.1
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hrl0 := hlen0.core_ok.repr_len; have htmpl0 := hlen0.core_ok.tmp_len_arr
  have hscrl0 := hlen0.scratch_ok.scratch_buf_len; have hvlen0 := hlen0.core_ok.vals_len
  clear hdw0 hrepr0 hht0 hlen0
  have hgat_g0' := hgat_g0
  obtain ⟨lhs0, mword, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, har_cv, har_31, hrhs0, hsem0⟩ :=
    hgat_g0'
  have hg_arr : g.toNat < s0.scratch.scratch_buf.length := by omega
  have hg1_n : (g + 1).toNat = g.toNat + 1 := by
    rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hg1_arr : (g + 1).toNat < s0.scratch.scratch_buf.length := by omega
  have hst_g : s0.scratch.scratch_buf[g.toNat]'hg_arr = lhs0 :=
    list_getElem_eq_of_eqD hg_arr ((hpref0 g.toNat hg_lt).trans hscr0_g)
  have hst_g1 : s0.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mword :=
    list_getElem_eq_of_eqD hg1_arr
      (by rw [hg1_n]; exact (hpref0 (g.toNat + 1) (by omega)).trans hscr0_g1)
  let tag := mword >>> 28; let arity := mword &&& 0xFF#32
  m6b_steps
  m6b_split
  · m6b_let
    exact m6Ev_exit hexit hok0 hm0 false false
  · clear hc; m6b_split
    · m6b_let
      exact m6Ev_exit hexit hok0 hm0 false false
    · clear hc; m6b_split
      · m6b_let
        exact m6Ev_exit hexit hok0 hm0 false false
      · clear hc
        m6b_steps; m6b_call hFind
        refine ⟨F_cur, 2 * cv0, s0.core.repr, FullReprRest c s0 ⋆ R, m6EvStOk_repr hok0,
          by rw [hst_g]; exact hlhs0_lt, focus_full_repr hm0,
          fun lhs repr1 m1 hrl1 hrepr1 _ hlhs_lt hlhs_eqv hm1 => ?_⟩
        clear hm0
        have hm1' : (FullMem c (wsState s0 repr1 s0.core.tmp) ⋆ R) m1 := unfocus_full_repr hm1
        clear hm1
        have hlhs_eqv0 : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat := by
          rwa [hst_g] at hlhs_eqv
        m6b_steps
        refine wp_loop_inv (ts := [i32])
          (M6EvFindInv ctx s0 g.toNat arity.toNat)
          (fun (i, ()) _ => arity.toNat - i.toNat)
          (fun Ji hJi => by
            m6b_let; exact hJi (0#32, ()) m1 ⟨repr1, s0.core.tmp, hrl1.trans hrl0, htmpl0,
              Nat.zero_le _, hrepr1, fun _ h => absurd h (Nat.not_lt_zero _), hm1'⟩)
          (fun Ji (i, ()) mi ⟨repri, tmpi, hrli, htli, hi_le, hrepri, htmp_i, hmi⟩ ihi => ?_)
        have hoki := m6EvStOk_wsState hok0 hrli htli hrepri
        dsimp only [ctx] at hrli htli hrepri htmp_i
        have har_def : arity.toNat = (mword &&& 0xFF#32).toNat := rfl
        m6b_split
        · have hi_lt : i.toNat < arity.toNat := bv32_ult_lt (by rw [hst_g1] at hc; exact hc)
          obtain ⟨ri, hri_get, hri_lt⟩ := hrhs0 i.toNat (by omega)
          have hg2i_n : (g + 2 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat :=
            bv64_add_zext32 (k := 2) (by omega)
          have hg2i_arr : (g + 2 + i.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
            rw [hg2i_n]; omega
          have hst_g2i : s0.scratch.scratch_buf[(g + 2 + i.setWidth 64).toNat]'hg2i_arr = ri :=
            scr_g2i_get hpref0 hri_get (by omega) hg2i_n hg2i_arr
          have hi_tmp : (i.setWidth 64).toNat < tmpi.length := by rw [bv_zext32_toNat]; omega
          have hi1_n : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_lt_of (by omega)
          m6b_steps; m6b_call hFind
          refine ⟨F_cur, 2 * cv0, repri, FullReprRest c (wsState s0 repri tmpi) ⋆ R, hrepri,
            by dsimp only [wsState]; rw [hst_g2i]; exact hri_lt, focus_full_repr hmi,
            fun rval repri' mi' hrl_i' hrepr_i' _ hrval_lt hrval_eqv hmi' => ?_⟩
          have hmi'' : (FullMem c (wsState s0 repri' tmpi) ⋆ R) mi' := ws_unfocus_repr hmi'
          clear hmi'
          have hfs_tmp := focus_full_tmp hmi''; clear hmi''
          generalize hR_tmp : FullTmpRest c (wsState s0 repri' tmpi) ⋆ R = R_tmp at hfs_tmp
          m6b_steps; subst hR_tmp
          rw [bv_zext32_toNat] at hm
          exact ihi (i + 1#32, ()) m (by dsimp only; omega)
            ⟨repri', tmpi.set i.toNat rval, hrl_i'.trans hrli,
             by rw [List.length_set]; exact htli, by omega, hrepr_i',
             fun k' hk' => ws_find_tmp_step htmp_i htli (by omega) hri_get hrval_lt
               (by dsimp only [wsState] at hrval_eqv; rwa [hst_g2i] at hrval_eqv)
               k' (hi1_n ▸ hk'),
             ws_unfocus_tmp hm⟩
        · have hi_eq : i.toNat = arity.toNat := by
            have hnot : ¬ i.toNat < arity.toNat := by
              rw [hst_g1] at hc; dsimp only [arity]; exact bv32_ult_not_lt hc
            omega
          have htmp_i_len : arity.toNat ≤ tmpi.length := by omega
          have htmp_i' : ∀ (k' : Nat) (hk' : k' < arity.toNat),
              (tmpi[k']'(by omega)).toNat < 2 * cv0 ∧
              LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
                (tmpi[k']'(by omega)).toNat := fun k' hk' => by
            have h := htmp_i k' (by omega)
            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
          clear hc; m6b_to_group
          refine wp_join_group (ts := [i32, i32, i32, .bool, .bool])
            (fun (lhs', _iw, harity, need_hash, _changed', ()) mj =>
              M6EvOut ctx lhs' tag harity need_hash mj)
            ?_ ?_
          · rintro _ ⟨lhs', _iw, harity, need_hash, changed', ⟨⟩⟩ mj h
            unfold M6EvOut at h
            obtain ⟨stj, hokj, hgatej, hlhsj_lt, hmj⟩ := h
            clear hSort
            m6b_to_group
            refine wp_join_group (ts := [i32, .bool, .bool])
              (fun (_iwk, _chk, _keepk, ()) mk => ∃ stk : FullState,
                M6EvStOk ctx stk ∧ (FullMem c stk ⋆ R) mk)
              ?_ ?_
            · rintro _ ⟨_iwk, chk, keepk, ⟨⟩⟩ mk ⟨stk, hokk, hmk⟩
              clear hUnit hEquiv hAndMatch hXorMatch
              m6b_to_group
              refine wp_loop_inv (ts := [i64])
                (fun (_te, ()) m_t => ∃ stt : FullState,
                  stt.core.trail_end = stk.core.trail_end ∧
                  M6EvStOk ctx stt ∧ (FullMem c stt ⋆ R) m_t)
                (fun (te, ()) _ => stk.core.trail_end - te.toNat)
                (fun Jt hJt => by
                  m6b_steps; exact hJt (_, ()) mk ⟨stk, rfl, hokk, hmk⟩)
                (fun Jt (te, ()) m_t ⟨stt, hte_eq, hokt, hmt⟩ iht => ?_)
              m6b_split
              · have hcv_t : stt.core.cur_vars = cv0 := m6EvStOk_cv hokt
                have hcv_le_t : stt.core.cur_vars ≤ c.max_vars :=
                  (m6EvStOk_dw hokt).1.core_ok.cur_vars_le
                have htrll_t : stt.core.trl.length = c.max_vars :=
                  (m6EvStOk_dw hokt).1.core_ok.trl_len
                have hte_lt : te.toNat < stt.core.trail_end := by
                  have hlt := bv64_ult_lt hc
                  rwa [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by
                      have := ev_trail_end_le_cur_vars (m6EvStOk_wit hokt); omega)] at hlt
                have hte_end : stt.core.trail_end ≤ cv0 := by
                  rw [← hcv_t]
                  exact ev_trail_end_le_cur_vars (m6EvStOk_wit hokt)
                have hte_trl : te.toNat < stt.core.trl.length := by
                  rw [htrll_t]; omega
                have htl_lt : (stt.core.trl[te.toNat]'hte_trl).toNat < 2 * cv0 := by
                  have h := (m6EvStOk_wit hokt).trail_lits_lt te.toNat hte_lt
                  rw [List.getElem?_eq_getElem hte_trl, Option.getD_some, hcv_t] at h
                  exact h
                have hte1 : (te + 1#64).toNat = te.toNat + 1 :=
                  bv64_add1_toNat (n := stt.core.trail_end) hte_lt (by omega)
                m6b_steps; m6b_call hEnq
                refine m6Ev_enq_core hexit hokt rfl hmt fun st1 m1 hok1 hc1 hm1 => ?_
                m6b_steps; m6b_call hFind
                refine ⟨F_cur, 2 * cv0, st1.core.repr, FullReprRest c st1 ⋆ R,
                  m6EvStOk_repr hok1, htl_lt, focus_full_repr hm1,
                  fun rtl repr_t m2 hrl_t hrepr_t _ hrtl_lt _ hm2 => ?_⟩
                let st2 : FullState := { st1 with core := { st1.core with repr := repr_t } }
                have hm2' : (FullMem c st2 ⋆ R) m2 := unfocus_full_repr hm2
                have hok2 := m6EvStOk_with_repr hok1
                  (hrl_t.trans (m6EvStOk_dw hok1).1.core_ok.repr_len) hrepr_t
                m6b_steps; m6b_call hEnq
                refine m6Ev_enq_core hexit hok2 rfl hm2' fun st3 m3 hok3 hc3 hm3 => ?_
                m6b_let; exact iht (te + 1#64, ()) m3 (by dsimp only; omega)
                  ⟨st3, by rw [hc3, show st2.core.trail_end = st1.core.trail_end from rfl, hc1]
                           exact hte_eq, hok3, hm3⟩
              · clear hc; m6b_split
                · have hne0 : stt.core.inconsistent ≠ 0#64 := bne_iff_ne.mp hc
                  m6b_steps
                  exact m6Ev_ret2 hexit hokt (unsat_of_inconsistent_w (m6EvStOk_wit hokt) hne0) hmt
                · clear hc; m6b_to_group
                  refine wp_join_group (ts := [i64])
                    (fun (v1, ()) mv => v1 = (if chk then 1#64 else 0#64) ∧ mv = m_t)
                    (fun _ ⟨v1, ⟨⟩⟩ mv ⟨hv1, hmv⟩ => by
                      m6b_to_group
                      refine wp_join_group (ts := [i64])
                        (fun (v2, ()) mw => v2 = (if keepk then 4#64 else 0#64) ∧ mw = mv)
                        (fun _ ⟨v2, ⟨⟩⟩ mw ⟨hv2, hmw⟩ => by
                          m6b_steps; rw [hmw, hmv]
                          have hg := m6Ev_exit hexit hokt hmt chk keepk
                          dsimp only at hv1 hv2 hg
                          rw [hv1, hv2]; exact hg)
                        (fun Jk hJk => by
                          m6b_split
                          · have hk' : keepk = true := hc
                            m6b_let; refine hJk (4#64, ()) mv ⟨?_, rfl⟩
                            simp only [hk', ite_true]
                          · have hk' : keepk = false := hc
                            m6b_let; refine hJk (0#64, ()) mv ⟨?_, rfl⟩
                            simp only [hk', Bool.false_eq_true, ite_false]))
                    (fun Jc hJc => by
                      m6b_split
                      · have hc' : chk = true := hc
                        m6b_let; refine hJc (1#64, ()) m_t ⟨?_, rfl⟩
                        simp only [hc', ite_true]
                      · have hc' : chk = false := hc
                        m6b_let; refine hJc (0#64, ()) m_t ⟨?_, rfl⟩
                        simp only [hc', Bool.false_eq_true, ite_false])
            · intro Jex hJex; m6b_split
              · have hnh : need_hash = true := hc
                clear hc; m6b_split
                · obtain ⟨hhar_cv, hgat0, hgat1, hgat2⟩ := hgatej hnh
                  have hlhs'_lt := hlhsj_lt hnh
                  have hhar_tmp : harity.toNat ≤ stj.core.tmp.length := by
                    rw [(m6EvStOk_dw hokj).1.core_ok.tmp_len_arr]
                    exact Nat.le_trans hhar_cv hcv_le
                  clear hc hUnit; m6b_to_group
                  refine wp_loop_inv (ts := [i32, i64])
                    (fun (ih_v, _hv, ()) mhv => mhv = mj ∧ ih_v.toNat ≤ harity.toNat)
                    (fun (ih_v, _, ()) _ => harity.toNat - ih_v.toNat)
                    (fun Jhv hJhv => by m6b_steps; exact hJhv (0#32, _, ()) mj ⟨rfl, Nat.zero_le _⟩)
                    (fun Jhv (ih_v, _hv, ()) mhv ⟨hmhv, hih_le⟩ ih_hv => ?_)
                  subst mhv; m6b_split
                  · have hih_lt : ih_v.toNat < harity.toNat := bv32_ult_lt hc
                    have hih_arr : (ih_v.setWidth 64).toNat < stj.core.tmp.length := by
                      rw [bv_zext32_toNat]; omega
                    have hih1 : (ih_v + 1#32).toNat = ih_v.toNat + 1 :=
                      bv32_add1_lt_of (by omega)
                    m6b_steps
                    exact ih_hv (ih_v + 1#32, _, ()) mj (by dsimp only; omega) ⟨rfl, by omega⟩
                  · clear hc; m6b_to_group
                    refine wp_loop_break_group (brkTs := [.bool, .bool, i64, i64, .bool])
                      (lpTs := [i64, i64, .bool])
                      (fun (ch_p, keep_p, _, _, _, ()) mp => ∃ stp : FullState,
                        M6EvStOk ctx stp ∧ (FullMem c stp ⋆ R) mp)
                      (M6EvProbeInv ctx stj ht_sz.toNat)
                      ?_ ?_ ?_
                    · rintro _ ⟨ch_p, keep_p, _, _, _, ⟨⟩⟩ mp ⟨stp, hokp, hmp⟩
                      m6b_let; exact hJex (ih_v, ch_p, keep_p, ()) mp ⟨stp, hokp, hmp⟩
                    · rintro Bp Lp remp ⟨slot, probes, seen_self, ⟨⟩⟩ mp hBp hLp
                        ⟨stp, hslot_lt, hpr_le, rfl, htmp_p, hokp, hmp⟩
                      have hscrl_p := (m6EvStOk_dw hokp).1.scratch_ok.scratch_buf_len
                      have hrl_p := (m6EvStOk_dw hokp).1.core_ok.repr_len
                      have hrepr_p := m6EvStOk_repr hokp
                      have hht_p := m6EvStOk_ht hokp
                      dsimp only [ctx] at hscrl_p hrl_p hrepr_p hht_p
                      have hpref_p := m6ScrFrame_pref hg_le_ht hht_le hpref0 hq0
                        (m6EvStOk_fr hokp)
                      m6b_split
                      · have hpr_lt : probes.toNat < 64 := bv64_ult_lt hc
                        have hhts_n : (ht_off + slot).toNat = ht_off.toNat + slot.toNat := by
                          show (ht_off.toNat + slot.toNat) % 2 ^ 64 = ht_off.toNat + slot.toNat
                          exact Nat.mod_eq_of_lt (by omega)
                        have hhts_arr : (ht_off + slot).toNat < stp.scratch.scratch_buf.length := by
                          omega
                        let ent := stp.scratch.scratch_buf[(ht_off + slot).toNat]'hhts_arr
                        have hent_slot : stp.scratch.scratch_buf[ht_off.toNat + slot.toNat]?.getD
                            0xFFFFFFFF#32 = ent := by
                          rw [← hhts_n, List.getElem?_eq_getElem hhts_arr, Option.getD_some]
                        clear hc; m6b_split
                        · m6b_to_group; refine wp_join_group (ts := [])
                            (fun () mins => ∃ stins : FullState,
                              M6EvStOk ctx stins ∧ (FullMem c stins ⋆ R) mins)
                            (fun _ ⟨⟩ mins ⟨stins, hokins, hmins⟩ => by
                              m6b_let
                              exact hBp (changed', true, slot, probes, seen_self, ()) mins
                                ⟨stins, hokins, hmins⟩)
                            ?_
                          intro Jins hJins; m6b_split
                          · m6b_let; exact hJins () mp ⟨stp, hokp, hmp⟩
                          · m6b_split
                            · have hi32 : i32.bytes = 4 := rfl; m6b_steps
                              have hm_ins : (FullMem c { stp with scratch := { stp.scratch with
                                  scratch_buf :=
                                    stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat)
                                      (g.setWidth 32)
                                  res_sz := stp.scratch.res_sz + 1#64 } } ⋆ R) m := by
                                rw [hhts_n] at hm; exact hm
                              have hok_ins := m6EvStOk_ht_insert hokp rfl rfl rfl rfl
                                hg_lt hg_le_ht hht_le hslot_lt hgat_g0
                              exact hJins () m ⟨_, hok_ins, hm_ins⟩
                            · m6b_let; exact hJins () mp ⟨stp, hokp, hmp⟩
                        · have hent_ne : ent ≠ 0xFFFFFFFF#32 := beq_eq_false_iff_ne.mp hc
                          clear hc; m6b_split
                          · have hslot_next_lt : ((slot + 1#64) &&& (ht_sz - 1#64)).toNat <
                                ht_sz.toNat := bv64_and_sub1_lt hht_pos
                            have hpr1 : (probes + 1#64).toNat = probes.toNat + 1 :=
                              bv64_add1_toNat (n := 64) hpr_lt (by decide)
                            m6b_steps
                            exact hLp (64 - (probes + 1#64).toNat)
                              ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, true, ()) mp
                              (by omega) ⟨stp, hslot_next_lt, by omega, rfl, htmp_p, hokp, hmp⟩
                          · have hent_gate : M6GateAt F_cur cv0 scr0 g_len ent.toNat := by
                              rcases hht_p slot.toNat hslot_lt with he | hg_e
                              · rw [hent_slot] at he; exact absurd he hent_ne
                              · rwa [hent_slot] at hg_e
                            have ⟨elhs, emword, he0, he1, helhs_lt, hbd_e, _, _, herhs, hsem_e⟩ :=
                              hent_gate
                            have he0_arr : ent.toNat < stp.scratch.scratch_buf.length := by omega
                            have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
                              rw [BitVec.toNat_add, bv_zext32_toNat]
                              show (ent.toNat + 1) % 2 ^ 64 = ent.toNat + 1; omega
                            have he1_arr : (ent.setWidth 64 + 1).toNat <
                                stp.scratch.scratch_buf.length := by omega
                            have hst_e0 : stp.scratch.scratch_buf[(ent.setWidth 64).toNat]'
                                (by rw [bv_zext32_toNat]; exact he0_arr) = elhs := by
                              have h := (hpref_p ent.toNat (by omega)).trans he0
                              rw [list_getElem_congr (bv_zext32_toNat ent) _ he0_arr]
                              rw [List.getElem?_eq_getElem he0_arr] at h; exact Option.some.inj h
                            have hst_e0' :
                                stp.scratch.scratch_buf[(BitVec.setWidth 64
                                  stp.scratch.scratch_buf[(ht_off + slot).toNat]).toNat]'he0_arr =
                                  elhs := hst_e0
                            have hst_e1 :
                                stp.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr =
                                  emword := by
                              have h := (hpref_p (ent.toNat + 1) (by omega)).trans he1
                              rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h
                              exact Option.some.inj h
                            have hslot_next_lt : ((slot + 1#64) &&& (ht_sz - 1#64)).toNat <
                                ht_sz.toNat := bv64_and_sub1_lt hht_pos
                            have hpr1 : (probes + 1#64).toNat = probes.toNat + 1 :=
                              bv64_add1_toNat (n := 64) hpr_lt (by decide)
                            clear hc; m6b_to_group
                            refine wp_join_group (ts := [.bool, .bool])
                              (fun _ mnxt => ∃ stn : FullState,
                                stn.core.tmp = stj.core.tmp ∧ M6EvStOk ctx stn ∧
                                (FullMem c stn ⋆ R) mnxt)
                              ?_ ?_
                            · rintro _ ⟨_, _, ⟨⟩⟩ mnxt ⟨stn, htmp_n, hokn, hmn⟩
                              m6b_let; exact hLp (64 - (probes + 1#64).toNat)
                                ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, seen_self, ())
                                mnxt (by omega)
                                ⟨stn, hslot_next_lt, by omega, rfl, htmp_n, hokn, hmn⟩
                            · intro Jnxt hJnxt
                              have hjnxt_keep : ∀ b1 b2 : Val .bool, Jnxt (b1, b2, ()) mp :=
                                fun b1 b2 => hJnxt (b1, b2, ()) mp ⟨stp, htmp_p, hokp, hmp⟩
                              m6b_split
                              · have hetag_eq : emword >>> 28 = tag := by
                                  have hc1 : (stp.scratch.scratch_buf[
                                      (ent.setWidth 64 + 1).toNat]'he1_arr >>> 28 ==
                                    s0.scratch.scratch_buf[(g + 1).toNat]'hg1_arr >>> 28) = true :=
                                      hc
                                  have hc2 := beq_iff_eq.mp hc1
                                  rwa [hst_e1, hst_g1] at hc2
                                clear hc; m6b_to_group
                                refine wp_join_group (M6EvMatchInv ctx stp lhs') ?_ ?_
                                · rintro _ ⟨matched, mlhs, ⟨⟩⟩ mmatch
                                    ⟨repr_m, mclr_m, hrl_m, hml_m, hrepr_m, heqv_m, hmm⟩
                                  let stm : FullState :=
                                    { stp with core :=
                                      { stp.core with repr := repr_m
                                                      min_clr := mclr_m } }
                                  have hokm :=
                                    m6EvStOk_with_repr_mclr hokp hrl_m hml_m hrepr_m
                                  m6b_split
                                  · obtain ⟨hml_lt, hlhs_ent⟩ := heqv_m hc
                                    m6b_steps; m6b_call hEquiv
                                    refine m6Ev_equiv hokm hlhs'_lt hml_lt hlhs_ent hmm
                                      fun ef se me hoke _ hef2 hme => ?_
                                    m6b_split
                                    · m6b_let
                                      exact m6Ev_ret2 hexit hoke (hef2 (beq_iff_eq.mp hc)) hme
                                    · m6b_to_group
                                      refine wp_join_group (ts := [.bool])
                                        (fun (ch_ef, ()) mef => ∃ stef : FullState,
                                          M6EvStOk ctx stef ∧ (FullMem c stef ⋆ R) mef)
                                        (fun _ ⟨ch_ef, ⟨⟩⟩ mef ⟨stef, hokef, hmef⟩ => by
                                          m6b_let
                                          exact hBp (ch_ef, false, slot, probes, seen_self, ()) mef
                                            ⟨stef, hokef, hmef⟩)
                                        ?_
                                      intro Jef hJef; m6b_split
                                      · m6b_steps; m6b_call hEnq
                                        refine m6Ev_enq hexit hoke rfl hme fun s1 m1 hk1 _ hm1 => ?_
                                        m6b_steps; m6b_call hEnq
                                        refine m6Ev_enq hexit hk1 rfl hm1 fun s2 m2 hk2 _ hm2 => ?_
                                        m6b_steps; m6b_call hFind
                                        refine ⟨F_cur, 2 * cv0, s2.core.repr,
                                          FullReprRest c s2 ⋆ R, m6EvStOk_repr hk2,
                                          hlhs'_lt, focus_full_repr hm2,
                                          fun fl r3 m3 hrl3 hrepr3 _ _ _ hm3 => ?_⟩
                                        let s3 : FullState :=
                                          { s2 with core := { s2.core with repr := r3 } }
                                        have hm3' : (FullMem c s3 ⋆ R) m3 := unfocus_full_repr hm3
                                        have hk3 := m6EvStOk_with_repr hk2
                                          (hrl3.trans (m6EvStOk_dw hk2).1.core_ok.repr_len)
                                          hrepr3
                                        m6b_steps; m6b_call hEnq
                                        refine m6Ev_enq hexit hk3 rfl hm3'
                                          fun s4 m4 hk4 _ hm4 => ?_
                                        m6b_steps; m6b_call hFind
                                        refine ⟨F_cur, 2 * cv0, s4.core.repr,
                                          FullReprRest c s4 ⋆ R, m6EvStOk_repr hk4,
                                          hml_lt, focus_full_repr hm4,
                                          fun fm r5 m5 hrl5 hrepr5 _ _ _ hm5 => ?_⟩
                                        let s5 : FullState :=
                                          { s4 with core := { s4.core with repr := r5 } }
                                        have hm5' : (FullMem c s5 ⋆ R) m5 := unfocus_full_repr hm5
                                        have hk5 := m6EvStOk_with_repr hk4
                                          (hrl5.trans (m6EvStOk_dw hk4).1.core_ok.repr_len)
                                          hrepr5
                                        m6b_steps; m6b_call hEnq
                                        refine m6Ev_enq hexit hk5 rfl hm5'
                                          fun s6 m6 hk6 _ hm6 => ?_
                                        m6b_let; exact hJef (true, ()) m6 ⟨s6, hk6, hm6⟩
                                      · m6b_let; exact hJef (changed', ()) me ⟨se, hoke, hme⟩
                                  · m6b_steps
                                    exact hJnxt (_, _, ()) mmatch ⟨stm, htmp_p, hokm, hmm⟩
                                · intro Jm hJm; m6b_split
                                  · have htag0_eq : tag = 0#32 := ws_tag_eq hst_g1 hc
                                    obtain ⟨_, _, hand_eq⟩ := hgat0 htag0_eq
                                    m6b_steps; m6b_call hAndMatch
                                    refine ⟨c, F0, F_cur, stp, scr0, g_len, R, rfl,
                                      (m6EvStOk_dw hokp).1, m6EvStOk_wit hokp, m6EvStOk_cl hokp,
                                      m6EvStOk_cv hokp ▸ hrepr_p, by omega, hpref_p,
                                      by rw [m6EvStOk_cv hokp]; exact hent_gate,
                                      by rw [he1, Option.getD_some, hetag_eq, htag0_eq],
                                      by rw [m6EvStOk_cv hokp]; exact hhar_cv, hmp, ?_⟩
                                    intro ok_m repr_m mm _ hrl_m hrepr_m hok_and hmm
                                    m6b_steps; rw [hst_e0']
                                    exact hJm (ok_m, elhs, ()) mm
                                      ⟨repr_m, stp.core.min_clr, hrl_m,
                                       (m6EvStOk_dw hokp).1.core_ok.min_clr_len_arr,
                                       by rw [← m6EvStOk_cv hokp]; exact hrepr_m,
                                       fun hokt => ⟨helhs_lt,
                                         ws_match_and_equiv (htmp_p ▸ hand_eq) he0
                                           (hok_and hokt).2.2⟩,
                                       hmm⟩
                                  · clear hc; m6b_to_group
                                    refine wp_join_group (M6EvMatchInv ctx stp lhs')
                                      (fun _ ⟨m_ok, mlhs, ⟨⟩⟩ mf h => by
                                        m6b_let; exact hJm (m_ok, mlhs, ()) mf h)
                                      ?_
                                    intro Jmb hJmb; m6b_split
                                    · have htag1_eq : tag = 1#32 := ws_tag_eq hst_g1 hc
                                      have hhar_24 : 2 ≤ harity.toNat ∧ harity.toNat ≤ 4 :=
                                        ⟨(hgat1 htag1_eq).1, (hgat1 htag1_eq).2.1⟩
                                      m6b_steps; m6b_call hXorMatch
                                      refine ⟨c, F0, F_cur, stp, scr0, g_len, R, rfl,
                                        (m6EvStOk_dw hokp).1, m6EvStOk_wit hokp, m6EvStOk_cl hokp,
                                        m6EvStOk_cv hokp ▸ hrepr_p, by rw [m6EvStOk_cv hokp]; omega,
                                        by omega, hpref_p,
                                        by rw [m6EvStOk_cv hokp]; exact hent_gate,
                                        by rw [he1, Option.getD_some, hetag_eq, htag1_eq],
                                        by rw [m6EvStOk_cv hokp]; exact hhar_cv,
                                        by intro k hk; rw [htmp_p, m6EvStOk_cv hokp]
                                           exact (hgat1 htag1_eq).2.2.1 k hk,
                                        hmp, ?_⟩
                                      intro ml repr_m mclr_m mm _ hrl_m hml_m hrepr_m hok_xor hmm
                                      have hmm' : (FullMem c { stp with core :=
                                          { stp.core with repr := repr_m
                                                          min_clr := mclr_m } } ⋆ R) mm := hmm
                                      clear hmm
                                      m6b_to_group
                                      refine wp_unroll_group (fun Js_m hJs_m => ?_)
                                      dsimp only; m6b_split
                                      · have hml_ne : ml ≠ 0xFFFFFFFF#32 := bne_iff_ne.mp hc
                                        obtain ⟨_, _, hml_lt, hml_ev⟩ := hok_xor hml_ne
                                        m6b_steps; apply hJs_m; m6b_steps
                                        exact hJmb (true, ml, ()) mm
                                          ⟨repr_m, mclr_m, hrl_m, hml_m, m6EvStOk_cv hokp ▸ hrepr_m,
                                           fun _ => ⟨m6EvStOk_cv hokp ▸ hml_lt, ev_tag1_match_equiv
                                             (htag1_eq ▸ htmp_p ▸ hgatej hnh) hml_ev⟩,
                                           hmm'⟩
                                      · m6b_steps; apply hJs_m; m6b_steps; rw [hst_e0']
                                        exact hJmb (false, elhs, ()) mm
                                          ⟨repr_m, mclr_m, hrl_m, hml_m, m6EvStOk_cv hokp ▸ hrepr_m,
                                           (fun h => by cases h), hmm'⟩
                                    · clear hc; m6b_to_group
                                      refine wp_join_group (M6EvMatchInv ctx stp lhs')
                                        (fun _ ⟨m_ok, mlhs, ⟨⟩⟩ mf' h => by
                                          m6b_let; exact hJmb (m_ok, mlhs, ()) mf' h)
                                        ?_
                                      intro Jm2 hJm2; m6b_split
                                      · have he_tag2 : tag = 2#32 := ws_tag_eq hst_g1 hc
                                        clear hc; m6b_split
                                        rotate_left
                                        · m6b_let; rw [hst_e0']
                                          exact hJm2 (false, elhs, ()) mp
                                            ⟨stp.core.repr, stp.core.min_clr, hrl_p,
                                             (m6EvStOk_dw hokp).1.core_ok.min_clr_len_arr, hrepr_p,
                                             (fun h => by cases h), hmp⟩
                                        obtain ⟨har_ite, hite_s⟩ := hgat2 he_tag2
                                        have h3 : harity.toNat = 3 := by rw [har_ite]; decide
                                        have hite_e := ev_gate_tag2_ite
                                          (by rw [hetag_eq, he_tag2]) hsem_e
                                        have ha_e : (emword &&& 0xFF#32).toNat = 3 := hite_e.1
                                        obtain ⟨er0, her0_get, her0_lt⟩ := herhs 0 (by omega)
                                        obtain ⟨er1, her1_get, her1_lt⟩ := herhs 1 (by omega)
                                        obtain ⟨er2, her2_get, her2_lt⟩ := herhs 2 (by omega)
                                        have he2_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                          (g_len := g_len) (ent := ent) 2 (by omega) (by omega)
                                          (by omega)
                                        have he3_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                          (g_len := g_len) (ent := ent) 3 (by omega) (by omega)
                                          (by omega)
                                        have he4_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                          (g_len := g_len) (ent := ent) 4 (by omega) (by omega)
                                          (by omega)
                                        have hst_e2 := scr_e_get (g_len := g_len) 2 (by omega)
                                          hpref_p her0_get he2_arr (by omega)
                                        have hst_e3 := scr_e_get (g_len := g_len) 3 (by omega)
                                          hpref_p her1_get he3_arr (by omega)
                                        have hst_e4 := scr_e_get (g_len := g_len) 4 (by omega)
                                          hpref_p her2_get he4_arr (by omega)
                                        m6b_steps; m6b_call hFind
                                        refine ⟨F_cur, 2 * cv0, stp.core.repr,
                                          FullReprRest c stp ⋆ R, hrepr_p, hst_e2 ▸ her0_lt,
                                          focus_full_repr hmp,
                                          fun ec repra ma hrla hrepra _ _ hec_eqv hma => ?_⟩
                                        have hma' := unfocus_full_repr hma; clear hma
                                        m6b_steps; m6b_call hFind
                                        refine ⟨F_cur, 2 * cv0, repra,
                                          FullReprRest c { stp with core :=
                                            { stp.core with repr := repra } } ⋆ R,
                                          hrepra, hst_e3 ▸ her1_lt, focus_full_repr hma',
                                          fun et reprb mb hrlb hreprb _ _ het_eqv hmb => ?_⟩
                                        have hmb' := unfocus_full_repr hmb; clear hmb
                                        m6b_steps; m6b_call hFind
                                        refine ⟨F_cur, 2 * cv0, reprb,
                                          FullReprRest c { stp with core :=
                                            { stp.core with repr := reprb } } ⋆ R,
                                          hreprb, hst_e4 ▸ her2_lt, focus_full_repr hmb',
                                          fun ee reprc mc hrlc hreprc _ _ hee_eqv hmc => ?_⟩
                                        let stpc : FullState :=
                                          { stp with core := { stp.core with repr := reprc } }
                                        have hmc' : (FullMem c stpc ⋆ R) mc := by
                                          simpa only [stpc] using unfocus_full_repr hmc
                                        clear hmc
                                        have hite_e' : IteGateDef (cnfOfClauses F_cur) elhs.toNat
                                            ec.toNat et.toNat ee.toNat :=
                                          ite_eval_congr hite_e.2 (LitEquiv.refl _ _)
                                            (by rw [her0_get, Option.getD_some, ← hst_e2]
                                                exact hec_eqv)
                                            (by rw [her1_get, Option.getD_some, ← hst_e3]
                                                exact het_eqv)
                                            (by rw [her2_get, Option.getD_some, ← hst_e4]
                                                exact hee_eqv)
                                        have hstj_tl : stj.core.tmp.length = c.max_vars :=
                                          (m6EvStOk_dw hokj).1.core_ok.tmp_len_arr
                                        have hstp_tl : stp.core.tmp.length = c.max_vars :=
                                          (m6EvStOk_dw hokp).1.core_ok.tmp_len_arr
                                        have htmp_ge3 : 3 ≤ stpc.core.tmp.length := by
                                          change 3 ≤ stp.core.tmp.length; omega
                                        have ht0_eq := tmp_st_get (k := 0) htmp_p (by omega)
                                        have ht1_eq := tmp_st_get (k := 1) htmp_p (by omega)
                                        have ht2_eq := tmp_st_get (k := 2) htmp_p (by omega)
                                        m6b_to_group
                                        refine wp_join_group (ts := [i32, i32, i32])
                                          (fun (ec1, et1, ee1, ()) mfin => mfin = mc ∧
                                            IteGateDef (cnfOfClauses F_cur) elhs.toNat
                                              ec1.toNat et1.toNat ee1.toNat)
                                          (fun _ ⟨ec1, et1, ee1, ⟨⟩⟩ mfin ⟨hmfin, hite_1⟩ => by
                                            subst mfin; m6b_to_group
                                            refine wp_join_group (ts := [i32, i32, i32])
                                              (fun (ml', et', ee', ()) mfin2 => mfin2 = mc ∧
                                                ml'.toNat < 2 * cv0 ∧
                                                IteGateDef (cnfOfClauses F_cur) ml'.toNat
                                                  ec1.toNat et'.toNat ee'.toNat)
                                              (fun _ ⟨ml', et', ee', ⟨⟩⟩ mfin2
                                                  ⟨hmfin2, hml'_lt, hite_f⟩ => by
                                                subst mfin2; m6b_to_group
                                                refine wp_join_group (ts := [.bool])
                                                  (fun (b, ()) mj => mj = mc ∧
                                                    (b = true → ml'.toNat < 2 * cv0 ∧
                                                      LitEquiv (cnfOfClauses F_cur)
                                                        lhs'.toNat ml'.toNat))
                                                  (fun _ ⟨b, ⟨⟩⟩ mj ⟨hmj, hm⟩ => by
                                                    subst mj; m6b_let
                                                    exact hJm2 (b, ml', ()) mc
                                                      ⟨reprc, stp.core.min_clr,
                                                       hrlc.trans (hrlb.trans (hrla.trans hrl_p)),
                                                       (m6EvStOk_dw hokp).1.core_ok.min_clr_len_arr,
                                                       hreprc, hm, hmc'⟩)
                                                  ?_
                                                intro Jmi hJmi
                                                have ht0_a : 0 < stpc.core.tmp.length := by omega
                                                have ht1_a : 1 < stpc.core.tmp.length := by omega
                                                have ht2_a : 2 < stpc.core.tmp.length := by omega
                                                m6b_steps; m6b_split
                                                · have hc0 :
                                                      ec1 = stj.core.tmp[0]'(by omega) := by
                                                    have h : ec1 = stpc.core.tmp[0] :=
                                                      beq_iff_eq.mp hc
                                                    rw [h, ht0_eq,
                                                      List.getElem?_eq_getElem (by omega),
                                                      Option.getD_some]
                                                  clear hc; m6b_steps; m6b_split
                                                  · have hc1 : et' = stj.core.tmp[1]'(by omega) :=
                                                    by
                                                      have h : et' = stpc.core.tmp[1] :=
                                                        beq_iff_eq.mp hc
                                                      rw [h, ht1_eq,
                                                        List.getElem?_eq_getElem (by omega),
                                                        Option.getD_some]
                                                    clear hc; m6b_steps; m6b_split
                                                    · have hc2 :
                                                          ee' = stj.core.tmp[2]'(by omega) := by
                                                        have h : ee' = stpc.core.tmp[2] :=
                                                          beq_iff_eq.mp hc
                                                        rw [h, ht2_eq,
                                                          List.getElem?_eq_getElem (by omega),
                                                          Option.getD_some]
                                                      m6b_steps
                                                      exact hJmi (true, ()) mc ⟨rfl, fun _ =>
                                                        ⟨hml'_lt, ws_hash_ite_equiv (by omega)
                                                          hite_s hite_f hc0 hc1 hc2⟩⟩
                                                    · m6b_let
                                                      exact hJmi (false, ()) mc
                                                        ⟨rfl, fun h => by cases h⟩
                                                  · m6b_let
                                                    exact hJmi (false, ()) mc
                                                      ⟨rfl, fun h => by cases h⟩
                                                · m6b_let
                                                  exact hJmi (false, ()) mc
                                                    ⟨rfl, fun h => by cases h⟩)
                                              ?_
                                            intro Jf hJf; m6b_split
                                            · have hml_flip :
                                                  (elhs ^^^ 1#32).toNat < 2 * cv0 := by
                                                rw [bv32_xor1_eq_litNeg]
                                                exact bv32_xor1_lt_even helhs_lt
                                              m6b_steps; rw [hst_e0']
                                              refine hJf
                                                (elhs ^^^ 1#32, et1 ^^^ 1#32, ee1 ^^^ 1#32, ())
                                                mc ⟨rfl, hml_flip, ?_⟩
                                              rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg,
                                                bv32_xor1_eq_litNeg]
                                              exact iteGateDef_flip_out hite_1
                                            · m6b_let; rw [hst_e0']
                                              exact hJf (elhs, et1, ee1, ()) mc
                                                ⟨rfl, helhs_lt, hite_1⟩)
                                          ?_
                                        intro Jc1 hJc1; m6b_split
                                        · m6b_steps
                                          refine hJc1 (ec ^^^ 1#32, ee, et, ()) mc ⟨rfl, ?_⟩
                                          rw [bv32_xor1_eq_litNeg]
                                          exact iteGateDef_flip_cond hite_e'
                                        · m6b_let; exact hJc1 (ec, et, ee, ()) mc ⟨rfl, hite_e'⟩
                                      · m6b_let; rw [hst_e0']
                                        exact hJm2 (false, elhs, ()) mp
                                          ⟨stp.core.repr, stp.core.min_clr, hrl_p,
                                           (m6EvStOk_dw hokp).1.core_ok.min_clr_len_arr, hrepr_p,
                                           (fun h => by cases h), hmp⟩
                              · m6b_let; exact hjnxt_keep _ _
                      · m6b_steps
                        exact hBp (changed', true, slot, probes, seen_self, ()) mp ⟨stp, hokp, hmp⟩
                    · intro _ Lp _ hLp; m6b_steps
                      exact hLp 64 (_ &&& (ht_sz - 1#64), 0#64, false, ()) mj
                        ⟨stj, bv64_and_sub1_lt hht_pos, by decide, rfl, rfl, hokj, hmj⟩
                · m6b_let; exact hJex (_iw, changed', false, ()) mj ⟨stj, hokj, hmj⟩
              · m6b_let; exact hJex (_iw, changed', false, ()) mj ⟨stj, hokj, hmj⟩
          -- `if (tag == 0u) ... else if (tag == 1u ...) ... else if (tag == 2u ...) ... else`
          · intro Js hJs; clear hAndMatch hXorMatch hFind
            m6b_split
            · -- `tag == 0u`
              have htag0 : tag = 0#32 := ws_tag_eq hst_g1 hc
              have ⟨har2_0, hand0⟩ := ev_gate_tag0_and htag0 hsem0
              let rhs : List Nat := ((scr0.drop (g.toNat + 2)).take arity.toNat).map BitVec.toNat
              have hscr_ge : g.toNat + 2 + arity.toNat ≤ scr0.length := by
                dsimp only [arity]
                rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hpos
                · have := (List.getElem?_eq_some_iff.mp hscr0_g1).1; omega
                · obtain ⟨_, hr, _⟩ := hrhs0 ((mword &&& 0xFF#32).toNat - 1) (by omega)
                  have := (List.getElem?_eq_some_iff.mp hr).1; omega
              obtain ⟨hraw_of_rhs, hrhs_of_raw⟩ :=
                ws_tag0_raw_of_rhs (F_cur := F_cur) htmp_i_len hscr_ge fun k hk => by
                  have h := (htmp_i k (hi_eq ▸ hk)).2
                  simpa only [List.getElem?_take_of_lt hk] using h
              let raw := tmpi.take arity.toNat
              have hraw_len : raw.length = arity.toNat := by
                simp only [raw, List.length_take]; omega
              have hraw_lt : ∀ k < arity.toNat, (raw[k]?.getD 0#32).toNat < 2 * cv0 :=
                fun k hk => by
                  have hget : raw[k]?.getD 0#32 = tmpi[k]'(by omega) := by
                    simp only [raw, List.getElem?_take, ite_eq_left hk]
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  rw [hget]; exact (htmp_i' k hk).1
              clear hc ihi htmp_i hsem0 hgat_g0 hrhs0 hscr0_g hscr0_g1 hst_g hi_le
                hrl1 hrepr1 hm1'
              m6b_to_group
              refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32, i32])
                (fun (il, has_false, na, ()) ml =>
                  M6EvTag0P1Brk ctx s0 repri raw arity.toNat il has_false na ml)
                (fun rem (il, na, ()) ml =>
                  rem = arity.toNat - il.toNat ∧
                  M6EvTag0P1Inv ctx s0 repri raw arity.toNat il na ml)
                ?_ ?_ ?_
              · rintro _ ⟨il, has_false, na, ⟨⟩⟩ ml ⟨tmpl, htl_l, hna_le, hhf_l, hnohf_l, hml⟩
                have hokl := m6EvStOk_wsState hok0 hrli htl_l hrepri
                dsimp only [ctx] at htl_l hna_le hhf_l hnohf_l
                let P_tag0 : Tup Val [i32, .bool, .bool] → Mem 64 → Prop :=
                  fun (har', nh', _, ()) mj => M6EvOut ctx lhs tag har' nh' mj
                m6b_to_group
                refine wp_join_group P_tag0
                  (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                    m6b_let; exact hJs (lhs, il, har', nh', ch', ()) mj h)
                  ?_
                intro Jt0 hJt0; m6b_split
                · obtain ⟨k, hk, hff⟩ := hhf_l hc
                  obtain ⟨x, hx_mem, hx_eqv⟩ := hrhs_of_raw k hk
                  have hun_ent := andFold_has_false_entails (m6EvStOk_wit hokl) hcl0 hand0
                    hlhs_eqv0 ⟨x, hx_mem, (raw[k]?.getD 0#32).toNat, hraw_lt k hk, hx_eqv, hff⟩
                  m6b_steps; m6b_call hUnit
                  refine m6Ev_unit_xor1 hokl hlhs_lt hun_ent hml
                    fun uf su mu hoku _ hu2 hmu => ?_
                  ev_after_fold hexit hu2 false hoku mu hmu ch' =>
                    rw [hst_g1]
                    exact hJt0 (arity, false, ch', ()) mu (m6EvOut su hoku
                      (fun h => by cases h) (fun h => by cases h) hmu)
                · have hhf_f : has_false = false := by
                    cases has_false <;> first | rfl | cases hc
                  obtain ⟨_, hsub_l, hnohf'⟩ := hnohf_l hhf_f
                  clear hc; m6b_to_group
                  refine wp_join_group P_tag0
                    (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                      m6b_let; exact hJt0 (har', nh', ch', ()) mj h)
                    ?_
                  intro Jt0b hJt0b; m6b_split
                  · have hna0 : na.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                    have hun_ent := ws_tag0_all_true_entails (m6EvStOk_wit hokl) hcl0 hand0
                      hlhs_eqv0 hraw_lt hraw_of_rhs (hna0 ▸ hnohf')
                    m6b_steps; m6b_call hUnit
                    refine m6Ev_unit hokl hlhs_lt hun_ent hml
                      fun uf su mu hoku _ hu2 hmu => ?_
                    ev_after_fold hexit hu2 false hoku mu hmu ch' =>
                      rw [hst_g1]
                      exact hJt0b (arity, false, ch', ()) mu (m6EvOut su hoku
                        (fun h => by cases h) (fun h => by cases h) hmu)
                  · have hna_pos : 0 < na.toNat := by
                      have hne : na ≠ 0#32 := beq_eq_false_iff_ne.mp hc
                      rcases Nat.eq_zero_or_pos na.toNat with hz | hp
                      · exact absurd (BitVec.eq_of_toNat_eq hz) hne
                      · exact hp
                    have hfwd_l := ws_tag0_hf_false_fwd F_cur hraw_lt hraw_of_rhs hnohf'
                    clear hc; m6b_to_group
                    refine wp_join_group (ts := [])
                      (fun () ms => ∃ tmps : List (BitVec 32),
                        tmps.length = c.max_vars ∧
                        (∀ j < na.toNat, ∃ k < arity.toNat, tmps[j]? = raw[k]?) ∧
                        (∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
                          (s0.core.vals[r]?.getD 0#8 = 1#8 ∨
                            ∃ j < na.toNat, (tmps[j]?.getD 0#32).toNat = r)) ∧
                        (FullMem c (wsState s0 repri tmps) ⋆ R) ms)
                      ?_ ?_
                    · rintro _ ⟨⟩ ms ⟨tmps, htl_s, hsub_s, hfwd_s, hms⟩
                      m6b_to_group
                      refine wp_loop_break_group (brkTs := [.bool, i32, i32])
                        (lpTs := [i32, i32])
                        (fun (clash, ua, _si, ()) md =>
                          M6EvTag0DedupBrk ctx s0 repri tmps lhs na.toNat clash ua md)
                        (fun remd (ua, si, ()) md =>
                          remd = na.toNat - si.toNat ∧
                          M6EvTag0DedupInv ctx s0 repri tmps na.toNat ua si md)
                        ?_ ?_ ?_
                      · rintro _ ⟨clash, ua, _si, ⟨⟩⟩ md
                          ⟨tmpd, htl_d, hua_le, hsub_tmps, hcl_d, huf_d, hmd⟩
                        have hokd := m6EvStOk_wsState hok0 hrli htl_d hrepri
                        dsimp only [ctx] at htl_d hua_le hcl_d huf_d
                        obtain ⟨hsub_d, hsub_raw_d⟩ := ws_tag0_sub_raw_d hsub_tmps hsub_s
                          hrhs_of_raw (by omega) hraw_len
                        m6b_to_group
                        refine wp_join_group P_tag0
                          (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                            m6b_let; exact hJt0b (har', nh', ch', ()) mj h)
                          ?_
                        intro Jt0c hJt0c; m6b_split
                        · have hun_ent : (cnfOfClauses F_cur).EntailsClause
                              (cnfClause [litNeg lhs.toNat]) := by
                            rcases hcl_d hc with hmem | hpair
                            · exact ev_tag0_clash_lhs_entails hand0 hlhs_eqv0 hsub_s hrhs_of_raw
                                hraw_len (by omega) hmem
                            · exact ws_tag0_clash_entails hand0 hlhs_eqv0 hsub_s hrhs_of_raw
                                hraw_len (by omega) hpair
                          m6b_steps; m6b_call hUnit
                          refine m6Ev_unit_xor1 hokd hlhs_lt hun_ent hmd
                            fun uf su mu hoku _ hu2 hmu => ?_
                          ev_after_fold hexit hu2 false hoku mu hmu ch' =>
                            rw [hst_g1]
                            exact hJt0c (arity, false, ch', ()) mu (m6EvOut su hoku
                              (fun h => by cases h) (fun h => by cases h) hmu)
                        · obtain ⟨hua_pos, hcov_d⟩ := huf_d hc; clear hc
                          m6b_to_group
                          refine wp_join_group P_tag0
                            (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                              m6b_let; exact hJt0c (har', nh', ch', ()) mj h)
                            ?_
                          intro Jt0d hJt0d; m6b_split
                          · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                            omega
                          · have hev_d := ws_tag0_dedup_eval (m6EvStOk_wit hokd) hcl0 rfl
                              (by omega) hand0 hlhs_eqv0 hfwd_s hcov_d hsub_raw_d
                            clear hc; m6b_to_group
                            refine wp_join_group P_tag0
                              (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                                m6b_let; exact hJt0d (har', nh', ch', ()) mj h)
                              ?_
                            intro Jt0e hJt0e; m6b_split
                            · have hua1 : ua.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
                              obtain ⟨ht0_lt, ht0_eqv⟩ := ws_tag0_ua1_equiv (by omega) hraw_len
                                (hsub_d 0 (by omega)) hraw_lt (hua1 ▸ hev_d)
                              have h0_tmp : (0#64 : BitVec 64).toNat < tmpd.length := by
                                change 0 < tmpd.length; omega
                              m6b_steps; m6b_call hEquiv
                              refine m6Ev_equiv hokd hlhs_lt ht0_lt ht0_eqv hmd
                                fun ef se me hoke _ hef2 hme => ?_
                              ev_after_equiv_enq2 hexit hEnq se hef2 false hoke me hme st_f hok_f
                                _ m_f hm_f ch_f =>
                                rw [hst_g1]
                                exact hJt0e (arity, false, ch_f, ()) m_f (m6EvOut st_f hok_f
                                  (fun h => by cases h) (fun h => by cases h) hm_f)
                            · have hua_ge2 : 2 ≤ ua.toNat := by
                                have hne := beq_eq_false_iff_ne.mp hc
                                have : ua.toNat ≠ 1 := fun h => hne (BitVec.eq_of_toNat_eq h); omega
                              have hlhs_vals : (lhs.setWidth 64).toNat < s0.core.vals.length := by
                                rw [bv_zext32_toNat, hvlen0]; omega
                              have hua_cv : ua.toNat ≤ cv0 := by omega
                              have hua_31 : ua.toNat ≤ 31 := by omega
                              clear hc; m6b_to_group
                              refine wp_join_group P_tag0
                                (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                                  m6b_let; exact hJt0e (har', nh', ch', ()) mj h)
                                ?_
                              intro Jt0f hJt0f; m6b_split
                              · have hv1 : s0.core.vals[lhs.toNat]?.getD 0#8 = 1#8 :=
                                  vals_sgt0_eq1 (by rw [hvlen0]; omega) hlhs_vals
                                    ((m6EvStOk_wit hokd).vals_domain lhs.toNat hlhs_lt) hc
                                have hents := ws_tag0_lhs_true_ents (m6EvStOk_wit hokd) hcl0 hlhs_lt
                                  hv1 hev_d
                                m6b_to_group; refine wp_loop_inv
                                  (fun (ch_k, k, ()) mk => ∃ stk : FullState,
                                    k.toNat ≤ ua.toNat ∧ M6EvStOk ctx stk ∧
                                    stk.core.tmp = tmpd ∧ (FullMem c stk ⋆ R) mk)
                                  (fun (_, k, ()) _ => ua.toNat - k.toNat)
                                  (fun Jk hJk => by
                                    m6b_steps; exact hJk (false, 0#32, ()) md
                                      ⟨wsState s0 repri tmpd, Nat.zero_le _, hokd, rfl, hmd⟩)
                                  (fun Jk (ch_k, k, ()) mk
                                    ⟨stk, hk_le, hokk, htmp_k, hmk⟩ ihk => ?_)
                                m6b_split
                                · have hk_lt : k.toNat < ua.toNat := bv32_ult_lt hc
                                  have hk_tmp : (k.setWidth 64).toNat < stk.core.tmp.length := by
                                    rw [bv_zext32_toNat, htmp_k]; omega
                                  have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
                                    bv32_add1_lt_of (by omega)
                                  obtain ⟨htk_lt, htk_ent⟩ := ws_tag0_unit_k_args htmp_k hk_lt
                                    hraw_len (by omega) hsub_d hraw_lt hents hk_tmp
                                  m6b_steps; m6b_call hUnit
                                  refine m6Ev_unit hokk htk_lt htk_ent hmk
                                    fun uf su mu hoku htmpu hu2 hmu => ?_
                                  ev_after_fold hexit hu2 ch_k hoku mu hmu ch_u =>
                                    exact ihk (ch_u, k + 1#32, ()) mu (by dsimp only; omega)
                                      ⟨su, by omega, hoku, htmpu.trans htmp_k, hmu⟩
                                · m6b_let; rw [hst_g1]
                                  exact hJt0f (arity, false, ch_k, ()) mk (m6EvOut stk hokk
                                    (fun h => by cases h) (fun h => by cases h) hmk)
                              · clear hc; m6b_to_group
                                refine wp_join_group (ts := [i32, .bool])
                                  (fun (har', nh', ()) mj => M6EvOut ctx lhs tag har' nh' mj)
                                  (fun _ ⟨har', nh', ⟨⟩⟩ mj h => by
                                    m6b_let; exact hJt0f (har', nh', false, ()) mj h)
                                  ?_
                                intro Jt0g hJt0g; m6b_split
                                · m6b_let; rw [hst_g1]
                                  exact hJt0g (arity, false, ()) md (m6EvOut (wsState s0 repri tmpd)
                                    hokd (fun h => by cases h) (fun h => by cases h) hmd)
                                · m6b_let
                                  exact hJt0g (ua, true, ()) md (m6EvOut (wsState s0 repri tmpd)
                                    hokd
                                    (fun _ => ⟨hua_cv,
                                      fun _ => ⟨hua_ge2, hua_31, hev_d⟩,
                                      fun h => absurd (htag0.symm.trans h) (by decide),
                                      fun h => absurd (htag0.symm.trans h) (by decide)⟩)
                                    (fun _ => hlhs_lt) hmd)
                      · rintro Bd Ld remd ⟨ua, si, ⟨⟩⟩ md hBd hLd
                          ⟨rfl, tmpd, htl_d, hua_le, hsi_le, hua_pos_if, htail_d,
                           hsub_tmps, hcov_d, hmd⟩
                        dsimp only [ctx] at htl_d
                        m6b_split
                        · have hsi_lt : si.toNat < na.toNat := bv32_ult_lt hc
                          have hna_max : na.toNat ≤ c.max_vars :=
                            Nat.le_trans hna_le (Nat.le_trans har_cv hcv_le)
                          have hsi_tmp : (si.setWidth 64).toNat < tmpd.length := by
                            rw [bv_zext32_toNat]; omega
                          have hsi_tl : si.toNat < tmpd.length := by omega
                          have hsi_ts : si.toNat < tmps.length := by omega
                          let cur := tmps[si.toNat]'hsi_ts
                          have hcur_eq : tmpd[(si.setWidth 64).toNat]'hsi_tmp = cur :=
                            (list_getElem_zext32_eq rfl hsi_tmp hsi_tl).trans
                              (list_getElem_eq_of_eqD hsi_tl
                                ((htail_d si.toNat (Nat.le_refl _) hsi_lt).trans
                                  (List.getElem?_eq_getElem hsi_ts)))
                          have hsi1 : (si + 1#32).toNat = si.toNat + 1 :=
                            bv32_add1_lt_of (by omega)
                          have hua1 : (ua + 1#32).toNat = ua.toNat + 1 :=
                            bv32_add1_lt_of (by omega)
                          clear hc; m6b_steps; m6b_split
                          · have hcl_lhs : (lhs ^^^ 1#32).toNat ∈
                                (tmps.take na.toNat).map BitVec.toNat := by
                              have hc' : cur = lhs ^^^ 1#32 := by
                                have h := beq_iff_eq.mp hc
                                simp only [wsState_tmp] at h; rw [hcur_eq] at h; exact h
                              have h_tk : (tmps.take na.toNat)[si.toNat]'(by
                                  simp only [List.length_take, htl_s]; omega) = cur := by
                                simp only [List.getElem_take, cur]
                              rw [List.mem_map]
                              exact ⟨cur, h_tk ▸ List.getElem_mem _, by rw [hc']⟩
                            m6b_steps; exact hBd (true, ua, si + 1#32, ()) md
                              ⟨tmpd, htl_d, by omega, hsub_tmps,
                               fun _ => Or.inl (by rwa [← bv32_xor1_eq_litNeg]),
                               (fun h => by cases h), hmd⟩
                          · clear hc; m6b_to_group
                            refine wp_join_group (ts := [.bool, i32])
                              (fun (_, ua', ()) md' =>
                                M6EvTag0DedupInv ctx s0 repri tmps na.toNat ua' (si + 1#32) md')
                              (fun _ ⟨_, ua', ⟨⟩⟩ md'
                                ⟨t', ht', hu', hs', hp', htl', hs_t', hc', hm'⟩ => by
                                m6b_let; exact hLd (na.toNat - (si + 1#32).toNat)
                                  (ua', si + 1#32, ()) md' (by omega)
                                  ⟨rfl, t', ht', hu', hs', hp', htl', hs_t', hc', hm'⟩)
                              ?_
                            intro Jua hJua; m6b_split
                            · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                              have hsi0 : si.toNat = 0 :=
                                Nat.eq_zero_of_not_pos fun h => by have := hua_pos_if h; omega
                              have h0_tmp : (0#64 : BitVec 64).toNat < tmpd.length := by
                                change 0 < tmpd.length; omega
                              have hfs_tmp := focus_ws_tmp hmd; clear hmd
                              generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpd) ⋆ R =
                                R_tmp at hfs_tmp
                              m6b_steps; subst hR_tmp
                              simp only [wsState_tmp] at hm; rw [hcur_eq] at hm
                              obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ws_tag0_dedup_first_inv hsi0
                                htl_d hsi_lt (by omega) htail_d (by omega)
                              exact hJua (false, 1#32, ()) m ⟨tmpd.set 0 cur, h1,
                                (by rw [hsi1]; have h1 : (1#32).toNat = 1 := rfl; omega),
                                hsi1 ▸ h3, hsi1 ▸ h4,
                                hsi1 ▸ h5, h6, hsi1 ▸ h7, unfocus_ws_tmp hm⟩
                            · have hua_pos : 0 < ua.toNat := by
                                have hne : ua ≠ 0#32 := beq_eq_false_iff_ne.mp hc
                                rcases Nat.eq_zero_or_pos ua.toNat with hz | hp
                                · exact absurd (BitVec.eq_of_toNat_eq hz) hne
                                · exact hp
                              have hum1_n : ((ua - 1#32).setWidth 64).toNat = ua.toNat - 1 := by
                                rw [bv_zext32_toNat, bv32_sub1_toNat hua_pos]
                              have hum1_tmp : ((ua - 1#32).setWidth 64).toNat < tmpd.length := by
                                rw [hum1_n]; omega
                              let prev := tmpd[((ua - 1#32).setWidth 64).toNat]'hum1_tmp
                              have hprev_eq : prev = tmpd[ua.toNat - 1]'(by omega) :=
                                list_getElem_congr hum1_n hum1_tmp (by omega)
                              m6b_split
                              · have hcur_prev : cur = tmpd[ua.toNat - 1]'(by omega) :=
                                  (hcur_eq ▸ beq_iff_eq.mp hc).trans hprev_eq
                                obtain ⟨h1, h2, h3, h4, h5⟩ := ws_tag0_dedup_dup_inv' (by omega)
                                  (by omega) hua_pos hua_le hsi_lt hcur_prev htail_d hcov_d
                                m6b_steps; exact hLd (na.toNat - (si + 1#32).toNat)
                                  (ua, si + 1#32, ()) md (by omega)
                                  ⟨rfl, tmpd, htl_d, hsi1 ▸ h1, hsi1 ▸ h2, hsi1 ▸ h3, hsi1 ▸ h4,
                                   hsub_tmps, hsi1 ▸ h5, hmd⟩
                              · m6b_split
                                · have hcur_xor : cur = prev ^^^ 1#32 := hcur_eq ▸ beq_iff_eq.mp hc
                                  have hcl := ws_tag0_dedup_clash (by omega) (by omega) hua_pos
                                    hua_le hsi_lt hprev_eq hsub_tmps hcur_xor
                                  m6b_steps; exact hBd (true, ua, si + 1#32, ()) md
                                    ⟨tmpd, htl_d, (by omega), hsub_tmps, fun _ => Or.inr hcl,
                                     (fun h => by cases h), hmd⟩
                                · have hua_tmp : (ua.setWidth 64).toNat < tmpd.length := by
                                    rw [bv_zext32_toNat]; omega
                                  have hfs_tmp := focus_ws_tmp hmd; clear hmd
                                  generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpd) ⋆ R =
                                    R_tmp at hfs_tmp
                                  m6b_steps; subst hR_tmp
                                  simp only [wsState_tmp] at hm
                                  rw [bv_zext32_toNat, hcur_eq] at hm
                                  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ws_tag0_dedup_push_inv
                                    htl_d (by omega) (by omega) hua_le hsi_lt htail_d hsub_tmps
                                    hcov_d
                                  exact hJua (false, ua + 1#32, ()) m ⟨tmpd.set ua.toNat cur, h1,
                                    hua1 ▸ hsi1 ▸ h2, hsi1 ▸ h3, hua1 ▸ hsi1 ▸ h4, hsi1 ▸ h5,
                                    hua1 ▸ h6, hua1 ▸ hsi1 ▸ h7, unfocus_ws_tmp hm⟩
                        · have hsi_eq : si.toNat = na.toNat := by
                            have := bv32_ult_not_lt hc; omega
                          rw [hsi_eq] at hua_pos_if hcov_d
                          m6b_steps; exact hBd (false, ua, si, ()) md
                            ⟨tmpd, htl_d, hsi_eq ▸ hua_le, hsub_tmps, (fun h => by cases h),
                             fun _ => ⟨hua_pos_if hna_pos, hcov_d⟩, hmd⟩
                      · intro _ Ld _ hLd; m6b_steps
                        exact hLd na.toNat (0#32, 0#32, ()) ms
                          ⟨rfl, tmps, htl_s, Nat.zero_le _, Nat.zero_le _,
                           fun h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl,
                           fun _ h => absurd h (Nat.not_lt_zero _),
                           fun _ h => absurd h (Nat.not_lt_zero _), hms⟩
                    · intro _ hJsort; m6b_split
                      · m6b_steps; m6b_call hSort
                        refine ⟨tmpl, FullTmpRest c (wsState s0 repri tmpl) ⋆ R, by omega,
                          focus_full_tmp hml, fun tmps ms htl_s hperm_s _ hms => ?_⟩
                        have hms' : (FullMem c (wsState s0 repri tmps) ⋆ R) ms :=
                          ws_unfocus_tmp hms
                        clear hms; m6b_steps
                        obtain ⟨hsub_s, hfwd_s⟩ := ws_tag0_post_sort (htl_s.trans htl_l) htl_l
                          hna_le (Nat.le_trans har_cv hcv_le) hperm_s hsub_l hfwd_l
                        exact hJsort () ms ⟨tmps, htl_s.trans htl_l, hsub_s, hfwd_s, hms'⟩
                      · m6b_steps; exact hJsort () ml ⟨tmpl, htl_l, hsub_l, hfwd_l, hml⟩
              · rintro Bl Ll rem ⟨il, na, ⟨⟩⟩ ml hBl hLl
                  ⟨rfl, tmpl, htl_l, hna_le, hil_le, htail_l, hsub_l, hnohf_l, hml⟩
                dsimp only [ctx] at htl_l
                m6b_split
                · have hil_lt : il.toNat < arity.toNat :=
                    bv32_ult_lt (by rw [hst_g1] at hc; exact hc)
                  have hil_tmp : (il.setWidth 64).toNat < tmpl.length := by
                    rw [bv_zext32_toNat]; omega
                  have hil_tl : il.toNat < tmpl.length := by omega
                  have hil_raw : il.toNat < raw.length := by rw [hraw_len]; exact hil_lt
                  have hr_eq : tmpl[(il.setWidth 64).toNat]'hil_tmp = raw[il.toNat]'hil_raw :=
                    (list_getElem_zext32_eq rfl hil_tmp hil_tl).trans
                      (list_getElem_eq_of_eqD hil_tl
                        ((htail_l il.toNat (Nat.le_refl _) hil_lt).trans
                          (List.getElem?_eq_getElem hil_raw)))
                  have hr_lt : (raw[il.toNat]'hil_raw).toNat < 2 * cv0 := by
                    have h := hraw_lt il.toNat hil_lt
                    rwa [List.getElem?_eq_getElem hil_raw, Option.getD_some] at h
                  have hr_vals' : (raw[il.toNat]'hil_raw).toNat < s0.core.vals.length := by omega
                  have hr_vals : ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat <
                      s0.core.vals.length := by
                    rw [hr_eq, bv_zext32_toNat]; exact hr_vals'
                  have hil1 : (il + 1#32).toNat = il.toNat + 1 := bv32_add1_lt_of (by omega)
                  have hna1 : (na + 1#32).toNat = na.toNat + 1 := bv32_add1_lt_of (by omega)
                  have hna_tmp : (na.setWidth 64).toNat < tmpl.length := by
                    rw [bv_zext32_toNat]; omega
                  have hrv_dom := hw0.vals_domain (raw[il.toNat]'hil_raw).toNat hr_lt
                  have hrv_get : s0.core.vals[
                      ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat]'hr_vals =
                      s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' := by
                    have h1 : ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat =
                        (raw[il.toNat]'hil_raw).toNat := by
                      rw [hr_eq, bv_zext32_toNat]
                    exact list_getElem_congr h1 hr_vals hr_vals'
                  clear hc; m6b_split
                  · have hr_gd : raw[il.toNat]?.getD 0#32 = raw[il.toNat]'hil_raw := by
                      rw [List.getElem?_eq_getElem hil_raw, Option.getD_some]
                    have hff : s0.core.vals[(raw[il.toNat]?.getD 0#32).toNat]?.getD 0#8 =
                        0xFF#8 := by
                      rw [hr_gd]
                      exact vals_slt0_eqff hr_vals' _ hrv_dom (hrv_get ▸ hc)
                    m6b_steps; exact hBl (il, true, na, ()) ml ⟨tmpl, htl_l, by omega,
                      fun _ => ⟨il.toNat, hil_lt, hff⟩, (fun h => by cases h), hml⟩
                  · have hnslt_se : ((s0.core.vals[
                        ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat]'
                          hr_vals).signExtend 32).slt 0#32 = false := hc
                    m6b_to_group; refine wp_join_group (ts := [i32])
                      (fun (na', ()) ml' =>
                        M6EvTag0P1Inv ctx s0 repri raw arity.toNat (il + 1#32) na' ml')
                      (fun _ ⟨na', ⟨⟩⟩ ml' ⟨t', ht', hn', hi', htl', hs', hno', hm'⟩ => by
                        m6b_let; exact hLl (arity.toNat - (il + 1#32).toNat)
                          (il + 1#32, na', ()) ml' (by omega)
                          ⟨rfl, t', ht', hn', hi', htl', hs', hno', hm'⟩)
                      ?_
                    intro Jna hJna; clear hc; m6b_split
                    · have hfs_tmp := focus_ws_tmp hml; clear hml
                      generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpl) ⋆ R =
                        R_tmp at hfs_tmp
                      m6b_steps; subst hR_tmp
                      simp only [wsState_tmp] at hm; rw [bv_zext32_toNat, hr_eq] at hm
                      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ws_tag0_il_push_inv htl_l hna_le hil_lt
                        (Nat.le_trans har_cv hcv_le) hraw_len htail_l hsub_l (fun _ => hnohf_l)
                      exact hJna (na + 1#32, ()) m
                        ⟨tmpl.set na.toNat (raw[il.toNat]'(by rw [hraw_len]; exact hil_lt)),
                         h1, hna1 ▸ hil1 ▸ h2, hil1 ▸ h3, hil1 ▸ h4, hna1 ▸ h5,
                         hil1 ▸ hna1 ▸ h6 rfl, unfocus_ws_tmp hm⟩
                    · have hr_gd : raw[il.toNat]?.getD 0#32 = raw[il.toNat]'hil_raw := by
                        rw [List.getElem?_eq_getElem hil_raw, Option.getD_some]
                      have h1_val : s0.core.vals[(raw[il.toNat]?.getD 0#32).toNat]?.getD 0#8 =
                          1#8 := by
                        rw [hr_gd]
                        exact vals_nslt0_ne0_eq1 hr_vals' _ hrv_dom (hrv_get ▸ hnslt_se)
                          (hrv_get ▸ hc)
                      m6b_steps; exact hJna (na, ()) ml
                        ⟨tmpl, htl_l, by omega, by omega,
                         fun j hj1 hj2 => htail_l j (by omega) hj2, hsub_l,
                         hil1 ▸ ws_tag0_il_true_inv h1_val (fun _ => hnohf_l) rfl, hml⟩
                · have hil_eq : il.toNat = arity.toNat := by
                    have hnot : ¬ il.toNat < arity.toNat := by
                      rw [hst_g1] at hc; dsimp only [arity]; exact bv32_ult_not_lt hc
                    omega
                  m6b_steps; exact hBl (il, false, na, ()) ml
                    ⟨tmpl, htl_l, by omega, (fun h => by cases h),
                     fun _ => ⟨hil_eq, hsub_l, hil_eq ▸ hnohf_l⟩, hml⟩
              · intro _ _ _ hLp
                m6b_steps; exact hLp arity.toNat (0#32, 0#32, ()) mi
                  ⟨rfl, tmpi, htli, Nat.zero_le _, Nat.zero_le _,
                   (fun j _ hj => by simp only [raw, List.getElem?_take_of_lt hj]),
                   (fun _ h => absurd h (Nat.not_lt_zero _)),
                   (fun _ h => absurd h (Nat.not_lt_zero _)), hmi⟩
            · -- `tag == 1u && 2 ≤ arity ≤ 4`, else `tag == 2u && arity == 3u`
              have htag_ne0 : tag ≠ 0#32 := ws_tag_ne hst_g1 hc
              clear hc; m6b_to_group
              refine wp_join_group (ts := [i32, i32, i32, .bool, .bool])
                (fun (lhs', _iw, harity, need_hash, _changed', ()) mj =>
                  M6EvOut ctx lhs' tag harity need_hash mj)
                (fun _ ⟨lhs', _iw, harity, need_hash, changed', ⟨⟩⟩ mj h => by
                  m6b_let; exact hJs (lhs', _iw, harity, need_hash, changed', ()) mj h)
                ?_
              intro Js hJs; m6b_to_group
              refine wp_join_group (ts := []) (fun () m_n1 => tag ≠ 1#32 ∧ m_n1 = mi) ?_ ?_
              · rintro _ ⟨⟩ m_n1 ⟨htag_ne1, hm_n1⟩
                subst m_n1
                clear hSort ihi htmp_i hgat_g0 hrhs0 hscr0_g hscr0_g1 hst_g
                  hrl1 hrepr1 hm1'
                m6b_to_group
                refine wp_join_group (ts := [i32, .bool, .bool])
                  (fun (lhs', nh', ch', ()) mj => M6EvOut ctx lhs' tag arity nh' mj)
                  (fun _ ⟨lhs', nh', ch', ⟨⟩⟩ mj h => by
                    m6b_let; rw [hst_g1]; exact hJs (lhs', i, arity, nh', ch', ()) mj h)
                  ?_
                intro Jt2b hJt2b; m6b_split
                · have htag2 : tag = 2#32 := ws_tag_eq hst_g1 hc
                  clear hc; m6b_split
                  · have har3 : arity = 3#32 := ws_har_eq hst_g1 hc
                    have har3_n : arity.toNat = 3 := by rw [har3]; decide
                    have hite0 := (ev_gate_tag2_ite htag2 hsem0).2
                    clear hsem0
                    have ht_ge3 : 3 ≤ tmpi.length := by omega
                    have ht0_a : (0#64 : BitVec 64).toNat < tmpi.length := by
                      change 0 < tmpi.length; omega
                    have ht1_a : (1#64 : BitVec 64).toNat < tmpi.length := by
                      change 1 < tmpi.length; omega
                    have ht2_a : (2#64 : BitVec 64).toNat < tmpi.length := by
                      change 2 < tmpi.length; omega
                    let cl := tmpi[0]'(by omega); let tl := tmpi[1]'(by omega)
                    let el := tmpi[2]'(by omega)
                    have hcl_lt : cl.toNat < 2 * cv0 := (htmp_i' 0 (by omega)).1
                    have htl_lt : tl.toNat < 2 * cv0 := (htmp_i' 1 (by omega)).1
                    have hel_lt : el.toNat < 2 * cv0 := (htmp_i' 2 (by omega)).1
                    have hcv2_le : 2 * cv0 ≤ 2 * c.max_vars := Nat.mul_le_mul_left 2 hcv_le
                    have hcl_v0 :
                        ((tmpi[0]'(by omega)).setWidth 64).toNat < s0.core.vals.length := by
                      rw [bv_zext32_toNat, hvlen0]; exact Nat.lt_of_lt_of_le hcl_lt hcv2_le
                    have htl_v0 :
                        ((tmpi[1]'(by omega)).setWidth 64).toNat < s0.core.vals.length := by
                      rw [bv_zext32_toNat, hvlen0]; exact Nat.lt_of_lt_of_le htl_lt hcv2_le
                    have hel_v0 :
                        ((tmpi[2]'(by omega)).setWidth 64).toNat < s0.core.vals.length := by
                      rw [bv_zext32_toNat, hvlen0]; exact Nat.lt_of_lt_of_le hel_lt hcv2_le
                    have hcl_vals : (cl.setWidth 64).toNat < s0.core.vals.length := hcl_v0
                    have htl_vals : (tl.setWidth 64).toNat < s0.core.vals.length := htl_v0
                    have hel_vals : (el.setWidth 64).toNat < s0.core.vals.length := hel_v0
                    have hvc_dom := hw0.vals_domain cl.toNat hcl_lt
                    have hvt_dom := hw0.vals_domain tl.toNat htl_lt
                    have hve_dom := hw0.vals_domain el.toNat hel_lt
                    have hite_t : IteGateDef (cnfOfClauses F_cur) lhs.toNat
                        cl.toNat tl.toNat el.toNat :=
                      ite_eval_congr hite0 hlhs_eqv0 (htmp_i' 0 (by omega)).2
                        (htmp_i' 1 (by omega)).2 (htmp_i' 2 (by omega)).2
                    let P_t2 : Tup Val [i32, .bool, .bool, i32, i32, i32] → Mem 64 → Prop :=
                      fun (lhs', nh', _, _, _, _, ()) mj => M6EvOut ctx lhs' tag arity nh' mj
                    clear hc; m6b_to_group
                    refine wp_join_group P_t2
                      (fun _ ⟨lhs', nh', ch', _, _, _, ⟨⟩⟩ mj h => by
                        m6b_let; exact hJt2b (lhs', nh', ch', ()) mj h)
                      ?_
                    intro Jt2_1 hJt2_1; m6b_split
                    · have hvc_ne := vals_ne0_1_or_ff (by rw [hvlen0]; omega) hcl_vals hvc_dom hc
                      have heqc := ite_cond_const_equiv hw0 hcl0 hite_t hcl_lt hvc_ne
                      m6b_to_group; refine wp_join_group (ts := [i32])
                        (fun (br, ()) mbr => mbr = mi ∧ br.toNat < 2 * cv0 ∧
                          LitEquiv (cnfOfClauses F_cur) lhs.toNat br.toNat)
                        (fun _ ⟨br, ⟨⟩⟩ mbr ⟨hmbr, hbr_lt, heqv_br⟩ => by
                          subst mbr; m6b_steps; m6b_call hEquiv
                          refine m6Ev_equiv hoki hlhs_lt hbr_lt heqv_br hmi
                            fun ef se me hoke _ hef2 hme => ?_
                          ev_after_equiv_enq2 hexit hEnq
                            se hef2 false hoke me hme st_f hok_f _ m_f hm_f
                            ch_f =>
                            exact hJt2_1 (lhs, false, ch_f, cl, tl, el, ()) m_f (m6EvOut st_f hok_f
                              (fun h => by cases h) (fun h => by cases h) hm_f))
                        ?_
                      intro Jbr hJbr; m6b_split
                      · have hvc1 := vals_sgt0_eq1 (by rw [hvlen0]; omega) hcl_vals hvc_dom hc
                        m6b_let; exact hJbr (tl, ()) mi
                          ⟨rfl, htl_lt, by simpa only [hvc1, bv_zext32_toNat, ite_true] using heqc⟩
                      · have hvcff := vals_ne0_nsgt0_eqff (by rw [hvlen0]; omega) hcl_vals
                          hvc_dom hvc_ne hc
                        m6b_let; exact hJbr (el, ()) mi
                          ⟨rfl, hel_lt,
                           by simpa only [hvcff, bv_zext32_toNat,
                                show ((0xFF#8 : BitVec 8) = 1#8) = False from by decide,
                                ite_false] using heqc⟩
                    · clear hc; m6b_to_group
                      refine wp_join_group P_t2
                        (fun _ ⟨lhs', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
                          m6b_let; exact hJt2_1 (lhs', nh', ch', c', t', e', ()) mj h)
                        ?_
                      intro Jt2_2 hJt2_2; m6b_split
                      · have hte : tl = el := beq_iff_eq.mp hc
                        have heqt : LitEquiv (cnfOfClauses F_cur) lhs.toNat tl.toNat :=
                          ite_equal_branches_equiv hite_t (LitEquiv.refl _ _)
                            (LitEquiv.refl _ _) (by rw [hte]; exact LitEquiv.refl _ _)
                        m6b_steps; m6b_call hEquiv
                        refine m6Ev_equiv hoki hlhs_lt htl_lt heqt hmi
                          fun ef se me hoke _ hef2 hme => ?_
                        ev_after_equiv_enq2 hexit hEnq
                          se hef2 false hoke me hme st_f hok_f _ m_f hm_f ch_f =>
                          exact hJt2_2 (lhs, false, ch_f, cl, tl, el, ()) m_f (m6EvOut st_f hok_f
                            (fun h => by cases h) (fun h => by cases h) hm_f)
                      · clear hc; m6b_to_group
                        refine wp_join_group P_t2
                          (fun _ ⟨lhs', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
                            m6b_let; exact hJt2_2 (lhs', nh', ch', c', t', e', ()) mj h)
                          ?_
                        intro Jt2_3 hJt2_3; m6b_to_group
                        refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ ?_
                        · rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
                          refine wp_join_group P_t2
                            (fun _ ⟨lhs', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
                              m6b_let; exact hJt2_3 (lhs', nh', ch', c', t', e', ()) mj h)
                            ?_
                          intro Jt2_4 hJt2_4; m6b_to_group
                          refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ ?_
                          · rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
                            refine wp_join_group P_t2
                              (fun _ ⟨lhs', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
                                m6b_let; exact hJt2_4 (lhs', nh', ch', c', t', e', ()) mj h)
                              ?_
                            intro Jt2_5 hJt2_5; m6b_to_group
                            refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ ?_
                            · rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
                              refine wp_join_group P_t2
                                (fun _ ⟨lhs', nh', ch', c', t', e', ⟨⟩⟩ mj h => by
                                  m6b_let; exact hJt2_5 (lhs', nh', ch', c', t', e', ()) mj h)
                                ?_
                              intro Jt2_6 hJt2_6; m6b_to_group
                              refine wp_join_group (ts := []) (fun _ mf => mf = mi) ?_ ?_
                              · rintro _ ⟨⟩ mf hmf; subst mf; m6b_to_group
                                refine wp_join_group (ts := [i32, i32, i32])
                                  (fun (c1, t1, e1, ()) m1 => m1 = mi ∧
                                    IteGateDef (cnfOfClauses F_cur) lhs.toNat
                                      c1.toNat t1.toNat e1.toNat)
                                  (fun _ ⟨c1, t1, e1, ⟨⟩⟩ m1 ⟨hm1, hite_1⟩ => by
                                    subst m1; m6b_to_group
                                    refine wp_join_group (ts := [i32, i32, i32])
                                      (fun (lhs_t, t2, e2, ()) m2 => m2 = mi ∧
                                        lhs_t.toNat < 2 * cv0 ∧
                                        IteGateDef (cnfOfClauses F_cur) lhs_t.toNat
                                          c1.toNat t2.toNat e2.toNat)
                                      (fun _ ⟨lhs_t, t2, e2, ⟨⟩⟩ m2
                                          ⟨hm2, hlht_lt, hite_f⟩ => by
                                        subst m2
                                        have hfs_tmp := focus_ws_tmp hmi; clear hmi
                                        generalize hR_tmp :
                                          FullTmpRest c (wsState s0 repri tmpi) ⋆ R =
                                          R_tmp at hfs_tmp
                                        have ht1_len : 1 < tmpi.length := by omega
                                        have ht2_len : 2 < tmpi.length := by omega
                                        m6b_steps; subst hR_tmp
                                        let tmps := ((tmpi.set 0 c1).set 1 t2).set 2 e2
                                        have htmps_mem :
                                            (FullMem c (wsState s0 repri tmps) ⋆ R) m := by
                                          simpa only [tmps,
                                            show (0#64 : BitVec 64).toNat = 0 from rfl,
                                            show (1#64 : BitVec 64).toNat = 1 from rfl,
                                            show (2#64 : BitVec 64).toNat = 2 from rfl] using
                                            unfocus_ws_tmp hm
                                        have htl_tmps : tmps.length = c.max_vars := by
                                          simp only [tmps, List.length_set, htli]
                                        have hoks := m6EvStOk_wsState hok0 hrli htl_tmps hrepri
                                        exact hJt2_6 (lhs_t, true, false, c1, t2, e2, ()) m
                                          (m6EvOut (wsState s0 repri tmps) hoks
                                            (fun _ => ⟨har_cv,
                                              fun h => absurd (htag2.symm.trans h) (by decide),
                                              fun h => absurd (htag2.symm.trans h) (by decide),
                                              fun _ => ⟨har3, ev_tag2_tmp_ite ht_ge3 hite_f⟩⟩)
                                            (fun _ => hlht_lt) htmps_mem))
                                      ?_
                                    intro Jfl hJfl; m6b_split
                                    · have hl_flip : (lhs ^^^ 1#32).toNat < 2 * cv0 := by
                                        rw [bv32_xor1_eq_litNeg]
                                        exact bv32_xor1_lt_even hlhs_lt
                                      m6b_steps
                                      refine hJfl (lhs ^^^ 1#32, t1 ^^^ 1#32, e1 ^^^ 1#32, ())
                                        mi ⟨rfl, hl_flip, ?_⟩
                                      rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg,
                                        bv32_xor1_eq_litNeg]
                                      exact iteGateDef_flip_out hite_1
                                    · m6b_let
                                      exact hJfl (lhs, t1, e1, ()) mi ⟨rfl, hlhs_lt, hite_1⟩)
                                  ?_
                                intro Jc hJc; m6b_split
                                · m6b_steps; refine hJc (cl ^^^ 1#32, el, tl, ()) mi ⟨rfl, ?_⟩
                                  rw [bv32_xor1_eq_litNeg]; exact iteGateDef_flip_cond hite_t
                                · m6b_let; exact hJc (cl, tl, el, ()) mi ⟨rfl, hite_t⟩
                              · intro J4 hJ4; m6b_split
                                · have htff := vals_slt0_eqff (by rw [hvlen0]; omega) htl_vals
                                    hvt_dom hc
                                  clear hc; m6b_split
                                  · have hun := ite_branches_both_false_entails hw0 hcl0 hite_t
                                      htl_lt hel_lt htff
                                      (vals_slt0_eqff (by rw [hvlen0]; omega) hel_vals hve_dom hc)
                                    m6b_steps; m6b_call hUnit
                                    refine m6Ev_unit_xor1 hoki hlhs_lt hun hmi
                                      fun uf su mu hoku _ hu2 hmu => ?_
                                    ev_after_fold hexit
                                      hu2 false hoku mu hmu ch' =>
                                      exact hJt2_6 (lhs, false, ch', cl, tl, el, ()) mu
                                        (m6EvOut su hoku (fun h => by cases h)
                                          (fun h => by cases h) hmu)
                                  · m6b_let; exact hJ4 () mi rfl
                                · m6b_let; exact hJ4 () mi rfl
                            · intro J3 hJ3; m6b_split
                              · have ht1 := vals_sgt0_eq1 (by rw [hvlen0]; omega) htl_vals
                                  hvt_dom hc
                                clear hc; m6b_split
                                · have hun := ite_branches_both_true_entails hw0 hcl0 hite_t
                                    htl_lt hel_lt ht1
                                    (vals_sgt0_eq1 (by rw [hvlen0]; omega) hel_vals hve_dom hc)
                                  m6b_steps; m6b_call hUnit
                                  refine m6Ev_unit hoki hlhs_lt hun hmi
                                    fun uf su mu hoku _ hu2 hmu => ?_
                                  ev_after_fold hexit
                                    hu2 false hoku mu hmu ch' =>
                                    exact hJt2_5 (lhs, false, ch', cl, tl, el, ()) mu
                                      (m6EvOut su hoku (fun h => by cases h)
                                        (fun h => by cases h) hmu)
                                · m6b_let; exact hJ3 () mi rfl
                              · m6b_let; exact hJ3 () mi rfl
                          · intro J2 hJ2; m6b_split
                            · have htff := vals_slt0_eqff (by rw [hvlen0]; omega) htl_vals
                                hvt_dom hc
                              clear hc; m6b_split
                              · have heqc := ite_branches_false_true_equiv hw0 hcl0 hite_t
                                  htl_lt hel_lt htff
                                  (vals_sgt0_eq1 (by rw [hvlen0]; omega) hel_vals hve_dom hc)
                                m6b_steps; m6b_call hEquiv
                                refine m6Ev_equiv hoki hlhs_lt
                                  (by change (cl ^^^ 1#32).toNat < 2 * cv0
                                      rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hcl_lt)
                                  (by change LitEquiv (cnfOfClauses F_cur) lhs.toNat
                                        (cl ^^^ 1#32).toNat
                                      rw [bv32_xor1_eq_litNeg]; exact heqc)
                                  hmi fun ef se me hoke _ hef2 hme => ?_
                                ev_after_equiv_enq2 hexit hEnq
                                  se hef2 false hoke me hme st_f hok_f _ m_f
                                  hm_f ch_f =>
                                  exact hJt2_4 (lhs, false, ch_f, cl, tl, el, ()) m_f
                                    (m6EvOut st_f hok_f (fun h => by cases h)
                                      (fun h => by cases h) hm_f)
                              · m6b_let; exact hJ2 () mi rfl
                            · m6b_let; exact hJ2 () mi rfl
                        · intro J1 hJ1; m6b_split
                          · have ht1 := vals_sgt0_eq1 (by rw [hvlen0]; omega) htl_vals hvt_dom hc
                            clear hc; m6b_split
                            · have heqc := ite_branches_true_false_equiv hw0 hcl0 hite_t
                                htl_lt hel_lt ht1
                                (vals_slt0_eqff (by rw [hvlen0]; omega) hel_vals hve_dom hc)
                              m6b_steps; m6b_call hEquiv
                              refine m6Ev_equiv hoki hlhs_lt hcl_lt heqc hmi
                                fun ef se me hoke _ hef2 hme => ?_
                              ev_after_equiv_enq2 hexit hEnq
                                se hef2 false hoke me hme st_f hok_f _ m_f hm_f
                                ch_f =>
                                exact hJt2_3 (lhs, false, ch_f, cl, tl, el, ()) m_f
                                  (m6EvOut st_f hok_f (fun h => by cases h)
                                    (fun h => by cases h) hm_f)
                            · m6b_let; exact hJ1 () mi rfl
                          · m6b_let; exact hJ1 () mi rfl
                  · m6b_let
                    exact hJt2b (lhs, false, false, ()) mi
                      (m6EvOut (wsState s0 repri tmpi) hoki (fun h => by cases h)
                        (fun h => by cases h) hmi)
                · m6b_let
                  exact hJt2b (lhs, false, false, ()) mi
                    (m6EvOut (wsState s0 repri tmpi) hoki (fun h => by cases h)
                      (fun h => by cases h) hmi)
              · intro Jn1 hJn1; m6b_split
                · have htag1 : tag = 1#32 := ws_tag_eq hst_g1 hc
                  have ⟨har2_1, har4_1, hxor0⟩ := ev_gate_tag1_xor htag1 hsem0
                  have hscr_ge : g.toNat + 2 + arity.toNat ≤ scr0.length := by
                    have har_def : arity.toNat = (mword &&& 0xFF#32).toNat := rfl
                    obtain ⟨_, hr, _⟩ := hrhs0 (arity.toNat - 1) (by omega)
                    have := (List.getElem?_eq_some_iff.mp hr).1; omega
                  have hxor_t : XorListGateDef (cnfOfClauses F_cur) lhs.toNat
                      ((tmpi.take arity.toNat).map BitVec.toNat) :=
                    ev_tag1_rx_congr hscr_ge htmp_i_len hlhs_eqv0
                      (fun k hk => (htmp_i k (hi_eq ▸ hk)).2) hxor0
                  let rx0 := (tmpi.take arity.toNat).map BitVec.toNat
                  have hrx0_len : rx0.length = arity.toNat := by
                    simp only [rx0, List.length_map, List.length_take,
                      Nat.min_eq_left htmp_i_len]
                  clear hc ihi htmp_i hsem0 hgat_g0 hscr0_g hscr0_g1 hst_g hi_le hrl1
                    hrepr1 hm1' hJn1 hrhs0 hxor0
                  m6b_split
                  rotate_left
                  · have hc' : (2#32).ule arity = false := by
                      rw [hst_g1] at hc; exact hc
                    have hlt := bv32_ule_not_le hc'
                    change arity.toNat < 2 at hlt; omega
                  · clear hc; m6b_split
                    rotate_left
                    · have hc' : arity.ule 4#32 = false := by
                        rw [hst_g1] at hc; exact hc
                      have hgt := bv32_ule_not_le hc'
                      change 4 < arity.toNat at hgt; omega
                    · clear hc; m6b_to_group
                      refine wp_loop_inv (ts := [i32, i32, i32])
                        (fun (i1, flip1, na1, ()) ml =>
                          M6EvTag1P1Inv ctx s0 repri tmpi rx0 arity.toNat i1 flip1 na1 ml)
                        (fun (i1, _, _, ()) _ => arity.toNat - i1.toNat)
                        (fun Jl1 hJl1 => by
                          m6b_steps; exact hJl1 (0#32, 0#32, 0#32, ()) mi
                            ⟨tmpi, htli, Nat.zero_le _, Nat.zero_le _, Or.inl rfl,
                             (fun _ _ _ => rfl), (fun _ h => by cases h),
                             (fun _ _ => by
                               simp only [show (0#32 : BitVec 32).toNat = 0 from rfl,
                                 List.take_zero, List.map_nil, xorEvalList_nil,
                                 show ((0#32 : BitVec 32) == 1#32) = false from rfl,
                                 Bool.false_bne]),
                             hmi⟩)
                        (fun Jl1 (i1, flip1, na1, ()) ml ⟨tmpl, htl_l, hna_le, hi1_le, hfl1,
                          htail_l, hlt_l, hxor_l, hml⟩ ihl1 => ?_)
                      dsimp only [ctx] at htl_l hlt_l hxor_l
                      m6b_split
                      · have hi1_lt : i1.toNat < arity.toNat :=
                          bv32_ult_lt (by rw [hst_g1] at hc; exact hc)
                        have hi1_tmp : (i1.setWidth 64).toNat < tmpl.length := by
                          rw [bv_zext32_toNat]; omega
                        have hi1_tl : i1.toNat < tmpl.length := by omega
                        let rl := tmpi[i1.toNat]'(by omega)
                        have hrl_eq : tmpl[(i1.setWidth 64).toNat]'hi1_tmp = rl :=
                          (list_getElem_zext32_eq rfl hi1_tmp hi1_tl).trans
                            (list_getElem_eq_of_eqD hi1_tl
                              ((htail_l i1.toNat (Nat.le_refl _) hi1_lt).trans
                                (List.getElem?_eq_getElem (by omega))))
                        have hrl_lt : rl.toNat < 2 * cv0 := (htmp_i' i1.toNat hi1_lt).1
                        have hrl_vals : (rl.setWidth 64).toNat < s0.core.vals.length := by
                          rw [bv_zext32_toNat, hvlen0]; omega
                        have hrl_vals' : rl.toNat < s0.core.vals.length := by
                          rw [bv_zext32_toNat] at hrl_vals; exact hrl_vals
                        have hrv_dom := hw0.vals_domain rl.toNat hrl_lt
                        have hrx_i : rx0[i1.toNat]'(by omega) = rl.toNat := by
                          simp only [rx0, List.getElem_map, List.getElem_take, rl]
                        have hi1_n : (i1 + 1#32).toNat = i1.toNat + 1 :=
                          bv32_add1_lt_of (by omega)
                        have hna1_n : (na1 + 1#32).toNat = na1.toNat + 1 :=
                          bv32_add1_lt_of (by omega)
                        have htr_vals :
                            ((tmpl[(i1.setWidth 64).toNat]'hi1_tmp).setWidth 64).toNat <
                              s0.core.vals.length := by
                          rw [hrl_eq]; exact hrl_vals
                        clear hc; m6b_to_group
                        refine wp_join_group (ts := [i32, i32])
                          (fun (fl', na', ()) ml' =>
                            M6EvTag1P1Inv ctx s0 repri tmpi rx0 arity.toNat (i1 + 1#32) fl' na' ml')
                          (fun _ ⟨fl', na', ⟨⟩⟩ ml'
                              ⟨t', ht', hn', hi', hfl', htl', hlt', hx', hm'⟩ => by
                            m6b_let; exact ihl1 (i1 + 1#32, fl', na', ()) ml' (by dsimp only; omega)
                              ⟨t', ht', hn', hi', hfl', htl', hlt', hx', hm'⟩)
                          ?_
                        intro Jst hJst; m6b_steps; m6b_split
                        · have hc_ne : ((s0.core.vals[(rl.setWidth 64).toNat]'
                              hrl_vals).signExtend 32 != 0#32) = true := by
                            simp only [wsState_vals, wsState_tmp] at hc
                            rwa [list_getElem_congr (by rw [hrl_eq]) htr_vals hrl_vals] at hc
                          have hrl_ne0 := vals_ne0_1_or_ff hrl_vals' hrl_vals hrv_dom hc_ne
                          clear hc hc_ne; m6b_to_group
                          refine wp_join_group (ts := [i32])
                            (fun (fl', ()) mfl => mfl = ml ∧ (fl' = 0#32 ∨ fl' = 1#32) ∧
                              ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                                xorEvalList α (rx0.take (i1 + 1#32).toNat) = ((fl' == 1#32) !=
                                  xorEvalList α ((tmpl.take na1.toNat).map BitVec.toNat)))
                            (fun _ ⟨fl', ⟨⟩⟩ mfl ⟨hmfl, hfl', hx'⟩ => by
                              subst mfl; m6b_let
                              exact hJst (fl', na1, ()) ml
                                ⟨tmpl, htl_l, by omega, by omega, hfl',
                                 fun q hq1 hq2 => htail_l q (by omega) hq2,
                                 hlt_l, hx', hml⟩)
                            ?_
                          intro Jf hJf; m6b_split
                          · have hc_gt : (0#32 : BitVec 32).slt ((s0.core.vals[
                                (rl.setWidth 64).toNat]'hrl_vals).signExtend 32) = true := by
                              simp only [wsState_vals, wsState_tmp] at hc
                              rwa [list_getElem_congr (by rw [hrl_eq]) htr_vals hrl_vals] at hc
                            have h1_v : s0.core.vals[rl.toNat]?.getD 0#8 = 1#8 :=
                              vals_sgt0_eq1 hrl_vals' hrl_vals hrv_dom hc_gt
                            m6b_let; refine hJf (flip1 ^^^ 1#32, ()) ml ⟨rfl, ?_, fun α hα => ?_⟩
                            · rcases hfl1 with rfl | rfl <;> simp
                            · rw [hi1_n]
                              exact ev_xor_list_step_eval_ne0 hfl1 (hxor_l α hα) (by omega) hrx_i
                                (Or.inl (entails_eval_true (vals1_entails hw0 hcl0 hrl_lt h1_v) hα))
                                (by rw [entails_eval_true
                                      (vals1_entails hw0 hcl0 hrl_lt h1_v) hα]; rfl)
                          · have hc_ngt : (0#32 : BitVec 32).slt ((s0.core.vals[
                                (rl.setWidth 64).toNat]'hrl_vals).signExtend 32) = false := by
                              simp only [wsState_vals, wsState_tmp] at hc
                              rwa [list_getElem_congr (by rw [hrl_eq]) htr_vals hrl_vals] at hc
                            have hff_v : s0.core.vals[rl.toNat]?.getD 0#8 = 0xFF#8 :=
                              vals_ne0_nsgt0_eqff hrl_vals' hrl_vals hrv_dom hrl_ne0 hc_ngt
                            m6b_let; refine hJf (flip1, ()) ml ⟨rfl, hfl1, fun α hα => ?_⟩
                            rw [hi1_n]
                            exact ev_xor_list_step_eval_ne0 hfl1 (hxor_l α hα) (by omega) hrx_i
                              (Or.inr (entails_neg_eval_false
                                (valsff_entails_neg hw0 hcl0 hrl_lt hff_v) hα))
                              (by rw [entails_neg_eval_false
                                    (valsff_entails_neg hw0 hcl0 hrl_lt hff_v) hα]; rfl)
                        · clear hc
                          let e0 := rl &&& ~~~1#32
                          have hfs_tmp := focus_ws_tmp hml; clear hml
                          generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpl) ⋆ R =
                            R_tmp at hfs_tmp
                          have hna_arr : (na1.setWidth 64).toNat < tmpl.length := by
                            rw [bv_zext32_toNat]; omega
                          m6b_steps; subst hR_tmp
                          simp only [wsState_tmp] at hm ⊢
                          rw [bv_zext32_toNat, hrl_eq] at hm
                          rw [hrl_eq]
                          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ev_tag1_push_inv htl_l hna_le
                            hi1_lt (Nat.le_trans har_cv hcv_le) hfl1 htail_l hlt_l hrl_lt
                            (by omega) hrx_i hxor_l
                          exact hJst (flip1 ^^^ (rl &&& 1#32), na1 + 1#32, ()) m
                            ⟨tmpl.set na1.toNat e0, h1, hna1_n ▸ hi1_n ▸ h2, hi1_n ▸ h3, h4,
                             hi1_n ▸ h5, hna1_n ▸ h6, hna1_n ▸ hi1_n ▸ h7, unfocus_ws_tmp hm⟩
                      · have hi1_eq : i1.toNat = arity.toNat := by
                          have hnot : ¬ i1.toNat < arity.toNat := by
                            rw [hst_g1] at hc; dsimp only [arity]; exact bv32_ult_not_lt hc
                          omega
                        rw [hi1_eq] at hxor_l
                        have htake_all : rx0.take arity.toNat = rx0 :=
                          List.take_of_length_le (by omega)
                        rw [htake_all] at hxor_l
                        let lhs' := lhs ^^^ flip1
                        have hlhs'_lt : lhs'.toNat < 2 * cv0 :=
                          xor1_bit01_lt hlhs_lt hfl1
                        have hxor_l' : XorListGateDef (cnfOfClauses F_cur) lhs'.toNat
                            ((tmpl.take na1.toNat).map BitVec.toNat) := by
                          intro α hα
                          have h1 := hxor_l α hα
                          rw [← hxor_t α hα] at h1
                          dsimp only [lhs']; rw [xor1_bit01_eval hfl1, h1]
                          cases (flip1 == 1#32) <;>
                            cases xorEvalList α ((tmpl.take na1.toNat).map BitVec.toNat) <;> rfl
                        clear hc ihl1 htail_l hxor_l hrx0_len
                        m6b_to_group
                        refine wp_join_group (ts := [])
                          (fun () ms => ∃ tmps : List (BitVec 32),
                            tmps.length = c.max_vars ∧
                            (∀ q < na1.toNat, (tmps[q]?.getD 0#32).toNat < 2 * cv0 ∧
                              (tmps[q]?.getD 0#32).toNat % 2 = 0) ∧
                            XorListGateDef (cnfOfClauses F_cur) lhs'.toNat
                              ((tmps.take na1.toNat).map BitVec.toNat) ∧
                            (FullMem c (wsState s0 repri tmps) ⋆ R) ms)
                          ?_ ?_
                        · rintro _ ⟨⟩ ms ⟨tmps, htl_s, hlt_s, hxor_s, hms⟩
                          m6b_to_group
                          let P_d1 : Tup Val [i32, i32] → Mem 64 → Prop :=
                            M6EvTag1DedupInv ctx s0 repri tmps lhs' na1.toNat
                          refine wp_loop_inv (ts := [i32, i32]) P_d1
                            (fun (jd, _, ()) _ => na1.toNat - jd.toNat)
                            (fun Jd hJd => by
                              m6b_steps; exact hJd (0#32, 0#32, ()) ms
                                ⟨tmps, htl_s, Nat.zero_le _, Nat.zero_le _, (fun _ _ _ => rfl),
                                 (fun _ h => by cases h),
                                 (fun α hα => by
                                   rw [hxor_s α hα]
                                   simp only [show (0#32 : BitVec 32).toNat = 0 from rfl,
                                     List.take_zero, List.map_nil, xorEvalList_nil,
                                     Nat.sub_zero, List.drop_zero, Bool.false_bne]),
                                 hms⟩)
                            (fun Jd (jd, ua, ()) md ⟨tmpd, htl_d, hua_le, hjd_le, htail_d,
                              hlt_d, hxord, hmd⟩ ihd => ?_)
                          dsimp only [ctx] at htl_d hlt_d hxord
                          m6b_split
                          · have hjd_lt : jd.toNat < na1.toNat := by
                              dsimp only at hc; exact bv32_ult_lt hc
                            clear hc
                            have hjd1_n : (jd + 1#32).toNat = jd.toNat + 1 :=
                              bv32_add1_lt_of (by omega)
                            m6b_to_group
                            refine wp_join_group (ts := [i32, i32])
                              (fun x mp =>
                                (na1.toNat - x.1.toNat < na1.toNat - jd.toNat) ∧ P_d1 x mp)
                              (fun _ ⟨jd', ua', ⟨⟩⟩ mp ⟨hdec, hP⟩ => by
                                m6b_let; exact ihd (jd', ua', ()) mp hdec hP)
                              ?_
                            intro Js_d hJs_d; m6b_to_group
                            refine wp_join_group (ts := []) (fun () mp => mp = md) ?_ ?_
                            · rintro _ ⟨⟩ mp rfl
                              have hjd_arr : (jd.setWidth 64).toNat < tmpd.length := by
                                rw [bv_zext32_toNat]; omega
                              have hua_arr : (ua.setWidth 64).toNat < tmpd.length := by
                                rw [bv_zext32_toNat]; omega
                              have hua1_n : (ua + 1#32).toNat = ua.toNat + 1 :=
                                bv32_add1_lt_of (by omega)
                              let vjd := tmpd[(jd.setWidth 64).toNat]'hjd_arr
                              have hvjd_eq : vjd = tmps[jd.toNat]?.getD 0#32 := by
                                have hjd_m : jd.toNat < tmpd.length := by omega
                                have hv0 : vjd = tmpd[jd.toNat]'hjd_m :=
                                  list_getElem_congr (bv_zext32_toNat jd) hjd_arr hjd_m
                                have hg := htail_d jd.toNat (Nat.le_refl _) hjd_lt
                                rw [List.getElem?_eq_getElem (by omega)] at hg
                                rw [hv0, ← hg, Option.getD_some]
                              have hfs_tmp := focus_ws_tmp hmd; clear hmd
                              generalize hR_tmp : FullTmpRest c (wsState s0 repri tmpd) ⋆ R =
                                R_tmp at hfs_tmp
                              m6b_steps; subst hR_tmp
                              let tmpd' := tmpd.set ua.toNat vjd
                              have hmd'' : (FullMem c (wsState s0 repri tmpd') ⋆ R) m := by
                                try simp only [wsState_tmp] at hm
                                simpa only [tmpd', vjd, bv_zext32_toNat] using unfocus_ws_tmp hm
                              m6b_let; refine hJs_d (jd + 1#32, ua + 1#32, ()) m
                                ⟨by dsimp only; rw [hjd1_n]; omega,
                                 ⟨tmpd', by simp only [tmpd', List.length_set, htl_d]; rfl,
                                  by rw [hua1_n, hjd1_n]; omega,
                                  by rw [hjd1_n]; omega,
                                  fun q hq1 hq2 => by
                                    dsimp only [tmpd']; rw [hjd1_n] at hq1
                                    rw [List.getElem?_set_ne (by omega)]
                                    exact htail_d q (by omega) hq2,
                                  fun q hq => by
                                    dsimp only [tmpd']; rw [hua1_n] at hq
                                    by_cases hqe : q = ua.toNat
                                    · subst hqe; rw [List.getElem?_set_self (by omega),
                                        Option.getD_some, hvjd_eq]
                                      exact hlt_s jd.toNat hjd_lt
                                    · rw [List.getElem?_set_ne (Ne.symm hqe)]
                                      exact hlt_d q (by omega),
                                  fun α hα => ?_, hmd''⟩⟩
                              rw [hua1_n, hjd1_n]
                              exact ev_tag1_dedup_push_eq (by omega) (by omega) hjd_lt
                                (by omega) hvjd_eq (hxord α hα)
                            · intro Jp hJp; m6b_split
                              · have hjd1_lt : jd.toNat + 1 < na1.toNat := by
                                  dsimp only at hc; rw [← hjd1_n]; exact bv32_ult_lt hc
                                have hjd_arr : (jd.setWidth 64).toNat < tmpd.length := by
                                  rw [bv_zext32_toNat]; omega
                                have hjd1_arr : ((jd + 1#32).setWidth 64).toNat < tmpd.length := by
                                  rw [bv_zext32_toNat]; omega
                                m6b_steps; m6b_split
                                · have heq_d : tmpd[(jd.setWidth 64).toNat]'hjd_arr =
                                      tmpd[((jd + 1#32).setWidth 64).toNat]'hjd1_arr := by
                                    dsimp only at hc; exact beq_iff_eq.mp hc
                                  have hsame : tmps[jd.toNat]?.getD 0#32 =
                                      tmps[jd.toNat + 1]?.getD 0#32 := by
                                    have hjd_m : jd.toNat < tmpd.length := by omega
                                    have hjd1_m : jd.toNat + 1 < tmpd.length := by omega
                                    have hl := list_getElem_congr (bv_zext32_toNat jd)
                                      hjd_arr hjd_m
                                    have hr := list_getElem_congr
                                      (by rw [bv_zext32_toNat, hjd1_n]) hjd1_arr hjd1_m
                                    have heq_d' := hl.symm.trans (heq_d.trans hr)
                                    rw [← htail_d jd.toNat (Nat.le_refl _) hjd_lt,
                                      ← htail_d (jd.toNat + 1) (by omega) hjd1_lt,
                                      List.getElem?_eq_getElem (by omega),
                                      List.getElem?_eq_getElem (by omega), Option.getD_some,
                                      Option.getD_some, heq_d']
                                  have hjd2_n : (jd + 2#32).toNat = jd.toNat + 2 :=
                                    bv32_add2_lt_of (by omega)
                                  m6b_let; refine hJs_d (jd + 2#32, ua, ()) md
                                    ⟨by dsimp only; rw [hjd2_n]; omega,
                                     ⟨tmpd, htl_d, by omega, by rw [hjd2_n]; omega,
                                      fun q hq1 hq2 => by
                                        rw [hjd2_n] at hq1; exact htail_d q (by omega) hq2,
                                      hlt_d, fun α hα => ?_, hmd⟩⟩
                                  rw [hjd2_n]
                                  exact ev_tag1_dedup_skip_eq (by omega) hjd1_lt hsame
                                    (hxord α hα)
                                · m6b_let; exact hJp () md rfl
                              · m6b_let; exact hJp () md rfl
                          · have hjd_eq : jd.toNat = na1.toNat := by
                              dsimp only at hc; have := bv32_ult_not_lt hc; omega
                            rw [hjd_eq, Nat.sub_self, List.take_zero, List.map_nil] at hxord
                            have hxor_d : XorListGateDef (cnfOfClauses F_cur) lhs'.toNat
                                ((tmpd.take ua.toNat).map BitVec.toNat) := fun α hα => by
                              have h := hxord α hα
                              change _ = (_ != xorEvalList α []) at h
                              rwa [show xorEvalList α [] = false from rfl, Bool.bne_false] at h
                            have hokd := m6EvStOk_wsState hok0 hrli htl_d hrepri
                            let P_t1 : Tup Val [i32, .bool, .bool] → Mem 64 → Prop :=
                              fun (har', nh', _, ()) mj => M6EvOut ctx lhs' tag har' nh' mj
                            clear hc ihd htail_d hSort
                            m6b_to_group
                            refine wp_join_group P_t1
                              (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                                m6b_let; exact hJs (lhs', jd, har', nh', ch', ()) mj h)
                              ?_
                            intro Jt1d hJt1d; m6b_split
                            · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                              have hnil : ((tmpd.take ua.toNat).map BitVec.toNat) = [] := by
                                rw [hua0, List.take_zero, List.map_nil]
                              have hun_ent := ev_tag1_ua0_entails (hnil ▸ hxor_d)
                              m6b_steps; m6b_call hUnit
                              refine m6Ev_unit_xor1 hokd hlhs'_lt hun_ent hmd
                                fun uf su mu hoku _ hu2 hmu => ?_
                              ev_after_fold hexit
                                hu2 false hoku mu hmu ch' =>
                                rw [hst_g1]
                                exact hJt1d (arity, false, ch', ()) mu (m6EvOut su hoku
                                  (fun h => by cases h) (fun h => by cases h) hmu)
                            · have hua_ne0 : ua ≠ 0#32 := beq_eq_false_iff_ne.mp hc
                              clear hc; m6b_to_group
                              refine wp_join_group P_t1
                                (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                                  m6b_let; exact hJt1d (har', nh', ch', ()) mj h)
                                ?_
                              intro Jt1e hJt1e; m6b_split
                              · have hua1 : ua.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
                                have h0_arr : 0 < tmpd.length := by omega
                                have hone : (tmpd.take ua.toNat).map BitVec.toNat =
                                    [(tmpd[0]'h0_arr).toNat] := by
                                  rw [hua1, List.take_one, List.head?_eq_getElem?,
                                    List.getElem?_eq_getElem h0_arr]
                                  rfl
                                have hr0_lt : (tmpd[0]'h0_arr).toNat < 2 * cv0 := by
                                  have h := (hlt_d 0 (by omega)).1
                                  rwa [List.getElem?_eq_getElem h0_arr, Option.getD_some] at h
                                have heqv := ev_tag1_ua1_equiv (hone ▸ hxor_d)
                                m6b_steps; m6b_call hEquiv
                                refine m6Ev_equiv hokd hlhs'_lt hr0_lt heqv hmd
                                  fun ef se me hoke _ hef2 hme => ?_
                                ev_after_equiv_enq2 hexit hEnq
                                  se hef2 false hoke me hme st_f hok_f _ m_f hm_f
                                  ch_f =>
                                  rw [hst_g1]
                                  exact hJt1e (arity, false, ch_f, ()) m_f (m6EvOut st_f hok_f
                                    (fun h => by cases h) (fun h => by cases h) hm_f)
                              · have hua_ne1 : ua ≠ 1#32 := beq_eq_false_iff_ne.mp hc
                                have hua_ge2 : 2 ≤ ua.toNat := by
                                  rcases Nat.lt_trichotomy ua.toNat 1 with h0 | h1 | h2
                                  · exact absurd (BitVec.eq_of_toNat_eq
                                      (by change ua.toNat = 0; omega)) hua_ne0
                                  · exact absurd (BitVec.eq_of_toNat_eq h1) hua_ne1
                                  · exact h2
                                clear hc; m6b_to_group
                                refine wp_join_group P_t1
                                  (fun _ ⟨har', nh', ch', ⟨⟩⟩ mj h => by
                                    m6b_let; exact hJt1e (har', nh', ch', ()) mj h)
                                  ?_
                                intro Jt1f hJt1f
                                have hJfb : Jt1f (ua, true, false, ()) md :=
                                  hJt1f (ua, true, false, ()) md (m6EvOut (wsState s0 repri tmpd)
                                    hokd
                                    (fun _ => ⟨(by show ua.toNat ≤ cv0; omega),
                                      fun h => absurd (htag1.symm.trans h) (by decide),
                                      fun _ => ⟨hua_ge2, (by show ua.toNat ≤ 4; omega),
                                        (fun q hq => by
                                          have h := (hlt_d q hq).1; exact h), hxor_d⟩,
                                      fun h => absurd (htag1.symm.trans h) (by decide)⟩)
                                    (fun _ => hlhs'_lt) hmd)
                                m6b_split
                                · have hua2 : ua.toNat = 2 := by rw [beq_iff_eq.mp hc]; rfl
                                  have h0_arr : 0 < tmpd.length := by omega
                                  have h1_arr : 1 < tmpd.length := by omega
                                  let t0 := tmpd[0]'h0_arr; let t1 := tmpd[1]'h1_arr
                                  have ht0_lt : t0.toNat < 2 * cv0 := by
                                    have h := (hlt_d 0 (by omega)).1
                                    rwa [List.getElem?_eq_getElem h0_arr, Option.getD_some] at h
                                  have ht1_lt : t1.toNat < 2 * cv0 := by
                                    have h := (hlt_d 1 (by omega)).1
                                    rwa [List.getElem?_eq_getElem h1_arr, Option.getD_some] at h
                                  have htwo : (tmpd.take ua.toNat).map BitVec.toNat =
                                      [t0.toNat, t1.toNat] := by
                                    have h2_d : 2 ≤ tmpd.length := by omega
                                    rw [hua2]; apply List.ext_getElem
                                    · simp only [List.length_map, List.length_take, h2_d,
                                        Nat.min_eq_left, List.length_cons, List.length_nil]
                                    · intro k hk h2
                                      rcases k with _ | _ | k'
                                      · simp only [List.getElem_map, List.getElem_take,
                                          List.getElem_cons_zero, t0]
                                      · simp only [List.getElem_map, List.getElem_take,
                                          List.getElem_cons_succ, List.getElem_cons_zero, t1]
                                      · simp only [List.length_cons, List.length_nil] at h2
                                        omega
                                  have hl_vals : (lhs'.setWidth 64).toNat <
                                      s0.core.vals.length := by
                                    rw [bv_zext32_toNat, hvlen0]; omega
                                  clear hc; m6b_split
                                  · have hvl_dom := hw0.vals_domain lhs'.toNat hlhs'_lt
                                    have hvl_ne := vals_ne0_1_or_ff (by rw [hvlen0]; omega)
                                      hl_vals hvl_dom hc
                                    have heqc := ev_tag1_ua2_equiv hw0 hcl0 hlhs'_lt
                                      (htwo ▸ hxor_d) hvl_ne
                                    clear hc; m6b_to_group
                                    refine wp_join_group (ts := [i32])
                                      (fun (a0, ()) ma => ma = md ∧ a0.toNat < 2 * cv0 ∧
                                        LitEquiv (cnfOfClauses F_cur) a0.toNat t1.toNat)
                                      (fun _ ⟨a0, ⟨⟩⟩ ma ⟨hma, ha0_lt, heqv_a⟩ => by
                                        subst ma; m6b_steps; m6b_call hEquiv
                                        refine m6Ev_equiv hokd ha0_lt ht1_lt heqv_a hmd
                                          fun ef se me hoke _ hef2 hme => ?_
                                        ev_after_equiv_enq2 hexit hEnq
                                          se hef2 false hoke
                                          me hme st_f hok_f _ m_f hm_f ch_f =>
                                          rw [hst_g1]
                                          exact hJt1f (arity, false, ch_f, ()) m_f
                                            (m6EvOut st_f hok_f (fun h => by cases h)
                                              (fun h => by cases h) hm_f))
                                      ?_
                                    intro Ja0 hJa0
                                    clear hUnit hEquiv hEnq hQ hJt1f hJt1e hJt1d hJs hok0 htmp_i'
                                      hpref0 hq0
                                    have hl_vals' : lhs'.toNat < s0.core.vals.length := by
                                      rw [← bv_zext32_toNat lhs']; exact hl_vals
                                    m6b_split
                                    · simp only [wsState_vals] at hc
                                      have hv1 := vals_sgt0_eq1 hl_vals' hl_vals hvl_dom hc
                                      m6b_let
                                      refine wp_load_of (c0_load_full_tmp0 hmd
                                        (by rw [wsState_tmp]; exact h0_arr)) ?_
                                      m6b_let
                                      refine hJa0 (t0 ^^^ 1#32, ()) md ⟨rfl,
                                        by rw [bv32_xor1_eq_litNeg]
                                           exact bv32_xor1_lt_even ht0_lt,
                                        by simpa only [hv1, ite_true] using heqc⟩
                                    · simp only [wsState_vals] at hc
                                      have hvff := vals_ne0_nsgt0_eqff hl_vals' hl_vals
                                        hvl_dom hvl_ne hc
                                      m6b_let
                                      refine wp_load_of (c0_load_full_tmp0 hmd
                                        (by rw [wsState_tmp]; exact h0_arr)) ?_
                                      m6b_let
                                      refine hJa0 (t0, ()) md
                                        ⟨rfl, ht0_lt,
                                         by simpa only [hvff, show (0xFF#8 : BitVec 8) ≠ 1#8 by
                                              decide, ite_false] using heqc⟩
                                  · m6b_let; exact hJfb
                                · m6b_let; exact hJfb
                        · intro _ hJsort1; m6b_split
                          · m6b_steps; m6b_call hSort
                            refine ⟨tmpl, FullTmpRest c (wsState s0 repri tmpl) ⋆ R, by omega,
                              focus_full_tmp hml, fun tmps ms htl_s hperm_s _ hms => ?_⟩
                            have hms' : (FullMem c (wsState s0 repri tmps) ⋆ R) ms :=
                              ws_unfocus_tmp hms
                            clear hms; m6b_steps
                            obtain ⟨hlt_s, hxor_s⟩ := ev_tag1_post_sort (by omega)
                              (htl_s.trans htl_l ▸ htl_l.symm) hperm_s hlt_l hxor_l'
                            exact hJsort1 () ms ⟨tmps, htl_s.trans htl_l, hlt_s, hxor_s, hms'⟩
                          · m6b_steps; exact hJsort1 () ml ⟨tmpl, htl_l, hlt_l, hxor_l', hml⟩
                · have htag_ne1 : tag ≠ 1#32 := ws_tag_ne hst_g1 hc
                  m6b_steps; exact hJn1 () mi ⟨htag_ne1, rfl⟩

end EvalGateProof

end LeanQbe.T.Examples.Kissat.FullM6CongSubst
