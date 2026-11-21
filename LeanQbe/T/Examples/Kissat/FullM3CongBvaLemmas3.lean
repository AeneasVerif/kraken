module

public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M3b Congruence & BVA/BVE Proofs — Part 3 (`full_cong_work_step`)

Builds on `FullM3CongBvaLemmas2` to prove the parametric `(Γ : Env)` `Func.wp` contract for:
5. `full_cong_work_step` (`m3_cong_work_step_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3CongBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open Kraken.Bedrock2.Test

section WorkStepProof

open scoped FullArenaTactics FullCongTactics M3HeadTactics

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

private theorem ws_tag0_il_push_inv' {hf : Bool} {vals : List (BitVec 8)}
    {tmpl raw : List (BitVec 32)} {il_n na_n ar_n maxv : Nat} (htl : tmpl.length = maxv)
    (hna : na_n ≤ il_n) (hil : il_n < ar_n) (har_le : ar_n ≤ maxv)
    (hraw_len : raw.length = ar_n) (htail : ∀ j, il_n ≤ j → j < ar_n → tmpl[j]? = raw[j]?)
    (hsub : ∀ j < na_n, ∃ k < ar_n, tmpl[j]? = raw[k]?)
    (hnohf : hf = false → ∀ k < il_n,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
        ∃ j < na_n, tmpl[j]? = raw[k]?) :
    let tmpl' := tmpl.set na_n (raw[il_n]'(by omega))
    tmpl'.length = maxv ∧ na_n + 1 ≤ il_n + 1 ∧ il_n + 1 ≤ ar_n ∧
    (∀ j, il_n + 1 ≤ j → j < ar_n → tmpl'[j]? = raw[j]?) ∧
    (∀ j < na_n + 1, ∃ k < ar_n, tmpl'[j]? = raw[k]?) ∧
    (hf = false → ∀ k < il_n + 1,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
        ∃ j < na_n + 1, tmpl'[j]? = raw[k]?) := by
  refine ⟨by rw [List.length_set]; exact htl, by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2; rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2
  · intro j hj; by_cases hjn : j = na_n
    · subst hjn; refine ⟨il_n, hil, ?_⟩
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_set_ne (Ne.symm hjn)]; exact hsub j (by omega)
  · intro hhf k hk; by_cases hki : k = il_n
    · subst hki; right; refine ⟨na_n, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · obtain h1 | ⟨j, hj, hget⟩ := hnohf hhf k (by omega)
      · exact Or.inl h1
      · right; refine ⟨j, by omega, ?_⟩
        rw [List.getElem?_set_ne (by omega)]; exact hget

@[local c0_store] private theorem c0_store_array32_set_0 {p : BitVec 64} {xs : List (BitVec 32)}
    {k0 : Nat} {v0 v1 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64} (h1 : 1 < xs.length)
    (hm : (array (t := i32) p (xs.set k0 v0) ⋆ R) m) :
    storeOk m i32 (p + 4#64) ∧
      (array (t := i32) p ((xs.set k0 v0).set 1 v1) ⋆ R) (storeMem m i32 (p + 4#64) v1) := by
  simpa [Ty.bytes, Ty.size, i32] using
    store_array (t := i32) (i := 1) v1 (by decide) (by simpa using h1) hm

@[local c0_store] private theorem c0_store_array32_set_0_mul {p : BitVec 64}
    {xs : List (BitVec 32)} {k0 : Nat} {v0 v1 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (h1 : 1 < xs.length) (hm : (array (t := i32) p (xs.set k0 v0) ⋆ R) m) :
    storeOk m i32 (p + 1#64 * 4) ∧
      (array (t := i32) p ((xs.set k0 v0).set 1 v1) ⋆ R)
        (storeMem m i32 (p + 1#64 * 4) v1) := by
  simpa [Ty.bytes, Ty.size, i32,
    show (1#64 : BitVec 64) * 4 = 4#64 from rfl] using
    c0_store_array32_set_0 (p := p) (xs := xs) (k0 := k0) (v0 := v0) (v1 := v1) h1 hm

@[local c0_store] private theorem c0_store_array32_set_01 {p : BitVec 64}
    {xs : List (BitVec 32)} {k0 k1 : Nat} {v0 v1 v2 : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} (h2 : 2 < xs.length)
    (hm : (array (t := i32) p ((xs.set k0 v0).set k1 v1) ⋆ R) m) :
    storeOk m i32 (p + 8#64) ∧
      (array (t := i32) p (((xs.set k0 v0).set k1 v1).set 2 v2) ⋆ R)
        (storeMem m i32 (p + 8#64) v2) := by
  simpa [Ty.bytes, Ty.size, i32] using
    store_array (t := i32) (i := 2) v2 (by decide) (by simpa using h2) hm

@[local c0_store] private theorem c0_store_array32_set_01_mul {p : BitVec 64}
    {xs : List (BitVec 32)} {k0 k1 : Nat} {v0 v1 v2 : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} (h2 : 2 < xs.length)
    (hm : (array (t := i32) p ((xs.set k0 v0).set k1 v1) ⋆ R) m) :
    storeOk m i32 (p + 2#64 * 4) ∧
      (array (t := i32) p (((xs.set k0 v0).set k1 v1).set 2 v2) ⋆ R)
        (storeMem m i32 (p + 2#64 * 4) v2) := by
  simpa [Ty.bytes, Ty.size, i32,
    show (2#64 : BitVec 64) * 4 = 8#64 from rfl] using
    c0_store_array32_set_01 (p := p) (xs := xs) (k0 := k0) (k1 := k1) (v0 := v0) (v1 := v1)
      (v2 := v2) h2 hm

/-- **#5 (`full_cong_work_step`)**: single epoch-filtered congruence pass preserving
`FullDenseInv`, `FullCongReprInv`, persistent `CongHtInv`, `scr[0..g_len)`, `cur_vars`, `fuel`,
and returning `st = r &&& 3` (`0`/`1`/`2`) with `st = 2 → F0.Unsat`. -/
theorem m3_cong_work_step_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullSortU32Spec a m Q X →
      Γ "full_sort_u32" [i64, i32] [] a m Q X)
    (hUnit : ∀ a m Q X, m3CongUnitFoldSpec a m Q X →
      Γ "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X)
    (hEquiv : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X)
    (hMatch : ∀ a m Q X, m3CongAndMatchSpec a m Q X →
      Γ "full_cong_and_match" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m3CongWorkStepSpec a m Q X → Func.wp Γ full_cong_work_step_body a m Q X := by
  rintro ⟨h, g_len, ht_off, ht_sz, cur_ep, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, scr0, R, rfl, hlen0, hw0, hmk0, hnd0, hext0, hcl0, hdm0, hrepr0,
     hht_pos, hg_le_ht, hht_le, hseq0, hpref0, hht0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  let ar0 := s0.core.arena; let alen0 := s0.core.arena_len
  m3_steps
  refine wp_loop_inv (ts := [.bool, i64, i64])
    (fun (changed, _work, g, ()) mg => ∃ st : FullState,
      g.toNat ≤ g_len.toNat ∧
      WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 st ∧
      FullCongSpecs.GateSeqOk F_cur cv0 scr0 g_len.toNat g.toNat ∧
      (FullMem c st ⋆ R) mg)
    (fun (_changed, _work, g, ()) _ => g_len.toNat - g.toNat)
    (fun Jg hJg => by
      m3_steps; exact hJg (false, 0#64, 0#64, ()) m0
        ⟨s0, Nat.zero_le _,
         ⟨hlen0, hw0, hmk0, hnd0, hext0, hcl0, hdm0, rfl, rfl, rfl, rfl, hrepr0, hpref0, hht0⟩,
         hseq0, hm0⟩)
    (fun Jg (changed, work, g, ()) mg ⟨st, hg_le, hok_t, hseq_t, hmg⟩ ihg => ?_)
  have ⟨hlen_t, hw_t, hmk_t, hnd_t, hext_t, hcl_t, hdm_t, hcv_t, hfl_t, har_t, hal_t,
    hrepr_t, hpref_t, hht_t⟩ := hok_t
  have hscrl_t := hlen_t.scratch_ok.scratch_buf_len
  have hcv_le := hlen_t.core_ok.cur_vars_le
  have hcv0_le : cv0 ≤ c.max_vars := hcv_t ▸ hcv_le
  have htmpl_t := hlen_t.core_ok.tmp_len_arr
  have hrl_t := hlen_t.core_ok.repr_len
  have htmkl_t := hlen_t.scratch_ok.tarjan_mark_len
  have hvlen_t := hlen_t.core_ok.vals_len
  m3_to_group
  refine wp_join0
    (fun m_ex => ∃ ste : FullState,
      WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 ste ∧
      (FullMem c ste ⋆ R) m_ex)
    (fun _ m_ex ⟨ste, hoke, hme⟩ => by
      m3_to_group
      refine wp_join_group (ts := [i64])
        (fun (st_v, ()) m_st =>
          st_v = (if ste.core.inconsistent ≠ 0#64 then 2#64 else if changed then 1#64 else 0#64) ∧
          m_st = m_ex)
        (fun _ ⟨st_v, ⟨⟩⟩ m_st ⟨hst_v, rfl⟩ => by
          m3_steps
          have hgoal := ws_exit_q hQ rfl rfl rfl rfl hoke hme changed work
          dsimp only at hst_v hgoal; rw [hst_v]
          simpa only [BitVec.reduceSignExtend, BitVec.reduceToNat] using hgoal)
        (fun Jst hJst => by
          m3_split_fast
          · have hne : ste.core.inconsistent ≠ 0#64 := bne_iff_ne.mp hc
            m3_let; exact hJst (2#64, ()) m_ex ⟨by rw [ite_eq_left hne], rfl⟩
          · have heq0 : ¬ ste.core.inconsistent ≠ 0#64 := by simpa using hc
            m3_to_group
            refine wp_join_group (ts := [i64])
              (fun (vc, ()) mc => vc = (if changed then 1#64 else 0#64) ∧ mc = m_ex)
              (fun _ ⟨vc, ⟨⟩⟩ mc ⟨hvc, hmc⟩ => by
                m3_let; exact hJst (vc, ()) mc ⟨by rw [ite_eq_right heq0]; exact hvc, hmc⟩)
              (fun Jch hJch => by
                m3_split_fast
                · m3_let; exact hJch (1#64, ()) m_ex ⟨by rw [ite_eq_left hc], rfl⟩
                · have hnch : ¬ changed = true := by intro h; rw [h] at hc; cases hc
                  m3_let; exact hJch (0#64, ()) m_ex ⟨by rw [ite_eq_right hnch], rfl⟩)))
    ?_
  intro Jex hJex
  m3_split_fast
  · have hg_lt : g.toNat < g_len.toNat := bv64_ult_lt hc
    clear hc
    m3_split_fast
    · clear hc
      obtain ⟨hgat, hseq_next⟩ := gateSeqOk_inv_lt hseq_t hg_lt
      have ⟨lhs0, mword, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, har_cv, har_8, hrhs0, hsem0⟩ := hgat
      have hg_arr : g.toNat < st.scratch.scratch_buf.length := by omega
      have hg1_n : (g + 1).toNat = g.toNat + 1 := by bv_omega
      have hg1_arr : (g + 1).toNat < st.scratch.scratch_buf.length := by omega
      have hst_g : st.scratch.scratch_buf[g.toNat]'hg_arr = lhs0 :=
        list_getElem_eq_of_eqD hg_arr ((hpref_t g.toNat hg_lt).trans hscr0_g)
      have hst_g1 : st.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mword :=
        list_getElem_eq_of_eqD hg1_arr
          (by rw [hg1_n]; exact (hpref_t (g.toNat + 1) (by omega)).trans hscr0_g1)
      let tag := mword >>> 28; let arity := mword &&& 0xFF#32
      have har_cv' : arity.toNat ≤ cv0 := har_cv
      have hbd_g' : g.toNat + 2 + arity.toNat ≤ g_len.toNat := hbd_g
      have hnext_g : (g + 2#64 + arity.setWidth 64).toNat = g.toNat + 2 + arity.toNat :=
        bv64_add_zext32 (k := 2) (by omega)
      have hseq_next' : FullCongSpecs.GateSeqOk F_cur cv0 scr0 g_len.toNat
          (g + 2#64 + arity.setWidth 64).toNat := by
        rw [hnext_g]; simpa [hscr0_g1, arity] using hseq_next
      m3_steps; m3_call hFind
      refine ⟨F_cur, 2 * cv0, st.core.repr, FullReprRest c st ⋆ R, hrepr_t,
        by rw [hst_g]; exact hlhs0_lt, focus_full_repr hmg,
        fun lhs repr1 m1 hrl1 hrepr1 _ hlhs_lt hlhs_eqv hm1 => ?_⟩
      have hm1' : (FullMem c (wsState st repr1 st.core.tmp) ⋆ R) m1 := unfocus_full_repr hm1
      clear hm1
      have hlhs_eqv0 : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat := by
        rwa [hst_g] at hlhs_eqv
      have hlhs0_v_lt : ((lhs0 >>> 1).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
        rw [bv_zext32_toNat]; have := bv32_div2_lt_of_lt2 hlhs0_lt; omega
      have hstg_v_lt :
          ((st.scratch.scratch_buf[g.toNat]'hg_arr >>> 1).setWidth 64).toNat <
            st.scratch.tarjan_mark.length := by
        rw [hst_g]; exact hlhs0_v_lt
      have hlhs_v_lt : ((lhs >>> 1).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
        rw [bv_zext32_toNat]; have := bv32_div2_lt_of_lt2 hlhs_lt; omega
      m3_to_group
      refine wp_join_group (ts := [.bool])
        (fun (_, ()) md => md = m1)
        (fun _ ⟨dty0, ⟨⟩⟩ md hmd => ?_)
        (fun Jd hJd => by
          m3_split_fast
          · m3_let; exact hJd (true, ()) m1 rfl
          · m3_split_fast <;> (m3_let; exact hJd (_, ()) m1 rfl))
      subst md; m3_to_group
      refine wp_loop_inv
        (fun (_dty, i, ()) mi => ∃ (repri tmpi : List (BitVec 32)),
          repri.length = 2 * c.max_vars ∧ tmpi.length = c.max_vars ∧
          i.toNat ≤ arity.toNat ∧ FullCongReprInv F_cur (2 * cv0) repri ∧
          (∀ k' < i.toNat,
            (tmpi[k']?.getD 0#32).toNat < 2 * cv0 ∧
            LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
              (tmpi[k']?.getD 0#32).toNat) ∧
          (FullMem c (wsState st repri tmpi) ⋆ R) mi)
        (fun (_, i, ()) _ => arity.toNat - i.toNat)
        (fun Ji hJi => by
          m3_steps; exact hJi (dty0, 0#32, ()) m1 ⟨repr1, st.core.tmp, hrl1.trans hrl_t, htmpl_t,
            Nat.zero_le _, hrepr1, fun _ h => by simp at h, hm1'⟩)
        (fun Ji (dty, i, ()) mi ⟨repri, tmpi, hrli, htli, hi_le, hrepri, htmp_i, hmi⟩ ihi => ?_)
      have hoki : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat
          scr0 (wsState st repri tmpi) := workStepOk_wsState hok_t hrli htli hrepri
      m3_split_fast
      · have hi_lt : i.toNat < arity.toNat := bv32_ult_lt (by rw [hst_g1] at hc; exact hc)
        obtain ⟨ri, hri_get, hri_lt⟩ := hrhs0 i.toNat hi_lt
        have hg2i_n : (g + 2 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat :=
          bv64_add_zext32 (k := 2) (by omega)
        have hg2i_arr : (g + 2 + i.setWidth 64).toNat < st.scratch.scratch_buf.length := by
          rw [hg2i_n]; omega
        have hst_g2i : st.scratch.scratch_buf[(g + 2 + i.setWidth 64).toNat]'hg2i_arr = ri :=
          scr_g2i_get hpref_t hri_get (by omega) hg2i_n hg2i_arr
        m3_steps; m3_call hFind
        refine ⟨F_cur, 2 * cv0, repri, FullReprRest c (wsState st repri tmpi) ⋆ R, hrepri,
          by dsimp only [wsState]; rw [hst_g2i]; exact hri_lt, focus_full_repr hmi,
          fun rval repri' mi' hrl_i' hrepr_i' _ hrval_lt hrval_eqv hmi' => ?_⟩
        have hmi'' : (FullMem c (wsState st repri' tmpi) ⋆ R) mi' := ws_unfocus_repr hmi'
        clear hmi'
        have hri_tmk : ((ri >>> 1).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
          rw [bv_zext32_toNat]; have := bv32_div2_lt_of_lt2 hri_lt; omega
        have hstg2i_tmk :
            ((st.scratch.scratch_buf[(g + 2 + i.setWidth 64).toNat]'hg2i_arr >>> 1).setWidth
              64).toNat < st.scratch.tarjan_mark.length := by
          rw [hst_g2i]; exact hri_tmk
        have hrval_tmk : ((rval >>> 1).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
          rw [bv_zext32_toNat]; have := bv32_div2_lt_of_lt2 hrval_lt; omega
        have hi_tmp : i.toNat < tmpi.length := by omega
        have hi1_n : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_toNat (by omega) (by omega)
        m3_to_group; refine wp_join_group (ts := [.bool])
          (fun (_dty', ()) m_d => m_d = mi' ∧ (FullMem c (wsState st repri' tmpi) ⋆ R) m_d) ?_ ?_
        · rintro _ ⟨dty', ⟨⟩⟩ m_d ⟨hmd_eq, hmd⟩; subst m_d
          have hfs_tmp := focus_full_tmp hmd; clear hmd
          generalize hR_tmp : FullTmpRest c (wsState st repri' tmpi) ⋆ R = R_tmp at hfs_tmp
          have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
          rw [bv_zext32_toNat] at hm
          exact ihi (dty', i + 1#32, ()) m (by dsimp only; omega)
            ⟨repri', tmpi.set i.toNat rval, hrl_i'.trans hrli,
             by rw [List.length_set]; exact htli, by omega, hrepr_i',
             fun k' hk' => ws_find_tmp_step htmp_i htli (by omega) hri_get hrval_lt
               (by dsimp only [wsState] at hrval_eqv; rwa [hst_g2i] at hrval_eqv)
               k' (hi1_n ▸ hk'),
             ws_unfocus_tmp hm⟩
        · intro Jd hJd; m3_split_fast
          · m3_steps; exact hJd (true, ()) mi' ⟨rfl, hmi''⟩
          · m3_split_fast
            · m3_steps; exact hJd (true, ()) mi' ⟨rfl, hmi''⟩
            · m3_let; exact hJd (dty, ()) mi' ⟨rfl, hmi''⟩
      · have hi_eq : i.toNat = arity.toNat := by
          have hnot : ¬ i.toNat < arity.toNat := by
            rw [hst_g1] at hc; simpa [arity] using bv32_ult_not_lt hc
          omega
        have htmp_i_len : arity.toNat ≤ tmpi.length := by omega
        have htmp_i' : ∀ (k' : Nat) (hk' : k' < arity.toNat),
            (tmpi[k']'(by omega)).toNat < 2 * cv0 ∧
            LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
              (tmpi[k']'(by omega)).toNat := fun k' hk' => by
          have h := htmp_i k' (by omega)
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
        clear hc; m3_split_fast
        rotate_left
        · m3_steps; rw [hst_g1]
          exact ihg (changed, work + 1#64, g + 2#64 + arity.setWidth 64, ()) mi
            (by dsimp only; rw [hnext_g]; omega)
            ⟨wsState st repri tmpi, by rw [hnext_g]; exact hbd_g', hoki, hseq_next', hmi⟩
        · clear hc; m3_to_group
          refine wp_join_group (ts := [.bool, i32, i32, .bool])
            (fun (changed', _iw, harity, need_hash, ()) mj => ∃ stj : FullState,
              WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat
                scr0 stj ∧
              (need_hash = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag harity) ∧
              (FullMem c stj ⋆ R) mj)
            ?_ ?_
          · rintro _ ⟨changed', _iw, harity, need_hash, ⟨⟩⟩ mj ⟨stj, hokj, hgatej, hmj⟩
            m3_split_fast
            rotate_left
            · m3_steps; rw [hst_g1]
              exact ihg (changed', work + 4#64, g + 2#64 + arity.setWidth 64, ()) mj
                (by dsimp only; rw [hnext_g]; omega)
                ⟨stj, by rw [hnext_g]; exact hbd_g', hokj, hseq_next', hmj⟩
            · obtain ⟨hhar_cv, hgat0, hgat1, hgat2⟩ := hgatej hc
              have hhar_tmp : harity.toNat ≤ stj.core.tmp.length := by
                rw [hokj.1.core_ok.tmp_len_arr]; exact Nat.le_trans hhar_cv hcv0_le
              m3_to_group
              refine wp_loop_inv
                (fun (ih_v, _hv, ()) mhv => mhv = mj ∧ ih_v.toNat ≤ harity.toNat)
                (fun (ih_v, _, ()) _ => harity.toNat - ih_v.toNat)
                (fun Jhv hJhv => by m3_steps; exact hJhv (0#32, _, ()) mj ⟨rfl, Nat.zero_le _⟩)
                (fun Jhv (ih_v, _hv, ()) mhv ⟨hmhv, hih_le⟩ ih_hv => ?_)
              subst mhv; m3_split_fast
              · have hih_lt : ih_v.toNat < harity.toNat := bv32_ult_lt hc
                have hih_arr : (ih_v.setWidth 64).toNat < stj.core.tmp.length := by
                  rw [bv_zext32_toNat]; omega
                have hih1 : (ih_v + 1#32).toNat = ih_v.toNat + 1 :=
                  bv32_add1_toNat (by omega) (by omega)
                m3_steps; exact ih_hv (ih_v + 1#32, _, ()) mj (by dsimp only; omega) ⟨rfl, by omega⟩
              · clear hc
                let StOkP := WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                  ht_off.toNat ht_sz.toNat scr0
                m3_to_group
                refine wp_loop_break_group (brkTs := [.bool, i64, i64])
                  (lpTs := [i64, i64])
                  (fun (ch_p, _, _, ()) mp => ∃ stp : FullState,
                    StOkP stp ∧ (FullMem c stp ⋆ R) mp)
                  (fun remp (slot, probes, ()) mp => ∃ stp : FullState,
                    slot.toNat < ht_sz.toNat ∧ probes.toNat ≤ 64 ∧ remp = 64 - probes.toNat ∧
                    stp.core.tmp = stj.core.tmp ∧ StOkP stp ∧ (FullMem c stp ⋆ R) mp)
                  ?_ ?_ ?_
                · rintro _ ⟨ch_p, _, _, ⟨⟩⟩ mp ⟨stp, hokp, hmp⟩
                  m3_let; rw [hst_g1]
                  exact ihg (ch_p, work + 4#64, g + 2#64 + arity.setWidth 64, ()) mp
                    (by dsimp only; rw [hnext_g]; omega)
                    ⟨stp, by rw [hnext_g]; exact hbd_g', hokp, hseq_next', hmp⟩
                · rintro Bp Lp remp ⟨slot, probes, ⟨⟩⟩ mp hBp hLp
                    ⟨stp, hslot_lt, hpr_le, rfl, htmp_p, hokp, hmp⟩
                  have hscrl_p := hokp.1.scratch_ok.scratch_buf_len
                  have hrl_p := hokp.1.core_ok.repr_len
                  have hrepr_p := hokp.2.2.2.2.2.2.2.2.2.2.2.1
                  have hpref_p := hokp.2.2.2.2.2.2.2.2.2.2.2.2.1
                  have hht_p := hokp.2.2.2.2.2.2.2.2.2.2.2.2.2
                  m3_split_fast
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
                    clear hc; m3_split_fast
                    · m3_to_group; refine wp_join_group (ts := [])
                        (fun () mins => ∃ stins : FullState,
                          StOkP stins ∧ (FullMem c stins ⋆ R) mins)
                        (fun _ ⟨⟩ mins ⟨stins, hokins, hmins⟩ => by
                          m3_let
                          exact hBp (changed', slot, probes, ()) mins ⟨stins, hokins, hmins⟩)
                        ?_
                      intro Jins hJins; m3_split_fast
                      · have hi32 : i32.bytes = 4 := rfl; m3_steps
                        have hm_ins : (FullMem c { stp with scratch := { stp.scratch with
                            scratch_buf := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat)
                              (g.setWidth 32)
                            res_sz := stp.scratch.res_sz + 1#64 } } ⋆ R) m := by
                          rw [hhts_n] at hm; exact hm
                        exact hJins () m ⟨_, ws_probe_insert_ok hokp hg_lt hg_le_ht hht_le
                          hslot_lt hgat, hm_ins⟩
                      · m3_let; exact hJins () mp ⟨stp, hokp, hmp⟩
                    · have hent_ne : ent ≠ 0xFFFFFFFF#32 := beq_eq_false_iff_ne.mp hc
                      have hent_gate : FullCongSpecs.GateAt
                          F_cur cv0 scr0 g_len.toNat ent.toNat := by
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
                      have hst_e1 : stp.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr =
                          emword := by
                        have h := (hpref_p (ent.toNat + 1) (by omega)).trans he1
                        rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h; exact Option.some.inj h
                      have hslot_next_lt : ((slot + 1#64) &&& (ht_sz - 1#64)).toNat <
                          ht_sz.toNat := bv64_and_sub1_lt hht_pos
                      have hpr1 : (probes + 1#64).toNat = probes.toNat + 1 :=
                        bv64_add1_toNat (n := 64) (by omega) (by decide)
                      m3_to_group; refine wp_join_group (ts := [.bool])
                        (fun _ mnxt => ∃ stn : FullState,
                          stn.core.tmp = stj.core.tmp ∧ StOkP stn ∧ (FullMem c stn ⋆ R) mnxt) ?_ ?_
                      · rintro _ ⟨_, ⟨⟩⟩ mnxt ⟨stn, htmp_n, hokn, hmn⟩
                        m3_let; exact hLp (64 - (probes + 1#64).toNat)
                          ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, ()) mnxt
                          (by omega) ⟨stn, hslot_next_lt, by omega, rfl, htmp_n, hokn, hmn⟩
                      · intro Jnxt hJnxt
                        have hjnxt_keep : ∀ b : Val .bool, Jnxt (b, ()) mp := fun b =>
                          hJnxt (b, ()) mp ⟨stp, htmp_p, hokp, hmp⟩
                        m3_split_fast
                        · have hetag_eq : emword >>> 28 = tag := by
                            have hc1 : (stp.scratch.scratch_buf[
                                (ent.setWidth 64 + 1).toNat]'he1_arr >>> 28 ==
                              st.scratch.scratch_buf[(g + 1).toNat]'hg1_arr >>> 28) = true := hc
                            have hc2 := beq_iff_eq.mp hc1
                            rwa [hst_e1, hst_g1] at hc2
                          clear hc; m3_to_group
                          refine wp_join_group (ts := [.bool])
                            (fun (matched, ()) mmatch => ∃ repr_m : List (BitVec 32),
                              repr_m.length = 2 * c.max_vars ∧
                              FullCongReprInv F_cur (2 * cv0) repr_m ∧
                              (matched = true →
                                LitEquiv (cnfOfClauses F_cur) lhs.toNat elhs.toNat) ∧
                              (FullMem c { stp with core :=
                                { stp.core with repr := repr_m } } ⋆ R) mmatch)
                            ?_ ?_
                          · rintro _ ⟨matched, ⟨⟩⟩ mmatch ⟨repr_m, hrl_m, hrepr_m, heqv_m, hmm⟩
                            let stm : FullState :=
                              { stp with core := { stp.core with repr := repr_m } }
                            have hokm : StOkP stm := workStepOk_with_repr hokp hrl_m hrepr_m
                            m3_split_fast
                            · have hlhs_ent := heqv_m hc
                              m3_steps; m3_call hEquiv
                              refine ws_equiv_call hokm hlhs_lt
                                (by rw [hst_e0]; exact helhs_lt)
                                (by rw [hst_e0]; exact hlhs_ent) hmm
                                fun ef se me hoke _ hef2 me_mem => ?_
                              m3_after_fold hQ hef2 changed' work hoke me me_mem ch_ef =>
                                exact hBp (ch_ef, slot, probes, ()) me ⟨se, hoke, me_mem⟩
                            · m3_steps; exact hJnxt (_, ()) mmatch ⟨stm, htmp_p, hokm, hmm⟩
                          · intro Jm hJm; m3_split_fast
                            · have htag0_eq : tag = 0#32 := ws_tag_eq hst_g1 hc
                              obtain ⟨_, _, hand_eq⟩ := hgat0 htag0_eq
                              m3_steps; m3_call hMatch
                              refine ⟨c, F0, F_cur, stp, scr0, g_len.toNat, R, rfl, hokp.1,
                                hokp.2.1, hokp.2.2.2.2.2.1, hokp.2.2.2.2.2.2.2.1 ▸ hrepr_p,
                                by omega, hpref_p,
                                by rw [hokp.2.2.2.2.2.2.2.1]; exact hent_gate,
                                by rw [he1, Option.getD_some, hetag_eq, htag0_eq],
                                by rw [hokp.2.2.2.2.2.2.2.1]; exact hhar_cv, hmp, ?_⟩
                              intro ok_m repr_m mm _ hrl_m hrepr_m hok_and hmm
                              m3_steps
                              exact hJm (ok_m, ()) mm
                                ⟨repr_m, hrl_m, hokp.2.2.2.2.2.2.2.1 ▸ hrepr_m,
                                 fun hokt => ws_match_and_equiv (htmp_p ▸ hand_eq) he0
                                   (hok_and hokt).2.2,
                                 hmm⟩
                            · clear hc; m3_to_group
                              refine wp_unroll_group (ts := [.bool]) fun Jmb hJmb => ?_
                              have hJmb_q : ∀ (m_ok : Bool) (repr_m : List (BitVec 32))
                                  (mf : Mem 64), repr_m.length = 2 * c.max_vars →
                                  FullCongReprInv F_cur (2 * cv0) repr_m →
                                  (m_ok = true → LitEquiv (cnfOfClauses F_cur)
                                    lhs.toNat elhs.toNat) →
                                  (FullMem c { stp with core :=
                                    { stp.core with repr := repr_m } } ⋆ R) mf →
                                  Jmb (m_ok, ()) mf :=
                                fun m_ok repr_m mf hrl hrepr hmok hmf =>
                                  hJmb (m_ok, ()) mf (by
                                    m3_let; exact hJm (m_ok, ()) mf ⟨repr_m, hrl, hrepr, hmok, hmf⟩)
                              m3_to_group; refine wp_join_group (ts := []) (fun () mf => mf = mp)
                                ?_ ?_
                              · rintro _ ⟨⟩ mf rfl; m3_to_group
                                refine wp_unroll_group (ts := [.bool]) fun Jm2 hJm2 => ?_
                                have hJm2_q : ∀ (m_ok : Bool) (repr_m : List (BitVec 32))
                                    (mf' : Mem 64), repr_m.length = 2 * c.max_vars →
                                    FullCongReprInv F_cur (2 * cv0) repr_m →
                                    (m_ok = true → LitEquiv (cnfOfClauses F_cur)
                                      lhs.toNat elhs.toNat) →
                                    (FullMem c { stp with core :=
                                      { stp.core with repr := repr_m } } ⋆ R) mf' →
                                    Jm2 (m_ok, ()) mf' :=
                                  fun m_ok repr_m mf' hrl hrepr hmok hmf =>
                                    hJm2 (m_ok, ()) mf' (by
                                      m3_let; exact hJmb_q m_ok repr_m mf' hrl hrepr hmok hmf)
                                m3_split_fast
                                · have he_tag2 : tag = 2#32 := ws_tag_eq hst_g1 hc
                                  clear hc; m3_split_fast
                                  rotate_left
                                  · m3_let; exact hJm2_q false stp.core.repr mf hrl_p hrepr_p
                                      (fun h => (by cases h)) hmp
                                  obtain ⟨har_ite, hite_s⟩ := hgat2 he_tag2
                                  have hite_e := ws_tag2_ite_def (by rw [hetag_eq, he_tag2]) hsem_e
                                  have ha_e : (emword &&& 0xFF#32).toNat = 3 := by
                                    have ht2 : (emword >>> 28).toNat = 2 := by
                                      rw [hetag_eq, he_tag2]; decide
                                    rcases hsem_e with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, h, _⟩
                                    · omega
                                    · omega
                                    · exact h
                                  obtain ⟨er0, her0_get, her0_lt⟩ := herhs 0 (by omega)
                                  obtain ⟨er1, her1_get, her1_lt⟩ := herhs 1 (by omega)
                                  obtain ⟨er2, her2_get, her2_lt⟩ := herhs 2 (by omega)
                                  have he2_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                    (g_len := g_len.toNat) (ent := ent) 2 (by omega) (by omega)
                                    (by omega)
                                  have he3_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                    (g_len := g_len.toNat) (ent := ent) 3 (by omega) (by omega)
                                    (by omega)
                                  have he4_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                    (g_len := g_len.toNat) (ent := ent) 4 (by omega) (by omega)
                                    (by omega)
                                  have hst_e2 := scr_e_get (g_len := g_len.toNat) 2 (by omega)
                                    hpref_p her0_get he2_arr (by omega)
                                  have hst_e3 := scr_e_get (g_len := g_len.toNat) 3 (by omega)
                                    hpref_p her1_get he3_arr (by omega)
                                  have hst_e4 := scr_e_get (g_len := g_len.toNat) 4 (by omega)
                                    hpref_p her2_get he4_arr (by omega)
                                  m3_steps; m3_call hFind
                                  refine ⟨F_cur, 2 * cv0, stp.core.repr, FullReprRest c stp ⋆ R,
                                    hrepr_p, hst_e2 ▸ her0_lt, focus_full_repr hmp,
                                    fun ec repra ma hrla hrepra _ _ hec_eqv hma => ?_⟩
                                  have hma' := unfocus_full_repr hma; clear hma
                                  m3_steps; m3_call hFind
                                  refine ⟨F_cur, 2 * cv0, repra,
                                    FullReprRest c { stp with core :=
                                      { stp.core with repr := repra } } ⋆ R,
                                    hrepra, hst_e3 ▸ her1_lt, focus_full_repr hma',
                                    fun et reprb mb hrlb hreprb _ _ het_eqv hmb => ?_⟩
                                  have hmb' := unfocus_full_repr hmb; clear hmb
                                  m3_steps; m3_call hFind
                                  refine ⟨F_cur, 2 * cv0, reprb,
                                    FullReprRest c { stp with core :=
                                      { stp.core with repr := reprb } } ⋆ R,
                                    hreprb, hst_e4 ▸ her2_lt, focus_full_repr hmb',
                                    fun ee reprc mc hrlc hreprc _ _ hee_eqv hmc => ?_⟩
                                  let stpc : FullState :=
                                    { stp with core := { stp.core with repr := reprc } }
                                  have hmc' : (FullMem c stpc ⋆ R) mc := by
                                    simpa [stpc] using unfocus_full_repr hmc
                                  clear hmc
                                  have hite_e' : IteGateDef (cnfOfClauses F_cur) elhs.toNat
                                      ec.toNat et.toNat ee.toNat :=
                                    ite_eval_congr hite_e (LitEquiv.refl _ _)
                                      (by rw [her0_get, Option.getD_some, ← hst_e2]; exact hec_eqv)
                                      (by rw [her1_get, Option.getD_some, ← hst_e3]; exact het_eqv)
                                      (by rw [her2_get, Option.getD_some, ← hst_e4]; exact hee_eqv)
                                  have h3 : harity.toNat = 3 := by rw [har_ite]; decide
                                  have hstp_tl : stp.core.tmp.length = c.max_vars :=
                                    hokp.1.core_ok.tmp_len_arr
                                  have htmp_ge3 : 3 ≤ stpc.core.tmp.length := by
                                    change 3 ≤ stp.core.tmp.length; omega
                                  have h0_c : (0#64 : BitVec 64).toNat < stpc.core.tmp.length := by
                                    change 0 < stp.core.tmp.length; omega
                                  have h1_c : (1#64 : BitVec 64).toNat < stpc.core.tmp.length := by
                                    change 1 < stp.core.tmp.length; omega
                                  have h2_c : (2#64 : BitVec 64).toNat < stpc.core.tmp.length := by
                                    change 2 < stp.core.tmp.length; omega
                                  have ht0_eq := tmp_st_get (k := 0) htmp_p (by omega)
                                  have ht1_eq := tmp_st_get (k := 1) htmp_p (by omega)
                                  have ht2_eq := tmp_st_get (k := 2) htmp_p (by omega)
                                  m3_to_group; refine wp_join_group (ts := [i32, i32, i32])
                                    (fun (ec', et', ee', ()) mfin => mfin = mc ∧
                                      IteGateDef (cnfOfClauses F_cur) elhs.toNat
                                        ec'.toNat et'.toNat ee'.toNat)
                                    (fun _ ⟨ec', et', ee', ⟨⟩⟩ mfin ⟨hmfin, hite_f⟩ => by
                                      subst mfin; m3_to_group
                                      refine wp_unroll_group (ts := [.bool]) fun Jmi hJmi => ?_
                                      have hJm_ok : ∀ b : Bool,
                                          (b = true → LitEquiv (cnfOfClauses F_cur)
                                            lhs.toNat elhs.toNat) →
                                          Jmi (b, ()) mc := fun b hm =>
                                        hJmi (b, ()) mc (by
                                          m3_let
                                          exact hJm2_q b reprc mc (by omega) hreprc hm hmc')
                                      m3_split_fast
                                      · have hc0 : ec' = stj.core.tmp[0]'(by omega) := by
                                          have h : ec' = stpc.core.tmp[0] := beq_iff_eq.mp hc
                                          rw [h, ht0_eq, List.getElem?_eq_getElem (by omega),
                                            Option.getD_some]
                                        clear hc; m3_split_fast
                                        · have hc1 : et' = stj.core.tmp[1]'(by omega) := by
                                            have h : et' = stpc.core.tmp[1] := beq_iff_eq.mp hc
                                            rw [h, ht1_eq, List.getElem?_eq_getElem (by omega),
                                              Option.getD_some]
                                          clear hc; m3_split_fast
                                          · have hc2 : ee' = stj.core.tmp[2]'(by omega) := by
                                              have h : ee' = stpc.core.tmp[2] := beq_iff_eq.mp hc
                                              rw [h, ht2_eq, List.getElem?_eq_getElem (by omega),
                                                Option.getD_some]
                                            m3_steps
                                            exact hJm_ok true fun _ => ws_hash_ite_equiv
                                              (by omega) hite_s hite_f hc0 hc1 hc2
                                          · m3_let; exact hJm_ok false (fun h => by cases h)
                                        · m3_let; exact hJm_ok false (fun h => by cases h)
                                      · m3_let; exact hJm_ok false (fun h => by cases h))
                                    ?_
                                  intro Jf hJf; m3_split_fast
                                  · m3_steps; refine hJf (ec ^^^ 1#32, ee, et, ()) mc ⟨rfl, ?_⟩
                                    rw [bv32_xor1_eq_litNeg]; exact iteGateDef_flip_cond hite_e'
                                  · m3_let; exact hJf (ec, et, ee, ()) mc ⟨rfl, hite_e'⟩
                                · m3_let; exact hJm2_q false stp.core.repr mf hrl_p hrepr_p
                                    (fun h => (by cases h)) hmp
                              · intro Jt2 hJt2; m3_split_fast
                                · have he_tag1 : tag = 1#32 := ws_tag_eq hst_g1 hc
                                  clear hc; m3_split_fast
                                  rotate_left
                                  · m3_let; exact hJt2 () mp rfl
                                  · obtain ⟨har_xor, hxor_s⟩ := hgat1 he_tag1
                                    have hxor_e := ws_tag1_xor_def (by rw [hetag_eq, he_tag1])
                                      hsem_e
                                    have ha_e : (emword &&& 0xFF#32).toNat = 2 := by
                                      have ht1 : (emword >>> 28).toNat = 1 := by
                                        rw [hetag_eq, he_tag1]; decide
                                      rcases hsem_e with ⟨ht, _⟩ | ⟨_, h, _⟩ | ⟨ht, _⟩
                                      · omega
                                      · exact h
                                      · omega
                                    obtain ⟨er0, her0_get, her0_lt⟩ := herhs 0 (by omega)
                                    obtain ⟨er1, her1_get, her1_lt⟩ := herhs 1 (by omega)
                                    have he2_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                      (g_len := g_len.toNat) (ent := ent) 2 (by omega) (by omega)
                                      (by omega)
                                    have he3_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                      (g_len := g_len.toNat) (ent := ent) 3 (by omega) (by omega)
                                      (by omega)
                                    have hst_e2 := scr_e_get (g_len := g_len.toNat) 2 (by omega)
                                      hpref_p her0_get he2_arr (by omega)
                                    have hst_e3 := scr_e_get (g_len := g_len.toNat) 3 (by omega)
                                      hpref_p her1_get he3_arr (by omega)
                                    m3_steps; m3_call hFind
                                    refine ⟨F_cur, 2 * cv0, stp.core.repr, FullReprRest c stp ⋆ R,
                                      hrepr_p, hst_e2 ▸ her0_lt, focus_full_repr hmp,
                                      fun e0 repra ma hrla hrepra _ _ he0_eqv hma => ?_⟩
                                    have hma' := unfocus_full_repr hma; clear hma
                                    m3_steps; m3_call hFind
                                    refine ⟨F_cur, 2 * cv0, repra,
                                      FullReprRest c { stp with core :=
                                        { stp.core with repr := repra } } ⋆ R,
                                      hrepra, hst_e3 ▸ her1_lt, focus_full_repr hma',
                                      fun e1 reprb mb hrlb hreprb _ _ he1_eqv hmb => ?_⟩
                                    let stpb : FullState :=
                                      { stp with core := { stp.core with repr := reprb } }
                                    have hmb' : (FullMem c stpb ⋆ R) mb := by
                                      simpa [stpb] using unfocus_full_repr hmb
                                    clear hmb
                                    have h2 : harity.toNat = 2 := by rw [har_xor]; decide
                                    have hstp_tl : stp.core.tmp.length = c.max_vars :=
                                      hokp.1.core_ok.tmp_len_arr
                                    have htmp_ge2 : 2 ≤ stpb.core.tmp.length := by
                                      change 2 ≤ stp.core.tmp.length; omega
                                    have h0_b :
                                        (0#64 : BitVec 64).toNat < stpb.core.tmp.length := by
                                      change 0 < stp.core.tmp.length; omega
                                    have h1_b :
                                        (1#64 : BitVec 64).toNat < stpb.core.tmp.length := by
                                      change 1 < stp.core.tmp.length; omega
                                    have ht0_eq := tmp_st_get (k := 0) htmp_p (by omega)
                                    have ht1_eq := tmp_st_get (k := 1) htmp_p (by omega)
                                    have hxor_e' : XorGateDef (cnfOfClauses F_cur) elhs.toNat
                                        e0.toNat e1.toNat :=
                                      xor_eval_congr hxor_e (LitEquiv.refl _ _)
                                        (by rw [her0_get, Option.getD_some, ← hst_e2]
                                            exact he0_eqv)
                                        (by rw [her1_get, Option.getD_some, ← hst_e3]
                                            exact he1_eqv)
                                    m3_to_group
                                    refine wp_unroll_group (ts := [.bool]) fun Jx0 hJx0 => ?_
                                    have hJxor : ∀ b : Bool,
                                        (b = true → LitEquiv (cnfOfClauses F_cur)
                                          lhs.toNat elhs.toNat) →
                                        Jx0 (b, ()) mb := fun b hm =>
                                      hJx0 (b, ()) mb (by
                                        m3_let
                                        exact hJmb_q b reprb mb (by omega) hreprb hm hmb')
                                    m3_to_group
                                    refine wp_join_group (ts := []) (fun _ mf => mf = mb) ?_ ?_
                                    · rintro _ ⟨⟩ _ rfl; m3_split_fast
                                      · have hc0 : e0 = stj.core.tmp[1]'(by omega) := by
                                          have h : e0 = stpb.core.tmp[1] := beq_iff_eq.mp hc
                                          rw [h, ht1_eq, List.getElem?_eq_getElem (by omega),
                                            Option.getD_some]
                                        clear hc; m3_split_fast
                                        · have hc1 : e1 = stj.core.tmp[0]'(by omega) := by
                                            have h : e1 = stpb.core.tmp[0] := beq_iff_eq.mp hc
                                            rw [h, ht0_eq, List.getElem?_eq_getElem (by omega),
                                              Option.getD_some]
                                          m3_let; exact hJxor true fun _ =>
                                            ws_hash_xor_equiv (by omega) hxor_s
                                              (xorGateDef_comm hxor_e') hc1 hc0
                                        · m3_let; exact hJxor false (fun h => by cases h)
                                      · m3_let; exact hJxor false (fun h => by cases h)
                                    · intro Jfb hJfb; m3_split_fast
                                      · have hc0 : e0 = stj.core.tmp[0]'(by omega) := by
                                          have h : e0 = stpb.core.tmp[0] := beq_iff_eq.mp hc
                                          rw [h, ht0_eq, List.getElem?_eq_getElem (by omega),
                                            Option.getD_some]
                                        clear hc; m3_split_fast
                                        · have hc1 : e1 = stj.core.tmp[1]'(by omega) := by
                                            have h : e1 = stpb.core.tmp[1] := beq_iff_eq.mp hc
                                            rw [h, ht1_eq, List.getElem?_eq_getElem (by omega),
                                              Option.getD_some]
                                          m3_let; exact hJxor true fun _ =>
                                            ws_hash_xor_equiv (by omega) hxor_s hxor_e' hc0 hc1
                                        · m3_let; exact hJfb () mb rfl
                                      · m3_let; exact hJfb () mb rfl
                                · m3_let; exact hJt2 () mp rfl
                        · m3_let; exact hjnxt_keep _
                  · m3_steps
                    exact hBp (changed', slot, probes, ()) mp ⟨stp, hokp, hmp⟩
                · intro _ Lp _ hLp; m3_steps
                  exact hLp 64 (_ &&& (ht_sz - 1#64), 0#64, ()) mj
                    ⟨stj, bv64_and_sub1_lt hht_pos, by decide, rfl, rfl, hokj, hmj⟩
          · intro Jgfin hJgfin
            let raw := tmpi.take arity.toNat
            have hraw_len : raw.length = arity.toNat := by simp [raw]; omega
            have hraw_lt : ∀ k < arity.toNat, (raw[k]?.getD 0#32).toNat < 2 * cv0 := fun k hk => by
              have hget : raw[k]?.getD 0#32 = tmpi[k]'(by omega) := by
                simp only [raw, List.getElem?_take, ite_eq_left hk]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              rw [hget]; exact (htmp_i' k hk).1
            have hraw_eqv : ∀ k < arity.toNat,
                LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k]?.getD 0#32).toNat
                  (raw[k]?.getD 0#32).toNat := fun k hk => by
              have hget : raw[k]?.getD 0#32 = tmpi[k]'(by omega) := by
                simp only [raw, List.getElem?_take, ite_eq_left hk]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              rw [hget]; exact (htmp_i' k hk).2
            m3_split_fast
            · -- Branch `tag == 0u`
              have htag0 : tag = 0#32 := ws_tag_eq hst_g1 hc
              have hand0 := ws_tag0_and_def htag0 hsem0
              let rhs : List Nat := ((scr0.drop (g.toNat + 2)).take arity.toNat).map BitVec.toNat
              have hscr_ge : g.toNat + 2 + arity.toNat ≤ scr0.length := by
                dsimp only [arity]
                rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hpos
                · have := (List.getElem?_eq_some_iff.mp hscr0_g1).1; omega
                · obtain ⟨_, hr, _⟩ := hrhs0 ((mword &&& 0xFF#32).toNat - 1) (by omega)
                  have := (List.getElem?_eq_some_iff.mp hr).1; omega
              obtain ⟨hraw_of_rhs, hrhs_of_raw⟩ :=
                ws_tag0_raw_of_rhs htmp_i_len hscr_ge hraw_eqv
              clear hc; m3_to_group
              refine wp_loop_inv
                (fun (il, has_false, na, ()) ml => ∃ tmpl : List (BitVec 32),
                  tmpl.length = c.max_vars ∧ na.toNat ≤ il.toNat ∧ il.toNat ≤ arity.toNat ∧
                  (∀ j, il.toNat ≤ j → j < arity.toNat → tmpl[j]? = raw[j]?) ∧
                  (∀ j < na.toNat, ∃ k < arity.toNat, tmpl[j]? = raw[k]?) ∧
                  (has_false = true → ∃ k < arity.toNat,
                    st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                  (has_false = false → ∀ k < il.toNat,
                    st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
                    ∃ j < na.toNat, tmpl[j]? = raw[k]?) ∧
                  (FullMem c (wsState st repri tmpl) ⋆ R) ml)
                (fun (il, _, _, ()) _ => arity.toNat - il.toNat)
                (fun Jl hJl => by
                  m3_steps
                  exact hJl (0#32, false, 0#32, ()) mi ⟨tmpi, htli, Nat.zero_le _, Nat.zero_le _,
                    fun j _ hj => (by simp [raw, hj]),
                    fun _ h => (by simp at h), fun h => (by cases h),
                    fun _ _ h => (by simp at h), hmi⟩)
                (fun Jl (il, has_false, na, ()) ml ⟨tmpl, htl_l, hna_le, hil_le, htail_l,
                  hsub_l, hhf_l, hnohf_l, hml⟩ ihl => ?_)
              have hokl := workStepOk_wsState hok_t hrli htl_l hrepri
              m3_split_fast
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
                have hr_vals' : (raw[il.toNat]'hil_raw).toNat < st.core.vals.length := by omega
                have hr_vals : ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat <
                    st.core.vals.length := by
                  rw [hr_eq, bv_zext32_toNat]; exact hr_vals'
                have hil1 : (il + 1#32).toNat = il.toNat + 1 :=
                  bv32_add1_toNat (n := arity.toNat) (by omega) (by omega)
                have hna1 : (na + 1#32).toNat = na.toNat + 1 :=
                  bv32_add1_toNat (n := arity.toNat) (by omega) (by omega)
                have hna_tmp : (na.setWidth 64).toNat < tmpl.length := by
                  rw [bv_zext32_toNat]; omega
                have hrv_dom := hokl.2.1.vals_domain (raw[il.toNat]'hil_raw).toNat
                  (by change _ < 2 * st.core.cur_vars; rw [hcv_t]; exact hr_lt)
                have hrv_get : st.core.vals[
                    ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat]'hr_vals =
                    st.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' := by
                  have h1 : ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat =
                      (raw[il.toNat]'hil_raw).toNat := by
                    rw [hr_eq, bv_zext32_toNat]
                  exact list_getElem_congr h1 hr_vals hr_vals'
                m3_to_group
                refine wp_unroll_group (ts := [.bool, i32]) fun Jil hJil => ?_
                have hJil_step : ∀ (hf' : Bool) (na' : BitVec 32) (ml' : Mem 64),
                    (∃ tmpl' : List (BitVec 32),
                      tmpl'.length = c.max_vars ∧ na'.toNat ≤ (il + 1#32).toNat ∧
                      (il + 1#32).toNat ≤ arity.toNat ∧
                      (∀ j, (il + 1#32).toNat ≤ j → j < arity.toNat → tmpl'[j]? = raw[j]?) ∧
                      (∀ j < na'.toNat, ∃ k < arity.toNat, tmpl'[j]? = raw[k]?) ∧
                      (hf' = true → ∃ k < arity.toNat,
                        st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                      (hf' = false → ∀ k < (il + 1#32).toNat,
                        st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
                        ∃ j < na'.toNat, tmpl'[j]? = raw[k]?) ∧
                      (FullMem c (wsState st repri tmpl') ⋆ R) ml') →
                    Jil (hf', na', ()) ml' := fun hf' na' ml' h =>
                  hJil (hf', na', ()) ml'
                    (by m3_let; exact ihl (il + 1#32, hf', na', ()) ml' (by dsimp only; omega) h)
                m3_split_fast
                · have hr_gd : raw[il.toNat]?.getD 0#32 = raw[il.toNat]'hil_raw := by
                    rw [List.getElem?_eq_getElem hil_raw, Option.getD_some]
                  have hff : st.core.vals[(raw[il.toNat]?.getD 0#32).toNat]?.getD 0#8 =
                      0xFF#8 := by
                    rw [hr_gd]
                    exact vals_slt0_eqff hr_vals' _ hrv_dom (hrv_get ▸ hc)
                  m3_steps; exact hJil_step true na ml ⟨tmpl, htl_l, by omega, by omega,
                    fun j hj1 hj2 => htail_l j (by omega) hj2, hsub_l,
                    fun _ => ⟨il.toNat, hil_lt, hff⟩, (fun h => by cases h), hml⟩
                · have hnslt_se : ((st.core.vals[
                      ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat]'
                        hr_vals).signExtend 32).slt 0#32 = false := hc
                  m3_to_group; refine wp_unroll_group (ts := [i32]) fun Jna hJna => ?_
                  have hJna_step : ∀ (na' : BitVec 32) (ml' : Mem 64),
                      (∃ tmpl' : List (BitVec 32),
                        tmpl'.length = c.max_vars ∧ na'.toNat ≤ (il + 1#32).toNat ∧
                        (il + 1#32).toNat ≤ arity.toNat ∧
                        (∀ j, (il + 1#32).toNat ≤ j → j < arity.toNat → tmpl'[j]? = raw[j]?) ∧
                        (∀ j < na'.toNat, ∃ k < arity.toNat, tmpl'[j]? = raw[k]?) ∧
                        (has_false = true → ∃ k < arity.toNat,
                          st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                        (has_false = false → ∀ k < (il + 1#32).toNat,
                          st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
                          ∃ j < na'.toNat, tmpl'[j]? = raw[k]?) ∧
                        (FullMem c (wsState st repri tmpl') ⋆ R) ml') →
                      Jna (na', ()) ml' := fun na' ml' h =>
                    hJna (na', ()) ml' (by m3_let; exact hJil_step has_false na' ml' h)
                  clear hc; m3_split_fast
                  · have hfs_tmp := focus_full_tmp hml; clear hml
                    generalize hR_tmp : FullTmpRest c (wsState st repri tmpl) ⋆ R = R_tmp at hfs_tmp
                    have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                    dsimp only [wsState] at hm; rw [bv_zext32_toNat, hr_eq] at hm
                    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ws_tag0_il_push_inv' htl_l hna_le hil_lt
                      (Nat.le_trans har_cv hcv0_le) hraw_len htail_l hsub_l hnohf_l
                    exact hJna_step (na + 1#32) m
                      ⟨tmpl.set na.toNat (raw[il.toNat]'(by rw [hraw_len]; exact hil_lt)),
                       h1, hna1 ▸ hil1 ▸ h2, hil1 ▸ h3, hil1 ▸ h4, hna1 ▸ h5, hhf_l,
                       hil1 ▸ hna1 ▸ h6, ws_unfocus_tmp hm⟩
                  · have hr_gd : raw[il.toNat]?.getD 0#32 = raw[il.toNat]'hil_raw := by
                      rw [List.getElem?_eq_getElem hil_raw, Option.getD_some]
                    have h1_val : st.core.vals[(raw[il.toNat]?.getD 0#32).toNat]?.getD 0#8 =
                        1#8 := by
                      rw [hr_gd]
                      exact vals_nslt0_ne0_eq1 hr_vals' _ hrv_dom (hrv_get ▸ hnslt_se)
                        (hrv_get ▸ hc)
                    m3_steps; exact hJna_step na ml
                      ⟨tmpl, htl_l, by omega, by omega,
                       fun j hj1 hj2 => htail_l j (by omega) hj2, hsub_l, hhf_l,
                       hil1 ▸ ws_tag0_il_true_inv h1_val hnohf_l, hml⟩
              · have hil_eq : il.toNat = arity.toNat := by
                  have hnot : ¬ il.toNat < arity.toNat := by
                    rw [hst_g1] at hc; simpa [arity] using bv32_ult_not_lt hc
                  omega
                rw [hil_eq] at hna_le htail_l hnohf_l; clear hc
                m3_to_group; refine wp_unroll_group fun Jt0 hJt0 => ?_
                have hJg0 : ∀ (ch' : Bool) (har' : BitVec 32) (nh' : Bool) (mj : Mem 64),
                    (∃ stj : FullState,
                      WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                        ht_sz.toNat scr0 stj ∧
                      (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag har') ∧
                      (FullMem c stj ⋆ R) mj) →
                    Jt0 (ch', har', nh', ()) mj := fun ch' har' nh' mj h =>
                  hJt0 (ch', har', nh', ()) mj
                    (by m3_let; exact hJgfin (ch', _, har', nh', ()) mj h)
                m3_split_fast
                · obtain ⟨k, hk, hff⟩ := hhf_l hc
                  obtain ⟨x, hx_mem, hx_eqv⟩ := hrhs_of_raw k hk
                  have hun_ent := andFold_has_false_entails hokl.2.1 hcl_t hand0 hlhs_eqv0
                    ⟨x, hx_mem, (raw[k]?.getD 0#32).toNat,
                     by change _ < 2 * st.core.cur_vars; rw [hcv_t]; exact hraw_lt k hk,
                     hx_eqv, hff⟩
                  m3_steps; m3_call hUnit
                  refine ws_unit_xor1 hokl hlhs_lt hun_ent hml
                    fun uf su mu hoku _ hu2 hmu => ?_
                  m3_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                    rw [hst_g1]; exact hJg0 ch' _ false mu ⟨su, hoku, (fun h => by cases h), hmu⟩
                · m3_to_group
                  refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt0b hJt0b => ?_
                  have hJg0b : ∀ (ch' : Bool) (har' : BitVec 32) (nh' : Bool) (mj : Mem 64),
                      (∃ stj : FullState,
                        WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                          ht_sz.toNat scr0 stj ∧
                        (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag har') ∧
                        (FullMem c stj ⋆ R) mj) →
                      Jt0b (ch', har', nh', ()) mj := fun ch' har' nh' mj h =>
                    hJt0b (ch', har', nh', ()) mj (by m3_let; exact hJg0 ch' har' nh' mj h)
                  m3_split_fast
                  · have hna0 : na.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                    have hun_ent := ws_tag0_all_true_entails hokl.2.1 hcl_t hand0 hlhs_eqv0
                      (fun m hm => hokl.2.2.2.2.2.2.2.1 ▸ hraw_lt m hm) hraw_of_rhs
                      (hna0 ▸ hnohf_l (by assumption))
                    m3_steps; m3_call hUnit
                    refine ws_unit_call hokl hlhs_lt hun_ent hml fun uf su mu hoku _ hu2 hmu => ?_
                    m3_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                      rw [hst_g1]; exact hJg0b ch' _ false mu ⟨su, hoku, (fun h => by cases h), hmu⟩
                  · have hhf_f : has_false = false := by assumption
                    have hna_pos : 0 < na.toNat := by
                      have hne : na ≠ 0#32 := beq_eq_false_iff_ne.mp hc
                      rcases Nat.eq_zero_or_pos na.toNat with hz | hp
                      · exact absurd (BitVec.eq_of_toNat_eq hz) hne
                      · exact hp
                    have hfwd_l := ws_tag0_hf_false_fwd F_cur hraw_lt hraw_of_rhs (hnohf_l hhf_f)
                    m3_to_group
                    refine wp_join_group (ts := [])
                      (fun () ms => ∃ tmps : List (BitVec 32),
                        tmps.length = c.max_vars ∧
                        (∀ j < na.toNat, ∃ k < arity.toNat, tmps[j]? = raw[k]?) ∧
                        (∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
                          (st.core.vals[r]?.getD 0#8 = 1#8 ∨
                            ∃ j < na.toNat, (tmps[j]?.getD 0#32).toNat = r)) ∧
                        (FullMem c (wsState st repri tmps) ⋆ R) ms)
                      ?_ ?_
                    · rintro _ ⟨⟩ ms ⟨tmps, htl_s, hsub_s, hfwd_s, hms⟩
                      m3_to_group
                      refine wp_loop_break_group (brkTs := [.bool, i32, i32])
                        (lpTs := [i32, i32])
                        (fun (clash, ua, _si, ()) md => ∃ tmpd : List (BitVec 32),
                          tmpd.length = c.max_vars ∧ ua.toNat ≤ na.toNat ∧
                          (∀ j < ua.toNat, ∃ k < na.toNat, tmpd[j]? = tmps[k]?) ∧
                          (clash = true → ∃ z ∈ (tmps.take na.toNat).map BitVec.toNat,
                            litNeg z ∈ (tmps.take na.toNat).map BitVec.toNat) ∧
                          (clash = false → 0 < ua.toNat ∧
                            ∀ j < na.toNat, ∃ q < ua.toNat,
                              (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32) ∧
                          (FullMem c (wsState st repri tmpd) ⋆ R) md)
                        (fun remd (ua, si, ()) md => ∃ tmpd : List (BitVec 32),
                          tmpd.length = c.max_vars ∧ ua.toNat ≤ si.toNat ∧ si.toNat ≤ na.toNat ∧
                          remd = na.toNat - si.toNat ∧
                          (0 < si.toNat → 0 < ua.toNat) ∧
                          (∀ j, si.toNat ≤ j → j < na.toNat → tmpd[j]? = tmps[j]?) ∧
                          (∀ j < ua.toNat, ∃ k < na.toNat, tmpd[j]? = tmps[k]?) ∧
                          (∀ j < si.toNat, ∃ q < ua.toNat,
                            (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32) ∧
                          (FullMem c (wsState st repri tmpd) ⋆ R) md)
                        ?_ ?_ ?_
                      · rintro _ ⟨clash, ua, _si, ⟨⟩⟩ md
                          ⟨tmpd, htl_d, hua_le, hsub_tmps, hcl_d, huf_d, hmd⟩
                        have hokd := workStepOk_wsState hok_t hrli htl_d hrepri
                        obtain ⟨hsub_d, hsub_raw_d⟩ := ws_tag0_sub_raw_d hsub_tmps hsub_s
                          hrhs_of_raw (by omega) hraw_len
                        m3_to_group
                        refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt0c hJt0c => ?_
                        have hJg0c : ∀ (ch' : Bool) (har' : BitVec 32) (nh' : Bool) (mj : Mem 64),
                            (∃ stj : FullState, WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0
                              g_len.toNat ht_off.toNat ht_sz.toNat scr0 stj ∧
                            (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag har') ∧
                            (FullMem c stj ⋆ R) mj) → Jt0c (ch', har', nh', ()) mj :=
                          fun ch' har' nh' mj h =>
                            hJt0c (ch', har', nh', ()) mj (by m3_let; exact hJg0b ch' har' nh' mj h)
                        m3_split_fast
                        · have hun_ent := ws_tag0_clash_entails hand0 hlhs_eqv0 hsub_s hrhs_of_raw
                            hraw_len (by omega) (hcl_d hc)
                          m3_steps; m3_call hUnit
                          refine ws_unit_xor1 hokd hlhs_lt hun_ent hmd
                            fun uf su mu hoku _ hu2 hmu => ?_
                          m3_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                            rw [hst_g1]
                            exact hJg0c ch' _ false mu ⟨su, hoku, (fun h => by cases h), hmu⟩
                        · obtain ⟨hua_pos, hcov_d⟩ := huf_d hc; clear hc; m3_to_group
                          refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt0d hJt0d => ?_
                          have hJg0d : ∀ (ch' : Bool) (har' : BitVec 32) (nh' : Bool) (mj : Mem 64),
                              (∃ stj : FullState, WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0
                                g_len.toNat ht_off.toNat ht_sz.toNat scr0 stj ∧
                              (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag har') ∧
                              (FullMem c stj ⋆ R) mj) → Jt0d (ch', har', nh', ()) mj :=
                            fun ch' har' nh' mj h =>
                              hJt0d (ch', har', nh', ()) mj
                                (by m3_let; exact hJg0c ch' har' nh' mj h)
                          m3_split_fast
                          · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                            omega
                          · have hev_d := ws_tag0_dedup_eval hokd.2.1 hcl_t hcv_t (by omega) hand0
                              hlhs_eqv0 hfwd_s hcov_d hsub_raw_d
                            m3_to_group
                            refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt0e hJt0e => ?_
                            have hJg0e : ∀ (ch' : Bool) (har' : BitVec 32) (nh' : Bool)
                                (mj : Mem 64),
                                (∃ stj : FullState, WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0
                                  g_len.toNat ht_off.toNat ht_sz.toNat scr0 stj ∧
                                (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag har') ∧
                                (FullMem c stj ⋆ R) mj) → Jt0e (ch', har', nh', ()) mj :=
                              fun ch' har' nh' mj h =>
                                hJt0e (ch', har', nh', ()) mj
                                  (by m3_let; exact hJg0d ch' har' nh' mj h)
                            m3_split_fast
                            · have hua1 : ua.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
                              obtain ⟨ht0_lt, ht0_eqv⟩ := ws_tag0_ua1_equiv (by omega) hraw_len
                                (hsub_d 0 (by omega)) hraw_lt (hua1 ▸ hev_d)
                              have h0_tmp : (0#64 : BitVec 64).toNat < tmpd.length := by
                                change 0 < tmpd.length; omega
                              m3_steps; m3_call hEquiv
                              refine ws_equiv_call hokd hlhs_lt ht0_lt ht0_eqv hmd
                                fun ef se me hoke _ hef2 hme => ?_
                              m3_after_fold hQ hef2 changed work hoke me hme ch' =>
                                exact hJg0e ch' _ false me ⟨se, hoke, (fun h => by cases h), hme⟩
                            · have hua_ge2 : 2 ≤ ua.toNat := by
                                have hne := beq_eq_false_iff_ne.mp hc
                                have : ua.toNat ≠ 1 := fun h => hne (BitVec.eq_of_toNat_eq h); omega
                              have hlhs_vals : (lhs.setWidth 64).toNat < st.core.vals.length := by
                                rw [bv_zext32_toNat, hvlen_t]; omega
                              have hua_cv : ua.toNat ≤ cv0 := by omega
                              have hua_8 : ua.toNat ≤ 8 := by
                                change arity.toNat ≤ 8 at har_8; omega
                              m3_to_group; refine wp_join_group (ts := [.bool])
                                (fun (ch_v, ()) mv => ∃ stv : FullState,
                                  WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                                    ht_off.toNat ht_sz.toNat scr0 stv ∧
                                  stv.core.tmp = tmpd ∧ (FullMem c stv ⋆ R) mv)
                                (fun _ ⟨ch_v, ⟨⟩⟩ mv ⟨stv, hokv, htmp_v, hmv⟩ => by
                                  m3_steps
                                  exact hJg0e ch_v ua true mv ⟨stv, hokv, fun _ =>
                                    ⟨hua_cv,
                                     fun _ => ⟨hua_ge2, hua_8, fun α hα => htmp_v ▸ hev_d α hα⟩,
                                     fun h => (by rw [htag0] at h; cases h),
                                     fun h => (by rw [htag0] at h; cases h)⟩, hmv⟩)
                                ?_
                              intro Jv hJv; m3_split_fast
                              · have hv1 : st.core.vals[lhs.toNat]?.getD 0#8 = 1#8 :=
                                  vals_sgt0_eq1 (by rw [hvlen_t]; omega) hlhs_vals
                                    (hokd.2.1.vals_domain lhs.toNat
                                      (hokd.2.2.2.2.2.2.2.1 ▸ hlhs_lt))
                                    hc
                                have hents := ws_tag0_lhs_true_ents hokd.2.1 hokd.2.2.2.2.2.1
                                  (hokd.2.2.2.2.2.2.2.1 ▸ hlhs_lt) hv1 hev_d
                                m3_to_group; refine wp_loop_inv
                                  (fun (ch_k, k, ()) mk => ∃ stk : FullState,
                                    k.toNat ≤ ua.toNat ∧
                                    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                                      ht_off.toNat ht_sz.toNat scr0 stk ∧
                                    stk.core.tmp = tmpd ∧ (FullMem c stk ⋆ R) mk)
                                  (fun (_, k, ()) _ => ua.toNat - k.toNat)
                                  (fun Jk hJk => by
                                    m3_steps; exact hJk (changed, 0#32, ()) md
                                      ⟨wsState st repri tmpd, Nat.zero_le _, hokd, rfl, hmd⟩)
                                  (fun Jk (ch_k, k, ()) mk
                                    ⟨stk, hk_le, hokk, htmp_k, hmk⟩ ihk => ?_)
                                m3_split_fast
                                · have hk_lt : k.toNat < ua.toNat := bv32_ult_lt hc
                                  have hk_tmp : (k.setWidth 64).toNat < stk.core.tmp.length := by
                                    rw [bv_zext32_toNat, htmp_k]; omega
                                  have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
                                    bv32_add1_toNat (n := ua.toNat) (by omega) (by omega)
                                  obtain ⟨htk_lt, htk_ent⟩ := ws_tag0_unit_k_args htmp_k hk_lt
                                    hraw_len (by omega) hsub_d hraw_lt hents hk_tmp
                                  m3_steps; m3_call hUnit
                                  refine ws_unit_call hokk htk_lt htk_ent hmk
                                    fun uf su mu hoku htmpu hu2 hmu => ?_
                                  m3_after_fold hQ hu2 ch_k work hoku mu hmu ch_u =>
                                    exact ihk (ch_u, k + 1#32, ()) mu (by dsimp only; omega)
                                      ⟨su, by omega, hoku, htmpu.trans htmp_k, hmu⟩
                                · m3_let; exact hJv (ch_k, ()) mk ⟨stk, hokk, htmp_k, hmk⟩
                              · m3_let
                                exact hJv (changed, ()) md ⟨wsState st repri tmpd, hokd, rfl, hmd⟩
                      · rintro Bd Ld remd ⟨ua, si, ⟨⟩⟩ md hBd hLd
                          ⟨tmpd, htl_d, hua_le, hsi_le, rfl, hua_pos_if, htail_d,
                           hsub_tmps, hcov_d, hmd⟩
                        m3_split_fast
                        · have hsi_lt : si.toNat < na.toNat := bv32_ult_lt hc
                          have hna_max : na.toNat ≤ c.max_vars :=
                            Nat.le_trans hna_le (Nat.le_trans har_cv hcv0_le)
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
                            bv32_add1_toNat (by omega) (by omega)
                          have hua1 : (ua + 1#32).toNat = ua.toNat + 1 :=
                            bv32_add1_toNat (n := na.toNat) (by omega) (by omega)
                          clear hc; m3_to_group
                          refine wp_unroll_group (ts := [.bool, i32]) fun Jua hJua => ?_
                          have hJua_step : ∀ (b' : Bool) (ua' : BitVec 32) (md' : Mem 64),
                              (∃ tmpd' : List (BitVec 32),
                                tmpd'.length = c.max_vars ∧
                                ua'.toNat ≤ (si + 1#32).toNat ∧ (si + 1#32).toNat ≤ na.toNat ∧
                                (0 < (si + 1#32).toNat → 0 < ua'.toNat) ∧
                                (∀ j, (si + 1#32).toNat ≤ j → j < na.toNat →
                                  tmpd'[j]? = tmps[j]?) ∧
                                (∀ j < ua'.toNat, ∃ k < na.toNat, tmpd'[j]? = tmps[k]?) ∧
                                (∀ j < (si + 1#32).toNat, ∃ q < ua'.toNat,
                                  (tmpd'[q]?.getD 0#32) = tmps[j]?.getD 0#32) ∧
                                (FullMem c (wsState st repri tmpd') ⋆ R) md') →
                              Jua (b', ua', ()) md' :=
                            fun b' ua' md' ⟨t', ht', hu', hs', hp', htl', hs_t', hc', hm'⟩ =>
                              hJua (b', ua', ()) md' (by
                                m3_let; exact hLd (na.toNat - (si + 1#32).toNat)
                                  (ua', si + 1#32, ()) md' (by omega)
                                  ⟨t', ht', hu', hs', rfl, hp', htl', hs_t', hc', hm'⟩)
                          m3_split_fast
                          · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                            have hsi0 : si.toNat = 0 :=
                              Nat.eq_zero_of_not_pos fun h => by have := hua_pos_if h; omega
                            have h0_tmp : (0#64 : BitVec 64).toNat < tmpd.length := by
                              change 0 < tmpd.length; omega
                            have hfs_tmp := focus_full_tmp hmd; clear hmd
                            generalize hR_tmp : FullTmpRest c (wsState st repri tmpd) ⋆ R =
                              R_tmp at hfs_tmp
                            have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                            dsimp only [wsState] at hm; rw [hcur_eq] at hm
                            obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ws_tag0_dedup_first_inv hsi0
                              htl_d hsi_lt (by omega) htail_d (by omega)
                            exact hJua_step _ 1#32 m ⟨tmpd.set 0 cur, h1,
                              (by rw [hsi1]; have h1 : (1#32).toNat = 1 := rfl; omega),
                              hsi1 ▸ h3, hsi1 ▸ h4,
                              hsi1 ▸ h5, h6, hsi1 ▸ h7, ws_unfocus_tmp hm⟩
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
                            m3_split_fast
                            · have hcur_prev : cur = tmpd[ua.toNat - 1]'(by omega) :=
                                (hcur_eq ▸ beq_iff_eq.mp hc).trans hprev_eq
                              obtain ⟨h1, h2, h3, h4, h5⟩ := ws_tag0_dedup_dup_inv' (by omega)
                                (by omega) hua_pos hua_le hsi_lt hcur_prev htail_d hcov_d
                              m3_steps; exact hLd (na.toNat - (si + 1#32).toNat)
                                (ua, si + 1#32, ()) md (by omega)
                                ⟨tmpd, htl_d, hsi1 ▸ h1, hsi1 ▸ h2, rfl, hsi1 ▸ h3, hsi1 ▸ h4,
                                 hsub_tmps, hsi1 ▸ h5, hmd⟩
                            · m3_split_fast
                              · have hcur_xor : cur = prev ^^^ 1#32 := hcur_eq ▸ beq_iff_eq.mp hc
                                have hcl := ws_tag0_dedup_clash (by omega) (by omega) hua_pos hua_le
                                  hsi_lt hprev_eq hsub_tmps hcur_xor
                                m3_steps; exact hBd (true, ua, si + 1#32, ()) md
                                  ⟨tmpd, htl_d, (by omega), hsub_tmps, fun _ => hcl,
                                   (fun h => by cases h), hmd⟩
                              · have hua_tmp : (ua.setWidth 64).toNat < tmpd.length := by
                                  rw [bv_zext32_toNat]; omega
                                have hfs_tmp := focus_full_tmp hmd; clear hmd
                                generalize hR_tmp : FullTmpRest c (wsState st repri tmpd) ⋆ R =
                                  R_tmp at hfs_tmp
                                have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                                dsimp only [wsState] at hm; rw [bv_zext32_toNat, hcur_eq] at hm
                                obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ws_tag0_dedup_push_inv htl_d
                                  (by omega) (by omega) hua_le hsi_lt htail_d hsub_tmps hcov_d
                                exact hJua_step _ (ua + 1#32) m ⟨tmpd.set ua.toNat cur, h1,
                                  hua1 ▸ hsi1 ▸ h2, hsi1 ▸ h3, hua1 ▸ hsi1 ▸ h4, hsi1 ▸ h5,
                                  hua1 ▸ h6, hua1 ▸ hsi1 ▸ h7, ws_unfocus_tmp hm⟩
                        · have hsi_eq : si.toNat = na.toNat := by
                            have := bv32_ult_not_lt hc; omega
                          rw [hsi_eq] at hua_pos_if hcov_d
                          m3_steps; exact hBd (false, ua, si, ()) md
                            ⟨tmpd, htl_d, hsi_eq ▸ hua_le, hsub_tmps, (fun h => by cases h),
                             fun _ => ⟨hua_pos_if hna_pos, hcov_d⟩, hmd⟩
                      · intro _ Ld _ hLd; m3_steps
                        exact hLd na.toNat (0#32, 0#32, ()) ms
                          ⟨tmps, htl_s, Nat.zero_le _, Nat.zero_le _, rfl,
                           fun h => by simp at h, fun _ _ _ => rfl,
                           fun _ h => by simp at h, fun _ h => by simp at h, hms⟩
                    · intro Js hJs; m3_split_fast
                      · m3_steps; m3_call hSort
                        refine ⟨tmpl, FullTmpRest c (wsState st repri tmpl) ⋆ R, by omega,
                          focus_full_tmp hml, fun tmps ms htl_s hperm_s _ hms => ?_⟩
                        have hms' : (FullMem c (wsState st repri tmps) ⋆ R) ms :=
                          ws_unfocus_tmp hms
                        clear hms; m3_steps
                        obtain ⟨hsub_s, hfwd_s⟩ := ws_tag0_post_sort (htl_s.trans htl_l) htl_l
                          hna_le (Nat.le_trans har_cv hcv0_le) hperm_s hsub_l hfwd_l
                        exact hJs () ms ⟨tmps, htl_s.trans htl_l, hsub_s, hfwd_s, hms'⟩
                      · m3_steps; exact hJs () ml ⟨tmpl, htl_l, hsub_l, hfwd_l, hml⟩
            · -- Not `tag == 0u`: check `tag == 1u && arity == 2u`, else `tag == 2u && arity == 3u`
              have htag_ne0 : tag ≠ 0#32 := ws_tag_ne hst_g1 hc
              clear hc; m3_to_group; refine wp_unroll_group fun Jt1 hJt1 => ?_
              have hJg1 : ∀ (ch' : Bool) (nh' : Bool) (mj : Mem 64),
                  (∃ stj : FullState,
                    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                      ht_sz.toNat scr0 stj ∧
                    (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                    (FullMem c stj ⋆ R) mj) →
                  Jt1 (ch', nh', ()) mj := fun ch' nh' mj h =>
                hJt1 (ch', nh', ()) mj
                  (by m3_let; rw [hst_g1]; exact hJgfin (ch', _, arity, nh', ()) mj h)
              m3_to_group
              refine wp_join_group (ts := []) (fun () mj => tag ≠ 1#32 ∧ mj = mi) ?_ ?_
              · rintro _ ⟨⟩ mj ⟨htag_ne1, rfl⟩
                m3_to_group
                refine wp_unroll_group (ts := [.bool, .bool]) fun Jt2b hJt2b => ?_
                have hJg2b : ∀ (ch' : Bool) (nh' : Bool) (mj : Mem 64),
                    (∃ stj : FullState,
                      WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                        ht_sz.toNat scr0 stj ∧
                      (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                      (FullMem c stj ⋆ R) mj) →
                    Jt2b (ch', nh', ()) mj := fun ch' nh' mj h =>
                  hJt2b (ch', nh', ()) mj (by m3_let; exact hJg1 ch' nh' mj h)
                m3_split_fast
                · have htag2 : tag = 2#32 := ws_tag_eq hst_g1 hc
                  m3_split_fast
                  · have har3 : arity = 3#32 := ws_har_eq hst_g1 hc
                    have har3_n : arity.toNat = 3 := by rw [har3]; decide
                    have hite0 := ws_tag2_ite_def htag2 hsem0
                    have ht_ge3 : 3 ≤ tmpi.length := by omega
                    have h0_tmp : (0#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 0 < tmpi.length; omega
                    have h1_tmp : (1#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 1 < tmpi.length; omega
                    have h2_tmp : (2#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 2 < tmpi.length; omega
                    let cl := tmpi[0]'(by omega); let tl := tmpi[1]'(by omega)
                    let el := tmpi[2]'(by omega)
                    have hcl_lt : cl.toNat < 2 * cv0 := (htmp_i' 0 (by omega)).1
                    have htl_lt : tl.toNat < 2 * cv0 := (htmp_i' 1 (by omega)).1
                    have hel_lt : el.toNat < 2 * cv0 := (htmp_i' 2 (by omega)).1
                    have hcl_vals : (cl.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat, hvlen_t]; omega
                    have htl_vals : (tl.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat, hvlen_t]; omega
                    have hel_vals : (el.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat, hvlen_t]; omega
                    have hvc_dom := hoki.2.1.vals_domain cl.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ hcl_lt)
                    have hvt_dom := hoki.2.1.vals_domain tl.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                    have hve_dom := hoki.2.1.vals_domain el.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt)
                    have hite_t : IteGateDef (cnfOfClauses F_cur) lhs.toNat
                        cl.toNat tl.toNat el.toNat :=
                      ite_eval_congr hite0 hlhs_eqv0 (htmp_i' 0 (by omega)).2
                        (htmp_i' 1 (by omega)).2 (htmp_i' 2 (by omega)).2
                    clear hFind hSort hMatch
                    clear hc; m3_to_group
                    refine wp_unroll_group (ts := [.bool, .bool]) fun Jt2c hJt2c => ?_
                    have hJg2c : ∀ (ch' nh' : Bool) (mj : Mem 64),
                        (∃ stj : FullState,
                          WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                            ht_sz.toNat scr0 stj ∧
                          (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                          (FullMem c stj ⋆ R) mj) → Jt2c (ch', nh', ()) mj :=
                      fun ch' nh' mj h =>
                        hJt2c (ch', nh', ()) mj (by m3_let; exact hJg2b ch' nh' mj h)
                    m3_split_fast
                    · have hvc_ne := vals_ne0_1_or_ff (by rw [hvlen_t]; omega) hcl_vals hvc_dom hc
                      have heqc := ite_cond_const_equiv hoki.2.1 hoki.2.2.2.2.2.1 hite_t
                        (hoki.2.2.2.2.2.2.2.1 ▸ hcl_lt) hvc_ne
                      dsimp only [wsState] at heqc
                      m3_to_group; refine wp_join_group (ts := [i32])
                        (fun (br, ()) mbr => mbr = mj ∧ br.toNat < 2 * cv0 ∧
                          LitEquiv (cnfOfClauses F_cur) lhs.toNat br.toNat)
                        (fun _ ⟨br, ⟨⟩⟩ mbr ⟨hmbr, hbr_lt, heqv_br⟩ => by
                          subst mbr; m3_steps; m3_call hEquiv
                          refine ws_equiv_call hoki hlhs_lt hbr_lt heqv_br hmi
                            fun ef se me hoke _ hef2 hme => ?_
                          m3_after_fold hQ hef2 changed work hoke me hme ch' =>
                            exact hJg2c ch' false me ⟨se, hoke, (fun h => by cases h), hme⟩)
                        ?_
                      intro Jbr hJbr; m3_split_fast
                      · have hvc1 := vals_sgt0_eq1 (by rw [hvlen_t]; omega) hcl_vals hvc_dom hc
                        m3_let; exact hJbr (tl, ()) mj
                          ⟨rfl, htl_lt, by simpa [hvc1, bv_zext32_toNat] using heqc⟩
                      · have hvcff := vals_ne0_nsgt0_eqff (by rw [hvlen_t]; omega) hcl_vals
                          hvc_dom hvc_ne hc
                        m3_let; exact hJbr (el, ()) mj
                          ⟨rfl, hel_lt, by simpa [hvcff, bv_zext32_toNat] using heqc⟩
                    · clear hc; m3_to_group
                      refine wp_unroll_group (ts := [.bool, .bool]) fun Jt2d hJt2d => ?_
                      have hJg2d : ∀ (ch' nh' : Bool) (mj' : Mem 64),
                          (∃ stj : FullState,
                            WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                              ht_sz.toNat scr0 stj ∧
                            (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                            (FullMem c stj ⋆ R) mj') → Jt2d (ch', nh', ()) mj' :=
                        fun ch' nh' mj' h =>
                          hJt2d (ch', nh', ()) mj' (by m3_let; exact hJg2c ch' nh' mj' h)
                      m3_split_fast
                      · have hte : tl = el := beq_iff_eq.mp hc
                        have heqt : LitEquiv (cnfOfClauses F_cur) lhs.toNat tl.toNat :=
                          ite_equal_branches_equiv hite_t (LitEquiv.refl _ _)
                            (LitEquiv.refl _ _) (by rw [hte]; exact LitEquiv.refl _ _)
                        m3_steps; m3_call hEquiv
                        refine ws_equiv_call hoki hlhs_lt htl_lt heqt hmi
                          fun ef se me hoke _ hef2 hme => ?_
                        m3_after_fold hQ hef2 changed work hoke me hme ch' =>
                          exact hJg2d ch' false me ⟨se, hoke, (fun h => by cases h), hme⟩
                      · clear hc; m3_to_group
                        refine wp_unroll_group (ts := [.bool, .bool]) fun Jt2e hJt2e => ?_
                        have hJg2e : ∀ (ch' nh' : Bool) (mj' : Mem 64),
                            (∃ stj : FullState,
                              WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                                ht_sz.toNat scr0 stj ∧
                              (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                              (FullMem c stj ⋆ R) mj') → Jt2e (ch', nh', ()) mj' :=
                          fun ch' nh' mj' h =>
                            hJt2e (ch', nh', ()) mj' (by m3_let; exact hJg2d ch' nh' mj' h)
                        m3_to_group; refine wp_join_group (ts := []) (fun _ mf => mf = mj) ?_ ?_
                        · rintro _ ⟨⟩ mf hmf; subst mf; m3_to_group
                          refine wp_unroll_group (ts := [.bool, .bool]) fun Jt2f hJt2f => ?_
                          have hJg2f : ∀ (ch' nh' : Bool) (mj' : Mem 64),
                              (∃ stj : FullState,
                                WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                                  ht_sz.toNat scr0 stj ∧
                                (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                                (FullMem c stj ⋆ R) mj') → Jt2f (ch', nh', ()) mj' :=
                            fun ch' nh' mj' h =>
                              hJt2f (ch', nh', ()) mj' (by m3_let; exact hJg2e ch' nh' mj' h)
                          m3_to_group; refine wp_join_group (ts := []) (fun _ mf => mf = mj)
                            ?_ ?_
                          · rintro _ ⟨⟩ mf hmf; subst mf; m3_to_group
                            refine wp_unroll_group (ts := [.bool, .bool]) fun Jt2g hJt2g => ?_
                            have hJg2g : ∀ (ch' nh' : Bool) (mj' : Mem 64),
                                (∃ stj : FullState,
                                  WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                                    ht_sz.toNat scr0 stj ∧
                                  (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                                  (FullMem c stj ⋆ R) mj') → Jt2g (ch', nh', ()) mj' :=
                              fun ch' nh' mj' h =>
                                hJt2g (ch', nh', ()) mj' (by m3_let; exact hJg2f ch' nh' mj' h)
                            m3_to_group; refine wp_join_group (ts := []) (fun _ mf => mf = mj)
                              ?_ ?_
                            · rintro _ ⟨⟩ mf hmf; subst mf; m3_to_group
                              refine wp_unroll_group (ts := [.bool, .bool]) fun Jt2h hJt2h => ?_
                              have hJg2h : ∀ (ch' nh' : Bool) (mj' : Mem 64),
                                  (∃ stj : FullState,
                                    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                                      ht_off.toNat ht_sz.toNat scr0 stj ∧
                                    (nh' = true →
                                      HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                                    (FullMem c stj ⋆ R) mj') → Jt2h (ch', nh', ()) mj' :=
                                fun ch' nh' mj' h =>
                                  hJt2h (ch', nh', ()) mj' (by m3_let; exact hJg2g ch' nh' mj' h)
                              m3_to_group; refine wp_join_group (ts := []) (fun _ mf => mf = mj)
                                ?_ ?_
                              · rintro _ ⟨⟩ mf hmf; subst mf; m3_to_group
                                refine wp_join_group (ts := [])
                                  (fun () mfl => ∃ tmps : List (BitVec 32),
                                    tmps.length = c.max_vars ∧
                                    IteGateDef (cnfOfClauses F_cur) lhs.toNat
                                      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat
                                      (tmps[2]?.getD 0#32).toNat ∧
                                    (FullMem c (wsState st repri tmps) ⋆ R) mfl)
                                  (fun _ ⟨⟩ mfl ⟨tmps, htl_s, hite_s, hmfl⟩ => by
                                    m3_let
                                    have hoks := workStepOk_wsState hok_t hrli htl_s hrepri
                                    exact hJg2h changed true mfl ⟨wsState st repri tmps, hoks,
                                      fun _ => ⟨har_cv',
                                       fun h => absurd (htag2.symm.trans h) (by decide),
                                       fun h => absurd (htag2.symm.trans h) (by decide),
                                       fun _ => ⟨har3, hite_s⟩⟩, hmfl⟩)
                                  ?_
                                intro _ hJflip; m3_split_fast
                                · have hfs_tmp := focus_full_tmp hmi; clear hmi
                                  dsimp only [wsState] at hfs_tmp
                                  generalize hR_tmp : FullTmpRest c (wsState st repri tmpi) ⋆ R =
                                    R_tmp at hfs_tmp
                                  have ht1_len : 1 < tmpi.length := by omega
                                  have ht2_len : 2 < tmpi.length := by omega
                                  have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                                  let tmps := ((tmpi.set 0 (cl ^^^ 1#32)).set 1 el).set 2 tl
                                  have htmps_mem : (FullMem c (wsState st repri tmps) ⋆ R) m := by
                                    simpa only [wsState, cl, tl, el, tmps,
                                      show (1 : BitVec 32) = 1#32 from rfl,
                                      show (0#64 : BitVec 64).toNat = 0 from rfl,
                                      show (1#64 : BitVec 64).toNat = 1 from rfl,
                                      show (2#64 : BitVec 64).toNat = 2 from rfl] using
                                      ws_unfocus_tmp hm
                                  refine hJflip () m ⟨tmps, by simp [tmps, htli], ?_, htmps_mem⟩
                                  have h0_c : tmps[0]?.getD 0#32 = cl ^^^ 1#32 := by
                                    dsimp only [tmps]
                                    rw [List.getElem?_set_ne (by decide),
                                      List.getElem?_set_ne (by decide),
                                      List.getElem?_set_self (by omega), Option.getD_some]
                                  have h1_c : tmps[1]?.getD 0#32 = el := by
                                    dsimp only [tmps]
                                    rw [List.getElem?_set_ne (by decide),
                                      List.getElem?_set_self (by simp; omega), Option.getD_some]
                                  have h2_c : tmps[2]?.getD 0#32 = tl := by
                                    dsimp only [tmps]
                                    rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
                                  rw [h0_c, h1_c, h2_c, bv32_xor1_eq_litNeg]
                                  exact iteGateDef_flip_cond hite_t
                                · m3_let; refine hJflip () mj ⟨tmpi, htli, ?_, hmi⟩
                                  rw [List.getElem?_eq_getElem (by omega),
                                    List.getElem?_eq_getElem (by omega),
                                    List.getElem?_eq_getElem (by omega),
                                    Option.getD_some, Option.getD_some, Option.getD_some]
                                  exact hite_t
                              · intro J4 hJ4; m3_split_fast
                                · have htff := vals_slt0_eqff (by rw [hvlen_t]; omega) htl_vals
                                    hvt_dom hc
                                  clear hc; m3_split_fast
                                  · have hun := ite_branches_both_false_entails hoki.2.1
                                      hoki.2.2.2.2.2.1 hite_t (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                                      (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt)
                                      (by simpa [wsState] using htff)
                                      (vals_slt0_eqff
                                        (by dsimp only [wsState]; rw [hvlen_t]; omega)
                                        hel_vals hve_dom hc)
                                    m3_steps; m3_call hUnit
                                    refine ws_unit_xor1 hoki hlhs_lt hun hmi
                                      fun uf su mu hoku _ hu2 hmu => ?_
                                    m3_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                                      exact hJg2h ch' false mu
                                        ⟨su, hoku, (fun h => by cases h), hmu⟩
                                  · m3_let; exact hJ4 () mj rfl
                                · m3_let; exact hJ4 () mj rfl
                            · intro J3 hJ3; m3_split_fast
                              · have ht1 := vals_sgt0_eq1 (by rw [hvlen_t]; omega) htl_vals
                                  hvt_dom hc
                                clear hc; m3_split_fast
                                · have hun := ite_branches_both_true_entails hoki.2.1
                                    hoki.2.2.2.2.2.1 hite_t (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                                    (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt) (by simpa [wsState] using ht1)
                                    (vals_sgt0_eq1 (by dsimp only [wsState]; rw [hvlen_t]; omega)
                                      hel_vals hve_dom hc)
                                  m3_steps; m3_call hUnit
                                  refine ws_unit_call hoki hlhs_lt hun hmi
                                    fun uf su mu hoku _ hu2 hmu => ?_
                                  m3_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                                    exact hJg2g ch' false mu ⟨su, hoku, (fun h => by cases h), hmu⟩
                                · m3_let; exact hJ3 () mj rfl
                              · m3_let; exact hJ3 () mj rfl
                          · intro J2 hJ2; m3_split_fast
                            · have htff := vals_slt0_eqff (by rw [hvlen_t]; omega) htl_vals
                                hvt_dom hc
                              clear hc; m3_split_fast
                              · have heqc := ite_branches_false_true_equiv hoki.2.1
                                  hoki.2.2.2.2.2.1 hite_t (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                                  (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt) (by simpa [wsState] using htff)
                                  (vals_sgt0_eq1 (by dsimp only [wsState]; rw [hvlen_t]; omega)
                                    hel_vals hve_dom hc)
                                m3_steps; m3_call hEquiv
                                refine ws_equiv_call hoki hlhs_lt
                                  (by change (cl ^^^ 1#32).toNat < 2 * cv0
                                      rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hcl_lt)
                                  (by change LitEquiv (cnfOfClauses F_cur) lhs.toNat
                                        (cl ^^^ 1#32).toNat
                                      rw [bv32_xor1_eq_litNeg]; exact heqc) hmi
                                  fun ef se me hoke _ hef2 hme => ?_
                                m3_after_fold hQ hef2 changed work hoke me hme ch' =>
                                  exact hJg2f ch' false me ⟨se, hoke, (fun h => by cases h), hme⟩
                              · m3_let; exact hJ2 () mj rfl
                            · m3_let; exact hJ2 () mj rfl
                        · intro J1 hJ1; m3_split_fast
                          · have ht1 := vals_sgt0_eq1 (by rw [hvlen_t]; omega) htl_vals hvt_dom hc
                            clear hc; m3_split_fast
                            · have heqc := ite_branches_true_false_equiv hoki.2.1
                                hoki.2.2.2.2.2.1 hite_t (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                                (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt) (by simpa [wsState] using ht1)
                                (vals_slt0_eqff (by dsimp only [wsState]; rw [hvlen_t]; omega)
                                  hel_vals hve_dom hc)
                              m3_steps; m3_call hEquiv
                              refine ws_equiv_call hoki hlhs_lt hcl_lt heqc hmi
                                fun ef se me hoke _ hef2 hme => ?_
                              m3_after_fold hQ hef2 changed work hoke me hme ch' =>
                                exact hJg2e ch' false me ⟨se, hoke, (fun h => by cases h), hme⟩
                            · m3_let; exact hJ1 () mj rfl
                          · m3_let; exact hJ1 () mj rfl
                  · have hc_n : arity ≠ 3#32 := ws_har_ne hst_g1 hc
                    exfalso; rcases hsem0 with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, ha3, _⟩
                    · have : (mword >>> 28).toNat = 2 := by
                        change tag.toNat = 2; rw [htag2]; decide
                      omega
                    · have : (mword >>> 28).toNat = 2 := by
                        change tag.toNat = 2; rw [htag2]; decide
                      omega
                    · exact hc_n (BitVec.eq_of_toNat_eq ha3)
                · have htag_ne2 : tag ≠ 2#32 := ws_tag_ne hst_g1 hc
                  exfalso; rcases hsem0 with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
                  · apply htag_ne0; apply BitVec.eq_of_toNat_eq; simpa [tag] using ht
                  · apply htag_ne1; apply BitVec.eq_of_toNat_eq; simpa [tag] using ht
                  · apply htag_ne2; apply BitVec.eq_of_toNat_eq; simpa [tag] using ht
              · intro Jt1_2 hJt1_2
                m3_split_fast
                · have htag1 : tag = 1#32 := ws_tag_eq hst_g1 hc
                  m3_split_fast
                  · have har2 : arity = 2#32 := ws_har_eq hst_g1 hc
                    have har2_n : arity.toNat = 2 := by rw [har2]; decide
                    have hxor0 := ws_tag1_xor_def htag1 hsem0
                    have ht_ge2 : 2 ≤ tmpi.length := by omega
                    have h0_tmp : (0#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 0 < tmpi.length; omega
                    have h1_tmp : (1#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 1 < tmpi.length; omega
                    let t0 := tmpi[0]'(by omega); let t1 := tmpi[1]'(by omega)
                    have ht0_lt : t0.toNat < 2 * cv0 := (htmp_i' 0 (by omega)).1
                    have ht1_lt : t1.toNat < 2 * cv0 := (htmp_i' 1 (by omega)).1
                    have ht0_vals : (t0.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat, hvlen_t]; omega
                    have ht1_vals : (t1.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat, hvlen_t]; omega
                    have hv0_dom := hoki.2.1.vals_domain t0.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ ht0_lt)
                    have hv1_dom := hoki.2.1.vals_domain t1.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ ht1_lt)
                    have hxor_t : XorGateDef (cnfOfClauses F_cur) lhs.toNat t0.toNat t1.toNat :=
                      xor_eval_congr hxor0 hlhs_eqv0 (htmp_i' 0 (by omega)).2
                        (htmp_i' 1 (by omega)).2
                    clear hFind hSort hMatch
                    clear hc; m3_to_group
                    refine wp_unroll_group (ts := [.bool, .bool]) fun Jt1c hJt1c => ?_
                    have hJg1c : ∀ (ch' nh' : Bool) (mj : Mem 64),
                        (∃ stj : FullState,
                          WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                            ht_sz.toNat scr0 stj ∧
                          (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                          (FullMem c stj ⋆ R) mj) → Jt1c (ch', nh', ()) mj :=
                      fun ch' nh' mj h =>
                        hJt1c (ch', nh', ()) mj (by m3_let; exact hJg1 ch' nh' mj h)
                    m3_split_fast
                    · have hv0_ne := vals_ne0_1_or_ff (by rw [hvlen_t]; omega) ht0_vals hv0_dom hc
                      m3_to_group; refine wp_join_group (ts := [i32])
                        (fun (eq, ()) meq => meq = mi ∧ eq.toNat < 2 * cv0 ∧
                          LitEquiv (cnfOfClauses F_cur) lhs.toNat eq.toNat)
                        ?_ ?_
                      · rintro _ ⟨eq, ⟨⟩⟩ meq ⟨hmeq, heq_lt, heqv_eq⟩; subst meq
                        m3_steps; m3_call hEquiv
                        refine ws_equiv_call hoki hlhs_lt heq_lt heqv_eq hmi
                          fun ef se me hoke _ hef2 hme => ?_
                        m3_after_fold hQ hef2 changed work hoke me hme ch' =>
                          exact hJg1c ch' false me ⟨se, hoke, (fun h => by cases h), hme⟩
                      · intro Jeq hJeq
                        have heqc := xor_const_equiv hoki.2.1 hoki.2.2.2.2.2.1 hxor_t
                          (hoki.2.2.2.2.2.2.2.1 ▸ ht0_lt) hv0_ne
                        dsimp only [wsState] at heqc
                        m3_split_fast
                        · have hv0_1 := vals_sgt0_eq1 (by rw [hvlen_t]; omega) ht0_vals hv0_dom hc
                          m3_let; refine hJeq (t1 ^^^ 1#32, ()) mi ⟨rfl,
                            by change (t1 ^^^ 1#32).toNat < 2 * cv0; rw [bv32_xor1_eq_litNeg]
                               exact bv32_xor1_lt_even ht1_lt,
                            by change LitEquiv (cnfOfClauses F_cur) lhs.toNat (t1 ^^^ 1#32).toNat
                               rw [bv32_xor1_eq_litNeg]
                               simpa [hv0_1, bv_zext32_toNat] using heqc⟩
                        · have hv0_ff := vals_ne0_nsgt0_eqff (by rw [hvlen_t]; omega) ht0_vals
                            hv0_dom hv0_ne hc
                          m3_let; refine hJeq (t1, ()) mi
                            ⟨rfl, ht1_lt, by simpa [hv0_ff, bv_zext32_toNat] using heqc⟩
                    · clear hc; m3_to_group
                      refine wp_unroll_group (ts := [.bool, .bool]) fun Jt1d hJt1d => ?_
                      have hJg1d : ∀ (ch' nh' : Bool) (mj : Mem 64),
                          (∃ stj : FullState,
                            WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                              ht_sz.toNat scr0 stj ∧
                            (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                            (FullMem c stj ⋆ R) mj) → Jt1d (ch', nh', ()) mj :=
                        fun ch' nh' mj h =>
                          hJt1d (ch', nh', ()) mj (by m3_let; exact hJg1c ch' nh' mj h)
                      m3_split_fast
                      · have hv1_ne := vals_ne0_1_or_ff (by rw [hvlen_t]; omega) ht1_vals
                          hv1_dom hc
                        m3_to_group; refine wp_join_group (ts := [i32])
                          (fun (eq, ()) meq => meq = mi ∧ eq.toNat < 2 * cv0 ∧
                            LitEquiv (cnfOfClauses F_cur) lhs.toNat eq.toNat)
                          ?_ ?_
                        · rintro _ ⟨eq, ⟨⟩⟩ meq ⟨hmeq, heq_lt, heqv_eq⟩; subst meq
                          m3_steps; m3_call hEquiv
                          refine ws_equiv_call hoki hlhs_lt heq_lt heqv_eq hmi
                            fun ef se me hoke _ hef2 hme => ?_
                          m3_after_fold hQ hef2 changed work hoke me hme ch' =>
                            exact hJg1d ch' false me ⟨se, hoke, (fun h => by cases h), hme⟩
                        · intro Jeq hJeq
                          have heqc := xor_const_equiv hoki.2.1 hoki.2.2.2.2.2.1
                            (xorGateDef_comm hxor_t) (hoki.2.2.2.2.2.2.2.1 ▸ ht1_lt) hv1_ne
                          dsimp only [wsState] at heqc
                          m3_split_fast
                          · have hv1_1 := vals_sgt0_eq1 (by rw [hvlen_t]; omega) ht1_vals
                              hv1_dom hc
                            m3_let; refine hJeq (t0 ^^^ 1#32, ()) mi ⟨rfl,
                              by change (t0 ^^^ 1#32).toNat < 2 * cv0; rw [bv32_xor1_eq_litNeg]
                                 exact bv32_xor1_lt_even ht0_lt,
                              by change LitEquiv (cnfOfClauses F_cur) lhs.toNat (t0 ^^^ 1#32).toNat
                                 rw [bv32_xor1_eq_litNeg]
                                 simpa [hv1_1, bv_zext32_toNat] using heqc⟩
                          · have hv1_ff := vals_ne0_nsgt0_eqff (by rw [hvlen_t]; omega) ht1_vals
                              hv1_dom hv1_ne hc
                            m3_let; refine hJeq (t0, ()) mi
                              ⟨rfl, ht0_lt, by simpa [hv1_ff, bv_zext32_toNat] using heqc⟩
                      · clear hc; m3_to_group
                        refine wp_unroll_group (ts := [.bool, .bool]) fun Jt1e hJt1e => ?_
                        have hJg1e : ∀ (ch' nh' : Bool) (mj : Mem 64),
                            (∃ stj : FullState,
                              WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                                ht_sz.toNat scr0 stj ∧
                              (nh' = true → HashGateOk F_cur cv0 lhs stj.core.tmp tag arity) ∧
                              (FullMem c stj ⋆ R) mj) → Jt1e (ch', nh', ()) mj :=
                          fun ch' nh' mj h =>
                            hJt1e (ch', nh', ()) mj (by m3_let; exact hJg1d ch' nh' mj h)
                        m3_split_fast
                        · obtain ⟨hul_lt, hul_ent⟩ := ws_tag1_same_var_unit_args hxor0 hlhs_eqv0
                            (htmp_i' 0 (by omega)).2 (htmp_i' 1 (by omega)).2 hlhs_lt
                            (bv32_shr1_eq_div2 hc)
                          clear hc; m3_to_group; refine wp_join_group (ts := [i32])
                            (fun (ul, ()) mu => mu = mi ∧ ul.toNat < 2 * cv0 ∧
                              (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]))
                            ?_ ?_
                          · rintro _ ⟨ul, ⟨⟩⟩ mu ⟨hmu, hul_lt', hul_ent'⟩; subst mu
                            m3_steps; m3_call hUnit
                            refine ws_unit_call hoki hul_lt' hul_ent' hmi
                              fun uf su mu hoku _ hu2 hmu => ?_
                            m3_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                              exact hJg1e ch' false mu ⟨su, hoku, (fun h => by cases h), hmu⟩
                          · intro Jul hJul; m3_split_fast
                            · have hc' : tmpi[0]'(by omega) = tmpi[1]'(by omega) :=
                                beq_iff_eq.mp hc
                              rw [ite_eq_left hc'] at hul_lt hul_ent
                              m3_let; exact hJul (lhs ^^^ 1#32, ()) mi ⟨rfl, hul_lt, hul_ent⟩
                            · have hc' : tmpi[0]'(by omega) ≠ tmpi[1]'(by omega) :=
                                beq_eq_false_iff_ne.mp hc
                              rw [ite_eq_right hc'] at hul_lt hul_ent
                              m3_let; exact hJul (lhs, ()) mi ⟨rfl, hul_lt, hul_ent⟩
                        · clear hc; m3_to_group
                          refine wp_join_group (ts := [])
                            (fun () mf => ∃ tmps : List (BitVec 32),
                              tmps.length = c.max_vars ∧
                              XorGateDef (cnfOfClauses F_cur) lhs.toNat
                                (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat ∧
                              (FullMem c (wsState st repri tmps) ⋆ R) mf)
                            (fun _ ⟨⟩ mf ⟨tmps, htl_s, hxor_s, hmf⟩ => by
                              m3_let
                              have hoks := workStepOk_wsState hok_t hrli htl_s hrepri
                              exact hJg1e changed true mf ⟨wsState st repri tmps, hoks,
                                fun _ => ⟨har_cv',
                                 fun h => absurd (htag1.symm.trans h) (by decide),
                                 fun _ => ⟨har2, hxor_s⟩,
                                 fun h => absurd (htag1.symm.trans h) (by decide)⟩, hmf⟩)
                            ?_
                          intro _ hJswap; m3_split_fast
                          · have hfs_tmp := focus_full_tmp hmi; clear hmi
                            dsimp only [wsState] at hfs_tmp
                            generalize hR_tmp : FullTmpRest c (wsState st repri tmpi) ⋆ R =
                              R_tmp at hfs_tmp
                            have ht1_len : 1 < tmpi.length := by omega
                            have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                            let tmps := (tmpi.set 0 t1).set 1 t0
                            have htmps_mem : (FullMem c (wsState st repri tmps) ⋆ R) m := by
                              simpa only [wsState, t0, t1, tmps,
                                show (0#64 : BitVec 64).toNat = 0 from rfl,
                                show (1#64 : BitVec 64).toNat = 1 from rfl] using
                                ws_unfocus_tmp hm
                            refine hJswap () m ⟨tmps, by simp [tmps, htli], ?_, htmps_mem⟩
                            have h0_c : tmps[0]?.getD 0#32 = t1 := by
                              dsimp only [tmps]
                              rw [List.getElem?_set_ne (by decide),
                                List.getElem?_set_self (by omega), Option.getD_some]
                            have h1_c : tmps[1]?.getD 0#32 = t0 := by
                              dsimp only [tmps]
                              rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
                            rw [h0_c, h1_c]; exact xorGateDef_comm hxor_t
                          · m3_let; refine hJswap () mi ⟨tmpi, htli, ?_, hmi⟩
                            rw [List.getElem?_eq_getElem (by omega),
                              List.getElem?_eq_getElem (by omega), Option.getD_some,
                              Option.getD_some]
                            exact hxor_t
                  · have hc_n : arity ≠ 2#32 := ws_har_ne hst_g1 hc
                    exfalso; rcases hsem0 with ⟨ht, _⟩ | ⟨_, ha2, _⟩ | ⟨ht, _⟩
                    · have : (mword >>> 28).toNat = 1 := by
                        change tag.toNat = 1; rw [htag1]; decide
                      omega
                    · exact hc_n (BitVec.eq_of_toNat_eq ha2)
                    · have : (mword >>> 28).toNat = 1 := by
                        change tag.toNat = 1; rw [htag1]; decide
                      omega
                · have htag_ne1 : tag ≠ 1#32 := ws_tag_ne hst_g1 hc
                  m3_let; exact hJt1_2 () mi ⟨htag_ne1, rfl⟩
    · m3_steps
      exact hJex mg ⟨st, ⟨hlen_t, hw_t, hmk_t, hnd_t, hext_t, hcl_t, hdm_t,
        hcv_t, hfl_t, har_t, hal_t, hrepr_t, hpref_t, hht_t⟩, hmg⟩
  · m3_steps
    exact hJex mg ⟨st, ⟨hlen_t, hw_t, hmk_t, hnd_t, hext_t, hcl_t, hdm_t,
      hcv_t, hfl_t, har_t, hal_t, hrepr_t, hpref_t, hht_t⟩, hmg⟩

end WorkStepProof

end LeanQbe.T.Examples.Kissat.FullM3CongBva
