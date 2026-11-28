/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGate0

/-!
# Congruence Gate Re-Evaluation Hash-Table Probe WP Proof (`WpEvalGateHash`)

Proves `ev_hash_wp` for `evHashExpr` (the 128-probe hash-table lookup, AND/XOR/ITE matching,
equivalence folding, and slot insertion block of `full_cong_eval_gate`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

attribute [local c0_load] ev_c0_load_full_tmp0 ev_c0_load_full_tmp1 ev_c0_load_full_tmp2
attribute [local c0_store] ev_c0_store_full_tmp0 ev_c0_store_full_tmp1 ev_c0_store_full_tmp2

local macro "ev_u" : tactic =>
  `(tactic| try dsimp only [evL2, evCmp32, evCmp64, evLd32, evLdK32, evLd8, evSgn0])

local macro "ev_steps" : tactic =>
  `(tactic| (ev_u; c0_hsteps!))

local macro "ev_steps_ng" : tactic =>
  `(tactic| (ev_u; c0_hsteps_nogrp))

local macro "ev_split" : tactic =>
  `(tactic| (ev_u; c0_hsplit))

private theorem ev_scr_ent_lt {scr : List (BitVec 32)} {g_len : Nat} {ent : BitVec 32}
    (k : Nat) (hk : ent.toNat + k < g_len) (hg : g_len ≤ scr.length) (hcap : scr.length < 2 ^ 32) :
    (ent.setWidth 64 + BitVec.ofNat 64 k).toNat < scr.length := by
  have h1 : (ent.setWidth 64 + BitVec.ofNat 64 k).toNat = ent.toNat + k := by
    rw [BitVec.toNat_add, bv_zext32_toNat, bv64_ofNat_toNat_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  omega

private theorem ev_scr_ent_get {scr scr0 : List (BitVec 32)} {g_len : Nat} {ent v : BitVec 32}
    (k : Nat) (hk : ent.toNat + k < g_len) (hg : g_len ≤ scr.length)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hget : scr0[ent.toNat + k]? = some v)
    (harr : (ent.setWidth 64 + BitVec.ofNat 64 k).toNat < scr.length) (hcap : scr.length < 2 ^ 32) :
    scr[(ent.setWidth 64 + BitVec.ofNat 64 k).toNat]'harr = v := by
  have h1 : (ent.setWidth 64 + BitVec.ofNat 64 k).toNat = ent.toNat + k := by
    rw [BitVec.toNat_add, bv_zext32_toNat, bv64_ofNat_toNat_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have h := (hpref (ent.toNat + k) hk).trans hget
  rw [← h1, List.getElem?_eq_getElem harr] at h
  exact Option.some.inj h

private theorem ev_gate_tag2_ite {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g : Nat}
    {scr0 : List (BitVec 32)} {lhs0 mword : BitVec 32}
    (hg : CongGateAt maxA F_cur cv scr0 g_len g)
    (h0 : scr0[g]? = some lhs0) (h1 : scr0[g + 1]? = some mword)
    (htag : mword >>> 28 = 2#32) :
    congGateArity mword = 3 ∧
    IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
      (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat := by
  obtain ⟨l', m', hl', hm', _, _, _, _, _, hsem⟩ := hg
  rcases Option.some.inj (hl'.symm.trans h0) with rfl
  rcases Option.some.inj (hm'.symm.trans h1) with rfl
  have h2 : (m' >>> 28).toNat = 2 := by rw [htag]; decide
  rcases hsem with ⟨⟨h0', _⟩ | ⟨h3', _⟩, _⟩ | ⟨ht, _⟩ | ⟨_, ha3, hite⟩
  · omega
  · omega
  · omega
  · exact ⟨ha3, hite⟩

private theorem ev_match_and_equiv {F_cur : List (List Nat)} {tmps scr0 : List (BitVec 32)}
    {lhs elhs : BitVec 32} {ent ha : Nat}
    (hand_eq : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range ha).all (fun k => evalLitVal α (tmps[k]?.getD 0#32).toNat))
    (he0 : scr0[ent]? = some elhs)
    (hm_all : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α (scr0[ent]?.getD 0#32).toNat =
        (List.range ha).all (fun k => evalLitVal α (tmps[k]?.getD 0#32).toNat)) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat elhs.toNat := by
  refine ev_litEquiv_of_eval fun α hα => ?_
  have hm' := hm_all α hα; rw [he0, Option.getD_some] at hm'; rw [hand_eq α hα, hm']

private theorem ev_hash_ite_equiv {F_cur : List (List Nat)} {elhs ec' et' ee' lhs : BitVec 32}
    {tmps : List (BitVec 32)} (htmp_ge3 : 3 ≤ tmps.length)
    (hite_s : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        if evalLitVal α (tmps[0]?.getD 0#32).toNat
        then evalLitVal α (tmps[1]?.getD 0#32).toNat
        else evalLitVal α (tmps[2]?.getD 0#32).toNat)
    (hite_f : IteGateDef (cnfOfClauses F_cur) elhs.toNat ec'.toNat et'.toNat ee'.toNat)
    (hc0 : ec' = tmps[0]'(by omega)) (hc1 : et' = tmps[1]'(by omega))
    (hc2 : ee' = tmps[2]'(by omega)) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat elhs.toNat := by
  refine ev_litEquiv_of_eval fun α hα => ?_
  rw [hite_s α hα, iteGateDef_eval hα hite_f, hc0, hc1, hc2,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some, Option.getD_some]

private theorem ev_egtype_cases {em htag : BitVec 32}
    (h : (if em >>> 28 = 3#32 then 0#32 else em >>> 28) = htag) :
    (htag = 0#32 → em >>> 28 = 0#32 ∨ em >>> 28 = 3#32) ∧
    (htag = 1#32 → em >>> 28 = 1#32) ∧
    (htag = 2#32 → em >>> 28 = 2#32) := by
  by_cases h3 : em >>> 28 = 3#32
  · rw [ite_eq_left h3] at h
    exact ⟨fun _ => Or.inr h3, fun h1 => (by rw [← h] at h1; cases h1),
      fun h2 => (by rw [← h] at h2; cases h2)⟩
  · rw [ite_eq_right h3] at h
    exact ⟨fun h0 => Or.inl (h.trans h0), fun h1 => h.trans h1, fun h2 => h.trans h2⟩

public section

/-- Canonical WP proof for the hash-table probe, match, fold, and insert block `evHashExpr`. -/
theorem ev_hash_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hAndMatch : Γ.Has "full_cong_and_match" Spec.fullCongAndMatchSpec)
    (hXorMatch : Γ.Has "full_cong_xor_match" Spec.fullCongXorMatchSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64}
    {g ht_off ht_sz ctrl_off ht_lim : BitVec 64}
    {next_ep gtype lhs' iw htag' harity : BitVec 32} {need_hash changed' : Bool}
    {J44 : Cont [i32, .bool, .bool]} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hmaxA : maxA ≤ congAndArityMax)
    (hht_pos : 0 < ht_sz.toNat) (hg_lt : g.toNat < g_len) (hg_ht : g_len ≤ ht_off.toNat)
    (hht_le : ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap)
    (hgat_g0 : CongGateAt maxA F_cur cv0 scr0 g_len g.toNat)
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat
      scr0 scr_in s0)
    (hgate0 : need_hash = true →
      EvHashGateOk maxA F_cur cv0 gtype htag' harity lhs' s0.core.tmp)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat
      ht_sz.toNat scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hJ44 : ∀ iw_o ch_o keep_o s' m',
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat
        scr0 scr_in s' → (FullMem c s' ⋆ R) m' → J44 (iw_o, ch_o, keep_o, ()) m') :
    wp Γ Q X (evHashExpr c.hdr g ht_off ht_sz ctrl_off c.pScratchBuf c.pRepr c.pTmp ht_lim
      next_ep gtype lhs' iw htag' harity need_hash changed' J44) m0 := by
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hcv_le : cv0 ≤ c.max_vars := hok0.2.1 ▸ hok0.1.1.core_ok.cur_vars_le
  unfold evHashExpr; ev_split
  rotate_left
  · ev_steps; exact hJ44 iw changed' false s0 m0 hok0 hm0
  have hnh : need_hash = true := hc; clear hc; ev_split
  rotate_left
  · ev_steps; exact hJ44 iw changed' false s0 m0 hok0 hm0
  obtain ⟨hlhs'_lt, hhar_cv, _, hhar_ge2, htmp_lt, _, hgat0, hgat1, hgat2, _⟩ := hgate0 hnh
  have hhar_tmp : harity.toNat ≤ s0.core.tmp.length := by
    rw [hok0.1.1.core_ok.tmp_len_arr]; exact Nat.le_trans hhar_cv hcv_le
  clear hc; ev_steps_ng
  refine wp_loop_inv (ts := [i32, i64])
    (fun (ih_v, _hv, ()) mhv => mhv = m0 ∧ ih_v.toNat ≤ harity.toNat)
    (fun (ih_v, _, ()) _ => harity.toNat - ih_v.toNat)
    (fun _ hJhv => by ev_steps; exact hJhv (0#32, _, ()) m0 ⟨rfl, Nat.zero_le _⟩)
    (fun _ ⟨ih_v, _hv, ⟨⟩⟩ mhv ⟨hmhv, hih_le⟩ ih_hv => ?_)
  subst mhv; ev_split
  · have hih_lt : ih_v.toNat < harity.toNat := by omega
    have hih_arr : (ih_v.setWidth 64).toNat < s0.core.tmp.length := by rw [bv_zext32_toNat]; omega
    have hih1 : (ih_v + 1#32).toNat = ih_v.toNat + 1 := bv32_add1_lt_of (by omega)
    ev_steps; exact ih_hv (ih_v + 1#32, _, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
  clear hc; ev_steps_ng
  refine wp_loop_break_group (brkTs := [.bool, .bool, i64, i64, .bool]) (lpTs := [i64, i64, .bool])
    (fun (_, _, _, _, _, ()) mp => ∃ stp : FullState,
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat
        scr0 scr_in stp ∧ (FullMem c stp ⋆ R) mp)
    (fun remp (slot, probes, _, ()) mp => ∃ stp : FullState,
      slot.toNat < ht_sz.toNat ∧ probes.toNat ≤ 128 ∧ remp = 128 - probes.toNat ∧
      stp.core.tmp = s0.core.tmp ∧
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat
        scr0 scr_in stp ∧ (FullMem c stp ⋆ R) mp) ?_ ?_ ?_
  · rintro _ ⟨ch_p, keep_p, _, _, _, ⟨⟩⟩ mp ⟨stp, hokp, hmp⟩
    ev_steps; exact hJ44 ih_v ch_p keep_p stp mp hokp hmp
  · rintro Bp Lp remp ⟨slot, probes, seen_self, ⟨⟩⟩ mp hBp hLp
      ⟨stp, hslot_lt, hpr_le, rfl, htmp_p, hokp, hmp⟩
    have hscrl_p := hokp.1.1.scratch_ok.scratch_buf_len
    have hrl_p := hokp.1.1.core_ok.repr_len
    have hrepr_p := hokp.2.2.2.2.2.1
    have hpref_p := hokp.2.2.2.2.2.2.1
    have hht_p := hokp.2.2.2.2.2.2.2.1
    ev_split
    rotate_left
    · ev_steps; exact hBp (changed', true, slot, probes, seen_self, ()) mp ⟨stp, hokp, hmp⟩
    have hpr_lt : probes.toNat < 128 := by simpa using hc
    have hhts_n : (ht_off + slot).toNat = ht_off.toNat + slot.toNat := by
      show (ht_off.toNat + slot.toNat) % 2 ^ 64 = ht_off.toNat + slot.toNat
      exact Nat.mod_eq_of_lt (by omega)
    have hhts_arr : (ht_off + slot).toNat < stp.scratch.scratch_buf.length := by omega
    let ent := stp.scratch.scratch_buf[(ht_off + slot).toNat]'hhts_arr
    have hent_slot : stp.scratch.scratch_buf[ht_off.toNat + slot.toNat]?.getD 0xFFFFFFFF#32 =
        ent := by rw [← hhts_n, List.getElem?_eq_getElem hhts_arr, Option.getD_some]
    clear hc; ev_split
    · clear hc; ev_steps_ng
      refine wp_join_group (ts := [])
        (fun () mins => ∃ stins : FullState,
          EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat
            scr0 scr_in stins ∧ (FullMem c stins ⋆ R) mins)
        (fun _ ⟨⟩ mins ⟨stins, hokins, hmins⟩ => by
          ev_steps; exact hBp (changed', true, slot, probes, seen_self, ()) mins
            ⟨stins, hokins, hmins⟩) ?_
      intro Jins hJins; ev_split
      · ev_steps; exact hJins () mp ⟨stp, hokp, hmp⟩
      clear hc; ev_split
      rotate_left; · ev_steps; exact hJins () mp ⟨stp, hokp, hmp⟩
      clear hc; ev_split
      rotate_left; · ev_steps; exact hJins () mp ⟨stp, hokp, hmp⟩
      clear hc; ev_steps
      have htr : (g.setWidth 32).toNat = g.toNat := ev_bv32_truncate_u64_of_lt g (by omega)
      have hm_ins : (FullMem c { stp with scratch := { stp.scratch with
          scratch_buf := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat) (g.setWidth 32)
          res_sz := stp.scratch.res_sz + 1#64 } } ⋆ R) m := by rw [hhts_n] at hm; exact hm
      exact hJins () m ⟨_, evCoreOk_set_ht hg_ht hslot_lt hht_le hokp (htr.symm ▸ hgat_g0) _,
        hm_ins⟩
    have hent_eq : ent ≠ 0xFFFFFFFF#32 := by simpa [ent] using hc
    have hslot_next_lt : ((slot + 1#64) &&& (ht_sz - 1#64)).toNat < ht_sz.toNat :=
      ev_ht_slot_lt hht_pos
    have hpr1 : (probes + 1#64).toNat = probes.toNat + 1 := bv64_add1_lt (by omega)
    have hent_gate : CongGateAt maxA F_cur cv0 scr0 g_len ent.toNat := by
      rcases hht_p slot.toNat hslot_lt with he | hg_e
      · rw [hent_slot] at he; exact absurd he hent_eq
      · rwa [hent_slot] at hg_e
    have ⟨elhs, emword, he0, he1, helhs_lt, hbd_e, _, _, herhs, _⟩ := hent_gate
    have he0_arr : ent.toNat < stp.scratch.scratch_buf.length := by omega
    have he1_arr : (ent.setWidth 64 + 1#64).toNat < stp.scratch.scratch_buf.length :=
      ev_scr_ent_lt (g_len := g_len) 1 (by omega) (by omega) (by omega)
    have hst_e0 : stp.scratch.scratch_buf[(ent.setWidth 64).toNat]'
        (by rw [bv_zext32_toNat]; exact he0_arr) = elhs := by
      have h := (hpref_p ent.toNat (by omega)).trans he0
      rw [list_getElem_congr (bv_zext32_toNat ent) _ he0_arr]
      rw [List.getElem?_eq_getElem he0_arr] at h; exact Option.some.inj h
    have hst_e1 : stp.scratch.scratch_buf[(ent.setWidth 64 + 1#64).toNat]'he1_arr = emword :=
      ev_scr_ent_get (g_len := g_len) 1 (by omega) (by omega) hpref_p he1 he1_arr (by omega)
    clear hc; ev_split
    · ev_steps
      exact hLp (128 - (probes + 1#64).toNat)
        ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, true, ()) mp (by omega)
        ⟨stp, hslot_next_lt, by omega, rfl, htmp_p, hokp, hmp⟩
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32])
      (fun (eg, ()) meg => meg = mp ∧
        eg = if emword >>> 28 = 3#32 then 0#32 else emword >>> 28) ?_
      (fun Jeg hJeg => by
        ev_split
        · have h3 : emword >>> 28 = 3#32 := by rw [← hst_e1]; exact hc
          ev_steps; exact hJeg (0#32, ()) mp ⟨rfl, by simp [h3]⟩
        · have hn3 : emword >>> 28 ≠ 3#32 := by rw [← hst_e1]; exact hc
          ev_steps
          have hge : stp.scratch.scratch_buf[(ent.setWidth 64 + 1#64).toNat]'he1_arr >>> 28 =
              emword >>> 28 := by rw [hst_e1]
          have hgoal := hJeg (emword >>> 28, ()) mp ⟨rfl, by simp [hn3]⟩
          rw [← hge] at hgoal; exact hgoal)
    rintro _ ⟨eg, ⟨⟩⟩ meg ⟨hmeg, heg_eq⟩; subst meg
    ev_steps_ng
    refine wp_join_group (ts := [.bool, .bool])
      (fun _ mnxt => ∃ stn : FullState, stn.core.tmp = s0.core.tmp ∧
        EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat
          scr0 scr_in stn ∧ (FullMem c stn ⋆ R) mnxt)
      (fun _ ⟨_, _, ⟨⟩⟩ mnxt ⟨stn, htmp_n, hokn, hmn⟩ => by
        ev_steps; exact hLp (128 - (probes + 1#64).toNat)
          ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, seen_self, ()) mnxt (by omega)
          ⟨stn, hslot_next_lt, by omega, rfl, htmp_n, hokn, hmn⟩) ?_
    intro Jnxt hJnxt; ev_split
    rotate_left; · ev_steps; exact hJnxt (_, _, ()) mp ⟨stp, htmp_p, hokp, hmp⟩
    have heg_htag : (if emword >>> 28 = 3#32 then 0#32 else emword >>> 28) = htag' := by
      rw [← heg_eq]; exact hc
    obtain ⟨heg0, heg1, heg2⟩ := ev_egtype_cases heg_htag
    let P_match : Tup Val [.bool, i32] → Mem 64 → Prop := fun (matched, mlhs, ()) mm =>
      ∃ stm : FullState, stm.core.tmp = s0.core.tmp ∧
        EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat
          scr0 scr_in stm ∧
        (matched = true → mlhs.toNat < 2 * cv0 ∧
          LitEquiv (cnfOfClauses F_cur) lhs'.toNat mlhs.toNat) ∧
        (FullMem c stm ⋆ R) mm
    clear hc; ev_steps_ng
    refine wp_join_group P_match ?_ ?_
    · rintro _ ⟨matched, mlhs, ⟨⟩⟩ mm ⟨stm, htmp_m, hokm, heqv_m, hmm⟩
      ev_split
      rotate_left; · ev_steps; exact hJnxt (_, _, ()) mm ⟨stm, htmp_m, hokm, hmm⟩
      obtain ⟨hml_lt, hlhs_ent⟩ := heqv_m hc
      clear hc; ev_steps; c0_call hEquiv
      refine ⟨c, F0, F_cur, stm, R, rfl, hokm.1.1, hokm.1.2.1, hokm.1.2.2.1, hokm.1.2.2.2.1,
        hokm.1.2.2.2.2.1, hokm.1.2.2.2.2.2.1, hokm.1.2.2.2.2.2.2, hokm.2.1 ▸ hokm.2.2.2.2.2.1,
        hokm.2.1 ▸ hlhs'_lt, hokm.2.1 ▸ hml_lt, hlhs_ent, hmm,
        fun ef se me hlen' hw' hmk' hnd' hext' hcl' hdm' hcv' hfl' har' hal' _ hsb' hrepr' _
          hef2 hme => ?_⟩
      have hoke := evCoreOk_unit_equiv hokm hlen' hw' hmk' hnd' hext' hcl' hdm' hcv' hfl' har'
        hal' hsb' hrepr'
      ev_split
      · ev_steps; exact hQ2 se me hoke (hef2 hc) hme
      clear hc; ev_steps_ng
      refine wp_join_group (ts := [.bool])
        (fun (_, ()) mef => ∃ stef : FullState,
          EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off.toNat
            ht_sz.toNat scr0 scr_in stef ∧ (FullMem c stef ⋆ R) mef)
        (fun _ ⟨ch_ef, ⟨⟩⟩ mef ⟨stef, hokef, hmef⟩ => by
          ev_steps; exact hBp (ch_ef, false, slot, probes, seen_self, ()) mef
            ⟨stef, hokef, hmef⟩) ?_
      intro Jef hJef; ev_split
      rotate_left; · ev_steps; exact hJef (changed', ()) me ⟨se, hoke, hme⟩
      clear hc; ev_steps; c0_call hEnq
      refine ⟨c, se, g_len, ht_off.toNat, ht_sz.toNat, R, rfl, hoke.1.1,
        hoke.2.2.2.2.2.2.2.2.1, hme, fun sc1 m1 hl1 hq1 hc1 hla1 hm1 => ?_⟩
      let s1 : FullState := { se with scratch := { se.scratch with scratch_buf := sc1 } }
      have hk1 := evCoreOk_enq hg_ht hoke hl1 hq1 hc1 hla1
      ev_steps; c0_call hEnq
      refine ⟨c, s1, g_len, ht_off.toNat, ht_sz.toNat, R, rfl, hk1.1.1,
        hk1.2.2.2.2.2.2.2.2.1, hm1, fun sc2 m2 hl2 hq2 hc2 hla2 hm2 => ?_⟩
      let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := sc2 } }
      have hk2 := evCoreOk_enq hg_ht hk1 hl2 hq2 hc2 hla2
      ev_steps; c0_call hFind
      refine ⟨F_cur, 2 * cv0, s2.core.repr, ArrayField.repr.rest c s2 ⋆ R, hk2.2.2.2.2.2.1,
        hlhs'_lt, focus_full_repr hm2, fun _ r3 m3 hrl3 hrepr3 _ _ _ hm3 => ?_⟩
      let s3 : FullState := { s2 with core := { s2.core with repr := r3 } }
      have hm3' := unfocus_full_repr hm3
      have hk3 := evCoreOk_repr hk2 (hrl3.trans hk2.1.1.core_ok.repr_len) hrepr3
      ev_steps; c0_call hEnq
      refine ⟨c, s3, g_len, ht_off.toNat, ht_sz.toNat, R, rfl, hk3.1.1,
        hk3.2.2.2.2.2.2.2.2.1, hm3', fun sc4 m4 hl4 hq4 hc4 hla4 hm4 => ?_⟩
      let s4 : FullState := { s3 with scratch := { s3.scratch with scratch_buf := sc4 } }
      have hk4 := evCoreOk_enq hg_ht hk3 hl4 hq4 hc4 hla4
      ev_steps; c0_call hFind
      refine ⟨F_cur, 2 * cv0, s4.core.repr, ArrayField.repr.rest c s4 ⋆ R, hk4.2.2.2.2.2.1,
        hml_lt, focus_full_repr hm4, fun _ r5 m5 hrl5 hrepr5 _ _ _ hm5 => ?_⟩
      let s5 : FullState := { s4 with core := { s4.core with repr := r5 } }
      have hm5' := unfocus_full_repr hm5
      have hk5 := evCoreOk_repr hk4 (hrl5.trans hk4.1.1.core_ok.repr_len) hrepr5
      ev_steps; c0_call hEnq
      refine ⟨c, s5, g_len, ht_off.toNat, ht_sz.toNat, R, rfl, hk5.1.1,
        hk5.2.2.2.2.2.2.2.2.1, hm5', fun sc6 m6 hl6 hq6 hc6 hla6 hm6 => ?_⟩
      let s6 : FullState := { s5 with scratch := { s5.scratch with scratch_buf := sc6 } }
      have hk6 := evCoreOk_enq hg_ht hk5 hl6 hq6 hc6 hla6
      ev_steps; exact hJef (true, ()) m6 ⟨s6, hk6, hm6⟩
    · intro Jm hJm; ev_split
      · have htag0_eq : htag' = 0#32 := hc
        have hand_eq := hgat0 htag0_eq
        clear hc; ev_steps; c0_call hAndMatch
        refine ⟨maxA, c, F0, F_cur, stp, scr0, g_len, R, hmaxA, rfl, hokp.1.1, hokp.1.2.1,
          hokp.1.2.2.1, hokp.1.2.2.2.2.2.1, hokp.2.1 ▸ hrepr_p, by omega, hpref_p,
          hokp.2.1 ▸ hent_gate, by rw [he1, Option.getD_some]; exact heg0 htag0_eq,
          hokp.2.1 ▸ hhar_cv, hmp, ?_⟩
        intro ok_m repr_m lm_m mm; dsimp only
        intro hrl_m hlm_m hmk_m hrepr_m hok_and hmm
        let stm : FullState :=
          { stp with core := { stp.core with repr := repr_m, lit_mark := lm_m } }
        have hokm := evCoreOk_and_match hokp hrl_m hlm_m hmk_m (hokp.2.1 ▸ hrepr_m)
        ev_steps
        have hgoal := hJm (ok_m, elhs, ()) mm
          ⟨stm, htmp_p, hokm,
           fun hokt => ⟨helhs_lt,
             ev_match_and_equiv (htmp_p ▸ hand_eq) he0 (hok_and hokt).2.2⟩,
           hmm⟩
        rw [← hst_e0] at hgoal; exact hgoal
      clear hc; ev_steps_ng
      refine wp_join_group P_match
        (fun _ ⟨b, l, ⟨⟩⟩ mf h => by ev_steps; exact hJm (b, l, ()) mf h) ?_
      intro Jmb hJmb; ev_split
      · have htag1_eq : htag' = 1#32 := hc
        obtain ⟨_, hxor_s⟩ := hgat1 htag1_eq
        clear hc; ev_steps; c0_call hXorMatch
        refine ⟨maxA, c, F0, F_cur, stp, scr0, g_len, R, hmaxA, rfl, hokp.1.1, hokp.1.2.1,
          hokp.1.2.2.2.2.2.1, hokp.2.1 ▸ hrepr_p, by rw [hokp.2.1]; omega, by omega, hpref_p,
          hokp.2.1 ▸ hent_gate, by rw [he1, Option.getD_some]; exact heg1 htag1_eq,
          hokp.2.1 ▸ hhar_cv, fun k hk => by rw [htmp_p, hokp.2.1]; exact htmp_lt k hk,
          hmp, ?_⟩
        intro ml repr_m mclr_m mm; dsimp only
        intro hrl_m hmc_m hrepr_m hok_xor hmm
        let stm : FullState :=
          { stp with core := { stp.core with repr := repr_m, min_clr := mclr_m } }
        have hokm := evCoreOk_xor_match hokp hrl_m hmc_m (hokp.2.1 ▸ hrepr_m)
        ev_steps_ng
        refine wp_join_group P_match
          (fun _ ⟨b, l, ⟨⟩⟩ mf h => by ev_steps; exact hJmb (b, l, ()) mf h) ?_
        intro Jmx hJmx; ev_split
        · obtain ⟨_, _, hml_lt, hml_ev⟩ := hok_xor hc
          ev_steps; exact hJmx (true, ml, ()) mm
            ⟨stm, htmp_p, hokm, fun _ => ⟨hokp.2.1 ▸ hml_lt,
              ev_litEquiv_of_eval fun α hα => by
                rw [hxor_s α hα, hml_ev α hα, htmp_p]⟩, hmm⟩
        · ev_steps
          exact hJmx (false, _, ()) mm ⟨stm, htmp_p, hokm, (fun h => by cases h), hmm⟩
      clear hc; ev_steps_ng
      refine wp_join_group P_match
        (fun _ ⟨b, l, ⟨⟩⟩ mf h => by ev_steps; exact hJmb (b, l, ()) mf h) ?_
      intro Jm2 hJm2; ev_split
      rotate_left
      · ev_steps; exact hJm2 (false, _, ()) mp ⟨stp, htmp_p, hokp, (fun h => by cases h), hmp⟩
      have htag2_eq : htag' = 2#32 := hc; clear hc; ev_split
      rotate_left
      · ev_steps; exact hJm2 (false, _, ()) mp ⟨stp, htmp_p, hokp, (fun h => by cases h), hmp⟩
      obtain ⟨_, hite_s⟩ := hgat2 htag2_eq
      have hite_e := ev_gate_tag2_ite hent_gate he0 he1 (heg2 htag2_eq)
      obtain ⟨er0, her0_get, her0_lt⟩ := herhs 0 (by rw [hite_e.1]; decide)
      obtain ⟨er1, her1_get, her1_lt⟩ := herhs 1 (by rw [hite_e.1]; decide)
      obtain ⟨er2, her2_get, her2_lt⟩ := herhs 2 (by rw [hite_e.1]; decide)
      have he2_arr := ev_scr_ent_lt (scr := stp.scratch.scratch_buf) (g_len := g_len)
        (ent := ent) 2 (by rw [hite_e.1] at hbd_e; omega) (by omega) (by omega)
      have he3_arr := ev_scr_ent_lt (scr := stp.scratch.scratch_buf) (g_len := g_len)
        (ent := ent) 3 (by rw [hite_e.1] at hbd_e; omega) (by omega) (by omega)
      have he4_arr := ev_scr_ent_lt (scr := stp.scratch.scratch_buf) (g_len := g_len)
        (ent := ent) 4 (by rw [hite_e.1] at hbd_e; omega) (by omega) (by omega)
      have hst_e2 := ev_scr_ent_get (g_len := g_len) 2 (by rw [hite_e.1] at hbd_e; omega)
        (by omega) hpref_p her0_get he2_arr (by omega)
      have hst_e3 := ev_scr_ent_get (g_len := g_len) 3 (by rw [hite_e.1] at hbd_e; omega)
        (by omega) hpref_p her1_get he3_arr (by omega)
      have hst_e4 := ev_scr_ent_get (g_len := g_len) 4 (by rw [hite_e.1] at hbd_e; omega)
        (by omega) hpref_p her2_get he4_arr (by omega)
      clear hc; ev_steps; c0_call hFind
      refine ⟨F_cur, 2 * cv0, stp.core.repr, ArrayField.repr.rest c stp ⋆ R, hrepr_p,
        by change (stp.scratch.scratch_buf[(ent.setWidth 64 + 2#64).toNat]'he2_arr).toNat < 2 * cv0
           rw [hst_e2]; exact her0_lt, focus_full_repr hmp,
        fun ec repra ma hrla hrepra _ _ hec_eqv hma => ?_⟩
      let sa : FullState := { stp with core := { stp.core with repr := repra } }
      have hma' : (FullMem c sa ⋆ R) ma := unfocus_full_repr hma
      ev_steps; c0_call hFind
      refine ⟨F_cur, 2 * cv0, repra, ArrayField.repr.rest c sa ⋆ R, hrepra,
        by change (stp.scratch.scratch_buf[(ent.setWidth 64 + 3#64).toNat]'he3_arr).toNat < 2 * cv0
           rw [hst_e3]; exact her1_lt, focus_full_repr hma',
        fun et reprb mb hrlb hreprb _ _ het_eqv hmb => ?_⟩
      let sb : FullState := { sa with core := { sa.core with repr := reprb } }
      have hmb' : (FullMem c sb ⋆ R) mb := unfocus_full_repr hmb
      ev_steps; c0_call hFind
      refine ⟨F_cur, 2 * cv0, reprb, ArrayField.repr.rest c sb ⋆ R, hreprb,
        by change (stp.scratch.scratch_buf[(ent.setWidth 64 + 4#64).toNat]'he4_arr).toNat < 2 * cv0
           rw [hst_e4]; exact her2_lt, focus_full_repr hmb',
        fun ee reprc mc hrlc hreprc _ _ hee_eqv hmc => ?_⟩
      let stpc : FullState := { stp with core := { stp.core with repr := reprc } }
      have hmc' : (FullMem c stpc ⋆ R) mc := by
        simpa only [stpc, sb, sa] using unfocus_full_repr hmc
      have hokc := evCoreOk_repr hokp (hrlc.trans (hrlb.trans (hrla.trans hrl_p))) hreprc
      have hite_e' : IteGateDef (cnfOfClauses F_cur) elhs.toNat ec.toNat et.toNat ee.toNat :=
        ev_ite_eval_congr hite_e.2 (LitEquiv.refl _ _)
          (by rw [her0_get, Option.getD_some, ← hst_e2]; exact hec_eqv)
          (by rw [her1_get, Option.getD_some, ← hst_e3]; exact het_eqv)
          (by rw [her2_get, Option.getD_some, ← hst_e4]; exact hee_eqv)
      have h3 : 3 ≤ stpc.core.tmp.length := by
        change 3 ≤ stp.core.tmp.length; rw [htmp_p]; have := (hgat2 htag2_eq).1
        have : harity.toNat = 3 := by rw [this]; decide
        omega
      ev_steps_ng
      refine wp_join_group (ts := [i32, i32, i32])
        (fun (ec1, et1, ee1, ()) m1 => m1 = mc ∧
          IteGateDef (cnfOfClauses F_cur) elhs.toNat ec1.toNat et1.toNat ee1.toNat) ?_ ?_
      · rintro _ ⟨ec1, et1, ee1, ⟨⟩⟩ m1 ⟨hm1, hite_1⟩; subst m1; ev_steps_ng
        refine wp_join_group (ts := [i32, i32, i32])
          (fun (ml', et', ee', ()) m2 => m2 = mc ∧ ml'.toNat < 2 * cv0 ∧
            IteGateDef (cnfOfClauses F_cur) ml'.toNat ec1.toNat et'.toNat ee'.toNat) ?_ ?_
        · rintro _ ⟨ml', et', ee', ⟨⟩⟩ m2 ⟨hm2, hml'_lt, hite_f⟩; subst m2; ev_steps_ng
          refine wp_join_group (ts := [.bool])
            (fun (b, ()) mj => mj = mc ∧ (b = true → ml'.toNat < 2 * cv0 ∧
              LitEquiv (cnfOfClauses F_cur) lhs'.toNat ml'.toNat))
            (fun _ ⟨b, ⟨⟩⟩ mj ⟨hmj, hm⟩ => by
              subst mj; ev_steps; exact hJm2 (b, ml', ()) mc ⟨stpc, htmp_p, hokc, hm, hmc'⟩) ?_
          intro Jmi hJmi
          have ht0_a : 0 < stpc.core.tmp.length := by omega
          have ht1_a : 1 < stpc.core.tmp.length := by omega
          have ht2_a : 2 < stpc.core.tmp.length := by omega
          ev_split
          rotate_left; · ev_steps; exact hJmi (false, ()) mc ⟨rfl, fun h => by cases h⟩
          have hc0 : ec1 = s0.core.tmp[0]'(by rw [← htmp_p]; exact ht0_a) := by
            simpa [stpc, htmp_p] using hc
          clear hc; ev_split
          rotate_left; · ev_steps; exact hJmi (false, ()) mc ⟨rfl, fun h => by cases h⟩
          have hc1 : et' = s0.core.tmp[1]'(by rw [← htmp_p]; exact ht1_a) := by
            simpa [stpc, htmp_p] using hc
          clear hc; ev_split
          rotate_left; · ev_steps; exact hJmi (false, ()) mc ⟨rfl, fun h => by cases h⟩
          have hc2 : ee' = s0.core.tmp[2]'(by rw [← htmp_p]; exact ht2_a) := by
            simpa [stpc, htmp_p] using hc
          ev_steps; exact hJmi (true, ()) mc ⟨rfl, fun _ =>
            ⟨hml'_lt, ev_hash_ite_equiv (by rw [← htmp_p]; exact h3) hite_s hite_f hc0 hc1
              hc2⟩⟩
        · intro Jf hJf; ev_split
          · ev_steps
            have hfl : IteGateDef (cnfOfClauses F_cur) (elhs ^^^ 1#32).toNat (ec1).toNat
                (et1 ^^^ 1#32).toNat (ee1 ^^^ 1#32).toNat := by
              rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg]
              exact ev_iteGateDef_flip_out hite_1
            have hgoal := hJf (elhs ^^^ 1#32, et1 ^^^ 1#32, ee1 ^^^ 1#32, ()) mc
              ⟨rfl, ev_bv32_xor1_lt_cv helhs_lt, hfl⟩
            rw [← hst_e0] at hgoal; exact hgoal
          · ev_steps
            have hgoal := hJf (elhs, et1, ee1, ()) mc ⟨rfl, helhs_lt, hite_1⟩
            rw [← hst_e0] at hgoal; exact hgoal
      · intro Jc1 hJc1; ev_split
        · ev_steps; refine hJc1 (ec ^^^ 1#32, ee, et, ()) mc ⟨rfl, ?_⟩
          rw [bv32_xor1_eq_litNeg]; exact ev_iteGateDef_flip_cond hite_e'
        · ev_steps; exact hJc1 (ec, et, ee, ()) mc ⟨rfl, hite_e'⟩
  · intro _ _ _ hLp; ev_steps
    exact hLp 128 (_ &&& (ht_sz - 1#64), 0#64, false, ()) m0
      ⟨s0, ev_ht_slot_lt hht_pos, by decide, rfl, rfl, hok0, hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
