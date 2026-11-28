/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGate0
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGateHash
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGateTag0
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGateTag1
import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGateTag2

/-!
# Congruence Gate Re-Evaluation & Hash-Consing WP Proof (`full_cong_eval_gate`)

Top-level canonical `Func.wp` proof for `full_cong_eval_gate` (`Spec.fullCongEvalGateSpec`),
combining `ev_tag0_wp`, `ev_tag1_wp`, `ev_tag2_wp`, `ev_hash_wp`, and `ev_trail_wp`.
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

local macro "ev_u" : tactic =>
  `(tactic| try dsimp only [evL2, evCmp32, evCmp64, evLd32, evLdK32, evLd8, evSgn0])

local macro "ev_steps" : tactic =>
  `(tactic| (ev_u; c0_hsteps!))

local macro "ev_steps_ng" : tactic =>
  `(tactic| (ev_u; c0_hsteps_nogrp))

local macro "ev_split" : tactic =>
  `(tactic| (ev_u; c0_hsplit))

private theorem ev_scr_g_lt {scr : List (BitVec 32)} {g_len : Nat} {g : BitVec 64}
    (k : Nat) (hk : g.toNat + k < g_len) (hg : g_len ≤ scr.length) (hcap : scr.length < 2 ^ 32) :
    (g + BitVec.ofNat 64 k).toNat < scr.length := by
  have h1 : (g + BitVec.ofNat 64 k).toNat = g.toNat + k := by
    rw [BitVec.toNat_add, bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem ev_scr_g_get {scr scr0 : List (BitVec 32)} {g_len : Nat} {g : BitVec 64}
    {v : BitVec 32} (k : Nat) (hk : g.toNat + k < g_len) (hg : g_len ≤ scr.length)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hget : scr0[g.toNat + k]? = some v)
    (harr : (g + BitVec.ofNat 64 k).toNat < scr.length) (hcap : scr.length < 2 ^ 32) :
    scr[(g + BitVec.ofNat 64 k).toNat]'harr = v := by
  have h1 : (g + BitVec.ofNat 64 k).toNat = g.toNat + k := by
    rw [BitVec.toNat_add, bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have h := (hpref (g.toNat + k) hk).trans hget
  rw [← h1, List.getElem?_eq_getElem harr] at h
  exact Option.some.inj h

private theorem ev_scr_g2i_lt {scr : List (BitVec 32)} {g_len : Nat} {g : BitVec 64}
    {i : BitVec 32} (hi : g.toNat + 2 + i.toNat < g_len) (hg : g_len ≤ scr.length)
    (hcap : scr.length < 2 ^ 32) :
    (g + 2#64 + i.setWidth 64).toNat < scr.length := by
  have h1 : (g + 2#64).toNat = g.toNat + 2 := by
    rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  have h2 : (g + 2#64 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat := by
    rw [BitVec.toNat_add, h1, bv_zext32_toNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem ev_scr_g2i_get {scr scr0 : List (BitVec 32)} {g_len : Nat} {g : BitVec 64}
    {i v : BitVec 32} (hi : g.toNat + 2 + i.toNat < g_len) (hg : g_len ≤ scr.length)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hget : scr0[g.toNat + 2 + i.toNat]? = some v)
    (harr : (g + 2#64 + i.setWidth 64).toNat < scr.length) (hcap : scr.length < 2 ^ 32) :
    scr[(g + 2#64 + i.setWidth 64).toNat]'harr = v := by
  have h1 : (g + 2#64).toNat = g.toNat + 2 := by
    rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  have h2 : (g + 2#64 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat := by
    rw [BitVec.toNat_add, h1, bv_zext32_toNat, Nat.mod_eq_of_lt (by omega)]
  have h := (hpref (g.toNat + 2 + i.toNat) hi).trans hget
  rw [← h2, List.getElem?_eq_getElem harr] at h
  exact Option.some.inj h

private theorem ev_gate_decode {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g : Nat}
    {scr0 : List (BitVec 32)} {lhs0 mword : BitVec 32}
    (hg : CongGateAt maxA F_cur cv scr0 g_len g)
    (h0 : scr0[g]? = some lhs0) (h1 : scr0[g + 1]? = some mword) :
    let arity := if mword >>> 28 = 3#32 then mword &&& 0x0FFFFFFF#32 else mword &&& 0xFF#32
    let gtype := if mword >>> 28 = 3#32 then 0#32 else mword >>> 28
    arity.toNat = congGateArity mword ∧
    2 ≤ arity.toNat ∧
    (gtype = 0#32 → AndGateDef (cnfOfClauses F_cur) lhs0.toNat
      (((scr0.drop (g + 2)).take arity.toNat).map BitVec.toNat)) ∧
    (gtype = 1#32 → 2 ≤ arity.toNat → arity.toNat ≤ 4 →
      XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
        (((scr0.drop (g + 2)).take arity.toNat).map BitVec.toNat)) ∧
    (gtype = 2#32 → arity = 3#32 →
      IteGateDef (cnfOfClauses F_cur) lhs0.toNat
        (scr0[g + 2]?.getD 0#32).toNat (scr0[g + 3]?.getD 0#32).toNat
        (scr0[g + 4]?.getD 0#32).toNat) := by
  obtain ⟨l', m', hl', hm', _, _, _, _, _, hsem⟩ := hg
  rcases Option.some.inj (hl'.symm.trans h0) with rfl
  rcases Option.some.inj (hm'.symm.trans h1) with rfl
  have har : (if m' >>> 28 = 3#32 then m' &&& 0x0FFFFFFF#32 else m' &&& 0xFF#32).toNat =
      congGateArity m' := by unfold congGateArity; split <;> rfl
  have hge2 : 2 ≤ congGateArity m' := by
    rcases hsem with ⟨⟨_, h2, _⟩ | ⟨_, h65⟩, _⟩ | ⟨_, h2, _, _⟩ | ⟨_, h3, _⟩ <;> omega
  refine ⟨har, har ▸ hge2, ?_, ?_, ?_⟩
  · intro hg0; rw [har]
    rcases hsem with ⟨_, hand⟩ | ⟨h1', _, _, _⟩ | ⟨h2', _, _⟩
    · exact hand
    · have hne : m' >>> 28 ≠ 3#32 := fun h => by rw [h] at h1'; cases h1'
      rw [ite_eq_right hne] at hg0; rw [hg0] at h1'; cases h1'
    · have hne : m' >>> 28 ≠ 3#32 := fun h => by rw [h] at h2'; cases h2'
      rw [ite_eq_right hne] at hg0; rw [hg0] at h2'; cases h2'
  · intro hg1 _ _; rw [har]
    rcases hsem with ⟨⟨h0', _⟩ | ⟨h3', _⟩, _⟩ | ⟨_, _, _, hxor⟩ | ⟨h2', _, _⟩
    · have hne : m' >>> 28 ≠ 3#32 := fun h => by rw [h] at h0'; cases h0'
      rw [ite_eq_right hne] at hg1; rw [hg1] at h0'; cases h0'
    · have h3 : m' >>> 28 = 3#32 := BitVec.eq_of_toNat_eq h3'
      rw [ite_eq_left h3] at hg1; cases hg1
    · exact hxor
    · have hne : m' >>> 28 ≠ 3#32 := fun h => by rw [h] at h2'; cases h2'
      rw [ite_eq_right hne] at hg1; rw [hg1] at h2'; cases h2'
  · intro hg2 _
    rcases hsem with ⟨⟨h0', _⟩ | ⟨h3', _⟩, _⟩ | ⟨h1', _, _, _⟩ | ⟨_, _, hite⟩
    · have hne : m' >>> 28 ≠ 3#32 := fun h => by rw [h] at h0'; cases h0'
      rw [ite_eq_right hne] at hg2; rw [hg2] at h0'; cases h0'
    · have h3 : m' >>> 28 = 3#32 := BitVec.eq_of_toNat_eq h3'
      rw [ite_eq_left h3] at hg2; cases hg2
    · have hne : m' >>> 28 ≠ 3#32 := fun h => by rw [h] at h1'; cases h1'
      rw [ite_eq_right hne] at hg2; rw [hg2] at h1'; cases h1'
    · exact hite

private theorem ev_trail_wp_any (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64} {ctrl64 te0 : BitVec 64}
    {chg keep : Bool} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (hctrl : ctrl64.toNat = ctrl_off)
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s0)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ : ∀ (r : BitVec 64) s' m',
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in s' →
      ((r &&& 2#64) = 0#64 → True) → ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (evTrailExpr c.hdr ctrl64 c.pRepr c.pTrail te0 chg keep) m0 := by
  by_cases hle : te0.toNat ≤ s0.core.trail_end
  · exact ev_trail_wp Γ hFind hEnq hg_ht hctrl hok0 hle hm0
      fun r s' m' hok _ huns hm' => hQ r s' m' hok (fun _ => trivial) huns hm'
  · unfold evTrailExpr; ev_steps_ng
    refine wp_loop_inv (ts := [i64])
      (fun (te, ()) m => m = m0 ∧ ¬ te.toNat < s0.core.trail_end)
      (fun _ _ => 0)
      (fun _ hJ => by ev_steps; exact hJ (te0, ()) m0 ⟨rfl, by omega⟩)
      (fun _ ⟨te, ⟨⟩⟩ m ⟨hm_eq, hnot⟩ _ => ?_)
    subst m; ev_split
    · have htr_lt : te.toNat < s0.core.trail_end := by
        have hlt : te.toNat < (BitVec.ofNat 64 s0.core.trail_end).toNat := hc
        have hbd := c.hmaxv; unfold dimacsBound at hbd
        have hte_bd : s0.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hok0.1.1.core_ok.trail_end_le hok0.1.1.core_ok.cur_vars_le
        rw [bv64_ofNat_toNat_lt (by omega)] at hlt; exact hlt
      exact absurd htr_lt hnot
    · clear hc; ev_split
      · have huns : F0.Unsat := unsat_of_inconsistent_w hok0.1.2.1 (by simpa using hc)
        ev_steps; exact hQ 2#64 s0 m0 hok0 (fun _ => trivial) (fun _ => huns) hm0
      · clear hc; ev_steps_ng
        refine wp_join_group (ts := [i64]) (fun (b1, ()) mc =>
          b1 = (if chg then 1#64 else 0#64) ∧ mc = m0) ?_ ?_
        · rintro _ ⟨b1, ⟨⟩⟩ mc ⟨rfl, hmc⟩; subst mc; ev_steps_ng
          refine wp_join_group (ts := [i64]) (fun (b4, ()) md =>
            b4 = (if keep then 4#64 else 0#64) ∧ md = m0) ?_ ?_
          · rintro _ ⟨b4, ⟨⟩⟩ md ⟨rfl, hmd⟩; subst md; ev_steps
            have h0 : (((if chg then 1#64 else 0#64) ||| (if keep then 4#64 else 0#64)) &&& 2#64) =
                0#64 := by cases chg <;> cases keep <;> decide
            exact hQ _ s0 m0 hok0 (fun _ => trivial) (fun h => absurd h0 h) hm0
          · intro J4 hJ4; cases keep <;> ev_steps <;>
              first | exact hJ4 (_, ()) m0 ⟨rfl, rfl⟩ | cases hc
        · intro J1 hJ1; cases chg <;> ev_steps <;>
            first | exact hJ1 (_, ()) m0 ⟨rfl, rfl⟩ | cases hc

public section

/-- Canonical WP proof for `full_cong_eval_gate` (`Spec.fullCongEvalGateSpec`). -/
theorem full_cong_eval_gate_wp (Γ : Env)
    (hSort : Γ.Has "full_sort_u32" fullSortU32Spec)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hUnit : Γ.Has "full_cong_unit_fold" Spec.fullCongUnitFoldSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hAndMatch : Γ.Has "full_cong_and_match" Spec.fullCongAndMatchSpec)
    (hXorMatch : Γ.Has "full_cong_xor_match" Spec.fullCongXorMatchSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec) :
    ∀ args m Q X, Spec.fullCongEvalGateSpec args m Q X →
      Func.wp Γ full_cong_eval_gate_body args m Q X := by
  rintro ⟨h, g, ht_off, ht_sz, next_ep, ctrl_off, ⟨⟩⟩ m Q X
    ⟨maxA, c, F0, F_cur, s, scr0, g_len, R, hmaxA, rfl, hd0, hrepr0, hht_pos, hht_bd, hg_lt,
     hg_ht, hht_le, hpref0, hgat0, hht0, hqctx0, hm, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hscrl0 := hd0.1.scratch_ok.scratch_buf_len
  have hcv_le0 : s.core.cur_vars ≤ c.max_vars := hd0.1.core_ok.cur_vars_le
  have ⟨raw_lhs, mword, hg0, hg1, hraw_lt, hbd_g, har_cv0, har_max0, hrhs_g, _⟩ := hgat0
  have hg0_arr : g.toNat < s.scratch.scratch_buf.length := by omega
  have hg1_arr : (g + 1#64).toNat < s.scratch.scratch_buf.length :=
    ev_scr_g_lt (g_len := g_len) 1 (by omega) (by omega) (by omega)
  have hst_g0 : s.scratch.scratch_buf[g.toNat]'hg0_arr = raw_lhs := by
    have h := (hpref0 g.toNat hg_lt).trans hg0
    rw [List.getElem?_eq_getElem hg0_arr] at h; exact Option.some.inj h
  have hst_g1 : s.scratch.scratch_buf[(g + 1#64).toNat]'hg1_arr = mword :=
    ev_scr_g_get (g_len := g_len) 1 (by omega) (by omega) hpref0 hg1 hg1_arr (by omega)
  have hok_init : EvCoreOk maxA c F0 F_cur s.core.cur_vars s.core.fuel s.core.arena
      s.core.arena_len g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat scr0
      s.scratch.scratch_buf s :=
    ⟨hd0, rfl, rfl, rfl, rfl, hrepr0, hpref0, hht0, hqctx0,
      fun _ _ _ => ⟨fun _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩⟩
  have hQ_all : ∀ r s' m',
      EvCoreOk maxA c F0 F_cur s.core.cur_vars s.core.fuel s.core.arena s.core.arena_len g_len
        ctrl_off.toNat ht_off.toNat ht_sz.toNat scr0 s.scratch.scratch_buf s' →
      ((r &&& 2#64) = 0#64 → True) → ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m' := fun r s' m' hok _ huns hm' =>
    hQ r s' m' hok.1 hok.2.1 hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1
      (hok.2.1.symm ▸ hok.2.2.2.2.2.1) hok.2.2.2.2.2.2.1
      (hok.2.1.symm ▸ hok.2.2.2.2.2.2.2.1) hok.2.2.2.2.2.2.2.2.1
      (fun _ => hok.2.2.2.2.2.2.2.2.2) huns hm'
  have hQ2 : ∀ s' m',
      EvCoreOk maxA c F0 F_cur s.core.cur_vars s.core.fuel s.core.arena s.core.arena_len g_len
        ctrl_off.toNat ht_off.toNat ht_sz.toNat scr0 s.scratch.scratch_buf s' →
      F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m' := fun s' m' hok huns hm' =>
    hQ_all 2#64 s' m' hok (fun _ => trivial) (fun _ => huns) hm'
  have hQ0 : Q (0#64, ()) m :=
    hQ_all 0#64 s m hok_init (fun _ => trivial) (fun h => absurd rfl h) hm
  unfold Func.wp full_cong_eval_gate_body; dsimp only; ev_steps_ng
  refine wp_join_group (ts := [i32])
    (fun (arity, ()) ma => ma = m ∧
      arity = if mword >>> 28 = 3#32 then mword &&& 0x0FFFFFFF#32 else mword &&& 0xFF#32) ?_
    (fun Ja hJa => by
      ev_split
      · have h3 : mword >>> 28 = 3#32 := by rw [← hst_g1]; exact hc
        ev_steps
        have hgoal := hJa (mword &&& 0x0FFFFFFF#32, ()) m ⟨rfl, by simp [h3]⟩
        rw [← hst_g1] at hgoal; exact hgoal
      · have hn3 : mword >>> 28 ≠ 3#32 := by rw [← hst_g1]; exact hc
        ev_steps
        have hgoal := hJa (mword &&& 0xFF#32, ()) m ⟨rfl, by simp [hn3]⟩
        rw [← hst_g1] at hgoal; exact hgoal)
  rintro _ ⟨arity, ⟨⟩⟩ ma ⟨hma, har_eq⟩; subst ma; ev_steps_ng
  refine wp_join_group (ts := [i32])
    (fun (gtype, ()) mg => mg = m ∧
      gtype = if mword >>> 28 = 3#32 then 0#32 else mword >>> 28) ?_
    (fun Jg hJg => by
      ev_split
      · have h3 : mword >>> 28 = 3#32 := by rw [← hst_g1]; exact hc
        ev_steps; exact hJg (0#32, ()) m ⟨rfl, by simp [h3]⟩
      · have hn3 : mword >>> 28 ≠ 3#32 := by rw [← hst_g1]; exact hc
        ev_steps
        have hgoal := hJg (mword >>> 28, ()) m ⟨rfl, by simp [hn3]⟩
        rw [← hst_g1] at hgoal; exact hgoal)
  rintro _ ⟨gtype, ⟨⟩⟩ mg ⟨hmg, hgt_eq⟩; subst mg
  obtain ⟨har_n, har_ge2, hand_g, hxor_g, hite_g⟩ := ev_gate_decode hgat0 hg0 hg1
  rw [← har_eq] at har_n har_ge2 hand_g hxor_g hite_g
  rw [← hgt_eq] at hand_g hxor_g hite_g
  have hscr_ge : g.toNat + 2 + arity.toNat ≤ scr0.length := by
    obtain ⟨r, hr, _⟩ := hrhs_g (arity.toNat - 1) (by omega)
    have hlt := (List.getElem?_eq_some_iff.mp hr).1; omega
  ev_split; · ev_steps; exact hQ0
  clear hc; ev_split; · ev_steps; exact hQ0
  clear hc; ev_split; · ev_steps; exact hQ0
  clear hc; ev_steps; c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, ArrayField.repr.rest c s ⋆ R, hrepr0,
    by rw [hst_g0]; exact hraw_lt, focus_full_repr hm,
    fun lhs repr1 m1 hrl1 hrepr1 _ hlhs_lt hlhs_eqv hm1 => ?_⟩
  let s1 : FullState := { s with core := { s.core with repr := repr1 } }
  have hm1' : (FullMem c s1 ⋆ R) m1 := unfocus_full_repr hm1
  have hok1 := evCoreOk_repr hok_init (hrl1.trans hd0.1.core_ok.repr_len) hrepr1
  have hlhs_eqv' : LitEquiv (cnfOfClauses F_cur) raw_lhs.toNat lhs.toNat := by
    rw [← hst_g0]; exact hlhs_eqv
  ev_steps_ng
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) mi => ∃ si : FullState, i.toNat ≤ arity.toNat ∧
      EvCoreOk maxA c F0 F_cur s.core.cur_vars s.core.fuel s.core.arena s.core.arena_len g_len
        ctrl_off.toNat ht_off.toNat ht_sz.toNat scr0 s.scratch.scratch_buf si ∧
      (∀ k < i.toNat, (si.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
        LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k]?.getD 0#32).toNat
          (si.core.tmp[k]?.getD 0#32).toNat) ∧
      (FullMem c si ⋆ R) mi)
    (fun (i, ()) _ => arity.toNat - i.toNat)
    (fun _ hJi => by
      ev_steps; exact hJi (0#32, ()) m1 ⟨s1, Nat.zero_le _, hok1,
        fun _ h => absurd h (Nat.not_lt_zero _), hm1'⟩)
    (fun _ ⟨i, ⟨⟩⟩ mi ⟨si, hi_le, hoki, htmp_i, hmi⟩ ihi => ?_)
  ev_split
  · have hi_lt : i.toNat < arity.toNat := by omega
    have hgi_arr : (g + 2#64 + i.setWidth 64).toNat < si.scratch.scratch_buf.length :=
      ev_scr_g2i_lt (g_len := g_len) (by omega)
        (by rw [hoki.1.1.scratch_ok.scratch_buf_len]; omega)
        (by rw [hoki.1.1.scratch_ok.scratch_buf_len]; omega)
    obtain ⟨rk, hrk_get, hrk_lt⟩ := hrhs_g i.toNat (by omega)
    have hst_gi : si.scratch.scratch_buf[(g + 2#64 + i.setWidth 64).toNat]'hgi_arr = rk :=
      ev_scr_g2i_get (g_len := g_len) (by omega)
        (by rw [hoki.1.1.scratch_ok.scratch_buf_len]; omega) hoki.2.2.2.2.2.2.1 hrk_get hgi_arr
        (by rw [hoki.1.1.scratch_ok.scratch_buf_len]; omega)
    have hi_tmp : (i.setWidth 64).toNat < si.core.tmp.length := by
      rw [bv_zext32_toNat, hoki.1.1.core_ok.tmp_len_arr]; omega
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_lt_of (by omega)
    clear hc; ev_steps; c0_call hFind
    refine ⟨F_cur, 2 * s.core.cur_vars, si.core.repr, ArrayField.repr.rest c si ⋆ R,
      hoki.2.2.2.2.2.1,
      by change (si.scratch.scratch_buf[(g + 2#64 + i.setWidth 64).toNat]'hgi_arr).toNat <
           2 * s.core.cur_vars
         rw [hst_gi]; exact hrk_lt, focus_full_repr hmi,
      fun rj reprj mj hrlj hreprj _ hrj_lt hrj_eqv hmj => ?_⟩
    let sj : FullState := { si with core := { si.core with repr := reprj } }
    have hmj' : (FullMem c sj ⋆ R) mj := unfocus_full_repr hmj
    have hi_tmp_j : (i.setWidth 64).toNat < sj.core.tmp.length := hi_tmp
    have hokj := evCoreOk_repr hoki (hrlj.trans hoki.1.1.core_ok.repr_len) hreprj
    ev_steps
    let sk : FullState :=
      { sj with core := { sj.core with tmp := sj.core.tmp.set i.toNat rj } }
    have hokk := evCoreOk_tmp hokj (by
      change (sj.core.tmp.set i.toNat rj).length = c.max_vars
      rw [List.length_set]; exact hokj.1.1.core_ok.tmp_len_arr)
    have hmk : (FullMem c sk ⋆ R) m := by
      dsimp only [sk, sj] at *; rw [bv_zext32_toNat] at hm; exact hm
    refine ihi (i + 1#32, ()) m (by dsimp only; omega) ⟨sk, by omega, hokk, fun k hk => ?_, hmk⟩
    rw [hi1] at hk
    by_cases hki : k = i.toNat
    · subst hki
      have ht_set : sk.core.tmp[i.toNat]?.getD 0#32 = rj := by
        change (si.core.tmp.set i.toNat rj)[i.toNat]?.getD 0#32 = rj
        rw [List.getElem?_set_self (by rw [hoki.1.1.core_ok.tmp_len_arr]; omega), Option.getD_some]
      rw [ht_set, hrk_get, Option.getD_some]
      exact ⟨hrj_lt, by
        change LitEquiv (cnfOfClauses F_cur) rk.toNat rj.toNat
        rw [← hst_gi]; exact hrj_eqv⟩
    · have ht_ne : sk.core.tmp[k]? = si.core.tmp[k]? := by
        change (si.core.tmp.set i.toNat rj)[k]? = si.core.tmp[k]?
        exact List.getElem?_set_ne (Ne.symm hki)
      rw [ht_ne]; exact htmp_i k (by omega)
  have hi_eq : i.toNat = arity.toNat := by omega
  rw [hi_eq] at htmp_i
  clear hc; ev_steps_ng
  let P_post : Tup Val [i32, i32, i32, i32, .bool, .bool] → Mem 64 → Prop :=
    fun (lhs', _iw, htag', har', nh', _ch', ()) mp => ∃ stp : FullState,
      EvCoreOk maxA c F0 F_cur s.core.cur_vars s.core.fuel s.core.arena s.core.arena_len g_len
        ctrl_off.toNat ht_off.toNat ht_sz.toNat scr0 s.scratch.scratch_buf stp ∧
      (nh' = true → EvHashGateOk maxA F_cur s.core.cur_vars gtype htag' har' lhs' stp.core.tmp) ∧
      (FullMem c stp ⋆ R) mp
  refine wp_join_group P_post ?_ ?_
  · rintro _ ⟨lhs', iw, htag', har', nh', ch', ⟨⟩⟩ mp ⟨stp, hokp, hgatep, hmp⟩
    ev_steps_ng
    refine wp_join_group (ts := [i32, .bool, .bool])
      (fun (_, _, _, ()) mt => ∃ stt : FullState,
        EvCoreOk maxA c F0 F_cur s.core.cur_vars s.core.fuel s.core.arena s.core.arena_len g_len
          ctrl_off.toNat ht_off.toNat ht_sz.toNat scr0 s.scratch.scratch_buf stt ∧
        (FullMem c stt ⋆ R) mt)
      (fun _ ⟨_, ch_t, keep_t, ⟨⟩⟩ mt ⟨stt, hokt, hmt⟩ =>
        ev_trail_wp_any Γ hFind hEnq hg_ht rfl hokt hmt hQ_all) ?_
    intro Jtrail hJtrail
    exact ev_hash_wp Γ hFind hEquiv hAndMatch hXorMatch hEnq hmaxA hht_pos hg_lt hg_ht hht_le
      hgat0 hokp hgatep hmp hQ2 fun iw_o ch_o keep_o s' m' hok' hm' =>
        hJtrail (iw_o, ch_o, keep_o, ()) m' ⟨s', hok', hm'⟩
  · intro Jpost hJpost; ev_split
    · exact ev_tag0_wp Γ hSort hUnit hEquiv hEnq hg_ht hc (by omega) (by omega)
        hscr_ge hlhs_lt hlhs_eqv' (hand_g hc) htmp_i hoki hmi hQ2
        fun iw_o har' nh' ch' s' m' hok' hgp' hm' =>
          hJpost (lhs, iw_o, gtype, har', nh', ch', ()) m' ⟨s', hok', hgp', hm'⟩
    · clear hc; ev_steps_ng
      refine wp_join_group P_post
        (fun _ ⟨l', iw', ht', ha', nh', ch', ⟨⟩⟩ mj h => by
          ev_steps; exact hJpost (l', iw', ht', ha', nh', ch', ()) mj h) ?_
      intro J39 hJ39; ev_steps_ng
      refine wp_join_group (ts := []) (fun () m2 => m2 = mi)
        (fun _ ⟨⟩ m2 hm2 => by
          subst m2; ev_steps_ng
          exact ev_tag2_wp Γ hUnit hEquiv hEnq hg_ht (by omega) (by omega) hlhs_lt hlhs_eqv'
            hite_g htmp_i hoki hmi hQ2 fun lhs' htag' har' nh' ch' s' m' hok' hgp' hm' =>
              hJ39 (lhs', i, htag', har', nh', ch', ()) m' ⟨s', hok', hgp', hm'⟩)
        (fun J40 hJ40 =>
          ev_tag1_wp Γ hSort hUnit hEquiv hEnq hg_ht (by omega) (by omega) hscr_ge hlhs_lt
            hlhs_eqv' hxor_g htmp_i hoki hmi hQ2
            (fun lhs' iw' har' nh' ch' s' m' hok' hgp' hm' =>
              hJ39 (lhs', iw', gtype, har', nh', ch', ()) m' ⟨s', hok', hgp', hm'⟩)
            (fun _ => hJ40 () mi rfl))

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
