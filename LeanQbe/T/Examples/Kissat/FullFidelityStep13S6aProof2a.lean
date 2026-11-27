/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BBveFwd
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas3
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard `S6a` — BVE Weaken & Heap-Push Lifts (`Proof2a`)

100% callee-parametric `(Γ : Env)` Step-13 `Func.wp` lift theorems (`0` cross-shard `S0..S5`
imports, `0` `@[expose]` on theorems/lemmas, `0` `import all`, `<= 100` cols, `<= std3`):
1. `full_bve_weaken_step13_wp` (`Full.full_bve_weaken_body` over `step13DeleteBinarySpec` ->
   `FullFastBveBudgets.fullBveWeakenTmkSpec`)
2. `full_bve_weaken_unit_fid_step13_wp` (`FullFidelityStep12B.full_bve_weaken_unit_fid_body` over
   `step13DeleteBinarySpec` -> `FullFastBveBudgets.fullBveWeakenTmkSpec`)
3. `full_bve_heap_push_m7_step13_wp` (`FullM7BveGates.full_bve_heap_push_m7_body` over
   `step13BveVarKeySpec` -> `step13BveHeapPushSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullFidelityStep12B
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullBveBvaTactics

local macro "s6a_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Shared `FullDenseInvW` & `TmkZero` Helpers -/

private theorem s6a_denseInvW_of_bve {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullBveBvaSpecs.FullDenseInvW c F0 F_cur s) :
    Full.FullDenseInvW c F0 F_cur s :=
  h

private theorem s6a_denseInvW_to_bve {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : Full.FullDenseInvW c F0 F_cur s) :
    FullBveBvaSpecs.FullDenseInvW c F0 F_cur s :=
  h

private theorem s6a_denseInvW_of_delete_binary13 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : Full.FullDenseInvW c F0 F_cur s)
    {flags' wvec' wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hlen' : ({ s with core := { s.core with
      flags := flags', wvec := wvec', wstk := wstk',
      wusable := wu', num_binary := nb' } } : FullState).LengthsOk c)
    (hwat : ∀ F, ModeWatchesInv F s.core →
      ModeWatchesInv F { s.core with
        flags := flags', wvec := wvec', wstk := wstk',
        wusable := wu', num_binary := nb' }) :
    Full.FullDenseInvW c F0 F_cur
      { s with core := { s.core with
        flags := flags', wvec := wvec', wstk := wstk',
        wusable := wu', num_binary := nb' } } := by
  have hfl := m6_fullDenseInvW_with_flags h hlen'.core_ok.flags_len
  exact s6a_denseInvW_of_bve
    (FullBveBvaHelpers.fullDenseInvW_of_delete_binary (s6a_denseInvW_to_bve hfl) hlen'
      fun F hF => hwat F (hF.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr))

private theorem s6a_fullDenseInvW_push_ext1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {ext' : List (BitVec 32)} {el' : Nat}
    (hext : ext'.length = c.extend_cap) (hel : el' ≤ c.extend_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with extend_stk := ext', extend_len := el' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with extend_stk_len := hext }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, ⟨h.2.2.2.2.1.1, hel⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem s6a_weakItem_bin_lt {k : FullCoreState} {w : BitVec 32} {m : Nat}
    (hitem : Full.FullBveWeakItemOk k w) (hbin : (w &&& 0x80000000#32) ≠ 0#32)
    (hcv : k.cur_vars ≤ m) : (w &&& 0x7FFFFFFF#32).toNat < 2 * m := by
  unfold Full.FullBveWeakItemOk at hitem
  rw [ite_eq_left hbin] at hitem
  omega

/-! ## 2. `full_bve_weaken_step13_wp` (`full_bve_weaken`) -/

/-- Step-13 lift for `full_bve_weaken` over `step13DeleteBinarySpec`. -/
public theorem full_bve_weaken_step13_wp (Γ : Env)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2TmkSpec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, step13DeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClTmkSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveWeakenTmkSpec args m Q X →
      Func.wp Γ Full.full_bve_weaken_body args m Q X := by
  rintro ⟨h, blk_lit, off, cnt, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, htmk0, hblk, hoff, hitems, hm, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmv hsc harc
  unfold Func.wp Full.full_bve_weaken_body
  bve_steps!
  refine wp_loop_inv (ts := [i32])
    (fun (i, _) mi =>
      i.toNat ≤ cnt.toNat ∧
      ∃ si, Full.FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
        si.core.cur_vars = s.core.cur_vars ∧ si.core.fuel = s.core.fuel ∧
        si.scratch.scratch_buf = s.scratch.scratch_buf ∧
        fullArenaClauseRefs si = fullArenaClauseRefs s ∧
        (FullMem c si ⋆ R) mi)
    (fun (i, _) _ => cnt.toNat - i.toNat)
    ?_ ?_
  · intro J hJ; bve_steps!
    exact hJ (0#32, PUnit.unit) m ⟨Nat.zero_le _, s, hdw, htmk0, rfl, rfl, rfl, rfl, hm⟩
  · rintro J ⟨i, ⟨⟩⟩ mi ⟨hi_le, si, hdw_i, htmk_i, hcv_eq, hfuel_eq, hscr_eq, hrefs_eq, hm_i⟩ ih
    have hcl_i := hdw_i.1.core_ok; have hsl_i := hdw_i.1.scratch_ok
    have hscrl_i : si.scratch.scratch_buf.length = c.scratch_cap := hsl_i.scratch_buf_len
    have harl_i : si.core.arena.length = c.arena_cap := hcl_i.arena_len_arr
    have harle_i : si.core.arena_len ≤ c.arena_cap := hcl_i.arena_len_le
    bve_steps
    · have hi_lt : i.toNat < cnt.toNat := by bv_omega
      have hoff_nat : (off + i).toNat = off.toNat + i.toNat := by bv_omega
      have hscr_lt : (BitVec.setWidth 64 (off + i)).toNat < si.scratch.scratch_buf.length := by
        rw [m6_zext32_toNat, hscrl_i, hoff_nat]; omega
      have hw_eq : si.scratch.scratch_buf[(off + i).toNat]'(by
          rw [hscrl_i, hoff_nat]; omega) =
          s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega), hscr_eq, hoff_nat,
            List.getElem?_eq_getElem (by rw [hdw.1.scratch_ok.scratch_buf_len]; omega)]; rfl)
      have hitem_i := hitems i.toNat hi_lt
      have hbin : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt &&&
          0x80000000#32) ≠ 0#32 := hc
      have hw_zext : si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt =
          s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by
        rw [← hw_eq]; exact m6_getElem_congr (m6_zext32_toNat _) _ _
      refine wp_call_of_spec _ _ (hExtPush2 _ mi _ X ⟨c, si, R,
        ⟨rfl, hdw_i.2.2.2.2.1.2⟩, hdw_i.1, hm_i, ?_⟩)
      rintro ok s1 m1 hcore1 hlen1 ⟨hll1, hel1, hscr1, htmk1_eq⟩ hm1
      dsimp only [fullSafetySlice_mem] at hm1
      have ⟨hdw1_b, hcv1, hfuel1, hrefs1⟩ :=
        FullBveBvaHelpers.weaken_ext_step (s6a_denseInvW_to_bve hdw_i) hlen1 hcore1 hll1 hel1
      have hdw1 : Full.FullDenseInvW c F0 F_cur s1 := s6a_denseInvW_of_bve hdw1_b
      have htmk1 : TmkZero s1 := htmk_i.congr hcv1 htmk1_eq
      have hblk_max : blk_lit.toNat < 2 * c.max_vars := by
        have := hdw.1.core_ok.cur_vars_le; omega
      have hot_max : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt &&&
          0x7FFFFFFF#32).toNat < 2 * c.max_vars := by
        rw [hw_zext]
        exact s6a_weakItem_bin_lt hitem_i (hw_zext ▸ hbin) hdw.1.core_ok.cur_vars_le
      bve_steps!
      · refine wp_call_of_spec _ _ (hDelBin _ m1 _ X ⟨c, s1, R, rfl, hdw1.1,
          hdw1.2.1.watches.layout, hblk_max, hot_max, hm1, ?_⟩)
        intro flags' wvec' wstk' wu' nb' m2 _ hlen2 _hwl2 hwat2 hm2
        let s2 : FullState :=
          { s1 with core := { s1.core with
            flags := flags', wvec := wvec', wstk := wstk',
            wusable := wu', num_binary := nb' } }
        have hdw2 := s6a_denseInvW_of_delete_binary13 hdw1 hlen2 hwat2
        have htmk2 : TmkZero s2 := htmk1.congr rfl rfl
        have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s1 := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rfl
        bve_steps!
        exact ih (i + 1#32, PUnit.unit) m2 (by bv_omega) ⟨by bv_omega, s2, hdw2, htmk2,
          hcv1.trans hcv_eq, hfuel1.trans hfuel_eq, hscr1.trans hscr_eq,
          hrefs2.trans (hrefs1.trans hrefs_eq), hm2⟩
      · exact hQ false s1 m1 hdw1 htmk1 (hcv1.trans hcv_eq) (hfuel1.trans hfuel_eq)
          (hscr1.trans hscr_eq) (hrefs1.trans hrefs_eq) hm1
    · have hi_lt : i.toNat < cnt.toNat := by bv_omega
      have hoff_nat : (off + i).toNat = off.toNat + i.toNat := by bv_omega
      have hscr_lt : (BitVec.setWidth 64 (off + i)).toNat < si.scratch.scratch_buf.length := by
        rw [m6_zext32_toNat, hscrl_i, hoff_nat]; omega
      have hw_eq : si.scratch.scratch_buf[(off + i).toNat]'(by
          rw [hscrl_i, hoff_nat]; omega) =
          s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega), hscr_eq, hoff_nat,
            List.getElem?_eq_getElem (by rw [hdw.1.scratch_ok.scratch_buf_len]; omega)]; rfl)
      have hitem_i := hitems i.toNat hi_lt
      unfold Full.FullBveWeakItemOk at hitem_i
      have hnb : ¬ (s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 &&&
          0x80000000#32) ≠ 0#32 := by
        intro hne
        have hhc : si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt &&&
            0x80000000#32 = 0#32 := hc
        simp only [m6_zext32_toNat] at hhc; rw [hw_eq] at hhc; exact hne hhc
      rw [ite_eq_right hnb] at hitem_i
      have hitem_ref : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt
          ).toNat ∈ fullArenaClauseRefs si := by
        simp only [m6_zext32_toNat]; rw [hw_eq, hrefs_eq]; exact hitem_i
      refine wp_call_of_spec _ _ (hExtPushCl _ mi _ X ⟨c, si, R,
        ⟨rfl, hdw_i.2.2.2.2.1.2⟩, hdw_i.1, hm_i, ?_⟩)
      rintro ok s1 m1 hcore1 hlen1 ⟨hll1, hel1, hscr1, htmk1_eq⟩ hm1
      dsimp only [fullSafetySlice_mem] at hm1
      have ⟨hdw1_b, hcv1, hfuel1, hrefs1⟩ :=
        FullBveBvaHelpers.weaken_ext_step (s6a_denseInvW_to_bve hdw_i) hlen1 hcore1 hll1 hel1
      have hdw1 : Full.FullDenseInvW c F0 F_cur s1 := s6a_denseInvW_of_bve hdw1_b
      have htmk1 : TmkZero s1 := htmk_i.congr hcv1 htmk1_eq
      have heq_core : s1.core = si.core := fullCoreState_agrees_with_scratch hcore1
      let w := si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt
      have hw_ref1 : w.toNat ∈ fullArenaClauseRefs s1 := by
        unfold fullArenaClauseRefs; rw [heq_core]; exact hitem_ref
      have hwf1 := hdw1.2.1.arena.refs_wf w.toNat hw_ref1
      have har1 : s1.core.arena.length = c.arena_cap := hlen1.core_ok.arena_len_arr
      have harle1 : s1.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
      have hbd1 : w.toNat + 3 + fullArenaClauseSize s1 w.toNat ≤ s1.core.arena_len := by
        unfold fullArenaClauseSize; omega
      have hw_ar : (BitVec.setWidth 64 w).toNat < s1.core.arena.length := by
        rw [m6_zext32_toNat]; omega
      have hw2_ar : (BitVec.setWidth 64 w + 2).toNat < s1.core.arena.length := by bv_omega
      have hw_lt_ar : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt
          ).toNat + 2 < s1.core.arena.length := by change w.toNat + 2 < _; omega
      bve_steps!
      · let w_hm := si.scratch.scratch_buf[(off + i).toNat]'(by rw [hscrl_i, hoff_nat]; omega)
        have hw_hm_eq : w_hm = w := Option.some.inj (by
          dsimp only [w_hm, w]
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega),
            ← List.getElem?_eq_getElem hscr_lt, m6_zext32_toNat])
        have hw_hm_ref : w_hm.toNat ∈ fullArenaClauseRefs s1 := by rw [hw_hm_eq]; exact hw_ref1
        have hw_hm_ar : w_hm.toNat < s1.core.arena.length := by
          have h1 := hw_ar; rw [m6_zext32_toNat, ← hw_hm_eq] at h1; exact h1
        have hw2_hm_ar : (BitVec.setWidth 64 w_hm + 2).toNat <
            (s1.core.arena.set w_hm.toNat
              (s1.core.arena[w_hm.toNat]'hw_hm_ar ||| 0x00080000#32)).length := by
          rw [List.length_set, hw_hm_eq]; exact hw2_ar
        let ag_hm := s1.core.arena_garbage + 3 + BitVec.setWidth 64
          ((s1.core.arena.set w_hm.toNat
            (s1.core.arena[w_hm.toNat]'hw_hm_ar ||| 0x00080000#32))[(BitVec.setWidth 64 w_hm +
              2).toNat]'hw2_hm_ar)
        have ⟨hrefs2, hdw2⟩ := FullBveBvaHelpers.weaken_markGarb_step
          hw_hm_ref hw_hm_ar ag_hm (s6a_denseInvW_to_bve hdw1)
        exact ih (i + 1#32, PUnit.unit) m (by bv_omega) ⟨by bv_omega, _, s6a_denseInvW_of_bve hdw2,
          htmk1.congr rfl rfl, hcv1.trans hcv_eq, hfuel1.trans hfuel_eq, hscr1.trans hscr_eq,
          hrefs2.trans (hrefs1.trans hrefs_eq), hm⟩
      · exact hQ false s1 m1 hdw1 htmk1 (hcv1.trans hcv_eq) (hfuel1.trans hfuel_eq)
          (hscr1.trans hscr_eq) (hrefs1.trans hrefs_eq) hm1
    · bve_steps!
      exact hQ true si mi hdw_i htmk_i hcv_eq hfuel_eq hscr_eq hrefs_eq hm_i

/-! ## 3. `full_bve_weaken_unit_fid_step13_wp` (`full_bve_weaken_unit_fid`) -/

/-- Step-13 lift for `full_bve_weaken_unit_fid` over `step13DeleteBinarySpec`. -/
public theorem full_bve_weaken_unit_fid_step13_wp (Γ : Env)
    (hDelBin : ∀ xs m Q X, step13DeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X) :
    ∀ args m Q X, fullBveWeakenTmkSpec args m Q X →
      Func.wp Γ full_bve_weaken_unit_fid_body args m Q X := by
  rintro ⟨h, blk_lit, off, cnt, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, htmk, hblk, hoff, hitems, hm0, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; have harc := c.harena; have hexc := c.hext
  unfold dimacsBound at hmv hsc harc hexc
  unfold Func.wp full_bve_weaken_unit_fid_body
  c0_hsplit
  · c0_hsteps!; exact hQ true s m0 hdw htmk rfl rfl rfl rfl hm0
  · c0_hsplit
    · c0_hsteps!; exact hQ false s m0 hdw htmk rfl rfl rfl rfl hm0
    · have hel_lt : s.scratch.extend_len < c.extend_cap := by
        have hel_le := hdw.2.2.2.2.1.2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem (i, ()) mi =>
          ∃ si : FullState,
            i.toNat ≤ cnt.toNat ∧ rem = cnt.toNat - i.toNat ∧
            FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
            si.core.cur_vars = s.core.cur_vars ∧ si.core.fuel = s.core.fuel ∧
            si.scratch.scratch_buf = s.scratch.scratch_buf ∧
            si.scratch.extend_len = s.scratch.extend_len ∧
            fullArenaClauseRefs si = fullArenaClauseRefs s ∧
            (FullMem c si ⋆ R) mi)
        ?_ ?_
      · rintro L rem ⟨i, ⟨⟩⟩ mi hL
          ⟨si, hi_le, rfl, hdw_i, htmk_i, hcv_eq, hfuel_eq, hscr_eq, hel_eq, hrefs_eq, hm_i⟩
        have hcl_i := hdw_i.1.core_ok; have hsl_i := hdw_i.1.scratch_ok
        have hscrl_i : si.scratch.scratch_buf.length = c.scratch_cap := hsl_i.scratch_buf_len
        have harl_i : si.core.arena.length = c.arena_cap := hcl_i.arena_len_arr
        have harle_i : si.core.arena_len ≤ c.arena_cap := hcl_i.arena_len_le
        c0_hsplit
        · have hi_lt : i.toNat < cnt.toNat := hc
          have hoff_nat : (off + i).toNat = off.toNat + i.toNat := by c0_bound
          have hscr_lt : ((off + i).setWidth 64).toNat < si.scratch.scratch_buf.length := by
            rw [m6_zext32_toNat, hscrl_i, hoff_nat]; omega
          have hw_eq : si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt =
              s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by
            have h1 : si.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 =
                s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by rw [hscr_eq]
            rw [← h1, List.getElem?_eq_getElem (by rw [hscrl_i]; omega), Option.getD_some]
            exact m6_getElem_congr (by rw [m6_zext32_toNat, hoff_nat]) _ _
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
            (fun sj mj =>
              FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
              sj.core.cur_vars = s.core.cur_vars ∧ sj.core.fuel = s.core.fuel ∧
              sj.scratch.scratch_buf = s.scratch.scratch_buf ∧
              sj.scratch.extend_len = s.scratch.extend_len ∧
              fullArenaClauseRefs sj = fullArenaClauseRefs s ∧
              (FullMem c sj ⋆ R) mj)
            (fun _ sj mj ⟨hdwj, htmkj, hcvj, hflj, hscrj, helj, hrefsj, hmj⟩ => by
              c0_hsteps!
              exact hL (cnt.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj (by omega)
                ⟨sj, by omega, rfl, hdwj, htmkj, hcvj, hflj, hscrj, helj, hrefsj, hmj⟩)
            (fun Jstep hJstep => by
              c0_hsplit
              · have hitem_i := hitems i.toNat hi_lt
                have hbin : (si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt &&&
                    0x80000000#32) ≠ 0#32 := hc
                have hblk_max : blk_lit.toNat < 2 * c.max_vars := by
                  have := hdw.1.core_ok.cur_vars_le; omega
                have hot_max : (si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt &&&
                    0x7FFFFFFF#32).toNat < 2 * c.max_vars := by
                  rw [hw_eq]
                  exact s6a_weakItem_bin_lt hitem_i (hw_eq ▸ hbin) hdw.1.core_ok.cur_vars_le
                c0_hsteps_nogrp
                s6a_call hDelBin
                refine ⟨c, si, R, rfl, hdw_i.1, hdw_i.2.1.watches.layout,
                  hblk_max, hot_max, hm_i, ?_⟩
                intro flags' wvec' wstk' wu' nb' m2 _ hlen2 _hwl2 hwat2 hm2
                let s2 : FullState :=
                  { si with core := { si.core with
                    flags := flags', wvec := wvec', wstk := wstk',
                    wusable := wu', num_binary := nb' } }
                have hdw2 := s6a_denseInvW_of_delete_binary13 hdw_i hlen2 hwat2
                have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs si := by
                  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rfl
                c0_hsteps!
                exact hJstep s2 m2 ⟨hdw2, htmk_i.congr rfl rfl, hcv_eq, hfuel_eq, hscr_eq,
                  hel_eq, hrefs2.trans hrefs_eq, hm2⟩
              · let w := si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                have hitem_i := hitems i.toNat hi_lt
                unfold FullBveWeakItemOk at hitem_i
                have hnb : ¬ (s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 &&&
                    0x80000000#32) ≠ 0#32 := by
                  intro hne
                  have hhc : w &&& 0x80000000#32 = 0#32 := by
                    dsimp only [w]
                    have hcongr := m6_getElem_congr
                      (by rw [m6_zext32_toNat, hoff_nat, Nat.mod_eq_of_lt (by omega)] :
                        ((off + i).setWidth 64).toNat = (off.toNat + i.toNat) % 2 ^ 32)
                      hscr_lt (by rw [hscrl_i, Nat.mod_eq_of_lt (by omega)]; omega)
                    rw [hcongr]; exact hc
                  dsimp only [w] at hhc; rw [hw_eq] at hhc; exact hne hhc
                rw [ite_eq_right hnb] at hitem_i
                have hw_ref : w.toNat ∈ fullArenaClauseRefs si := by
                  dsimp only [w]; rw [hw_eq, hrefs_eq]; exact hitem_i
                have hwf := hdw_i.2.1.arena.refs_wf w.toNat hw_ref
                have hw_ar : ((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                    ).setWidth 64).toNat < si.core.arena.length := by
                  change (w.setWidth 64).toNat < si.core.arena.length
                  rw [m6_zext32_toNat, harl_i]; omega
                have hw_ar_nat : w.toNat < si.core.arena.length := by rw [harl_i]; omega
                have hw2_ar : ((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                    ).setWidth 64 + 2#64).toNat < si.core.arena.length := by
                  change (w.setWidth 64 + 2#64).toNat < si.core.arena.length
                  rw [harl_i]; c0_bound
                have hw2_ar_set : ((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                    ).setWidth 64 + 2#64).toNat < (si.core.arena.set
                    ((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt).setWidth
                      64).toNat
                    (si.core.arena[((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                      ).setWidth 64).toNat]'hw_ar ||| 0x00080000#32)).length := by
                  rw [List.length_set]; exact hw2_ar
                c0_hsteps!
                let ar' := si.core.arena.set (w.setWidth 64).toNat
                  (si.core.arena[(w.setWidth 64).toNat]'hw_ar ||| 0x00080000#32)
                let ag' := si.core.arena_garbage + 3#64 +
                  (ar'[(w.setWidth 64 + 2#64).toNat]'hw2_ar_set).setWidth 64
                let s2 : FullState :=
                  { si with core := { si.core with arena := ar', arena_garbage := ag' } }
                have hhdr_eq : si.core.arena[w.toNat]'hw_ar_nat = fullArenaHdr si w.toNat := by
                  unfold fullArenaHdr fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hw_ar_nat, Option.getD_some]
                have har'_eq : ar' = si.core.arena.set w.toNat
                    (fullArenaHdr si w.toNat ||| 0x00080000#32) := by
                  dsimp only [ar']; rw [← hhdr_eq]
                  have hval := m6_getElem_congr (m6_zext32_toNat w) hw_ar hw_ar_nat
                  rw [hval, m6_zext32_toNat]
                have hmg := m6_fullDenseInvW_markGarb hdw_i hw_ref (arena' := ar') (ag' := ag')
                  (by simp [ar', harl_i])
                  (Or.inl (by rw [har'_eq]; exact List.getElem?_set_self hw_ar_nat))
                  (fun idx hne _ => by rw [har'_eq]; exact List.getElem?_set_ne hne.symm)
                exact hJstep s2 _ ⟨hmg.1, htmk_i.congr rfl rfl, hcv_eq, hfuel_eq, hscr_eq,
                  hel_eq, hmg.2.trans hrefs_eq, hm⟩)
        · have hp_lt : si.scratch.extend_len < si.scratch.extend_stk.length := by
            rw [hsl_i.extend_stk_len, hel_eq]; exact hel_lt
          have hp_bv : (BitVec.ofNat 64 si.scratch.extend_len).toNat = si.scratch.extend_len := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hp1_bv : (BitVec.ofNat 64 si.scratch.extend_len + 1#64).toNat =
              si.scratch.extend_len + 1 := by
            rw [BitVec.toNat_add, hp_bv, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          c0_hsteps!
          let ext' := si.scratch.extend_stk.set si.scratch.extend_len
            ((blk_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
          let sf : FullState :=
            { si with scratch :=
              { si.scratch with extend_stk := ext', extend_len := si.scratch.extend_len + 1 } }
          have hdwf : FullDenseInvW c F0 F_cur sf :=
            s6a_fullDenseInvW_push_ext1 hdw_i (by simp [ext', hsl_i.extend_stk_len])
              (by rw [hel_eq]; omega)
          exact hQ true sf _ hdwf (htmk_i.congr rfl rfl) hcv_eq hfuel_eq hscr_eq hrefs_eq
            (by simpa [sf, ext', hp_bv, hp1_bv] using hm)
      · intro L hL; c0_hsteps!
        exact hL cnt.toNat (0#32, ()) m0
          ⟨s, Nat.zero_le _, by simp, hdw, htmk, rfl, rfl, rfl, rfl, rfl, hm0⟩

/-! ## 4. `full_bve_heap_push_m7_step13_wp` (`full_bve_heap_push_m7`) -/

private theorem full_bve_heap_push_m6_step13_wp (Γ : Env)
    (hKey : ∀ a m Q X, step13BveVarKeySpec a m Q X →
      Γ "full_bve_var_key_m6" [i64, i32] [i64] a m Q X)
    (hUp : ∀ a m Q X, fullBveHeapUpM6Spec a m Q X →
      Γ "full_bve_heap_up_m6" [i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fullBveHeapDownM6Spec a m Q X →
      Γ "full_bve_heap_down_m6" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, step13BveHeapPushSpec a m Q X →
      Func.wp Γ full_bve_heap_push_m6_body a m Q X := by
  rintro ⟨h, hlen, v, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hl0, hwl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hl0.core_ok.cur_vars_le
  have hws1_0 := hl0.scratch_ok.work_stk1_len
  have hss_0 := hl0.scratch_ok.sim_sig_len
  unfold Func.wp full_bve_heap_push_m6_body
  c0_hsplit
  · c0_hsteps!; exact hQ hlen s.scratch.work_stk1 s.scratch.sim_sig m0 hws1_0 hss_0 id hm0
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    c0_hsplit
    · c0_hsteps!; exact hQ hlen s.scratch.work_stk1 s.scratch.sim_sig m0 hws1_0 hss_0 id hm0
    · have hhl_le : hlen.toNat ≤ s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
      c0_hsteps_nogrp
      s6a_call hKey
      refine ⟨c, s, R, rfl, hl0, hwl0, hm0, ?_⟩
      intro nk
      have hv_ss : (v.setWidth 64).toNat < s.scratch.sim_sig.length := by
        rw [hss_0, m6_zext32_toNat]; omega
      have hmv_v : (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat <
          s.scratch.work_stk1.length := by rw [hws1_0]; c0_bound
      let ss1 := s.scratch.sim_sig.set (v.setWidth 64).toNat nk
      let s1 : FullState := { s with scratch := { s.scratch with sim_sig := ss1 } }
      have hss1_l : ss1.length = c.max_vars := by simp only [ss1, List.length_set, hss_0]
      have hl1 : s1.LengthsOk c := ⟨hl0.core_ok, { hl0.scratch_ok with sim_sig_len := hss1_l }⟩
      c0_hsplit
      · refine wp_join0 (P := fun mj => ∃ ws1' : List (BitVec 32),
          ws1'.length = 2 * c.max_vars ∧
          (FullMem c { s1 with scratch := { s1.scratch with work_stk1 := ws1' } } ⋆ R) mj)
          (fun _ mj ⟨ws1', hws1', hmj⟩ => by
            c0_hsteps!; exact hQ hlen ws1' ss1 mj hws1' (by simp [ss1, hss_0]) id hmj)
          (fun J1 hJ1 => by
            c0_hsplit
            · c0_hsteps_nogrp
              s6a_call hUp
              refine fullBveHeapUpM6Spec_intro rfl hl1 hm ?_
              intro ws1' m1 hws1' hm1
              c0_hsteps!; exact hJ1 m1 ⟨ws1', hws1', hm1⟩
            · refine wp_join0 (P := fun mj => ∃ ws1' : List (BitVec 32),
                ws1'.length = 2 * c.max_vars ∧
                (FullMem c { s1 with scratch := { s1.scratch with work_stk1 := ws1' } } ⋆ R) mj)
                (fun _ mj h => by c0_hsteps!; exact hJ1 mj h)
                (fun _ hJ2 => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    s6a_call hDown
                    refine fullBveHeapDownM6Spec_intro rfl hl1 hm ?_
                    intro ws1' m1 hws1' hm1
                    c0_hsteps!; exact hJ2 m1 ⟨ws1', hws1', hm1⟩
                  · c0_hsteps!; exact hJ2 _ ⟨s.scratch.work_stk1, hws1_0, hm⟩))
      · c0_hsplit
        · c0_hsteps!; exact hQ hlen s.scratch.work_stk1 ss1 _ hws1_0 (by simp [ss1, hss_0]) id hm
        · have hhl_lt : hlen.toNat < s.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
          have hhl_b : hlen.toNat < s.scratch.work_stk1.length := by omega
          have hhl1 : (hlen + 1#64).toNat = hlen.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          let ws1_a := (s.scratch.work_stk1.set hlen.toNat v).set
            (BitVec.ofNat 64 c.max_vars + v.setWidth 64).toNat (hlen.setWidth 32)
          let s2 : FullState :=
            { s1 with scratch := { s1.scratch with work_stk1 := ws1_a } }
          have hws1a_l : ws1_a.length = 2 * c.max_vars := by
            simp only [ws1_a, List.length_set, hws1_0]
          have hl2 : s2.LengthsOk c :=
            ⟨hl1.core_ok, { hl1.scratch_ok with work_stk1_len := hws1a_l }⟩
          s6a_call hUp
          refine fullBveHeapUpM6Spec_intro rfl hl2 hm ?_
          intro ws1' m1 hws1' hm1
          c0_hsteps!
          exact hQ (hlen + 1#64) ws1' ss1 m1 hws1' (by simp [ss1, hss_0])
            (fun _ => by omega) hm1

private def s6a_m6ToM7Sym : Sym → Sym
  | "full_bve_var_key_m6" => "full_bve_var_key_m7"
  | "full_bve_heap_up_m6" => "full_bve_heap_up_m7"
  | "full_bve_heap_down_m6" => "full_bve_heap_down_m7"
  | x => x

/-- Step-13 lift for `full_bve_heap_push_m7` over `step13BveVarKeySpec`. -/
public theorem full_bve_heap_push_m7_step13_wp (Γ : Env)
    (hKey : ∀ a m Q X, step13BveVarKeySpec a m Q X →
      Γ "full_bve_var_key_m7" [i64, i32] [i64] a m Q X)
    (hUp : ∀ a m Q X, fullBveHeapUpM6Spec a m Q X →
      Γ "full_bve_heap_up_m7" [i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fullBveHeapDownM6Spec a m Q X →
      Γ "full_bve_heap_down_m7" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, step13BveHeapPushSpec a m Q X →
      Func.wp Γ full_bve_heap_push_m7_body a m Q X := by
  refine func_wp_of_rename s6a_m6ToM7Sym full_bve_heap_push_m6_body full_bve_heap_push_m7_body
    ?_ Γ (full_bve_heap_push_m6_step13_wp _ hKey hUp hDown)
  intro _; unfold full_bve_heap_push_m6_body full_bve_heap_push_m7_body
  repeat (first
    | exact ExprRename.jump
    | exact ExprRename.ret
    | exact ExprRename.hlt
    | exact BlocksRename.nil
    | (apply ExprRename.let_; intro _)
    | (apply ExprRename.load; intro _)
    | apply ExprRename.store
    | (apply ExprRename.call _ _ rfl; intro _)
    | apply ExprRename.jnz
    | (apply ExprRename.group <;> intro _)
    | (apply BlocksRename.cons; intro _))

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
