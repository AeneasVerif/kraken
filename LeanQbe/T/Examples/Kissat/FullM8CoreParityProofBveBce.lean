/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity (`FullM8CoreParity`) Rank #8 Proofs — BCE & Heap/Elim Bridge (`BveBce`)

UNSAT-only `Func.wp` proofs (`public section`, clean `std3`, `XPost := False`):
1. `full_bve_bce_side_m8_wp`: certifies `m8BveBceSideSpec` for `full_bve_bce_side_m8_body`.
2. `full_bve_heap_push_m7_m8_wp`: certifies `m8BveHeapPushSpec` for
   `FullM7BveGates.full_bve_heap_push_m7_body` against `m8BveVarKeySpec`.
3. `full_elim_bve_fid_m8_wp`: certifies canonical `FullM3CongBva.m3ElimBveSpec` for
   `FullM7FidelityCore.full_elim_bve_fid_body` against `m8BveHeapPushSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM7FidelityCore
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

/-! ## 1. Private Helpers for `full_bve_bce_side_m8_wp` -/

private theorem m8_bce_entry_to_weak {c : FullCfg} {s : FullState} {w : BitVec 32}
    (h : FullBveVarSpecs.FullBveTryBceEntryOk c s w) :
    FullBveBceWeakOk c s w ∧
    ((w &&& 0x80000000#32) = 0#32 → ((fullArenaClauseLits s w.toNat).map (· / 2)).Nodup) := by
  unfold FullBveVarSpecs.FullBveTryBceEntryOk at h
  unfold FullBveBceWeakOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact ⟨h, fun h0 => absurd h0 hb⟩
  · rw [ite_eq_right hb] at h ⊢; exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, fun _ => h.2.2.2⟩

private theorem m8_bce_opp_to_weak {c : FullCfg} {s : FullState} {w : BitVec 32}
    (h : FullBveVarSpecs.FullBveTryBceOppOk c s w) :
    FullBveBceWeakOk c s w := by
  unfold FullBveVarSpecs.FullBveTryBceOppOk at h
  unfold FullBveBceWeakOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact h
  · rw [ite_eq_right hb] at h ⊢; exact h

private theorem m8_bce_weak_congr {c : FullCfg} {s s' : FullState} {w : BitVec 32}
    (h : FullBveBceWeakOk c s w) (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s)
    (hal : s'.core.arena_len = s.core.arena_len)
    (hsz : ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r)
    (hlits : ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseLits s' r = fullArenaClauseLits s r) :
    FullBveBceWeakOk c s' w := by
  unfold FullBveBceWeakOk at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact h
  · rw [ite_eq_right hb] at h ⊢; rw [hrefs, hal, hsz _ h.1, hlits _ h.1]; exact h

private theorem m8_bce_denseInv_of_extPush {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : s'.core = s.core) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len ≤ c.extend_cap) : FullDenseInvW c F0 F_cur s' :=
  ⟨hlen', hcore ▸ h.2.1,
   ⟨fun v hv => by rw [hcore]; exact h.2.2.1.1 v hv,
    fun l hl => by rw [hcore]; exact h.2.2.1.2 l hl⟩,
   fun r hr hng => by
     change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hcore] at hr
     change fullArenaClauseGarbCore s'.core r = false at hng; rw [hcore] at hng
     change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
     rw [hcore]; exact h.2.2.2.1 r hr hng,
   ⟨fun k hk => by
     change s'.scratch.last_learned[k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
       _ ∈ fullArenaClauseRefsCore s'.core
     rw [hll, hcore]; exact h.2.2.2.2.1.1 k hk, hext⟩,
   by rw [hcore]; exact h.2.2.2.2.2.1, by rw [hcore]; exact h.2.2.2.2.2.2⟩

private theorem m8_bce_fullDenseInvW_delBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hlen' : ({ s with core :=
      { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :
      FullState).LengthsOk c)
    (hw' : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :=
  ⟨hlen', { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }, watches := hw' },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m8_bce_markGarb_pres_lits {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {ag' : BitVec 64} :
    let ar' := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
    let s' : FullState := { s with core := { s.core with arena := ar', arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro ar' s'
  have hcl := h.1.core_ok; have hw := h.2.1
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hmg := m6_fullDenseInvW_markGarb h href (arena' := ar') (ag' := ag')
    (by simp [ar', hcl.arena_len_arr]) (Or.inl (List.getElem?_set_self har_len))
    (fun i hne _ => List.getElem?_set_ne (Ne.symm hne))
  refine ⟨hmg.1, hmg.2, fun r hr => ?_⟩
  have hwf := hw.arena.refs_wf r hr
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hsz : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
    unfold fullArenaClauseSizeCore; dsimp only [s', ar']
    by_cases hrc : r = cref
    · subst hrc; rw [List.getElem?_set_ne (by omega)]
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr href hlt
        rw [List.getElem?_set_ne (by omega)]
      · have := fullArenaScanRefs_disjoint href hr hgt
        rw [List.getElem?_set_ne (by omega)]
  have hlits : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
    fullArenaClauseLitsCore_eq_of_hold hbd (by simp [s', ar', hbd]) hsz fun j hj => by
      dsimp only [s', ar']
      by_cases hrc : r = cref
      · subst hrc; exact List.getElem?_set_ne (by omega)
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := fullArenaScanRefs_disjoint hr href hlt
          exact List.getElem?_set_ne (by omega)
        · have := fullArenaScanRefs_disjoint href hr hgt
          exact List.getElem?_set_ne (by omega)
  exact ⟨hsz, hlits⟩

private theorem m8_bce_hm {c : FullCfg} {se : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {w w0 : BitVec 32} (hw_eq : w = w0)
    (hw0_lt : w0.toNat < se.core.arena.length)
    (hw_ne : w0.toNat ≠ (w0.setWidth 64 + 2#64).toNat)
    {hw : (w.setWidth 64).toNat < se.core.arena.length}
    {hw2 : (w.setWidth 64 + 2).toNat < (se.core.arena.set (w.setWidth 64).toNat
      (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288)).length}
    {hw0_2 : (w0.setWidth 64 + 2#64).toNat < se.core.arena.length}
    (hhdr : se.core.arena[w0.toNat]'hw0_lt = fullArenaHdr se w0.toNat)
    (hm : (FullMem c { se with
      core := { se.core with
        arena := se.core.arena.set (w.setWidth 64).toNat
          (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288),
        arena_garbage := se.core.arena_garbage + 3 +
          ((se.core.arena.set (w.setWidth 64).toNat
            (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288))[(w.setWidth 64 +
              2).toNat]'hw2).setWidth 64 }
      scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1 } } ⋆ R) m) :
    (FullMem c { se with
      core := { se.core with
        arena := se.core.arena.set w0.toNat (fullArenaHdr se w0.toNat ||| 0x00080000#32),
        arena_garbage := se.core.arena_garbage + 3#64 +
          (se.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw0_2).setWidth 64 }
      scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1#64 } } ⋆ R) m := by
  subst hw_eq
  have hz : (w.setWidth 64).toNat = w.toNat := m6_zext32_toNat w
  have har_eq : se.core.arena.set (w.setWidth 64).toNat
      (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288) =
      se.core.arena.set w.toNat (fullArenaHdr se w.toNat ||| 0x00080000#32) := by
    exact congrArg (se.core.arena.set w.toNat)
      (by rw [m6_getElem_congr hz hw hw0_lt, hhdr]; rfl)
  have hag_eq : se.core.arena_garbage + 3 +
      ((se.core.arena.set (w.setWidth 64).toNat
        (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288))[(w.setWidth 64 +
          2).toNat]'hw2).setWidth 64 =
      se.core.arena_garbage + 3#64 +
      (se.core.arena[(w.setWidth 64 + 2#64).toNat]'hw0_2).setWidth 64 := by
    have h2 : (2 : BitVec 64) = 2#64 := rfl
    have hne' : (w.setWidth 64).toNat ≠ (w.setWidth 64 + 2).toNat := by
      rw [hz, h2]; exact hw_ne
    have hge_ne : (se.core.arena.set (w.setWidth 64).toNat
        (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288))[(w.setWidth 64 +
          2).toNat]'hw2 =
        se.core.arena[(w.setWidth 64 + 2).toNat]'(by
          rw [List.length_set] at hw2; exact hw2) := by
      rw [List.getElem_set_ne hne']
    have hge_eq : se.core.arena[(w.setWidth 64 + 2).toNat]'(by
        rw [List.length_set] at hw2; exact hw2) =
        se.core.arena[(w.setWidth 64 + 2#64).toNat]'hw0_2 :=
      m6_getElem_congr (by rw [h2]) _ hw0_2
    rw [hge_ne, hge_eq]; rfl
  have hs_eq : ({ se with
      core := { se.core with
        arena := se.core.arena.set (w.setWidth 64).toNat
          (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288),
        arena_garbage := se.core.arena_garbage + 3 +
          ((se.core.arena.set (w.setWidth 64).toNat
            (se.core.arena[(w.setWidth 64).toNat]'hw ||| 524288))[(w.setWidth 64 +
              2).toNat]'hw2).setWidth 64 }
      scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1 } } : FullState) =
      { se with
      core := { se.core with
        arena := se.core.arena.set w.toNat (fullArenaHdr se w.toNat ||| 0x00080000#32),
        arena_garbage := se.core.arena_garbage + 3#64 +
          (se.core.arena[(w.setWidth 64 + 2#64).toNat]'hw0_2).setWidth 64 }
      scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1#64 } } := by
    rw [hag_eq, har_eq, show (1 : BitVec 64) = 1#64 from rfl]
  rwa [hs_eq] at hm

/-! ## 2. `full_bve_bce_side_m8_wp` (`m8BveBceSideSpec`) -/

/-- Certifies `m8BveBceSideSpec` for `full_bve_bce_side_m8`. -/
theorem full_bve_bce_side_m8_wp (Γ : Env)
    (hTryBce : ∀ a m Q X, Full.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hExtPush2 : ∀ a m Q X, FullFastBveBudgets.fullExtendPush2TmkSpec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hExtPushCl : ∀ a m Q X, FullFastBveBudgets.fullExtendPushClTmkSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m8BveBceSideSpec a m Q X →
      Func.wp Γ full_bve_bce_side_m8_body a m Q X := by
  rintro ⟨h, lit, off, cnt, opp_off, opp_n, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, htmk0, hlit_lt, hoff_le, hopp_le,
    hcnt_ok, hopp_ok, hm0, hQ⟩ := m8BveBceSideSpec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; have harc := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmx hsc harc hwc
  let P_bce : FullState → Mem 64 → Prop := fun sj mj =>
    FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
    sj.core.cur_vars = s0.core.cur_vars ∧
    sj.core.arena_len = s0.core.arena_len ∧
    sj.core.fuel = s0.core.fuel ∧
    sj.scratch.scratch_buf = s0.scratch.scratch_buf ∧
    fullArenaClauseRefs sj = fullArenaClauseRefs s0 ∧
    (∀ r ∈ fullArenaClauseRefs s0,
      fullArenaClauseSize sj r = fullArenaClauseSize s0 r ∧
      fullArenaClauseLits sj r = fullArenaClauseLits s0 r) ∧
    (FullMem c sj ⋆ R) mj
  unfold Func.wp full_bve_bce_side_m8_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem_i (i, ()) mi => ∃ si : FullState,
      i.toNat ≤ cnt.toNat ∧ rem_i = cnt.toNat - i.toNat ∧ P_bce si mi)
    ?_ ?_
  · rintro Li rem_i ⟨i, ⟨⟩⟩ mi hLi
      ⟨si, hi_le, rfl, hdwi, htmki, hcvi, hali, hfli, hscri, hrefsi, hperi, hmi⟩
    c0_hsplit
    · have hi_lt : i.toNat < cnt.toNat := hc
      have hoff_i_eq : ((off + i).setWidth 64).toNat = off.toNat + i.toNat := by
        rw [m6_zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hi_sc : ((off + i).setWidth 64).toNat < si.scratch.scratch_buf.length := by
        rw [hdwi.1.scratch_ok.scratch_buf_len, hoff_i_eq]; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      let wi := si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hi_sc
      have hwi_eq : wi = s0.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by
        have h0 : some wi = s0.scratch.scratch_buf[off.toNat + i.toNat]? := by
          dsimp only [wi]
          rw [← List.getElem?_eq_getElem hi_sc, hscri, hoff_i_eq]
        rw [← h0]; rfl
      have hbce_w := m8_bce_entry_to_weak (hcnt_ok i.toNat hi_lt).1
      c0_hsteps_nogrp
      refine wp_join_state (ts := []) (α := FullState) (fun _ => ()) P_bce
        (fun _ sj mj hj => by
          c0_hsteps!
          exact hLi (cnt.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj
            (by omega) ⟨sj, by omega, rfl, hj⟩)
        (fun Jstep hJstep => by
          c0_hsteps_nogrp
          refine wp_call_of_spec _ _ (hTryBce _ _ _ _ ?_)
          dsimp only [vals, Arg.val]
          refine ⟨c, F0, F_cur, si, R, rfl, hdwi, by rw [hcvi]; exact hlit_lt,
            by change FullBveBceWeakOk c si wi
               rw [hwi_eq]
               exact m8_bce_weak_congr hbce_w.1 hrefsi hali
                 (fun r hr => (hperi r hr).1) (fun r hr => (hperi r hr).2),
            fun hnb => by
              have hnb' : (wi &&& 0x80000000#32) = 0#32 := hnb
              rw [hwi_eq] at hnb'
              have hmem := hbce_w.1; unfold FullBveBceWeakOk at hmem
              simp only [hnb', ne_eq, not_true_eq_false, ↓reduceIte] at hmem
              have hwl_eq :
                  fullArenaClauseLits si
                    (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]).toNat =
                  fullArenaClauseLits si wi.toNat := rfl
              rw [hwl_eq, hwi_eq, (hperi _ hmem.1).2]
              exact hbce_w.2 hnb',
            hopp_le, fun k hk => by
              rw [hscri]
              exact m8_bce_weak_congr (m8_bce_opp_to_weak (hopp_ok k hk)) hrefsi hali
                (fun r hr => (hperi r hr).1) (fun r hr => (hperi r hr).2),
            hmi, ?_⟩
          intro blk lm_t tmp_t m_t st_b hdwt_b hm_t
          have htmkt_b : TmkZero st_b := htmki
          c0_hsplit
          · refine wp_join_state (ts := []) (α := FullState) (fun _ => ()) P_bce
              (fun _ sj mj hj => by c0_hsteps!; exact hJstep sj mj hj)
              (fun Jb hJb => by
                c0_hsplit
                · refine wp_join_state (ts := []) (α := FullState) (fun _ => ()) P_bce
                    (fun _ sj mj hj => by c0_hsteps!; exact hJb sj mj hj)
                    (fun Jbin hJbin => by
                      c0_hsteps_nogrp
                      refine wp_call_of_spec _ _ (hExtPush2 _ _ _ _ ?_)
                      dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                        fullSafetySlice_safe, vals, Arg.val]
                      refine ⟨c, st_b, R, ⟨rfl, hdwt_b.2.2.2.2.1.2⟩, hdwt_b.1, hm_t, ?_⟩
                      rintro ⟨ok_e, ⟨⟩⟩ se me hpr_e hlen_e hpost_e hm_e
                      dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                        fullSafetySlice_safe] at hpr_e hlen_e hm_e
                      have hcore_e : se.core = st_b.core :=
                        fullCoreState_agrees_with_scratch (c := c) hpr_e
                      have hdwe := m8_bce_denseInv_of_extPush hdwt_b hlen_e hcore_e
                        hpost_e.1 hpost_e.2.1
                      have htmke : TmkZero se :=
                        htmkt_b.congr (congrArg FullCoreState.cur_vars hcore_e) hpost_e.2.2.2
                      have hsc_e : se.scratch.scratch_buf = s0.scratch.scratch_buf :=
                        hpost_e.2.2.1.trans hscri
                      dsimp only
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_call_of_spec _ _ (hDelBin _ _ _ _ ?_)
                        refine ⟨c, se, R, rfl, hdwe.1,
                          (m6_denseWatchesInv_of_w hdwe).layout, hm_e, ?_⟩
                        intro wvec' wstk' wu' nb' m_d sd hlen_d _ hwm_d hm_d
                        have hdwd := m8_bce_fullDenseInvW_delBin hdwe hlen_d
                          (hwm_d F_cur hdwe.2.1.watches)
                        c0_hsteps!
                        let sd2 : FullState := { sd with scratch :=
                          { sd.scratch with bce_cnt := sd.scratch.bce_cnt + 1#64 } }
                        have hdwd2 := m6_fullDenseInvW_with_scratch hdwd
                          (sc' := sd2.scratch) { hdwd.1.scratch_ok with } rfl rfl
                        exact hJbin sd2 _ ⟨hdwd2, htmke,
                          (congrArg FullCoreState.cur_vars hcore_e).trans hcvi,
                          (congrArg FullCoreState.arena_len hcore_e).trans hali,
                          (congrArg FullCoreState.fuel hcore_e).trans hfli,
                          hsc_e, by
                            unfold fullArenaClauseRefs fullArenaClauseRefsCore
                            dsimp only [sd2, sd]
                            rw [congrArg FullCoreState.arena hcore_e,
                              congrArg FullCoreState.arena_len hcore_e]
                            exact hrefsi,
                          fun r hr => by
                            unfold fullArenaClauseSize fullArenaClauseSizeCore
                              fullArenaClauseLits fullArenaClauseLitsCore
                            dsimp only [sd2, sd]
                            rw [congrArg FullCoreState.arena hcore_e]
                            exact hperi r hr, hm⟩
                      · c0_hsteps!
                        exact hJbin se me ⟨hdwe, htmke,
                          (congrArg FullCoreState.cur_vars hcore_e).trans hcvi,
                          (congrArg FullCoreState.arena_len hcore_e).trans hali,
                          (congrArg FullCoreState.fuel hcore_e).trans hfli,
                          hsc_e, by
                            unfold fullArenaClauseRefs fullArenaClauseRefsCore
                            rw [congrArg FullCoreState.arena hcore_e,
                              congrArg FullCoreState.arena_len hcore_e]
                            exact hrefsi,
                          fun r hr => by
                            have har_stb : st_b.core.arena = si.core.arena := rfl
                            have hp := hperi r hr
                            unfold fullArenaClauseSize fullArenaClauseLits
                              fullArenaClauseLitsCore fullArenaClauseSizeCore at hp ⊢
                            rw [congrArg FullCoreState.arena hcore_e, har_stb]
                            exact hp, hm_e⟩)
                · have hwi_nb : (wi &&& 0x80000000#32) = 0#32 := hc
                  refine wp_join_state (ts := []) (α := FullState) (fun _ => ()) P_bce
                    (fun _ sj mj hj => by c0_hsteps!; exact hJb sj mj hj)
                    (fun Jcl hJcl => by
                      c0_hsteps_nogrp
                      refine wp_call_of_spec _ _ (hExtPushCl _ _ _ _ ?_)
                      dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                        fullSafetySlice_safe, vals, Arg.val]
                      refine ⟨c, st_b, R, ⟨rfl, hdwt_b.2.2.2.2.1.2⟩, hdwt_b.1, hm_t, ?_⟩
                      rintro ⟨ok_e, ⟨⟩⟩ se me hpr_e hlen_e hpost_e hm_e
                      dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                        fullSafetySlice_safe] at hpr_e hlen_e hm_e
                      have hcore_e : se.core = st_b.core :=
                        fullCoreState_agrees_with_scratch (c := c) hpr_e
                      have hdwe := m8_bce_denseInv_of_extPush hdwt_b hlen_e hcore_e
                        hpost_e.1 hpost_e.2.1
                      have htmke : TmkZero se :=
                        htmkt_b.congr (congrArg FullCoreState.cur_vars hcore_e) hpost_e.2.2.2
                      have hsc_e : se.scratch.scratch_buf = s0.scratch.scratch_buf :=
                        hpost_e.2.2.1.trans hscri
                      have hrefse : fullArenaClauseRefs se = fullArenaClauseRefs s0 := by
                        unfold fullArenaClauseRefs fullArenaClauseRefsCore
                        rw [congrArg FullCoreState.arena hcore_e,
                          congrArg FullCoreState.arena_len hcore_e]
                        exact hrefsi
                      dsimp only
                      c0_hsplit
                      · have hwi_ref : wi.toNat ∈ fullArenaClauseRefs se := by
                          rw [hrefse]
                          have hmem := hbce_w.1
                          unfold FullBveBceWeakOk at hmem
                          rw [← hwi_eq] at hmem
                          rw [ite_eq_right (by intro h; exact h hwi_nb)] at hmem
                          exact hmem.1
                        have hwi_wf := hdwe.2.1.arena.refs_wf wi.toNat hwi_ref
                        have hale := hdwe.1.core_ok.arena_len_le
                        have hwi_ar : wi.toNat < se.core.arena.length := by
                          rw [hdwe.1.core_ok.arena_len_arr]; omega
                        have hwi_2ar : (wi.setWidth 64 + 2#64).toNat < se.core.arena.length := by
                          rw [hdwe.1.core_ok.arena_len_arr]; c0_bound
                        have hwi_2ar' :
                            (wi.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 <
                              (se.core.arena.set wi.toNat
                                (se.core.arena[wi.toNat]'hwi_ar ||| 0x00080000#32)).length := by
                          rw [List.length_set, hdwe.1.core_ok.arena_len_arr]
                          simp; c0_bound
                        c0_hsteps!
                        have hmg := m8_bce_markGarb_pres_lits hdwe hwi_ref
                          (ag' := se.core.arena_garbage + 3#64 +
                            (se.core.arena[(wi.setWidth 64 + 2#64).toNat]'hwi_2ar).setWidth 64)
                        let sg : FullState := { se with
                          core := { se.core with
                            arena := se.core.arena.set wi.toNat
                              (fullArenaHdr se wi.toNat ||| 0x00080000#32),
                            arena_garbage := se.core.arena_garbage + 3#64 +
                              (se.core.arena[(wi.setWidth 64 + 2#64).toNat]'hwi_2ar).setWidth 64 }
                          scratch := { se.scratch with bce_cnt := se.scratch.bce_cnt + 1#64 } }
                        have hdwg := m6_fullDenseInvW_with_scratch hmg.1
                          (sc' := sg.scratch) { hdwe.1.scratch_ok with } rfl rfl
                        have hhdr_c : se.core.arena[wi.toNat]'hwi_ar =
                            fullArenaHdr se wi.toNat := by
                          unfold fullArenaHdr fullArenaHdrCore
                          rw [List.getElem?_eq_getElem hwi_ar, Option.getD_some]
                        exact hJcl sg _ ⟨hdwg, htmke,
                          (congrArg FullCoreState.cur_vars hcore_e).trans hcvi,
                          (congrArg FullCoreState.arena_len hcore_e).trans hali,
                          (congrArg FullCoreState.fuel hcore_e).trans hfli,
                          hsc_e, hmg.2.1.trans hrefse, fun r hr => by
                            have hp1 := hmg.2.2 r (hrefse.symm ▸ hr)
                            have hp2 := hperi r hr
                            have hpe : fullArenaClauseSize se r = fullArenaClauseSize si r ∧
                                fullArenaClauseLits se r = fullArenaClauseLits si r := by
                              unfold fullArenaClauseSize fullArenaClauseLits
                                fullArenaClauseLitsCore fullArenaClauseSizeCore
                              rw [congrArg FullCoreState.arena hcore_e]
                              exact ⟨rfl, rfl⟩
                            exact ⟨hp1.1.trans (hpe.1.trans hp2.1),
                              hp1.2.trans (hpe.2.trans hp2.2)⟩,
                          by
                            dsimp only at hm
                            have hwi_z : (wi.setWidth 64).toNat = wi.toNat := m6_zext32_toNat wi
                            have hwi_lt : wi.toNat < 2 ^ 32 := wi.isLt
                            have hhm_ne : wi.toNat ≠ (wi.setWidth 64 + 2#64).toNat := by
                              rw [BitVec.toNat_add, hwi_z,
                                show (2#64 : BitVec 64).toNat = 2 from rfl,
                                Nat.mod_eq_of_lt (by omega)]
                              omega
                            exact m8_bce_hm (w0 := wi) rfl hwi_ar hhm_ne
                              (hw0_2 := hwi_2ar) hhdr_c hm⟩
                      · c0_hsteps!
                        exact hJcl se me ⟨hdwe, htmke,
                          (congrArg FullCoreState.cur_vars hcore_e).trans hcvi,
                          (congrArg FullCoreState.arena_len hcore_e).trans hali,
                          (congrArg FullCoreState.fuel hcore_e).trans hfli,
                          hsc_e, hrefse, fun r hr => by
                            have har_stb : st_b.core.arena = si.core.arena := rfl
                            have hp := hperi r hr
                            unfold fullArenaClauseSize fullArenaClauseLits
                              fullArenaClauseLitsCore fullArenaClauseSizeCore at hp ⊢
                            rw [congrArg FullCoreState.arena hcore_e, har_stb]
                            exact hp, hm_e⟩))
          · c0_hsteps!
            exact hJstep st_b m_t ⟨hdwt_b, htmkt_b, hcvi, hali, hfli, hscri, hrefsi, hperi, hm_t⟩)
    · c0_hsteps!
      exact hQ si mi hdwi htmki hcvi hali hfli hscri hrefsi hperi hmi
  · intro Li hLi; c0_hsteps!
    exact hLi cnt.toNat (0#32, ()) m0
      ⟨s0, Nat.zero_le _, by simp, hdw0, htmk0, rfl, rfl, rfl, rfl, rfl,
        fun _ _ => ⟨rfl, rfl⟩, hm0⟩

/-! ## 3. `full_bve_heap_push_m7_m8_wp` (`m8BveHeapPushSpec`) -/

/-- Certifies `m8BveHeapPushSpec` for `FullM7BveGates.full_bve_heap_push_m7_body` against
`m8BveVarKeySpec`. -/
theorem full_bve_heap_push_m7_m8_wp (Γ : Env)
    (hKey : ∀ a m Q X, m8BveVarKeySpec a m Q X →
      Γ "full_bve_var_key_m7" [i64, i32] [i64] a m Q X)
    (hUp : ∀ a m Q X, FullM6BveFwd.fullBveHeapUpM6Spec a m Q X →
      Γ "full_bve_heap_up_m7" [i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, FullM6BveFwd.fullBveHeapDownM6Spec a m Q X →
      Γ "full_bve_heap_down_m7" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, m8BveHeapPushSpec a m Q X →
      Func.wp Γ FullM7BveGates.full_bve_heap_push_m7_body a m Q X := by
  rintro ⟨h, hlen, v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hl0, hm0, hQ⟩ := m8BveHeapPushSpec_elim hSpec
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hl0.core_ok.cur_vars_le
  have hws1_0 := hl0.scratch_ok.work_stk1_len
  have hss_0 := hl0.scratch_ok.sim_sig_len
  unfold Func.wp FullM7BveGates.full_bve_heap_push_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ hlen s.scratch.work_stk1 s.scratch.sim_sig m0 hws1_0 hss_0 id hm0
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    c0_hsplit
    · c0_hsteps!; exact hQ hlen s.scratch.work_stk1 s.scratch.sim_sig m0 hws1_0 hss_0 id hm0
    · have hhl_le : hlen.toNat ≤ s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
      c0_hsteps_nogrp
      refine wp_call_of_spec _ _ (hKey _ _ _ _ ?_)
      refine m8BveVarKeySpec_intro rfl hl0 hm0 ?_
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
              refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
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
                    refine wp_call_of_spec _ _ (hDown _ _ _ _ ?_)
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
          refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
          refine fullBveHeapUpM6Spec_intro rfl hl2 hm ?_
          intro ws1' m1 hws1' hm1
          c0_hsteps!
          exact hQ (hlen + 1#64) ws1' ss1 m1 hws1' (by simp [ss1, hss_0])
            (fun _ => by omega) hm1

/-! ## 4. `full_elim_bve_fid_m8_wp` (Canonical `FullM3CongBva.m3ElimBveSpec`) -/

private theorem m8_elimDenseInv_with_ws1_ss {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {ws1' : List (BitVec 32)} {ss' : List (BitVec 64)}
    (hws1 : ws1'.length = 2 * c.max_vars) (hss : ss'.length = c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  let sc' : FullScratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' }
  exact (m6_fullDenseInvW_with_scratch hdw (sc' := sc')
    { hdw.1.scratch_ok with work_stk1_len := hws1, sim_sig_len := hss } rfl rfl).toDense

private theorem m8_elimDenseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {scr' : FullScratch}
    (hok : scr'.LengthsOk c) (hll : scr'.last_learned = s.scratch.last_learned)
    (hel : scr'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := scr' } :=
  fullDenseInv_with_scratch_keep h hok hll hel

private theorem m8_elimDenseInv_with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } :=
  fullDenseInv_with_flags h hfl

/-- Certifies canonical `FullM3CongBva.m3ElimBveSpec` for
`FullM7FidelityCore.full_elim_bve_fid_body` against `m8BveHeapPushSpec`. -/
theorem full_elim_bve_fid_m8_wp (Γ : Env)
    (hFlush : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, m8BveHeapPushSpec a m Q X →
      Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X)
    (hPop : ∀ a m Q X, FullM6BveFwd.fullBveHeapPopM6Spec a m Q X →
      Γ "full_bve_heap_pop_m7" [i64, i64] [i32] a m Q X)
    (hNbrs : ∀ a m Q X, FullM3CongBva.m3ElimCollectNbrsSpec a m Q X →
      Γ "full_bve_collect_nbrs_m7" [i64, i32] [i64] a m Q X)
    (hBveVar : ∀ a m Q X, FullFastBveBudgets.fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Func.wp Γ FullM7FidelityCore.full_elim_bve_fid_body a m Q X := by
  rintro ⟨h, bve_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, htmk0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv0_le := hden0.lengths.core_ok.cur_vars_le
  have hmcl0 := hden0.lengths.core_ok.min_clr_len_arr
  unfold Func.wp FullM7FidelityCore.full_elim_bve_fid_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem_c (ci, ()) mc => ∃ mclrc : List (BitVec 32),
      mclrc.length = c.max_vars ∧ ci.toNat ≤ s0.core.cur_vars ∧
      rem_c = s0.core.cur_vars - ci.toNat ∧
      (FullMem c { s0 with core := { s0.core with min_clr := mclrc } } ⋆ R) mc)
    ?_ (fun Lc hLc => by
      c0_hsteps!
      exact hLc s0.core.cur_vars (0#64, ()) m0
        ⟨s0.core.min_clr, hmcl0, Nat.zero_le _, by simp, hm0⟩)
  rintro Lc rem_c ⟨ci, ⟨⟩⟩ mc hLc ⟨mclrc, hmclrc, hci_le, rfl, hmc⟩
  c0_hsplit
  · have hci_lt : ci.toNat < s0.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hmcl_b : ci.toNat < mclrc.length := by omega
    have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps!
    exact hLc (s0.core.cur_vars - (ci + 1#64).toNat) (ci + 1#64, ()) _ (by omega)
      ⟨_, by simp [hmclrc], by omega, rfl, hm⟩
  let sz : FullState := { s0 with core := { s0.core with min_clr := mclrc } }
  have hdenz : FullDenseInv c F0 sz := by
    obtain ⟨F_cur, hw0⟩ := hden0.exists_witness
    exact FullDenseInvW.toDense
      ⟨⟨{ hw0.1.core_ok with min_clr_len_arr := hmclrc }, hw0.1.scratch_ok⟩,
       fullWitnessInv_with_min_clr hw0.2.1 mclrc, hw0.2.2.1, hw0.2.2.2.1,
       hw0.2.2.2.2.1, hw0.2.2.2.2.2.1, hw0.2.2.2.2.2.2⟩
  have htmkz : TmkZero sz := htmk0.congr rfl rfl
  c0_hsteps_nogrp
  refine wp_loop_break_group (brkTs := [i64, i64, .bool, i64]) (lpTs := [i64, i64, .bool, i64])
    (fun (_tr, _hl, _lre, _rd, ()) mb => ∃ sb : FullState,
      FullDenseInv c F0 sb ∧ TmkZero sb ∧ sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sb ⋆ R) mb)
    (fun rem_r (tried, hlen, _lre, round, ()) mr => ∃ sr : FullState,
      round.toNat ≤ 2 ∧ rem_r = 2 - round.toNat ∧
      tried.toNat ≤ bve_lim.toNat ∧ hlen.toNat ≤ sr.core.cur_vars ∧
      FullDenseInv c F0 sr ∧ TmkZero sr ∧ sr.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sr ⋆ R) mr)
    ?_ ?_ ?_
  · rintro _ ⟨_tr, _hl, _lre, _rd, ⟨⟩⟩ mb ⟨sb, hdenb, htmkb, hfub, hmb⟩
    c0_hsteps_nogrp
    refine wp_join0 (P := fun mf => ∃ sf : FullState,
      FullDenseInv c F0 sf ∧ TmkZero sf ∧ sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sf ⋆ R) mf)
      (fun _ mf ⟨sf, hdenf, htmkf, hfuf, hmf⟩ => by
        c0_hsteps!
        · exact hQ 20#64 sf mf hdenf htmkf hfuf (Or.inr rfl)
            (fun _ => hdenf.inconsistent_unsat hc) hmf
        · exact hQ 1#64 sf mf hdenf htmkf hfuf (Or.inl rfl) (fun h => by cases h) hmf)
      (fun Jf hJf => by
        c0_hsplit
        · have hcvb := hdenb.lengths.core_ok.cur_vars_le
          have hflb := hdenb.lengths.core_ok.flags_len
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
            (fun _ comp _ => by
              c0_hsteps_nogrp
              refine wp_join0 (P := fun mj => ∃ sj : FullState,
                  FullDenseInv c F0 sj ∧ TmkZero sj ∧ sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                  (FullMem c sj ⋆ R) mj)
                (fun _ mj h => by c0_hsteps!; exact hJf mj h)
                (fun _ hJc => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join0 (P := fun mj => ∃ sj : FullState,
                        FullDenseInv c F0 sj ∧ TmkZero sj ∧
                        sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj)
                      (fun _ mj h => by c0_hsteps!; exact hJc mj h)
                      (fun _ hJc2 => by
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                            (fun x => (x, ())) (fun _ => True)
                            (fun _ nb0 _ => by
                              c0_hsteps_nogrp
                              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                (fun x => (x, ())) (fun _ => True)
                                (fun _ nb _ => by
                                  c0_hsteps_nogrp
                                  let sb1 : FullState :=
                                    { sb with scratch := { sb.scratch with elim_bound := nb } }
                                  have hden1 : FullDenseInv c F0 sb1 :=
                                    m8_elimDenseInv_with_scratch_keep hdenb
                                      { hdenb.lengths.scratch_ok with
                                        walk_vals_len := hdenb.lengths.scratch_ok.walk_vals_len }
                                      rfl rfl
                                  refine wp_loop_group (ts := [i64])
                                    (fun rem_k (k, ()) mk => ∃ flk : List (BitVec 32),
                                      flk.length = c.max_vars ∧ k.toNat ≤ sb.core.cur_vars ∧
                                      rem_k = sb.core.cur_vars - k.toNat ∧
                                      (FullMem c
                                        { sb1 with core := { sb1.core with flags := flk } } ⋆ R)
                                        mk)
                                    ?_ ?_
                                  · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk
                                      ⟨flk, hflk, hk_le, rfl, hmk⟩
                                    c0_hsplit
                                    · have hk_lt : k.toNat < sb.core.cur_vars := by
                                        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                      have hk_b : k.toNat < flk.length := by omega
                                      have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                                      c0_hsteps!
                                      exact hLk (sb.core.cur_vars - (k + 1#64).toNat)
                                        (k + 1#64, ()) _ (by omega)
                                        ⟨_, by simp [hflk], by omega, rfl, hm⟩
                                    · c0_hsteps!
                                      let sf : FullState :=
                                        { sb1 with core := { sb1.core with flags := flk } }
                                      exact hJc2 mk ⟨sf, m8_elimDenseInv_with_flags hden1 hflk,
                                        htmkb.congr rfl rfl, hfub, hmk⟩
                                  · intro Lk hLk; c0_hsteps!
                                    exact hLk sb.core.cur_vars (0#64, ()) _
                                      ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hm⟩)
                                (fun Jm hJm => by c0_hsplit <;> (c0_hsteps!; exact hJm _ trivial)))
                            (fun Jb hJb => by c0_hsplit <;> (c0_hsteps!; exact hJb _ trivial))
                        · c0_hsteps!; exact hJc2 mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)
                  · c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i64])
                      (fun rem_k (k, ()) mk => ∃ flk : List (BitVec 32),
                        flk.length = c.max_vars ∧ k.toNat ≤ sb.core.cur_vars ∧
                        rem_k = sb.core.cur_vars - k.toNat ∧
                        (FullMem c { sb with core := { sb.core with flags := flk } } ⋆ R) mk)
                      ?_ ?_
                    · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk ⟨flk, hflk, hk_le, rfl, hmk⟩
                      c0_hsplit
                      · have hk_lt : k.toNat < sb.core.cur_vars := by
                          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                        have hk_b : k.toNat < flk.length := by omega
                        have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                        c0_hsteps!
                        exact hLk (sb.core.cur_vars - (k + 1#64).toNat) (k + 1#64, ()) _ (by omega)
                          ⟨_, by simp [hflk], by omega, rfl, hm⟩
                      · c0_hsteps!
                        let sf : FullState := { sb with core := { sb.core with flags := flk } }
                        exact hJc mk ⟨sf, m8_elimDenseInv_with_flags hdenb hflk,
                          htmkb.congr rfl rfl, hfub, hmk⟩
                    · intro Lk hLk; c0_hsteps!
                      exact hLk sb.core.cur_vars (0#64, ()) mb
                        ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hmb⟩))
            (fun Jc hJc => by c0_hsteps! <;> exact hJc _ trivial)
        · c0_hsteps!; exact hJf mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)
  · rintro Br Lr rem_r ⟨tried, hlen, lre, round, ⟨⟩⟩ mr hBr hLr
      ⟨sr, hrd_le, rfl, htr_le, hhl_le, hdenr, htmkr, hfur, hmr⟩
    have hbrk_r : Br (tried, hlen, lre, round, ()) mr :=
      hBr (tried, hlen, lre, round, ()) mr ⟨sr, hdenr, htmkr, hfur, hmr⟩
    c0_hsplit
    · have hrd_lt : round.toNat < 2 := hc
      have hrd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
      c0_hsplit
      · have htr_lt : tried.toNat < bve_lim.toNat := hc
        c0_hsplit
        · c0_hsplit
          · c0_hsplit
            · c0_hsteps_nogrp
              obtain ⟨F_cur, hdwr⟩ := hdenr.exists_witness
              refine wp_call_of_spec _ _ (hFlush _ _ _ _ ?_)
              refine fullDenseFlushUnitsM6Spec_intro rfl hdwr hmr ?_
              intro ok_u su mu hdwu hcvu _ hfuu _ htmku _ _ _ _ _ hfu_uns hmu
              have hdenu : FullDenseInv c F0 su := hdwu.toDense
              have htmku' : TmkZero su := htmkr.congr hcvu htmku
              have hfuu' : su.core.fuel.toNat ≤ s0.core.fuel.toNat := by rw [hfuu]; exact hfur
              c0_hsplit
              · have hcvu_le := hdwu.1.core_ok.cur_vars_le
                have hws1u := hdwu.1.scratch_ok.work_stk1_len
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i64])
                  (fun rem_i (i, ()) mi => ∃ ws1 : List (BitVec 32),
                    ws1.length = 2 * c.max_vars ∧ i.toNat ≤ su.core.cur_vars ∧
                    rem_i = su.core.cur_vars - i.toNat ∧
                    (FullMem c { su with scratch := { su.scratch with work_stk1 := ws1 } } ⋆ R) mi)
                  ?_ ?_
                · rintro Li rem_i ⟨i, ⟨⟩⟩ mi hLi ⟨ws1, hws1, hi_le, rfl, hmi⟩
                  c0_hsplit
                  · have hi_lt : i.toNat < su.core.cur_vars := by
                      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                    have hmv_i : (BitVec.ofNat 64 c.max_vars + i).toNat < ws1.length := by
                      rw [hws1]; c0_bound
                    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                    c0_hsteps!
                    exact hLi (su.core.cur_vars - (i + 1#64).toNat) (i + 1#64, ()) _ (by omega)
                      ⟨_, by simp [hws1], by omega, rfl, hm⟩
                  · let su1 : FullState :=
                      { su with scratch := { su.scratch with work_stk1 := ws1 } }
                    have hdenu1 : FullDenseInv c F0 su1 :=
                      m8_elimDenseInv_with_ws1_ss hdenu hws1 hdwu.1.scratch_ok.sim_sig_len
                    c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i64, i64])
                      (fun rem_p (hl_p, ip, ()) mp => ∃ (ws1p : List (BitVec 32))
                          (ssp : List (BitVec 64)),
                        let sp : FullState :=
                          { su with scratch :=
                            { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                        ws1p.length = 2 * c.max_vars ∧ ssp.length = c.max_vars ∧
                        ip.toNat ≤ su.core.cur_vars ∧ rem_p = su.core.cur_vars - ip.toNat ∧
                        hl_p.toNat ≤ su.core.cur_vars ∧ (FullMem c sp ⋆ R) mp)
                      ?_ ?_
                    · rintro Lp rem_p ⟨hl_p, ip, ⟨⟩⟩ mp hLp
                        ⟨ws1p, ssp, hws1p, hssp, hip_le, rfl, hhlp_le, hmp⟩
                      let sp : FullState :=
                        { su with scratch :=
                          { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                      c0_hsplit
                      · have hip_lt : ip.toNat < su.core.cur_vars := by
                          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                        have hip1 : (ip + 1#64).toNat = ip.toNat + 1 := by c0_bound
                        have hip_fl : ip.toNat < su.core.flags.length := by
                          rw [hdwu.1.core_ok.flags_len]; omega
                        have hip_vl : (ip <<< (1 : Nat)).toNat < su.core.vals.length := by
                          rw [hdwu.1.core_ok.vals_len]; c0_bound
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i64])
                          (α := BitVec 64 × List (BitVec 32) × List (BitVec 64))
                          (fun x => (x.1, ()))
                          (fun x mj =>
                            let sj : FullState :=
                              { su with scratch :=
                                { su.scratch with work_stk1 := x.2.1, sim_sig := x.2.2 } }
                            x.2.1.length = 2 * c.max_vars ∧ x.2.2.length = c.max_vars ∧
                            x.1.toNat ≤ su.core.cur_vars ∧ (FullMem c sj ⋆ R) mj)
                          (fun _ ⟨hl_j, ws1j, ssj⟩ mj ⟨hws1j, hssj, hhlj, hmj⟩ => by
                            c0_hsteps!
                            exact hLp (su.core.cur_vars - (ip + 1#64).toNat)
                              (hl_j, ip + 1#64, ()) mj (by omega)
                              ⟨ws1j, ssj, hws1j, hssj, by omega, rfl, hhlj, hmj⟩)
                          (fun Jp hJp => by
                            c0_hsplit
                            · c0_hsplit
                              · c0_hsteps_nogrp
                                refine wp_call_of_spec _ _ (hPush _ _ _ _ ?_)
                                refine m8BveHeapPushSpec_intro rfl
                                  (m8_elimDenseInv_with_ws1_ss hdenu hws1p hssp).lengths hmp ?_
                                intro hl_n ws1n ssn mn hws1n hssn hhln hmn
                                c0_hsteps!
                                exact hJp (hl_n, ws1n, ssn) mn
                                  ⟨hws1n, hssn, hhln hhlp_le, hmn⟩
                              · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                                  ⟨hws1p, hssp, hhlp_le, hmp⟩
                            · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                                ⟨hws1p, hssp, hhlp_le, hmp⟩)
                      · have hdensp : FullDenseInv c F0 sp :=
                          m8_elimDenseInv_with_ws1_ss hdenu hws1p hssp
                        have htmksp : TmkZero sp := htmku'.congr rfl rfl
                        c0_hsplit
                        · c0_hsteps!
                          exact hBr (tried, hl_p, false, round, ()) mp
                            ⟨sp, hdensp, htmksp, hfuu', hmp⟩
                        · c0_hsteps_nogrp
                          refine wp_loop_break_group
                            (brkTs := [i64, i64, .bool]) (lpTs := [i64, i64, .bool])
                            (fun (tr_b, hl_b, re_b, ()) mb => ∃ sb : FullState,
                              tr_b.toNat ≤ bve_lim.toNat ∧ hl_b.toNat ≤ sb.core.cur_vars ∧
                              FullDenseInv c F0 sb ∧ TmkZero sb ∧
                              sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sb ⋆ R) mb)
                            (fun rem_h (tr_h, hl_h, re_h, ()) mh => ∃ sh : FullState,
                              tr_h.toNat ≤ bve_lim.toNat ∧ hl_h.toNat ≤ sh.core.cur_vars ∧
                              rem_h = (bve_lim.toNat - tr_h.toNat) * (c.max_vars + 1) +
                                hl_h.toNat ∧
                              FullDenseInv c F0 sh ∧ TmkZero sh ∧
                              sh.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sh ⋆ R) mh)
                            ?_ ?_ ?_
                          · rintro _ ⟨tr_b, hl_b, re_b, ⟨⟩⟩ mb
                              ⟨sb, htrb, hhlb, hdenb, htmkb, hfub, hmb⟩
                            c0_hsplit
                            · c0_hsteps!
                              exact hLr (2 - (round + 1#64).toNat)
                                (tr_b, hl_b, re_b, round + 1#64, ()) mb (by omega)
                                ⟨sb, by omega, rfl, htrb, hhlb, hdenb, htmkb, hfub, hmb⟩
                            · c0_hsteps!
                              exact hBr (tr_b, hl_b, re_b, round, ()) mb
                                ⟨sb, hdenb, htmkb, hfub, hmb⟩
                          · rintro Bh Lh rem_h ⟨tr_h, hl_h, re_h, ⟨⟩⟩ mh hBh hLh
                              ⟨sh, htrh, hhlh, rfl, hdenh, htmkh, hfuh, hmh⟩
                            have hbrk_h : Bh (tr_h, hl_h, re_h, ()) mh :=
                              hBh (tr_h, hl_h, re_h, ()) mh
                                ⟨sh, htrh, hhlh, hdenh, htmkh, hfuh, hmh⟩
                            c0_hsplit
                            · have hhl_pos : 0 < hl_h.toNat := hc
                              have hhl_dec : (hl_h - 1#64).toNat = hl_h.toNat - 1 := by c0_bound
                              c0_hsplit
                              · have htrh_lt : tr_h.toNat < bve_lim.toNat := hc
                                have htrh1 : (tr_h + 1#64).toNat = tr_h.toNat + 1 := by c0_bound
                                c0_hsplit
                                · c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps_nogrp
                                      refine wp_call_of_spec _ _ (hPop _ _ _ _ ?_)
                                      refine fullBveHeapPopM6Spec_intro rfl hdenh.lengths hmh ?_
                                      intro v ws1_1 m1 hws1_1 hm1
                                      let s1 : FullState :=
                                        { sh with scratch :=
                                          { sh.scratch with work_stk1 := ws1_1 } }
                                      have hden1 : FullDenseInv c F0 s1 :=
                                        m8_elimDenseInv_with_ws1_ss hdenh hws1_1
                                          hdenh.lengths.scratch_ok.sim_sig_len
                                      have htmk1 : TmkZero s1 := htmkh.congr rfl rfl
                                      have hcv1_le := hden1.lengths.core_ok.cur_vars_le
                                      have hhl_dec1 : (hl_h - 1#64).toNat ≤ s1.core.cur_vars := by
                                        dsimp only [s1]; rw [hhl_dec]; omega
                                      c0_hsplit
                                      · c0_hsteps!
                                        exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                          (by rw [hhl_dec]; omega)
                                          ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                      · c0_hsplit
                                        · c0_hsteps!
                                          exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                            (by rw [hhl_dec]; omega)
                                            ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                        · have hv_lt : v.toNat < s1.core.cur_vars := by
                                            rw [Nat.mod_eq_of_lt
                                              (by omega : s1.core.cur_vars < 2 ^ 64)] at hc
                                            omega
                                          have hv_fl : (v.setWidth 64).toNat <
                                              s1.core.flags.length := by
                                            rw [hden1.lengths.core_ok.flags_len, m6_zext32_toNat]
                                            omega
                                          have hv_vl : (v.setWidth 64 <<< (1 : Nat)).toNat <
                                              s1.core.vals.length := by
                                            rw [hden1.lengths.core_ok.vals_len]; c0_bound
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                              (by rw [hhl_dec]; omega)
                                              ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                          · c0_hsplit
                                            · c0_hsteps!
                                              exact hLh _ (tr_h, hl_h - 1#64, re_h, ()) m1
                                                (by rw [hhl_dec]; omega)
                                                ⟨s1, htrh, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                            · c0_hsteps_nogrp
                                              let fl2 := s1.core.flags.set (v.setWidth 64).toNat
                                                (s1.core.flags[(v.setWidth 64).toNat]'hv_fl &&&
                                                  ~~~16#32)
                                              let s2 : FullState :=
                                                { s1 with core := { s1.core with flags := fl2 } }
                                              have hden2 : FullDenseInv c F0 s2 :=
                                                m8_elimDenseInv_with_flags hden1
                                                  (by simp [fl2, hden1.lengths.core_ok.flags_len])
                                              have htmk2 : TmkZero s2 := htmk1.congr rfl rfl
                                              refine wp_call_of_spec _ _ (hNbrs _ _ _ _ ?_)
                                              refine ⟨c, F0, s2, R, rfl, hden2, htmk2, hm, ?_⟩
                                              intro nn mclr3 ws2_3 m3 _s3_n hl3 hnn_le _ hm3
                                              have hcv2_le := hden2.lengths.core_ok.cur_vars_le
                                              have hnn_mv : nn.toNat ≤ c.max_vars :=
                                                Nat.le_trans hnn_le hcv2_le
                                              let s3 : FullState :=
                                                { s2 with
                                                  core := { s2.core with min_clr := mclr3 },
                                                  scratch :=
                                                    { s2.scratch with work_stk2 := ws2_3 } }
                                              have hden3 : FullDenseInv c F0 s3 :=
                                                fullDenseInv_with_min_clr_work_stk2 hden2
                                                  hl3.core_ok.min_clr_len_arr
                                                  hl3.scratch_ok.work_stk2_len
                                              have htmk3 : TmkZero s3 := htmk2.congr rfl rfl
                                              c0_hsteps_nogrp
                                              refine wp_call_of_spec _ _ (hBveVar _ _ _ _ ?_)
                                              refine ⟨c, F0, s3, R, rfl, hden3, htmk3, hv_lt,
                                                hm3, ?_⟩
                                              intro st s4 m4 hden4 htmk4 hcv4 hfu4 _ hst20 hm4
                                              have hfu4' : s4.core.fuel.toNat ≤
                                                  s0.core.fuel.toNat := Nat.le_trans hfu4 hfuh
                                              have hcv4_le := hden4.lengths.core_ok.cur_vars_le
                                              have hhl_s4 : (hl_h - 1#64).toNat ≤
                                                  s4.core.cur_vars := by
                                                dsimp only [s3, s2, s1] at hcv4
                                                rw [hhl_dec]; omega
                                              have htr_s4 : (tr_h + 1#64).toNat ≤
                                                  bve_lim.toNat := by omega
                                              c0_hsplit
                                              · c0_hsteps!
                                                exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                                  (Or.inr rfl) (fun _ => hst20 hc) hm4
                                              · c0_hsplit
                                                · c0_hsteps!
                                                  exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                                    (Or.inr rfl)
                                                    (fun _ => hden4.inconsistent_unsat hc) hm4
                                                · c0_hsplit
                                                  · c0_hsteps!
                                                    exact hBh (tr_h + 1#64, hl_h - 1#64, re_h, ())
                                                      m4 ⟨s4, htr_s4, hhl_s4, hden4, htmk4,
                                                        hfu4', hm4⟩
                                                  · have hcont_4 : ∀ (hl_f : BitVec 64)
                                                        (re_f : Bool) (sf : FullState)
                                                        (mf : Mem 64),
                                                        hl_f.toNat ≤ sf.core.cur_vars →
                                                        FullDenseInv c F0 sf → TmkZero sf →
                                                        sf.core.fuel.toNat ≤ s0.core.fuel.toNat →
                                                        (FullMem c sf ⋆ R) mf →
                                                        Lh (tr_h + 1#64, hl_f, re_f, ()) mf :=
                                                      fun hl_f re_f sf mf hhlf hdenf htmkf hfuf
                                                          hmf => by
                                                        have hcvf :=
                                                          hdenf.lengths.core_ok.cur_vars_le
                                                        have htr_sub : bve_lim.toNat - tr_h.toNat =
                                                            (bve_lim.toNat - (tr_h + 1#64).toNat) +
                                                              1 := by omega
                                                        refine hLh
                                                          ((bve_lim.toNat - (tr_h + 1#64).toNat) *
                                                            (c.max_vars + 1) + hl_f.toNat)
                                                          (tr_h + 1#64, hl_f, re_f, ()) mf ?_
                                                          ⟨sf, htr_s4, hhlf, rfl, hdenf, htmkf,
                                                            hfuf, hmf⟩
                                                        rw [htr_sub, Nat.add_mul, Nat.one_mul]
                                                        omega
                                                    refine wp_join_state (ts := [i64, .bool])
                                                      (α := BitVec 64 × Bool × FullState)
                                                      (fun x => (x.1, x.2.1, ()))
                                                      (fun x mj =>
                                                        x.1.toNat ≤ x.2.2.core.cur_vars ∧
                                                        FullDenseInv c F0 x.2.2 ∧ TmkZero x.2.2 ∧
                                                        x.2.2.core.fuel.toNat ≤
                                                          s0.core.fuel.toNat ∧
                                                        (FullMem c x.2.2 ⋆ R) mj)
                                                      (fun _ ⟨hl_f, re_f, sf⟩ mf
                                                          ⟨hhlf, hdenf, htmkf, hfuf, hmf⟩ => by
                                                        c0_hsteps!
                                                        exact hcont_4 hl_f re_f sf mf hhlf hdenf
                                                          htmkf hfuf hmf)
                                                      (fun Jn hJn => by
                                                        refine wp_join0 (P := fun mj => mj = m4)
                                                          (fun _ mj hmj => by
                                                            have hmj4 : (FullMem c s4 ⋆ R) mj :=
                                                              hmj ▸ hm4
                                                            let mkFl := @m8_elimDenseInv_with_flags
                                                            let mkWs := @m8_elimDenseInv_with_ws1_ss
                                                            let mkPsh := @m8BveHeapPushSpec_intro
                                                            c0_hsteps_nogrp
                                                            refine wp_join_state_pure
                                                              (ts := [.bool]) (α := Bool)
                                                              (fun b => (b, ())) (fun _ => True)
                                                              (fun _ re_1 _ => by
                                                                c0_hsteps_nogrp
                                                                refine wp_loop_group
                                                                  (ts := [i64, i64])
                                                                  (fun rem_k (hl_k, k, ()) mk =>
                                                                    ∃ sk : FullState,
                                                                      k.toNat ≤ nn.toNat ∧
                                                                      rem_k = nn.toNat - k.toNat ∧
                                                                      hl_k.toNat ≤
                                                                        sk.core.cur_vars ∧
                                                                      sk.core.cur_vars =
                                                                        s4.core.cur_vars ∧
                                                                      FullDenseInv c F0 sk ∧
                                                                      TmkZero sk ∧
                                                                      sk.core.fuel.toNat ≤
                                                                        s0.core.fuel.toNat ∧
                                                                      (FullMem c sk ⋆ R) mk)
                                                                  ?_ ?_
                                                                · rintro Lk rem_k ⟨hl_k, k, ⟨⟩⟩ mk
                                                                    hLk ⟨sk, hk_le, rfl, hhlk, hcvk,
                                                                      hdenk, htmkk, hfuk, hmk⟩
                                                                  have hlkl := hdenk.lengths
                                                                  c0_hsplit
                                                                  · have hk_lt :
                                                                        k.toNat < nn.toNat := hc
                                                                    have hk1 : (k + 1#64).toNat =
                                                                        k.toNat + 1 := by c0_bound
                                                                    have hws2_k :=
                                                                      hlkl.scratch_ok.work_stk2_len
                                                                    have hk_w : k.toNat <
                                                                        sk.scratch.work_stk2.length
                                                                        := by omega
                                                                    let uk :=
                                                                      sk.scratch.work_stk2[
                                                                        k.toNat]'hk_w
                                                                    c0_hsteps_nogrp
                                                                    refine wp_join_state
                                                                      (ts := [i64])
                                                                      (α := BitVec 64 × FullState)
                                                                      (fun x => (x.1, ()))
                                                                      (fun x mj =>
                                                                        x.1.toNat ≤
                                                                          x.2.core.cur_vars ∧
                                                                        x.2.core.cur_vars =
                                                                          s4.core.cur_vars ∧
                                                                        FullDenseInv c F0 x.2 ∧
                                                                        TmkZero x.2 ∧
                                                                        x.2.core.fuel.toNat ≤
                                                                          s0.core.fuel.toNat ∧
                                                                        (FullMem c x.2 ⋆ R) mj)
                                                                      (fun _ ⟨hl_j, sj⟩ mj
                                                                          ⟨hhlj, hcvj, hdenj, htmkj,
                                                                            hfuj, hmj⟩ => by
                                                                        c0_hsteps!
                                                                        exact hLk
                                                                          (nn.toNat -
                                                                            (k + 1#64).toNat)
                                                                          (hl_j, k + 1#64, ()) mj
                                                                          (by omega)
                                                                          ⟨sj, by omega, rfl, hhlj,
                                                                            hcvj, hdenj, htmkj,
                                                                            hfuj, hmj⟩)
                                                                      (fun Jk hJk => by
                                                                        c0_hsplit
                                                                        · have huk_lt : uk.toNat <
                                                                              sk.core.cur_vars := by
                                                                            rw [← hcvk,
                                                                              Nat.mod_eq_of_lt
                                                                                (by omega :
                                                                                  sk.core.cur_vars <
                                                                                    2 ^ 64)] at hc
                                                                            exact hc
                                                                          have hflk_l :=
                                                                            hlkl.core_ok.flags_len
                                                                          have huk_fl :
                                                                              (uk.setWidth
                                                                                64).toNat <
                                                                                sk.core.flags.length
                                                                              := by
                                                                            rw [hflk_l,
                                                                              m6_zext32_toNat]
                                                                            omega
                                                                          c0_hsplit
                                                                          · have hvlk_l :=
                                                                              hlkl.core_ok.vals_len
                                                                            have huk_vl :
                                                                                (uk.setWidth 64 <<<
                                                                                  (1 : Nat)).toNat <
                                                                                sk.core.vals.length
                                                                                := by
                                                                              rw [hvlk_l]; c0_bound
                                                                            c0_hsplit
                                                                            · c0_hsteps_nogrp
                                                                              let u64 :=
                                                                                (uk.setWidth
                                                                                  64).toNat
                                                                              let fl_u :=
                                                                                sk.core.flags.set
                                                                                  u64
                                                                                  (sk.core.flags[
                                                                                    u64]'huk_fl |||
                                                                                    16#32)
                                                                              let su_k :
                                                                                  FullState :=
                                                                                { sk with core :=
                                                                                  { sk.core with
                                                                                    flags :=
                                                                                      fl_u } }
                                                                              have hflu_l :
                                                                                  fl_u.length =
                                                                                    c.max_vars := by
                                                                                simp only [fl_u,
                                                                                  List.length_set,
                                                                                  hflk_l]
                                                                              have hden_u :=
                                                                                mkFl (fl' := fl_u)
                                                                                  hdenk hflu_l
                                                                              refine wp_call_of_spec
                                                                                _ _ (hPush _ _ _ _
                                                                                ?_)
                                                                              refine mkPsh rfl
                                                                                hden_u.lengths
                                                                                hm ?_
                                                                              intro hl_p ws1p ssp
                                                                                mp_ hws1p hssp hhlp
                                                                                hmp_
                                                                              c0_hsteps!
                                                                              let s_pu :
                                                                                FullState :=
                                                                                { su_k with
                                                                                  scratch :=
                                                                                    { su_k.scratch
                                                                                      with
                                                                                      work_stk1 :=
                                                                                        ws1p,
                                                                                      sim_sig :=
                                                                                        ssp } }
                                                                              exact hJk
                                                                                (hl_p, s_pu)
                                                                                mp_
                                                                                ⟨hhlp hhlk, hcvk,
                                                                                 mkWs hden_u hws1p
                                                                                   hssp,
                                                                                 htmkk.congr rfl
                                                                                   rfl,
                                                                                 hfuk, hmp_⟩
                                                                            · c0_hsteps!
                                                                              exact hJk (hl_k, sk)
                                                                                mk ⟨hhlk, hcvk,
                                                                                  hdenk, htmkk,
                                                                                  hfuk, hmk⟩
                                                                          · c0_hsteps!
                                                                            exact hJk (hl_k, sk) mk
                                                                              ⟨hhlk, hcvk, hdenk,
                                                                                htmkk, hfuk, hmk⟩
                                                                        · c0_hsteps!
                                                                          exact hJk (hl_k, sk) mk
                                                                            ⟨hhlk, hcvk, hdenk,
                                                                              htmkk, hfuk, hmk⟩)
                                                                  · c0_hsteps!
                                                                    exact hJn (hl_k, re_1, sk) mk
                                                                      ⟨hhlk, hdenk, htmkk, hfuk,
                                                                        hmk⟩
                                                                · intro Lk hLk; c0_hsteps!
                                                                  exact hLk nn.toNat
                                                                    (hl_h - 1#64, 0#64, ()) mj
                                                                    ⟨s4, Nat.zero_le _, by simp,
                                                                     by omega, rfl, hden4, htmk4,
                                                                     hfu4', hmj4⟩)
                                                              (fun Jre hJre => by
                                                                c0_hsplit <;>
                                                                  (c0_hsteps!;
                                                                    exact hJre _ trivial)))
                                                          (fun Jth hJth => by
                                                            c0_hsplit
                                                            · c0_hsteps!; exact hJth m4 rfl
                                                            · c0_hsplit
                                                              · c0_hsteps!; exact hJth m4 rfl
                                                              · c0_hsteps!
                                                                exact hJn (hl_h - 1#64, re_h, s4) m4
                                                                  ⟨by omega, hden4, htmk4, hfu4',
                                                                    hm4⟩))
                                    · c0_hsteps!; exact hbrk_h
                                  · c0_hsteps!; exact hbrk_h
                                · c0_hsteps!; exact hbrk_h
                              · c0_hsteps!; exact hbrk_h
                            · c0_hsteps!; exact hbrk_h
                          · intro _ Lh _ hLh; c0_hsteps!
                            exact hLh _ (tried, hl_p, false, ()) mp
                              ⟨sp, htr_le, hhlp_le, rfl, hdensp, htmksp, hfuu', hmp⟩
                    · intro Lp hLp; c0_hsteps!
                      exact hLp su.core.cur_vars (0#64, 0#64, ()) mi
                        ⟨ws1, su.scratch.sim_sig, hws1, hdwu.1.scratch_ok.sim_sig_len,
                         Nat.zero_le _, by simp, Nat.zero_le _, hmi⟩
                · intro Li hLi; c0_hsteps!
                  exact hLi su.core.cur_vars (0#64, ()) mu
                    ⟨su.scratch.work_stk1, hws1u, Nat.zero_le _, by simp, hmu⟩
              · c0_hsteps!
                exact hQ 20#64 su mu hdenu htmku' hfuu' (Or.inr rfl)
                  (fun _ => hfu_uns (by simpa using hc)) hmu
            · c0_hsteps!; exact hbrk_r
          · c0_hsteps!; exact hbrk_r
        · c0_hsteps!; exact hbrk_r
      · c0_hsteps!; exact hbrk_r
    · c0_hsteps!; exact hbrk_r
  · intro _ Lr _ hLr; c0_hsteps!
    exact hLr 2 (0#64, 0#64, false, 0#64, ()) mc
      ⟨sz, Nat.zero_le _, rfl, Nat.zero_le _, Nat.zero_le _, hdenz, htmkz, Nat.le_refl _, hmc⟩

end LeanQbe.T.Examples.Kissat.FullM8CoreParity
