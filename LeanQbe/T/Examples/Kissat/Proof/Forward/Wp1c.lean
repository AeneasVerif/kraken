/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Lemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Forward WP Proofs Part 1c (`Proof.Forward.Wp1c`)

`full_fwd_reconnect_irred_m7_wp` (`Src.Forward.full_fwd_reconnect_irred_m7_body`).

Zero legacy imports (`Full*`, `PatchModule`, `Solver`), `0` `@[expose]` on theorems/lemmas,
every file `<= 1,500`L, every decl `<= 450`L, every line `<= 100` cols.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Forward

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Forward
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "fwd_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem fwd_arenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel → r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r + 3 ≤ alen →
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, hr, _ => by simp [fullArenaScanRefs] at hr
  | fuel + 1, pos, r, hfl, hr, hnxt3 => by
    unfold fullArenaScanRefs at hr; split at hr
    · rename_i hle
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      simp only [List.mem_cons] at hr
      unfold fullArenaScanRefs; simp only [hle, ↓reduceIte, List.mem_cons]
      rcases hr with rfl | hr'
      · right
        cases fuel with
        | zero => omega
        | succ _ =>
          unfold fullArenaScanRefs; simp only [hnxt3, ↓reduceIte, List.mem_cons, true_or]
      · exact Or.inr (fwd_arenaScanRefs_next_mem (by omega) hr' hnxt3)
    · simp at hr

/-- Either the next arena clause offset after `r` equals `k.arena_len`, or it belongs to
`fullArenaClauseRefsCore k`. -/
theorem fwd_arenaClauseRefs_next_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k := by
  rcases ha.refs_wf r hr with ⟨_, _, _, _, hlen | h3⟩
  · exact Or.inl hlen
  · exact Or.inr (fwd_arenaScanRefs_next_mem (by omega) hr h3)

/-- Parametric `Func.wp` proof for `full_fwd_reconnect_irred_m7`. -/
theorem full_fwd_reconnect_irred_m7_wp (Γ : Env)
    (hFlush : Γ.Has "full_fwd_flush_large_m7" fullFwdFlushLargeM7Spec)
    (hArenaNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hWatchPush : Γ.Has "full_watch_push" fullWatchPushSpec) :
    ∀ a m Q X, fullFwdReconnectIrredM7Spec a m Q X →
      Func.wp Γ full_fwd_reconnect_irred_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  unfold Func.wp full_fwd_reconnect_irred_m7_body
  c0_hsteps_nogrp
  fwd_call hFlush
  refine fullFwdFlushLargeM7Spec_intro rfl hdw0.1 hdw0.2.1 hdw0.2.2.1 hdw0.2.2.2.1
    hdw0.2.2.2.2.1 hm0 ?_
  intro s1 m1 hlen1 hw1 hlm1 hnd1 hext1 hcv1 hcl1 hdm1 har1 hal1 _ _ _ hfl1 _ hinc1 _ _ _ _ _
    _ _ _ _ _ _ _ _ htmk1 _ _ _ _ _ hm1
  have hdw1 : FullDenseInvW c F0 F_cur s1 :=
    ⟨hlen1, hw1, hlm1, hnd1, hext1, hcl1 ▸ hdw0.2.2.2.2.2.1, hdm1 ▸ hdw0.2.2.2.2.2.2⟩
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem (p, ()) mp => ∃ sp : FullState,
      p.toNat ≤ sp.core.arena_len ∧ rem = sp.core.arena_len - p.toNat ∧
      (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s0.core.cur_vars ∧
      sp.core.arena_len = s0.core.arena_len ∧ sp.core.fuel = s0.core.fuel ∧
      sp.core.inconsistent = s0.core.inconsistent ∧
      sp.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      (FullMem c sp ⋆ R) mp)
    ?_ ?_
  · rintro L rem ⟨p, ⟨⟩⟩ mp hL
      ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hincp, htmkp, hmp⟩
    have hal_le := hdwp.1.core_ok.arena_len_le
    c0_hsplit
    · have hp_lt : p.toNat < sp.core.arena_len := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      c0_hsplit
      · have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hp_mem.resolve_left (by omega)
        have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
        have hp_ar : p.toNat < sp.core.arena.length := by
          rw [hdwp.1.core_ok.arena_len_arr]; omega
        have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
          rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
        have hp32 : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        let hdr_p := sp.core.arena[p.toNat]'hp_ar
        let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
        have hsz_eq : sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
          unfold sz_p fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
            Option.getD_some]
          exact congrArg BitVec.toNat (fwd_getElem_congr (by c0_bound) _ _)
        c0_hsteps_nogrp
        fwd_call hArenaNext
        refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
        have hnb := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
          (cref := p.toNat) hwf_p.1
        have hnp_mem := fwd_arenaClauseRefs_next_mem hdwp.2.1.arena hp_ref
        let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
          (p.setWidth 32).toNat)).setWidth 64
        have hnp_toNat :
            np.toNat = fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
          dsimp only [np]; rw [hp32, fwd_zext32_toNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)]
        c0_hsteps_nogrp
        refine wp_join0 (P := fun mj => ∃ sj : FullState,
            FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
            sj.core.arena_len = s0.core.arena_len ∧ sj.core.fuel = s0.core.fuel ∧
            sj.core.inconsistent = s0.core.inconsistent ∧
            sj.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
            fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
            (FullMem c sj ⋆ R) mj)
          (fun _ mj ⟨sj, hdwj, hcvj, halj, hflj, hincj, htmkj, hrefsj, hmj⟩ => by
            c0_hsteps!
            exact hL (sj.core.arena_len - np.toNat) (np, ()) mj (by omega)
              ⟨sj, by omega, rfl, by rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
               hdwj, hcvj, halj, hflj, hincj, htmkj, hmj⟩)
          (fun Jp hJp => by
            c0_hsplit
            · have hng : fullArenaClauseGarb sp p.toNat = false := by
                unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                rw [fwd_and_garb_zero_of_mask hc]; rfl
              c0_hsplit
              · have hsz3 : 3 ≤ sz_p.toNat := hc
                c0_hsteps_nogrp
                refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                  (fun (sat_b, _kb, ()) ms => ms = mp)
                  (fun rem_k (k, ()) mk => k.toNat ≤ sz_p.toNat ∧
                    rem_k = sz_p.toNat - k.toNat ∧ mk = mp)
                  ?_ ?_ ?_
                · rintro _ ⟨sat_b, _kb, ⟨⟩⟩ ms hm_s
                  subst ms
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i32]) (α := BitVec 32 × FullState)
                    (fun x => (x.1, ()))
                    (fun x mj =>
                      FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
                      x.2.core.arena_len = s0.core.arena_len ∧ x.2.core.fuel = s0.core.fuel ∧
                      x.2.core.inconsistent = s0.core.inconsistent ∧
                      x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                      fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧ (FullMem c x.2 ⋆ R) mj)
                    (fun _ ⟨_, sj⟩ mj h => by c0_hsteps!; exact hJp mj ⟨sj, h⟩)
                    (fun J31 hJ31 => by
                      c0_hsplit
                      · have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                          unfold hdr_p fullArenaHdr fullArenaHdrCore
                          rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                        c0_hsteps!
                        let ag' := sp.core.arena_garbage + 3#64 + sz_p.setWidth 64
                        let ar' := sp.core.arena.set p.toNat (hdr_p ||| 0x00080000#32)
                        let smg : FullState :=
                          { sp with core := { sp.core with arena := ar', arena_garbage := ag' } }
                        have hmg := fwd_denseInvW_markGarb hdwp hp_ref (arena' := ar')
                          (ag' := ag') (by simp [ar', hdwp.1.core_ok.arena_len_arr])
                          (Or.inl (by
                            dsimp only [ar']; rw [hhdr_eq]; exact List.getElem?_set_self hp_ar))
                          (fun i hne _ => by dsimp only [ar']; exact List.getElem?_set_ne hne.symm)
                        exact hJ31 (_, smg) _ ⟨hmg.1, hcvp, halp, hflp, hincp, htmkp, hmg.2, by
                          assumption⟩
                      · c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32]) (α := BitVec 32 × FullState)
                          (fun x => (x.1, ()))
                          (fun x mw =>
                            FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
                            x.2.core.arena_len = s0.core.arena_len ∧ x.2.core.fuel = s0.core.fuel ∧
                            x.2.core.inconsistent = s0.core.inconsistent ∧
                            x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                            fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧
                            (FullMem c x.2 ⋆ R) mw)
                          (fun _ x mw h => by c0_hsteps!; exact hJ31 x mw h)
                          (fun J32 hJ32 => by
                            c0_hsteps_nogrp
                            refine wp_loop_group (ts := [i32])
                              (fun rem_w (k, ()) mw => ∃ sw : FullState,
                                k.toNat ≤ sz_p.toNat ∧ rem_w = sz_p.toNat - k.toNat ∧
                                FullDenseInvW c F0 F_cur sw ∧
                                sw.core.cur_vars = s0.core.cur_vars ∧
                                sw.core.arena = sp.core.arena ∧
                                sw.core.arena_len = s0.core.arena_len ∧
                                sw.core.fuel = s0.core.fuel ∧
                                sw.core.inconsistent = s0.core.inconsistent ∧
                                sw.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                                (FullMem c sw ⋆ R) mw)
                              ?_ ?_
                            · rintro Lw rem_w ⟨k, ⟨⟩⟩ mw hLw
                                ⟨sw, hk_le, rfl, hdww, hcvw, harw, halw, hflw, hincw, htmkw, hmw⟩
                              have hrefsw : fullArenaClauseRefs sw = fullArenaClauseRefs sp := by
                                unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                rw [harw, halw, halp]
                              c0_hsplit
                              · have hk_lt : k.toNat < sz_p.toNat := hc
                                have hpi_ar : (p + 3#64 + k.setWidth 64).toNat <
                                    sw.core.arena.length := by
                                  rw [hdww.1.core_ok.arena_len_arr]; c0_bound
                                have hsz_lt31 : sz_p.toNat < 2 ^ 31 := by omega
                                have hsz_mask : (sz_p &&& 0x7FFFFFFF#32) = sz_p :=
                                  fwd_sz_and_mask_eq hsz_lt31
                                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                                c0_hsteps_nogrp
                                fwd_call hWatchPush
                                refine ⟨c, sw, R, rfl, hdww.1,
                                  (fwd_denseWatchesInv_of_w hdww).layout, fun h => by simp at h,
                                  fun _ => by
                                    dsimp only [Arg.val]
                                    refine ⟨?_, fwd_bv32_ne_sent_of_lt (by rw [hp32]; omega)⟩
                                    rw [show (sp.core.arena[(p + 2).toNat]'hp2_ar &&&
                                        2147483647 : BitVec 32) = sz_p &&& 0x7FFFFFFF#32 from rfl,
                                      hsz_mask]
                                    exact fwd_bv32_ne_sent_of_lt hsz_lt31,
                                  hmw, ?_⟩
                                intro ok wvec' wstk' wlen' wu' wsort' m2 s2 hlen2 hlay2 hoth2 hokt
                                  hokf hm2
                                have hdw2 : FullDenseInvW c F0 F_cur s2 :=
                                  fwd_denseInvW_of_watchPush_occ hdww hlen2 hlay2
                                    fwd_sz_and_mask_no_bin (by rw [hsz_mask]; omega)
                                    (by rw [hp32]; omega) (by rw [hp32, hrefsw]; exact hp_ref)
                                    hoth2
                                    (fun ht => by
                                      obtain ⟨h1, _, h3, h4, h5, h6⟩ := hokt ht
                                      exact ⟨h1, h3, h4, h5, h6 rfl⟩)
                                    (fun hf => (hokf hf).1)
                                c0_hsplit
                                · c0_hsteps!
                                  exact hLw (sz_p.toNat - (k + 1#32).toNat) (k + 1#32, ()) m2
                                    (by omega) ⟨s2, by omega, rfl, hdw2, hcvw, harw, halw, hflw,
                                      hincw, htmkw, hm2⟩
                                · c0_hsteps!
                                  let soom : FullState :=
                                    { s2 with core := { s2.core with oom := 1#64 } }
                                  exact hJ32 (_, soom) _
                                    ⟨fwd_denseInvW_with_oom hdw2 1#64, hcvw, halw, hflw,
                                     hincw, htmkw, hrefsw, by assumption⟩
                              · c0_hsteps!
                                exact hJ32 (_, sw) mw
                                  ⟨hdww, hcvw, halw, hflw, hincw, htmkw, hrefsw, hmw⟩
                            · intro Lw hLw; c0_hsteps!
                              exact hLw sz_p.toNat (0#32, ()) mp
                                ⟨sp, Nat.zero_le _, by simp, hdwp, hcvp, rfl, halp, hflp, hincp,
                                 htmkp, hmp⟩))
                · rintro Bk Lk rem_k ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hk_le, rfl, hmk_eq⟩
                  subst mk
                  c0_hsplit
                  · have hk_lt : k.toNat < sz_p.toNat := hc
                    have hpi_ar : (p + 3#64 + k.setWidth 64).toNat < sp.core.arena.length := by
                      rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                    have hcl_lt : (sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'
                        hpi_ar).toNat < 2 * sp.core.cur_vars := by
                      have hmem : (sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'
                          hpi_ar).toNat ∈ fullArenaClauseLitsCore sp.core p.toNat := by
                        rw [mem_fullArenaClauseLitsCore_iff (by
                          rw [hdwp.1.core_ok.arena_len_arr]; omega)]
                        exact ⟨k.toNat, by omega, congrArg BitVec.toNat
                          (fwd_getElem_congr (by c0_bound) _ _)⟩
                      exact hdwp.2.1.arena.lits_lt p.toNat hp_ref hng _ hmem
                    have hcl_v : ((sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'
                        hpi_ar).setWidth 64).toNat < sp.core.vals.length := by
                      rw [hdwp.1.core_ok.vals_len]; have := hdwp.1.core_ok.cur_vars_le; c0_bound
                    c0_hsplit
                    · c0_hsteps!; exact hBk (true, k, ()) mp rfl
                    · c0_hsteps!
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      exact hLk (sz_p.toNat - (k + 1#32).toNat) (k + 1#32, ()) mp (by omega)
                        ⟨by omega, rfl, rfl⟩
                  · c0_hsteps!; exact hBk (false, k, ()) mp rfl
                · intro _ Lk _ hLk; c0_hsteps!
                  exact hLk sz_p.toNat (0#32, ()) mp ⟨Nat.zero_le _, by simp, rfl⟩
              · c0_hsteps!
                exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, hincp, htmkp, rfl, hmp⟩
            · c0_hsteps!
              exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, hincp, htmkp, rfl, hmp⟩)
      · c0_hsteps!; exact hQ sp mp hdwp hcvp halp hflp hincp htmkp hmp
    · c0_hsteps!; exact hQ sp mp hdwp hcvp halp hflp hincp htmkp hmp
  · intro L hL; c0_hsteps!
    exact hL s1.core.arena_len (0#64, ()) m1
      ⟨s1, Nat.zero_le _, by simp, by
        by_cases hz : s1.core.arena_len = 0
        · exact Or.inl hz.symm
        · exact Or.inr (fwd_zero_mem_arenaRefs hdw1.2.1.arena (Nat.pos_of_ne_zero hz)),
       hdw1, hcv1, hal1, hfl1, hinc1, htmk1, hm1⟩

end LeanQbe.T.Examples.Kissat.Proof.Forward
