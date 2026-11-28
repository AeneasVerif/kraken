/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Lemmas
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp1c
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Forward WP Proofs Part 4 (`Proof.Forward.Wp4`)

`full_forward_sub_m7_wp` (`fullForwardSubM7Spec`).

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
open LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
open LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "fwd_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Helpers -/

private theorem fwd_sub_lit_var_lt {p : BitVec 64} {hdr' : BitVec 32}
    {ar fl : List (BitVec 32)} {acap mv cv d : Nat}
    (hlen : ar.length = acap) (hflen : fl.length = mv) (hp_lt : p.toNat < acap)
    (_hd3 : 3 ≤ d) (hpd : p.toNat + d < acap) (hcv_le : cv ≤ mv)
    (hcv_lt : mv < 2 * 2 ^ 28) (hcap_lt : acap < 2 * 2 ^ 28)
    (hpd_ar : (p + BitVec.ofNat 64 d).toNat < (ar.set p.toNat hdr').length)
    (hc : ((ar.set p.toNat hdr')[(p.toNat + d) % 2 ^ 64]'(by
      rw [List.length_set, hlen, Nat.mod_eq_of_lt (by omega)]; omega)).toNat / 2 < cv % 2 ^ 64) :
    (((ar.set p.toNat hdr')[(p + BitVec.ofNat 64 d).toNat]'hpd_ar >>> (1 : Nat)).setWidth 64).toNat
      < fl.length := by
  have hpd_mod : (p + BitVec.ofNat 64 d).toNat = (p.toNat + d) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  have har_eq := fwd_getElem_congr hpd_mod.symm
    (by rw [List.length_set, hlen, Nat.mod_eq_of_lt (by omega)]; omega) hpd_ar
  have hsh : (((ar.set p.toNat hdr')[(p + BitVec.ofNat 64 d).toNat]'hpd_ar >>> (1 : Nat)) :
      BitVec 32).toNat =
      ((ar.set p.toNat hdr')[(p + BitVec.ofNat 64 d).toNat]'hpd_ar).toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [har_eq, Nat.mod_eq_of_lt (by omega : cv < 2 ^ 64)] at hc
  rw [fwd_zext32_toNat, hflen, hsh]; omega

private theorem fwd_sub_lit_var_lt' {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {fl : List (BitVec 32)} {p : BitVec 64} {cv_b d : Nat}
    (hdw : FullDenseInvW c F0 F_cur sp) (hp_ar : p.toNat < sp.core.arena.length)
    (hflen : fl.length = c.max_vars) (hcv_eq : cv_b = sp.core.cur_vars)
    (_hp_lt : p.toNat < sp.core.arena_len) (hd3 : 3 ≤ d)
    (hpd : p.toNat + d < sp.core.arena_len)
    (hpd_ar : (p + BitVec.ofNat 64 d).toNat <
      (sp.core.arena.set p.toNat ((sp.core.arena[p.toNat]'hp_ar) &&& ~~~0x01000000#32)).length)
    (hc : ((sp.core.arena.set p.toNat ((sp.core.arena[p.toNat]'hp_ar) &&& ~~~0x01000000#32))[
      (p.toNat + d) % 2 ^ 64]'(by
        have := hdw.1.core_ok.arena_len_le
        rw [List.length_set, hdw.1.core_ok.arena_len_arr,
          Nat.mod_eq_of_lt (by have := c.harena; unfold dimacsBound at this; omega)]
        omega)).toNat / 2 < cv_b % 2 ^ 64) :
    (((sp.core.arena.set p.toNat ((sp.core.arena[p.toNat]'hp_ar) &&& ~~~0x01000000#32))[
      (p + BitVec.ofNat 64 d).toNat]'hpd_ar >>> (1 : Nat)).setWidth 64).toNat < fl.length := by
  have harc := c.harena; have hmx := c.hmaxv; unfold dimacsBound at harc hmx
  have hal := hdw.1.core_ok.arena_len_le; subst hcv_eq
  exact fwd_sub_lit_var_lt hdw.1.core_ok.arena_len_arr hflen (by omega) hd3 (by omega)
    hdw.1.core_ok.cur_vars_le (by omega) (by omega) hpd_ar hc

private theorem fwd_sub_denseInvW_of_flushLarge {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s3 s4 : FullState} (hdw3 : FullDenseInvW c F0 F_cur s3)
    (hlen4 : s4.LengthsOk c) (hw4 : FullWitnessInv c F0 F_cur s4.core)
    (hlm4 : FullLitMarksClear c s4) (hnd4 : FullArenaVarsNodup s4)
    (hext4 : FullExtScratchOk c s4) (hcl4 : s4.core.cur_level = s3.core.cur_level)
    (hdm4 : s4.core.dense_mode = s3.core.dense_mode) : FullDenseInvW c F0 F_cur s4 :=
  ⟨hlen4, hw4, hlm4, hnd4, hext4, hcl4.trans hdw3.2.2.2.2.2.1, hdm4 ▸ hdw3.2.2.2.2.2.2⟩

private def FwdClearInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 sl sp : FullState) (R : Mem 64 → Prop) (mj : Mem 64) : Prop :=
  ∃ sj : FullState,
    FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
    sj.core.arena_len = sl.core.arena_len ∧ sj.core.fuel = s0.core.fuel ∧
    fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧ (FullMem c sj ⋆ R) mj

/-! ## 2. `full_forward_sub_m7_wp` -/

/-- Parametric `Func.wp` proof for `full_forward_sub_m7`. -/
theorem full_forward_sub_m7_wp (Γ : Env)
    (hDedup : Γ.Has "full_fwd_dedup_bins" Proof.Forward.Spec.fullFwdDedupBinsSpec)
    (hFlushUnits : Γ.Has "full_dense_flush_units_m7" fullDenseFlushUnitsSpec)
    (hCollectSort : Γ.Has "full_fwd_collect_sort_m7" fullFwdCollectSortM7Spec)
    (hFlushLarge : Γ.Has "full_fwd_flush_large_m7" fullFwdFlushLargeM7Spec)
    (hCheckCl : Γ.Has "full_fwd_check_cl_m7" fullFwdCheckClM7Spec)
    (hConnectSub : Γ.Has "full_fwd_connect_subsumer_m7" fullFwdConnectSubsumerM7Spec)
    (hArenaNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hReconnect : Γ.Has "full_fwd_reconnect_irred_m7" fullFwdReconnectIrredM7Spec) :
    ∀ a m Q X, fullForwardSubM7Spec a m Q X → Func.wp Γ full_forward_sub_m7_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X hspec
  obtain ⟨c, F0, s0, R, rfl, hd0, hm0, hQ⟩ := fullForwardSubM7Spec_elim hspec
  have hmx := c.hmaxv; have harc := c.harena; have hrc := c.hred; unfold dimacsBound at hmx harc hrc
  obtain ⟨F_cur, hdw0⟩ := hd0.exists_witness
  let hw0 := hdw0.2.1
  unfold Func.wp full_forward_sub_m7_body
  c0_hsplit
  · c0_hsteps_nogrp; fwd_call hReconnect
    refine fullFwdReconnectIrredM7Spec_intro rfl hdw0 hm0 ?_
    intro s1 m1 hdw1 hcv1 _ hfl1 _ _ hm1
    c0_hsteps!; exact hQ 1#64 s1 m1 hdw1.toDense hcv1 hfl1 (Or.inl rfl) (by simp) hm1
  · c0_hsteps_nogrp; fwd_call hDedup; refine ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, ?_⟩
    intro ok1 s1 m1 hdw1 hcv1 hfl1 hf1 hm1
    c0_hsplit
    · c0_hsteps_nogrp; fwd_call hFlushUnits
      refine ⟨c, F0, F_cur, s1, R, rfl, hdw1, hm1, ?_⟩
      intro ok2 s2 m2 hdw2 hcv2 _ hfl2 _ _ _ _ _ _ _ hf2 hm2
      have hsp_lt : s2.core.propagated < 2 ^ 64 := by
        have := hdw2.1.core_ok.propagated_le; have := hdw2.1.core_ok.trail_end_le
        have := hdw2.1.core_ok.cur_vars_le; omega
      c0_hsplit
      · c0_hsteps_nogrp; fwd_call hCollectSort
        refine fullFwdCollectSortM7Spec_intro rfl hdw2 hm2 ?_
        intro ncand s3 m3 hdw3 hcv3 hal3 hfl3 _ _ _ hnc_le hrr3 hm3
        c0_hsplit
        · c0_hsteps_nogrp; fwd_call hReconnect
          refine fullFwdReconnectIrredM7Spec_intro rfl hdw3 hm3 ?_
          intro s3r m3r hdw3r hcv3r _ hfl3r _ _ hm3r
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ()))
            (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
            (fun _ r ⟨hr_disj, hr20⟩ => by
              c0_hsteps!
              exact hQ r s3r m3r hdw3r.toDense (hcv3r.trans (hcv3.trans (hcv2.trans hcv1)))
                (hfl3r.trans (hfl3.trans (hfl2.trans hfl1))) hr_disj hr20 hm3r)
            (fun J7 hJ7 => by
              c0_hsplit
              · c0_hsteps!; exact hJ7 20#64 ⟨Or.inr rfl, fun _ =>
                  hdw3r.2.1.ext_sound.2 (hdw3r.2.1.inconsistent_sound hc)⟩
              · c0_hsteps!; exact hJ7 1#64 ⟨Or.inl rfl, by simp⟩)
        · c0_hsteps_nogrp; fwd_call hFlushLarge
          refine fullFwdFlushLargeM7Spec_intro rfl hdw3.1 hdw3.2.1 hdw3.2.2.1 hdw3.2.2.2.1
            hdw3.2.2.2.2.1 hm3 ?_
          intro s4 m4 hlen4 hw4 hlm4 hnd4 hext4 hcv4 hcl4 hdm4 har4 hal4
            _ _ _ hfl4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrr4 _ _ _ _ _ _ hm4
          have hdw4 : FullDenseInvW c F0 F_cur s4 :=
            fwd_sub_denseInvW_of_flushLarge hdw3 hlen4 hw4 hlm4 hnd4 hext4 hcl4 hdm4
          have hrr4_ok : ∀ k < ncand.toNat,
              (s4.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s4 := fun k hk => by
            rw [show s4.scratch.red_refs = s3.scratch.red_refs from hrr4,
              show fullArenaClauseRefs s4 = fullArenaClauseRefs s3 from by
                unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, hal4]]
            exact hrr3 k hk
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64, i64])
            (fun r_lp (i, rem, ()) ml => ∃ sl : FullState,
              i.toNat ≤ ncand.toNat ∧ r_lp = ncand.toNat - i.toNat ∧
              FullDenseInvW c F0 F_cur sl ∧ sl.core.cur_vars = s0.core.cur_vars ∧
              sl.core.fuel = s0.core.fuel ∧ fullArenaClauseRefs sl = fullArenaClauseRefs s4 ∧
              sl.scratch.red_refs = s4.scratch.red_refs ∧ (FullMem c sl ⋆ R) ml) ?_ ?_
          · rintro L r_lp ⟨i, rem, ⟨⟩⟩ ml hL ⟨sl, hi_le, rfl, hdwl, hcvl, hfll, hrefsl, hrrl, hml⟩
            refine wp_join0 (P := fun mb => mb = ml)
              (fun _ mb hmb => by
                rcases hmb.symm with rfl
                refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                  (fun sf mf => FullDenseInvW c F0 F_cur sf ∧ sf.core.cur_vars = s0.core.cur_vars ∧
                    sf.core.fuel = s0.core.fuel ∧ (FullMem c sf ⋆ R) mf)
                  (fun _ sf mf ⟨hdwf, hcvf, hflf, hmf⟩ => by
                    c0_hsteps_nogrp; c0_hsplit
                    · c0_hsteps!; exact hQ 20#64 sf mf hdwf.toDense hcvf hflf (Or.inr rfl)
                        (fun _ => hdwf.2.1.ext_sound.2 (hdwf.2.1.inconsistent_sound hc)) hmf
                    · c0_hsteps_nogrp; fwd_call hReconnect
                      refine fullFwdReconnectIrredM7Spec_intro rfl hdwf hmf ?_
                      intro s5 m5 hdw5 hcv5 _ hfl5 _ _ hm5
                      refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                        (fun s5p m5p => FullDenseInvW c F0 F_cur s5p ∧
                          s5p.core.cur_vars = s0.core.cur_vars ∧ s5p.core.fuel = s0.core.fuel ∧
                          (FullMem c s5p ⋆ R) m5p)
                        (fun _ s5p m5p ⟨hdw5p, hcv5p, hfl5p, hm5p⟩ => by
                          c0_hsteps_nogrp; fwd_call hFlushUnits
                          refine ⟨c, F0, F_cur, s5p, R, rfl, hdw5p, hm5p, ?_⟩
                          intro ok6 s6 m6 hdw6 hcv6 _ hfl6 _ _ _ _ _ _ _ hf6 hm6
                          c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                              (fun r => (r, ())) (fun r => (r = 1#64 ∨ r = 20#64) ∧
                                (r = 20#64 → F0.Unsat))
                              (fun _ r ⟨hr_disj, hr20⟩ => by
                                c0_hsteps!; exact hQ r s6 m6 hdw6.toDense (hcv6.trans hcv5p)
                                  (hfl6.trans hfl5p) hr_disj hr20 hm6)
                              (fun J20 hJ20 => by
                                c0_hsplit
                                · c0_hsteps!; exact hJ20 20#64 ⟨Or.inr rfl, fun _ =>
                                    hdw6.2.1.ext_sound.2 (hdw6.2.1.inconsistent_sound hc)⟩
                                · c0_hsteps!; exact hJ20 1#64 ⟨Or.inl rfl, by simp⟩)
                          · c0_hsteps!; exact hQ 20#64 s6 m6 hdw6.toDense (hcv6.trans hcv5p)
                              (hfl6.trans hfl5p) (Or.inr rfl)
                              (fun _ => hf6 (by simpa using hc)) hm6)
                        (fun Jrw hJrw => by
                          c0_hsplit
                          · c0_hsplit
                            · have hte5_lt : s5.core.trail_end < 2 ^ 64 := by
                                have := hdw5.1.core_ok.trail_end_le
                                have := hdw5.1.core_ok.cur_vars_le; omega
                              have hle_te : s2.core.propagated ≤ s5.core.trail_end := by
                                rw [Nat.mod_eq_of_lt hsp_lt, Nat.mod_eq_of_lt hte5_lt] at hc
                                exact hc
                              c0_hsteps!
                              exact hJrw { s5 with core := { s5.core with
                                propagated := s2.core.propagated } } _
                                ⟨fwd_denseInvW_with_prop hdw5 hle_te,
                                 hcv5.trans hcvf, hfl5.trans hflf, hm⟩
                            · c0_hsteps!
                              exact hJrw s5 m5 ⟨hdw5, hcv5.trans hcvf, hfl5.trans hflf, hm5⟩
                          · c0_hsteps!
                            exact hJrw s5 m5 ⟨hdw5, hcv5.trans hcvf, hfl5.trans hflf, hm5⟩))
                  (fun Jc hJc => by
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsplit
                        · have hcvl_le := hdwl.1.core_ok.cur_vars_le
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i64])
                            (fun rem_v (v, ()) mv => ∃ fl_v : List (BitVec 32),
                              fl_v.length = c.max_vars ∧ v.toNat ≤ sl.core.cur_vars ∧
                              rem_v = sl.core.cur_vars - v.toNat ∧
                              (FullMem c { sl with core := { sl.core with flags := fl_v } } ⋆ R) mv)
                            ?_ ?_
                          · rintro Lv rem_v ⟨v, ⟨⟩⟩ mv hLv ⟨fl_v, hflv, hv_le, rfl, hmv⟩
                            c0_hsplit
                            · have hv_lt : v.toNat < sl.core.cur_vars := by
                                rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                              have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
                              c0_hsteps!
                              exact hLv (sl.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) _
                                (by omega) ⟨_, by simp [hflv], by omega, rfl, hm⟩
                            · let sv0 : FullState :=
                                { sl with core := { sl.core with flags := fl_v } }
                              have hdw_v0 := fwd_denseInvW_with_flags hdwl hflv
                              c0_hsteps_nogrp
                              refine wp_loop_group (ts := [i64])
                                (fun rem_p (p, ()) mp => ∃ sp : FullState,
                                  p.toNat ≤ sp.core.arena_len ∧
                                  rem_p = sp.core.arena_len - p.toNat ∧
                                  (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
                                  FullDenseInvW c F0 F_cur sp ∧
                                  sp.core.cur_vars = s0.core.cur_vars ∧
                                  sp.core.arena_len = sl.core.arena_len ∧
                                  sp.core.fuel = s0.core.fuel ∧ (FullMem c sp ⋆ R) mp)
                                ?_ ?_
                              · rintro Lp rem_p ⟨p, ⟨⟩⟩ mp hLp
                                  ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hmp⟩
                                have hal_p := hdwp.1.core_ok.arena_len_le
                                c0_hsplit
                                · have hp_lt : p.toNat < sp.core.arena_len := by
                                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                  have hp_ref := hp_mem.resolve_left (by omega)
                                  have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
                                  have hp_ar : p.toNat < sp.core.arena.length := by
                                    rw [hdwp.1.core_ok.arena_len_arr]; omega
                                  have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
                                    rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                                  have hp32 : (p.setWidth 32).toNat = p.toNat := by
                                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                                  let hdr_p := sp.core.arena[p.toNat]'hp_ar
                                  let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
                                  have hsz_p :
                                      sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
                                    unfold sz_p fullArenaClauseSizeCore
                                    rw [List.getElem?_eq_getElem (by
                                      rw [hdwp.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                                    exact congrArg BitVec.toNat
                                      (fwd_getElem_congr (by c0_bound) _ _)
                                  c0_hsteps_nogrp; fwd_call hArenaNext
                                  dsimp only [vals, Arg.val]
                                  refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
                                  have hnb := fullArenaNextOff_bounds (ar := sp.core.arena)
                                    (alen := sp.core.arena_len) (cref := p.toNat) hwf_p.1
                                  have hnp_mem :=
                                    fwd_arenaClauseRefs_next_mem hdwp.2.1.arena hp_ref
                                  let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena
                                    sp.core.arena_len (p.setWidth 32).toNat)).setWidth 64
                                  have hnp_toNat : np.toNat =
                                      fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
                                    dsimp only [np]; rw [hp32, fwd_zext32_toNat, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega)]
                                  c0_hsteps_nogrp
                                  refine wp_join0 (P := FwdClearInv c F0 F_cur s0 sl sp R)
                                    (fun _ mj ⟨sj, hdwj, hcvj, halj, hflj, hrefsj, hmj⟩ => by
                                      c0_hsteps!
                                      exact hLp (sj.core.arena_len - np.toNat) (np, ()) mj
                                        (by omega) ⟨sj, by omega, rfl, by
                                          rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
                                         hdwj, hcvj, halj, hflj, hmj⟩)
                                    (fun Jp hJp => by
                                      c0_hsplit
                                      · c0_hsteps_nogrp
                                        let v' := hdr_p &&& ~~~0x01000000#32
                                        let sc : FullState :=
                                          { sp with core := { sp.core with
                                            arena := sp.core.arena.set p.toNat v' } }
                                        have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                                          unfold hdr_p fullArenaHdr fullArenaHdrCore
                                          rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                                        have hcb := fwd_bit24_clear_pres hdr_p
                                        have hset := fwd_denseInvW_set_hdr_bit24 hdwp hp_ref
                                          (v' := v') (by rw [← hhdr_eq]; exact hcb.1)
                                          (by rw [← hhdr_eq]; exact hcb.2)
                                        refine wp_join0 (P := FwdClearInv c F0 F_cur s0 sl sp R)
                                          (fun _ mj hmj => hJp mj hmj)
                                          (fun J52 hJ52 => by
                                            c0_hsplit
                                            · c0_hsteps_nogrp
                                              refine wp_loop_group (ts := [i32])
                                                (fun rem_k (k, ()) mk => ∃ fl_k : List (BitVec 32),
                                                  fl_k.length = c.max_vars ∧ k.toNat ≤ sz_p.toNat ∧
                                                  rem_k = sz_p.toNat - k.toNat ∧
                                                  (FullMem c { sc with core :=
                                                    { sc.core with flags := fl_k } } ⋆ R) mk) ?_ ?_
                                              · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk
                                                  ⟨fl_k, hflk, hk_le, rfl, hmk⟩
                                                c0_hsplit
                                                · have hk_lt : k.toNat < sz_p.toNat := hc
                                                  have hpi_ar : (p + 3#64 + k.setWidth 64).toNat <
                                                      sc.core.arena.length := by
                                                    rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                                                    c0_bound
                                                  c0_hsteps_nogrp
                                                  refine wp_join0
                                                    (P := fun mj => ∃ fl' : List (BitVec 32),
                                                      fl'.length = c.max_vars ∧ (FullMem c
                                                        { sc with core :=
                                                          { sc.core with flags := fl' } } ⋆ R) mj)
                                                    (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                                      c0_hsteps!
                                                      exact hLk (sz_p.toNat - (k + 1#32).toNat)
                                                        (k + 1#32, ()) mj (by omega)
                                                        ⟨fl', hfl', by omega, rfl, hmj⟩)
                                                    (fun J65 hJ65 => by
                                                      c0_hsplit
                                                      · have hpd_eq : p + 3#64 + k.setWidth 64 =
                                                            p + BitVec.ofNat 64 (3 + k.toNat) := by
                                                          apply BitVec.eq_of_toNat_eq
                                                          rw [BitVec.toNat_add, BitVec.toNat_add,
                                                            BitVec.toNat_add, fwd_zext32_toNat]
                                                          simp [BitVec.toNat_ofNat, Nat.add_assoc]
                                                        have hlv_lt : ((sc.core.arena[(p + 3#64 +
                                                            k.setWidth 64).toNat]'hpi_ar >>>
                                                            (1 : Nat)).setWidth 64).toNat <
                                                            fl_k.length := by
                                                          simpa only [hpd_eq] using
                                                            fwd_sub_lit_var_lt' hdwp hp_ar hflk
                                                              (hcvl.trans hcvp.symm) hp_lt
                                                              (d := 3 + k.toNat) (by omega)
                                                              (by omega)
                                                              (by rw [← hpd_eq]; exact hpi_ar)
                                                              (by dsimp only [sc] at hc
                                                                  simpa only [Nat.add_assoc,
                                                                    show (3 : BitVec 64).toNat = 3
                                                                      from rfl] using hc)
                                                        c0_hsteps!
                                                        exact hJ65 _ ⟨_, by simp [hflk], hm⟩
                                                      · c0_hsteps!; exact hJ65 mk ⟨fl_k, hflk, hmk⟩)
                                                · c0_hsteps!
                                                  exact hJ52 mk ⟨{ sc with core :=
                                                    { sc.core with flags := fl_k } },
                                                    fwd_denseInvW_with_flags hset.1 hflk,
                                                    hcvp, halp, hflp, hset.2.1, hmk⟩
                                              · intro Lk hLk; c0_hsteps!
                                                exact hLk sz_p.toNat (0#32, ()) m
                                                  ⟨sc.core.flags, hset.1.1.core_ok.flags_len,
                                                   Nat.zero_le _, by simp, hm⟩
                                            · refine wp_join0
                                                (P := FwdClearInv c F0 F_cur s0 sl sp R)
                                                (fun _ mj hmj => hJ52 mj hmj)
                                                (fun J55p hJ55p => by
                                                  c0_hsplit
                                                  · have hsz2 : 2 ≤ sz_p.toNat := hc
                                                    have hp3_ar : (p + 3#64).toNat <
                                                        sc.core.arena.length := by
                                                      rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                    have hp4_ar : (p + 4#64).toNat <
                                                        sc.core.arena.length := by
                                                      rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                    c0_hsteps_nogrp
                                                    refine wp_join_state (ts := [])
                                                      (α := List (BitVec 32)) (fun _ => ())
                                                      (fun fl1 m1 => fl1.length = c.max_vars ∧
                                                        (FullMem c { sc with core :=
                                                          { sc.core with flags := fl1 } } ⋆ R) m1)
                                                      (fun _ fl1 m1 ⟨hfl1, hm1⟩ => by
                                                        c0_hsteps_nogrp
                                                        refine wp_join_state (ts := [])
                                                          (α := List (BitVec 32)) (fun _ => ())
                                                          (fun fl2 m2 => fl2.length = c.max_vars ∧
                                                            (FullMem c { sc with core :=
                                                              { sc.core with flags := fl2 } } ⋆ R)
                                                              m2)
                                                          (fun _ fl2 m2 ⟨hfl2, hm2⟩ => by
                                                            c0_hsteps!
                                                            exact hJ55p m2 ⟨{ sc with core :=
                                                              { sc.core with flags := fl2 } },
                                                              fwd_denseInvW_with_flags hset.1 hfl2,
                                                              hcvp, halp, hflp, hset.2.1, hm2⟩)
                                                          (fun J68 hJ68 => by
                                                            c0_hsplit
                                                            · have hv1_lt :
                                                                ((sc.core.arena[(p + 4#64).toNat]'
                                                                  hp4_ar >>>
                                                                  (1 : Nat)).setWidth 64).toNat <
                                                                  fl1.length :=
                                                                fwd_sub_lit_var_lt' hdwp hp_ar hfl1
                                                                  (hcvl.trans hcvp.symm) hp_lt
                                                                  (d := 4) (by omega) (by omega)
                                                                  hp4_ar hc
                                                              c0_hsteps!
                                                              exact hJ68 _ _ ⟨by simp [hfl1], hm⟩
                                                            · c0_hsteps!
                                                              exact hJ68 fl1 m1 ⟨hfl1, hm1⟩))
                                                      (fun J67 hJ67 => by
                                                        c0_hsplit
                                                        · have hv0_lt :
                                                            ((sc.core.arena[(p + 3#64).toNat]'
                                                              hp3_ar >>>
                                                              (1 : Nat)).setWidth 64).toNat <
                                                              sc.core.flags.length :=
                                                            fwd_sub_lit_var_lt' hdwp hp_ar
                                                              hset.1.1.core_ok.flags_len
                                                              (hcvl.trans hcvp.symm) hp_lt (d := 3)
                                                              (by omega) (by omega) hp3_ar hc
                                                          c0_hsteps!; exact hJ67 _ _ ⟨by
                                                            simp [hset.1.1.core_ok.flags_len], hm⟩
                                                        · c0_hsteps!; exact hJ67 sc.core.flags m
                                                            ⟨hset.1.1.core_ok.flags_len, hm⟩)
                                                  · c0_hsteps!; exact hJ55p m
                                                      ⟨sc, hset.1, hcvp, halp, hflp, hset.2.1, hm⟩))
                                      · c0_hsteps!
                                        exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, rfl, hmp⟩)
                                · c0_hsteps!; exact hJc sp mp ⟨hdwp, hcvp, hflp, hmp⟩
                              · intro Lp hLp; c0_hsteps!; exact hLp sv0.core.arena_len (0#64, ()) mv
                                  ⟨sv0, Nat.zero_le _, by simp, by
                                    by_cases hz : sv0.core.arena_len = 0
                                    · exact Or.inl hz.symm
                                    · exact Or.inr (fwd_zero_mem_arenaRefs hdw_v0.2.1.arena
                                        (Nat.pos_of_ne_zero hz)), hdw_v0, hcvl, rfl, hfll, hmv⟩
                          · intro Lv hLv; c0_hsteps!; exact hLv sl.core.cur_vars (0#64, ()) ml
                              ⟨sl.core.flags, hdwl.1.core_ok.flags_len, Nat.zero_le _, by simp, hml⟩
                        · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩
                      · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩
                    · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩))
              (fun B hB => by
                c0_hsplit
                · have hi_lt : i.toNat < ncand.toNat := hc
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsplit
                      · have hi_rr : i.toNat < sl.scratch.red_refs.length := by
                          rw [hdwl.1.scratch_ok.red_refs_len]; omega
                        have hcr_ref : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                            fullArenaClauseRefs sl := by
                          rw [hrefsl]; have h0 := hrr4_ok i.toNat hi_lt
                          rwa [← hrrl, List.getElem?_eq_getElem hi_rr, Option.getD_some] at h0
                        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp; fwd_call hCheckCl
                        refine fullFwdCheckClM7Spec_intro rfl hdwl hcr_ref hml ?_
                        intro ok_c sc mc hdwc hcvc _ hflc hrefsc _ hrrc hfc hmc
                        c0_hsplit
                        · have hcr_ref_c : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                              fullArenaClauseRefs sc := hrefsc.symm ▸ hcr_ref
                          refine wp_join0 (P := fun mj => ∃ sj : FullState,
                              FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
                              sj.core.fuel = s0.core.fuel ∧
                              fullArenaClauseRefs sj = fullArenaClauseRefs s4 ∧
                              sj.scratch.red_refs = s4.scratch.red_refs ∧ (FullMem c sj ⋆ R) mj)
                            (fun _ mj ⟨sj, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩ => by
                              c0_hsteps!; exact hL (ncand.toNat - (i + 1#64).toNat)
                                (i + 1#64, rem - 1#64, ()) mj (by omega)
                                ⟨sj, by omega, rfl, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩)
                            (fun Jcon hJcon => by
                              c0_hsplit
                              · c0_hsplit
                                · have hcr_ar :
                                      ((sl.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
                                      sc.core.arena.length := by
                                    have hwf_c := hdwc.2.1.arena.refs_wf _ hcr_ref_c
                                    have := hdwc.1.core_ok.arena_len_le
                                    rw [hdwc.1.core_ok.arena_len_arr, fwd_zext32_toNat]; omega
                                  c0_hsplit
                                  · c0_hsteps_nogrp; fwd_call hConnectSub
                                    refine fullFwdConnectSubsumerM7Spec_intro rfl hdwc hcr_ref_c hmc
                                      ?_
                                    intro s_con m_con hdw_con hcv_con har_con hal_con hfl_con _ _
                                      hrr_con hm_con
                                    have hrefs_con : fullArenaClauseRefs s_con =
                                        fullArenaClauseRefs sc := by
                                      unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                      rw [har_con, hal_con]
                                    c0_hsteps!; exact hJcon m_con ⟨s_con, hdw_con,
                                      hcv_con.trans (hcvc.trans hcvl),
                                      hfl_con.trans (hflc.trans hfll),
                                      hrefs_con.trans (hrefsc.trans hrefsl),
                                      hrr_con.trans (hrrc.trans hrrl), hm_con⟩
                                  · c0_hsteps!; exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl,
                                      hflc.trans hfll, hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                                · c0_hsteps!; exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl,
                                    hflc.trans hfll, hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                              · c0_hsteps!; exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl,
                                  hflc.trans hfll, hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩)
                        · c0_hsteps!; exact hQ 20#64 sc mc hdwc.toDense (hcvc.trans hcvl)
                            (hflc.trans hfll) (Or.inr rfl) (fun _ => hfc (by simpa using hc)) hmc
                      · c0_hsteps!; exact hB ml rfl
                    · c0_hsteps!; exact hB ml rfl
                  · c0_hsteps!; exact hB ml rfl
                · c0_hsteps!; exact hB ml rfl)
          · intro L hL; c0_hsteps!; exact hL ncand.toNat (0#64, budget, ()) m4
              ⟨s4, Nat.zero_le _, by simp, hdw4, hcv4.trans (hcv3.trans (hcv2.trans hcv1)),
               hfl4.trans (hfl3.trans (hfl2.trans hfl1)), rfl, rfl, hm4⟩
      · c0_hsteps!; exact hQ 20#64 s2 m2 hdw2.toDense (hcv2.trans hcv1) (hfl2.trans hfl1)
          (Or.inr rfl) (fun _ => hf2 (by simpa using hc)) hm2
    · c0_hsteps!; exact hQ 20#64 s1 m1 hdw1.toDense hcv1 hfl1 (Or.inr rfl)
        (fun _ => hf1 (by simpa using hc)) hm1

end LeanQbe.T.Examples.Kissat.Proof.Forward
