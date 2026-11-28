/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Src.Substitute
import LeanQbe.T.Examples.Kissat.Proof.Substitute.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpRewriteAr0
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# WP Proof for `full_subst_rewrite_ar` (`Proof.Substitute.WpRewriteAr`)

Proves `full_subst_rewrite_ar_wp` parametrically over `Γ : Env` against
`Spec.fullSubstRewriteArSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Substitute
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
open scoped Proof.Spec.FullArenaTactics SubstArenaTactics
open Kraken.Bedrock2.Test

private theorem ra_bv64_one : (1#64 : BitVec 64).toNat = 1 := rfl
private theorem ra_bv64_two : (2#64 : BitVec 64).toNat = 2 := rfl

private theorem ra_rl2_idx_eq {ar rp : List (BitVec 32)} {p : BitVec 64} {k : BitVec 32}
    (hpk_eq : (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat)
    (hpk_lt : (p + 3#64 + BitVec.setWidth 64 k).toNat < ar.length)
    (hl2_lt : (BitVec.setWidth 64 (ar[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt)).toNat <
      rp.length)
    (hmod_lt : (p.toNat + (3#64).toNat + k.toNat) % 2 ^ 64 < ar.length)
    (hr_lt : ar[(p.toNat + (3#64).toNat + k.toNat) % 2 ^ 64].toNat < rp.length) :
    (rp[(BitVec.setWidth 64 (ar[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt)).toNat]'
      hl2_lt).toNat =
      (rp[ar[(p.toNat + (3#64).toNat + k.toNat) % 2 ^ 64].toNat]'hr_lt).toNat := by
  have hpk_m : (p.toNat + (3#64).toNat + k.toNat) % 2 ^ 64 =
      (p + 3#64 + BitVec.setWidth 64 k).toNat := by
    rw [hpk_eq, show (3#64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
  have h1 := bv32_getElem_congr (xs := ar) (hi := hpk_lt) (hj := hmod_lt) hpk_m.symm
  have h2 : (BitVec.setWidth 64 (ar[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt)).toNat =
      ar[(p.toNat + (3#64).toNat + k.toNat) % 2 ^ 64].toNat := by
    have hlt := (ar[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt).isLt
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), h1]
  have hget : rp[(BitVec.setWidth 64 (ar[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt)).toNat]'
      hl2_lt =
      rp[ar[(p.toNat + (3#64).toNat + k.toNat) % 2 ^ 64].toNat]'hr_lt :=
    Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, h2])
  exact congrArg BitVec.toNat hget

public section

theorem full_subst_rewrite_ar_wp (Γ : Env)
    (hArenaNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec) :
    ∀ args m Q X, Spec.fullSubstRewriteArSpec args m Q X →
      Func.wp Γ full_subst_rewrite_ar_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hrepr0, hm, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  unfold Func.wp full_subst_rewrite_ar_body
  c0_hsplit
  · c0_hsteps; exact hQ true s0 m hsp0 hl0 rfl rfl (fun h => by cases h) hm
  · c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (p, ()) ml => ∃ st, RaOuterCore c F0 F_cur s0 p st ∧ (FullMem c st ⋆ R) ml)
      (fun (p, ()) _ => s0.core.arena_len - p.toNat) ?_ ?_
    · intro J hJ; c0_hsteps
      exact hJ (0#64, ()) m
        ⟨s0, ⟨hsp0, rfl, hl0, rfl, rfl, rfl, fullArenaClauseRefs_zero_mem hsp0.2.1.arena⟩, hm⟩
    · rintro J ⟨p, ⟨⟩⟩ ml ⟨st, ho, hml⟩ hJ
      have hcl := ho.sp.1.core_ok; have hsl := ho.sp.1.scratch_ok
      have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le
      have hcv_le := hcl.cur_vars_le; have hlml := hcl.lit_mark_len; have hrpl := hcl.repr_len
      have hrepr_st : FullReprEquiv F_cur st := fun l hl => by
        rw [ho.cv_eq] at hl; have h0 := hrepr0 l hl; rw [ho.repr_eq, ho.cv_eq]; exact h0
      c0_hsplit
      · have hp_lt_alen : p.toNat < st.core.arena_len := by
          rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hp_ref : p.toNat ∈ fullArenaClauseRefs st := ho.p_pos.elim (fun he => by omega) id
        have hpwf := ho.sp.2.1.arena.refs_wf p.toNat hp_ref
        have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
          rw [BitVec.toNat_add, ra_bv64_two, Nat.mod_eq_of_lt (by omega)]
        have hp2_lt : (p + 2#64).toNat < st.core.arena.length := by rw [hp2_eq, harl]; omega
        have hp_trunc : (BitVec.setWidth 32 p).toNat = p.toNat := bv32_trunc_toNat (by omega)
        have hnp_lt_next := fullArenaClauseRefs_next_or_end ho.sp.2.1.arena hp_ref
        c0_hsteps; c0_hcall hArenaNext
        refine ⟨c, st, R, rfl, ho.sp.1, hml, ?_⟩; dsimp only
        let np := BitVec.setWidth 64 (BitVec.ofNat 32
          (fullArenaNextOff st.core.arena st.core.arena_len (BitVec.setWidth 32 p).toNat))
        have hnp_nat : np.toNat = fullArenaNextOff st.core.arena st.core.arena_len p.toNat := by
          dsimp only [np]; rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hp_trunc]
          have hnb := (fullArenaNextOff_bounds (ar := st.core.arena) (alen := st.core.arena_len)
            (cref := p.toNat) hpwf.1).2
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hnp_meas : s0.core.arena_len - np.toNat < s0.core.arena_len - p.toNat := by
          rw [hnp_nat, ← ho.alen_eq]
          have := fullArenaNextOff_bounds (ar := st.core.arena) (alen := st.core.arena_len)
            (cref := p.toNat) hpwf.1; omega
        have hnp_pos : np.toNat = st.core.arena_len ∨ np.toNat ∈ fullArenaClauseRefs st :=
          hnp_nat ▸ hnp_lt_next
        let hdr := st.core.arena[p.toNat]'(by omega)
        let sz32 := st.core.arena[(p + 2#64).toNat]'hp2_lt
        have hp2_get : st.core.arena[p.toNat + 2]? = some sz32 := by
          dsimp only [sz32]; rw [← hp2_eq, List.getElem?_eq_getElem hp2_lt]
        have hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat := by
          unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [hp2_get, Option.getD_some]
        have hsz_core : fullArenaClauseSizeCore st.core p.toNat = sz32.toNat := hsz_eq.symm
        have hp_blk_le : p.toNat + 3 + sz32.toNat ≤ st.core.arena_len := by
          change fullArenaClauseSizeCore st.core p.toNat = sz32.toNat at hsz_core
          have := hpwf.2.2.1; have := hpwf.2.2.2.1; omega
        have hhdr_eq : fullArenaHdr st p.toNat = hdr := by
          dsimp only [hdr, fullArenaHdr, fullArenaHdrCore]
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        c0_hsplit
        · c0_hsteps
          exact hJ (np, ()) ml hnp_meas ⟨st, ⟨ho.sp, ho.cv_eq, ho.hl0, ho.fuel_eq,
            ho.repr_eq, ho.alen_eq, hnp_pos⟩, hml⟩
        · c0_hsplit
          · c0_hsteps
            exact hJ (np, ()) ml hnp_meas ⟨st, ⟨ho.sp, ho.cv_eq, ho.hl0, ho.fuel_eq,
              ho.repr_eq, ho.alen_eq, hnp_pos⟩, hml⟩
          · have hng : fullArenaClauseGarb st p.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore
              rw [show fullArenaHdrCore st.core p.toNat = hdr from hhdr_eq,
                (by assumption : (hdr &&& 0x00080000#32) = 0#32)]; decide
            have hsz3 : 3 ≤ sz32.toNat := by have := hpwf.2.1; omega
            c0_hsteps_nogrp
            refine wp_loop_break_group
              (fun (chg, _k1, ()) m1 => (chg = true ∨ chg = false) ∧ (FullMem c st ⋆ R) m1)
              (fun n (k, ()) m1 =>
                n = sz32.toNat - k.toNat ∧ k.toNat ≤ sz32.toNat ∧ (FullMem c st ⋆ R) m1)
              ?_ ?_ ?_
            · rintro B ⟨chg, _k1, ⟨⟩⟩ m1 ⟨_, hm1⟩
              c0_hsplit
              · c0_hsteps_nogrp
                refine wp_loop_break_group
                  (fun (_k2, taut, nsz, ()) m2 =>
                    ∃ st2, RaLoop2Brk c F_cur st p sz32.toNat taut nsz st2 ∧ (FullMem c st2 ⋆ R) m2)
                  (fun n (k, nsz, ()) m2 =>
                    n = sz32.toNat - k.toNat ∧
                    ∃ st2, RaLoop2Inv c F_cur st p sz32.toNat k nsz st2 ∧ (FullMem c st2 ⋆ R) m2)
                  ?_ ?_ ?_
                · rintro B2 ⟨_k2, taut, nsz, ⟨⟩⟩ m2 ⟨st2, hb2, hm2⟩
                  c0_hsteps_nogrp
                  refine wp_loop_inv
                    (fun (k3, ()) m3 => ∃ st3,
                      RaClear3Core c st st2 p nsz.toNat k3 st3 ∧ (FullMem c st3 ⋆ R) m3)
                    (fun (k3, ()) _ => nsz.toNat - k3.toNat) ?_ ?_
                  · intro J3 hJ3; c0_hsteps
                    exact hJ3 (0#32, ()) m2 ⟨st2, ra_clear3_init hb2, hm2⟩
                  · rintro J3 ⟨k3, ⟨⟩⟩ m3 ⟨st3, hc3, hm3⟩ hJ3
                    c0_hsplit
                    · have hk3_lt : k3.toNat < nsz.toNat := hc
                      have hk3_1 := fullSubst_add_u32_toNat (k := k3) (by omega)
                      have hpk3_eq := fullSubst_off3_toNat (p := p) (k := k3) (by omega)
                      obtain ⟨hpk3_lt, _, hc3_next⟩ :=
                        ra_clear3_step hb2 hc3 hk3_lt hk3_1 hpk3_eq (by omega) hcv_le
                      c0_hsteps
                      exact hJ3 (k3 + 1#32, ()) _ (by dsimp only; omega)
                        ⟨_, hc3_next, by assumption⟩
                    · obtain ⟨hlm3_zero, har3_lt, har3_pw, har3_in_out, har3_pad, hent2⟩ :=
                        ra_clear3_done hb2 hc3 hc
                      have hcl3 := hc3.len.core_ok
                      have harl3 := hcl3.arena_len_arr; have hlml3 := hcl3.lit_mark_len
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [])
                        (fun () m4 => ∃ st4,
                          RaDoneCore c F0 F_cur s0 st st4 ∧ (FullMem c st4 ⋆ R) m4)
                        ?_ ?_
                      · rintro _ ⟨⟩ m4 ⟨st4, hd4, hm4⟩
                        c0_hsteps
                        exact hJ (np, ()) m4 hnp_meas
                          ⟨st4, ⟨hd4.sp, hd4.cv_eq, hd4.hl0, hd4.fuel_eq,
                          hd4.repr_eq, hd4.alen_eq, by
                            rw [hd4.alen_eq, ← ho.alen_eq, hd4.refs_eq]; exact hnp_pos⟩, hm4⟩
                      · intro Jdone hDone; c0_hsteps_nogrp
                        refine wp_join_group (ts := [])
                          (fun () mg =>
                            st3.LengthsOk c ∧ (FullMem c st3 ⋆ R) mg ∧
                              (taut = true ∨ nsz.toNat ≤ 2))
                          ?_ ?_
                        · rintro _ ⟨⟩ mg ⟨_, hmg, _⟩
                          obtain ⟨hp_lt3, hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4, _⟩ :=
                            ra_garb_step ho hp_ref hsz_eq hhdr_eq hc3.sc_eq hc3.core_eq harl3 hlml3
                              hlm3_zero har3_in_out rfl
                          c0_hstraight
                          let st4 : FullState :=
                            { st3 with core := { st3.core with
                                arena := st3.core.arena.set p.toNat (hdr ||| 0x00080000#32)
                                arena_garbage := st3.core.arena_garbage + 3#64 +
                                  BitVec.setWidth 64 sz32 } }
                          have ⟨m4, hm4⟩ : ∃ m4, (FullMem c st4 ⋆ R) m4 := ⟨_, by assumption⟩
                          have hp3_eq : (p + 3#64).toNat = p.toNat + 3 := by
                            rw [BitVec.toNat_add, show (3#64).toNat = 3 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          have hp4_eq : (p + 4#64).toNat = p.toNat + 4 := by
                            rw [BitVec.toNat_add, show (4#64).toNat = 4 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := [])
                            (fun () m4a =>
                              (taut = true ∨ 1 ≤ nsz.toNat) ∧ (FullMem c st4 ⋆ R) m4a)
                            ?_ ?_
                          · rintro _ ⟨⟩ m4a ⟨_, hm4a⟩
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [])
                              (fun () m5 => ∃ st5 : FullState,
                                st5.core.arena = st4.core.arena ∧ FullSparseInvW c F0 F_cur st5 ∧
                                st5.core.cur_vars = s0.core.cur_vars ∧ st5.core.cur_level = 0 ∧
                                st5.core.fuel = s0.core.fuel ∧ st5.core.repr = s0.core.repr ∧
                                st5.core.arena_len = s0.core.arena_len ∧
                                fullArenaClauseRefs st5 = fullArenaClauseRefs st ∧
                                (FullMem c st5 ⋆ R) m5)
                              ?_ ?_
                            · rintro _ ⟨⟩ m5 ⟨st5, har5_eq, hsp5, hcv5, hl05, hfl5, hrp5, hal5,
                                hrefs5, hm5⟩
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun () m6 => ∃ st6, RaDoneCore c F0 F_cur s0 st st6 ∧
                                  (FullMem c st6 ⋆ R) m6)
                                (fun _ ⟨⟩ m6 h6 => by c0_hsteps; exact hDone () m6 h6)
                                (fun J2b hJ2b => ?_)
                              c0_hsplit
                              · c0_hsteps; exact hJ2b () m5
                                  ⟨st5, ⟨hsp5, hcv5, hl05, hfl5, hrp5, hal5, hrefs5⟩, hm5⟩
                              · have htaut_f2 : taut = false := by
                                  cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                                c0_hsplit
                                · have hnsz2 : nsz.toNat = 2 := by
                                    have hbe : nsz = 2#32 := hc; rw [hbe]; rfl
                                  obtain ⟨hp3_lt5, hp4_lt5, hent_b⟩ := ra_addbin_prep ho hsp5 hp_ref
                                    hng hsz_eq rfl harl3 (fun _ hf => hf.elim) har5_eq
                                    (by dsimp only [st4]; rw [hhdr_eq]) har3_in_out hp3_eq hp4_eq
                                    (by omega) (fun j hj => by
                                      have ⟨m', hm', heq⟩ := hent2 htaut_f2 j hj
                                      exact ⟨m', by omega, heq⟩)
                                  c0_hsteps; c0_hcall hAddBin
                                  refine ⟨c, F0, F_cur, st5, R, rfl, hsp5.1, hsp5.2.1, hl05,
                                    fun _ _ => hent_b, hm5, ?_⟩
                                  intro r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 st6
                                    hlen6 hw6 _ hr20 _ hm6
                                  have hsp6 := fullSparseInvW_afterAddBin hsp5 hlen6 hw6
                                  c0_hsplit
                                  · c0_hsteps
                                    exact hQ false st6 m6 hsp6 hl05 hcv5 hfl5
                                      (fun _ => (hr20 hc).1) hm6
                                  · c0_hsteps_nogrp
                                    refine wp_join_group (ts := [])
                                      (fun () m6' => (FullMem c st6 ⋆ R) m6')
                                      (fun _ ⟨⟩ m6' _ => by
                                        c0_hsteps
                                        let st6o : FullState :=
                                          { st6 with core := { st6.core with oom := 1#64 } }
                                        exact hQ true st6o _ (fullSparseInvW_with_oom hsp6 1#64)
                                          hl05 hcv5 hfl5 (fun h => by cases h) (by assumption))
                                      (fun Joom hOom => ?_)
                                    c0_hsplit
                                    · c0_hsteps; exact hOom () m6 hm6
                                    · c0_hsplit
                                      · c0_hsteps; exact hOom () m6 hm6
                                      · c0_hsteps; exact hJ2b () m6
                                          ⟨st6, ⟨hsp6, hcv5, hl05, hfl5, hrp5, hal5, hrefs5⟩, hm6⟩
                                · c0_hsteps; exact hJ2b () m5
                                    ⟨st5, ⟨hsp5, hcv5, hl05, hfl5, hrp5, hal5, hrefs5⟩, hm5⟩
                            · intro J_1 hJ_1; c0_hsplit
                              · c0_hsteps; exact hJ_1 () m4a
                                  ⟨st4, rfl, hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4, hm4a⟩
                              · have htaut_f1 : taut = false := by
                                  cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                                c0_hsplit
                                · have hnsz1 : nsz.toNat = 1 := by
                                    have hbe : nsz = 1#32 := hc; rw [hbe]; rfl
                                  obtain ⟨hp3_lt4, hlit_lt_cv, hlit_ent⟩ := ra_addunit_prep ho hsp4
                                    hp_ref hng hsz_eq rfl ho.cv_eq hcv4 harl3
                                    (by dsimp only [st4]; rw [hhdr_eq]) har3_lt hp3_eq (by omega)
                                    (fun j hj => by
                                      have ⟨m', hm', heq⟩ := hent2 htaut_f1 j hj
                                      exact ⟨m', by omega, heq⟩)
                                  c0_hsteps; c0_hcall hAddUnit
                                  refine ⟨c, F0, F_cur, st4, R, rfl, hsp4.1, hsp4.2.1,
                                    fun _ => hlit_ent, hm4a, ?_⟩
                                  intro ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 st5
                                    hlen5 hw5 hcl5 hfail5 _ hm5
                                  have hsp5 := fullSparseInvW_afterAddUnit hsp4 hlen5 hw5
                                  c0_hsplit
                                  · c0_hsteps; exact hJ_1 () m5
                                      ⟨st5, rfl, hsp5, hcv4, hcl5, hfl4, hrp4, hal4', hrefs4, hm5⟩
                                  · c0_hsteps; exact hQ false st5 m5 hsp5 hcl5 hcv4 hfl4
                                      (fun _ => (hfail5 hlit_lt_cv (by
                                        cases ok <;>
                                          first | rfl | contradiction | exact absurd rfl hc)).1)
                                      hm5
                                · c0_hsteps; exact hJ_1 () m4a
                                    ⟨st4, rfl, hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4, hm4a⟩
                          · intro J0 hJ0; c0_hsplit
                            · c0_hsteps; exact hJ0 () _ ⟨Or.inl hc, by assumption⟩
                            · have htaut_f0 : taut = false := by
                                cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                              c0_hsplit
                              · exfalso
                                have := hb2.nsz_pos htaut_f0
                                have h0 : nsz.toNat = 0 := by
                                  have hbe : nsz = 0#32 := hc; rw [hbe]; rfl
                                omega
                              · have := hb2.nsz_pos htaut_f0
                                c0_hsteps; exact hJ0 () _ ⟨Or.inr (by omega), by assumption⟩
                        · intro Jgarb hGarb; c0_hsplit
                          · c0_hsteps; exact hGarb () m3 ⟨hc3.len, hm3, Or.inl hc⟩
                          · c0_hsplit
                            · c0_hsteps; exact hGarb () m3 ⟨hc3.len, hm3, Or.inr hc⟩
                            · have htaut_f : taut = false := by
                                cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                              have hnsz3 : 3 ≤ nsz.toNat := by
                                have hnot : ¬ nsz.toNat ≤ 2 := hc; omega
                              have hent_n : (cnfOfClauses F_cur).EntailsClause
                                  (cnfClause ((List.range nsz.toNat).map fun j =>
                                    (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat)) :=
                                entails_clause_subst (fun l hl => by
                                  obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff
                                    (by rw [harl]; omega)).mp hl
                                  rw [hsz_core] at hj
                                  obtain ⟨m', hm', heqv⟩ := hent2 htaut_f j (by omega)
                                  refine ⟨_, List.mem_map.mpr ⟨m', List.mem_range.mpr hm', rfl⟩, ?_⟩
                                  rw [List.getElem?_eq_getElem (by rw [harl]; omega),
                                    Option.getD_some] at heqv; exact heqv)
                                  (ho.sp.2.1.arena.entails p.toNat hp_ref hng)
                              have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by
                                rw [BitVec.toNat_add, ra_bv64_one, Nat.mod_eq_of_lt (by omega)]
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun () m4 => ∃ st4, RaDoneCore c F0 F_cur s0 st st4 ∧
                                  (FullMem c st4 ⋆ R) m4)
                                (fun _ ⟨⟩ m4 h4 => by c0_hsteps; exact hDone () m4 h4)
                                (fun Jshr hShr => ?_)
                              c0_hsplit
                              · have hnsz_lt : nsz.toNat < sz32.toNat := hc
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := [])
                                  (fun () m4 => ∃ st4, RaDoneCore c F0 F_cur s0 st st4 ∧
                                    (FullMem c st4 ⋆ R) m4)
                                  (fun _ ⟨⟩ m4 h4 => by c0_hsteps; exact hShr () m4 h4)
                                  (fun Jshrk hShrk => ?_)
                                c0_hsplit
                                · have hshrk_z : (hdr &&& 0x00800000#32) = 0#32 := hc
                                  have hsent_idx :
                                      (p + 3#64 + BitVec.setWidth 64 sz32 - 1#64).toNat =
                                        p.toNat + 3 + sz32.toNat - 1 := by
                                    have hoff3 := fullSubst_off3_toNat (p := p) (k := sz32)
                                      (by omega)
                                    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                                      rw [hoff3, ra_bv64_one]; omega)), hoff3, ra_bv64_one]
                                  obtain ⟨hp2_lt3, hp1_lt3, hp_lt3, hsent_lt3, hdone_0⟩ :=
                                    ra_shrink_lt_shrk0_step ho hp_ref hng hsz_eq hhdr_eq hnsz3
                                      hnsz_lt hshrk_z hc3.sc_eq hc3.core_eq harl3 hlml3 hlm3_zero
                                      har3_pad (fun i hi => har3_in_out i
                                        (hi.elim (fun h1 => Or.inl (by omega)) Or.inr))
                                      har3_lt har3_pw hent_n hp1_eq hp2_eq hsent_idx
                                  c0_hsteps
                                  exact hShrk () _ ⟨_, hdone_0, by assumption⟩
                                · have _hp2_lt3 : (p + 2#64).toNat < st3.core.arena.length := by
                                    rw [hp2_eq, harl3]; omega
                                  have _hp1_lt3 : (p + 1#64).toNat <
                                      (st3.core.arena.set (p + 2#64).toNat nsz).length := by
                                    rw [List.length_set, hp1_eq, harl3]; omega
                                  c0_hsteps
                                  exact hShrk () _ ⟨_, ra_shrink_lt_shrk1_step ho hp_ref hng hsz_eq
                                    hhdr_eq hnsz3 hnsz_lt hc hc3.sc_eq hc3.core_eq harl3 hlml3
                                    hlm3_zero har3_pad har3_in_out har3_lt har3_pw hent_n hp1_eq
                                    hp2_eq, by assumption⟩
                              · have hnsz_eq : nsz.toNat = sz32.toNat := by
                                  have := hb2.core.nsz_le
                                  have hnot : ¬ nsz.toNat <
                                      st.core.arena[(p.toNat + 2) % 2 ^ 64].toNat := hc
                                  rw [bv32_getElem_congr (j := (p + 2#64).toNat) (hj := hp2_lt)
                                    (by rw [hp2_eq, Nat.mod_eq_of_lt (by omega)])] at hnot
                                  change ¬ nsz.toNat < sz32.toNat at hnot
                                  omega
                                c0_hsteps
                                exact hShr () m3 ⟨_, ra_shrink_eq_step ho hp_ref hng hsz_eq hp2_get
                                  hnsz3 hnsz_eq hc3.sc_eq hc3.core_eq harl3 hlml3 hlm3_zero har3_pad
                                  har3_in_out har3_lt har3_pw hent_n, hm3⟩
                · rintro B2 L2 _ ⟨k, nsz, ⟨⟩⟩ m2 hB2 hL2 ⟨hk_n, st2, h2inv, hm2⟩
                  subst hk_n
                  have hcl2 := h2inv.core.len.core_ok
                  c0_hsplit
                  · have hk_lt : k.toNat < sz32.toNat := hc
                    have hk1 := fullSubst_add_u32_toNat (k := k) (by omega)
                    have hpk_eq := fullSubst_off3_toNat (p := p) (k := k) (by omega)
                    obtain ⟨hpk_lt, hl2_lt_rp, hl2_orig_eq, hrl2_lt_v, hrl2_eqv, hrl2_1_z64,
                        hrl2_1_lt_lm, hrl_z64, hrl2_lt_lm⟩ :=
                      ra_loop2_lit_prep ho hrepr_st h2inv hk_lt hpk_eq (by omega)
                    let l2 := st2.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt
                    let rl2 := st2.core.repr[(BitVec.setWidth 64 l2).toNat]'hl2_lt_rp
                    c0_hsplit
                    · c0_hsteps; exact hB2 (k, true, nsz, ()) m2
                        ⟨st2, ⟨h2inv.core, fun h => Bool.noConfusion h,
                          fun h => Bool.noConfusion h⟩, hm2⟩
                    · have hpk_m : (p.toNat + (3#64).toNat + k.toNat) % 2 ^ 64 =
                          (p + 3#64 + BitVec.setWidth 64 k).toNat := by
                        rw [hpk_eq, show (3#64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
                      have hrl2_m : rl2.toNat = _ := ra_rl2_idx_eq hpk_eq hpk_lt hl2_lt_rp
                        (by rw [hpk_m]; exact hpk_lt)
                        (by rw [bv32_getElem_congr hpk_m]
                            have := hl2_lt_rp
                            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at this
                            exact this)
                      have hlm_neg0 : st2.core.lit_mark[rl2.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
                        ra_lm_zero (hi := by rw [← hrl2_1_z64]; exact hrl2_1_lt_lm)
                          (hrl2_1_z64.trans (congrArg (· ^^^ 1) hrl2_m)) hc
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i32])
                        (fun (nsz', ()) m2' =>
                          ∃ st2', RaLoop2Inv c F_cur st p sz32.toNat (k + 1#32) nsz' st2' ∧
                            (FullMem c st2' ⋆ R) m2')
                        (fun _ ⟨nsz', ⟨⟩⟩ m2' ⟨st2', h2', hm2'⟩ => by
                          c0_hsteps
                          exact hL2 (sz32.toNat - (k + 1#32).toNat) (k + 1#32, nsz', ()) m2'
                            (by omega) ⟨rfl, st2', h2', hm2'⟩)
                        (fun Jnsz hJnsz => ?_)
                      c0_hsplit
                      · have hlm_pos0 : st2.core.lit_mark[rl2.toNat]?.getD 0#8 = 0#8 :=
                          ra_lm_zero (hi := by rw [← hrl_z64]; exact hrl2_lt_lm)
                            (hrl_z64.trans hrl2_m) hc
                        have := h2inv.nsz_k
                        have hpnsz_eq := fullSubst_off3_toNat (p := p) (k := nsz) (by omega)
                        have hpnsz_lt : (p + 3#64 + BitVec.setWidth 64 nsz).toNat <
                            st2.core.arena.length := by
                          rw [hpnsz_eq, hcl2.arena_len_arr]; omega
                        have hnsz1 := fullSubst_add_u32_toNat (k := nsz) (by omega)
                        c0_hsteps
                        refine hJnsz (nsz + 1#32, ()) _
                          ⟨_, ra_push_step hk_lt hk1 hnsz1 h2inv.core h2inv.nsz_k h2inv.ent hcv_le
                            (by rw [hcl2.arena_len_arr]; omega) hl2_orig_eq hrl2_lt_v hrl2_eqv
                            hlm_neg0 hlm_pos0, ?_⟩
                        rw [← hrl_z64, ← hpnsz_eq]; assumption
                      · have hlm_nz : st2.core.lit_mark[rl2.toNat]?.getD 0#8 ≠ 0#8 :=
                          ra_lm_ne (hi := by rw [← hrl_z64]; exact hrl2_lt_lm)
                            (hrl_z64.trans hrl2_m) hc
                        c0_hsteps
                        exact hJnsz (nsz, ()) m2
                          ⟨st2, ra_loop2_dup_step h2inv hk_lt hk1 hrl2_lt_v hcv_le hl2_orig_eq
                            hrl2_eqv hlm_nz, hm2⟩
                  · have hk_eq : k.toNat = sz32.toNat := by
                      have := h2inv.k_le
                      have hnl : ¬ k.toNat <
                          st.core.arena[(p.toNat + 2) % 2 ^ 64].toNat := hc
                      rw [bv32_getElem_congr (j := (p + 2#64).toNat) (hj := hp2_lt)
                        (by rw [hp2_eq, Nat.mod_eq_of_lt (by omega)])] at hnl
                      change ¬ k.toNat < sz32.toNat at hnl; omega
                    c0_hsteps
                    exact hB2 (k, false, nsz, ()) m2
                      ⟨st2, ⟨h2inv.core, fun _ => h2inv.nsz_pos (by omega),
                        fun _ j hj => h2inv.ent j (by omega)⟩, hm2⟩
                · intro B2 L2 _ hL2; c0_hsteps
                  exact hL2 sz32.toNat (0#32, 0#32, ()) m1
                    ⟨rfl, st, ra_loop2_init ho hp_ref hng hsz_eq, hm1⟩
              · c0_hsteps
                exact hJ (np, ()) m1 hnp_meas ⟨st, ⟨ho.sp, ho.cv_eq, ho.hl0, ho.fuel_eq,
                  ho.repr_eq, ho.alen_eq, hnp_pos⟩, hm1⟩
            · rintro B1 L1 _ ⟨k, ⟨⟩⟩ m1 hB1 hL1 ⟨hk_n, hk_le, hm1⟩; subst hk_n
              c0_hsplit
              · have hk_lt : k.toNat < sz32.toNat := hc
                have hk1 := fullSubst_add_u32_toNat (k := k) (by omega)
                have hpk_eq := fullSubst_off3_toNat (p := p) (k := k) (by omega)
                have hpk_lt : (p + 3#64 + BitVec.setWidth 64 k).toNat < st.core.arena.length := by
                  rw [hpk_eq, harl]; omega
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun () mi => (FullMem c st ⋆ R) mi)
                  (fun _ ⟨⟩ mi hmi => by
                    c0_hsteps
                    exact hL1 (sz32.toNat - (k + 1#32).toNat) (k + 1#32, ()) mi (by omega)
                      ⟨rfl, by omega, hmi⟩)
                  (fun Ji hJi => ?_)
                c0_hsplit
                · obtain ⟨hl_lt_v, hl_lt_nl⟩ :=
                    ra_loop1_lit_lt ho hp_ref hng hsz_eq hk_lt hpk_eq hpk_lt
                  c0_hsplit
                  · c0_hsteps; exact hB1 (true, k, ()) m1 ⟨Or.inl rfl, hm1⟩
                  · c0_hsteps; exact hJi () m1 hm1
                · c0_hsteps; exact hJi () m1 hm1
              · c0_hsteps; exact hB1 (false, k, ()) m1 ⟨Or.inr rfl, hm1⟩
            · intro B1 L1 _ hL1; c0_hsteps
              exact hL1 sz32.toNat (0#32, ()) ml ⟨rfl, Nat.zero_le _, hml⟩
      · c0_hsteps
        exact hQ true st ml ho.sp ho.hl0 ho.cv_eq (by rw [ho.fuel_eq]) (fun h => by cases h) hml

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
