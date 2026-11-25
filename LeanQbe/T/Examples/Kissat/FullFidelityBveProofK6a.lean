/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVE Parity Proofs — Dynamic K6 Primitives (`FidBveProofK6a`)

UNSAT-only `Func.wp` proofs (`public section`, strictly `std3`, zero expose attrs):
1. `full_k6_watch_fid_wp` (`fidK6WatchSpec`).
2. `full_k6_assign_fid_wp` (`fidK6AssignSpec`).
3. `full_k6_mtf_fid_wp` (`fidK6MtfSpec`).
4. `full_k6_backtrack_fid_wp` (`fidK6BacktrackSpec`).
5. `full_k6_ana_cl_fid_wp` (`fidK6AnaClSpec`).
6. `full_k6_core_fid_wp` (`fidK6CoreSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open Kraken.Bedrock2.Test

open scoped M8K6bTactics FidK6Tactics

attribute [local bv_c0] List.length_set

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide | omega | fid_omega)

private theorem fid_bv32_and_ffff_toNat (x : BitVec 32) :
    (x &&& 0xFFFF#32).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and]
  rw [show (0xFFFF#32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

private theorem fid_sub1_mod32 (a x : Nat) (hx : 0 < x)
    (hlt : a + (x - 1) < 4294967296) :
    (a + (4294967296 - 1 + x)) % 4294967296 = a + (x - 1) := by
  rw [show a + (4294967296 - 1 + x) = (a + (x - 1)) + 4294967296 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-! ## 1. `full_k6_watch_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_watch_fid`, certifying `fidK6WatchSpec`. -/
theorem full_k6_watch_fid_wp (Γ : Env) :
    ∀ a m Q X, fidK6WatchSpec a m Q X → Func.wp Γ full_k6_watch_fid_body a m Q X := by
  rintro ⟨h, cid, l0, l1, sz, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6WatchSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have h4214 : 4214 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  rw [hmv_eq] at hmv_lo hmv_hi hbge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q () m0 := hQ scr0 m0 hscr_len (fun _ _ _ => rfl) hm0
  unfold Func.wp full_k6_watch_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hcid : cid.toNat < 4 * mv.toNat := by fid_omega
        c0_hsplit
        · c0_hsteps!; exact hret_noop
        · have hl0 : l0.toNat < 2 * mv.toNat := by fid_omega
          c0_hsplit
          · c0_hsteps!; exact hret_noop
          · have hl1 : l1.toNat < 2 * mv.toNat := by fid_omega
            have hw0_n : (cid <<< (1 : Nat)).toNat = 2 * cid.toNat := m8_bv32_shl1_toNat (by omega)
            have hw1_n : ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 :=
              m8_bv32_shl1_or1_toNat (by omega)
            have hb0_e := fid_k6_off_add (mv := mv) (k := 21) (x := cid <<< (1 : Nat))
              hmv_hi (by decide) (by omega)
            have hb1_e := fid_k6_off_add (mv := mv) (k := 21) (x := (cid <<< (1 : Nat)) ||| 1#32)
              hmv_hi (by decide) (by omega)
            have hn0_e := fid_k6_off_add (mv := mv) (k := 13) (x := cid <<< (1 : Nat))
              hmv_hi (by decide) (by omega)
            have hn1_e := fid_k6_off_add (mv := mv) (k := 13) (x := (cid <<< (1 : Nat)) ||| 1#32)
              hmv_hi (by decide) (by omega)
            have hh0_e := fid_k6_off_add (mv := mv) (k := 11) (x := l0) hmv_hi (by decide)
              (by omega)
            have hh1_e := fid_k6_off_add (mv := mv) (k := 11) (x := l1) hmv_hi (by decide)
              (by omega)
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
              (fun bf => (bf, ())) (fun _ => True)
              (fun _ bf _ => by
                have hb0_lt : ((4224 + 21 * mv + (cid <<< (1 : Nat))).setWidth 64).toNat <
                    scr0.length := by rw [hb0_e, hw0_n]; omega
                have hh0_lt : ((4224 + 11 * mv + l0).setWidth 64).toNat < scr0.length := by
                  rw [hh0_e]; omega
                have hn0_lt : ((4224 + 13 * mv + (cid <<< (1 : Nat))).setWidth 64).toNat <
                    scr0.length := by rw [hn0_e, hw0_n]; omega
                have hb1_lt : ((4224 + 21 * mv + ((cid <<< (1 : Nat)) ||| 1#32)).setWidth
                    64).toNat < scr0.length := by rw [hb1_e, hw1_n]; omega
                have hh1_lt : ((4224 + 11 * mv + l1).setWidth 64).toNat < scr0.length := by
                  rw [hh1_e]; omega
                have hn1_lt : ((4224 + 13 * mv + ((cid <<< (1 : Nat)) ||| 1#32)).setWidth
                    64).toNat < scr0.length := by rw [hn1_e, hw1_n]; omega
                c0_hsteps!
                refine hQ _ _ (by simp [hscr_len]) (fun idx hi hor => by
                  rw [hmv_eq] at hor; (repeat rw [List.getElem?_set_ne (by fid_ne)]))
                  (m8ScrSt_eq s _ ▸ hm))
              (fun Jb hJb => by
                c0_hsplit
                · c0_hsteps!; exact hJb 0x80000000#32 trivial
                · c0_hsteps!; exact hJb 0#32 trivial)

/-! ## 2. `full_k6_assign_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_assign_fid`, certifying `fidK6AssignSpec`. -/
theorem full_k6_assign_fid_wp (Γ : Env) :
    ∀ a m Q X, fidK6AssignSpec a m Q X → Func.wp Γ full_k6_assign_fid_body a m Q X := by
  rintro ⟨h, lit, rsn_cid, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6AssignSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have h4214 : 4214 < scr0.length := by omega
  have h4197 : 4197 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  let te := scr0[4197]'h4197
  have hte_o : (scr0[(@OfNat.ofNat Nat 4197 _)]'h4197).toNat = te.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  rw [hmv_eq] at hmv_lo hmv_hi hbge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q () m0 := hQ scr0 m0 hscr_len (fun _ _ _ _ _ _ _ => rfl) hm0
  unfold Func.wp full_k6_assign_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hlit : lit.toNat < 2 * mv.toNat := by fid_omega
        c0_hsplit
        · c0_hsteps!; exact hret_noop
        · have hte : te.toNat < mv.toNat := Nat.lt_of_not_le hc
          let v := lit >>> (1 : Nat)
          have hv_n : v.toNat = lit.toNat / 2 := m8_bv32_lshr1_toNat lit
          have hv_lt : v.toNat < mv.toNat := by omega
          have hln_lt : (lit ^^^ 1#32).toNat < 2 * mv.toNat := (m8_bv32_xor1_lt lit hlit).2
          have hv0_e := fid_k6_off_add (mv := mv) (k := 9) (x := lit) hmv_hi (by decide) (by omega)
          have hv1_e := fid_k6_off_add (mv := mv) (k := 9) (x := lit ^^^ 1#32)
            hmv_hi (by decide) (by omega)
          have hlv_e := fid_k6_off_add0 (x := v) (by omega)
          have hrs_e := fid_k6_off_add1 (mv := mv) (x := v) hmv_hi (by omega)
          have htr_e := fid_k6_off_add (mv := mv) (k := 5) (x := te) hmv_hi (by decide) (by omega)
          have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := v) hmv_hi (by decide) (by omega)
          have hv0_lt : ((4224 + 9 * mv + lit).setWidth 64).toNat < scr0.length := by
            rw [hv0_e]; omega
          have hv1_lt : ((4224 + 9 * mv + (lit ^^^ 1#32)).setWidth 64).toNat <
              scr0.length := by rw [hv1_e]; omega
          have hlv_lt : (((4224 : BitVec 32) + v).setWidth 64).toNat < scr0.length := by
            rw [hlv_e]; omega
          have hrs_lt : ((4224 + mv + v).setWidth 64).toNat < scr0.length := by
            rw [hrs_e]; omega
          have htr_lt : ((4224 + 5 * mv + te).setWidth 64).toNat < scr0.length := by
            rw [htr_e]; omega
          c0_hsteps_nogrp
          refine wp_join0
            (fun mj => ∃ scrj : List (BitVec 32),
              scrj.length = c.scratch_cap ∧
              (∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
                (idx < 4224 ∨ 4224 + 2 * mv.toNat ≤ idx) →
                (idx < 4224 + 5 * mv.toNat ∨ 4224 + 7 * mv.toNat ≤ idx) →
                (idx < 4224 + 9 * mv.toNat ∨ 4224 + 11 * mv.toNat ≤ idx) →
                scrj[idx]? = scr0[idx]?) ∧
              (FullMem c (m8ScrSt s scrj) ⋆ R) mj)
            ?_ ?_
          · rintro _ mj ⟨scrj, hlj, hkj, hmj⟩
            have hfl_lt : ((4224 + 6 * mv + v).setWidth 64).toNat < scrj.length := by
              rw [hlj, hfl_e]; omega
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
              (fun nfl => (nfl, ())) (fun _ => True)
              (fun _ nfl _ => by
                c0_hsteps!
                refine hQ _ _ (by simp [hlj]) (fun idx hi h97 h98 ha hb hc' => by
                  rw [hmv_eq] at ha hb hc'
                  rw [List.getElem?_set_ne (by fid_ne)]
                  exact hkj idx hi h97 h98 ha hb hc') (m8ScrSt_eq s _ ▸ hm))
              (fun Jf hJf => by
                c0_hsplit
                · c0_hsteps!; exact hJf _ trivial
                · c0_hsteps!; exact hJf _ trivial)
          · intro J0 hJ0
            c0_hsplit
            · c0_hsteps!
              refine hJ0 _ ⟨_, by simp [hscr_len], fun idx hi h97 h98 ha hb hc' => by
                repeat rw [List.getElem?_set_ne (by fid_ne)], hm⟩
            · c0_hsteps!
              refine hJ0 _ ⟨_, by simp [hscr_len], fun idx hi h97 h98 ha hb hc' => by
                repeat rw [List.getElem?_set_ne (by fid_ne)], hm⟩

/-! ## 3. `full_k6_mtf_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_mtf_fid`, certifying `fidK6MtfSpec`. -/
theorem full_k6_mtf_fid_wp (Γ : Env) :
    ∀ a m Q X, fidK6MtfSpec a m Q X → Func.wp Γ full_k6_mtf_fid_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6MtfSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have h4214 : 4214 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  let nv := scr0[4192]'h4192
  have hnv_o : (scr0[(@OfNat.ofNat Nat 4192 _)]'h4192).toNat = nv.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  rw [hmv_eq] at hmv_lo hmv_hi hbge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q () m0 := hQ scr0 m0 hscr_len (fun _ _ _ => rfl) hm0
  unfold Func.wp full_k6_mtf_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hv_lt : v.toNat < nv.toNat := Nat.lt_of_not_le hc
        c0_hsplit
        · c0_hsteps!; exact hret_noop
        · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
          have hqp_v := fid_k6_off_add (mv := mv) (k := 2) (x := v) hmv_hi (by decide) (by omega)
          have hqn_v := fid_k6_off_add (mv := mv) (k := 3) (x := v) hmv_hi (by decide) (by omega)
          have hqs_v := fid_k6_off_add (mv := mv) (k := 4) (x := v) hmv_hi (by decide) (by omega)
          let invM : Mem 64 → Prop := fun mj => ∃ scrj : List (BitVec 32),
            scrj.length = c.scratch_cap ∧ (∀ idx < c.scratch_cap, (idx < 4200 ∨
              (4204 ≤ idx ∧ idx < 4224 + 2 * mv.toNat) ∨ 4224 + 5 * mv.toNat ≤ idx) →
              scrj[idx]? = scr0[idx]?) ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj
          c0_hsteps_nogrp
          refine wp_join0 invM ?_ ?_
          · rintro _ mj ⟨scrj, hlj, hkj, hmj⟩
            have hmin_j : 15744 ≤ scrj.length := by omega
            have hqs_lt : ((4224 + 4 * mv + v).setWidth 64).toNat < scrj.length := by
              rw [hlj, hqs_v]; omega
            c0_hsteps!
            refine hQ _ _ (by simp [hlj]) (fun idx hi hor => by
              rw [hmv_eq] at hor; (repeat rw [List.getElem?_set_ne (by fid_ne)])
              exact hkj idx hi hor) (m8ScrSt_eq s _ ▸ hm)
          · intro J0 hJ0
            c0_hsplit
            · have hqpv_lt : ((4224 + 2 * mv + v).setWidth 64).toNat < scr0.length := by
                rw [hqp_v]; omega
              have hqnv_lt : ((4224 + 3 * mv + v).setWidth 64).toNat < scr0.length := by
                rw [hqn_v]; omega
              let pv := scr0[((4224 + 2 * mv + v).setWidth 64).toNat]'hqpv_lt
              let nx := scr0[((4224 + 3 * mv + v).setWidth 64).toNat]'hqnv_lt
              c0_hsteps_nogrp; refine wp_join0 invM ?_ ?_
              · rintro _ m1 ⟨scr1, hl1, hk1, hm1⟩
                have hmin_1 : 15744 ≤ scr1.length := by omega
                refine wp_join0 invM ?_ ?_
                · rintro _ m2 ⟨scr2, hl2, hk2, hm2⟩
                  have hmin_2 : 15744 ≤ scr2.length := by omega
                  have h4201 : 4201 < scr2.length := by omega
                  let ol := scr2[4201]'h4201
                  have hol_o : (scr2[(@OfNat.ofNat Nat 4201 _)]'h4201).toNat = ol.toNat := rfl
                  have hqp2 : ((4224 + 2 * mv + v).setWidth 64).toNat < scr2.length := by
                    rw [hl2, hqp_v]; omega
                  have hqn2 : ((4224 + 3 * mv + v).setWidth 64).toNat < scr2.length := by
                    rw [hl2, hqn_v]; omega
                  c0_hsteps_nogrp; refine wp_join0 invM ?_ ?_
                  · rintro _ m3 ⟨scr3, hl3, hk3, hm3⟩
                    have hmin_3 : 15744 ≤ scr3.length := by omega
                    c0_hsteps!; refine hJ0 _ ⟨_, by simp [hl3], fun idx hi hor => by
                      rw [List.getElem?_set_ne (by fid_ne)]; exact hk3 idx hi hor, hm⟩
                  · intro J3 hJ3; c0_hsplit
                    · have hol_lt : ol.toNat < nv.toNat := hc
                      have hqn_ol := fid_k6_off_add (mv := mv) (k := 3) (x := ol)
                        hmv_hi (by decide) (by omega)
                      have hqn_ol_lt : ((4224 + 3 * mv + ol).setWidth 64).toNat <
                          scr2.length := by rw [hl2, hqn_ol]; omega
                      c0_hsteps!; refine hJ3 _ ⟨_, by simp [hl2], fun idx hi hor => by
                        (repeat rw [List.getElem?_set_ne (by fid_ne)]); exact hk2 idx hi hor, hm⟩
                    · c0_hsteps!; refine hJ3 _ ⟨_, by simp [hl2], fun idx hi hor => by
                        (repeat rw [List.getElem?_set_ne (by fid_ne)]); exact hk2 idx hi hor, hm⟩
                · intro J2 hJ2; c0_hsplit
                  · have hnx_lt : nx.toNat < nv.toNat := by
                      dsimp only [nx, nv, mv]; fid_norm_ofnat
                      simp (disch := fid_omega) only [bv_c0, BitVec.reduceToNat,
                        Nat.mod_eq_of_lt] at hc ⊢; exact hc
                    have hnx_nat : (scr0[4224 + 3 * (scr0[4214]'h4214).toNat + v.toNat]'(by
                        fid_omega)).toNat = nx.toNat :=
                      congrArg BitVec.toNat (m8_k6_get_congr hqn_v.symm _ _)
                    have hqp_nx := fid_k6_off_add (mv := mv) (k := 2) (x := nx)
                      hmv_hi (by decide) (by omega)
                    have hqp_nx_lt : ((4224 + 2 * mv + nx).setWidth 64).toNat <
                        scr1.length := by rw [hl1, hqp_nx]; fid_omega
                    c0_hsteps!; refine hJ2 _ ⟨_, by simp [hl1], fun idx hi hor => by
                      rw [List.getElem?_set_ne (by fid_ne)]; exact hk1 idx hi hor, hm⟩
                  · c0_hsteps!; refine hJ2 _ ⟨_, by simp [hl1], fun idx hi hor => by
                      rw [List.getElem?_set_ne (by fid_ne)]; exact hk1 idx hi hor, hm⟩
              · intro J1 hJ1; c0_hsplit
                · have hpv_lt : pv.toNat < nv.toNat := by
                    dsimp only [pv, nv, mv]; fid_norm_ofnat
                    simp (disch := fid_omega) only [bv_c0, BitVec.reduceToNat,
                      Nat.mod_eq_of_lt] at hc ⊢; exact hc
                  have hpv_nat : (scr0[4224 + 2 * (scr0[4214]'h4214).toNat + v.toNat]'(by
                      fid_omega)).toNat = pv.toNat :=
                    congrArg BitVec.toNat (m8_k6_get_congr hqp_v.symm _ _)
                  have hqn_pv := fid_k6_off_add (mv := mv) (k := 3) (x := pv)
                    hmv_hi (by decide) (by omega)
                  have hqn_pv_lt : ((4224 + 3 * mv + pv).setWidth 64).toNat <
                      scr0.length := by rw [hqn_pv]; fid_omega
                  c0_hsteps!; refine hJ1 _ ⟨_, by simp [hscr_len], fun idx hi hor => by
                    rw [List.getElem?_set_ne (by fid_ne)], hm⟩
                · c0_hsteps!; refine hJ1 _ ⟨_, by simp [hscr_len], fun idx hi hor => by
                    rw [List.getElem?_set_ne (by fid_ne)], hm⟩
            · c0_hsteps!; exact hJ0 m0 ⟨scr0, hscr_len, fun _ _ _ => rfl, hm0'⟩

/-! ## 4. `full_k6_backtrack_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_backtrack_fid`, certifying `fidK6BacktrackSpec`. -/
theorem full_k6_backtrack_fid_wp (Γ : Env) :
    ∀ a m Q X, fidK6BacktrackSpec a m Q X → Func.wp Γ full_k6_backtrack_fid_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6BacktrackSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have h4214 : 4214 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  let nv := scr0[4192]'h4192
  have hnv_o : (scr0[(@OfNat.ofNat Nat 4192 _)]'h4192).toNat = nv.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  rw [hmv_eq] at hmv_lo hmv_hi hbge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q () m0 := hQ scr0 m0 hscr_len (fun _ _ _ => rfl) hm0
  unfold Func.wp full_k6_backtrack_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun te => (te, ())) (fun te => te.toNat ≤ mv.toNat)
          ?_ ?_
        · intro _ te0 hte0
          let invB : List (BitVec 32) → Prop := fun scr => scr.length = c.scratch_cap ∧
            (∀ idx < c.scratch_cap, (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨
              (4224 + 2 * mv.toNat ≤ idx ∧ idx < 4224 + 9 * mv.toNat) ∨
              4224 + 11 * mv.toNat ≤ idx) → scr[idx]? = scr0[idx]?)
          c0_hsteps_nogrp
          refine wp_loop_break_group (brkTs := [i32]) (lpTs := [i32])
            (fun (te, ()) me => ∃ scre : List (BitVec 32), invB scre ∧
              (FullMem c (m8ScrSt s scre) ⋆ R) me)
            (fun rem (te, ()) ml => ∃ scrl : List (BitVec 32), te.toNat ≤ mv.toNat ∧
              rem = te.toNat ∧ invB scrl ∧ (FullMem c (m8ScrSt s scrl) ⋆ R) ml) ?_ ?_ ?_
          · rintro _ ⟨te, ⟨⟩⟩ me ⟨scre, ⟨hle, hke⟩, hme⟩
            have hmin_e : 15744 ≤ scre.length := by omega
            have hfin : ∀ (scrf : List (BitVec 32)) (mf : Mem 64), invB scrf →
                (FullMem c (m8ScrSt s scrf) ⋆ R) mf → Q () mf := fun scrf mf ⟨hlf, hkf⟩ hmf =>
              hQ scrf mf hlf (fun idx hi hor => by rw [hmv_eq] at hor; exact hkf idx hi hor)
                (m8ScrSt_eq s scrf ▸ hmf)
            c0_hsteps_nogrp
            refine wp_join0 (fun mf => ∃ scrf : List (BitVec 32), invB scrf ∧
                (FullMem c (m8ScrSt s scrf) ⋆ R) mf)
              (fun _ mf ⟨scrf, hbf, hmf⟩ => by c0_hsteps!; exact hfin scrf mf hbf hmf)
              (fun J0 hJ0 => by
                c0_hsplit
                · c0_hsteps!; refine hJ0 _ ⟨_, ⟨by simp [hle], fun idx hi hor => by
                    (repeat rw [List.getElem?_set_ne (by fid_ne)]); exact hke idx hi hor⟩, hm⟩
                · c0_hsteps!; refine hJ0 _ ⟨_, ⟨by simp [hle], fun idx hi hor => by
                    (repeat rw [List.getElem?_set_ne (by fid_ne)]); exact hke idx hi hor⟩, hm⟩)
          · rintro Je Lt rem ⟨te, ⟨⟩⟩ ml hJe hLt ⟨scrl, hte_le, rfl, ⟨hll, hkl⟩, hml⟩
            have hmin_l : 15744 ≤ scrl.length := by omega
            c0_hsplit
            · have hte_pos : 0 < te.toNat := hc
              have hte1 : (te - 1#32).toNat = te.toNat - 1 := m8_bv32_sub1_toNat hte_pos
              have htr0 : ((4224 : BitVec 32) + (5 : BitVec 32) * mv + te).toNat =
                  4224 + 5 * mv.toNat + te.toNat := by
                rw [← fid_zext32_toNat]
                exact fid_k6_off_add (mv := mv) (k := 5) (x := te) hmv_hi (by decide) (by omega)
              have htr_e : (((4224 : BitVec 32) + (5 : BitVec 32) * mv + te - 1#32).setWidth
                  64).toNat = 4224 + 5 * mv.toNat + te.toNat - 1 := by
                rw [fid_zext32_toNat, m8_bv32_sub1_toNat (by omega), htr0]
              have htr_lt : (((4224 : BitVec 32) + (5 : BitVec 32) * mv + te - 1#32).setWidth
                  64).toNat < scrl.length := by rw [hll, htr_e]; omega
              let lit := scrl[(((4224 : BitVec 32) + (5 : BitVec 32) * mv + te - 1#32).setWidth
                64).toNat]'htr_lt
              let v := lit >>> (1 : Nat)
              have hv_n : v.toNat = lit.toNat / 2 := m8_bv32_lshr1_toNat lit
              c0_hsplit
              · c0_hsteps!; exact hJe (te, ()) ml ⟨scrl, ⟨hll, hkl⟩, hml⟩
              · have hv_lt : v.toNat < nv.toNat := by
                  have hc' := hc; fid_norm_ofnat
                  simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                  have hlit_eq : scrl[(4294967295 + (4224 + 5 * (scr0[4214]'h4214).toNat +
                      te.toNat)) % 4294967296]'(by rw [hll]; fid_omega) = lit :=
                    m8_k6_get_congr (by rw [htr_e]; fid_omega) _ _
                  rw [hlit_eq] at hc'; dsimp only [v, nv]; rw [m8_bv32_lshr1_toNat]
                  exact Nat.lt_of_not_le hc'
                have hlit_lt : lit.toNat < 2 * mv.toNat := by omega
                have hlit_raw : (scrl[((4224 : BitVec 32) + (5 : BitVec 32) * (scr0[4214]'h4214) +
                    te - 1#32).setWidth 64 |>.toNat]'(by
                      rw [show scr0[4214] = mv from rfl]; exact htr_lt)).toNat = lit.toNat := rfl
                have hlit_v : scrl[((4224 : BitVec 32) + (5 : BitVec 32) * (scr0[4214]'h4214) +
                    te - 1#32).setWidth 64 |>.toNat]'(by
                      rw [show scr0[4214] = mv from rfl]; exact htr_lt) = lit := rfl
                have hln_lt : (lit ^^^ 1#32).toNat < 2 * mv.toNat := (m8_bv32_xor1_lt lit hlit_lt).2
                have hlv_e := fid_k6_off_add0 (x := v) (by omega)
                have hrs_e := fid_k6_off_add1 (mv := mv) (x := v) hmv_hi (by omega)
                have hv0_e := fid_k6_off_add (mv := mv) (k := 9) (x := lit)
                  hmv_hi (by decide) (by omega)
                have hv1_e := fid_k6_off_add (mv := mv) (k := 9) (x := lit ^^^ 1#32)
                  hmv_hi (by decide) (by omega)
                have hlv_lt : (((4224 : BitVec 32) + v).setWidth 64).toNat < scrl.length := by
                  rw [hll, hlv_e]; omega
                have hrs_lt : (((4224 : BitVec 32) + mv + v).setWidth 64).toNat <
                    scrl.length := by rw [hll, hrs_e]; omega
                have hv0_lt : (((4224 : BitVec 32) + (9 : BitVec 32) * mv + lit).setWidth
                    64).toNat < scrl.length := by rw [hll, hv0_e]; omega
                have hv1_lt : (((4224 : BitVec 32) + (9 : BitVec 32) * mv + (lit ^^^
                    1#32)).setWidth 64).toNat < scrl.length := by rw [hll, hv1_e]; omega
                let s1 := scrl.set (((4224 : BitVec 32) + (9 : BitVec 32) * mv + lit).setWidth
                  64).toNat (0 : BitVec 32)
                let s2 := s1.set (((4224 : BitVec 32) + (9 : BitVec 32) * mv + (lit ^^^
                  1#32)).setWidth 64).toNat (0 : BitVec 32)
                let s3 := s2.set (((4224 : BitVec 32) + v).setWidth 64).toNat (0 : BitVec 32)
                let s4 := s3.set (((4224 : BitVec 32) + mv + v).setWidth 64).toNat
                  (4294967295 : BitVec 32)
                have hv1_lt' : (((4224 : BitVec 32) + (9 : BitVec 32) * mv + (lit ^^^
                    1#32)).setWidth 64).toNat < s1.length := by rw [List.length_set]; exact hv1_lt
                have hrs_lt' : (((4224 : BitVec 32) + mv + v).setWidth 64).toNat < s3.length := by
                  simp only [s3, s2, s1, List.length_set]; exact hrs_lt
                have h4197_lt' : 4197 < s4.length := by
                  simp only [s4, s3, s2, s1, List.length_set]; omega
                c0_hsplit
                · c0_hsteps!; exact hJe (te, ()) ml ⟨scrl, ⟨hll, hkl⟩, hml⟩
                · c0_hsteps!; fid_norm_ofnat; c0_hsteps!
                  refine hLt (te - 1#32).toNat (te - 1#32, ()) _ (by omega)
                    ⟨_, by omega, rfl, ⟨by simp [hll], fun idx hi hor => by
                      dsimp only [mv, v, lit] at hor hrs_e hlv_e hv1_e hv0_e hv_lt hlit_lt
                      dsimp only [mv, v, lit] at hln_lt hnv_le
                      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by
                        erw [hrs_e]; omega), List.getElem?_set_ne (by erw [hlv_e]; omega),
                        List.getElem?_set_ne (by erw [hv1_e]; omega),
                        List.getElem?_set_ne (by erw [hv0_e]; omega)]
                      exact hkl idx hi hor⟩, hm⟩
            · c0_hsteps!; exact hJe (te, ()) ml ⟨scrl, ⟨hll, hkl⟩, hml⟩
          · intro _ Lt _ hLt; c0_hsteps!
            exact hLt te0.toNat (te0, ()) m0 ⟨scr0, hte0, rfl, ⟨hscr_len, fun _ _ _ => rfl⟩, hm0'⟩
        · intro Jt hJt; c0_hsplit
          · c0_hsteps!; exact hJt mv (Nat.le_refl _)
          · c0_hsteps!; exact hJt _ (Nat.le_of_not_lt hc)

/-! ## 5. `full_k6_ana_cl_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_ana_cl_fid`, certifying `fidK6AnaClSpec`. -/
theorem full_k6_ana_cl_fid_wp (Γ : Env) :
    ∀ a m Q X, fidK6AnaClSpec a m Q X → Func.wp Γ full_k6_ana_cl_fid_body a m Q X := by
  rintro ⟨h, cid, skip_v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6AnaClSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have hlen_ge := hok.length_ge
  have hlen_lt := hok.length_lt
  have h4214 : 4214 < scr0.length := by omega
  have h4193 : 4193 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  have h4207 : 4207 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  have hmv_d : (scr0[4214]'h4214).toNat = mv.toNat := rfl
  let nc := scr0[4193]'h4193
  have hnc_o : (scr0[(@OfNat.ofNat Nat 4193 _)]'h4193).toNat = nc.toNat := rfl
  let nv := scr0[4192]'h4192
  have hnv_o : (scr0[(@OfNat.ofNat Nat 4192 _)]'h4192).toNat = nv.toNat := rfl
  let acap := scr0[4207]'h4207
  have hacap_o : (scr0[(@OfNat.ofNat Nat 4207 _)]'h4207).toNat = acap.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  have hac_eq : (scr0[4207]?.getD 0#32) = acap := m8_k6_get_eq h4207
  rw [hmv_eq] at hmv_lo hmv_hi hbge hlen_ge
  rw [hac_eq] at hlen_ge
  have hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length := hlen_ge
  have hcap_lt : scr0.length < 2 ^ 30 := hlen_lt
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q () m0 := hQ scr0 m0 hscr_len (fun _ _ _ _ _ _ _ _ => rfl) hm0
  unfold Func.wp full_k6_ana_cl_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hcid : cid.toNat < nc.toNat := Nat.lt_of_not_le hc
        c0_hsplit
        · c0_hsteps!; exact hret_noop
        · have hnc_le : nc.toNat ≤ 4 * mv.toNat := by fid_omega
          c0_hsplit
          · c0_hsteps!; exact hret_noop
          · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
            have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := cid)
              hmv_hi (by decide) (by omega)
            have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := cid)
              hmv_hi (by decide) (by omega)
            have hco_lt : ((4224 + 29 * mv + cid).setWidth 64).toNat < scr0.length := by
              rw [hco_e]; omega
            have hcm_lt : ((4224 + 33 * mv + cid).setWidth 64).toNat < scr0.length := by
              rw [hcm_e]; omega
            let off := scr0[((4224 + 29 * mv + cid).setWidth 64).toNat]'hco_lt
            let cm := scr0[((4224 + 33 * mv + cid).setWidth 64).toNat]'hcm_lt
            let sz := cm &&& 0xFFFF#32
            have hsz_le : sz.toNat ≤ 65535 := m8_and_ffff_le cm
            have hcl_ok := hok.clause_ok (cid := cid.toNat) (by rw [m8_k6_get_eq h4193]; exact hcid)
            dsimp only at hcl_ok
            rw [hmv_eq, hac_eq] at hcl_ok
            have hoff_eq : (scr0[4224 + 29 * mv.toNat + cid.toNat]?.getD 0#32) = off := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              exact m8_k6_get_congr hco_e.symm _ _
            have hcm_eq : (scr0[4224 + 33 * mv.toNat + cid.toNat]?.getD 0#32) = cm := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              exact m8_k6_get_congr hcm_e.symm _ _
            rw [hoff_eq, hcm_eq] at hcl_ok
            have hos_le : off.toNat + sz.toNat ≤ acap.toNat := hcl_ok.1
            c0_hsplit
            · c0_hsteps!; exact hret_noop
            · have hmo_n : (mv <<< (1 : Nat)).toNat = 2 * mv.toNat :=
                m8_bv32_shl1_toNat (by omega)
              let invAP : List (BitVec 32) → Prop := fun scr1 => scr1.length = c.scratch_cap ∧
                (∀ idx < c.scratch_cap, idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
                  (idx < 4224 + 6 * mv.toNat ∨ 4224 + 9 * mv.toNat ≤ idx) →
                  (idx < 4224 + 43 * mv.toNat ∨ 4224 + 45 * mv.toNat ≤ idx) →
                  scr1[idx]? = scr0[idx]?)
              let invA : Mem 64 → Prop := fun m1 => ∃ scr1 : List (BitVec 32), invAP scr1 ∧
                (FullMem c (m8ScrSt s scr1) ⋆ R) m1
              c0_hsteps_nogrp; refine wp_join0 invA ?_ ?_
              · rintro _ m1 ⟨scr1, ⟨hl1, hk1⟩, hm1⟩
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i32])
                  (fun rem (i, ()) ml => ∃ scrl : List (BitVec 32), i.toNat ≤ sz.toNat ∧
                    rem = sz.toNat - i.toNat ∧ invAP scrl ∧ (FullMem c (m8ScrSt s scrl) ⋆ R) ml)
                  ?_ ?_
                · rintro Li rem ⟨i, ⟨⟩⟩ ml hLi ⟨scrl, hi_le, rfl, ⟨hll, hkl⟩, hml⟩
                  have hmin_l : 15744 ≤ scrl.length := by omega
                  have hcm_get : scr0[(4224 + 33 * (scr0[4214]'h4214).toNat + cid.toNat) %
                      4294967296]'(by fid_omega) = cm :=
                    m8_k6_get_congr (by rw [hcm_e]; fid_omega) _ _
                  have hoff_get : scr0[(4224 + 29 * (scr0[4214]'h4214).toNat + cid.toNat) %
                      4294967296]'(by fid_omega) = off :=
                    m8_k6_get_congr (by rw [hco_e]; fid_omega) _ _
                  c0_hsplit
                  · have hi_lt : i.toNat < sz.toNat := by
                      have hc' := hc; dsimp only [sz]; fid_norm_ofnat
                      simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat,
                        Nat.mod_eq_of_lt] at hc' ⊢
                      have h1 : (scr0[4224 + 33 * (scr0[4214]'h4214).toNat + cid.toNat]'(by
                          fid_omega)).toNat = cm.toNat :=
                        congrArg BitVec.toNat (m8_k6_get_congr hcm_e.symm _ _)
                      try rw [h1] at hc'
                      try rw [congrArg BitVec.toNat hcm_get] at hc'
                      exact hc'
                    have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_bv32_add1_toNat hi_lt (by omega)
                    have har_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := off) (y := i)
                      hmv_hi (by decide) (by omega)
                    have har_nat : 4224 + 45 * mv.toNat + off.toNat + i.toNat < scr0.length := by
                      omega
                    have har_lt : (((4224 : BitVec 32) + (45 : BitVec 32) * mv + off + i).setWidth
                        64).toNat < scrl.length := by rw [hll, ← hscr_len, har_e]; exact har_nat
                    let l := scrl[(((4224 : BitVec 32) + (45 : BitVec 32) * mv + off + i).setWidth
                      64).toNat]'har_lt
                    let v := l >>> (1 : Nat)
                    have hl_get : scrl[(4224 + 45 * mv.toNat + off.toNat + i.toNat) %
                        4294967296]'(by
                          rw [hll, ← hscr_len, Nat.mod_eq_of_lt (by omega)]; exact har_nat) = l :=
                      m8_k6_get_congr (by rw [har_e, Nat.mod_eq_of_lt (by omega)]) _ _
                    c0_hsteps_nogrp
                    refine wp_join0 invA (fun _ mj ⟨scrj, hj, hmj⟩ => by
                        c0_hsteps!; exact hLi (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj
                          (by omega) ⟨scrj, by omega, rfl, hj, hmj⟩)
                      (fun Jstep hJstep => by
                        c0_hsplit
                        · have hv_lt : v.toNat < nv.toNat := by
                            have hc' := hc; fid_norm_ofnat
                            simp (disch := fid_omega) only [bv_c0, Nat.reducePow,
                              BitVec.reduceToNat, Nat.mod_eq_of_lt] at hc'
                            try rw [hmv_d] at hc'
                            have h1 : scr0[4224 + 29 * (scr0[4214]'h4214).toNat + cid.toNat]'(by
                                dsimp only [mv] at hco_e ⊢; omega) = off :=
                              m8_k6_get_congr (by dsimp only [mv] at hco_e ⊢; exact hco_e.symm) _ _
                            have h2 : scrl[(4224 + 45 * (scr0[4214]'h4214).toNat + (scr0[4224 + 29 *
                                (scr0[4214]'h4214).toNat + cid.toNat]'(by
                                  dsimp only [mv] at hco_e ⊢; omega)).toNat + i.toNat) %
                                4294967296]'(by
                                  rw [h1, hll, Nat.mod_eq_of_lt (by omega), ← hscr_len]
                                  exact har_nat) = l :=
                              m8_k6_get_congr (by
                                rw [h1, Nat.mod_eq_of_lt (by omega)]
                                dsimp only [mv] at har_e ⊢; exact har_e.symm) _ har_lt
                            rw [h2] at hc'; dsimp only [v, nv]; rw [m8_bv32_lshr1_toNat]; exact hc'
                          have hoff_raw : (scr0[((4224 : BitVec 32) + (29 : BitVec 32) *
                              (scr0[4214]'h4214) + cid).setWidth 64 |>.toNat]'(by
                                rw [show scr0[4214] = mv from rfl]; exact hco_lt)).toNat =
                              off.toNat := rfl
                          have hl_raw : (scrl[((4224 : BitVec 32) + (45 : BitVec 32) *
                              (scr0[4214]'h4214) + off + i).setWidth 64 |>.toNat]'(by
                                rw [show scr0[4214] = mv from rfl]; exact har_lt)).toNat =
                              l.toNat := rfl
                          c0_hsplit
                          · have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := v)
                              hmv_hi (by decide) (by omega)
                            have hfl_lt : ((4224 + 6 * mv + v).setWidth 64).toNat <
                                scrl.length := by rw [hll, hfl_e]; omega
                            c0_hsplit
                            · c0_hsteps_nogrp; refine wp_join0 invA ?_ ?_
                              · rintro _ ma ⟨scra, ⟨hla, hka⟩, hma⟩
                                have hmin_a : 15744 ≤ scra.length := by omega
                                have hlv_e := fid_k6_off_add0 (x := v) (by omega)
                                have hlv_lt : (((4224 : BitVec 32) + v).setWidth 64).toNat <
                                    scra.length := by rw [hla, hlv_e]; omega
                                c0_hsteps_nogrp
                                refine wp_join0 invA
                                  (fun _ mj h => by c0_hsteps!; exact hJstep mj h)
                                  (fun Js0 hJs0 => by
                                    c0_hsplit
                                    · have hrs_e := fid_k6_off_add1 (mv := mv) (x := v)
                                        hmv_hi (by omega)
                                      have hrs_lt : (((4224 : BitVec 32) + mv + v).setWidth
                                          64).toNat < scra.length := by rw [hla, hrs_e]; omega
                                      c0_hsteps_nogrp
                                      refine wp_join0 invA
                                        (fun _ mj h => by c0_hsteps!; exact hJs0 mj h)
                                        (fun J5 hJ5 => by
                                          c0_hsplit
                                          · c0_hsteps_nogrp
                                            refine wp_join0 invA
                                              (fun _ mj h => by c0_hsteps!; exact hJ5 mj h)
                                              (fun J6 hJ6 => by
                                                c0_hsplit
                                                · have hnres_lt : (scra[4210]'(by omega)).toNat <
                                                      2 * mv.toNat := by
                                                    fid_norm_ofnat; have := hmo_n
                                                    dsimp only [mv] at this hc ⊢; omega
                                                  have hres_e := fid_k6_off_add (mv := mv) (k := 43)
                                                    (x := scra[4210]'(by omega)) hmv_hi (by decide)
                                                    (by omega)
                                                  have hres_lt : (((4224 : BitVec 32) +
                                                      (43 : BitVec 32) * mv + scra[4210]'(by
                                                        omega)).setWidth 64).toNat <
                                                      scra.length := by rw [hres_e]; omega
                                                  c0_hsteps!; refine hJ6 _ ⟨_, ⟨by simp [hla],
                                                    fun idx hi h08 h09 h10 h12 ha hb => by
                                                      rw [List.getElem?_set_ne (by
                                                        change (4210 : Nat) ≠ idx; omega)]
                                                      rw [List.getElem?_set_ne (by
                                                        dsimp only [mv] at hres_e ⊢
                                                        erw [hres_e]; omega)]
                                                      exact hka idx hi h08 h09 h10 h12 ha hb⟩, hm⟩
                                                · c0_hsteps!; refine hJ6 _ ⟨_, ⟨by simp [hla],
                                                    fun idx hi h08 h09 h10 h12 ha hb => by
                                                      rw [List.getElem?_set_ne (by
                                                        change (4210 : Nat) ≠ idx; omega)]
                                                      exact hka idx hi h08 h09 h10 h12 ha hb⟩, hm⟩)
                                          · c0_hsteps!; exact hJ5 ma ⟨scra, ⟨hla, hka⟩, hma⟩)
                                    · c0_hsteps_nogrp
                                      refine wp_join0 invA
                                        (fun _ mj h => by c0_hsteps!; exact hJs0 mj h)
                                        (fun Js1 hJs1 => by
                                          c0_hsplit
                                          · c0_hsteps!; refine hJs1 _ ⟨_, ⟨by simp [hla],
                                              fun idx hi h08 h09 h10 h12 ha hb => by
                                                rw [List.getElem?_set_ne (by fid_ne)]
                                                exact hka idx hi h08 h09 h10 h12 ha hb⟩, hm⟩
                                          · c0_hsteps_nogrp
                                            refine wp_join0 invA
                                              (fun _ mj h => by c0_hsteps!; exact hJs1 mj h)
                                              (fun Js2 hJs2 => by
                                                c0_hsplit
                                                · have hnkl_lt : (scra[4209]'(by omega)).toNat <
                                                      mv.toNat := by fid_omega
                                                  have hkl_e := fid_k6_off_add (mv := mv) (k := 8)
                                                    (x := scra[4209]'(by omega)) hmv_hi (by decide)
                                                    (by omega)
                                                  have hkl_lt : (((4224 : BitVec 32) +
                                                      (8 : BitVec 32) * mv + scra[4209]'(by
                                                        omega)).setWidth 64).toNat <
                                                      scra.length := by rw [hkl_e]; omega
                                                  c0_hsteps!; refine hJs2 _ ⟨_, ⟨by simp [hla],
                                                    fun idx hi h08 h09 h10 h12 ha hb => by
                                                      (repeat rw [List.getElem?_set_ne (by fid_ne)])
                                                      exact hka idx hi h08 h09 h10 h12 ha hb⟩, hm⟩
                                                · c0_hsteps!
                                                  exact hJs2 ma ⟨scra, ⟨hla, hka⟩, hma⟩)))
                              · intro Ja hJa; c0_hsplit
                                · have hfl_ne4208 : (((4224 : BitVec 32) + (6 : BitVec 32) * mv +
                                      v).setWidth 64).toNat ≠ 4208 := by rw [hfl_e]; omega
                                  have hnana_lt : (scrl[4208]'(by omega)).toNat < mv.toNat := by
                                    have hc' := hc; fid_norm_ofnat
                                    simp (disch := fid_omega) only [bv_c0, Nat.reducePow,
                                      BitVec.reduceToNat, Nat.mod_eq_of_lt] at hc'
                                    rw [List.getElem_set_ne (by fid_omega)] at hc'; exact hc'
                                  let scrf := scrl.set (((4224 : BitVec 32) + (6 : BitVec 32) *
                                    mv + v).setWidth 64).toNat ((scrl[(((4224 : BitVec 32) +
                                      (6 : BitVec 32) * mv + v).setWidth 64).toNat]'hfl_lt) |||
                                      2#32)
                                  have hfl_len : scrf.length = scrl.length := List.length_set
                                  have h4208_f : 4208 < scrf.length := by rw [hfl_len, hll]; omega
                                  have hana_e := fid_k6_off_add (mv := mv) (k := 7)
                                    (x := scrf[4208]'h4208_f) hmv_hi (by decide)
                                    (by rw [List.getElem_set_ne hfl_ne4208]; omega)
                                  have hana_lt : (((4224 : BitVec 32) + (7 : BitVec 32) * mv +
                                      scrf[4208]'h4208_f).setWidth 64).toNat < scrf.length := by
                                    have : scrl.length = scr0.length := hll.trans hscr_len.symm
                                    have h1 : (scrf[4208]'h4208_f).toNat =
                                        (scrl[4208]'(by omega)).toNat :=
                                      congrArg BitVec.toNat (List.getElem_set_ne hfl_ne4208 h4208_f)
                                    rw [hana_e, h1, hfl_len]; omega
                                  c0_hsteps!; refine hJa _ ⟨_, ⟨by simp [hll],
                                    fun idx hi h08 h09 h10 h12 ha hb => by
                                      rw [List.getElem?_set_ne (by
                                        change (4208 : Nat) ≠ idx; omega)]
                                      rw [List.getElem?_set_ne (by
                                        change (((4224 : BitVec 32) + (7 : BitVec 32) * mv +
                                          scrf[4208]'h4208_f).setWidth 64).toNat ≠ idx
                                        rw [hana_e, List.getElem_set_ne hfl_ne4208]; omega)]
                                      rw [List.getElem?_set_ne (by
                                        change (((4224 : BitVec 32) + (6 : BitVec 32) * mv +
                                          v).setWidth 64).toNat ≠ idx
                                        rw [hfl_e]; omega)]
                                      exact hkl idx hi h08 h09 h10 h12 ha hb⟩, hm⟩
                                · c0_hsteps!; refine hJa _ ⟨_, ⟨by simp [hll],
                                    fun idx hi h08 h09 h10 h12 ha hb => by
                                      rw [List.getElem?_set_ne (by
                                        change (((4224 : BitVec 32) + (6 : BitVec 32) * mv +
                                          v).setWidth 64).toNat ≠ idx
                                        rw [hfl_e]; omega)]
                                      exact hkl idx hi h08 h09 h10 h12 ha hb⟩, hm⟩
                            · c0_hsteps!; exact hJstep ml ⟨scrl, ⟨hll, hkl⟩, hml⟩
                          · c0_hsteps!; exact hJstep ml ⟨scrl, ⟨hll, hkl⟩, hml⟩
                        · c0_hsteps!; exact hJstep ml ⟨scrl, ⟨hll, hkl⟩, hml⟩)
                  · c0_hsteps!; rw [m8ScrSt_eq] at hml
                    exact hQ scrl ml hll (fun idx hi h08 h09 h10 h12 ha hb => by
                      rw [hmv_eq] at ha hb; exact hkl idx hi h08 h09 h10 h12 ha hb) hml
                · intro Li hLi; c0_hsteps!; exact hLi sz.toNat (0#32, ()) m1
                    ⟨scr1, Nat.zero_le _, by simp, ⟨hl1, hk1⟩, hm1⟩
              · intro J1 hJ1; c0_hsplit
                · have hnres_lt : (scr0[4210]'(by omega)).toNat < 2 * mv.toNat := by fid_omega
                  have hres_e := fid_k6_off_add (mv := mv) (k := 43)
                    (x := scr0[4210]'(by omega)) hmv_hi (by decide) (by omega)
                  c0_hsteps!; refine hJ1 _ ⟨_, ⟨by simp [hscr_len],
                    fun idx hi h08 h09 h10 h12 ha hb => by
                      (repeat rw [List.getElem?_set_ne (by fid_ne)])⟩, hm⟩
                · c0_hsteps!; refine hJ1 _ ⟨_, ⟨by simp [hscr_len],
                    fun idx hi h08 h09 h10 h12 ha hb =>
                      List.getElem?_set_ne (Ne.symm h10)⟩, hm⟩

/-! ## 6. `full_k6_core_fid_wp` -/

/-- Loop invariant for `full_k6_core_fid`: preserves `FidK6BufOk`, everything outside
`o_flags` and `o_cl_meta`, and the low 16 bits + `KM_LRN` bit of `o_cl_meta[0..nc)`. -/
private def FidCoreInv (scr0 : List (BitVec 32)) (mv nc : BitVec 32)
    (scr : List (BitVec 32)) : Prop :=
  FidK6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ idx < scr0.length,
    (idx < 4224 + 6 * mv.toNat ∨
      (4224 + 7 * mv.toNat ≤ idx ∧ idx < 4224 + 33 * mv.toNat) ∨
      4224 + 37 * mv.toNat ≤ idx) →
    scr[idx]? = scr0[idx]?) ∧
  (∀ cid < nc.toNat,
    let m0 := scr0[4224 + 33 * mv.toNat + cid]?.getD 0#32
    let m1 := scr[4224 + 33 * mv.toNat + cid]?.getD 0#32
    (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
    (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32))

private theorem fidCoreInv_mv {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (h : FidCoreInv scr0 mv nc scr) : scr[4214]?.getD 0#32 = mv := by
  have hk := h.2.2.1 4214 h4214 (Or.inl (by omega))
  rw [hk, hmv_eq]

private theorem fidCoreInv_set_meta {scr0 : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hnc_le : nc.toNat ≤ 4 * mv.toNat) {scr : List (BitVec 32)} (hik : FidCoreInv scr0 mv nc scr)
    {cid : Nat} (hcid : cid < nc.toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((scr[4224 + 33 * mv.toNat + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) =
      ((scr[4224 + 33 * mv.toNat + cid]?.getD 0#32) &&& 0x40000000#32)) :
    FidCoreInv scr0 mv nc (scr.set (4224 + 33 * mv.toNat + cid) v) := by
  have hmv' := fidCoreInv_mv h4214 hmv_eq hik
  have hb := hik.1.base_ge; rw [hmv'] at hb
  have hok' : FidK6BufOk (scr.set (4224 + 33 * mv.toNat + cid) v) := by
    have h1 := fidK6BufOk_set_core_meta hik.1 (cid := cid) (v := v)
      (by rw [hmv']; omega) (by rw [hmv']; exact hsz) (by rw [hmv']; exact hlrn)
    rwa [hmv'] at h1
  refine ⟨hok', by simp [hik.2.1], fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.1 idx hi hor
  · by_cases heq : j = cid
    · subst heq
      dsimp only
      rw [List.getElem?_set_self (by omega), Option.getD_some, hsz, hlrn]
      exact hik.2.2.2 j hj
    · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.2 j hj

private theorem fidCoreInv_set_flags {scr0 : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    {scr : List (BitVec 32)} (hik : FidCoreInv scr0 mv nc scr)
    {v : Nat} (hv : v < mv.toNat) (val : BitVec 32) :
    FidCoreInv scr0 mv nc (scr.set (4224 + 6 * mv.toNat + v) val) := by
  have hmv' := fidCoreInv_mv h4214 hmv_eq hik
  have hok' : FidK6BufOk (scr.set (4224 + 6 * mv.toNat + v) val) := by
    have h1 := fidK6BufOk_set_flags hik.1 (i := v) (by rw [hmv']; exact hv) val
    rwa [hmv'] at h1
  refine ⟨hok', by simp [hik.2.1], fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.1 idx hi hor
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.2 j hj

private theorem fidCoreInv_set_meta_pres {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hnc_le : nc.toNat ≤ 4 * mv.toNat) (hik : FidCoreInv scr0 mv nc scr)
    {cid : BitVec 32} (hcid : cid.toNat < nc.toNat) {v : BitVec 32}
    (he : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hlt : ((4224 + 33 * mv + cid).setWidth 64).toNat < scr.length)
    (hpres : (v &&& 0xFFFF#32) =
        ((scr[((4224 + 33 * mv + cid).setWidth 64).toNat]'hlt) &&& 0xFFFF#32) ∧
      (v &&& 0x40000000#32) =
        ((scr[((4224 + 33 * mv + cid).setWidth 64).toNat]'hlt) &&& 0x40000000#32)) :
    FidCoreInv scr0 mv nc (scr.set ((4224 + 33 * mv + cid).setWidth 64).toNat v) := by
  have hll := hik.2.1
  have h1 := fidCoreInv_set_meta h4214 hmv_eq hnc_le hik hcid (v := v)
    (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        m8_k6_get_congr he.symm (by omega) hlt]; exact hpres.1)
    (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        m8_k6_get_congr he.symm (by omega) hlt]; exact hpres.2)
  simpa only [he] using h1

private theorem fidCoreInv_set_flags_e {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hik : FidCoreInv scr0 mv nc scr) {v : BitVec 32} (hv : v.toNat < mv.toNat)
    (he : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (val : BitVec 32) :
    FidCoreInv scr0 mv nc (scr.set ((4224 + 6 * mv + v).setWidth 64).toNat val) := by
  simpa only [he] using fidCoreInv_set_flags h4214 hmv_eq hik hv val

private theorem fidCore_ne45_aux {m v ti : Nat} (hm : m ≤ 8192) (hv : v < m) (hti : ti ≤ m) :
    (4224 + 6 * m + v) % 4294967296 ≠ (4224 + m + v) % 4294967296 ∧
    4224 + m + v < 4294967296 ∧ 4224 + 6 * m + v ≠ 4224 + m + v ∧
    4224 + 5 * m + (ti - 1) < 4294967296 := by
  have h1 : 4224 + 6 * m + v < 4294967296 := by omega
  have h2 : 4224 + m + v < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  exact ⟨Nat.ne_of_gt (by omega), h2, Nat.ne_of_gt (by omega), by omega⟩

private theorem fidCore_scrt2_rsz_lt {xs : List (BitVec 32)} {idx : Nat} {hb1 hb2}
    {mr rsz j : BitVec 32} (hmr : xs[idx]'hb1 = mr)
    (hrsz : (mr ||| 0x80000000#32) &&& 0xFFFF#32 = rsz)
    (hc : j.toNat <
      ((xs.set idx (xs[idx]'hb1 ||| 2147483648#32))[idx]'hb2).toNat % 65536) :
    j.toNat < rsz.toNat := by
  have h1 : (xs.set idx (xs[idx]'hb1 ||| 2147483648#32))[idx]'hb2 = mr ||| 0x80000000#32 := by
    rw [List.getElem_set_self, hmr]
  rw [h1, ← FidK6Tactics.fid_bv32_and_ffff_toNat, hrsz] at hc
  exact hc

private abbrev ftTi (scr0 : List (BitVec 32)) (h4214 : 4214 < scr0.length) (ti : BitVec 32) :
    Nat :=
  (4224 + 5 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + ti.toNat)) % 4294967296

private abbrev ftFl (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length) : Nat :=
  (4224 + 6 * (scr0[4214]'h4214).toNat +
    (scrt[ftTi scr0 h4214 ti]'hb0).toNat / 2) % 4294967296

private abbrev ftS1 (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length)
    (hb1 : ftFl scr0 scrt h4214 ti hb0 < scrt.length) : List (BitVec 32) :=
  scrt.set (ftFl scr0 scrt h4214 ti hb0) (scrt[ftFl scr0 scrt h4214 ti hb0]'hb1 &&& ~~~2#32)

private abbrev ftRs (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length) : Nat :=
  (4224 + (scr0[4214]'h4214).toNat + (scrt[ftTi scr0 h4214 ti]'hb0).toNat / 2) % 4294967296

private abbrev ftMr (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length)
    (hb1 : ftFl scr0 scrt h4214 ti hb0 < scrt.length)
    (hb_r : ftRs scr0 scrt h4214 ti hb0 < (ftS1 scr0 scrt h4214 ti hb0 hb1).length) : Nat :=
  (4224 + 33 * (scr0[4214]'h4214).toNat +
    ((ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb_r).toNat) % 4294967296

private abbrev ftS2 (scr0 scrt : List (BitVec 32)) (h4214 : 4214 < scr0.length)
    (ti : BitVec 32) (hb0 : ftTi scr0 h4214 ti < scrt.length)
    (hb1 : ftFl scr0 scrt h4214 ti hb0 < scrt.length)
    (hb_k hb_v : ftRs scr0 scrt h4214 ti hb0 < (ftS1 scr0 scrt h4214 ti hb0 hb1).length)
    (hb4 : ftMr scr0 scrt h4214 ti hb0 hb1 hb_v < (ftS1 scr0 scrt h4214 ti hb0 hb1).length) :
    List (BitVec 32) :=
  let s1 := ftS1 scr0 scrt h4214 ti hb0 hb1
  s1.set (ftMr scr0 scrt h4214 ti hb0 hb1 hb_k)
    (s1[ftMr scr0 scrt h4214 ti hb0 hb1 hb_v]'hb4 ||| 2147483648#32)

private theorem fidCore_trace_hj_lt {scr0 scrt : List (BitVec 32)}
    {mv ti ti' v rsn mr rsz j : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (hmv_hi : mv.toNat ≤ 8192) (_hlt : scrt.length = scr0.length)
    (hti_pos : 0 < ti.toNat) (hti_le : ti.toNat ≤ mv.toNat) (hti1 : ti'.toNat = ti.toNat - 1)
    (htr_e : ((4224 + 5 * mv + ti').setWidth 64).toNat = 4224 + 5 * mv.toNat + ti'.toNat)
    (htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat < scrt.length)
    (hv_eq : (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b).toNat / 2 = v.toNat)
    (hv_lt : v.toNat < mv.toNat)
    (hfl_e : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (hfl_b : ((4224 + 6 * mv + v).setWidth 64).toNat < scrt.length)
    (hrs_e : ((4224 + mv + v).setWidth 64).toNat = 4224 + mv.toNat + v.toNat)
    (hrs_b : ((4224 + mv + v).setWidth 64).toNat <
      (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
        (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32)).length)
    (hrsn : (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
      (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32))[
        ((4224 + mv + v).setWidth 64).toNat]'hrs_b = rsn)
    (hrsn_lt : rsn.toNat < 4 * mv.toNat)
    (hmr_e : ((4224 + 33 * mv + rsn).setWidth 64).toNat = 4224 + 33 * mv.toNat + rsn.toNat)
    (hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat <
      (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
        (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32)).length)
    (hmr_d : (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
      (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32))[
        ((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b = mr)
    (hrsz : ((mr ||| 0x80000000#32) &&& 0xFFFF#32) = rsz)
    {hb0 hb1 hb2 hb3 hb4 hb5 hb6}
    (hc : j.toNat < ((ftS2 scr0 scrt h4214 ti hb0 hb1 hb2 hb3 hb4)[
      (4224 + 33 * (scr0[4214]'h4214).toNat +
        ((ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb5).toNat) %
      4294967296]'hb6).toNat % 65536) :
    j.toNat < rsz.toNat := by
  have hti_u : 4224 + 5 * mv.toNat + (ti.toNat - 1) < 4294967296 := by
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq htr_b hfl_b; omega
  have hfl_u : 4224 + 6 * mv.toNat + v.toNat < 4294967296 := by
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq htr_b hfl_b; omega
  have hrs_u : 4224 + mv.toNat + v.toNat < 4294967296 := by
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq htr_b hfl_b; omega
  have hmr_u : 4224 + 33 * mv.toNat + rsn.toNat < 4294967296 := by
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq htr_b hfl_b; omega
  have htr1 : ftTi scr0 h4214 ti = ((4224 + 5 * mv + ti').setWidth 64).toNat := by
    dsimp only [ftTi]; rw [htr_e, hmv_d, fid_sub1_mod32 _ _ hti_pos hti_u, hti1]
  have hv_g : (scrt[ftTi scr0 h4214 ti]'hb0).toNat / 2 = v.toNat := by
    rw [m8_k6_get_congr htr1 hb0 htr_b, hv_eq]
  have hfl1 : ftFl scr0 scrt h4214 ti hb0 = ((4224 + 6 * mv + v).setWidth 64).toNat := by
    dsimp only [ftFl]; rw [hv_g, hmv_d, hfl_e, Nat.mod_eq_of_lt hfl_u]
  have hrs1 : ftRs scr0 scrt h4214 ti hb0 = ((4224 + mv + v).setWidth 64).toNat := by
    dsimp only [ftRs]; rw [hv_g, hmv_d, hrs_e, Nat.mod_eq_of_lt hrs_u]
  have hne_fl_rs :
      ((4224 + 6 * mv + v).setWidth 64).toNat ≠ ((4224 + mv + v).setWidth 64).toNat := by
    rw [hfl_e, hrs_e]
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq hv_g htr_b hfl_b htr1 hfl1 hrs1; omega
  have hne_fl_mr :
      ((4224 + 6 * mv + v).setWidth 64).toNat ≠ ((4224 + 33 * mv + rsn).setWidth 64).toNat := by
    rw [hfl_e, hmr_e]
    clear hc hmr_d hrsn hmr_b hrs_b hv_eq hv_g htr_b hfl_b htr1 hfl1 hrs1; omega
  have h_rsn : ∀ {w : BitVec 32} {hb_r}, (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat w)[
      ((4224 + mv + v).setWidth 64).toNat]'hb_r = rsn := by
    intro w hb_r
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, List.getElem?_set_ne hne_fl_rs, ← hrsn,
      ← List.getElem?_eq_getElem, List.getElem?_set_ne hne_fl_rs]
  have hset1 : ftS1 scr0 scrt h4214 ti hb0 hb1 = scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
      (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32) := by
    simp only [ftS1, hfl1]
  have hinner : ∀ {hb_r},
      (ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb_r = rsn := by
    intro hb_r
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, hset1, hrs1, ← hrsn,
      ← List.getElem?_eq_getElem]
  refine fidCore_scrt2_rsz_lt (mr := mr) ?_ hrsz hc
  dsimp only [ftS2, ftMr]
  rw [← Option.some_inj, ← List.getElem?_eq_getElem, hinner, hset1, hmv_d,
    Nat.mod_eq_of_lt hmr_u, ← hmr_e, List.getElem?_set_ne hne_fl_mr, ← hmr_d,
    ← List.getElem?_eq_getElem, List.getElem?_set_ne hne_fl_mr]

private theorem fidCore_trace_lv_aux {scr0 scr_raw scrt1 scrt2 scrj : List (BitVec 32)}
    {mv rsn mr roff j nv : BitVec 32} {rsn_a rsn_b rsn_c : Nat}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (hset_eq : scr_raw = scrt1)
    (hra : rsn_a = rsn.toNat) (hrb : rsn_b = rsn.toNat) (hrc : rsn_c = rsn.toNat)
    (hmr_u : 4224 + 33 * mv.toNat + rsn.toNat < 4294967296)
    (hor_u : 4224 + 29 * mv.toNat + rsn.toNat < 4294967296)
    (har_u : 4224 + 45 * mv.toNat + roff.toNat + j.toNat < 4294967296)
    (hmr_e : ((4224 + 33 * mv + rsn).setWidth 64).toNat = 4224 + 33 * mv.toNat + rsn.toNat)
    (hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt1.length)
    (hmr_d : scrt1[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b = mr)
    (hscrt2 : scrt2 = scrt1.set ((4224 + 33 * mv + rsn).setWidth 64).toNat (mr ||| 0x80000000#32))
    (hor_e : ((4224 + 29 * mv + rsn).setWidth 64).toNat = 4224 + 29 * mv.toNat + rsn.toNat)
    (hor_b2 : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt2.length)
    (hroff_d : scrt2[((4224 + 29 * mv + rsn).setWidth 64).toNat]'hor_b2 = roff)
    (har_e : ((4224 + 45 * mv + roff + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + roff.toNat + j.toNat)
    (har_b : ((4224 + 45 * mv + roff + j).setWidth 64).toNat < scrj.length)
    {hb4 : (4224 + 33 * (scr0[4214]'h4214).toNat + rsn_b) % 4294967296 < scr_raw.length}
    {hb6 : (4224 + 29 * (scr0[4214]'h4214).toNat + rsn_c) % 4294967296 <
      (scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn_a) % 4294967296)
        (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn_b) % 4294967296]'hb4 |||
          2147483648#32)).length}
    {hb7 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      ((scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn_a) % 4294967296)
        (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn_b) % 4294967296]'hb4 |||
          2147483648#32))[(4224 + 29 * (scr0[4214]'h4214).toNat + rsn_c) %
        4294967296]'hb6).toNat + j.toNat) % 4294967296 < scrj.length}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      ((scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn_a) % 4294967296)
        (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn_b) % 4294967296]'hb4 |||
          2147483648#32))[(4224 + 29 * (scr0[4214]'h4214).toNat + rsn_c) %
        4294967296]'hb6).toNat + j.toNat) % 4294967296]'hb7).toNat / 2 <
      (scr0[4192]'h4192).toNat) :
    ((scrj[((4224 + 45 * mv + roff + j).setWidth 64).toNat]'har_b) >>> (1 : Nat)).toNat <
      nv.toNat := by
  subst hset_eq; subst hra; subst hrb; subst hrc
  have hmr_i : (4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296 =
      ((4224 + 33 * mv + rsn).setWidth 64).toNat := by
    rw [hmv_d, hmr_e, Nat.mod_eq_of_lt hmr_u]
  have hmr_g :
      scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296]'hb4 = mr := by
    rw [m8_k6_get_congr hmr_i hb4 hmr_b, hmr_d]
  have hor_i : (4224 + 29 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296 =
      ((4224 + 29 * mv + rsn).setWidth 64).toNat := by
    rw [hmv_d, hor_e, Nat.mod_eq_of_lt hor_u]
  have hset2 :
      scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296)
          (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296]'hb4 |||
            2147483648#32) =
        scrt2 := by
    rw [hmr_g, hmr_i]; exact hscrt2.symm
  have hroff_g :
      (scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296)
        (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296]'hb4 |||
          2147483648#32))[(4224 + 29 * (scr0[4214]'h4214).toNat + rsn.toNat) %
        4294967296]'hb6 = roff := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, hset2, hor_i, ← hroff_d,
      ← List.getElem?_eq_getElem]
  have har_i :
      (4224 + 45 * (scr0[4214]'h4214).toNat +
        ((scr_raw.set ((4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296)
          (scr_raw[(4224 + 33 * (scr0[4214]'h4214).toNat + rsn.toNat) % 4294967296]'hb4 |||
            2147483648#32))[(4224 + 29 * (scr0[4214]'h4214).toNat + rsn.toNat) %
          4294967296]'hb6).toNat + j.toNat) % 4294967296 =
        ((4224 + 45 * mv + roff + j).setWidth 64).toNat := by
    rw [hroff_g, hmv_d, har_e, Nat.mod_eq_of_lt har_u]
  rw [m8_k6_get_congr har_i hb7 har_b, ← m8_bv32_lshr1_toNat, hnv_d] at hc
  exact hc

private theorem fidCore_b6_lt {mv n len : Nat} (h1 : n < mv) (h2 : 4224 + 45 * mv ≤ len) :
    4224 + 6 * mv + n < len := by omega

private theorem fidCore_trace_lv_lt {scr0 scrt scrt1 scrt2 scrj : List (BitVec 32)}
    {mv ti ti' v rsn mr roff j nv : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (hmv_hi : mv.toNat ≤ 8192) (_hlt : scrt.length = scr0.length)
    (hti_pos : 0 < ti.toNat) (hti_le : ti.toNat ≤ mv.toNat) (hti1 : ti'.toNat = ti.toNat - 1)
    (htr_e : ((4224 + 5 * mv + ti').setWidth 64).toNat = 4224 + 5 * mv.toNat + ti'.toNat)
    (htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat < scrt.length)
    (hv_eq : (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b).toNat / 2 = v.toNat)
    (hv_lt : v.toNat < mv.toNat)
    (hfl_e : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (hfl_b : ((4224 + 6 * mv + v).setWidth 64).toNat < scrt.length)
    (hrs_e : ((4224 + mv + v).setWidth 64).toNat = 4224 + mv.toNat + v.toNat)
    (hrs_b : ((4224 + mv + v).setWidth 64).toNat < scrt1.length)
    (hrsn : scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b = rsn)
    (hrsn_lt : rsn.toNat < 8 * mv.toNat)
    (hmr_e : ((4224 + 33 * mv + rsn).setWidth 64).toNat = 4224 + 33 * mv.toNat + rsn.toNat)
    (hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt1.length)
    (hmr_d : scrt1[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b = mr)
    (hscrt1 : scrt1 = scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
      (scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b &&& ~~~2#32))
    (hscrt2 : scrt2 = scrt1.set ((4224 + 33 * mv + rsn).setWidth 64).toNat (mr ||| 0x80000000#32))
    (hor_e : ((4224 + 29 * mv + rsn).setWidth 64).toNat = 4224 + 29 * mv.toNat + rsn.toNat)
    (hor_b2 : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt2.length)
    (hroff_d : scrt2[((4224 + 29 * mv + rsn).setWidth 64).toNat]'hor_b2 = roff)
    (har_e : ((4224 + 45 * mv + roff + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + roff.toNat + j.toNat)
    (har_b : ((4224 + 45 * mv + roff + j).setWidth 64).toNat < scrj.length)
    {hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      ((ftS2 scr0 scrt h4214 ti hb0 hb1 hb3 hb2 hb4)[
        (4224 + 29 * (scr0[4214]'h4214).toNat +
          ((ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb5).toNat) %
        4294967296]'hb6).toNat + j.toNat) % 4294967296]'hb7).toNat / 2 <
      (scr0[4192]'h4192).toNat) :
    ((scrj[((4224 + 45 * mv + roff + j).setWidth 64).toNat]'har_b) >>> (1 : Nat)).toNat <
      nv.toNat := by
  have hti_u : 4224 + 5 * mv.toNat + (ti.toNat - 1) < 4294967296 := by
    clear hc hscrt2 hroff_d hmr_d hrsn hmr_b hrs_b hv_eq htr_b hor_b2 har_b hscrt1 hfl_b; omega
  have hfl_u : 4224 + 6 * mv.toNat + v.toNat < 4294967296 := by
    clear hc hscrt2 hroff_d hmr_d hrsn hmr_b hrs_b hv_eq htr_b hor_b2 har_b hscrt1 hfl_b; omega
  have hrs_u : 4224 + mv.toNat + v.toNat < 4294967296 := by
    clear hc hscrt2 hroff_d hmr_d hrsn hmr_b hrs_b hv_eq htr_b hor_b2 har_b hscrt1 hfl_b; omega
  have hmr_u : 4224 + 33 * mv.toNat + rsn.toNat < 4294967296 := by
    clear hc hscrt2 hroff_d hmr_d hrsn hmr_b hrs_b hv_eq htr_b hor_b2 har_b hscrt1 hfl_b; omega
  have hor_u : 4224 + 29 * mv.toNat + rsn.toNat < 4294967296 := by
    rw [← hor_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + 29 * mv + rsn).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + 29 * mv + rsn).isLt (by decide)
  have har_u : 4224 + 45 * mv.toNat + roff.toNat + j.toNat < 4294967296 := by
    rw [← har_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + 45 * mv + roff + j).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + 45 * mv + roff + j).isLt (by decide)
  have htr1 : ftTi scr0 h4214 ti = ((4224 + 5 * mv + ti').setWidth 64).toNat := by
    dsimp only [ftTi]; rw [htr_e, hmv_d, fid_sub1_mod32 _ _ hti_pos hti_u, hti1]
  have hv_g : (scrt[ftTi scr0 h4214 ti]'hb0).toNat / 2 = v.toNat := by
    rw [m8_k6_get_congr htr1 hb0 htr_b, hv_eq]
  have hfl1 : ftFl scr0 scrt h4214 ti hb0 = ((4224 + 6 * mv + v).setWidth 64).toNat := by
    dsimp only [ftFl]; rw [hv_g, hmv_d, hfl_e, Nat.mod_eq_of_lt hfl_u]
  have hrs1 : ftRs scr0 scrt h4214 ti hb0 = ((4224 + mv + v).setWidth 64).toNat := by
    dsimp only [ftRs]; rw [hv_g, hmv_d, hrs_e, Nat.mod_eq_of_lt hrs_u]
  have hset1 : ftS1 scr0 scrt h4214 ti hb0 hb1 = scrt1 := by
    simp only [ftS1, hfl1]; exact hscrt1.symm
  have hrsn_g : ∀ {hb_r},
      (ftS1 scr0 scrt h4214 ti hb0 hb1)[ftRs scr0 scrt h4214 ti hb0]'hb_r = rsn := by
    intro hb_r
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, hset1, hrs1, ← hrsn,
      ← List.getElem?_eq_getElem]
  exact fidCore_trace_lv_aux h4214 hmv_d h4192 hnv_d hset1 (congrArg BitVec.toNat hrsn_g)
    (congrArg BitVec.toNat hrsn_g) (congrArg BitVec.toNat hrsn_g) hmr_u hor_u har_u
    hmr_e hmr_b hmr_d hscrt2 hor_e hor_b2 hroff_d har_e har_b hc

private theorem fidCore_k_lt (k : Nat) {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ 4 * mv.toNat) (hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) (hk : k ≤ 40 := by decide) :
    4224 + k * mv.toNat + x < len := by
  have hk_le : k * mv.toNat ≤ 40 * mv.toNat := Nat.mul_le_mul_right mv.toNat hk
  omega

private theorem fidCore_mv_lt (k : Nat) {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ mv.toNat) (hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) (hk : k ≤ 40 := by decide) :
    4224 + k * mv.toNat + x < len :=
  fidCore_k_lt k (Nat.le_trans hx (by omega)) hmv hbge hk

private theorem fidCore_1_lt {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ mv.toNat) (hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) :
    4224 + mv.toNat + x < len := by
  have h := fidCore_mv_lt 1 hx hmv hbge; omega

private theorem fidCore_rsn_lt {scr0 scrt scrt1 : List (BitVec 32)}
    {mv ti ti' v rsn nc val1 val_set : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4193 : 4193 < scr0.length) (hnc_d : scr0[4193]'h4193 = nc)
    (hscrt1 : scrt1 = scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat val1)
    (_hlt : scrt.length = scr0.length) (hmv_hi : mv.toNat ≤ 8192)
    (hti_pos : 0 < ti.toNat) (hti_le : ti.toNat ≤ mv.toNat)
    (hti1 : ti'.toNat = ti.toNat - 1)
    (htr_e : ((4224 + 5 * mv + ti').setWidth 64).toNat = 4224 + 5 * mv.toNat + ti'.toNat)
    (htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat < scrt.length)
    (hv_eq : (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b).toNat / 2 = v.toNat)
    (hv_lt : v.toNat < mv.toNat)
    (hfl_e : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (hrs_e : ((4224 + mv + v).setWidth 64).toNat = 4224 + mv.toNat + v.toNat)
    (hrs_b : ((4224 + mv + v).setWidth 64).toNat < scrt1.length)
    (hrsn : scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b = rsn)
    {hb1 hb2}
    (hc : ¬ (scr0[4193]'h4193).toNat ≤
        ((scrt.set ((4224 + 6 * (scr0[4214]'h4214).toNat +
          (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
            (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296)
          val_set)[(4224 + (scr0[4214]'h4214).toNat +
            (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
              (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) %
            4294967296]'hb2).toNat) :
    rsn.toNat < nc.toNat := by
  have ⟨hne_mod, hlt32, hne_raw, hti32⟩ := fidCore_ne45_aux hmv_hi hv_lt hti_le
  have hadd : (4224 + 5 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + ti.toNat)) % 4294967296 = 4224 + 5 * mv.toNat + (ti.toNat - 1) := by
    rw [hmv_d]; exact fid_sub1_mod32 _ _ hti_pos hti32
  have hidx_nat : (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2 = v.toNat := by
    rw [← hv_eq]
    exact congrArg (fun x => x.toNat / 2)
      (m8_k6_get_congr (by rw [hadd, htr_e, hti1]) hb1 htr_b)
  have hset_ne : (4224 + 6 * (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296 ≠
      (4224 + (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296 := by
    rw [hidx_nat, hmv_d]; exact hne_mod
  have hget_b : (4224 + (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296 <
      scrt.length := by
    rw [List.length_set] at hb2; exact hb2
  have hkey : (4224 + (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296 =
      ((4224 + mv + v).setWidth 64).toNat := by
    rw [hidx_nat, hmv_d, hrs_e, Nat.mod_eq_of_lt hlt32]
  have hrs_old_b : ((4224 + mv + v).setWidth 64).toNat < scrt.length := by
    rw [← hkey]; exact hget_b
  have hget_eq : scrt[(4224 + (scr0[4214]'h4214).toNat +
      (scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
        (4294967296 - 1 + ti.toNat)) % 4294967296]'hb1).toNat / 2) % 4294967296]'hget_b =
      rsn := by
    have h1 := m8_k6_get_congr hkey hget_b hrs_old_b
    have h2 : scrt[((4224 + mv + v).setWidth 64).toNat]'hrs_old_b =
        scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b := by
      subst hscrt1
      exact (List.getElem_set_ne (by rw [hfl_e, hrs_e]; exact hne_raw) hrs_b).symm
    exact h1.trans (h2.trans hrsn)
  rw [List.getElem_set_ne hset_ne hb2, hget_eq, hnc_d] at hc
  exact Nat.lt_of_not_le hc

private theorem fidCore_clause_ok_bnds {scr0 scrt : List (BitVec 32)} {mv nc acap cid : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (h4193 : 4193 < scr0.length) (hnc_eq : scr0[4193]?.getD 0#32 = nc)
    (h4207 : 4207 < scr0.length) (hac_eq : scr0[4207]?.getD 0#32 = acap)
    (hmv_hi : mv.toNat ≤ 8192) (_hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hik : FidCoreInv scr0 mv nc scrt) (hcid : cid.toNat < nc.toNat)
    (hor_e : ((4224 + 29 * mv + cid).setWidth 64).toNat = 4224 + 29 * mv.toNat + cid.toNat)
    (hmr_e : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hor_b : ((4224 + 29 * mv + cid).setWidth 64).toNat < scrt.length)
    (hmr_b : ((4224 + 33 * mv + cid).setWidth 64).toNat < scrt.length) :
    let roff := scrt[((4224 + 29 * mv + cid).setWidth 64).toNat]'hor_b
    let rmeta := scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b
    roff.toNat + (rmeta &&& 0xFFFF#32).toNat ≤ acap.toNat ∧
    (scrt[4224 + 33 * mv.toNat + cid.toNat]?.getD 0#32).toNat % 65536 =
      (rmeta &&& 0xFFFF#32).toNat ∧
    roff.toNat + (rmeta &&& 0xFFFF#32).toNat ≤ 65535 + acap.toNat ∧
    4224 + 45 * mv.toNat + acap.toNat ≤ scrt.length := by
  have hlt := hik.2.1; have hmin := hik.1.base_ge
  have hmv_t := fidCoreInv_mv h4214 hmv_eq hik
  have hnc_t : scrt[4193]?.getD 0#32 = nc := by
    rw [hik.2.2.1 4193 h4193 (Or.inl (by omega)), hnc_eq]
  have hac_t : scrt[4207]?.getD 0#32 = acap := by
    rw [hik.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq]
  have hcl := hik.1.clause_ok (cid := cid.toNat) (by rw [hnc_t]; exact hcid)
  dsimp only at hcl
  rw [hmv_t, hac_t] at hcl
  have hroff_eq : (scrt[4224 + 29 * mv.toNat + cid.toNat]?.getD 0#32) =
      scrt[((4224 + 29 * mv + cid).setWidth 64).toNat]'hor_b := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact m8_k6_get_congr hor_e.symm _ _
  have hrm_eq : (scrt[4224 + 33 * mv.toNat + cid.toNat]?.getD 0#32) =
      scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact m8_k6_get_congr hmr_e.symm _ _
  rw [hroff_eq, hrm_eq] at hcl
  have hlen_ge := hik.1.length_ge
  rw [hmv_t, hac_t] at hlen_ge
  refine ⟨hcl.1, ?_, ?_, hlen_ge⟩
  · rw [hrm_eq, FidK6Tactics.fid_bv32_and_ffff_toNat]
  · have := m8_and_ffff_le (scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b)
    omega

private theorem fidCore_p3_hant_lt {scr0 scrc scrj : List (BitVec 32)}
    {mv nc acap cid cid' off cmeta sz na ant j : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (hmv_hi : mv.toNat ≤ 8192) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hcid'_lt : cid'.toNat < nc.toNat) (hcid_pos : 0 < cid.toNat)
    (hcid1 : (cid - 1#32).toNat = cid.toNat - 1) (hcid'_d : cid - 1#32 = cid')
    (hlc : scrc.length = scr0.length) (_hsz_le : sz.toNat ≤ 65535) (hj_lt : j.toNat < na.toNat)
    (hosn_le : off.toNat + sz.toNat + na.toNat ≤ acap.toNat)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length)
    (hcap_lt : scr0.length < 2 ^ 30)
    (hco_e : ((4224 + 29 * mv + cid').setWidth 64).toNat = 4224 + 29 * mv.toNat + cid'.toNat)
    (hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length)
    (hoff_d : scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt = off)
    (hcm_e : ((4224 + 33 * mv + cid').setWidth 64).toNat = 4224 + 33 * mv.toNat + cid'.toNat)
    (hcm_lt : ((4224 + 33 * mv + cid').setWidth 64).toNat < scrc.length)
    (hcmeta_d : scrc[((4224 + 33 * mv + cid').setWidth 64).toNat]'hcm_lt = cmeta)
    (hsz_d : cmeta &&& 0xFFFF#32 = sz)
    (har_e : ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off.toNat + sz.toNat + j.toNat)
    (har_lt : ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat < scrj.length)
    (hant_d : scrj[((4224 + 45 * mv + off + sz + j).setWidth 64).toNat]'har_lt = ant)
    {hb1 hb2 hb3}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat +
      (scrc[(4224 + 33 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb2).toNat % 65536 + j.toNat) % 4294967296]'hb3).toNat < nc.toNat) :
    ant.toNat < nc.toNat := by
  have hcid_sub : cid.toNat - 1 < nc.toNat := by rw [← hcid1, hcid'_d]; exact hcid'_lt
  have h1 : (4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) % 4294967296 =
      ((4224 + 29 * mv + cid').setWidth 64).toNat := by
    rw [hmv_d, hco_e, ← hcid'_d, hcid1, fid_sub1_mod32 _ _ hcid_pos (by omega)]
  have hoff_g : scrc[(4224 + 29 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + cid.toNat)) % 4294967296]'hb1 = off := by
    rw [m8_k6_get_congr h1 hb1 hco_lt, hoff_d]
  have h2 : (4224 + 33 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) % 4294967296 =
      ((4224 + 33 * mv + cid').setWidth 64).toNat := by
    rw [hmv_d, hcm_e, ← hcid'_d, hcid1, fid_sub1_mod32 _ _ hcid_pos (by omega)]
  have hsz_g : (scrc[(4224 + 33 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + cid.toNat)) % 4294967296]'hb2).toNat % 65536 = sz.toNat := by
    rw [m8_k6_get_congr h2 hb2 hcm_lt, hcmeta_d, ← hsz_d, fid_bv32_and_ffff_toNat]
  have h3 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat +
      (scrc[(4224 + 33 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb2).toNat % 65536 + j.toNat) % 4294967296 =
      ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat := by
    rw [hoff_g, hsz_g, hmv_d, har_e, Nat.mod_eq_of_lt (by omega)]
  rw [m8_k6_get_congr h3 hb3 har_lt, hant_d] at hc
  exact hc

private theorem fidCore_p3_hlv_lt {scr0 scrc scrj : List (BitVec 32)}
    {mv nc acap cid cid' off sz j lv nv : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (_hmv_hi : mv.toNat ≤ 8192) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hcid'_lt : cid'.toNat < nc.toNat) (hcid_pos : 0 < cid.toNat)
    (hcid1 : (cid - 1#32).toNat = cid.toNat - 1) (hcid'_d : cid - 1#32 = cid')
    (hj_lt : j.toNat < sz.toNat) (hos_le : off.toNat + sz.toNat ≤ acap.toNat)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length)
    (hcap_lt : scr0.length < 2 ^ 30)
    (hco_e : ((4224 + 29 * mv + cid').setWidth 64).toNat = 4224 + 29 * mv.toNat + cid'.toNat)
    (hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length)
    (hoff_d : scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt = off)
    (har_e : ((4224 + 45 * mv + off + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off.toNat + j.toNat)
    (har_lt : ((4224 + 45 * mv + off + j).setWidth 64).toNat < scrj.length)
    (hlv_d :
      scrj[((4224 + 45 * mv + off + j).setWidth 64).toNat]'har_lt >>> (1 : Nat) = lv)
    {hb1 hb2}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat + j.toNat) % 4294967296]'hb2).toNat / 2 <
      (scr0[4192]'h4192).toNat) :
    lv.toNat < nv.toNat := by
  have hcid_sub : cid.toNat - 1 < nc.toNat := by rw [← hcid1, hcid'_d]; exact hcid'_lt
  have h1 : (4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) % 4294967296 =
      ((4224 + 29 * mv + cid').setWidth 64).toNat := by
    rw [hmv_d, hco_e, ← hcid'_d, hcid1, fid_sub1_mod32 _ _ hcid_pos (by omega)]
  have hoff_g : scrc[(4224 + 29 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + cid.toNat)) % 4294967296]'hb1 = off := by
    rw [m8_k6_get_congr h1 hb1 hco_lt, hoff_d]
  have h2 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat + j.toNat) % 4294967296 =
      ((4224 + 45 * mv + off + j).setWidth 64).toNat := by
    rw [hoff_g, hmv_d, har_e, Nat.mod_eq_of_lt (by omega)]
  rw [m8_k6_get_congr h2 hb2 har_lt, ← m8_bv32_lshr1_toNat, hlv_d, hnv_d] at hc
  exact hc

private theorem fidCore_p4_hc_rw {scra : List (BitVec 32)} {j : BitVec 32} {i_raw i_new : Nat}
    (hi : i_raw = i_new)
    {hb1 : i_raw < scra.length}
    {hb2 : i_raw < (scra.set i_raw (scra[i_raw]'hb1 ||| 2147483648#32)).length}
    {hb1' : i_new < scra.length}
    {hb2' : i_new < (scra.set i_new (scra[i_new]'hb1' ||| 2147483648#32)).length}
    (hc : j.toNat <
      ((scra.set i_raw (scra[i_raw]'hb1 ||| 2147483648#32))[i_raw]'hb2).toNat % 65536) :
    j.toNat <
      ((scra.set i_new (scra[i_new]'hb1' ||| 2147483648#32))[i_new]'hb2').toNat % 65536 := by
  subst hi; exact hc

private theorem fidCore_p4_hlv_off {scr0 scrj : List (BitVec 32)}
    {mv off_i j nv lv : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (har_e : ((4224 + 45 * mv + off_i + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off_i.toNat + j.toNat)
    (har_b : ((4224 + 45 * mv + off_i + j).setWidth 64).toNat < scrj.length)
    (hlv_d : scrj[((4224 + 45 * mv + off_i + j).setWidth 64).toNat]'har_b >>> (1 : Nat) = lv)
    {hb : (4224 + 45 * (scr0[4214]'h4214).toNat + off_i.toNat + j.toNat) % 4294967296 <
      scrj.length}
    (hc : (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat + off_i.toNat + j.toNat) %
      4294967296]'hb).toNat / 2 < (scr0[4192]'h4192).toNat) :
    lv.toNat < nv.toNat := by
  have har_u : 4224 + 45 * mv.toNat + off_i.toNat + j.toNat < 4294967296 := by
    rw [← har_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + 45 * mv + off_i + j).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + 45 * mv + off_i + j).isLt (by decide)
  have har_i : (4224 + 45 * (scr0[4214]'h4214).toNat + off_i.toNat + j.toNat) % 4294967296 =
      ((4224 + 45 * mv + off_i + j).setWidth 64).toNat := by
    rw [hmv_d, har_e, Nat.mod_eq_of_lt har_u]
  rw [m8_k6_get_congr har_i hb har_b, ← m8_bv32_lshr1_toNat, hlv_d, hnv_d] at hc
  exact hc

private theorem fidCore_p3_hr0_lt {scr0 scrc scrj : List (BitVec 32)}
    {mv nc cid cid' off j lv r0 : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (h4193 : 4193 < scr0.length) (hnc_d : scr0[4193]'h4193 = nc)
    (hmv_hi : mv.toNat ≤ 8192) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hcid'_lt : cid'.toNat < nc.toNat) (hcid_pos : 0 < cid.toNat)
    (hcid1 : (cid - 1#32).toNat = cid.toNat - 1) (hcid'_d : cid - 1#32 = cid')
    (hco_e : ((4224 + 29 * mv + cid').setWidth 64).toNat = 4224 + 29 * mv.toNat + cid'.toNat)
    (hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length)
    (hoff_d : scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt = off)
    (har_e : ((4224 + 45 * mv + off + j).setWidth 64).toNat =
      4224 + 45 * mv.toNat + off.toNat + j.toNat)
    (har_lt : ((4224 + 45 * mv + off + j).setWidth 64).toNat < scrj.length)
    (hlv_d :
      scrj[((4224 + 45 * mv + off + j).setWidth 64).toNat]'har_lt >>> (1 : Nat) = lv)
    (hrs_e : ((4224 + mv + lv).setWidth 64).toNat = 4224 + mv.toNat + lv.toNat)
    (hrs_b : ((4224 + mv + lv).setWidth 64).toNat < scrj.length)
    (hr0_d : scrj[((4224 + mv + lv).setWidth 64).toNat]'hrs_b = r0)
    {hb1 hb2 hb3}
    (hc : (scrj[(4224 + (scr0[4214]'h4214).toNat +
      (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
        (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
          4294967296]'hb1).toNat + j.toNat) % 4294967296]'hb2).toNat / 2) %
      4294967296]'hb3).toNat < (scr0[4193]'h4193).toNat) :
    r0.toNat < nc.toNat := by
  have hcid_sub : cid.toNat - 1 < nc.toNat := by rw [← hcid1, hcid'_d]; exact hcid'_lt
  have har_u : 4224 + 45 * mv.toNat + off.toNat + j.toNat < 4294967296 := by
    rw [← har_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + 45 * mv + off + j).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + 45 * mv + off + j).isLt (by decide)
  have hrs_u : 4224 + mv.toNat + lv.toNat < 4294967296 := by
    rw [← hrs_e, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (4224 + mv + lv).isLt (by decide))]
    exact Nat.lt_of_lt_of_eq (4224 + mv + lv).isLt (by decide)
  have h1 : (4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) % 4294967296 =
      ((4224 + 29 * mv + cid').setWidth 64).toNat := by
    rw [hmv_d, hco_e, ← hcid'_d, hcid1, fid_sub1_mod32 _ _ hcid_pos (by omega)]
  have hoff_g : scrc[(4224 + 29 * (scr0[4214]'h4214).toNat +
      (4294967296 - 1 + cid.toNat)) % 4294967296]'hb1 = off := by
    rw [m8_k6_get_congr h1 hb1 hco_lt, hoff_d]
  have h2 : (4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat + j.toNat) % 4294967296 =
      ((4224 + 45 * mv + off + j).setWidth 64).toNat := by
    rw [hoff_g, hmv_d, har_e, Nat.mod_eq_of_lt har_u]
  have hlv_g : scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
      (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
        4294967296]'hb1).toNat + j.toNat) % 4294967296]'hb2 =
      scrj[((4224 + 45 * mv + off + j).setWidth 64).toNat]'har_lt :=
    m8_k6_get_congr h2 hb2 har_lt
  have h3 : (4224 + (scr0[4214]'h4214).toNat +
      (scrj[(4224 + 45 * (scr0[4214]'h4214).toNat +
        (scrc[(4224 + 29 * (scr0[4214]'h4214).toNat + (4294967296 - 1 + cid.toNat)) %
          4294967296]'hb1).toNat + j.toNat) % 4294967296]'hb2).toNat / 2) % 4294967296 =
      ((4224 + mv + lv).setWidth 64).toNat := by
    rw [hlv_g, ← m8_bv32_lshr1_toNat, hlv_d, hmv_d, hrs_e, Nat.mod_eq_of_lt hrs_u]
  rw [m8_k6_get_congr h3 hb3 hrs_b, hr0_d, hnc_d] at hc
  exact hc

/-- Parametric `Func.wp` proof for `full_k6_core_fid`, certifying `fidK6CoreSpec`. -/
theorem full_k6_core_fid_wp (Γ : Env) :
    ∀ a m Q X, fidK6CoreSpec a m Q X → Func.wp Γ full_k6_core_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6CoreSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have hlen_ge := hok.length_ge; have hlen_lt := hok.length_lt
  have h4214 : 4214 < scr0.length := by omega
  have h4193 : 4193 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  have h4207 : 4207 < scr0.length := by omega
  let mv := scr0[4214]'h4214; let nc := scr0[4193]'h4193
  let nv := scr0[4192]'h4192; let acap := scr0[4207]'h4207
  have hmv_o : (scr0[(@OfNat.ofNat Nat 4214 _)]'h4214).toNat = mv.toNat := rfl
  have hmv_d : (scr0[4214]'h4214).toNat = mv.toNat := rfl
  have hnc_o : (scr0[(@OfNat.ofNat Nat 4193 _)]'h4193).toNat = nc.toNat := rfl
  have hnv_o : (scr0[(@OfNat.ofNat Nat 4192 _)]'h4192).toNat = nv.toNat := rfl
  have hacap_o : (scr0[(@OfNat.ofNat Nat 4207 _)]'h4207).toNat = acap.toNat := rfl
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  have hnc_eq : (scr0[4193]?.getD 0#32) = nc := m8_k6_get_eq h4193
  have hac_eq : (scr0[4207]?.getD 0#32) = acap := m8_k6_get_eq h4207
  rw [hmv_eq] at hmv_lo hmv_hi hbge hlen_ge; rw [hac_eq] at hlen_ge
  have hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length := hlen_ge
  have hcap_lt : scr0.length < 2 ^ 30 := hlen_lt
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q () m0 := hQ scr0 m0 hscr_len (fun _ _ _ => rfl) hok hm0
  let invB : Bool × List (BitVec 32) → Mem 64 → Prop := fun x mk =>
    FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) mk
  let invS : Mem 64 → Prop := fun mj =>
    ∃ scrj : List (BitVec 32), FidCoreInv scr0 mv nc scrj ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj
  unfold Func.wp full_k6_core_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hnc_le : nc.toNat ≤ 4 * mv.toNat := by fid_omega
        c0_hsplit
        · c0_hsteps!; exact hret_noop
        · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
          have hinv0 : FidCoreInv scr0 mv nc scr0 :=
            ⟨hok, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
          -- Loop 1: clear `KM_CORE` on `0 ..< nc`
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem (i, ()) ml => ∃ scrl : List (BitVec 32),
              FidCoreInv scr0 mv nc scrl ∧ i.toNat ≤ nc.toNat ∧ rem = nc.toNat - i.toNat ∧
              (FullMem c (m8ScrSt s scrl) ⋆ R) ml)
            ?_ ?_
          · rintro L1 rem ⟨i, ⟨⟩⟩ ml hL1 ⟨scrl, hikl, hi_le, rfl, hml⟩
            have hll : scrl.length = scr0.length := hikl.2.1
            have hmin_l : 15744 ≤ scrl.length := by rw [hll]; exact hmin
            c0_hsplit
            · have hi_lt : i.toNat < nc.toNat := hc
              have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_bv32_add1_toNat hi_lt
                (by clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hml hikl; omega)
              have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := i)
                hmv_hi (by decide) (by clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hml hikl; omega)
              have hcm_lt :
                  (((4224 : BitVec 32) + (33 : BitVec 32) * mv + i).setWidth 64).toNat <
                  scrl.length := by
                clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hml hikl
                rw [hll, hcm_e]; omega
              c0_hsteps!
              exact hL1 (nc.toNat - (i + 1#32).toNat) (i + 1#32, ()) _
                (by clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hikl hm; omega)
                ⟨_, fidCoreInv_set_meta_pres h4214 hmv_eq hnc_le hikl hi_lt hcm_e hcm_lt
                  (m8_km_core_clear_pres _),
                  by clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hikl hm; omega, rfl, hm⟩
            · -- Phase 2: optional `inc < nc` trail traceback
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 32))
                (fun x => (x.1, ()))
                (fun x m2 => FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) m2)
                ?_ ?_
              · rintro _ ⟨_, scr2⟩ m2 ⟨hik2, hm2⟩
                -- Phase 3: fixpoint closure loop `changed && pass < nc`
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i32, .bool])
                  (fun rem (pass, chg, ()) mp => ∃ scrp : List (BitVec 32),
                    FidCoreInv scr0 mv nc scrp ∧ pass.toNat ≤ nc.toNat ∧
                    rem = (if chg then nc.toNat - pass.toNat else 0) ∧
                    (FullMem c (m8ScrSt s scrp) ⋆ R) mp)
                  ?_ ?_
                · rintro Lp rem ⟨pass, chg, ⟨⟩⟩ mp hLp ⟨scrp, hikp, hpass_le, rfl, hmp⟩
                  have hlp : scrp.length = scr0.length := hikp.2.1
                  have hfin_p : Q () mp :=
                    hQ scrp mp (hlp.trans hscr_len)
                      (fun idx hi hor => by
                        rw [hmv_eq] at hor; exact hikp.2.2.1 idx (by omega) hor)
                      hikp.1 (m8ScrSt_eq s scrp ▸ hmp)
                  clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1 hml hikl hm2 hik2
                  c0_hsplit
                  · have hchg_t : chg = true := hc
                    c0_hsplit
                    · have hpass_lt : pass.toNat < nc.toNat := hc
                      have hp1 : (pass + 1#32).toNat = pass.toNat + 1 :=
                        m8_bv32_add1_toNat hpass_lt (by clear hfin_p hLp hmp hikp; omega)
                      c0_hsteps_nogrp
                      refine wp_loop_group (ts := [.bool, i32])
                        (fun rem_c (chg_c, cid, ()) mc_m => ∃ scrc : List (BitVec 32),
                          FidCoreInv scr0 mv nc scrc ∧ cid.toNat ≤ nc.toNat ∧
                          rem_c = cid.toNat ∧ (FullMem c (m8ScrSt s scrc) ⋆ R) mc_m)
                        ?_ ?_
                      · rintro Lc rem_c ⟨chg_c, cid, ⟨⟩⟩ mc_m hLc ⟨scrc, hikc, hcid_le, rfl, hmc⟩
                        have hlc : scrc.length = scr0.length := hikc.2.1
                        c0_hsplit
                        · have hcid_pos : 0 < cid.toNat := hc
                          clear hc
                          have hcid1 : (cid - 1#32).toNat = cid.toNat - 1 :=
                            m8_bv32_sub1_toNat hcid_pos
                          let cid' := cid - 1#32
                          have hcid'_lt : cid'.toNat < nc.toNat := by
                            clear hfin_p hLp hmp hikp hLc hmc hikc
                            dsimp only [cid']; rw [hcid1]; omega
                          have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := cid')
                            hmv_hi (by decide)
                            (by clear hfin_p hLp hmp hikp hLc hmc hikc; omega)
                          have hcm_lt : ((4224 + 33 * mv + cid').setWidth 64).toNat <
                              scrc.length := by
                            clear hfin_p hLp hmp hikp hLc hmc hikc; rw [hlc, hcm_e]; omega
                          let cmeta :=
                            scrc[((4224 + 33 * mv + cid').setWidth 64).toNat]'hcm_lt
                          c0_hsteps_nogrp
                          refine wp_join_state (ts := [.bool])
                            (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
                            (fun _ ⟨chgj, scrj⟩ mj ⟨hikj, hmj⟩ => by
                              c0_hsteps!
                              exact hLc cid'.toNat (chgj, cid', ()) mj (by
                                clear hfin_p hLp hmp hikp hLc hmc hikc hikj hmj
                                dsimp only [cid']; rw [hcid1]; omega)
                                ⟨scrj, hikj,
                                  by clear hfin_p hLp hmp hikp hLc hmc hikc hikj hmj; omega,
                                  rfl, hmj⟩)
                            (fun Jc hJc => by
                              c0_hsplit
                              · have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := cid')
                                  hmv_hi (by decide)
                                  (by clear hfin_p hLp hmp hikp hLc hmc hikc hJc; omega)
                                have hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat <
                                    scrc.length := by
                                  clear hfin_p hLp hmp hikp hLc hmc hikc hJc
                                  rw [hlc, hco_e]; omega
                                let off :=
                                  scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt
                                let sz := cmeta &&& 0xFFFF#32
                                have hcm_get :
                                    scrc[(4224 + 33 * mv.toNat +
                                      (4294967296 - 1 + cid.toNat)) %
                                      4294967296]'(by
                                        clear hfin_p hLp hmp hikp hLc hmc hikc hJc
                                        rw [hlc, fid_sub1_mod32 _ _ hcid_pos (by omega)]
                                        omega) = cmeta :=
                                  m8_k6_get_congr (by
                                    clear hfin_p hLp hmp hikp hLc hmc hikc hJc
                                    rw [hcm_e]; dsimp only [cid']; rw [hcid1]
                                    exact fid_sub1_mod32 _ _ hcid_pos (by omega)) _ _
                                have hsz_le : sz.toNat ≤ 65535 := m8_and_ffff_le cmeta
                                have hmv_c := fidCoreInv_mv h4214 hmv_eq hikc
                                have hnc_c : scrc[4193]?.getD 0#32 = nc := by
                                  rw [hikc.2.2.1 4193 h4193 (Or.inl (by omega)), hnc_eq]
                                have hac_c : scrc[4207]?.getD 0#32 = acap := by
                                  rw [hikc.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq]
                                have hcl_c := hikc.1.clause_ok (cid := cid'.toNat)
                                  (by rw [hnc_c]; exact hcid'_lt)
                                dsimp only at hcl_c; rw [hmv_c, hac_c] at hcl_c
                                have hoff_eq :
                                    (scrc[4224 + 29 * mv.toNat + cid'.toNat]?.getD 0#32) = off := by
                                  rw [List.getElem?_eq_getElem (by
                                    rw [hlc]
                                    exact fidCore_k_lt 29
                                      (Nat.le_trans (Nat.le_of_lt hcid'_lt) hnc_le) hmv_lo hbge),
                                    Option.getD_some]
                                  exact m8_k6_get_congr hco_e.symm _ _
                                have hcm_eq :
                                    (scrc[4224 + 33 * mv.toNat + cid'.toNat]?.getD 0#32) =
                                      cmeta := by
                                  rw [List.getElem?_eq_getElem (by
                                    rw [hlc]
                                    exact fidCore_k_lt 33
                                      (Nat.le_trans (Nat.le_of_lt hcid'_lt) hnc_le) hmv_lo hbge),
                                    Option.getD_some]
                                  exact m8_k6_get_congr hcm_e.symm _ _
                                rw [hoff_eq, hcm_eq,
                                  show (cmeta &&& 0xFFFF#32) = sz from rfl] at hcl_c
                                have hoff_g :
                                    scrc[(4224 + 29 * (scr0[4214]'h4214).toNat +
                                      (4294967296 - 1 + cid.toNat)) % 4294967296]'(by
                                        clear hfin_p hLp hmp hikp hLc hmc hikc hJc
                                        rw [hlc, fid_sub1_mod32 _ _ hcid_pos (by omega)]
                                        omega) = off :=
                                  m8_k6_get_congr (by
                                    clear hfin_p hLp hmp hikp hLc hmc hikc hJc
                                    rw [hco_e]; dsimp only [cid']; rw [hcid1]
                                    exact fid_sub1_mod32 _ _ hcid_pos (by omega)) _ _
                                have hsz_g :
                                    (scrc[(4224 + 33 * (scr0[4214]'h4214).toNat +
                                      (4294967296 - 1 + cid.toNat)) % 4294967296]'(by
                                        clear hfin_p hLp hmp hikp hLc hmc hikc hJc
                                        rw [hlc, fid_sub1_mod32 _ _ hcid_pos (by omega)]
                                        omega)).toNat % 65536 = sz.toNat := by
                                  rw [hcm_get]; dsimp only [sz]; rw [fid_bv32_and_ffff_toNat]
                                c0_hsteps_nogrp
                                refine wp_join_state (ts := [.bool])
                                  (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
                                  (fun _ x mj h => by c0_hsteps!; exact hJc x mj h)
                                  (fun Jm hJm => by
                                    c0_hsplit
                                    · -- Learned clause: traverse `na` antecedents
                                      have hlrn : (cmeta &&& 0x40000000#32) ≠ 0#32 := by
                                        intro heq; apply hc
                                        have hc' := hcm_get; dsimp only [mv] at hc'
                                        rw [← hc'] at heq; exact heq
                                      have hca_e := fid_k6_off_add (mv := mv) (k := 37) (x := cid')
                                        hmv_hi (by decide)
                                        (by clear hfin_p hLp hmp hikp hLc hmc hikc hJc hJm; omega)
                                      have hca_lt : ((4224 + 37 * mv + cid').setWidth 64).toNat <
                                          scrc.length := by
                                        clear hfin_p hLp hmp hikp hLc hmc hikc hJc hJm
                                        rw [hlc, hca_e]; omega
                                      let na :=
                                        scrc[((4224 + 37 * mv + cid').setWidth 64).toNat]'hca_lt
                                      have hna_eq :
                                          (scrc[4224 + 37 * mv.toNat + cid'.toNat]?.getD 0#32) =
                                            na := by
                                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                        exact m8_k6_get_congr hca_e.symm _ _
                                      have hosn_le : off.toNat + sz.toNat + na.toNat ≤
                                          acap.toNat := by
                                        rw [hna_eq] at hcl_c; exact hcl_c.2 hlrn
                                      c0_hsteps_nogrp
                                      refine wp_join_state (ts := [.bool])
                                        (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
                                        (fun _ x mj h => by c0_hsteps!; exact hJm x mj h)
                                        (fun Jw hJw => by
                                          c0_hsplit
                                          · c0_hsteps_nogrp
                                            refine wp_loop_group (ts := [.bool, i32])
                                              (fun rj (chgj, j, ()) mj => ∃ scrj : List (BitVec 32),
                                                FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ na.toNat ∧
                                                rj = na.toNat - j.toNat ∧
                                                (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
                                            · rintro Lj rem_j ⟨chgj, j, ⟨⟩⟩ mj hLj
                                                ⟨scrj, hikj, hj_le, rfl, hmj⟩
                                              have hlj : scrj.length = scr0.length := hikj.2.1
                                              c0_hsplit
                                              · have hj_lt : j.toNat < na.toNat := by
                                                   have hc' := hc
                                                   clear hc hmc hikc hmj hikj hmp hikp hLp
                                                     hLc hLj hJc hJm hJw
                                                   fid_norm_ofnat
                                                   simp (disch := fid_omega) only [bv_c0,
                                                     Nat.reducePow, BitVec.reduceToNat] at hc'
                                                   try rw [hmv_d] at hc'
                                                   have hna_g :
                                                       (scrc[(4224 + 37 * mv.toNat +
                                                         (4294967296 - 1 + cid.toNat)) %
                                                         4294967296]'(by
                                                           clear hc'
                                                           rw [hlc, fid_sub1_mod32 _ _ hcid_pos
                                                             (by omega)]
                                                           omega)).toNat = na.toNat :=
                                                     congrArg BitVec.toNat (m8_k6_get_congr (by
                                                       clear hc'
                                                       rw [hca_e]; dsimp only [cid']; rw [hcid1]
                                                       exact fid_sub1_mod32 _ _ hcid_pos
                                                         (by omega)) _ _)
                                                   try rw [hna_g] at hc'
                                                   exact hc'
                                                have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                                                  m8_bv32_add1_toNat hj_lt
                                                    (by clear hmc hikc hmj hikj hmp hikp hLp
                                                          hLc hLj hJc hJm hJw; omega)
                                                have har_e := fid_k6_off_add3 (mv := mv) (k := 45)
                                                  (x := off) (y := sz) (z := j)
                                                  hmv_hi (by decide)
                                                  (by clear hmc hikc hmj hikj hmp hikp hLp
                                                        hLc hLj hJc hJm hJw; omega)
                                                have har_lt :
                                                    ((4224 + 45 * mv + off + sz + j).setWidth
                                                      64).toNat < scrj.length := by
                                                  clear hmc hikc hmj hikj hmp hikp hLp
                                                    hLc hLj hJc hJm hJw
                                                  rw [hlj, har_e]; omega
                                                let ant :=
                                                  scrj[((4224 + 45 * mv + off + sz + j).setWidth
                                                    64).toNat]'har_lt
                                                c0_hsteps_nogrp
                                                refine wp_join_state (ts := [.bool])
                                                  (α := Bool × List (BitVec 32))
                                                  (fun x => (x.1, ())) invB
                                                  (fun _ ⟨chgk, scrk⟩ mk ⟨hikk, hmk⟩ => by
                                                    c0_hsteps!
                                                    exact hLj (na.toNat - (j + 1#32).toNat)
                                                      (chgk, j + 1#32, ()) mk (by omega)
                                                      ⟨scrk, hikk, by omega, rfl, hmk⟩)
                                                  (fun Jk hJk => by
                                                    c0_hsplit
                                                    · have hant_lt : ant.toNat < nc.toNat := by
                                                        have hc' := hc
                                                        clear hc hmc hikc hmj hikj hmp hikp hLp
                                                          hLc hLj hJc hJm hJw hJk
                                                        fid_norm_ofnat
                                                        simp (disch := fid_omega) only [bv_c0,
                                                          Nat.reducePow, BitVec.reduceToNat] at hc'
                                                        exact fidCore_p3_hant_lt h4214 rfl hmv_hi
                                                          hnc_le hcid'_lt hcid_pos hcid1 rfl hlc
                                                          hsz_le hj_lt hosn_le hlen_scr hcap_lt
                                                          hco_e hco_lt rfl hcm_e hcm_lt rfl rfl
                                                          har_e har_lt rfl hc'
                                                      clear hc
                                                      have hma_e := fid_k6_off_add (mv := mv)
                                                        (k := 33) (x := ant) hmv_hi (by decide)
                                                        (by omega)
                                                      have hma_lt : ((4224 + 33 * mv +
                                                          ant).setWidth 64).toNat <
                                                          scrj.length := by
                                                        rw [hlj, hma_e]; omega
                                                      c0_hsplit
                                                      · c0_hsteps!
                                                        refine hJk (true, _) _
                                                          ⟨fidCoreInv_set_meta_pres h4214 hmv_eq
                                                            hnc_le hikj hant_lt hma_e hma_lt
                                                            (m8_km_core_or_pres _), hm⟩
                                                      · c0_hsteps!
                                                        exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩
                                                    · c0_hsteps!
                                                      exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩)
                                              · c0_hsteps!; exact hJw (chgj, scrj) mj ⟨hikj, hmj⟩
                                            · intro Lj hLj; c0_hsteps!
                                              exact hLj na.toNat (chg_c, 0#32, ()) mc_m
                                                ⟨scrc, hikc, Nat.zero_le _, by simp, hmc⟩
                                          · c0_hsteps!; exact hJw (chg_c, scrc) mc_m ⟨hikc, hmc⟩)
                                    · -- Original clause: traverse `sz` lits, mark lvl-0 reasons
                                      refine wp_join_state (ts := [.bool])
                                        (α := Bool × List (BitVec 32)) (fun x => (x.1, ())) invB
                                        (fun _ x mj h => by c0_hsteps!; exact hJm x mj h)
                                        (fun Jw hJw => by
                                          c0_hsplit
                                          · c0_hsteps_nogrp
                                            refine wp_loop_group (ts := [.bool, i32])
                                              (fun rj (chgj, j, ()) mj => ∃ scrj : List (BitVec 32),
                                                FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ sz.toNat ∧
                                                rj = sz.toNat - j.toNat ∧
                                                (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
                                            · rintro Lj rem_j ⟨chgj, j, ⟨⟩⟩ mj hLj
                                                ⟨scrj, hikj, hj_le, rfl, hmj⟩
                                              have hlj : scrj.length = scr0.length := hikj.2.1
                                              c0_hsplit
                                              · have hj_lt : j.toNat < sz.toNat := by
                                                 have hc' := hc; fid_norm_ofnat
                                                 simp (disch := fid_omega) only [bv_c0,
                                                   Nat.reducePow, BitVec.reduceToNat] at hc'
                                                 have hsz_g :
                                                     (scrc[(4224 + 33 * (scr0[4214]'h4214).toNat +
                                                       (4294967296 - 1 + cid.toNat)) %
                                                       4294967296]'(by
                                                         rw [hlc, fid_sub1_mod32 _ _ hcid_pos
                                                           (by omega)]
                                                         omega)).toNat %
                                                       65536 = sz.toNat := by
                                                   rw [hcm_get]; dsimp only [sz]
                                                   rw [fid_bv32_and_ffff_toNat]
                                                 try rw [hsz_g] at hc'
                                                 exact hc'
                                                have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                                                  m8_bv32_add1_toNat hj_lt (by omega)
                                                have har_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                                  (x := off) (y := j) hmv_hi (by decide) (by omega)
                                                have har_lt :
                                                    ((4224 + 45 * mv + off + j).setWidth 64).toNat <
                                                      scrj.length := by rw [hlj, har_e]; omega
                                                let lv := (scrj[((4224 + 45 * mv + off + j).setWidth
                                                  64).toNat]'har_lt) >>> (1 : Nat)
                                                c0_hsteps_nogrp
                                                refine wp_join_state (ts := [.bool])
                                                  (α := Bool × List (BitVec 32))
                                                  (fun x => (x.1, ())) invB
                                                  (fun _ ⟨chgk, scrk⟩ mk ⟨hikk, hmk⟩ => by
                                                    c0_hsteps!
                                                    exact hLj (sz.toNat - (j + 1#32).toNat)
                                                      (chgk, j + 1#32, ()) mk
                                                      (by clear hmc hikc hmj hikj hmp hikp hLp
                                                            hLc hLj hJc hJm hJw hikk hmk; omega)
                                                      ⟨scrk, hikk,
                                                        by clear hmc hikc hmj hikj hmp hikp hLp
                                                             hLc hLj hJc hJm hJw hikk hmk; omega,
                                                        rfl, hmk⟩)
                                                  (fun Jk hJk => by
                                                    c0_hsplit
                                                    · have hlv_lt : lv.toNat < nv.toNat := by
                                                        have hc' := hc
                                                        clear hc hmc hikc hmj hikj hmp hikp hLp
                                                          hLc hLj hJc hJm hJw hJk
                                                        fid_norm_ofnat
                                                        simp (disch := fid_omega) only [bv_c0,
                                                          Nat.reducePow, BitVec.reduceToNat] at hc'
                                                        exact fidCore_p3_hlv_lt h4214 rfl h4192 rfl
                                                          hmv_hi hnc_le hcid'_lt hcid_pos hcid1 rfl
                                                          hj_lt hcl_c.1 hlen_scr hcap_lt hco_e
                                                          hco_lt rfl har_e har_lt rfl hc'
                                                      clear hc
                                                      have hlv_e := fid_k6_off_add0 (x := lv)
                                                        (by clear hmc hikc hmj hikj hmp hikp hLp
                                                              hLc hLj hJc hJm hJw hJk; omega)
                                                      have hlv_b :
                                                          (((4224 : BitVec 32) + lv).setWidth
                                                            64).toNat < scrj.length := by
                                                        clear hmc hikc hmj hikj hmp hikp hLp
                                                          hLc hLj hJc hJm hJw hJk
                                                        rw [hlj, hlv_e]; omega
                                                      c0_hsplit
                                                      · have hrs_e := fid_k6_off_add1 (mv := mv)
                                                          (x := lv) hmv_hi
                                                          (by clear hmc hikc hmj hikj hmp hikp
                                                                hLp hLc hLj hJc hJm hJw hJk; omega)
                                                        have hrs_b : ((4224 + mv + lv).setWidth
                                                            64).toNat < scrj.length := by
                                                          clear hmc hikc hmj hikj hmp hikp hLp
                                                            hLc hLj hJc hJm hJw hJk
                                                          rw [hlj, hrs_e]; omega
                                                        c0_hsteps_nogrp
                                                        refine wp_join_state (ts := [.bool])
                                                          (α := Bool × List (BitVec 32))
                                                          (fun x => (x.1, ())) invB
                                                          (fun _ ⟨chg9, scr9⟩ m9 ⟨hik9, hm9⟩ => by
                                                            c0_hsteps!
                                                            exact hJk (chg9, scr9) m9 ⟨hik9, hm9⟩)
                                                          (fun J9 hJ9 => by
                                                            let r0 := scrj[((4224 + mv +
                                                              lv).setWidth 64).toNat]'hrs_b
                                                            c0_hsplit
                                                            · have hr0_lt :
                                                                  r0.toNat < nc.toNat := by
                                                                have hc' := hc
                                                                clear hc hmc hikc hmj hikj hmp hikp
                                                                  hLp hLc hLj hJc hJm hJw hJk hJ9
                                                                fid_norm_ofnat
                                                                simp (disch := fid_omega) only
                                                                  [bv_c0, Nat.reducePow,
                                                                   BitVec.reduceToNat] at hc'
                                                                exact fidCore_p3_hr0_lt h4214 rfl
                                                                  h4193 rfl hmv_hi hnc_le hcid'_lt
                                                                  hcid_pos hcid1 rfl hco_e hco_lt
                                                                  rfl har_e har_lt rfl hrs_e hrs_b
                                                                  rfl hc'
                                                              clear hc
                                                              have hmr_e := fid_k6_off_add
                                                                (mv := mv) (k := 33) (x := r0)
                                                                hmv_hi (by decide)
                                                                (Nat.lt_of_lt_of_le hr0_lt
                                                                  (Nat.le_trans hnc_le
                                                                    (Nat.le_trans
                                                                      (Nat.mul_le_mul_left 4 hmv_hi)
                                                                      (by decide))))
                                                              have hmr_b :
                                                                  ((4224 + 33 * mv + r0).setWidth
                                                                    64).toNat < scrj.length := by
                                                                rw [hlj, hmr_e]
                                                                exact fidCore_k_lt 33
                                                                  (Nat.le_trans (Nat.le_of_lt
                                                                    hr0_lt) hnc_le) hmv_lo hbge
                                                              c0_hsplit
                                                              · c0_hsteps!
                                                                refine hJ9 (true, _) _
                                                                  ⟨fidCoreInv_set_meta_pres h4214
                                                                    hmv_eq hnc_le hikj hr0_lt hmr_e
                                                                    hmr_b (m8_km_core_or_pres _),
                                                                    hm⟩
                                                              · c0_hsteps!; exact
                                                                  hJ9 (chgj, scrj) mj ⟨hikj, hmj⟩
                                                            · c0_hsteps!
                                                              exact hJ9 (chgj, scrj) mj ⟨hikj, hmj⟩)
                                                      · c0_hsteps!
                                                        exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩
                                                    · c0_hsteps!
                                                      exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩)
                                              · c0_hsteps!; exact hJw (chgj, scrj) mj ⟨hikj, hmj⟩
                                            · intro Lj hLj; c0_hsteps!
                                              exact hLj sz.toNat (chg_c, 0#32, ()) mc_m
                                                ⟨scrc, hikc, Nat.zero_le _, by simp, hmc⟩
                                          · c0_hsteps!; exact hJw (chg_c, scrc) mc_m ⟨hikc, hmc⟩))
                              · c0_hsteps!; exact hJc (chg_c, scrc) mc_m ⟨hikc, hmc⟩)
                        · c0_hsteps!
                          exact hLp (if chg_c then nc.toNat - (pass + 1#32).toNat else 0)
                            (pass + 1#32, chg_c, ()) mc_m
                            (by subst hchg_t; cases chg_c <;> simp [hp1] <;> omega)
                            ⟨scrc, hikc, by omega, rfl, hmc⟩
                      · intro Lc hLc; c0_hsteps!
                        exact hLc nc.toNat (false, nc, ()) mp ⟨scrp, hikp, Nat.le_refl _, rfl, hmp⟩
                    · c0_hsteps!; exact hfin_p
                  · c0_hsteps!; exact hfin_p
                · intro Lp hLp; c0_hsteps!
                  exact hLp nc.toNat (0#32, true, ()) m2
                    ⟨scr2, hik2, Nat.zero_le _, by simp, hm2⟩
              · intro J2 hJ2
                clear hQ hSpec hm0 hm0' hret_noop hinv0 hL1
                have h4199 : 4199 < scrl.length := by omega
                let inc := scrl[4199]'h4199
                have hinc_o : (scrl[(@OfNat.ofNat Nat 4199 _)]'h4199).toNat = inc.toNat := rfl
                c0_hsplit
                · have hinc_lt : inc.toNat < nc.toNat := hc
                  -- Sub-loop 2a: clear `flags & 2` on `0 ..< nv`
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i32])
                    (fun rem (i, ()) ma => ∃ scra : List (BitVec 32),
                      FidCoreInv scr0 mv nc scra ∧ i.toNat ≤ nv.toNat ∧ rem = nv.toNat - i.toNat ∧
                      (FullMem c (m8ScrSt s scra) ⋆ R) ma)
                    ?_ ?_
                  · rintro La rem ⟨i, ⟨⟩⟩ ma hLa ⟨scra, hika, hi_le, rfl, hma⟩
                    have hla : scra.length = scr0.length := hika.2.1
                    c0_hsplit
                    · have hi_lt : i.toNat < nv.toNat := hc
                      have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                        m8_bv32_add1_toNat hi_lt (by omega)
                      have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := i)
                        hmv_hi (by decide) (by omega)
                      have hfl_b : ((4224 + 6 * mv + i).setWidth 64).toNat < scra.length :=
                        by rw [hla, hfl_e]; omega
                      c0_hsteps!
                      exact hLa (nv.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
                        ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hika (by omega) hfl_e _,
                          by omega, rfl, hm⟩
                    · -- Mark `inc` core and mark its literals' vars
                      have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := inc)
                        hmv_hi (by decide) (by omega)
                      have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := inc)
                        hmv_hi (by decide) (by omega)
                      have hcm_b : ((4224 + 33 * mv + inc).setWidth 64).toNat <
                          scra.length := by rw [hla, hcm_e]; omega
                      have hco_b : ((4224 + 29 * mv + inc).setWidth 64).toNat <
                          scra.length := by rw [hla, hco_e]; omega
                      let meta_i :=
                        scra[((4224 + 33 * mv + inc).setWidth 64).toNat]'hcm_b
                      have hmeta_get : scra[4224 + 33 * mv.toNat + inc.toNat]'(by omega) = meta_i :=
                        m8_k6_get_congr hcm_e.symm (by omega) hcm_b
                      let scrb := scra.set (4224 + 33 * mv.toNat + inc.toNat)
                        (meta_i ||| 0x80000000#32)
                      have hikb : FidCoreInv scr0 mv nc scrb := by
                        have hpres := m8_km_core_or_pres meta_i
                        refine fidCoreInv_set_meta h4214 hmv_eq hnc_le hika hinc_lt ?_ ?_
                        · rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hmeta_get]
                          exact hpres.1
                        · rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hmeta_get]
                          exact hpres.2
                      have hlb : scrb.length = scr0.length := hikb.2.1
                      have hmv_b := fidCoreInv_mv h4214 hmv_eq hikb
                      have hnc_b : scrb[4193]?.getD 0#32 = nc := by
                        rw [hikb.2.2.1 4193 h4193 (Or.inl (by omega)), hnc_eq]
                      have hac_b : scrb[4207]?.getD 0#32 = acap := by
                        rw [hikb.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq]
                      have hcl_b := hikb.1.clause_ok (cid := inc.toNat)
                        (by rw [hnc_b]; exact hinc_lt)
                      dsimp only at hcl_b
                      rw [hmv_b, hac_b] at hcl_b
                      c0_hsteps_nogrp
                      replace hm : (FullMem c (m8ScrSt s scrb) ⋆ R) m := by
                        dsimp only [scrb]; rw [← hcm_e]; exact hm
                      -- Join after `if (off + sz <= acap)` mark loop
                      refine wp_join0 invS ?_ ?_
                      · rintro _ mb ⟨scrm, hikm, hmb⟩
                        clear hLa hika hikb hcl_b hm hml hikl hmeta_get
                          hmv_b hnc_b hac_b hco_b hcm_b hco_e hcm_e hlb scrb meta_i hla hll
                        have hlm : scrm.length = scr0.length := hikm.2.1
                        have hmin_m : 15744 ≤ scrm.length := by omega
                        c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                          (fun ti => (ti, ())) (fun ti => ti.toNat ≤ mv.toNat) ?_ ?_
                        · intro _ ti0 hti0
                          -- Trail traceback loop `while (ti > 0)`
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem_t (ti, ()) mt => ∃ scrt : List (BitVec 32),
                              FidCoreInv scr0 mv nc scrt ∧ ti.toNat ≤ mv.toNat ∧
                              rem_t = ti.toNat ∧ (FullMem c (m8ScrSt s scrt) ⋆ R) mt) ?_ ?_
                          · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨scrt, hikt, hti_le, rfl, hmt⟩
                            clear hikm hmb
                            have hlt : scrt.length = scr0.length := hikt.2.1
                            c0_hsplit
                            · have hti_pos : 0 < ti.toNat := hc
                              have hti1 : (ti - 1#32).toNat = ti.toNat - 1 :=
                                m8_bv32_sub1_toNat hti_pos
                              let ti' := ti - 1#32
                              have htr_e := fid_k6_off_add (mv := mv) (k := 5) (x := ti')
                                hmv_hi (by decide) (by dsimp only [ti']; rw [hti1]; omega)
                              have htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat <
                                  scrt.length := by
                                rw [hlt, htr_e]; dsimp only [ti']; rw [hti1]; omega
                              let v := (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'
                                htr_b) >>> (1 : Nat)
                              c0_hsplit
                              · c0_hsteps!; exact hLt ti'.toNat (ti', ()) mt
                                  (by dsimp only [ti']; rw [hti1]; omega)
                                  ⟨scrt, hikt, by dsimp only [ti']; rw [hti1]; omega, rfl, hmt⟩
                              · have hv_lt : v.toNat < nv.toNat := by
                                  have hc' := hc; fid_norm_ofnat
                                  simp (disch := fid_omega) only [bv_c0, Nat.reducePow,
                                    BitVec.reduceToNat] at hc'
                                  try rw [hmv_d] at hc'
                                  have hsub := fid_sub1_mod32 0 ti.toNat hti_pos (by omega)
                                  simp only [Nat.zero_add] at hsub
                                  have hadd : (4224 + 5 * (scr0[4214]'h4214).toNat +
                                        (4294967296 - 1 + ti.toNat)) % 4294967296 =
                                        4224 + 5 * mv.toNat + (ti.toNat - 1) := by
                                    rw [Nat.add_mod, hsub]; dsimp only [mv]; omega
                                  have hidx_eq : scrt[(4224 + 5 * (scr0[4214]'h4214).toNat +
                                        (4294967296 - 1 + ti.toNat)) % 4294967296]'(by
                                          rw [hadd, hlt]; exact fidCore_mv_lt 5
                                            (Nat.le_trans (Nat.sub_le ti.toNat 1) hti_le)
                                            hmv_lo hbge) =
                                        scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b :=
                                    m8_k6_get_congr (by
                                      rw [hadd, htr_e]; dsimp only [ti']; rw [hti1]) _ _
                                  rw [hidx_eq] at hc'; dsimp only [v, nv]
                                  rw [m8_bv32_lshr1_toNat]; exact Nat.lt_of_not_le hc'
                                have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := v)
                                  hmv_hi (by decide) (by omega)
                                have hfl_b : ((4224 + 6 * mv + v).setWidth 64).toNat <
                                    scrt.length := by
                                  rw [hlt, hfl_e]
                                  exact fidCore_mv_lt 6
                                    (Nat.le_trans (Nat.le_of_lt hv_lt) hnv_le) hmv_lo hbge
                                c0_hsplit
                                · c0_hsteps!; exact hLt ti'.toNat (ti', ()) mt
                                    (by dsimp only [ti']; rw [hti1]; omega)
                                    ⟨scrt, hikt, by dsimp only [ti']; rw [hti1]; omega, rfl, hmt⟩
                                · have hrs_e := fid_k6_off_add1 (mv := mv) (x := v)
                                    hmv_hi (by omega)
                                  let scrt1 := scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
                                    ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b)
                                      &&& ~~~2#32)
                                  have hikt1 := fidCoreInv_set_flags_e h4214 hmv_eq hikt
                                    (Nat.lt_of_lt_of_le hv_lt hnv_le) hfl_e
                                    ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b) &&&
                                      ~~~2#32)
                                  have hlt1 : scrt1.length = scr0.length := hikt1.2.1
                                  have hrs_b : ((4224 + mv + v).setWidth 64).toNat <
                                      scrt1.length := by
                                    rw [hlt1, hrs_e]
                                    exact fidCore_1_lt
                                      (Nat.le_trans (Nat.le_of_lt hv_lt) hnv_le) hmv_lo hbge
                                  c0_hsteps_nogrp; c0_hsplit
                                  · c0_hsteps!; exact hLt ti'.toNat (ti', ()) _
                                      (by dsimp only [ti']; rw [hti1]; omega)
                                      ⟨scrt1, hikt1, by dsimp only [ti']; rw [hti1]; omega, rfl, hm⟩
                                  · let rsn := scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b
                                    have hrsn_lt : rsn.toNat < nc.toNat := by
                                      have hc' := hc; fid_norm_ofnat
                                      simp (disch := fid_omega) only [bv_c0, Nat.reducePow,
                                        BitVec.reduceToNat] at hc'
                                      exact fidCore_rsn_lt h4214 rfl h4193 rfl rfl hlt hmv_hi
                                        hti_pos hti_le hti1 htr_e htr_b
                                        (by dsimp only [v]; rw [m8_bv32_lshr1_toNat])
                                        (Nat.lt_of_lt_of_le hv_lt hnv_le) hfl_e hrs_e hrs_b rfl hc'
                                    clear hc
                                    have hmr_e := fid_k6_off_add (mv := mv) (k := 33) (x := rsn)
                                      hmv_hi (by decide) (by omega)
                                    have hor_e := fid_k6_off_add (mv := mv) (k := 29) (x := rsn)
                                      hmv_hi (by decide) (by omega)
                                    have hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat <
                                        scrt1.length := by
                                      rw [hlt1, hmr_e]
                                      exact fidCore_k_lt 33
                                        (Nat.le_trans (Nat.le_of_lt hrsn_lt) hnc_le) hmv_lo hbge
                                    have hor_b : ((4224 + 29 * mv + rsn).setWidth 64).toNat <
                                        scrt1.length := by
                                      rw [hlt1, hor_e]
                                      exact fidCore_k_lt 29
                                        (Nat.le_trans (Nat.le_of_lt hrsn_lt) hnc_le) hmv_lo hbge
                                    let mr :=
                                      scrt1[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b
                                    let scrt2 := scrt1.set ((4224 + 33 * mv + rsn).setWidth
                                      64).toNat (mr ||| 0x80000000#32)
                                    have hikt2 : FidCoreInv scr0 mv nc scrt2 :=
                                      fidCoreInv_set_meta_pres h4214 hmv_eq hnc_le hikt1 hrsn_lt
                                        hmr_e hmr_b (m8_km_core_or_pres _)
                                    have hlt2 : scrt2.length = scr0.length := hikt2.2.1
                                    have hor_b2 : ((4224 + 29 * mv + rsn).setWidth 64).toNat <
                                        scrt2.length := by
                                      rw [hlt2, hor_e]
                                      exact fidCore_k_lt 29
                                        (Nat.le_trans (Nat.le_of_lt hrsn_lt) hnc_le) hmv_lo hbge
                                    have hmr_b2 : ((4224 + 33 * mv + rsn).setWidth 64).toNat <
                                        scrt2.length := by
                                      rw [hlt2, hmr_e]
                                      exact fidCore_k_lt 33
                                        (Nat.le_trans (Nat.le_of_lt hrsn_lt) hnc_le) hmv_lo hbge
                                    have ⟨hcl_t2, _, _, hlen_t2⟩ := fidCore_clause_ok_bnds
                                      h4214 hmv_eq h4193 hnc_eq h4207 hac_eq hmv_hi hnc_le
                                      hikt2 hrsn_lt hor_e hmr_e hor_b2 hmr_b2
                                    c0_hsteps_nogrp
                                    let roff :=
                                      scrt2[((4224 + 29 * mv + rsn).setWidth 64).toNat]'hor_b2
                                    let rsz := (scrt2[((4224 + 33 * mv + rsn).setWidth 64).toNat]'
                                      hmr_b2) &&& 0xFFFF#32
                                    have hrsz_le : rsz.toNat ≤ 65535 := m8_and_ffff_le _
                                    have hroff_bnd : roff.toNat + rsz.toNat ≤ acap.toNat := hcl_t2
                                    refine wp_join0 invS
                                      (fun _ mj ⟨scrj, hikj, hmj⟩ => by
                                        c0_hsteps!; exact hLt ti'.toNat (ti', ()) mj
                                          (by clear hLt hikj hmj; dsimp only [ti']
                                              rw [hti1]; omega)
                                          ⟨scrj, hikj,
                                            by clear hLt hikj hmj; dsimp only [ti']
                                               rw [hti1]; omega, rfl, hmj⟩)
                                      (fun Jc hJc => by
                                        c0_hsteps_nogrp; c0_hsplit
                                        · clear hc; c0_hsteps_nogrp
                                          refine wp_loop_group (ts := [i32])
                                            (fun rem_j (j, ()) mj => ∃ scrj : List (BitVec 32),
                                              FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ rsz.toNat ∧
                                              rem_j = rsz.toNat - j.toNat ∧
                                              (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
                                          · rintro Lj rem_j ⟨j, ⟨⟩⟩ mj hLj
                                              ⟨scrj, hikj, hj_le, rfl, hmj⟩
                                            have hlj : scrj.length = scr0.length := hikj.2.1
                                            c0_hsplit
                                            · have hj_lt : j.toNat < rsz.toNat := by
                                                have hc' := hc; clear hc; fid_norm_ofnat
                                                simp only [bv_c0, Nat.reducePow,
                                                  BitVec.reduceToNat] at hc'
                                                exact fidCore_trace_hj_lt h4214 rfl hmv_hi hlt
                                                  hti_pos hti_le hti1 htr_e (hlt ▸ htr_b)
                                                  (by dsimp only [v]; rw [m8_bv32_lshr1_toNat])
                                                  (Nat.lt_of_lt_of_le hv_lt hnv_le) hfl_e hfl_b
                                                  hrs_e hrs_b rfl (Nat.lt_of_lt_of_le hrsn_lt
                                                    hnc_le) hmr_e hmr_b rfl (by
                                                      dsimp only [rsz, scrt2]
                                                      rw [List.getElem_set_self]) hc'
                                              clear hc
                                              have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                                                m8_bv32_add1_toNat hj_lt
                                                  (by clear hikt1 hikt2 hcl_t2 hm hmj hikj hLt hLj
                                                      omega)
                                              have har_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                                (x := roff) (y := j) hmv_hi (by decide)
                                                (by clear hikt1 hikt2 hcl_t2 hm hmj hikj hLt hLj
                                                    omega)
                                              have har_b : ((4224 + 45 * mv + roff + j).setWidth
                                                  64).toNat < scrj.length := by
                                                clear hikt1 hikt2 hcl_t2 hm hmj hikj
                                                rw [hlj, har_e]; omega
                                              let lv := (scrj[((4224 + 45 * mv + roff + j).setWidth
                                                64).toNat]'har_b) >>> (1 : Nat)
                                              c0_hsteps_nogrp
                                              refine wp_join0 invS
                                                (fun _ mj' ⟨scrj', hikj', hmj'⟩ => by
                                                  c0_hsteps!
                                                  exact hLj (rsz.toNat - (j + 1#32).toNat)
                                                    (j + 1#32, ()) mj' (by
                                                      clear hLj hikj' hmj' hm hmj hikj hikt1 hikt2
                                                        hcl_t2 hLt; omega)
                                                    ⟨scrj', hikj', by
                                                      clear hLj hikj' hmj' hm hmj hikj hikt1 hikt2
                                                        hcl_t2 hLt; omega, rfl, hmj'⟩)
                                                (fun Js hJs => by
                                                  c0_hsplit
                                                  · have hlv_lt : lv.toNat < nv.toNat := by
                                                      have hc' := hc; clear hc; fid_norm_ofnat
                                                      simp only [bv_c0, Nat.reducePow,
                                                        BitVec.reduceToNat] at hc'
                                                      exact fidCore_trace_lv_lt h4214 rfl h4192 rfl
                                                        hmv_hi hlt hti_pos hti_le hti1 htr_e
                                                        (hlt ▸ htr_b)
                                                        (by dsimp only [v]
                                                            rw [m8_bv32_lshr1_toNat])
                                                        (Nat.lt_of_lt_of_le hv_lt hnv_le) hfl_e
                                                        hfl_b hrs_e hrs_b rfl
                                                        (show rsn.toNat <
                                                            8 * (scr0[4214]'h4214).toNat
                                                          from Nat.lt_of_lt_of_le hrsn_lt
                                                            (Nat.le_trans hnc_le
                                                              (Nat.mul_le_mul_right _
                                                                (by decide : 4 ≤ 8))))
                                                        hmr_e hmr_b rfl rfl rfl
                                                        (fid_k6_off_add (mv := mv) (k := 29)
                                                          (x := rsn) hmv_hi (by decide)
                                                          (Nat.lt_of_lt_of_le hrsn_lt
                                                            (Nat.le_trans hnc_le
                                                              (Nat.le_trans
                                                                (Nat.mul_le_mul_left 4 hmv_hi)
                                                                (by decide)))))
                                                        hor_b2 rfl har_e har_b hc'
                                                    clear hc
                                                    c0_hsplit
                                                    · have hfl_lv := fid_k6_off_add (mv := mv)
                                                        (k := 6) (x := lv) hmv_hi (by decide)
                                                        (Nat.lt_of_lt_of_le
                                                          (Nat.lt_of_lt_of_le hlv_lt hnv_le)
                                                          (Nat.le_trans hmv_hi (by decide)))
                                                      have hfl_lvb :
                                                          ((4224 + 6 * mv + lv).setWidth 64).toNat
                                                            < scrj.length := by
                                                        rw [hlj, hfl_lv]
                                                        exact fidCore_b6_lt
                                                          (Nat.lt_of_lt_of_le hlv_lt hnv_le) hbge
                                                      c0_hsteps!
                                                      exact hJs _ ⟨_, fidCoreInv_set_flags_e
                                                        h4214 hmv_eq hikj
                                                        (by first | exact hlv_lt |
                                                          exact Nat.lt_of_lt_of_le hlv_lt hnv_le)
                                                        hfl_lv _, hm⟩
                                                    · c0_hsteps!; exact hJs _ ⟨scrj, hikj, hmj⟩
                                                  · c0_hsteps!; exact hJs _ ⟨scrj, hikj, hmj⟩)
                                            · c0_hsteps!; exact hJc mj ⟨scrj, hikj, hmj⟩
                                          · intro Lj hLj; c0_hsteps!; exact hLj rsz.toNat (0#32, ())
                                              _ ⟨scrt2, hikt2, Nat.zero_le _, by simp, hm⟩
                                        · c0_hsteps!; exact hJc _ ⟨scrt2, hikt2, hm⟩)
                            · -- Clear `flags & 2` on `0 ..< nv` after traceback
                              c0_hsteps_nogrp
                              refine wp_loop_group (ts := [i32])
                                (fun rem_f (i, ()) mf => ∃ scrf : List (BitVec 32),
                                  FidCoreInv scr0 mv nc scrf ∧ i.toNat ≤ nv.toNat ∧
                                  rem_f = nv.toNat - i.toNat ∧
                                  (FullMem c (m8ScrSt s scrf) ⋆ R) mf) ?_ ?_
                              · rintro Lf rem_f ⟨i, ⟨⟩⟩ mf hLf ⟨scrf, hikf, hi_le, rfl, hmf⟩
                                have hlf : scrf.length = scr0.length := hikf.2.1
                                c0_hsplit
                                · have hi_lt : i.toNat < nv.toNat := hc
                                  have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                                    m8_bv32_add1_toNat hi_lt (by clear hLf hikf hmf; omega)
                                  have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := i)
                                    hmv_hi (by decide) (by clear hLf hikf hmf; omega)
                                  have hfl_b : ((4224 + 6 * mv + i).setWidth 64).toNat <
                                      scrf.length := by
                                    rw [hlf, hfl_e]
                                    exact fidCore_mv_lt 6
                                      (Nat.le_trans (Nat.le_of_lt hi_lt) hnv_le) hmv_lo hbge
                                  c0_hsteps!
                                  exact hLf (nv.toNat - (i + 1#32).toNat) (i + 1#32, ()) _
                                    (by clear hLf hikf; omega)
                                    ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hikf
                                      (by clear hLf hikf; omega)
                                      hfl_e _, by clear hLf hikf; omega, rfl, hm⟩
                                · c0_hsteps!; exact hJ2 (_, scrf) mf ⟨hikf, hmf⟩
                              · intro Lf hLf; c0_hsteps!
                                exact hLf nv.toNat (0#32, ()) mt
                                  ⟨scrt, hikt, Nat.zero_le _, by simp, hmt⟩
                          · intro Lt hLt; c0_hsteps!
                            exact hLt ti0.toNat (ti0, ()) mb ⟨scrm, hikm, hti0, rfl, hmb⟩
                        · intro Jti hJti; c0_hsplit
                          · c0_hsteps!; exact hJti mv (Nat.le_refl _)
                          · c0_hsteps!; exact hJti _ (Nat.le_of_not_lt hc)
                      · intro Jm hJm
                        clear hLa hml hikl hJ2
                        have hco_b2 : ((4224 + 29 * mv + inc).setWidth 64).toNat < scrb.length := by
                          rw [hlb, hco_e]
                          exact fidCore_k_lt 29
                            (Nat.le_trans (Nat.le_of_lt hinc_lt) hnc_le) hmv_lo hbge
                        have hcm_b2 : ((4224 + 33 * mv + inc).setWidth 64).toNat < scrb.length := by
                          rw [hlb, hcm_e]
                          exact fidCore_k_lt 33
                            (Nat.le_trans (Nat.le_of_lt hinc_lt) hnc_le) hmv_lo hbge
                        let off_i := scrb[((4224 + 29 * mv + inc).setWidth 64).toNat]'hco_b2
                        let sz_i :=
                          (scrb[((4224 + 33 * mv + inc).setWidth 64).toNat]'hcm_b2) &&& 0xFFFF#32
                        have hszi_le : sz_i.toNat ≤ 65535 := m8_and_ffff_le _
                        have hszi_bnd := (fidCore_clause_ok_bnds
                          h4214 hmv_eq h4193 hnc_eq h4207 hac_eq hmv_hi hnc_le
                          hikb hinc_lt hco_e hcm_e hco_b2 hcm_b2).1
                        c0_hsplit
                        · try clear hc
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem_j (j, ()) mj => ∃ scrj : List (BitVec 32),
                              FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ sz_i.toNat ∧
                              rem_j = sz_i.toNat - j.toNat ∧
                              (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
                          · rintro Lj rem_j ⟨j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
                            clear hikb hm hmv_b hnc_b hac_b
                            have hlj : scrj.length = scr0.length := hikj.2.1
                            c0_hsplit
                            · have hj_lt : j.toNat < sz_i.toNat := by
                                have hc' := hc; fid_norm_ofnat
                                simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                                have hcm_u4 : 4224 + 33 * mv.toNat +
                                    (scrl[4199]'h4199).toNat < 4294967296 := by
                                  clear hc hc' hLj hikj hcl_b hJm; exact by omega
                                have hcm_eq_i : (4224 + 33 * (scr0[4214]'h4214).toNat +
                                      (scrl[4199]'h4199).toNat) % 4294967296 =
                                      4224 + 33 * mv.toNat + (scrl[4199]'h4199).toNat := by
                                  rw [hmv_d, Nat.mod_eq_of_lt hcm_u4]
                                have hc1 := fidCore_p4_hc_rw hcm_eq_i
                                  (hb1' := by
                                    clear hc hc' hLj hikj hcl_b
                                    rw [show scrl[4199]'h4199 = inc from rfl, ← hcm_e]
                                    exact hcm_b)
                                  (hb2' := by
                                    clear hc hc' hLj hikj hcl_b
                                    rw [List.length_set, show scrl[4199]'h4199 = inc from rfl,
                                      ← hcm_e]
                                    exact hcm_b) hc'
                                clear hc'; have hc' := hc1; clear hc1
                                have hmeta_e :
                                    ((scra.set (4224 + 33 * mv.toNat +
                                      (scrl[4199]'(by omega)).toNat)
                                      ((scra[4224 + 33 * mv.toNat +
                                        (scrl[4199]'(by omega)).toNat]'(by
                                          rw [show (scra.length = scr0.length) from hika.2.1]
                                          omega)) |||
                                        2147483648#32))[4224 + 33 * mv.toNat +
                                      (scrl[4199]'(by omega)).toNat]'(by
                                        rw [List.length_set, show scra.length = scr0.length from
                                          hika.2.1]
                                        omega)).toNat % 65536 = sz_i.toNat := by
                                  have h1 :
                                      4224 + 33 * mv.toNat + (scrl[4199]'(by omega)).toNat =
                                        ((4224 + 33 * mv + inc).setWidth 64).toNat := by rw [hcm_e]
                                  have h2 :
                                      scra[4224 + 33 * mv.toNat +
                                        (scrl[4199]'(by omega)).toNat]'(by
                                          rw [show scra.length = scr0.length from hika.2.1]
                                          omega) =
                                        scra[((4224 + 33 * mv + inc).setWidth 64).toNat]'hcm_b :=
                                    m8_k6_get_congr h1 _ _
                                  have hset_eq :
                                      (scra.set (4224 + 33 * mv.toNat +
                                          (scrl[4199]'(by omega)).toNat)
                                        ((scra[4224 + 33 * mv.toNat +
                                          (scrl[4199]'(by omega)).toNat]'(by
                                            rw [show (scra.length = scr0.length) from hika.2.1]
                                            omega)) ||| 2147483648#32))[4224 + 33 * mv.toNat +
                                        (scrl[4199]'(by omega)).toNat]'(by
                                          rw [List.length_set, show scra.length = scr0.length from
                                            hika.2.1]
                                          omega) = scrb[((4224 + 33 * mv + inc).setWidth
                                          64).toNat]'hcm_b2 := by
                                    rw [← Option.some_inj, ← List.getElem?_eq_getElem,
                                      ← List.getElem?_eq_getElem, List.getElem?_set_self (by
                                        rw [show scra.length = scr0.length from hika.2.1]; omega)]
                                    dsimp only [scrb]
                                    rw [hcm_e, List.getElem?_set_self (by
                                      rw [show scra.length = scr0.length from hika.2.1]; omega),
                                      Option.some_inj]
                                    exact congrArg (· ||| 2147483648#32) h2
                                  dsimp only [sz_i]; rw [fid_bv32_and_ffff_toNat, hset_eq]
                                try rw [hmeta_e] at hc'
                                exact hc'
                              have hszi_bnd : off_i.toNat + sz_i.toNat ≤ acap.toNat := hszi_bnd
                              have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                                m8_bv32_add1_toNat hj_lt (by clear hLj hikj hcl_b hJm; omega)
                              have har_e := fid_k6_off_add2 (mv := mv) (k := 45)
                                (x := off_i) (y := j) hmv_hi (by decide)
                                (by clear hLj hikj hcl_b hJm; omega)
                              have har_b :
                                  ((4224 + 45 * mv + off_i + j).setWidth 64).toNat <
                                    scrj.length := by
                                clear hLj hikj hcl_b hJm; rw [hlj, har_e]; omega
                              let lv :=
                                (scrj[((4224 + 45 * mv + off_i + j).setWidth 64).toNat]'
                                  har_b) >>> (1 : Nat)
                              have hoff_raw_g : ∀ {hb_a1 hb_a2 hb_a3 hb_b1 hb_b2 hb_b3 hb_c hb_d},
                                  (scra.set
                                      (((4224 : BitVec 32) + (33 : BitVec 32) * (scr0[4214]'hb_a1) +
                                        (scrl[4199]'hb_b1)).setWidth 64).toNat
                                      ((scra[((4224 : BitVec 32) + (33 : BitVec 32) *
                                        (scr0[4214]'hb_a2) + (scrl[4199]'hb_b2)).setWidth
                                        64 |>.toNat]'hb_c) ||| 2147483648#32))[
                                      ((4224 : BitVec 32) + (29 : BitVec 32) * (scr0[4214]'hb_a3) +
                                      (scrl[4199]'hb_b3)).setWidth 64 |>.toNat]'hb_d = off_i := by
                                intro hb_a1 hb_a2 hb_a3 hb_b1 hb_b2 hb_b3 hb_c hb_d
                                rw [← Option.some_inj, ← List.getElem?_eq_getElem,
                                  ← List.getElem?_eq_getElem, List.getElem?_set_ne (by
                                    change ((4224 + 33 * mv + inc).setWidth 64).toNat ≠
                                      ((4224 + 29 * mv + inc).setWidth 64).toNat
                                    rw [hcm_e, hco_e]; clear hLj hikj hcl_b hJm; omega)]
                                dsimp only [off_i, scrb]
                                rw [List.getElem?_set_ne (by
                                  rw [hco_e]; clear hLj hikj hcl_b hJm; omega)]
                              conv =>
                                arg 4; arg 1; arg 2; arg 2; arg 1; arg 1
                                tactic => exact hoff_raw_g
                              c0_hsteps_nogrp
                              refine wp_join0 invS
                                (fun _ mj' ⟨scrj', hikj', hmj'⟩ => by
                                  c0_hsteps!
                                  exact hLj (sz_i.toNat - (j + 1#32).toNat) (j + 1#32, ()) mj'
                                    (by clear hLj hikj' hmj' hmj hikj; omega)
                                    ⟨scrj', hikj', by clear hLj hikj' hmj' hmj hikj; omega,
                                      rfl, hmj'⟩)
                                (fun Js hJs => by
                                  c0_hsplit
                                  · have hlv_lt : lv.toNat < nv.toNat := by
                                      first
                                      | exact hc
                                      | (have hc' := hc; clear hc; fid_norm_ofnat
                                         simp only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                                         exact fidCore_p4_hlv_off h4214 rfl h4192 rfl har_e har_b
                                           rfl hc')
                                    have hfl_lv := fid_k6_off_add (mv := mv) (k := 6) (x := lv)
                                      hmv_hi (by decide)
                                      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlv_lt hnv_le)
                                        (Nat.le_trans hmv_hi (by decide)))
                                    have hfl_lvb : ((4224 + 6 * mv + lv).setWidth 64).toNat <
                                        scrj.length := by
                                      rw [hlj, hfl_lv]
                                      exact fidCore_b6_lt (Nat.lt_of_lt_of_le hlv_lt hnv_le) hbge
                                    c0_hsteps!
                                    exact hJs _ ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hikj
                                      (Nat.lt_of_lt_of_le hlv_lt hnv_le) hfl_lv _, hm⟩
                                  · c0_hsteps!; exact hJs _ ⟨scrj, hikj, hmj⟩)
                            · c0_hsteps!; exact hJm mj ⟨scrj, hikj, hmj⟩
                          · intro Lj hLj; c0_hsteps!
                            exact hLj sz_i.toNat (0#32, ()) _
                              ⟨scrb, hikb, Nat.zero_le _, by simp, hm⟩
                        · c0_hsteps!; exact hJm _ ⟨scrb, hikb, hm⟩
                  · intro La hLa; c0_hsteps!
                    exact hLa nv.toNat (0#32, ()) ml ⟨scrl, hikl, Nat.zero_le _, by simp, hml⟩
                · c0_hsteps!; exact hJ2 (_, scrl) ml ⟨hikl, hml⟩
          · intro L1 hL1; c0_hsteps!
            exact hL1 nc.toNat (0#32, ()) m0 ⟨scr0, hinv0, Nat.zero_le _, by simp, hm0'⟩

end LeanQbe.T.Examples.Kissat.FullFidelityBve
