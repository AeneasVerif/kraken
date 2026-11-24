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
# Kissat M8 Core Parity K6 Primitives — Part 0 (`watch`, `assign`, `mtf`, `backtrack`, `ana_cl`)
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
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m8_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-- Parametric `Func.wp` proof for `full_k6_watch_m8`. -/
theorem full_k6_watch_m8_wp (Γ : Env) :
    ∀ a m Q X, m8K6WatchSpec a m Q X →
      Func.wp Γ full_k6_watch_m8_body a m Q X := by
  rintro ⟨h, cid, l0, l1, sz, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hm0, hQ⟩ := m8K6WatchSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hsc := c.hscr; unfold dimacsBound at hsc
  unfold Func.wp full_k6_watch_m8_body
  c0_hsplit
  · c0_hsteps!; exact hQ s.scratch.scratch_buf m0 hscr_len (fun _ _ _ => rfl) hm0
  · have hcid : cid.toNat < 1024 := Nat.lt_of_not_le (show ¬1024 ≤ cid.toNat from by simpa using hc)
    c0_hsplit
    · c0_hsteps!; exact hQ s.scratch.scratch_buf m0 hscr_len (fun _ _ _ => rfl) hm0
    · have hl0 : l0.toNat < 512 :=
        Nat.lt_of_not_le (show ¬512 ≤ l0.toNat from by simpa [BitVec.toNat_shiftLeft,
          Nat.shiftLeft_eq] using hc)
      c0_hsplit
      · c0_hsteps!; exact hQ s.scratch.scratch_buf m0 hscr_len (fun _ _ _ => rfl) hm0
      · have hl1 : l1.toNat < 512 :=
          Nat.lt_of_not_le (show ¬512 ≤ l1.toNat from by simpa [BitVec.toNat_shiftLeft,
            Nat.shiftLeft_eq] using hc)
        have hcid2_or1 : ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 :=
          m8_bv32_shl1_or1_toNat (by omega)
        have hw0_eq : ((7552#32 + (cid <<< (1 : Nat))).setWidth 64).toNat = 7552 + 2 * cid.toNat :=
          by
          rw [m6_zext32_toNat, BitVec.toNat_add, show (7552#32 : BitVec 32).toNat = 7552 from rfl,
            BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          omega
        have hw1_eq : ((7552#32 + ((cid <<< (1 : Nat)) ||| 1#32)).setWidth 64).toNat = 7553 +
          2 * cid.toNat := by
          rw [m6_zext32_toNat, BitVec.toNat_add, show (7552#32 : BitVec 32).toNat = 7552 from rfl,
            hcid2_or1]
          omega
        have hb0_eq : ((9600#32 + (cid <<< (1 : Nat))).setWidth 64).toNat = 9600 + 2 * cid.toNat :=
          by
          rw [m6_zext32_toNat, BitVec.toNat_add, show (9600#32 : BitVec 32).toNat = 9600 from rfl,
            BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          omega
        have hb1_eq : ((9600#32 + ((cid <<< (1 : Nat)) ||| 1#32)).setWidth 64).toNat = 9601 +
          2 * cid.toNat := by
          rw [m6_zext32_toNat, BitVec.toNat_add, show (9600#32 : BitVec 32).toNat = 9600 from rfl,
            hcid2_or1]
          omega
        have hh0_eq : ((7040#32 + l0).setWidth 64).toNat = 7040 + l0.toNat := by
          rw [m6_zext32_toNat, BitVec.toNat_add, show (7040#32 : BitVec 32).toNat = 7040 from rfl]
          omega
        have hh1_eq : ((7040#32 + l1).setWidth 64).toNat = 7040 + l1.toNat := by
          rw [m6_zext32_toNat, BitVec.toNat_add, show (7040#32 : BitVec 32).toNat = 7040 from rfl]
          omega
        have hw0 : ((7552#32 + (cid <<< (1 : Nat))).setWidth 64).toNat <
          s.scratch.scratch_buf.length := by
          rw [hw0_eq, hscr_len]; omega
        have hw1 : ((7552#32 + ((cid <<< (1 : Nat)) ||| 1#32)).setWidth 64).toNat <
          s.scratch.scratch_buf.length := by
          rw [hw1_eq, hscr_len]; omega
        have hb0 : ((9600#32 + (cid <<< (1 : Nat))).setWidth 64).toNat <
          s.scratch.scratch_buf.length := by
          rw [hb0_eq, hscr_len]; omega
        have hb1 : ((9600#32 + ((cid <<< (1 : Nat)) ||| 1#32)).setWidth 64).toNat <
          s.scratch.scratch_buf.length := by
          rw [hb1_eq, hscr_len]; omega
        have hh0 : ((7040#32 + l0).setWidth 64).toNat < s.scratch.scratch_buf.length := by
          rw [hh0_eq, hscr_len]; omega
        have hh1 : ((7040#32 + l1).setWidth 64).toNat < s.scratch.scratch_buf.length := by
          rw [hh1_eq, hscr_len]; omega
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun bf => (bf, ())) (fun _ => True)
          ?_ ?_
        · rintro _ bf _
          have hcid_shl1_lt : (cid <<< (1 : BitVec 32)).toNat < 2048 := by
            change (cid <<< (1 : Nat)).toNat < 2048
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; omega
          have hcid_shl1_nat_lt : (cid <<< (1 : Nat)).toNat < 2048 := hcid_shl1_lt
          have hcid_or1_lt : ((cid <<< (1 : BitVec 32)) ||| (1 : BitVec 32)).toNat < 2048 := by
            change ((cid <<< (1 : Nat)) ||| 1#32).toNat < 2048
            rw [hcid2_or1]; omega
          have hcid_or1_nat_lt : ((cid <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat < 2048 :=
            hcid_or1_lt
          c0_hsteps!
          refine hQ _ _ (by simp [hscr_len]) (fun idx hi hor => by
            have h1_w : (cid <<< OfNat.ofNat 1 ||| 1).toNat = 2 * cid.toNat + 1 := hcid2_or1
            have h0_w : (cid <<< OfNat.ofNat 1).toNat = 2 * cid.toNat := by
              change (cid <<< (1 : Nat)).toNat = _; rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                Nat.pow_one]; omega
            repeat rw [List.getElem?_set_ne (by
              simp only [m6_zext32_toNat, BitVec.toNat_add]
              try rw [h1_w]
              try rw [h0_w]
              try rw [show BitVec.toNat (7040 : BitVec 32) = 7040 from rfl]
              try rw [show BitVec.toNat (7552 : BitVec 32) = 7552 from rfl]
              try rw [show BitVec.toNat (9600 : BitVec 32) = 9600 from rfl]
              rw [Nat.mod_eq_of_lt (by omega)]
              omega)]) hm
        · intro J hJ
          c0_hsplit
          · c0_hsteps!; exact hJ 0x80000000#32 trivial
          · c0_hsteps!; exact hJ 0#32 trivial

/-- Parametric `Func.wp` proof for `full_k6_assign_m8`. -/
theorem full_k6_assign_m8_wp (Γ : Env) :
    ∀ a m Q X, m8K6AssignSpec a m Q X →
      Func.wp Γ full_k6_assign_m8_body a m Q X := by
  rintro ⟨h, lit, rsn_cid, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hm0, hQ⟩ := m8K6AssignSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hsc := c.hscr; unfold dimacsBound at hsc
  have h4195 := m8_scr_imm_lt hscr_len hsc16 (k := 4195) (by decide)
  have h4197 := m8_scr_imm_lt hscr_len hsc16 (k := 4197) (by decide)
  have h4198 := m8_scr_imm_lt hscr_len hsc16 (k := 4198) (by decide)
  unfold Func.wp full_k6_assign_m8_body
  c0_hsplit
  · c0_hsteps!; exact hQ s.scratch.scratch_buf m0 hscr_len (fun _ _ _ _ _ _ _ => rfl) hm0
  · have hlit : lit.toNat < 512 :=
      Nat.lt_of_not_le (show ¬512 ≤ lit.toNat from by simpa [BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq] using hc)
    c0_hsplit
    · c0_hsteps!; exact hQ s.scratch.scratch_buf m0 hscr_len (fun _ _ _ _ _ _ _ => rfl) hm0
    · have hte : (s.scratch.scratch_buf[4197]'(by omega)).toNat < 256 :=
        Nat.lt_of_not_le (show ¬256 ≤ (s.scratch.scratch_buf[4197]'(by omega)).toNat from hc)
      let v := lit >>> (1 : Nat)
      have hv_lt : v.toNat < 256 := by dsimp only [v]; rw [m8_bv32_lshr1_toNat]; omega
      have hln_lt : (lit ^^^ 1#32).toNat < 512 := (m8_bv32_xor1_lt (n := 256) lit hlit).2
      have hl6528 : ((6528#32 + lit).setWidth 64).toNat < s.scratch.scratch_buf.length := by
        rw [hscr_len, m6_zext32_toNat]; c0_bound
      have hln6528_s : ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat <
          (s.scratch.scratch_buf.set ((6528#32 + lit).setWidth 64).toNat 1#32).length := by
        rw [List.length_set, hscr_len, m6_zext32_toNat]; c0_bound
      have hv4224_s : ((4224#32 + v).setWidth 64).toNat <
          ((s.scratch.scratch_buf.set ((6528#32 + lit).setWidth 64).toNat 1#32).set
            ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat 2#32).length := by
        rw [List.length_set, List.length_set, hscr_len, m6_zext32_toNat]; c0_bound
      have hv4480_s : ((4480#32 + v).setWidth 64).toNat <
          (((s.scratch.scratch_buf.set ((6528#32 + lit).setWidth 64).toNat 1#32).set
            ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat 2#32).set
            ((4224#32 + v).setWidth 64).toNat (s.scratch.scratch_buf[4195]'(by omega))).length := by
        rw [List.length_set, List.length_set, List.length_set, hscr_len, m6_zext32_toNat]; c0_bound
      have hte5504_s : ((5504#32 + s.scratch.scratch_buf[4197]'(by omega)).setWidth 64).toNat <
          ((((s.scratch.scratch_buf.set ((6528#32 + lit).setWidth 64).toNat 1#32).set
            ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat 2#32).set
            ((4224#32 + v).setWidth 64).toNat (s.scratch.scratch_buf[4195]'(by omega))).set
            ((4480#32 + v).setWidth 64).toNat rsn_cid).length := by
        have h4197_lt : (s.scratch.scratch_buf[4197]'(by omega)).toNat < 256 := hte
        rw [List.length_set, List.length_set, List.length_set, List.length_set]
        exact Nat.lt_of_lt_of_eq (by
          rw [m6_zext32_toNat, BitVec.toNat_add, show (5504#32 : BitVec 32).toNat = 5504 from rfl,
            Nat.mod_eq_of_lt (by omega)]
          omega) hscr_len.symm
      have h4197_s : 4197 <
          (((((s.scratch.scratch_buf.set ((6528#32 + lit).setWidth 64).toNat 1#32).set
            ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat 2#32).set
            ((4224#32 + v).setWidth 64).toNat (s.scratch.scratch_buf[4195]'(by omega))).set
            ((4480#32 + v).setWidth 64).toNat rsn_cid).set
            ((5504#32 + s.scratch.scratch_buf[4197]'(by omega)).setWidth 64).toNat lit).length := by
        simp only [List.length_set]; exact h4197
      c0_hsteps_nogrp
      refine wp_join0
        (fun mj => ∃ scrj : List (BitVec 32),
          scrj.length = c.scratch_cap ∧
          (∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
            (idx < 4224 ∨ 4736 ≤ idx) → (idx < 5504 ∨ 5760 ≤ idx) →
            (idx < 6528 ∨ 7040 ≤ idx) → scrj[idx]? = s.scratch.scratch_buf[idx]?) ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scrj } } ⋆ R) mj)
        ?_ ?_
      · rintro _ mj ⟨scrj, hlj, hkj, hmj⟩
        have hv5760 : ((5760#32 + v).setWidth 64).toNat < scrj.length := by
          rw [hlj, m6_zext32_toNat]; c0_bound
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun nfl => (nfl, ())) (fun _ => True)
          ?_ ?_
        · rintro _ nfl _
          c0_hsteps!
          refine hQ _ _ (by simp [hlj]) (fun idx hi h97 h98 ha hb hc' => by
            rw [List.getElem?_set_ne (by
              simp only [m6_zext32_toNat, BitVec.toNat_add,
                show BitVec.toNat (5760 : BitVec 32) = 5760 from rfl,
                show (lit >>> (1 : Nat)).toNat = lit.toNat / 2 from m8_bv32_lshr1_toNat lit]
              rw [Nat.mod_eq_of_lt (by omega)]
              omega)]
            exact hkj idx hi h97 h98 ha (Or.imp_right (fun h => by omega) hb) hc') hm
        · intro Jf hJf
          c0_hsplit
          · c0_hsteps!; exact hJf _ trivial
          · c0_hsteps!; exact hJf _ trivial
      · intro J0 hJ0
        have h4197_lt : (s.scratch.scratch_buf[(4197#64).toNat]'(by
            rw [show (4197#64).toNat = 4197 from rfl]; exact h4197)).toNat < 256 := by
          simpa [show (4197#64).toNat = 4197 from rfl] using hte
        c0_hsplit
        · have h4198_s : (4198#64).toNat <
              ((((((s.scratch.scratch_buf.set ((6528#32 + lit).setWidth 64).toNat 1#32).set
                ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat 2#32).set
                ((4224#32 + v).setWidth 64).toNat (s.scratch.scratch_buf[4195]'(by omega))).set
                ((4480#32 + v).setWidth 64).toNat rsn_cid).set
                ((5504#32 + s.scratch.scratch_buf[4197]'(by omega)).setWidth 64).toNat lit).set
                (4197#64).toNat (s.scratch.scratch_buf[4197]'(by omega) + 1#32)).length := by
            simp only [List.length_set, hscr_len, show (4198#64).toNat = 4198 from rfl]; omega
          dsimp only at *
          c0_hsteps!
          refine hJ0 _ ⟨_, by simp [hscr_len], fun idx hi h97 h98 ha hb hc' => by
            simp only [m6_zext32_toNat, BitVec.toNat_add,
              show (4197#64).toNat = 4197 from rfl,
              show (4198#64).toNat = 4198 from rfl,
              show (4224#32 : BitVec 32).toNat = 4224 from rfl,
              show (4480#32 : BitVec 32).toNat = 4480 from rfl,
              show (5504#32 : BitVec 32).toNat = 5504 from rfl,
              show (6528#32 : BitVec 32).toNat = 6528 from rfl] at *
            repeat (first | rw [List.getElem?_set_ne (by omega)] | rw [List.getElem?_set_ne (by
              c0_bound)]), hm⟩
        · c0_hsteps!
          refine hJ0 _ ⟨_, by simp [hscr_len], fun idx hi h97 h98 ha hb hc' => by
            simp only [m6_zext32_toNat, BitVec.toNat_add,
              show (4197#64).toNat = 4197 from rfl,
              show (4224#32 : BitVec 32).toNat = 4224 from rfl,
              show (4480#32 : BitVec 32).toNat = 4480 from rfl,
              show (5504#32 : BitVec 32).toNat = 5504 from rfl,
              show (6528#32 : BitVec 32).toNat = 6528 from rfl] at *
            repeat (first | rw [List.getElem?_set_ne (by omega)] | rw [List.getElem?_set_ne (by
              c0_bound)]), hm⟩

/-- Parametric `Func.wp` proof for `full_k6_mtf_m8`. -/
theorem full_k6_mtf_m8_wp (Γ : Env) :
    ∀ a m Q X, m8K6MtfSpec a m Q X →
      Func.wp Γ full_k6_mtf_m8_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hm0, hQ⟩ := m8K6MtfSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hsc := c.hscr; unfold dimacsBound at hsc
  let scr := s.scratch.scratch_buf
  have hscr_l : scr.length = c.scratch_cap := hscr_len
  have h4192 := m8_scr_imm_lt hscr_len hsc16 (k := 4192) (by decide)
  have h4200 := m8_scr_imm_lt hscr_len hsc16 (k := 4200) (by decide)
  have h4201 := m8_scr_imm_lt hscr_len hsc16 (k := 4201) (by decide)
  have h4202 := m8_scr_imm_lt hscr_len hsc16 (k := 4202) (by decide)
  have h4203 := m8_scr_imm_lt hscr_len hsc16 (k := 4203) (by decide)
  let nv := scr[4192]'(by rw [hscr_l]; omega)
  unfold Func.wp full_k6_mtf_m8_body
  c0_hsplit
  · c0_hsteps!; exact hQ scr m0 hscr_len (fun _ _ _ => rfl) hm0
  · have hv_lt : v.toNat < nv.toNat :=
      Nat.lt_of_not_le (show ¬nv.toNat ≤ v.toNat from by simpa [nv, scr] using hc)
    c0_hsplit
    · c0_hsteps!; exact hQ scr m0 hscr_len (fun _ _ _ => rfl) hm0
    · have hnv : nv.toNat ≤ 256 := Nat.le_of_not_lt (show ¬256 < nv.toNat from by simpa [nv,
        scr] using hc)
      have hv4736 : ((4736#32 + v).setWidth 64).toNat < scr.length := by
        rw [hscr_l, m6_zext32_toNat]; c0_bound
      have hv4992 : ((4992#32 + v).setWidth 64).toNat < scr.length := by
        rw [hscr_l, m6_zext32_toNat]; c0_bound
      let pv := scr[4736 + v.toNat]'(by omega)
      let nxt := scr[4992 + v.toNat]'(by omega)
      let keep := fun (scr' : List (BitVec 32)) (m' : Mem 64) =>
        scr'.length = c.scratch_cap ∧
        (∀ idx < c.scratch_cap, (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4736) ∨ 5504 ≤ idx) →
          scr'[idx]? = scr[idx]?) ∧
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m'
      c0_hsteps_nogrp
      refine wp_join0 (fun m1 => ∃ sc1, keep sc1 m1) ?_ ?_
      · intro _ m1 ⟨sc1, hl1, hk1, hm1⟩
        have h4202_1 : 4202 < sc1.length := by rw [hl1]; omega
        have h4203_1 : 4203 < sc1.length := by rw [hl1]; omega
        have hv5248 : ((5248#32 + v).setWidth 64).toNat < sc1.length := by
          rw [hl1, m6_zext32_toNat]; c0_bound
        c0_hsteps!
        refine hQ _ _ (by simp [hl1]) (fun idx hi hor => by
          have hv5248_eq : ((5248#32 + v).setWidth 64).toNat = 5248 + v.toNat := by
            rw [m6_zext32_toNat, BitVec.toNat_add, show (5248#32 : BitVec 32).toNat = 5248 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          rw [List.getElem?_set_ne (by
                change (4202#64).toNat ≠ idx
                rw [show (4202#64).toNat = 4202 from rfl]; omega),
            List.getElem?_set_ne (by
                change ((5248#32 + v).setWidth 64).toNat ≠ idx
                rw [hv5248_eq]; omega),
            List.getElem?_set_ne (by
                change (4203#64).toNat ≠ idx
                rw [show (4203#64).toNat = 4203 from rfl]; omega)]
          exact hk1 idx hi hor) hm
      · intro J1 hJ1
        c0_hsplit
        · c0_hsteps_nogrp
          refine wp_join0 (fun m2 => ∃ sc2, keep sc2 m2) ?_ ?_
          · intro _ m2 ⟨sc2, hl2, hk2, hm2⟩
            c0_hsteps_nogrp
            refine wp_join0 (fun m3 => ∃ sc3, keep sc3 m3) ?_ ?_
            · intro _ m3 ⟨sc3, hl3, hk3, hm3⟩
              have h4200_3 : 4200 < sc3.length := by rw [hl3]; omega
              have h4201_3 : 4201 < sc3.length := by rw [hl3]; omega
              have hv4736_3 : ((4736#32 + v).setWidth 64).toNat < sc3.length := by
                rw [hl3, m6_zext32_toNat]; c0_bound
              have hv4992_3 : ((4992#32 + v).setWidth 64).toNat < sc3.length := by
                rw [hl3, m6_zext32_toNat]; c0_bound
              c0_hsteps_nogrp
              refine wp_join0 (fun m4 => ∃ sc4, keep sc4 m4) ?_ ?_
              · intro _ m4 ⟨sc4, hl4, hk4, hm4⟩
                have h4201_4 : 4201 < sc4.length := by rw [hl4]; omega
                c0_hsteps!; exact hJ1 _ ⟨_, by simp [hl4], fun idx hi hor => by
                  rw [List.getElem?_set_ne (by
                    have : (4201#64).toNat = 4201 := rfl
                    rw [this]; omega)]
                  exact hk4 idx hi hor, hm⟩
              · intro J4 hJ4
                c0_hsplit
                · have hold_lt : (sc3[4201]'h4201_3).toNat < nv.toNat := by
                    have h1 : OfNat.ofNat 4201 % 2 ^ 64 = 4201 := by decide
                    have h2 : OfNat.ofNat 4192 % 2 ^ 64 = 4192 := by decide
                    simpa only [h1, h2, nv, scr] using hc
                  have hold_lt_4201 : (sc3[4201]'h4201_3).toNat < nv.toNat := hold_lt
                  have ho4992 : ((4992#32 + (sc3[(4201#64).toNat]'(by
                        rw [show (4201#64).toNat =
                          4201 from rfl]; exact h4201_3))).setWidth 64).toNat <
                      ((sc3.set ((4736#32 + v).setWidth 64).toNat (sc3[(4201#64).toNat]'(by
                          rw [show (4201#64).toNat = 4201 from rfl]; exact h4201_3))).set
                        ((4992#32 + v).setWidth 64).toNat 0xFFFFFFFF#32).length := by
                    simp only [List.length_set, hl3, m6_zext32_toNat]; c0_bound
                  c0_hsteps!
                  refine hJ4 _ ⟨_, by simp [hl3], fun idx hi hor => by
                    dsimp only
                    have h4992_o : ((4992#32 + sc3[(4201#64).toNat]'(by
                        rw [show (4201#64).toNat =
                          4201 from rfl]; exact h4201_3)).setWidth 64).toNat =
                        4992 + (sc3[4201]'h4201_3).toNat := by
                      rw [m6_zext32_toNat, BitVec.toNat_add,
                        show (4992#32 : BitVec 32).toNat = 4992 from rfl,
                        m8_k6_get_congr (show (4201#64).toNat = 4201 from rfl) _ h4201_3,
                        Nat.mod_eq_of_lt (by omega)]
                    have h4992_v : ((4992#32 + v).setWidth 64).toNat = 4992 + v.toNat := by
                      rw [m6_zext32_toNat, BitVec.toNat_add,
                        show (4992#32 : BitVec 32).toNat = 4992 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    have h4736_v : ((4736#32 + v).setWidth 64).toNat = 4736 + v.toNat := by
                      rw [m6_zext32_toNat, BitVec.toNat_add,
                        show (4736#32 : BitVec 32).toNat = 4736 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    rw [List.getElem?_set_ne (by
                        change ((4992#32 + sc3[(4201#64).toNat]'(by
                          rw [show (4201#64).toNat =
                            4201 from rfl]; exact h4201_3)).setWidth 64).toNat ≠ idx
                        rw [h4992_o]; omega),
                      List.getElem?_set_ne (by
                        change ((4992#32 + v).setWidth 64).toNat ≠ idx
                        rw [h4992_v]; omega),
                      List.getElem?_set_ne (by
                        change ((4736#32 + v).setWidth 64).toNat ≠ idx
                        rw [h4736_v]; omega)]
                    exact hk3 idx hi hor, hm⟩
                · have h4200_3_2 : ∀ (x0 x1 : BitVec 32) (i0 i1 : Nat),
                      (4200#64).toNat < ((sc3.set i0 x0).set i1 x1).length := fun _ _ _ _ => by
                    simp only [List.length_set, hl3, show (4200#64).toNat = 4200 from rfl]; omega
                  c0_hsteps!
                  refine hJ4 _ ⟨_, by simp [hl3], fun idx hi hor => by
                    have h4992_v : ((4992#32 + v).setWidth 64).toNat = 4992 + v.toNat := by
                      rw [m6_zext32_toNat, BitVec.toNat_add,
                        show (4992#32 : BitVec 32).toNat = 4992 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    have h4736_v : ((4736#32 + v).setWidth 64).toNat = 4736 + v.toNat := by
                      rw [m6_zext32_toNat, BitVec.toNat_add,
                        show (4736#32 : BitVec 32).toNat = 4736 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    rw [List.getElem?_set_ne (by
                        change (4200#64).toNat ≠ idx
                        rw [show (4200#64).toNat = 4200 from rfl]; omega),
                      List.getElem?_set_ne (by
                        change ((4992#32 + v).setWidth 64).toNat ≠ idx
                        rw [h4992_v]; omega),
                      List.getElem?_set_ne (by
                        change ((4736#32 + v).setWidth 64).toNat ≠ idx
                        rw [h4736_v]; omega)]
                    exact hk3 idx hi hor, hm⟩
            · intro J3 hJ3
              have h4201_2 : 4201 < sc2.length := by rw [hl2]; omega
              c0_hsplit
              · have hnxt : nxt.toNat < nv.toNat := by
                  have h1 : (BitVec.toNat (4992 : BitVec 32) + v.toNat) % 2 ^ 32 = 4992 +
                    v.toNat := by
                    rw [show BitVec.toNat (4992 : BitVec 32) = 4992 from rfl]; omega
                  have h2 : OfNat.ofNat 4192 % 2 ^ 64 = 4192 := by decide
                  simpa only [nxt, h1, h2, nv, scr] using hc
                have hnxt4736 : ((4736#32 + nxt).setWidth 64).toNat < sc2.length := by
                  rw [hl2, m6_zext32_toNat]; c0_bound
                c0_hsteps!
                refine hJ3 _ ⟨_, by simp [hl2], fun idx hi hor => by
                  dsimp only
                  have h4992_eq : ((4992#32 + v).setWidth 64).toNat = 4992 + v.toNat := by
                    rw [m6_zext32_toNat, BitVec.toNat_add,
                      show (4992#32 : BitVec 32).toNat = 4992 from rfl,
                      Nat.mod_eq_of_lt (by omega)]
                  rw [List.getElem?_set_ne (by
                    change ((4736#32 + s.scratch.scratch_buf[((4992#32 +
                      v).setWidth 64).toNat]'hv4992).setWidth 64).toNat ≠ idx
                    rw [m8_k6_get_congr (xs := scr) h4992_eq hv4992 (by omega)]
                    change ((4736#32 + nxt).setWidth 64).toNat ≠ idx
                    rw [m6_zext32_toNat, BitVec.toNat_add,
                      show (4736#32 : BitVec 32).toNat = 4736 from rfl,
                      Nat.mod_eq_of_lt (by omega)]
                    omega)]
                  exact hk2 idx hi hor, hm⟩
              · c0_hsteps!
                refine hJ3 _ ⟨_, by simp [hl2], fun idx hi hor => by
                  rw [List.getElem?_set_ne (by
                    have : (4201#64).toNat = 4201 := rfl
                    rw [this]; omega)]
                  exact hk2 idx hi hor, hm⟩
          · intro J2 hJ2
            c0_hsplit
            · have hpv : pv.toNat < nv.toNat := by
                have h1 : (BitVec.toNat (4736 : BitVec 32) + v.toNat) % 2 ^ 32 = 4736 + v.toNat :=
                  by
                  rw [show BitVec.toNat (4736 : BitVec 32) = 4736 from rfl]; omega
                have h2 : OfNat.ofNat 4192 % 2 ^ 64 = 4192 := by decide
                simpa only [pv, h1, h2, nv, scr] using hc
              have hpv4992 : ((4992#32 + pv).setWidth 64).toNat < scr.length := by
                rw [hscr_l, m6_zext32_toNat]; c0_bound
              c0_hsteps!
              refine hJ2 _ ⟨_, by simp [hscr_len], fun idx hi hor => by
                have h4736_eq : ((4736#32 + v).setWidth 64).toNat = 4736 + v.toNat := by
                  rw [m6_zext32_toNat, BitVec.toNat_add,
                    show (4736#32 : BitVec 32).toNat = 4736 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                rw [List.getElem?_set_ne (by
                  change ((4992#32 + s.scratch.scratch_buf[((4736#32 +
                    v).setWidth 64).toNat]'hv4736).setWidth 64).toNat ≠ idx
                  rw [m8_k6_get_congr (xs := scr) h4736_eq hv4736 (by omega)]
                  change ((4992#32 + pv).setWidth 64).toNat ≠ idx
                  rw [m6_zext32_toNat, BitVec.toNat_add,
                    show (4992#32 : BitVec 32).toNat = 4992 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                  omega)], hm⟩
            · c0_hsteps!
              refine hJ2 _ ⟨_, by simp [hscr_len], fun idx hi hor => by
                rw [List.getElem?_set_ne (by
                  have : (4200#64).toNat = 4200 := rfl
                  rw [this]; omega)], hm⟩
        · c0_hsteps!; exact hJ1 m0 ⟨scr, hscr_len, fun _ _ _ => rfl, hm0⟩

/-- Parametric `Func.wp` proof for `full_k6_backtrack_m8`. -/
theorem full_k6_backtrack_m8_wp (Γ : Env) :
    ∀ a m Q X, m8K6BacktrackSpec a m Q X →
      Func.wp Γ full_k6_backtrack_m8_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hm0, hQ⟩ := m8K6BacktrackSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hsc := c.hscr; unfold dimacsBound at hsc
  let scr := s.scratch.scratch_buf
  have hscr_l : scr.length = c.scratch_cap := hscr_len
  have h4192 := m8_scr_imm_lt hscr_len hsc16 (k := 4192) (by decide)
  have h4200 := m8_scr_imm_lt hscr_len hsc16 (k := 4200) (by decide)
  have h4201 := m8_scr_imm_lt hscr_len hsc16 (k := 4201) (by decide)
  have h4202 := m8_scr_imm_lt hscr_len hsc16 (k := 4202) (by decide)
  have h4203 := m8_scr_imm_lt hscr_len hsc16 (k := 4203) (by decide)
  let nv := scr[4192]'(by rw [hscr_l]; omega)
  have h4195 := m8_scr_imm_lt hscr_len hsc16 (k := 4195) (by decide)
  have h4196 := m8_scr_imm_lt hscr_len hsc16 (k := 4196) (by decide)
  have h4197 := m8_scr_imm_lt hscr_len hsc16 (k := 4197) (by decide)
  have h4198 := m8_scr_imm_lt hscr_len hsc16 (k := 4198) (by decide)
  unfold Func.wp full_k6_backtrack_m8_body
  c0_hsplit
  · c0_hsteps!; exact hQ scr m0 hscr_len (fun _ _ _ => rfl) hm0
  · have hnv : nv.toNat ≤ 256 := Nat.le_of_not_lt (show ¬256 < nv.toNat from by simpa [nv,
      scr] using hc)
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
      (fun te => (te, ())) (fun te => te.toNat ≤ 256)
      ?_ ?_
    · rintro _ te hte
      let keep := fun (kb : List (BitVec 32)) =>
        kb.length = c.scratch_cap ∧
        (∀ idx < c.scratch_cap,
          (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨ (4736 ≤ idx ∧ idx < 6528) ∨ 7040 ≤ idx) →
          kb[idx]? = scr[idx]?)
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i32]) (lpTs := [i32])
        (fun (te_b, ()) mb => ∃ kbb, keep kbb ∧ te_b.toNat ≤ 256 ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := kbb } } ⋆ R) mb)
        (fun rem (te_l, ()) ml => ∃ kbl, keep kbl ∧ te_l.toNat ≤ 256 ∧
          rem = te_l.toNat ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := kbl } } ⋆ R) ml)
        ?_ ?_ ?_
      · rintro _ ⟨te_b, ⟨⟩⟩ mb ⟨kbb, hkb_k, hte_b, hmb⟩
        have hkb_l := hkb_k.1
        have hkbb_4195 : 4195 < kbb.length := by rw [hkb_l]; omega
        have hkbb_4196 : 4196 < kbb.length := by rw [hkb_l]; omega
        have hkbb_4197 : 4197 < kbb.length := by rw [hkb_l]; omega
        c0_hsteps_nogrp
        refine wp_join0 (fun mj => ∃ kbj, keep kbj ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := kbj } } ⋆ R) mj)
          ?_ ?_
        · rintro _ mj ⟨kbj, hkj_k, hmj⟩
          c0_hsteps!; exact hQ _ _ hkj_k.1 hkj_k.2 hmj
        · intro Jp hJp
          c0_hsplit
          · c0_hsteps!
            refine hJp _ ⟨_, ⟨by simp [hkb_l], fun idx hi hor => by
              simp only [show (4195#64).toNat = 4195 from rfl,
                show (4196#64).toNat = 4196 from rfl,
                show (4197#64).toNat = 4197 from rfl]
              repeat rw [List.getElem?_set_ne (by omega)]
              exact hkb_k.2 idx hi hor⟩, hm⟩
          · c0_hsteps!
            refine hJp _ ⟨_, ⟨by simp [hkb_l], fun idx hi hor => by
              simp only [show (4195#64).toNat = 4195 from rfl,
                show (4197#64).toNat = 4197 from rfl]
              repeat rw [List.getElem?_set_ne (by omega)]
              exact hkb_k.2 idx hi hor⟩, hm⟩
      · rintro B L rem ⟨te_l, ⟨⟩⟩ ml hB hL ⟨kbl, hkl_k, hte_l, rfl, hml⟩
        have hkl_l := hkl_k.1
        have hkbl_4192 : 4192 < kbl.length := by rw [hkl_l]; omega
        have hkbl_4198 : 4198 < kbl.length := by rw [hkl_l]; omega
        have hkb_nv : kbl[4192]'hkbl_4192 = nv := by
          have := hkl_k.2 4192 (by omega) (Or.inl (by decide))
          rw [List.getElem?_eq_getElem hkbl_4192,
            List.getElem?_eq_getElem (show 4192 < scr.length from h4192)] at this
          exact Option.some.inj this
        c0_hsplit
        · have hte_pos : 0 < te_l.toNat := by simpa using hc
          clear hc
          have hte1_lt : (te_l - 1#32).toNat < 256 := by
            rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
          have hsub5504 : (5504#32 + te_l - 1#32).toNat = 5503 + te_l.toNat := by
            rw [BitVec.toNat_sub, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
          c0_hsplit
          · c0_hsteps!; exact hB (te_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
          · have hlit_idx : (BitVec.setWidth 64 (5504#32 + te_l - 1#32)).toNat =
                (4294967295 + (5504 + te_l.toNat)) % 4294967296 := by
              rw [BitVec.toNat_setWidth, hsub5504]; omega
            have hlit_len1 : (BitVec.setWidth 64 (5504#32 + te_l - 1#32)).toNat < kbl.length := by
              rw [BitVec.toNat_setWidth, hsub5504]; omega
            have hlit_len2 : (4294967295 + (5504 + te_l.toNat)) % 4294967296 < kbl.length := by
              omega
            let lit := kbl[(BitVec.setWidth 64 (5504#32 + te_l - 1#32)).toNat]'hlit_len1
            have hv_kbl_lt : lit.toNat / 2 < nv.toNat := by
              dsimp only [lit]
              rw [m6_getElem_congr hlit_idx hlit_len1 hlit_len2]
              simpa [nv, scr, Nat.shiftRight_eq_div_pow] using hc
            clear hc
            have hlit512 : lit.toNat < 512 := by have := hv_kbl_lt; have := hnv; omega
            have hv_lt : (lit >>> (1 : Nat)).toNat < 256 := by
              rw [m8_bv32_lshr1_toNat]; omega
            have hv_lt32 : (lit >>> (1#32 : BitVec 32)).toNat < 256 := hv_lt
            have hln_lt : (lit ^^^ 1#32).toNat < 512 := (m8_bv32_xor1_lt (n := 256) lit hlit512).2
            have hv4224_kbl : ((4224#32 + (lit >>> (1#32 : BitVec 32))).setWidth 64).toNat <
              kbl.length := by
              rw [hkl_l, m6_zext32_toNat]; c0_bound
            have hl6528_kbl : ((6528#32 + lit).setWidth 64).toNat < kbl.length := by
              rw [hkl_l, m6_zext32_toNat]; c0_bound
            have hln6528_kbl : ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat <
                (kbl.set ((6528#32 + lit).setWidth 64).toNat 0#32).length := by
              rw [List.length_set, hkl_l, m6_zext32_toNat]; c0_bound
            have hv4224_s2 : ((4224#32 + (lit >>> (1#32 : BitVec 32))).setWidth 64).toNat <
                ((kbl.set ((6528#32 + lit).setWidth 64).toNat 0#32).set
                  ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat 0#32).length := by
              simp only [List.length_set, hkl_l, m6_zext32_toNat]; c0_bound
            have hv4480_s3 : ((4480#32 + (lit >>> (1#32 : BitVec 32))).setWidth 64).toNat <
                (((kbl.set ((6528#32 + lit).setWidth 64).toNat 0#32).set
                  ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat 0#32).set
                  ((4224#32 + (lit >>> (1#32 : BitVec 32))).setWidth 64).toNat 0#32).length := by
              simp only [List.length_set, hkl_l, m6_zext32_toNat]; c0_bound
            have h4198_s4 : (4198#64).toNat <
                ((((kbl.set ((6528#32 + lit).setWidth 64).toNat 0#32).set
                  ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat 0#32).set
                  ((4224#32 + (lit >>> (1#32 : BitVec 32))).setWidth 64).toNat 0#32).set
                  ((4480#32 +
                    (lit >>> (1#32 : BitVec 32))).setWidth 64).toNat 0xFFFFFFFF#32).length := by
              simp only [List.length_set, hkl_l, show (4198#64).toNat = 4198 from rfl]; omega
            c0_hsplit
            · c0_hsteps!; exact hB (te_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
            · have hsub_lt : (te_l - 1#32).toNat < te_l.toNat := by
                rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
              c0_hsteps!
              exact hL (te_l - 1#32).toNat (te_l - 1#32, ()) _ hsub_lt
                ⟨_, ⟨by simp [hkl_l], fun idx hi hor => by
                  have h4198_eq : (4198#64).toNat = 4198 := rfl
                  have h4480_eq : ((4480#32 + (lit >>> (1 : Nat))).setWidth 64).toNat =
                      4480 + (lit >>> (1 : Nat)).toNat := by
                    rw [m6_zext32_toNat, BitVec.toNat_add,
                      show (4480#32 : BitVec 32).toNat = 4480 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have h4224_eq : ((4224#32 + (lit >>> (1 : Nat))).setWidth 64).toNat =
                      4224 + (lit >>> (1 : Nat)).toNat := by
                    rw [m6_zext32_toNat, BitVec.toNat_add,
                      show (4224#32 : BitVec 32).toNat = 4224 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have h6528_n : ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat =
                      6528 + (lit ^^^ 1#32).toNat := by
                    rw [m6_zext32_toNat, BitVec.toNat_add,
                      show (6528#32 : BitVec 32).toNat = 6528 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have h6528_l : ((6528#32 + lit).setWidth 64).toNat = 6528 + lit.toNat := by
                    rw [m6_zext32_toNat, BitVec.toNat_add,
                      show (6528#32 : BitVec 32).toNat = 6528 from rfl, Nat.mod_eq_of_lt (by omega)]
                  rw [List.getElem?_set_ne (by
                        change (4198#64).toNat ≠ idx; rw [h4198_eq]; omega),
                    List.getElem?_set_ne (by
                        change ((4480#32 + (lit >>> (1 : Nat))).setWidth 64).toNat ≠ idx
                        rw [h4480_eq]; omega),
                    List.getElem?_set_ne (by
                        change ((4224#32 + (lit >>> (1 : Nat))).setWidth 64).toNat ≠ idx
                        rw [h4224_eq]; omega),
                    List.getElem?_set_ne (by
                        change ((6528#32 + (lit ^^^ 1#32)).setWidth 64).toNat ≠ idx
                        rw [h6528_n]; omega),
                    List.getElem?_set_ne (by
                        change ((6528#32 + lit).setWidth 64).toNat ≠ idx
                        rw [h6528_l]; omega)]
                  exact hkl_k.2 idx hi hor⟩, by omega, rfl, hm⟩
        · c0_hsteps!; exact hB (te_l, ()) ml ⟨kbl, hkl_k, hte_l, hml⟩
      · intro _ L _ hL; c0_hsteps!
        exact hL te.toNat (te, ()) m0 ⟨scr, ⟨hscr_len, fun _ _ _ => rfl⟩, hte, rfl, hm0⟩
    · intro Jte hJte
      c0_hsplit
      · c0_hsteps!; exact hJte 256#32 (by decide)
      · c0_hsteps!; exact hJte _ (Nat.le_of_not_lt (by simpa using hc))


/-- Parametric `Func.wp` proof for `full_k6_ana_cl_m8`. -/
theorem full_k6_ana_cl_m8_wp (Γ : Env) :
    ∀ a m Q X, m8K6AnaClSpec a m Q X →
      Func.wp Γ full_k6_ana_cl_m8_body a m Q X := by
  rintro ⟨h, cid, skip_v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hok0, hm0, hQ⟩ := m8K6AnaClSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hsc := c.hscr; unfold dimacsBound at hsc
  let scr0 := s.scratch.scratch_buf
  have hscr_l : scr0.length = c.scratch_cap := hscr_len
  have hlen_ge := hok0.base_ge
  have h4192 := m8_scr_imm_lt hscr_len hsc16 (k := 4192) (by decide)
  have h4193 := m8_scr_imm_lt hscr_len hsc16 (k := 4193) (by decide)
  have h4195 := m8_scr_imm_lt hscr_len hsc16 (k := 4195) (by decide)
  have h4207 := m8_scr_imm_lt hscr_len hsc16 (k := 4207) (by decide)
  have h4210 := m8_scr_imm_lt hscr_len hsc16 (k := 4210) (by decide)
  let nc := scr0[4193]'(by rw [hscr_l]; omega)
  let nv := scr0[4192]'(by rw [hscr_l]; omega)
  let acap := scr0[4207]'(by rw [hscr_l]; omega)
  unfold Func.wp full_k6_ana_cl_m8_body
  c0_hsplit
  · c0_hsteps!; exact hQ scr0 m0 hscr_len (fun _ _ _ _ _ _ _ _ => rfl) hm0
  · have hcid : cid.toNat < nc.toNat :=
      Nat.lt_of_not_le (show ¬nc.toNat ≤ cid.toNat from by simpa [nc, scr0] using hc)
    clear hc
    c0_hsplit
    · c0_hsteps!; exact hQ scr0 m0 hscr_len (fun _ _ _ _ _ _ _ _ => rfl) hm0
    · have hnc_le : nc.toNat ≤ 1024 :=
        Nat.le_of_not_lt (show ¬1024 < nc.toNat from by simpa [nc, scr0] using hc)
      clear hc
      c0_hsplit
      · c0_hsteps!; exact hQ scr0 m0 hscr_len (fun _ _ _ _ _ _ _ _ => rfl) hm0
      · have hnv_le : nv.toNat ≤ 256 :=
          Nat.le_of_not_lt (show ¬256 < nv.toNat from by simpa [nv, scr0] using hc)
        clear hc
        have h11648_bd : 11648 + cid.toNat < scr0.length := by rw [hscr_l]; omega
        have h12672_bd : 12672 + cid.toNat < scr0.length := by rw [hscr_l]; omega
        have h11648_idx : (BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat =
            11648 + cid.toNat := by
          rw [m6_zext32_toNat]; c0_bound
        have h12672_idx : (BitVec.setWidth 64 ((12672 : BitVec 32) + cid)).toNat =
            12672 + cid.toNat := by
          rw [m6_zext32_toNat]; c0_bound
        have h11648_c0 : (BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat < scr0.length := by
          rw [h11648_idx]; exact h11648_bd
        have h12672_c0 : (BitVec.setWidth 64 ((12672 : BitVec 32) + cid)).toNat < scr0.length := by
          rw [h12672_idx]; exact h12672_bd
        let off := scr0[11648 + cid.toNat]'h11648_bd
        let cm := scr0[12672 + cid.toNat]'h12672_bd
        let sz := cm &&& 0xFFFF#32
        have hcl_ok := hok0.clause_ok (by
          rw [List.getElem?_eq_getElem (by rw [hscr_l]; omega), Option.getD_some]; exact hcid)
        rw [List.getElem?_eq_getElem h11648_bd, List.getElem?_eq_getElem h12672_bd,
          List.getElem?_eq_getElem (by rw [hscr_l]; omega : 4207 < scr0.length),
          Option.getD_some, Option.getD_some, Option.getD_some] at hcl_ok
        have hoff_sz : off.toNat + sz.toNat ≤ acap.toNat := hcl_ok.1
        have hlt28 := hok0.length_lt
        have hac_le := hok0.length_ge
        rw [List.getElem?_eq_getElem (by rw [hscr_l]; omega : 4207 < scr0.length),
          Option.getD_some] at hac_le
        change 15744 + acap.toNat ≤ scr0.length at hac_le
        have hoff_sz_nw : off.toNat + sz.toNat < 2 ^ 30 := by omega
        c0_hsplit
        · c0_hsteps!; exact hQ scr0 m0 hscr_len (fun _ _ _ _ _ _ _ _ => rfl) hm0
        · clear hc
          let keep := fun (kb : List (BitVec 32)) =>
            kb.length = c.scratch_cap ∧
            (∀ idx < c.scratch_cap, idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
              (idx < 5760 ∨ 6528 ≤ idx) → (idx < 15232 ∨ 15744 ≤ idx) →
              kb[idx]? = scr0[idx]?)
          refine wp_join0 (fun m1 => ∃ kb1, keep kb1 ∧
            (FullMem c { s with scratch := { s.scratch with scratch_buf := kb1 } } ⋆ R) m1) ?_ ?_
          · intro _ m1 ⟨kb1, hk1, hm1⟩
            have hkb1_l := hk1.1
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i32])
              (fun rem (i, ()) mi => ∃ kbi, keep kbi ∧ i.toNat ≤ sz.toNat ∧
                rem = sz.toNat - i.toNat ∧
                (FullMem c { s with scratch := { s.scratch with scratch_buf := kbi } } ⋆ R) mi)
              ?_ ?_
            · rintro L rem ⟨i, ⟨⟩⟩ mi hL ⟨kbi, hki, hi_le, rfl, hmi⟩
              have hki_l := hki.1
              c0_hsplit
              · have hi_lt : i.toNat < sz.toNat := by
                  have h1 : (BitVec.toNat (12672 : BitVec 32) + cid.toNat) % 2 ^ 32 =
                      12672 + cid.toNat := by
                    rw [show BitVec.toNat (12672 : BitVec 32) = 12672 from rfl]; omega
                  have hcm_eq : scr0[(BitVec.toNat (12672 : BitVec 32) + cid.toNat) % 2 ^ 32]'(by
                      rw [h1]; exact h12672_bd) = cm :=
                    m8_k6_get_congr h1 _ h12672_bd
                  rw [hcm_eq] at hc; exact hc
                clear hc
                have har_bd : 15744 + off.toNat + i.toNat < kbi.length := by omega
                have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                have har_c0_idx : (BitVec.setWidth 64 ((15744 : BitVec 32) +
                    scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat]'h11648_c0 +
                    i)).toNat = 15744 + off.toNat + i.toNat := by
                  rw [m8_k6_get_congr h11648_idx h11648_c0 h11648_bd]
                  change ((15744#32 + off + i).setWidth 64).toNat = 15744 + off.toNat + i.toNat
                  rw [m6_zext32_toNat]; c0_bound
                have har_c0_bd : (BitVec.setWidth 64 ((15744 : BitVec 32) +
                    scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat]'h11648_c0 +
                    i)).toNat < kbi.length := by
                  rw [har_c0_idx]; exact har_bd
                dsimp only
                c0_hsteps_nogrp
                refine wp_join0 (fun mj => ∃ kbj, keep kbj ∧
                  (FullMem c { s with scratch := { s.scratch with scratch_buf := kbj } } ⋆ R) mj)
                  ?_ ?_
                · intro _ mj ⟨kbj, hkj, hmj⟩
                  c0_hsteps!
                  exact hL (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj
                    (by omega) ⟨kbj, hkj, by omega, rfl, hmj⟩
                · intro J349 hJ349
                  let l := kbi[15744 + off.toNat + i.toNat]'har_bd
                  let v := l >>> (1 : Nat)
                  have hl_c0_eq : kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                      scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat]'h11648_c0 +
                      i)).toNat]'har_c0_bd = l :=
                    m8_k6_get_congr har_c0_idx har_c0_bd har_bd
                  have h11648_mod : (BitVec.toNat (11648 : BitVec 32) + cid.toNat) % 2 ^ 32 =
                      11648 + cid.toNat := by
                    rw [show BitVec.toNat (11648 : BitVec 32) = 11648 from rfl]; omega
                  have h11648_mbd : (BitVec.toNat (11648 : BitVec 32) + cid.toNat) % 2 ^ 32 <
                      scr0.length := by
                    rw [h11648_mod]; exact h11648_bd
                  have hget1 : scr0[(BitVec.toNat (11648 : BitVec 32) + cid.toNat) %
                      2 ^ 32]'h11648_mbd = off :=
                    m8_k6_get_congr h11648_mod h11648_mbd h11648_bd
                  have h15744_raw : (BitVec.toNat (15744 : BitVec 32) +
                      (scr0[(BitVec.toNat (11648 : BitVec 32) + cid.toNat) %
                        2 ^ 32]'h11648_mbd).toNat + i.toNat) % 2 ^ 32 =
                      15744 + off.toNat + i.toNat := by
                    rw [hget1, show BitVec.toNat (15744 : BitVec 32) = 15744 from rfl]; omega
                  have h15744_mbd : (BitVec.toNat (15744 : BitVec 32) +
                      (scr0[(BitVec.toNat (11648 : BitVec 32) + cid.toNat) %
                        2 ^ 32]'h11648_mbd).toNat + i.toNat) % 2 ^ 32 < kbi.length := by
                    rw [h15744_raw]; exact har_bd
                  have hget2 : kbi[(BitVec.toNat (15744 : BitVec 32) +
                      (scr0[(BitVec.toNat (11648 : BitVec 32) + cid.toNat) %
                        2 ^ 32]'h11648_mbd).toNat + i.toNat) % 2 ^ 32]'h15744_mbd = l :=
                    m8_k6_get_congr h15744_raw h15744_mbd har_bd
                  c0_hsplit
                  · have hv_lt : v.toNat < nv.toNat := by
                      dsimp only [v]; rw [m8_bv32_lshr1_toNat, ← hget2]
                      simpa [nv, scr0] using hc
                    clear hc
                    have hv5760_idx : (BitVec.setWidth 64 ((5760 : BitVec 32) +
                        (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                          scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat]'h11648_c0 +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat = 5760 + v.toNat := by
                      rw [hl_c0_eq]
                      change ((5760#32 + v).setWidth 64).toNat = 5760 + v.toNat
                      rw [m6_zext32_toNat]; c0_bound
                    have hv5760_c0 : (BitVec.setWidth 64 ((5760 : BitVec 32) +
                        (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                          scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat]'h11648_c0 +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hv5760_idx]; omega
                    have hv4224_c0 : (BitVec.setWidth 64 ((4224 : BitVec 32) +
                        (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                          scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat]'h11648_c0 +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hl_c0_eq]
                      change ((4224#32 + v).setWidth 64).toNat < kbi.length
                      rw [m6_zext32_toNat]; c0_bound
                    have hv4480_c0 : (BitVec.setWidth 64 ((4480 : BitVec 32) +
                        (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                          scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) + cid)).toNat]'h11648_c0 +
                          i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kbi.length := by
                      rw [hl_c0_eq]
                      change ((4480#32 + v).setWidth 64).toNat < kbi.length
                      rw [m6_zext32_toNat]; c0_bound
                    dsimp only
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join0 (fun m361 => ∃ kb361, keep kb361 ∧
                          (FullMem c { s with scratch := { s.scratch with scratch_buf :=
                            kb361 } } ⋆ R) m361)
                          ?_ ?_
                        · intro _ m361 ⟨kb361, hk361, hm361⟩
                          have hk361_l := hk361.1
                          have hv4224_361 : (BitVec.setWidth 64 ((4224 : BitVec 32) +
                              (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) +
                                  cid)).toNat]'h11648_c0 +
                                i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kb361.length := by
                            rw [hk361_l, ← hki_l]; exact hv4224_c0
                          have hv4480_361 : (BitVec.setWidth 64 ((4480 : BitVec 32) +
                              (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) +
                                  cid)).toNat]'h11648_c0 +
                                i)).toNat]'har_c0_bd >>> (1 : Nat)))).toNat < kb361.length := by
                            rw [hk361_l, ← hki_l]; exact hv4480_c0
                          have h4209_361 := m8_scr_imm_lt hk361_l hsc16 (k := 4209) (by decide)
                          have h4210_361 := m8_scr_imm_lt hk361_l hsc16 (k := 4210) (by decide)
                          have h4212_361 := m8_scr_imm_lt hk361_l hsc16 (k := 4212) (by decide)
                          c0_hsteps_nogrp
                          refine wp_join0 (fun m361b => ∃ kb361b, keep kb361b ∧
                            (FullMem c { s with scratch := { s.scratch with scratch_buf :=
                              kb361b } } ⋆ R) m361b)
                            ?_ ?_
                          · intro _ m361b ⟨kb361b, hk361b, hm361b⟩
                            c0_hsteps!; exact hJ349 m361b ⟨kb361b, hk361b, hm361b⟩
                          · intro J361b hJ361b
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_join0 (fun m367 => ∃ kb367, keep kb367 ∧
                                (FullMem c { s with scratch := { s.scratch with scratch_buf :=
                                  kb367 } } ⋆ R) m367)
                                ?_ ?_
                              · intro _ m367 ⟨kb367, hk367, hm367⟩
                                c0_hsteps!; exact hJ361b m367 ⟨kb367, hk367, hm367⟩
                              · intro J367 hJ367
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_join0 (fun m367b => ∃ kb367b, keep kb367b ∧
                                    (FullMem c { s with scratch := { s.scratch with scratch_buf :=
                                      kb367b } } ⋆ R) m367b)
                                    ?_ ?_
                                  · intro _ m367b ⟨kb367b, hk367b, hm367b⟩
                                    c0_hsteps!; exact hJ367 m367b ⟨kb367b, hk367b, hm367b⟩
                                  · intro J367b hJ367b
                                    c0_hsplit
                                    · have hnr : (kb361[4210]'(by omega)).toNat < 512 := by
                                        simpa using hc
                                      have h4210_eq : (BitVec.ofNat (OfNat.ofNat 64)
                                          (OfNat.ofNat 4210)).toNat = 4210 := rfl
                                      have h15232_bd : (BitVec.setWidth 64 ((15232 : BitVec 32) +
                                          kb361[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 4210)).toNat]'h4210_361)).toNat =
                                          15232 + (kb361[4210]'(by omega)).toNat := by
                                        rw [m8_k6_get_congr (xs := kb361) h4210_eq _ (by omega),
                                          m6_zext32_toNat]; c0_bound
                                      have h15232_c0 : (BitVec.setWidth 64 ((15232 : BitVec 32) +
                                          kb361[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 4210)).toNat]'h4210_361)).toNat <
                                          kb361.length := by
                                        rw [h15232_bd]; omega
                                      have h4210_361s : (BitVec.ofNat (OfNat.ofNat 64)
                                          (OfNat.ofNat 4210)).toNat <
                                          (kb361.set (BitVec.setWidth 64 ((15232 : BitVec 32) +
                                            kb361[(BitVec.ofNat (OfNat.ofNat 64)
                                              (OfNat.ofNat 4210)).toNat]'h4210_361)).toNat
                                            (kb361[(BitVec.setWidth 64 ((4480 : BitVec 32) +
                                              (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                                scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) +
                                                  cid)).toNat]'h11648_c0 + i)).toNat]'har_c0_bd >>>
                                              (1 : Nat)))).toNat]'hv4480_361)).length := by
                                        rw [List.length_set]; exact h4210_361
                                      dsimp only
                                      c0_hsteps!; dsimp only at hm
                                      refine hJ367b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, List.length_set, hk361_l]
                                      · intro idx hidx h8 h9 h10 h12 ha hb
                                        rw [List.getElem?_set_ne (by change 4210 ≠ idx; omega),
                                          List.getElem?_set_ne (by rw [h15232_bd]; omega)]
                                        exact hk361.2 idx hidx h8 h9 h10 h12 ha hb
                                    · c0_hsteps!; dsimp only at hm
                                      refine hJ367b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, hk361_l]
                                      · intro idx hidx h8 h9 h10 h12 ha hb
                                        rw [List.getElem?_set_ne (by change 4210 ≠ idx; omega)]
                                        exact hk361.2 idx hidx h8 h9 h10 h12 ha hb
                                · c0_hsteps!; exact hJ367 m361 ⟨kb361, hk361, hm361⟩
                            · refine wp_join0 (fun m385 => ∃ kb385, keep kb385 ∧
                                (FullMem c { s with scratch := { s.scratch with scratch_buf :=
                                  kb385 } } ⋆ R) m385)
                                ?_ ?_
                              · intro _ m385 ⟨kb385, hk385, hm385⟩
                                c0_hsteps!; exact hJ361b m385 ⟨kb385, hk385, hm385⟩
                              · intro J385 hJ385
                                c0_hsplit
                                · c0_hsteps!; dsimp only at hm
                                  refine hJ385 m ⟨_, ⟨?_, ?_⟩, hm⟩
                                  · rw [List.length_set, hk361_l]
                                  · intro idx hidx h8 h9 h10 h12 ha hb
                                    rw [List.getElem?_set_ne (by change 4212 ≠ idx; omega)]
                                    exact hk361.2 idx hidx h8 h9 h10 h12 ha hb
                                · c0_hsteps_nogrp
                                  refine wp_join0 (fun m385b => ∃ kb385b, keep kb385b ∧
                                    (FullMem c { s with scratch := { s.scratch with scratch_buf :=
                                      kb385b } } ⋆ R) m385b)
                                    ?_ ?_
                                  · intro _ m385b ⟨kb385b, hk385b, hm385b⟩
                                    c0_hsteps!; exact hJ385 m385b ⟨kb385b, hk385b, hm385b⟩
                                  · intro J385b hJ385b
                                    c0_hsplit
                                    · have hnkl : (kb361[4209]'(by omega)).toNat < 256 := by
                                        simpa using hc
                                      have h4209_eq : (BitVec.ofNat (OfNat.ofNat 64)
                                          (OfNat.ofNat 4209)).toNat = 4209 := rfl
                                      have h6272_bd : (BitVec.setWidth 64 ((6272 : BitVec 32) +
                                          kb361[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 4209)).toNat]'h4209_361)).toNat =
                                          6272 + (kb361[4209]'(by omega)).toNat := by
                                        rw [m8_k6_get_congr (xs := kb361) h4209_eq _ (by omega),
                                          m6_zext32_toNat]; c0_bound
                                      have h6272_c0 : (BitVec.setWidth 64 ((6272 : BitVec 32) +
                                          kb361[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 4209)).toNat]'h4209_361)).toNat <
                                          kb361.length := by
                                        rw [h6272_bd]; omega
                                      have h4209_361s : (BitVec.ofNat (OfNat.ofNat 64)
                                          (OfNat.ofNat 4209)).toNat <
                                          (kb361.set (BitVec.setWidth 64 ((6272 : BitVec 32) +
                                            kb361[(BitVec.ofNat (OfNat.ofNat 64)
                                              (OfNat.ofNat 4209)).toNat]'h4209_361)).toNat
                                            (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                              scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) +
                                                cid)).toNat]'h11648_c0 +
                                                  i)).toNat]'har_c0_bd)).length := by
                                        rw [List.length_set]; exact h4209_361
                                      dsimp only
                                      c0_hsteps!; dsimp only at hm
                                      refine hJ385b m ⟨_, ⟨?_, ?_⟩, hm⟩
                                      · rw [List.length_set, List.length_set, hk361_l]
                                      · intro idx hidx h8 h9 h10 h12 ha hb
                                        rw [List.getElem?_set_ne (by change 4209 ≠ idx; omega),
                                          List.getElem?_set_ne (by rw [h6272_bd]; omega)]
                                        exact hk361.2 idx hidx h8 h9 h10 h12 ha hb
                                    · c0_hsteps!; exact hJ385b m361 ⟨kb361, hk361, hm361⟩
                        · intro J361 hJ361
                          dsimp only at hm
                          have hm1_eq := m8_k6_set_congr (xs := kbi) hv5760_idx
                            (congrArg (· ||| (2 : BitVec 32))
                              (m8_k6_get_congr (xs := kbi) hv5760_idx hv5760_c0 (by omega)))
                          rw [hm1_eq] at hm
                          have hkbi1_ex : ∃ kbi1 : List (BitVec 32), kbi1.length = c.scratch_cap ∧
                              keep kbi1 ∧
                              (FullMem c { s with scratch := { s.scratch with scratch_buf :=
                                kbi1 } } ⋆ R) m :=
                            ⟨kbi.set (5760 + v.toNat) ((kbi[5760 + v.toNat]'(by omega)) ||| 2#32),
                              by simp [hki_l],
                              ⟨by simp [hki_l], fun idx hidx h8 h9 h10 h12 ha hb => by
                                rw [List.getElem?_set_ne (by omega)]
                                exact hki.2 idx hidx h8 h9 h10 h12 ha hb⟩, hm⟩
                          obtain ⟨kbi1, hk1_l, hki1, hm_n⟩ := hkbi1_ex
                          clear hm hm1_eq
                          have hm := hm_n; clear hm_n
                          have h4208_1 := m8_scr_imm_lt hk1_l hsc16 (k := 4208) (by decide)
                          dsimp only
                          c0_hsplit
                          · have hna : (kbi1[4208]'(by omega)).toNat < 256 := by simpa using hc
                            have h4208_eq : (BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 4208)).toNat = 4208 := rfl
                            have h6016_bd : (BitVec.setWidth 64 ((6016 : BitVec 32) +
                                kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                  (OfNat.ofNat 4208)).toNat]'h4208_1)).toNat =
                                6016 + (kbi1[4208]'(by omega)).toNat := by
                              rw [m8_k6_get_congr (xs := kbi1) h4208_eq _ (by omega),
                                m6_zext32_toNat]; c0_bound
                            have h6016_c0 : (BitVec.setWidth 64 ((6016 : BitVec 32) +
                                kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                  (OfNat.ofNat 4208)).toNat]'h4208_1)).toNat < kbi1.length := by
                              rw [h6016_bd]; omega
                            have h4208_1s : (BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 4208)).toNat <
                                (kbi1.set (BitVec.setWidth 64 ((6016 : BitVec 32) +
                                  kbi1[(BitVec.ofNat (OfNat.ofNat 64)
                                    (OfNat.ofNat 4208)).toNat]'h4208_1)).toNat
                                  (kbi[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                    scr0[(BitVec.setWidth 64 ((11648 : BitVec 32) +
                                      cid)).toNat]'h11648_c0 + i)).toNat]'har_c0_bd >>>
                                  (1 : Nat))).length := by
                              rw [List.length_set]; exact h4208_1
                            c0_hsteps!; dsimp only at hm
                            refine hJ361 m ⟨_, ⟨?_, ?_⟩, hm⟩
                            · rw [List.length_set, List.length_set, hk1_l]
                            · intro idx hidx h8 h9 h10 h12 ha hb
                              rw [List.getElem?_set_ne (by change 4208 ≠ idx; omega),
                                List.getElem?_set_ne (by rw [h6016_bd]; omega)]
                              exact hki1.2 idx hidx h8 h9 h10 h12 ha hb
                          · c0_hsteps!; exact hJ361 m ⟨kbi1, hki1, hm⟩
                      · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
                    · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
                  · c0_hsteps!; exact hJ349 mi ⟨kbi, hki, hmi⟩
              · c0_hsteps!; exact hQ kbi mi hki.1 hki.2 hmi
            · intro L hL; c0_hsteps!
              exact hL sz.toNat (0#32, ()) m1 ⟨kb1, hk1, Nat.zero_le _, by simp, hm1⟩
          · intro J343 hJ343
            c0_hsplit
            · have hnr : (scr0[4210]'(by rw [hscr_l]; omega)).toNat < 512 := by
                simpa [scr0] using hc
              have h4210_eq : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4210)).toNat =
                  4210 := rfl
              have h15232_bd : (BitVec.setWidth 64 ((15232 : BitVec 32) +
                  scr0[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4210)).toNat]'h4210)).toNat =
                  15232 + (scr0[4210]'(by rw [hscr_l]; omega)).toNat := by
                rw [m8_k6_get_congr (xs := scr0) h4210_eq _ (by rw [hscr_l]; omega),
                  m6_zext32_toNat]; c0_bound
              have h15232_c0 : (BitVec.setWidth 64 ((15232 : BitVec 32) +
                  scr0[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4210)).toNat]'h4210)).toNat <
                  scr0.length := by
                rw [h15232_bd]; omega
              have h4210_s : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4210)).toNat <
                  (scr0.set (BitVec.setWidth 64 ((15232 : BitVec 32) +
                    scr0[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4210)).toNat]'h4210)).toNat
                      cid).length := by
                rw [List.length_set]; exact h4210
              c0_hsteps!; dsimp only at hm
              refine hJ343 m ⟨_, ⟨?_, ?_⟩, hm⟩
              · rw [List.length_set, List.length_set, hscr_l]
              · intro idx hidx h8 h9 h10 h12 ha hb
                rw [List.getElem?_set_ne (by change 4210 ≠ idx; omega),
                  List.getElem?_set_ne (by rw [h15232_bd]; omega)]
            · c0_hsteps!; dsimp only at hm
              refine hJ343 m ⟨_, ⟨?_, ?_⟩, hm⟩
              · rw [List.length_set, hscr_l]
              · intro idx hidx h8 h9 h10 h12 ha hb
                rw [List.getElem?_set_ne (by change 4210 ≠ idx; omega)]


end LeanQbe.T.Examples.Kissat.FullM8CoreParity
