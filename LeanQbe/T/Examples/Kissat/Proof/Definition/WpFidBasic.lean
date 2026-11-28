/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.Inv

/-!
# Kissat Fidelity BVE WP Proofs — Leaf & Dynamic K6 Primitives (`Proof.Definition.WpFidBasic`)

`CanonicalEnv`-clean `Func.wp` proofs (`0` legacy `Full*` imports; zero `@[expose]` on theorems;
every decl `<= 450` LOC; `<= 100` cols):
1. `full_bve_k6_mv_fid_wp` (`fidBveK6MvSpec`).
2. `full_fid_k6_add_ticks_wp` (`fidK6AddTicksSpec`).
3. `full_k6_watch_fid_wp` (`fidK6WatchSpec`).
4. `full_k6_assign_fid_wp` (`fidK6AssignSpec`).
5. `full_k6_mtf_fid_wp` (`fidK6MtfSpec`).
6. `full_k6_backtrack_fid_wp` (`fidK6BacktrackSpec`).
7. `full_k6_ana_cl_fid_wp` (`fidK6AnaClSpec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FidK6Tactics M8K6bTactics

public section

namespace FidK6DefTactics

@[scoped bv_c0] theorem fid_bv32_mul_toNat (a b : BitVec 32) :
    (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 32 :=
  BitVec.toNat_mul a b

@[scoped bv_c0] theorem fid_bv32_zext64_toNat (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat :=
  m6_zext32_toNat x

end FidK6DefTactics

open scoped FidK6DefTactics

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide | omega | fid_omega)

/-! ## 1. Shared Pure Arithmetic & Clause-Meta Helpers -/

theorem fid_list_set_idx_eq {α : Type _} (xs : List α) {i j : Nat} (h : i = j) (v : α) :
    xs.set i v = xs.set j v :=
  h ▸ rfl

theorem fid_bv32_and_ffff_toNat (x : BitVec 32) :
    (x &&& 0xFFFF#32).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and]
  rw [show (0xFFFF#32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem fid_sub1_mod32 (a x : Nat) (hx : 0 < x)
    (hlt : a + (x - 1) < 4294967296) :
    (a + (4294967296 - 1 + x)) % 4294967296 = a + (x - 1) := by
  rw [show a + (4294967296 - 1 + x) = (a + (x - 1)) + 4294967296 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

theorem m8_km_core_clear_pres (x : BitVec 32) :
    ((x &&& ~~~0x80000000#32) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) ∧
    ((x &&& ~~~0x80000000#32) &&& 0x40000000#32) = (x &&& 0x40000000#32) :=
  ⟨(m8_bv32_bit_disj x 0x80000000#32 0xFFFF#32 (by decide)).2,
   (m8_bv32_bit_disj x 0x80000000#32 0x40000000#32 (by decide)).2⟩

theorem m8_km_core_or_pres (x : BitVec 32) :
    ((x ||| 0x80000000#32) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) ∧
    ((x ||| 0x80000000#32) &&& 0x40000000#32) = (x &&& 0x40000000#32) :=
  ⟨(m8_bv32_bit_disj x 0x80000000#32 0xFFFF#32 (by decide)).1,
   (m8_bv32_bit_disj x 0x80000000#32 0x40000000#32 (by decide)).1⟩

theorem m8_and_ffff_le (cm : BitVec 32) : (cm &&& 0xFFFF#32).toNat ≤ 65535 := by
  rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem m8k6_slot_xor1_lt {w : BitVec 32} :
    ((w &&& 1#32) ^^^ 1#32).toNat < 2 := by
  have hlt : (w &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    have := Nat.and_le_right (n := w.toNat) (m := 1); omega
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h0 | h1
  · have h : (w &&& 1#32) = 0#32 :=
      BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)
    rw [h]; decide
  · have h : (w &&& 1#32) = 1#32 := BitVec.eq_of_toNat_eq h1
    rw [h]; decide

/-! ## 2. `full_bve_k6_mv_fid_wp` & `full_fid_k6_add_ticks_wp` -/

/-- Exact `Func.wp` proof for `full_bve_k6_mv_fid`, certifying `fidBveK6MvSpec`. -/
theorem full_bve_k6_mv_fid_wp (Γ : Env) :
    ∀ a m Q X, fidBveK6MvSpec a m Q X → Func.wp Γ full_bve_k6_mv_fid_body a m Q X := by
  rintro ⟨cap, ⟨⟩⟩ m Q X hQ
  unfold fidBveK6MvSpec at hQ
  have heq := fidK6MaxV_bv64_eq (cap := cap.toNat) cap.isLt
  have hcap : BitVec.ofNat 64 cap.toNat = cap := BitVec.eq_of_toNat_eq (by simp)
  dsimp at heq; rw [hcap] at heq
  unfold Func.wp full_bve_k6_mv_fid_body
  c0_hsplit
  · c0_hsteps!
    have hlt : cap < 16384#64 := hc
    simp only [hlt, ↓reduceIte] at heq
    simpa [← heq] using hQ
  · have hge1 : ¬ cap < 16384#64 := by intro h; exact hc h
    c0_hsplit
    · c0_hsteps!
      have hge512 : 524288#64 ≤ cap := by
        change (524288#64).toNat ≤ cap.toNat
        change (524288#64).toNat ≤ cap.toNat at hc; exact hc
      simp only [hge1, hge512, ↓reduceIte] at heq
      simpa [← heq] using hQ
    · have hlt512 : ¬ 524288#64 ≤ cap := by
        intro h; exact hc h
      c0_hsplit
      · c0_hsteps!
        have hr1 : ((cap - 4224#64) / 64#64 &&& 0xFFFFFFFFFFFFFFC0#64) < 256#64 := hc
        simp only [hge1, hlt512, hr1, ↓reduceIte] at heq
        simpa [← heq] using hQ
      · have hr1 : ¬ ((cap - 4224#64) / 64#64 &&& 0xFFFFFFFFFFFFFFC0#64) < 256#64 := by
          intro h; exact hc h
        c0_hsplit
        · c0_hsteps!
          have hr2 : 8192#64 < ((cap - 4224#64) / 64#64 &&& 0xFFFFFFFFFFFFFFC0#64) := hc
          simp only [hge1, hlt512, hr1, hr2, ↓reduceIte] at heq
          simpa [← heq] using hQ
        · c0_hsteps!
          have hr2 : ¬ 8192#64 < ((cap - 4224#64) / 64#64 &&& 0xFFFFFFFFFFFFFFC0#64) := by
            intro h; exact hc h
          simp only [hge1, hlt512, hr1, hr2, ↓reduceIte] at heq
          simpa [← heq] using hQ

/-- Parametric `Func.wp` proof for `full_fid_k6_add_ticks`, certifying `fidK6AddTicksSpec`. -/
theorem full_fid_k6_add_ticks_wp (Γ : Env) :
    ∀ a m Q X, fidK6AddTicksSpec a m Q X → Func.wp Γ full_fid_k6_add_ticks_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hm0, hQ⟩ := fidK6AddTicksSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have h4204 : 4204 < s.scratch.scratch_buf.length := by omega
  unfold Func.wp full_fid_k6_add_ticks_body
  have hm0' : (FullMem c (m8ScrSt s s.scratch.scratch_buf) ⋆ R) m0 := by
    rwa [m8ScrSt_self]
  have h15744 : 15744 ≤ s.scratch.scratch_buf.length := by omega
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun tk => (tk, ())) (fun _ => True)
    (fun _ tk _ => by
      c0_hsteps!
      rw [m8ScrSt_eq] at hm
      exact hQ tk _ hm)
    (fun Jt hJt => by
      c0_hsplit
      · c0_hsteps!; exact hJt 0xFFFFFFFF#32 trivial
      · c0_hsteps!; exact hJt _ trivial)

/-! ## 3. `full_k6_watch_fid_wp` -/

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

/-! ## 4. `full_k6_assign_fid_wp` -/

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

/-! ## 5. `full_k6_mtf_fid_wp` -/

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

/-! ## 6. `full_k6_backtrack_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_backtrack_fid`, certifying `fidK6BacktrackSpec`. -/
theorem full_k6_backtrack_fid_wp (Γ : Env) :
    ∀ a m Q X, fidK6BacktrackSpec a m Q X →
      Func.wp Γ full_k6_backtrack_fid_body a m Q X := by
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

/-! ## 7. `full_k6_ana_cl_fid_wp` -/

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
            have hcl_ok := hok.clause_ok (cid := cid.toNat)
              (by rw [m8_k6_get_eq h4193]; exact hcid)
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
                            have h2 : scrl[(4224 + 45 * (scr0[4214]'h4214).toNat +
                                (scr0[4224 + 29 * (scr0[4214]'h4214).toNat + cid.toNat]'(by
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

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
