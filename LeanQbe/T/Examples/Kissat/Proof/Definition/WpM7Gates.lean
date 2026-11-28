/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7DefK6Helpers1
public import LeanQbe.T.Examples.Kissat.Proof.Gates.Spec
public import LeanQbe.T.Examples.Kissat.Src.Definition

/-!
# Kissat M7 Gates Dispatcher WP Proof (`Proof.Definition.WpM7Gates`)

Flat `CanonicalEnv` `Func.wp` proof for `full_bve_gates_m7` (`Spec.fullBveGatesM7Spec`).

`0` legacy `Full*` imports; `0` `@[expose]` on theorems/lemmas/sections; every decl `<= 450` LOC;
every line `<= 100` cols.
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
open LeanQbe.T.Examples.Kissat.Proof.Gates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide |
      ((repeat rw [List.length_set]); omega))

private theorem m7_gates_and_1_eq {v : BitVec 32} :
    ((v <<< 1) &&& 1#32) = 0#32 ∧ (((v <<< 1) ||| 1#32) &&& 1#32) = 1#32 := by
  have hz : (v <<< 1).toNat % 2 = 0 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
      ← Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]
    simp [Nat.mul_mod_right]
  have h1bit : ∀ j : Nat, Nat.testBit 1 (j + 1) = false := fun j => by
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (by have : 2 ≤ 2 ^ (j + 1) := Nat.le_self_pow (by omega) 2; omega : 1 < 2 ^ (j + 1))]
    decide
  have h0 : ((v <<< 1) &&& 1#32).toNat = 0 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, hz]
  have h1 : (((v <<< 1) ||| 1#32) &&& 1#32).toNat = 1 := by
    rw [BitVec.toNat_and, BitVec.toNat_or, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; cases i with
    | zero =>
      rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero]
      simp [show (1 : Nat) % 2 = 1 by decide]
    | succ j => rw [Nat.testBit_and, h1bit j, Bool.and_false]
  exact ⟨BitVec.eq_of_toNat_eq h0, BitVec.eq_of_toNat_eq h1⟩

private theorem m7_gates_and_1_shl9_zero {v : BitVec 32} :
    (((v <<< 1) &&& 1#32) <<< 9).toNat = 0 ∧
      (512#32 - (((v <<< 1) &&& 1#32) <<< 9)).toNat = 512 := by
  have h0 : ((v <<< 1) &&& 1#32) = 0#32 := m7_gates_and_1_eq.1
  rw [h0]; constructor <;> decide

private theorem m7_gates_and_1_shl9_one {v : BitVec 32} :
    ((((v <<< 1) ||| 1#32) &&& 1#32) <<< 9).toNat = 512 ∧
      (512#32 - ((((v <<< 1) ||| 1#32) &&& 1#32) <<< 9)).toNat = 0 := by
  have h1 : (((v <<< 1) ||| 1#32) &&& 1#32) = 1#32 := m7_gates_and_1_eq.2
  rw [h1]; constructor <;> decide

private theorem m7_gates_v_shl1_toNat {cv : Nat} {v : BitVec 32}
    (hcv : cv ≤ 2 ^ 30) (hv : v.toNat < cv) :
    (v <<< 1).toNat = 2 * v.toNat ∧
      ((v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hlt : 2 * v.toNat + 1 < 2 ^ 32 := by omega
  have h0 : (v <<< 1).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨h0, ?_⟩
  rw [BitVec.toNat_or, h0, show (1#32 : BitVec 32).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro i; cases i with
  | zero => simp [Nat.testBit_zero, show (2 * v.toNat + 1) % 2 = 1 by omega]
  | succ j =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      Nat.mul_add_div (by omega : 0 < 2), Nat.mul_div_right _ (by omega)]
    simp

private theorem m7_gates_entry_of_core_eq {F_cur : List (List Nat)} {s1 s2 : FullState}
    {lit : Nat} {w : BitVec 32}
    (hcv : s1.core.cur_vars = s2.core.cur_vars)
    (har : s1.core.arena = s2.core.arena)
    (hal : s1.core.arena_len = s2.core.arena_len) :
    FullBveEntryOkW F_cur s1 lit w → FullBveEntryOkW F_cur s2 lit w := by
  unfold FullBveEntryOkW fullArenaClauseRefs fullArenaClauseGarb
    fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaHdrCore
  rw [hcv, har, hal]; exact id

private theorem m7_gates_inv_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    (s0 : FullState) {np nn : BitVec 32} {R : Mem 64 → Prop}
    {s : FullState} {m : Mem 64}
    (hinv' : FullDenseInvW c F0 F_cur s)
    (htmk' : Spec.TmkZero s)
    (hcv : s.core.cur_vars = s0.core.cur_vars)
    (har : s.core.arena = s0.core.arena)
    (harl : s.core.arena_len = s0.core.arena_len)
    (hfl : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hpres : ∀ k < 1024, s.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]?)
    (hm : (FullMem c s ⋆ R) m)
    (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    {Q : Post []}
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → Spec.TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s0.scratch.scratch_buf[512 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    Q () m :=
  hQ s m hinv' htmk' hcv har harl hfl
    (fun i hi => hpres i (by omega))
    (fun j hj => hpres (512 + j) (by omega))
    hm

public section

/-- Certifies `fullBveGatesM7Spec` for `full_bve_gates_m7`. -/
theorem full_bve_gates_m7_wp (Γ : Env)
    (h_eq : Γ.Has "full_bve_find_equiv_m7" fullBveFindEquivM7Spec)
    (h_and : Γ.Has "full_bve_find_and_m7" fullBveFindAndM7Spec)
    (h_ite : Γ.Has "full_bve_find_ite_m7" fullBveFindIteM7Spec)
    (h_xor : Γ.Has "full_bve_find_xor_m7" fullBveFindXorM7Spec)
    (h_k6 : Γ.Has "full_bve_def_k6_m7" fullBveGatesM7Spec) :
    ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Func.wp Γ full_bve_gates_m7_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  rcases hSpec with ⟨c, F0, F_cur, s0, R, rfl, hinv, htmk0, hcap, hv, hnp, hnn,
    hpos, hneg, hm0, hQ⟩
  unfold Func.wp full_bve_gates_m7_body
  have hscr_len0 : s0.scratch.scratch_buf.length = c.scratch_cap :=
    hinv.1.scratch_ok.scratch_buf_len
  have hscr_lt : c.scratch_cap < 2 ^ 28 := c.hscr
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun p m => ∃ scr : List (BitVec 32), p.fst.toNat ≤ 34 ∧ scr.length = c.scratch_cap ∧
      (∀ k < 1024, scr[k]? = s0.scratch.scratch_buf[k]?) ∧
      (FullMem c { core := s0.core, scratch := { s0.scratch with scratch_buf := scr } } ⋆ R) m)
    (fun p _ => 34 - p.fst.toNat) ?_ ?_
  · intro J hJ; c0_hsteps!
    exact hJ (0#32, ()) m0 ⟨s0.scratch.scratch_buf, Nat.zero_le _, hscr_len0, fun _ _ => rfl, hm0⟩
  · intro J ⟨i, ⟨⟩⟩ m ⟨scr, hi_le, hscr_len, hpres, hm⟩ hrec
    c0_hsplit
    · have hi : i.toNat < 34 := by c0_bound
      have hidx_lt : (1024 + i.toNat) < scr.length := by omega
      have hidx_bv : (BitVec.setWidth 64 ((1024 : BitVec 32) + i)).toNat = 1024 + i.toNat := by
        bv_omega
      c0_hsteps!
      refine hrec (i + 1, ()) _ (by bv_omega)
        ⟨scr.set (1024 + i.toNat) 0#32, by bv_omega, by rw [List.length_set, hscr_len],
          fun k hk => by rw [List.getElem?_set_ne (by c0_bound)]; exact hpres k hk,
          m7_p6_fullMem_subst hm rfl (by dsimp only; rw [hidx_bv]; rfl)⟩
    · let s1 : FullState :=
        { core := s0.core, scratch := { s0.scratch with scratch_buf := scr } }
      have hinv1 : FullDenseInvW c F0 F_cur s1 :=
        m7_p6_fullDenseInvW_def hinv hinv.1.core_ok.tmp_len_arr
          hinv.1.scratch_ok.wsort_len hinv.1.scratch_ok.tarjan_mark_len hscr_len
      have hpos1 : ∀ j < np.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat)
          (s1.scratch.scratch_buf[j]?.getD 0#32) := by
        intro j hj; simp only [s1, hpres j (by omega)]
        exact m7_gates_entry_of_core_eq rfl rfl rfl (hpos j hj)
      have hneg1 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat + 1)
          (s1.scratch.scratch_buf[512 + j]?.getD 0#32) := by
        intro j hj; simp only [s1, hpres (512 + j) (by omega)]
        exact m7_gates_entry_of_core_eq rfl rfl rfl (hneg j hj)
      have hbin1 : ∀ k < np.toNat,
          have w := s1.scratch.scratch_buf[k]?.getD 0#32
          w &&& 0x80000000#32 ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s1.core.cur_vars :=
        fun k hk hbit => m7_p6_entry_bin_bounds (hpos1 k hk) hbit
      have hbin2 : ∀ k < nn.toNat,
          have w := s1.scratch.scratch_buf[512 + k]?.getD 0#32
          w &&& 0x80000000#32 ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s1.core.cur_vars :=
        fun k hk hbit => m7_p6_entry_bin_bounds (hneg1 k hk) hbit
      c0_hsplit
      · c0_hsteps!
        exact m7_gates_inv_exit s0 hinv1 htmk0 rfl rfl rfl (Nat.le_refl _) hpres hm hnp hnn hQ
      · c0_hsplit
        · c0_hsteps!
          exact m7_gates_inv_exit s0 hinv1 htmk0 rfl rfl rfl (Nat.le_refl _) hpres hm hnp hnn hQ
        · apply wp_call_of_spec; apply h_eq
          refine fullBveFindEquivM7Spec_intro rfl hinv1 hcap hnp hnn hbin1 hbin2 hm ?_
          intro ok1 lm1 scr1 m1 s_e hinv_e hlen1 hpres1 hm1
          have hpres_e : ∀ k < 1024, s_e.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
            fun k hk => (hpres1 k (by omega) (Or.inl hk)).trans (hpres k hk)
          have hpos_e : ∀ j < np.toNat, FullBveEntryOkW F_cur s_e (2 * v.toNat)
              (s_e.scratch.scratch_buf[j]?.getD 0#32) := by
            intro j hj; simp only [s_e, hpres1 j (by omega) (Or.inl (by omega))]
            exact m7_gates_entry_of_core_eq rfl rfl rfl (hpos1 j hj)
          have hneg_e : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_e (2 * v.toNat + 1)
              (s_e.scratch.scratch_buf[512 + j]?.getD 0#32) := by
            intro j hj; simp only [s_e, hpres1 (512 + j) (by omega) (Or.inl (by omega))]
            exact m7_gates_entry_of_core_eq rfl rfl rfl (hneg1 j hj)
          c0_hsplit
          · c0_hsteps!
            exact m7_gates_inv_exit s0 hinv_e htmk0 rfl rfl rfl (Nat.le_refl _)
              hpres_e hm1 hnp hnn hQ
          · have hl_eq := m7_gates_v_shl1_toNat (cv := s_e.core.cur_vars)
              (by have := hinv_e.1.core_ok.cur_vars_le; have := c.hmaxv
                  rw [show dimacsBound = 2 ^ 28 from rfl] at *; omega)
              hv
            c0_hsteps_nogrp
            apply wp_call_of_spec; apply h_and
            dsimp only [vals, Arg.val]
            rw [show (OfNat.ofNat 1 : Nat) = 1 from rfl, show (1 : BitVec 32) = 1#32 from rfl]
            refine fullBveFindAndM7Spec_intro rfl hinv_e (by omega)
              (show (v <<< 1).toNat < 2 * s_e.core.cur_vars by
                rw [hl_eq.1]; exact Nat.mul_lt_mul_of_pos_left hv (by omega))
              hnp hnn
              (fun j hj => by
                rw [m7_gates_and_1_shl9_zero.1, Nat.zero_add, hl_eq.1]; exact hpos_e j hj)
              (fun j hj => by
                rw [m7_gates_and_1_shl9_zero.2, hl_eq.1, m7_p6_xor_two_mul]
                exact hneg_e j hj)
              hm1 ?_
            intro ok2 lm2 scr2 m2 s_a1 hinv_a1 hlen2 hpres2 hm2
            have hpres_a1 : ∀ k < 1024, s_a1.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
              fun k hk => (hpres2 k (by omega) (Or.inl hk)).trans (hpres_e k hk)
            have hpos_a1 : ∀ j < np.toNat, FullBveEntryOkW F_cur s_a1 (2 * v.toNat)
                (s_a1.scratch.scratch_buf[j]?.getD 0#32) := by
              intro j hj; simp only [s_a1, hpres2 j (by omega) (Or.inl (by omega))]
              exact m7_gates_entry_of_core_eq rfl rfl rfl (hpos_e j hj)
            have hneg_a1 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_a1 (2 * v.toNat + 1)
                (s_a1.scratch.scratch_buf[512 + j]?.getD 0#32) := by
              intro j hj; simp only [s_a1, hpres2 (512 + j) (by omega) (Or.inl (by omega))]
              exact m7_gates_entry_of_core_eq rfl rfl rfl (hneg_e j hj)
            c0_hsplit
            · c0_hsteps!
              exact m7_gates_inv_exit s0 hinv_a1 htmk0 rfl rfl rfl (Nat.le_refl _)
                hpres_a1 hm2 hnp hnn hQ
            · apply wp_call_of_spec; apply h_and
              dsimp only [vals, Arg.val]
              refine fullBveFindAndM7Spec_intro rfl hinv_a1 (by omega)
                (show ((v <<< 1) ||| 1#32).toNat < 2 * s_a1.core.cur_vars by
                  rw [hl_eq.2]; exact by have : v.toNat < s_a1.core.cur_vars := hv; omega)
                hnn hnp
                (fun j hj => by rw [m7_gates_and_1_shl9_one.1, hl_eq.2]; exact hneg_a1 j hj)
                (fun j hj => by
                  rw [m7_gates_and_1_shl9_one.2, Nat.zero_add, hl_eq.2, m7_p6_xor_two_mul_add1]
                  exact hpos_a1 j hj)
                hm2 ?_
              intro ok3 lm3 scr3 m3 s_a2 hinv_a2 hlen3 hpres3 hm3
              have hpres_a2 : ∀ k < 1024,
                  s_a2.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
                fun k hk => (hpres3 k (by omega) (Or.inl hk)).trans (hpres_a1 k hk)
              have hpos_a2 : ∀ j < np.toNat, FullBveEntryOkW F_cur s_a2 (2 * v.toNat)
                  (s_a2.scratch.scratch_buf[j]?.getD 0#32) := by
                intro j hj; simp only [s_a2, hpres3 j (by omega) (Or.inl (by omega))]
                exact m7_gates_entry_of_core_eq rfl rfl rfl (hpos_a1 j hj)
              have hneg_a2 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_a2 (2 * v.toNat + 1)
                  (s_a2.scratch.scratch_buf[512 + j]?.getD 0#32) := by
                intro j hj; simp only [s_a2, hpres3 (512 + j) (by omega) (Or.inl (by omega))]
                exact m7_gates_entry_of_core_eq rfl rfl rfl (hneg_a1 j hj)
              c0_hsplit
              · c0_hsteps!
                exact m7_gates_inv_exit s0 hinv_a2 htmk0 rfl rfl rfl (Nat.le_refl _)
                  hpres_a2 hm3 hnp hnn hQ
              · apply wp_call_of_spec; apply h_ite
                refine fullBveFindIteM7Spec_intro rfl hinv_a2 (by omega) hv hnp hnn
                  hpos_a2 hneg_a2 hm3 ?_
                intro ok4 scr4 m4 s_i hlen4 hpres4 hm4
                have hinv_i : FullDenseInvW c F0 F_cur s_i :=
                  m7_p6_fullDenseInvW_def hinv_a2 hinv_a2.1.core_ok.tmp_len_arr
                    hinv_a2.1.scratch_ok.wsort_len hinv_a2.1.scratch_ok.tarjan_mark_len hlen4
                have hpres_i : ∀ k < 1024,
                    s_i.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
                  fun k hk => (hpres4 k (by omega) (Or.inl hk)).trans (hpres_a2 k hk)
                have hpos_i : ∀ j < np.toNat, FullBveEntryOkW F_cur s_i (2 * v.toNat)
                    (s_i.scratch.scratch_buf[j]?.getD 0#32) := by
                  intro j hj; simp only [s_i, hpres4 j (by omega) (Or.inl (by omega))]
                  exact m7_gates_entry_of_core_eq rfl rfl rfl (hpos_a2 j hj)
                have hneg_i : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_i (2 * v.toNat + 1)
                    (s_i.scratch.scratch_buf[512 + j]?.getD 0#32) := by
                  intro j hj; simp only [s_i, hpres4 (512 + j) (by omega) (Or.inl (by omega))]
                  exact m7_gates_entry_of_core_eq rfl rfl rfl (hneg_a2 j hj)
                c0_hsplit
                · c0_hsteps!
                  exact m7_gates_inv_exit s0 hinv_i htmk0 rfl rfl rfl (Nat.le_refl _)
                    hpres_i hm4 hnp hnn hQ
                · apply wp_call_of_spec; apply h_xor
                  refine fullBveFindXorM7Spec_intro rfl hinv_i hcap hv hnp hnn
                    hpos_i hneg_i hm4 ?_
                  intro ok5 lm5 scr5 m5 s_x hinv_x hlen5 hpres5 hm5
                  have hpres_x : ∀ k < 1024,
                      s_x.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
                    fun k hk => (hpres5 k (by omega) (Or.inl hk)).trans (hpres_i k hk)
                  have hpos_x : ∀ j < np.toNat, FullBveEntryOkW F_cur s_x (2 * v.toNat)
                      (s_x.scratch.scratch_buf[j]?.getD 0#32) := by
                    intro j hj; simp only [s_x, hpres5 j (by omega) (Or.inl (by omega))]
                    exact m7_gates_entry_of_core_eq rfl rfl rfl (hpos_i j hj)
                  have hneg_x : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_x (2 * v.toNat + 1)
                      (s_x.scratch.scratch_buf[512 + j]?.getD 0#32) := by
                    intro j hj; simp only [s_x, hpres5 (512 + j) (by omega) (Or.inl (by omega))]
                    exact m7_gates_entry_of_core_eq rfl rfl rfl (hneg_i j hj)
                  c0_hsplit
                  · c0_hsteps!
                    exact m7_gates_inv_exit s0 hinv_x htmk0 rfl rfl rfl (Nat.le_refl _)
                      hpres_x hm5 hnp hnn hQ
                  · apply wp_call_of_spec; apply h_k6
                    refine ⟨c, F0, F_cur, s_x, R, rfl, hinv_x, htmk0, hcap, hv, hnp, hnn,
                      hpos_x, hneg_x, hm5, ?_⟩
                    intro s' m' hinv' htmk' hcv' har' harl' hfl' hsp hsn hm'
                    c0_hsteps!
                    exact hQ s' m' hinv' htmk' hcv' har' harl' hfl'
                      (fun i hi => (hsp i hi).trans (hpres_x i (by omega)))
                      (fun j hj => (hsn j hj).trans (hpres_x (512 + j) (by omega)))
                      hm'

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
