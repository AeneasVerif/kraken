/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
public import LeanQbe.T.Examples.Kissat.Src.Extend
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Model Extension & Unpermutation WP Proofs for `Kissat.Src.Extend`

Proves `Func.wp Γ ...` against `CanonicalEnv` specs for:
- `full_extend_core_fid` (`full_extend_core_fid_wp`)
- `full_unperm_fid` (`full_unperm_fid_wp`)
- `full_extend` (`full_extend_wp`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Extend

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Extend
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

private theorem bv_zext_toNat {w1 w2 : Nat} (x : BitVec w1) (hle : w1 ≤ w2) :
    (x.setWidth w2).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hle))]

private theorem nat_bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

private theorem bv64_shl1_nat_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 63) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

private theorem bv64_shl1_or1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 63) :
    ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
  have hs : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_nat_toNat hv
  rw [BitVec.toNat_or, hs, show (1#64 : BitVec 64).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    simp [Nat.testBit_succ, show (2 * v.toNat + 1) / 2 = v.toNat by omega,
      show (2 * v.toNat) / 2 = v.toNat by omega]

private theorem bv32_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat / 2 < n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  have h1 : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl
  rw [h1]; exact litNeg_lt_two_mul (by omega)

private theorem bv32_and_mask_lt {x : BitVec 32} :
    (x &&& 0x7FFFFFFF#32).toNat < 2 ^ 31 := by
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

private theorem extendSlice_set_vals {c : FullCfg} {s : FullState}
    (i : Nat) (v : BitVec 8) :
    PreservesCoreSlice (fullExtendSlice c).coreProj s
      { s with core := { s.core with vals := s.core.vals.set i v } } :=
  rfl

private theorem extendSlice_set_vals_len {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (i : Nat) (v : BitVec 8) :
    ({ s with core := { s.core with vals := s.core.vals.set i v } } : FullState).LengthsOk c :=
  ⟨{ hlen.core_ok with vals_len := by simp [hlen.core_ok.vals_len] }, hlen.scratch_ok⟩

public section

theorem full_extend_core_fid_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullExtendCoreFidSpec a m Q X →
      Func.wp Γ full_extend_core_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain hext : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at hmax hext
  obtain hvl := hlen.core_ok.vals_len
  obtain hfll := hlen.core_ok.flags_len
  obtain hesl := hlen.scratch_ok.extend_stk_len
  unfold Func.wp full_extend_core_fid_body
  c0_hsteps_nogrp
  refine wp_while_state
    (fun (p : BitVec 64 × FullState) => (p.1, ()))
    (fun p => c.max_vars - p.1.toNat)
    (fun p ml =>
      p.1.toNat ≤ c.max_vars ∧ PreservesCoreSlice (fullExtendSlice c).coreProj s p.2 ∧
      p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) ml)
    (fun J hJ => by c0_hsteps; exact hJ (0#64, s) m ⟨Nat.zero_le _, rfl, hlen, hm⟩)
    (fun J ⟨v, s1⟩ m1 ⟨hvle, hcore1, hs1, hm1⟩ ih1 => ?_)
  dsimp only at hvle hcore1 hs1 hm1 ih1 ⊢
  c0_hsplit
  · have hv_lt : v.toNat < c.max_vars := by
      have h1 : v.toNat < c.max_vars % 2 ^ 64 := by assumption
      omega
    have hv1 : (v + 1#64).toNat = v.toNat + 1 := by simp only [bv_c0]; omega
    have hfl_v : v.toNat < s1.core.flags.length := by
      rw [hs1.core_ok.flags_len]; exact hv_lt
    have hv_shl : (v <<< (1 : Nat)).toNat < s1.core.vals.length := by
      rw [hs1.core_ok.vals_len, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
    c0_hsteps_nogrp
    refine wp_join_state0 (α := FullState)
      (fun s2 m2 => PreservesCoreSlice (fullExtendSlice c).coreProj s1 s2 ∧ s2.LengthsOk c ∧
        (FullMem c s2 ⋆ R) m2)
      (fun J2 s2 m2 ⟨hcore2, hs2, hm2⟩ => by
        c0_hsteps
        exact ih1 (v + 1#64, s2) m2 (by dsimp only; rw [hv1]; omega)
          ⟨by rw [hv1]; omega, hcore1.trans hcore2, hs2, hm2⟩)
      (fun J2 hJ2 => by
        have hvl1 := hs1.core_ok.vals_len
        have hv_or : ((v <<< (1 : Nat)) ||| 1#64).toNat <
            (s1.core.vals.set (v <<< (1 : Nat)).toNat 1#8).length := by
          rw [List.length_set, hvl1, bv64_shl1_or1_toNat (by omega)]; omega
        c0_hsteps
        · exact hJ2 { s1 with core := { s1.core with vals :=
            ((s1.core.vals.set (v <<< (1 : Nat)).toNat 1#8).set
              ((v <<< (1 : Nat)) ||| 1#64).toNat (BitVec.setWidth 8 (-1))) } } _
            ⟨rfl, ⟨{ hs1.core_ok with vals_len := by simp [hvl1] }, hs1.scratch_ok⟩, hm⟩
        · exact hJ2 { s1 with core := { s1.core with vals :=
            ((s1.core.vals.set (v <<< (1 : Nat)).toNat 1#8).set
              ((v <<< (1 : Nat)) ||| 1#64).toNat (BitVec.setWidth 8 (-1))) } } _
            ⟨rfl, ⟨{ hs1.core_ok with vals_len := by simp [hvl1] }, hs1.scratch_ok⟩, hm⟩
        · exact hJ2 s1 m1 ⟨rfl, hs1, hm1⟩)
  · clear hm hlen
    obtain ⟨hsc1, _, _, _, _, _⟩ := fullExtend_preserves_nonVals hcore1
    c0_hsteps
    refine wp_while_state
      (fun (p : BitVec 64 × FullState) => (p.1, ()))
      (fun p => p.1.toNat)
      (fun p ml =>
        p.1.toNat ≤ c.extend_cap ∧ PreservesCoreSlice (fullExtendSlice c).coreProj s p.2 ∧
        p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) ml)
      (fun Je hJe => by
        c0_hsteps
        exact hJe (BitVec.ofNat 64 s1.scratch.extend_len, s1) m1
          ⟨by rw [hsc1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hel,
           hcore1, hs1, hm1⟩)
      (fun Je ⟨end_v, s2⟩ m2 ⟨hend_le, hcore2, hs2, hm2⟩ ihe => ?_)
    dsimp only at hend_le hcore2 hs2 hm2 ihe ⊢
    c0_hsplit
    · have hend_pos : 0 < end_v.toNat := by c0_bound
      have hesl2 : s2.scratch.extend_stk.length = c.extend_cap := hs2.scratch_ok.extend_stk_len
      c0_hsteps_nogrp
      refine wp_while_break_state (α := BitVec 64) (β := BitVec 64)
        (fun sv => (sv, ()))
        (fun sv ml => sv.toNat < end_v.toNat ∧ ml = m2)
        (fun sv => (sv, ()))
        BitVec.toNat
        (fun sv ml => sv.toNat ≤ end_v.toNat ∧ ml = m2)
        (fun B start_v mb ⟨hstart_lt, hm_eq⟩ => ?_)
        (fun B L start_v ml hB hL ⟨hstart_le, hm_eq⟩ => ?_)
        (fun _ _ _ hL => by c0_hsteps; exact hL end_v m2 ⟨Nat.le_refl _, rfl⟩)
      · dsimp only at hstart_lt hm_eq ⊢; subst mb
        have hstart_ext : start_v.toNat < s2.scratch.extend_stk.length := by omega
        c0_hsteps_nogrp
        refine wp_join_state0 (α := FullState)
          (fun s3 m3 => PreservesCoreSlice (fullExtendSlice c).coreProj s2 s3 ∧ s3.LengthsOk c ∧
            (FullMem c s3 ⋆ R) m3)
          (fun Jext s3 m3 ⟨hcore3, hs3, hm3⟩ => by
            c0_hsteps
            exact ihe (start_v, s3) m3 (by dsimp only; exact hstart_lt)
              ⟨by dsimp only; omega, hcore2.trans hcore3, hs3, hm3⟩)
          (fun Jext hJext => by
            c0_hsplit
            · c0_hsteps_nogrp
              refine wp_join_state0 (α := FullState)
                (fun s3 m3 => PreservesCoreSlice (fullExtendSlice c).coreProj s2 s3 ∧
                  s3.LengthsOk c ∧ (FullMem c s3 ⋆ R) m3)
                (fun Jcm s3 m3 h => by c0_hsteps; exact hJext s3 m3 h)
                (fun Jcm hJcm => by
                  c0_hsplit
                  · c0_hsplit
                    · let ncv := (s2.scratch.extend_stk[start_v.toNat]'hstart_ext &&&
                        0x3FFFFFFF#32).setWidth 64
                      have hncv_eq : ncv.toNat =
                          (s2.scratch.extend_stk[start_v.toNat]'hstart_ext &&&
                            0x3FFFFFFF#32).toNat := by
                        dsimp only [ncv]; exact bv_zext_toNat _ (by decide)
                      have hncv_lt : ncv.toNat < 2 ^ 30 := by
                        rw [hncv_eq, BitVec.toNat_and,
                          show (0x3FFFFFFF#32 : BitVec 32).toNat = 2 ^ 30 - 1 from rfl,
                          Nat.and_two_pow_sub_one_eq_mod]
                        exact Nat.mod_lt _ (by decide)
                      have hs1ncv_le : start_v.toNat + 1 + ncv.toNat ≤ end_v.toNat := by
                        have h64 : start_v.toNat + 1 + ncv.toNat < 2 ^ 64 := by omega
                        have h1 : (start_v.toNat + BitVec.toNat (1#64) + ncv.toNat) % 2 ^ 64 ≤
                            end_v.toNat := by rw [hncv_eq]; assumption
                        rw [show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h64] at h1
                        exact h1
                      have hncv_mx : ncv.toNat ≤ c.max_vars := by
                        have h1 : ncv.toNat ≤ c.max_vars % 2 ^ 64 := by
                          rw [hncv_eq]; assumption
                        omega
                      c0_hsteps_nogrp
                      refine wp_while_state
                        (fun (p : BitVec 64 × FullState) => (p.1, ()))
                        (fun p => p.1.toNat)
                        (fun p mk =>
                          p.1.toNat ≤ ncv.toNat ∧
                          PreservesCoreSlice (fullExtendSlice c).coreProj s2 p.2 ∧
                          p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) mk)
                        (fun Jk hJk => by
                          c0_hsteps; exact hJk (ncv, s2) m2 ⟨Nat.le_refl _, rfl, hs2, hm2⟩)
                        (fun Jk ⟨kv, sk⟩ mk ⟨hk_le, hcorek, hsk, hmk⟩ ihk => ?_)
                      dsimp only at hk_le hcorek hsk hmk ihk ⊢
                      c0_hsplit
                      · have hk_pos : 0 < kv.toNat := by c0_bound
                        have hk1 : (kv - 1#64).toNat = kv.toNat - 1 := by bv_omega
                        obtain ⟨_, _, _, _, _, _⟩ := fullExtend_preserves_nonVals hcorek
                        have hesk : sk.scratch.extend_stk = s2.scratch.extend_stk :=
                          (fullExtend_preserves_nonVals hcorek).1 ▸ rfl
                        have hk_add64 : start_v.toNat + 1 + (kv.toNat - 1) < 2 ^ 64 := by omega
                        have hext_k_eq : (start_v + 1#64 + (kv - 1#64)).toNat =
                            start_v.toNat + 1 + (kv.toNat - 1) := by
                          rw [BitVec.toNat_add, BitVec.toNat_add, hk1,
                            show (1#64 : BitVec 64).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega : start_v.toNat + 1 < 2 ^ 64),
                            Nat.mod_eq_of_lt hk_add64]
                        have hext_k : (start_v + 1#64 + (kv - 1#64)).toNat <
                            sk.scratch.extend_stk.length := by
                          rw [hesk, hesl2, hext_k_eq]; omega
                        c0_hsteps_nogrp
                        refine wp_join_state0 (α := FullState)
                          (fun sk' mk' => PreservesCoreSlice (fullExtendSlice c).coreProj sk sk' ∧
                            sk'.LengthsOk c ∧ (FullMem c sk' ⋆ R) mk')
                          (fun _ sk' mk' ⟨hck', hsk', hmk'⟩ => by
                            c0_hsteps
                            exact ihk (kv - 1#64, sk') mk' (by dsimp only; omega)
                              ⟨by dsimp only; omega, hcorek.trans hck', hsk', hmk'⟩)
                          (fun Jk2 hJk2 => by
                            c0_hsplit
                            · have hext_c0 : (start_v + 1#64 + (kv - 1#64)).toNat =
                                  (start_v.toNat + BitVec.toNat (1 : BitVec 64) +
                                    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + kv.toNat)) %
                                    2 ^ 64 := by
                                rw [hext_k_eq]
                                change start_v.toNat + 1 + (kv.toNat - 1) =
                                  (start_v.toNat + 1 + (2 ^ 64 - 1 + kv.toNat)) % 2 ^ 64
                                omega
                              have hov_32 : (sk.scratch.extend_stk[(start_v + 1#64 +
                                    (kv - 1#64)).toNat]'hext_k).toNat < c.max_vars % 2 ^ 64 := by
                                simpa only [hext_c0] using hc
                              let ov64 := (sk.scratch.extend_stk[(start_v + 1#64 +
                                (kv - 1#64)).toNat]'hext_k).setWidth 64
                              have hov_lt : ov64.toNat < c.max_vars := by
                                dsimp only [ov64]; rw [bv_zext_toNat _ (by decide)]; omega
                              have hvlk := hsk.core_ok.vals_len
                              have hk_shl0 : ((kv - 1#64) <<< (1 : Nat)).toNat <
                                  sk.core.vals.length := by
                                rw [hvlk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                                  show (2 : Nat) ^ 1 = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                                omega
                              have hk_shl1 : (((kv - 1#64) <<< (1 : Nat)) ||| 1#64).toNat <
                                  sk.core.vals.length := by
                                rw [hvlk, bv64_shl1_or1_toNat (by omega)]; omega
                              have hov_shl0 : (ov64 <<< (1 : Nat)).toNat < sk.core.vals.length := by
                                rw [hvlk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                                  show (2 : Nat) ^ 1 = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                                omega
                              have hov_shl1 : ((ov64 <<< (1 : Nat)) ||| 1#64).toNat <
                                  (sk.core.vals.set (ov64 <<< (1 : Nat)).toNat
                                    (sk.core.vals[((kv - 1#64) <<< (1 : Nat)).toNat]'hk_shl0)
                                  ).length := by
                                rw [List.length_set, hvlk, bv64_shl1_or1_toNat (by omega)]; omega
                              c0_hsteps
                              let sk' : FullState := { sk with core := { sk.core with vals :=
                                ((sk.core.vals.set (ov64 <<< (1 : Nat)).toNat
                                  (sk.core.vals[((kv - 1#64) <<< (1 : Nat)).toNat]'hk_shl0)).set
                                  ((ov64 <<< (1 : Nat)) ||| 1#64).toNat
                                  (sk.core.vals[(((kv - 1#64) <<< (1 : Nat)) |||
                                    1#64).toNat]'hk_shl1)) } }
                              exact hJk2 sk' _
                                ⟨rfl, ⟨{ hsk.core_ok with
                                    vals_len := by dsimp only [sk']; simp [hvlk] },
                                  hsk.scratch_ok⟩, hm⟩
                            · c0_hsteps; exact hJk2 sk mk ⟨rfl, hsk, hmk⟩)
                      · c0_hsteps_nogrp
                        refine wp_while_state
                          (fun (p : BitVec 64 × BitVec 64 × FullState) => (p.1, p.2.1, ()))
                          (fun p => c.max_vars - p.2.1.toNat)
                          (fun p mg =>
                            p.1.toNat ≤ ncv.toNat ∧ p.2.1.toNat ≤ c.max_vars ∧
                            PreservesCoreSlice (fullExtendSlice c).coreProj s2 p.2.2 ∧
                            p.2.2.LengthsOk c ∧ (FullMem c p.2.2 ⋆ R) mg)
                          (fun Jg hJg => by
                            c0_hsteps
                            exact hJg (0#64, 0#64, sk) mk
                              ⟨Nat.zero_le _, Nat.zero_le _, hcorek, hsk, hmk⟩)
                          (fun Jg ⟨jv, gv, sg⟩ mg ⟨hj_le, hg_le, hcoreg, hsg, hmg⟩ ihg => ?_)
                        dsimp only at hj_le hg_le hcoreg hsg hmg ihg ⊢
                        c0_hsplit
                        · have hg_lt : gv.toNat < c.max_vars := by
                            have h1 : gv.toNat < c.max_vars % 2 ^ 64 := by assumption
                            omega
                          have hg1 : (gv + 1#64).toNat = gv.toNat + 1 := by
                            simp only [bv_c0]; omega
                          have hesg : sg.scratch.extend_stk = s2.scratch.extend_stk :=
                            (fullExtend_preserves_nonVals hcoreg).1 ▸ rfl
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                            (fun b => (b, ()))
                            (fun nxt => jv.toNat < ncv.toNat ∨ nxt.toNat = c.max_vars)
                            (fun _ nxt hnxt => by
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [i64])
                                (fun (p : BitVec 64 × FullState) => (p.1, ()))
                                (fun p mg' =>
                                  p.1.toNat ≤ ncv.toNat ∧
                                  PreservesCoreSlice (fullExtendSlice c).coreProj sg p.2 ∧
                                  p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) mg')
                                (fun _ ⟨j', sg'⟩ mg' ⟨hj', hcg', hsg', hmg'⟩ => by
                                  dsimp only at hj' hcg' hsg' hmg' ⊢
                                  c0_hsteps
                                  exact ihg (j', gv + 1#64, sg') mg'
                                    (by dsimp only; rw [hg1]; omega)
                                    ⟨hj', by rw [hg1]; omega, hcoreg.trans hcg', hsg', hmg'⟩)
                                (fun _ hJj => by
                                  c0_hsplit
                                  · have hj_lt : jv.toNat < ncv.toNat := by
                                      rcases hnxt with h | h
                                      · exact h
                                      · exfalso; have hgv : gv.toNat = nxt.toNat :=
                                          congrArg BitVec.toNat (by assumption)
                                        omega
                                    have hj1 : (jv + 1#64).toNat = jv.toNat + 1 := by
                                      simp only [bv_c0]; omega
                                    c0_hsteps
                                    exact hJj (jv + 1#64, sg) mg
                                      ⟨by rw [hj1]; omega, rfl, hsg, hmg⟩
                                  · have hvlg := hsg.core_ok.vals_len
                                    have hg_shl0 : (gv <<< (1 : Nat)).toNat <
                                        sg.core.vals.length := by
                                      rw [hvlg, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                                        show (2 : Nat) ^ 1 = 2 from rfl,
                                        Nat.mod_eq_of_lt (by omega)]
                                      omega
                                    have hg_shl1 : ((gv <<< (1 : Nat)) ||| 1#64).toNat <
                                        (sg.core.vals.set (gv <<< (1 : Nat)).toNat 1#8).length := by
                                      rw [List.length_set, hvlg, bv64_shl1_or1_toNat (by omega)]
                                      omega
                                    c0_hsteps
                                    let sg' : FullState := { sg with core := { sg.core with vals :=
                                      ((sg.core.vals.set (gv <<< (1 : Nat)).toNat 1#8).set
                                        ((gv <<< (1 : Nat)) ||| 1#64).toNat
                                        (BitVec.setWidth 8 (-1#32))) } }
                                    exact hJj (jv, sg') _ ⟨hj_le, rfl,
                                      ⟨{ hsg.core_ok with
                                          vals_len := by dsimp only [sg']; simp [hvlg] },
                                        hsg.scratch_ok⟩, hm⟩))
                            (fun _ hJn => by
                              c0_hsplit
                              · have hj_lt : jv.toNat < ncv.toNat := by c0_bound
                                have hj_add64 : start_v.toNat + 1 + jv.toNat < 2 ^ 64 := by omega
                                have hext_j_eq : (start_v + 1#64 + jv).toNat =
                                    start_v.toNat + 1 + jv.toNat := by
                                  rw [BitVec.toNat_add, BitVec.toNat_add,
                                    show (1#64 : BitVec 64).toNat = 1 from rfl,
                                    Nat.mod_eq_of_lt (by omega : start_v.toNat + 1 < 2 ^ 64),
                                    Nat.mod_eq_of_lt hj_add64]
                                have hext_j : (start_v + 1#64 + jv).toNat <
                                    sg.scratch.extend_stk.length := by
                                  rw [hesg, hesl2, hext_j_eq]; omega
                                c0_hsteps; exact hJn _ (Or.inl hj_lt)
                              · c0_hsteps
                                exact hJn (BitVec.ofNat 64 c.max_vars)
                                  (Or.inr (nat_bv64_ofNat_toNat (by omega))))
                        · c0_hsteps; exact hJcm sg mg ⟨hcoreg, hsg, hmg⟩
                    · c0_hsteps; exact hJcm s2 m2 ⟨rfl, hs2, hm2⟩
                  · c0_hsteps; exact hJcm s2 m2 ⟨rfl, hs2, hm2⟩)
            · c0_hsteps_nogrp
              refine wp_while_break_state (α := BitVec 64) (β := Bool × BitVec 64)
                (fun p => (p.1, p.2, ()))
                (fun _ ml => ml = m2)
                (fun pv => (pv, ()))
                (fun pv => end_v.toNat - pv.toNat)
                (fun pv ml => start_v.toNat ≤ pv.toNat ∧ pv.toNat ≤ end_v.toNat ∧ ml = m2)
                (fun _ ⟨sat, pv_end⟩ mb hm_eq => ?_)
                (fun B L pv ml hB hL ⟨hps, hpe, hm_eq⟩ => ?_)
                (fun _ _ _ hL => by
                  c0_hsteps; exact hL start_v m2 ⟨Nat.le_refl _, by omega, rfl⟩)
              · dsimp only at hm_eq ⊢; subst mb
                let head := s2.scratch.extend_stk[start_v.toNat]'hstart_ext
                let blk := head &&& 0x7FFFFFFF#32
                have hblk_v_lt : blk.toNat < 2 ^ 31 := bv32_and_mask_lt
                refine wp_join_state0 (α := FullState)
                  (fun s3 m3 => PreservesCoreSlice (fullExtendSlice c).coreProj s2 s3 ∧
                    s3.LengthsOk c ∧ (FullMem c s3 ⋆ R) m3)
                  (fun _ s3 m3 ⟨hcore3, hs3, hm3⟩ => by
                    c0_hsteps; exact hJext s3 m3 ⟨hcore3, hs3, hm3⟩)
                  (fun _ hJif => by
                    c0_hsplit
                    · c0_hsteps; exact hJif s2 m2 ⟨rfl, hs2, hm2⟩
                    · c0_hsplit
                      · have hblk_v : blk.toNat / 2 < c.max_vars := by
                          have h1 : blk.toNat / 2 < c.max_vars % 2 ^ 64 := by
                            change blk.toNat / 2 < c.max_vars % 2 ^ 64 at hc; exact hc
                          omega
                        have hvl2 := hs2.core_ok.vals_len
                        have hblk0 : (blk.setWidth 64).toNat < s2.core.vals.length := by
                          rw [hvl2, bv_zext_toNat _ (by decide)]; omega
                        have hblk_xor : ((blk ^^^ 1#32).setWidth 64).toNat <
                            (s2.core.vals.set (blk.setWidth 64).toNat 1#8).length := by
                          rw [List.length_set, hvl2, bv_zext_toNat _ (by decide)]
                          exact bv32_xor1_lt hblk_v
                        c0_hsteps
                        let s2' : FullState := { s2 with core := { s2.core with vals :=
                          ((s2.core.vals.set (blk.setWidth 64).toNat 1#8).set
                            ((blk ^^^ 1#32).setWidth 64).toNat
                            (BitVec.setWidth 8 (-1#32))) } }
                        exact hJif s2' _
                          ⟨rfl, ⟨{ hs2.core_ok with
                              vals_len := by dsimp only [s2']; simp [hvl2] },
                            hs2.scratch_ok⟩, hm⟩
                      · c0_hsteps; exact hJif s2 m2 ⟨rfl, hs2, hm2⟩)
              · dsimp only at hps hpe hm_eq ⊢; subst ml
                c0_hsplit
                · have hp_lt : pv.toNat < end_v.toNat := by c0_bound
                  have hp1 : (pv + 1#64).toNat = pv.toNat + 1 := by simp only [bv_c0]; omega
                  have hp_ext : pv.toNat < s2.scratch.extend_stk.length := by omega
                  let lit := s2.scratch.extend_stk[pv.toNat]'hp_ext &&& 0x7FFFFFFF#32
                  have hlit_lt31 : lit.toNat < 2 ^ 31 := bv32_and_mask_lt
                  c0_hsteps_nogrp
                  refine wp_join0 (fun m' => m' = m2)
                    (fun _ _ hm_eq => by
                      dsimp only at hm_eq ⊢; rw [hm_eq]; c0_hsteps
                      exact hL (pv + 1#64) m2 (by rw [hp1]; omega)
                        ⟨by rw [hp1]; omega, by rw [hp1]; omega, rfl⟩)
                    (fun _ hJnx => by
                      c0_hsplit
                      · have hlit_v : lit.toNat / 2 < c.max_vars := by
                          have h1 : lit.toNat / 2 < c.max_vars % 2 ^ 64 := by
                            change lit.toNat / 2 < c.max_vars % 2 ^ 64 at hc; exact hc
                          omega
                        have hlit_vals : (lit.setWidth 64).toNat < s2.core.vals.length := by
                          rw [hs2.core_ok.vals_len, bv_zext_toNat _ (by decide)]; omega
                        c0_hsplit
                        · c0_hsteps; exact hB (true, pv) m2 rfl
                        · c0_hsteps; exact hJnx m2 rfl
                      · c0_hsteps; exact hJnx m2 rfl)
                · c0_hsteps; exact hB (false, pv) m2 rfl)
      · dsimp only at hstart_le hm_eq ⊢; subst ml
        c0_hsplit
        · have hs_pos : 0 < start_v.toNat := by c0_bound
          have hsm1 : (start_v - 1#64).toNat < start_v.toNat := by bv_omega
          have hsm1_ext : (start_v - 1#64).toNat < s2.scratch.extend_stk.length := by omega
          c0_hsteps_nogrp; c0_hsplit
          · c0_hsteps; exact hB (start_v - 1#64) m2 ⟨by omega, rfl⟩
          · c0_hsteps; exact hL (start_v - 1#64) m2 hsm1 ⟨by omega, rfl⟩
        · c0_hsteps; exact hB start_v m2 ⟨by omega, rfl⟩
    · c0_hsteps; exact hQ () s2 m2 hcore2 hs2 trivial hm2

theorem full_unperm_fid_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullUnpermFidSpec a m Q X → Func.wp Γ full_unperm_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hlen hm hQ
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hext : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at hmax hext
  have hesl : s.scratch.extend_stk.length = c.extend_cap := hlen.scratch_ok.extend_stk_len
  unfold Func.wp full_unperm_fid_body
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen trivial hm
  · have hlen_pos : 0 < s.scratch.extend_len := by
      have hne : ¬ BitVec.ofNat 64 s.scratch.extend_len = 0#64 := by assumption
      exact Nat.pos_of_ne_zero fun hz => hne (by rw [hz])
    have h0_lt : (BitVec.ofNat 64 0).toNat < s.scratch.extend_stk.length := by
      rw [hesl]; simp only [BitVec.toNat_ofNat]; omega
    c0_hsteps_nogrp
    · exact hQ () s m rfl hlen trivial hm
    · exact hQ () s m rfl hlen trivial hm
    · exact hQ () s m rfl hlen trivial hm
    · have hmv_le_mx : ((s.scratch.extend_stk[0]'(by simpa using h0_lt) &&&
          536870911#32).setWidth 64).toNat ≤ c.max_vars := by
        have h1 : ¬ c.max_vars % 2 ^ 64 <
            (s.scratch.extend_stk[OfNat.ofNat 0 % 2 ^ 64]'(by simpa using h0_lt) &&&
              536870911#32).toNat := by assumption
        have h2 : c.max_vars % 2 ^ 64 = c.max_vars := Nat.mod_eq_of_lt (by omega)
        have h3 : ((s.scratch.extend_stk[0]'(by simpa using h0_lt) &&&
            536870911#32).setWidth 64).toNat =
            (s.scratch.extend_stk[OfNat.ofNat 0 % 2 ^ 64]'(by simpa using h0_lt) &&&
              536870911#32).toNat := by
          simp only [BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt]
          have := (s.scratch.extend_stk[0]'(by simpa using h0_lt) &&& 536870911#32).isLt; omega
        omega
      let mv_bv : BitVec 64 :=
        (s.scratch.extend_stk[0]'(by simpa using h0_lt) &&& 536870911#32).setWidth 64
      have hmv_to : mv_bv.toNat ≤ c.max_vars := hmv_le_mx
      have h1mv_le_len : 1 + mv_bv.toNat ≤ s.scratch.extend_len := by
        have h1 : ¬ s.scratch.extend_len % 2 ^ 64 <
            (BitVec.toNat (1 : BitVec 64) +
              (s.scratch.extend_stk[OfNat.ofNat 0 % 2 ^ 64]'(by simpa using h0_lt) &&&
                536870911#32).toNat) % 2 ^ 64 := by assumption
        have h2 : mv_bv.toNat =
            (s.scratch.extend_stk[OfNat.ofNat 0 % 2 ^ 64]'(by simpa using h0_lt) &&&
              536870911#32).toNat := by
          dsimp only [mv_bv]; simp only [BitVec.toNat_setWidth]
          rw [Nat.mod_eq_of_lt]
          have := (s.scratch.extend_stk[0]'(by simpa using h0_lt) &&& 536870911#32).isLt; omega
        have h3 : s.scratch.extend_len % 2 ^ 64 = s.scratch.extend_len :=
          Nat.mod_eq_of_lt (by omega)
        have h4 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
        rw [h4, ← h2, h3] at h1
        have h5 : (1 + mv_bv.toNat) % 2 ^ 64 = 1 + mv_bv.toNat := Nat.mod_eq_of_lt (by omega)
        omega
      refine wp_while_state
        (fun (p : BitVec 64 × FullState) => (p.1, ()))
        (fun p => mv_bv.toNat - p.1.toNat)
        (fun p ml =>
          p.1.toNat ≤ mv_bv.toNat ∧
          PreservesCoreSlice (fullExtendSlice c).coreProj s p.2 ∧
          p.2.LengthsOk c ∧ (FullMem c p.2 ⋆ R) ml)
        (fun J hJ => by c0_hsteps; exact hJ (0#64, s) m ⟨Nat.zero_le _, rfl, hlen, hm⟩)
        (fun J ⟨e, s1⟩ m1 ⟨hele, hcore1, hs1, hm1⟩ ih1 => ?_)
      dsimp only at hele hcore1 hs1 hm1 ih1 ⊢
      have hpres1 := fullExtend_preserves_nonVals hcore1
      have hesk1 : s1.scratch.extend_stk.length = c.extend_cap :=
        hs1.scratch_ok.extend_stk_len
      have hvl1 : s1.core.vals.length = 2 * c.max_vars := hs1.core_ok.vals_len
      c0_hsteps_nogrp
      · have he_lt : e.toNat < mv_bv.toNat := by assumption
        have he1 : (e + 1#64).toNat = e.toNat + 1 := by simp only [bv_c0]; omega
        have h1e_lt : (1#64 + e).toNat < s1.scratch.extend_stk.length := by
          rw [hesk1]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i8])
          (fun _ m2 => (FullMem c s1 ⋆ R) m2)
          (fun J2 ⟨pv, ⟨⟩⟩ m2 hm2 => by
            have he_or1 : ((e <<< (1 : Nat)) ||| 1#64).toNat < s1.core.vals.length := by
              rw [hvl1, bv64_shl1_or1_toNat (by omega)]; omega
            c0_hsteps
            exact ih1 (e + 1#64, _) _ (by dsimp only; rw [he1]; omega)
              ⟨by rw [he1]; omega,
               hcore1.trans (extendSlice_set_vals _ _),
               extendSlice_set_vals_len hs1 _ _, ‹_›⟩)
          (fun J2 hJ2 => by
            c0_hsteps_nogrp
            · have hiv_lt :
                  ((s1.scratch.extend_stk[(1#64 + e).toNat]'h1e_lt).setWidth 64).toNat <
                    c.max_vars := by
                have h1 :
                    (s1.scratch.extend_stk[(1#64 + e).toNat]'h1e_lt).toNat <
                      c.max_vars % 2 ^ 64 := by assumption
                simp only [BitVec.toNat_setWidth]
                have := (s1.scratch.extend_stk[(1#64 + e).toNat]'h1e_lt).isLt
                omega
              have hiv2 :
                  (((s1.scratch.extend_stk[(1#64 + e).toNat]'h1e_lt).setWidth 64) <<<
                    (1 : Nat)).toNat < s1.core.vals.length := by
                rw [hvl1, bv64_shl1_nat_toNat (by omega)]; omega
              c0_hsteps
              · exact hJ2 (BitVec.ofNat 8 255, ()) m1 hm1
              · exact hJ2 (1#8, ()) m1 hm1
            · exact hJ2 (1#8, ()) m1 hm1)
      · refine wp_while_state
          (fun (p : BitVec 64 × FullState) => (p.1, ()))
          (fun p => mv_bv.toNat - p.1.toNat)
          (fun p ml =>
            (FullMem c p.2 ⋆ R) ml ∧
            p.1.toNat ≤ mv_bv.toNat ∧
            PreservesCoreSlice (fullExtendSlice c).coreProj s p.2 ∧
            p.2.LengthsOk c)
          (fun J2 hJ2 => by
            c0_hsteps; exact hJ2 (0#64, s1) m1 ⟨hm1, Nat.zero_le _, hcore1, hs1⟩)
          (fun J2 ⟨e2, s2⟩ m2 ⟨hm2, he2le, hcore2, hs2⟩ ih2 => ?_)
        dsimp only at he2le hcore2 hs2 hm2 ih2 ⊢
        have hvl2 : s2.core.vals.length = 2 * c.max_vars := hs2.core_ok.vals_len
        c0_hsteps_nogrp
        · have he2_lt : e2.toNat < mv_bv.toNat := by assumption
          have he2_1 : (e2 + 1#64).toNat = e2.toNat + 1 := by simp only [bv_c0]; omega
          have he2_or1 : ((e2 <<< (1 : Nat)) ||| 1#64).toNat < s2.core.vals.length := by
            rw [hvl2, bv64_shl1_or1_toNat (by omega)]; omega
          have he2_shl : (e2 <<< (1 : Nat)).toNat < s2.core.vals.length := by
            rw [hvl2, bv64_shl1_nat_toNat (by omega)]; omega
          c0_hsteps_nogrp
          let s2a : FullState :=
            { s2 with core := { s2.core with
                vals := s2.core.vals.set (e2 <<< (1 : Nat)).toNat
                  (s2.core.vals[((e2 <<< (1 : Nat)) ||| 1#64).toNat]'he2_or1) } }
          have hcore2a : PreservesCoreSlice (fullExtendSlice c).coreProj s s2a :=
            hcore2.trans (extendSlice_set_vals _ _)
          have hs2a : s2a.LengthsOk c := extendSlice_set_vals_len hs2 _ _
          have he2_or1a : ((e2 <<< (1 : Nat)) ||| 1#64).toNat < s2a.core.vals.length := by
            rw [hs2a.core_ok.vals_len, bv64_shl1_or1_toNat (by omega)]; omega
          refine wp_join_group (ts := [i32])
            (fun _ m3 => (FullMem c s2a ⋆ R) m3) ?_ ?_
          · rintro J3 ⟨nv, ⟨⟩⟩ m3 hm3
            clear hm
            c0_hsteps
            exact ih2 (e2 + 1#64, _) m (by dsimp only; rw [he2_1]; omega)
              ⟨hm, by rw [he2_1]; omega,
               hcore2a.trans (extendSlice_set_vals _ _),
               extendSlice_set_vals_len hs2a _ _⟩
          · intro J3 hJ3
            c0_hsteps
            · exact hJ3 (_, ()) m hm
            · exact hJ3 (_, ()) m hm
        · exact hQ () s2 m2 hcore2 hs2 trivial hm2

theorem full_extend_wp (Γ : Env)
    (hCore : Γ.Has "full_extend_core_fid" Spec.fullExtendCoreFidSpec)
    (hUnperm : Γ.Has "full_unperm_fid" Spec.fullUnpermFidSpec) :
    ∀ a m Q X, Spec.fullExtendSpec a m Q X → Func.wp Γ full_extend_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hlen hm hQ
  unfold Func.wp full_extend_body
  c0_call hCore
  refine ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, fun _ s1 m1 hcore1 hlen1 _ hm1 => ?_⟩
  have hpres1 := fullExtend_preserves_nonVals hcore1
  have hel1 : s1.scratch.extend_len ≤ c.extend_cap := by rw [hpres1.1]; exact hel
  c0_call hUnperm
  refine ⟨c, s1, R, ⟨rfl, hel1⟩, hlen1, hm1, fun _ s2 m2 hcore2 hlen2 _ hm2 => ?_⟩
  c0_hsteps
  exact hQ () s2 m2 (hcore1.trans hcore2) hlen2 trivial hm2

end

end LeanQbe.T.Examples.Kissat.Proof.Extend
