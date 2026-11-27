/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Src.Limits
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import Lean.Elab.Tactic
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proofs for `Kissat/Src/Limits.lean` (`15` fns)

Self-contained `CanonicalEnv` `Func.wp` proofs for all `15` functions of `Src.Limits.fns`,
with zero legacy `Full*` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Limits

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Limits
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local macro "lim_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

private theorem bv64_shr2_toNat (x : BitVec 64) : (x >>> (2 : BitVec 64)).toNat = x.toNat / 4 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv64_shr1_toNat (x : BitVec 64) : (x >>> (1 : BitVec 64)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ## Local Scoped `array64` / `array32` Step Rules -/

private theorem addr64_bv_eq (a i : BitVec 64) : a + i * 8 = a + BitVec.ofNat 64 (8 * i.toNat) := by
  have : i * 8 = BitVec.ofNat 64 (8 * i.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [this]

private theorem addr64_nat_eq (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 i * 8 = a + BitVec.ofNat 64 (8 * i) := by
  have : BitVec.ofNat 64 i * 8 = BitVec.ofNat 64 (8 * i) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm, Nat.mul_mod]
  rw [this]

private theorem addr64_add_nat_eq (a : BitVec 64) (i k : Nat) :
    a + (BitVec.ofNat 64 i + BitVec.ofNat 64 k) * 8 = a + BitVec.ofNat 64 (8 * (i + k)) := by
  have : (BitVec.ofNat 64 i + BitVec.ofNat 64 k) * 8 = BitVec.ofNat 64 (8 * (i + k)) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_add, Nat.mul_comm, Nat.add_mod, Nat.mul_mod]
  rw [this]

private theorem addr32_bv_eq (a i : BitVec 64) : a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
  have : i * 4 = BitVec.ofNat 64 (4 * i.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [this]

@[local c0_store] private theorem c0_store_arr64_bv {a i v : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length) (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + i * 8) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + i * 8) v) := by
  rw [addr64_bv_eq]; exact store_array64 v hi hm

@[local c0_store] private theorem c0_store_arr64_ofNat {a v : BitVec 64} {i : Nat}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length)
    (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + BitVec.ofNat 64 i * 8) ∧
      (array64 a (xs.set i v) ⋆ R) (storeMem m i64 (a + BitVec.ofNat 64 i * 8) v) := by
  rw [addr64_nat_eq]; exact store_array64 v hi hm

@[local c0_store] private theorem c0_store_arr64_addNat {a v : BitVec 64} {i k : Nat}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (hi : i + k < xs.length)
    (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + (BitVec.ofNat 64 i + BitVec.ofNat 64 k) * 8) ∧
      (array64 a (xs.set (i + k) v) ⋆ R)
        (storeMem m i64 (a + (BitVec.ofNat 64 i + BitVec.ofNat 64 k) * 8) v) := by
  rw [addr64_add_nat_eq]; exact store_array64 v hi hm

@[local c0_load] private theorem c0_load_arr32_bv {a i : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i32 (a + i * 4) = some xs[i.toNat] := by
  rw [addr32_bv_eq]; exact loadVal_array (t := i32) (by decide) hi hm

@[local c0_store] private theorem c0_store_arr32_bv {a i : BitVec 64} {v : BitVec 32}
    {xs : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    storeOk m i32 (a + i * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R) (storeMem m i32 (a + i * 4) v) := by
  rw [addr32_bv_eq]; exact store_array (t := i32) v (by decide) hi hm

/-! ## Section 1: Pure Math & Scalar Utilities (`full_isqrt`, `full_ilog10`, `full_max_u64`) -/

private def IsqrtInv (x0 x r : BitVec 64) (s : Nat) : Prop :=
  (∃ p, s = 2 ^ p ∧ p ≤ 31) ∧ 2 * s ∣ r.toNat ∧
  let q := r.toNat / (2 * s)
  q + 2 * s ≤ 2 ^ 32 ∧ x.toNat + q * q = x0.toNat ∧ x.toNat < 4 * s * q + 4 * s * s

private theorem mul_sq_two_eq (k : Nat) : (2 * k) * (2 * k) = 4 * (k * k) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm k 2 k, ← Nat.mul_assoc]

private theorem sq_succ_eq (q : Nat) : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega

private theorem isqrt_loop2_step {x0 x r bit : BitVec 64} {s : Nat}
    (hinv : IsqrtInv x0 x r s) (hsnz : 0 < s) (hbit : bit = BitVec.ofNat 64 (s * s)) :
    have hlt_s2 : s * s < 2 ^ 64 := by
      rcases hinv.1 with ⟨p, rfl, hp⟩
      calc 2 ^ p * 2 ^ p = 2 ^ (2 * p) := by rw [← Nat.pow_add, Nat.two_mul]
        _ < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    have hbit_eq : bit.toNat = s * s := by
      rw [hbit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_s2]
    let q := r.toNat / (2 * s)
    have hr_eq : r.toNat = 2 * s * q := (Nat.mul_div_cancel' hinv.2.1).symm
    have hrb_lt : r.toNat + bit.toNat < 2 ^ 64 := by
      rcases hinv.1 with ⟨p, hp_eq, hp_le⟩
      have hqbd := hinv.2.2.1
      by_cases hp31 : p = 31
      · subst hp_eq hp31
        have hq0 : q = 0 := by omega
        have hr0 : r.toNat = 0 := by rw [hr_eq, hq0, Nat.mul_zero]
        rw [hr0, Nat.zero_add, hbit_eq]; decide
      · have hp30 : p ≤ 30 := by omega
        have hs_le : s ≤ 2 ^ 30 := by rw [hp_eq]; exact Nat.pow_le_pow_right (by decide) hp30
        have hsum_le : 2 * q + s < 2 ^ 33 := by
          have : q + 2 * s ≤ 2 ^ 32 := hqbd
          omega
        have hmul_lt : s * (2 * q + s) < 2 ^ 30 * 2 ^ 33 :=
          Nat.mul_lt_mul_of_le_of_lt hs_le hsum_le (by omega)
        have hfactor : 2 * s * q + s * s = s * (2 * q + s) := by
          rw [Nat.mul_comm 2 s, Nat.mul_assoc, ← Nat.mul_add]
        rw [hr_eq, hbit_eq, hfactor]
        exact Nat.lt_trans hmul_lt (by decide)
    (x.ult (r + bit) = false →
      (bit >>> (2 : BitVec 64) = 0#64 →
        let r' := (r >>> (1 : BitVec 64)) + bit
        r'.toNat ≤ 2 ^ 32 ∧ r'.toNat * r'.toNat ≤ x0.toNat ∧
        (2 ≤ x0.toNat → 1 ≤ r'.toNat ∧ x0.toNat < (r'.toNat + 1) * (r'.toNat + 1))) ∧
      (bit >>> (2 : BitVec 64) ≠ 0#64 →
        IsqrtInv x0 (x - (r + bit)) ((r >>> (1 : BitVec 64)) + bit) (s / 2) ∧
        bit >>> (2 : BitVec 64) = BitVec.ofNat 64 ((s / 2) * (s / 2)))) ∧
    (x.ult (r + bit) = true →
      (bit >>> (2 : BitVec 64) = 0#64 →
        let r' := r >>> (1 : BitVec 64)
        r'.toNat ≤ 2 ^ 32 ∧ r'.toNat * r'.toNat ≤ x0.toNat ∧
        (2 ≤ x0.toNat → 1 ≤ r'.toNat ∧ x0.toNat < (r'.toNat + 1) * (r'.toNat + 1))) ∧
      (bit >>> (2 : BitVec 64) ≠ 0#64 →
        IsqrtInv x0 x (r >>> (1 : BitVec 64)) (s / 2) ∧
        bit >>> (2 : BitVec 64) = BitVec.ofNat 64 ((s / 2) * (s / 2)))) := by
  intro hlt_s2 hbit_eq q hr_eq hrb_lt
  obtain ⟨⟨p, hp_eq, hp_le⟩, hdvd, hqbd, hsum, hrem⟩ := hinv
  change q + 2 * s ≤ 2 ^ 32 at hqbd
  change x.toNat + q * q = x0.toNat at hsum
  change x.toNat < 4 * s * q + 4 * s * s at hrem
  have hrb_toNat : (r + bit).toNat = r.toNat + bit.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hrb_lt]
  have hbit_shr : (bit >>> (2 : BitVec 64)).toNat = (s * s) / 4 := by
    rw [bv64_shr2_toNat, hbit_eq]
  have hp_cases : p = 0 ∨ 1 ≤ p := by omega
  constructor
  · intro hge_b
    have hge : r.toNat + bit.toNat ≤ x.toNat := by
      have hu : (x.ult (r + bit)) = decide (x.toNat < (r + bit).toNat) := rfl
      rw [hu, decide_eq_false_iff_not, hrb_toNat] at hge_b
      omega
    have hge_s : 2 * s * q + s * s ≤ x.toNat := by rw [hr_eq, hbit_eq] at hge; exact hge
    have hx'_eq : (x - (r + bit)).toNat = x.toNat - (2 * s * q + s * s) := by
      rw [BitVec.toNat_sub, hrb_toNat, hr_eq, hbit_eq]
      have hxlt := x.isLt; omega
    have hsq_add : (q + s) * (q + s) = q * q + 2 * s * q + s * s := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm q s, Nat.mul_assoc]; omega
    have hsum_q1 : (x - (r + bit)).toNat + (q + s) * (q + s) = x0.toNat := by
      rw [hx'_eq, hsq_add]; omega
    have hr_half_add_lt : r.toNat / 2 + bit.toNat < 2 ^ 64 := by
      have := r.isLt; omega
    have hr'_eq : ((r >>> (1 : BitVec 64)) + bit).toNat = s * q + s * s := by
      rw [BitVec.toNat_add, bv64_shr1_toNat, Nat.mod_eq_of_lt hr_half_add_lt, hbit_eq, hr_eq,
        Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
    constructor
    · intro hbit0
      have hs1 : s = 1 := by
        rcases hp_cases with rfl | hp1
        · exact hp_eq
        · have h2p : 2 ≤ 2 ^ p := Nat.le_self_pow (by omega) 2
          have hge4 : 4 ≤ s * s := by
            rw [hp_eq]; exact Nat.mul_le_mul h2p h2p
          have hpos : 0 < (bit >>> (2 : BitVec 64)).toNat := by rw [hbit_shr]; omega
          rw [hbit0] at hpos; exact absurd hpos (by decide)
      subst hs1
      simp only [Nat.one_mul, Nat.mul_one] at hr'_eq hx'_eq hsum_q1 hrem hqbd
      have hq_eq : ((r >>> (1 : BitVec 64)) + bit).toNat = q + 1 := by rw [hr'_eq]
      have hrem1 : (x - (r + bit)).toNat < 2 * q + 3 := by rw [hx'_eq]; omega
      have hx0_lt : x0.toNat < ((q + 1) + 1) * ((q + 1) + 1) := by
        rw [sq_succ_eq (q + 1), ← hsum_q1]; omega
      refine ⟨by rw [hq_eq]; omega, by rw [hq_eq]; omega, fun hx2 => ⟨by rw [hq_eq]; omega, ?_⟩⟩
      rw [hq_eq]; exact hx0_lt
    · intro hbit_nz
      have hp1 : 1 ≤ p := by
        rcases hp_cases with rfl | hp1
        · exfalso; apply hbit_nz
          apply BitVec.eq_of_toNat_eq
          rw [hbit_shr, hp_eq]; rfl
        · exact hp1
      have hs_eq : s = 2 * (s / 2) := by
        rw [hp_eq]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hp1
        rw [Nat.pow_succ, Nat.mul_comm]
        exact (congrArg (2 * ·) (Nat.mul_div_cancel_left (2 ^ k) (by decide))).symm
      have hs_div : s / 2 = 2 ^ (p - 1) := by
        rw [hp_eq]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hp1
        rw [Nat.pow_succ, Nat.add_sub_cancel, Nat.mul_comm, Nat.mul_div_cancel_left _ (by decide)]
      have hss_eq : s * s = 4 * ((s / 2) * (s / 2)) := by
        conv => lhs; rw [hs_eq]
        exact mul_sq_two_eq (s / 2)
      have hbit'_eq : (s * s) / 4 = (s / 2) * (s / 2) := by rw [hss_eq]; omega
      have hsq_half : s * q + s * s = 2 * (s / 2) * (q + s) := by
        have : s = 2 * (s / 2) := hs_eq
        conv => rhs; rw [← this]
        rw [Nat.mul_add]
      have hdiv_dvd : 2 * (s / 2) ∣ ((r >>> (1 : BitVec 64)) + bit).toNat := by
        rw [hr'_eq, hsq_half]; exact ⟨q + s, rfl⟩
      have hq'_eq : ((r >>> (1 : BitVec 64)) + bit).toNat / (2 * (s / 2)) = q + s := by
        rw [hr'_eq, hsq_half, Nat.mul_div_cancel_left _ (by omega)]
      have h4sq : 4 * (s / 2) * (q + s) = 2 * s * (q + s) := by
        have : 4 * (s / 2) = 2 * s := by omega
        rw [this]
      have h2ss : 2 * s * (q + s) = 2 * s * q + 2 * s * s := by
        rw [Nat.mul_add, Nat.mul_assoc 2 s s]
      have h4ss : 4 * (s / 2) * (s / 2) = s * s := by
        have : 4 * (s / 2) * (s / 2) = 4 * ((s / 2) * (s / 2)) := Nat.mul_assoc _ _ _
        rw [this, ← hss_eq]
      have hlt_x : x.toNat < 4 * (s * q) + 4 * (s * s) := by
        have h := hrem
        rwa [Nat.mul_assoc 4 s q, Nat.mul_assoc 4 s s] at h
      have hge_x : 2 * (s * q) + s * s ≤ x.toNat := by
        have h := hge_s
        rwa [Nat.mul_assoc 2 s q] at h
      have hx'_eq2 : (x - (r + bit)).toNat = x.toNat - (2 * (s * q) + s * s) := by
        rw [hx'_eq, Nat.mul_assoc 2 s q]
      have h4sq' : 4 * (s / 2) * (q + s) = 2 * (s * q) + 2 * (s * s) := by
        rw [h4sq, h2ss, Nat.mul_assoc 2 s q, Nat.mul_assoc 2 s s]
      have hrem' : (x - (r + bit)).toNat < 4 * (s / 2) * (q + s) + 4 * (s / 2) * (s / 2) := by
        rw [h4sq', h4ss, hx'_eq2]; omega
      refine ⟨⟨⟨p - 1, hs_div, by omega⟩, hdiv_dvd, ?_, ?_, ?_⟩, ?_⟩
      · rw [hq'_eq]; omega
      · rw [hq'_eq]; exact hsum_q1
      · rw [hq'_eq]; exact hrem'
      · apply BitVec.eq_of_toNat_eq
        rw [hbit_shr, hbit'_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · intro hlt_b
    have hlt : x.toNat < r.toNat + bit.toNat := by
      have hu : (x.ult (r + bit)) = decide (x.toNat < (r + bit).toNat) := rfl
      rw [hu, decide_eq_true_iff, hrb_toNat] at hlt_b
      exact hlt_b
    have hlt_s : x.toNat < 2 * s * q + s * s := by rw [hr_eq, hbit_eq] at hlt; exact hlt
    have hr'_eq : (r >>> (1 : BitVec 64)).toNat = s * q := by
      rw [bv64_shr1_toNat, hr_eq, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
    constructor
    · intro hbit0
      have hs1 : s = 1 := by
        rcases hp_cases with rfl | hp1
        · exact hp_eq
        · have h2p : 2 ≤ 2 ^ p := Nat.le_self_pow (by omega) 2
          have hge4 : 4 ≤ s * s := by
            rw [hp_eq]; exact Nat.mul_le_mul h2p h2p
          have hpos : 0 < (bit >>> (2 : BitVec 64)).toNat := by rw [hbit_shr]; omega
          rw [hbit0] at hpos; exact absurd hpos (by decide)
      subst hs1
      simp only [Nat.one_mul, Nat.mul_one] at hr'_eq hlt_s hqbd
      have hq_eq : (r >>> (1 : BitVec 64)).toNat = q := by rw [hr'_eq]
      have hx0_lt : x0.toNat < (q + 1) * (q + 1) := by
        rw [sq_succ_eq q, ← hsum]; omega
      refine ⟨by rw [hq_eq]; omega, by rw [hq_eq]; omega, fun hx2 => ⟨?_, ?_⟩⟩
      · rw [hq_eq]
        refine Classical.byContradiction fun hq0 => ?_
        have hq_z : q = 0 := by omega
        rw [hq_z] at hlt_s hsum; simp at hlt_s hsum; omega
      · rw [hq_eq]; exact hx0_lt
    · intro hbit_nz
      have hp1 : 1 ≤ p := by
        rcases hp_cases with rfl | hp1
        · exfalso; apply hbit_nz
          apply BitVec.eq_of_toNat_eq
          rw [hbit_shr, hp_eq]; rfl
        · exact hp1
      have hs_eq : s = 2 * (s / 2) := by
        rw [hp_eq]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hp1
        rw [Nat.pow_succ, Nat.mul_comm]
        exact (congrArg (2 * ·) (Nat.mul_div_cancel_left (2 ^ k) (by decide))).symm
      have hs_div : s / 2 = 2 ^ (p - 1) := by
        rw [hp_eq]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hp1
        rw [Nat.pow_succ, Nat.add_sub_cancel, Nat.mul_comm, Nat.mul_div_cancel_left _ (by decide)]
      have hss_eq : s * s = 4 * ((s / 2) * (s / 2)) := by
        conv => lhs; rw [hs_eq]
        exact mul_sq_two_eq (s / 2)
      have hbit'_eq : (s * s) / 4 = (s / 2) * (s / 2) := by rw [hss_eq]; omega
      have hdiv_dvd : 2 * (s / 2) ∣ (r >>> (1 : BitVec 64)).toNat := by
        rw [hr'_eq]; refine ⟨q, ?_⟩
        conv => lhs; rw [hs_eq]
      have hq'_eq : (r >>> (1 : BitVec 64)).toNat / (2 * (s / 2)) = q := by
        rw [hr'_eq]
        have hfactor : s * q = (2 * (s / 2)) * q := by
          conv => lhs; rw [hs_eq]
        rw [hfactor, Nat.mul_div_cancel_left _ (by omega)]
      have h4sq : 4 * (s / 2) * q = 2 * s * q := by
        have : 4 * (s / 2) = 2 * s := by omega
        rw [this]
      have h4ss : 4 * (s / 2) * (s / 2) = s * s := by
        have : 4 * (s / 2) * (s / 2) = 4 * ((s / 2) * (s / 2)) := Nat.mul_assoc _ _ _
        rw [this, ← hss_eq]
      have hrem' : x.toNat < 4 * (s / 2) * q + 4 * (s / 2) * (s / 2) := by
        rw [h4sq, h4ss]; exact hlt_s
      refine ⟨⟨⟨p - 1, hs_div, by omega⟩, hdiv_dvd, ?_, ?_, ?_⟩, ?_⟩
      · rw [hq'_eq]; omega
      · rw [hq'_eq]; exact hsum
      · rw [hq'_eq]; exact hrem'
      · apply BitVec.eq_of_toNat_eq
        rw [hbit_shr, hbit'_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem full_isqrt_wp (Γ : Env) :
    ∀ a m Q X, fullIsqrtSpec a m Q X → Func.wp Γ full_isqrt_body a m Q X := by
  rintro ⟨x0, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_isqrt_body
  c0_hsteps_nogrp
  · have hxle1 : x0.toNat ≤ 1 := by c0_bound
    have hsq : x0.toNat * x0.toNat ≤ x0.toNat := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hxle1 with h | h <;> simp [h]
    exact hQ x0 hsq (fun _ => rfl) (fun h2 => by omega)
  · have hxge2 : 2 ≤ x0.toNat := by c0_bound
    refine wp_while_state1 (α := Nat)
      (proj := fun p => BitVec.ofNat 64 (4 ^ p))
      (μ := fun p => p)
      (Inv := fun p m1 => m1 = m ∧ p ≤ 31 ∧ x0.toNat < 4 * 4 ^ p)
      (fun J1 hJ1 => hJ1 31 m ⟨rfl, by omega, by
        have := x0.isLt; exact Nat.lt_of_lt_of_le this (by decide)⟩)
      ?_
    rintro J1 p m1 ⟨hm1, hp31, hlt4⟩ ih1
    subst m1
    rw [Blocks.get_here]
    have h4p_lt : 4 ^ p < 2 ^ 64 := by
      have : 4 ^ p ≤ 4 ^ 31 := Nat.pow_le_pow_right (by decide) hp31
      omega
    have hbit_toNat : (BitVec.ofNat 64 (4 ^ p)).toNat = 4 ^ p := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4p_lt]
    lim_hsteps_nogrp
    · have hlt_x0 : x0.toNat < 4 ^ p := by
        have h1 : x0.toNat < (BitVec.ofNat 64 (4 ^ p)).toNat := by c0_bound
        rwa [hbit_toNat] at h1
      have hp_nz : 0 < p := by
        refine Classical.byContradiction fun hp0 => ?_
        have hpz : p = 0 := by omega
        rw [hpz] at hlt_x0; simp at hlt_x0; omega
      have h4mul : 4 * 4 ^ (p - 1) = 4 ^ p := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hp_nz
        rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
      have hp1_eq : 4 ^ p / 4 = 4 ^ (p - 1) := by
        rw [← h4mul, Nat.mul_div_right _ (by decide)]
      have hshr_nat : BitVec.ofNat 64 (4 ^ p) >>> (2 : Nat) =
          BitVec.ofNat 64 (4 ^ (p - 1)) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show 2 ^ 2 = 4 from rfl,
          hbit_toNat, hp1_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hshr_nat]
      exact ih1 (p - 1) m (by omega) ⟨rfl, by omega, by rw [h4mul]; exact hlt_x0⟩
    · have hle_x0 : 4 ^ p ≤ x0.toNat := by
        have h1 : ¬ x0.toNat < (BitVec.ofNat 64 (4 ^ p)).toNat := by c0_bound
        rw [hbit_toNat] at h1; omega
      have h4p_eq : 4 ^ p = 2 ^ p * 2 ^ p :=
        calc 4 ^ p = (2 * 2) ^ p := rfl
          _ = 2 ^ p * 2 ^ p := Nat.mul_pow 2 2 p
      have hinit_inv : IsqrtInv x0 x0 0#64 (2 ^ p) := by
        refine ⟨⟨p, rfl, hp31⟩, Nat.dvd_zero (2 * 2 ^ p), ?_, ?_, ?_⟩
        · rw [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.zero_div, Nat.zero_add]
          have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hp31
          omega
        · simp
        · rw [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.zero_div, Nat.mul_zero,
            Nat.zero_add, Nat.mul_assoc, ← h4p_eq]
          exact hlt4
      refine wp_while_state (ts := [i64, i64, i64]) (α := BitVec 64 × BitVec 64 × Nat)
        (proj := fun st => (st.1, st.2.1, BitVec.ofNat 64 (st.2.2 * st.2.2), ()))
        (μ := fun st => if st.2.2 = 0 then 0 else st.2.2)
        (Inv := fun st m2 => m2 = m ∧ (st.2.2 = 0 → st.2.1.toNat ≤ 2 ^ 32 ∧
          st.2.1.toNat * st.2.1.toNat ≤ x0.toNat ∧
          (2 ≤ x0.toNat → 1 ≤ st.2.1.toNat ∧ x0.toNat < (st.2.1.toNat + 1) * (st.2.1.toNat + 1))) ∧
          (0 < st.2.2 → IsqrtInv x0 st.1 st.2.1 st.2.2))
        (fun J2 hJ2 => by
          have hgoal := hJ2 (x0, 0#64, 2 ^ p) m
            ⟨rfl, fun h0 => absurd h0 (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))),
             fun _ => hinit_inv⟩
          dsimp only at hgoal; rwa [← h4p_eq] at hgoal)
        ?_
      rintro J2 ⟨xcur, rcur, s⟩ m2 ⟨hm2, hdone, hinv⟩ ih2
      subst m2
      rw [Blocks.get_here]; dsimp only at *
      lim_hsteps_nogrp
      · have hsnz : 0 < s := by
          refine Classical.byContradiction fun hs0 => ?_
          have hsz : s = 0 := by omega
          have hbit0 : BitVec.ofNat 64 (s * s) = 0#64 := by rw [hsz]
          exact absurd hbit0 (by assumption)
        have hstep := isqrt_loop2_step (x := xcur) (r := rcur) (bit := BitVec.ofNat 64 (s * s))
          (hinv hsnz) hsnz rfl
        have hs_half_lt : s / 2 < s := Nat.div_lt_self hsnz (by decide)
        refine wp_join_group (ts := [i64, i64])
          (fun (x', r', ()) mJ => mJ = m ∧
            ((BitVec.ofNat 64 (s * s)) >>> (2 : BitVec 64) = 0#64 →
              r'.toNat ≤ 2 ^ 32 ∧ r'.toNat * r'.toNat ≤ x0.toNat ∧
              (2 ≤ x0.toNat → 1 ≤ r'.toNat ∧ x0.toNat < (r'.toNat + 1) * (r'.toNat + 1))) ∧
            ((BitVec.ofNat 64 (s * s)) >>> (2 : BitVec 64) ≠ 0#64 →
              IsqrtInv x0 x' r' (s / 2) ∧
              (BitVec.ofNat 64 (s * s)) >>> (2 : BitVec 64) = BitVec.ofNat 64 ((s / 2) * (s / 2))))
          ?_ ?_
        · rintro _ ⟨x', r', ⟨⟩⟩ mJ ⟨hmJ, h0, hnz⟩
          subst mJ
          lim_hsteps_nogrp
          have hshr2 : (BitVec.ofNat 64 (s * s)) >>> (2 : Nat) =
              (BitVec.ofNat 64 (s * s)) >>> (2 : BitVec 64) := by
            apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight]
          by_cases hbit0 : (BitVec.ofNat 64 (s * s)) >>> (2 : BitVec 64) = 0#64
          · rw [← hshr2] at hbit0
            rw [hbit0]
            exact ih2 (x', r', 0) m
              (by dsimp only
                  rw [ite_eq_left rfl, ite_eq_right (Nat.ne_of_gt hsnz)]
                  exact hsnz)
              ⟨rfl, fun _ => h0 (by rw [← hshr2]; exact hbit0),
                fun hz => by dsimp only at hz; omega⟩
          · obtain ⟨hinv', hbit'⟩ := hnz hbit0
            have hsnz' : 0 < s / 2 := by
              refine Classical.byContradiction fun h0' => ?_
              have hsd0 : s / 2 = 0 := by omega
              rw [hsd0] at hbit'; exact absurd hbit' hbit0
            rw [hshr2, hbit']
            exact ih2 (x', r', s / 2) m
              (by dsimp only
                  rw [ite_eq_right (Nat.ne_of_gt hsnz'), ite_eq_right (Nat.ne_of_gt hsnz)]
                  exact hs_half_lt)
              ⟨rfl, fun hz => by dsimp only at hz; omega, fun _ => hinv'⟩
        · intro Jstep hJstep
          c0_hsplit
          · lim_hsteps_nogrp
            have hult_f : xcur.ult (rcur + BitVec.ofNat 64 (s * s)) = false := by
              rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_add, BitVec.toNat_ofNat,
                ← Nat.mod_eq_of_lt rcur.isLt, ← Nat.add_mod]
              omega
            exact hJstep _ m ⟨rfl, (hstep.1 hult_f).1, (hstep.1 hult_f).2⟩
          · lim_hsteps_nogrp
            have hult_t : xcur.ult (rcur + BitVec.ofNat 64 (s * s)) = true := by
              rw [BitVec.ult, decide_eq_true_iff, BitVec.toNat_add, BitVec.toNat_ofNat,
                ← Nat.mod_eq_of_lt rcur.isLt, ← Nat.add_mod]
              omega
            exact hJstep _ m ⟨rfl, (hstep.2 hult_t).1, (hstep.2 hult_t).2⟩
      · have hsz : s = 0 := by
          refine Classical.byContradiction fun hnz => ?_
          obtain ⟨⟨p', hp', hp'_le⟩, _⟩ := hinv (Nat.pos_of_ne_zero hnz)
          have h4p'_lt : 2 ^ p' * 2 ^ p' < 2 ^ 64 := by
            calc 2 ^ p' * 2 ^ p' = 2 ^ (2 * p') := by rw [← Nat.pow_add, Nat.two_mul]
              _ < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
          have hpos : 0 < (BitVec.ofNat 64 (s * s)).toNat := by
            rw [hp', BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4p'_lt]
            exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
          rw [show BitVec.ofNat 64 (s * s) = 0#64 from by assumption] at hpos
          exact absurd hpos (by decide)
        obtain ⟨_, h2, h3⟩ := hdone hsz
        c0_hsteps
        exact hQ rcur h2 (fun _ => by omega) (fun _ => h3 hxge2)

theorem full_ilog10_wp (Γ : Env) :
    ∀ a m Q X, fullIlog10Spec a m Q X → Func.wp Γ full_ilog10_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_ilog10_body
  c0_hsteps_nogrp
  refine wp_while_state (ts := [i64, i64]) (α := BitVec 64 × BitVec 64)
    (proj := fun st => (st.1, st.2, ()))
    (μ := fun st => 19 - st.1.toNat)
    (Inv := fun st m1 => m1 = m ∧ 1 ≤ st.1.toNat ∧ st.1.toNat ≤ 19)
    (fun J hJ => hJ (1#64, 10#64) m ⟨rfl, by decide, by decide⟩) ?_
  rintro J ⟨r, p⟩ m1 ⟨hm1, hr1, hr19⟩ ih
  subst m1
  rw [Blocks.get_here]; dsimp only at *
  lim_hsteps_nogrp
  · have hr_lt : r.toNat < 19 := by c0_bound
    have hr1_toNat : (r + 1#64).toNat = r.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    exact ih (r + 1#64, p * 10#64) m (by dsimp only; rw [hr1_toNat]; omega)
      ⟨rfl, by rw [hr1_toNat]; omega, by rw [hr1_toNat]; omega⟩
  all_goals exact hQ r hr1 hr19

theorem full_max_u64_wp (Γ : Env) :
    ∀ a m Q X, schedMaxU64Spec a m Q X → Func.wp Γ full_max_u64_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_max_u64_body schedMaxU64Spec at *
  refine wp_join_group (ts := [i64])
    (fun (rx, ()) m1 => m1 = m ∧ rx = if b < a then a else b)
    (fun _ (rx, ()) m1 ⟨hm1, hrx⟩ => by subst hm1 hrx; c0_hsteps; exact hQ)
    (fun J hJ => by
      c0_hsteps_nogrp
      · have hult : b < a := by c0_bound
        exact hJ (a, ()) m ⟨rfl, (ite_eq_left hult).symm⟩
      · have hnult : ¬ b < a := by c0_bound
        exact hJ (b, ()) m ⟨rfl, (ite_eq_right hnult).symm⟩)

/-! ## Section 2: Telemetry & Scheduler Utilities -/

private theorem fullProbeScratchPres_rfl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def fullUpdRel (s : FullState) (ru rv r_wait rt : BitVec 64) : FullState :=
  { s with
    scratch :=
      { s.scratch with
        rel_u := ru, rel_v := rv, rel_wait := r_wait, rel_trigger := rt } }

private theorem fullUpdRel_lengths {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (ru rv r_wait rt : BitVec 64) :
    (fullUpdRel s ru rv r_wait rt).LengthsOk c :=
  ⟨hlen.core_ok, by unfold fullUpdRel; cases hlen.scratch_ok; constructor <;> assumption⟩

private theorem fullUpdRel_pres (s : FullState) (ru rv r_wait rt : BitVec 64) :
    FullProbeScratchPres s (fullUpdRel s ru rv r_wait rt) :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def fullUpdRelWait (s : FullState) (r_wait : BitVec 64) : FullState :=
  { s with scratch := { s.scratch with rel_wait := r_wait } }

private theorem fullUpdRelWait_lengths {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (r_wait : BitVec 64) :
    (fullUpdRelWait s r_wait).LengthsOk c :=
  ⟨hlen.core_ok, by unfold fullUpdRelWait; cases hlen.scratch_ok; constructor <;> assumption⟩

private theorem fullUpdRelWait_pres (s : FullState) (r_wait : BitVec 64) :
    FullProbeScratchPres s (fullUpdRelWait s r_wait) :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem full_tick_rel_wp (Γ : Env) :
    ∀ a m Q X, fullTickRelSpec a m Q X → Func.wp Γ full_tick_rel_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm
  unfold Func.wp full_tick_rel_body
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (fullProbeScratchPres_rfl s) hm
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (fullProbeScratchPres_rfl s) hm
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (fullProbeScratchPres_rfl s) hm
  refine wp_join_group (ts := []) (fun _ m1 =>
      ∃ rw', (FullMem c (fullUpdRelWait s rw') ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨rw', hm1⟩
    let s1 := fullUpdRelWait s rw'
    have hlen1 := fullUpdRelWait_lengths hlen rw'
    c0_hsteps_nogrp
    · exact hQ () s1 m1 rfl hlen1 (fullUpdRelWait_pres s rw') hm1
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64, i64]) (α := BitVec 64 × BitVec 64)
      (fun p => (p.1, p.2, ())) (fun _ => True) ?_ ?_
    · rintro _ ⟨u1, v1⟩ _
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i64, i64]) (α := BitVec 64 × BitVec 64)
        (fun p => (p.1, p.2, ())) (fun _ => True) ?_ ?_
      · rintro _ ⟨u2, v2⟩ _
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64, i64]) (α := BitVec 64 × BitVec 64)
          (fun p => (p.1, p.2, ())) (fun _ => True) ?_ ?_
        · rintro _ ⟨u3, v3⟩ _
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64, i64, i64])
            (α := BitVec 64 × BitVec 64 × BitVec 64)
            (fun p => (p.1, p.2.1, p.2.2, ())) (fun _ => True) ?_ ?_
          · rintro _ ⟨u4, v4, w4⟩ _
            c0_hsteps
            exact hQ () (fullUpdRel s u4 v4 w4 1#64) _ rfl
              (fullUpdRel_lengths hlen u4 v4 w4 1#64)
              (fullUpdRel_pres s u4 v4 w4 1#64) (by assumption)
          · intro _ hJ4; c0_hsteps <;> exact hJ4 (_, _, _) trivial
        · intro _ hJ3; c0_hsteps <;> exact hJ3 (_, _) trivial
      · intro _ hJ2; c0_hsteps <;> exact hJ2 (_, _) trivial
    · intro _ hJ1; c0_hsteps <;> exact hJ1 (_, _) trivial
  · intro J0 hJ0
    c0_hsteps
    · exact hJ0 () _ ⟨_, (by assumption)⟩
    · exact hJ0 () _ ⟨s.scratch.rel_wait, hm⟩

local macro "scale_delta_core" hLog:ident hSub:ident hMul:ident hAdd:ident hFrom:ident hTo:ident
    hQ:ident m:ident : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    · exact $hQ 0#64
    · refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
        (fun r => (r, ())) (fun _ => True) ?_ ?_
      · rintro _ _ _
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun r => (r, ())) (fun _ => True) ?_ ?_
        · rintro _ _ _
          c0_hsteps_nogrp
          c0_call $hLog; intro _
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
            (fun r => (r, ())) (fun _ => True) ?_ ?_
          · rintro _ _ _
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m1 => m1 = $m) ?_ ?_
            · rintro _ ⟨_, ⟨⟩⟩ m_in hm_in
              subst m_in
              c0_hsteps_nogrp
              c0_call $hMul; intro _; c0_call $hMul; intro _; c0_call $hAdd; intro _
              c0_call $hFrom; intro _; c0_call $hMul; intro _; c0_call $hTo; intro r
              c0_hsteps; dsimp only; exact $hQ r
            · intro _ hJf
              c0_hstraight
              c0_hsplit <;>
                (c0_call $hSub; intro _; c0_hsteps; exact hJf (_, ()) $m rfl)
          · intro _ Jl; c0_hsteps <;> exact Jl _ trivial
        · intro _ Jc2; c0_hsteps <;> exact Jc2 _ trivial
      · intro _ Jc; c0_hsteps <;> exact Jc _ trivial))

theorem full_scale_delta_m5_wp (Γ : Env)
    (hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec)
    (hSub : Γ.Has "f64u_sub" f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hAdd : Γ.Has "f64u_add" f64uPure2Spec)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec)
    (hTo : Γ.Has "f64u_to_u64" f64uPure1Spec) :
    ∀ a m Q X, schedScaleDeltaSpec a m Q X → Func.wp Γ full_scale_delta_m5_body a m Q X := by
  rintro ⟨h, base, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp full_scale_delta_m5_body
  scale_delta_core hLog hSub hMul hAdd hFrom hTo hQ m

theorem full_scale_delta_wp (Γ : Env)
    (hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec)
    (hSub : Γ.Has "f64u_sub" f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hAdd : Γ.Has "f64u_add" f64uPure2Spec)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec)
    (hTo : Γ.Has "f64u_to_u64" f64uPure1Spec) :
    ∀ a m Q X, schedScaleDeltaSpec a m Q X → Func.wp Γ full_scale_delta_body a m Q X := by
  rintro ⟨h, base, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp full_scale_delta_body
  scale_delta_core hLog hSub hMul hAdd hFrom hTo hQ m

theorem full_ema_update_wp (Γ : Env)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec)
    (hAdd : Γ.Has "f64u_add" f64uPure2Spec)
    (hSub : Γ.Has "f64u_sub" f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec) :
    ∀ a m Q X, fullEmaUpdateSpec a m Q X → Func.wp Γ full_ema_update_body a m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm
  unfold Func.wp full_ema_update_body
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps; exact hQ () s m rfl hlen (fullProbeScratchPres_rfl s) hm
  · c0_call hFrom; intro y
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
      (fun r => (r, ())) (fun _ => True) ?_ ?_
    · rintro _ fb' _
      c0_hsteps_nogrp
      let s1 : FullState :=
        { s with scratch := { s.scratch with ema_fast_biased := fb' } }
      refine wp_join_group (ts := []) (fun _ m2 =>
          ∃ efe', (FullMem c
            { s1 with scratch := { s1.scratch with ema_fast_exp := efe' } } ⋆ R) m2)
        ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨efe', hm2⟩
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun r => (r, ())) (fun _ => True) ?_ ?_
        · rintro _ sb' _
          c0_hsteps_nogrp
          let s2 : FullState :=
            { s1 with
              scratch := { s1.scratch with ema_fast_exp := efe', ema_slow_biased := sb' } }
          refine wp_join_group (ts := []) (fun _ m4 =>
              ∃ ese', (FullMem c
                { s2 with scratch := { s2.scratch with ema_slow_exp := ese' } } ⋆ R) m4)
            ?_ ?_
          · rintro _ ⟨⟩ m4 ⟨ese', hm4⟩
            c0_hsteps
            let s3 : FullState := { s2 with scratch := { s2.scratch with ema_slow_exp := ese' } }
            have hm4' : (FullMem c s3 ⋆ R) m4 := hm4
            have hlen3 : s3.LengthsOk c :=
              ⟨hlen.core_ok, by
                dsimp only [s3, s2, s1]
                cases hlen.scratch_ok; constructor <;> assumption⟩
            exact hQ () s3 m4 rfl hlen3 ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hm4'
          · intro Jse hJse
            c0_hsteps_nogrp
            c0_hsplit
            · c0_call hMul; intro r_se
              c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                (fun r => (r, ())) (fun _ => True) ?_ ?_
              · rintro _ se' _
                c0_hsteps
                refine hJse () _ ⟨se', ?_⟩; assumption
              · intro Jse0 hJse0
                c0_hsteps
                · exact hJse0 0#64 trivial
                · exact hJse0 r_se trivial
            · c0_hsteps
              refine hJse () _ ⟨s.scratch.ema_slow_exp, ?_⟩; assumption
        · intro Jsb hJsb
          c0_hsteps_nogrp
          c0_hsplit
          · c0_call hSub; intro _; c0_call hMul; intro _; c0_call hAdd; intro sb'
            exact hJsb sb' trivial
          · c0_call hSub; intro _; c0_call hMul; intro _; c0_call hSub; intro sb'
            exact hJsb sb' trivial
      · intro Jfe hJfe
        c0_hsteps_nogrp
        c0_hsplit
        · c0_call hMul; intro r_fe
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
            (fun r => (r, ())) (fun _ => True) ?_ ?_
          · rintro _ fe' _
            c0_hsteps
            refine hJfe () _ ⟨fe', ?_⟩; assumption
          · intro Jfe0 hJfe0
            c0_hsteps
            · exact hJfe0 0#64 trivial
            · exact hJfe0 r_fe trivial
        · c0_hsteps
          refine hJfe () _ ⟨s.scratch.ema_fast_exp, ?_⟩; assumption
    · intro Jfb hJfb
      c0_hsteps_nogrp
      c0_hsplit
      · c0_call hSub; intro _; c0_call hMul; intro _; c0_call hAdd; intro fb'
        exact hJfb fb' trivial
      · c0_call hSub; intro _; c0_call hMul; intro _; c0_call hSub; intro fb'
        exact hJfb fb' trivial

theorem full_elim_dticks_wp (Γ : Env) (hMax : Γ.Has "full_max_u64" schedMaxU64Spec) :
    ∀ a m Q X, schedElimDticksSpec a m Q X → Func.wp Γ full_elim_dticks_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp full_elim_dticks_body
  c0_hsteps
  all_goals (c0_call hMax; exact hQ _)

/-! ## Section 3: Array & Sort Utilities (`full_fill_u64_m7`, `full_sort_u32`) -/

private theorem fill_step_inv {xs cur : List (BitVec 64)} {i : Nat} {val : BitVec 64}
    (hlen : cur.length = xs.length) (hlt : i < xs.length)
    (hpre : ∀ k < i, cur[k]? = some val) (hsuf : ∀ k, i ≤ k → cur[k]? = xs[k]?) :
    (∀ k < i + 1, (cur.set i val)[k]? = some val) ∧
    (∀ k, i + 1 ≤ k → (cur.set i val)[k]? = xs[k]?) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt' | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hpre k hlt'
    · rw [List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_ne (by omega)]; exact hsuf k (by omega)

private theorem fill_unroll4_inv {xs cur : List (BitVec 64)} {i : Nat} {val : BitVec 64}
    (hlen : cur.length = xs.length) (hle : i + 4 ≤ xs.length)
    (hpre : ∀ k < i, cur[k]? = some val) (hsuf : ∀ k, i ≤ k → cur[k]? = xs[k]?) :
    let cur' := (((cur.set i val).set (i + 1) val).set (i + 2) val).set (i + 3) val
    cur'.length = xs.length ∧ (∀ k < i + 4, cur'[k]? = some val) ∧
    (∀ k, i + 4 ≤ k → cur'[k]? = xs[k]?) := by
  have h1 : (cur.set i val).length = xs.length := by simp [hlen]
  have s1 := fill_step_inv hlen (by omega) hpre hsuf
  have h2 : ((cur.set i val).set (i + 1) val).length = xs.length := by simp [h1]
  have s2 := fill_step_inv h1 (by omega) s1.1 (fun k hk => s1.2 k (by omega))
  have h3 : (((cur.set i val).set (i + 1) val).set (i + 2) val).length = xs.length := by simp [h2]
  have s3 := fill_step_inv h2 (by omega) s2.1 (fun k hk => s2.2 k (by omega))
  have s4 := fill_step_inv h3 (by omega) s3.1 (fun k hk => s3.2 k (by omega))
  refine ⟨by simp [h3], s4.1, s4.2⟩

private theorem fill_list_eq_replicate_append {xs cur : List (BitVec 64)} {n : Nat}
    {val : BitVec 64} (_hn : n ≤ xs.length) (_hlen : cur.length = xs.length)
    (hpre : ∀ k < n, cur[k]? = some val) (hsuf : ∀ k, n ≤ k → cur[k]? = xs[k]?) :
    cur = List.replicate n val ++ xs.drop n := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < n
  · rw [hpre k hk, List.getElem?_append_left (by simp [hk]), List.getElem?_replicate]
    simp [hk]
  · rw [hsuf k (by omega), List.getElem?_append_right (by simp; omega), List.length_replicate,
      List.getElem?_drop, show n + (k - n) = k by omega]

theorem full_fill_u64_m7_wp (Γ : Env) :
    ∀ a m Q X, m7FillU64Spec a m Q X → Func.wp Γ full_fill_u64_m7_body a m Q X := by
  rintro ⟨dst, n, val, ⟨⟩⟩ m Q X ⟨xs, R, hn, hfit, hm, hpost⟩
  unfold Func.wp full_fill_u64_m7_body
  c0_hsteps_nogrp
  refine wp_while_state1 (α := Nat × List (BitVec 64)) (proj := fun st => BitVec.ofNat 64 st.1)
    (μ := fun st => n.toNat - st.1)
    (Inv := fun st m' => st.1 ≤ n.toNat ∧ st.2.length = xs.length ∧
      (∀ k < st.1, st.2[k]? = some val) ∧ (∀ k, st.1 ≤ k → st.2[k]? = xs[k]?) ∧
      (array64 dst st.2 ⋆ R) m')
    (fun J1 hJ1 => hJ1 (0, xs) m ⟨Nat.zero_le _, rfl, fun _ hk => by omega, fun _ _ => rfl, hm⟩)
    ?_
  rintro J1 ⟨i, cur⟩ m1 ⟨hi, hcl, hpre, hsuf, hm1⟩ ih1
  rw [Blocks.get_here]; dsimp only at *
  have hi_toNat : (BitVec.ofNat 64 i).toNat = i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hi1_toNat : (BitVec.ofNat 64 i + (1 : BitVec 64)).toNat = i + 1 := by
    rw [BitVec.toNat_add, hi_toNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hi2_toNat : (BitVec.ofNat 64 i + (2 : BitVec 64)).toNat = i + 2 := by
    rw [BitVec.toNat_add, hi_toNat, show (2 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hi3_toNat : (BitVec.ofNat 64 i + (3 : BitVec 64)).toNat = i + 3 := by
    rw [BitVec.toNat_add, hi_toNat, show (3 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hi4_toNat : (BitVec.ofNat 64 i + (4 : BitVec 64)).toNat = i + 4 := by
    rw [BitVec.toNat_add, hi_toNat, show (4 : BitVec 64).toNat = 4 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  c0_hsplit
  · have hle : i + 4 ≤ n.toNat := by
      have h1 : (BitVec.ofNat 64 i + (4 : BitVec 64)).toNat ≤ n.toNat := by c0_bound
      omega
    have h0 : (BitVec.ofNat 64 i).toNat < cur.length := by omega
    have h1 : (BitVec.ofNat 64 i + (1 : BitVec 64)).toNat <
        (cur.set (BitVec.ofNat 64 i).toNat val).length := by simp [hcl]; omega
    have h2 : (BitVec.ofNat 64 i + (2 : BitVec 64)).toNat <
        ((cur.set (BitVec.ofNat 64 i).toNat val).set
          (BitVec.ofNat 64 i + (1 : BitVec 64)).toNat val).length := by
      simp [hcl]; omega
    have h3 : (BitVec.ofNat 64 i + (3 : BitVec 64)).toNat <
        (((cur.set (BitVec.ofNat 64 i).toNat val).set
          (BitVec.ofNat 64 i + (1 : BitVec 64)).toNat val).set
          (BitVec.ofNat 64 i + (2 : BitVec 64)).toNat val).length := by
      simp [hcl]; omega
    c0_hsteps
    have hst : BitVec.ofNat 64 i + (4 : BitVec 64) = BitVec.ofNat 64 (i + 4) := by
      apply BitVec.eq_of_toNat_eq; rw [hi4_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hst]
    have hinv4 := fill_unroll4_inv hcl (by omega) hpre hsuf
    have hcur4 :
        (((cur.set (BitVec.ofNat 64 i).toNat val).set
            (BitVec.ofNat 64 i + (1 : BitVec 64)).toNat val).set
            (BitVec.ofNat 64 i + (2 : BitVec 64)).toNat val).set
            (BitVec.ofNat 64 i + (3 : BitVec 64)).toNat val =
        (((cur.set i val).set (i + 1) val).set (i + 2) val).set (i + 3) val := by
      rw [hi_toNat, hi1_toNat, hi2_toNat, hi3_toNat]
    refine ih1 (i + 4, _) _ (by omega) ⟨hle, hinv4.1, hinv4.2.1, hinv4.2.2, ?_⟩
    rw [← hcur4]; exact (by assumption)
  · have hgt : n.toNat < i + 4 := by
      have h1 : n.toNat < (BitVec.ofNat 64 i + (4 : BitVec 64)).toNat := by c0_bound
      omega
    refine wp_while_state1 (α := Nat × List (BitVec 64)) (proj := fun st => BitVec.ofNat 64 st.1)
      (μ := fun st => n.toNat - st.1)
      (Inv := fun st m' => st.1 ≤ n.toNat ∧ st.2.length = xs.length ∧
        (∀ k < st.1, st.2[k]? = some val) ∧ (∀ k, st.1 ≤ k → st.2[k]? = xs[k]?) ∧
        (array64 dst st.2 ⋆ R) m')
      (fun J2 hJ2 => hJ2 (i, cur) m1 ⟨hi, hcl, hpre, hsuf, hm1⟩) ?_
    rintro J2 ⟨j, cur2⟩ m2 ⟨hj, hcl2, hpre2, hsuf2, hm2⟩ ih2
    rw [Blocks.get_here]; dsimp only at *
    have hj_toNat : (BitVec.ofNat 64 j).toNat = j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    c0_hsplit
    · have hj_lt : j < n.toNat := by rw [← hj_toNat]; c0_bound
      have hj_arr : (BitVec.ofNat 64 j).toNat < cur2.length := by omega
      c0_hsteps
      have hst : BitVec.ofNat 64 j + (1 : BitVec 64) = BitVec.ofNat 64 (j + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, hj_toNat, show (1 : BitVec 64).toNat = 1 from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hst]
      have hinv2 := fill_step_inv hcl2 (by omega) hpre2 hsuf2
      have hcur1 : cur2.set (BitVec.ofNat 64 j).toNat val = cur2.set j val := by rw [hj_toNat]
      refine ih2 (j + 1, cur2.set j val) _ (by omega)
        ⟨by omega, by simp [hcl2], hinv2.1, hinv2.2, ?_⟩
      rw [← hcur1]; exact (by assumption)
    · have hj_ge : n.toNat ≤ j := by rw [← hj_toNat]; c0_bound
      have hj_eq : j = n.toNat := by omega
      c0_hsteps
      apply hpost m2
      have hcur_eq := fill_list_eq_replicate_append hn hcl2 (hj_eq ▸ hpre2) (hj_eq ▸ hsuf2)
      rwa [← hcur_eq]

private theorem list_count_set32 (xs : List (BitVec 32)) (k : Nat) (v a : BitVec 32)
    (hk : k < xs.length) :
    (xs.set k v).count a + (if xs[k] == a then 1 else 0) =
      xs.count a + (if v == a then 1 else 0) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.count_cons, List.getElem_cons_zero]
      by_cases hx : x == a <;> by_cases hv : v == a <;> simp [hx, hv] <;> omega
    | succ k =>
      have hk' : k < xs.length := by simpa using hk
      have ihk := ih k hk'
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ] at *
      omega

private theorem list_swap_set_perm (xs : List (BitVec 32)) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (v : BitVec 32) :
    ((xs.set i (xs[j]'hj)).set j v).Perm (xs.set i v) := by
  by_cases heq : i = j
  · subst j; simp
  · refine List.perm_iff_count.mpr fun a => ?_
    have c1 := list_count_set32 xs i v a hi
    have c2 := list_count_set32 xs i (xs[j]'hj) a hi
    have c3 := list_count_set32 (xs.set i (xs[j]'hj)) j v a (by simp [hj])
    have hget : (xs.set i (xs[j]'hj))[j]'(by simp [hj]) = xs[j]'hj :=
      List.getElem_set_ne heq (by simp [hj])
    rw [hget] at c3
    omega

private theorem list_take_set_lt {α : Type} (xs : List α) {i n : Nat} (v : α) (hi : i < n) :
    (xs.set i v).take n = (xs.take n).set i v := by
  induction xs generalizing i n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero => simp
      | succ i => rw [List.set_cons_succ, List.take_succ_cons, List.take_succ_cons,
          List.set_cons_succ, ih (by omega)]

private theorem list_set_getElem_self {α : Type} (xs : List α) {i : Nat} (hi : i < xs.length) :
    xs.set i (xs[i]'hi) = xs := by
  apply List.ext_getElem (by simp)
  intro k _ _
  by_cases hne : i = k
  · subst hne; simp
  · rw [List.getElem_set_ne hne]

private def SortInv (arr cur : List (BitVec 32)) (n : Nat) : Prop :=
  cur.length = arr.length ∧ List.Perm (cur.take n) (arr.take n) ∧
  ∀ k, n ≤ k → cur[k]? = arr[k]?

private theorem sortInv_swap01 {xs : List (BitVec 32)} (h2 : 2 ≤ xs.length) :
    SortInv xs ((xs.set 0 (xs[1]'(by omega))).set 1 (xs[0]'(by omega))) 2 := by
  refine ⟨by simp, ?_, fun k hk => ?_⟩
  · rw [list_take_set_lt _ _ (by decide), list_take_set_lt _ _ (by decide)]
    have hlen : (xs.take 2).length = 2 := by simp [h2]
    have h0 : 0 < (xs.take 2).length := by omega
    have h1 : 1 < (xs.take 2).length := by omega
    have hx1 : xs[1]'(by omega) = (xs.take 2)[1]'h1 := by simp [List.getElem_take]
    have hperm := list_swap_set_perm (xs.take 2) h0 h1 (xs[0]'(by omega))
    have hid : (xs.take 2).set 0 (xs[0]'(by omega)) = xs.take 2 := by
      apply List.ext_getElem (by simp)
      intro k _ _
      by_cases hk0 : 0 = k
      · subst hk0; simp [List.getElem_take]
      · rw [List.getElem_set_ne hk0]
    rw [hx1]; rw [hid] at hperm; exact hperm
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem sortInv_shift {xs cur : List (BitVec 32)} {n j j' : Nat} {x : BitVec 32}
    (hn : n ≤ xs.length) (hcur : cur.length = xs.length) (hj : j < n) (hjp : j' < n)
    (hperm : List.Perm ((cur.set j x).take n) (xs.take n))
    (hsuf : ∀ k, n ≤ k → cur[k]? = xs[k]?) :
    let cur' := cur.set j (cur[j']'(by omega))
    cur'.length = xs.length ∧ List.Perm ((cur'.set j' x).take n) (xs.take n) ∧
    ∀ k, n ≤ k → cur'[k]? = xs[k]? := by
  refine ⟨by simp [hcur], ?_, fun k hk => ?_⟩
  · rw [list_take_set_lt _ _ hjp, list_take_set_lt _ _ hj]
    have hlen : (cur.take n).length = n := by simp [hcur, hn]
    have hx : cur[j']'(by omega) = (cur.take n)[j']'(by rw [hlen]; omega) := by
      simp [List.getElem_take]
    have hp := list_swap_set_perm (cur.take n) (i := j) (j := j')
      (by rw [hlen]; omega) (by rw [hlen]; omega) x
    rw [← hx] at hp
    rw [← list_take_set_lt cur x hj] at hp
    exact hp.trans hperm
  · rw [List.getElem?_set_ne (by omega)]; exact hsuf k hk

private def SortGoPost (xs : List (BitVec 32)) (a : BitVec 64) (R : Mem 64 → Prop)
    (n j : Nat) (x : BitVec 32) (p : Tup Val [i64, .bool]) (m' : Mem 64) : Prop :=
  ∃ cur' : List (BitVec 32),
    (if p.2.1 then p.1.toNat + 1 else 0) < j + 1 ∧ p.1.toNat < n ∧
    cur'.length = xs.length ∧ List.Perm ((cur'.set p.1.toNat x).take n) (xs.take n) ∧
    (∀ k, n ≤ k → cur'[k]? = xs[k]?) ∧ (array (t := i32) a cur' ⋆ R) m'

theorem full_sort_u32_wp (Γ : Env) :
    ∀ a m Q X, fullSortU32Spec a m Q X → Func.wp Γ full_sort_u32_body a m Q X := by
  rintro ⟨a, n, ⟨⟩⟩ m Q X ⟨xs, R, hn, hm, hQ⟩
  have hlen64 : (n.setWidth 64).toNat = n.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans n.isLt (by decide))]
  unfold Func.wp full_sort_u32_body
  c0_hstraight
  c0_hsplit
  · c0_hsteps
    exact hQ xs m rfl (List.Perm.refl _) (fun _ _ => rfl) hm
  · have hn2 : 2 ≤ n.toNat := by
      have h1 : ¬ (n.setWidth 64).toNat ≤ 1 := by c0_bound
      omega
    c0_hstraight
    c0_hsplit
    · have h0 : (BitVec.ofNat 64 0).toNat < xs.length := by rw [BitVec.toNat_ofNat]; omega
      have h1 : (BitVec.ofNat 64 1).toNat < xs.length := by rw [BitVec.toNat_ofNat]; omega
      have hn_eq : n.toNat = 2 := by
        have h1 : (n.setWidth 64).toNat = 2 := by c0_bound
        omega
      rw [hn_eq] at hQ
      c0_hstraight
      refine wp_join_group (ts := []) (fun _ m1 =>
          ∃ arr1 : List (BitVec 32), arr1.length = xs.length ∧
            List.Perm (arr1.take 2) (xs.take 2) ∧ (∀ k, 2 ≤ k → arr1[k]? = xs[k]?) ∧
            (array (t := i32) a arr1 ⋆ R) m1) ?_ ?_
      · rintro _ ⟨⟩ m1 ⟨arr1, hlen1, hp1, hsuf1, hm1⟩
        c0_hsteps
        exact hQ arr1 m1 hlen1 hp1 hsuf1 hm1
      · intro J2 hJ2
        c0_hstraight
        c0_hsplit
        · have h1' : (BitVec.ofNat 64 1).toNat <
              (xs.set (BitVec.ofNat 64 0).toNat (xs[(BitVec.ofNat 64 1).toNat]'h1)).length := by
            simp; omega
          c0_hsteps
          have hinv := sortInv_swap01 (by omega : 2 ≤ xs.length)
          exact hJ2 () _ ⟨_, hinv.1, hinv.2.1, hinv.2.2, (by assumption)⟩
        · c0_hsteps
          exact hJ2 () m ⟨xs, rfl, List.Perm.refl _, fun _ _ => rfl, hm⟩
    · c0_hstraight
      refine wp_join_group (ts := [i64]) (fun _ m1 => m1 = m) ?_ ?_
      · rintro _ ⟨gap0, ⟨⟩⟩ m1 hm1
        subst m1
        c0_hsteps_nogrp
        refine wp_while_state (ts := [i64]) (α := BitVec 64 × List (BitVec 32))
          (proj := fun st => (st.1, ())) (μ := fun st => st.1.toNat)
          (Inv := fun st m2 => SortInv xs st.2 n.toNat ∧ (array (t := i32) a st.2 ⋆ R) m2)
          (fun Jg hJg => hJg (gap0, xs) m
            ⟨⟨rfl, List.Perm.refl _, fun _ _ => rfl⟩, hm⟩) ?_
        rintro Jg ⟨gap, cur⟩ m2 ⟨⟨hcl, hperm, hsuf⟩, hm2⟩ ihg
        rw [Blocks.get_here]; dsimp only at *
        c0_hsteps_nogrp
        · have hgap1 : 1 ≤ gap.toNat := by c0_bound
          refine wp_while_state (ts := [i64]) (α := BitVec 64 × List (BitVec 32))
            (proj := fun st => (st.1, ())) (μ := fun st => n.toNat - st.1.toNat)
            (Inv := fun st m3 =>
              gap.toNat ≤ st.1.toNat ∧ SortInv xs st.2 n.toNat ∧
              (array (t := i32) a st.2 ⋆ R) m3)
            (fun Ji hJi => hJi (gap, cur) m2
              ⟨by dsimp only; exact Nat.le_refl _, ⟨hcl, hperm, hsuf⟩, hm2⟩) ?_
          rintro Ji ⟨i, cur1⟩ m3 ⟨hgi, ⟨hcl1, hperm1, hsuf1⟩, hm3⟩ ihi
          rw [Blocks.get_here]; dsimp only at *
          c0_hsteps_nogrp
          · have hi_lt : i.toNat < n.toNat := by
              have h1 : i.toNat < (n.setWidth 64).toNat := by c0_bound
              omega
            have hi_arr : i.toNat < cur1.length := by omega
            c0_hsteps_nogrp
            let x := cur1[i.toNat]'hi_arr
            refine wp_while_state (ts := [i64, .bool])
              (α := BitVec 64 × Bool × List (BitVec 32))
              (proj := fun st => (st.1, st.2.1, ()))
              (μ := fun st => if st.2.1 then st.1.toNat + 1 else 0)
              (Inv := fun st m4 =>
                st.1.toNat < n.toNat ∧ st.2.2.length = xs.length ∧
                List.Perm ((st.2.2.set st.1.toNat x).take n.toNat) (xs.take n.toNat) ∧
                (∀ k, n.toNat ≤ k → st.2.2[k]? = xs[k]?) ∧
                (array (t := i32) a st.2.2 ⋆ R) m4)
              (fun Jj hJj => hJj (i, true, cur1) m3 ⟨hi_lt, hcl1, by
                rw [list_set_getElem_self cur1 hi_arr]; exact hperm1, hsuf1, hm3⟩) ?_
            rintro Jj ⟨j, go, cur2⟩ m4 ⟨hjn, hcl2, hperm2, hsuf2, hm4⟩ ihj
            rw [Blocks.get_here]; dsimp only at *
            c0_hsteps_nogrp
            · refine wp_join_group (ts := [i64, .bool])
                (SortGoPost xs a R n.toNat j.toNat x) ?_ ?_
              · rintro _ ⟨j', go', ⟨⟩⟩ m' ⟨cur', hdec, hjn', hcl', hp', hs', hm'⟩
                c0_hsteps
                exact ihj (j', go', cur') m'
                  (by dsimp only at hdec ⊢; have hgo : go = true := by assumption
                      rw [ite_eq_left hgo]; exact hdec)
                  ⟨hjn', hcl', hp', hs', hm'⟩
              · intro J2 hJ2
                c0_hsteps_nogrp
                c0_hsplit
                · c0_hsteps
                  exact hJ2 (j, false, ()) m4 ⟨cur2, by simp, hjn, hcl2, hperm2, hsuf2, hm4⟩
                · have hgj : gap.toNat ≤ j.toNat := by c0_bound
                  have hjp_toNat : (j - gap).toNat = j.toNat - gap.toNat :=
                    BitVec.toNat_sub_of_le (BitVec.le_def.mpr hgj)
                  have hjp_lt : (j - gap).toNat < cur2.length := by omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, .bool])
                    (SortGoPost xs a R n.toNat j.toNat x) ?_ ?_
                  · rintro _ ⟨j', go', ⟨⟩⟩ m' hpost'
                    c0_hsteps
                    exact hJ2 (j', go', ()) m' hpost'
                  · intro J3 hJ3
                    c0_hsteps_nogrp
                    c0_hsplit
                    · c0_hsteps
                      exact hJ3 (j, false, ()) m4 ⟨cur2, by simp, hjn, hcl2, hperm2, hsuf2, hm4⟩
                    · have hj_arr : j.toNat < cur2.length := by omega
                      c0_hsteps
                      have hinv' := sortInv_shift (j' := (j - gap).toNat) hn hcl2 hjn
                        (by omega) hperm2 hsuf2
                      exact hJ3 (j - gap, go, ()) _
                        ⟨cur2.set j.toNat (cur2[(j - gap).toNat]'hjp_lt),
                          by dsimp only; rw [ite_eq_left (by assumption), hjp_toNat]; omega,
                          by rw [hjp_toNat]; omega,
                          hinv'.1, hinv'.2.1, hinv'.2.2, (by assumption)⟩
            · have hj_arr : j.toNat < cur2.length := by omega
              c0_hsteps
              have hsuf' : ∀ k, n.toNat ≤ k → (cur2.set j.toNat x)[k]? = xs[k]? := by
                intro k hk; rw [List.getElem?_set_ne (by omega)]; exact hsuf2 k hk
              have hi1_toNat : (i + 1#64).toNat = i.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by have := n.isLt; omega)]
              exact ihi (i + 1#64, cur2.set j.toNat x) _
                (by rw [hi1_toNat]; omega)
                ⟨by rw [hi1_toNat]; omega, ⟨by simp [hcl2], hperm2, hsuf'⟩, (by assumption)⟩
          · c0_hsteps
            have hdiv_lt : (gap / 3#64).toNat < gap.toNat := by
              rw [BitVec.toNat_udiv, show (3#64 : BitVec 64).toNat = 3 from rfl]
              exact Nat.div_lt_self hgap1 (by decide)
            exact ihg (gap / 3#64, cur1) m3 hdiv_lt ⟨⟨hcl1, hperm1, hsuf1⟩, hm3⟩
        · c0_hsteps
          exact hQ cur m2 hcl hperm hsuf hm2
      · intro Jgap hJgap
        c0_hsteps_nogrp
        c0_hsplit
        · c0_hsteps_nogrp
          refine wp_while_state1 (α := BitVec 64) (proj := id)
            (μ := fun g => n.toNat / 3 - g.toNat)
            (Inv := fun g m1 => m1 = m ∧ g.toNat < 2 ^ 32)
            (fun Jw hJw => hJw 1#64 m ⟨rfl, by decide⟩) ?_
          rintro Jw g m1 ⟨hm1, hg32⟩ ihw
          subst m1
          rw [Blocks.get_here]; dsimp only at *
          c0_hsteps_nogrp
          · have hglim : g.toNat < (n.setWidth 64 / 3#64).toNat := by c0_bound
            have hlim_eq : (n.setWidth 64 / 3#64).toNat = n.toNat / 3 := by
              rw [BitVec.toNat_udiv, hlen64]; rfl
            have hpow : 2 ^ 32 * 3 + 1 < 2 ^ 64 := by decide
            have hm1 : g.toNat * 3 < 2 ^ 64 := by omega
            have hg3_eq : (g * 3#64).toNat = 3 * g.toNat := by
              rw [BitVec.toNat_mul, show (3#64 : BitVec 64).toNat = 3 from rfl,
                Nat.mod_eq_of_lt hm1]; omega
            have hm2 : (g * 3#64).toNat + 1 < 2 ^ 64 := by omega
            have hg1_eq : (g * 3#64 + 1#64).toNat = 3 * g.toNat + 1 := by
              rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt hm2, hg3_eq]
            c0_hsteps
            have hgn : g.toNat < n.toNat / 3 := hlim_eq ▸ hglim
            exact ihw (g * 3#64 + 1#64) m (by rw [hg1_eq]; omega)
              ⟨rfl, by rw [hg1_eq]; have := n.isLt; omega⟩
          · c0_hsteps
            exact hJgap (g, ()) m rfl
        · c0_hsteps
          exact hJgap (1#64, ()) m rfl

/-! ## Section 4: M7 LCG, GlueUsed Accessors, Init, and EMA Swap -/

theorem full_lcg_next_m7_wp (Γ : Env) :
    ∀ a m Q X, m7LcgNextSpec a m Q X → Func.wp Γ full_lcg_next_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp full_lcg_next_m7_body
  c0_hsteps
  exact hQ _ (by assumption)

theorem full_m7_get64_wp (Γ : Env) :
    ∀ a m Q X, m7Get64Spec a m Q X → Func.wp Γ full_m7_get64_body a m Q X := by
  rintro ⟨h, idx, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hgl : s.scratch.glue_used.length = 64 := hlen.scratch_ok.glue_used_len
  unfold Func.wp full_m7_get64_body
  c0_hsteps_nogrp
  · have hge : ¬ idx.toNat < 63 := by
      have : (63#64 : BitVec 64).toNat = 63 := rfl
      have h1 : (63#64 : BitVec 64).toNat ≤ idx.toNat := by c0_bound
      omega
    rw [ite_eq_right hge] at hQ; exact hQ
  · have hlt : idx.toNat < 63 := by
      have : (63#64 : BitVec 64).toNat = 63 := rfl
      have h1 : ¬ (63#64 : BitVec 64).toNat ≤ idx.toNat := by c0_bound
      omega
    have hidx0 : idx.toNat < s.scratch.glue_used.length := by omega
    have hidx1 : (idx + (1 : BitVec 64)).toNat < s.scratch.glue_used.length := by
      rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]; omega
    c0_hsteps
    have heq : (idx + (1 : BitVec 64)).toNat = idx.toNat + 1 := by
      rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left hlt] at hQ
    have hget1 : s.scratch.glue_used[idx.toNat + 1]? =
        some (s.scratch.glue_used[(idx + (1 : BitVec 64)).toNat]'hidx1) := by
      rw [← heq]; exact List.getElem?_eq_getElem hidx1
    unfold m7Get64Val u64Of32Pair at hQ
    rw [List.getElem?_eq_getElem hidx0, hget1, Option.getD_some, Option.getD_some] at hQ
    exact hQ

theorem full_m7_set64_wp (Γ : Env) :
    ∀ a m Q X, m7Set64Spec a m Q X → Func.wp Γ full_m7_set64_body a m Q X := by
  rintro ⟨h, idx, val, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hgl : s.scratch.glue_used.length = 64 := hlen.scratch_ok.glue_used_len
  unfold Func.wp full_m7_set64_body
  c0_hsteps_nogrp
  · have hge : ¬ idx.toNat < 63 := by
      have : (63#64 : BitVec 64).toNat = 63 := rfl
      have h1 : (63#64 : BitVec 64).toNat ≤ idx.toNat := by c0_bound
      omega
    rw [ite_eq_right hge] at hQ; exact hQ m hm
  · have hlt : idx.toNat < 63 := by
      have : (63#64 : BitVec 64).toNat = 63 := rfl
      have h1 : ¬ (63#64 : BitVec 64).toNat ≤ idx.toNat := by c0_bound
      omega
    have hidx0 : idx.toNat < s.scratch.glue_used.length := by omega
    have hidx1 : (idx + (1 : BitVec 64)).toNat <
        (s.scratch.glue_used.set idx.toNat (val.setWidth 32)).length := by
      rw [List.length_set, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]; omega
    c0_hsteps
    have heq : (idx + (1 : BitVec 64)).toNat = idx.toNat + 1 := by
      rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left hlt] at hQ
    dsimp only at hQ
    refine hQ _ ?_
    unfold m7Set64List; rw [← heq]
    exact (by assumption)

private def M7StepInv (c : FullCfg) (s s' : FullState) : Prop :=
  s'.core = s.core ∧ s'.LengthsOk c ∧ FullExtScratchPres s s' ∧
  M7GuPrefixPres s s' ∧ M7StateInitOk s'.scratch.glue_used

private def m7UpdGu (s : FullState) (idx : Nat) (val : BitVec 64) : FullState :=
  { s with scratch := { s.scratch with glue_used := m7Set64List s.scratch.glue_used idx val } }

private theorem m7UpdGu_lengths {c : FullCfg} {s : FullState} (idx : Nat) (val : BitVec 64)
    (hlen : s.LengthsOk c) : (m7UpdGu s idx val).LengthsOk c :=
  ⟨hlen.core_ok,
    { hlen.scratch_ok with
      glue_used_len := by
        unfold m7UpdGu; rw [m7Set64List_length]; exact hlen.scratch_ok.glue_used_len }⟩

private theorem m7StepInv_upd {c : FullCfg} {s s1 : FullState} (idx : Nat) (val : BitVec 64)
    (hinv : M7StepInv c s s1) (hlo : 38 ≤ idx) (hhi : idx < 63) :
    M7StepInv c s (m7UpdGu s1 idx val) := by
  obtain ⟨hcore, hlen, hext, hpre, hinit⟩ := hinv
  refine ⟨hcore, m7UpdGu_lengths idx val hlen, ⟨hext.1, hext.2⟩,
    hpre.trans fun k hk => by unfold m7UpdGu; exact m7Set64List_get_lt val (by omega),
    by unfold m7UpdGu; exact hinit.of_set64 hlo val⟩

private theorem m7_mem_of_set64_lt {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    {idx : BitVec 64} {n : Nat} {val : BitVec 64} (hn : idx.toNat = n) (hlt : n < 63)
    (h : (FullMem c
      { s with
        scratch :=
          { s.scratch with
            glue_used := if idx.toNat < 63 then m7Set64List s.scratch.glue_used idx.toNat val
                         else s.scratch.glue_used } } ⋆ R) m') :
    (FullMem c (m7UpdGu s n val) ⋆ R) m' := by
  rw [hn, ite_eq_left hlt] at h
  exact h

private theorem m7_hset_step {c : FullCfg} {s s1 : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    {idx : BitVec 64} (n : Nat) {val : BitVec 64}
    (hn : idx.toNat = n) (hlo : 38 ≤ n) (hhi : n < 63) (hinv : M7StepInv c s s1)
    (h : (FullMem c
      { s1 with
        scratch :=
          { s1.scratch with
            glue_used := if idx.toNat < 63 then m7Set64List s1.scratch.glue_used idx.toNat val
                         else s1.scratch.glue_used } } ⋆ R) m') :
    ∃ s2 : FullState, M7StepInv c s s2 ∧ (FullMem c s2 ⋆ R) m' :=
  ⟨m7UpdGu s1 n val, m7StepInv_upd n val hinv hlo hhi, m7_mem_of_set64_lt hn hhi h⟩

local macro "m7_set_step" hSet:ident c:ident R:ident sPrev:ident hInv:ident "," hmPrev:term ","
    idx:term "," hlo:term "," hhi:term "," sNext:ident hNext:ident hmNext:ident mNext:ident :
    tactic =>
  `(tactic| (
    c0_hsteps_nogrp; c0_call $hSet
    refine ⟨$c, $sPrev, $R, rfl, $hInv.2.1, $hmPrev, fun $mNext h_step_m => ?_⟩
    obtain ⟨$sNext, $hNext, $hmNext⟩ := m7_hset_step $idx rfl $hlo $hhi $hInv h_step_m))

local macro "m7_set_lit" hSet:ident c:ident R:ident sPrev:ident hInv:ident "," hmPrev:term ","
    k:num "," sNext:ident hNext:ident hmNext:ident mNext:ident : tactic =>
  `(tactic| m7_set_step $hSet $c $R $sPrev $hInv, $hmPrev, $k, (by decide), (by decide),
      $sNext $hNext $hmNext $mNext)

local macro "m7_set4_lit" hSet:ident c:ident R:ident s0:ident h0:ident hm0:ident
    k0:num k1:num k2:num k3:num s4:ident h4:ident hm4:ident m4:ident : tactic =>
  `(tactic| (
    m7_set_lit $hSet $c $R $s0 $h0, $hm0, $k0, s_a h_a hm_a m_a
    m7_set_lit $hSet $c $R s_a h_a, hm_a, $k1, s_b h_b hm_b m_b
    m7_set_lit $hSet $c $R s_b h_b, hm_b, $k2, s_c h_c hm_c m_c
    m7_set_lit $hSet $c $R s_c h_c, hm_c, $k3, $s4 $h4 $hm4 $m4))

local macro "m7_set4_off" hSet:ident c:ident R:ident s0:ident h0:ident "," hm0:term ","
    b:ident hb:ident s4:ident h4:ident hm4:ident m4:ident : tactic =>
  `(tactic| (
    m7_set_step $hSet $c $R $s0 $h0, $hm0, ($b).toNat, $hb.1, $hb.2.1, s_a h_a hm_a m_a
    m7_set_step $hSet $c $R s_a h_a, hm_a, ($b + 2#64).toNat, $hb.2.2.1, $hb.2.2.2.1,
      s_b h_b hm_b m_b
    m7_set_step $hSet $c $R s_b h_b, hm_b, ($b + 4#64).toNat,
      $hb.2.2.2.2.1, $hb.2.2.2.2.2.1, s_c h_c hm_c m_c
    m7_set_step $hSet $c $R s_c h_c, hm_c, ($b + 6#64).toNat,
      $hb.2.2.2.2.2.2.1, $hb.2.2.2.2.2.2.2, $s4 $h4 $hm4 $m4))

theorem full_m7_state_init_wp (Γ : Env)
    (hGet : Γ.Has "full_m7_get64" m7Get64Spec)
    (hSet : Γ.Has "full_m7_set64" m7Set64Spec) :
    ∀ a m Q X, step13M7StateInitSpec a m Q X → Func.wp Γ full_m7_state_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm
  unfold Func.wp full_m7_state_init_body
  c0_hsteps_nogrp
  c0_call hGet
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  c0_hsteps_nogrp
  c0_hsplit
  · have hmag : m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic := by
      have h1 : (if (36#64 : BitVec 64).toNat < 63 then
          m7Get64Val s.scratch.glue_used (36#64 : BitVec 64).toNat else 0#64) =
          m7SearchMagic := by assumption
      rw [ite_eq_left (by decide)] at h1
      exact h1
    c0_hsteps
    exact hQ () s m rfl hlen ⟨⟨rfl, rfl⟩, M7GuPrefixPres.refl s,
      ⟨hlen.scratch_ok.glue_used_len, hmag⟩⟩ hm
  · c0_call hSet
    refine ⟨c, s, R, rfl, hlen, hm, fun m1 hm1 => ?_⟩
    let s1 : FullState := m7UpdGu s 36 m7SearchMagic
    have hm1' := m7_mem_of_set64_lt (n := 36) rfl (by decide) hm1
    have hinv1 : M7StepInv c s s1 :=
      ⟨rfl, m7UpdGu_lengths 36 m7SearchMagic hlen,
        ⟨rfl, rfl⟩, fun k hk => by unfold s1 m7UpdGu; exact m7Set64List_get_lt _ (by omega),
        ⟨by unfold s1 m7UpdGu; rw [m7Set64List_length]; exact hlen.scratch_ok.glue_used_len,
         by unfold s1 m7UpdGu
            exact m7Get64Val_set64_self _ (by rw [hlen.scratch_ok.glue_used_len]; decide)⟩⟩
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ())) (fun _ => True)
      ?_ ?_
    · rintro _ cm _
      m7_set_lit hSet c R s1 hinv1, hm1', 38, s2 hinv2 hm2' m2
      c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState) (fun st mt => M7StepInv c s st ∧ (FullMem c st ⋆ R) mt)
        (fun _ st mt ⟨hst, hmt⟩ => ?_) (fun Jbr hJbr => ?_)
      · m7_set4_lit hSet c R st hst hmt 56 58 60 62 st6 hst6 hm6' m6
        c0_hsteps
        exact hQ () st6 m6 hst6.1 hst6.2.1 ⟨hst6.2.2.1, hst6.2.2.2.1, hst6.2.2.2.2⟩ hm6'
      · c0_hsplit
        · m7_set4_lit hSet c R s2 hinv2 hm2' 40 42 44 46 sa3 ha3 hma3' ma3
          m7_set4_lit hSet c R sa3 ha3 hma3' 48 50 52 54 sa7 ha7 hma7' ma7
          c0_hsteps; exact hJbr _ ma7 ⟨ha7, hma7'⟩
        · m7_set4_lit hSet c R s2 hinv2 hm2' 48 50 52 54 sb3 hb3 hmb3' mb3
          m7_set4_lit hSet c R sb3 hb3 hmb3' 40 42 44 46 sb7 hb7 hmb7' mb7
          c0_hsteps; exact hJbr _ mb7 ⟨hb7, hmb7'⟩
    · intro Jcm hJcm; c0_hsteps <;> exact hJcm _ trivial

private theorem m7StepInv_updScratch {c : FullCfg} {s s1 s2 : FullState}
    (hc : s2.core = s1.core) (hok : s2.LengthsOk c)
    (hext : FullExtScratchPres s1 s2) (hgu : s2.scratch.glue_used = s1.scratch.glue_used)
    (hinv : M7StepInv c s s1) : M7StepInv c s s2 :=
  ⟨hc.trans hinv.1, hok, ⟨hext.1.trans hinv.2.2.1.1, hext.2.trans hinv.2.2.1.2⟩,
    fun k hk => by rw [hgu]; exact hinv.2.2.2.1 k hk,
    ⟨by rw [hgu]; exact hinv.2.2.2.2.1, by rw [hgu]; exact hinv.2.2.2.2.2⟩⟩

private def m7UpdStable (s : FullState) (st : BitVec 64) : FullState :=
  { s with scratch := { s.scratch with stable := st } }

private theorem m7UpdStable_lengths {c : FullCfg} {s : FullState} (st : BitVec 64)
    (hlen : s.LengthsOk c) : (m7UpdStable s st).LengthsOk c :=
  ⟨hlen.core_ok, by unfold m7UpdStable; cases hlen.scratch_ok; constructor <;> assumption⟩

private theorem m7_updEmaStep {c : FullCfg} {s s1 s2 : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    (hinv : M7StepInv c s s1) (h : (FullMem c s2 ⋆ R) m') (hc : s2.core = s1.core)
    (hext : FullExtScratchPres s1 s2) (hgu : s2.scratch.glue_used = s1.scratch.glue_used)
    (hok : s2.LengthsOk c) : ∃ st : FullState, M7StepInv c s st ∧ (FullMem c st ⋆ R) m' :=
  ⟨s2, m7StepInv_updScratch hc hok hext hgu hinv, h⟩

private theorem m7_updFb_step {c : FullCfg} {s s1 : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    {v : BitVec 64} (hinv : M7StepInv c s s1)
    (h : (FullMem c { s1 with scratch := { s1.scratch with ema_fast_biased := v } } ⋆ R) m') :
    ∃ s2 : FullState, M7StepInv c s s2 ∧ (FullMem c s2 ⋆ R) m' :=
  m7_updEmaStep hinv h rfl ⟨rfl, rfl⟩ rfl
    ⟨hinv.2.1.core_ok, by cases hinv.2.1.scratch_ok; constructor <;> assumption⟩
private theorem m7_updFe_step {c : FullCfg} {s s1 : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    {v : BitVec 64} (hinv : M7StepInv c s s1)
    (h : (FullMem c { s1 with scratch := { s1.scratch with ema_fast_exp := v } } ⋆ R) m') :
    ∃ s2 : FullState, M7StepInv c s s2 ∧ (FullMem c s2 ⋆ R) m' :=
  m7_updEmaStep hinv h rfl ⟨rfl, rfl⟩ rfl
    ⟨hinv.2.1.core_ok, by cases hinv.2.1.scratch_ok; constructor <;> assumption⟩
private theorem m7_updSb_step {c : FullCfg} {s s1 : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    {v : BitVec 64} (hinv : M7StepInv c s s1)
    (h : (FullMem c { s1 with scratch := { s1.scratch with ema_slow_biased := v } } ⋆ R) m') :
    ∃ s2 : FullState, M7StepInv c s s2 ∧ (FullMem c s2 ⋆ R) m' :=
  m7_updEmaStep hinv h rfl ⟨rfl, rfl⟩ rfl
    ⟨hinv.2.1.core_ok, by cases hinv.2.1.scratch_ok; constructor <;> assumption⟩
private theorem m7_updSe_step {c : FullCfg} {s s1 : FullState} {R : Mem 64 → Prop} {m' : Mem 64}
    {v : BitVec 64} (hinv : M7StepInv c s s1)
    (h : (FullMem c { s1 with scratch := { s1.scratch with ema_slow_exp := v } } ⋆ R) m') :
    ∃ s2 : FullState, M7StepInv c s s2 ∧ (FullMem c s2 ⋆ R) m' :=
  m7_updEmaStep hinv h rfl ⟨rfl, rfl⟩ rfl
    ⟨hinv.2.1.core_ok, by cases hinv.2.1.scratch_ok; constructor <;> assumption⟩

private def m7UpdEma4 (s : FullState) (fb fe sb se : BitVec 64) : FullState :=
  { s with scratch := { s.scratch with
    ema_fast_biased := fb, ema_fast_exp := fe, ema_slow_biased := sb, ema_slow_exp := se } }

private theorem m7_base_lt63 {b : BitVec 64} (hb : b = 40#64 ∨ b = 48#64) :
    38 ≤ b.toNat ∧ b.toNat < 63 ∧
    38 ≤ (b + 2#64).toNat ∧ (b + 2#64).toNat < 63 ∧
    38 ≤ (b + 4#64).toNat ∧ (b + 4#64).toNat < 63 ∧
    38 ≤ (b + 6#64).toNat ∧ (b + 6#64).toNat < 63 := by
  rcases hb with rfl | rfl <;> decide

theorem full_ema_swap_m7_wp (Γ : Env)
    (hInit : Γ.Has "full_m7_state_init" step13M7StateInitSpec)
    (hGet : Γ.Has "full_m7_get64" m7Get64Spec)
    (hSet : Γ.Has "full_m7_set64" m7Set64Spec) :
    ∀ a m Q X, step13EmaSwapSpec a m Q X → Func.wp Γ full_ema_swap_m7_body a m Q X := by
  rintro ⟨h, old_m, new_m, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm
  unfold Func.wp full_ema_swap_m7_body
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ())) (fun _ => True)
    ?_ ?_
  · rintro _ om _
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ())) (fun _ => True)
      ?_ ?_
    · rintro _ nm _
      c0_hsteps_nogrp
      let s0 := m7UpdStable s om
      c0_call hInit
      refine ⟨c, s0, R, rfl, m7UpdStable_lengths om hlen, hm,
        fun _ s1 m1 hc1 hlen1 hpre1 hm1 => ?_⟩
      dsimp only [fullSafetySlice] at hc1 hlen1 hm1
      have hinv1 : M7StepInv c s s1 := ⟨hc1, hlen1, hpre1.1, hpre1.2.1, hpre1.2.2⟩
      c0_hsteps_nogrp
      have hinv2 : M7StepInv c s (m7UpdStable s1 nm) :=
        m7StepInv_updScratch (s1 := s1) (s2 := m7UpdStable s1 nm)
          rfl (m7UpdStable_lengths nm hlen1) ⟨rfl, rfl⟩ rfl hinv1
      let s2 := m7UpdStable s1 nm
      refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ()))
        (fun ob => ob = 40#64 ∨ ob = 48#64) ?_ ?_
      · rintro _ ob hob
        have hbr := m7_base_lt63 hob
        m7_set4_off hSet c R s2 hinv2, (by assumption), ob hbr so3 ho3 hmo3' mo3
        c0_hsteps_nogrp; c0_call hGet; refine ⟨c, so3, R, rfl, ho3.2.1, hmo3', ?_⟩
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ()))
          (fun nb => nb = 40#64 ∨ nb = 48#64) ?_ ?_
        · rintro _ nb hnb
          have hnbr := m7_base_lt63 hnb
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ mst =>
              ∃ st : FullState, M7StepInv c s st ∧ (FullMem c st ⋆ R) mst) ?_ ?_
          · rintro _ ⟨mask_out, ⟨⟩⟩ mst ⟨st, hst, hmst⟩
            m7_set_lit hSet c R st hst, hmst, 38, sf hsf hmf' mf
            c0_hsteps; exact hQ () sf mf hsf.1 hsf.2.1 ⟨hsf.2.2.1, hsf.2.2.2.1, hsf.2.2.2.2⟩ hmf'
          · intro Jm hJm
            c0_hsteps_nogrp
            c0_hsplit
            · c0_hsteps_nogrp; c0_call hGet; refine ⟨c, so3, R, rfl, ho3.2.1, hmo3', ?_⟩
              c0_hsteps_nogrp; obtain ⟨se1, he1, hme1⟩ := m7_updFb_step ho3 (by assumption)
              c0_call hGet; refine ⟨c, se1, R, rfl, he1.2.1, hme1, ?_⟩
              c0_hsteps_nogrp; obtain ⟨se2, he2, hme2⟩ := m7_updFe_step he1 (by assumption)
              c0_call hGet; refine ⟨c, se2, R, rfl, he2.2.1, hme2, ?_⟩
              c0_hsteps_nogrp; obtain ⟨se3, he3, hme3⟩ := m7_updSb_step he2 (by assumption)
              c0_call hGet; refine ⟨c, se3, R, rfl, he3.2.1, hme3, ?_⟩
              c0_hsteps_nogrp; obtain ⟨se4, he4, hme4⟩ := m7_updSe_step he3 (by assumption)
              c0_hsteps; exact hJm _ _ ⟨se4, he4, hme4⟩
            · c0_hsteps_nogrp
              let sn := m7UpdEma4 so3 0#64 m7EmaInitExp 0#64 m7EmaInitExp
              have hn0 : M7StepInv c s sn := m7StepInv_updScratch (s1 := so3) (s2 := sn) rfl
                ⟨ho3.2.1.core_ok, by
                  unfold sn m7UpdEma4; cases ho3.2.1.scratch_ok; constructor <;> assumption⟩
                ⟨rfl, rfl⟩ rfl ho3
              m7_set4_off hSet c R sn hn0, (by assumption), nb hnbr sn3 hsn3 hmn3' mn3
              c0_hsteps; exact hJm _ _ ⟨sn3, hsn3, hmn3'⟩
        · intro Jnb hJnb
          c0_hsteps <;> first | exact hJnb 40#64 (Or.inl rfl) | exact hJnb 48#64 (Or.inr rfl)
      · intro Job hJob
        c0_hsteps <;> first | exact hJob 40#64 (Or.inl rfl) | exact hJob 48#64 (Or.inr rfl)
    · intro Jnm hJnm; c0_hsteps <;> exact hJnm _ trivial
  · intro Jom hJom; c0_hsteps <;> exact hJom _ trivial

end LeanQbe.T.Examples.Kissat.Proof.Limits
