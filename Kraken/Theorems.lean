/-
Kraken - Helper Theorems
-/

import Kraken.Semantics
import Kraken.Tactics

-- UInt64.ofInt (k : Int) ≠ 0 when k is a natural number with k < 2^64 and k ≠ 0
-- This proof uses only core Lean lemmas (no Batteries/Mathlib)
theorem UInt64_ofInt_natCast_ne_zero (k : Nat) (h_lt : k < 2^64) (h_ne : k ≠ 0) :
    UInt64.ofInt (k : Int) ≠ 0 := by
  simp only [UInt64.ofInt, ne_eq]
  intro h
  have h1 := congrArg UInt64.toNat h
  simp only [UInt64.toNat_ofNat] at h1
  -- Int mod to Nat conversion
  have h_klt : (k : Int) < 2^64 := Int.ofNat_lt.mpr h_lt
  have h_mod : (↑k : Int) % (2^64 : Int) = k := Int.emod_eq_of_lt (Int.natCast_nonneg k) h_klt
  conv at h1 => lhs; rw [show (↑k : Int) % (2^64 : Int) = ↑k from h_mod]
  simp only [Int.toNat_natCast] at h1
  -- h1: (UInt64.ofNat k).toNat = 0 % 2^64
  have h2 : (UInt64.ofNat k).toNat = k % 2^64 := UInt64.toNat_ofNat
  have hkmod : k % 2^64 = k := Nat.mod_eq_of_lt h_lt
  have hzero : (0 : Nat) % 2^64 = 0 := Nat.zero_mod (2^64)
  rw [h2, hkmod, hzero] at h1
  exact h_ne h1

-- ============================================================================
-- Omnisemantics Step Mixing (And soundness of straightline instantiation)
-- ============================================================================

theorem eventually_straightline_to_step1 [Layout] (p: Executable) (initial: MachineState) (post: Post)
  (h: Eventually (straightlineStep p) post initial):
  Eventually (step1 p) post initial := by
    sorry
