/-
Kraken - Helper Theorems

Small helper theorems for working with integer types.
Used by tactics and examples for simplification.
-/

import Kraken.Semantics

-- Immediate conversion simp lemmas
@[simp] theorem Int64_toUInt64_zero : Int64.toUInt64 0 = 0 := by native_decide
@[simp] theorem Int64_toUInt64_one : Int64.toUInt64 1 = 1 := by native_decide
@[simp] theorem Int64_toUInt64_two : Int64.toUInt64 2 = 2 := by native_decide
@[simp] theorem Int64_toUInt64_zero_toNat : (Int64.toUInt64 0).toNat = 0 := by native_decide
@[simp] theorem Int64_toUInt64_one_toNat : (Int64.toUInt64 1).toNat = 1 := by native_decide
@[simp] theorem Int64_toUInt64_two_toNat : (Int64.toUInt64 2).toNat = 2 := by native_decide

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
-- Heap Region Helpers
-- ============================================================================

/-- Asserts that a contiguous region of n 64-bit words starting at addr exists in the heap.
    Each word is at addr, addr+8, addr+16, ..., addr+(n-1)*8 -/
def heapRegionValid (s : MachineState) (addr : UInt64) (n : Nat) : Prop :=
  ∀ i : Nat, i < n → (s.heap[addr + i.toUInt64 * 8]?).isSome
