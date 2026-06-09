/-
Kraken - Helper Theorems
-/

import Kraken.Semantics
import Kraken.Syntax

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

theorem simpleAlignedStore64 (s : MachineData) (addr : BitVec 64) (v : BitVec 64) (ret: MachineData → Effects)
  (hAligned: addr % 8 = 0)
  (hContains: UInt64.ofBitVec addr ∈ s.dmem):
  MachineData.store s addr v ret =
  require_write_access addr Width.W64 (fun _unit =>
    ret { s with dmem := s.dmem.insert (UInt64.ofBitVec addr) (UInt64.ofBitVec v) }) :=
by
  simp only [MachineData.store,Width.bytesv,Width.bytes]
  have: addr % 8#64 = 0#64 := by grind
  simp only [this]
  have: UInt64.ofBitVec (addr &&& ~~~0b111#64) = UInt64.ofBitVec addr := by
    bv_decide
  rw [this]
  have: addr &&& 7#64 = 0 := by bv_decide
  simp [this,Width.bits]
  -- TODO: lift and generalize this
  have (old v: BitVec 64): BitVec.replace old 0 v = v := by
    simp [BitVec.replace,BitVec.drop]
    bv_decide
  simp [this]
  rw [Std.ExtHashMap.getElem?_eq_some_getElem! hContains]

-- AE, JP: it would be nice to eliminate CPS from the post and say that the post
-- is just called with the value that is loaded
theorem simpleAlignedLoad64 (s : MachineData) (addr : BitVec 64) (ret: BitVec 64 → MachineData → Effects)
  (hAligned: addr % 8 = 0)
  (hContains: UInt64.ofBitVec addr ∈ s.dmem):
  MachineData.load s addr .W64 ret =
  require_read_access addr Width.W64 (fun _unit =>
    ret (s.dmem[UInt64.ofBitVec addr]!.toBitVec) s) :=
by
  simp only [MachineData.load,Width.bytesv,Width.bytes]
  -- TODO: figure out why `simp` cannot deduce the fact below; setting
  -- pp.coercions to false reveals that one version of the lemma uses
  -- `OfNat.ofNat` to produce a BitVec, while the other uses `OfNat.ofNat` to
  -- produce a Nat, followed by a call to `BitVec.ofNat`, and there appears to
  -- be no simp-rule that would show that one can be rewritten into the other.
  have: addr % 8#64 = 0#64 := by grind
  simp only [this]
  -- TODO: perhaps there should be a rule for this that can be in a simpset or a
  -- grindset to facilitate this sort of reasoning
  have: UInt64.ofBitVec (addr &&& ~~~0b111#64) = UInt64.ofBitVec addr := by
    bv_decide
  rw [this]
  have: addr &&& 7#64 = 0 := by bv_decide
  simp [this,Width.bits]
  rw [Std.ExtHashMap.getElem?_eq_some_getElem! hContains]
