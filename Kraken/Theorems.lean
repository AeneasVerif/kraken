/-
Kraken - Helper Theorems
-/

import Kraken.Semantics
import Kraken.Tactics

-- UInt64.ofInt (k : Int) ≠ 0 when k is a natural number with k < 2^64 and k ≠ 0
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

@[simp] theorem extract_self (v : BitVec 64) :
  BitVec.extractLsb' 0 64 (BitVec.extractLsb' 0 64 v) = v := by
  apply BitVec.eq_of_toNat_eq
  simp

@[simp] theorem ofInt_signed (v : BitVec 64) : BitVec.ofInt 64 v.signed = v := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.signed, BitVec.toInt, BitVec.ofInt]
  omega


@[simp] theorem align_check (rdi : UInt64) (h_align : rdi.toNat % 8 = 0) (disp : Int) (h_disp : disp % 8 = 0) :
  (BitVec.ofInt 64 (rdi.toBitVec.toInt + disp)) % 8#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have h2 : rdi.toBitVec.toInt % 8 = 0 := by
    have h_toNat : rdi.toBitVec.toNat = rdi.toNat := rfl
    have h_toInt : rdi.toBitVec.toInt = if 2 * rdi.toBitVec.toNat < 18446744073709551616 then (rdi.toBitVec.toNat : Int) else (rdi.toBitVec.toNat : Int) - 18446744073709551616 := rfl
    omega
  simp
  omega

theorem uint64_ext (a b : UInt64) (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b
  dsimp [UInt64.toBitVec] at h
  congr

@[simp]
theorem uint64_align_bv_8 (x : UInt64) (h : x.toNat % 8 = 0) : x.toBitVec % 8#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  change x.toNat % 8 = 0
  exact h

-- This is ~~~7 which is used as a mask in the kraken memory model. This is written in the format
-- that makes it most useful for simp.
@[simp]
theorem uint64_mask_align_8 (x : UInt64) (h : x.toNat % 8 = 0) : x &&& 18446744073709551608 = x := by
  have h_test_pre : x.toBitVec % 8#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    exact h
  have h_test : x.toBitVec &&& 18446744073709551608#64 = x.toBitVec := by
    revert h_test_pre
    bv_decide
  try rw [←UInt64.toBitVec_inj]
  try change x.toBitVec &&& 18446744073709551608#64 = x.toBitVec
  exact h_test

@[simp]
theorem uint64_idx_align_8 (x : UInt64) (h : x.toNat % 8 = 0) : (x.toNat &&& 7) = 0 := by
  have h_align_bv : x.toBitVec % 8#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    exact h
  have h1 : x.toBitVec &&& 7#64 = 0#64 := by
    revert h_align_bv
    bv_decide
  have h2 : (x.toBitVec &&& 7#64).toNat = 0 := by rw [h1]; rfl
  change (x.toBitVec.toNat &&& _) = _ at h2
  exact h2

@[simp]
theorem bitvec_replace_all_64 (old : BitVec 64) (new : BitVec 64) :
    BitVec.replace old 0 new = new := by
    dsimp only [BitVec.replace, BitVec.drop, BitVec.take]
    bv_decide


theorem option_eq_some {α} (opt : Option α) (h : opt.isSome = true) :
    opt = some (opt.get (by simp [h])) := by
  cases opt with
  | none => contradiction
  | some v => rfl

theorem ofInt_add (z1 z2 : Int) :
    BitVec.ofInt 64 (z1 + z2) = BitVec.ofInt 64 z1 + BitVec.ofInt 64 z2 := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [BitVec.ofInt, HAdd.hAdd, Add.add, BitVec.add, BitVec.toNat]
  simp
  omega

theorem ofInt_toInt (x : BitVec 64) :
    BitVec.ofInt 64 x.toInt = x := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [BitVec.ofInt, BitVec.toInt, BitVec.toNat]
  simp
  omega

@[simp]
theorem ofInt_toInt_add (x : BitVec 64) (offset : Nat) :
    BitVec.ofInt 64 (x.toInt + (offset : Int)) = x + BitVec.ofNat 64 offset := by
  rw [ofInt_add, ofInt_toInt]
  rfl

theorem toNat_ofInt_eq (z : Int) :
    ((z % 18446744073709551616).toNat) = (BitVec.ofInt 64 z).toNat := by
  rfl

theorem bitvec_add_align_8_mask_7 (x : BitVec 64) (offset : BitVec 64)
    (h_x : x % 8#64 = 0#64) (h_off : offset % 8#64 = 0#64) :
    ((x + offset).toNat &&& 7) = 0 := by
  have h_add : (x + offset) &&& 7#64 = 0#64 := by
    revert h_x h_off
    bv_decide
  have h_add_toNat : ((x + offset) &&& 7#64).toNat = 0 := by rw [h_add]; rfl
  change ((x + offset).toNat &&& 7) = 0 at h_add_toNat
  exact h_add_toNat

theorem int_add_mask_align_8 (x : BitVec 64) (offset : Nat)
    (h_x : x % 8#64 = 0#64) (h_off : offset % 8 = 0) :
    (((x.toInt + (offset : Int)) % 18446744073709551616).toNat &&& 7) = 0 := by
  rw [toNat_ofInt_eq]
  rw [ofInt_toInt_add]
  apply bitvec_add_align_8_mask_7 x (BitVec.ofNat 64 offset) h_x
  apply BitVec.eq_of_toNat_eq
  change ((BitVec.ofNat 64 offset).umod 8#64).toNat = (0#64).toNat
  dsimp only [BitVec.umod]
  simp
  omega

@[simp]
theorem uint64_add_mask_align_8 (x : UInt64) (offset : Nat)
    (h_x : x.toNat % 8 = 0) (h_off : offset % 8 = 0) :
    (((x.toBitVec.toInt + (offset : Int)) % 18446744073709551616).toNat &&& 7) = 0 := by
  apply int_add_mask_align_8 x.toBitVec offset
  · apply uint64_align_bv_8 _ h_x
  · exact h_off

@[simp]
theorem bitvec_add_align_8 (x y : BitVec 64) (h_x : x % 8#64 = 0#64) (h_y : y % 8#64 = 0#64) :
    (x + y) % 8#64 = 0#64 := by
  revert h_x h_y
  bv_decide

@[simp]
theorem bitvec_mask_align_8 (x : BitVec 64) (h : x % 8#64 = 0#64) :
    x &&& 18446744073709551608#64 = x := by
  revert h
  bv_decide

@[simp]
theorem uint64_add_align_bv_8 (x : UInt64) (offset : Nat)
    (h_x : x.toNat % 8 = 0) (h_off : offset % 8 = 0) :
    BitVec.ofInt 64 (x.toBitVec.toInt + (offset : Int)) % 8#64 = 0#64 := by
  rw [ofInt_toInt_add]
  apply bitvec_add_align_8 x.toBitVec (BitVec.ofNat 64 offset)
  · apply uint64_align_bv_8 _ h_x
  · apply BitVec.eq_of_toNat_eq
    change ((BitVec.ofNat 64 offset).umod 8#64).toNat = (0#64).toNat
    dsimp only [BitVec.umod]
    simp
    omega

theorem bitvec_add_left_cancel (x y z : BitVec 64) (h : x + y = x + z) : y = z := by
  revert h
  bv_decide

theorem ofNat_inj (o1 o2 : Nat) (h_o1 : o1 < 18446744073709551616) (h_o2 : o2 < 18446744073709551616)
    (h : BitVec.ofNat 64 o1 = BitVec.ofNat 64 o2) : o1 = o2 := by
  have h_eq : (BitVec.ofNat 64 o1).toNat = (BitVec.ofNat 64 o2).toNat := by rw [h]
  simp only [BitVec.toNat_ofNat] at h_eq
  omega

@[simp]
theorem uint64_ne_align_8 (x : UInt64) (offset1 offset2 : Nat)
    (h_o1 : offset1 < 18446744073709551616) (h_o2 : offset2 < 18446744073709551616)
    (h_ne : offset1 ≠ offset2) :
    ((UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset1 : Int)))) ==
     (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset2 : Int))))) = false := by
  have h_ne_bv : BitVec.ofInt 64 (x.toBitVec.toInt + (offset1 : Int)) ≠
                 BitVec.ofInt 64 (x.toBitVec.toInt + (offset2 : Int)) := by
    intro h_eq_bv
    rw [ofInt_toInt_add, ofInt_toInt_add] at h_eq_bv
    have h_eq_off : BitVec.ofNat 64 offset1 = BitVec.ofNat 64 offset2 := by
      apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv
    have h_eq_num : offset1 = offset2 := by
      apply ofNat_inj _ _ h_o1 h_o2 h_eq_off
    exact h_ne h_eq_num
  have h_ne_u : (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset1 : Int)))) ≠
                (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset2 : Int)))) := by
    intro h_eq
    apply h_ne_bv
    exact congrArg UInt64.toBitVec h_eq
  have h_ne_eq : ((UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset1 : Int)))) ==
                  (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset2 : Int))))) = false := by
    match h : (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset1 : Int)))) ==
              (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset2 : Int)))) with
    | true =>
      rw [beq_iff_eq] at h
      contradiction
    | false => rfl
  exact h_ne_eq

@[simp]
theorem uint64_add_mask_align_8_val (x : UInt64) (offset : Nat)
    (h_x : x.toNat % 8 = 0) (h_off : offset % 8 = 0) :
    (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset : Int)))) &&& 18446744073709551608 =
    (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset : Int)))) := by
  apply uint64_ext
  have h_align : BitVec.ofInt 64 (x.toBitVec.toInt + (offset : Int)) % 8#64 = 0#64 := by
    apply uint64_add_align_bv_8 _ _ h_x h_off
  have h_mask : BitVec.ofInt 64 (x.toBitVec.toInt + (offset : Int)) &&& 18446744073709551608#64 =
      BitVec.ofInt 64 (x.toBitVec.toInt + (offset : Int)) := by
    revert h_align
    bv_decide
  change (BitVec.ofInt 64 (x.toBitVec.toInt + (offset : Int)) &&& 18446744073709551608#64) = _
  exact h_mask

@[simp]
theorem uint64_ne_align_8_eq (x : UInt64) (offset1 offset2 : Nat)
    (h_o1 : offset1 < 18446744073709551616) (h_o2 : offset2 < 18446744073709551616)
    (h_ne : offset1 ≠ offset2) :
    (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset1 : Int))) =
     UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + (offset2 : Int)))) = False := by
  apply eq_false
  intro h_eq
  have h_ne_bv : BitVec.ofInt 64 (x.toBitVec.toInt + (offset1 : Int)) ≠
                 BitVec.ofInt 64 (x.toBitVec.toInt + (offset2 : Int)) := by
    intro h_eq_bv
    rw [ofInt_toInt_add, ofInt_toInt_add] at h_eq_bv
    have h_eq_off : BitVec.ofNat 64 offset1 = BitVec.ofNat 64 offset2 := by
      apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv
    have h_eq_num : offset1 = offset2 := by
      apply ofNat_inj _ _ h_o1 h_o2 h_eq_off
    exact h_ne h_eq_num
  apply h_ne_bv
  exact congrArg UInt64.toBitVec h_eq

theorem ofInt_mod_8 (offset : Int) (h : offset % 8 = 0) :
    (BitVec.ofInt 64 offset).toNat % 8 = 0 := by
  dsimp [BitVec.ofInt]
  have h_ge : offset % 18446744073709551616 ≥ 0 := by
    apply Int.emod_nonneg
    decide
  omega

theorem ofInt_add_align_8 (x : BitVec 64) (offset : Int) (h_x : x % 8#64 = 0#64) (h_off : offset % 8 = 0) :
    BitVec.ofInt 64 (x.toInt + offset) % 8#64 = 0#64 := by
  have h_add : BitVec.ofInt 64 (x.toInt + offset) = x + BitVec.ofInt 64 offset := by
    rw [ofInt_add, ofInt_toInt]
  rw [h_add]
  apply bitvec_add_align_8 _ _ h_x
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofInt 64 offset).toNat % 8 = 0
  apply ofInt_mod_8 _ h_off

theorem int_add_mask_align_8_int (x : BitVec 64) (offset : Int)
    (h_x : x % 8#64 = 0#64) (h_off : offset % 8 = 0) :
    (((x.toInt + offset) % 18446744073709551616).toNat &&& 7) = 0 := by
  rw [toNat_ofInt_eq]
  have h_add : BitVec.ofInt 64 (x.toInt + offset) = x + BitVec.ofInt 64 offset := by
    rw [ofInt_add, ofInt_toInt]
  rw [h_add]
  apply bitvec_add_align_8_mask_7 _ _ h_x
  have h_mod : (BitVec.ofInt 64 offset).toNat % 8 = 0 := by
    apply ofInt_mod_8 _ h_off
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofInt 64 offset).toNat % 8 = 0
  exact h_mod

@[simp]
theorem uint64_add_mask_align_8_int (x : UInt64) (offset : Int)
    (h_x : x.toNat % 8 = 0) (h_off : offset % 8 = 0) :
    (((x.toBitVec.toInt + offset) % 18446744073709551616).toNat &&& 7) = 0 := by
  apply int_add_mask_align_8_int x.toBitVec offset
  · apply uint64_align_bv_8 _ h_x
  · exact h_off

@[simp]
theorem uint64_add_align_bv_8_int (x : UInt64) (offset : Int)
    (h_x : x.toNat % 8 = 0) (h_off : offset % 8 = 0) :
    BitVec.ofInt 64 (x.toBitVec.toInt + offset) % 8#64 = 0#64 := by
  apply ofInt_add_align_8 x.toBitVec offset
  · apply uint64_align_bv_8 _ h_x
  · exact h_off

@[simp]
theorem uint64_add_mask_align_8_val_int (x : UInt64) (offset : Int)
    (h_x : x.toNat % 8 = 0) (h_off : offset % 8 = 0) :
    (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset))) &&& 18446744073709551608 =
    (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset))) := by
  apply uint64_ext
  have h_align : BitVec.ofInt 64 (x.toBitVec.toInt + offset) % 8#64 = 0#64 := by
    apply uint64_add_align_bv_8_int _ _ h_x h_off
  have h_mask : BitVec.ofInt 64 (x.toBitVec.toInt + offset) &&& 18446744073709551608#64 =
      BitVec.ofInt 64 (x.toBitVec.toInt + offset) := by
    revert h_align
    bv_decide
  change (BitVec.ofInt 64 (x.toBitVec.toInt + offset) &&& 18446744073709551608#64) = _
  exact h_mask

theorem ofInt_inj_int (o1 o2 : Int) (h_o1 : 0 ≤ o1 ∧ o1 < 18446744073709551616)
    (h_o2 : 0 ≤ o2 ∧ o2 < 18446744073709551616) (h : BitVec.ofInt 64 o1 = BitVec.ofInt 64 o2) :
    o1 = o2 := by
  have h_eq : (BitVec.ofInt 64 o1).toNat = (BitVec.ofInt 64 o2).toNat := by rw [h]
  have h_o1_eq : (BitVec.ofInt 64 o1).toNat = (o1 % 18446744073709551616).toNat := rfl
  have h_o2_eq : (BitVec.ofInt 64 o2).toNat = (o2 % 18446744073709551616).toNat := rfl
  rw [h_o1_eq, h_o2_eq] at h_eq
  have h1 : o1 % 18446744073709551616 = o1 := by omega
  have h2 : o2 % 18446744073709551616 = o2 := by omega
  rw [h1, h2] at h_eq
  omega

@[simp]
theorem uint64_ne_align_8_int (x : UInt64) (offset1 offset2 : Int)
    (h_o1 : 0 ≤ offset1 ∧ offset1 < 18446744073709551616)
    (h_o2 : 0 ≤ offset2 ∧ offset2 < 18446744073709551616)
    (h_ne : offset1 ≠ offset2) :
    ((UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset1))) ==
     (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset2)))) = false := by
  have h_ne_bv : BitVec.ofInt 64 (x.toBitVec.toInt + offset1) ≠
                 BitVec.ofInt 64 (x.toBitVec.toInt + offset2) := by
    intro h_eq_bv
    rw [ofInt_add, ofInt_add, ofInt_toInt] at h_eq_bv
    have h_eq_off : BitVec.ofInt 64 offset1 = BitVec.ofInt 64 offset2 := by
      apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv
    have h_eq_num : offset1 = offset2 := by
      apply ofInt_inj_int _ _ h_o1 h_o2 h_eq_off
    exact h_ne h_eq_num
  have h_ne_u : (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset1))) ≠
                (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset2))) := by
    intro h_eq
    apply h_ne_bv
    exact congrArg UInt64.toBitVec h_eq
  have h_ne_eq : ((UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset1))) ==
                  (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset2)))) = false := by
    match h : (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset1))) ==
              (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset2))) with
    | true =>
      rw [beq_iff_eq] at h
      contradiction
    | false => rfl
  exact h_ne_eq

@[simp]
theorem uint64_ne_align_8_eq_int (x : UInt64) (offset1 offset2 : Int)
    (h_o1 : 0 ≤ offset1 ∧ offset1 < 18446744073709551616)
    (h_o2 : 0 ≤ offset2 ∧ offset2 < 18446744073709551616)
    (h_ne : offset1 ≠ offset2) :
    (UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset1)) =
     UInt64.ofBitVec (BitVec.ofInt 64 (x.toBitVec.toInt + offset2))) = False := by
  apply eq_false
  intro h_eq
  have h_ne_bv : BitVec.ofInt 64 (x.toBitVec.toInt + offset1) ≠
                 BitVec.ofInt 64 (x.toBitVec.toInt + offset2) := by
    intro h_eq_bv
    rw [ofInt_add, ofInt_add, ofInt_toInt] at h_eq_bv
    have h_eq_off : BitVec.ofInt 64 offset1 = BitVec.ofInt 64 offset2 := by
      apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv
    have h_eq_num : offset1 = offset2 := by
      apply ofInt_inj_int _ _ h_o1 h_o2 h_eq_off
    exact h_ne h_eq_num
  apply h_ne_bv
  exact congrArg UInt64.toBitVec h_eq

@[simp]
theorem uint64_ne_align_8_u64 (x : UInt64) (offset1 offset2 : UInt64)
    (h_ne : offset1 ≠ offset2) :
    ((x + offset1) == (x + offset2)) = false := by
  have h_ne_bv : x.toBitVec + offset1.toBitVec ≠ x.toBitVec + offset2.toBitVec := by
    intro h_eq_bv
    have h_eq_off : offset1.toBitVec = offset2.toBitVec := by
      apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv
    have h_eq_num : offset1 = offset2 := by
      apply uint64_ext _ _ h_eq_off
    exact h_ne h_eq_num
  have h_ne_u : (x + offset1) ≠ (x + offset2) := by
    intro h_eq
    apply h_ne_bv
    have h_eq_bv2 : (x + offset1).toBitVec = (x + offset2).toBitVec := congrArg UInt64.toBitVec h_eq
    exact h_eq_bv2
  match h : (x + offset1) == (x + offset2) with
  | true =>
    rw [beq_iff_eq] at h
    contradiction
  | false => rfl

@[simp]
theorem uint64_ne_align_8_u64_zero_right (x : UInt64) (offset : UInt64)
    (h_ne : offset ≠ 0) :
    ((x + offset) == x) = false := by
  have h_ne_bv : x.toBitVec + offset.toBitVec ≠ x.toBitVec := by
    intro h_eq_bv
    have h_eq_off : offset.toBitVec = 0#64 := by
      have h_eq_bv_zero : x.toBitVec + offset.toBitVec = x.toBitVec + 0#64 := by
        rw [h_eq_bv]
        simp
      apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv_zero
    have h_eq_num : offset = 0 := by
      apply uint64_ext _ _ h_eq_off
    exact h_ne h_eq_num
  have h_ne_u : (x + offset) ≠ x := by
    intro h_eq
    apply h_ne_bv
    have h_eq_bv2 : (x + offset).toBitVec = x.toBitVec := congrArg UInt64.toBitVec h_eq
    exact h_eq_bv2
  match h : (x + offset) == x with
  | true =>
    rw [beq_iff_eq] at h
    contradiction
  | false => rfl

@[simp]
theorem uint64_ne_align_8_u64_zero_left (x : UInt64) (offset : UInt64)
    (h_ne : offset ≠ 0) :
    (x == (x + offset)) = false := by
  have h_ne_bv : x.toBitVec ≠ x.toBitVec + offset.toBitVec := by
    intro h_eq_bv
    have h_eq_off : 0#64 = offset.toBitVec := by
      have h_eq_bv_zero : x.toBitVec + 0#64 = x.toBitVec + offset.toBitVec := by
        rw [←h_eq_bv]
        simp
      apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv_zero
    have h_eq_num : offset = 0 := by
      apply uint64_ext _ _ h_eq_off.symm
    exact h_ne h_eq_num
  have h_ne_u : x ≠ (x + offset) := by
    intro h_eq
    apply h_ne_bv
    have h_eq_bv2 : x.toBitVec = (x + offset).toBitVec := congrArg UInt64.toBitVec h_eq
    exact h_eq_bv2
  match h : x == (x + offset) with
  | true =>
    rw [beq_iff_eq] at h
    contradiction
  | false => rfl

@[simp]
theorem uint64_ne_align_8_u64_eq (x : UInt64) (offset1 offset2 : UInt64)
    (h_ne : offset1 ≠ offset2 := by decide) :
    (x + offset1 = x + offset2) = False := by
  apply eq_false
  intro h_eq
  have h_eq_bv : x.toBitVec + offset1.toBitVec = x.toBitVec + offset2.toBitVec := congrArg UInt64.toBitVec h_eq
  have h_eq_off : offset1.toBitVec = offset2.toBitVec := by
    apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv
  have h_eq_num : offset1 = offset2 := by
    apply uint64_ext _ _ h_eq_off
  exact h_ne h_eq_num

@[simp]
theorem uint64_ne_align_8_u64_zero_right_eq (x : UInt64) (offset : UInt64)
    (h_ne : offset ≠ 0 := by decide) :
    (x + offset = x) = False := by
  apply eq_false
  intro h_eq
  have h_eq_bv : x.toBitVec + offset.toBitVec = x.toBitVec := congrArg UInt64.toBitVec h_eq
  have h_eq_off : offset.toBitVec = 0#64 := by
    have h_eq_bv_zero : x.toBitVec + offset.toBitVec = x.toBitVec + 0#64 := by
      rw [h_eq_bv]
      simp
    apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv_zero
  have h_eq_num : offset = 0 := by
    apply uint64_ext _ _ h_eq_off
  exact h_ne h_eq_num

@[simp]
theorem uint64_ne_align_8_u64_zero_left_eq (x : UInt64) (offset : UInt64)
    (h_ne : offset ≠ 0 := by decide) :
    (x = x + offset) = False := by
  apply eq_false
  intro h_eq
  have h_eq_bv : x.toBitVec = x.toBitVec + offset.toBitVec := congrArg UInt64.toBitVec h_eq
  have h_eq_off : 0#64 = offset.toBitVec := by
    have h_eq_bv_zero : x.toBitVec + 0#64 = x.toBitVec + offset.toBitVec := by
      rw [←h_eq_bv]
      simp
    apply bitvec_add_left_cancel x.toBitVec _ _ h_eq_bv_zero
  have h_eq_num : offset = 0 := by
    apply uint64_ext _ _ h_eq_off.symm
  exact h_ne h_eq_num
@[simp]
theorem ofInt_toInt_add_int (x : BitVec 64) (offset : Int) :
    BitVec.ofInt 64 (x.toInt + offset) = x + BitVec.ofInt 64 offset := by
  rw [ofInt_add, ofInt_toInt]

@[simp]
theorem uint64_toNat_add_mask_align_8 (x : UInt64) (offset : Nat)
    (h_x : x.toNat % 8 = 0) (h_off : offset % 8 = 0)
    (h_bounds : offset < 18446744073709551616) :
    ((x.toNat + offset) % 18446744073709551616 &&& 7) = 0 := by
  have h_eq : ((x.toNat + offset) % 18446744073709551616) = (x.toBitVec + BitVec.ofNat 64 offset).toNat := by
    change (x.toNat + offset) % (2^64) =
      (BitVec.ofNat 64 (x.toBitVec.toNat + (BitVec.ofNat 64 offset).toNat)).toNat
    rw [BitVec.toNat_ofNat]
    rw [BitVec.toNat_ofNat]
    have h_mod : offset % 2^64 = offset := Nat.mod_eq_of_lt h_bounds
    rw [h_mod]
    rfl
  rw [h_eq]
  have h_align_bv : x.toBitVec % 8#64 = 0#64 := by
    apply uint64_align_bv_8 _ h_x
  have h_add : (x.toBitVec + BitVec.ofNat 64 offset) &&& 7#64 = 0#64 := by
    have h_off_bv : BitVec.ofNat 64 offset % 8#64 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      change ((BitVec.ofNat 64 offset).umod 8#64).toNat = (0#64).toNat
      dsimp [BitVec.umod]
      rw [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt h_bounds]
      change (offset % 8) = 0
      exact h_off
    revert h_align_bv h_off_bv
    bv_decide
  have h_add_toNat : ((x.toBitVec + BitVec.ofNat 64 offset) &&& 7#64).toNat = 0 := by rw [h_add]; rfl
  change ((x.toBitVec + BitVec.ofNat 64 offset).toNat &&& 7) = 0 at h_add_toNat
  exact h_add_toNat

@[simp]
theorem uint64_toNat_add_align_8 (x : UInt64) (offset : Nat)
    (h_x : x.toNat % 8 = 0) (h_off : offset % 8 = 0)
    (h_bounds : offset < 18446744073709551616) :
    ((x.toNat + offset) % 18446744073709551616) % 8 = 0 := by
  have h_eq : ((x.toNat + offset) % 18446744073709551616) = (x.toBitVec + BitVec.ofNat 64 offset).toNat := by
    change (x.toNat + offset) % (2^64) =
      (BitVec.ofNat 64 (x.toBitVec.toNat + (BitVec.ofNat 64 offset).toNat)).toNat
    rw [BitVec.toNat_ofNat]
    rw [BitVec.toNat_ofNat]
    have h_mod : offset % 2^64 = offset := Nat.mod_eq_of_lt h_bounds
    rw [h_mod]
    rfl
  rw [h_eq]
  have h_align_bv : x.toBitVec % 8#64 = 0#64 := by
    apply uint64_align_bv_8 _ h_x
  have h_add : (x.toBitVec + BitVec.ofNat 64 offset) % 8#64 = 0#64 := by
    have h_off_bv : BitVec.ofNat 64 offset % 8#64 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      change ((BitVec.ofNat 64 offset).umod 8#64).toNat = (0#64).toNat
      dsimp [BitVec.umod]
      rw [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt h_bounds]
      change (offset % 8) = 0
      exact h_off
    revert h_align_bv h_off_bv
    bv_decide
  have h_add_toNat : ((x.toBitVec + BitVec.ofNat 64 offset) % 8#64).toNat = 0 := by rw [h_add]; rfl
  change ((x.toBitVec + BitVec.ofNat 64 offset).toNat % 8) = 0 at h_add_toNat
  exact h_add_toNat

@[simp]
theorem uint64_add_align_8 (x : UInt64) (offset : UInt64)
    (h_x : x.toNat % 8 = 0) (h_off : offset.toNat % 8 = 0 := by decide) :
    (x + offset).toNat % 8 = 0 := by
  have h1 : (x + offset).toNat = (x.toNat + offset.toNat) % 18446744073709551616 := rfl
  rw [h1]
  have h2 : 18446744073709551616 % 8 = 0 := by decide
  omega

@[simp]
theorem base_offset_eq_false (base : UInt64) (off1 off2 : Nat)
    (h_o1 : off1 < 18446744073709551616 := by decide)
    (h_o2 : off2 < 18446744073709551616 := by decide)
    (h_ne : off1 ≠ off2 := by decide) :
    (base + UInt64.ofNat off1 = base + UInt64.ofNat off2) = False := by
  apply uint64_ne_align_8_u64_eq
  intro h_eq_off
  apply h_ne
  have h_eq_bv : BitVec.ofNat 64 off1 = BitVec.ofNat 64 off2 := congrArg UInt64.toBitVec h_eq_off
  exact ofNat_inj off1 off2 h_o1 h_o2 h_eq_bv

theorem base_offset_ne (base : UInt64) (off1 off2 : Nat)
    (h_o1 : off1 < 18446744073709551616 := by decide)
    (h_o2 : off2 < 18446744073709551616 := by decide)
    (h_ne : off1 ≠ off2 := by decide) :
    base + UInt64.ofNat off1 ≠ base + UInt64.ofNat off2 := by
  intro h
  have h_false : (base + UInt64.ofNat off1 = base + UInt64.ofNat off2) = False := base_offset_eq_false base off1 off2 h_o1 h_o2 h_ne
  rw [h] at h_false
  simp at h_false

@[simp]
theorem align_add_u64 (x y : UInt64) (hx : x.toNat % 8 = 0) (hy : y.toNat % 8 = 0) : (x + y).toNat % 8 = 0 := by
  have h1 : (x + y).toNat = (x.toNat + y.toNat) % 18446744073709551616 := rfl
  rw [h1]
  have h2 : 18446744073709551616 % 8 = 0 := by decide
  omega

@[simp]
theorem align_8_const (c : UInt64) (h : c.toNat % 8 = 0 := by decide) : c.toNat % 8 = 0 := h


@[simp] theorem bitvec_extractLsb'_0_64 (x : BitVec 64) : BitVec.extractLsb' 0 64 x = x := by bv_decide
@[simp] theorem bitvec_zeroExtend_64_64 (x : BitVec 64) : BitVec.zeroExtend 64 x = x := by bv_decide
@[simp] theorem int64_toint_zero : Int64.toInt 0 = 0 := rfl
@[simp] theorem int_add_zero_end (x : Int) : x + 0 = x := by omega
@[simp] theorem int_add_zero_middle (x y : Int) : x + 0 + y = x + y := by omega

@[simp]
theorem bitvec_ofInt_add_mask_align_8 (rdi : UInt64) (h : rdi.toNat % 8 = 0) (c : Int) (hc : c % 8 = 0 := by decide) :
  BitVec.ofInt 64 (rdi.toBitVec.toInt + c) &&& ~~~7#64 = BitVec.ofInt 64 (rdi.toBitVec.toInt + c) := by
  apply bitvec_mask_align_8
  apply uint64_add_align_bv_8_int _ _ h hc

@[simp]
theorem bitvec_ofInt_add_mod_8_neq (rdi : UInt64) (h : rdi.toNat % 8 = 0) (c : Int) (hc : c % 8 = 0 := by decide) :
  (BitVec.ofInt 64 (rdi.toBitVec.toInt + c) % 8#64 != 0) = false := by
  have h_mod := uint64_add_align_bv_8_int rdi c h hc
  rw [h_mod]
  rfl

@[simp]
theorem bitvec_ofInt_add_and_7 (rdi : UInt64) (h : rdi.toNat % 8 = 0) (c : Int) (hc : c % 8 = 0 := by decide) :
  BitVec.ofInt 64 (rdi.toBitVec.toInt + c) &&& 7#64 = 0#64 := by
  have h_mod := uint64_add_align_bv_8_int rdi c h hc
  revert h_mod
  bv_decide


@[simp] theorem bv_mod_8 (v : UInt64) (h : v.toNat % 8 = 0) : v.toBitVec % 8#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  change v.toNat % 8 = 0
  exact h

@[simp] theorem bv_and_mask (v : UInt64) (h : v.toNat % 8 = 0) : v &&& 18446744073709551608 = v := by
  apply UInt64.toNat_inj.1
  have : (v &&& 18446744073709551608).toNat = v.toNat &&& 18446744073709551608 := by rfl
  rw [this]
  have hk : v.toNat = 8 * (v.toNat / 8) := by omega
  have hv_lt : 8 * (v.toNat / 8) < 18446744073709551616 := by rw [← hk]; exact UInt64.toNat_lt_size v
  generalize (v.toNat / 8) = k at hk hv_lt
  rw [hk]
  apply Nat.eq_of_testBit_eq
  intro i
  simp
  cases i with
  | zero =>
    have : (8 * k).testBit 0 = false := by simp [Nat.testBit]; omega
    simp [this]
  | succ i => cases i with
    | zero =>
      have : (8 * k).testBit 1 = false := by simp [Nat.testBit]; omega
      simp [this]
    | succ i => cases i with
      | zero =>
        have : (8 * k).testBit 2 = false := by simp [Nat.testBit]; omega
        simp [this]
      | succ i =>
        by_cases hi : i < 61
        · have h_tb : Nat.testBit 18446744073709551608 (i + 3) = true := by
            have : ∀ j : Fin 61, Nat.testBit 18446744073709551608 (j.val + 3) = true := by decide
            exact this ⟨i, hi⟩
          simp [h_tb]
        · have h_tb : (8 * k).testBit (i + 3) = false := by
            apply Nat.testBit_lt_two_pow
            have : 8 * k < 2^64 := hv_lt
            have : 2^64 ≤ 2^(i + 3) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          simp [h_tb]

theorem mul_8_and_7 (k : Nat) : (8 * k) &&& 7 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : Nat.testBit ((8 * k) &&& 7) i = (Nat.testBit (8 * k) i && Nat.testBit 7 i) := by simp
  rw [h1]
  cases i with
  | zero =>
    have : (8 * k).testBit 0 = false := by simp [Nat.testBit]; omega
    simp [this]
  | succ i => cases i with
    | zero =>
      have : (8 * k).testBit 1 = false := by simp [Nat.testBit]; omega
      simp [this]
    | succ i => cases i with
      | zero =>
        have : (8 * k).testBit 2 = false := by simp [Nat.testBit]; omega
        simp [this]
      | succ i =>
        have h2 : Nat.testBit 7 (i + 3) = false := by
          apply Nat.testBit_lt_two_pow
          have : 2^3 ≤ 2^(i+3) := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        simp [h2]

@[simp] theorem bv_and_7 (v : UInt64) (h : v.toNat % 8 = 0) : v.toNat &&& 7 = 0 := by
  have hk : v.toNat = 8 * (v.toNat / 8) := by omega
  rw [hk, mul_8_and_7]

@[simp] theorem ext_hash_map_insert_eq (m : Std.ExtHashMap UInt64 UInt64) (k : UInt64) (v : UInt64) :
  (m.insert k v)[k]? = some v := by
  exact Std.ExtHashMap.getElem?_insert_self

@[simp] theorem ext_hash_map_insert_ne (m : Std.ExtHashMap UInt64 UInt64) (k k' : UInt64) (v : UInt64) (h : k ≠ k') :
  (m.insert k v)[k']? = m[k']? := by
  rw [Std.ExtHashMap.getElem?_insert]
  simp [h]


@[simp] theorem isSome_to_exists {α} (o : Option α) (h : o.isSome) : ∃ v, o = some v := by
  cases o
  · contradiction
  · exact ⟨_, rfl⟩

@[simp] theorem rdi_add_mask_c (rdi c : UInt64) (h1 : rdi.toNat % 8 = 0) (h2 : c.toNat % 8 = 0) :
  (rdi + c) &&& 18446744073709551608 = rdi + c := by
  apply bv_and_mask
  exact uint64_add_align_8 rdi c h1 h2



@[simp] theorem bitvec_add_mask_0 (rdi : UInt64) (h1 : rdi.toNat % 8 = 0) :
  rdi.toBitVec &&& ~~~7#64 = rdi.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  have h3 : (~~~7#64).toNat = 18446744073709551608 := rfl
  have h4 : (rdi.toBitVec &&& ~~~7#64).toNat = rdi.toBitVec.toNat &&& 18446744073709551608 := by rfl
  rw [h4]
  have hk1 : rdi.toBitVec.toNat = rdi.toNat := rfl
  have hk2 : rdi.toNat = 8 * (rdi.toNat / 8) := by omega
  have hv : rdi.toBitVec.toNat % 8 = 0 := by
    rw [hk1, hk2]
    omega
  have hk : rdi.toBitVec.toNat = 8 * (rdi.toBitVec.toNat / 8) := by omega
  have hv_lt : 8 * (rdi.toBitVec.toNat / 8) < 18446744073709551616 := by rw [← hk]; exact rdi.toBitVec.isLt
  generalize (rdi.toBitVec.toNat / 8) = k at hk hv_lt
  rw [hk]
  apply Nat.eq_of_testBit_eq
  intro i
  simp
  cases i with
  | zero =>
    have : (8 * k).testBit 0 = false := by simp [Nat.testBit]; omega
    simp [this]
  | succ i => cases i with
    | zero =>
      have : (8 * k).testBit 1 = false := by simp [Nat.testBit]; omega
      simp [this]
    | succ i => cases i with
      | zero =>
        have : (8 * k).testBit 2 = false := by simp [Nat.testBit]; omega
        simp [this]
      | succ i =>
        by_cases hi : i < 61
        · have h_tb : Nat.testBit 18446744073709551608 (i + 3) = true := by
            have : ∀ j : Fin 61, Nat.testBit 18446744073709551608 (j.val + 3) = true := by decide
            exact this ⟨i, hi⟩
          simp [h_tb]
        · have h_tb : (8 * k).testBit (i + 3) = false := by
            apply Nat.testBit_lt_two_pow
            have : 8 * k < 2^64 := hv_lt
            have : 2^64 ≤ 2^(i + 3) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          simp [h_tb]

@[simp] theorem bitvec_add_mask_c (rdi : UInt64) (c : BitVec 64) (h1 : rdi.toNat % 8 = 0) (h2 : c.toNat % 8 = 0 := by decide) :
  (rdi.toBitVec + c) &&& ~~~7#64 = rdi.toBitVec + c := by
  apply BitVec.eq_of_toNat_eq
  have h3 : (~~~7#64).toNat = 18446744073709551608 := rfl
  have h4 : ((rdi.toBitVec + c) &&& ~~~7#64).toNat = (rdi.toBitVec + c).toNat &&& 18446744073709551608 := by rfl
  rw [h4]
  have hk1 : rdi.toBitVec.toNat = rdi.toNat := rfl
  have hk2 : rdi.toNat = 8 * (rdi.toNat / 8) := by omega
  have hk3 : c.toNat = 8 * (c.toNat / 8) := by omega
  have hv : (rdi.toBitVec + c).toNat % 8 = 0 := by
    change (rdi.toBitVec.toNat + c.toNat) % 18446744073709551616 % 8 = 0
    rw [hk1, hk2, hk3]
    omega
  have hk : (rdi.toBitVec + c).toNat = 8 * ((rdi.toBitVec + c).toNat / 8) := by omega
  have hv_lt : 8 * ((rdi.toBitVec + c).toNat / 8) < 18446744073709551616 := by rw [← hk]; exact (rdi.toBitVec + c).isLt
  generalize ((rdi.toBitVec + c).toNat / 8) = k at hk hv_lt
  rw [hk]
  apply Nat.eq_of_testBit_eq
  intro i
  simp
  cases i with
  | zero =>
    have : (8 * k).testBit 0 = false := by simp [Nat.testBit]; omega
    simp [this]
  | succ i => cases i with
    | zero =>
      have : (8 * k).testBit 1 = false := by simp [Nat.testBit]; omega
      simp [this]
    | succ i => cases i with
      | zero =>
        have : (8 * k).testBit 2 = false := by simp [Nat.testBit]; omega
        simp [this]
      | succ i =>
        by_cases hi : i < 61
        · have h_tb : Nat.testBit 18446744073709551608 (i + 3) = true := by
            have : ∀ j : Fin 61, Nat.testBit 18446744073709551608 (j.val + 3) = true := by decide
            exact this ⟨i, hi⟩
          simp [h_tb]
        · have h_tb : (8 * k).testBit (i + 3) = false := by
            apply Nat.testBit_lt_two_pow
            have : 8 * k < 2^64 := hv_lt
            have : 2^64 ≤ 2^(i + 3) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          simp [h_tb]

@[simp] theorem int64_toint_zero_add_general (rdi : UInt64) :
  BitVec.zeroExtend 64 (BitVec.ofInt 64 ((BitVec.extractLsb' 0 64 rdi.toBitVec).toInt + 0 + Int64.toInt 0)) = rdi.toBitVec := by
  have h1 : BitVec.extractLsb' 0 64 rdi.toBitVec = rdi.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [h1]
  have h2 : Int64.toInt 0 = 0 := rfl
  rw [h2]
  have h3 : rdi.toBitVec.toInt + 0 + 0 = rdi.toBitVec.toInt := by omega
  rw [h3]
  have h4 : rdi.toBitVec.toInt = rdi.toBitVec.signed := rfl
  rw [h4]
  rw [ofInt_signed]
  apply BitVec.eq_of_toNat_eq
  simp

@[simp] theorem int64_toint_c_add_general (rdi : UInt64) (c : Int) :
  BitVec.zeroExtend 64 (BitVec.ofInt 64 ((BitVec.extractLsb' 0 64 rdi.toBitVec).toInt + 0 + c)) = rdi.toBitVec + BitVec.ofInt 64 c := by
  have h1 : BitVec.extractLsb' 0 64 rdi.toBitVec = rdi.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [h1]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toInt, BitVec.ofInt]
  have h_toInt : rdi.toBitVec.toInt = if 2 * rdi.toBitVec.toNat < 18446744073709551616 then (rdi.toBitVec.toNat : Int) else (rdi.toBitVec.toNat : Int) - 18446744073709551616 := rfl
  omega

-- Bridge lemma: lets simp prove (n : UInt64).toNat % 8 = 0 for concrete n.
-- simp chains: bv_and_mask needs alignment → uint64_add_align_8 propagates it
-- → this lemma reduces UInt64 literal alignment to Nat alignment (n % 8 = 0)
-- → Nat.reduceMod computes n % 8 for ground n.
@[simp] theorem uint64_ofNat_toNat_mod_8 (n : Nat) (h : n % 8 = 0) :
    (OfNat.ofNat n : UInt64).toNat % 8 = 0 := by
  change n % 18446744073709551616 % 8 = 0
  omega

@[simp] theorem uint64_add_c_general (rdi : UInt64) (c : Int) :
  ({ toBitVec := BitVec.ofInt 64 (rdi.toBitVec.signed + c) } : UInt64) = rdi + (UInt64.ofBitVec (BitVec.ofInt 64 c)) := by
  have : rdi + (UInt64.ofBitVec (BitVec.ofInt 64 c)) = { toBitVec := rdi.toBitVec + BitVec.ofInt 64 c } := rfl
  rw [this]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.signed, BitVec.toInt, BitVec.ofInt]
  omega

@[simp] theorem int64_toint_8 : Int64.toInt (Int64.ofNat 8) = 8 := rfl
@[simp] theorem int64_toint_16 : Int64.toInt (Int64.ofNat 16) = 16 := rfl
@[simp] theorem int64_toint_24 : Int64.toInt (Int64.ofNat 24) = 24 := rfl
@[simp] theorem int64_toint_32 : Int64.toInt (Int64.ofNat 32) = 32 := rfl
@[simp] theorem int64_toint_40 : Int64.toInt (Int64.ofNat 40) = 40 := rfl
@[simp] theorem int64_toint_48 : Int64.toInt (Int64.ofNat 48) = 48 := rfl
@[simp] theorem int64_toint_56 : Int64.toInt (Int64.ofNat 56) = 56 := rfl
@[simp] theorem int64_toint_64 : Int64.toInt (Int64.ofNat 64) = 64 := rfl
@[simp] theorem int64_toint_72 : Int64.toInt (Int64.ofNat 72) = 72 := rfl

theorem align_check_add_lem (v : UInt64) (h : v.toNat % 8 = 0) (c : Int) (hc : c % 8 = 0) :
  ((v.toBitVec.toInt + c) % 18446744073709551616).toNat % 8 = 0 := by
  have hv : v.toBitVec.toInt % 8 = 0 := by
    have h_toNat : v.toBitVec.toNat = v.toNat := rfl
    have h_toInt : v.toBitVec.toInt = if 2 * v.toBitVec.toNat < 18446744073709551616 then (v.toBitVec.toNat : Int) else (v.toBitVec.toNat : Int) - 18446744073709551616 := rfl
    omega
  have hc_int : (v.toBitVec.toInt + c) % 8 = 0 := by omega
  omega

@[simp] theorem align_check_add (v : UInt64) (h : v.toNat % 8 = 0) (c : Int) (hc : c % 8 = 0) :
  (BitVec.ofInt 64 (v.toBitVec.signed + c)) % 8#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have : v.toBitVec.signed = v.toBitVec.toInt := rfl
  rw [this]
  have := align_check_add_lem v h c hc
  simp
  omega


@[simp] theorem md_regs_proj (r s d) : ({ regs := r, status := s, dmem := d } : MachineData).regs = r := rfl

@[simp] theorem setReg_regs (s : MachineData) {w} (r : Reg w) (v : w.type) :
  (s.setReg r v).regs = s.regs.set r v := rfl

@[simp] theorem setReg_dmem (s : MachineData) {w} (r : Reg w) (v : w.type) :
  (s.setReg r v).dmem = s.dmem := rfl

@[simp] theorem setReg_status (s : MachineData) {w} (r : Reg w) (v : w.type) :
  (s.setReg r v).status = s.status := rfl

@[simp] theorem set_low_w64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
  s.set (.low r .W64) v = s.set64 r v := rfl

macro "u64_omega" : tactic => `(tactic| (
  intro h;
  have h2 := congrArg UInt64.toNat h;
  revert h2;
  intro h2;
  omega
))

@[simp]
theorem bitvec_and_7_align_8 (x : BitVec 64) (h : x % 8#64 = 0#64) : x &&& 7#64 = 0#64 := by
  revert h
  bv_decide


@[simp] theorem bv_replace_0_64 (v : BitVec 64) (new : BitVec 64) :
  v.replace 0 new = new := by
  have h1 : v.take 0 = 0#0 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.take]
  have h2 : v.drop 64 = 0#0 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.drop]
  unfold BitVec.replace
  rw [h1, h2]
  have h3 : 0#0 ++ new = new := by
    apply BitVec.eq_of_toNat_eq
    change (0#0).toNat <<< 64 ||| new.toNat = new.toNat
    simp
  simp [h3]

@[simp] theorem uint64_mk_bv (v : BitVec 64) :
  ({ toBitVec := v } : UInt64) = UInt64.ofBitVec v := by
  rfl

@[simp] theorem ext_hash_map_getElem_insert_eq (m : Std.ExtHashMap UInt64 UInt64) (k : UInt64) (v : UInt64) (h) :
  getElem (m.insert k v) k h = v := by
  simp
@[simp] theorem ext_hash_map_getElem_insert_ne (m : Std.ExtHashMap UInt64 UInt64) (k k' : UInt64) (v : UInt64) (h_ne : k ≠ k') (h1) (h2) :
  getElem (m.insert k v) k' h1 = getElem m k' h2 := by
  apply Option.some.inj
  have h3 : some (getElem (m.insert k v) k' h1) = (m.insert k v).get? k' := by simp
  have h4 : some (getElem m k' h2) = m.get? k' := by simp
  rw [h3, h4]
  simp [h_ne]

@[simp] theorem add_inj_left_eq_self (a b : UInt64) : (a + b = a) ↔ (b = 0) := by
  constructor
  · intro h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h; revert h2; change (a.toNat + b.toNat) % 18446744073709551616 = a.toNat → (b.toNat = 0); intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; omega
  · intro h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h; revert h2; change b.toNat = 0 → (a.toNat + b.toNat) % 18446744073709551616 = a.toNat; intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; omega

@[simp] theorem add_inj_right_eq_self (a b : UInt64) : (a = a + b) ↔ (b = 0) := by
  constructor
  · intro h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h; revert h2; change a.toNat = (a.toNat + b.toNat) % 18446744073709551616 → (b.toNat = 0); intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; omega
  · intro h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h; revert h2; change b.toNat = 0 → a.toNat = (a.toNat + b.toNat) % 18446744073709551616; intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; omega

@[simp] theorem add_inj_left_ne (a b c : UInt64) : (a + b ≠ a + c) ↔ (b ≠ c) := by
  constructor
  · intro h h_eq; apply h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h_eq; revert h2; change b.toNat = c.toNat → (a.toNat + b.toNat) % 18446744073709551616 = (a.toNat + c.toNat) % 18446744073709551616; intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; have h5 := UInt64.toNat_lt_size c; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; change c.toNat < 18446744073709551616 at h5; omega
  · intro h h_eq; apply h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h_eq; revert h2; change (a.toNat + b.toNat) % 18446744073709551616 = (a.toNat + c.toNat) % 18446744073709551616 → (b.toNat = c.toNat); intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; have h5 := UInt64.toNat_lt_size c; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; change c.toNat < 18446744073709551616 at h5; omega

@[simp] theorem add_inj_left_ne_self (a b : UInt64) : (a + b ≠ a) ↔ (b ≠ 0) := by
  constructor
  · intro h h_eq; apply h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h_eq; revert h2; change b.toNat = 0 → (a.toNat + b.toNat) % 18446744073709551616 = a.toNat; intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; omega
  · intro h h_eq; apply h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h_eq; revert h2; change (a.toNat + b.toNat) % 18446744073709551616 = a.toNat → (b.toNat = 0); intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; omega

@[simp] theorem add_inj_right_ne_self (a b : UInt64) : (a ≠ a + b) ↔ (b ≠ 0) := by
  constructor
  · intro h h_eq; apply h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h_eq; revert h2; change b.toNat = 0 → a.toNat = (a.toNat + b.toNat) % 18446744073709551616; intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; omega
  · intro h h_eq; apply h; apply UInt64.toNat_inj.1; have h2 := congrArg UInt64.toNat h_eq; revert h2; change a.toNat = (a.toNat + b.toNat) % 18446744073709551616 → (b.toNat = 0); intro h; have h3 := UInt64.toNat_lt_size a; have h4 := UInt64.toNat_lt_size b; change a.toNat < 18446744073709551616 at h3; change b.toNat < 18446744073709551616 at h4; omega

@[simp]
theorem bitvec_extract_eq (rdi : UInt64) :
  BitVec.extractLsb' 0 64 rdi.toBitVec = rdi.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  dsimp [BitVec.extractLsb']
  simp

@[simp]
theorem bitvec_zeroExtend_eq (x : BitVec 64) :
  BitVec.zeroExtend 64 x = x := by
  apply BitVec.eq_of_toNat_eq
  dsimp [BitVec.zeroExtend]
  simp
