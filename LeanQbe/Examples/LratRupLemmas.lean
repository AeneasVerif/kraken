module

public import LeanQbe.Examples.LratRup
public import LeanQbe.Logic.MemLemmas
public import LeanQbe.Logic.Rules
public import Kraken.Bedrock2.Test.LratTrimRupProof
public import Kraken.SeparationTactics

/-!
# The RUP check: correctness

The specification is the one of Kraken's `br_check_clause_non_strictly_by_propagation_ok`
(`LratTrimRupProof.lean`), with `lrat_fail` an `exit` (decision D5). The model and memory predicates
(`assignBytes`, `ClauseTable`, `ZeroTermInts`, `kernelState`, `byte1Array`, …) and the pure RUP lemmas
(`phase1_step_*`, `phase2_inner_*`, `entails_insert_of_unit_prop`, …) are imported from there unchanged;
everything about the program is new.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratRup

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test

/-! ## Bit-level facts -/

theorem sar63 (lit : Val) : lit.sshiftRight 63 = if lit.slt 0 then -1 else 0 := by
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_sshiftRight, BitVec.slt]
  split <;> simp <;> grind

theorem negif (b : Val) (c : Bool) :
    (b ^^^ (if c then -1 else 0)) - (if c then -1 else 0) = if c then -b else b := by
  cases c <;> simp [BitVec.neg_eq_not_add, BitVec.sub_eq_add_neg]
  exact BitVec.xor_allOnes

theorem abs_eq (lit : Val) : (lit ^^^ lit.sshiftRight 63) - lit.sshiftRight 63 = bvAbs lit := by
  rw [sar63, negif]; rfl

theorem negif_eq (b lit : Val) : (b ^^^ lit.sshiftRight 63) - lit.sshiftRight 63 = evalAssignedLit b lit := by
  rw [sar63, negif]; rfl

theorem sext8 (v : Val) (h : IsInt8 v) :
    (BitVec.setWidth 8 (BitVec.ofInt 64 ((v.toNat : Int).take 8))).signExtend 64 = v := by
  have : BitVec.ofInt 64 ((v.toNat : Int).take 8) = (v.setWidth 8).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq; simp [Int.take]; omega
  rw [this]; unfold IsInt8 at h; grind

theorem sext32 (v : Val) (h : IsInt32 v) :
    (BitVec.setWidth 32 (BitVec.ofInt 64 ((v.toNat : Int).take 32))).signExtend 64 = v := by
  have : BitVec.ofInt 64 ((v.toNat : Int).take 32) = (v.setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq; simp [Int.take]; omega
  rw [this]; unfold IsInt32 at h; grind

theorem truthy_iff (v : Val) (h : IsInt32 v) : Truthy v ↔ v ≠ 0 := by
  unfold Truthy IsInt32 at *; constructor <;> intro h1 h2 <;> apply h1 <;> grind

/-! ## Memory: Kraken's cells read and written by QBE loads and stores -/

theorem loadsb_byte1 {a v : Val} {R : Mem 64 → Prop} {m : Mem 64} (h : (byte1 a v ⋆ R) m)
    (hv : IsInt8 v) : loadVal m .l .b true a = some v := by
  rw [loadVal_toBytes (s := .b) h]; exact congrArg some (sext8 v hv)

theorem loadsw_int4 {a v : Val} {R : Mem 64 → Prop} {m : Mem 64} (h : (int4 a v ⋆ R) m)
    (hv : IsInt32 v) : loadVal m .l .w true a = some v := by
  rw [loadVal_toBytes (s := .w) h]; exact congrArg some (sext32 v hv)

theorem loadl_word8 {a v : Val} {sg : Bool} {R : Mem 64 → Prop} {m : Mem 64} (h : (word8 a v ⋆ R) m) :
    loadVal m .l .l sg a = some v := by
  rw [loadVal_toBytes (s := .l) h]
  simp only [Sz.bytes, Int.take, Cls.trunc, Sz.extend]
  rw [Int.emod_eq_of_lt (by omega) (by have := v.isLt; omega)]
  exact congrArg some (BitVec.eq_of_toNat_eq (by simp))

theorem store_byte1 {a v0 : Val} (v : Val) {R : Mem 64 → Prop} {m : Mem 64} (h : (byte1 a v0 ⋆ R) m) :
    storeOk m .b a ∧ (byte1 a v ⋆ R) (storeMem m .b a v) := store_toBytes (s := .b) v h

theorem store_int4 {a v0 : Val} (v : Val) {R : Mem 64 → Prop} {m : Mem 64} (h : (int4 a v0 ⋆ R) m) :
    storeOk m .w a ∧ (int4 a v ⋆ R) (storeMem m .w a v) := store_toBytes (s := .w) v h

theorem store_word8 {a v0 : Val} (v : Val) {R : Mem 64 → Prop} {m : Mem 64} (h : (word8 a v0 ⋆ R) m) :
    storeOk m .l a ∧ (word8 a v ⋆ R) (storeMem m .l a v) := store_toBytes (s := .l) v h

theorem loadsb_byte1Array {a : Val} {xs : List Val} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < xs.length) (hv : IsInt8 xs[i]) (h : (byte1Array a xs ⋆ R) m) :
    loadVal m .l .b true (a + BitVec.ofNat 64 i) = some xs[i] := by
  rw [byte1Array_focus a xs hi, sep_assoc] at h; exact loadsb_byte1 h hv

theorem storeb_byte1Array {a : Val} {xs : List Val} {i : Nat} (v : Val) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (byte1Array a xs ⋆ R) m) :
    storeOk m .b (a + BitVec.ofNat 64 i) ∧
      (byte1Array a (xs.set i v) ⋆ R) (storeMem m .b (a + BitVec.ofNat 64 i) v) := by
  rw [byte1Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_byte1 v h
  exact ⟨h1, by rwa [byte1Array_set a xs hi, sep_assoc]⟩

theorem storew_int4Array {a : Val} {xs : List Val} {i : Nat} (v : Val) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (int4Array a xs ⋆ R) m) :
    storeOk m .w (a + BitVec.ofNat 64 (4 * i)) ∧
      (int4Array a (xs.set i v) ⋆ R) (storeMem m .w (a + BitVec.ofNat 64 (4 * i)) v) := by
  rw [int4Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_int4 v h
  exact ⟨h1, by rwa [int4Array_set a xs hi, sep_assoc]⟩

theorem loadl_word8Array {a : Val} {xs : List Val} {i : Nat} {sg : Bool} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m) :
    loadVal m .l .l sg (a + BitVec.ofNat 64 (8 * i)) = some xs[i] := by
  rw [word8Array_focus a xs hi, sep_assoc] at h; exact loadl_word8 h

theorem storel_word8Array {a : Val} {xs : List Val} {i : Nat} (v : Val) {R : Mem 64 → Prop}
    {m : Mem 64} (hi : i < xs.length) (h : (word8Array a xs ⋆ R) m) :
    storeOk m .l (a + BitVec.ofNat 64 (8 * i)) ∧
      (word8Array a (xs.set i v) ⋆ R) (storeMem m .l (a + BitVec.ofNat 64 (8 * i)) v) := by
  rw [word8Array_focus a xs hi, sep_assoc] at h
  obtain ⟨h1, h2⟩ := store_word8 v h
  exact ⟨h1, by rwa [word8Array_set a xs hi, sep_assoc]⟩

theorem loadsw_zeroTerm {p : Val} {xs : List Val} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i ≤ xs.length) (h32 : ∀ x ∈ xs, IsInt32 x) (h : (ZeroTermInts p xs ⋆ R) m) :
    loadVal m .l .w true (p + BitVec.ofNat 64 (4 * i)) = some (zeroTermGet xs i) := by
  unfold zeroTermGet; split
  · rename_i hlt
    rw [zeroTermInts_focus_elem p xs hlt, sep_assoc] at h
    exact loadsw_int4 h (h32 _ (List.getElem_mem hlt))
  · obtain rfl : i = xs.length := by omega
    rw [zeroTermInts_focus_end p xs, sep_assoc] at h
    exact loadsw_int4 h isInt32_zero

end LeanQbe.LratRup
