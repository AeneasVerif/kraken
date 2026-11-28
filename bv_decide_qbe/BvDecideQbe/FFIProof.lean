module

public import BvDecideQbe.FFI
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg

/-!
# Verified Byte-Packing Bridge: `packWordsArrayU32LE` ↔ `BVProg.wordsToBytesLE`

Closes Gap #2 (`bvdq_arisca_strategy_review.md` §3.2): proves with zero `sorry` (`≤ std3`) that
the FFI byte packers `packWordsU32LE` and `packWordsArrayU32LE` produce byte lists strictly equal
to `BVProg.wordsToBytesLE`.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open LeanQbe.T.Examples.Bitblast.Ref

private theorem packWordsU32LEGo_toList :
    ∀ (ws : List Nat) (ba res : ByteArray),
      packWordsU32LEGo ws ba = some res →
      res.toList = ba.toList ++ BVProg.wordsToBytesLE ws
  | [], ba, res, h => by
    simp only [packWordsU32LEGo, Option.some.injEq] at h
    subst h
    simp [BVProg.wordsToBytesLE]
  | w :: ws, ba, res, h => by
    unfold packWordsU32LEGo at h
    split at h
    · next hw =>
      have ih := packWordsU32LEGo_toList ws (pushWordU32LE ba w) res h
      rw [ih, pushWordU32LE_toList ba hw, BVProg.wordsToBytesLE]
      simp [List.append_assoc]
    · cases h

/-- `packWordsU32LE` produces the exact byte stream `BVProg.wordsToBytesLE ws`. -/
theorem packWordsU32LE_toList {ws : List Nat} {ba : ByteArray}
    (h : packWordsU32LE ws = some ba) :
    ba.toList = BVProg.wordsToBytesLE ws := by
  have hgo := packWordsU32LEGo_toList ws (ByteArray.emptyWithCapacity (ws.length * 4)) ba h
  have hempty : (ByteArray.emptyWithCapacity (ws.length * 4)).toList = [] := by
    rw [byteArray_toList_eq_data_toList]
    rfl
  rw [hempty, List.nil_append] at hgo
  exact hgo

/-- `packWordsArrayU32LE` produces the exact byte stream `BVProg.wordsToBytesLE ws.toList`. -/
theorem packWordsArrayU32LE_toList {ws : Array Nat} {ba : ByteArray}
    (h : packWordsArrayU32LE ws = some ba) :
    ba.toList = BVProg.wordsToBytesLE ws.toList := by
  rw [packWordsArrayU32LE_eq_packWordsU32LE] at h
  exact packWordsU32LE_toList h

private theorem packWordsU32LEGo_eq_some_iff :
    ∀ (ws : List Nat) (ba : ByteArray),
      (∃ res, packWordsU32LEGo ws ba = some res) ↔ ∀ w ∈ ws, w < BVProg.u32Bound
  | [], ba => by
    simp [packWordsU32LEGo]
  | w :: ws, ba => by
    unfold packWordsU32LEGo
    constructor
    · rintro ⟨res, h⟩ x hx
      split at h
      · next hw =>
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hw
        · exact (packWordsU32LEGo_eq_some_iff ws (pushWordU32LE ba w)).mp ⟨res, h⟩ x hmem
      · cases h
    · intro hall
      have hw : w < BVProg.u32Bound := hall w List.mem_cons_self
      have hws : ∀ x ∈ ws, x < BVProg.u32Bound := fun x hx => hall x (List.mem_cons_of_mem w hx)
      have hw' : w < bvProgU32Bound := hw
      simp only [hw', ↓reduceIte]
      exact (packWordsU32LEGo_eq_some_iff ws (pushWordU32LE ba w)).mpr hws

/-- `packWordsArrayU32LE ws` succeeds iff every word in `ws` is strictly below `2^32`. -/
theorem packWordsArrayU32LE_eq_some_iff (ws : Array Nat) :
    (∃ ba, packWordsArrayU32LE ws = some ba) ↔ ∀ w ∈ ws.toList, w < BVProg.u32Bound := by
  rw [packWordsArrayU32LE_eq_packWordsU32LE]
  exact packWordsU32LEGo_eq_some_iff ws.toList (ByteArray.emptyWithCapacity (ws.toList.length * 4))

end BvDecideQbe
