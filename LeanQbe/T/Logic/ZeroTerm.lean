module

public import LeanQbe.T.Logic.Bytes
public import Kraken.Bedrock2.Test.LratTrimCheckProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Zero-terminated arrays of 32-bit integers for `LeanQbe.T` (`T4`)

Typed-IR counterpart of `LeanQbe/Logic/ZeroTerm.lean` over `ZeroTermInts` and `zeroTermGet`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std Std.ExtHashMap
open Kraken.Bedrock2.Test

theorem load_zeroTerm {p : BitVec 64} {xs : List (BitVec 64)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i ≤ xs.length) (h : (ZeroTermInts p xs ⋆ R) m) :
    loadVal m i32 (p + BitVec.ofNat 64 (4 * i)) = some ((zeroTermGet xs i).setWidth 32) := by
  unfold zeroTermGet; split
  · rename_i hlt
    rw [zeroTermInts_focus_elem p xs hlt, sep_assoc] at h
    exact load_int4 h
  · obtain rfl : i = xs.length := by omega
    rw [zeroTermInts_focus_end p xs, sep_assoc] at h
    exact load_int4 h

theorem load_zeroTerm_head {p : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (ZeroTermInts p xs ⋆ R) m) :
    loadVal m i32 p = some (((xs ++ [0])[0]'(by simp)).setWidth 32) := by
  rw [zeroTermInts_split_head p xs, sep_assoc] at h
  exact load_int4 h

theorem zeroTermGet_isInt32 {xs : List (BitVec 64)} (h32 : ∀ x ∈ xs, IsInt32 x) (i : Nat) :
    IsInt32 (zeroTermGet xs i) := by
  unfold zeroTermGet; split
  · exact h32 _ (List.getElem_mem _)
  · exact isInt32_zero

theorem zeroTerm_jnz_step {p : BitVec 64} {xs : List (BitVec 64)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {T E : BitVec 32 → Prop}
    (hi : i ≤ xs.length) (h32 : ∀ x ∈ xs, IsInt32 x) (hne0 : ∀ x ∈ xs, x ≠ 0)
    (hm : (ZeroTermInts p xs ⋆ R) m)
    (hnz : ∀ hlt : i < xs.length, T (xs[i].setWidth 32))
    (hz : i = xs.length → E 0#32) :
    ∃ v, loadVal m i32 (p + BitVec.ofNat 64 (4 * i)) = some v ∧
      ((v ≠ 0#32 → T v) ∧ (v = 0#32 → E v)) := by
  refine ⟨(zeroTermGet xs i).setWidth 32, load_zeroTerm hi hm, fun hne => ?_, fun heq => ?_⟩
  · have hnz64 : zeroTermGet xs i ≠ 0 := by
      intro hz0
      apply hne
      simp [hz0]
    have hlt := (zeroTermGet_ne_zero_iff hi hne0).1 hnz64
    simpa [zeroTermGet, hlt] using hnz hlt
  · have hz64 : zeroTermGet xs i = 0 := by
      have hi32 := zeroTermGet_isInt32 h32 i
      have hsext := sext32 (zeroTermGet xs i) hi32
      rw [heq] at hsext
      simpa using hsext.symm
    obtain rfl := (zeroTermGet_eq_zero_iff hi hne0).1 hz64
    simpa [zeroTermGet] using hz rfl

theorem zeroTermInts_to_region {a : BitVec 64} {xs : List (BitVec 64)} {f : Mem 64}
    (h : 4 * (xs.length + 1) ≤ 2 ^ 64) (hf : ZeroTermInts a xs f) :
    region a (4 * (xs.length + 1)) f := by
  unfold ZeroTermInts at hf
  have hr := int4Array_to_region (by simpa using h) hf
  simpa using hr

end LeanQbe.T
