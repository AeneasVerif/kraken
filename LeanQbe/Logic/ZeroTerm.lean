module

public import LeanQbe.Logic.Bytes
public import Kraken.Bedrock2.Test.LratTrimCheckProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Zero-terminated arrays of 32-bit integers

Kraken's `ZeroTermInts p xs` (`xs` followed by a `0`, as `int4` cells; `LratTrimSpec`) and
`zeroTermGet` (`LratTrimRupProof`), read by QBE loads: element `i` or the terminator
(`loadsw_zeroTerm`), the first word unsigned (`loaduw_zeroTerm_head`), the loop test `jnz` on a loaded
element (`zeroTerm_jnz_step`), and the bytes as a `region` (`zeroTermInts_to_region`).

This file is separate because of its imports: `zeroTermGet` and `zeroTermInts_split_head` live in
Kraken's LRAT proof files, which the rest of `LeanQbe/Logic/` does not need.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

open Std Std.ExtHashMap
open Kraken.Bedrock2.Test

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

theorem loaduw_zeroTerm_head {p : Val} {xs : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (ZeroTermInts p xs ⋆ R) m) :
    loadVal m .l .w false p = some (((xs ++ [0])[0]'(by simp)) &&& 0xffffffff#64) := by
  rw [zeroTermInts_split_head p xs, sep_assoc] at h
  exact loaduw_int4 h

theorem zeroTermGet_isInt32 {xs : List Val} (h32 : ∀ x ∈ xs, IsInt32 x) (i : Nat) :
    IsInt32 (zeroTermGet xs i) := by
  unfold zeroTermGet; split
  · exact h32 _ (List.getElem_mem _)
  · exact isInt32_zero

theorem zeroTerm_jnz_step {p : Val} {xs : List Val} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {T E : Val → Prop}
    (hi : i ≤ xs.length) (h32 : ∀ x ∈ xs, IsInt32 x) (hne0 : ∀ x ∈ xs, x ≠ 0)
    (hm : (ZeroTermInts p xs ⋆ R) m)
    (hnz : ∀ hlt : i < xs.length, T xs[i])
    (hz : i = xs.length → E 0) :
    ∃ v, loadVal m .l .w true (p + BitVec.ofNat 64 (4 * i)) = some v ∧
      ((Truthy v → T v) ∧ (¬ Truthy v → E v)) := by
  refine ⟨zeroTermGet xs i, loadsw_zeroTerm hi h32 hm, fun h => ?_, fun h => ?_⟩
  · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i)] at h
    have hlt := (zeroTermGet_ne_zero_iff hi hne0).1 h
    simpa [zeroTermGet, hlt] using hnz hlt
  · rw [truthy_iff _ (zeroTermGet_isInt32 h32 i), Classical.not_not] at h
    obtain rfl := (zeroTermGet_eq_zero_iff hi hne0).1 h
    simpa [zeroTermGet] using hz rfl

theorem zeroTermInts_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : 4 * (xs.length + 1) ≤ 2 ^ 64) (hf : ZeroTermInts a xs f) :
    region a (4 * (xs.length + 1)) f := by
  unfold ZeroTermInts at hf
  have hr := int4Array_to_region (by simpa using h) hf
  simpa using hr

end LeanQbe
