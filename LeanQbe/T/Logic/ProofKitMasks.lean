module

public import LeanQbe.T.Logic.C0StepAttr
public meta import Lean.Elab.Tactic

/-!
# `ProofKitMasks`: Pure-Kernel Bitmask Orthogonality & Packed-Word (`PWordKit`) Automation

Strictly pure-kernel (`[propext, Classical.choice, Quot.sound]` only — no boolean reflection or
external SAT tactics) bitmask and packed-field lemmas + tactics:

1. **`KissatHdrBitMaskKit`**: general orthogonality identities for arbitrary width `w`:
   * `(x &&& ~~~m1) &&& m2 = x &&& m2` under `(m1 &&& m2) = 0#w`
   * `(x ||| v) &&& m2 = x &&& m2` under `(v &&& m2) = 0#w`
   * Single-bit test/set/clear/toggle orthogonality (`1#w <<< k`) via `BitVec.getLsbD`
   * Non-sentinel / non-zero witnesses (`x ≠ BitVec.allOnes w`, `≠ 0#w`)
2. **`PWordKit`**: packed-field extract/update identities (`BitVec.ofNat w (2 ^ len - 1) <<< off`),
   Kissat 32-bit `pword` bit-31 / 23-bit / 19-bit arena header masks, and 64-bit flag packing.
3. **`pword_mask` tactic & `@[bv_c0]` mask-to-`Nat` normalizations**: pure-kernel closed mask
   simproc + distributive/orthogonality simplification + `getLsbD` extensionality.
-/

set_option autoImplicit false

namespace LeanQbe.T.ProofKit

/-! ## 1. `KissatHdrBitMaskKit`: General Pure-Kernel Bitmask Orthogonality -/

public section

namespace KissatHdrBitMaskKit

private theorem bit_false_of_and_zero {w : Nat} {a b : BitVec w} (h : (a &&& b) = 0#w)
    (i : Nat) (ha : a.getLsbD i = true) : b.getLsbD i = false := by
  have hi := congrArg (fun v : BitVec w => v.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, ha, Bool.true_and] at hi
  exact hi

private theorem bit_false_of_and_zero_left {w : Nat} {a b : BitVec w} (h : (a &&& b) = 0#w)
    (i : Nat) (hb : b.getLsbD i = true) : a.getLsbD i = false := by
  have hi := congrArg (fun v : BitVec w => v.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hb, Bool.and_true] at hi
  exact hi

theorem bv_and_not_and_of_disjoint {w : Nat} {x m1 m2 : BitVec w} (h : (m1 &&& m2) = 0#w) :
    ((x &&& ~~~m1) &&& m2) = (x &&& m2) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases hm2 : m2.getLsbD i
  · simp
  · have hm1 : m1.getLsbD i = false := bit_false_of_and_zero_left h i hm2
    simp [hm1]

theorem bv_and_not_and_right_of_disjoint {w : Nat} {x m1 m2 : BitVec w}
    (h : (m2 &&& m1) = 0#w) :
    ((x &&& ~~~m1) &&& m2) = (x &&& m2) :=
  bv_and_not_and_of_disjoint (by rwa [BitVec.and_comm])

theorem bv_or_and_of_disjoint {w : Nat} {x v m2 : BitVec w} (h : (v &&& m2) = 0#w) :
    ((x ||| v) &&& m2) = (x &&& m2) := by
  rw [BitVec.and_or_distrib_right, h, BitVec.or_zero]

theorem bv_or_and_left_of_disjoint {w : Nat} {x v m2 : BitVec w} (h : (m2 &&& v) = 0#w) :
    ((x ||| v) &&& m2) = (x &&& m2) :=
  bv_or_and_of_disjoint (by rwa [BitVec.and_comm])

theorem bv_or_and_mask_of_disjoint {w : Nat} {x v m1 m2 : BitVec w}
    (h : (m1 &&& m2) = 0#w) (hv : (v &&& m1) = v) :
    ((x ||| v) &&& m2) = (x &&& m2) := by
  have hvm2 : (v &&& m2) = 0#w := by
    calc
      v &&& m2 = (v &&& m1) &&& m2 := by rw [hv]
      _ = v &&& (m1 &&& m2) := BitVec.and_assoc v m1 m2
      _ = 0#w := by rw [h, BitVec.and_zero]
  exact bv_or_and_of_disjoint hvm2

theorem bv_and_or_and_of_disjoint {w : Nat} {x v m1 m2 : BitVec w} (h : (m1 &&& m2) = 0#w) :
    (((x &&& ~~~m1) ||| v) &&& m2) = ((x &&& m2) ||| (v &&& m2)) := by
  rw [BitVec.and_or_distrib_right, bv_and_not_and_of_disjoint h]

theorem bv_clear_or_and_self {w : Nat} {x v m : BitVec w} (hv : (v &&& m) = v) :
    (((x &&& ~~~m) ||| v) &&& m) = v := by
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.not_and_self]
  simp [hv]

theorem bv_clear_or_and_other {w : Nat} {x v m1 m2 : BitVec w}
    (h : (m1 &&& m2) = 0#w) (hv : (v &&& m2) = 0#w) :
    (((x &&& ~~~m1) ||| v) &&& m2) = (x &&& m2) := by
  rw [bv_and_or_and_of_disjoint h, hv, BitVec.or_zero]

theorem bv_clear_or_and_other_sub {w : Nat} {x v m1 m2 : BitVec w}
    (h : (m1 &&& m2) = 0#w) (hv : (v &&& m1) = v) :
    (((x &&& ~~~m1) ||| v) &&& m2) = (x &&& m2) := by
  rw [BitVec.and_or_distrib_right, bv_and_not_and_of_disjoint h]
  have hvm2 : (v &&& m2) = 0#w := by
    rw [← hv, BitVec.and_assoc, h]
    simp
  rw [hvm2, BitVec.or_zero]

theorem bv_and_or_self {w : Nat} (x m : BitVec w) :
    ((x &&& m) ||| m) = m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases _ : x.getLsbD i <;> cases _ : m.getLsbD i <;> simp

theorem bv_or_self_and {w : Nat} (x m : BitVec w) :
    (m ||| (x &&& m)) = m := by
  rw [BitVec.or_comm, bv_and_or_self]

theorem bv_and_eq_zero_of_submask {w : Nat} {v m1 m2 : BitVec w}
    (hv : (v &&& m1) = v) (hd : (m1 &&& m2) = 0#w) :
    (v &&& m2) = 0#w := by
  rw [← hv, BitVec.and_assoc, hd, BitVec.and_zero]

theorem bv_clear_or_and_not_self {w : Nat} {x v m : BitVec w} (hv : (v &&& m) = v) :
    (((x &&& ~~~m) ||| v) &&& ~~~m) = (x &&& ~~~m) := by
  have hvnot : (v &&& ~~~m) = 0#w := by
    rw [← hv, BitVec.and_assoc, BitVec.and_not_self]
    simp
  rw [BitVec.and_or_distrib_right, hvnot, BitVec.or_zero, BitVec.and_assoc, BitVec.and_self]

theorem bv_clear_idem {w : Nat} (x m : BitVec w) : (x &&& ~~~m) &&& ~~~m = x &&& ~~~m := by
  rw [BitVec.and_assoc, BitVec.and_self]

theorem bv_and_idem {w : Nat} (x m : BitVec w) : (x &&& m) &&& m = x &&& m := by
  rw [BitVec.and_assoc, BitVec.and_self]

theorem bv_or_idem {w : Nat} (x m : BitVec w) : (x ||| m) ||| m = x ||| m := by
  rw [BitVec.or_assoc, BitVec.or_self]

theorem bv_and_submask_eq_zero {w : Nat} {x m sub : BitVec w}
    (hsub : (m &&& sub) = sub) (hx : (x &&& m) = 0#w) :
    (x &&& sub) = 0#w := by
  calc
    x &&& sub = x &&& (m &&& sub) := by rw [hsub]
    _ = (x &&& m) &&& sub := (BitVec.and_assoc x m sub).symm
    _ = 0#w := by rw [hx, BitVec.zero_and]

theorem bv_and_or_eq_zero_iff {w : Nat} (x m1 m2 : BitVec w) :
    (x &&& (m1 ||| m2)) = 0#w ↔ (x &&& m1) = 0#w ∧ (x &&& m2) = 0#w := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_getLsbD_eq; intro i hi
      have h0 := congrArg (fun v : BitVec w => v.getLsbD i) h
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at h0 ⊢
      cases hx : x.getLsbD i <;> simp_all
    · apply BitVec.eq_of_getLsbD_eq; intro i hi
      have h0 := congrArg (fun v : BitVec w => v.getLsbD i) h
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at h0 ⊢
      cases hx : x.getLsbD i <;> simp_all
  · rintro ⟨h1, h2⟩
    rw [BitVec.and_comm, BitVec.and_or_distrib_right, BitVec.and_comm m1 x, h1,
      BitVec.and_comm m2 x, h2, BitVec.or_zero]

theorem bv_or_and_self_ne_zero {w : Nat} {x m : BitVec w} (hm : m ≠ 0#w) :
    ((x ||| m) &&& m) ≠ 0#w := by
  intro he
  rw [BitVec.and_or_distrib_right, BitVec.and_self] at he
  apply hm
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have h0 := congrArg (fun v : BitVec w => v.getLsbD i) he
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.or_eq_false_iff] at h0
  simp [h0.2]

theorem bv_ne_allOnes_of_getLsbD_false {w : Nat} {x : BitVec w} {k : Nat}
    (hk : k < w) (hf : x.getLsbD k = false) :
    x ≠ BitVec.allOnes w := by
  intro he
  have hbit := congrArg (fun v : BitVec w => v.getLsbD k) he
  simp only [BitVec.getLsbD_allOnes, hk, decide_true, hf] at hbit
  exact Bool.false_ne_true hbit

theorem bv_ne_allOnes_of_disjoint {w : Nat} {x m : BitVec w}
    (hm : m ≠ 0#w) (hz : (x &&& m) = 0#w) :
    x ≠ BitVec.allOnes w := by
  intro he
  rw [he, BitVec.allOnes_and] at hz
  exact hm hz

theorem bv_or_ne_zero_of_right {w : Nat} {x m : BitVec w} (hm : m ≠ 0#w) :
    (x ||| m) ≠ 0#w := by
  intro he
  have h := congrArg (· &&& m) he
  rw [BitVec.zero_and] at h
  exact bv_or_and_self_ne_zero hm h

theorem bv_or_ne_zero_of_left {w : Nat} {x m : BitVec w} (hm : m ≠ 0#w) :
    (m ||| x) ≠ 0#w := by
  rw [BitVec.or_comm]
  exact bv_or_ne_zero_of_right hm

theorem bv_ne_of_and_ne {w : Nat} {x y m : BitVec w}
    (hne : (x &&& m) ≠ (y &&& m)) : x ≠ y := by
  intro h; apply hne; rw [h]

/-! ### Single-Bit Test / Set / Clear / Toggle Orthogonality (`1#w <<< k`) -/

theorem bv_getLsbD_bitmask {w k : Nat} (hk : k < w) (i : Nat) :
    (1#w <<< k).getLsbD i = decide (i = k) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
  have hw0 : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  by_cases hik : i = k
  · subst hik
    simp [hk, hw0]
  · by_cases hiw : i < w <;> by_cases hik_lt : i < k
    · simp [hiw, hik_lt, hw0, hik]
    · have hne0 : i - k ≠ 0 := by omega
      simp [hiw, hik_lt, hw0, hne0, hik]
    · simp [hiw, hik]
    · simp [hiw, hik]

theorem bv_bitmask_disjoint_of_ne {w k j : Nat} (hk : k < w) (hj : j < w) (hne : k ≠ j) :
    ((1#w <<< k) &&& (1#w <<< j)) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, bv_getLsbD_bitmask hk, bv_getLsbD_bitmask hj, BitVec.getLsbD_zero]
  by_cases hik : i = k
  · subst hik; simp [hne]
  · simp [hik]

theorem bv_and_bit_eq_zero_iff {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) :
    (x &&& (1#w <<< k)) = 0#w ↔ x.getLsbD k = false := by
  constructor
  · intro h
    have hk0 := congrArg (fun v : BitVec w => v.getLsbD k) h
    simp only [BitVec.getLsbD_and, bv_getLsbD_bitmask hk, decide_true, Bool.and_true,
      BitVec.getLsbD_zero] at hk0
    exact hk0
  · intro hf
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_and, bv_getLsbD_bitmask hk, BitVec.getLsbD_zero]
    by_cases hik : i = k
    · subst hik; simp [hf]
    · simp [hik]

theorem bv_and_bit_ne_zero_iff {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) :
    (x &&& (1#w <<< k)) ≠ 0#w ↔ x.getLsbD k = true := by
  rw [ne_eq, bv_and_bit_eq_zero_iff x hk, Bool.not_eq_false]

theorem bv_set_bit_getLsbD {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) (i : Nat) :
    (x ||| (1#w <<< k)).getLsbD i = if i = k then true else x.getLsbD i := by
  rw [BitVec.getLsbD_or, bv_getLsbD_bitmask hk]
  by_cases hik : i = k <;> simp [hik]

theorem bv_clear_bit_getLsbD {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w)
    {i : Nat} (hi : i < w) :
    (x &&& ~~~(1#w <<< k)).getLsbD i = if i = k then false else x.getLsbD i := by
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, bv_getLsbD_bitmask hk]
  by_cases hik : i = k <;> simp [hik, hi]

theorem bv_toggle_bit_getLsbD {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) (i : Nat) :
    (x ^^^ (1#w <<< k)).getLsbD i = if i = k then !x.getLsbD i else x.getLsbD i := by
  rw [BitVec.getLsbD_xor, bv_getLsbD_bitmask hk]
  by_cases hik : i = k <;> simp [hik]

theorem bv_set_bit_getLsbD_self {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) :
    (x ||| (1#w <<< k)).getLsbD k = true := by
  simp [bv_set_bit_getLsbD x hk k]

theorem bv_set_bit_getLsbD_ne {w : Nat} (x : BitVec w) {k i : Nat} (hk : k < w) (hne : i ≠ k) :
    (x ||| (1#w <<< k)).getLsbD i = x.getLsbD i := by
  simp [bv_set_bit_getLsbD x hk i, hne]

theorem bv_clear_bit_getLsbD_self {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) :
    (x &&& ~~~(1#w <<< k)).getLsbD k = false := by
  simp [bv_clear_bit_getLsbD x hk hk]

theorem bv_clear_bit_getLsbD_ne {w : Nat} (x : BitVec w) {k i : Nat}
    (hk : k < w) (hi : i < w) (hne : i ≠ k) :
    (x &&& ~~~(1#w <<< k)).getLsbD i = x.getLsbD i := by
  simp [bv_clear_bit_getLsbD x hk hi, hne]

theorem bv_set_bit_test_self {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) :
    ((x ||| (1#w <<< k)) &&& (1#w <<< k)) ≠ 0#w := by
  rw [bv_and_bit_ne_zero_iff _ hk]
  exact bv_set_bit_getLsbD_self x hk

theorem bv_clear_bit_test_self {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) :
    ((x &&& ~~~(1#w <<< k)) &&& (1#w <<< k)) = 0#w := by
  rw [bv_and_bit_eq_zero_iff _ hk]
  exact bv_clear_bit_getLsbD_self x hk

theorem bv_set_bit_test_ne {w : Nat} (x : BitVec w) {k j : Nat}
    (hk : k < w) (hj : j < w) (hne : k ≠ j) :
    ((x ||| (1#w <<< k)) &&& (1#w <<< j)) = (x &&& (1#w <<< j)) :=
  bv_or_and_of_disjoint (bv_bitmask_disjoint_of_ne hk hj hne)

theorem bv_clear_bit_test_ne {w : Nat} (x : BitVec w) {k j : Nat}
    (hk : k < w) (hj : j < w) (hne : k ≠ j) :
    ((x &&& ~~~(1#w <<< k)) &&& (1#w <<< j)) = (x &&& (1#w <<< j)) :=
  bv_and_not_and_of_disjoint (bv_bitmask_disjoint_of_ne hk hj hne)

theorem bv_toggle_bit_test_ne {w : Nat} (x : BitVec w) {k j : Nat}
    (hk : k < w) (hj : j < w) (hne : k ≠ j) :
    ((x ^^^ (1#w <<< k)) &&& (1#w <<< j)) = (x &&& (1#w <<< j)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, bv_getLsbD_bitmask hk,
    bv_getLsbD_bitmask hj]
  by_cases hij : i = j
  · subst hij; simp [hne.symm]
  · simp [hij]

theorem bv_ne_allOnes_of_and_bit_zero {w : Nat} {x : BitVec w} {k : Nat}
    (hk : k < w) (hz : (x &&& (1#w <<< k)) = 0#w) :
    x ≠ BitVec.allOnes w :=
  bv_ne_allOnes_of_getLsbD_false hk ((bv_and_bit_eq_zero_iff x hk).mp hz)

end KissatHdrBitMaskKit

/-! ## 2. `PWordKit`: Packed-Field Mask Extract/Update & Kissat Header Helpers -/

namespace PWordKit

open KissatHdrBitMaskKit

theorem bv_mask_low_bits_toNat {w k : Nat} (x : BitVec w) (hk : k ≤ w) :
    (x &&& BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  have hlt : 2 ^ k - 1 < 2 ^ w := by
    have hp : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hk
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.and_two_pow_sub_one_eq_mod]

theorem bv_mask_low_bits_eq_self {w k : Nat} {x : BitVec w}
    (hk : k ≤ w) (hx : x.toNat < 2 ^ k) :
    (x &&& BitVec.ofNat w (2 ^ k - 1)) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_mask_low_bits_toNat x hk, Nat.mod_eq_of_lt hx]

theorem bv_getLsbD_lowMask {w k : Nat} (hk : k ≤ w) (i : Nat) :
    (BitVec.ofNat w (2 ^ k - 1)).getLsbD i = decide (i < k) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hik : i < k
  · have hiw : i < w := Nat.lt_of_lt_of_le hik hk
    simp [hik, hiw]
  · simp [hik]

theorem bv_getLsbD_fieldMask {w off len : Nat} (hlen : off + len ≤ w) (i : Nat) :
    (BitVec.ofNat w (2 ^ len - 1) <<< off).getLsbD i =
      decide (off ≤ i ∧ i < off + len) := by
  rw [BitVec.getLsbD_shiftLeft, bv_getLsbD_lowMask (Nat.le_trans (Nat.le_add_left len off) hlen)]
  by_cases hoff : off ≤ i
  · by_cases hhi : i < off + len
    · have hiw : i < w := Nat.lt_of_lt_of_le hhi hlen
      have hil : i - off < len := by omega
      simp [hoff, hhi, hiw, hil, show ¬ (i < off) by omega]
    · simp [hoff, hhi, show ¬ (i - off < len) by omega]
  · simp [hoff, show i < off by omega]

theorem bv_fieldMask_disjoint_of_le {w off₁ len₁ off₂ len₂ : Nat}
    (h1 : off₁ + len₁ ≤ w) (h2 : off₂ + len₂ ≤ w) (hdisj : off₁ + len₁ ≤ off₂) :
    ((BitVec.ofNat w (2 ^ len₁ - 1) <<< off₁) &&&
      (BitVec.ofNat w (2 ^ len₂ - 1) <<< off₂)) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_and, bv_getLsbD_fieldMask h1, bv_getLsbD_fieldMask h2, BitVec.getLsbD_zero]
  by_cases h1i : off₁ ≤ i ∧ i < off₁ + len₁
  · have : ¬ (off₂ ≤ i ∧ i < off₂ + len₂) := by omega
    simp [h1i, this]
  · simp [h1i]

theorem bv_fieldMask_disjoint {w off₁ len₁ off₂ len₂ : Nat}
    (h1 : off₁ + len₁ ≤ w) (h2 : off₂ + len₂ ≤ w)
    (hdisj : off₁ + len₁ ≤ off₂ ∨ off₂ + len₂ ≤ off₁) :
    ((BitVec.ofNat w (2 ^ len₁ - 1) <<< off₁) &&&
      (BitVec.ofNat w (2 ^ len₂ - 1) <<< off₂)) = 0#w := by
  rcases hdisj with hl | hr
  · exact bv_fieldMask_disjoint_of_le h1 h2 hl
  · rw [BitVec.and_comm]
    exact bv_fieldMask_disjoint_of_le h2 h1 hr

theorem bv_field_val_in_mask {w off len : Nat} {v : BitVec w}
    (hlen : off + len ≤ w) (hv : v.toNat < 2 ^ len) :
    ((v <<< off) &&& (BitVec.ofNat w (2 ^ len - 1) <<< off)) = (v <<< off) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_and, bv_getLsbD_fieldMask hlen, BitVec.getLsbD_shiftLeft]
  by_cases hiw : i < w
  · by_cases hioff : i < off
    · simp [hiw, hioff]
    · by_cases hlen' : i - off < len
      · have : off ≤ i ∧ i < off + len := by omega
        simp [hiw, hioff, this]
      · have hge : len ≤ i - off := Nat.not_lt.mp hlen'
        have hv0 : v.getLsbD (i - off) = false := by
          rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat]
          exact Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hge))
        simp [hv0]
  · simp [hiw]

theorem bv_packed_extract_self {w off len : Nat} {v : BitVec w}
    (hlen : off + len ≤ w) (hv : v.toNat < 2 ^ len) :
    ((v <<< off) >>> off) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hlt : i < len
  · have hw : off + i < w := by omega
    simp [hw, show ¬ (off + i < off) by omega, Nat.add_sub_cancel_left]
  · have hv_false : v.getLsbD i = false := by
      rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hlt)))
    rw [hv_false]
    by_cases hw : off + i < w
    · simp [hw, show ¬ (off + i < off) by omega, Nat.add_sub_cancel_left, hv_false]
    · simp [hw]

theorem bv_packed_extract_clear_or {w off len : Nat} (x v : BitVec w)
    (hlen : off + len ≤ w) (hv : v.toNat < 2 ^ len) :
    let mask := BitVec.ofNat w (2 ^ len - 1) <<< off
    (((x &&& ~~~mask) ||| (v <<< off)) &&& mask) >>> off = v := by
  intro mask
  rw [bv_clear_or_and_self (bv_field_val_in_mask hlen hv)]
  exact bv_packed_extract_self hlen hv

theorem bv_packed_extract_other {w off₁ len₁ off₂ len₂ : Nat} (x v : BitVec w)
    (h1 : off₁ + len₁ ≤ w) (h2 : off₂ + len₂ ≤ w)
    (hdisj : off₁ + len₁ ≤ off₂ ∨ off₂ + len₂ ≤ off₁) (hv : v.toNat < 2 ^ len₁) :
    let m1 := BitVec.ofNat w (2 ^ len₁ - 1) <<< off₁
    let m2 := BitVec.ofNat w (2 ^ len₂ - 1) <<< off₂
    ((((x &&& ~~~m1) ||| (v <<< off₁)) &&& m2) >>> off₂) = ((x &&& m2) >>> off₂) := by
  intro m1 m2
  rw [bv_clear_or_and_other_sub (bv_fieldMask_disjoint h1 h2 hdisj) (bv_field_val_in_mask h1 hv)]

theorem bv_packed_update_getLsbD_in {w off len : Nat} (x v : BitVec w)
    (hlen : off + len ≤ w) (hv : v.toNat < 2 ^ len) {i : Nat}
    (hlo : off ≤ i) (hhi : i < off + len) :
    let mask := BitVec.ofNat w (2 ^ len - 1) <<< off
    ((x &&& ~~~mask) ||| (v <<< off)).getLsbD i = v.getLsbD (i - off) := by
  intro mask
  have hm := congrArg (fun z : BitVec w => z.getLsbD i)
    (bv_clear_or_and_self (x := x) (bv_field_val_in_mask hlen hv))
  have hmask : mask.getLsbD i = true := by
    dsimp only [mask]
    rw [bv_getLsbD_fieldMask hlen]
    exact decide_eq_true ⟨hlo, hhi⟩
  have hnot : ¬ (i < off) := by omega
  have hiw : i < w := Nat.lt_of_lt_of_le hhi hlen
  have hm' : ((x &&& ~~~mask) ||| (v <<< off)).getLsbD i = (v <<< off).getLsbD i := by
    have := hm
    dsimp only [mask] at hmask ⊢
    rw [BitVec.getLsbD_and, hmask, Bool.and_true] at this
    exact this
  rw [hm', BitVec.getLsbD_shiftLeft]
  simp [hiw, hnot]

theorem bv_packed_update_getLsbD_out {w off len : Nat} (x v : BitVec w)
    (hlen : off + len ≤ w) (hv : v.toNat < 2 ^ len) {i : Nat} (hi : i < w)
    (hout : i < off ∨ off + len ≤ i) :
    let mask := BitVec.ofNat w (2 ^ len - 1) <<< off
    ((x &&& ~~~mask) ||| (v <<< off)).getLsbD i = x.getLsbD i := by
  intro mask
  have hm0 : mask.getLsbD i = false := by
    dsimp only [mask]
    rw [bv_getLsbD_fieldMask hlen]
    exact decide_eq_false (by omega)
  have hv0 : (v <<< off).getLsbD i = false := by
    rw [BitVec.getLsbD_shiftLeft]
    rcases hout with hlt | hge
    · simp [hi, hlt]
    · have hle : len ≤ i - off := by omega
      have hvf : v.getLsbD (i - off) = false := by
        rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat]
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hle))
      simp [hvf]
  rw [BitVec.getLsbD_or, hv0, Bool.or_false, BitVec.getLsbD_and, BitVec.getLsbD_not, hm0,
    Bool.not_false, decide_eq_true hi]
  simp only [Bool.and_true]

/-! ### Kissat 32-Bit & 64-Bit `PWord` / Header Flag Helpers -/

theorem bv32_pword_payload_lt (pw : BitVec 32) : (pw &&& 0x7FFFFFFF#32).toNat < 2 ^ 31 := by
  rw [show (0x7FFFFFFF#32 : BitVec 32) = BitVec.ofNat 32 (2 ^ 31 - 1) from rfl,
    bv_mask_low_bits_toNat pw (by decide)]
  exact Nat.mod_lt _ (by decide)

theorem bv32_pword_payload_and_flag (pw : BitVec 32) :
    ((pw &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 from rfl, BitVec.and_zero]

theorem bv32_pword_payload_ne_sent (pw : BitVec 32) :
    (pw &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 :=
  bv_ne_allOnes_of_disjoint (by decide) (bv32_pword_payload_and_flag pw)

theorem bv32_pword_pack_payload {pw v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (((pw &&& 0x80000000#32) ||| v) &&& 0x7FFFFFFF#32) = v := by
  have hv' : (v &&& 0x7FFFFFFF#32) = v :=
    bv_mask_low_bits_eq_self (by decide) hv
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
    show (0x80000000#32 &&& 0x7FFFFFFF#32) = 0#32 from rfl, BitVec.and_zero, BitVec.zero_or, hv']

theorem bv32_pword_pack_flag {pw v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (((pw &&& 0x80000000#32) ||| v) &&& 0x80000000#32) = (pw &&& 0x80000000#32) := by
  have hv' : (v &&& 0x7FFFFFFF#32) = v :=
    bv_mask_low_bits_eq_self (by decide) hv
  rw [bv_or_and_mask_of_disjoint (x := pw &&& 0x80000000#32) (m1 := 0x7FFFFFFF#32)
    (show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 from rfl) hv',
    BitVec.and_assoc, BitVec.and_self]

theorem bv32_pword_tag_flag (x : BitVec 32) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) = 0x80000000#32 :=
  bv_clear_or_and_self (m := 0x80000000#32) (x := x) rfl

theorem bv32_pword_tag_payload {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = x := by
  have hx' : (x &&& 0x7FFFFFFF#32) = x := bv_mask_low_bits_eq_self (by decide) hx
  rw [bv_or_and_of_disjoint (show (0x80000000#32 &&& 0x7FFFFFFF#32) = 0#32 from rfl),
    BitVec.and_assoc, BitVec.and_self, hx']

theorem bv64_pword_mask_low_toNat {k : Nat} (x : BitVec 64) (hk : k ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k :=
  bv_mask_low_bits_toNat x hk

theorem bv64_pword_extract_lt {off len : Nat} (x : BitVec 64) (hlen : off + len ≤ 64) :
    (((x &&& (BitVec.ofNat 64 (2 ^ len - 1) <<< off)) >>> off)).toNat < 2 ^ len := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hp : 0 < 2 ^ len := Nat.pow_pos (by decide)
  have hsub : ∀ i, len ≤ i →
      ((x &&& (BitVec.ofNat 64 (2 ^ len - 1) <<< off)) >>> off).getLsbD i = false := by
    intro i hi
    have hnot : ¬ (off ≤ off + i ∧ off + i < off + len) := by omega
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, bv_getLsbD_fieldMask hlen,
      decide_eq_false hnot, Bool.and_false]
  have heq :
      (((x &&& (BitVec.ofNat 64 (2 ^ len - 1) <<< off)) >>> off) &&&
        BitVec.ofNat 64 (2 ^ len - 1)) =
      ((x &&& (BitVec.ofNat 64 (2 ^ len - 1) <<< off)) >>> off) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [BitVec.getLsbD_and, bv_getLsbD_lowMask (by omega)]
    by_cases hil : i < len
    · simp [hil]
    · simp [hil, hsub i (Nat.not_lt.mp hil)]
  have hto := congrArg BitVec.toNat heq
  rw [bv_mask_low_bits_toNat _ (by omega), BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow] at hto
  rw [← hto]
  exact Nat.mod_lt _ hp

end PWordKit

/-! ## 3. `@[bv_c0]` Bitmask Rules & Pure-Kernel `pword_mask` Tactic -/

@[bv_c0 high] theorem bv_c0_toNat_and_3_32 (x : BitVec 32) :
    (x &&& 3#32).toNat = x.toNat % 4 :=
  PWordKit.bv_mask_low_bits_toNat (k := 2) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_3_64 (x : BitVec 64) :
    (x &&& 3#64).toNat = x.toNat % 4 :=
  PWordKit.bv_mask_low_bits_toNat (k := 2) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_7_32 (x : BitVec 32) :
    (x &&& 7#32).toNat = x.toNat % 8 :=
  PWordKit.bv_mask_low_bits_toNat (k := 3) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_7_64 (x : BitVec 64) :
    (x &&& 7#64).toNat = x.toNat % 8 :=
  PWordKit.bv_mask_low_bits_toNat (k := 3) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_31_32 (x : BitVec 32) :
    (x &&& 31#32).toNat = x.toNat % 32 :=
  PWordKit.bv_mask_low_bits_toNat (k := 5) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_63_64 (x : BitVec 64) :
    (x &&& 63#64).toNat = x.toNat % 64 :=
  PWordKit.bv_mask_low_bits_toNat (k := 6) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_255_32 (x : BitVec 32) :
    (x &&& 255#32).toNat = x.toNat % 256 :=
  PWordKit.bv_mask_low_bits_toNat (k := 8) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_255_64 (x : BitVec 64) :
    (x &&& 255#64).toNat = x.toNat % 256 :=
  PWordKit.bv_mask_low_bits_toNat (k := 8) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_7fffffff_32 (x : BitVec 32) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat % 2 ^ 31 :=
  PWordKit.bv_mask_low_bits_toNat (k := 31) x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_align8_64 (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFFFF8#64).toNat = (x.toNat / 8) * 8 := by
  have hmask : (0xFFFFFFFFFFFFFFF8#64 : BitVec 64).toNat = 2 ^ 64 - 8 := by decide
  rw [BitVec.toNat_and, hmask]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have hsh : (x.toNat / 8) * 8 = (x.toNat >>> 3) <<< 3 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [hsh, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsub : 2 ^ 64 - 8 = (2 ^ 61 - 1) <<< 3 := by decide
  rw [hsub, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hi3 : 3 ≤ i <;> by_cases hi64 : i < 64
  · have h61 : i - 3 < 61 := by omega
    simp [hi3, h61, Nat.add_sub_cancel' hi3]
  · have hlt : x.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    have hxf : x.toNat.testBit i = false := Nat.testBit_lt_two_pow hlt
    simp [hi3, hxf, show ¬ (i - 3 < 61) by omega]
  · simp [hi3]
  · simp [hi3]

open Lean Meta Elab Tactic

private meta partial def pureMaskNat? (e : Lean.Expr) : Option Nat :=
  let e := e.consumeMData.headBeta
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then pureMaskNat? (e.getArg! 1)
    else if e.isConstOf ``Nat.zero then some 0
    else if e.isAppOfArity ``Nat.succ 1 then (· + 1) <$> pureMaskNat? (e.getArg! 0)
    else e.nat?

private meta partial def maskLitVal? (e : Lean.Expr) : Option (Nat × Nat) := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``BitVec.ofNat 2 then
    let w ← pureMaskNat? e.appFn!.appArg!
    let v ← pureMaskNat? e.appArg!
    return (w, v % 2 ^ w)
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty := (e.getArg! 0).consumeMData.headBeta
    guard (ty.isAppOfArity ``BitVec 1)
    let w ← pureMaskNat? ty.appArg!
    let v ← pureMaskNat? (e.getArg! 1)
    return (w, v % 2 ^ w)
  if e.isAppOfArity ``Complement.complement 3 then
    let (w, v) ← maskLitVal? e.appArg!
    return (w, (2 ^ w - 1) - v)
  if e.isAppOfArity ``BitVec.allOnes 1 then
    let w ← pureMaskNat? e.appArg!
    return (w, 2 ^ w - 1)
  if e.isAppOfArity ``HAnd.hAnd 6 then
    let (w1, v1) ← maskLitVal? (e.getArg! 4)
    let (w2, v2) ← maskLitVal? (e.getArg! 5)
    guard (w1 == w2)
    return (w1, v1 &&& v2)
  if e.isAppOfArity ``HOr.hOr 6 then
    let (w1, v1) ← maskLitVal? (e.getArg! 4)
    let (w2, v2) ← maskLitVal? (e.getArg! 5)
    guard (w1 == w2)
    return (w1, v1 ||| v2)
  if e.isAppOfArity ``HXor.hXor 6 then
    let (w1, v1) ← maskLitVal? (e.getArg! 4)
    let (w2, v2) ← maskLitVal? (e.getArg! 5)
    guard (w1 == w2)
    return (w1, v1 ^^^ v2)
  if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 then
    let (w, v) ← maskLitVal? (e.getArg! 4)
    let k ← pureMaskNat? (e.getArg! 5)
    return (w, (v <<< k) % 2 ^ w)
  if e.isAppOfArity ``HShiftRight.hShiftRight 6 then
    let (w, v) ← maskLitVal? (e.getArg! 4)
    let k ← pureMaskNat? (e.getArg! 5)
    return (w, v >>> k)
  none

private meta def mkMaskLitExpr (w v : Nat) : Lean.Expr :=
  Lean.mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit v)

/-- Kernel-sound simproc evaluating closed `BitVec` mask expressions (`&&&`, `|||`, `^^^`,
`~~~`, `<<<`, `>>>`, `BitVec.allOnes`) up to width `64` using `Eq.refl`. -/
simproc ↓ pwordMaskClosedSimproc (_) := fun e => do
  let fn := e.getAppFn.consumeMData
  let isMaskOp := fn.isConstOf ``HAnd.hAnd || fn.isConstOf ``HOr.hOr ||
    fn.isConstOf ``HXor.hXor || fn.isConstOf ``Complement.complement ||
    fn.isConstOf ``HShiftLeft.hShiftLeft || fn.isConstOf ``HShiftRight.hShiftRight ||
    fn.isConstOf ``BitVec.allOnes
  if !isMaskOp then return .continue
  let some (w, v) := maskLitVal? e | return .continue
  if w ≤ 64 then
    let litE := mkMaskLitExpr w v
    if litE == e then return .continue
    let prf ← mkEqRefl e
    return .done { expr := litE, proof? := some prf }
  return .continue

private meta def runPwordMaskSimp (extraHyps : Array Lean.Expr) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let (g, tail) := match ← getGoals with | g :: gs => (g, gs) | [] => unreachable!
  let res? ← g.withContext do
    let mut thms : SimpTheorems := {}
    for c in [
      ``BitVec.and_or_distrib_right, ``BitVec.and_or_distrib_left,
      ``BitVec.and_assoc, ``BitVec.or_assoc, ``BitVec.xor_assoc,
      ``BitVec.and_zero, ``BitVec.zero_and, ``BitVec.or_zero, ``BitVec.zero_or,
      ``BitVec.xor_zero, ``BitVec.zero_xor,
      ``BitVec.and_allOnes, ``BitVec.allOnes_and,
      ``BitVec.and_self, ``BitVec.or_self, ``BitVec.xor_self,
      ``BitVec.and_not_self, ``BitVec.not_and_self,
      ``KissatHdrBitMaskKit.bv_clear_idem,
      ``KissatHdrBitMaskKit.bv_and_idem,
      ``KissatHdrBitMaskKit.bv_or_idem,
      ``KissatHdrBitMaskKit.bv_and_or_self,
      ``KissatHdrBitMaskKit.bv_or_self_and,
      ``KissatHdrBitMaskKit.bv_set_bit_getLsbD_self,
      ``KissatHdrBitMaskKit.bv_clear_bit_getLsbD_self,
      ``KissatHdrBitMaskKit.bv_and_bit_eq_zero_iff,
      ``KissatHdrBitMaskKit.bv_and_bit_ne_zero_iff,
      ``PWordKit.bv32_pword_payload_and_flag,
      ``PWordKit.bv32_pword_tag_flag,
      ``BitVec.getLsbD_zero, ``BitVec.getLsbD_allOnes,
      ``Bool.and_true, ``Bool.true_and, ``Bool.and_false, ``Bool.false_and,
      ``Bool.or_true, ``Bool.true_or, ``Bool.or_false, ``Bool.false_or,
      ``Bool.not_true, ``Bool.not_false] do
      thms ← thms.addConst c
    for h in extraHyps do
      let ty ← instantiateMVars (← inferType h)
      if ty.eq?.isSome && !ty.hasLooseBVars then
        thms ← thms.add (.fvar h.fvarId!) #[] h
    let mut simprocs : Simp.Simprocs := {}
    simprocs ← simprocs.add ``pwordMaskClosedSimproc true
    let ctx ← Simp.mkContext
      (config := { failIfUnchanged := false, maxSteps := 100000 })
      (simpTheorems := #[thms])
    let (res?, _) ← simpGoal g ctx #[simprocs] (simplifyTarget := true) (fvarIdsToSimp := #[])
    return res?
  match res? with
  | none => setGoals tail
  | some (_, g') => setGoals (g' :: tail)

private meta def tryDecideClosedGoal : TacticM Bool := do
  if (← getUnsolvedGoals).isEmpty then return true
  let g ← getMainGoal
  let ty ← g.withContext do instantiateMVars (← g.getType)
  if ty.hasFVar || ty.hasMVar then return false
  let s ← saveState
  try
    evalTactic (← `(tactic| decide))
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

elab "pword_decide_closed" : tactic => do
  unless ← tryDecideClosedGoal do
    throwError "pword_decide_closed: goal is not closed decidably"

elab "pword_rw_submask " h:term : tactic => do
  focus do
    evalTactic (← `(tactic| rw [KissatHdrBitMaskKit.bv_and_eq_zero_of_submask $h]))
    let gMain :: sideGoals ← getUnsolvedGoals | return
    for sg in sideGoals do
      setGoals [sg]
      unless ← tryDecideClosedGoal do
        throwError "pword_rw_submask: disjointness subgoal did not close"
    setGoals [gMain]

private meta def tryApplyMaskOrthog (hyps : Array Lean.Expr) : TacticM Unit := do
  let mut rules : Array (TSyntax `tactic) := #[]
  for h in hyps do
    let ty ← withMainContext do instantiateMVars (← inferType h)
    if ty.eq?.isSome then
      let hStx ← withMainContext do Term.exprToSyntax h
      rules := rules.push (← `(tactic| rw [KissatHdrBitMaskKit.bv_and_not_and_of_disjoint $hStx]))
      rules := rules.push (← `(tactic|
        rw [KissatHdrBitMaskKit.bv_and_not_and_right_of_disjoint $hStx]))
      rules := rules.push (← `(tactic| rw [KissatHdrBitMaskKit.bv_or_and_of_disjoint $hStx]))
      rules := rules.push (← `(tactic| rw [KissatHdrBitMaskKit.bv_or_and_left_of_disjoint $hStx]))
      rules := rules.push (← `(tactic| rw [KissatHdrBitMaskKit.bv_clear_or_and_self $hStx]))
      rules := rules.push (← `(tactic| rw [KissatHdrBitMaskKit.bv_clear_or_and_not_self $hStx]))
      rules := rules.push (← `(tactic| pword_rw_submask $hStx))
      for h2 in hyps do
        let ty2 ← withMainContext do instantiateMVars (← inferType h2)
        if ty2.eq?.isSome then
          let h2Stx ← withMainContext do Term.exprToSyntax h2
          rules := rules.push (← `(tactic|
            rw [KissatHdrBitMaskKit.bv_clear_or_and_other $hStx $h2Stx]))
          rules := rules.push (← `(tactic|
            rw [KissatHdrBitMaskKit.bv_clear_or_and_other_sub $hStx $h2Stx]))
          rules := rules.push (← `(tactic|
            rw [KissatHdrBitMaskKit.bv_or_and_mask_of_disjoint $hStx $h2Stx]))
  if !rules.isEmpty then
    evalTactic (← `(tactic| try repeat (first $[| $rules:tactic]*)))

private meta def closeBitwiseGoal? : TacticM Bool := do
  if (← getUnsolvedGoals).isEmpty then return true
  let s ← saveState
  try
    evalTactic (← `(tactic| first | rfl | assumption))
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore
  catch _ =>
    s.restore
  if ← tryDecideClosedGoal then return true
  return false

private meta def tryBitwiseExtClose : TacticM Unit := do
  if (← getUnsolvedGoals).isEmpty then return
  let s ← saveState
  try
    let g ← getMainGoal
    let tgt ← g.withContext do instantiateMVars (← g.getType)
    if tgt.eq?.isSome then
      evalTactic (← `(tactic| (
        apply BitVec.eq_of_getLsbD_eq
        intro _bi _hbi
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor,
          BitVec.getLsbD_not, BitVec.getLsbD_zero, BitVec.getLsbD_allOnes,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
          _hbi, decide_true, Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
          Bool.or_false, Bool.false_or] at *)))
      if ← closeBitwiseGoal? then return
      evalTactic (← `(tactic| all_goals (try simp_all; try omega)))
      for rem in ← getUnsolvedGoals do
        setGoals [rem]
        unless ← tryDecideClosedGoal do
          s.restore
          return
      setGoals []
      return
    s.restore
  catch _ =>
    s.restore

private meta partial def collectClosedMasks (e : Lean.Expr) (acc : Array Lean.Expr := #[]) :
    Array Lean.Expr := Id.run do
  let e := e.consumeMData
  if let some (w, v) := maskLitVal? e then
    if w ≤ 64 then
      let mut out := acc
      if v != 0 then
        let m := mkMaskLitExpr w v
        if !out.any (· == m) then out := out.push m
      let vc := (~~~(BitVec.ofNat w v)).toNat
      if vc != 0 then
        let mc := mkMaskLitExpr w vc
        if !out.any (· == mc) then out := out.push mc
      return out
  match e with
  | .app f a =>
      let acc := collectClosedMasks f acc
      collectClosedMasks a acc
  | _ => acc

private meta def tryAssumptionClose : TacticM Bool := do
  let s2 ← saveState
  try
    evalTactic (← `(tactic| assumption))
    if (← getUnsolvedGoals).isEmpty then return true
    s2.restore; return false
  catch _ =>
    s2.restore; return false

private meta def tryApplyCloseDecide (tac : TSyntax `tactic) : TacticM Bool := do
  if (← getUnsolvedGoals).isEmpty then return true
  let s ← saveState
  try
    evalTactic tac
    for sg in ← getUnsolvedGoals do
      setGoals [sg]
      unless ← (tryDecideClosedGoal <||> tryAssumptionClose) do
        s.restore
        return false
    setGoals []
    return true
  catch _ =>
    s.restore
    return false

private meta def tryMaskDisjointNe (hyps : Array Lean.Expr) : TacticM Unit := do
  if (← getUnsolvedGoals).isEmpty then return
  let g ← getMainGoal
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  if tgt.isAppOfArity ``Ne 3 then
    let lhs := tgt.getArg! 1
    let rhs := tgt.getArg! 2
    if ← tryApplyCloseDecide (← `(tactic| apply KissatHdrBitMaskKit.bv_or_and_self_ne_zero)) then
      return
    if ← tryApplyCloseDecide (← `(tactic| apply KissatHdrBitMaskKit.bv_or_ne_zero_of_right)) then
      return
    if ← tryApplyCloseDecide (← `(tactic| apply KissatHdrBitMaskKit.bv_or_ne_zero_of_left)) then
      return
    -- Project `congrArg (· &&& m)` for each candidate closed mask `m` appearing in `lhs` or `rhs`
    let cands := collectClosedMasks rhs (collectClosedMasks lhs)
    for m in cands do
      let ms ← saveState
      try
        let mStx ← withMainContext do Term.exprToSyntax m
        evalTactic (← `(tactic| apply KissatHdrBitMaskKit.bv_ne_of_and_ne (m := $mStx)))
        for _ in [:2] do
          runPwordMaskSimp hyps
          evalTactic (← `(tactic| try simp only [BitVec.and_assoc, BitVec.and_or_distrib_right]))
          tryApplyMaskOrthog hyps
          runPwordMaskSimp hyps
        if ← tryDecideClosedGoal then return
        ms.restore
      catch _ =>
        ms.restore

/-- Pure-kernel bitmask and packed-word tactic (`std3` axioms only). Reduces closed bitmask
expressions, applies `KissatHdrBitMaskKit` / `PWordKit` orthogonality identities using local or
provided hypotheses `[h1, ...]`, and finishes via `getLsbD` extensionality, `decide`, or `omega`. -/
syntax "pword_mask" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| pword_mask $[ [ $hs,* ] ]?) => do
    let hyps : Array Lean.Expr ← withMainContext do
      let mut out : Array Lean.Expr := #[]
      if let some arr := hs then
        for stx in arr.getElems do
          out := out.push (← elabTerm stx none)
      else
        for d in ← getLCtx do
          if !d.isImplementationDetail then
            if ← isProp d.type then
              let ty ← instantiateMVars d.type
              if ty.eq?.isSome then
                out := out.push d.toExpr
      return out
    if ← closeBitwiseGoal? then return
    for _ in [:2] do
      tryApplyMaskOrthog hyps
      runPwordMaskSimp hyps
      if ← closeBitwiseGoal? then return
    -- Reassociate `BitVec.and_assoc` then re-apply orthogonality rules
    let s ← saveState
    try
      evalTactic (← `(tactic| simp only [BitVec.and_assoc]))
      for _ in [:2] do
        tryApplyMaskOrthog hyps
        runPwordMaskSimp hyps
        if ← closeBitwiseGoal? then return
      s.restore
    catch _ =>
      s.restore
    tryBitwiseExtClose
    if (← getUnsolvedGoals).isEmpty then return
    tryMaskDisjointNe hyps

end

end LeanQbe.T.ProofKit
