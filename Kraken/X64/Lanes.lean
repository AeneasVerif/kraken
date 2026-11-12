module

/-
Lane lemmas for the x86-64 vector semantics.

Lane `i` of each vector helper's result, in terms of lanes of its inputs.
-/

public import Kraken.X64.Semantics

public section

namespace BitVec

/-! ### Lanes and bits -/

theorem getLsbD_lane {w c i : Nat} (v : BitVec w) (j : Nat) :
    (v.lane c i).getLsbD j = (decide (j < c) && v.getLsbD (c * i + j)) := by
  simp [lane]

private theorem getLsbD_foldl_lanes {w c q r : Nat} (f : Nat → BitVec c) (hr : r < c) (n : Nat) :
    ((List.range n).foldl (fun acc i => acc ||| ((f i).setWidth w <<< (c * i))) 0#w).getLsbD
        (c * q + r) =
      (decide (c * q + r < w) && decide (q < n) && (f q).getLsbD r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, getLsbD_or, ih, getLsbD_shiftLeft,
      getLsbD_setWidth]
    rcases Nat.lt_trichotomy q n with h | rfl | h
    · have : c * (q + 1) ≤ c * n := Nat.mul_le_mul_left c h
      rw [Nat.mul_succ] at this
      have h1 : c * q + r < c * n := by omega
      simp [h1, h, Nat.lt_succ_of_lt h]
    · by_cases hw : c * q + r < w
      · simp [hw, show r < w by omega]
      · simp [hw]
    · have : c * (n + 1) ≤ c * q := Nat.mul_le_mul_left c h
      rw [Nat.mul_succ] at this
      have h1 : c ≤ c * q + r - c * n := by omega
      simp [getLsbD_of_ge _ _ h1, show ¬q < n by omega, show ¬q < n + 1 by omega]

private theorem getLsbD_ofLanes_mul_add {w c q r : Nat} (f : Nat → BitVec c) (hr : r < c) :
    (ofLanes w c f).getLsbD (c * q + r) =
      (decide (c * q + r < w) && decide (q < w / c) && (f q).getLsbD r) :=
  getLsbD_foldl_lanes f hr _

/-- Bit `k` of `ofLanes w c f` is bit `k % c` of lane `k / c`, if that lane fits in `w` bits. -/
theorem getLsbD_ofLanes {w c : Nat} (f : Nat → BitVec c) (k : Nat) (hc : 0 < c) :
    (ofLanes w c f).getLsbD k =
      (decide (k < w) && decide (k / c < w / c) && (f (k / c)).getLsbD (k % c)) := by
  have h := getLsbD_ofLanes_mul_add (w := w) (q := k / c) f (Nat.mod_lt k hc)
  rwa [Nat.div_add_mod] at h

/-! ### Building a vector from its lanes -/

@[simp] theorem lane_ofLanes {w c i : Nat} (f : Nat → BitVec c) (hi : i < w / c) :
    (ofLanes w c f).lane c i = f i := by
  apply eq_of_getLsbD_eq
  intro j hj
  have h : c * (i + 1) ≤ w := by
    rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).1 hi
  rw [Nat.mul_succ] at h
  rw [getLsbD_lane, getLsbD_ofLanes_mul_add f hj]
  simp [hj, hi, show c * i + j < w by omega]

theorem ofLanes_congr {w c : Nat} {f g : Nat → BitVec c} (h : ∀ i, i < w / c → f i = g i) :
    ofLanes w c f = ofLanes w c g := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [ofLanes]
  apply eq_of_getLsbD_eq
  intro k _
  rw [getLsbD_ofLanes _ _ hc, getLsbD_ofLanes _ _ hc]
  by_cases hq : k / c < w / c
  · simp [hq, h _ hq]
  · simp [hq]

@[simp] theorem ofLanes_lane {w c : Nat} (v : BitVec w) (h : c ∣ w) :
    ofLanes w c (fun i => v.lane c i) = v := by
  apply eq_of_getLsbD_eq
  intro k hk
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · obtain rfl := Nat.eq_zero_of_zero_dvd h
    omega
  have hq : k / c < w / c := by
    obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left m hc, Nat.div_lt_iff_lt_mul hc, Nat.mul_comm]
    exact hk
  rw [getLsbD_ofLanes _ _ hc, getLsbD_lane]
  simp [hk, hq, Nat.mod_lt k hc, Nat.div_add_mod]

/-- Two vectors are equal when all their lanes are. -/
theorem eq_of_lane_eq {w c : Nat} {a b : BitVec w} (h : c ∣ w)
    (hab : ∀ i, i < w / c → a.lane c i = b.lane c i) : a = b := by
  rw [← ofLanes_lane a h, ← ofLanes_lane b h]
  exact ofLanes_congr hab

/-! ### Bitwise operations -/

@[simp] theorem lane_zero {w c i : Nat} : (0#w).lane c i = 0#c := by
  simp [lane, extractLsb'_zero]

@[simp] theorem lane_and {w c i : Nat} (a b : BitVec w) :
    (a &&& b).lane c i = a.lane c i &&& b.lane c i :=
  extractLsb'_and

@[simp] theorem lane_or {w c i : Nat} (a b : BitVec w) :
    (a ||| b).lane c i = a.lane c i ||| b.lane c i :=
  extractLsb'_or

@[simp] theorem lane_xor {w c i : Nat} (a b : BitVec w) :
    (a ^^^ b).lane c i = a.lane c i ^^^ b.lane c i :=
  extractLsb'_xor

/-- Above the width, `~~~v` has no bits set, so the lane must fit. -/
@[simp] theorem lane_not {w c i : Nat} (v : BitVec w) (h : c * i + c ≤ w) :
    (~~~v).lane c i = ~~~(v.lane c i) := by
  apply eq_of_getLsbD_eq
  intro j hj
  simp only [getLsbD_lane, getLsbD_not]
  simp [hj, show c * i + j < w by omega]

/-! ### Widening, narrowing and slicing -/

@[simp] theorem lane_setWidth {w w' c i : Nat} (v : BitVec w) (h : c * i + c ≤ w') :
    (v.setWidth w').lane c i = v.lane c i :=
  extractLsb'_setWidth_of_le h

@[simp] theorem lane_zeroExtend {w w' c i : Nat} (v : BitVec w) (h : c * i + c ≤ w') :
    (v.zeroExtend w').lane c i = v.lane c i :=
  lane_setWidth v h

/-- The lanes that `setWidth` adds above the source width are zero. -/
theorem lane_setWidth_of_le {w w' c i : Nat} (v : BitVec w) (h : w ≤ c * i) :
    (v.setWidth w').lane c i = 0#c := by
  apply eq_of_getLsbD_eq
  intro j _
  simp [getLsbD_lane, getLsbD_of_ge v (c * i + j) (by omega)]

theorem lane_zeroExtend_of_le {w w' c i : Nat} (v : BitVec w) (h : w ≤ c * i) :
    (v.zeroExtend w').lane c i = 0#c :=
  lane_setWidth_of_le v h

@[simp] theorem lane_take {w n c i : Nat} (v : BitVec w) (h : c * i + c ≤ n) :
    (v.take n).lane c i = v.lane c i := by
  apply eq_of_getLsbD_eq
  intro j hj
  simp only [take, getLsbD_lane, getLsbD_extractLsb']
  simp [hj, show c * i + j < n by omega]

theorem lane_extractLsb' {w n c k i : Nat} (v : BitVec w) (h : c * i + c ≤ n) :
    (v.extractLsb' (c * k) n).lane c i = v.lane c (k + i) := by
  apply eq_of_getLsbD_eq
  intro j hj
  simp only [getLsbD_lane, getLsbD_extractLsb']
  simp [hj, show c * i + j < n by omega, Nat.mul_add, Nat.add_assoc]

/-- Lane `k` of `d` bits within lane `j` of `c` bits. -/
theorem lane_lane {w c d j k : Nat} (v : BitVec w) (hd : d ∣ c) (hk : k < c / d) :
    (v.lane c j).lane d k = v.lane d (c / d * j + k) := by
  obtain ⟨m, rfl⟩ := hd
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp at hk
  rw [Nat.mul_div_cancel_left m hd] at hk ⊢
  apply eq_of_getLsbD_eq
  intro t ht
  have : d * k + t < d * m := by
    have := Nat.mul_le_mul_left d (show k + 1 ≤ m by omega)
    rw [Nat.mul_succ] at this
    omega
  simp only [getLsbD_lane]
  simp [ht, this, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Lane `i` of `d` bits of `ofLanes w c f`, when `d` divides `c`. -/
theorem lane_ofLanes_of_dvd {w c d i : Nat} (f : Nat → BitVec c) (hd : d ∣ c)
    (hi : i / (c / d) < w / c) :
    (ofLanes w c f).lane d i = (f (i / (c / d))).lane d (i % (c / d)) := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp at hi
    · exact hc
  have hcd : 0 < c / d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd'
    · obtain rfl := Nat.eq_zero_of_zero_dvd hd; omega
    · exact Nat.div_pos (Nat.le_of_dvd hc hd) hd'
  rw [← lane_ofLanes f hi, lane_lane _ hd (Nat.mod_lt i hcd), Nat.div_add_mod]

/-! ### The lane-wise binary operation -/

private theorem lane_append_zero {m c : Nat} (hi : BitVec m) (lo : BitVec c) :
    (hi ++ lo).lane c 0 = lo := by
  simpa [lane] using extractLsb'_append_eq_right (a := hi) (b := lo)

private theorem lane_append_succ {m c i : Nat} (hi : BitVec m) (lo : BitVec c) :
    (hi ++ lo).lane c (i + 1) = hi.lane c i := by
  apply eq_of_getLsbD_eq
  intro j hj
  simp only [getLsbD_lane, getLsbD_append]
  rw [Nat.mul_succ, ite_eq_right (by omega), show c * i + c + j - c = c * i + j by omega]

@[simp] theorem lane_packedBinOp {w c i : Nat} (op : BitVec c → BitVec c → BitVec c)
    (a b : BitVec w) (hi : i < w / c) :
    (packedBinOp c op a b).lane c i = op (a.lane c i) (b.lane c i) := by
  induction w using Nat.strongRecOn generalizing i with
  | ind w ih =>
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp at hi
    · exact hc
  have h : c * (i + 1) ≤ w := by
    rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hc).1 hi
  rw [Nat.mul_succ] at h
  rw [packedBinOp, dite_eq_right (by omega)]
  simp only []
  rw [lane_setWidth _ h]
  cases i with
  | zero =>
    rw [append_eq, lane_append_zero]
    simp [take, lane]
  | succ i =>
    rw [append_eq, lane_append_succ]
    have hi' : i < (w - c) / c := by
      apply (Nat.le_div_iff_mul_le hc).2
      rw [Nat.succ_mul, Nat.mul_comm]
      rw [Nat.mul_succ] at h
      omega
    have hd : c * i + c ≤ w - c := by rw [Nat.mul_succ] at h; omega
    have hdrop (v : BitVec w) : (v.drop c).lane c i = v.lane c (i + 1) := by
      have := lane_extractLsb' (k := 1) v hd
      rw [Nat.mul_one] at this
      rw [drop, this, Nat.add_comm]
    rw [ih (w - c) (by omega) _ _ hi', hdrop, hdrop]

/-! ### The vector helpers -/

@[simp] theorem lane_mapLanes {w c i : Nat} (f : BitVec c → BitVec c) (a : BitVec w)
    (hi : i < w / c) :
    (a.mapLanes c f).lane c i = f (a.lane c i) :=
  lane_ofLanes _ hi

@[simp] theorem lane_shuffleBytes {w i : Nat} (a m : BitVec w) (hi : i < w / 8) :
    (a.shuffleBytes m).lane 8 i =
      if (m.lane 8 i).msb then 0#8 else a.lane 8 (16 * (i / 16) + (m.lane 8 i).toNat % 16) :=
  lane_ofLanes _ hi

@[simp] theorem lane_shuffleDwords {w i : Nat} (a : BitVec w) (imm : BitVec 8) (hi : i < w / 32) :
    (a.shuffleDwords imm).lane 32 i = a.lane 32 (4 * (i / 4) + (imm.toNat >>> (2 * (i % 4))) % 4) :=
  lane_ofLanes _ hi

@[simp] theorem lane_alignBytes {w i : Nat} (hi lo : BitVec w) (imm : BitVec 8) (h : i < w / 8) :
    (hi.alignBytes lo imm).lane 8 i =
      if i % 16 + imm.toNat < 16 then lo.lane 8 (16 * (i / 16) + (i % 16 + imm.toNat))
      else if i % 16 + imm.toNat < 32 then hi.lane 8 (16 * (i / 16) + (i % 16 + imm.toNat) - 16)
      else 0#8 :=
  lane_ofLanes _ h

@[simp] theorem lane_blendWords {w i : Nat} (a b : BitVec w) (imm : BitVec 8) (hi : i < w / 16) :
    (a.blendWords b imm).lane 16 i = if imm.getLsbD (i % 8) then b.lane 16 i else a.lane 16 i :=
  lane_ofLanes _ hi

@[simp] theorem lane_shuffleDwordPairs {w i : Nat} (a b : BitVec w) (imm : BitVec 8)
    (hi : i < w / 32) :
    (a.shuffleDwordPairs b imm).lane 32 i =
      if i % 4 < 2 then a.lane 32 (4 * (i / 4) + (imm.toNat >>> (2 * (i % 4))) % 4)
      else b.lane 32 (4 * (i / 4) + (imm.toNat >>> (2 * (i % 4))) % 4) :=
  lane_ofLanes _ hi

@[simp] theorem lane_permute2 {w c i : Nat} (idx a b : BitVec w) (hi : i < w / c) :
    (permute2 c idx a b).lane c i =
      if (idx.lane c i).toNat / (w / c) % 2 == 1 then b.lane c ((idx.lane c i).toNat % (w / c))
      else a.lane c ((idx.lane c i).toNat % (w / c)) :=
  lane_ofLanes _ hi

@[simp] theorem lane_unpackLanes {w c i : Nat} (high : Bool) (a b : BitVec w) (hi : i < w / c) :
    (unpackLanes c high a b).lane c i =
      let n := 128 / c
      let k := n * (i / n) + (if high then n / 2 else 0) + i % n / 2
      if i % 2 == 0 then a.lane c k else b.lane c k :=
  lane_ofLanes _ hi

@[simp] theorem lane_permute128 {w i : Nat} (a b : BitVec w) (imm : BitVec 8) (hi : i < w / 128) :
    (permute128 a b imm).lane 128 i =
      if (imm.toNat >>> (4 * i)) % 16 / 8 == 1 then 0#128
      else if (imm.toNat >>> (4 * i)) % 16 / 2 % 2 == 1 then
        b.lane 128 ((imm.toNat >>> (4 * i)) % 16 % 2)
      else a.lane 128 ((imm.toNat >>> (4 * i)) % 16 % 2) :=
  lane_ofLanes _ hi

/-- The 256-bit half `half` of `a` replaced by `b`, seen in lanes of `d` bits. -/
theorem lane_ofLanes_256_ite {d i half : Nat} (a : BitVec 512) (b : BitVec 256) (hd : d ∣ 256)
    (hi : i < 512 / d) :
    (ofLanes 512 256 fun j => if j == half then b else a.lane 256 j).lane d i =
      if i / (256 / d) == half then b.lane d (i % (256 / d)) else a.lane d i := by
  obtain ⟨m, hm⟩ := hd
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp at hm
    · exact hd
  have h256 : 256 / d = m := by rw [hm, Nat.mul_div_cancel_left m hd]
  have h512 : 512 / d = 2 * m := by
    rw [show 512 = d * (2 * m) by rw [Nat.mul_left_comm, ← hm], Nat.mul_div_cancel_left _ hd]
  rw [h512] at hi
  have hq : i / m < 2 := (Nat.div_lt_iff_lt_mul (by omega)).2 hi
  rw [lane_ofLanes_of_dvd _ ⟨m, hm⟩ (by rw [h256]; exact hq), h256]
  split
  · rfl
  · rw [lane_lane _ ⟨m, hm⟩ (by rw [h256]; exact Nat.mod_lt i (by omega)), h256, Nat.div_add_mod]

@[simp] theorem lane_ternaryLogic {w c i : Nat} (a b x : BitVec w) (imm : BitVec 8)
    (h : c * i + c ≤ w) :
    (ternaryLogic a b x imm).lane c i =
      ternaryLogic (a.lane c i) (b.lane c i) (x.lane c i) imm := by
  simp [ternaryLogic, List.range, List.range.loop, apply_ite (lane c i), lane_not _ h]

@[simp] theorem lane_msg1 {i : Nat} (x y : BitVec 128) (hi : i < 4) :
    (Sha256.msg1 x y).lane 32 i =
      x.lane 32 i + Sha256.σ₀ (if i < 3 then x.lane 32 (i + 1) else y.lane 32 0) :=
  lane_ofLanes _ hi

end BitVec
