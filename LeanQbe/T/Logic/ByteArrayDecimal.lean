module

/-!
# `ByteArray` / `String.toUTF8` Algebra and Decimal Formatting Proofs

Arch-free, AVX-free leaf module providing shared `ByteArray` / UTF-8 byte-append algebra,
string byte-copy loop equivalence, and exact `UInt64` / `Int64` decimal formatting proofs
(`digitsPow10`, `pow10Up`, `emitPowDown`, `emitU64Dec`, `emitI64Dec`) used by both
`LeanQbe.T.Amd64.PrintAsm0Lemmas` and `LeanQbe.T.Bootstrap0.PrintDir0Lemmas`.
-/

set_option autoImplicit false

namespace LeanQbe.T.ByteArrayDecimal

@[expose] public section

/-! ## 1. `ByteArray`, `UInt64`, and `String.toUTF8` Algebra -/

theorem u64_ext {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem toString_str (s : String) : toString s = s := rfl

theorem emptyWithCapacity_eq_empty (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := rfl

theorem ba_eq_of_data_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b; congr 1; exact Array.ext' h

theorem ba_push_data_toList (ba : ByteArray) (b : UInt8) :
    (ba.push b).data.toList = ba.data.toList ++ [b] := by
  cases ba; dsimp only [ByteArray.push]; exact Array.toList_push

theorem ba_push_eq_append (ba : ByteArray) (b : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [b]) : ba.push b = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  rw [ba_push_data_toList, ByteArray.toList_data_append, h]

theorem ba_push2_eq_append (ba : ByteArray) (a b : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b]) : (ba.push a).push b = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  simp only [ba_push_data_toList, ByteArray.toList_data_append, h, List.append_assoc]; rfl

theorem ba_push3_eq_append (ba : ByteArray) (a b c : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b, c]) :
    ((ba.push a).push b).push c = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  simp only [ba_push_data_toList, ByteArray.toList_data_append, h, List.append_assoc]; rfl

theorem ba_push4_eq_append (ba : ByteArray) (a b c d : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b, c, d]) :
    (((ba.push a).push b).push c).push d = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  simp only [ba_push_data_toList, ByteArray.toList_data_append, h, List.append_assoc]; rfl

theorem toUTF8_append (s t : String) : (s ++ t).toUTF8 = s.toUTF8 ++ t.toUTF8 := by
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray,
    String.toUTF8_eq_toByteArray, String.toByteArray_append]

theorem toUTF8_empty : "".toUTF8 = ByteArray.empty := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_empty]

theorem toUTF8_concat_l (s1 s2 : String) (r : ByteArray) :
    s1.toUTF8 ++ (s2.toUTF8 ++ r) = (s1 ++ s2).toUTF8 ++ r := by
  rw [← ByteArray.append_assoc, ← toUTF8_append]

theorem fromUTF8!_toUTF8 (s : String) : String.fromUTF8! s.toUTF8 = s := by
  dsimp only [String.fromUTF8!]
  rw [String.toUTF8_eq_toByteArray]
  split
  · exact String.fromUTF8_eq_ofByteArray
  · exact absurd s.isValidUTF8 ‹_›

theorem toUTF8_data_length (s : String) : s.toUTF8.data.toList.length = s.utf8ByteSize := by
  rw [String.toUTF8_eq_toByteArray, Array.length_toList]; rfl

/-! ## 2. String Byte-Copy Loop Equivalence -/

theorem emitStrLoop_eq_of_steps
    (loop : ByteArray → String → Nat → ByteArray)
    (hDone : ∀ ba s i, ¬ i < s.utf8ByteSize → loop ba s i = ba)
    (hStep : ∀ ba s i (h : i < s.utf8ByteSize),
      loop ba s i = loop (ba.push (s.getUTF8Byte ⟨i⟩ h)) s (Nat.add i 1))
    (s : String) :
    ∀ (k i : Nat) (ba : ByteArray), k = s.utf8ByteSize - i →
      (loop ba s i).data.toList = ba.data.toList ++ s.toUTF8.data.toList.drop i
  | 0, i, ba, hk => by
    have hge : ¬ i < s.utf8ByteSize := by omega
    have hdrop : s.toUTF8.data.toList.drop i = [] :=
      List.drop_eq_nil_of_le (by rw [toUTF8_data_length]; omega)
    rw [hDone ba s i hge, hdrop, List.append_nil]
  | k + 1, i, ba, hk => by
    have hlt : i < s.utf8ByteSize := by omega
    have hstep : k = s.utf8ByteSize - Nat.add i 1 := by rw [Nat.add_eq]; omega
    rw [hStep ba s i hlt,
      emitStrLoop_eq_of_steps loop hDone hStep s k (Nat.add i 1)
        (ba.push (s.getUTF8Byte ⟨i⟩ hlt)) hstep,
      ba_push_data_toList, List.append_assoc]
    congr 1
    have hlen : i < s.toUTF8.data.toList.length := by rw [toUTF8_data_length]; exact hlt
    have hbyte : s.getUTF8Byte ⟨i⟩ hlt = s.toUTF8.data.toList[i]'hlen := by
      rw [String.getUTF8Byte_eq_getElem]; simp only [String.toUTF8_eq_toByteArray]; rfl
    rw [hbyte, List.cons_append, List.nil_append, Nat.add_eq]
    exact (List.drop_eq_getElem_cons hlen).symm

theorem emitStr_eq_of_steps
    (loop : ByteArray → String → Nat → ByteArray)
    (hDone : ∀ ba s i, ¬ i < s.utf8ByteSize → loop ba s i = ba)
    (hStep : ∀ ba s i (h : i < s.utf8ByteSize),
      loop ba s i = loop (ba.push (s.getUTF8Byte ⟨i⟩ h)) s (Nat.add i 1))
    (ba : ByteArray) (s : String) : loop ba s 0 = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  rw [emitStrLoop_eq_of_steps loop hDone hStep s s.utf8ByteSize 0 ba (by omega),
    List.drop_zero, ByteArray.toList_data_append]

/-! ## 3. Exact `UInt64` / `Int64` Decimal Formatting -/

/-- Big-endian list of ASCII decimal bytes for `n` with `k + 1` digits. -/
def digitsPow10 : Nat → Nat → List UInt8
  | 0, n => [UInt8.ofNat (48 + n)]
  | k + 1, n => UInt8.ofNat (48 + n / 10 ^ (k + 1)) :: digitsPow10 k (n % 10 ^ (k + 1))

private theorem pow10_lt_u64 {k : Nat} (hk : k ≤ 19) : 10 ^ k < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) (by decide : 10 ^ 19 < 2 ^ 64)

private theorem u64_pow10_toNat {k : Nat} (hk : k ≤ 19) :
    (UInt64.ofNat (10 ^ k)).toNat = 10 ^ k := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (pow10_lt_u64 hk)]

private theorem digit_u8_eq (n p : UInt64) (_hlt : n.toNat / p.toNat < 10) :
    48 + (n / p).toUInt8 = UInt8.ofNat (48 + n.toNat / p.toNat) := by
  apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  change (48 + (n / p).toUInt8).toNat = (UInt8.ofNat (48 + n.toNat / p.toNat)).toNat
  rw [UInt8.toNat_add, UInt64.toNat_toUInt8, UInt64.toNat_div, UInt8.toNat_ofNat']
  change (48 + (n.toNat / p.toNat) % 256) % 256 = (48 + n.toNat / p.toNat) % 256
  omega

theorem emitPowDown_eq_digitsPow10_of_steps
    (downFn : Nat → ByteArray → UInt64 → UInt64 → ByteArray)
    (hZero : ∀ ba n p, downFn 0 ba n p = ba.push (48 + (n / p).toUInt8))
    (hSucc : ∀ fuel ba n p, fuel < 20 →
      downFn (fuel + 1) ba n p =
        let ba' := ba.push (48 + (n / p).toUInt8)
        if p == 1 then ba' else downFn fuel ba' (n % p) (p / 10)) :
    ∀ (k fuel : Nat) (ba : ByteArray) (n : UInt64),
      k ≤ fuel → fuel ≤ 20 → k ≤ 19 → n.toNat < 10 ^ (k + 1) →
      (downFn fuel ba n (UInt64.ofNat (10 ^ k))).data.toList =
        ba.data.toList ++ digitsPow10 k n.toNat
  | 0, fuel, ba, n, _, hfuel, _, hn => by
    have hd : 48 + (n / 1).toUInt8 = UInt8.ofNat (48 + n.toNat) := by
      have h := digit_u8_eq n 1 (by change n.toNat / 1 < 10; omega)
      rwa [show (1 : UInt64).toNat = 1 from rfl, Nat.div_one] at h
    rw [show UInt64.ofNat (10 ^ 0) = 1 from rfl]
    cases fuel with
    | zero => rw [hZero, ba_push_data_toList, hd]; rfl
    | succ f' =>
      rw [hSucc f' ba n 1 (by omega)]
      simp only [beq_self_eq_true, ↓reduceIte, ba_push_data_toList, hd]; rfl
  | k + 1, fuel, ba, n, hle, hfuel, hk, hn => by
    cases fuel with
    | zero => omega
    | succ f' =>
      have hp_toNat := u64_pow10_toNat hk
      have hp_ne1 : (UInt64.ofNat (10 ^ (k + 1)) == 1) = false := beq_false_of_ne fun hEq => by
        have h10 : 10 ^ 1 ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hNat := congrArg UInt64.toNat hEq
        rw [hp_toNat] at hNat; change 10 ^ (k + 1) = 1 at hNat; omega
      have hdiv_p : UInt64.ofNat (10 ^ (k + 1)) / 10 = UInt64.ofNat (10 ^ k) := u64_ext <| by
        rw [UInt64.toNat_div, hp_toNat, u64_pow10_toNat (by omega)]
        change 10 ^ (k + 1) / 10 = 10 ^ k; rw [Nat.pow_succ, Nat.mul_div_cancel _ (by omega)]
      have hmod_lt : (n % UInt64.ofNat (10 ^ (k + 1))).toNat < 10 ^ (k + 1) := by
        rw [UInt64.toNat_mod, hp_toNat]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))
      have hq_lt : n.toNat / (UInt64.ofNat (10 ^ (k + 1))).toNat < 10 := by
        rw [hp_toNat, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), Nat.mul_comm, ← Nat.pow_succ]
        exact hn
      have hd := digit_u8_eq n (UInt64.ofNat (10 ^ (k + 1))) hq_lt
      rw [hp_toNat] at hd
      rw [hSucc f' ba n _ (by omega)]
      simp only [hp_ne1, Bool.false_eq_true, ↓reduceIte, hdiv_p]
      rw [emitPowDown_eq_digitsPow10_of_steps downFn hZero hSucc k f' _
          (n % UInt64.ofNat (10 ^ (k + 1))) (by omega) (by omega) (by omega) hmod_lt,
        ba_push_data_toList, List.append_assoc, hd, UInt64.toNat_mod, hp_toNat,
        List.singleton_append]; rfl

theorem pow10Up_spec_of_steps
    (upFn : Nat → UInt64 → UInt64 → UInt64)
    (hSucc : ∀ fuel q p, fuel < 20 →
      upFn (fuel + 1) q p = if p ≤ q then upFn fuel q (p * 10) else p)
    (n : UInt64) :
    ∀ (fuel j : Nat),
      j + fuel = 20 → j ≤ 19 → (j = 0 ∨ 10 ^ j ≤ n.toNat) →
      ∃ k, k ≤ 19 ∧ upFn fuel (n / 10) (UInt64.ofNat (10 ^ j)) = UInt64.ofNat (10 ^ k) ∧
        (k = 0 ∨ 10 ^ k ≤ n.toNat) ∧ n.toNat < 10 ^ (k + 1)
  | 0, _, _, _, _ => by omega
  | f' + 1, j, _, hj, hlow => by
    rw [hSucc f' (n / 10) (UInt64.ofNat (10 ^ j)) (by omega)]
    have hp_toNat := u64_pow10_toNat hj
    have hq_toNat : (n / 10).toNat = n.toNat / 10 := by rw [UInt64.toNat_div]; rfl
    by_cases hle : UInt64.ofNat (10 ^ j) ≤ n / 10
    · simp only [hle, ↓reduceIte]
      have hle_nat : 10 ^ j ≤ n.toNat / 10 := by
        have h := UInt64.le_iff_toNat_le.mp hle; rwa [hp_toNat, hq_toNat] at h
      have hnext_le : 10 ^ (j + 1) ≤ n.toNat := by rw [Nat.pow_succ]; omega
      have hn_lt20 : n.toNat < 10 ^ 20 :=
        Nat.lt_trans n.toNat_lt_size (by decide : 2 ^ 64 < 10 ^ 20)
      have hj1 : j + 1 ≤ 19 := by
        by_cases h19 : j + 1 ≤ 19
        · exact h19
        · have hpow : 10 ^ 20 ≤ 10 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
      have hmul : UInt64.ofNat (10 ^ j) * 10 = UInt64.ofNat (10 ^ (j + 1)) := u64_ext <| by
        rw [UInt64.toNat_mul, hp_toNat, u64_pow10_toNat hj1]
        change (10 ^ j * 10) % 2 ^ 64 = 10 ^ (j + 1)
        rw [← Nat.pow_succ, Nat.mod_eq_of_lt (pow10_lt_u64 hj1)]
      rw [hmul]
      exact pow10Up_spec_of_steps upFn hSucc n f' (j + 1) (by omega) hj1 (Or.inr hnext_le)
    · simp only [hle, ↓reduceIte]
      have hgt_nat : n.toNat / 10 < 10 ^ j := by
        have h : ¬ (UInt64.ofNat (10 ^ j)).toNat ≤ (n / 10).toNat :=
          fun hle' => hle (UInt64.le_iff_toNat_le.mpr hle')
        rw [hp_toNat, hq_toNat] at h; omega
      exact ⟨j, hj, rfl, hlow, by rw [Nat.pow_succ]; omega⟩

theorem digitsPow10_succ_right :
    ∀ (k m : Nat),
      digitsPow10 (k + 1) m = digitsPow10 k (m / 10) ++ [UInt8.ofNat (48 + m % 10)]
  | 0, _ => rfl
  | k + 1, m => by
    change UInt8.ofNat (48 + m / 10 ^ (k + 2)) :: digitsPow10 (k + 1) (m % 10 ^ (k + 2)) =
      (UInt8.ofNat (48 + (m / 10) / 10 ^ (k + 1)) ::
        digitsPow10 k ((m / 10) % 10 ^ (k + 1))) ++ [UInt8.ofNat (48 + m % 10)]
    have hpow : 10 ^ (k + 2) = 10 * 10 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmod_mod : m % 10 ^ (k + 2) % 10 = m % 10 := Nat.mod_mod_of_dvd m ⟨10 ^ (k + 1), hpow⟩
    rw [List.cons_append, digitsPow10_succ_right k (m % 10 ^ (k + 2)), hmod_mod,
      Nat.div_div_eq_div_mul, hpow, Nat.mod_mul_right_div_self]

theorem digitChar_0 : Nat.digitChar 0 = '0' := Nat.digitChar_eq_zero.mpr rfl
theorem digitChar_1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
theorem digitChar_2 : Nat.digitChar 2 = '2' := Nat.digitChar_eq_two.mpr rfl
theorem digitChar_3 : Nat.digitChar 3 = '3' := Nat.digitChar_eq_three.mpr rfl
theorem digitChar_4 : Nat.digitChar 4 = '4' := Nat.digitChar_eq_four.mpr rfl
theorem digitChar_5 : Nat.digitChar 5 = '5' := Nat.digitChar_eq_five.mpr rfl
theorem digitChar_6 : Nat.digitChar 6 = '6' := Nat.digitChar_eq_six.mpr rfl
theorem digitChar_7 : Nat.digitChar 7 = '7' := Nat.digitChar_eq_seven.mpr rfl
theorem digitChar_8 : Nat.digitChar 8 = '8' := Nat.digitChar_eq_eight.mpr rfl
theorem digitChar_9 : Nat.digitChar 9 = '9' := Nat.digitChar_eq_nine.mpr rfl

theorem nat_repr_1d (d : Nat) (hd : d < 10) (c : Char) (hc : Nat.digitChar d = c) :
    Nat.repr d = String.singleton c := by rw [Nat.repr_of_lt hd, hc]

theorem u64_repr_1d (u : UInt64) (d : Nat) (hu : u.toNat = d) (hd : d < 10) (c : Char)
    (hc : Nat.digitChar d = c) : Nat.repr u.toNat = String.singleton c := by
  rw [hu, Nat.repr_of_lt hd, hc]

theorem u64_repr_2d (u : UInt64) (n : Nat) (hu : u.toNat = n) (h10 : 10 ≤ n)
    (hd1 : n / 10 < 10) (c1 c2 : Char)
    (hc1 : Nat.digitChar (n / 10) = c1) (hc2 : Nat.digitChar (n % 10) = c2) :
    Nat.repr u.toNat = String.singleton c1 ++ String.singleton c2 := by
  rw [hu, Nat.repr_of_ge h10, Nat.repr_of_lt hd1, hc1, hc2]

theorem digit_toUTF8_eq (d : Nat) (hd : d < 10) :
    (String.singleton d.digitChar).toUTF8.data.toList = [UInt8.ofNat (48 + d)] := by
  match d, hd with
  | 0, _ => rw [digitChar_0]; rfl | 1, _ => rw [digitChar_1]; rfl
  | 2, _ => rw [digitChar_2]; rfl | 3, _ => rw [digitChar_3]; rfl
  | 4, _ => rw [digitChar_4]; rfl | 5, _ => rw [digitChar_5]; rfl
  | 6, _ => rw [digitChar_6]; rfl | 7, _ => rw [digitChar_7]; rfl
  | 8, _ => rw [digitChar_8]; rfl | 9, _ => rw [digitChar_9]; rfl
  | _ + 10, _ => omega

theorem digitsPow10_eq_natRepr :
    ∀ (k m : Nat), (k = 0 ∨ 10 ^ k ≤ m) → m < 10 ^ (k + 1) →
      digitsPow10 k m = (Nat.repr m).toUTF8.data.toList
  | 0, m, _, hm => by
    have hm10 : m < 10 := by simpa using hm
    rw [Nat.repr_of_lt hm10, digit_toUTF8_eq m hm10]; rfl
  | k + 1, m, hlow, hm => by
    have hge_pow : 10 ^ (k + 1) ≤ m := hlow.resolve_left (Nat.succ_ne_zero k)
    have h10 : 10 ≤ 10 ^ (k + 1) :=
      Nat.le_trans (by decide : 10 ≤ 10 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega))
    have hge10 : 10 ≤ m := by omega
    have hdiv_lt : m / 10 < 10 ^ (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]; exact hm
    have hdiv_low : k = 0 ∨ 10 ^ k ≤ m / 10 :=
      Or.inr ((Nat.le_div_iff_mul_le (by omega)).mpr (by rw [← Nat.pow_succ]; exact hge_pow))
    rw [digitsPow10_succ_right, digitsPow10_eq_natRepr k (m / 10) hdiv_low hdiv_lt,
      Nat.repr_of_ge hge10, toUTF8_append, ByteArray.toList_data_append,
      digit_toUTF8_eq (m % 10) (Nat.mod_lt m (by omega))]

theorem emitU64Dec_eq_of_steps
    (upFn : Nat → UInt64 → UInt64 → UInt64)
    (downFn : Nat → ByteArray → UInt64 → UInt64 → ByteArray)
    (hUpSucc : ∀ fuel q p, fuel < 20 →
      upFn (fuel + 1) q p = if p ≤ q then upFn fuel q (p * 10) else p)
    (hDownZero : ∀ ba n p, downFn 0 ba n p = ba.push (48 + (n / p).toUInt8))
    (hDownSucc : ∀ fuel ba n p, fuel < 20 →
      downFn (fuel + 1) ba n p =
        let ba' := ba.push (48 + (n / p).toUInt8)
        if p == 1 then ba' else downFn fuel ba' (n % p) (p / 10))
    (ba : ByteArray) (n : UInt64) :
    downFn 20 ba n (upFn 20 (n / 10) 1) = ba ++ (Nat.repr n.toNat).toUTF8 := by
  obtain ⟨k, hk, hpow, hlow, hlt⟩ :=
    pow10Up_spec_of_steps upFn hUpSucc n 20 0 rfl (by omega) (Or.inl rfl)
  apply ba_eq_of_data_toList
  rw [show (1 : UInt64) = UInt64.ofNat (10 ^ 0) from rfl, hpow,
    emitPowDown_eq_digitsPow10_of_steps downFn hDownZero hDownSucc k 20 ba n
      (by omega) (by omega) hk hlt,
    digitsPow10_eq_natRepr k n.toNat hlow hlt, ByteArray.toList_data_append]

theorem int64_toInt_eq_u64 (i : Int64) :
    ((i.toUInt64 >>> 63) = 1 →
      i.toInt = -((0 - i.toUInt64).toNat : Int) ∧ 0 < (0 - i.toUInt64).toNat) ∧
    ((i.toUInt64 >>> 63) ≠ 1 → i.toInt = (i.toUInt64.toNat : Int)) := by
  have hlt : i.toUInt64.toNat < 2 ^ 64 := i.toUInt64.toNat_lt_size
  have hsh : (i.toUInt64 >>> 63).toNat = i.toUInt64.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight]
    change i.toUInt64.toNat >>> (63 % 64) = i.toUInt64.toNat / 2 ^ 63
    rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  have htoInt : i.toInt = if 2 * i.toUInt64.toNat < 2 ^ 64 then (i.toUInt64.toNat : Int)
      else (i.toUInt64.toNat : Int) - (2 ^ 64 : Nat) := rfl
  rw [htoInt]
  refine ⟨fun hneg => ?_, fun hpos => ?_⟩
  · have hq := congrArg UInt64.toNat hneg; rw [hsh] at hq
    have hcond : ¬ (2 * i.toUInt64.toNat < 2 ^ 64) := by
      change i.toUInt64.toNat / 2 ^ 63 = 1 at hq; omega
    have hsub : (0 - i.toUInt64).toNat = 2 ^ 64 - i.toUInt64.toNat := by
      rw [UInt64.toNat_sub, UInt64.toNat_zero, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    simp only [hcond, ↓reduceIte]; rw [hsub]; omega
  · have hq : i.toUInt64.toNat / 2 ^ 63 = 0 :=
      match Nat.eq_zero_or_pos (i.toUInt64.toNat / 2 ^ 63) with
      | .inl hz => hz
      | .inr _ => absurd (u64_ext <| by rw [hsh]; change i.toUInt64.toNat / 2 ^ 63 = 1; omega)
          hpos
    have hcond : 2 * i.toUInt64.toNat < 2 ^ 64 := by omega
    simp only [hcond, ↓reduceIte]

theorem emitI64Dec_eq_of_u64
    (emitU64 : ByteArray → UInt64 → ByteArray)
    (hU64 : ∀ ba n, emitU64 ba n = ba ++ (Nat.repr n.toNat).toUTF8)
    (ba : ByteArray) (i : Int64) :
    (if (i.toUInt64 >>> 63) == 1 then emitU64 (ba.push 0x2d) (0 - i.toUInt64)
      else emitU64 ba i.toUInt64) = ba ++ (toString i).toUTF8 := by
  have ⟨hneg, hpos⟩ := int64_toInt_eq_u64 i
  change _ = ba ++ (Int.repr i.toInt).toUTF8
  by_cases h : (i.toUInt64 >>> 63) = 1
  · simp only [h, beq_self_eq_true, ↓reduceIte]
    obtain ⟨hi, hm⟩ := hneg h
    rw [hi, Int.repr_eq_ite]
    have hneg_lt : ¬ (0 ≤ -((0 - i.toUInt64).toNat : Int)) := by omega
    simp only [hneg_lt, ↓reduceIte, Int.neg_neg, Int.toNat_natCast]
    rw [hU64, toUTF8_append, ba_push_eq_append ba 0x2d "-" rfl, ByteArray.append_assoc]
  · simp only [beq_false_of_ne h, Bool.false_eq_true, ↓reduceIte]
    rw [hpos h, Int.repr_eq_ite]
    simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
    exact hU64 ba i.toUInt64

end

end LeanQbe.T.ByteArrayDecimal
