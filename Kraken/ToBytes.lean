abbrev Nat.take (v : Nat) (w : Nat) : Nat := v % 2 ^ w
abbrev Int.take (v : Int) (w : Nat) : Int := v % (2 : Int) ^ w

instance : Coe UInt8 (BitVec 8) := ⟨UInt8.toBitVec⟩
instance : Coe UInt16 (BitVec 16) := ⟨UInt16.toBitVec⟩
instance : Coe UInt32 (BitVec 32) := ⟨UInt32.toBitVec⟩
instance : Coe UInt64 (BitVec 64) := ⟨UInt64.toBitVec⟩

def Int.ofBytes (bs : List UInt8) : Int :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

def Nat.ofBytes (bs : List UInt8) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

def Int.toBytes (n : Nat) (v : Int) : List UInt8 :=
  match n with
  | 0 => []
  | n' + 1 => ((v.take 8).toNat.toUInt8) :: Int.toBytes n' (v / 256)

theorem Int.toBytes_length (n : Nat) (v : Int) : (Int.toBytes n v).length = n := by
  induction n generalizing v <;> simp [Int.toBytes, *]

def Nat.toBytes (n : Nat) (v : Nat) : List UInt8 :=
  match n with
  | 0 => []
  | n' + 1 => (v.take 8).toUInt8 :: Nat.toBytes n' (v / 256)

theorem Nat.toBytes_length (n : Nat) (v : Nat) : (Nat.toBytes n v).length = n := by
  induction n generalizing v <;> simp [Nat.toBytes, *]

def UInt8.toBytes (val : UInt8) : List UInt8 :=
  Int.toBytes 1 val.toBitVec.toInt

theorem UInt8.toBytes_length (val : UInt8) : val.toBytes.length = 1 := by
  simp [toBytes, Int.toBytes_length]

def UInt16.toBytes (val : UInt16) : List UInt8 :=
  Int.toBytes 2 val.toBitVec.toInt

theorem UInt16.toBytes_length (val : UInt16) : val.toBytes.length = 2 := by
  simp [toBytes, Int.toBytes_length]

def UInt32.toBytes (val : UInt32) : List UInt8 :=
  Int.toBytes 4 val.toBitVec.toInt

theorem UInt32.toBytes_length (val : UInt32) : val.toBytes.length = 4 := by
  simp [toBytes, Int.toBytes_length]

def UInt64.toBytes (val : UInt64) : List UInt8 :=
  Int.toBytes 8 val.toBitVec.toInt

theorem UInt64.toBytes_length (val : UInt64) : val.toBytes.length = 8 := by
  simp [toBytes, Int.toBytes_length]


private theorem emod_mul_add_div_helper (d M K RQ RV : Int) : d * (M * K + RQ) + RV = RQ * d + RV + (M * d) * K := by
  rw [Int.mul_add]
  ac_rfl

private theorem emod_mul_add_div (v : Int) (M : Int) (d : Int) (hM : M > 0) (hd : d > 0) :
    ((v / d) % M) * d + v % d = v % (M * d) := by
  have h_vd : v / d = M * ((v / d) / M) + (v / d) % M := (Int.mul_ediv_add_emod (v / d) M).symm
  have h_v : v = d * (v / d) + v % d := (Int.mul_ediv_add_emod v d).symm
  rw [h_vd, emod_mul_add_div_helper] at h_v
  conv => rhs; rw [h_v, Int.add_mul_emod_self_left]
  have h_nn : 0 ≤ ((v / d) % M) * d + v % d :=
    Int.add_nonneg (Int.mul_nonneg (Int.emod_nonneg _ (by omega)) (by omega)) (Int.emod_nonneg _ (by omega))
  have h_lt : ((v / d) % M) * d + v % d < M * d := by
    have h := Int.mul_le_mul_of_nonneg_right (show (v / d) % M ≤ M - 1 by have := Int.emod_lt_of_pos (v / d) hM; omega) (show 0 ≤ d by omega)
    have := Int.emod_lt_of_pos v hd; rw [Int.sub_mul, Int.one_mul] at h; omega
  exact (Int.emod_eq_of_lt h_nn h_lt).symm

theorem Int.ofBytes_cons (b : UInt8) (bs : List UInt8) : Int.ofBytes (b :: bs) = Int.ofBytes bs * 256 + b.toNat := rfl

theorem ofBytes_toBytes (n : Nat) (v : Int) : Int.ofBytes (Int.toBytes n v) = v.take (8 * n) := by
  induction n generalizing v with
  | zero =>
    simp [Int.toBytes, Int.ofBytes, Int.take]
  | succ n ih =>
    simp [Int.toBytes, Int.ofBytes_cons]
    rw [ih]
    simp [Int.take]
    have h_eq : max (v % 256) 0 % 256 = v % 256 := by omega
    rw [h_eq]
    have h_pow : (2 : Int) ^ (8 * (n + 1)) = (2 : Int) ^ (8 * n) * 256 := by
      have h1 : 8 * (n + 1) = 8 * n + 8 := by omega
      rw [h1]
      rw [Int.pow_add]
      rfl
    rw [h_pow]
    apply emod_mul_add_div
    · exact Int.pow_pos (by decide)
    · omega

private theorem BitVec.ofInt_emod_self (w : Nat) (i : Int) : BitVec.ofInt w (i % (2 : Int) ^ w) = BitVec.ofInt w i := by
  simp [BitVec.ofInt]


private theorem pow_256_eq_pow_2 (n : Nat) (w : Nat) (h : w = 8 * n) : (256 : Int)^n = (2 : Int)^w := by
  subst w
  rw [show (256 : Int) = 2 ^ 8 by decide, ← Int.pow_mul]

theorem BitVec.ofInt_ofBytes_toBytes (w : Nat) (n : Nat) (h_wn : w = 8 * n) (val : BitVec w) :
    BitVec.ofInt w (Int.ofBytes (Int.toBytes n val.toInt)) = val := by
  rw [ofBytes_toBytes, show 8 * n = w from h_wn.symm, Int.take, BitVec.ofInt_emod_self]
  exact BitVec.ofInt_toInt

theorem Int.ofBytes_ge_zero (bs : List UInt8) : 0 <= Int.ofBytes bs := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    simp [Int.ofBytes_cons]
    omega

theorem Int.ofBytes_lt (bs : List UInt8) : Int.ofBytes bs < 256 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    simp [Int.ofBytes_cons, Int.pow_succ]
    have := Int.ofBytes_ge_zero bs
    dsimp [UInt8.toNat]
    omega

private theorem emod_div_mul (x : Int) (M : Int) (d : Int) (hM : M > 0) (hd : d > 0) :
    (x % (M * d)) / d = (x / d) % M := by
  have h_mul_pos : M * d > 0 := Int.mul_pos hM hd
  have h_eq : x = x % (M * d) + (M * d) * (x / (M * d)) := by
    have := Int.mul_ediv_add_emod x (M * d)
    omega
  have h_div : x / d = (x % (M * d)) / d + M * (x / (M * d)) := by
    have h_mul : (M * d) * (x / (M * d)) = (M * (x / (M * d))) * d := by ac_rfl
    have h_eq' := h_eq
    rw [h_mul] at h_eq'
    have h_div_exact : x / d = (x % (M * d) + (M * (x / (M * d))) * d) / d := congrArg (· / d) h_eq'
    rw [h_div_exact]
    apply Int.add_mul_ediv_right
    omega
  have h_mod_eq : (x / d) % M = ((x % (M * d)) / d) % M := by
    rw [h_div]
    rw [Int.add_mul_emod_self_left]
  symm
  rw [h_mod_eq]
  apply Int.emod_eq_of_lt
  · rw [Int.ediv_nonneg_iff_of_pos hd]
    apply Int.emod_nonneg
    omega
  · have h_md_ne : M * d ≠ 0 := by omega
    have h_lt := Int.emod_lt x h_md_ne
    have h_abs : (Int.natAbs (M * d) : Int) = M * d := Int.natAbs_of_nonneg (by omega)
    rw [h_abs] at h_lt
    apply Int.ediv_lt_of_lt_mul hd
    exact h_lt

theorem Int.toBytes_emod (n : Nat) (x : Int) : Int.toBytes n (x.take (8 * n)) = Int.toBytes n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Int.toBytes, Int.take]
    have h_pow : (2 : Int) ^ (8 * (n + 1)) = (2 : Int) ^ (8 * n) * 256 := by
      have h1 : 8 * (n + 1) = 8 * n + 8 := by omega
      rw [h1]
      rw [Int.pow_add]
      rfl
    rw [h_pow]
    have h_mod : (x % ((2 : Int) ^ (8 * n) * 256)) % 2 ^ 8 = x % 2 ^ 8 := by
      show (x % ((2 : Int) ^ (8 * n) * 256)) % 256 = x % 256
      apply Int.emod_emod_of_dvd
      rw [Int.mul_comm]
      exact ⟨(2 : Int) ^ (8 * n), rfl⟩
    have h_div : (x % ((2 : Int) ^ (8 * n) * 256)) / 256 = (x / 256) % (2 : Int) ^ (8 * n) := by
      apply emod_div_mul
      · exact Int.pow_pos (by decide)
      · decide
    rw [h_mod, h_div]
    rw [ih (x / 256)]

theorem Int.ofBytes_append (l1 l2 : List UInt8) :
    Int.ofBytes (l1 ++ l2) = Int.ofBytes l1 + 256 ^ l1.length * Int.ofBytes l2 := by
  induction l1 with
  | nil => simp [Int.ofBytes]
  | cons b l1 ih =>
    simp [Int.ofBytes_cons, ih, Int.pow_succ]
    rw [show 256 ^ l1.length * 256 * Int.ofBytes l2 = 256 ^ l1.length * Int.ofBytes l2 * 256 by ac_rfl]
    omega

theorem BitVec.ofInt_ofBytes_take (w : Nat) (n : Nat) (h_wn : w = 8 * n) (bs : List UInt8) :
    BitVec.ofInt w (Int.ofBytes bs) = BitVec.ofInt w (Int.ofBytes (bs.take n)) := by
  conv => lhs; rw [show bs = bs.take n ++ bs.drop n by exact (List.take_append_drop n bs).symm]
  rw [Int.ofBytes_append]
  by_cases hn : bs.length < n
  · rw [show bs.drop n = [] by apply List.drop_eq_nil_of_le; omega]
    simp [Int.ofBytes]
  · rw [show (bs.take n).length = n by apply List.length_take_of_le; omega]
    rw [pow_256_eq_pow_2 n w h_wn]
    rw [BitVec.ofInt_add, BitVec.ofInt_mul]
    rw [show BitVec.ofInt w (2 ^ w) = 0#w by apply BitVec.eq_of_toNat_eq; simp]
    simp

theorem Int.toBytes_ofBytes_all (bs : List UInt8) :
    Int.toBytes bs.length (Int.ofBytes bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with | ofBitVec val =>
    simp [Int.toBytes, Int.ofBytes_cons, UInt8.toNat]
    have h_lt : val.toNat < 256 := val.isLt
    have h2 : (Int.ofBytes bs * 256 + val.toNat) / 256 = Int.ofBytes bs := by omega
    have h_take : (Int.ofBytes bs * 256 + val.toNat).take 8 = (val.toNat : Int).take 8 := by
      dsimp [Int.take]
      omega
    have h3 : ((val.toNat : Int).take 8).toNat = val.toNat := by
      dsimp [Int.take]
      omega
    simp [h2, h_take, h3, ih]

theorem Int.toBytes_ofBytes (n : Nat) (bs : List UInt8) (h : n ≤ bs.length) :
    Int.toBytes n (Int.ofBytes bs) = bs.take n := by
  have h_lt : Int.ofBytes (bs.take n) < 256 ^ n := by
    have := Int.ofBytes_lt (bs.take n)
    rw [List.length_take_of_le h] at this
    exact this
  rw [← Int.toBytes_emod n (Int.ofBytes bs)]
  simp only [Int.take]
  rw [← pow_256_eq_pow_2 n (8 * n) rfl]
  have h_mod : Int.ofBytes bs % 256 ^ n = Int.ofBytes (bs.take n) := by
    conv =>
      lhs
      arg 1
      rw [show bs = bs.take n ++ bs.drop n by exact (List.take_append_drop n bs).symm]
    rw [Int.ofBytes_append]
    rw [List.length_take_of_le h]
    rw [Int.add_mul_emod_self_left]
    rw [Int.emod_eq_of_lt (Int.ofBytes_ge_zero _) h_lt]
  rw [h_mod]
  rw [← Int.toBytes_emod n]
  simp only [Int.take]
  rw [← pow_256_eq_pow_2 n (8 * n) rfl]
  rw [Int.emod_eq_of_lt (Int.ofBytes_ge_zero _) h_lt]
  conv =>
    lhs
    arg 1
    rw [show n = (bs.take n).length by rw [List.length_take_of_le h]]
  exact Int.toBytes_ofBytes_all (bs.take n)

theorem Int.toBytes_bmod_ofBytes (n : Nat) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n ((Int.ofBytes bs).bmod (256 ^ n)) = bs := by
  have h_toBytes : Int.toBytes n (Int.ofBytes bs) = bs := by
    have h_tob := Int.toBytes_ofBytes_all bs
    rw [h] at h_tob
    exact h_tob
  conv =>
    rhs
    rw [← h_toBytes]
  rw [← Int.toBytes_emod n ((Int.ofBytes bs).bmod (256 ^ n))]
  rw [← Int.toBytes_emod n (Int.ofBytes bs)]
  congr 1
  unfold Int.bmod
  dsimp
  have h_pow : (256 : Int)^n = (2 : Int) ^ (8 * n) := by
    exact pow_256_eq_pow_2 n (8 * n) rfl
  split
  · simp only [Int.take]
    rw [h_pow]
    rw [Int.emod_emod]
  · have h_sub : ofBytes bs % 256 ^ n - 256 ^ n = ofBytes bs % 256 ^ n + 256 ^ n * -1 := by omega
    rw [h_sub]
    simp only [Int.take]
    rw [h_pow]
    rw [Int.add_mul_emod_self_left]
    rw [Int.emod_emod]


private theorem Nat.mod_mul_add_div (v : Nat) (M : Nat) (d : Nat) :
    ((v / d) % M) * d + v % d = v % (M * d) := by
  rw [Nat.mul_comm M d, Nat.mod_mul, Nat.add_comm, Nat.mul_comm]

theorem Nat.ofBytes_cons (b : UInt8) (bs : List UInt8) : Nat.ofBytes (b :: bs) = Nat.ofBytes bs * 256 + b.toNat := rfl



theorem Nat.ofBytes_toBytes (n : Nat) (v : Nat) : Nat.ofBytes (Nat.toBytes n v) = v.take (8 * n) := by
  induction n generalizing v with
  | zero =>
    simp [Nat.toBytes, Nat.ofBytes, Nat.take]
    omega
  | succ n ih =>
    simp [Nat.toBytes, Nat.ofBytes_cons, ih, Nat.take]
    rw [show 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 by
      have : 8 * (n + 1) = 8 * n + 8 := by omega
      rw [this, Nat.pow_add]]
    exact Nat.mod_mul_add_div v (2 ^ (8 * n)) 256

theorem Nat.toBytes_ofBytes (n : Nat) (bs : List UInt8) (h : n ≤ bs.length) :
    Nat.toBytes n (Nat.ofBytes bs) = bs.take n := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      cases b with | ofBitVec val =>
      simp only [Nat.toBytes, Nat.ofBytes_cons, List.take_succ_cons, UInt8.toNat]
      have h_div : (Nat.ofBytes bs * 256 + val.toNat) / 256 = Nat.ofBytes bs := by omega
      have h_mod : (Nat.ofBytes bs * 256 + val.toNat).take 8 = val.toNat := by
        dsimp [Nat.take]
        omega
      rw [h_div, h_mod]
      simp only [List.length_cons] at h
      simp [ih bs (by omega)]

private theorem BitVec.toBytes_ofBytes (w n : Nat) (h_wn : w = 8 * n)
    (bs : List UInt8) (h : n ≤ bs.length) :
    Int.toBytes n (BitVec.ofInt w (Int.ofBytes bs)).toInt = bs.take n := by
  rw [BitVec.ofInt_ofBytes_take w n h_wn, BitVec.toInt_ofInt]
  rw [show 2 ^ w = 256 ^ n by
    subst w
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]]
  exact Int.toBytes_bmod_ofBytes n (bs.take n) (List.length_take_of_le h)

def UInt8.ofBytes (bs : List UInt8) : UInt8 :=
  ⟨BitVec.ofInt 8 (Int.ofBytes bs)⟩

theorem UInt8.ofBytes_toBytes (val : UInt8) : UInt8.ofBytes val.toBytes = val := by
  exact congrArg UInt8.ofBitVec (BitVec.ofInt_ofBytes_toBytes 8 1 rfl val.toBitVec)

theorem UInt8.toBytes_ofBytes (bs : List UInt8) (h : 1 ≤ bs.length) : (UInt8.ofBytes bs).toBytes = bs.take 1 := by
  exact BitVec.toBytes_ofBytes 8 1 rfl bs h

def UInt16.ofBytes (bs : List UInt8) : UInt16 :=
  ⟨BitVec.ofInt 16 (Int.ofBytes bs)⟩

theorem UInt16.ofBytes_toBytes (val : UInt16) : UInt16.ofBytes val.toBytes = val := by
  exact congrArg UInt16.ofBitVec (BitVec.ofInt_ofBytes_toBytes 16 2 rfl val.toBitVec)

theorem UInt16.toBytes_ofBytes (bs : List UInt8) (h : 2 ≤ bs.length) : (UInt16.ofBytes bs).toBytes = bs.take 2 := by
  exact BitVec.toBytes_ofBytes 16 2 rfl bs h

def UInt32.ofBytes (bs : List UInt8) : UInt32 :=
  ⟨BitVec.ofInt 32 (Int.ofBytes bs)⟩

theorem UInt32.ofBytes_toBytes (val : UInt32) : UInt32.ofBytes val.toBytes = val := by
  exact congrArg UInt32.ofBitVec (BitVec.ofInt_ofBytes_toBytes 32 4 rfl val.toBitVec)

theorem UInt32.toBytes_ofBytes (bs : List UInt8) (h : 4 ≤ bs.length) : (UInt32.ofBytes bs).toBytes = bs.take 4 := by
  exact BitVec.toBytes_ofBytes 32 4 rfl bs h

def UInt64.ofBytes (bs : List UInt8) : UInt64 :=
  ⟨BitVec.ofInt 64 (Int.ofBytes bs)⟩

theorem UInt64.ofBytes_toBytes (val : UInt64) : UInt64.ofBytes val.toBytes = val := by
  exact congrArg UInt64.ofBitVec (BitVec.ofInt_ofBytes_toBytes 64 8 rfl val.toBitVec)

theorem UInt64.toBytes_ofBytes (bs : List UInt8) (h : 8 ≤ bs.length) : (UInt64.ofBytes bs).toBytes = bs.take 8 := by
  exact BitVec.toBytes_ofBytes 64 8 rfl bs h
