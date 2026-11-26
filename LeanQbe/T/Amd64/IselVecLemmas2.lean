module

public import LeanQbe.T.Amd64.IselVecLemmas1

/-!
# SysV x64 Vector Target Verification — Part 2

* Pure `Float32.Model` / `sseBinOp` ↔ `liftFloatRel2` (`v4f32`) soundness (`addps`/`subps`).
* Balanced `32`-bit SIMD vector & shuffle `BitVec` bridges (`vpaddd`, `vpternlogd`, `vprord`,
  `vpsrld`, `pshufd`, `pshufb`, `palignr`, `pblendw`, `mkpair`/`unpair`).
* Single-instruction `Directive.FallsTo` lemmas and `x64Emit*` weak-precondition combinators.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std

/-! ## 1. `Float32.Model` / `sseBinOp` soundness (`addps`, `subps` on `v4f32`) -/

section FloatBridge

open Float.Model

private theorem sign_ofBitVec_toBitVec (s : UnpackedFloat.Sign) :
    UnpackedFloat.Sign.ofBitVec s.toBitVec = s := by
  cases s <;> decide

private theorem sign_toBitVec_ofBitVec (b : BitVec 1) :
    (UnpackedFloat.Sign.ofBitVec b).toBitVec = b := by
  by_cases h : b = 0#1
  · subst h; rfl
  · have h1 : b = 1#1 := BitVec.eq_of_toNat_eq (by
      have hlt : b.toNat < 2 := b.isLt
      have h0 : b.toNat ≠ 0 := fun ht => h (BitVec.eq_of_toNat_eq ht)
      change b.toNat = 1; omega)
    subst h1; rfl

private theorem unpackSign_packComponents_binary32 (s : UnpackedFloat.Sign)
    (e : BitVec 8) (m : BitVec 23) :
    UnpackedFloat.unpackSign (spec := .binary32) (UnpackedFloat.packComponents .binary32 s e m) =
      s.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain rfl : i = 0 := by omega
  simp only [UnpackedFloat.unpackSign, UnpackedFloat.packComponents, BitVec.getLsbD_extractLsb',
    Nat.add_zero, show (0 : Nat) < 1 from by decide, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  simp [show ¬(23 + 8 < 23) from by decide, show ¬(23 + 8 - 23 < 8) from by decide]

private theorem unpackExponent_packComponents_binary32 (s : UnpackedFloat.Sign)
    (e : BitVec 8) (m : BitVec 23) :
    UnpackedFloat.unpackExponent (spec := .binary32)
      (UnpackedFloat.packComponents .binary32 s e m) = e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi8 : i < 8 := hi
  simp only [UnpackedFloat.unpackExponent, UnpackedFloat.packComponents, BitVec.getLsbD_extractLsb',
    hi8, decide_true, Bool.true_and, BitVec.getLsbD_append]
  simp [show ¬(23 + i < 23) from by omega, show 23 + i - 23 = i from by omega, hi8]

private theorem unpackMantissa_packComponents_binary32 (s : UnpackedFloat.Sign)
    (e : BitVec 8) (m : BitVec 23) :
    UnpackedFloat.unpackMantissa (spec := .binary32)
      (UnpackedFloat.packComponents .binary32 s e m) = m := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi23 : i < 23 := hi
  simp only [UnpackedFloat.unpackMantissa, UnpackedFloat.packComponents, BitVec.getLsbD_extractLsb',
    hi23, decide_true, Bool.true_and, BitVec.getLsbD_append]
  simp [hi23]

private theorem unpack_not_isNaN_of_exp_ne {b : BitVec 32}
    (h : UnpackedFloat.unpackExponent (spec := .binary32) b ≠ -1#8) :
    (UnpackedFloat.unpack .binary32 b).isNaN = false := by
  simp only [UnpackedFloat.unpack, h, ↓reduceIte]
  by_cases h0 : UnpackedFloat.unpackExponent (spec := .binary32) b = 0#8
  · simp only [h0, ↓reduceIte]; split <;> rfl
  · simp only [h0, ↓reduceIte]; rfl

private theorem packComponents_unpack_eq (a : BitVec 32) :
    UnpackedFloat.packComponents .binary32
      (UnpackedFloat.Sign.ofBitVec (UnpackedFloat.unpackSign (spec := .binary32) a))
      (UnpackedFloat.unpackExponent (spec := .binary32) a)
      (UnpackedFloat.unpackMantissa (spec := .binary32) a) = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi32 : i < 32 := hi
  simp only [UnpackedFloat.packComponents, BitVec.getLsbD_append, sign_toBitVec_ofBitVec,
    UnpackedFloat.unpackSign, UnpackedFloat.unpackExponent, UnpackedFloat.unpackMantissa,
    BitVec.getLsbD_extractLsb']
  by_cases hi23 : i < 23
  · simp [hi23]
  · by_cases hi31 : i < 31
    · simp [hi23, show i - 23 < 8 by omega, show 23 + (i - 23) = i by omega]
    · obtain rfl : i = 31 := by omega
      simp

private theorem unpack_notANumber_of_packedNaN :
    UnpackedFloat.unpack .binary32 (UnpackedFloat.packedNaN .binary32) = .notANumber := by
  simp [UnpackedFloat.unpack, UnpackedFloat.packedNaN]

private theorem unpack_packedInfinity (s : UnpackedFloat.Sign) :
    UnpackedFloat.unpack .binary32 (UnpackedFloat.packedInfinity .binary32 s) = .infinity s := by
  simp [UnpackedFloat.unpack, UnpackedFloat.packedInfinity,
    unpackSign_packComponents_binary32, sign_ofBitVec_toBitVec]

private theorem unpack_packedZero (s : UnpackedFloat.Sign) :
    UnpackedFloat.unpack .binary32 (UnpackedFloat.packedZero .binary32 s) = .zero s := by
  simp [UnpackedFloat.unpack, UnpackedFloat.packedZero,
    unpackSign_packComponents_binary32, sign_ofBitVec_toBitVec]

private theorem isNaN_unpack_pack_binary32 (u : UnpackedFloat) :
    (UnpackedFloat.unpack .binary32 (UnpackedFloat.pack .binary32 u)).isNaN = u.isNaN := by
  cases u with
  | notANumber => simp [UnpackedFloat.pack, unpack_notANumber_of_packedNaN, UnpackedFloat.isNaN]
  | infinity s => simp [UnpackedFloat.pack, unpack_packedInfinity, UnpackedFloat.isNaN]
  | zero s => simp [UnpackedFloat.pack, unpack_packedZero, UnpackedFloat.isNaN]
  | finite s m e hm =>
    dsimp only [UnpackedFloat.pack]
    have h8 : Format.binary32.exponentBits = 8 := rfl
    have h23 : Format.binary32.mantissaBitsWithoutImplicit = 23 := rfl
    by_cases hinf : 2 ^ Format.binary32.exponentBits ≤
        (e + ↑Format.binary32.exponentBias + ↑Format.binary32.mantissaBitsWithoutImplicit).toNat + 1
    · simp only [eq_true hinf, ↓reduceIte, unpack_packedInfinity]; rfl
    · simp only [eq_false hinf, ↓reduceIte]
      by_cases hm24 : m.log2 + 1 = Format.binary32.mantissaBits
      · simp only [eq_true hm24, ↓reduceIte]
        refine unpack_not_isNaN_of_exp_ne ?_
        rw [unpackExponent_packComponents_binary32]; intro h
        have hv := congrArg BitVec.toNat h
        have hlt : (e + ↑Format.binary32.exponentBias + ↑(23 : Nat)).toNat < 255 := by
          rw [h8, h23] at hinf; omega
        have hmod : (e + ↑Format.binary32.exponentBias + ↑(23 : Nat)).toNat % 2 ^ 8 =
            (e + ↑Format.binary32.exponentBias + ↑(23 : Nat)).toNat :=
          Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_ofNat, hmod] at hv
        have h255 : (-1#8 : BitVec 8).toNat = 255 := rfl
        omega
      · simp only [eq_false hm24, ↓reduceIte]
        refine unpack_not_isNaN_of_exp_ne ?_
        rw [unpackExponent_packComponents_binary32]; decide

private theorem pack_unpack_of_not_isNaN (a : BitVec 32)
    (hna : (UnpackedFloat.unpack .binary32 a).isNaN = false) :
    UnpackedFloat.pack .binary32 (UnpackedFloat.unpack .binary32 a) = a := by
  unfold UnpackedFloat.unpack at hna ⊢
  by_cases hexp1 : UnpackedFloat.unpackExponent (spec := .binary32) a = -1#8
  · by_cases hman0 : UnpackedFloat.unpackMantissa (spec := .binary32) a = 0#23
    · simp only [eq_true hexp1, eq_true hman0, ↓reduceIte, UnpackedFloat.pack,
        UnpackedFloat.packedInfinity]
      have h := packComponents_unpack_eq a; rwa [hexp1, hman0] at h
    · simp [hexp1, hman0, UnpackedFloat.isNaN] at hna
  · by_cases hexp0 : UnpackedFloat.unpackExponent (spec := .binary32) a = 0#8
    · by_cases hman0 : UnpackedFloat.unpackMantissa (spec := .binary32) a = 0#23
      · simp only [eq_false hexp1, eq_true hexp0, eq_true hman0, ↓reduceIte,
          UnpackedFloat.pack, UnpackedFloat.packedZero]
        have h := packComponents_unpack_eq a; rwa [hexp0, hman0] at h
      · simp only [eq_false hexp1, eq_true hexp0, ↓reduceIte, hman0, ↓reduceDIte,
          UnpackedFloat.pack]
        have hnz : (UnpackedFloat.unpackMantissa (spec := .binary32) a).toNat ≠ 0 :=
          fun h => hman0 (BitVec.eq_of_toNat_eq (by simpa using h))
        have hlog : (UnpackedFloat.unpackMantissa (spec := .binary32) a).toNat.log2 < 23 :=
          (Nat.log2_lt hnz).mpr (UnpackedFloat.unpackMantissa (spec := .binary32) a).isLt
        have hbi : (↑(UnpackedFloat.unpackExponent (spec := .binary32) a).toNat -
            (↑Format.binary32.exponentBias + ↑(23 : Nat)) +
            1 + ↑Format.binary32.exponentBias + ↑(23 : Nat) : Int).toNat = 1 := by
          rw [hexp0]; decide
        have hne24 : ¬((UnpackedFloat.unpackMantissa (spec := .binary32) a).toNat.log2 + 1 =
            Format.binary32.mantissaBits) := by
          change _ ≠ 24; omega
        rw [hbi]
        simp only [show ¬(2 ^ 8 ≤ (1 : Nat) + 1) from by decide, eq_false hne24, ↓reduceIte,
          show BitVec.ofNat Format.binary32.mantissaBitsWithoutImplicit
            (UnpackedFloat.unpackMantissa (spec := .binary32) a).toNat =
            UnpackedFloat.unpackMantissa (spec := .binary32) a from
              BitVec.eq_of_toNat_eq (by simp)]
        have h := packComponents_unpack_eq a; rwa [hexp0] at h
    · simp only [eq_false hexp1, eq_false hexp0, ↓reduceIte, UnpackedFloat.pack]
      have hbi_eq : (↑(UnpackedFloat.unpackExponent (spec := .binary32) a).toNat -
          (↑Format.binary32.exponentBias + ↑(23 : Nat)) +
          ↑Format.binary32.exponentBias + ↑(23 : Nat) : Int).toNat =
          (UnpackedFloat.unpackExponent (spec := .binary32) a).toNat := by
        change (↑(UnpackedFloat.unpackExponent (spec := .binary32) a).toNat -
          (↑127 + ↑23) + ↑127 + ↑23 : Int).toNat = _; omega
      have hexp_lt : (UnpackedFloat.unpackExponent (spec := .binary32) a).toNat < 255 := by
        have hlt8 : (UnpackedFloat.unpackExponent (spec := .binary32) a).toNat < 2 ^ 8 :=
          (UnpackedFloat.unpackExponent (spec := .binary32) a).isLt
        have hne : (UnpackedFloat.unpackExponent (spec := .binary32) a).toNat ≠ 255 :=
          fun h => hexp1 (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      have h23_bit :
          (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).getLsbD 23 =
            true := by
        rw [BitVec.getLsbD_append]; simp
      have hge :
          2 ^ 23 ≤
            (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).toNat := by
        rcases Nat.lt_or_ge
            (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).toNat
            (2 ^ 23) with hlt | h
        · have hsh :
              (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).toNat >>>
                23 = 0 := by
            rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
          have hfalse :
              (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).getLsbD 23 =
                false := by
            unfold BitVec.getLsbD Nat.testBit; rw [hsh]; decide
          rw [hfalse] at h23_bit; exact absurd h23_bit Bool.false_ne_true
        · exact h
      have hlt24 :
          (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).toNat < 2 ^ 24 :=
        (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).isLt
      have hlog_ge := (Nat.le_log2 (by omega)).mpr hge
      have hlog_lt := (Nat.log2_lt (by omega)).mpr hlt24
      have heq24 :
          (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).toNat.log2 + 1 =
          Format.binary32.mantissaBits := by
        change _ = 24; omega
      rw [hbi_eq]
      simp only [show ¬(2 ^ 8 ≤ (UnpackedFloat.unpackExponent (spec := .binary32) a).toNat + 1)
          by omega, eq_true heq24, ↓reduceIte]
      have hexp_eq : BitVec.ofNat 8 (UnpackedFloat.unpackExponent (spec := .binary32) a).toNat =
          UnpackedFloat.unpackExponent (spec := .binary32) a := BitVec.eq_of_toNat_eq (by simp)
      have hman_eq : BitVec.ofNat 23
            (1#1 ++ UnpackedFloat.unpackMantissa (spec := .binary32) a : BitVec 24).toNat =
          UnpackedFloat.unpackMantissa (spec := .binary32) a := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        have hi23 : i < 23 := hi
        simp only [BitVec.getLsbD_ofNat, hi23, decide_true, Bool.true_and, BitVec.testBit_toNat,
          BitVec.getLsbD_append]
        simp [hi23]
      rw [hexp_eq, hman_eq, packComponents_unpack_eq]

private theorem isFloatNaN_quiet (a : BitVec 32) (h : isFloatNaN .s a = true) :
    isFloatNaN .s (a ||| 0x400000#32) = true := by
  simp only [isFloatNaN, unpackFloat, Fmt.format, BitVec.cast_eq] at h ⊢
  unfold UnpackedFloat.unpack at h ⊢
  by_cases hexp : UnpackedFloat.unpackExponent (spec := .binary32) a = -1#8
  · have hexp' : UnpackedFloat.unpackExponent (spec := .binary32) (a ||| 0x400000#32) = -1#8 := by
      rw [← hexp]; apply BitVec.eq_of_getLsbD_eq; intro i hi
      have h0 : (0x400000#32 : BitVec 32).getLsbD (23 + i) = false := by
        have hi8 : i < 8 := hi
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | decide | omega
      simp [UnpackedFloat.unpackExponent, show i < 8 from hi, h0]
    have hman' : UnpackedFloat.unpackMantissa (spec := .binary32) (a ||| 0x400000#32) ≠ 0#23 := by
      intro hz; have h22 := congrArg (fun bv : BitVec 23 => bv.getLsbD 22) hz
      simp [UnpackedFloat.unpackMantissa] at h22
    simp [hexp', hman', UnpackedFloat.isNaN]
  · simp only [eq_false hexp, ↓reduceIte] at h
    by_cases hexp0 : UnpackedFloat.unpackExponent (spec := .binary32) a = 0#8
    · simp only [eq_true hexp0, ↓reduceIte] at h
      by_cases hman0 : UnpackedFloat.unpackMantissa (spec := .binary32) a = 0#23 <;>
        simp [hman0, UnpackedFloat.isNaN] at h
    · simp [eq_false hexp0, UnpackedFloat.isNaN] at h

private theorem toFloat32_isNaN_eq (a : BitVec 32) :
    a.toFloat32.isNaN = isFloatNaN .s a := by
  simp only [BitVec.toFloat32, Float32.isNaN, Float32.Model.isNaN, Float32.Model.unpack]
  exact isNaN_unpack_pack_binary32 (UnpackedFloat.unpack .binary32 a)

private theorem toFloat32_toModel_unpack (a : BitVec 32) (h : isFloatNaN .s a = false) :
    a.toFloat32.toModel.unpack = unpackFloat .s a := by
  simp only [BitVec.toFloat32, Float32.Model.unpack, unpackFloat]
  change UnpackedFloat.unpack .binary32
    (UnpackedFloat.pack .binary32 (UnpackedFloat.unpack .binary32 a)) = _
  rw [pack_unpack_of_not_isNaN a h]; rfl

private theorem sseBinOp_floatResultWp (op : Float32 → Float32 → Float32)
    (mop : Float.Model.Format → UnpackedFloat → UnpackedFloat → UnpackedFloat)
    (hop_bits : ∀ x y : Float32, (op x y).toBitVec =
      UnpackedFloat.pack .binary32 (mop .binary32 x.toModel.unpack y.toModel.unpack))
    (hop_nanL : ∀ y : UnpackedFloat, mop .binary32 .notANumber y = .notANumber)
    (hop_nanR : ∀ x : UnpackedFloat, mop .binary32 x .notANumber = .notANumber)
    (a b : BitVec 32) (k : BitVec 32 → Prop) :
    floatResultWp .s (mop .binary32 (unpackFloat .s a) (unpackFloat .s b)) k →
    k (sseBinOp op a b) := by
  intro hk
  dsimp only [sseBinOp]
  rw [toFloat32_isNaN_eq a, toFloat32_isNaN_eq b]
  by_cases ha : isFloatNaN .s a = true
  · have hna : unpackFloat .s a = .notANumber := by
      dsimp only [isFloatNaN] at ha; cases h : unpackFloat .s a <;> simp_all [UnpackedFloat.isNaN]
    rw [hna, hop_nanL] at hk
    simpa [ha] using hk _ (isFloatNaN_quiet a ha)
  · have ha' := Bool.eq_false_iff.mpr ha
    by_cases hb : isFloatNaN .s b = true
    · have hnb : unpackFloat .s b = .notANumber := by
        dsimp only [isFloatNaN] at hb; cases h : unpackFloat .s b <;> simp_all [UnpackedFloat.isNaN]
      rw [hnb, hop_nanR] at hk
      simpa [ha', hb] using hk _ (isFloatNaN_quiet b hb)
    · have hb' := Bool.eq_false_iff.mpr hb
      simp only [ha', hb', Bool.false_eq_true, ↓reduceIte]
      have hpack : (op a.toFloat32 b.toFloat32).toBitVec =
          packFloat .s (mop .binary32 (unpackFloat .s a) (unpackFloat .s b)) := by
        rw [hop_bits, toFloat32_toModel_unpack a ha', toFloat32_toModel_unpack b hb']; rfl
      have hnan : (op a.toFloat32 b.toFloat32).isNaN =
          (mop .binary32 (unpackFloat .s a) (unpackFloat .s b)).isNaN := by
        simp only [Float32.isNaN, Float32.Model.isNaN, Float32.Model.unpack]
        change UnpackedFloat.isNaN (UnpackedFloat.unpack .binary32 (op _ _).toBitVec) = _
        rw [hpack]; exact isNaN_unpack_pack_binary32 _
      rw [hnan]
      dsimp only [floatResultWp] at hk
      by_cases hres : (mop .binary32 (unpackFloat .s a) (unpackFloat .s b)).isNaN = true
      · simp only [hres, ↓reduceIte] at hk ⊢; exact hk _ (by decide)
      · have hres' := Bool.eq_false_iff.mpr hres
        simp only [hres', Bool.false_eq_true, ↓reduceIte] at hk ⊢; rwa [hpack]

theorem sseBinOp_add_wp (a b : BitVec 32) (k : BitVec 32 → Prop) :
    floatResultWp .s (UnpackedFloat.add .binary32 (unpackFloat .s a) (unpackFloat .s b)) k →
    k (sseBinOp (· + ·) a b) :=
  sseBinOp_floatResultWp (· + ·) UnpackedFloat.add
    (fun _ _ => rfl) (fun _ => rfl) (fun x => by cases x <;> rfl) a b k

theorem sseBinOp_sub_wp (a b : BitVec 32) (k : BitVec 32 → Prop) :
    floatResultWp .s (UnpackedFloat.sub .binary32 (unpackFloat .s a) (unpackFloat .s b)) k →
    k (sseBinOp (· - ·) a b) :=
  sseBinOp_floatResultWp (· - ·) UnpackedFloat.sub
    (fun _ _ => rfl) (fun _ => rfl) (fun x => by cases x <;> rfl) a b k

theorem x64IsF32Vec_size_pos {t : Ty} (h : x64IsF32Vec t = true) : 32 ≤ t.size := by
  induction t with
  | bool | bits _ => simp [x64IsF32Vec] at h
  | float f => cases f <;> simp [x64IsF32Vec] at h; decide
  | pair a b iha _ =>
    simp only [x64IsF32Vec, Bool.and_eq_true, beq_iff_eq] at h
    have := iha h.2; simp only [Ty.size]; omega

theorem x64IsF32Vec_128_eq {t : Ty} (hf : x64IsF32Vec t = true) (hsz : t.size = 128) :
    t = v4f32 := by
  have f32_64 : ∀ u, x64IsF32Vec u = true → u.size = 64 → u = .pair (.float .s) (.float .s) := by
    intro u hu husz
    cases u with
    | bool | bits _ => simp [x64IsF32Vec] at hu
    | float f => cases f <;> simp [x64IsF32Vec, Ty.size, Fmt.width] at hu husz
    | pair c d =>
      simp only [x64IsF32Vec, Bool.and_eq_true, beq_iff_eq] at hu
      rcases hu with ⟨rfl, hc⟩
      have hc32 : c.size = 32 := by simp only [Ty.size] at husz; omega
      cases c with
      | bool | bits _ => simp [x64IsF32Vec] at hc
      | float f => cases f <;> simp [x64IsF32Vec, Ty.size] at hc hc32; rfl
      | pair e f =>
        simp only [x64IsF32Vec, Bool.and_eq_true, beq_iff_eq] at hc
        rcases hc with ⟨rfl, he⟩
        have := x64IsF32Vec_size_pos he; simp only [Ty.size] at hc32; omega
  cases t with
  | bool | bits _ => simp [x64IsF32Vec] at hf
  | float f => cases f <;> simp [x64IsF32Vec, Ty.size, Fmt.width] at hf hsz
  | pair a b =>
    simp only [x64IsF32Vec, Bool.and_eq_true, beq_iff_eq] at hf
    rcases hf with ⟨rfl, ha⟩
    have haeq := f32_64 a ha (by simp only [Ty.size] at hsz; omega)
    rw [haeq]

end FloatBridge

/-! ## 2. Balanced SIMD vector & shuffle `BitVec` bridges -/

section BitVecBridges

theorem x64IsI32Vec_dvd_32 {t : Ty} (h : x64IsI32Vec t = true) : 32 ∣ t.size := by
  induction t with
  | bool | float _ => simp [x64IsI32Vec] at h
  | bits n =>
    by_cases hn : n = 32
    · subst hn; exact ⟨1, rfl⟩
    · simp [x64IsI32Vec, hn] at h
  | pair a b iha _ =>
    simp only [x64IsI32Vec, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, ha⟩
    obtain ⟨k, hk⟩ := iha ha
    exact ⟨k + k, by simp [Ty.size, hk, Nat.mul_add]⟩

theorem x64IsF32Vec_dvd_32 {t : Ty} (h : x64IsF32Vec t = true) : 32 ∣ t.size := by
  induction t with
  | bool | bits _ => simp [x64IsF32Vec] at h
  | float f => cases f <;> simp [x64IsF32Vec] at h; exact ⟨1, rfl⟩
  | pair a b iha _ =>
    simp only [x64IsF32Vec, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨k, hk⟩ := iha h.2
    exact ⟨k + k, by simp [Ty.size, ← h.1, hk, Nat.mul_add]⟩

theorem x64IsVecBits_dvd_32 {t : Ty} (h : x64IsVecBits t = true) : 32 ∣ t.size := by
  rcases Bool.or_eq_true_iff.mp h with h1 | h1
  · exact x64IsI32Vec_dvd_32 h1
  · exact x64IsF32Vec_dvd_32 h1

theorem x64IsVecBits_pos {t : Ty} (h : x64IsVecBits t = true) : 0 < t.size := by
  induction t with
  | bool => simp [x64IsVecBits, x64IsI32Vec, x64IsF32Vec] at h
  | bits n =>
    by_cases hn : n = 32
    · subst hn; decide
    · simp [x64IsVecBits, x64IsI32Vec, x64IsF32Vec, hn] at h
  | float f => cases f <;> simp [x64IsVecBits, x64IsI32Vec, x64IsF32Vec] at h; decide
  | pair a b iha _ =>
    rcases Bool.or_eq_true_iff.mp h with h1 | h1 <;>
      simp only [x64IsI32Vec, x64IsF32Vec, Bool.and_eq_true, beq_iff_eq] at h1 <;>
      have := iha (by simp [x64IsVecBits, h1.2]) <;> simp only [Ty.size] <;> omega

theorem x64IsVecBits_pair_elim {a b : Ty} (h : x64IsVecBits (.pair a b) = true) :
    x64IsVecBits a = true ∧ x64IsVecBits b = true := by
  rcases Bool.or_eq_true_iff.mp h with h1 | h1 <;>
    simp only [x64IsI32Vec, x64IsF32Vec, Bool.and_eq_true, beq_iff_eq] at h1 <;>
    obtain ⟨rfl, ha⟩ := h1 <;>
    simp [x64IsVecBits, ha]

theorem toBits_lift1_not {t : Ty} (h : x64IsVecBits t = true) (g : Bool → Bool) (x : Val t) :
    toBits t (lift1 (~~~ ·) g t x) = ~~~(toBits t x) := by
  induction t with
  | bool => simp [x64IsVecBits, x64IsI32Vec, x64IsF32Vec] at h
  | bits _ | float _ => rfl
  | pair a b iha ihb =>
    obtain ⟨ha, hb⟩ := x64IsVecBits_pair_elim h
    simp only [lift1, toBits]
    rw [iha ha x.1, ihb hb x.2]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [Ty.size] at hi
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_not, BitVec.getLsbD_append,
      hi, decide_true, Bool.true_and]
    by_cases hlt : i < a.size <;> simp [hlt, show ¬(i < a.size) → i - a.size < b.size from by omega]

theorem toBits_lift2_bitwise
    (op : ∀ {n}, BitVec n → BitVec n → BitVec n) (opb : Bool → Bool → Bool)
    (hop : ∀ {n} (u v : BitVec n) i, i < n → (op u v).getLsbD i = opb (u.getLsbD i) (v.getLsbD i))
    {t : Ty} (h : x64IsVecBits t = true) (g : Bool → Bool → Bool) (x y : Val t) :
    toBits t (lift2 op g t x y) = op (toBits t x) (toBits t y) := by
  induction t with
  | bool => simp [x64IsVecBits, x64IsI32Vec, x64IsF32Vec] at h
  | bits _ | float _ => rfl
  | pair a b iha ihb =>
    obtain ⟨ha, hb⟩ := x64IsVecBits_pair_elim h
    simp only [lift2, toBits]
    rw [iha ha x.1 y.1, ihb hb x.2 y.2]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_cast, hop _ _ i hi, BitVec.getLsbD_cast, BitVec.getLsbD_cast,
      BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
    by_cases hlt : i < a.size
    · simp only [hlt, ↓reduceIte]; exact hop _ _ i hlt
    · simp only [hlt, ↓reduceIte]
      exact hop _ _ (i - a.size) (by simp only [Ty.size] at hi; omega)

theorem toBits_lift3_ternlog {t : Ty} (h : x64IsVecBits t = true) (imm : BitVec 8)
    (g : Bool → Bool → Bool → Bool) (a b c : Val t) :
    toBits t (lift3 (fun x y z => LeanQbe.T.ternaryLogic x y z imm) g t a b c) =
      BitVec.ternaryLogic (toBits t a) (toBits t b) (toBits t c) imm := by
  induction t with
  | bool => simp [x64IsVecBits, x64IsI32Vec, x64IsF32Vec] at h
  | bits _ | float _ => rfl
  | pair s u ihs ihu =>
    obtain ⟨hs, hu⟩ := x64IsVecBits_pair_elim h
    simp only [lift3, toBits]
    rw [ihs hs a.1 b.1 c.1, ihu hu a.2 b.2 c.2]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_cast, getLsbD_ternaryLogic _ _ _ imm i hi]
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hlt : i < s.size
    · simp only [hlt, ↓reduceIte]; exact getLsbD_ternaryLogic _ _ _ imm i hlt
    · simp only [hlt, ↓reduceIte]
      exact getLsbD_ternaryLogic _ _ _ imm (i - s.size) (by simp only [Ty.size] at hi; omega)

private theorem ternaryLogic_bin2 {w : Nat} (a b : BitVec w) (imm : BitVec 8) (rhs : BitVec w)
    (h : ∀ i, i < w →
      imm.getLsbD (4 * (a.getLsbD i).toNat + 2 * (b.getLsbD i).toNat + (b.getLsbD i).toNat) =
        rhs.getLsbD i) :
    BitVec.ternaryLogic a b b imm = rhs := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_ternaryLogic a b b imm i hi]; exact h i hi

theorem ternaryLogic_0x33 {w : Nat} (a x : BitVec w) :
    BitVec.ternaryLogic a x x 0x33#8 = ~~~x :=
  ternaryLogic_bin2 a x 0x33#8 (~~~x) fun i hi => by
    simp only [BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    cases a.getLsbD i <;> cases x.getLsbD i <;> rfl

theorem ternaryLogic_0xC0 {w : Nat} (a b : BitVec w) :
    BitVec.ternaryLogic a b b 0xC0#8 = a &&& b :=
  ternaryLogic_bin2 a b 0xC0#8 (a &&& b) fun i _ => by
    rw [BitVec.getLsbD_and]; cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem ternaryLogic_0xFC {w : Nat} (a b : BitVec w) :
    BitVec.ternaryLogic a b b 0xFC#8 = a ||| b :=
  ternaryLogic_bin2 a b 0xFC#8 (a ||| b) fun i _ => by
    rw [BitVec.getLsbD_or]; cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem ternaryLogic_0x3C {w : Nat} (a b : BitVec w) :
    BitVec.ternaryLogic a b b 0x3C#8 = a ^^^ b :=
  ternaryLogic_bin2 a b 0x3C#8 (a ^^^ b) fun i _ => by
    rw [BitVec.getLsbD_xor]; cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem ternlog_keep_flip {w : Nat} (x bvB bvC : BitVec w) (imm : BitVec 8) :
    (x &&& (BitVec.ternaryLogic (BitVec.allOnes w) bvB bvC imm ^^^
        BitVec.ternaryLogic 0#w bvB bvC imm)) ^^^ BitVec.ternaryLogic 0#w bvB bvC imm =
      BitVec.ternaryLogic x bvB bvC imm := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and,
    getLsbD_ternaryLogic _ bvB bvC imm i hi,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, hi, decide_true]
  cases x.getLsbD i <;> cases bvB.getLsbD i <;> cases bvC.getLsbD i <;> simp

theorem packedBinOp32_cast {p q : Nat} (f : BitVec 32 → BitVec 32 → BitVec 32)
    (hp : p = q) (a b : BitVec p) :
    BitVec.packedBinOp 32 f (a.cast hp) (b.cast hp) = (BitVec.packedBinOp 32 f a b).cast hp := by
  subst hp; rfl

private theorem take32_append {w1 w2 : Nat} (h : 32 ≤ w1) (u2 : BitVec w2) (u1 : BitVec w1) :
    (u2 ++ u1).take 32 = u1.take 32 :=
  BitVec.eq_of_getLsbD_eq fun i hi => by
    simp [take_eq_setWidth, BitVec.getLsbD_append, show i < 32 from hi, show i < w1 by omega]

private theorem drop32_append {w1 w2 : Nat} (h : 32 ≤ w1) (u2 : BitVec w2) (u1 : BitVec w1) :
    (u2 ++ u1).drop 32 = (u2 ++ u1.drop 32).cast (by omega) :=
  BitVec.eq_of_getLsbD_eq fun i hi => by
    simp only [BitVec.drop, BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hlt : i < w1 - 32
    · simp [hlt, show 32 + i < w1 by omega, show i < w2 + w1 - 32 from hi]
    · simp [hlt, show ¬(32 + i < w1) by omega, show 32 + i - w1 = i - (w1 - 32) by omega,
        show i < w2 + w1 - 32 from hi]

private theorem packedBinOp32_append_mul {w2 : Nat} (f : BitVec 32 → BitVec 32 → BitVec 32)
    (k : Nat) : ∀ {w1 : Nat}, w1 = 32 * k →
    ∀ (u2 v2 : BitVec w2) (u1 v1 : BitVec w1),
      BitVec.packedBinOp 32 f (u2 ++ u1) (v2 ++ v1) =
        BitVec.packedBinOp 32 f u2 v2 ++ BitVec.packedBinOp 32 f u1 v1 := by
  induction k with
  | zero =>
    intro w1 hw1 u2 v2 u1 v1; subst hw1
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hu : u2 ++ u1 = u2 := BitVec.eq_of_getLsbD_eq fun j hj => by simp [show j < w2 from hj]
    have hv : v2 ++ v1 = v2 := BitVec.eq_of_getLsbD_eq fun j hj => by simp [show j < w2 from hj]
    simp only [Nat.mul_zero] at hi
    rw [hu, hv, BitVec.getLsbD_append]; simp [show i < w2 from hi]
  | succ k ih =>
    intro w1 hw1 u2 v2 u1 v1
    have hw32 : 32 ≤ w1 := by omega
    rw [BitVec.packedBinOp.eq_1 32 f (u2 ++ u1) (v2 ++ v1), BitVec.packedBinOp.eq_1 32 f u1 v1]
    simp only [show ¬(32 = 0 ∨ w2 + w1 < 32) by omega, show ¬(32 = 0 ∨ w1 < 32) by omega,
      ↓reduceDIte, take32_append hw32, drop32_append hw32, packedBinOp32_cast,
      ih (by omega) u2 v2 (u1.drop 32) (v1.drop 32)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [show ∀ {m n} (x : BitVec m) (y : BitVec n), x.append y = x ++ y from fun _ _ => rfl,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
    simp only [show i < w2 + w1 from hi, decide_true, Bool.true_and]
    by_cases hi32 : i < 32
    · simp [hi32, show i < w1 by omega, BitVec.getLsbD_append]
    · by_cases hiw1 : i < w1
      · simp [hi32, hiw1, show i - 32 < w1 - 32 by omega, BitVec.getLsbD_append]
      · simp [hi32, hiw1, show ¬(i - 32 < w1 - 32) by omega,
          show i - w1 = i - 32 - (w1 - 32) by omega, BitVec.getLsbD_append]

private theorem packedBinOp32_append {w1 w2 : Nat} (f : BitVec 32 → BitVec 32 → BitVec 32)
    (h1 : 32 ∣ w1) (u2 v2 : BitVec w2) (u1 v1 : BitVec w1) :
    BitVec.packedBinOp 32 f (u2 ++ u1) (v2 ++ v1) =
      BitVec.packedBinOp 32 f u2 v2 ++ BitVec.packedBinOp 32 f u1 v1 :=
  let ⟨k, hk⟩ := h1; packedBinOp32_append_mul f k hk u2 v2 u1 v1

private theorem packedBinOp32_32 (f : BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 32) :
    BitVec.packedBinOp 32 f a b = f a b := by
  rw [BitVec.packedBinOp.eq_1 32 f a b]
  simp only [show ¬(32 = 0 ∨ 32 < 32) from by decide, ↓reduceDIte]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 : a.take 32 = a := by rw [take_eq_setWidth, BitVec.setWidth_eq]
  have h2 : b.take 32 = b := by rw [take_eq_setWidth, BitVec.setWidth_eq]
  rw [h1, h2, show ∀ {m n} (x : BitVec m) (y : BitVec n), x.append y = x ++ y from fun _ _ => rfl,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [show i < 32 from hi]

private theorem ofBits_v4f32_pack (w0 w1 w2 w3 : BitVec 32) :
    ofBits v4f32 ((w3 ++ w2) ++ (w1 ++ w0)) = ((w0, w1), (w2, w3)) := by
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [ofBits, Fmt.width, Ty.size, BitVec.getLsbD_extractLsb']
    rw [BitVec.getLsbD_append]
    grind

theorem sseBinOp_v4f32_spec (op : Float32 → Float32 → Float32)
    (mop : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (hlane : ∀ x y k, floatResultWp .s (mop .binary32 (unpackFloat .s x) (unpackFloat .s y)) k →
      k (sseBinOp op x y))
    (a b : Val v4f32) (P : Val v4f32 → Prop)
    (hwp : liftFloatRel2 mop v4f32 a b P) :
    P (ofBits v4f32 (BitVec.packedBinOp 32 (sseBinOp op) (toBits v4f32 a) (toBits v4f32 b))) := by
  rcases a with ⟨⟨a0, a1⟩, ⟨a2, a3⟩⟩
  rcases b with ⟨⟨b0, b1⟩, ⟨b2, b3⟩⟩
  have hexpr : ofBits v4f32 (BitVec.packedBinOp 32 (sseBinOp op)
      (toBits v4f32 ((a0, a1), (a2, a3))) (toBits v4f32 ((b0, b1), (b2, b3)))) =
      ((sseBinOp op a0 b0, sseBinOp op a1 b1), (sseBinOp op a2 b2, sseBinOp op a3 b3)) := by
    change ofBits v4f32 (BitVec.packedBinOp 32 (sseBinOp op)
      ((a3 ++ a2) ++ (a1 ++ a0)) ((b3 ++ b2) ++ (b1 ++ b0))) = _
    rw [packedBinOp32_append _ ⟨2, rfl⟩, packedBinOp32_append _ ⟨1, rfl⟩,
      packedBinOp32_append _ ⟨1, rfl⟩,
      packedBinOp32_32, packedBinOp32_32, packedBinOp32_32, packedBinOp32_32, ofBits_v4f32_pack]
  dsimp only [liftFloatRel2, Fmt.format] at hwp
  rw [hexpr]
  exact hlane a3 b3 _ (hlane a2 b2 _ (hlane a1 b1 _ (hlane a0 b0 _ hwp)))

theorem toBits_lift2_add {t : Ty} (ht : x64IsI32Vec t = true) (g : Bool → Bool → Bool)
    (a b : Val t) :
    toBits t (lift2 (· + ·) g t a b) = BitVec.packedBinOp 32 (· + ·) (toBits t a) (toBits t b) := by
  induction t with
  | bool | float _ => simp [x64IsI32Vec] at ht
  | bits n =>
    by_cases hn : n = 32
    · subst hn; exact (packedBinOp32_32 (· + ·) a b).symm
    · simp [x64IsI32Vec, hn] at ht
  | pair x y ihx ihy =>
    simp only [x64IsI32Vec, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨rfl, hx⟩ := ht
    have hdvd := x64IsI32Vec_dvd_32 hx
    simp only [lift2, toBits]
    rw [ihx hx a.1 b.1, ihy hx a.2 b.2, ← packedBinOp32_append (· + ·) hdvd]
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp

private theorem mapLanes32_32 (f : BitVec 32 → BitVec 32) (a : BitVec 32) :
    a.mapLanes 32 f = f a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.mapLanes, getLsbD_ofLanes _ (by decide) (by decide) i hi]
  have hl : a.lane 32 0 = a := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [BitVec.lane, show j < 32 from hj]
  simp [show i / 32 = 0 by omega, show i % 32 = i by omega, hl]

private theorem mapLanes32_append {w1 w2 : Nat} (f : BitVec 32 → BitVec 32)
    (h1 : 32 ∣ w1) (h2 : 32 ∣ w2) (u2 : BitVec w2) (u1 : BitVec w1) :
    (u2 ++ u1).mapLanes 32 f = u2.mapLanes 32 f ++ u1.mapLanes 32 f := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  have hdvd : 32 ∣ w2 + w1 := ⟨k2 + k1, by rw [hk1, hk2, Nat.mul_add]⟩
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.mapLanes, getLsbD_ofLanes _ (by decide) hdvd i hi, BitVec.getLsbD_append]
  by_cases hil : i < w1
  · rw [BitVec.mapLanes, getLsbD_ofLanes _ (by decide) ⟨k1, hk1⟩ i hil]
    have hlan : (u2 ++ u1).lane 32 (i / 32) = u1.lane 32 (i / 32) := by
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp [BitVec.lane, BitVec.getLsbD_append, show 32 * (i / 32) + j < w1 by omega]
    simp [hil, hlan]
  · have hdiv : k1 ≤ i / 32 :=
      (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr (by rw [Nat.mul_comm, ← hk1]; omega)
    dsimp only [BitVec.mapLanes]
    rw [getLsbD_ofLanes _ (by decide) ⟨k2, hk2⟩ (i - w1) (by omega),
      show (i - w1) / 32 = i / 32 - k1 by rw [hk1]; omega,
      show (i - w1) % 32 = i % 32 by rw [hk1]; omega]
    have hlan : (u2 ++ u1).lane 32 (i / 32) = u2.lane 32 (i / 32 - k1) := by
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp [BitVec.lane, BitVec.getLsbD_append, show ¬(32 * (i / 32) + j < w1) by rw [hk1]; omega,
        show 32 * (i / 32) + j - w1 = 32 * (i / 32 - k1) + j by rw [hk1]; omega]
    simp [hil, hlan]

private theorem x64UniformI32Splat?_pair {x : Ty} {cb : Val (.pair x x)} {cnt : Nat}
    (h : x64UniformI32Splat? (.pair x x) cb = some cnt) :
    x64UniformI32Splat? x cb.1 = some cnt ∧ x64UniformI32Splat? x cb.2 = some cnt := by
  dsimp only [x64UniformI32Splat?] at h
  cases hx1 : x64UniformI32Splat? x cb.1 with
  | none => simp [hx1] at h
  | some c1 =>
    cases hx2 : x64UniformI32Splat? x cb.2 with
    | none => simp [hx1, hx2] at h
    | some c2 =>
      simp [hx1, hx2] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

theorem toBits_lift2_splat32 (op : ∀ {n}, BitVec n → BitVec n → BitVec n)
    (f : Nat → BitVec 32 → BitVec 32) (cnt : Nat)
    (hstep : ∀ x y : BitVec 32, y.toNat % 32 = cnt → op x y = f cnt x)
    {t : Ty} (ht : x64IsI32Vec t = true) (g : Bool → Bool → Bool) (a cb : Val t)
    (hsplat : x64UniformI32Splat? t cb = some cnt) :
    toBits t (lift2 op g t a cb) = (toBits t a).mapLanes 32 (f cnt) := by
  induction t with
  | bool | float _ => dsimp only [x64IsI32Vec] at ht; cases ht
  | bits n =>
    by_cases hn : n = 32
    · subst hn; simp only [x64UniformI32Splat?, Option.some.injEq] at hsplat
      dsimp only [toBits, lift2]; rw [mapLanes32_32 (f cnt) a]; exact hstep a cb hsplat
    · simp [x64IsI32Vec, hn] at ht
  | pair x y ihx ihy =>
    dsimp only [x64IsI32Vec] at ht; simp only [Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨rfl, hx⟩ := ht
    obtain ⟨hs1, hs2⟩ := x64UniformI32Splat?_pair hsplat
    have hdvd := x64IsI32Vec_dvd_32 hx
    simp only [lift2, toBits]
    rw [ihx hx a.1 cb.1 hs1, ihy hx a.2 cb.2 hs2]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_cast, ← mapLanes32_append (f cnt) hdvd hdvd]; rfl

theorem x64UniformI32Splat?_lt32 {t : Ty} {cb : Val t} {cnt : Nat}
    (ht : x64IsI32Vec t = true) (h : x64UniformI32Splat? t cb = some cnt) : cnt < 32 := by
  induction t with
  | bool | float _ => dsimp only [x64IsI32Vec] at ht; cases ht
  | bits n =>
    by_cases hn : n = 32
    · subst hn; simp only [x64UniformI32Splat?, Option.some.injEq] at h; omega
    · simp [x64IsI32Vec, hn] at ht
  | pair x y ihx _ =>
    dsimp only [x64IsI32Vec] at ht; simp only [Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨rfl, hx⟩ := ht
    exact ihx hx (x64UniformI32Splat?_pair h).1

theorem shuffleDwords_eq {w : Nat} (a : BitVec w) (imm : BitVec 8) :
    LeanQbe.T.shuffleDwords a imm = a.shuffleDwords imm := rfl

theorem shuffleBytes_eq {w : Nat} (a m : BitVec w) :
    LeanQbe.T.shuffleBytes a m = a.shuffleBytes m := rfl

theorem alignBytes_eq {w : Nat} (hi lo : BitVec w) (imm : BitVec 8) :
    LeanQbe.T.alignBytes hi lo imm = hi.alignBytes lo imm := rfl

theorem blendWords_eq {w : Nat} (a b : BitVec w) (imm : BitVec 8) :
    LeanQbe.T.blendWords a b imm = a.blendWords b imm := rfl

end BitVecBridges

/-! ## 3. Single-instruction `Directive.FallsTo` and generic `x64Vop` combinators -/

section OpSpecs

private theorem x64Vpaddd_fallsTo (w : SlotWidth) (vd s1 s2 : RegMm) (s : MachineData) :
    Directive.FallsTo
      (x64Avx w (.vpaddd (.avx (x64AvxRegOf w vd)) (.avx (x64AvxRegOf w s1))
        (.avx (x64AvxRegOf w s2)))) s
      (fun s' => s' = { s with zmms := (s.zmms.set (x64AvxRegOf w vd)
        (BitVec.packedBinOp 32 (· + ·)
          ((s.zmms.get512 s1).setWidth (x64AwOf w).bits)
          ((s.zmms.get512 s2).setWidth (x64AwOf w).bits))) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvx,
    MachineData.setAvxReg, RegZmms.get_eq_setWidth, x64AvxRegOf_base]
  exact hk _ rfl

theorem x64Vprord_fallsTo (w : SlotWidth) (vd vs : RegMm) (cnt : Nat) (hcnt : cnt < 32)
    (s : MachineData) :
    Directive.FallsTo
      (x64Avx w (.vprord (.avx (x64AvxRegOf w vd)) (.avx (x64AvxRegOf w vs))
        (.int64 (Int64.ofNat cnt)))) s
      (fun s' => s' = { s with zmms := (s.zmms.set (x64AvxRegOf w vd)
        (((s.zmms.get512 vs).setWidth (x64AwOf w).bits).mapLanes 32 (·.rotateRight cnt))) }) := by
  intro _ p next jmp P hk
  have himm : ((Int64.ofNat cnt).toBitVec.take 8).toNat % 32 = cnt := by
    rw [Int64_toBitVec_ofNat, take_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 8), Nat.mod_eq_of_lt hcnt]
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvx,
    MachineData.setAvxReg, RegZmms.get_eq_setWidth, x64AvxRegOf_base, ConstExpr.interp, himm]
  exact hk _ rfl

theorem x64Vpsrld_fallsTo (w : SlotWidth) (vd vs : RegMm) (cnt : Nat) (hcnt : cnt < 32)
    (s : MachineData) :
    Directive.FallsTo
      (x64Avx w (.vpsrld (.avx (x64AvxRegOf w vd)) (.avx (x64AvxRegOf w vs))
        (.int64 (Int64.ofNat cnt)))) s
      (fun s' => s' = { s with zmms := (s.zmms.set (x64AvxRegOf w vd)
        (((s.zmms.get512 vs).setWidth (x64AwOf w).bits).mapLanes 32 (· >>> cnt))) }) := by
  intro _ p next jmp P hk
  have himm : ((Int64.ofNat cnt).toBitVec.take 8).toNat = cnt := by
    rw [Int64_toBitVec_ofNat, take_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 64), Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 8)]
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvx,
    MachineData.setAvxReg, RegZmms.get_eq_setWidth, x64AvxRegOf_base, ConstExpr.interp, himm,
    show cnt < 32 from hcnt, ↓reduceIte]
  exact hk _ rfl

theorem x64Pshufb_fallsTo (vd vs : RegMm) (s : MachineData) :
    Directive.FallsTo (x64Avx128 (.pshufb (.avx (.xmm vd)) (.avx (.xmm vs)))) s
      (fun s' => s' = { s with zmms := (s.zmms.setLegacy (.xmm vd)
        (((s.zmms.get512 vd).setWidth 128).shuffleBytes ((s.zmms.get512 vs).setWidth 128))) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy,
    MachineData.setAvxLegacyReg, RegZmms.get_eq_setWidth, AvxReg.base]
  exact hk _ rfl

theorem x64Palignr_fallsTo (vd vs : RegMm) (imm : BitVec 8) (s : MachineData) :
    Directive.FallsTo
      (x64Avx128 (.palignr (.avx (.xmm vd)) (.avx (.xmm vs)) (.int64 (Int64.ofNat imm.toNat)))) s
      (fun s' => s' = { s with zmms := (s.zmms.setLegacy (.xmm vd)
        (BitVec.alignBytes ((s.zmms.get512 vd).setWidth 128)
          ((s.zmms.get512 vs).setWidth 128) imm)) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy,
    MachineData.setAvxLegacyReg, RegZmms.get_eq_setWidth, AvxReg.base, ConstExpr.interp,
    Int64_toBitVec_ofNat, imm8_take imm]
  exact hk _ rfl

theorem x64Pblendw_fallsTo (vd vs : RegMm) (imm : BitVec 8) (s : MachineData) :
    Directive.FallsTo
      (x64Avx128 (.pblendw (.avx (.xmm vd)) (.avx (.xmm vs)) (.int64 (Int64.ofNat imm.toNat)))) s
      (fun s' => s' = { s with zmms := (s.zmms.setLegacy (.xmm vd)
        (((s.zmms.get512 vd).setWidth 128).blendWords
          ((s.zmms.get512 vs).setWidth 128) imm)) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy,
    MachineData.setAvxLegacyReg, RegZmms.get_eq_setWidth, AvxReg.base, ConstExpr.interp,
    Int64_toBitVec_ofNat, imm8_take imm]
  exact hk _ rfl

theorem x64Addps_fallsTo (vd vs : RegMm) (s : MachineData) :
    Directive.FallsTo (x64Avx128 (.addps (.avx (.xmm vd)) (.avx (.xmm vs)))) s
      (fun s' => s' = { s with zmms := (s.zmms.setLegacy (.xmm vd)
        (BitVec.packedBinOp 32 (sseBinOp (· + ·))
          ((s.zmms.get512 vd).setWidth 128) ((s.zmms.get512 vs).setWidth 128))) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy,
    MachineData.setAvxLegacyReg, RegZmms.get_eq_setWidth, AvxReg.base]
  exact hk _ rfl

theorem x64Subps_fallsTo (vd vs : RegMm) (s : MachineData) :
    Directive.FallsTo (x64Avx128 (.subps (.avx (.xmm vd)) (.avx (.xmm vs)))) s
      (fun s' => s' = { s with zmms := (s.zmms.setLegacy (.xmm vd)
        (BitVec.packedBinOp 32 (sseBinOp (· - ·))
          ((s.zmms.get512 vd).setWidth 128) ((s.zmms.get512 vs).setWidth 128))) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy,
    MachineData.setAvxLegacyReg, RegZmms.get_eq_setWidth, AvxReg.base]
  exact hk _ rfl

theorem x64VmovOut64_reg_fallsTo (rd : Reg64) (vs : RegMm) (s : MachineData) :
    Directive.FallsTo (x64Avx128 (.vmovOut .W64 (.reg (q rd)) (.xmm vs))) s
      (fun s' => s' = { s with regs := s.regs.set64 rd ((s.zmms.get512 vs).setWidth 64) }) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, AvxOperation.interp, RegZmms.get_eq_setWidth, AvxReg.base,
    take_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128)]
  exact hk _ rfl

theorem x64Mov32_fallsTo (rd rs : Reg64) (s : MachineData) :
    Directive.FallsTo (ins32 (.mov (.reg (d rd)) (.reg (d rs)))) s (fun s' => s' =
      { s with regs := s.regs.set64 rd (BitVec.setWidth 64 ((s.regs.get64 rs).setWidth 32)) }) := by
  intro _ p next jmp P hk; simp only [t_step_simp]; exact hk _ rfl

private theorem shift32_mask_eq : ((Int64.toBitVec 32).take 8).toNat &&& 63 = 32 := by decide

theorem x64Shl32Imm_fallsTo (r : Reg64) (s : MachineData) :
    Directive.FallsTo (ins (.shl (.reg (q r)) (.imm8 (.int64 32)))) s
      (fun s' => s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
        s'.regs = s.regs.set64 r (s.regs.get64 r <<< (32 : Nat))) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, ConstExpr.interp, ShiftCountExpr.interp, ShiftCountExpr.interpMasked,
    shift32_mask_eq, show (32 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show (32 < 64) by decide, show (32 == 1) = false from rfl, Effects.All]
  intro _ _; exact hk _ ⟨rfl, rfl, rfl⟩

theorem x64Shr32Imm_fallsTo (r : Reg64) (s : MachineData) :
    Directive.FallsTo (ins (.shr (.reg (q r)) (.imm8 (.int64 32)))) s
      (fun s' => s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
        s'.regs = s.regs.set64 r ((s.regs.get64 r).ushiftRight 32)) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, ConstExpr.interp, ShiftCountExpr.interp, ShiftCountExpr.interpMasked,
    shift32_mask_eq, show (32 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show (32 < 64) by decide, show (32 == 1) = false from rfl, Effects.All]
  intro _ _; exact hk _ ⟨rfl, rfl, rfl⟩

theorem x64Or64_fallsTo (rd rs : Reg64) (s : MachineData) :
    Directive.FallsTo (ins (.or (.reg (q rd)) (.reg (q rs)))) s
      (fun s' => s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
        s'.regs = s.regs.set64 rd (s.regs.get64 rd ||| s.regs.get64 rs)) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, Effects.All]; intro _; exact hk _ ⟨rfl, rfl, rfl⟩

theorem regMm_beq_true {a b : RegMm} (h : a = b) : (a == b) = true := by
  subst h; cases a <;> rfl

theorem regMm_eq_of_beq {a b : RegMm} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem regMm_beq_false {a b : RegMm} (h : a ≠ b) : (a == b) = false := by
  cases he : (a == b) with
  | false => rfl
  | true => exact absurd (regMm_eq_of_beq he) h

theorem setWidth_of_eq {m n : Nat} (h : m = n) (x : BitVec m) :
    x.setWidth n = x.cast h := by
  subst h; exact BitVec.setWidth_eq x

theorem setWidth_vecHolds {t : Ty} {w : Nat} (hw : t.size = w)
    (v : BitVec 512) (val : Val t) (hh : VecHolds v t val) :
    v.setWidth w = (toBits t val).cast hw := by
  subst hw; exact hh.2

theorem setWidth_ternaryLogic {m w : Nat} (hle : w ≤ m)
    (a b c : BitVec m) (imm : BitVec 8) :
    (BitVec.ternaryLogic a b c imm).setWidth w =
      BitVec.ternaryLogic (a.setWidth w) (b.setWidth w) (c.setWidth w) imm := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, getLsbD_ternaryLogic _ _ _ imm i (Nat.lt_of_lt_of_le hi hle),
    getLsbD_ternaryLogic _ _ _ imm i hi]
  simp [show (i : Nat) < w from hi, show (i : Nat) < m by omega]

theorem x64IsI32Vec_not_hasFloat {t : Ty} (h : x64IsI32Vec t = true) :
    t.hasFloat = false := by
  induction t with
  | bool => simp [x64IsI32Vec] at h
  | bits _ => rfl
  | float _ => simp [x64IsI32Vec] at h
  | pair a b iha _ =>
    simp only [x64IsI32Vec, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, ha⟩; simp [Ty.hasFloat, iha ha]

@[expose] def VecStepFrame (vd : RegMm) (s s' : MachineData) : Prop :=
  s'.dmem = s.dmem ∧ s'.status = s.status ∧
    (∀ r, r ≠ .r10 → s'.regs.get64 r = s.regs.get64 r) ∧
    (∀ vr, vr ∉ vd :: x64VecScratch → s'.zmms.get512 vr = s.zmms.get512 vr)

theorem VecStepFrame.refl (vd : RegMm) (s : MachineData) : VecStepFrame vd s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem VecStepFrame.trans {vd : RegMm} {s s1 s2 : MachineData}
    (h1 : VecStepFrame vd s s1) (h2 : VecStepFrame vd s1 s2) : VecStepFrame vd s s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr => (h2.2.2.1 r hr).trans (h1.2.2.1 r hr),
    fun v hv => (h2.2.2.2 v hv).trans (h1.2.2.2 v hv)⟩

theorem VecStepFrame.r (s s' : MachineData) {vd : RegMm} (h : VecStepFrame vd s s')
    {vr : RegMm} (hvr : vr ≠ vd) (hvs : vr ∉ x64VecScratch) :
    s'.zmms.get512 vr = s.zmms.get512 vr :=
  h.2.2.2 vr (by simp [hvr, hvs])

@[expose] def pargVecs {t : Ty} : PArg Reg64 RegMm CondCode t → List RegMm
  | .vec v => [v]
  | _ => []

theorem x64Vmov_step [Host] (w : SlotWidth) (d vs vd : RegMm)
    (hd : d ∈ vd :: x64VecScratch) (s : MachineData) :
    @Program.wp _ (x64Vmov w d vs)
      (fun s' => VecStepFrame vd s s' ∧ (∀ vr, vr ≠ d → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
        (s'.zmms.get512 d).setWidth w.bits = (s.zmms.get512 vs).setWidth w.bits)
      (fun _ _ => False) s := by
  refine Program.wp.mono (Directive.FallsTo.wp (x64VmovDqu32_fallsTo w d vs s)) ?_
  rintro s' rfl
  refine ⟨⟨rfl, rfl, fun _ _ => rfl, fun vr hvr =>
    RegZmms.get512_set_avx_of_ne _ w (fun e => hvr (by rw [← e]; exact hd)) _⟩,
    fun vr hvr => RegZmms.get512_set_avx_of_ne _ w hvr.symm _, ?_⟩
  rw [RegZmms.get512_set_avx_same, BitVec.setWidth_setWidth_of_le _ w.bits_le_512,
    BitVec.setWidth_setWidth_of_le _ (x64W_bits_le_awBits w)]

theorem x64Vmovi_step [Host] (tmp : RegMm) (w : SlotWidth) (d vd : RegMm)
    (hd : d ∈ vd :: x64VecScratch) (htmp : tmp ∈ vd :: x64VecScratch) (hne : tmp ≠ d)
    (c : BitVec 512) {p : List Instr} (hv : x64VmoviWithIns tmp w d c = some p)
    (s : MachineData) :
    @Program.wp _ (emitClean p)
      (fun s' => VecStepFrame vd s s' ∧
        (∀ vr, vr ≠ d → vr ≠ tmp → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
        (s'.zmms.get512 d).setWidth w.bits = c.setWidth w.bits)
      (fun _ _ => False) s := by
  have hwp := x64VmoviWith_wp (w := w) (c := c) (code := emitClean p)
    (by simp [x64VmoviWith, emitCleanOpt, hv]) hne s
  refine Program.wp.mono hwp ?_
  rintro s' ⟨hd', hs', hr', hz', hval⟩
  exact ⟨⟨hd', hs', hr', fun vr hvr => hz' vr (fun e => hvr (by simp [e, hd]))
    (fun e => hvr (by simp [e, htmp]))⟩, hz', hval⟩

theorem x64Vmovi_step_cast [Host] (tmp : RegMm) (w : SlotWidth) {t : Ty} (ht : t.size = w.bits)
    (d vd : RegMm) (hd : d ∈ vd :: x64VecScratch) (htmp : tmp ∈ vd :: x64VecScratch)
    (hne : tmp ≠ d) (va : Val t) {p : List Instr}
    (hv : x64VmoviWithIns tmp w d ((toBits t va).setWidth 512) = some p) (s : MachineData) :
    @Program.wp _ (emitClean p)
      (fun s' => VecStepFrame vd s s' ∧
        (∀ vr, vr ≠ d → vr ≠ tmp → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
        (s'.zmms.get512 d).setWidth w.bits = (toBits t va).cast ht)
      (fun _ _ => False) s := by
  refine Program.wp.mono (x64Vmovi_step tmp w d vd hd htmp hne _ hv s) ?_
  rintro s' ⟨hf, hz, hval⟩
  exact ⟨hf, hz, hval.trans (setWidth_512_cast ht _)⟩

theorem x64Vmovi_scratch_step [Host] (tmp d vd : RegMm) (w : SlotWidth) {t : Ty}
    (ht : t.size = w.bits) (hd : d ∈ x64VecScratch) (htmp : tmp ∈ x64VecScratch)
    (hne : tmp ≠ d) (va : Val t) {p : List Instr}
    (hv : x64VmoviWithIns tmp w d ((toBits t va).setWidth 512) = some p) (s : MachineData) :
    @Program.wp _ (emitClean p)
      (fun s' => VecStepFrame vd s s' ∧
        (∀ vr, vr ∉ x64VecScratch → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
        (s'.zmms.get512 d).setWidth w.bits = (toBits t va).cast ht)
      (fun _ _ => False) s := by
  refine Program.wp.mono (x64Vmovi_step_cast tmp w ht d vd
    (List.mem_cons_of_mem _ hd) (List.mem_cons_of_mem _ htmp) hne va hv s) ?_
  rintro s' ⟨hf, hz, hval⟩
  exact ⟨hf, fun vr hvr => hz vr (fun e => hvr (e ▸ hd)) (fun e => hvr (e ▸ htmp)), hval⟩

theorem x64Vmov_self_or_step [Host] (w : SlotWidth) (vd rx : RegMm) (s : MachineData)
    {val : BitVec w.bits} (hx : (s.zmms.get512 rx).setWidth w.bits = val) :
    @Program.wp _ (if rx == vd then [] else x64Vmov w vd rx)
      (fun s' => VecStepFrame vd s s' ∧
        (∀ vr, vr ≠ vd → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
        (s'.zmms.get512 vd).setWidth w.bits = val)
      (fun _ _ => False) s := by
  by_cases hrx : rx = vd
  · subst rx; simp only [regMm_beq_true rfl, ↓reduceIte]
    exact Program.wp_nil ⟨VecStepFrame.refl vd s, fun _ _ => rfl, hx⟩
  · simp only [regMm_beq_false hrx, Bool.false_eq_true, ↓reduceIte]
    refine Program.wp.mono (x64Vmov_step w vd rx vd (by simp) s) ?_
    rintro s' ⟨hf, hz, hv⟩; exact ⟨hf, hz, hv.trans hx⟩

theorem x64FallsTo_widen {h : Host} {k : Nat} {c : List Directive}
    {g1 g2 : List Reg64} {v1 v2 : List RegMm} {f : FlagMask} {s : MachineData}
    {Q R : MachineData → Prop} {post : MachineState → Prop}
    (hg : ∀ r ∈ g1, r ∈ g2) (hv : ∀ vr ∈ v1, vr ∈ v2)
    (hft : x64Mach.FallsTo x64CondReads h k c g1 v1 f s Q post) (hq : ∀ s', Q s' → R s') :
    x64Mach.FallsTo x64CondReads h k c g2 v2 f s R post := by
  intro hc hk
  refine hft hc fun s' hqs hfr => hk s' (hq s' hqs) ⟨fun r hr => hfr.1 r fun hm => hr (hg r hm),
    fun vr hr => hfr.2.1 vr fun hm => hr (hv vr hm), hfr.2.2⟩

theorem vecOpFallsTo {h : Host} {k : Nat} {c : List Directive} {vd : RegMm} {t : Ty}
    {out : Val t} {s : MachineData} {post : MachineState → Prop}
    (ht : t.size ≤ 512)
    (hwp : @Program.wp h c (fun s' => VecStepFrame vd s s' ∧
      (s'.zmms.get512 vd).setWidth t.size = toBits t out) (fun _ _ => False) s) :
    x64Mach.FallsTo x64CondReads h k c ([] ++ x64Scratch) ([vd] ++ x64VecScratch) maskNone s
      (fun s' => (∃ (rvs : Tup Val [t]), rvs = (out, ()) ∧
        TRel (x64Mach.PDstHolds s') (.vec vd, ()) rvs) ∧ x64Mach.mem s' = x64Mach.mem s) post := by
  apply vecFallsTo_of_wp
  refine Program.wp.mono hwp ?_
  rintro s' ⟨⟨hd, hs, hr, hz⟩, hval⟩
  refine ⟨⟨⟨(out, ()), rfl, TRel.cons ⟨ht, hval⟩ .nil⟩, hd⟩,
    vecFrame_upd (fun r hrm => hr r (ne_of_not_mem_x64Scratch (by simpa using hrm)).1)
      (fun vr hvm => hz vr (by simpa using hvm)) (Or.inr hs)⟩

theorem x64EmitUnary_wp [Host] (w : SlotWidth) {t : Ty} (ht : t.size = w.bits)
    {vd : RegMm} {pa : PArg Reg64 RegMm CondCode t} {va : Val t} {c : List Instr} {s : MachineData}
    {emit : RegMm → RegMm → Instr} {upd : BitVec 512 → BitVec w.bits → BitVec 512}
    {res : BitVec w.bits → BitVec t.size}
    (hupd : ∀ old x, (upd old x).setWidth t.size = res x)
    (hemit : ∀ d src st, Directive.FallsTo (.instr (emit d src)) st
      (fun st' => st'.dmem = st.dmem ∧ st'.status = st.status ∧ st'.regs = st.regs ∧
        (∀ vr, vr ≠ d → st'.zmms.get512 vr = st.zmms.get512 vr) ∧
        st'.zmms.get512 d = upd (st.zmms.get512 d) ((st.zmms.get512 src).setWidth w.bits)))
    (hc : x64EmitUnaryIns w t vd pa emit = some c) (hvd : vd ∉ x64VecScratch)
    (hhold : x64Mach.PArgHolds s t pa va) :
    @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
      (s'.zmms.get512 vd).setWidth t.size = res ((toBits t va).cast ht)) (fun _ _ => False) s := by
  have hne14 : .mm14 ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
  have step_unary : ∀ (s1 : MachineData) (src : RegMm),
      (s1.zmms.get512 src).setWidth w.bits = (toBits t va).cast ht →
      @Program.wp _ [.instr (emit vd src)] (fun s' => VecStepFrame vd s1 s' ∧
        (s'.zmms.get512 vd).setWidth t.size = res ((toBits t va).cast ht))
        (fun _ _ => False) s1 := by
    intro s1 src hsrc
    refine Program.wp.mono (Directive.FallsTo.wp (hemit vd src s1)) ?_
    rintro s' ⟨hd, hs, hr, hz, hres⟩
    exact ⟨⟨hd, hs, fun _ _ => hr ▸ rfl, fun v hv => hz v (fun e => hv (e ▸ List.mem_cons_self))⟩,
      by rw [hres, hsrc, hupd]⟩
  cases pa with
  | gpr _ | flag _ => dsimp only [x64EmitUnaryIns] at hc; cases hc
  | vec vr =>
    dsimp only [x64EmitUnaryIns] at hc; simp only [Option.some.injEq] at hc; subst hc
    exact step_unary s vr (setWidth_vecHolds ht _ _ hhold)
  | imm ca =>
    rcases hhold with rfl
    dsimp only [x64EmitUnaryIns] at hc
    cases hv : x64VmoviIns w vd ((toBits t ca).setWidth 512) with
    | none => simp [hv] at hc
    | some p =>
      rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
      simp only [emitClean_append, emitClean_cons, emitClean_nil]
      refine Program.wp.append (x64Vmovi_step_cast .mm14 w ht vd vd (by simp)
        (by simp [x64VecScratch]) hne14 ca hv s) ?_
      rintro s1 ⟨hf1, _, hv1⟩
      refine Program.wp.mono (step_unary s1 vd hv1) ?_
      rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩

theorem x64EmitVpaddd_wp [Host] (w : SlotWidth) (hw : w ≠ .w64) {t : Ty} (ht : t.size = w.bits)
    {vd : RegMm} {pa pb : PArg Reg64 RegMm CondCode t} {va vb : Val t} {c : List Instr}
    {s : MachineData} (hc : x64EmitVpadddIns w t vd pa pb = some c) (hvd : vd ∉ x64VecScratch)
    (hpaV : ∀ vr ∈ pargVecs pa, vr ∉ x64VecScratch) (hpbV : ∀ vr ∈ pargVecs pb, vr ∉ x64VecScratch)
    (hha : x64Mach.PArgHolds s t pa va) (hhb : x64Mach.PArgHolds s t pb vb) :
    @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
      (s'.zmms.get512 vd).setWidth t.size =
        (BitVec.packedBinOp 32 (· + ·)
          ((toBits t va).cast ht) ((toBits t vb).cast ht)).cast ht.symm)
      (fun _ _ => False) s := by
  have hne14d : .mm14 ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
  have hne15d : .mm15 ≠ vd := (ne_of_not_mem_x64VecScratch hvd).2.symm
  have hne145 : (.mm14 : RegMm) ≠ .mm15 := by decide
  have step_padd : ∀ (s1 : MachineData) (r1 r2 : RegMm),
      (s1.zmms.get512 r1).setWidth w.bits = (toBits t va).cast ht →
      (s1.zmms.get512 r2).setWidth w.bits = (toBits t vb).cast ht →
      @Program.wp _ [x64Avx w (.vpaddd (.avx (x64AvxRegOf w vd))
          (.avx (x64AvxRegOf w r1)) (.avx (x64AvxRegOf w r2)))]
        (fun s' => VecStepFrame vd s1 s' ∧ (s'.zmms.get512 vd).setWidth t.size =
          (BitVec.packedBinOp 32 (· + ·)
          ((toBits t va).cast ht) ((toBits t vb).cast ht)).cast ht.symm)
        (fun _ _ => False) s1 := by
    intro s1 r1 r2 ha hb
    refine Program.wp.mono (Directive.FallsTo.wp (x64Vpaddd_fallsTo w vd r1 r2 s1)) ?_
    rintro s' rfl
    refine ⟨⟨rfl, rfl, fun _ _ => rfl, fun vr hvr =>
      RegZmms.get512_set_avx_of_ne _ w (fun e => hvr (by simp [e])) _⟩, ?_⟩
    rw [RegZmms.get512_set_avx_same, BitVec.setWidth_setWidth_of_le _ (ht ▸ w.bits_le_512)]
    cases w with
    | w64 => exact absurd rfl hw
    | w128 | w256 | w512 =>
      dsimp only [x64AwOf, AvxWidth.bits] at *
      rw [setWidth_of_eq ht.symm, ha, hb]
  cases pa with
  | gpr _ | flag _ => dsimp only [x64EmitVpadddIns] at hc; cases hc
  | vec r1 =>
    have hr1 := hpaV r1 (by dsimp only [pargVecs]; exact List.mem_cons_self)
    cases pb with
    | gpr _ | flag _ => dsimp only [x64EmitVpadddIns] at hc; cases hc
    | vec r2 =>
      dsimp only [x64EmitVpadddIns] at hc; simp only [Option.some.injEq] at hc; subst hc
      exact step_padd s r1 r2 (setWidth_vecHolds ht _ _ hha) (setWidth_vecHolds ht _ _ hhb)
    | imm cb =>
      rcases hhb with rfl; dsimp only [x64EmitVpadddIns] at hc
      cases hv : x64VmoviIns w .mm15 ((toBits t cb).setWidth 512) with
      | none => simp [hv] at hc
      | some p =>
        rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
        simp only [emitClean_append, emitClean_cons, emitClean_nil]
        refine Program.wp.append (x64Vmovi_scratch_step .mm14 .mm15 vd w ht
          (by simp [x64VecScratch]) (by simp [x64VecScratch]) hne145 cb hv s) ?_
        rintro s1 ⟨hf1, hz1, hv1⟩
        refine Program.wp.mono (step_padd s1 r1 .mm15
          (by rw [hz1 r1 hr1]; exact setWidth_vecHolds ht _ _ hha) hv1) ?_
        rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩
  | imm ca =>
    rcases hha with rfl
    cases pb with
    | gpr _ | flag _ => dsimp only [x64EmitVpadddIns] at hc; cases hc
    | vec r2 =>
      have hr2 := hpbV r2 (by dsimp only [pargVecs]; exact List.mem_cons_self)
      dsimp only [x64EmitVpadddIns] at hc
      cases hv : x64VmoviIns w .mm15 ((toBits t ca).setWidth 512) with
      | none => simp [hv] at hc
      | some p =>
        rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
        simp only [emitClean_append, emitClean_cons, emitClean_nil]
        refine Program.wp.append (x64Vmovi_scratch_step .mm14 .mm15 vd w ht
          (by simp [x64VecScratch]) (by simp [x64VecScratch]) hne145 ca hv s) ?_
        rintro s1 ⟨hf1, hz1, hv1⟩
        refine Program.wp.mono (step_padd s1 .mm15 r2 hv1
          (by rw [hz1 r2 hr2]; exact setWidth_vecHolds ht _ _ hhb)) ?_
        rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩
    | imm cb =>
      rcases hhb with rfl
      dsimp only [x64EmitVpadddIns, Bind.bind, Option.bind] at hc
      cases hv1 : x64VmoviIns w vd ((toBits t ca).setWidth 512) with
      | none => simp [hv1] at hc
      | some p1 =>
        cases hv2 : x64VmoviIns w .mm15 ((toBits t cb).setWidth 512) with
        | none => simp [hv1, hv2] at hc
        | some p2 =>
          rw [hv1, hv2] at hc; simp only [Option.some.injEq] at hc; subst hc
          simp only [emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
          refine Program.wp.append (x64Vmovi_step_cast .mm14 w ht vd vd (by simp)
            (by simp [x64VecScratch]) hne14d ca hv1 s) ?_
          rintro s1 ⟨hf1, _, hvd1⟩
          refine Program.wp.append (x64Vmovi_scratch_step .mm14 .mm15 vd w ht
            (by simp [x64VecScratch]) (by simp [x64VecScratch]) hne145 cb hv2 s1) ?_
          rintro s2 ⟨hf2, hz2, hv2s⟩
          refine Program.wp.mono (step_padd s2 vd .mm15
            (by rw [hz2 vd hvd, hvd1]) hv2s) ?_
          rintro s' ⟨hf3, hres⟩; exact ⟨(hf1.trans hf2).trans hf3, hres⟩

theorem x64EmitBinInPlace_wp [Host] (w : SlotWidth) {t : Ty} (ht : t.size = w.bits)
    {vd : RegMm} {pa pb : PArg Reg64 RegMm CondCode t} {va vb : Val t} {c : List Instr}
    {s : MachineData} {emit : RegMm → RegMm → Instr}
    {upd : BitVec 512 → BitVec w.bits → BitVec w.bits → BitVec 512}
    {res : BitVec w.bits → BitVec w.bits → BitVec t.size}
    (hupd : ∀ old x y, (upd old x y).setWidth t.size = res x y)
    (hemit : ∀ d src st, Directive.FallsTo (.instr (emit d src)) st
      (fun st' => st'.dmem = st.dmem ∧ st'.status = st.status ∧ st'.regs = st.regs ∧
        (∀ vr, vr ≠ d → st'.zmms.get512 vr = st.zmms.get512 vr) ∧
        st'.zmms.get512 d = upd (st.zmms.get512 d)
          ((st.zmms.get512 d).setWidth w.bits) ((st.zmms.get512 src).setWidth w.bits)))
    (hc : x64EmitBinInPlaceIns w t vd pa pb emit = some c) (hvd : vd ∉ x64VecScratch)
    (hpaV : ∀ vr ∈ pargVecs pa, vr ∉ x64VecScratch) (hpbV : ∀ vr ∈ pargVecs pb, vr ∉ x64VecScratch)
    (hha : x64Mach.PArgHolds s t pa va) (hhb : x64Mach.PArgHolds s t pb vb) :
    @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
      (s'.zmms.get512 vd).setWidth t.size = res ((toBits t va).cast ht) ((toBits t vb).cast ht))
      (fun _ _ => False) s := by
  have hne14d : .mm14 ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
  have hne15d : .mm15 ≠ vd := (ne_of_not_mem_x64VecScratch hvd).2.symm
  have hne145 : (.mm14 : RegMm) ≠ .mm15 := by decide
  have finish : ∀ (s1 : MachineData) (src : RegMm),
      (s1.zmms.get512 vd).setWidth w.bits = (toBits t va).cast ht →
      (s1.zmms.get512 src).setWidth w.bits = (toBits t vb).cast ht →
      @Program.wp _ [.instr (emit vd src)] (fun s' => VecStepFrame vd s1 s' ∧
        (s'.zmms.get512 vd).setWidth t.size = res ((toBits t va).cast ht) ((toBits t vb).cast ht))
        (fun _ _ => False) s1 := by
    intro s1 src hvd1 hsrc1
    refine Program.wp.mono (Directive.FallsTo.wp (hemit vd src s1)) ?_
    rintro s' ⟨hd', hs', hr', hz', hres⟩
    exact ⟨⟨hd', hs', fun _ _ => hr' ▸ rfl,
        fun v hvm => hz' v (fun e => hvm (e ▸ List.mem_cons_self))⟩,
      by rw [hres, hvd1, hsrc1, hupd]⟩
  cases pa with
  | gpr _ | flag _ => dsimp only [x64EmitBinInPlaceIns] at hc; cases hc
  | vec r1 =>
    have hr1 := hpaV r1 (by dsimp only [pargVecs]; exact List.mem_cons_self)
    cases pb with
    | gpr _ | flag _ => dsimp only [x64EmitBinInPlaceIns] at hc; cases hc
    | vec r2 =>
      have hr2 := hpbV r2 (by dsimp only [pargVecs]; exact List.mem_cons_self)
      dsimp only [x64EmitBinInPlaceIns] at hc; simp only [Option.some.injEq] at hc; subst hc
      by_cases h1 : r1 = vd
      · subst h1; simp only [regMm_beq_true rfl, ↓reduceIte, emitClean_cons, emitClean_nil]
        exact finish s r2 (setWidth_vecHolds ht _ _ hha) (setWidth_vecHolds ht _ _ hhb)
      · by_cases h2 : r2 = vd
        · subst h2
          simp only [regMm_beq_false h1, Bool.false_eq_true, ↓reduceIte, regMm_beq_true rfl,
            emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
          refine Program.wp.append (x64Vmov_step w .mm15 r2 r2 (by simp [x64VecScratch]) s) ?_
          rintro s1 ⟨hf1, hz1, h15⟩
          refine Program.wp.append (x64Vmov_step w r2 r1 r2 (by simp) s1) ?_
          rintro s2 ⟨hf2, hz2, hrd2⟩
          refine Program.wp.mono (finish s2 .mm15
            (by rw [hrd2, hz1 r1 (ne_of_not_mem_x64VecScratch hr1).2]
                exact setWidth_vecHolds ht _ _ hha)
            (by rw [hz2 .mm15 hne15d, h15]; exact setWidth_vecHolds ht _ _ hhb)) ?_
          rintro s' ⟨hf3, hres⟩; exact ⟨(hf1.trans hf2).trans hf3, hres⟩
        · simp only [regMm_beq_false h1, regMm_beq_false h2, Bool.false_eq_true, ↓reduceIte,
            emitClean_append, emitClean_cons, emitClean_nil]
          refine Program.wp.append (x64Vmov_step w vd r1 vd (by simp) s) ?_
          rintro s1 ⟨hf1, hz1, hrd1⟩
          refine Program.wp.mono (finish s1 r2
            (by rw [hrd1]; exact setWidth_vecHolds ht _ _ hha)
            (by rw [hz1 r2 h2]; exact setWidth_vecHolds ht _ _ hhb)) ?_
          rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩
    | imm cb =>
      rcases hhb with rfl; dsimp only [x64EmitBinInPlaceIns] at hc
      cases hv : x64VmoviIns w .mm15 ((toBits t cb).setWidth 512) with
      | none => simp [hv] at hc
      | some p =>
        rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
        simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil,
          List.append_assoc]
        refine Program.wp.append (x64Vmovi_scratch_step .mm14 .mm15 vd w ht
          (by simp [x64VecScratch]) (by simp [x64VecScratch]) hne145 cb hv s) ?_
        rintro s1 ⟨hf1, hz1, h15⟩
        refine Program.wp.append (x64Vmov_self_or_step w vd r1 s1 (val := (toBits t va).cast ht)
          (by rw [hz1 r1 hr1]; exact setWidth_vecHolds ht _ _ hha)) ?_
        rintro s2 ⟨hf2, hz2, hrd2⟩
        refine Program.wp.mono (finish s2 .mm15 hrd2 (by rw [hz2 .mm15 hne15d, h15])) ?_
        rintro s' ⟨hf3, hres⟩; exact ⟨(hf1.trans hf2).trans hf3, hres⟩
  | imm ca =>
    rcases hha with rfl
    cases pb with
    | gpr _ | flag _ => dsimp only [x64EmitBinInPlaceIns] at hc; cases hc
    | vec r2 =>
      have hr2 := hpbV r2 (by dsimp only [pargVecs]; exact List.mem_cons_self)
      dsimp only [x64EmitBinInPlaceIns] at hc
      cases hv : x64VmoviIns w vd ((toBits t ca).setWidth 512) with
      | none => simp [hv] at hc
      | some p =>
        rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
        by_cases h2 : r2 = vd
        · subst h2
          simp only [regMm_beq_true rfl, ↓reduceIte, emitClean_append, emitClean_cons,
            emitClean_nil, List.append_assoc]
          refine Program.wp.append (x64Vmov_step w .mm15 r2 r2 (by simp [x64VecScratch]) s) ?_
          rintro s1 ⟨hf1, _, h15⟩
          refine Program.wp.append (x64Vmovi_step_cast .mm14 w ht r2 r2 (by simp)
            (by simp [x64VecScratch]) hne14d ca hv s1) ?_
          rintro s2 ⟨hf2, hz2, hrd2⟩
          refine Program.wp.mono (finish s2 .mm15 hrd2
            (by rw [hz2 .mm15 hne15d hne145.symm, h15]; exact setWidth_vecHolds ht _ _ hhb)) ?_
          rintro s' ⟨hf3, hres⟩; exact ⟨(hf1.trans hf2).trans hf3, hres⟩
        · simp only [regMm_beq_false h2, Bool.false_eq_true, ↓reduceIte, emitClean_append,
            emitClean_cons, emitClean_nil]
          refine Program.wp.append (x64Vmovi_step_cast .mm14 w ht vd vd (by simp)
            (by simp [x64VecScratch]) hne14d ca hv s) ?_
          rintro s1 ⟨hf1, hz1, hrd1⟩
          refine Program.wp.mono (finish s1 r2 hrd1
            (by rw [hz1 r2 h2 (ne_of_not_mem_x64VecScratch hr2).1]
                exact setWidth_vecHolds ht _ _ hhb)) ?_
          rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩
    | imm cb =>
      rcases hhb with rfl; dsimp only [x64EmitBinInPlaceIns, Bind.bind, Option.bind] at hc
      cases hv1 : x64VmoviIns w vd ((toBits t ca).setWidth 512) with
      | none => simp [hv1] at hc
      | some p1 =>
        cases hv2 : x64VmoviIns w .mm15 ((toBits t cb).setWidth 512) with
        | none => simp [hv1, hv2] at hc
        | some p2 =>
          rw [hv1, hv2] at hc; simp only [Option.some.injEq] at hc; subst hc
          simp only [emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
          refine Program.wp.append (x64Vmovi_step_cast .mm14 w ht vd vd (by simp)
            (by simp [x64VecScratch]) hne14d ca hv1 s) ?_
          rintro s1 ⟨hf1, _, hrd1⟩
          refine Program.wp.append (x64Vmovi_scratch_step .mm14 .mm15 vd w ht
            (by simp [x64VecScratch]) (by simp [x64VecScratch]) hne145 cb hv2 s1) ?_
          rintro s2 ⟨hf2, hz2, h15⟩
          refine Program.wp.mono (finish s2 .mm15 (by rw [hz2 vd hvd, hrd1]) h15) ?_
          rintro s' ⟨hf3, hres⟩; exact ⟨(hf1.trans hf2).trans hf3, hres⟩

theorem x64TernlogD_step [Host] (w : SlotWidth) (vd dst s2 s3 : RegMm)
    (hd : dst ∈ vd :: x64VecScratch) (imm : BitVec 8) (st : MachineData) :
    @Program.wp _ [x64TernlogD w dst s2 s3 imm]
      (fun st' => VecStepFrame vd st st' ∧
        (st'.zmms.get512 dst).setWidth w.bits = BitVec.ternaryLogic
          ((st.zmms.get512 dst).setWidth w.bits) ((st.zmms.get512 s2).setWidth w.bits)
          ((st.zmms.get512 s3).setWidth w.bits) imm)
      (fun _ _ => False) st := by
  refine Program.wp.mono (Directive.FallsTo.wp (x64Vpternlogd_fallsTo w dst s2 s3 imm st)) ?_
  rintro s' rfl
  refine ⟨⟨rfl, rfl, fun _ _ => rfl, fun vr hvr =>
    RegZmms.get512_set_avx_of_ne _ w (fun e => hvr (by rw [← e]; exact hd)) _⟩, ?_⟩
  rw [RegZmms.get512_set_avx_same, BitVec.setWidth_setWidth_of_le _ w.bits_le_512,
    setWidth_ternaryLogic (x64W_bits_le_awBits w),
    BitVec.setWidth_setWidth_of_le _ (x64W_bits_le_awBits w),
    BitVec.setWidth_setWidth_of_le _ (x64W_bits_le_awBits w),
    BitVec.setWidth_setWidth_of_le _ (x64W_bits_le_awBits w)]

theorem x64TernlogD_step_ty [Host] (w : SlotWidth) {t : Ty} (ht : t.size = w.bits)
    (vd s2 s3 : RegMm) (a b c : BitVec t.size) (imm : BitVec 8) (st : MachineData)
    (h1 : (st.zmms.get512 vd).setWidth w.bits = a.setWidth w.bits)
    (h2 : (st.zmms.get512 s2).setWidth w.bits = b.setWidth w.bits)
    (h3 : (st.zmms.get512 s3).setWidth w.bits = c.setWidth w.bits) :
    @Program.wp _ [x64TernlogD w vd s2 s3 imm]
      (fun s' => VecStepFrame vd st s' ∧
        (s'.zmms.get512 vd).setWidth t.size = BitVec.ternaryLogic a b c imm)
      (fun _ _ => False) st := by
  refine Program.wp.mono (x64TernlogD_step w vd vd s2 s3 (by simp) imm st) ?_
  rintro s' ⟨hf, hvd'⟩
  refine ⟨hf, ?_⟩
  have h0 : (s'.zmms.get512 vd).setWidth w.bits =
      BitVec.ternaryLogic (a.setWidth w.bits) (b.setWidth w.bits) (c.setWidth w.bits) imm := by
    rw [hvd', h1, h2, h3]
  have h1' := congrArg (BitVec.setWidth t.size) h0
  simpa only [BitVec.setWidth_setWidth_of_le _ (by omega : t.size ≤ w.bits),
    setWidth_ternaryLogic (by omega : t.size ≤ w.bits), BitVec.setWidth_eq] using h1'

theorem x64EmitTernlog1Vec_wp [Host] (w : SlotWidth) {vd rx : RegMm}
    {f0 f1 x : BitVec 512} {c : List Instr} {s : MachineData}
    (hc : x64EmitTernlog1VecIns w vd rx f0 f1 = some c) (hvd : vd ∉ x64VecScratch)
    (hx : (s.zmms.get512 rx).setWidth w.bits = x.setWidth w.bits) :
    @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
      (s'.zmms.get512 vd).setWidth w.bits = ((x &&& (f1 ^^^ f0)) ^^^ f0).setWidth w.bits)
      (fun _ _ => False) s := by
  have hne14d : .mm14 ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
  have hne15d : .mm15 ≠ vd := (ne_of_not_mem_x64VecScratch hvd).2.symm
  have hne145 : (.mm14 : RegMm) ≠ .mm15 := by decide
  dsimp only [x64EmitTernlog1VecIns, Bind.bind, Option.bind] at hc
  cases hk : x64VmoviIns w .mm15 (f1 ^^^ f0) with
  | none => simp [hk] at hc
  | some pk =>
    cases hf : x64VmoviIns w .mm15 f0 with
    | none => simp [hk, hf] at hc
    | some pf =>
      rw [hk, hf] at hc; simp only [Option.some.injEq] at hc; subst hc
      simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil,
        List.append_assoc, List.cons_append, List.nil_append]
      refine Program.wp.append (x64Vmov_self_or_step w vd rx s hx) ?_
      rintro s1 ⟨hf1, hvd1⟩
      refine Program.wp.append (x64Vmovi_step .mm14 w .mm15 vd (by simp [x64VecScratch])
        (by simp [x64VecScratch]) hne145 _ hk s1) ?_
      rintro s2 ⟨hf2, hz2, h15_2⟩
      refine Program.wp.cons (x64TernlogD_step w vd vd .mm15 .mm15 (by simp) 0xC0#8 s2) ?_
      rintro s3 ⟨hf3, hvd3⟩
      refine Program.wp.append (x64Vmovi_step .mm14 w .mm15 vd (by simp [x64VecScratch])
        (by simp [x64VecScratch]) hne145 _ hf s3) ?_
      rintro s4 ⟨hf4, hz4, h15_4⟩
      refine Program.wp.mono (x64TernlogD_step w vd vd .mm15 .mm15 (by simp) 0x3C#8 s4) ?_
      rintro s' ⟨hf5, hvd5⟩
      refine ⟨(((hf1.trans hf2).trans hf3).trans hf4).trans hf5, ?_⟩
      rw [hvd5, ternaryLogic_0x3C, hz4 vd hne15d.symm hne14d.symm, hvd3, ternaryLogic_0xC0,
        hz2 vd hne15d.symm hne14d.symm, hvd1.2, h15_2, h15_4]
      simp only [BitVec.setWidth_and, BitVec.setWidth_xor]

theorem t_ternaryLogic_eq {w : Nat} (a b c : BitVec w) (imm : BitVec 8) :
    ternaryLogic a b c imm = BitVec.ternaryLogic a b c imm := rfl

theorem ternlog_3reg_wp [Host] (w : SlotWidth) {t : Ty} (ht : t.size = w.bits)
    {vd ra sb sc : RegMm} {a b c : BitVec t.size} {imm : BitVec 8} {st : MachineData}
    (hvd : vd ∉ x64VecScratch) (hra : ra ∉ x64VecScratch)
    (hsb15 : sb ≠ .mm15) (hsc15 : sc ≠ .mm15)
    (ha : (st.zmms.get512 ra).setWidth w.bits = a.setWidth w.bits)
    (hb : (st.zmms.get512 sb).setWidth w.bits = b.setWidth w.bits)
    (hc : (st.zmms.get512 sc).setWidth w.bits = c.setWidth w.bits) :
    @Program.wp _ (if ra == vd then [x64TernlogD w vd sb sc imm]
      else if sb != vd && sc != vd then x64Vmov w vd ra ++ [x64TernlogD w vd sb sc imm]
      else x64Vmov w .mm15 vd ++ x64Vmov w vd ra ++
        [x64TernlogD w vd (if sb == vd then .mm15 else sb) (if sc == vd then .mm15 else sc) imm])
      (fun s' => VecStepFrame vd st s' ∧
        (s'.zmms.get512 vd).setWidth t.size = BitVec.ternaryLogic a b c imm)
      (fun _ _ => False) st := by
  have h15d : (.mm15 : RegMm) ≠ vd := (ne_of_not_mem_x64VecScratch hvd).2.symm
  have h15a : ra ≠ .mm15 := (ne_of_not_mem_x64VecScratch hra).2
  by_cases had : ra = vd
  · subst ra; simp only [regMm_beq_true rfl, ↓reduceIte]
    exact x64TernlogD_step_ty w ht vd sb sc a b c imm st ha hb hc
  · simp only [regMm_beq_false had, Bool.false_eq_true, ↓reduceIte]
    by_cases hbc : sb ≠ vd ∧ sc ≠ vd
    · simp only [bne, regMm_beq_false hbc.1, regMm_beq_false hbc.2,
        Bool.not_false, Bool.and_self, ↓reduceIte]
      refine Program.wp.append (x64Vmov_step w vd ra vd (by simp) st) ?_
      rintro s1 ⟨hf1, hz1, hvd1⟩
      refine Program.wp.mono (x64TernlogD_step_ty w ht vd sb sc a b c imm s1
        (hvd1.trans ha) (by rw [hz1 sb hbc.1, hb]) (by rw [hz1 sc hbc.2, hc])) ?_
      rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩
    · have hnot : (sb != vd && sc != vd) = false := by
        cases hbd : (sb == vd) <;> cases hcd : (sc == vd)
        · exact absurd ⟨fun e => by subst e; simp [regMm_beq_true rfl] at hbd,
            fun e => by subst e; simp [regMm_beq_true rfl] at hcd⟩ hbc
        all_goals simp [bne, hbd, hcd]
      simp only [hnot, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
      refine Program.wp.append (x64Vmov_step w .mm15 vd vd (by simp [x64VecScratch]) st) ?_
      rintro s1 ⟨hf1, hz1, h15⟩
      refine Program.wp.append (x64Vmov_step w vd ra vd (by simp) s1) ?_
      rintro s2 ⟨hf2, hz2, hvd2⟩
      have hsrc : ∀ (r : RegMm) (val : BitVec t.size), r ≠ .mm15 →
          (st.zmms.get512 r).setWidth w.bits = val.setWidth w.bits →
          (s2.zmms.get512 (if r == vd then .mm15 else r)).setWidth w.bits =
            val.setWidth w.bits := by
        intro r val hr15 hrval
        by_cases hrd : r = vd
        · subst hrd; simp only [regMm_beq_true rfl, ↓reduceIte, hz2 .mm15 h15d, h15, hrval]
        · simp only [regMm_beq_false hrd, Bool.false_eq_true, ↓reduceIte,
            hz2 r hrd, hz1 r hr15, hrval]
      refine Program.wp.mono (x64TernlogD_step_ty w ht vd _ _ a b c imm s2
        (by rw [hvd2, hz1 ra h15a, ha]) (hsrc sb b hsb15 hb) (hsrc sc c hsc15 hc)) ?_
      rintro s' ⟨hf3, hres⟩; exact ⟨(hf1.trans hf2).trans hf3, hres⟩

theorem pargVecs_sub_2_1 {a b : Ty} (pa : PArg Reg64 RegMm CondCode a)
    (pb : PArg Reg64 RegMm CondCode b) :
    ∀ vr ∈ pargVecs pa,
      vr ∈ tupArgVecs (R := Reg64) (V := RegMm) (C := CondCode)
        (ts := [a, b]) (pa, pb, ()) := by
  cases pa <;> dsimp only [pargVecs, tupArgVecs] <;> simp

theorem pargVecs_sub_2_2 {a b : Ty} (pa : PArg Reg64 RegMm CondCode a)
    (pb : PArg Reg64 RegMm CondCode b) :
    ∀ vr ∈ pargVecs pb,
      vr ∈ tupArgVecs (R := Reg64) (V := RegMm) (C := CondCode)
        (ts := [a, b]) (pa, pb, ()) := by
  cases pa <;> cases pb <;> dsimp only [pargVecs, tupArgVecs] <;> simp

theorem pargVecs_sub_3_1 {a b c : Ty} (pa : PArg Reg64 RegMm CondCode a)
    (pb : PArg Reg64 RegMm CondCode b) (pc : PArg Reg64 RegMm CondCode c) :
    ∀ vr ∈ pargVecs pa,
      vr ∈ tupArgVecs (R := Reg64) (V := RegMm) (C := CondCode)
        (ts := [a, b, c]) (pa, pb, pc, ()) := by
  cases pa <;> dsimp only [pargVecs, tupArgVecs] <;> simp

theorem pargVecs_sub_3_2 {a b c : Ty} (pa : PArg Reg64 RegMm CondCode a)
    (pb : PArg Reg64 RegMm CondCode b) (pc : PArg Reg64 RegMm CondCode c) :
    ∀ vr ∈ pargVecs pb,
      vr ∈ tupArgVecs (R := Reg64) (V := RegMm) (C := CondCode)
        (ts := [a, b, c]) (pa, pb, pc, ()) := by
  cases pa <;> cases pb <;> dsimp only [pargVecs, tupArgVecs] <;> simp

theorem pargVecs_sub_3_3 {a b c : Ty} (pa : PArg Reg64 RegMm CondCode a)
    (pb : PArg Reg64 RegMm CondCode b) (pc : PArg Reg64 RegMm CondCode c) :
    ∀ vr ∈ pargVecs pc,
      vr ∈ tupArgVecs (R := Reg64) (V := RegMm) (C := CondCode)
        (ts := [a, b, c]) (pa, pb, pc, ()) := by
  cases pa <;> cases pb <;> cases pc <;> dsimp only [pargVecs, tupArgVecs] <;> simp

theorem vecOpFallsTo_P {h : Host} {k : Nat} {c : List Directive} {vd : RegMm} {t : Ty}
    {out : Val t} {P : Tup Val [t] → Prop} {s : MachineData} {post : MachineState → Prop}
    (ht : t.size ≤ 512) (hp : P (out, ()))
    (hwp : @Program.wp h c (fun s' => VecStepFrame vd s s' ∧
      (s'.zmms.get512 vd).setWidth t.size = toBits t out) (fun _ _ => False) s) :
    x64Mach.FallsTo x64CondReads h k c ([] ++ x64Scratch) ([vd] ++ x64VecScratch) maskNone s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') (.vec vd, ()) rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post :=
  x64FallsTo_widen (fun _ h => h) (fun _ h => h) (vecOpFallsTo ht hwp)
    (fun _ ⟨⟨rvs, hrv, htr⟩, hm⟩ => ⟨⟨rvs, hrv ▸ hp, htr⟩, hm⟩)

theorem fallsTo_mono {d : Directive} {s : MachineData} {P Q : MachineData → Prop}
    (h : Directive.FallsTo d s P) (hpq : ∀ s', P s' → Q s') : Directive.FallsTo d s Q :=
  fun {_} p next jmp R hk => h p next jmp R fun s' hp => hk s' (hpq s' hp)

end OpSpecs

end LeanQbe.T.Amd64
