module

public import LeanQbe.T.Arm64.IselLemmas2

/-!
# AArch64 Scalar Instruction Selection Proofs — Part 3.0

Weakest-precondition correctness for `armDivRemOp`, `bswap`, `clz`/`cls`/`rbit`/`ctz`, and
`armCmpOp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Arithmetic, bitfield, status-frame, and instruction WP helpers -/

@[reducible] def armDivEval (k : ArmDivK) {n : Nat} (a b : BitVec n) : BitVec n :=
  match k with
  | .udiv => if b == 0 then 0 else a / b
  | .sdiv => if b == 0 then 0 else a.sdiv b
  | .urem => a % b
  | .srem => a.srem b

private theorem sdivDefined_ne_zero {n : Nat} {a b : BitVec n}
    (h : sdivDefined a b = true) : b ≠ 0 := by
  simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne] at h; exact h.1

private theorem setWidth32_ne_zero {n : Nat} (hn : n ≤ 32) {x : BitVec n} (hx : x ≠ 0) :
    x.setWidth 32 ≠ 0#32 := fun h => hx (by
  have := congrArg (BitVec.setWidth n) h
  rwa [BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq, BitVec.setWidth_zero] at this)

private theorem signExtend32_ne_zero {n : Nat} (hn : n ≤ 32) {x : BitVec n} (hx : x ≠ 0) :
    x.signExtend 32 ≠ 0#32 := fun h => hx (by
  have := congrArg (BitVec.setWidth n) h
  rwa [setWidth_signExtend_self hn, BitVec.setWidth_zero] at this)

theorem armStatusScratch_after [Host] {c : List Directive} {s s₂ : MachineData}
    {st : StatusFlags}
    (hwp : _root_.Program.wp c (fun s' => s' = { s₂ with status := st }) (fun _ _ => False) s₂)
    (hd₂ : s₂.dmem = s.dmem) (hfr₂ : armMach.Frame armCondReads s s₂ armScratch [] maskNone) :
    _root_.Program.wp c (fun s' =>
      s'.regs = s₂.regs ∧ s'.status = st ∧ s'.dmem = s.dmem ∧
      armMach.Frame armCondReads s s' armScratch [] maskNZCV) (fun _ _ => False) s₂ :=
  armWp_mono hwp fun s' hs' => by
    subst hs'; refine ⟨rfl, rfl, hd₂, armFrame_nzcv fun r hr => by simpa [get] using hfr₂.1 r hr⟩

private theorem armDivDir_wp [Host] (isSigned : Bool) (w : RegWidth) (t ra rb : XReg)
    (s : MachineData) :
    _root_.Program.wp
      [if isSigned then ins (.SDIV (zr t w) (zr ra w) (zr rb w))
       else ins (.UDIV (zr t w) (zr ra w) (zr rb w))]
      (fun s' => s' = wr s t (BitVec.setWidth 64
        (let a := (s.regs.getXReg ra).toBitVec.setWidth w.bits
         let b := (s.regs.getXReg rb).toBitVec.setWidth w.bits
         if b == 0 then 0#w.bits else if isSigned then a.sdiv b else a / b)))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases isSigned <;> cases w <;>
      (simp only [t_step_simp, Bool.false_eq_true, ↓reduceIte]
       exact hk _ (by simp [RegWidth.bits, MemWidth.bits]))

private theorem armMsubDir_wp [Host] (w : RegWidth) (d t rb ra : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.MSUB (zr d w) (zr t w) (zr rb w) (zr ra w))]
      (fun s' => s' = wr s d (BitVec.setWidth 64
        ((s.regs.getXReg ra).toBitVec.setWidth w.bits -
         (s.regs.getXReg t).toBitVec.setWidth w.bits *
             (s.regs.getXReg rb).toBitVec.setWidth w.bits)))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases w <;> (simp only [t_step_simp]; exact hk _ (by simp [RegWidth.bits, MemWidth.bits]))

theorem armCselDir_wp [Host] (w : RegWidth) (d a b : XReg) (cond : CondCode) (s : MachineData) :
    _root_.Program.wp [ins (.CSEL (zr d w) (zr a w) (zr b w) cond)]
      (fun s' => s' = wr s d ((if cond.interp s.status
        then (s.regs.getXReg a).toBitVec.setWidth w.bits
        else (s.regs.getXReg b).toBitVec.setWidth w.bits).setWidth 64))
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases w <;> (simp only [t_step_simp]; exact hk _ (by simp [RegWidth.bits, MemWidth.bits]))

private theorem getLsbD_ff {w : Nat} (hw : 8 ≤ w) (i : Nat) :
    (BitVec.ofNat w 255).getLsbD i = decide (i < 8) := by
  rw [BitVec.getLsbD_ofNat]
  have h255 : 255 < 2 ^ 8 := by decide
  by_cases hi : i < 8
  · simp only [hi, decide_true, show i < w by omega, Bool.true_and]
    match i with | 0|1|2|3|4|5|6|7 => rfl
  · have hlt :=
      Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le h255 (Nat.pow_le_pow_right (by decide) (by omega : 8 ≤ i)))
    simp [hi, hlt]

private theorem getLsbD_bswapGo {w : Nat} (x : BitVec w) :
    ∀ k i, i < 8 * k → 8 * k ≤ w →
      (bswapBits.go x k).getLsbD i = x.getLsbD (8 * (k - 1 - i / 8) + i % 8)
  | 0, _, hi, _ => by omega
  | k + 1, i, hi, hkw => by
    simp only [bswapBits.go, BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases h8 : i < 8
    · simp only [h8, ↓reduceIte, show i / 8 = 0 by omega, show k + 1 - 1 - 0 = k by omega,
        show i % 8 = i by omega, decide_true, Bool.true_and]
    · simp only [h8, ↓reduceIte]
      rw [getLsbD_bswapGo x k (i - 8) (by omega) (by omega)]
      congr 1; omega

private theorem getLsbD_bswap {w : Nat} (hdvd : w = 16 ∨ w = 32 ∨ w = 64) (x : BitVec w)
    {i : Nat} (hi : i < w) :
    (bswapBits x).getLsbD i = x.getLsbD (8 * (w / 8 - 1 - i / 8) + i % 8) := by
  rcases hdvd with rfl | rfl | rfl <;>
    (simp only [bswapBits, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and];
     exact getLsbD_bswapGo x _ i hi (by decide))

private theorem getLsbD_byteMask {w : Nat} (hw : 8 ≤ w) (q k : Nat) (hk : k < w) :
    (BitVec.ofNat w 255 <<< (8 * q)).getLsbD k = decide (k / 8 = q) := by
  rw [BitVec.getLsbD_shiftLeft, getLsbD_ff hw]
  by_cases h1 : k < 8 * q <;> by_cases h2 : k - 8 * q < 8 <;>
    simp only [hk, h1, h2, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.and_true, Bool.and_false]
  all_goals first
    | (exact (decide_eq_true (by omega)).symm)
    | (exact (decide_eq_false (by omega)).symm)

private theorem mask32_getLsbD {k : Nat} (hk : k < 32) :
    ((0x00FF00FF#32 : BitVec 32).getLsbD k = decide ((k / 8) % 2 = 0)) ∧
    ((0xFF00FF00#32 : BitVec 32).getLsbD k = decide ((k / 8) % 2 = 1)) ∧
    ((0x0000FFFF#32 : BitVec 32).getLsbD k = decide (k < 16)) ∧
    ((0xFFFF0000#32 : BitVec 32).getLsbD k = decide (16 ≤ k)) := by
  have hm1 : (0x00FF00FF#32 : BitVec 32) = BitVec.ofNat 32 255 <<< (8 * 0) |||
    BitVec.ofNat 32 255 <<< (8 * 2) := rfl
  have hm2 : (0xFF00FF00#32 : BitVec 32) = BitVec.ofNat 32 255 <<< (8 * 1) |||
    BitVec.ofNat 32 255 <<< (8 * 3) := rfl
  have hm3 : (0x0000FFFF#32 : BitVec 32) = BitVec.ofNat 32 255 <<< (8 * 0) |||
    BitVec.ofNat 32 255 <<< (8 * 1) := rfl
  have hm4 : (0xFFFF0000#32 : BitVec 32) = BitVec.ofNat 32 255 <<< (8 * 2) |||
    BitVec.ofNat 32 255 <<< (8 * 3) := rfl
  have hlt16 : decide (k < 16) = decide (k / 8 < 2) :=
    if h : k < 16 then by rw [decide_eq_true h, decide_eq_true (by omega)]
    else by rw [decide_eq_false h, decide_eq_false (by omega)]
  have hge16 : decide (16 ≤ k) = decide (2 ≤ k / 8) :=
    if h : 16 ≤ k then by rw [decide_eq_true h, decide_eq_true (by omega)]
    else by rw [decide_eq_false h, decide_eq_false (by omega)]
  rw [hm1, hm2, hm3, hm4, hlt16, hge16]
  simp only [BitVec.getLsbD_or, getLsbD_byteMask (by decide : 8 ≤ 32) _ k hk]
  match hq : k / 8 with
  | 0 | 1 | 2 | 3 => exact ⟨rfl, rfl, rfl, rfl⟩
  | _ + 4 => omega

private theorem bswap1_32 (x : BitVec 32) (j : Nat) (hj : j < 32) :
    (((x &&& 0x00FF00FF#32) <<< 8) ||| ((x &&& 0xFF00FF00#32) >>> 8)).getLsbD j =
      x.getLsbD (if (j / 8) % 2 = 0 then j + 8 else j - 8) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and,
    hj, decide_true, Bool.true_and]
  match hq : j / 8 with
  | 0 =>
    rw [decide_eq_true (by omega : j < 8), (mask32_getLsbD (by omega : 8 + j < 32)).2.1,
      decide_eq_true (by omega : (8 + j) / 8 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 1 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask32_getLsbD (by omega : j - 8 < 32)).1,
      (mask32_getLsbD (by omega : 8 + j < 32)).2.1, decide_eq_true (by omega : (j - 8) / 8 % 2 = 0),
      decide_eq_false (by omega : (8 + j) / 8 % 2 ≠ 1), ite_eq_right_of_eq_false _ _
          (eq_false (by decide))]
    simp
  | 2 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask32_getLsbD (by omega : j - 8 < 32)).1,
      (mask32_getLsbD (by omega : 8 + j < 32)).2.1, decide_eq_false
          (by omega : (j - 8) / 8 % 2 ≠ 0),
      decide_eq_true (by omega : (8 + j) / 8 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 3 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask32_getLsbD (by omega : j - 8 < 32)).1,
      BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ 8 + j),
      decide_eq_true (by omega : (j - 8) / 8 % 2 = 0), ite_eq_right_of_eq_false _ _
          (eq_false (by decide))]
    simp
  | _ + 4 => omega

private theorem bswap2_32 (v : BitVec 32) (j : Nat) (hj : j < 32) :
    (((v &&& 0x0000FFFF#32) <<< 16) ||| ((v &&& 0xFFFF0000#32) >>> 16)).getLsbD j =
      v.getLsbD (if j < 16 then j + 16 else j - 16) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and,
    hj, decide_true, Bool.true_and]
  by_cases h16 : j < 16
  · rw [decide_eq_true h16, (mask32_getLsbD (by omega : 16 + j < 32)).2.2.2,
      decide_eq_true (by omega : 16 ≤ 16 + j), ite_eq_left_of_eq_true _ _ (eq_true h16)]
    simp; congr 1; omega
  · rw [decide_eq_false h16, (mask32_getLsbD (by omega : j - 16 < 32)).2.2.1,
      BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ 16 + j),
      decide_eq_true (by omega : j - 16 < 16), ite_eq_right_of_eq_false _ _ (eq_false h16)]
    simp

private theorem bswap_rev16_32 (x : BitVec 32) :
    ((((x &&& 0x00FF00FF00FF00FF#32) <<< 8) |||
      ((x &&& 0xFF00FF00FF00FF00#32) >>> 8)).setWidth 16) =
      bswapBits (x.setWidth 16) := by
  change (((x &&& 0x00FF00FF#32) <<< 8 ||| (x &&& 0xFF00FF00#32) >>> 8).setWidth 16) = _
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, bswap1_32 x i (by omega), getLsbD_bswap (Or.inl rfl) _ hi,
    BitVec.getLsbD_setWidth,
    decide_eq_true hi, Bool.true_and]
  match hq : i / 8 with
  | 0 =>
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl),
      show 8 * (16 / 8 - 1 - 0) + i % 8 = i + 8 by omega,
      decide_eq_true (by omega : i + 8 < 16), Bool.true_and]
  | 1 =>
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      show 8 * (16 / 8 - 1 - 1) + i % 8 = i - 8 by omega,
      decide_eq_true (by omega : i - 8 < 16), Bool.true_and]
  | _ + 2 => omega

private theorem bswap_rev_32 (x : BitVec 32) :
    let step1 := ((x &&& 0x00FF00FF#32) <<< 8) ||| ((x &&& 0xFF00FF00#32) >>> 8)
    (((step1 &&& 0x0000FFFF#32) <<< 16) ||| ((step1 &&& 0xFFFF0000#32) >>> 16)) = bswapBits x := by
  dsimp only; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [bswap2_32 _ i hi, bswap1_32 _ _ (by split <;> omega),
    getLsbD_bswap (Or.inr (Or.inl rfl)) _ hi]
  match hq : i / 8 with
  | 0 | 1 | 2 | 3 => split <;> (try split) <;> first | omega | (congr 1; omega)
  | _ + 4 => omega

private theorem mask64_getLsbD {k : Nat} (hk : k < 64) :
    ((0x00FF00FF00FF00FF#64 : BitVec 64).getLsbD k = decide ((k / 8) % 2 = 0)) ∧
    ((0xFF00FF00FF00FF00#64 : BitVec 64).getLsbD k = decide ((k / 8) % 2 = 1)) ∧
    ((0x0000FFFF0000FFFF#64 : BitVec 64).getLsbD k = decide ((k / 16) % 2 = 0)) ∧
    ((0xFFFF0000FFFF0000#64 : BitVec 64).getLsbD k = decide ((k / 16) % 2 = 1)) ∧
    ((0x00000000FFFFFFFF#64 : BitVec 64).getLsbD k = decide (k < 32)) ∧
    ((0xFFFFFFFF00000000#64 : BitVec 64).getLsbD k = decide (32 ≤ k)) := by
  have hm1 : (0x00FF00FF00FF00FF#64 : BitVec 64) =
      BitVec.ofNat 64 255 <<< (8 * 0) ||| BitVec.ofNat 64 255 <<< (8 * 2) |||
      BitVec.ofNat 64 255 <<< (8 * 4) ||| BitVec.ofNat 64 255 <<< (8 * 6) := rfl
  have hm2 : (0xFF00FF00FF00FF00#64 : BitVec 64) =
      BitVec.ofNat 64 255 <<< (8 * 1) ||| BitVec.ofNat 64 255 <<< (8 * 3) |||
      BitVec.ofNat 64 255 <<< (8 * 5) ||| BitVec.ofNat 64 255 <<< (8 * 7) := rfl
  have hm3 : (0x0000FFFF0000FFFF#64 : BitVec 64) =
      BitVec.ofNat 64 255 <<< (8 * 0) ||| BitVec.ofNat 64 255 <<< (8 * 1) |||
      BitVec.ofNat 64 255 <<< (8 * 4) ||| BitVec.ofNat 64 255 <<< (8 * 5) := rfl
  have hm4 : (0xFFFF0000FFFF0000#64 : BitVec 64) =
      BitVec.ofNat 64 255 <<< (8 * 2) ||| BitVec.ofNat 64 255 <<< (8 * 3) |||
      BitVec.ofNat 64 255 <<< (8 * 6) ||| BitVec.ofNat 64 255 <<< (8 * 7) := rfl
  have hm5 : (0x00000000FFFFFFFF#64 : BitVec 64) =
      BitVec.ofNat 64 255 <<< (8 * 0) ||| BitVec.ofNat 64 255 <<< (8 * 1) |||
      BitVec.ofNat 64 255 <<< (8 * 2) ||| BitVec.ofNat 64 255 <<< (8 * 3) := rfl
  have hm6 : (0xFFFFFFFF00000000#64 : BitVec 64) =
      BitVec.ofNat 64 255 <<< (8 * 4) ||| BitVec.ofNat 64 255 <<< (8 * 5) |||
      BitVec.ofNat 64 255 <<< (8 * 6) ||| BitVec.ofNat 64 255 <<< (8 * 7) := rfl
  have hlt32 : decide (k < 32) = decide (k / 8 < 4) :=
    if h : k < 32 then by rw [decide_eq_true h, decide_eq_true (by omega)]
    else by rw [decide_eq_false h, decide_eq_false (by omega)]
  have hge32 : decide (32 ≤ k) = decide (4 ≤ k / 8) :=
    if h : 32 ≤ k then by rw [decide_eq_true h, decide_eq_true (by omega)]
    else by rw [decide_eq_false h, decide_eq_false (by omega)]
  rw [hm1, hm2, hm3, hm4, hm5, hm6, hlt32, hge32, show k / 16 = (k / 8) / 2 by omega]
  simp only [BitVec.getLsbD_or, getLsbD_byteMask (by decide : 8 ≤ 64) _ k hk]
  match hq : k / 8 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | _ + 8 => omega

private theorem bswap1_64 (v : BitVec 64) (j : Nat) (hj : j < 64) :
    (((v &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((v &&& 0xFF00FF00FF00FF00#64) >>> 8)).getLsbD j =
      v.getLsbD (if (j / 8) % 2 = 0 then j + 8 else j - 8) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and,
    hj, decide_true, Bool.true_and]
  match hq : j / 8 with
  | 0 =>
    rw [decide_eq_true (by omega : j < 8), (mask64_getLsbD (by omega : 8 + j < 64)).2.1,
      decide_eq_true (by omega : (8 + j) / 8 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 1 | 3 | 5 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask64_getLsbD (by omega : j - 8 < 64)).1,
      (mask64_getLsbD (by omega : 8 + j < 64)).2.1, decide_eq_true (by omega : (j - 8) / 8 % 2 = 0),
      decide_eq_false (by omega : (8 + j) / 8 % 2 ≠ 1), ite_eq_right_of_eq_false _ _
          (eq_false (by decide))]
    simp
  | 2 | 4 | 6 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask64_getLsbD (by omega : j - 8 < 64)).1,
      (mask64_getLsbD (by omega : 8 + j < 64)).2.1, decide_eq_false
          (by omega : (j - 8) / 8 % 2 ≠ 0),
      decide_eq_true (by omega : (8 + j) / 8 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 7 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask64_getLsbD (by omega : j - 8 < 64)).1,
      BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 8 + j),
      decide_eq_true (by omega : (j - 8) / 8 % 2 = 0), ite_eq_right_of_eq_false _ _
          (eq_false (by decide))]
    simp
  | _ + 8 => omega

private theorem bswap2_64 (v : BitVec 64) (j : Nat) (hj : j < 64) :
    (((v &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((v &&& 0xFFFF0000FFFF0000#64) >>> 16)).getLsbD j =
      v.getLsbD (if (j / 16) % 2 = 0 then j + 16 else j - 16) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and,
    hj, decide_true, Bool.true_and]
  match hq : j / 16 with
  | 0 =>
    rw [decide_eq_true (by omega : j < 16), (mask64_getLsbD (by omega : 16 + j < 64)).2.2.2.1,
      decide_eq_true (by omega : (16 + j) / 16 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 1 =>
    rw [decide_eq_false (by omega : ¬(j < 16)), (mask64_getLsbD (by omega : j - 16 < 64)).2.2.1,
      (mask64_getLsbD (by omega : 16 + j < 64)).2.2.2.1, decide_eq_true
          (by omega : (j - 16) / 16 % 2 = 0),
      decide_eq_false (by omega : (16 + j) / 16 % 2 ≠ 1), ite_eq_right_of_eq_false _ _
          (eq_false (by decide))]
    simp
  | 2 =>
    rw [decide_eq_false (by omega : ¬(j < 16)), (mask64_getLsbD (by omega : j - 16 < 64)).2.2.1,
      (mask64_getLsbD (by omega : 16 + j < 64)).2.2.2.1, decide_eq_false
          (by omega : (j - 16) / 16 % 2 ≠ 0),
      decide_eq_true (by omega : (16 + j) / 16 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 3 =>
    rw [decide_eq_false (by omega : ¬(j < 16)), (mask64_getLsbD (by omega : j - 16 < 64)).2.2.1,
      BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 16 + j),
      decide_eq_true (by omega : (j - 16) / 16 % 2 = 0), ite_eq_right_of_eq_false _ _
          (eq_false (by decide))]
    simp
  | _ + 4 => omega

private theorem bswap3_64 (v : BitVec 64) (j : Nat) (hj : j < 64) :
    (((v &&& 0x00000000FFFFFFFF#64) <<< 32) ||| ((v &&& 0xFFFFFFFF00000000#64) >>> 32)).getLsbD j =
      v.getLsbD (if j < 32 then j + 32 else j - 32) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and,
    hj, decide_true, Bool.true_and]
  by_cases h32 : j < 32
  · rw [decide_eq_true h32, (mask64_getLsbD (by omega : 32 + j < 64)).2.2.2.2.2,
      decide_eq_true (by omega : 32 ≤ 32 + j), ite_eq_left_of_eq_true _ _ (eq_true h32)]
    simp; congr 1; omega
  · rw [decide_eq_false h32, (mask64_getLsbD (by omega : j - 32 < 64)).2.2.2.2.1,
      BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 32 + j),
      decide_eq_true (by omega : j - 32 < 32), ite_eq_right_of_eq_false _ _ (eq_false h32)]
    simp

private theorem bswap_rev_64 (x : BitVec 64) :
    let step1 := ((x &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((x &&& 0xFF00FF00FF00FF00#64) >>> 8)
    let step2 :=
        ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
    (((step2 &&& 0x00000000FFFFFFFF#64) <<< 32) |||
      ((step2 &&& 0xFFFFFFFF00000000#64) >>> 32)) = bswapBits x := by
  dsimp only; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [bswap3_64 _ i hi, bswap2_64 _ _ (by split <;> omega),
    bswap1_64 _ _ (by split <;> split <;> omega),
    getLsbD_bswap (Or.inr (Or.inr rfl)) _ hi]
  match hq : i / 8 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    split <;> (try split) <;> (try split) <;> first | omega | (congr 1; omega)
  | _ + 8 => omega


/-! ## 2. Part 3 `armOp` WP theorems (`div/rem`, `bswap`, `clz/cls/rbit/ctz`, `cmp`, `select`, `addc/subb`) -/

private theorem armDiv3264_fallback_wp [Host] (isSigned isRem : Bool) {n : Nat}
    (hn' : n = 32 ∨ n = 64) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb : BitVec n} {ca cb : List Instr} {ra rb : XReg} {s : MachineData}
    (ha : armArgInIns .X16 pa = some (ca, ra)) (hb : armArgInIns .X17 pb = some (cb, rb))
    (hnotii : ∀ ca' cb', pa = .imm ca' → pb = .imm cb' → False)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hrem : isRem = true → vb ≠ 0) :
    let w := armWidthOf n
    let t : XReg := match pb with | .gpr _ => .X17 | .imm _ => .X16
    let divD r : Instr :=
      if isSigned then armIselInsI (.SDIV (zr r w) (zr ra w) (zr rb w))
      else armIselInsI (.UDIV (zr r w) (zr ra w) (zr rb w))
    let code : List Instr :=
      if isRem then ca ++ cb ++ [divD t, armIselInsI (.MSUB (zr d w) (zr t w) (zr rb w) (zr ra w))]
      else ca ++ cb ++ [divD d]
    let target := if isRem then (if isSigned then va.srem vb else va % vb)
                  else (if vb == 0 then 0 else if isSigned then va.sdiv vb else va / vb)
    _root_.Program.wp (emitClean code) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n target ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ => False) s := by
  intro w t divD code target
  have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl <;> decide
  cases isRem
  · dsimp only [code]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
    rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
    dsimp only [target]
    rcases hn' with rfl | rfl
    · rw [show [Kraken.Directive.instr (divD d)] =
          [if isSigned then ins (.SDIV (zr d .W32) (zr ra .W32) (zr rb .W32))
           else ins (.UDIV (zr d .W32) (zr ra .W32) (zr rb .W32))] by cases isSigned <;> rfl]
      refine armWrDst_after_scratch hn64 d (armDivDir_wp isSigned .W32 d ra rb s₂) hd₂ hfr₂ ?_ ?_
      · dsimp only [RegWidth.bits, MemWidth.bits] at hra hrb ⊢
        rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), hra, hrb]
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_eq]; rfl
      · intro _; dsimp only [RegWidth.bits, MemWidth.bits] at hra hrb ⊢
        rw [hra, hrb]; rfl
    · rw [show [Kraken.Directive.instr (divD d)] =
          [if isSigned then ins (.SDIV (zr d .W64) (zr ra .W64) (zr rb .W64))
           else ins (.UDIV (zr d .W64) (zr ra .W64) (zr rb .W64))] by cases isSigned <;> rfl]
      refine armWrDst_after_scratch hn64 d (armDivDir_wp isSigned .W64 d ra rb s₂) hd₂ hfr₂ ?_
        (fun h => by cases h)
      dsimp only [RegWidth.bits, MemWidth.bits] at hra hrb ⊢
      simp only [BitVec.setWidth_eq] at hra hrb ⊢
      rw [hra, hrb]
      simp only [Bool.false_eq_true, ↓reduceIte]; rfl
  · have hb0 := hrem rfl
    have htSpec : XRegOrSp.reg t ∈ armScratch ∧ t ≠ ra ∧ t ≠ rb := by
      cases pb with
      | vec vr => exact vr.elim
      | gpr r => cases r with
        | SP => simp [armArgInIns] at hb
        | reg xb =>
          dsimp only [t]
          simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at hb; rcases hb with ⟨rfl, rfl⟩
          have hxb : xb ≠ .X17 :=
              (xreg_ne_scratch_of_not_mem (hgb (.reg xb) (by simp [PArg.gprs]))).2
          have hra17 : ra ≠ .X17 := by
            cases pa with
            | vec vr => exact vr.elim
            | imm _ => simp [armArgInIns] at ha; rcases ha with ⟨rfl, rfl⟩; decide
            | gpr r' => cases r' with | SP => simp [armArgInIns] at ha | reg xa =>
              simp [armArgInIns] at ha; rcases ha with ⟨rfl, rfl⟩
              exact (xreg_ne_scratch_of_not_mem (hga (.reg xa) (by simp [PArg.gprs]))).2
          exact ⟨x17_mem_scratch, hra17.symm, hxb.symm⟩
      | imm cb' =>
        dsimp only [t]
        simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at hb; rcases hb with ⟨rfl, rfl⟩
        have hra16 : ra ≠ .X16 := by
          cases pa with
          | vec vr => exact vr.elim
          | imm ca' => exact absurd rfl (hnotii ca' cb' rfl)
          | gpr r' => cases r' with | SP => simp [armArgInIns] at ha | reg xa =>
            simp [armArgInIns] at ha; rcases ha with ⟨rfl, rfl⟩
            exact (xreg_ne_scratch_of_not_mem (hga (.reg xa) (by simp [PArg.gprs]))).1
        exact ⟨x16_mem_scratch, hra16.symm, by decide⟩
    obtain ⟨htmem, htra, htrb⟩ := htSpec
    dsimp only [code]; simp only [↓reduceIte, List.append_assoc]
    rw [← List.append_assoc ca cb, emitClean_append]
    refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
    rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
    simp only [emitClean_cons, emitClean_nil]
    rcases hn' with rfl | rfl
    · rw [show [Kraken.Directive.instr (divD t), Kraken.Directive.instr
            (armIselInsI (.MSUB (zr d w) (zr t w) (zr rb w) (zr ra w)))] =
          [if isSigned then ins (.SDIV (zr t .W32) (zr ra .W32) (zr rb .W32))
           else ins (.UDIV (zr t .W32) (zr ra .W32) (zr rb .W32)),
           ins (.MSUB (zr d .W32) (zr t .W32) (zr rb .W32) (zr ra .W32))] by
        cases isSigned <;> rfl]
      refine armScratch_cons htmem hd₂ hfr₂
          (armDivDir_wp isSigned .W32 t ra rb s₂) fun s₃ hs₃ hd₃ hfr₃ => ?_
      refine armWrDst_after_scratch hn64 d (armMsubDir_wp .W32 d t rb ra s₃) hd₃ hfr₃ ?_ ?_
      · rw [hs₃]; simp only [RegWidth.bits, MemWidth.bits, target,
          Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ htra, Reg64s.getXReg_setXReg_of_ne _ _ _ _ htrb]
        rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
          hra, hrb, beq_false_of_ne hb0]
        cases isSigned
        · exact (umod_eq_sub _ _).symm
        · exact (srem_eq_sub _ _).symm
      · intro _; rw [hs₃]; simp only [RegWidth.bits, MemWidth.bits, target,
          Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ htra, Reg64s.getXReg_setXReg_of_ne _ _ _ _ htrb]
        rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), hra, hrb, beq_false_of_ne hb0]
        cases isSigned
        · exact congrArg (BitVec.setWidth 64) (umod_eq_sub _ _).symm
        · exact congrArg (BitVec.setWidth 64) (srem_eq_sub _ _).symm
    · rw [show [Kraken.Directive.instr (divD t), Kraken.Directive.instr
            (armIselInsI (.MSUB (zr d w) (zr t w) (zr rb w) (zr ra w)))] =
          [if isSigned then ins (.SDIV (zr t .W64) (zr ra .W64) (zr rb .W64))
           else ins (.UDIV (zr t .W64) (zr ra .W64) (zr rb .W64)),
           ins (.MSUB (zr d .W64) (zr t .W64) (zr rb .W64) (zr ra .W64))] by
        cases isSigned <;> rfl]
      refine armScratch_cons htmem hd₂ hfr₂
          (armDivDir_wp isSigned .W64 t ra rb s₂) fun s₃ hs₃ hd₃ hfr₃ => ?_
      refine armWrDst_after_scratch hn64 d (armMsubDir_wp .W64 d t rb ra s₃) hd₃ hfr₃ ?_
        (fun h => by cases h)
      rw [hs₃]; simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq, target] at hra hrb ⊢
      simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ htra, Reg64s.getXReg_setXReg_of_ne _ _ _ _ htrb]
      rw [hra, hrb, beq_false_of_ne hb0]
      cases isSigned
      · exact (umod_eq_sub _ _).symm
      · exact (srem_eq_sub _ _).symm

private theorem armDiv816_wp [Host] (isSigned isRem : Bool) {n : Nat}
    (hn' : n = 8 ∨ n = 16) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb : BitVec n} {ca cb : List Instr} {ra rb : XReg} {s : MachineData}
    (hd : XRegOrSp.reg d ∉ armScratch)
    (ha : armArgInIns .X16 pa = some (ca, ra)) (hb : armArgInIns .X17 pb = some (cb, rb))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hrem : isRem = true → vb ≠ 0) :
    let divD : Instr :=
      if isSigned then armIselInsI (.SDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
      else armIselInsI (.UDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
    let post : List Instr :=
      if isRem then
        [divD, armIselInsI (.MSUB (zr d .W32) (zr d .W32) (zr .X17 .W32) (zr .X16 .W32))]
      else [divD]
    let target := if isRem then (if isSigned then va.srem vb else va % vb)
                  else (if vb == 0 then 0 else if isSigned then va.sdiv vb else va / vb)
    _root_.Program.wp (emitClean (ca ++ cb ++
        [armExt32I isSigned n .X16 ra, armExt32I isSigned n .X17 rb] ++ post))
      (fun s' => GprHoldsZ (armMach.getGpr s' (.reg d)) n target ∧
        armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone)
      (fun _ _ => False) s := by
  intro divD post target
  have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
  have hnw32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
  have hn64 : n ≤ 64 := Nat.le_trans hnw32 (by decide)
  have hn32 : n ≠ 32 := by rcases hn' with rfl | rfl <;> decide
  have ⟨hd16, hd17⟩ := xreg_ne_scratch_of_not_mem hd
  simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
  refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
  rintro s₂ ⟨hra, hrb, _, hneB, hd₂, _, hfr₂⟩
  simp only [emitClean_append, emitClean_cons, emitClean_nil]
  refine armScratch_cons x16_mem_scratch hd₂ hfr₂
      (armExt32_wp isSigned hn0 hnw32 .X16 ra s₂ va hra) fun s₂' hs₂' hd₂' hfr₂' => ?_
  have hrb' : (s₂'.regs.getXReg rb).toBitVec.setWidth n = vb := by
    rw [hs₂', Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm]; exact hrb
  refine armScratch_cons x17_mem_scratch hd₂' hfr₂'
      (armExt32_wp isSigned hn0 hnw32 .X17 rb s₂' vb hrb') fun s₃ hs₃ hd₃ hfr₃ => ?_
  have h16₃ :
      (s₃.regs.getXReg
          .X16).toBitVec.setWidth 32 = if isSigned then va.signExtend 32 else va.setWidth 32 := by
    rw [hs₃, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide), hs₂']
    simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have h17₃ :
      (s₃.regs.getXReg
          .X17).toBitVec.setWidth 32 = if isSigned then vb.signExtend 32 else vb.setWidth 32 := by
    rw [hs₃]; simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  cases isRem
  · rw [show (emitClean post : List Directive) =
        [if isSigned then ins (.SDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
         else ins (.UDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))] by
      cases isSigned <;> rfl]
    refine armWrDst_after_scratch hn64 d (armDivDir_wp isSigned .W32 d .X16 .X17 s₃) hd₃ hfr₃ ?_
      (fun h => absurd h hn32)
    simp only [RegWidth.bits, MemWidth.bits, h16₃, h17₃, BitVec.setWidth_setWidth_of_le _ hn64,
      target]
    by_cases hvb0 : vb = 0
    · subst hvb0
      cases isSigned <;> (rcases hn' with rfl | rfl <;> rfl)
    · have hne32 : (if isSigned then vb.signExtend 32 else vb.setWidth 32) ≠ 0 := by
        cases isSigned; exact setWidth32_ne_zero hnw32 hvb0; exact signExtend32_ne_zero hnw32 hvb0
      rw [beq_false_of_ne hvb0]
      cases isSigned
      · simp only [Bool.false_eq_true, ↓reduceIte] at hne32 ⊢
        rw [beq_false_of_ne hne32]; exact udiv_subword_32 hn' va vb
      · simp only [↓reduceIte] at hne32 ⊢
        rw [beq_false_of_ne hne32]; exact sdiv_subword_32 hn' va vb
  · have hvb0 := hrem rfl
    have hne32 : (if isSigned then vb.signExtend 32 else vb.setWidth 32) ≠ 0 := by
      cases isSigned; exact setWidth32_ne_zero hnw32 hvb0; exact signExtend32_ne_zero hnw32 hvb0
    rw [show (emitClean post : List Directive) =
        [if isSigned then ins (.SDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
         else ins (.UDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32)),
         ins (.MSUB (zr d .W32) (zr d .W32) (zr .X17 .W32) (zr .X16 .W32))] by
      cases isSigned <;> rfl]
    refine armWp_cons (armDivDir_wp isSigned .W32 d .X16 .X17 s₃) fun s₄ hs₄ => ?_
    refine armWp_mono (armMsubDir_wp .W32 d d .X17 .X16 s₄) fun s₅ hs₅ => ?_
    have hs₅' :
        s₅ = wr s₃ d (BitVec.setWidth 64 ((if isSigned then va.signExtend 32 else va.setWidth 32) -
        (if isSigned then (va.signExtend 32).sdiv (vb.signExtend 32) else va.setWidth 32 /
            vb.setWidth 32) *
        (if isSigned then vb.signExtend 32 else vb.setWidth 32))) := by
      rw [hs₅, hs₄]; simp only [wr_wr_same, RegWidth.bits, MemWidth.bits,
        Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, BitVec.setWidth_setWidth_of_le _
            (by decide : 32 ≤ 64),
        Reg64s.getXReg_setXReg_of_ne s₃.regs d .X16 _ hd16, Reg64s.getXReg_setXReg_of_ne s₃.regs d
        .X17 _ hd17,
        h16₃, h17₃]
      cases isSigned
      · simp only [Bool.false_eq_true, ↓reduceIte] at hne32 ⊢; rw [beq_false_of_ne hne32]
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_eq]
      · simp only [↓reduceIte] at hne32 ⊢; rw [beq_false_of_ne hne32]
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_eq]
    rw [hs₅']
    refine ⟨⟨⟨hn64, ?_⟩, fun h => absurd h hn32⟩, hd₃,
      armFrame_scratch_wr hfr₃ (frame_wr d _ List.mem_cons_self maskNone)⟩
    simp only [get_wr_same, BitVec.setWidth_setWidth_of_le _ hn64, target]
    cases isSigned
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← umod_eq_sub]; exact urem_subword_32 hn' va vb
    · simp only [↓reduceIte]; rw [← srem_eq_sub]; exact srem_subword_32 hn' va vb

private theorem armDivRemOp_runK [Host] (k : ArmDivK) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (isSigned isRem : Bool)
    (hk : (do
      if ![8, 16, 32, 64].contains n then none
      else if n == 32 || n == 64 then
        let w := armWidthOf n
        match pa, pb with
        | .imm ca, .imm cb =>
          let res := if isRem then (if isSigned then ca.srem cb else ca % cb)
                     else if cb == 0 then 0 else if isSigned then ca.sdiv cb else ca / cb
          some (armMovImmI d (res.setWidth 64), maskNone)
        | _, _ =>
          let (ca, ra) ← armArgInIns .X16 pa; let (cb, rb) ← armArgInIns .X17 pb
          if isRem then
            let t : XReg := match pb with | .gpr _ => .X17 | .imm _ => .X16
            let divD :=
              if isSigned then armIselInsI (.SDIV (zr t w) (zr ra w) (zr rb w))
              else armIselInsI (.UDIV (zr t w) (zr ra w) (zr rb w))
            some (ca ++ cb ++
              [divD, armIselInsI (.MSUB (zr d w) (zr t w) (zr rb w) (zr ra w))], maskNone)
          else
            let divD :=
              if isSigned then armIselInsI (.SDIV (zr d w) (zr ra w) (zr rb w))
              else armIselInsI (.UDIV (zr d w) (zr ra w) (zr rb w))
            some (ca ++ cb ++ [divD], maskNone)
      else
        let (ca, ra) ← armArgInIns .X16 pa; let (cb, rb) ← armArgInIns .X17 pb
        let prep := [armExt32I isSigned n .X16 ra, armExt32I isSigned n .X17 rb]
        let divD :=
          if isSigned then armIselInsI (.SDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
          else armIselInsI (.UDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
        if isRem then
          some (ca ++ cb ++ prep ++
            [divD, armIselInsI (.MSUB (zr d .W32) (zr d .W32) (zr .X17 .W32) (zr .X16 .W32))],
            maskNone)
        else some (ca ++ cb ++ prep ++ [divD], maskNone)) = some (c, clob))
    (hd : XRegOrSp.reg d ∉ armScratch)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hrem' : isRem = true → vb ≠ 0)
    (heval : (if isRem then (if isSigned then va.srem vb else va % vb)
              else (if vb == 0 then 0 else if isSigned then va.sdiv vb else va /
                  vb)) = armDivEval k va vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (armDivEval k va vb) ∧
      armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only at hk; split at hk
  · simp at hk
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    split at hk
    · rename_i hn3264
      have hn' : n = 32 ∨ n = 64 := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
      cases pa with
      | vec vr => exact vr.elim
      | imm ca => cases pb with
        | vec vr => exact vr.elim
        | imm cb =>
          dsimp only at hk; rcases Option.some.inj hk with ⟨rfl, rfl⟩
          have hca : ca = va := hpa; have hcb : cb = vb := hpb; subst hca; subst hcb
          refine armWp_mono (armImmPool_wp hn64 d s _) fun s' ⟨hg, hm, hfr⟩ => ⟨?_, hm, hfr⟩
          rwa [heval] at hg
        | gpr _ =>
          simp only [bind, Option.bind_eq_some_iff] at hk
          rcases hk with ⟨⟨ca', ra⟩, ha, ⟨cb', rb⟩, hb, htail⟩
          cases isRem <;> simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq,
            Prod.mk.injEq] at htail <;>
            rcases htail with ⟨rfl, rfl⟩ <;>
            exact armWp_mono (armDiv3264_fallback_wp isSigned _ hn' _ _ d ha hb (fun _ _ _ h =>
              by cases h) hga hgb hpa hpb hrem')
              fun s' ⟨hg, hm, hfr⟩ => ⟨heval ▸ hg, hm, hfr⟩
      | gpr _ => cases pb with
        | vec vr => exact vr.elim
        | gpr _ | imm _ =>
          simp only [bind, Option.bind_eq_some_iff] at hk
          rcases hk with ⟨⟨ca', ra⟩, ha, ⟨cb', rb⟩, hb, htail⟩
          cases isRem <;> simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq,
            Prod.mk.injEq] at htail <;>
            rcases htail with ⟨rfl, rfl⟩ <;>
            exact armWp_mono (armDiv3264_fallback_wp isSigned _ hn' _ _ d ha hb (fun _ _ h _ =>
              by cases h) hga hgb hpa hpb hrem')
              fun s' ⟨hg, hm, hfr⟩ => ⟨heval ▸ hg, hm, hfr⟩
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      simp only [bind, Option.bind_eq_some_iff] at hk
      rcases hk with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, htail⟩
      cases isRem <;> simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq,
        Prod.mk.injEq] at htail <;>
        rcases htail with ⟨rfl, rfl⟩ <;>
        exact armWp_mono (armDiv816_wp isSigned _ hn' pa pb d hd ha hb hga hgb hpa hpb hrem')
          fun s' ⟨hg, hm, hfr⟩ => ⟨heval ▸ hg, hm, hfr⟩

theorem armDivRemOp_wp [Host] (k : ArmDivK) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armDivRemOpIns k n pa pb d = some (c, clob)) (hd : XRegOrSp.reg d ∉ armScratch)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hrem : k = .urem ∨ k = .srem → vb ≠ 0) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (armDivEval k va vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  cases k
  · dsimp only [armDivRemOpIns] at hc
    exact armDivRemOp_runK .udiv pa pb d false false hc hd hga hgb hpa hpb (fun h => by cases h) rfl
  · dsimp only [armDivRemOpIns] at hc
    exact armDivRemOp_runK .sdiv pa pb d true false hc hd hga hgb hpa hpb (fun h => by cases h) rfl
  · dsimp only [armDivRemOpIns] at hc
    exact armDivRemOp_runK .urem pa pb d false true hc hd hga hgb hpa hpb
      (fun _ => hrem (Or.inl rfl)) rfl
  · dsimp only [armDivRemOpIns] at hc
    exact armDivRemOp_runK .srem pa pb d true true hc hd hga hgb hpa hpb
      (fun _ => hrem (Or.inr rfl)) rfl

theorem armBswap_wp [Host] {n : Nat} (pa : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : (do
      if ![16, 32, 64].contains n then none
      else
        let (ca, ra) ← armArgInIns .X16 pa
        let dir := if n == 16 then armIselInsI (.REV16 (zr d .W32) (zr ra .W32))
                   else if n == 32 then armIselInsI (.REV (zr d .W32) (zr ra .W32))
                   else armIselInsI (.REV (zr d .W64) (zr ra .W64))
        some (ca ++ [dir], maskNone)) = some (c, clob))
    (hpa : armMach.PArgHolds s (.bits n) pa va) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (bswapBits va) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    have hn' : n = 16 ∨ n = 32 ∨ n = 64 := by simpa using hn
    have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl | rfl <;> decide
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨⟨ca, ra⟩, ha, rfl, rfl⟩
    rw [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append (armArgIn_wp hn64 ha hpa) ?_
    rintro s₁ ⟨hra, hd₁, _, hfr₁⟩
    have hfr₁' : armMach.Frame armCondReads s s₁ armScratch [] maskNone :=
      hfr₁.weaken (fun x hr =>
        by simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hr; subst hr; exact x16_mem_scratch)
        (fun v => v.elim) rfl
    rcases hn' with rfl | rfl | rfl
    · simp only [show (16 == 16) = true from rfl, ↓reduceIte]
      refine armWrDst_after_scratch (by decide) d (armDirFallsTo_wp (Q :=
          fun s' => s' = wr s₁ d (BitVec.setWidth 64
        ((((s₁.regs.getXReg ra).toBitVec.setWidth 32 &&& 0x00FF00FF00FF00FF#32) <<< 8) |||
         (((s₁.regs.getXReg ra).toBitVec.setWidth 32 &&& 0xFF00FF00FF00FF00#32) >>> 8))))
           fun {_} p next jmp Q hk => by
        simp only [t_step_simp]; exact hk _ rfl) hd₁ hfr₁' ?_ (fun h => by cases h)
      rw [BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64), bswap_rev16_32,
        BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 32), hra]
    · simp only [show (32 == 16) = false from rfl, show (32 == 32) = true from rfl,
        Bool.false_eq_true, ↓reduceIte]
      refine armWrDst_after_scratch (by decide) d (armDirFallsTo_wp (Q :=
          fun s' => s' = wr s₁ d (BitVec.setWidth 64 (bswapBits va)))
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp] at hra ⊢; rw [hra, bswap_rev_32]; exact hk _ rfl) hd₁ hfr₁'
        (by rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq])
        (fun _ => rfl)
    · simp only [show (64 == 16) = false from rfl, show (64 == 32) = false from rfl,
        Bool.false_eq_true, ↓reduceIte]
      refine armWrDst_after_scratch (by decide) d (armDirFallsTo_wp (Q :=
          fun s' => s' = wr s₁ d (bswapBits va))
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp, BitVec.setWidth_eq] at hra ⊢
          rw [hra, bswap_rev_64]; exact hk _ rfl)
        hd₁ hfr₁' (BitVec.setWidth_eq _) (fun h => by cases h)

inductive ArmBitK | clz | cls | rbit | ctz

@[reducible] def armBitCode (k : ArmBitK) (w : RegWidth) (d ra : XReg) : List Directive :=
  match k with
  | .clz => [ins (.CLZ (zr d w) (zr ra w))]
  | .cls => [ins (.CLS (zr d w) (zr ra w))]
  | .rbit => [ins (.RBIT (zr d w) (zr ra w))]
  | .ctz => [ins (.RBIT (zr d w) (zr ra w)), ins (.CLZ (zr d w) (zr d w))]

@[reducible] def armBitCodeI (k : ArmBitK) (w : RegWidth) (d ra : XReg) : List Instr :=
  match k with
  | .clz => [armIselInsI (.CLZ (zr d w) (zr ra w))]
  | .cls => [armIselInsI (.CLS (zr d w) (zr ra w))]
  | .rbit => [armIselInsI (.RBIT (zr d w) (zr ra w))]
  | .ctz => [armIselInsI (.RBIT (zr d w) (zr ra w)), armIselInsI (.CLZ (zr d w) (zr d w))]

@[reducible] def armBitEval (k : ArmBitK) {n : Nat} (x : BitVec n) : BitVec n :=
  match k with
  | .clz => x.clz
  | .cls => (if x.msb then (~~~x).clz else x.clz) - 1#n
  | .rbit => x.reverse
  | .ctz => x.reverse.clz

theorem armBitOp_wp [Host] (k : ArmBitK) {n : Nat} (pa : PArg Reg Empty ArmCond (.bits n))
    (d : XReg)
    {va : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : (do
      if !(n == 32 || n == 64) then none
      else let (ca, ra) ← armArgInIns .X16 pa
           some (ca ++ armBitCodeI k (armWidthOf n) d ra, maskNone)) = some (c, clob))
    (hpa : armMach.PArgHolds s (.bits n) pa va) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (armBitEval k va) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only at hc; split at hc
  · simp at hc
  · rename_i hn3264
    have hn' : n = 32 ∨ n = 64 := by cases h32 : (n == 32) <;> cases h64 : (n == 64) <;> simp_all
    have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl <;> decide
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨⟨ca, ra⟩, ha, rfl, rfl⟩
    rw [emitClean_append]
    refine armWp_append (armArgIn_wp hn64 ha hpa) ?_
    rintro s₁ ⟨hra, hd₁, _, hfr₁⟩
    have hfr₁' : armMach.Frame armCondReads s s₁ armScratch [] maskNone :=
      hfr₁.weaken (fun x hr =>
        by simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hr; subst hr; exact x16_mem_scratch)
        (fun v => v.elim) rfl
    have step1 :
        ∀ (w : RegWidth) (hnw : n = w.bits)
            (hra' : (s₁.regs.getXReg ra).toBitVec.setWidth w.bits = hnw ▸ va),
        _root_.Program.wp (emitClean (armBitCodeI k w d ra)) (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n (armBitEval k va) ∧
          armMach.mem s' = armMach.mem s ∧
            armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone)
          (fun _ _ => False) s₁ := by
      intro w hnw hra'; subst hnw
      rw [show emitClean (armBitCodeI k w d ra) = armBitCode k w d ra by cases k <;> rfl]
      cases k
      · refine armWrDst_after_scratch hn64 d (armDirFallsTo_wp (Q :=
          fun s' => s' = wr s₁ d (va.clz.setWidth 64))
          fun {_} p next jmp Q hk => by
            dsimp only [armBitCode, ins]
            cases w <;>
              (simp only [t_step_simp, BitVec.setWidth_eq] at hra' ⊢; rw [hra']; exact hk _ rfl))
          hd₁ hfr₁' (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
          (fun _ => rfl)
      · refine armWrDst_after_scratch hn64 d (armDirFallsTo_wp (Q :=
          fun s' => s' = wr s₁ d ((armBitEval .cls va).setWidth 64))
          fun {_} p next jmp Q hk => by
            dsimp only [armBitCode, ins]
            cases w <;>
              (simp only [t_step_simp, BitVec.setWidth_eq] at hra' ⊢; rw [hra']; exact hk _ rfl))
          hd₁ hfr₁' (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
          (fun _ => rfl)
      · refine armWrDst_after_scratch hn64 d (armDirFallsTo_wp (Q :=
          fun s' => s' = wr s₁ d (va.reverse.setWidth 64))
          fun {_} p next jmp Q hk => by
            dsimp only [armBitCode, ins]
            cases w <;>
              (simp only [t_step_simp, BitVec.setWidth_eq] at hra' ⊢; rw [hra']; exact hk _ rfl))
          hd₁ hfr₁' (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
          (fun _ => rfl)
      · refine armWp_cons (armDirFallsTo_wp (Q := fun s' => s' = wr s₁ d (va.reverse.setWidth 64))
          fun {_} p next jmp Q hk => by
            dsimp only [armBitCode, ins]
            cases w <;>
              (simp only [t_step_simp, BitVec.setWidth_eq] at hra' ⊢; rw [hra']; exact hk _ rfl))
          fun s₂ hs₂ => ?_
        subst hs₂
        refine armWp_mono (armDirFallsTo_wp (Q :=
            fun s' => s' = wr (wr s₁ d (va.reverse.setWidth 64)) d (va.reverse.clz.setWidth 64))
          fun {_} p next jmp Q hk => by
            cases w
            · simp only [t_step_simp, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
                BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
              exact hk _ rfl
            · simp only [t_step_simp, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
                BitVec.setWidth_eq]
              exact hk _ rfl)
          fun s₃ hs₃ => ?_
        rw [hs₃, wr_wr_same]
        refine ⟨⟨⟨hn64, ?_⟩, fun hn32 => by
          cases w
          · dsimp only [armBitEval]
            exact get_wr_same s₁ d _
          · simp [RegWidth.bits, MemWidth.bits] at hn32⟩, hd₁,
          armFrame_scratch_wr hfr₁' (frame_wr d _ List.mem_cons_self maskNone)⟩
        rw [show armMach.getGpr (wr s₁ d (va.reverse.clz.setWidth 64)) (.reg d) = get (wr s₁ d
            (va.reverse.clz.setWidth 64)) (.reg d) from rfl,
          get_wr_same, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]
    rcases hn' with rfl | rfl
    · exact step1 .W32 rfl hra
    · exact step1 .W64 rfl (by simpa [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq] using hra)

private theorem armImm12_toNat_lt {n : Nat} {c : BitVec n} {ei : ExtOrImmReg}
    (h : armImm12? c = some ei) : c.toNat < 16777216 := by
  dsimp only [armImm12?] at h
  split at h
  · rename_i hlt; have := Nat.blt_eq.mp hlt; omega
  · split at h
    · rename_i hand; simp only [Bool.and_eq_true, Nat.blt_eq] at hand; exact hand.1
    · cases h

private theorem adds_eq_subs_neg {w : Nat} (hw : 32 ≤ w) (x k : BitVec w)
    (hk0 : k ≠ 0#w) (hklt : k.toNat < 16777216) :
    StatusFlags.adds (x + k) x k = StatusFlags.subs (x - (-k)) x (-k) := by
  have hpow : 16777216 < 2 ^ (w - 1) := by
    have : 2 ^ 31 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have : 16777216 < 2 ^ 31 := by decide
    omega
  have hxlt := x.isLt
  have hkpos : 0 < k.toNat := by
    rcases Nat.eq_zero_or_pos k.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hk0
    · exact h
  have hpoww : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have hw1 : (w - 1) + 1 = w := by omega
    calc 2 ^ w = 2 ^ ((w - 1) + 1) := by rw [hw1]
      _ = 2 * 2 ^ (w - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hres : x + k = x - (-k) := by rw [BitVec.sub_neg]
  have hnknat : (-k).toNat = 2 ^ w - k.toNat := by
    rw [BitVec.toNat_neg]; exact Nat.mod_eq_of_lt (by omega)
  have hc : ((x + k).unsigned != x.unsigned + k.unsigned) =
      ((x - (-k)).unsigned == x.unsigned - (-k).unsigned) := by
    rw [← hres]; simp only [BitVec.unsigned, BitVec.toNat_add]
    by_cases hsum : x.toNat + k.toNat < 2 ^ w
    · have hm : (x.toNat + k.toNat) % 2 ^ w = x.toNat + k.toNat := Nat.mod_eq_of_lt hsum
      rw [hm, hnknat]
      have hb1 : (((x.toNat + k.toNat : Nat) : Int) != (x.toNat : Int) + (k.toNat : Int)) =
          false := by simp
      have hb2 : (((x.toNat + k.toNat : Nat) : Int) ==
          (x.toNat : Int) - ((2 ^ w - k.toNat : Nat) : Int)) = false :=
        beq_false_of_ne (by omega)
      exact hb1.trans hb2.symm
    · have hq : 2 ^ w ≤ x.toNat + k.toNat := by omega
      have hm : (x.toNat + k.toNat) % 2 ^ w = x.toNat + k.toNat - 2 ^ w := by
        rw [Nat.mod_eq_sub_mod hq, Nat.mod_eq_of_lt (by omega)]
      rw [hm, hnknat]
      have hb1 : (((x.toNat + k.toNat - 2 ^ w : Nat) : Int) !=
          (x.toNat : Int) + (k.toNat : Int)) = true := bne_iff_ne.mpr (by omega)
      have hb2 : (((x.toNat + k.toNat - 2 ^ w : Nat) : Int) ==
          (x.toNat : Int) - ((2 ^ w - k.toNat : Nat) : Int)) = true := beq_iff_eq.mpr (by omega)
      exact hb1.trans hb2.symm
  have hksgn : k.signed = (k.toNat : Int) := by
    simp only [BitVec.signed, BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hnksgn : (-k).signed = -(k.toNat : Int) := by
    simp only [BitVec.signed, BitVec.toInt_eq_toNat_cond, hnknat]; split <;> omega
  have hv : ((x + k).signed != x.signed + k.signed) =
      ((x - (-k)).signed != x.signed - (-k).signed) := by
    rw [← hres, hksgn, hnksgn,
      show x.signed - -(k.toNat : Int) = x.signed + (k.toNat : Int) by omega]
  simp only [StatusFlags.adds, StatusFlags.subs, StatusFlags.from_result]
  rw [hc, hv, hres]

private theorem armSubsImm_wp [Host] {n : Nat} (hn : n ≤ 64) (w : RegWidth) (rx : XReg)
    (imm : BitVec n) (ei : ExtOrImmReg) (hei : armImm12? imm = some ei) (s : MachineData) :
    _root_.Program.wp [ins (.SUBS_e (xzr w) (.low (.reg rx) w) ei)]
      (fun s' => s' =
        { s with
          status := StatusFlags.subs
            ((s.regs.getXReg rx).toBitVec.setWidth w.bits - imm.setWidth w.bits)
            ((s.regs.getXReg rx).toBitVec.setWidth w.bits) (imm.setWidth w.bits) })
      (fun _ _ => False) s := by
  refine armDirFallsTo_wp fun {_} p next jmp Q hk => ?_
  have himm := armImm12_some hn hei w p s.regs
  dsimp only [ExtOrImmReg.interp] at himm
  cases w <;>
    (simp only [t_step_simp, Reg64s.setRegOrZr_xzr] at himm ⊢
     rw [himm]
     exact hk _ (by simp [RegWidth.bits, MemWidth.bits]))

private theorem armAddsImm_wp [Host] {n : Nat} (hn : n ≤ 64) (w : RegWidth) (rx : XReg)
    (imm : BitVec n) (ei : ExtOrImmReg) (hei : armImm12? imm = some ei) (s : MachineData) :
    _root_.Program.wp [ins (.ADDS_e (xzr w) (.low (.reg rx) w) ei)]
      (fun s' => s' =
        { s with
          status := StatusFlags.adds
            ((s.regs.getXReg rx).toBitVec.setWidth w.bits + imm.setWidth w.bits)
            ((s.regs.getXReg rx).toBitVec.setWidth w.bits) (imm.setWidth w.bits) })
      (fun _ _ => False) s := by
  refine armDirFallsTo_wp fun {_} p next jmp Q hk => ?_
  have himm := armImm12_some hn hei w p s.regs
  dsimp only [ExtOrImmReg.interp] at himm
  cases w <;>
    (simp only [t_step_simp, Reg64s.setRegOrZr_xzr] at himm ⊢
     rw [himm]
     exact hk _ (by simp [RegWidth.bits, MemWidth.bits]))

private theorem armCmpImm_wp [Host] {n : Nat} (hn : n = 32 ∨ n = 64) (w : RegWidth)
    (hw : w.bits = n) (rx : XReg) (imm : BitVec n) {cmp : List Instr}
    (hc : armCmpImmIns? w rx imm = some cmp) (s : MachineData) :
    _root_.Program.wp (emitClean cmp)
      (fun sx =>
        sx.status = StatusFlags.subs
          ((s.regs.getXReg rx).toBitVec.setWidth n - imm)
          ((s.regs.getXReg rx).toBitVec.setWidth n) imm ∧
        sx.dmem = s.dmem ∧ armMach.Frame armCondReads s sx armScratch [] maskNZCV)
      (fun _ _ => False) s := by
  have hn64 : n ≤ 64 := by rcases hn with rfl | rfl <;> decide
  have hw32 : 32 ≤ w.bits := by rw [hw]; rcases hn with rfl | rfl <;> decide
  dsimp only [armCmpImmIns?] at hc
  cases himm : armImm12? imm with
  | some ei =>
    simp only [himm, Option.some.injEq] at hc
    subst hc
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armSubsImm_wp hn64 w rx imm ei himm s) ?_
    rintro s₁ rfl
    refine ⟨?_, rfl, armFrame_nzcv fun _ _ => rfl⟩
    cases w <;> simp only [RegWidth.bits, MemWidth.bits] at hw <;> subst hw <;>
      simp [BitVec.setWidth_eq]
  | none =>
    simp only [himm] at hc
    split at hc
    · cases hc
    · rename_i hne0
      have himm0 : imm ≠ 0#n := fun e => hne0 (beq_iff_eq.mpr e)
      have hnimm0 : -imm ≠ 0#n := fun h => himm0 (by simpa using congrArg (- ·) h)
      cases hni : armImm12? (-imm) with
      | none => simp [hni] at hc
      | some ei =>
        simp only [hni, Option.some.injEq] at hc
        subst hc
        simp only [emitClean_cons, emitClean_nil]
        refine armWp_mono (armAddsImm_wp hn64 w rx (-imm) ei hni s) ?_
        rintro s₁ rfl
        refine ⟨?_, rfl, armFrame_nzcv fun _ _ => rfl⟩
        have hlt : (-imm).toNat < 16777216 := armImm12_toNat_lt hni
        cases w <;> simp only [RegWidth.bits, MemWidth.bits] at hw <;> subst hw <;>
          simp only [BitVec.setWidth_eq] <;>
          rw [adds_eq_subs_neg (by decide) _ _ hnimm0 hlt, BitVec.neg_neg]

theorem subword_and_eq_zero {n : Nat} (hn : n ≤ 32) {x : BitVec 32} {va cy : BitVec n}
    (hx : x.setWidth n = va) :
    ((x &&& cy.setWidth 32) == 0#32) = ((va &&& cy) == 0#n) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h0; apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h32 : i < 32 := Nat.lt_of_lt_of_le hi hn
    have hb := congrArg (fun z => z.getLsbD i) h0
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, h32, decide_true, Bool.true_and,
      BitVec.getLsbD_zero] at hb
    have hxi : x.getLsbD i = va.getLsbD i := by
      rw [← hx, BitVec.getLsbD_setWidth]; simp [hi]
    rw [BitVec.getLsbD_and, ← hxi, BitVec.getLsbD_zero]
    exact hb
  · intro h0; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
      BitVec.getLsbD_zero]
    by_cases hin : i < n
    · have hb := congrArg (fun z => z.getLsbD i) h0
      have hxi : x.getLsbD i = va.getLsbD i := by
        rw [← hx, BitVec.getLsbD_setWidth]; simp [hin]
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hb
      rw [hxi]; exact hb
    · have hc : cy.getLsbD i = false := by
        cases h : cy.getLsbD i; rfl; exact absurd (BitVec.lt_of_getLsbD h) hin
      rw [hc, Bool.and_false]

theorem testCond_eq_of_z {w n : Nat} (neg : Bool) (r1 : BitVec w) (r2 : BitVec n)
    (hz : (r1 == 0#w) = (r2 == 0#n)) :
    (if neg then ArmCond.ne else ArmCond.eq).interp
        (StatusFlags.from_result r1 { c := false, v := false }) =
      (if neg then CmpOp.ne else CmpOp.eq).evalBits r2 0#n := by
  have hzd : (r1 == 0#w) = decide (r2 = 0#n) := by
    cases h1 : (r1 == 0#w) <;> cases h2 : (r2 == 0#n) <;> simp_all [beq_iff_eq]
  cases neg <;> simp [ArmCond.interp, ArmCond.toKraken, CondCode.interp,
    StatusFlags.from_result, CmpOp.evalBits, BitVec.zero, hzd]

theorem armAndsImm_wp [Host] (w : RegWidth) (rx : XReg) (c64 : BitVec 64)
    (s : MachineData) :
    _root_.Program.wp
      [ins (.ANDS_i (xzr w) (zr rx w) (.int64 (Int64.ofBitVec c64)))]
      (fun s' => s' = { s with
        status := StatusFlags.from_result
          ((s.regs.getXReg rx).toBitVec.setWidth w.bits &&& c64.setWidth w.bits)
          { c := false, v := false } })
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases w <;>
      (simp only [t_step_simp, Reg64s.setRegOrZr_xzr, ConstExpr.interp]
       rw [int64_toInt_ofBitVec_setWidth]
       exact hk _ rfl)


private theorem armZeroAndsFinish_wp [Host] {n : Nat} (hn' : n = 8 ∨ n = 16) (o : CmpOp)
    (neg : Bool) (rx : XReg) (dst : PDst Reg Empty ArmCond .bool)
    {vr : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hrx : (s.regs.getXReg rx).toBitVec.setWidth n = vr)
    (hev : o.evalBits vr 0#n = (if neg then CmpOp.ne else CmpOp.eq).evalBits vr 0#n)
    (hfin : (match dst with
      | .flag cf =>
        if cf == (if neg then ArmCond.ne else ArmCond.eq) then
          some ([armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32)
            (.int64 (if n == 8 then 0xFF else 0xFFFF)))], maskNZCV)
        else none
      | .gpr (.reg d) =>
        some ([armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32)
            (.int64 (if n == 8 then 0xFF else 0xFFFF))),
          armCset64I d (if neg then ArmCond.ne else ArmCond.eq)], maskNZCV)
      | .gpr .SP | .vec _ => none) = some (c, clob)) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst (o.evalBits vr 0#n) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  have ands816_wp :
      let c64 : BitVec 64 := BitVec.ofNat 64 (if n == 8 then 0xFF else 0xFFFF)
      _root_.Program.wp
        [ins (.ANDS_i (xzr .W32) (zr rx .W32) (.int64 (if n == 8 then 0xFF else 0xFFFF)))]
        (fun s' => (if neg then ArmCond.ne else ArmCond.eq).interp s'.status =
            (if neg then CmpOp.ne else CmpOp.eq).evalBits vr 0#n ∧
          s'.dmem = s.dmem ∧
          armMach.Frame armCondReads s s' armScratch [] maskNZCV)
        (fun _ _ => False) s := by
    intro c64
    have hc64 : (if n == 8 then (0xFF : Int64) else 0xFFFF) = Int64.ofBitVec c64 := by
      rcases hn' with rfl | rfl <;> rfl
    rw [hc64]
    refine armWp_mono (armAndsImm_wp .W32 rx c64 s) ?_
    rintro sx rfl
    refine ⟨?_, rfl, armFrame_nzcv fun _ _ => rfl⟩
    have hmask : c64.setWidth 32 = (~~~0#n).setWidth 32 := by
      rcases hn' with rfl | rfl <;> rfl
    have hrx32 : ((s.regs.getXReg rx).toBitVec.setWidth 32).setWidth n = vr := by
      rwa [BitVec.setWidth_setWidth_of_le _ (by rcases hn' with rfl | rfl <;> decide)]
    have hz : ((s.regs.getXReg rx).toBitVec.setWidth 32 &&& c64.setWidth 32 == 0#32) =
        (vr == 0#n) := by
      rw [hmask, subword_and_eq_zero (by rcases hn' with rfl | rfl <;> decide) hrx32]
      have hand : vr &&& ~~~0#n = vr := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
      rw [hand]
    simpa [RegWidth.bits, MemWidth.bits] using testCond_eq_of_z neg _ vr hz
  cases dst with
  | vec vr' => exact vr'.elim
  | flag cf =>
    dsimp only at hfin
    by_cases heqc : (cf == (if neg then ArmCond.ne else ArmCond.eq)) = true
    · simp only [heqc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hfin
      rcases hfin with ⟨rfl, rfl⟩
      have hcf : cf = (if neg then ArmCond.ne else ArmCond.eq) := by
        cases cf <;> cases neg <;> first | rfl | exact absurd heqc (by decide)
      subst hcf
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono ands816_wp ?_
      rintro sx ⟨hcc, hdm, hfr⟩
      refine ⟨?_, hdm, hfr⟩
      simpa [Machine.PDstHolds, hev] using hcc
    · simp only [heqc, Bool.false_eq_true, ↓reduceIte] at hfin; cases hfin
  | gpr r => cases r with | SP => cases hfin | reg d =>
    rcases Option.some.inj hfin with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_cons ands816_wp ?_
    rintro sx ⟨hcc, hdm, hfr⟩
    refine armWp_mono (armCset64_wp d (if neg then .ne else .eq) sx) ?_
    rintro sy rfl
    refine ⟨?_, hdm, armFrame_nzcv fun r hr => ?_⟩
    · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hcc, hev]
      cases (if neg then CmpOp.ne else CmpOp.eq).evalBits vr 0#n <;> rfl
    · have hne : r ≠ .reg d ∧ r ∉ armScratch :=
        ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne sx d _ r hne.1]; exact hfr.1 r hne.2

private theorem armZeroCmp_wp [Host] {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    (o : CmpOp) (rx : XReg) (dst : PDst Reg Empty ArmCond .bool)
    {vr : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armZeroCmpIns? o n rx dst = some (c, clob))
    (hrx : (s.regs.getXReg rx).toBitVec.setWidth n = vr) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst (o.evalBits vr 0#n) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  have hn64 := mem_armWidths_le_64 hn
  have hnw := mem_armWidths_le_armWidth hn
  have hn0 : 0 < n := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> decide
  have sltBitEq : ((s.regs.getXReg rx).toBitVec.setWidth (armWidthOf n).bits).getLsbD (n - 1) =
      vr.slt 0#n := by
    have hnltw : n - 1 < (armWidthOf n).bits := by omega
    rw [← hrx, BitVec.getLsbD_setWidth]
    have hbit : vr.slt 0#n = vr.msb := by
      simp only [BitVec.slt, BitVec.toInt_eq_msb_cond, BitVec.msb_zero, BitVec.toNat_zero,
        Bool.false_eq_true, ↓reduceIte]
      have hlt : (vr.toNat : Int) < (2 : Int) ^ n := by exact_mod_cast vr.isLt
      have h0 : (0 : Int) ≤ vr.toNat := Int.natCast_nonneg _
      cases hv : vr.msb <;> simp <;> try omega
    rw [← hrx] at hbit
    rw [hbit, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]
    simp [show n - 1 < n by omega, hnltw]
  cases o with
  | slt =>
    cases dst with
    | vec vr' => exact vr'.elim
    | flag _ => dsimp only [armZeroCmpIns?] at hc; cases hc
    | gpr r => cases r with
      | SP => dsimp only [armZeroCmpIns?] at hc; cases hc
      | reg d =>
        dsimp only [armZeroCmpIns?] at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl
        all_goals
          (refine armWp_mono (armDirFallsTo_wp fun {_} p next jmp Q hk => by
             simp only [armWidthOf,
               t_step_simp]; rw [evalUBFM_bit _ (by decide)]; exact hk _ rfl) ?_
           rintro s' rfl
           refine ⟨?_, rfl, frame_wr d _ List.mem_cons_self maskNone⟩
           simp only [Machine.PDstHolds, GprHolds, get_wr_same, RegWidth.bits, MemWidth.bits]
           have heval : CmpOp.slt.evalBits vr 0#_ = vr.slt 0#_ := rfl
           rw [heval, ← sltBitEq]
           simp only [armWidthOf, RegWidth.bits, MemWidth.bits]
           cases ((s.regs.getXReg rx).toBitVec.setWidth _).getLsbD _ <;> decide)
  | sge =>
    cases dst with
    | vec vr' => exact vr'.elim
    | flag _ => dsimp only [armZeroCmpIns?] at hc; cases hc
    | gpr r => cases r with
      | SP => dsimp only [armZeroCmpIns?] at hc; cases hc
      | reg d =>
        dsimp only [armZeroCmpIns?] at hc
        split at hc
        · rename_i hn816
          have hn' : n = 8 ∨ n = 16 := by
            rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
          rcases Option.some.inj hc with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          have hw32 : armWidthOf n = .W32 := by rcases hn' with rfl | rfl <;> rfl
          have hsge : CmpOp.sge.evalBits vr 0#n = !(vr.slt 0#n) := by
            simp only [CmpOp.evalBits, BitVec.sle, BitVec.slt]
            by_cases hlt : vr.toInt < (0#n).toInt
            · simp only [hlt, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
            · simp only [hlt, decide_false, Bool.not_false, decide_eq_true_eq]; omega
          have hbit32 : ((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n - 1) = vr.slt 0#n :=
              by
            simpa [hw32] using sltBitEq
          refine armWp_cons (armDirFallsTo_wp (Q := fun s' => s' = wr s d
              ((BitVec.ofNat 32 (((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n -
                  1)).toNat).setWidth 64))
            fun {_} p next jmp Q hk => by
              simp only [t_step_simp]
              rw [evalUBFM_bit _ (by rcases hn' with rfl | rfl <;> decide)]
              exact hk _ rfl) ?_
          rintro s₁ rfl
          refine armWp_mono (armDirFallsTo_wp (Q := fun s₂ => s₂ = wr (wr s d
              ((BitVec.ofNat 32 (((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n -
                  1)).toNat).setWidth 64)) d
              ((BitVec.ofNat 32
                (((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n -
                    1)).toNat ^^^ 1#32).setWidth 64))
            fun {_} p next jmp Q hk => by
              simp only [t_step_simp, ConstExpr.interp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
                RegWidth.bits, MemWidth.bits, Reg64s.getXReg_setXReg_same,
                BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
                show BitVec.ofInt 32 (Int64.toInt 1) = 1#32 from rfl]
              exact hk _ rfl) ?_
          rintro s₂ rfl
          rw [wr_wr_same]
          refine ⟨?_, rfl, frame_wr d _ List.mem_cons_self maskNone⟩
          simp only [Machine.PDstHolds, GprHolds, get_wr_same, hsge, ← hbit32]
          cases ((s.regs.getXReg rx).toBitVec.setWidth 32).getLsbD (n - 1) <;> decide
        · cases hc
  | eq =>
    dsimp only [armZeroCmpIns?] at hc
    split at hc
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      dsimp only [armCmpCond] at hc
      exact armZeroAndsFinish_wp hn' .eq false rx dst hrx rfl hc
    · cases hc
  | ne =>
    dsimp only [armZeroCmpIns?] at hc
    split at hc
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      dsimp only [armCmpCond] at hc
      exact armZeroAndsFinish_wp hn' .ne true rx dst hrx rfl hc
    · cases hc
  | ule =>
    cases dst with
    | vec vr' => exact vr'.elim
    | flag _ => dsimp only [armZeroCmpIns?] at hc; cases hc
    | gpr r => cases r with
      | SP => dsimp only [armZeroCmpIns?] at hc; cases hc
      | reg d =>
        dsimp only [armZeroCmpIns?] at hc
        split at hc
        · rename_i hn816
          have hn' : n = 8 ∨ n = 16 := by
            rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
          have hev : CmpOp.ule.evalBits vr 0#n = CmpOp.eq.evalBits vr 0#n := by
            simp only [CmpOp.evalBits, BitVec.ule, BitVec.toNat_zero, Nat.le_zero]
            by_cases hv : vr = 0#n
            · simp [hv]
            · have hne0 : vr.toNat ≠ 0 := fun h => hv (BitVec.eq_of_toNat_eq (by simpa using h))
              simp [hv, hne0]
          exact armZeroAndsFinish_wp hn' .ule false rx (.gpr (.reg d)) hrx hev hc
        · cases hc
  | ugt =>
    cases dst with
    | vec vr' => exact vr'.elim
    | flag _ => dsimp only [armZeroCmpIns?] at hc; cases hc
    | gpr r => cases r with
      | SP => dsimp only [armZeroCmpIns?] at hc; cases hc
      | reg d =>
        dsimp only [armZeroCmpIns?] at hc
        split at hc
        · rename_i hn816
          have hn' : n = 8 ∨ n = 16 := by
            rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
          have hev : CmpOp.ugt.evalBits vr 0#n = CmpOp.ne.evalBits vr 0#n := by
            simp only [CmpOp.evalBits, BitVec.ult, BitVec.toNat_zero]
            by_cases hv : vr = 0#n
            · simp [hv]
            · have hpos : 0 < vr.toNat :=
                Nat.pos_of_ne_zero (fun h => hv (BitVec.eq_of_toNat_eq (by simpa using h)))
              simp [hv, hpos]
          exact armZeroAndsFinish_wp hn' .ugt true rx (.gpr (.reg d)) hrx hev hc
        · cases hc
  | ult | uge | sle | sgt =>
    dsimp only [armZeroCmpIns?] at hc; cases hc

theorem armCmpOp_wp [Host] (o : CmpOp) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dst : PDst Reg Empty ArmCond .bool)
    {va vb : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armCmpOpIns o n pa pb dst = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (_hd : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst (o.evalBits va vb) ∧
      (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
        FlagCmpOk armMach armGpr s' (if lf then va else vb) (if lf then vb else va) false) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  dsimp only [armCmpOpIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hSub3264 : ∀ {sx : MachineData} {m : Nat} (hm : m = 32 ∨ m = 64) {x y : BitVec m},
        sx.status = StatusFlags.subs (x - y) x y →
        FlagCmpOk armMach armGpr sx x y false := by
      intro sx m hm x y hst co' cc' _ hco'
      cases hco'; dsimp only [Machine.evalCond, armMach]; rw [hst]
      exact armCmpCond_subs hm co' x y
    have hSignExtEval : ∀ {m : Nat} (hm : m = 8 ∨ m = 16) (co' : CmpOp) (x y : BitVec m),
        co'.evalBits (x.signExtend 32) (y.signExtend 32) = co'.evalBits x y := by
      intro m hm co' x y
      have hle : m ≤ 32 := by rcases hm with rfl | rfl <;> decide
      have hmsb : ∀ z : BitVec m, (z.signExtend 32).msb = z.msb := fun z => by
        rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
        have hz : z.msb = z.getLsbD (m - 1) := by
          rcases hm with rfl | rfl <;> exact BitVec.msb_eq_getLsbD_last z
        rw [hz]; rcases hm with rfl | rfl <;> simp
      have hseNat : ∀ z : BitVec m,
          (z.signExtend 32).toNat =
            if z.msb then 2 ^ 32 - 2 ^ m + z.toNat else z.toNat := fun z => by
        have hltz := z.isLt
        have hlt32 := (z.signExtend 32).isLt
        have hti := BitVec.toInt_signExtend_of_le (x := z) hle
        rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond, hmsb z] at hti
        cases hz : z.msb <;> simp only [hz, ↓reduceIte, Bool.false_eq_true] at hti ⊢ <;>
          rcases hm with rfl | rfl <;> omega
      have hmle : ∀ z : BitVec m, z.msb = true ↔ 2 ^ (m - 1) ≤ z.toNat := fun z => by
        rw [BitVec.msb_eq_decide, decide_eq_true_eq]
      have hult : ∀ a b : BitVec m,
          (a.signExtend 32).ult (b.signExtend 32) = a.ult b := fun a b => by
        have ha := a.isLt; have hb := b.isLt
        simp only [BitVec.ult, hseNat]
        cases ha' : a.msb <;> cases hb' : b.msb
        · simp only [Bool.false_eq_true, ↓reduceIte]
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have ha2 : ¬(2 ^ (m - 1) ≤ a.toNat) := fun h => by
            have := (hmle a).mpr h; rw [ha'] at this; cases this
          have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
          rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
          rcases hm with rfl | rfl <;>
            simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
          have hb2 : ¬(2 ^ (m - 1) ≤ b.toNat) := fun h => by
            have := (hmle b).mpr h; rw [hb'] at this; cases this
          rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
          rcases hm with rfl | rfl <;>
            simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
        · simp only [↓reduceIte]
          have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
          have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
          rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
          rcases hm with rfl | rfl <;>
            simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
      have heq : (x.signExtend 32 = y.signExtend 32) ↔ x = y := by
        refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
        have h' := congrArg (BitVec.setWidth m) h
        simpa only [setWidth_signExtend_self hle] using h'
      have hule : ∀ a b : BitVec m,
          (a.signExtend 32).ule (b.signExtend 32) = a.ule b := fun a b => by
        have ha := a.isLt; have hb := b.isLt
        simp only [BitVec.ule, hseNat]
        cases ha' : a.msb <;> cases hb' : b.msb
        · simp only [Bool.false_eq_true, ↓reduceIte]
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have ha2 : ¬(2 ^ (m - 1) ≤ a.toNat) := fun h => by
            have := (hmle a).mpr h; rw [ha'] at this; cases this
          have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
          rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
          rcases hm with rfl | rfl <;>
            simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
          have hb2 : ¬(2 ^ (m - 1) ≤ b.toNat) := fun h => by
            have := (hmle b).mpr h; rw [hb'] at this; cases this
          rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
          rcases hm with rfl | rfl <;>
            simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
        · simp only [↓reduceIte]
          have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
          have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
          rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
          rcases hm with rfl | rfl <;>
            simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
      cases co' with
      | eq => simp only [CmpOp.evalBits, heq]
      | ne => simp only [CmpOp.evalBits, ne_eq, heq]
      | ult => exact hult x y
      | ule => exact hule x y
      | ugt => exact hult y x
      | uge => exact hule y x
      | slt | sle | sgt | sge => exact cmp_subword_signed hm _ rfl x y
    have hCmpFlagsExtract : ∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
        ((n = 32 ∨ n = 64) ∨ armIsSignedCmp o = true) ∧
        (match pa, pb with
          | .gpr (.reg ra), .imm cb =>
            (!(cb == 0#n && (armZeroCmpIns? o n ra dst).isSome)) = true ∧ lf = true
          | .imm ca, .gpr (.reg rb) =>
            if ca == 0#n then
              (armZeroCmpIns? o.swap n rb dst = none) ∧ lf = false
            else if n == 32 || n == 64 then
              lf = !(armCmpImmIns? (armWidthOf n) rb ca).isSome
            else lf = false
          | .gpr (.reg _), .gpr (.reg _) => lf = true
          | _, _ => False) := by
      intro lf hfl
      dsimp only [armCmpFlagsOut] at hfl
      split at hfl; · cases hfl
      split at hfl; · rename_i hbad; cases hfl
      rename_i _ hnotbad
      have hsgnOk : (n = 32 ∨ n = 64) ∨ armIsSignedCmp o = true := by
        rcases mem_armWidths hn with rfl | rfl | rfl | rfl
        · simp at hnotbad; exact Or.inr hnotbad
        · simp at hnotbad; exact Or.inr hnotbad
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr rfl)
      refine ⟨hsgnOk, ?_⟩
      simp only [Option.bind_eq_some_iff] at hfl
      rcases hfl with ⟨lf', hlf', hfin⟩
      have hlfEq : lf' = lf := by
        cases dst with
        | gpr r =>
          cases r
          · simp at hfin; exact hfin
          · simp at hfin
        | flag cf =>
          dsimp only at hfin
          by_cases hcf : (cf == armCmpCond (if lf' then o else o.swap)) = true
          · simp only [hcf, ↓reduceIte, Option.some.injEq] at hfin; exact hfin
          · simp only [hcf, ↓reduceIte, reduceCtorEq] at hfin
        | vec v => exact v.elim
      subst hlfEq
      cases pa with
      | vec v => exact v.elim
      | imm ca => cases pb with
        | vec v => exact v.elim
        | imm _ => simp at hlf'
        | gpr r2 => cases r2 with
          | SP => simp at hlf'
          | reg rb =>
            dsimp only at hlf'
            cases hca0 : ca == 0#n <;>
              simp only [hca0, Bool.false_eq_true, ↓reduceIte] at hlf' ⊢
            · cases hn3264 : n == 32 || n == 64 <;>
                simp only [hn3264, Bool.false_eq_true, ↓reduceIte] at hlf' ⊢ <;>
                cases hlf' <;> rfl
            · cases hzc : armZeroCmpIns? o.swap n rb dst
              · simp only [hzc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                  Option.some.injEq] at hlf'
                exact ⟨rfl, hlf'.symm⟩
              · simp only [hzc, Option.isSome_some, ↓reduceIte] at hlf'; cases hlf'
      | gpr r1 => cases r1 with
        | SP => simp at hlf'
        | reg ra => cases pb with
          | vec v => exact v.elim
          | imm cb =>
            dsimp only at hlf'
            cases hcond : (cb == 0#n && (armZeroCmpIns? o n ra dst).isSome) <;>
              simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hlf'
            · cases hlf'; simp [hcond]
            · cases hlf'
          | gpr r2 => cases r2 with
            | SP => simp at hlf'
            | reg rb => cases hlf'; rfl
    have hSgn816 : ∀ {lf}, n = 8 ∨ n = 16 → armCmpFlagsOut o n pa pb dst = some lf →
        armIsSignedCmp o = true := fun hn' hfl => by
      rcases (hCmpFlagsExtract hfl).1 with (rfl | rfl) | hs
      · rcases hn' with h | h <;> cases h
      · rcases hn' with h | h <;> cases h
      · exact hs
    have hSub816 : ∀ {sx : MachineData} (hn' : n = 8 ∨ n = 16) {x y : BitVec n},
        sx.status = StatusFlags.subs (x.signExtend 32 - y.signExtend 32)
          (x.signExtend 32) (y.signExtend 32) →
        FlagCmpOk armMach armGpr sx x y false := by
      intro sx hn' x y hst co' cc' _ hco'
      cases hco'; dsimp only [Machine.evalCond, armMach]; rw [hst]
      exact (armCmpCond_subs (Or.inl rfl) co' _ _).trans (hSignExtEval hn' co' x y)
    have finishSpec : ∀ {cmpCode : List Instr} {cond s'},
        _root_.Program.wp (emitClean cmpCode)
          (fun sx => cond.interp sx.status = o.evalBits va vb ∧
            (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
              FlagCmpOk armMach armGpr sx
                (if lf then va else vb) (if lf then vb else va) false) ∧
            sx.dmem = s.dmem ∧
            armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s' →
        (match dst with
          | .flag cf => if cf == cond then some (cmpCode, maskNZCV) else none
          | .gpr (.reg d) => some (cmpCode ++ [armCset64I d cond], maskNZCV)
          | .gpr .SP | .vec _ => none) = some (c, clob) →
        _root_.Program.wp (emitClean c)
          (fun sy => armMach.PDstHolds sy .bool dst (o.evalBits va vb) ∧
            (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
              FlagCmpOk armMach armGpr sy
                (if lf then va else vb) (if lf then vb else va) false) ∧
            armMach.mem sy = armMach.mem s ∧
            armMach.Frame armCondReads s sy (tupDstGprs (ts :=
                [.bool]) (dst, ()) ++ armScratch) [] clob)
          (fun _ _ => False) s' := by
      intro cmpCode cond s' hcmp hfin
      cases dst with
      | vec vr => exact vr.elim
      | flag cf =>
        dsimp only at hfin; split at hfin
        · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
          rcases Option.some.inj hfin with ⟨rfl, rfl⟩
          exact armWp_mono hcmp fun _ ⟨hcc, hfc, hdm, hfr⟩ => ⟨hcc, hfc, hdm, hfr⟩
        · cases hfin
      | gpr r => cases r with | SP => cases hfin | reg d =>
        rcases Option.some.inj hfin with ⟨rfl, rfl⟩
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append hcmp ?_; rintro sx ⟨hcc, hfc, hdm, hfr⟩
        refine armWp_mono (armCset64_wp d cond sx) ?_; rintro sy rfl
        refine ⟨?_, hfc, hdm, armFrame_nzcv fun r hr => ?_⟩
        · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hcc]; cases o.evalBits va vb <;> rfl
        · have hne : r ≠ .reg d ∧ r ∉ armScratch :=
            ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
          rw [get_wr_of_ne sx d _ r hne.1]; exact hfr.1 r hne.2
    have fallback : ∀ {ca ra cb rb},
        armArgInIns .X16 pa = some (ca, ra) → armArgInIns .X17 pb = some (cb, rb) →
        (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf → lf = true) →
        (if n == 32 || n == 64 then
           match dst with
           | .flag cf =>
             if cf == armCmpCond o then
               some (ca ++ cb ++
                 [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb))],
                 maskNZCV)
             else none
           | .gpr (.reg d) =>
             some (ca ++ cb ++
               [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb))] ++
               [armCset64I d (armCmpCond o)], maskNZCV)
           | .gpr .SP | .vec _ => none
         else
           match dst with
           | .flag cf =>
             if cf == armCmpCond o then
               some (ca ++ cb ++ [armExt32I (armIsSignedCmp o) n .X16 ra,
                 armExt32I (armIsSignedCmp o) n .X17 rb,
                 armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))], maskNZCV)
             else none
           | .gpr (.reg d) =>
             some (ca ++ cb ++ [armExt32I (armIsSignedCmp o) n .X16 ra,
               armExt32I (armIsSignedCmp o) n .X17 rb,
               armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))] ++
               [armCset64I d (armCmpCond o)], maskNZCV)
           | .gpr .SP | .vec _ => none) = some (c, clob) →
        _root_.Program.wp (emitClean c)
          (fun sy => armMach.PDstHolds sy .bool dst (o.evalBits va vb) ∧
            (∀ {lf}, armCmpFlagsOut o n pa pb dst = some lf →
              FlagCmpOk armMach armGpr sy
                (if lf then va else vb) (if lf then vb else va) false) ∧
            armMach.mem sy = armMach.mem s ∧
            armMach.Frame armCondReads s sy (tupDstGprs (ts :=
                [.bool]) (dst, ()) ++ armScratch) [] clob)
          (fun _ _ => False) s := by
      intro ca ra cb rb ha hb hlf hfb
      split at hfb
      · rename_i hn3264
        have hn' : n = 32 ∨ n = 64 := by
          simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
        refine finishSpec
          (cmpCode := ca ++ cb ++
            [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb))])
          (cond := armCmpCond o) ?_ hfb
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
        rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
        rcases hn' with rfl | rfl
        · rw [show armWidthOf 32 = .W32 from rfl]
          refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp (Q := fun s' =>
              s' = { s₂ with status :=
                  StatusFlags.subs (va - vb) va vb }) fun {_} p next jmp Q hk => by
            simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
              BitVec.shiftLeft_zero]
            rw [hra, hrb]; exact hk _ rfl) hd₂ hfr₂) ?_
          rintro s₃ ⟨_, hst₃, hdm₃, hfr₃⟩
          refine ⟨hst₃ ▸ armCmpCond_subs (Or.inl rfl) o va vb, ?_, hdm₃, hfr₃⟩
          intro lf hfl; obtain rfl := hlf hfl
          exact hSub3264 (Or.inl rfl) hst₃
        · rw [show armWidthOf 64 = .W64 from rfl]
          refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp (Q := fun s' =>
              s' = { s₂ with status :=
                  StatusFlags.subs (va - vb) va vb }) fun {_} p next jmp Q hk => by
            simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
              BitVec.shiftLeft_zero, BitVec.setWidth_eq] at hra hrb ⊢
            rw [hra, hrb]; exact hk _ rfl) hd₂ hfr₂) ?_
          rintro s₃ ⟨_, hst₃, hdm₃, hfr₃⟩
          refine ⟨hst₃ ▸ armCmpCond_subs (Or.inr rfl) o va vb, ?_, hdm₃, hfr₃⟩
          intro lf hfl; obtain rfl := hlf hfl
          exact hSub3264 (Or.inr rfl) hst₃
      · rename_i hn816
        have hn' : n = 8 ∨ n = 16 := by
          rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
        have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
        have hnw32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
        refine finishSpec (cmpCode := ca ++ cb ++ [armExt32I (armIsSignedCmp o) n .X16 ra,
          armExt32I (armIsSignedCmp o) n .X17 rb,
          armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]) (cond := armCmpCond o) ?_ hfb
        simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
        refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
        rintro s₂ ⟨hra, hrb, _, hneB, hd₂, _, hfr₂⟩
        simp only [emitClean_cons, emitClean_nil]
        refine armScratch_cons x16_mem_scratch hd₂ hfr₂
          (armExt32_wp (armIsSignedCmp o) hn0 hnw32 .X16 ra s₂ va hra) fun s₂' hs₂' hd₂' hfr₂' => ?_
        have hrb' : (s₂'.regs.getXReg rb).toBitVec.setWidth n = vb := by
          rw [hs₂', Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm]; exact hrb
        refine armScratch_cons x17_mem_scratch hd₂' hfr₂'
          (armExt32_wp (armIsSignedCmp o) hn0 hnw32 .X17 rb s₂' vb hrb') fun s₃ hs₃ hd₃ hfr₃ => ?_
        have h16₃ : (s₃.regs.getXReg .X16).toBitVec.setWidth 32 =
            if armIsSignedCmp o then va.signExtend 32 else va.setWidth 32 := by
          rw [hs₃, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide), hs₂']
          simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
        have h17₃ : (s₃.regs.getXReg .X17).toBitVec.setWidth 32 =
            if armIsSignedCmp o then vb.signExtend 32 else vb.setWidth 32 := by
          rw [hs₃]; simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
            BitVec.setWidth_eq]
        refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
            BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, h16₃, h17₃]; exact hk _ rfl) hd₃
            hfr₃) ?_
        rintro s₄ ⟨_, hst₄, hdm₄, hfr₄⟩
        refine ⟨?_, ?_, hdm₄, hfr₄⟩
        · rw [hst₄, armCmpCond_subs (Or.inl rfl)]
          cases hsgn : armIsSignedCmp o
          · simp only [Bool.false_eq_true, ↓reduceIte]; exact cmp_subword_unsigned hn' o hsgn va vb
          · simp only [↓reduceIte]; exact cmp_subword_signed hn' o hsgn va vb
        · intro lf hfl
          have hsgn := hSgn816 hn' hfl
          obtain rfl := hlf hfl
          have h16 : (if armIsSignedCmp o then va.signExtend 32 else va.setWidth 32) =
              va.signExtend 32 := by simp [hsgn]
          have h17 : (if armIsSignedCmp o then vb.signExtend 32 else vb.setWidth 32) =
              vb.signExtend 32 := by simp [hsgn]
          rw [h16, h17] at hst₄
          exact hSub816 hn' hst₄
    have cmpImm816Run : ∀ (hn' : n = 8 ∨
      n = 16) (isSwap : Bool) (rx : XReg) (vr vimm : BitVec n) (o' : CmpOp),
        (s.regs.getXReg rx).toBitVec.setWidth n = vr →
        (if isSwap then o' = o.swap ∧ va = vimm ∧ vb = vr
          else o' = o ∧ va = vr ∧ vb = vimm) →
        let sgn := armIsSignedCmp o
        let c32 := if sgn then vimm.signExtend 32 else vimm.setWidth 32
        let cmpCode := match armCmpImmIns? .W32 .X16 c32 with
          | some cmp => armExt32I sgn n .X16 rx :: cmp
          | none => armExt32I sgn n .X16 rx :: armMovImmI .X17 (c32.setWidth 64) ++
              [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]
        _root_.Program.wp (emitClean cmpCode)
          (fun sx => (armCmpCond o').interp sx.status = o.evalBits va vb ∧
            (sgn = true → FlagCmpOk armMach armGpr sx vr vimm false) ∧
            sx.dmem = s.dmem ∧
            armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s := by
      intro hn' isSwap rx vr vimm o' hrx hsweq sgn c32 cmpCode
      have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
      have hnw32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
      have hevalSub : o'.evalBits (if sgn then vr.signExtend 32 else vr.setWidth 32) c32 =
          o.evalBits va vb := by
        have ho'sgn : armIsSignedCmp o' = sgn := by
          cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hsweq
          · rcases hsweq with ⟨rfl, _⟩; rfl
          · rcases hsweq with ⟨rfl, _⟩; cases o <;> rfl
        cases hsgn : sgn
        · simp only [hsgn, Bool.false_eq_true, ↓reduceIte, c32]
          cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hsweq
          · rcases hsweq with ⟨rfl, rfl, rfl⟩
            exact cmp_subword_unsigned hn' o' (hsgn ▸ ho'sgn) va vb
          · rcases hsweq with ⟨rfl, rfl, rfl⟩
            rw [CmpOp.swap_evalBits]
            exact cmp_subword_unsigned hn' o hsgn va vb
        · simp only [hsgn, ↓reduceIte, c32]
          cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hsweq
          · rcases hsweq with ⟨rfl, rfl, rfl⟩
            exact cmp_subword_signed hn' o' (hsgn ▸ ho'sgn) va vb
          · rcases hsweq with ⟨rfl, rfl, rfl⟩
            rw [CmpOp.swap_evalBits]
            exact cmp_subword_signed hn' o hsgn va vb
      dsimp only [cmpCode]
      cases hci : armCmpImmIns? .W32 .X16 c32 with
      | some cmp =>
        dsimp only
        rw [emitClean_cons]
        refine armWp_cons (armExt32_wp sgn hn0 hnw32 .X16 rx s vr hrx) ?_
        rintro s₁ rfl
        refine armWp_mono (armCmpImm_wp (Or.inl rfl) .W32 rfl .X16 c32 hci _) ?_
        rintro sx ⟨hst, hdm, hfr⟩
        have h16 :
            let v32 := if sgn then vr.signExtend 32 else vr.setWidth 32
            ((wr s .X16 (v32.setWidth 64)).regs.getXReg .X16).toBitVec.setWidth 32 = v32 := by
          simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
        rw [h16] at hst
        have hcc : (armCmpCond o').interp sx.status = o.evalBits va vb := by
          rw [hst, armCmpCond_subs (Or.inl rfl)]; exact hevalSub
        refine ⟨hcc, fun hs => ?_, hdm, armFrame_nzcv fun r hr => ?_⟩
        · dsimp only [sgn] at hs; dsimp only [sgn, c32] at hst
          have hv' : (if armIsSignedCmp o then vr.signExtend 32 else vr.setWidth 32) =
              vr.signExtend 32 := by simp [hs]
          have hc' : (if armIsSignedCmp o then vimm.signExtend 32 else vimm.setWidth 32) =
              vimm.signExtend 32 := by simp [hs]
          rw [hv', hc'] at hst
          exact hSub816 hn' hst
        · exact (hfr.1 r hr).trans ((frame_wr .X16 _ x16_mem_scratch maskNone).1 r hr)
      | none =>
        dsimp only
        rw [List.cons_append, emitClean_cons, emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_cons (armExt32_wp sgn hn0 hnw32 .X16 rx s vr hrx) ?_
        rintro s₁ hs₁
        have hfr₁ : armMach.Frame armCondReads s s₁ armScratch [] maskNone :=
          hs₁ ▸ frame_wr .X16 _ x16_mem_scratch maskNone
        refine armWp_append (armMovImm_wp .X17 (c32.setWidth 64) s₁) ?_
        rintro s₂ hs₂
        have hfr₂ : armMach.Frame armCondReads s s₂ armScratch [] maskNone :=
          armFrame_scratch_trans hfr₁ (hs₂ ▸ frame_wr .X17 _ x17_mem_scratch maskNone)
        have h16₂ : (s₂.regs.getXReg .X16).toBitVec.setWidth 32 =
            if sgn then vr.signExtend 32 else vr.setWidth 32 := by
          rw [hs₂, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide), hs₁]
          simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
        have h17₂ : (s₂.regs.getXReg .X17).toBitVec.setWidth 32 = c32 := by
          rw [hs₂]
          simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
        refine armWp_mono (armStatusScratch_after (s := s) (s₂ := s₂)
          (armDirFallsTo_wp fun {_} p next jmp Q hk => by
            simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
              BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, h16₂, h17₂]
            exact hk _ rfl) (by rw [hs₂, hs₁]) hfr₂) ?_
        rintro s₃ ⟨_, hst₃, hdm₃, hfr₃⟩
        refine ⟨hst₃ ▸ (armCmpCond_subs (Or.inl rfl) o' _ _).trans hevalSub,
          fun hs => ?_, hdm₃, hfr₃⟩
        dsimp only [sgn] at hs; dsimp only [sgn, c32] at hst₃
        have hv' : (if armIsSignedCmp o then vr.signExtend 32 else vr.setWidth 32) =
            vr.signExtend 32 := by simp [hs]
        have hc' : (if armIsSignedCmp o then vimm.signExtend 32 else vimm.setWidth 32) =
            vimm.signExtend 32 := by simp [hs]
        rw [hv', hc'] at hst₃
        exact hSub816 hn' hst₃
    cases pa with
    | vec vr => exact vr.elim
    | gpr r => cases r with
      | SP =>
        cases pb with
        | vec vr => exact vr.elim
        | imm _ | gpr _ => dsimp only at hc; simp [armArgInIns] at hc
      | reg ra => cases pb with
        | vec vr => exact vr.elim
        | gpr r2 =>
          cases r2 with
          | SP => dsimp only at hc; simp [armArgInIns] at hc
          | reg rb =>
            dsimp only at hc; simp only [bind, Option.bind_eq_some_iff] at hc
            rcases hc with ⟨⟨_, _⟩, ha, ⟨_, _⟩, hb, hfin⟩
            exact fallback ha hb (fun hfl => (hCmpFlagsExtract hfl).2) hfin
        | imm cb =>
          dsimp only at hc
          have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
          have hcb : cb = vb := hpb
          have hlfT : ∀ {lf}, armCmpFlagsOut o n (.gpr (.reg ra)) (.imm cb) dst = some lf →
              lf = true := fun hfl => (hCmpFlagsExtract hfl).2.2
          by_cases hcb0 : cb == 0#n
          · simp only [hcb0, ↓reduceIte] at hc
            have hvb0 : vb = 0#n := hcb.symm.trans (beq_iff_eq.mp hcb0)
            cases hzc : armZeroCmpIns? o n ra dst with
            | some rz =>
              rw [hzc] at hc; rcases Option.some.inj hc with rfl
              refine armWp_mono (armZeroCmp_wp hn o ra dst hzc hra) ?_
              rintro sy ⟨h1, h2, h3⟩
              refine ⟨hvb0 ▸ h1, fun hfl => ?_, h2, h3⟩
              have hbad := (hCmpFlagsExtract hfl).2.1
              simp [hcb0, hzc] at hbad
            | none =>
              rw [hzc] at hc
              by_cases hn3264 : (n == 32 || n == 64) = true
              · have hn' : n = 32 ∨ n = 64 := by
                  simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
                simp only [hn3264, ↓reduceIte] at hc
                rcases option_none_or_some (armCmpImmIns? (armWidthOf n) ra cb) with hnone | ⟨cmp,
                  hcmp⟩
                · rw [hnone] at hc; cases hc
                · rw [hcmp] at hc
                  have hw : (armWidthOf n).bits = n := by rcases hn' with rfl | rfl <;> rfl
                  refine finishSpec (cmpCode := cmp) (cond := armCmpCond o)
                    (armWp_mono (armCmpImm_wp hn' (armWidthOf n) hw ra cb hcmp s) ?_) hc
                  rintro s₁ ⟨hst, hdm, hfr⟩; rw [hra, hcb] at hst
                  refine ⟨hst ▸ armCmpCond_subs hn' o va vb, ?_, hdm, hfr⟩
                  intro lf hfl; obtain rfl := hlfT hfl; exact hSub3264 hn' hst
              · have hn' : n = 8 ∨ n = 16 := by
                  rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                    first | exact Or.inl rfl | exact Or.inr rfl | simp at hn3264
                simp only [hn3264, Bool.false_eq_true, ↓reduceIte] at hc
                rcases option_none_or_some (armCmpImmIns? .W32 .X16 0#32) with hnone | ⟨cmp, hcmp⟩
                · rw [hnone] at hc; cases hc
                · rw [hcmp] at hc
                  have hsub := cmpImm816Run hn' false ra va cb o hra ⟨rfl, rfl, hcb.symm⟩
                  have hcb0' : cb = 0#n := beq_iff_eq.mp hcb0
                  have hc32 :
                      (if armIsSignedCmp o then cb.signExtend 32 else cb.setWidth 32) = 0#32 := by
                    rw [hcb0']; rcases hn' with rfl | rfl <;> cases armIsSignedCmp o <;> decide
                  simp only [hc32, hcmp] at hsub
                  refine finishSpec (armWp_mono hsub ?_) hc
                  rintro s₁ ⟨hcc, hfc, hdm, hfr⟩
                  refine ⟨hcc, fun hfl => ?_, hdm, hfr⟩
                  have hsgn := hSgn816 hn' hfl
                  obtain rfl := hlfT hfl; rw [hcb] at hfc; exact hfc hsgn
          · simp only [hcb0, Bool.false_eq_true, ↓reduceIte] at hc
            split at hc
            · rename_i hn3264
              have hn' : n = 32 ∨ n = 64 := by
                simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
              rcases option_none_or_some (armCmpImmIns? (armWidthOf n) ra cb) with hnone | ⟨cmp,
                hcmp⟩
              · simp only [hnone, bind, Option.bind_eq_some_iff] at hc
                rcases hc with ⟨⟨_, _⟩, ha, hfin⟩
                have hfb := fallback (ca := []) (ra := ra) rfl ha hlfT
                simp only [hn3264, ↓reduceIte] at hfb
                exact hfb hfin
              · simp only [hcmp] at hc
                have hw : (armWidthOf n).bits = n := by rcases hn' with rfl | rfl <;> rfl
                refine finishSpec (cmpCode := cmp) (cond := armCmpCond o)
                  (armWp_mono (armCmpImm_wp hn' (armWidthOf n) hw ra cb hcmp s) ?_) hc
                rintro s₁ ⟨hst, hdm, hfr⟩; rw [hra, hcb] at hst
                refine ⟨hst ▸ armCmpCond_subs hn' o va vb, ?_, hdm, hfr⟩
                intro lf hfl; obtain rfl := hlfT hfl; exact hSub3264 hn' hst
            · rename_i hn816
              have hn' : n = 8 ∨ n = 16 := by
                rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
              refine finishSpec
                (armWp_mono (cmpImm816Run hn' false ra va cb o hra ⟨rfl, rfl, hcb.symm⟩) ?_) hc
              rintro s₁ ⟨hcc, hfc, hdm, hfr⟩
              refine ⟨hcc, fun hfl => ?_, hdm, hfr⟩
              have hsgn := hSgn816 hn' hfl
              obtain rfl := hlfT hfl; rw [hcb] at hfc; exact hfc hsgn
    | imm ca => cases pb with
      | vec vr => exact vr.elim
      | imm _ =>
        dsimp only at hc; simp only [bind, Option.bind_eq_some_iff] at hc
        rcases hc with ⟨⟨_, _⟩, ha, ⟨_, _⟩, hb, hfin⟩
        exact fallback ha hb (fun hfl => False.elim (hCmpFlagsExtract hfl).2) hfin
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgInIns] at hc
        | reg rb =>
          dsimp only at hc
          have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
          have hca : ca = va := hpa
          by_cases hca0 : ca == 0#n
          · simp only [hca0, ↓reduceIte] at hc
            have hva0 : va = 0#n := hca.symm.trans (beq_iff_eq.mp hca0)
            have hlfF : ∀ {lf}, armCmpFlagsOut o n (.imm ca) (.gpr (.reg rb)) dst = some lf →
                lf = false := fun hfl => by
              have h := (hCmpFlagsExtract hfl).2; simp only [hca0, ↓reduceIte] at h; exact h.2
            cases hzc : armZeroCmpIns? o.swap n rb dst with
            | some rz =>
              rw [hzc] at hc; rcases Option.some.inj hc with rfl
              refine armWp_mono (armZeroCmp_wp hn o.swap rb dst hzc hrb) ?_
              rintro sy ⟨h1, h2, h3⟩
              refine ⟨by rw [CmpOp.swap_evalBits] at h1; exact hva0 ▸ h1, fun hfl => ?_, h2, h3⟩
              have h := (hCmpFlagsExtract hfl).2
              simp [hca0, hzc] at h
            | none =>
              rw [hzc] at hc
              by_cases hn3264 : (n == 32 || n == 64) = true
              · have hn' : n = 32 ∨ n = 64 := by
                  simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
                simp only [hn3264, ↓reduceIte] at hc
                rcases option_none_or_some (armCmpImmIns? (armWidthOf n) rb ca) with hnone | ⟨cmp,
                  hcmp⟩
                · rw [hnone] at hc; cases hc
                · rw [hcmp] at hc
                  have hw : (armWidthOf n).bits = n := by rcases hn' with rfl | rfl <;> rfl
                  refine finishSpec (cmpCode := cmp) (cond := armCmpCond o.swap)
                    (armWp_mono (armCmpImm_wp hn' (armWidthOf n) hw rb ca hcmp s) ?_) hc
                  rintro s₁ ⟨hst, hdm, hfr⟩; rw [hrb, hca] at hst
                  refine ⟨?_, ?_, hdm, hfr⟩
                  · rw [hst, armCmpCond_subs hn' o.swap vb va, CmpOp.swap_evalBits]
                  · intro lf hfl; obtain rfl := hlfF hfl; exact hSub3264 hn' hst
              · have hn' : n = 8 ∨ n = 16 := by
                  rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                    first | exact Or.inl rfl | exact Or.inr rfl | simp at hn3264
                simp only [hn3264, Bool.false_eq_true, ↓reduceIte] at hc
                rcases option_none_or_some (armCmpImmIns? .W32 .X16 0#32) with hnone | ⟨cmp, hcmp⟩
                · rw [hnone] at hc; cases hc
                · rw [hcmp] at hc
                  have hsub := cmpImm816Run hn' true rb vb ca o.swap hrb ⟨rfl, hca.symm, rfl⟩
                  have hca0' : ca = 0#n := beq_iff_eq.mp hca0
                  have hc32 :
                      (if armIsSignedCmp o then ca.signExtend 32 else ca.setWidth 32) = 0#32 := by
                    rw [hca0']; rcases hn' with rfl | rfl <;> cases armIsSignedCmp o <;> decide
                  simp only [hc32, hcmp] at hsub
                  refine finishSpec (armWp_mono hsub ?_) hc
                  rintro s₁ ⟨hcc, hfc, hdm, hfr⟩
                  refine ⟨hcc, fun hfl => ?_, hdm, hfr⟩
                  have hsgn := hSgn816 hn' hfl
                  obtain rfl := hlfF hfl; rw [hca] at hfc; exact hfc hsgn
          · simp only [hca0, Bool.false_eq_true, ↓reduceIte] at hc
            split at hc
            · rename_i hn3264
              have hn' : n = 32 ∨ n = 64 := by
                simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
              rcases option_none_or_some (armCmpImmIns? (armWidthOf n) rb ca) with hnone | ⟨cmp,
                hcmp⟩
              · simp only [hnone, bind, Option.bind_eq_some_iff] at hc
                rcases hc with ⟨⟨_, _⟩, ha, hfin⟩
                have hlfT : ∀ {lf}, armCmpFlagsOut o n (.imm ca) (.gpr (.reg rb)) dst = some lf →
                    lf = true := fun hfl => by
                  have h := (hCmpFlagsExtract hfl).2
                  simp [hca0, hn3264, hnone] at h; exact h
                have hfb := fallback (cb := []) (rb := rb) ha rfl hlfT
                simp only [hn3264, ↓reduceIte, List.append_nil] at hfb
                exact hfb hfin
              · simp only [hcmp] at hc
                have hw : (armWidthOf n).bits = n := by rcases hn' with rfl | rfl <;> rfl
                have hlfF : ∀ {lf}, armCmpFlagsOut o n (.imm ca) (.gpr (.reg rb)) dst = some lf →
                    lf = false := fun hfl => by
                  have h := (hCmpFlagsExtract hfl).2
                  simp [hca0, hn3264, hcmp] at h; exact h
                refine finishSpec (cmpCode := cmp) (cond := armCmpCond o.swap)
                  (armWp_mono (armCmpImm_wp hn' (armWidthOf n) hw rb ca hcmp s) ?_) hc
                rintro s₁ ⟨hst, hdm, hfr⟩; rw [hrb, hca] at hst
                refine ⟨?_, ?_, hdm, hfr⟩
                · rw [hst, armCmpCond_subs hn' o.swap vb va, CmpOp.swap_evalBits]
                · intro lf hfl; obtain rfl := hlfF hfl; exact hSub3264 hn' hst
            · rename_i hn816
              have hn' : n = 8 ∨ n = 16 := by
                rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
              have hlfF : ∀ {lf}, armCmpFlagsOut o n (.imm ca) (.gpr (.reg rb)) dst = some lf →
                  lf = false := fun hfl => by
                have h := (hCmpFlagsExtract hfl).2
                simp [hca0, hn816] at h; exact h
              refine finishSpec
                (armWp_mono (cmpImm816Run hn' true rb vb ca o.swap hrb ⟨rfl, hca.symm, rfl⟩) ?_) hc
              rintro s₁ ⟨hcc, hfc, hdm, hfr⟩
              refine ⟨hcc, fun hfl => ?_, hdm, hfr⟩
              have hsgn := hSgn816 hn' hfl
              obtain rfl := hlfF hfl; rw [hca] at hfc; exact hfc hsgn


end LeanQbe.T.Arm64
