module

public import LeanQbe.T.Arm64.IselLemmas2

/-!
# AArch64 Scalar Instruction Selection Proofs — Part 3 (`T9`)

Weakest-precondition correctness for `armDivRemOp`, `bswap`, `clz`/`cls`/`rbit`/`ctz`,
`armCmpOp`, `armSelectOp`, `armAddcOp`, and `armSubbOp`.
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

private theorem armDivDir_wp [Host] (isSigned : Bool) (w : RegWidth) (t ra rb : XReg) (s : MachineData) :
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
      (simp only [t_step_simp, Bool.false_eq_true, ↓reduceIte]; exact hk _ (by simp [RegWidth.bits, MemWidth.bits]))

private theorem armMsubDir_wp [Host] (w : RegWidth) (d t rb ra : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.MSUB (zr d w) (zr t w) (zr rb w) (zr ra w))]
      (fun s' => s' = wr s d (BitVec.setWidth 64
        ((s.regs.getXReg ra).toBitVec.setWidth w.bits -
         (s.regs.getXReg t).toBitVec.setWidth w.bits * (s.regs.getXReg rb).toBitVec.setWidth w.bits)))
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
  · have hlt := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h255 (Nat.pow_le_pow_right (by decide) (by omega : 8 ≤ i)))
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
  all_goals first | (exact (decide_eq_true (by omega)).symm) | (exact (decide_eq_false (by omega)).symm)

private theorem mask32_getLsbD {k : Nat} (hk : k < 32) :
    ((0x00FF00FF#32 : BitVec 32).getLsbD k = decide ((k / 8) % 2 = 0)) ∧
    ((0xFF00FF00#32 : BitVec 32).getLsbD k = decide ((k / 8) % 2 = 1)) ∧
    ((0x0000FFFF#32 : BitVec 32).getLsbD k = decide (k < 16)) ∧
    ((0xFFFF0000#32 : BitVec 32).getLsbD k = decide (16 ≤ k)) := by
  have hm1 : (0x00FF00FF#32 : BitVec 32) = BitVec.ofNat 32 255 <<< (8 * 0) ||| BitVec.ofNat 32 255 <<< (8 * 2) := rfl
  have hm2 : (0xFF00FF00#32 : BitVec 32) = BitVec.ofNat 32 255 <<< (8 * 1) ||| BitVec.ofNat 32 255 <<< (8 * 3) := rfl
  have hm3 : (0x0000FFFF#32 : BitVec 32) = BitVec.ofNat 32 255 <<< (8 * 0) ||| BitVec.ofNat 32 255 <<< (8 * 1) := rfl
  have hm4 : (0xFFFF0000#32 : BitVec 32) = BitVec.ofNat 32 255 <<< (8 * 2) ||| BitVec.ofNat 32 255 <<< (8 * 3) := rfl
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
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
    hj, decide_true, Bool.true_and]
  match hq : j / 8 with
  | 0 =>
    rw [decide_eq_true (by omega : j < 8), (mask32_getLsbD (by omega : 8 + j < 32)).2.1,
      decide_eq_true (by omega : (8 + j) / 8 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 1 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask32_getLsbD (by omega : j - 8 < 32)).1,
      (mask32_getLsbD (by omega : 8 + j < 32)).2.1, decide_eq_true (by omega : (j - 8) / 8 % 2 = 0),
      decide_eq_false (by omega : (8 + j) / 8 % 2 ≠ 1), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    simp
  | 2 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask32_getLsbD (by omega : j - 8 < 32)).1,
      (mask32_getLsbD (by omega : 8 + j < 32)).2.1, decide_eq_false (by omega : (j - 8) / 8 % 2 ≠ 0),
      decide_eq_true (by omega : (8 + j) / 8 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 3 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask32_getLsbD (by omega : j - 8 < 32)).1,
      BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ 8 + j),
      decide_eq_true (by omega : (j - 8) / 8 % 2 = 0), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    simp
  | _ + 4 => omega

private theorem bswap2_32 (v : BitVec 32) (j : Nat) (hj : j < 32) :
    (((v &&& 0x0000FFFF#32) <<< 16) ||| ((v &&& 0xFFFF0000#32) >>> 16)).getLsbD j =
      v.getLsbD (if j < 16 then j + 16 else j - 16) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
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
    ((((x &&& 0x00FF00FF00FF00FF#32) <<< 8) ||| ((x &&& 0xFF00FF00FF00FF00#32) >>> 8)).setWidth 16) =
      bswapBits (x.setWidth 16) := by
  change (((x &&& 0x00FF00FF#32) <<< 8 ||| (x &&& 0xFF00FF00#32) >>> 8).setWidth 16) = _
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, bswap1_32 x i (by omega), getLsbD_bswap (Or.inl rfl) _ hi, BitVec.getLsbD_setWidth,
    decide_eq_true hi, Bool.true_and]
  match hq : i / 8 with
  | 0 =>
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), show 8 * (16 / 8 - 1 - 0) + i % 8 = i + 8 by omega,
      decide_eq_true (by omega : i + 8 < 16), Bool.true_and]
  | 1 =>
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), show 8 * (16 / 8 - 1 - 1) + i % 8 = i - 8 by omega,
      decide_eq_true (by omega : i - 8 < 16), Bool.true_and]
  | _ + 2 => omega

private theorem bswap_rev_32 (x : BitVec 32) :
    let step1 := ((x &&& 0x00FF00FF#32) <<< 8) ||| ((x &&& 0xFF00FF00#32) >>> 8)
    (((step1 &&& 0x0000FFFF#32) <<< 16) ||| ((step1 &&& 0xFFFF0000#32) >>> 16)) = bswapBits x := by
  dsimp only; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [bswap2_32 _ i hi, bswap1_32 _ _ (by split <;> omega), getLsbD_bswap (Or.inr (Or.inl rfl)) _ hi]
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
  have hm1 : (0x00FF00FF00FF00FF#64 : BitVec 64) = BitVec.ofNat 64 255 <<< (8 * 0) ||| BitVec.ofNat 64 255 <<< (8 * 2) ||| BitVec.ofNat 64 255 <<< (8 * 4) ||| BitVec.ofNat 64 255 <<< (8 * 6) := rfl
  have hm2 : (0xFF00FF00FF00FF00#64 : BitVec 64) = BitVec.ofNat 64 255 <<< (8 * 1) ||| BitVec.ofNat 64 255 <<< (8 * 3) ||| BitVec.ofNat 64 255 <<< (8 * 5) ||| BitVec.ofNat 64 255 <<< (8 * 7) := rfl
  have hm3 : (0x0000FFFF0000FFFF#64 : BitVec 64) = BitVec.ofNat 64 255 <<< (8 * 0) ||| BitVec.ofNat 64 255 <<< (8 * 1) ||| BitVec.ofNat 64 255 <<< (8 * 4) ||| BitVec.ofNat 64 255 <<< (8 * 5) := rfl
  have hm4 : (0xFFFF0000FFFF0000#64 : BitVec 64) = BitVec.ofNat 64 255 <<< (8 * 2) ||| BitVec.ofNat 64 255 <<< (8 * 3) ||| BitVec.ofNat 64 255 <<< (8 * 6) ||| BitVec.ofNat 64 255 <<< (8 * 7) := rfl
  have hm5 : (0x00000000FFFFFFFF#64 : BitVec 64) = BitVec.ofNat 64 255 <<< (8 * 0) ||| BitVec.ofNat 64 255 <<< (8 * 1) ||| BitVec.ofNat 64 255 <<< (8 * 2) ||| BitVec.ofNat 64 255 <<< (8 * 3) := rfl
  have hm6 : (0xFFFFFFFF00000000#64 : BitVec 64) = BitVec.ofNat 64 255 <<< (8 * 4) ||| BitVec.ofNat 64 255 <<< (8 * 5) ||| BitVec.ofNat 64 255 <<< (8 * 6) ||| BitVec.ofNat 64 255 <<< (8 * 7) := rfl
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
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
    hj, decide_true, Bool.true_and]
  match hq : j / 8 with
  | 0 =>
    rw [decide_eq_true (by omega : j < 8), (mask64_getLsbD (by omega : 8 + j < 64)).2.1,
      decide_eq_true (by omega : (8 + j) / 8 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 1 | 3 | 5 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask64_getLsbD (by omega : j - 8 < 64)).1,
      (mask64_getLsbD (by omega : 8 + j < 64)).2.1, decide_eq_true (by omega : (j - 8) / 8 % 2 = 0),
      decide_eq_false (by omega : (8 + j) / 8 % 2 ≠ 1), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    simp
  | 2 | 4 | 6 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask64_getLsbD (by omega : j - 8 < 64)).1,
      (mask64_getLsbD (by omega : 8 + j < 64)).2.1, decide_eq_false (by omega : (j - 8) / 8 % 2 ≠ 0),
      decide_eq_true (by omega : (8 + j) / 8 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 7 =>
    rw [decide_eq_false (by omega : ¬(j < 8)), (mask64_getLsbD (by omega : j - 8 < 64)).1,
      BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 8 + j),
      decide_eq_true (by omega : (j - 8) / 8 % 2 = 0), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    simp
  | _ + 8 => omega

private theorem bswap2_64 (v : BitVec 64) (j : Nat) (hj : j < 64) :
    (((v &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((v &&& 0xFFFF0000FFFF0000#64) >>> 16)).getLsbD j =
      v.getLsbD (if (j / 16) % 2 = 0 then j + 16 else j - 16) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
    hj, decide_true, Bool.true_and]
  match hq : j / 16 with
  | 0 =>
    rw [decide_eq_true (by omega : j < 16), (mask64_getLsbD (by omega : 16 + j < 64)).2.2.2.1,
      decide_eq_true (by omega : (16 + j) / 16 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 1 =>
    rw [decide_eq_false (by omega : ¬(j < 16)), (mask64_getLsbD (by omega : j - 16 < 64)).2.2.1,
      (mask64_getLsbD (by omega : 16 + j < 64)).2.2.2.1, decide_eq_true (by omega : (j - 16) / 16 % 2 = 0),
      decide_eq_false (by omega : (16 + j) / 16 % 2 ≠ 1), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    simp
  | 2 =>
    rw [decide_eq_false (by omega : ¬(j < 16)), (mask64_getLsbD (by omega : j - 16 < 64)).2.2.1,
      (mask64_getLsbD (by omega : 16 + j < 64)).2.2.2.1, decide_eq_false (by omega : (j - 16) / 16 % 2 ≠ 0),
      decide_eq_true (by omega : (16 + j) / 16 % 2 = 1), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    simp; congr 1; omega
  | 3 =>
    rw [decide_eq_false (by omega : ¬(j < 16)), (mask64_getLsbD (by omega : j - 16 < 64)).2.2.1,
      BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 16 + j),
      decide_eq_true (by omega : (j - 16) / 16 % 2 = 0), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    simp
  | _ + 4 => omega

private theorem bswap3_64 (v : BitVec 64) (j : Nat) (hj : j < 64) :
    (((v &&& 0x00000000FFFFFFFF#64) <<< 32) ||| ((v &&& 0xFFFFFFFF00000000#64) >>> 32)).getLsbD j =
      v.getLsbD (if j < 32 then j + 32 else j - 32) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
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
    let step2 := ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
    (((step2 &&& 0x00000000FFFFFFFF#64) <<< 32) ||| ((step2 &&& 0xFFFFFFFF00000000#64) >>> 32)) = bswapBits x := by
  dsimp only; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [bswap3_64 _ i hi, bswap2_64 _ _ (by split <;> omega), bswap1_64 _ _ (by split <;> split <;> omega),
    getLsbD_bswap (Or.inr (Or.inr rfl)) _ hi]
  match hq : i / 8 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    split <;> (try split) <;> (try split) <;> first | omega | (congr 1; omega)
  | _ + 8 => omega

private theorem andi_bit0_mask {rc : BitVec 64} {b : Bool}
    (hb : rc.setWidth 8 = BitVec.ofNat 8 b.toNat) :
    rc.setWidth 32 &&& 1#32 = if b then 1#32 else 0#32 := by
  have hb0 := congrArg (fun z => z.getLsbD 0) hb
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hi0 : i = 0
  · subst hi0; simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth] at hb0 ⊢; cases b <;> simp_all <;> decide
  · have h0 : (1#32 : BitVec 32).getLsbD i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ i)))
    cases b <;> simp [BitVec.getLsbD_and, h0]

private theorem ne_of_tstBit0 {rc : BitVec 64} {b : Bool}
    (hb : rc.setWidth 8 = BitVec.ofNat 8 b.toNat) :
    CondCode.NE.interp (StatusFlags.from_result (rc.setWidth 32 &&& 1#32) { c := false, v := false }) = b := by
  rw [andi_bit0_mask hb]; cases b <;> decide

private theorem adds_carry_iff {n : Nat} (a b : BitVec n) :
    (StatusFlags.adds (a + b) a b).c = decide (2 ^ n ≤ a.toNat + b.toNat) := by
  have ha := a.isLt; have hb := b.isLt; have hp := Nat.two_pow_pos n
  simp only [StatusFlags.adds, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add]
  by_cases h : 2 ^ n ≤ a.toNat + b.toNat
  · have hm : (a.toNat + b.toNat) % 2 ^ n = a.toNat + b.toNat - 2 ^ n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [h, hm, decide_true, bne_iff_ne, ne_eq]; rw [Int.ofNat_sub h]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; simp [h]

private theorem adcs_carry_iff {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) (c : Bool) :
    (BitVec.unsigned (a + b + BitVec.ofNat n c.toNat) !=
      a.unsigned + b.unsigned + (if c = true then (1 : Int) else 0)) =
      decide (2 ^ n ≤ a.toNat + b.toNat + c.toNat) := by
  have h1 : 1 < 2 ^ n := by rcases hn with rfl | rfl <;> decide
  have ha := a.isLt; have hb := b.isLt
  have hc1 : c.toNat ≤ 1 := by cases c <;> decide
  have hc : c.toNat < 2 ^ n := by omega
  simp only [BitVec.unsigned, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  rw [Nat.mod_add_mod]
  by_cases h : 2 ^ n ≤ a.toNat + b.toNat + c.toNat
  · have hm : (a.toNat + b.toNat + c.toNat) % 2 ^ n = a.toNat + b.toNat + c.toNat - 2 ^ n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [h, hm, decide_true, bne_iff_ne, ne_eq]
    rw [Int.ofNat_sub h]
    cases c
    · rw [show false.toNat = 0 from rfl]; simp only [Nat.add_zero, ↓reduceIte, Bool.false_eq_true]; omega
    · rw [show true.toNat = 1 from rfl]; simp only [↓reduceIte]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; simp only [h, decide_false, bne_eq_false_iff_eq]
    cases c
    · rw [show false.toNat = 0 from rfl]; simp only [Nat.add_zero, ↓reduceIte, Bool.false_eq_true]; omega
    · rw [show true.toNat = 1 from rfl]; simp only [↓reduceIte]; omega

private theorem subs_borrow_iff {n : Nat} (a b : BitVec n) :
    (!(StatusFlags.subs (a - b) a b).c) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt; have hp := Nat.two_pow_pos n
  simp only [StatusFlags.subs, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · rw [Nat.mod_eq_of_lt (by omega)]; simp only [h, decide_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    rw [show ((2 ^ n - b.toNat + a.toNat : Nat) : Int) = (2 ^ n : Nat) - (b.toNat : Int) + (a.toNat : Int) by omega]
    omega
  · have hm : 2 ^ n - b.toNat + a.toNat = 2 ^ n + (a.toNat - b.toNat) := by omega
    rw [hm, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp only [h, decide_false, Bool.not_eq_false', beq_iff_eq]
    rw [Int.ofNat_sub (by omega : b.toNat ≤ a.toNat)]

private theorem sbcs_borrow_iff {n : Nat} (a b : BitVec n) (cflag : Bool) :
    (!decide ((a.unsigned : Int) ≥ b.unsigned + (if cflag = true then 0 else 1))) =
      decide (a.toNat < b.toNat + (!cflag).toNat) := by
  dsimp only [BitVec.unsigned]
  cases cflag
  · change (!decide ((a.toNat : Int) ≥ (b.toNat : Int) + 1)) = decide (a.toNat < b.toNat + 1)
    by_cases h : a.toNat < b.toNat + 1
    · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false h]; rfl
  · change (!decide ((a.toNat : Int) ≥ (b.toNat : Int) + 0)) = decide (a.toNat < b.toNat + 0)
    by_cases h : a.toNat < b.toNat + 0
    · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false h]; rfl

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
          have hxb : xb ≠ .X17 := (xreg_ne_scratch_of_not_mem (hgb (.reg xb) (by simp [PArg.gprs]))).2
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
      refine armScratch_cons htmem hd₂ hfr₂ (armDivDir_wp isSigned .W32 t ra rb s₂) fun s₃ hs₃ hd₃ hfr₃ => ?_
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
      refine armScratch_cons htmem hd₂ hfr₂ (armDivDir_wp isSigned .W64 t ra rb s₂) fun s₃ hs₃ hd₃ hfr₃ => ?_
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
        armMach.mem s' = armMach.mem s ∧ armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone)
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
  refine armScratch_cons x16_mem_scratch hd₂ hfr₂ (armExt32_wp isSigned hn0 hnw32 .X16 ra s₂ va hra) fun s₂' hs₂' hd₂' hfr₂' => ?_
  have hrb' : (s₂'.regs.getXReg rb).toBitVec.setWidth n = vb := by
    rw [hs₂', Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm]; exact hrb
  refine armScratch_cons x17_mem_scratch hd₂' hfr₂' (armExt32_wp isSigned hn0 hnw32 .X17 rb s₂' vb hrb') fun s₃ hs₃ hd₃ hfr₃ => ?_
  have h16₃ : (s₃.regs.getXReg .X16).toBitVec.setWidth 32 = if isSigned then va.signExtend 32 else va.setWidth 32 := by
    rw [hs₃, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide), hs₂']
    simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have h17₃ : (s₃.regs.getXReg .X17).toBitVec.setWidth 32 = if isSigned then vb.signExtend 32 else vb.setWidth 32 := by
    rw [hs₃]; simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  cases isRem
  · rw [show (emitClean post : List Directive) =
        [if isSigned then ins (.SDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))
         else ins (.UDIV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))] by
      cases isSigned <;> rfl]
    refine armWrDst_after_scratch hn64 d (armDivDir_wp isSigned .W32 d .X16 .X17 s₃) hd₃ hfr₃ ?_
      (fun h => absurd h hn32)
    simp only [RegWidth.bits, MemWidth.bits, h16₃, h17₃, BitVec.setWidth_setWidth_of_le _ hn64, target]
    by_cases hvb0 : vb = 0
    · subst hvb0
      cases isSigned <;> (rcases hn' with rfl | rfl <;> rfl)
    · have hne32 : (if isSigned then vb.signExtend 32 else vb.setWidth 32) ≠ 0 := by
        cases isSigned; exact setWidth32_ne_zero hnw32 hvb0; exact signExtend32_ne_zero hnw32 hvb0
      rw [beq_false_of_ne hvb0]
      cases isSigned
      · simp only [Bool.false_eq_true, ↓reduceIte] at hne32 ⊢; rw [beq_false_of_ne hne32]; exact udiv_subword_32 hn' va vb
      · simp only [↓reduceIte] at hne32 ⊢; rw [beq_false_of_ne hne32]; exact sdiv_subword_32 hn' va vb
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
    have hs₅' : s₅ = wr s₃ d (BitVec.setWidth 64 ((if isSigned then va.signExtend 32 else va.setWidth 32) -
        (if isSigned then (va.signExtend 32).sdiv (vb.signExtend 32) else va.setWidth 32 / vb.setWidth 32) *
        (if isSigned then vb.signExtend 32 else vb.setWidth 32))) := by
      rw [hs₅, hs₄]; simp only [wr_wr_same, RegWidth.bits, MemWidth.bits,
        Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
        Reg64s.getXReg_setXReg_of_ne s₃.regs d .X16 _ hd16, Reg64s.getXReg_setXReg_of_ne s₃.regs d .X17 _ hd17,
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
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [← umod_eq_sub]; exact urem_subword_32 hn' va vb
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
              else (if vb == 0 then 0 else if isSigned then va.sdiv vb else va / vb)) = armDivEval k va vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (armDivEval k va vb) ∧
      armMach.mem s' = armMach.mem s ∧ armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only at hk; split at hk
  · simp at hk
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    split at hk
    · rename_i hn3264
      have hn' : n = 32 ∨ n = 64 := by simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
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
          cases isRem <;> simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at htail <;>
            rcases htail with ⟨rfl, rfl⟩ <;>
            exact armWp_mono (armDiv3264_fallback_wp isSigned _ hn' _ _ d ha hb (fun _ _ _ h => by cases h) hga hgb hpa hpb hrem')
              fun s' ⟨hg, hm, hfr⟩ => ⟨heval ▸ hg, hm, hfr⟩
      | gpr _ => cases pb with
        | vec vr => exact vr.elim
        | gpr _ | imm _ =>
          simp only [bind, Option.bind_eq_some_iff] at hk
          rcases hk with ⟨⟨ca', ra⟩, ha, ⟨cb', rb⟩, hb, htail⟩
          cases isRem <;> simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at htail <;>
            rcases htail with ⟨rfl, rfl⟩ <;>
            exact armWp_mono (armDiv3264_fallback_wp isSigned _ hn' _ _ d ha hb (fun _ _ h _ => by cases h) hga hgb hpa hpb hrem')
              fun s' ⟨hg, hm, hfr⟩ => ⟨heval ▸ hg, hm, hfr⟩
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      simp only [bind, Option.bind_eq_some_iff] at hk
      rcases hk with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, htail⟩
      cases isRem <;> simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at htail <;>
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
      hfr₁.weaken (fun x hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact x16_mem_scratch)
        (fun v => v.elim) rfl
    rcases hn' with rfl | rfl | rfl
    · simp only [show (16 == 16) = true from rfl, ↓reduceIte]
      refine armWrDst_after_scratch (by decide) d (armDirFallsTo_wp (Q := fun s' => s' = wr s₁ d (BitVec.setWidth 64
        ((((s₁.regs.getXReg ra).toBitVec.setWidth 32 &&& 0x00FF00FF00FF00FF#32) <<< 8) |||
         (((s₁.regs.getXReg ra).toBitVec.setWidth 32 &&& 0xFF00FF00FF00FF00#32) >>> 8)))) fun {_} p next jmp Q hk => by
        simp only [t_step_simp]; exact hk _ rfl) hd₁ hfr₁' ?_ (fun h => by cases h)
      rw [BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 64), bswap_rev16_32,
        BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 32), hra]
    · simp only [show (32 == 16) = false from rfl, show (32 == 32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
      refine armWrDst_after_scratch (by decide) d (armDirFallsTo_wp (Q := fun s' => s' = wr s₁ d (BitVec.setWidth 64 (bswapBits va)))
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp] at hra ⊢; rw [hra, bswap_rev_32]; exact hk _ rfl) hd₁ hfr₁'
        (by rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq])
        (fun _ => rfl)
    · simp only [show (64 == 16) = false from rfl, show (64 == 32) = false from rfl, Bool.false_eq_true, ↓reduceIte]
      refine armWrDst_after_scratch (by decide) d (armDirFallsTo_wp (Q := fun s' => s' = wr s₁ d (bswapBits va))
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

theorem armBitOp_wp [Host] (k : ArmBitK) {n : Nat} (pa : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
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
      hfr₁.weaken (fun x hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact x16_mem_scratch)
        (fun v => v.elim) rfl
    have step1 : ∀ (w : RegWidth) (hnw : n = w.bits) (hra' : (s₁.regs.getXReg ra).toBitVec.setWidth w.bits = hnw ▸ va),
        _root_.Program.wp (emitClean (armBitCodeI k w d ra)) (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n (armBitEval k va) ∧
          armMach.mem s' = armMach.mem s ∧ armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone)
          (fun _ _ => False) s₁ := by
      intro w hnw hra'; subst hnw
      rw [show emitClean (armBitCodeI k w d ra) = armBitCode k w d ra by cases k <;> rfl]
      cases k
      · refine armWrDst_after_scratch hn64 d (armDirFallsTo_wp (Q := fun s' => s' = wr s₁ d (va.clz.setWidth 64))
          fun {_} p next jmp Q hk => by
            dsimp only [armBitCode, ins]; cases w <;> (simp only [t_step_simp, BitVec.setWidth_eq] at hra' ⊢; rw [hra']; exact hk _ rfl))
          hd₁ hfr₁' (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
          (fun _ => rfl)
      · refine armWrDst_after_scratch hn64 d (armDirFallsTo_wp (Q := fun s' => s' = wr s₁ d ((armBitEval .cls va).setWidth 64))
          fun {_} p next jmp Q hk => by
            dsimp only [armBitCode, ins]; cases w <;> (simp only [t_step_simp, BitVec.setWidth_eq] at hra' ⊢; rw [hra']; exact hk _ rfl))
          hd₁ hfr₁' (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
          (fun _ => rfl)
      · refine armWrDst_after_scratch hn64 d (armDirFallsTo_wp (Q := fun s' => s' = wr s₁ d (va.reverse.setWidth 64))
          fun {_} p next jmp Q hk => by
            dsimp only [armBitCode, ins]; cases w <;> (simp only [t_step_simp, BitVec.setWidth_eq] at hra' ⊢; rw [hra']; exact hk _ rfl))
          hd₁ hfr₁' (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq])
          (fun _ => rfl)
      · refine armWp_cons (armDirFallsTo_wp (Q := fun s' => s' = wr s₁ d (va.reverse.setWidth 64))
          fun {_} p next jmp Q hk => by
            dsimp only [armBitCode, ins]; cases w <;> (simp only [t_step_simp, BitVec.setWidth_eq] at hra' ⊢; rw [hra']; exact hk _ rfl))
          fun s₂ hs₂ => ?_
        subst hs₂
        refine armWp_mono (armDirFallsTo_wp (Q := fun s' => s' = wr (wr s₁ d (va.reverse.setWidth 64)) d (va.reverse.clz.setWidth 64))
          fun {_} p next jmp Q hk => by
            cases w
            · simp only [t_step_simp, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
                BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
              exact hk _ rfl
            · simp only [t_step_simp, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, BitVec.setWidth_eq]
              exact hk _ rfl)
          fun s₃ hs₃ => ?_
        rw [hs₃, wr_wr_same]
        refine ⟨⟨⟨hn64, ?_⟩, fun hn32 => by
          cases w
          · dsimp only [armBitEval]
            exact get_wr_same s₁ d _
          · simp [RegWidth.bits, MemWidth.bits] at hn32⟩, hd₁,
          armFrame_scratch_wr hfr₁' (frame_wr d _ List.mem_cons_self maskNone)⟩
        rw [show armMach.getGpr (wr s₁ d (va.reverse.clz.setWidth 64)) (.reg d) = get (wr s₁ d (va.reverse.clz.setWidth 64)) (.reg d) from rfl,
          get_wr_same, BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]
    rcases hn' with rfl | rfl
    · exact step1 .W32 rfl hra
    · exact step1 .W64 rfl (by simpa [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq] using hra)

private theorem armSubsImm_wp [Host] {n : Nat} (hn : n ≤ 64) (w : RegWidth) (rx : XReg)
    (imm : BitVec n) (ei : ExtOrImmReg) (hei : armImm12? imm = some ei) (s : MachineData) :
    _root_.Program.wp [ins (.SUBS_e (xzr w) (.low (.reg rx) w) ei)]
      (fun s' => s' = { s with status := StatusFlags.subs ((s.regs.getXReg rx).toBitVec.setWidth w.bits - imm.setWidth w.bits) ((s.regs.getXReg rx).toBitVec.setWidth w.bits) (imm.setWidth w.bits) })
      (fun _ _ => False) s := by
  refine armDirFallsTo_wp fun {_} p next jmp Q hk => ?_
  have himm := armImm12_some hn hei w p s.regs
  dsimp only [ExtOrImmReg.interp] at himm
  cases w <;>
    (simp only [t_step_simp, Reg64s.setRegOrZr_xzr] at himm ⊢
     rw [himm]
     exact hk _ (by simp [RegWidth.bits, MemWidth.bits]))

theorem armCmpOp_wp [Host] (o : CmpOp) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dst : PDst Reg Empty ArmCond .bool)
    {va vb : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armCmpOpIns o n pa pb dst = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (_hd : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst (o.evalBits va vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  dsimp only [armCmpOpIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have finishSpec : ∀ {cmpCode : List Instr} {cond s'},
        _root_.Program.wp (emitClean cmpCode)
          (fun sx => cond.interp sx.status = o.evalBits va vb ∧ sx.dmem = s.dmem ∧
            armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s' →
        (match dst with
          | .flag cf => if cf == cond then some (cmpCode, maskNZCV) else none
          | .gpr (.reg d) => some (cmpCode ++ [armCset64I d cond], maskNZCV)
          | .gpr .SP | .vec _ => none) = some (c, clob) →
        _root_.Program.wp (emitClean c)
          (fun sy => armMach.PDstHolds sy .bool dst (o.evalBits va vb) ∧
          armMach.mem sy = armMach.mem s ∧
          armMach.Frame armCondReads s sy (tupDstGprs (ts := [.bool]) (dst, ()) ++ armScratch) [] clob)
          (fun _ _ => False) s' := by
      intro cmpCode cond s' hcmp hfin
      cases dst with
      | vec vr => exact vr.elim
      | flag cf =>
        dsimp only at hfin; split at hfin
        · rename_i heq; simp only [beq_iff_eq] at heq; subst heq; rcases Option.some.inj hfin with ⟨rfl, rfl⟩
          exact armWp_mono hcmp fun _ ⟨hcc, hdm, hfr⟩ => ⟨hcc, hdm, hfr⟩
        · cases hfin
      | gpr r => cases r with | SP => cases hfin | reg d =>
        rcases Option.some.inj hfin with ⟨rfl, rfl⟩
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append hcmp ?_; rintro sx ⟨hcc, hdm, hfr⟩
        refine armWp_mono (armCset64_wp d cond sx) ?_; rintro sy rfl
        refine ⟨?_, hdm, armFrame_nzcv fun r hr => ?_⟩
        · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hcc]; cases o.evalBits va vb <;> rfl
        · have hne : r ≠ .reg d ∧ r ∉ armScratch := ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
          rw [get_wr_of_ne sx d _ r hne.1]; exact hfr.1 r hne.2
    split at hc
    · rename_i hn3264
      have hn' : n = 32 ∨ n = 64 := by simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
      have fallback : ∀ {ca ra cb rb},
          armArgInIns .X16 pa = some (ca, ra) → armArgInIns .X17 pb = some (cb, rb) →
          _root_.Program.wp (emitClean (ca ++ cb ++
            [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb))]))
            (fun sx => (armCmpCond o).interp sx.status = o.evalBits va vb ∧ sx.dmem = s.dmem ∧
              armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s := by
        intro ca ra cb rb ha hb
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
        rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
        rcases hn' with rfl | rfl
        · rw [show armWidthOf 32 = .W32 from rfl]
          refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp (Q := fun s' =>
              s' = { s₂ with status := StatusFlags.subs (va - vb) va vb }) fun {_} p next jmp Q hk => by
            simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero]
            rw [hra, hrb]; exact hk _ rfl) hd₂ hfr₂) ?_
          rintro s₃ ⟨_, hst₃, hdm₃, hfr₃⟩; exact ⟨hst₃ ▸ armCmpCond_subs (Or.inl rfl) o va vb, hdm₃, hfr₃⟩
        · rw [show armWidthOf 64 = .W64 from rfl]
          refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp (Q := fun s' =>
              s' = { s₂ with status := StatusFlags.subs (va - vb) va vb }) fun {_} p next jmp Q hk => by
            simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
              BitVec.shiftLeft_zero, BitVec.setWidth_eq] at hra hrb ⊢
            rw [hra, hrb]; exact hk _ rfl) hd₂ hfr₂) ?_
          rintro s₃ ⟨_, hst₃, hdm₃, hfr₃⟩; exact ⟨hst₃ ▸ armCmpCond_subs (Or.inr rfl) o va vb, hdm₃, hfr₃⟩
      cases pa with
      | vec vr => exact vr.elim
      | gpr r => cases r with
        | SP => dsimp only at hc; simp [armArgInIns] at hc
        | reg ra => cases pb with
          | vec vr => exact vr.elim
          | gpr _ =>
            dsimp only at hc; simp only [bind, Option.bind_eq_some_iff] at hc
            rcases hc with ⟨⟨_, _⟩, ha, ⟨_, _⟩, hb, hfin⟩; exact finishSpec (fallback ha hb) hfin
          | imm cb =>
            dsimp only at hc
            rcases option_none_or_some (armImm12? cb) with hnone | ⟨ei, hei⟩
            · simp only [hnone, bind, Option.bind_eq_some_iff] at hc
              rcases hc with ⟨⟨_, _⟩, hb, hfin⟩; exact finishSpec (fallback (ca := []) (ra := ra) rfl hb) hfin
            · simp only [hei] at hc
              have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
                simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
              refine finishSpec
                (cmpCode := [armIselInsI (.SUBS_e (xzr (armWidthOf n))
                  (.low (.reg ra) (armWidthOf n)) ei)])
                (armWp_mono (armSubsImm_wp hn64 (armWidthOf n) ra cb ei hei s) ?_) hc
              rintro s₁ rfl; refine ⟨?_, rfl, armFrame_nzcv fun _ _ => rfl⟩
              rcases hn' with rfl | rfl
              · rw [show armWidthOf 32 = .W32 from rfl]; dsimp only [RegWidth.bits, MemWidth.bits]; simp only [BitVec.setWidth_eq] at hpb ⊢; rw [hra, hpb]; exact armCmpCond_subs (Or.inl rfl) o va vb
              · rw [show armWidthOf 64 = .W64 from rfl]; dsimp only [RegWidth.bits, MemWidth.bits]; simp only [BitVec.setWidth_eq] at hra hpb ⊢; rw [hra, hpb]; exact armCmpCond_subs (Or.inr rfl) o va vb
      | imm ca => cases pb with
        | vec vr => exact vr.elim
        | imm _ =>
          dsimp only at hc; simp only [bind, Option.bind_eq_some_iff] at hc
          rcases hc with ⟨⟨_, _⟩, ha, ⟨_, _⟩, hb, hfin⟩; exact finishSpec (fallback ha hb) hfin
        | gpr r => cases r with
          | SP => dsimp only at hc; simp [armArgInIns] at hc
          | reg rb =>
            dsimp only at hc
            rcases option_none_or_some (armImm12? ca) with hnone | ⟨ei, hei⟩
            · simp only [hnone, bind, Option.bind_eq_some_iff] at hc
              rcases hc with ⟨⟨_, _⟩, ha, hfin⟩
              have hfb := fallback (cb := []) (rb := rb) ha rfl
              rw [List.append_nil] at hfb
              exact finishSpec hfb hfin
            · simp only [hei] at hc
              have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
                simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
              refine finishSpec
                (cmpCode := [armIselInsI (.SUBS_e (xzr (armWidthOf n))
                  (.low (.reg rb) (armWidthOf n)) ei)])
                (armWp_mono (armSubsImm_wp hn64 (armWidthOf n) rb ca ei hei s) ?_) hc
              rintro s₁ rfl; refine ⟨?_, rfl, armFrame_nzcv fun _ _ => rfl⟩
              rcases hn' with rfl | rfl
              · rw [show armWidthOf 32 = .W32 from rfl]
                dsimp only [RegWidth.bits, MemWidth.bits]
                simp only [BitVec.setWidth_eq] at hpa ⊢
                rw [hrb, hpa, armCmpCond_subs (Or.inl rfl), CmpOp.swap_evalBits]
              · rw [show armWidthOf 64 = .W64 from rfl]
                dsimp only [RegWidth.bits, MemWidth.bits]
                simp only [BitVec.setWidth_eq] at hrb hpa ⊢
                rw [hrb, hpa, armCmpCond_subs (Or.inr rfl), CmpOp.swap_evalBits]
    · rename_i hn816
      have hn' : n = 8 ∨ n = 16 := by rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
      have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
      have hnw32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
      simp only [bind, Option.bind_eq_some_iff] at hc
      rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, hfin⟩
      have hcmp32 : _root_.Program.wp
          (emitClean (ca ++ cb ++ [armExt32I (armIsSignedCmp o) n .X16 ra,
            armExt32I (armIsSignedCmp o) n .X17 rb,
            armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]))
          (fun sx => (armCmpCond o).interp sx.status = o.evalBits va vb ∧ sx.dmem = s.dmem ∧
            armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s := by
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
          rw [hs₃]; simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
        refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
            BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, h16₃, h17₃]; exact hk _ rfl) hd₃ hfr₃) ?_
        rintro s₄ ⟨_, hst₄, hdm₄, hfr₄⟩
        refine ⟨?_, hdm₄, hfr₄⟩; rw [hst₄, armCmpCond_subs (Or.inl rfl)]
        cases hsgn : armIsSignedCmp o
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact cmp_subword_unsigned hn' o hsgn va vb
        · simp only [↓reduceIte]; exact cmp_subword_signed hn' o hsgn va vb
      exact finishSpec hcmp32 hfin

theorem armSelectOp_wp [Host] {n : Nat}
    (pc : PArg Reg Empty ArmCond .bool) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {vc : Bool} {va vb : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armSelectOpIns n pc pa pb d = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hgc : ∀ r ∈ pc.gprs, r ∉ armScratch) (hpc : armMach.PArgHolds s .bool pc vc)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armSelectOpIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hnw := mem_armWidths_le_armWidth hn
    cases pc with
    | vec vr => exact vr.elim
    | imm bv =>
      simp only [Machine.PArgHolds] at hpc; subst hpc
      cases bv
      · simpa using armCopyBits_wp hn d hc hpb
      · simpa using armCopyBits_wp hn d hc hpa
    | flag cond =>
      dsimp only at hc; simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl, rfl⟩
      simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
      refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
      rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂⟩
      simp only [emitClean_cons, emitClean_nil]
      refine armWrDst_after_scratch hn64 d
        (armCselDir_wp (armWidthOf n) d ra rb cond.toKraken s₂) hd₂ hfr₂ ?_ ?_
      · rw [show cond.toKraken.interp s₂.status = vc from hst₂ ▸ hpc]
        cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, BitVec.setWidth_setWidth_of_le _ hn64]
        · rw [BitVec.setWidth_setWidth_of_le _ hnw, hrb]
        · rw [BitVec.setWidth_setWidth_of_le _ hnw, hra]
      · intro hn32; subst hn32
        rw [show cond.toKraken.interp s₂.status = vc from hst₂ ▸ hpc,
          show (armWidthOf 32).bits = 32 from rfl]
        cases vc <;> simp only [↓reduceIte, Bool.false_eq_true]
        · rw [hrb]
        · rw [hra]
    | gpr r => cases r with | SP => simp at hc | reg rc =>
      dsimp only at hc; simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl, rfl⟩
      have hrc : (s.regs.getXReg rc).toBitVec.setWidth 8 = BitVec.ofNat 8 vc.toNat := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hpc
      have ⟨hrc16, hrc17⟩ := xreg_ne_scratch_of_not_mem (hgc (.reg rc) (by simp [PArg.gprs]))
      simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
      refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
      rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
      simp only [emitClean_cons, emitClean_nil]
      have hrc₂ : (s₂.regs.getXReg rc).toBitVec.setWidth 8 = BitVec.ofNat 8 vc.toNat := by
        have h := hfr₂.1 (.reg rc) (by simp [armScratch, hrc16, hrc17])
        simpa [get_reg] using (congrArg (BitVec.setWidth 8) h).trans hrc
      let st2 := StatusFlags.from_result ((s₂.regs.getXReg rc).toBitVec.setWidth 32 &&& 1#32) { c := false, v := false }
      refine armWp_cons (armStatusScratch_after (armDirFallsTo_wp (Q := fun s' => s' = { s₂ with status := st2 })
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_one, RegWidth.bits, MemWidth.bits]
          exact hk _ rfl) hd₂ hfr₂) fun s₃ ⟨hregs₃, hst₃, hd₃, hfr₃⟩ => ?_
      refine armWp_mono (armCselDir_wp (armWidthOf n) d ra rb .NE s₃) fun s₄ hs₄ => ?_
      have hs₄' : s₄ = wr s₃ d ((if vc then (s₂.regs.getXReg ra).toBitVec.setWidth (armWidthOf n).bits
          else (s₂.regs.getXReg rb).toBitVec.setWidth (armWidthOf n).bits).setWidth 64) := by
        rw [hs₄, hst₃, ne_of_tstBit0 hrc₂, hregs₃]
      rw [hs₄']
      refine ⟨⟨⟨hn64, ?_⟩, fun hn32 => ?_⟩, hd₃, armFrame_nzcv fun r hr => ?_⟩
      · rw [get_wr_same, BitVec.setWidth_setWidth_of_le _ hn64]
        cases vc
        · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_setWidth_of_le _ hnw]; exact hrb
        · simp only [↓reduceIte, BitVec.setWidth_setWidth_of_le _ hnw]; exact hra
      · subst hn32
        rw [get_wr_same, show (armWidthOf 32).bits = 32 from rfl]
        cases vc <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · rw [hrb]
        · rw [hra]
      · have hne : r ≠ .reg d ∧ r ∉ armScratch := ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
        rw [get_wr_of_ne s₃ d _ r hne.1, show get s₃ r = get s₂ r from by dsimp only [get]; rw [hregs₃]]
        exact hfr₂.1 r hne.2

private theorem armAndi1Sub_wp [Host] (isSubb : Bool) (rc : XReg) {b : Bool} {s : MachineData}
    (hb : (s.regs.getXReg rc).toBitVec.setWidth 8 = BitVec.ofNat 8 b.toNat) (_hrc16 : rc ≠ .X16) :
    _root_.Program.wp
      [ins (.AND_i (.low (.reg .X16) .W32) (zr rc .W32) (.int64 1)),
       if isSubb then ins (.SUBS_s (xzr .W32) (xzr .W32) (sh .X16))
       else ins (.SUBS_e (xzr .W32) (.low (.reg .X16) .W32) (.imm { imm := .int64 1, shift := .S0 }))]
      (fun s₁ => (∀ r, r ∉ armScratch → get s₁ r = get s r) ∧ s₁.dmem = s.dmem ∧
        (if isSubb then ((!s₁.status.c) = b) else (s₁.status.c = b))) (fun _ _ => False) s := by
  refine armWp_cons (armDirFallsTo_wp (Q := fun s' =>
      s' = wr s .X16 (((s.regs.getXReg rc).toBitVec.setWidth 32 &&& 1#32).setWidth 64))
    fun {_} p next jmp Q hk => by simp only [t_step_simp, Int64.toInt_one, RegWidth.bits, MemWidth.bits]; exact hk _ rfl)
    fun s₀ hs₀ => ?_
  have hw16 : (s₀.regs.getXReg .X16).toBitVec.setWidth 32 = if b then 1#32 else 0#32 := by
    rw [hs₀]; simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
    exact andi_bit0_mask hb
  have hkeep0 : ∀ r, r ∉ armScratch → get s₀ r = get s r := fun r hr => by
    rw [hs₀]; exact get_wr_of_ne s .X16 _ r (ne_of_not_mem_armScratch hr).1
  cases isSubb
  · let st0 := StatusFlags.subs (BitVec.setWidth 32 (s₀.regs.getXReg .X16).toBitVec - 1#32)
      (BitVec.setWidth 32 (s₀.regs.getXReg .X16).toBitVec) 1#32
    refine armWp_mono (armDirFallsTo_wp (d := ins (.SUBS_e (xzr .W32) (.low (.reg .X16) .W32) (.imm { imm := .int64 1, shift := .S0 })))
      (Q := fun s' => s' = { s₀ with status := st0 })
      fun {_} p next jmp Q hk => by
        simp only [t_step_simp, Int64.toInt_one, RegWidth.bits, MemWidth.bits]
        dsimp only [xzr]; exact hk _ rfl) ?_
    rintro s₁ rfl; refine ⟨hkeep0, by rw [hs₀], ?_⟩; simp only [st0, hw16]; cases b <;> decide
  · let st1 := StatusFlags.subs (0#32 - BitVec.setWidth 32 (s₀.regs.getXReg .X16).toBitVec)
      0#32 (BitVec.setWidth 32 (s₀.regs.getXReg .X16).toBitVec)
    refine armWp_mono (armDirFallsTo_wp (d := ins (.SUBS_s (xzr .W32) (xzr .W32) (sh .X16)))
      (Q := fun s' => s' = { s₀ with status := st1 })
      fun {_} p next jmp Q hk => by
        simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
          BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits]
        dsimp only [xzr]; exact hk _ rfl) ?_
    rintro s₁ rfl; refine ⟨hkeep0, by rw [hs₀], ?_⟩; simp only [st1, hw16]; cases b <;> decide

private theorem armCarryFinish_wp [Host] {n : Nat} (hn : n = 32 ∨ n = 64)
    (res : BitVec n) (cflag : Bool) (d : XReg) (cout : PDst Reg Empty ArmCond .bool)
    (flagCond : ArmCond) (s s₃ : MachineData) (post : List Directive)
    (hp : (cout = .flag flagCond ∧ post = []) ∨
      (∃ dc, dc ≠ d ∧ cout = .gpr (.reg dc) ∧ post = [armCset64 dc flagCond]))
    (hres : (s₃.regs.getXReg d).toBitVec.setWidth n = res) (hflag : flagCond.interp s₃.status = cflag)
    (hdm : s₃.dmem = s.dmem) (hkeep : ∀ r, r ∉ (.reg d :: armScratch) → get s₃ r = get s r) :
    _root_.Program.wp post (fun s' =>
      (∃ rvs : Tup Val [.bits n, .bool], rvs = (res, cflag, ()) ∧
        TRel (armMach.PDstHolds s') (as := [.bits n, .bool]) ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout, ()) rvs) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s'
        (tupDstGprs (ts := [.bits n, .bool]) ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout, ()) ++ armScratch)
        [] maskNZCV) (fun _ _ => False) s₃ := by
  have hn64 : n ≤ 64 := by rcases hn with rfl | rfl <;> decide
  rcases hp with ⟨rfl, rfl⟩ | ⟨dc, hdc, rfl, rfl⟩
  · exact armWp_nil ⟨⟨(res, cflag, ()), rfl, .cons ⟨hn64, by simpa [get_reg] using hres⟩ (.cons hflag .nil)⟩, hdm, armFrame_nzcv hkeep⟩
  · refine armWp_mono (armCset64_wp dc flagCond s₃) ?_; rintro s₄ rfl
    refine ⟨⟨(res, cflag, ()), rfl, .cons ?_ (.cons ?_ .nil)⟩, hdm, armFrame_nzcv fun r hr => ?_⟩
    · refine ⟨hn64, ?_⟩
      dsimp only [armMach, get_reg]
      rw [Reg64s.getXReg_setXReg_of_ne s₃.regs dc d _ hdc]
      exact hres
    · change GprHolds (get (wr s₃ dc (BitVec.ofNat 64 (flagCond.interp s₃.status).toNat)) (.reg dc)) .bool cflag
      rw [GprHolds, get_wr_same, hflag]; cases cflag <;> rfl
    · have hne : r ≠ .reg d ∧ r ≠ .reg dc ∧ r ∉ armScratch := by
        simpa [tupDstGprs, armScratch] using hr
      rw [get_wr_of_ne s₃ dc _ r hne.2.1]
      exact hkeep r (fun hm => by
        simp only [List.mem_cons] at hm; rcases hm with rfl | hm; exact hne.1 rfl
        exact hne.2.2 (by simpa [armScratch] using hm))

private theorem armCarryOp_wp [Host] (isSub : Bool) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (cin : PArg Reg Empty ArmCond .bool)
    (d : XReg) (cout : PDst Reg Empty ArmCond .bool) (vh : VariantHint)
    {va vb : BitVec n} {vcin : Bool} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : (if isSub then armSubbOpIns n pa pb cin d cout vh
           else armAddcOpIns n pa pb cin d cout vh) = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hgc : ∀ r ∈ cin.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hpc : armMach.PArgHolds s .bool cin vcin) :
    _root_.Program.wp (emitClean c) (fun s' =>
      (∃ rvs : Tup Val [.bits n, .bool],
        rvs = (if isSub then va - vb - BitVec.ofNat n vcin.toNat
               else va + vb + BitVec.ofNat n vcin.toNat,
          if isSub then decide (va.toNat < vb.toNat + vcin.toNat)
          else decide (2 ^ n ≤ va.toNat + vb.toNat + vcin.toNat), ()) ∧
        TRel (armMach.PDstHolds s') (as := [.bits n, .bool])
          ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout, ()) rvs) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s'
        (tupDstGprs (ts := [.bits n, .bool])
          ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout, ()) ++ armScratch)
        [] clob) (fun _ _ => False) s := by
  let flagCond : ArmCond := if isSub then .cc else .cs
  let res : BitVec n :=
    if isSub then va - vb - BitVec.ofNat n vcin.toNat
    else va + vb + BitVec.ofNat n vcin.toNat
  let cflag : Bool :=
    if isSub then decide (va.toNat < vb.toNat + vcin.toNat)
    else decide (2 ^ n ≤ va.toNat + vb.toNat + vcin.toNat)
  have hunpack : ∃ (hn' : n = 32 ∨ n = 64) (post ca : List Instr) (ra : XReg)
      (cb : List Instr) (rb : XReg) (m : List Instr),
      armArgInIns .X16 pa = some (ca, ra) ∧
      armArgInIns .X17 pb = some (cb, rb) ∧
      ((cout = .flag flagCond ∧ post = []) ∨
        (∃ dc, dc ≠ d ∧ cout = .gpr (.reg dc) ∧ post = [armCset64I dc flagCond])) ∧
      (match cin with
       | .flag cf => cf = flagCond ∧ m = ca ++ cb ++ [armIselInsI (if isSub
           then .SBCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n))
           else .ADCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))]
       | .imm false => m = ca ++ cb ++ [armIselInsI (if isSub
           then .SUBS_s (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb)
           else .ADDS_s (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb))]
       | .imm true => m = [armIselInsI (if isSub
           then .ADDS_s (xzr .W32) (xzr .W32) { reg := xzr .W32, amount := 0, shift := .LSL }
           else .SUBS_s (xzr .W32) (xzr .W32) { reg := xzr .W32, amount := 0, shift := .LSL })] ++
           ca ++ cb ++ [armIselInsI (if isSub
           then .SBCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n))
           else .ADCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))]
       | .gpr (.reg rc) =>
           m = [armIselInsI (.AND_i (.low (.reg .X16) .W32) (zr rc .W32) (.int64 1)),
           armIselInsI (if isSub then .SUBS_s (xzr .W32) (xzr .W32) (sh .X16)
             else .SUBS_e (xzr .W32) (.low (.reg .X16) .W32)
               (.imm { imm := .int64 1, shift := .S0 }))] ++
           ca ++ cb ++ [armIselInsI (if isSub
           then .SBCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n))
           else .ADCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))]
       | _ => False) ∧
      c = m ++ post ∧ clob = maskNZCV := by
    cases isSub <;>
      (simp only [Bool.false_eq_true, ↓reduceIte] at hc;
       dsimp only [armAddcOpIns, armSubbOpIns] at hc)
    all_goals
      split at hc
      · simp at hc
      · have hn' : n = 32 ∨ n = 64 := by
          cases h32 : (n == 32) <;> cases h64 : (n == 64) <;> simp_all
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨post, hpost, ⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, m, hm, rfl, rfl⟩
        refine ⟨hn', post, ca, ra, cb, rb, m, ha, hb, ?_, ?_, rfl, rfl⟩
        · cases cout with
          | vec vr => exact vr.elim
          | flag cf => cases cf <;> simp_all [flagCond]
          | gpr r => cases r with
            | SP => cases hpost
            | reg dc =>
              dsimp only at hpost; split at hpost
              · cases hpost
              · rename_i hne
                exact Or.inr ⟨dc, fun h => by
                  subst h; exact absurd (by cases dc <;> rfl : (dc == dc) = true) hne,
                  rfl, (Option.some.inj hpost).symm⟩
        · cases cin with
          | vec vr => exact vr.elim
          | flag cf =>
            cases cf <;> dsimp only at hm <;>
              first
              | contradiction
              | (rcases Option.some.inj hm with rfl; exact ⟨by simp [flagCond], by simp⟩)
          | gpr r => cases r with
            | SP => dsimp only at hm; cases hm
            | reg rc => dsimp only at hm; rcases Option.some.inj hm with rfl; rfl
          | imm bv =>
            cases bv <;> dsimp only at hm <;> rcases Option.some.inj hm with rfl <;> rfl
  rcases hunpack with ⟨hn', post, ca, ra, cb, rb, m, ha, hb, hpost', hm, rfl, rfl⟩
  have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl <;> decide
  have hpostClean : (cout = .flag flagCond ∧ (emitClean post : List Directive) = []) ∨
      (∃ dc, dc ≠ d ∧ cout = .gpr (.reg dc) ∧ emitClean post = [armCset64 dc flagCond]) := by
    rcases hpost' with ⟨rfl, rfl⟩ | ⟨dc, hdc, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨dc, hdc, rfl, rfl⟩
  let Q : MachineData → Prop := fun s' =>
    (∃ rvs : Tup Val [.bits n, .bool],
      rvs = (res, cflag, ()) ∧
      TRel (armMach.PDstHolds s') (as := [.bits n, .bool])
        ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout, ()) rvs) ∧
    armMach.mem s' = armMach.mem s ∧
    armMach.Frame armCondReads s s'
      (tupDstGprs (ts := [.bits n, .bool])
        ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout, ()) ++ armScratch)
      [] maskNZCV
  have runCarry : ∀ {pre : List Instr},
      _root_.Program.wp (emitClean pre)
        (fun sx => (∀ r, r ∉ armScratch → get sx r = get s r) ∧ sx.dmem = s.dmem ∧
          (if isSub then (!sx.status.c) = vcin else sx.status.c = vcin))
        (fun _ _ => False) s →
      m = pre ++ ca ++ cb ++ [armIselInsI (if isSub
          then .SBCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n))
          else .ADCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))] →
      _root_.Program.wp (emitClean (m ++ post)) Q (fun _ _ => False) s := by
    intro pre hpre hmeq
    have hp_eq : pre ++ ca ++ cb ++ [armIselInsI (if isSub
          then .SBCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n))
          else .ADCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))] =
        pre ++ (ca ++ cb ++ [armIselInsI (if isSub
          then .SBCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n))
          else .ADCS (zr d (armWidthOf n)) (zr ra (armWidthOf n)) (zr rb (armWidthOf n)))]) := by
      simp [List.append_assoc]
    rw [hmeq, emitClean_append, hp_eq, emitClean_append, List.append_assoc]
    refine armWp_append hpre ?_; rintro sx ⟨hkeepx, hdmx, hcx⟩
    have hfrx : armMach.Frame armCondReads s sx armScratch [] maskNZCV := armFrame_nzcv hkeepx
    have hpax := Machine.PArgHolds.frame hfrx hpa
      (fun r hr => hga r (hr ▸ by simp [PArg.gprs])) (fun v => v.elim) (fun _ ht => nomatch ht)
    have hpbx := Machine.PArgHolds.frame hfrx hpb
      (fun r hr => hgb r (hr ▸ by simp [PArg.gprs])) (fun v => v.elim) (fun _ ht => nomatch ht)
    rw [emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
    refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpax hpbx hga hgb) ?_
    rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂⟩
    have hcs₂ : s₂.status.c = if isSub then !vcin else vcin := by
      cases isSub <;> simp only [Bool.false_eq_true, ↓reduceIte] at hcx ⊢
      · rw [hst₂]; exact hcx
      · rw [hst₂, ← hcx, Bool.not_not]
    refine armWp_cons (armDirFallsTo_wp (Q := fun s' => ∃ st,
        s' = { wr s₂ d (BitVec.setWidth 64 res) with status := st } ∧
          flagCond.interp st = cflag)
      fun {_} p next jmp Q' hk => by
        cases isSub <;> simp only [Bool.false_eq_true, ↓reduceIte] at hcs₂ ⊢
        · rcases hn' with rfl | rfl
          · rw [show armWidthOf 32 = .W32 from rfl]
            simp only [t_step_simp]; rw [hra, hrb, hcs₂]
            cases vcin
            · exact hk _ ⟨_, rfl, by
                simpa [flagCond, cflag, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
                  StatusFlags.from_result] using adcs_carry_iff (Or.inl rfl) va vb false⟩
            · exact hk _ ⟨_, rfl, by
                simpa [flagCond, cflag, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
                  StatusFlags.from_result] using adcs_carry_iff (Or.inl rfl) va vb true⟩
          · rw [show armWidthOf 64 = .W64 from rfl]
            simp only [t_step_simp, BitVec.setWidth_eq] at hra hrb ⊢
            rw [hra, hrb, hcs₂]
            cases vcin
            · exact hk _ ⟨_, rfl, by
                simpa [flagCond, cflag, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
                  StatusFlags.from_result] using adcs_carry_iff (Or.inr rfl) va vb false⟩
            · exact hk _ ⟨_, rfl, by
                simpa [flagCond, cflag, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
                  StatusFlags.from_result] using adcs_carry_iff (Or.inr rfl) va vb true⟩
        · rcases hn' with rfl | rfl
          · rw [show armWidthOf 32 = .W32 from rfl]
            simp only [t_step_simp]; rw [hra, hrb, hcs₂]
            cases vcin
            · exact hk _ ⟨_, rfl, by
                have h := sbcs_borrow_iff va vb true
                simpa [flagCond, cflag, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
                  StatusFlags.from_result] using h⟩
            · exact hk _ ⟨_, rfl, by
                have h := sbcs_borrow_iff va vb false
                simpa [flagCond, cflag, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
                  StatusFlags.from_result] using h⟩
          · rw [show armWidthOf 64 = .W64 from rfl]
            simp only [t_step_simp, BitVec.setWidth_eq] at hra hrb ⊢
            rw [hra, hrb, hcs₂]
            cases vcin
            · exact hk _ ⟨_, rfl, by
                have h := sbcs_borrow_iff va vb true
                simpa [flagCond, cflag, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
                  StatusFlags.from_result] using h⟩
            · exact hk _ ⟨_, rfl, by
                have h := sbcs_borrow_iff va vb false
                simpa [flagCond, cflag, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
                  StatusFlags.from_result] using h⟩)
      ?_
    rintro s₃ ⟨st, rfl, hflag₃⟩
    refine armCarryFinish_wp hn' res cflag d cout flagCond s
      { wr s₂ d (BitVec.setWidth 64 res) with status := st }
      (emitClean post) hpostClean (by rcases hn' with rfl | rfl <;> simp [BitVec.setWidth_eq])
      hflag₃ (hd₂.trans hdmx) fun r hr => ?_
    have hne : r ≠ .reg d ∧ r ∉ armScratch :=
      ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
    exact (get_wr_of_ne s₂ d _ r hne.1).trans ((hfr₂.1 r hne.2).trans (hkeepx r hne.2))
  cases cin with
  | vec vr => exact vr.elim
  | flag cf =>
    rcases hm with ⟨rfl, rfl⟩
    exact runCarry (pre := []) (armWp_nil ⟨fun _ _ => rfl, rfl, by cases isSub <;> exact hpc⟩)
      (by simp)
  | gpr r => cases r with | SP => exact False.elim hm | reg rc =>
    have hrc : (s.regs.getXReg rc).toBitVec.setWidth 8 = BitVec.ofNat 8 vcin.toNat := by
      simpa [Machine.PArgHolds, GprHolds, get_reg] using hpc
    have hpre := armAndi1Sub_wp isSub rc hrc
      (xreg_ne_scratch_of_not_mem (hgc (.reg rc) (by simp [PArg.gprs]))).1
    have hpre' : _root_.Program.wp (emitClean
        [armIselInsI (.AND_i (.low (.reg .X16) .W32) (zr rc .W32) (.int64 1)),
         armIselInsI (if isSub then .SUBS_s (xzr .W32) (xzr .W32) (sh .X16)
           else .SUBS_e (xzr .W32) (.low (.reg .X16) .W32)
             (.imm { imm := .int64 1, shift := .S0 }))])
        (fun sx => (∀ r, r ∉ armScratch → get sx r = get s r) ∧ sx.dmem = s.dmem ∧
          (if isSub then (!sx.status.c) = vcin else sx.status.c = vcin))
        (fun _ _ => False) s := by
      cases isSub <;> exact hpre
    exact runCarry hpre' hm
  | imm bv =>
    simp only [Machine.PArgHolds] at hpc; subst hpc
    cases bv
    · rw [hm, emitClean_append, emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
      have hres0 : res = if isSub then va - vb else va + vb := by
        cases isSub <;> simp [res]
      have hcflag0 : cflag = if isSub then decide (va.toNat < vb.toNat)
          else decide (2 ^ n ≤ va.toNat + vb.toNat) := by
        cases isSub <;> simp [cflag]
      refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
      rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
      refine armWp_cons (armDirFallsTo_wp (Q := fun s' => ∃ st,
          s' = { wr s₂ d (BitVec.setWidth 64 (if isSub then va - vb else va + vb)) with
            status := st } ∧
            flagCond.interp st = cflag)
        fun {_} p next jmp Q' hk => by
          cases isSub <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · rcases hn' with rfl | rfl
            · rw [show armWidthOf 32 = .W32 from rfl]
              simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero]
              rw [hra, hrb]
              exact hk _ ⟨_, rfl, by
                simp only [flagCond, hcflag0, ArmCond.interp, ArmCond.toKraken, CondCode.interp]
                exact adds_carry_iff va vb⟩
            · rw [show armWidthOf 64 = .W64 from rfl]
              simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
                BitVec.setWidth_eq] at hra hrb ⊢
              rw [hra, hrb]
              exact hk _ ⟨_, rfl, by
                simp only [flagCond, hcflag0, ArmCond.interp, ArmCond.toKraken, CondCode.interp]
                exact adds_carry_iff va vb⟩
          · rcases hn' with rfl | rfl
            · rw [show armWidthOf 32 = .W32 from rfl]
              simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero]
              rw [hra, hrb]
              exact hk _ ⟨_, rfl, by
                simp only [flagCond, hcflag0, ArmCond.interp, ArmCond.toKraken, CondCode.interp]
                exact subs_borrow_iff va vb⟩
            · rw [show armWidthOf 64 = .W64 from rfl]
              simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
                BitVec.setWidth_eq] at hra hrb ⊢
              rw [hra, hrb]
              exact hk _ ⟨_, rfl, by
                simp only [flagCond, hcflag0, ArmCond.interp, ArmCond.toKraken, CondCode.interp]
                exact subs_borrow_iff va vb⟩)
        ?_
      rintro s₃ ⟨st, rfl, hflag₃⟩
      have hnil : ([] : List Directive).append (emitClean post) = emitClean post :=
        List.nil_append _
      have hres1 : (if isSub then va - vb - BitVec.ofNat n false.toNat
          else va + vb + BitVec.ofNat n false.toNat) =
          if isSub then va - vb else va + vb := by cases isSub <;> simp
      have hcflag1 : (if isSub then decide (va.toNat < vb.toNat + false.toNat)
          else decide (2 ^ n ≤ va.toNat + vb.toNat + false.toNat)) = cflag := hcflag0.symm
      rw [hnil, hres1, hcflag1]
      exact armCarryFinish_wp hn' (if isSub then va - vb else va + vb) cflag d
        cout flagCond s
        { wr s₂ d (BitVec.setWidth 64 (if isSub then va - vb else va + vb)) with status := st }
        (emitClean post) hpostClean (by rcases hn' with rfl | rfl <;> simp [BitVec.setWidth_eq])
        hflag₃ hd₂ fun r hr => by
          have hne : r ≠ .reg d ∧ r ∉ armScratch :=
            ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
          exact (get_wr_of_ne s₂ d _ r hne.1).trans (hfr₂.1 r hne.2)
    · cases isSub
      · exact runCarry (pre := [armIselInsI
            (.SUBS_s (xzr .W32) (xzr .W32) { reg := xzr .W32, amount := 0, shift := .LSL })])
          (armWp_mono (armDirFallsTo_wp
            (d := ins (.SUBS_s (xzr .W32) (xzr .W32)
              { reg := xzr .W32, amount := 0, shift := .LSL }))
            (Q := fun s' => s' = { s with status := StatusFlags.subs 0#32 0#32 0#32 })
            fun {_} p next jmp Q' hk => by
              simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
                BitVec.shiftLeft_zero, BitVec.sub_zero]
              dsimp only [xzr]; exact hk _ rfl)
            fun sx hsx => by subst hsx; exact ⟨fun _ _ => rfl, rfl, rfl⟩) hm
      · exact runCarry (pre := [armIselInsI
            (.ADDS_s (xzr .W32) (xzr .W32) { reg := xzr .W32, amount := 0, shift := .LSL })])
          (armWp_mono (armDirFallsTo_wp
            (d := ins (.ADDS_s (xzr .W32) (xzr .W32)
              { reg := xzr .W32, amount := 0, shift := .LSL }))
            (Q := fun s' => s' = { s with status := StatusFlags.adds 0#32 0#32 0#32 })
            fun {_} p next jmp Q' hk => by
              simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
                BitVec.shiftLeft_zero, BitVec.add_zero]
              dsimp only [xzr]; exact hk _ rfl)
            fun sx hsx => by subst hsx; exact ⟨fun _ _ => rfl, rfl, rfl⟩) hm

theorem armAddcOp_wp [Host] {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (cin : PArg Reg Empty ArmCond .bool)
    (d : XReg) (cout : PDst Reg Empty ArmCond .bool) (vh : VariantHint)
    {va vb : BitVec n} {vcin : Bool} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armAddcOpIns n pa pb cin d cout vh = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hgc : ∀ r ∈ cin.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hpc : armMach.PArgHolds s .bool cin vcin) :
    _root_.Program.wp (emitClean c) (fun s' =>
      (∃ rvs : Tup Val [.bits n, .bool],
        rvs = (va + vb + BitVec.ofNat n vcin.toNat,
          decide (2 ^ n ≤ va.toNat + vb.toNat + vcin.toNat), ()) ∧
        TRel (armMach.PDstHolds s') (as := [.bits n, .bool])
          ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout, ()) rvs) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s'
        (tupDstGprs (ts := [.bits n, .bool])
          ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout, ()) ++ armScratch)
        [] clob) (fun _ _ => False) s :=
  armCarryOp_wp false pa pb cin d cout vh hc hga hgb hgc hpa hpb hpc

theorem armSubbOp_wp [Host] {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (bin : PArg Reg Empty ArmCond .bool)
    (d : XReg) (bout : PDst Reg Empty ArmCond .bool) (vh : VariantHint)
    {va vb : BitVec n} {vbin : Bool} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armSubbOpIns n pa pb bin d bout vh = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hgc : ∀ r ∈ bin.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hpb' : armMach.PArgHolds s .bool bin vbin) :
    _root_.Program.wp (emitClean c) (fun s' =>
      (∃ rvs : Tup Val [.bits n, .bool],
        rvs = (va - vb - BitVec.ofNat n vbin.toNat,
          decide (va.toNat < vb.toNat + vbin.toNat), ()) ∧
        TRel (armMach.PDstHolds s') (as := [.bits n, .bool])
          ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), bout, ()) rvs) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s'
        (tupDstGprs (ts := [.bits n, .bool])
          ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), bout, ()) ++ armScratch)
        [] clob) (fun _ _ => False) s :=
  armCarryOp_wp true pa pb bin d bout vh hc hga hgb hgc hpa hpb hpb'

end LeanQbe.T.Arm64
