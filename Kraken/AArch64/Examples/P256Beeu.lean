module

public import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
public import Kraken.AArch64.Semantics
import Kraken.AArch64.Sep
public import Kraken.SeparationMem
import Kraken.Tactics
public import Kraken.ToBytes

/-!
# Verification of BoringSSL's `beeu_mod_inverse_vartime`

End-to-end functional correctness of the AArch64 binary extended Euclidean modular inverse
`beeu_mod_inverse_vartime` from BoringSSL's
`third_party/openssl/boringssl/src/gen/bcm/p256_beeu-armv8-asm-linux.S` (stripped of assembler
directives and `AARCH64_SIGN_LINK_REGISTER` / `AARCH64_VALIDATE_LINK_REGISTER` PAC annotations).
-/

open Kraken (WellFormedLayout)
open Kraken.AArch64
open Kraken.AArch64.Parser
open Std.ExtHashMap

attribute [local ksimp]
  BitVec.add_zero
  BitVec.ofInt_add
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq
  Int.add_zero
  Int64.toInt_neg
  Nat.shiftRight_zero
  Nat.sub_zero
  UInt64.ofBitVec_add
  UInt64.ofBitVec_ofNat
  UInt64.ofBitVec_sub
  UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

public section

namespace Examples.P256Beeu

def beeu_mod_inverse_vartime : Program := ⸨prog|
beeu_mod_inverse_vartime:
    -- Reserve enough space for 14 8-byte registers on the stack
    -- in the first stp call for x29, x30.
    -- Then store the remaining callee-saved registers.
    --
    --    | x29 | x30 | x19 | x20 | ... | x27 | x28 |  x0 |  x2 |
    --    ^                                                     ^
    --    sp  <------------------- 112 bytes ----------------> old sp
    --   x29 (FP)
    --
  stp x29,x30,[sp,#-112]!
  add x29,sp,#0
  stp x19,x20,[sp,#16]
  stp x21,x22,[sp,#32]
  stp x23,x24,[sp,#48]
  stp x25,x26,[sp,#64]
  stp x27,x28,[sp,#80]
  stp x0,x2,[sp,#96]

    -- B = b3..b0 := a
  ldp x25,x26,[x1]
  ldp x27,x28,[x1,#16]

    -- n3..n0 := n
    -- Note: the value of input params are changed in the following.
  ldp x0,x1,[x2]
  ldp x2,x30,[x2,#16]

    -- A = a3..a0 := n
  mov x21, x0
  mov x22, x1
  mov x23, x2
  mov x24, x30

    -- X = x4..x0 := 1
  mov x3, #1
  eor x4, x4, x4
  eor x5, x5, x5
  eor x6, x6, x6
  eor x7, x7, x7

    -- Y = y4..y0 := 0
  eor x8, x8, x8
  eor x9, x9, x9
  eor x10, x10, x10
  eor x11, x11, x11
  eor x12, x12, x12

.Lbeeu_loop:
    -- if B == 0, jump to .Lbeeu_loop_end
  orr x14, x25, x26
  orr x14, x14, x27

    -- reverse the bit order of x25. This is needed for clz after this macro
  rbit x15, x25

  orr x14, x14, x28
  cbz x14,.Lbeeu_loop_end

    -- shift := number of trailing 0s in x25
  orr x15, x15, #1
  clz x13, x15

    -- If there is no shift, goto shift_A_Y
  cbz x13, .Lbeeu_shift_A_Y

    -- Shift B right by x13 bits
  neg x14, x13
  lsr x25, x25, x13
  lsl x15, x26, x14

  lsr x26, x26, x13
  lsl x19, x27, x14

  orr x25, x25, x15

  lsr x27, x27, x13
  lsl x20, x28, x14

  orr x26, x26, x19

  lsr x28, x28, x13

  orr x27, x27, x20

    -- Shift X right by x13 bits, adding n whenever X becomes odd.
  eor x14, x14, x14
.Lbeeu_shift_loop_X:
  tbz x3, #0, .Lshift1_0
  adds x3, x3, x0
  adcs x4, x4, x1
  adcs x5, x5, x2
  adcs x6, x6, x30
  adc x7, x7, x14
.Lshift1_0:
  extr x3, x4, x3, #1
  extr x4, x5, x4, #1
  extr x5, x6, x5, #1
  extr x6, x7, x6, #1
  lsr x7, x7, #1

  subs x13, x13, #1
  bne .Lbeeu_shift_loop_X

.Lbeeu_shift_A_Y:
  rbit x15, x21
  orr x15, x15, #1
  clz x13, x15

  cbz x13, .Lbeeu_update_B_X_or_A_Y

  neg x14, x13
  lsr x21, x21, x13
  lsl x15, x22, x14

  lsr x22, x22, x13
  lsl x19, x23, x14

  orr x21, x21, x15

  lsr x23, x23, x13
  lsl x20, x24, x14

  orr x22, x22, x19

  lsr x24, x24, x13

  orr x23, x23, x20

  eor x14, x14, x14
.Lbeeu_shift_loop_Y:
  tbz x8, #0, .Lshift1_1
  adds x8, x8, x0
  adcs x9, x9, x1
  adcs x10, x10, x2
  adcs x11, x11, x30
  adc x12, x12, x14
.Lshift1_1:
  extr x8, x9, x8, #1
  extr x9, x10, x9, #1
  extr x10, x11, x10, #1
  extr x11, x12, x11, #1
  lsr x12, x12, #1

  subs x13, x13, #1
  bne .Lbeeu_shift_loop_Y

.Lbeeu_update_B_X_or_A_Y:
  subs x14, x25, x21
  sbcs x15, x26, x22
  sbcs x19, x27, x23
  sbcs x20, x28, x24
  bcs .Lbeeu_B_greater_than_A

  subs x21, x21, x25
  sbcs x22, x22, x26
  sbcs x23, x23, x27
  sbcs x24, x24, x28

  adds x8, x8, x3
  adcs x9, x9, x4
  adcs x10, x10, x5
  adcs x11, x11, x6
  adc x12, x12, x7
  b .Lbeeu_loop

.Lbeeu_B_greater_than_A:
  mov x25, x14
  mov x26, x15
  mov x27, x19
  mov x28, x20

  adds x3, x3, x8
  adcs x4, x4, x9
  adcs x5, x5, x10
  adcs x6, x6, x11
  adc x7, x7, x12
  b .Lbeeu_loop

.Lbeeu_loop_end:
  sub x14, x21, #1
  orr x14, x14, x22
  orr x14, x14, x23
  orr x14, x14, x24
  cbnz x14, .Lbeeu_err

.Lbeeu_reduction_loop:
  subs x3, x8, x0
  sbcs x4, x9, x1
  sbcs x5, x10, x2
  sbcs x6, x11, x30
  sbcs x7, x12, x14

  csel x8, x3, x8, cs
  csel x9, x4, x9, cs
  csel x10, x5, x10, cs
  csel x11, x6, x11, cs
  csel x12, x7, x12, cs
  bcs .Lbeeu_reduction_loop

  subs x8, x0, x8
  sbcs x9, x1, x9
  sbcs x10, x2, x10
  sbcs x11, x30, x11

  ldr x3, [sp,#96]
  stp x8, x9, [x3]
  stp x10, x11, [x3,#16]
  mov x0, #1
  b .Lbeeu_finish

.Lbeeu_err:
  eor x0, x0, x0

.Lbeeu_finish:
  add sp,x29,#0
  ldp x19,x20,[sp,#16]
  ldp x21,x22,[sp,#32]
  ldp x23,x24,[sp,#48]
  ldp x25,x26,[sp,#64]
  ldp x27,x28,[sp,#80]
  ldp x29,x30,[sp],#112

  ret
⸩

abbrev lbl [WellFormedLayout beeu_mod_inverse_vartime] (l : String) : Int64 :=
  @Labels.label! (Executable.labels beeu_mod_inverse_vartime.toExecutable) l

/-- Equality on the AArch64 callee-saved registers (`x19..x29`). -/
def CalleeSavedEq (r r₀ : Reg64s) : Prop :=
  r.X19 = r₀.X19 ∧ r.X20 = r₀.X20 ∧ r.X21 = r₀.X21 ∧ r.X22 = r₀.X22 ∧
  r.X23 = r₀.X23 ∧ r.X24 = r₀.X24 ∧ r.X25 = r₀.X25 ∧ r.X26 = r₀.X26 ∧
  r.X27 = r₀.X27 ∧ r.X28 = r₀.X28 ∧ r.X29 = r₀.X29

/-- 256-bit unsigned integer represented across four 64-bit registers (little-endian limbs). -/
def val256 (w0 w1 w2 w3 : UInt64) : Int :=
  (w0.toNat : Int) +
  256 ^ 8 * (w1.toNat : Int) +
  256 ^ 16 * (w2.toNat : Int) +
  256 ^ 24 * (w3.toNat : Int)

/-- The 12 saved callee-saved/frame registers in the `beeu_mod_inverse_vartime` stack frame. -/
def BeeuSavedRegs (r₀ : Reg64s) (sp' : BitVec 64) : DataMem → Prop :=
  Eq ((Int.toBytes 8 r₀.X29.toBitVec.toInt).At sp') ⋆
  Eq ((Int.toBytes 8 r₀.X30.toBitVec.toInt).At (sp' + 8#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X19.toBitVec.toInt).At (sp' + 16#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X20.toBitVec.toInt).At (sp' + 24#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X21.toBitVec.toInt).At (sp' + 32#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X22.toBitVec.toInt).At (sp' + 40#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X23.toBitVec.toInt).At (sp' + 48#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X24.toBitVec.toInt).At (sp' + 56#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X25.toBitVec.toInt).At (sp' + 64#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X26.toBitVec.toInt).At (sp' + 72#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X27.toBitVec.toInt).At (sp' + 80#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X28.toBitVec.toInt).At (sp' + 88#64))

/-- The 112-byte stack frame saved by the `beeu_mod_inverse_vartime` prologue. -/
def BeeuStackFrame (r₀ : Reg64s) (sp' : BitVec 64) : DataMem → Prop :=
  BeeuSavedRegs r₀ sp' ⋆
  Eq ((Int.toBytes 8 r₀.X0.toBitVec.toInt).At (sp' + 96#64)) ⋆
  Eq ((Int.toBytes 8 r₀.X2.toBitVec.toInt).At (sp' + 104#64))

/-- Four 64-bit limbs stored contiguously in memory at address `p`. -/
def Words256At (w0 w1 w2 w3 : UInt64) (p : BitVec 64) : DataMem → Prop :=
  Eq ((Int.toBytes 8 w0.toBitVec.toInt).At p) ⋆
  Eq ((Int.toBytes 8 w1.toBitVec.toInt).At (p + 8#64)) ⋆
  Eq ((Int.toBytes 8 w2.toBitVec.toInt).At (p + 16#64)) ⋆
  Eq ((Int.toBytes 8 w3.toBitVec.toInt).At (p + 24#64))

/-! ## Private Label Resolution and Multi-Limb Helpers -/

private abbrev beeuExec [WellFormedLayout beeu_mod_inverse_vartime] : Executable :=
  beeu_mod_inverse_vartime.toExecutable

private theorem lbl_entry [WellFormedLayout beeu_mod_inverse_vartime] :
    lbl "beeu_mod_inverse_vartime" = beeuExec.addrOf 0 :=
  Labels.label!_of_label? (label?_eq_some_addrOf rfl)

/-- 320-bit unsigned integer represented across five 64-bit registers (little-endian limbs). -/
private def val320 (w0 w1 w2 w3 w4 : UInt64) : Int :=
  (w0.toNat : Int) +
  256 ^ 8 * (w1.toNat : Int) +
  256 ^ 16 * (w2.toNat : Int) +
  256 ^ 24 * (w3.toNat : Int) +
  256 ^ 32 * (w4.toNat : Int)

private abbrev beeuB (r : Reg64s) : Int := val256 r.X25 r.X26 r.X27 r.X28
private abbrev beeuA (r : Reg64s) : Int := val256 r.X21 r.X22 r.X23 r.X24
private abbrev beeuN (r : Reg64s) : Int := val256 r.X0 r.X1 r.X2 r.X30
private abbrev beeuX (r : Reg64s) : Int := val320 r.X3 r.X4 r.X5 r.X6 r.X7
private abbrev beeuY (r : Reg64s) : Int := val320 r.X8 r.X9 r.X10 r.X11 r.X12
private abbrev beeuY256 (r : Reg64s) : Int := val256 r.X8 r.X9 r.X10 r.X11

/-! ### Bit-Vector, Byte-Splitting, Carry-Chain, and Number-Theoretic Helpers -/

private theorem extractLsb'_0_64 (x : BitVec 64) : x.extractLsb' 0 64 = x := by
  simp [BitVec.extractLsb']

private theorem umod_64_eq_self {k : BitVec 64} (hk63 : k ≤ 63#64) : k % 64#64 = k := by
  have hk : k.toNat ≤ 63 := by simpa [BitVec.le_def] using hk63
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod]
  change k.toNat % 64 = k.toNat
  exact Nat.mod_eq_of_lt (by omega)

private theorem toNat_le_63 {k : BitVec 64} (hk63 : k ≤ 63#64) : k.toNat ≤ 63 := by
  simpa [BitVec.le_def] using hk63

private theorem neg_umod_64 {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    (0#64 - k) % 64#64 = 64#64 - k := by grind

private theorem toNat_neg_umod_64 {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((0#64 - k) % 64#64).toNat = 64 - k.toNat := by
  have hk := toNat_le_63 hk63
  rw [neg_umod_64 hk1 hk63, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change k.toNat ≤ 64; omega)]
  rfl

private theorem two_pow_le_two_pow_63 {k : BitVec 64} (hk63 : k ≤ 63#64) : 2 ^ k.toNat ≤ 2 ^ 63 :=
  Nat.pow_le_pow_right (by decide) (toNat_le_63 hk63)

private theorem toNat_one_shiftLeft {k : BitVec 64} (hk63 : k ≤ 63#64) :
    (1#64 <<< k).toNat = 2 ^ k.toNat := by
  have hk := toNat_le_63 hk63
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : 1 % 2 ^ 64 = 1 := by decide
  rw [this, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

private theorem toNat_mask {k : BitVec 64} (hk63 : k ≤ 63#64) :
    ((1#64 <<< k) - 1#64).toNat = 2 ^ k.toNat - 1 := by
  rw [BitVec.toNat_sub, toNat_one_shiftLeft hk63, BitVec.toNat_ofNat]
  have : 1 % 2 ^ 64 = 1 := by decide
  rw [this]
  have hp_pos : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  have hp_le := two_pow_le_two_pow_63 hk63
  omega

private theorem toNat_and_mask (x : BitVec 64) {k : BitVec 64} (hk63 : k ≤ 63#64) :
    (x &&& ((1#64 <<< k) - 1#64)).toNat = x.toNat % 2 ^ k.toNat := by
  rw [BitVec.toNat_and, toNat_mask hk63, Nat.and_two_pow_sub_one_eq_mod]

private theorem two_pow_mul_two_pow_sub {k : BitVec 64} (hk63 : k ≤ 63#64) :
    2 ^ k.toNat * 2 ^ (64 - k.toNat) = 2 ^ 64 := by
  have hk := toNat_le_63 hk63
  rw [← Nat.pow_add]; congr 1; omega

private theorem toNat_funnel_nat' {w : Nat} (lo hi : BitVec w) {k m : Nat} (hkm : k + m = w) :
    ((lo >>> k) ||| (hi <<< m)).toNat = lo.toNat / 2 ^ k + (hi.toNat % 2 ^ k) * 2 ^ m := by
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have hpq : 2 ^ k * 2 ^ m = 2 ^ w := by rw [← Nat.pow_add, hkm]
  rw [← hpq, Nat.mul_mod_mul_right]
  have hA : lo.toNat / 2 ^ k < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hpq]; exact lo.isLt
  have h := Nat.two_pow_add_eq_or_of_lt hA (hi.toNat % 2 ^ k)
  rw [Nat.mul_comm (hi.toNat % 2 ^ k), Nat.or_comm, ← h]
  omega

private theorem toNat_funnel_nat {w : Nat} (lo hi : BitVec w) {k : Nat} (hkw : k ≤ w) :
    ((lo >>> k) ||| (hi <<< (w - k))).toNat =
      lo.toNat / 2 ^ k + (hi.toNat % 2 ^ k) * 2 ^ (w - k) :=
  toNat_funnel_nat' lo hi (by omega)

private theorem toNat_funnel (lo hi : BitVec 64) {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).toNat =
      lo.toNat / 2 ^ k.toNat + (hi.toNat % 2 ^ k.toNat) * 2 ^ (64 - k.toNat) := by
  rw [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', umod_64_eq_self hk63,
    toNat_neg_umod_64 hk1 hk63]
  have hk := toNat_le_63 hk63
  exact toNat_funnel_nat lo hi (by omega)

private theorem toNat_funnel_mul_add_and_mask (lo hi : BitVec 64) {k : BitVec 64}
    (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).toNat +
      (lo &&& mask).toNat =
      lo.toNat + 2 ^ 64 * (hi &&& mask).toNat := by
  dsimp only
  rw [toNat_funnel lo hi hk1 hk63, umod_64_eq_self hk63, toNat_and_mask lo hk63,
    toNat_and_mask hi hk63]
  have := two_pow_mul_two_pow_sub hk63
  have := Nat.div_add_mod lo.toNat (2 ^ k.toNat)
  grind

private theorem toNat_ushiftRight_mul_add_and_mask (hi : BitVec 64) {k : BitVec 64}
    (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (hi >>> (k % 64#64)).toNat + (hi &&& mask).toNat = hi.toNat := by
  dsimp only
  rw [BitVec.ushiftRight_eq', umod_64_eq_self hk63, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, toNat_and_mask hi hk63]
  exact Nat.div_add_mod hi.toNat (2 ^ k.toNat)

private theorem getLsbD_reverse_or_one_reverse {w : Nat} (x : BitVec w) (i : Nat) (hw : 0 < w) :
    (x.reverse ||| 1#w).reverse.getLsbD i = (x.getLsbD i || decide (i = w - 1)) := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_or, BitVec.getMsbD_reverse, BitVec.getMsbD_eq_getLsbD,
    BitVec.getLsbD_one]
  by_cases hi : i < w
  · have : (w - 1 - i = 0) ↔ (i = w - 1) := by omega
    simp [hi, hw, this]
  · have hx : x.getLsbD i = false := BitVec.getLsbD_of_ge x i (by omega)
    have : ¬ (i = w - 1) := by omega
    simp [hi, hx, this]

private theorem reverse_or_one_reverse_ne_zero {w : Nat} (x : BitVec w) (hw : 0 < w) :
    (x.reverse ||| 1#w).reverse ≠ 0#w := by
  intro h
  have := getLsbD_reverse_or_one_reverse x (w - 1) hw
  rw [h] at this
  simp at this

private theorem clz_reverse_or_one_lt {w : Nat} (x : BitVec w) (hw : 0 < w) :
    (x.reverse ||| 1#w).clz < BitVec.ofNat w w := by
  rw [BitVec.clz_eq_reverse_ctz]
  exact BitVec.ctz_lt_iff_ne_zero.mpr (reverse_or_one_reverse_ne_zero x hw)

private theorem toNat_clz_reverse_or_one_lt {w : Nat} (x : BitVec w) (hw : 0 < w) :
    ((x.reverse ||| 1#w).clz).toNat < w := by
  have h := BitVec.lt_def.mp (clz_reverse_or_one_lt x hw)
  rw [BitVec.toNat_ofNat] at h
  exact Nat.lt_of_lt_of_le h (Nat.mod_le _ _)

private theorem clz_reverse_or_one_le_63 (x : BitVec 64) : (x.reverse ||| 1#64).clz ≤ 63#64 := by
  have h := toNat_clz_reverse_or_one_lt x (by decide)
  rw [BitVec.le_def]
  change _ ≤ 63
  omega

private theorem getLsbD_false_of_lt_clz_reverse_or_one {w : Nat} {x : BitVec w} {i : Nat} (hw : 0 < w)
    (hi : i < ((x.reverse ||| 1#w).clz).toNat) : x.getLsbD i = false := by
  rw [BitVec.clz_eq_reverse_ctz] at hi
  have h := BitVec.getLsbD_false_of_lt_ctz hi
  rw [getLsbD_reverse_or_one_reverse x i hw] at h
  exact (Bool.or_eq_false_iff.mp h).1

private theorem toNat_mod_two_pow_clz_reverse_or_one {w : Nat} (x : BitVec w) (hw : 0 < w) :
    x.toNat % 2 ^ ((x.reverse ||| 1#w).clz).toNat = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < ((x.reverse ||| 1#w).clz).toNat
  · have h := getLsbD_false_of_lt_clz_reverse_or_one hw hi
    simp only [hi, decide_true, Bool.true_and]
    exact h
  · simp [hi]

private theorem getLsbD_clz_reverse_or_one {w : Nat} (x : BitVec w) (hw : 0 < w) :
    x.getLsbD ((x.reverse ||| 1#w).clz).toNat = true ∨ ((x.reverse ||| 1#w).clz).toNat = w - 1 := by
  rw [BitVec.clz_eq_reverse_ctz]
  have h := BitVec.getLsbD_true_ctz_of_ne_zero (reverse_or_one_reverse_ne_zero x hw)
  rw [getLsbD_reverse_or_one_reverse x _ hw, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h

private theorem getLsbD_clz_reverse_or_one_64 (x : BitVec 64) :
    x.getLsbD ((x.reverse ||| 1#64).clz).toNat = true ∨ (x.reverse ||| 1#64).clz = 63#64 := by
  rcases getLsbD_clz_reverse_or_one x (by decide) with h | h
  · exact Or.inl h
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

private theorem shift256Word_lsb_or_clamped (b0 b1 : BitVec 64) :
    let k := (b0.reverse ||| 1#64).clz
    ((b0 >>> (k % 64#64)) ||| (b1 <<< ((0#64 - k) % 64#64))).getLsbD 0 = true ∨ k = 63#64 := by
  intro k
  have hk63 : k ≤ 63#64 := clz_reverse_or_one_le_63 b0
  rw [BitVec.getLsbD_or, BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight,
    umod_64_eq_self hk63, Nat.add_zero]
  rcases getLsbD_clz_reverse_or_one_64 b0 with h | h
  · exact Or.inl (by rw [h, Bool.true_or])
  · exact Or.inr h

private theorem getLsbD_zero_of_clz_reverse_or_one_eq_zero {w : Nat} {x : BitVec w} (hw : 1 < w)
    (h : (x.reverse ||| 1#w).clz = 0#w) : x.getLsbD 0 = true := by
  have hc : ((x.reverse ||| 1#w).clz).toNat = 0 := by rw [h]; simp
  rcases getLsbD_clz_reverse_or_one x (by omega) with h' | h'
  · rwa [hc] at h'
  · omega

private theorem and_mask_clz_reverse_or_one (x : BitVec 64) :
    x &&& ((1#64 <<< ((x.reverse ||| 1#64).clz % 64#64)) - 1#64) = 0#64 := by
  have hk63 := clz_reverse_or_one_le_63 x
  apply BitVec.eq_of_toNat_eq
  rw [umod_64_eq_self hk63, toNat_and_mask x hk63, toNat_mod_two_pow_clz_reverse_or_one x (by decide)]
  rfl

private theorem toNat_add_cases {w : Nat} (x y : BitVec w) :
    (x.toNat + y.toNat < 2 ^ w ∧ (x + y).toNat = x.toNat + y.toNat) ∨
    (2 ^ w ≤ x.toNat + y.toNat ∧ (x + y).toNat + 2 ^ w = x.toNat + y.toNat) := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · exact Or.inl ⟨h, BitVec.toNat_add_of_lt h⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

private theorem toNat_sub_cases {w : Nat} (x y : BitVec w) :
    (y.toNat ≤ x.toNat ∧ (x - y).toNat + y.toNat = x.toNat) ∨
    (x.toNat < y.toNat ∧ (x - y).toNat + y.toNat = x.toNat + 2 ^ w) := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · exact Or.inl ⟨h, by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]; omega⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [BitVec.toNat_sub_of_lt (BitVec.lt_def.mpr (by omega))]
    omega

private theorem toNat_ofNat_toNat_bool {w : Nat} (hw : 0 < w) (c : Bool) :
    (BitVec.ofNat w c.toNat).toNat = c.toNat := by
  rw [BitVec.toNat_ofNat]
  cases c
  · simp
  · exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

private abbrev sub0Word (b a : UInt64) : BitVec 64 := b.toBitVec - a.toBitVec
private abbrev sub0Carry (b a : UInt64) : Bool :=
  (((b.toBitVec - a.toBitVec).toNat : Int) == (b.toBitVec.toNat : Int) - (a.toBitVec.toNat : Int))

private abbrev sbcWord (b a : UInt64) (c : Bool) : BitVec 64 :=
  b.toBitVec - a.toBitVec - BitVec.ofNat 64 (!c).toNat
private abbrev sbcCarry (b a : UInt64) (c : Bool) : Bool :=
  decide ((a.toBitVec.toNat : Int) + (if c then 0 else 1) ≤ (b.toBitVec.toNat : Int))

private abbrev add0Word (x y : UInt64) : BitVec 64 := x.toBitVec + y.toBitVec
private abbrev add0Carry (x y : UInt64) : Bool :=
  (((x.toBitVec + y.toBitVec).toNat : Int) != (x.toBitVec.toNat : Int) + (y.toBitVec.toNat : Int))

private abbrev adcWord (x y : UInt64) (c : Bool) : BitVec 64 :=
  x.toBitVec + y.toBitVec + BitVec.ofNat 64 c.toNat
private abbrev adcCarry (x y : UInt64) (c : Bool) : Bool :=
  (((x.toBitVec + y.toBitVec + BitVec.ofNat 64 c.toNat).toNat : Int) !=
    (x.toBitVec.toNat : Int) + (y.toBitVec.toNat : Int) + (if c then 1 else 0))

private theorem sub0_step (b a : UInt64) :
    ((UInt64.ofBitVec (sub0Word b a)).toNat : Int) - (if sub0Carry b a then 0 else 1) * 256 ^ 8 =
      (b.toNat : Int) - (a.toNat : Int) := by
  dsimp only [sub0Word, sub0Carry]
  rw [UInt64.toNat_ofBitVec]
  have h := toNat_sub_cases b.toBitVec a.toBitVec
  have hb := b.toBitVec.isLt
  have ha := a.toBitVec.isLt
  simp only [UInt64.toNat_toBitVec] at h hb ha ⊢
  rcases h with ⟨hle, heq⟩ | ⟨hlt, heq⟩
  · have hc : (((b.toBitVec - a.toBitVec).toNat : Int) == (b.toNat : Int) - (a.toNat : Int)) = true := by
      rw [beq_iff_eq]; omega
    simp only [hc, ↓reduceIte]; omega
  · have hc : (((b.toBitVec - a.toBitVec).toNat : Int) == (b.toNat : Int) - (a.toNat : Int)) = false := by
      rw [beq_eq_false_iff_ne]; omega
    simp only [hc, Bool.false_eq_true, ↓reduceIte]; omega

private theorem sbc_step (b a : UInt64) (c : Bool) :
    ((UInt64.ofBitVec (sbcWord b a c)).toNat : Int) - (if sbcCarry b a c then 0 else 1) * 256 ^ 8 =
      (b.toNat : Int) - (a.toNat : Int) - (if c then 0 else 1) := by
  dsimp only [sbcWord, sbcCarry]
  rw [UInt64.toNat_ofBitVec]
  have h1 := toNat_sub_cases b.toBitVec a.toBitVec
  have h2 := toNat_sub_cases (b.toBitVec - a.toBitVec) (BitVec.ofNat 64 (!c).toNat)
  rw [toNat_ofNat_toNat_bool (by decide)] at h2
  have hb := b.toBitVec.isLt
  have ha := a.toBitVec.isLt
  simp only [UInt64.toNat_toBitVec] at h1 h2 hb ha ⊢
  cases c <;> simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
    Bool.false_eq_true, ↓reduceIte] at h2 ⊢
  · by_cases hle : (a.toNat : Int) + 1 ≤ (b.toNat : Int)
    · simp only [hle, decide_true, ↓reduceIte]; omega
    · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
  · by_cases hle : (a.toNat : Int) + 0 ≤ (b.toNat : Int)
    · simp only [hle, decide_true, ↓reduceIte]; omega
    · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

private theorem add0_step (x y : UInt64) :
    ((UInt64.ofBitVec (add0Word x y)).toNat : Int) + (if add0Carry x y then 1 else 0) * 256 ^ 8 =
      (x.toNat : Int) + (y.toNat : Int) := by
  dsimp only [add0Word, add0Carry]
  rw [UInt64.toNat_ofBitVec]
  have h := toNat_add_cases x.toBitVec y.toBitVec
  simp only [UInt64.toNat_toBitVec] at h ⊢
  rcases h with ⟨hlt, heq⟩ | ⟨hle, heq⟩
  · have hc : (((x.toBitVec + y.toBitVec).toNat : Int) != (x.toNat : Int) + (y.toNat : Int)) = false := by
      rw [bne_eq_false_iff_eq]; omega
    simp only [hc, Bool.false_eq_true, ↓reduceIte]; omega
  · have hc : (((x.toBitVec + y.toBitVec).toNat : Int) != (x.toNat : Int) + (y.toNat : Int)) = true := by
      rw [bne_iff_ne]; omega
    simp only [hc, ↓reduceIte]; omega

private theorem adc_step (x y : UInt64) (c : Bool) :
    ((UInt64.ofBitVec (adcWord x y c)).toNat : Int) + (if adcCarry x y c then 1 else 0) * 256 ^ 8 =
      (x.toNat : Int) + (y.toNat : Int) + (if c then 1 else 0) := by
  dsimp only [adcWord, adcCarry]
  rw [UInt64.toNat_ofBitVec]
  have h1 := toNat_add_cases x.toBitVec y.toBitVec
  have h2 := toNat_add_cases (x.toBitVec + y.toBitVec) (BitVec.ofNat 64 c.toNat)
  rw [toNat_ofNat_toNat_bool (by decide)] at h2
  have hx := x.toBitVec.isLt
  have hy := y.toBitVec.isLt
  simp only [UInt64.toNat_toBitVec] at h1 h2 hx hy ⊢
  cases c <;> simp only [Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
  · rcases h1 with ⟨_, _⟩ | ⟨_, _⟩
    · have hc : (((x.toBitVec + y.toBitVec + BitVec.ofNat 64 0).toNat : Int) != (x.toNat : Int) + (y.toNat : Int) + 0) = false := by
        rw [bne_eq_false_iff_eq]; omega
      simp only [hc, Bool.false_eq_true, ↓reduceIte]; omega
    · have hc : (((x.toBitVec + y.toBitVec + BitVec.ofNat 64 0).toNat : Int) != (x.toNat : Int) + (y.toNat : Int) + 0) = true := by
        rw [bne_iff_ne]; omega
      simp only [hc, ↓reduceIte]; omega
  · by_cases hlt : x.toNat + y.toNat + 1 < 2 ^ 64
    · have hc : (((x.toBitVec + y.toBitVec + BitVec.ofNat 64 1).toNat : Int) != (x.toNat : Int) + (y.toNat : Int) + 1) = false := by
        rw [bne_eq_false_iff_eq]; omega
      simp only [hc, Bool.false_eq_true, ↓reduceIte]; omega
    · have hc : (((x.toBitVec + y.toBitVec + BitVec.ofNat 64 1).toNat : Int) != (x.toNat : Int) + (y.toNat : Int) + 1) = true := by
        rw [bne_iff_ne]; omega
      simp only [hc, ↓reduceIte]; omega

private theorem or4_eq_zero_iff (x0 x1 x2 x3 : BitVec 64) :
    ((x0 ||| x1 ||| x2 ||| x3) = 0#64) ↔
      (x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64) := by
  grind

private theorem or4_sub_one_eq_zero_iff (x0 x1 x2 x3 : BitVec 64) :
    ((x0 - 1#64 ||| x1 ||| x2 ||| x3) = 0#64) ↔
      (x0 = 1#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64) := by
  grind

private theorem getLsbD_zero_eq_false_mod2 (x : UInt64) (h : x.toBitVec.getLsbD 0 = false) :
    x.toNat % 2 = 0 := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_false_iff_not] at h
  rw [← UInt64.toNat_toBitVec]
  omega

private theorem getLsbD_zero_eq_true_mod2 (x : UInt64) (h : x.toBitVec.getLsbD 0 = true) :
    x.toNat % 2 = 1 := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_true_eq] at h
  rw [← UInt64.toNat_toBitVec]
  exact h

private theorem toNat_ofBitVec_ushiftRight_one (x : UInt64) :
    (UInt64.ofBitVec (x.toBitVec >>> 1)).toNat = x.toNat / 2 := by
  rw [UInt64.toNat_ofBitVec, BitVec.toNat_ushiftRight, UInt64.toNat_toBitVec, Nat.shiftRight_eq_div_pow]

private theorem sub_one_beq_zero_false_of_gt_one (x : UInt64) (h : 1 < x.toNat) :
    ((x.toBitVec - 1#64) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_eq
  have h_nat : (x.toBitVec - 1#64).toNat = 0 := congrArg BitVec.toNat h_eq
  rw [BitVec.toNat_sub_of_le] at h_nat
  · change x.toNat - 1 = 0 at h_nat; omega
  · rw [BitVec.le_def]; change 1 ≤ x.toNat; omega

private theorem toNat_sub_one_of_pos (x : UInt64) (h : 0 < x.toNat) :
    (UInt64.ofBitVec (x.toBitVec - 1#64)).toNat = x.toNat - 1 := by
  rw [UInt64.toNat_ofBitVec, BitVec.toNat_sub_of_le]
  · rfl
  · rw [BitVec.le_def]; change 1 ≤ x.toNat; omega

private def extr1Word (hi lo : UInt64) : BitVec 64 :=
  (hi.toBitVec <<< 63) ||| (lo.toBitVec >>> 1)

private theorem extr1Word_toNat (hi lo : UInt64) :
    (UInt64.ofBitVec (extr1Word hi lo)).toNat =
      lo.toNat / 2 + 2 ^ 63 * (hi.toNat % 2) := by
  dsimp only [extr1Word]
  rw [UInt64.toNat_ofBitVec, BitVec.or_comm,
    toNat_funnel_nat' lo.toBitVec hi.toBitVec (k := 1) (m := 63) rfl,
    UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]
  omega

private def ctzClamped (w : UInt64) : BitVec 64 :=
  (w.toBitVec.reverse ||| 1#64).clz

private def shift256Word (lo hi : UInt64) (k : BitVec 64) : BitVec 64 :=
  lo.toBitVec.ushiftRight (k.toNat % 64) ||| (hi.toBitVec <<< ((0#64 - k).toNat % 64))

private def shift256TopWord (hi : UInt64) (k : BitVec 64) : BitVec 64 :=
  hi.toBitVec.ushiftRight (k.toNat % 64)

private theorem shift256Word_eq (lo hi : UInt64) (k : BitVec 64) :
    shift256Word lo hi k =
      (lo.toBitVec >>> (k % 64#64)) ||| (hi.toBitVec <<< ((0#64 - k) % 64#64)) := by
  dsimp only [shift256Word]
  have h1 : (k % 64#64).toNat = k.toNat % 64 := BitVec.toNat_umod
  have h2 : ((0#64 - k) % 64#64).toNat = (0#64 - k).toNat % 64 := BitVec.toNat_umod
  rw [← h1, ← h2]
  rfl

private theorem shift256TopWord_eq (hi : UInt64) (k : BitVec 64) :
    shift256TopWord hi k = hi.toBitVec >>> (k % 64#64) := by
  dsimp only [shift256TopWord]
  have h1 : (k % 64#64).toNat = k.toNat % 64 := BitVec.toNat_umod
  rw [← h1]
  rfl

private theorem shift256_limb_toNat (lo hi : UInt64) (k : BitVec 64)
    (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (UInt64.ofBitVec (shift256Word lo hi k)).toNat +
      (lo.toBitVec &&& mask).toNat =
      lo.toNat + 2 ^ 64 * (hi.toBitVec &&& mask).toNat := by
  dsimp only
  rw [UInt64.toNat_ofBitVec, shift256Word_eq]
  exact toNat_funnel_mul_add_and_mask lo.toBitVec hi.toBitVec hk1 hk63

private theorem shift256_top_toNat (hi : UInt64) (k : BitVec 64) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (UInt64.ofBitVec (shift256TopWord hi k)).toNat +
      (hi.toBitVec &&& mask).toNat = hi.toNat := by
  dsimp only
  rw [UInt64.toNat_ofBitVec, shift256TopWord_eq]
  exact toNat_ushiftRight_mul_add_and_mask hi.toBitVec hk63

private theorem ofBytes_take_drop_pair (bs : List UInt8) (n : Nat) (h : n ≤ bs.length) :
    Int.ofBytes bs = Int.ofBytes (bs.take n) + 256 ^ n * Int.ofBytes (bs.drop n) := by
  conv => lhs; rw [← List.take_append_drop n bs]
  rw [Int.ofBytes_append, List.length_take_of_le h]

private theorem ofBytes_32_split (bs : List UInt8) (h : bs.length = 32) :
    Int.ofBytes bs =
      Int.ofBytes (bs.take 8) +
      256 ^ 8 * Int.ofBytes ((bs.drop 8).take 8) +
      256 ^ 16 * Int.ofBytes ((bs.drop 16).take 8) +
      256 ^ 24 * Int.ofBytes ((bs.drop 24).take 8) := by
  rw [ofBytes_take_drop_pair bs 8 (by omega),
      ofBytes_take_drop_pair (bs.drop 8) 8 (by simp [h]),
      List.drop_drop,
      ofBytes_take_drop_pair (bs.drop 16) 8 (by simp [h]),
      List.drop_drop,
      show 16 + 8 = 24 by rfl,
      List.take_of_length_le (l := bs.drop 24) (i := 8) (by simp [h])]
  omega

private theorem ofBytes_toNat_ofInt_64 (bs : List UInt8) (h : bs.length = 8) :
    ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) = Int.ofBytes bs := by
  have h_ge : 0 ≤ Int.ofBytes bs := Int.ofBytes_ge_zero bs
  have h_lt : Int.ofBytes bs < (2 : Int) ^ 64 := by
    have := Int.ofBytes_lt bs
    rw [h] at this
    exact lt_of_lt_of_eq this (by decide)
  have h_eq : BitVec.ofInt 64 (Int.ofBytes bs) = BitVec.ofNat 64 (Int.ofBytes bs).toNat := by
    rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg h_ge]
  have h_lt_nat : (Int.ofBytes bs).toNat < 2 ^ 64 := by
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg h_ge]
    exact_mod_cast h_lt
  rw [h_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt_nat, Int.toNat_of_nonneg h_ge]

private theorem odd_of_dvd_odd (c g : Int) (hg : g % 2 = 1) (h : c ∣ g) : c % 2 = 1 := by
  obtain ⟨q, rfl⟩ := h
  have h01 : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases h01 with h0 | h1
  · rw [Int.mul_emod, h0, Int.zero_mul, Int.zero_emod] at hg
    omega
  · exact h1

private theorem odd_dvd_of_dvd_two_mul (c m : Int) (hc : c % 2 = 1) (h : c ∣ 2 * m) : c ∣ m := by
  have h2 : (c + 1) / 2 * 2 = c + 1 :=
    Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (by omega))
  have h_eq : m = (c + 1) / 2 * (2 * m) - c * m := by
    rw [← Int.mul_assoc, h2, Int.add_mul, Int.one_mul]
    omega
  rw [h_eq]
  exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h) (Int.dvd_mul_right c m)

private theorem odd_dvd_of_dvd_two_pow_mul (c : Int) (hc : c % 2 = 1) (k : Nat) (m : Int)
    (h : c ∣ ((2 ^ k : Nat) : Int) * m) : c ∣ m := by
  induction k generalizing m with
  | zero => simpa using h
  | succ k ih =>
    apply odd_dvd_of_dvd_two_mul c m hc
    apply ih
    have : ((2 ^ (k + 1) : Nat) : Int) * m = ((2 ^ k : Nat) : Int) * (2 * m) := by
      rw [Nat.pow_succ, Int.natCast_mul]; grind
    rw [← this]
    exact h

private theorem gcd_of_two_pow_mul_odd (A B B' : Int) (k : Nat) (h : ((2 ^ k : Nat) : Int) * B' = B)
    (hodd : (Int.gcd A B : Int) % 2 = 1) : Int.gcd A B' = Int.gcd A B := by
  rw [Int.gcd_right_eq_iff]
  intro c hcA
  constructor
  · intro hcB'
    rw [← h]
    exact Int.dvd_mul_of_dvd_right hcB'
  · intro hcB
    have hcg : c ∣ (Int.gcd A B : Int) := Int.dvd_coe_gcd hcA hcB
    have hc_odd : c % 2 = 1 := odd_of_dvd_odd c _ hodd hcg
    exact odd_dvd_of_dvd_two_pow_mul c hc_odd k B' (h ▸ hcB)

private theorem pow2_mul_bound_step (m : Nat) (x x' n z : Int)
    (h_inv : ((2 ^ m : Nat) : Int) * x ≤ z + (((2 ^ m : Nat) : Int) - 1) * n)
    (h_step : 2 * x' ≤ x + n) :
    ((2 ^ (m + 1) : Nat) : Int) * x' ≤ z + (((2 ^ (m + 1) : Nat) : Int) - 1) * n := by
  have h0 : (0 : Int) ≤ ((2 ^ m : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left h_step h0
  have h_pow : ((2 ^ (m + 1) : Nat) : Int) = ((2 ^ m : Nat) : Int) * 2 := by
    rw [Nat.pow_succ, Int.natCast_mul]; rfl
  rw [h_pow]
  grind

private theorem pow2_mul_emod_step (m : Nat) (x x' n z : Int)
    (h_inv : (((2 ^ m : Nat) : Int) * x) % n = z)
    (h_step : (2 * x') % n = x % n) :
    (((2 ^ (m + 1) : Nat) : Int) * x') % n = z := by
  have h_pow : ((2 ^ (m + 1) : Nat) : Int) * x' = ((2 ^ m : Nat) : Int) * (2 * x') := by
    rw [Nat.pow_succ, Int.natCast_mul]; grind
  rw [h_pow, Int.mul_emod, h_step, ← Int.mul_emod, h_inv]

private theorem two_mul_emod_eq_zero_of_odd (z n : Int) (hn_odd : n % 2 = 1)
    (h : (2 * z) % n = 0) : z % n = 0 := by
  obtain ⟨q, hq⟩ : n ∣ 2 * z := Int.dvd_of_emod_eq_zero h
  have hn_eq : n = 2 * (n / 2) + 1 := by omega
  have hz : z = n * (z - (n / 2) * q) + (2 * z - n * q) * (n / 2) := by grind
  have h2z : 2 * z - n * q = 0 := by omega
  rw [h2z, Int.zero_mul, Int.add_zero] at hz
  exact Int.emod_eq_zero_of_dvd ⟨z - (n / 2) * q, hz⟩

private theorem pow2_mul_emod_eq_zero_of_odd (k : Nat) (z n : Int) (hn_odd : n % 2 = 1)
    (h : (((2 ^ k : Nat) : Int) * z) % n = 0) : z % n = 0 := by
  induction k generalizing z with
  | zero =>
    simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul] at h
    exact h
  | succ k ih =>
    apply ih z
    apply two_mul_emod_eq_zero_of_odd (((2 ^ k : Nat) : Int) * z) n hn_odd
    have h_eq : 2 * (((2 ^ k : Nat) : Int) * z) = ((2 ^ (k + 1) : Nat) : Int) * z := by
      rw [Nat.pow_succ, Int.natCast_mul]; grind
    rw [h_eq]
    exact h

private theorem pos_and_le_of_pow2_mul (k : Nat) (b b' : Int)
    (hb_pos : 0 < b) (hb'_nonneg : 0 ≤ b')
    (h_eq : ((2 ^ k : Nat) : Int) * b' = b) :
    0 < b' ∧ b' ≤ b := by
  have h_pow_nat : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have h_pow_pos : (1 : Int) ≤ ((2 ^ k : Nat) : Int) := by omega
  have hb'_pos : 0 < b' := by
    rcases Int.lt_trichotomy 0 b' with h_pos | h_zero | h_neg
    · exact h_pos
    · rw [← h_zero, Int.mul_zero] at h_eq; omega
    · omega
  have hb'_le : b' ≤ b := by
    have : 1 * b' ≤ ((2 ^ k : Nat) : Int) * b' :=
      Int.mul_le_mul_of_nonneg_right h_pow_pos hb'_nonneg
    omega
  exact ⟨hb'_pos, hb'_le⟩

/-! ### Multi-Limb Arithmetic and Loop Invariant Lemmas -/

private def beeuBound (σ τ : Nat) : Int := (σ + τ + 2 : Nat)

private structure BeeuInv (a N : Int) (σ τ : Nat) (B A X Y : Int) : Prop where
  N_odd : N % 2 = 1
  gcd_eq : Int.gcd A B = Int.gcd a N
  B_nonneg : 0 ≤ B
  B_le : B ≤ N
  A_pos : 0 < A
  A_le : A ≤ N
  X_inv : (a * X - B) % N = 0
  Y_inv : (a * Y + A) % N = 0
  B_shifted : ((2 ^ σ : Nat) : Int) * B ≤ N
  A_shifted : ((2 ^ τ : Nat) : Int) * A ≤ N
  X_lt : X < 2 * (N * beeuBound σ τ)
  X_lt_odd : B % 2 = 1 → X < N * beeuBound σ τ
  Y_lt : Y < 2 * (N * beeuBound σ τ)
  Y_lt_odd : A % 2 = 1 → Y < N * beeuBound σ τ

private theorem sp_sub_112_mod_16 (sp : BitVec 64) :
    (sp + 18446744073709551504#64) % 16#64 = sp % 16#64 := by grind

private theorem sp_add_112_cancel (sp : BitVec 64) :
    sp + 18446744073709551504#64 + 112#64 = sp := by grind

private theorem val256_of_limbs (bs : List UInt8) (h : bs.length = 32) :
    val256
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (bs.take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 8).take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 16).take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 24).take 8)))) =
      Int.ofBytes bs := by
  dsimp only [val256]
  rw [UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
      ofBytes_toNat_ofInt_64 _ (by simp [h]),
      ofBytes_toNat_ofInt_64 _ (by simp [h]),
      ofBytes_toNat_ofInt_64 _ (by simp [h]),
      ofBytes_toNat_ofInt_64 _ (by simp [h]),
      ofBytes_32_split bs h]

private theorem val256_nonneg (w0 w1 w2 w3 : UInt64) : 0 ≤ val256 w0 w1 w2 w3 := by
  dsimp [val256]; omega

private theorem val256_lt (w0 w1 w2 w3 : UInt64) : val256 w0 w1 w2 w3 < 256 ^ 32 := by
  have h0 : w0.toNat < 2 ^ 64 := w0.toBitVec.isLt
  have h1 : w1.toNat < 2 ^ 64 := w1.toBitVec.isLt
  have h2 : w2.toNat < 2 ^ 64 := w2.toBitVec.isLt
  have h3 : w3.toNat < 2 ^ 64 := w3.toBitVec.isLt
  dsimp [val256]; omega

private theorem val320_nonneg (w0 w1 w2 w3 w4 : UInt64) : 0 ≤ val320 w0 w1 w2 w3 w4 := by
  dsimp [val320]; omega

private theorem val320_lt (w0 w1 w2 w3 w4 : UInt64) : val320 w0 w1 w2 w3 w4 < 256 ^ 40 := by
  have h0 : w0.toNat < 2 ^ 64 := w0.toBitVec.isLt
  have h1 : w1.toNat < 2 ^ 64 := w1.toBitVec.isLt
  have h2 : w2.toNat < 2 ^ 64 := w2.toBitVec.isLt
  have h3 : w3.toNat < 2 ^ 64 := w3.toBitVec.isLt
  have h4 : w4.toNat < 2 ^ 64 := w4.toBitVec.isLt
  dsimp [val320]; omega

private theorem val256_eq_zero_limbs (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 = 0) :
    w0.toBitVec = 0#64 ∧ w1.toBitVec = 0#64 ∧ w2.toBitVec = 0#64 ∧ w3.toBitVec = 0#64 := by
  dsimp [val256] at h
  have hw0 : w0.toNat = 0 := by omega
  have hw1 : w1.toNat = 0 := by omega
  have hw2 : w2.toNat = 0 := by omega
  have hw3 : w3.toNat = 0 := by omega
  refine ⟨BitVec.eq_of_toNat_eq hw0, BitVec.eq_of_toNat_eq hw1,
          BitVec.eq_of_toNat_eq hw2, BitVec.eq_of_toNat_eq hw3⟩

private theorem val256_eq_one_limbs (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 = 1) :
    w0.toBitVec = 1#64 ∧ w1.toBitVec = 0#64 ∧ w2.toBitVec = 0#64 ∧ w3.toBitVec = 0#64 := by
  dsimp [val256] at h
  have hw0 : w0.toNat = 1 := by omega
  have hw1 : w1.toNat = 0 := by omega
  have hw2 : w2.toNat = 0 := by omega
  have hw3 : w3.toNat = 0 := by omega
  refine ⟨BitVec.eq_of_toNat_eq hw0, BitVec.eq_of_toNat_eq hw1,
          BitVec.eq_of_toNat_eq hw2, BitVec.eq_of_toNat_eq hw3⟩

private theorem val256_ne_one_or_ne_zero (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 ≠ 1) :
    ((w0.toBitVec - 1#64 ||| w1.toBitVec ||| w2.toBitVec ||| w3.toBitVec) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_zero
  have ⟨h0, h1, h2, h3⟩ := (or4_sub_one_eq_zero_iff w0.toBitVec w1.toBitVec w2.toBitVec w3.toBitVec).mp h_zero
  apply h
  dsimp [val256]
  have hw0 : w0.toNat = 1 := congrArg BitVec.toNat h0
  have hw1 : w1.toNat = 0 := congrArg BitVec.toNat h1
  have hw2 : w2.toNat = 0 := congrArg BitVec.toNat h2
  have hw3 : w3.toNat = 0 := congrArg BitVec.toNat h3
  omega

private theorem val320_lt_256_pow_32 (w0 w1 w2 w3 w4 : UInt64) (h : val320 w0 w1 w2 w3 w4 < 256 ^ 32) :
    w4 = 0 ∧ val256 w0 w1 w2 w3 = val320 w0 w1 w2 w3 w4 := by
  dsimp only [val320, val256] at h ⊢
  have hw4 : w4.toNat = 0 := by omega
  refine ⟨UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw4), by omega⟩

private theorem val256_pos_or_ne_zero (w0 w1 w2 w3 : UInt64) (h : 0 < val256 w0 w1 w2 w3) :
    ((w0.toBitVec ||| w1.toBitVec ||| w2.toBitVec ||| w3.toBitVec) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_zero
  have ⟨h0, h1, h2, h3⟩ := (or4_eq_zero_iff w0.toBitVec w1.toBitVec w2.toBitVec w3.toBitVec).mp h_zero
  have hw0 : w0.toNat = 0 := congrArg BitVec.toNat h0
  have hw1 : w1.toNat = 0 := congrArg BitVec.toNat h1
  have hw2 : w2.toNat = 0 := congrArg BitVec.toNat h2
  have hw3 : w3.toNat = 0 := congrArg BitVec.toNat h3
  dsimp [val256] at h
  omega

private theorem shift1_val320 (x0 x1 x2 x3 x4 : UInt64) :
    let w0 := UInt64.ofBitVec (extr1Word x1 x0)
    let w1 := UInt64.ofBitVec (extr1Word x2 x1)
    let w2 := UInt64.ofBitVec (extr1Word x3 x2)
    let w3 := UInt64.ofBitVec (extr1Word x4 x3)
    let w4 := UInt64.ofBitVec (x4.toBitVec >>> 1)
    2 * val320 w0 w1 w2 w3 w4 + (x0.toNat % 2 : Int) = val320 x0 x1 x2 x3 x4 := by
  have h0 := extr1Word_toNat x1 x0
  have h1 := extr1Word_toNat x2 x1
  have h2 := extr1Word_toNat x3 x2
  have h3 := extr1Word_toNat x4 x3
  have h4 := toNat_ofBitVec_ushiftRight_one x4
  dsimp only [val320]
  omega

private theorem val320_emod_two (x0 x1 x2 x3 x4 : UInt64) :
    val320 x0 x1 x2 x3 x4 % 2 = (x0.toNat % 2 : Int) := by
  dsimp only [val320]; omega

private theorem val256_emod_two (x0 x1 x2 x3 : UInt64) :
    val256 x0 x1 x2 x3 % 2 = (x0.toNat % 2 : Int) := by
  dsimp only [val256]; omega

private theorem shift256_val256 (b0 b1 b2 b3 : UInt64) (h_nz : ctzClamped b0 ≠ 0#64) :
    let k := ctzClamped b0
    let w0 := UInt64.ofBitVec (shift256Word b0 b1 k)
    let w1 := UInt64.ofBitVec (shift256Word b1 b2 k)
    let w2 := UInt64.ofBitVec (shift256Word b2 b3 k)
    let w3 := UInt64.ofBitVec (shift256TopWord b3 k)
    ((2 ^ k.toNat : Nat) : Int) * val256 w0 w1 w2 w3 = val256 b0 b1 b2 b3 := by
  let k := ctzClamped b0
  have hk63 : k ≤ 63#64 := clz_reverse_or_one_le_63 b0.toBitVec
  have hk1 : 1#64 ≤ k := by
    rw [BitVec.le_def]
    have : k.toNat ≠ 0 := fun h0 => h_nz (BitVec.eq_of_toNat_eq h0)
    change 1 ≤ k.toNat
    omega
  have h0 := shift256_limb_toNat b0 b1 k hk1 hk63
  have h1 := shift256_limb_toNat b1 b2 k hk1 hk63
  have h2 := shift256_limb_toNat b2 b3 k hk1 hk63
  have h3 := shift256_top_toNat b3 k hk63
  have hm0 : (b0.toBitVec &&& ((1#64 <<< (k % 64#64)) - 1#64)).toNat = 0 := by
    dsimp +zetaDelta only [ctzClamped]
    rw [and_mask_clz_reverse_or_one]
    rfl
  dsimp +zetaDelta only [val256] at h0 h1 h2 h3 ⊢
  rw [hm0] at h0
  grind

private theorem val256_odd_of_ctzClamped_eq_zero (b0 b1 b2 b3 : UInt64)
    (h : ctzClamped b0 = 0#64) : val256 b0 b1 b2 b3 % 2 = 1 := by
  rw [val256_emod_two]
  have h_lsb := getLsbD_zero_of_clz_reverse_or_one_eq_zero (by decide) h
  have := getLsbD_zero_eq_true_mod2 b0 h_lsb
  omega

private theorem shift256_val256_even_imp_clamped (b0 b1 b2 b3 : UInt64) :
    let k := ctzClamped b0
    val256 (UInt64.ofBitVec (shift256Word b0 b1 k)) (UInt64.ofBitVec (shift256Word b1 b2 k))
      (UInt64.ofBitVec (shift256Word b2 b3 k)) (UInt64.ofBitVec (shift256TopWord b3 k)) % 2 = 0 →
    k = 63#64 := by
  intro k h
  rw [val256_emod_two] at h
  rcases shift256Word_lsb_or_clamped b0.toBitVec b1.toBitVec with h1 | h1
  · exfalso
    have h2 : (UInt64.ofBitVec (shift256Word b0 b1 k)).toBitVec.getLsbD 0 = true := by
      rw [UInt64.toBitVec_ofBitVec, shift256Word_eq]; exact h1
    have := getLsbD_zero_eq_true_mod2 _ h2
    omega
  · exact h1

private theorem sub256_step (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    val256
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2)) -
      (if c3 then 0 else 1) * 256 ^ 32 =
      val256 b0 b1 b2 b3 - val256 a0 a1 a2 a3 := by
  have h0 := sub0_step b0 a0
  have h1 := sbc_step b1 a1 (sub0Carry b0 a0)
  have h2 := sbc_step b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))
  have h3 := sbc_step b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0)))
  dsimp only [val256]
  omega

private theorem sub256_carry_of_ge (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 ≥ val256 a0 a1 a2 a3) :
    sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))) = true := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  have h_lt := val256_lt
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
  dsimp +zetaDelta only at h_step h_lt
  revert h_step
  cases sbcCarry b3 a3 c2
  · intro h_step; simp only [Bool.false_eq_true, ↓reduceIte] at h_step; omega
  · intro _; rfl

private theorem sub256_val_of_ge (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 ≥ val256 a0 a1 a2 a3) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    val256
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2)) =
      val256 b0 b1 b2 b3 - val256 a0 a1 a2 a3 := by
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  dsimp +zetaDelta only at h_step ⊢
  have h_c := sub256_carry_of_ge b0 b1 b2 b3 a0 a1 a2 a3 h
  simp only [h_c, ↓reduceIte] at h_step
  omega

private theorem sub256_carry_of_lt (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 < val256 a0 a1 a2 a3) :
    sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))) = false := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  have h_nonneg := val256_nonneg
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
  dsimp +zetaDelta only at h_step h_nonneg
  revert h_step
  cases sbcCarry b3 a3 c2
  · intro _; rfl
  · intro h_step; simp only [↓reduceIte] at h_step; omega

private theorem add320_val_of_lt (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : UInt64)
    (h : val320 x0 x1 x2 x3 x4 + val320 y0 y1 y2 y3 y4 < 256 ^ 40) :
    let c0 := add0Carry x0 y0
    let c1 := adcCarry x1 y1 c0
    let c2 := adcCarry x2 y2 c1
    let c3 := adcCarry x3 y3 c2
    val320
      (UInt64.ofBitVec (add0Word x0 y0))
      (UInt64.ofBitVec (adcWord x1 y1 c0))
      (UInt64.ofBitVec (adcWord x2 y2 c1))
      (UInt64.ofBitVec (adcWord x3 y3 c2))
      (UInt64.ofBitVec (adcWord x4 y4 c3)) =
      val320 x0 x1 x2 x3 x4 + val320 y0 y1 y2 y3 y4 := by
  let c0 := add0Carry x0 y0
  let c1 := adcCarry x1 y1 c0
  let c2 := adcCarry x2 y2 c1
  let c3 := adcCarry x3 y3 c2
  have h0 := add0_step x0 y0
  have h1 := adc_step x1 y1 c0
  have h2 := adc_step x2 y2 c1
  have h3 := adc_step x3 y3 c2
  have h4 := adc_step x4 y4 c3
  have h_nonneg := val320_nonneg
    (UInt64.ofBitVec (add0Word x0 y0))
    (UInt64.ofBitVec (adcWord x1 y1 c0))
    (UInt64.ofBitVec (adcWord x2 y2 c1))
    (UInt64.ofBitVec (adcWord x3 y3 c2))
    (UInt64.ofBitVec (adcWord x4 y4 c3))
  dsimp +zetaDelta only [val320] at h0 h1 h2 h3 h4 h h_nonneg ⊢
  omega

private theorem sub320_step (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    let c4 := sbcCarry b4 a4 c3
    val320
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2))
      (UInt64.ofBitVec (sbcWord b4 a4 c3)) -
      (if c4 then 0 else 1) * 256 ^ 40 =
      val320 b0 b1 b2 b3 b4 - val320 a0 a1 a2 a3 a4 := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  let c3 := sbcCarry b3 a3 c2
  have h0 := sub0_step b0 a0
  have h1 := sbc_step b1 a1 c0
  have h2 := sbc_step b2 a2 c1
  have h3 := sbc_step b3 a3 c2
  have h4 := sbc_step b4 a4 c3
  dsimp +zetaDelta only [val320] at h0 h1 h2 h3 h4 ⊢
  omega

private theorem sub320_carry_of_ge (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64)
    (h : val320 b0 b1 b2 b3 b4 ≥ val320 a0 a1 a2 a3 a4) :
    sbcCarry b4 a4 (sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0)))) = true := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  let c3 := sbcCarry b3 a3 c2
  have h_step := sub320_step b0 b1 b2 b3 b4 a0 a1 a2 a3 a4
  have h_lt := val320_lt
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
    (UInt64.ofBitVec (sbcWord b4 a4 c3))
  dsimp +zetaDelta only at h_step h_lt
  revert h_step
  cases sbcCarry b4 a4 c3
  · intro h_step; simp only [Bool.false_eq_true, ↓reduceIte] at h_step; omega
  · intro _; rfl

private theorem sub320_carry_of_lt (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64)
    (h : val320 b0 b1 b2 b3 b4 < val320 a0 a1 a2 a3 a4) :
    sbcCarry b4 a4 (sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0)))) = false := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  let c3 := sbcCarry b3 a3 c2
  have h_step := sub320_step b0 b1 b2 b3 b4 a0 a1 a2 a3 a4
  have h_nonneg := val320_nonneg
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
    (UInt64.ofBitVec (sbcWord b4 a4 c3))
  dsimp +zetaDelta only at h_step h_nonneg
  revert h_step
  cases sbcCarry b4 a4 c3
  · intro _; rfl
  · intro h_step; simp only [↓reduceIte] at h_step; omega

private theorem sub320_val_of_ge (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64)
    (h : val320 b0 b1 b2 b3 b4 ≥ val320 a0 a1 a2 a3 a4) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    val320
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2))
      (UInt64.ofBitVec (sbcWord b4 a4 c3)) =
      val320 b0 b1 b2 b3 b4 - val320 a0 a1 a2 a3 a4 := by
  have h_step := sub320_step b0 b1 b2 b3 b4 a0 a1 a2 a3 a4
  dsimp +zetaDelta only at h_step ⊢
  have h_c := sub320_carry_of_ge b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 h
  simp only [h_c, ↓reduceIte] at h_step
  omega

private theorem beeuBound_pos (σ τ : Nat) : 0 < beeuBound σ τ := by
  unfold beeuBound; omega

private theorem beeuBound_add (σ τ k₁ k₂ : Nat) :
    beeuBound (σ + k₁) (τ + k₂) = beeuBound σ τ + k₁ + k₂ := by
  unfold beeuBound; omega

private theorem beeuBound_le (σ τ : Nat) (hσ : σ ≤ 255) (hτ : τ ≤ 255) :
    beeuBound σ τ ≤ 512 := by
  unfold beeuBound; omega

private theorem beeuBound_zero : beeuBound 0 0 = 2 := rfl

private theorem shift_bound_step (X X' N M : Int) (p : Nat) (hp : 2 ≤ p) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hX : X < 2 * (N * M)) (h : (p : Int) * X' ≤ X + ((p : Int) - 1) * N) : X' < N * (M + 1) := by
  rcases Int.lt_or_le X' (N * (M + 1)) with hlt | hle
  · exact hlt
  exfalso
  have h1 : (p : Int) * (N * (M + 1)) ≤ (p : Int) * X' :=
    Int.mul_le_mul_of_nonneg_left hle (by omega)
  have h2 : 2 * (N * M) ≤ (p : Int) * (N * M) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (Int.mul_nonneg hN hM)
  grind

private theorem shift_clamped_bound (X X₁ N M : Int) (hN : 0 ≤ N) (hM : M ≤ 512)
    (hX : X < 2 * (N * M))
    (h : ((2 ^ 63 : Nat) : Int) * X₁ ≤ X + (((2 ^ 63 : Nat) : Int) - 1) * N) :
    X₁ < N * 2 := by
  have hM_le : N * M ≤ N * 512 := Int.mul_le_mul_of_nonneg_left hM hN
  rcases Int.lt_or_le X₁ (N * 2) with hlt | hle
  · exact hlt
  exfalso
  have h1 : ((2 ^ 63 : Nat) : Int) * (N * 2) ≤ ((2 ^ 63 : Nat) : Int) * X₁ :=
    Int.mul_le_mul_of_nonneg_left hle (by decide)
  omega

private theorem update_bound_even (X₁ Y₁ N M M₂ : Int) (k₁ k₂ : Nat) (hN : 0 ≤ N)
    (hX : X₁ < N * (M + k₁)) (hY : Y₁ < N * (M + k₂)) (hM₂ : M + k₁ + k₂ ≤ M₂) :
    X₁ + Y₁ < 2 * (N * M₂) := by
  have : N * (M + k₁ + (M + k₂)) ≤ N * (2 * M₂) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hN
  grind

private theorem update_bound_clamped (X X₁ Y Y₁ N M M₂ : Int) (k₁ k₂ : Nat)
    (hN : 0 ≤ N) (hM_le : M ≤ 512)
    (hX : X < 2 * (N * M)) (hY : Y < 2 * (N * M))
    (hX₁ : X₁ < N * (M + k₁)) (hY₁ : Y₁ < N * (M + k₂))
    (hX_bnd : ((2 ^ k₁ : Nat) : Int) * X₁ ≤ X + (((2 ^ k₁ : Nat) : Int) - 1) * N)
    (hY_bnd : ((2 ^ k₂ : Nat) : Int) * Y₁ ≤ Y + (((2 ^ k₂ : Nat) : Int) - 1) * N)
    (hclamp : k₁ = 63 ∨ k₂ = 63) (hM₂ : M + k₁ + k₂ ≤ M₂) :
    X₁ + Y₁ < N * M₂ := by
  rcases hclamp with rfl | rfl
  · have hX2 := shift_clamped_bound X X₁ N M hN hM_le hX hX_bnd
    have : N * (2 + (M + k₂)) ≤ N * M₂ :=
      Int.mul_le_mul_of_nonneg_left (by omega) hN
    grind
  · have hY2 := shift_clamped_bound Y Y₁ N M hN hM_le hY hY_bnd
    have : N * ((M + k₁) + 2) ≤ N * M₂ :=
      Int.mul_le_mul_of_nonneg_left (by omega) hN
    grind

private theorem bound_mono_right (N M M' Z : Int) (hN : 0 ≤ N) (h : Z < N * M) (hM : M ≤ M') :
    Z < N * M' := by
  have := Int.mul_le_mul_of_nonneg_left hM hN
  omega

private theorem two_pow_le_imp_le_255 (σ : Nat) (N : Int) (h : ((2 ^ σ : Nat) : Int) ≤ N)
    (hN : N < 256 ^ 32) : σ ≤ 255 := by
  have h256 : ((2 ^ 256 : Nat) : Int) = 256 ^ 32 := by decide
  have h1 : ((2 ^ σ : Nat) : Int) < ((2 ^ 256 : Nat) : Int) := by rw [h256]; omega
  have h2 : (2 ^ σ : Nat) < 2 ^ 256 := by exact_mod_cast h1
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

private theorem BeeuInv.sigma_le {a N : Int} {σ τ : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ B A X Y) (hB : 0 < B) (hN : N < 256 ^ 32) : σ ≤ 255 := by
  have h0 : (0 : Int) ≤ ((2 ^ σ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ B by omega) h0
  have h2 := h.B_shifted
  exact two_pow_le_imp_le_255 σ N (by omega) hN

private theorem BeeuInv.tau_le {a N : Int} {σ τ : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ B A X Y) (hN : N < 256 ^ 32) : τ ≤ 255 := by
  have h0 : (0 : Int) ≤ ((2 ^ τ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ A by have := h.A_pos; omega) h0
  have h2 := h.A_shifted
  exact two_pow_le_imp_le_255 τ N (by omega) hN

private theorem BeeuInv.bounds {a N : Int} {σ τ : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ B A X Y) (hB : 0 < B) (hN : N < 256 ^ 32) :
    X < 256 ^ 40 / 2 ∧ Y < 256 ^ 40 / 2 ∧ beeuBound σ τ ≤ 512 := by
  have hσ := h.sigma_le hB hN
  have hτ := h.tau_le hN
  have hM := beeuBound_le σ τ hσ hτ
  have hN0 : 0 ≤ N := by have := h.A_pos; have := h.A_le; omega
  have h1 : N * beeuBound σ τ ≤ N * 512 := Int.mul_le_mul_of_nonneg_left hM hN0
  have hX := h.X_lt
  have hY := h.Y_lt
  exact ⟨by omega, by omega, hM⟩

private theorem shift_phase_bound (X X₁ N M B : Int) (k : Nat) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hX : X < 2 * (N * M)) (hX_odd : B % 2 = 1 → X < N * M)
    (hk : B % 2 = 0 → 1 ≤ k)
    (h : ((2 ^ k : Nat) : Int) * X₁ ≤ X + (((2 ^ k : Nat) : Int) - 1) * N) :
    X₁ < N * (M + k) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul, Int.sub_self, Int.zero_mul,
      Int.add_zero, Int.natCast_zero] at h ⊢
    have hB : B % 2 = 1 := by
      have h01 : B % 2 = 0 ∨ B % 2 = 1 := by omega
      rcases h01 with h0 | h1
      · exact absurd (hk h0) (by omega)
      · exact h1
    have := hX_odd hB
    omega
  · have hp : 2 ≤ 2 ^ k := Nat.one_lt_two_pow hk0
    have h1 := shift_bound_step X X₁ N M (2 ^ k) hp hN hM hX h
    exact bound_mono_right N (M + 1) (M + k) X₁ hN h1 (by omega)

private theorem shift_B_X_mod_inv (k : Nat) (a B B' X X' n : Int)
    (hn_odd : n % 2 = 1)
    (hB : ((2 ^ k : Nat) : Int) * B' = B)
    (hX : (((2 ^ k : Nat) : Int) * X') % n = X % n)
    (h_inv : (a * X - B) % n = 0) :
    (a * X' - B') % n = 0 := by
  apply pow2_mul_emod_eq_zero_of_odd k (a * X' - B') n hn_odd
  have h_lin : ((2 ^ k : Nat) : Int) * (a * X' - B') =
      a * (((2 ^ k : Nat) : Int) * X') - B := by
    rw [← hB]; grind
  rw [h_lin, Int.sub_emod, Int.mul_emod a, hX, ← Int.mul_emod, ← Int.sub_emod, h_inv]

private theorem shift_A_Y_mod_inv (k : Nat) (a A A' Y Y' n : Int)
    (hn_odd : n % 2 = 1)
    (hA : ((2 ^ k : Nat) : Int) * A' = A)
    (hY : (((2 ^ k : Nat) : Int) * Y') % n = Y % n)
    (h_inv : (a * Y + A) % n = 0) :
    (a * Y' + A') % n = 0 := by
  simpa [Int.sub_neg] using
    shift_B_X_mod_inv k a (-A) (-A') Y Y' n hn_odd (by grind) hY (by simpa [Int.sub_neg] using h_inv)

private theorem mod_inv_of_beeu_end (a y out n : Int)
    (hn_pos : 0 < n)
    (h_inv : (a * y + 1) % n = 0)
    (h_out : out = n - (y % n)) :
    0 < out ∧ out ≤ n ∧ (a * out) % n = 1 % n := by
  have hy_nonneg : 0 ≤ y % n := Int.emod_nonneg y (by omega)
  have hy_lt : y % n < n := Int.emod_lt_of_pos y hn_pos
  refine ⟨by omega, by omega, ?_⟩
  have h_sub_mod : (y - y % n) % n = 0 := by
    rw [Int.sub_emod, Int.emod_emod, Int.sub_self, Int.zero_emod]
  obtain ⟨q, hq⟩ : n ∣ a * y + 1 := Int.dvd_of_emod_eq_zero h_inv
  obtain ⟨k, hk⟩ : n ∣ y - y % n := Int.dvd_of_emod_eq_zero h_sub_mod
  have h_eq : a * out = 1 + (a - q + a * k) * n := by
    rw [h_out]; grind
  rw [h_eq, Int.add_emod, Int.mul_emod, Int.emod_self, Int.mul_zero,
    Int.zero_emod, Int.add_zero, Int.emod_emod]

/-! ### Memory-Instruction Stepping Helpers and Byte Splitting -/

private theorem ofInt_add_int64 (v : BitVec 64) (off : Int64) :
    BitVec.ofInt 64 (v.toInt + off.toInt) = v + BitVec.ofInt 64 off.toInt := by
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt]

private theorem checkSPAlignment_ok (base : RegOrSp .W64) (off : AddrOff) (s : MachineData)
    (ok : Unit → Effects)
    (h_align : base = .SP → s.regs.SP.toBitVec % 16#64 = 0#64) :
    AddrExpr.checkSPAlignment ⟨base, off⟩ s ok = ok () := by
  cases base with
  | low b _ =>
    cases b with
    | reg r => rfl
    | SP =>
      have h := h_align rfl
      simp only [AddrExpr.checkSPAlignment, Reg64s.getRegOrSp, RegOrSp.base,
        Reg64s.getRegOrSp64, BitVec.take, extractLsb'_0_64, h, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte]

private theorem step_add64_zero [WellFormedLayout beeu_mod_inverse_vartime]
    {k : Nat} {dst src : RegOrSp .W64}
    (hd : beeu_mod_inverse_vartime[k]? =
      some (.instr ⟨.W64, .ADD_e dst src (.imm ⟨.int64 0, .S0⟩)⟩))
    {regs : Reg64s} {status : StatusFlags} {dmem : DataMem} {post : MachineState → Prop}
    (h_cont :
      Eventually (step1 beeuExec) post
        ⟨⟨regs.setRegOrSp dst (regs.getRegOrSp64 src.base), status, dmem⟩,
         beeuExec.addrOf (k + 1)⟩) :
    Eventually (step1 beeuExec) post ⟨⟨regs, status, dmem⟩, beeuExec.addrOf k⟩ := by
  refine step_at hd ?_
  dsimp only [Directive.interp, Instr.interp, Operation.interp, ExtOrImmReg.interp, ConstExpr.interp,
    Reg64s.getRegOrSp, BitVec.take, MachineData.setRegOrSp, Effects.All]
  rw [extractLsb'_0_64, show BitVec.ofInt 64 (Int64.toInt 0) = 0#64 from rfl, BitVec.add_zero]
  exact h_cont

private theorem step_label [WellFormedLayout beeu_mod_inverse_vartime]
    {k : Nat} {l : Label} (hd : beeu_mod_inverse_vartime[k]? = some (.label l))
    {s : MachineData} {post : MachineState → Prop}
    (h_cont : Eventually (step1 beeuExec) post ⟨s, beeuExec.addrOf (k + 1)⟩) :
    Eventually (step1 beeuExec) post ⟨s, beeuExec.addrOf k⟩ := by
  refine step_at hd ?_
  simpa [Directive.interp, Effects.All] using h_cont

private theorem length_drop_take_8 {bs : List UInt8} {k n : Nat}
    (h : bs.length = n) (hk : k + 8 ≤ n) : ((bs.drop k).take 8).length = 8 := by
  simp only [List.length_take, List.length_drop, h]; omega

private theorem length_take_8 {bs : List UInt8} {n : Nat}
    (h : bs.length = n) (hn : 8 ≤ n) : (bs.take 8).length = 8 := by
  simp only [List.length_take, h]; omega

private theorem split_bytes (bs : List UInt8) (n : Nat) (p : BitVec 64)
    (hn : n ≤ bs.length) (h_bound : bs.length ≤ 2 ^ 64) :
    Eq (bs.At p) = Eq ((bs.take n).At p) ⋆ Eq ((bs.drop n).At (p + BitVec.ofNat 64 n)) := by
  have h := Mem.At_append_sep (bs.take n) (bs.drop n) p (by simp; omega)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

private theorem split_32_to_4x8 (bs : List UInt8) (p : BitVec 64) (h : bs.length = 32) :
    Eq (bs.At p) =
      Eq ((bs.take 8).At p) ⋆
      Eq (((bs.drop 8).take 8).At (p + 8#64)) ⋆
      Eq (((bs.drop 16).take 8).At (p + 16#64)) ⋆
      Eq (((bs.drop 24).take 8).At (p + 24#64)) := by
  rw [split_bytes bs 8 p (by omega) (by omega),
      split_bytes (bs.drop 8) 8 (p + 8#64) (by simp only [List.length_drop, h]; omega)
        (by simp only [List.length_drop, h]; omega),
      List.drop_drop,
      show p + 8#64 + 8#64 = p + 16#64 by grind,
      split_bytes (bs.drop 16) 8 (p + 16#64) (by simp only [List.length_drop, h]; omega)
        (by simp only [List.length_drop, h]; omega),
      List.drop_drop,
      show p + 16#64 + 8#64 = p + 24#64 by grind,
      List.take_of_length_le (l := bs.drop 24) (i := 8) (by simp only [List.length_drop, h]; omega)]
  ac_rfl

private theorem sep_pair_comm_right {A B R : DataMem → Prop} {m : DataMem}
    (h : m =⋆ B ⋆ (A ⋆ R)) : m =⋆ A ⋆ B ⋆ R := by
  have heq : (B ⋆ (A ⋆ R)) = (A ⋆ B ⋆ R) := by ac_rfl
  exact heq ▸ h

private theorem sep_pull_pair {D A B E R : DataMem → Prop} {m : DataMem}
    (h : m =⋆ D ⋆ ((A ⋆ B ⋆ E) ⋆ R)) : m =⋆ A ⋆ B ⋆ (D ⋆ (E ⋆ R)) := by
  have heq : (D ⋆ ((A ⋆ B ⋆ E) ⋆ R)) = (A ⋆ B ⋆ (D ⋆ (E ⋆ R))) := by ac_rfl
  exact heq ▸ h

private theorem sep_pull_pair_end {D A B R : DataMem → Prop} {m : DataMem}
    (h : m =⋆ D ⋆ ((A ⋆ B) ⋆ R)) : m =⋆ A ⋆ B ⋆ (D ⋆ R) := by
  have heq : (D ⋆ ((A ⋆ B) ⋆ R)) = (A ⋆ B ⋆ (D ⋆ R)) := by ac_rfl
  exact heq ▸ h

private theorem sep_push_pair {D A B R : DataMem → Prop} {m : DataMem}
    (h : m =⋆ A ⋆ B ⋆ (D ⋆ R)) : m =⋆ (D ⋆ (A ⋆ B)) ⋆ R := by
  have heq : (A ⋆ B ⋆ (D ⋆ R)) = ((D ⋆ (A ⋆ B)) ⋆ R) := by ac_rfl
  exact heq ▸ h

private theorem sep_pull_2nd {A B C D R : DataMem → Prop} {m : DataMem}
    (h : m =⋆ (A ⋆ B ⋆ C ⋆ D) ⋆ R) : m =⋆ C ⋆ D ⋆ ((A ⋆ B) ⋆ R) := by
  have heq : ((A ⋆ B ⋆ C ⋆ D) ⋆ R) = (C ⋆ D ⋆ ((A ⋆ B) ⋆ R)) := by ac_rfl
  exact heq ▸ h

private theorem sep_split_16 (bs : List UInt8) (k : Nat) (p a1 a2 a3 : BitVec 64)
    (h_len : k + 16 ≤ bs.length) (h_bound : bs.length ≤ 2 ^ 64)
    (h1 : a1 = p + BitVec.ofNat 64 k)
    (h2 : a2 = a1 + 8#64)
    (h3 : a3 = p + BitVec.ofNat 64 (k + 16)) :
    Eq ((bs.drop k).At a1) =
      Eq (((bs.drop k).take 8).At a1) ⋆
      Eq (((bs.drop (k + 8)).take 8).At a2) ⋆
      Eq ((bs.drop (k + 16)).At a3) := by
  have hlen1 : 8 ≤ (bs.drop k).length := by simp only [List.length_drop]; omega
  have hlen2 : 8 ≤ (bs.drop (k + 8)).length := by simp only [List.length_drop]; omega
  have hb1 : (bs.drop k).length ≤ 2 ^ 64 := by simp only [List.length_drop]; omega
  have hb2 : (bs.drop (k + 8)).length ≤ 2 ^ 64 := by simp only [List.length_drop]; omega
  have ha3 : a2 + 8#64 = a3 := by
    rw [h3, h2, h1, BitVec.add_assoc, BitVec.add_assoc]
    congr 1
    calc BitVec.ofNat 64 k + (8#64 + 8#64)
        = BitVec.ofNat 64 k + BitVec.ofNat 64 16 := rfl
      _ = BitVec.ofNat 64 (k + 16) := (BitVec.ofNat_add k 16).symm
  rw [split_bytes (bs.drop k) 8 a1 hlen1 hb1, List.drop_drop, ← h2,
      split_bytes (bs.drop (k + 8)) 8 a2 hlen2 hb2, List.drop_drop,
      show k + 8 + 8 = k + 16 by omega, ha3]
  ac_rfl

private theorem sep_split_16_end (bs : List UInt8) (k : Nat) (a1 a2 : BitVec 64)
    (h_len : bs.length = k + 16) (h2 : a2 = a1 + 8#64) :
    Eq ((bs.drop k).At a1) =
      Eq (((bs.drop k).take 8).At a1) ⋆
      Eq (((bs.drop (k + 8)).take 8).At a2) := by
  have hlen1 : 8 ≤ (bs.drop k).length := by simp only [List.length_drop, h_len]; omega
  have hb1 : (bs.drop k).length ≤ 2 ^ 64 := by simp only [List.length_drop, h_len]; omega
  rw [split_bytes (bs.drop k) 8 a1 hlen1 hb1, List.drop_drop, ← h2,
      List.take_of_length_le (l := bs.drop (k + 8)) (i := 8) (by simp only [List.length_drop, h_len]; omega)]

private theorem step_stp64_sp_pre [WellFormedLayout beeu_mod_inverse_vartime]
    {k : Nat} {r1 r2 : RegOrZr .W64} {off : Int64}
    (hd : beeu_mod_inverse_vartime[k]? =
      some (.instr ⟨.W64, .STP r1 r2 ⟨.SP, .imm ⟨.int64 off, some .Pre⟩⟩⟩))
    {regs : Reg64s} {status : StatusFlags} {dmem : DataMem}
    (bs1 bs2 : List UInt8) {R : DataMem → Prop} {post : MachineState → Prop}
    (h_align : regs.SP.toBitVec % 16#64 = 0#64)
    (addr addr2 : BitVec 64)
    (h_addr : addr = regs.SP.toBitVec + BitVec.ofInt 64 off.toInt)
    (h_addr2 : addr2 = addr + 8#64)
    (h_len1 : bs1.length = 8) (h_len2 : bs2.length = 8)
    (h_mem : dmem =⋆ Eq (bs1.At addr) ⋆ Eq (bs2.At addr2) ⋆ R)
    (h_cont : ∀ dmem',
      (dmem' =⋆
        Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆
        Eq ((Int.toBytes 8 (regs.getRegOrZr64 r2.base).toInt).At addr2) ⋆ R) →
      Eventually (step1 beeuExec) post
        ⟨⟨{ regs with SP := UInt64.ofBitVec addr }, status, dmem'⟩,
         beeuExec.addrOf (k + 1)⟩) :
    Eventually (step1 beeuExec) post ⟨⟨regs, status, dmem⟩, beeuExec.addrOf k⟩ := by
  subst h_addr2
  refine step_at hd ?_
  have h1 : dmem =⋆ Eq (bs1.At addr) ⋆ (Eq (bs2.At (addr + 8#64)) ⋆ R) := by
    simpa only [sep_assoc] using h_mem
  have h_st1 := Mem.storeInt_sep addr 8 bs1 (Eq (bs2.At (addr + 8#64)) ⋆ R) dmem
    ⟨h1, h_len1⟩ (regs.getRegOrZr64 r1.base).toInt
  have h2 : Mem.storeInt dmem addr 8 (regs.getRegOrZr64 r1.base).toInt =⋆
      Eq (bs2.At (addr + 8#64)) ⋆
      (Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆ R) := by
    have heq : (Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆
        (Eq (bs2.At (addr + 8#64)) ⋆ R)) =
        (Eq (bs2.At (addr + 8#64)) ⋆
        (Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆ R)) := by ac_rfl
    exact heq ▸ h_st1
  have h_st2 := Mem.storeInt_sep (addr + 8#64) 8 bs2
    (Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆ R) _
    ⟨h2, h_len2⟩ (regs.getRegOrZr64 r2.base).toInt
  dsimp only [Directive.interp, Instr.interp, Operation.interp, Effects.All]
  rw [checkSPAlignment_ok .SP _ ⟨regs, status, dmem⟩ _ (fun _ => h_align)]
  simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp, RegOrSp.base,
    Reg64s.getRegOrSp64, Reg64s.getRegOrZr, BitVec.take, extractLsb'_0_64, BitVec.signed,
    ofInt_add_int64, ← h_addr, Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
  rw [store_sep ⟨{ regs with SP := UInt64.ofBitVec addr }, status, dmem⟩ addr .W64 _ _ bs1 _ h1 h_len1]
  dsimp only [Effects.All, MemWidth.bytes]
  rw [store_sep _ (addr + 8#64) .W64 _ _ bs2 _ h2 h_len2]
  dsimp only [Effects.All, MemWidth.bytes]
  exact h_cont _ (sep_pair_comm_right h_st2)

private theorem step_stp64_offset [WellFormedLayout beeu_mod_inverse_vartime]
    {k : Nat} {r1 r2 : RegOrZr .W64} {base : RegOrSp .W64} {off : Int64}
    (hd : beeu_mod_inverse_vartime[k]? =
      some (.instr ⟨.W64, .STP r1 r2 ⟨base, .imm ⟨.int64 off, none⟩⟩⟩))
    {regs : Reg64s} {status : StatusFlags} {dmem : DataMem}
    (bs1 bs2 : List UInt8) {R : DataMem → Prop} {post : MachineState → Prop}
    (h_align : base = .SP → regs.SP.toBitVec % 16#64 = 0#64)
    (addr addr2 : BitVec 64)
    (h_addr : addr = regs.getRegOrSp64 base.base + BitVec.ofInt 64 off.toInt)
    (h_addr2 : addr2 = addr + 8#64)
    (h_len1 : bs1.length = 8) (h_len2 : bs2.length = 8)
    (h_mem : dmem =⋆ Eq (bs1.At addr) ⋆ Eq (bs2.At addr2) ⋆ R)
    (h_cont : ∀ dmem',
      (dmem' =⋆
        Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆
        Eq ((Int.toBytes 8 (regs.getRegOrZr64 r2.base).toInt).At addr2) ⋆ R) →
      Eventually (step1 beeuExec) post ⟨⟨regs, status, dmem'⟩, beeuExec.addrOf (k + 1)⟩) :
    Eventually (step1 beeuExec) post ⟨⟨regs, status, dmem⟩, beeuExec.addrOf k⟩ := by
  subst h_addr2
  refine step_at hd ?_
  have h1 : dmem =⋆ Eq (bs1.At addr) ⋆ (Eq (bs2.At (addr + 8#64)) ⋆ R) := by
    simpa only [sep_assoc] using h_mem
  have h_st1 := Mem.storeInt_sep addr 8 bs1 (Eq (bs2.At (addr + 8#64)) ⋆ R) dmem
    ⟨h1, h_len1⟩ (regs.getRegOrZr64 r1.base).toInt
  have h2 : Mem.storeInt dmem addr 8 (regs.getRegOrZr64 r1.base).toInt =⋆
      Eq (bs2.At (addr + 8#64)) ⋆
      (Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆ R) := by
    have heq : (Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆
        (Eq (bs2.At (addr + 8#64)) ⋆ R)) =
        (Eq (bs2.At (addr + 8#64)) ⋆
        (Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆ R)) := by ac_rfl
    exact heq ▸ h_st1
  have h_st2 := Mem.storeInt_sep (addr + 8#64) 8 bs2
    (Eq ((Int.toBytes 8 (regs.getRegOrZr64 r1.base).toInt).At addr) ⋆ R) _
    ⟨h2, h_len2⟩ (regs.getRegOrZr64 r2.base).toInt
  dsimp only [Directive.interp, Instr.interp, Operation.interp, Effects.All]
  rw [checkSPAlignment_ok base _ ⟨regs, status, dmem⟩ _ h_align]
  simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp, Reg64s.getRegOrZr,
    BitVec.take, extractLsb'_0_64, BitVec.signed, ofInt_add_int64, ← h_addr]
  rw [store_sep ⟨regs, status, dmem⟩ addr .W64 _ _ bs1 _ h1 h_len1]
  dsimp only [Effects.All, MemWidth.bytes]
  rw [store_sep _ (addr + 8#64) .W64 _ _ bs2 _ h2 h_len2]
  dsimp only [Effects.All, MemWidth.bytes]
  exact h_cont _ (sep_pair_comm_right h_st2)

private theorem step_ldp64_offset [WellFormedLayout beeu_mod_inverse_vartime]
    {k : Nat} {r1 r2 : RegOrZr .W64} {base : RegOrSp .W64} {off : Int64}
    (hd : beeu_mod_inverse_vartime[k]? =
      some (.instr ⟨.W64, .LDP r1 r2 ⟨base, .imm ⟨.int64 off, none⟩⟩⟩))
    {regs : Reg64s} {status : StatusFlags} {dmem : DataMem}
    (bs1 bs2 : List UInt8) {R : DataMem → Prop} {post : MachineState → Prop}
    (h_align : base = .SP → regs.SP.toBitVec % 16#64 = 0#64)
    (addr addr2 : BitVec 64)
    (h_addr : addr = regs.getRegOrSp64 base.base + BitVec.ofInt 64 off.toInt)
    (h_addr2 : addr2 = addr + 8#64)
    (h_len1 : bs1.length = 8) (h_len2 : bs2.length = 8)
    (h_mem : dmem =⋆ Eq (bs1.At addr) ⋆ Eq (bs2.At addr2) ⋆ R)
    (h_cont :
      Eventually (step1 beeuExec) post
        ⟨⟨(regs.setRegOrZr r1 (BitVec.ofInt 64 (Int.ofBytes bs1))).setRegOrZr r2
            (BitVec.ofInt 64 (Int.ofBytes bs2)), status, dmem⟩,
         beeuExec.addrOf (k + 1)⟩) :
    Eventually (step1 beeuExec) post ⟨⟨regs, status, dmem⟩, beeuExec.addrOf k⟩ := by
  subst h_addr2
  refine step_at hd ?_
  have h1 : dmem =⋆ Eq (bs1.At addr) ⋆ (Eq (bs2.At (addr + 8#64)) ⋆ R) := by
    simpa only [sep_assoc] using h_mem
  have h2 : dmem =⋆ Eq (bs2.At (addr + 8#64)) ⋆ (Eq (bs1.At addr) ⋆ R) := by
    have heq : (Eq (bs1.At addr) ⋆ (Eq (bs2.At (addr + 8#64)) ⋆ R)) =
        (Eq (bs2.At (addr + 8#64)) ⋆ (Eq (bs1.At addr) ⋆ R)) := by ac_rfl
    exact heq ▸ h1
  dsimp only [Directive.interp, Instr.interp, Operation.interp, Effects.All]
  rw [checkSPAlignment_ok base _ ⟨regs, status, dmem⟩ _ h_align]
  simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp, BitVec.take, extractLsb'_0_64,
    BitVec.signed, ofInt_add_int64, ← h_addr]
  rw [load_sep ⟨regs, status, dmem⟩ addr .W64 _ bs1 _ h1 h_len1]
  dsimp only [Effects.All]
  rw [load_sep ⟨regs, status, dmem⟩ (addr + 8#64) .W64 _ bs2 _ h2 h_len2]
  dsimp only [MachineData.setRegOrZr, Effects.All]
  exact h_cont

private theorem step_ldp64_sp_post [WellFormedLayout beeu_mod_inverse_vartime]
    {k : Nat} {r1 r2 : RegOrZr .W64} {off : Int64}
    (hd : beeu_mod_inverse_vartime[k]? =
      some (.instr ⟨.W64, .LDP r1 r2 ⟨.SP, .imm ⟨.int64 off, some .Post⟩⟩⟩))
    {regs : Reg64s} {status : StatusFlags} {dmem : DataMem}
    (bs1 bs2 : List UInt8) {R : DataMem → Prop} {post : MachineState → Prop}
    (h_align : regs.SP.toBitVec % 16#64 = 0#64)
    (addr addr2 : BitVec 64)
    (h_addr : addr = regs.SP.toBitVec)
    (h_addr2 : addr2 = addr + 8#64)
    (h_len1 : bs1.length = 8) (h_len2 : bs2.length = 8)
    (h_mem : dmem =⋆ Eq (bs1.At addr) ⋆ Eq (bs2.At addr2) ⋆ R)
    (h_cont :
      let regs1 := { regs with SP := UInt64.ofBitVec (addr + BitVec.ofInt 64 off.toInt) }
      Eventually (step1 beeuExec) post
        ⟨⟨(regs1.setRegOrZr r1 (BitVec.ofInt 64 (Int.ofBytes bs1))).setRegOrZr r2
            (BitVec.ofInt 64 (Int.ofBytes bs2)), status, dmem⟩,
         beeuExec.addrOf (k + 1)⟩) :
    Eventually (step1 beeuExec) post ⟨⟨regs, status, dmem⟩, beeuExec.addrOf k⟩ := by
  subst h_addr2
  refine step_at hd ?_
  have h1 : dmem =⋆ Eq (bs1.At addr) ⋆ (Eq (bs2.At (addr + 8#64)) ⋆ R) := by
    simpa only [sep_assoc] using h_mem
  have h2 : dmem =⋆ Eq (bs2.At (addr + 8#64)) ⋆ (Eq (bs1.At addr) ⋆ R) := by
    have heq : (Eq (bs1.At addr) ⋆ (Eq (bs2.At (addr + 8#64)) ⋆ R)) =
        (Eq (bs2.At (addr + 8#64)) ⋆ (Eq (bs1.At addr) ⋆ R)) := by ac_rfl
    exact heq ▸ h1
  dsimp only [Directive.interp, Instr.interp, Operation.interp, Effects.All]
  rw [checkSPAlignment_ok .SP _ ⟨regs, status, dmem⟩ _ (fun _ => h_align)]
  simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp, RegOrSp.base,
    Reg64s.getRegOrSp64, BitVec.take, extractLsb'_0_64, BitVec.signed, BitVec.ofInt_toInt,
    ofInt_add_int64, ← h_addr, Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
  rw [load_sep _ addr .W64 _ bs1 _ h1 h_len1]
  dsimp only [Effects.All]
  rw [load_sep _ (addr + 8#64) .W64 _ bs2 _ h2 h_len2]
  dsimp only [MachineData.setRegOrZr, Effects.All]
  exact h_cont

private theorem step_ldr64_sp_offset [WellFormedLayout beeu_mod_inverse_vartime]
    {k : Nat} {r : RegOrZr .W64} {off : Int64}
    (hd : beeu_mod_inverse_vartime[k]? =
      some (.instr ⟨.W64, .LDR r (.addr ⟨.SP, .imm ⟨.int64 off, none⟩⟩)⟩))
    {regs : Reg64s} {status : StatusFlags} {dmem : DataMem}
    (bs : List UInt8) {R : DataMem → Prop} {post : MachineState → Prop}
    (h_align : regs.SP.toBitVec % 16#64 = 0#64)
    (addr : BitVec 64) (h_addr : addr = regs.SP.toBitVec + BitVec.ofInt 64 off.toInt)
    (h_len : bs.length = 8)
    (h_mem : dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_cont :
      Eventually (step1 beeuExec) post
        ⟨⟨regs.setRegOrZr r (BitVec.ofInt 64 (Int.ofBytes bs)), status, dmem⟩,
         beeuExec.addrOf (k + 1)⟩) :
    Eventually (step1 beeuExec) post ⟨⟨regs, status, dmem⟩, beeuExec.addrOf k⟩ := by
  refine step_at hd ?_
  dsimp only [Directive.interp, Instr.interp, Operation.interp, AddrOrLit.interpLoad,
    AddrExpr.interpLoad, Effects.All]
  rw [checkSPAlignment_ok .SP _ ⟨regs, status, dmem⟩ _ (fun _ => h_align)]
  simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp, RegOrSp.base,
    Reg64s.getRegOrSp64, BitVec.take, extractLsb'_0_64, BitVec.signed,
    ofInt_add_int64, ← h_addr]
  rw [load_sep ⟨regs, status, dmem⟩ addr .W64 _ bs R h_mem h_len]
  dsimp only [MachineData.setRegOrZr, Effects.All]
  exact h_cont

/-! ### Epilogue and Prologue Specifications -/

private theorem beeu_finish_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (r₀ : Reg64s) (R : DataMem → Prop)
    (h_sp_align : r₀.SP.toBitVec % 16#64 = 0#64)
    (h_x29 : s.regs.X29 = UInt64.ofBitVec (r₀.SP.toBitVec + 18446744073709551504#64))
    (h_mem : s.dmem =⋆ BeeuStackFrame r₀ (r₀.SP.toBitVec + 18446744073709551504#64) ⋆ R) :
    Eventually (step1 beeuExec)
      (fun st =>
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
        st.data.regs.X0 = s.regs.X0 ∧
        st.data.regs.SP = r₀.SP ∧
        st.data.regs.X30 = r₀.X30 ∧
        CalleeSavedEq st.data.regs r₀ ∧
        (st.data.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R))
      ⟨s, beeuExec.addrOf 151⟩ := by
  obtain ⟨regs, status, dmem⟩ := s
  dsimp only at h_x29 h_mem ⊢
  let sp' := r₀.SP.toBitVec + 18446744073709551504#64
  have h_sp'_align : sp' % 16#64 = 0#64 := by
    dsimp only [sp']; rw [sp_sub_112_mod_16]; exact h_sp_align
  -- Peel `BeeuStackFrame` into 6 opaque 16-byte pairs + tail (no large AC calls).
  let P0 : DataMem → Prop :=
    Eq ((Int.toBytes 8 r₀.X29.toBitVec.toInt).At sp') ⋆
    Eq ((Int.toBytes 8 r₀.X30.toBitVec.toInt).At (sp' + 8#64))
  let P1 : DataMem → Prop :=
    Eq ((Int.toBytes 8 r₀.X19.toBitVec.toInt).At (sp' + 16#64)) ⋆
    Eq ((Int.toBytes 8 r₀.X20.toBitVec.toInt).At (sp' + 24#64))
  let P2 : DataMem → Prop :=
    Eq ((Int.toBytes 8 r₀.X21.toBitVec.toInt).At (sp' + 32#64)) ⋆
    Eq ((Int.toBytes 8 r₀.X22.toBitVec.toInt).At (sp' + 40#64))
  let P3 : DataMem → Prop :=
    Eq ((Int.toBytes 8 r₀.X23.toBitVec.toInt).At (sp' + 48#64)) ⋆
    Eq ((Int.toBytes 8 r₀.X24.toBitVec.toInt).At (sp' + 56#64))
  let P4 : DataMem → Prop :=
    Eq ((Int.toBytes 8 r₀.X25.toBitVec.toInt).At (sp' + 64#64)) ⋆
    Eq ((Int.toBytes 8 r₀.X26.toBitVec.toInt).At (sp' + 72#64))
  let P5 : DataMem → Prop :=
    Eq ((Int.toBytes 8 r₀.X27.toBitVec.toInt).At (sp' + 80#64)) ⋆
    Eq ((Int.toBytes 8 r₀.X28.toBitVec.toInt).At (sp' + 88#64))
  let P6 : DataMem → Prop :=
    Eq ((Int.toBytes 8 r₀.X0.toBitVec.toInt).At (sp' + 96#64)) ⋆
    Eq ((Int.toBytes 8 r₀.X2.toBitVec.toInt).At (sp' + 104#64)) ⋆ R
  have h_frame_grp : dmem =⋆ P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 := by
    have h := h_mem
    dsimp only [BeeuStackFrame, BeeuSavedRegs] at h
    dsimp only [P0, P1, P2, P3, P4, P5, P6]
    simpa only [sep_assoc] using h
  -- 151: label .Lbeeu_finish
  refine step_label rfl ?_
  -- 152: add sp, x29, #0
  refine step_add64_zero (k := 152) rfl ?_
  dsimp only [RegOrSp.base, Reg64s.getRegOrSp64, Reg64s.getXReg,
    Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
  rw [h_x29, UInt64.toBitVec_ofBitVec]
  -- 153: ldp x19, x20, [sp, #16]
  have hm1 : dmem =⋆ P1 ⋆ (P0 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) := by
    have heq : (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) = (P1 ⋆ (P0 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6)) := by ac_rfl
    exact heq ▸ h_frame_grp
  refine step_ldp64_offset (k := 153) rfl
    (Int.toBytes 8 r₀.X19.toBitVec.toInt) (Int.toBytes 8 r₀.X20.toBitVec.toInt)
    (fun _ => h_sp'_align) (sp' + 16#64) (sp' + 24#64) rfl (BitVec.add_assoc sp' 16#64 8#64).symm
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (by dsimp only [P1] at hm1; exact hm1) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 154: ldp x21, x22, [sp, #32]
  have hm2 : dmem =⋆ P2 ⋆ (P0 ⋆ P1 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) := by
    have heq : (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) = (P2 ⋆ (P0 ⋆ P1 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6)) := by ac_rfl
    exact heq ▸ h_frame_grp
  refine step_ldp64_offset (k := 154) rfl
    (Int.toBytes 8 r₀.X21.toBitVec.toInt) (Int.toBytes 8 r₀.X22.toBitVec.toInt)
    (fun _ => h_sp'_align) (sp' + 32#64) (sp' + 40#64) rfl (BitVec.add_assoc sp' 32#64 8#64).symm
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (by dsimp only [P2] at hm2; exact hm2) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 155: ldp x23, x24, [sp, #48]
  have hm3 : dmem =⋆ P3 ⋆ (P0 ⋆ P1 ⋆ P2 ⋆ P4 ⋆ P5 ⋆ P6) := by
    have heq : (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) = (P3 ⋆ (P0 ⋆ P1 ⋆ P2 ⋆ P4 ⋆ P5 ⋆ P6)) := by ac_rfl
    exact heq ▸ h_frame_grp
  refine step_ldp64_offset (k := 155) rfl
    (Int.toBytes 8 r₀.X23.toBitVec.toInt) (Int.toBytes 8 r₀.X24.toBitVec.toInt)
    (fun _ => h_sp'_align) (sp' + 48#64) (sp' + 56#64) rfl (BitVec.add_assoc sp' 48#64 8#64).symm
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (by dsimp only [P3] at hm3; exact hm3) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 156: ldp x25, x26, [sp, #64]
  have hm4 : dmem =⋆ P4 ⋆ (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P5 ⋆ P6) := by
    have heq : (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) = (P4 ⋆ (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P5 ⋆ P6)) := by ac_rfl
    exact heq ▸ h_frame_grp
  refine step_ldp64_offset (k := 156) rfl
    (Int.toBytes 8 r₀.X25.toBitVec.toInt) (Int.toBytes 8 r₀.X26.toBitVec.toInt)
    (fun _ => h_sp'_align) (sp' + 64#64) (sp' + 72#64) rfl (BitVec.add_assoc sp' 64#64 8#64).symm
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (by dsimp only [P4] at hm4; exact hm4) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 157: ldp x27, x28, [sp, #80]
  have hm5 : dmem =⋆ P5 ⋆ (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P6) := by
    have heq : (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) = (P5 ⋆ (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P6)) := by ac_rfl
    exact heq ▸ h_frame_grp
  refine step_ldp64_offset (k := 157) rfl
    (Int.toBytes 8 r₀.X27.toBitVec.toInt) (Int.toBytes 8 r₀.X28.toBitVec.toInt)
    (fun _ => h_sp'_align) (sp' + 80#64) (sp' + 88#64) rfl (BitVec.add_assoc sp' 80#64 8#64).symm
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (by dsimp only [P5] at hm5; exact hm5) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 158: ldp x29, x30, [sp], #112
  have hm0 : dmem =⋆ P0 ⋆ (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) := by
    have heq : (P0 ⋆ P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6) = (P0 ⋆ (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6)) := by ac_rfl
    exact heq ▸ h_frame_grp
  refine step_ldp64_sp_post (k := 158) rfl
    (Int.toBytes 8 r₀.X29.toBitVec.toInt) (Int.toBytes 8 r₀.X30.toBitVec.toInt)
    h_sp'_align sp' (sp' + 8#64) rfl rfl
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (by dsimp only [P0] at hm0; exact hm0) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 159: ret
  refine step_at (k := 159) rfl ?_
  dsimp only [Directive.interp, Instr.interp, Operation.interp, Reg64s.getRegOrZr, RegOrZr.base,
    Reg64s.getRegOrZr64, Reg64s.getXReg, BitVec.take, BitVec.signed, Effects.All]
  simp only [extractLsb'_0_64, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, UInt64.ofBitVec_toBitVec,
    show BitVec.ofInt 64 (Int64.toInt 112) = 112#64 from rfl]
  refine .done _ ⟨rfl, rfl, ?_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, h_mem⟩
  dsimp only [sp']
  rw [sp_add_112_cancel, UInt64.ofBitVec_toBitVec]

private theorem beeu_epilogue_err_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (r₀ : Reg64s) (R : DataMem → Prop)
    (h_sp_align : r₀.SP.toBitVec % 16#64 = 0#64)
    (h_x29 : s.regs.X29 = UInt64.ofBitVec (r₀.SP.toBitVec + 18446744073709551504#64))
    (h_mem : s.dmem =⋆ BeeuStackFrame r₀ (r₀.SP.toBitVec + 18446744073709551504#64) ⋆ R) :
    Eventually (step1 beeuExec)
      (fun st =>
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
        st.data.regs.X0 = 0 ∧
        st.data.regs.SP = r₀.SP ∧
        st.data.regs.X30 = r₀.X30 ∧
        CalleeSavedEq st.data.regs r₀ ∧
        (st.data.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R))
      ⟨s, beeuExec.addrOf 149⟩ := by
  refine step_label rfl ?_
  refine step_at (k := 150) rfl ?_
  dsimp only [Directive.interp, Instr.interp, Operation.interp, ShiftRegExpr.interp,
    Reg64s.getRegOrZr, RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg,
    BitVec.take, Effects.All]
  simp only [extractLsb'_0_64, show (Int64.toInt 0).toNat = 0 from rfl,
    BitVec.shiftLeft_zero, BitVec.xor_self]
  exact beeu_finish_correct { s with regs := { s.regs with X0 := UInt64.ofBitVec 0#64 } }
    r₀ R h_sp_align h_x29 h_mem

private theorem beeu_prologue_init_regs [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 27 ∧
        st.data.dmem = s.dmem ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.X0 = s.regs.X0 ∧
        st.data.regs.X1 = s.regs.X1 ∧
        st.data.regs.X2 = s.regs.X2 ∧
        st.data.regs.X30 = s.regs.X30 ∧
        st.data.regs.X25 = s.regs.X25 ∧
        st.data.regs.X26 = s.regs.X26 ∧
        st.data.regs.X27 = s.regs.X27 ∧
        st.data.regs.X28 = s.regs.X28 ∧
        st.data.regs.X21 = s.regs.X0 ∧
        st.data.regs.X22 = s.regs.X1 ∧
        st.data.regs.X23 = s.regs.X2 ∧
        st.data.regs.X24 = s.regs.X30 ∧
        beeuX st.data.regs = 1 ∧
        beeuY st.data.regs = 0)
      ⟨s, beeuExec.addrOf 13⟩ := by
  sym => kstep 14; tactic =>
  refine .done _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply UInt64.eq_of_toBitVec_eq; dsimp +zetaDelta only; simp
  · apply UInt64.eq_of_toBitVec_eq; dsimp +zetaDelta only; simp
  · apply UInt64.eq_of_toBitVec_eq; dsimp +zetaDelta only; simp
  · apply UInt64.eq_of_toBitVec_eq; dsimp +zetaDelta only; simp
  · dsimp +zetaDelta only [beeuX, val320]
    simp only [extractLsb'_0_64, show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero,
      BitVec.xor_self, show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
    decide
  · dsimp +zetaDelta only [beeuY, val320]
    simp only [extractLsb'_0_64, show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero,
      BitVec.xor_self]
    decide

private theorem beeu_prologue_save_stack [WellFormedLayout beeu_mod_inverse_vartime]
    (s₀ : MachineData) (stack : List UInt8) (R_rest : DataMem → Prop)
    (h_sp_align : s₀.regs.SP.toBitVec % 16#64 = 0#64)
    (h_stack_len : stack.length = 112)
    (h_mem : s₀.dmem =⋆
      Eq (stack.At (s₀.regs.SP.toBitVec + 18446744073709551504#64)) ⋆ R_rest) :
    Eventually (step1 beeuExec)
      (fun st =>
        let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
        st.pc = beeuExec.addrOf 9 ∧
        st.data.regs = { s₀.regs with SP := UInt64.ofBitVec sp', X29 := UInt64.ofBitVec sp' } ∧
        (st.data.dmem =⋆ BeeuStackFrame s₀.regs sp' ⋆ R_rest))
      ⟨s₀, beeuExec.addrOf 0⟩ := by
  obtain ⟨r₀, status₀, dmem₀⟩ := s₀
  dsimp only at h_sp_align h_mem ⊢
  let sp' := r₀.SP.toBitVec + 18446744073709551504#64
  have h_sp'_align : sp' % 16#64 = 0#64 := by
    dsimp only [sp']; rw [sp_sub_112_mod_16]; exact h_sp_align
  have h_m0 : dmem₀ =⋆ Eq ((stack.drop 0).At sp') ⋆ R_rest := by
    simpa only [List.drop_zero] using h_mem
  rw [sep_split_16 stack 0 sp' sp' (sp' + 8#64) (sp' + 16#64)
        (by omega) (by omega) (by simp) rfl rfl] at h_m0
  -- 0: label beeu_mod_inverse_vartime
  refine step_label rfl ?_
  -- 1: stp x29, x30, [sp, #-112]!
  refine step_stp64_sp_pre (k := 1) rfl
    ((stack.drop 0).take 8) ((stack.drop 8).take 8)
    h_sp_align sp' (sp' + 8#64) rfl rfl
    (length_drop_take_8 h_stack_len (by decide))
    (length_drop_take_8 h_stack_len (by decide))
    (by simpa only [sep_assoc] using h_m0) ?_
  intro dm1 h_dm1
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at h_dm1
  -- 2: add x29, sp, #0
  refine step_add64_zero (k := 2) rfl ?_
  dsimp only [RegOrSp.base, Reg64s.getRegOrSp64, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
    Reg64s.setXReg]
  -- 3: stp x19, x20, [sp, #16]
  rw [sep_split_16 stack 16 sp' (sp' + 16#64) (sp' + 24#64) (sp' + 32#64)
        (by omega) (by omega) rfl (BitVec.add_assoc sp' 16#64 8#64).symm rfl] at h_dm1
  refine step_stp64_offset (k := 3) rfl
    ((stack.drop 16).take 8) ((stack.drop 24).take 8)
    (fun _ => h_sp'_align) (sp' + 16#64) (sp' + 24#64) rfl (BitVec.add_assoc sp' 16#64 8#64).symm
    (length_drop_take_8 h_stack_len (by decide))
    (length_drop_take_8 h_stack_len (by decide)) (sep_pull_pair h_dm1) ?_
  intro dm2 h_dm2
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at h_dm2
  have h_dm2 := sep_push_pair h_dm2
  -- 4: stp x21, x22, [sp, #32]
  rw [sep_split_16 stack 32 sp' (sp' + 32#64) (sp' + 40#64) (sp' + 48#64)
        (by omega) (by omega) rfl (BitVec.add_assoc sp' 32#64 8#64).symm rfl] at h_dm2
  refine step_stp64_offset (k := 4) rfl
    ((stack.drop 32).take 8) ((stack.drop 40).take 8)
    (fun _ => h_sp'_align) (sp' + 32#64) (sp' + 40#64) rfl (BitVec.add_assoc sp' 32#64 8#64).symm
    (length_drop_take_8 h_stack_len (by decide))
    (length_drop_take_8 h_stack_len (by decide)) (sep_pull_pair h_dm2) ?_
  intro dm3 h_dm3
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at h_dm3
  have h_dm3 := sep_push_pair h_dm3
  -- 5: stp x23, x24, [sp, #48]
  rw [sep_split_16 stack 48 sp' (sp' + 48#64) (sp' + 56#64) (sp' + 64#64)
        (by omega) (by omega) rfl (BitVec.add_assoc sp' 48#64 8#64).symm rfl] at h_dm3
  refine step_stp64_offset (k := 5) rfl
    ((stack.drop 48).take 8) ((stack.drop 56).take 8)
    (fun _ => h_sp'_align) (sp' + 48#64) (sp' + 56#64) rfl (BitVec.add_assoc sp' 48#64 8#64).symm
    (length_drop_take_8 h_stack_len (by decide))
    (length_drop_take_8 h_stack_len (by decide)) (sep_pull_pair h_dm3) ?_
  intro dm4 h_dm4
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at h_dm4
  have h_dm4 := sep_push_pair h_dm4
  -- 6: stp x25, x26, [sp, #64]
  rw [sep_split_16 stack 64 sp' (sp' + 64#64) (sp' + 72#64) (sp' + 80#64)
        (by omega) (by omega) rfl (BitVec.add_assoc sp' 64#64 8#64).symm rfl] at h_dm4
  refine step_stp64_offset (k := 6) rfl
    ((stack.drop 64).take 8) ((stack.drop 72).take 8)
    (fun _ => h_sp'_align) (sp' + 64#64) (sp' + 72#64) rfl (BitVec.add_assoc sp' 64#64 8#64).symm
    (length_drop_take_8 h_stack_len (by decide))
    (length_drop_take_8 h_stack_len (by decide)) (sep_pull_pair h_dm4) ?_
  intro dm5 h_dm5
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at h_dm5
  have h_dm5 := sep_push_pair h_dm5
  -- 7: stp x27, x28, [sp, #80]
  rw [sep_split_16 stack 80 sp' (sp' + 80#64) (sp' + 88#64) (sp' + 96#64)
        (by omega) (by omega) rfl (BitVec.add_assoc sp' 80#64 8#64).symm rfl] at h_dm5
  refine step_stp64_offset (k := 7) rfl
    ((stack.drop 80).take 8) ((stack.drop 88).take 8)
    (fun _ => h_sp'_align) (sp' + 80#64) (sp' + 88#64) rfl (BitVec.add_assoc sp' 80#64 8#64).symm
    (length_drop_take_8 h_stack_len (by decide))
    (length_drop_take_8 h_stack_len (by decide)) (sep_pull_pair h_dm5) ?_
  intro dm6 h_dm6
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at h_dm6
  have h_dm6 := sep_push_pair h_dm6
  -- 8: stp x0, x2, [sp, #96]
  rw [sep_split_16_end stack 96 (sp' + 96#64) (sp' + 104#64) h_stack_len
        (BitVec.add_assoc sp' 96#64 8#64).symm] at h_dm6
  refine step_stp64_offset (k := 8) rfl
    ((stack.drop 96).take 8) ((stack.drop 104).take 8)
    (fun _ => h_sp'_align) (sp' + 96#64) (sp' + 104#64) rfl (BitVec.add_assoc sp' 96#64 8#64).symm
    (length_drop_take_8 h_stack_len (by decide))
    (length_drop_take_8 h_stack_len (by decide)) (sep_pull_pair_end h_dm6) ?_
  intro dm7 h_dm7
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at h_dm7
  refine .done _ ⟨rfl, rfl, ?_⟩
  have h1 := sep_push_pair h_dm7
  dsimp only [BeeuStackFrame, BeeuSavedRegs] at h1 ⊢
  simpa only [sep_assoc] using h1

private theorem beeu_prologue_load_inputs [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (a_bs n_bs : List UInt8) (R_frame : DataMem → Prop)
    (h_a_len : a_bs.length = 32)
    (h_n_len : n_bs.length = 32)
    (h_mem : s.dmem =⋆ R_frame ⋆ Eq (a_bs.At s.regs.X1.toBitVec) ⋆ Eq (n_bs.At s.regs.X2.toBitVec)) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 27 ∧
        st.data.dmem = s.dmem ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        beeuB st.data.regs = Int.ofBytes a_bs ∧
        beeuA st.data.regs = Int.ofBytes n_bs ∧
        beeuN st.data.regs = Int.ofBytes n_bs ∧
        beeuX st.data.regs = 1 ∧
        beeuY st.data.regs = 0)
      ⟨s, beeuExec.addrOf 9⟩ := by
  obtain ⟨regs, status, dmem⟩ := s
  dsimp only at h_mem ⊢
  have h_a : dmem =⋆ Eq (a_bs.At regs.X1.toBitVec) ⋆ (R_frame ⋆ Eq (n_bs.At regs.X2.toBitVec)) := by
    have heq : (R_frame ⋆ Eq (a_bs.At regs.X1.toBitVec) ⋆ Eq (n_bs.At regs.X2.toBitVec)) =
        (Eq (a_bs.At regs.X1.toBitVec) ⋆ (R_frame ⋆ Eq (n_bs.At regs.X2.toBitVec))) := by ac_rfl
    exact heq ▸ h_mem
  rw [split_32_to_4x8 a_bs regs.X1.toBitVec h_a_len] at h_a
  have h_n : dmem =⋆ Eq (n_bs.At regs.X2.toBitVec) ⋆ (R_frame ⋆ Eq (a_bs.At regs.X1.toBitVec)) := by
    have heq : (R_frame ⋆ Eq (a_bs.At regs.X1.toBitVec) ⋆ Eq (n_bs.At regs.X2.toBitVec)) =
        (Eq (n_bs.At regs.X2.toBitVec) ⋆ (R_frame ⋆ Eq (a_bs.At regs.X1.toBitVec))) := by ac_rfl
    exact heq ▸ h_mem
  rw [split_32_to_4x8 n_bs regs.X2.toBitVec h_n_len] at h_n
  -- 9: ldp x25, x26, [x1]
  refine step_ldp64_offset (k := 9) rfl
    (a_bs.take 8) ((a_bs.drop 8).take 8)
    (fun h => by cases h) regs.X1.toBitVec (regs.X1.toBitVec + 8#64)
    (by simp [RegOrSp.base, Reg64s.getRegOrSp64, Reg64s.getXReg]) rfl
    (length_take_8 h_a_len (by decide))
    (length_drop_take_8 h_a_len (by decide))
    (by simpa only [sep_assoc] using h_a) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 10: ldp x27, x28, [x1, #16]
  refine step_ldp64_offset (k := 10) rfl
    ((a_bs.drop 16).take 8) ((a_bs.drop 24).take 8)
    (fun h => by cases h) (regs.X1.toBitVec + 16#64) (regs.X1.toBitVec + 24#64)
    rfl (BitVec.add_assoc regs.X1.toBitVec 16#64 8#64).symm
    (length_drop_take_8 h_a_len (by decide))
    (length_drop_take_8 h_a_len (by decide))
    (sep_pull_2nd h_a) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 11: ldp x0, x1, [x2]
  refine step_ldp64_offset (k := 11) rfl
    (n_bs.take 8) ((n_bs.drop 8).take 8)
    (fun h => by cases h) regs.X2.toBitVec (regs.X2.toBitVec + 8#64)
    (by simp [RegOrSp.base, Reg64s.getRegOrSp64, Reg64s.getXReg]) rfl
    (length_take_8 h_n_len (by decide))
    (length_drop_take_8 h_n_len (by decide))
    (by simpa only [sep_assoc] using h_n) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 12: ldp x2, x30, [x2, #16]
  refine step_ldp64_offset (k := 12) rfl
    ((n_bs.drop 16).take 8) ((n_bs.drop 24).take 8)
    (fun h => by cases h) (regs.X2.toBitVec + 16#64) (regs.X2.toBitVec + 24#64)
    rfl (BitVec.add_assoc regs.X2.toBitVec 16#64 8#64).symm
    (length_drop_take_8 h_n_len (by decide))
    (length_drop_take_8 h_n_len (by decide))
    (sep_pull_2nd h_n) ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  -- 13..26: register initialization
  refine eventually_weaken _ _ _ _ ?_ (beeu_prologue_init_regs _)
  rintro st ⟨hpc, hdmem, hsp, hx29, hx0, hx1, hx2, hx30, hx25, hx26, hx27, hx28,
    hx21, hx22, hx23, hx24, hX, hY⟩
  refine ⟨hpc, hdmem, hsp, hx29, ?_, ?_, ?_, hX, hY⟩
  · dsimp only [beeuB]; rw [hx25, hx26, hx27, hx28]; exact val256_of_limbs a_bs h_a_len
  · dsimp only [beeuA]; rw [hx21, hx22, hx23, hx24]; exact val256_of_limbs n_bs h_n_len
  · dsimp only [beeuN]; rw [hx0, hx1, hx2, hx30]; exact val256_of_limbs n_bs h_n_len

private theorem beeu_prologue_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s₀ : MachineData) (stack a_bs n_bs : List UInt8) (R : DataMem → Prop)
    (h_sp_align : s₀.regs.SP.toBitVec % 16#64 = 0#64)
    (h_stack_len : stack.length = 112)
    (h_a_len : a_bs.length = 32)
    (h_n_len : n_bs.length = 32)
    (h_mem : s₀.dmem =⋆
      Eq (stack.At (s₀.regs.SP.toBitVec + 18446744073709551504#64)) ⋆
      Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆
      Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R) :
    Eventually (step1 beeuExec)
      (fun st =>
        let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
        st.pc = beeuExec.addrOf 27 ∧
        st.data.regs.SP.toBitVec = sp' ∧
        st.data.regs.X29.toBitVec = sp' ∧
        beeuB st.data.regs = Int.ofBytes a_bs ∧
        beeuA st.data.regs = Int.ofBytes n_bs ∧
        beeuN st.data.regs = Int.ofBytes n_bs ∧
        beeuX st.data.regs = 1 ∧
        beeuY st.data.regs = 0 ∧
        (st.data.dmem =⋆
          BeeuStackFrame s₀.regs sp' ⋆
          Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆
          Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R))
      ⟨s₀, beeuExec.addrOf 0⟩ := by
  let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
  let R_rest : DataMem → Prop := Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆ Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R
  have h_mem0 : s₀.dmem =⋆ Eq (stack.At sp') ⋆ R_rest := by
    dsimp only [R_rest]; simpa only [sep_assoc] using h_mem
  refine eventually_trans _ _ _ _ (beeu_prologue_save_stack s₀ stack R_rest h_sp_align h_stack_len h_mem0) ?_
  rintro ⟨s1, pc1⟩ ⟨hpc1, hregs1, hmem1⟩
  dsimp only at hpc1 hregs1 hmem1
  subst hpc1
  have hmem1' : s1.dmem =⋆ (BeeuStackFrame s₀.regs sp' ⋆ R) ⋆
      Eq (a_bs.At s1.regs.X1.toBitVec) ⋆ Eq (n_bs.At s1.regs.X2.toBitVec) := by
    have h1 : s1.regs.X1 = s₀.regs.X1 := by rw [hregs1]
    have h2 : s1.regs.X2 = s₀.regs.X2 := by rw [hregs1]
    rw [h1, h2]
    dsimp only [R_rest] at hmem1
    have heq : (BeeuStackFrame s₀.regs sp' ⋆ (Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆
        Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R)) =
        ((BeeuStackFrame s₀.regs sp' ⋆ R) ⋆
        Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆ Eq (n_bs.At s₀.regs.X2.toBitVec)) := by ac_rfl
    exact heq ▸ hmem1
  refine eventually_weaken _ _ _ _ ?_
    (beeu_prologue_load_inputs s1 a_bs n_bs (BeeuStackFrame s₀.regs sp' ⋆ R) h_a_len h_n_len hmem1')
  rintro st ⟨hpc, hdmem, hsp, hx29, hB, hA, hN, hX, hY⟩
  refine ⟨hpc, ?_, ?_, hB, hA, hN, hX, hY, ?_⟩
  · rw [hsp, hregs1]
  · rw [hx29, hregs1]
  · rw [hdmem]; dsimp only [R_rest] at hmem1; simpa only [sep_assoc] using hmem1

/-! ### Inner Shift Loop, `SHIFT256`, Update Step, and Outer Loop Specifications -/

private theorem val256_congr {a0 a1 a2 a3 b0 b1 b2 b3 : UInt64}
    (h0 : a0.toBitVec = b0.toBitVec) (h1 : a1.toBitVec = b1.toBitVec)
    (h2 : a2.toBitVec = b2.toBitVec) (h3 : a3.toBitVec = b3.toBitVec) :
    val256 a0 a1 a2 a3 = val256 b0 b1 b2 b3 := by
  rw [UInt64.eq_of_toBitVec_eq h0, UInt64.eq_of_toBitVec_eq h1,
    UInt64.eq_of_toBitVec_eq h2, UInt64.eq_of_toBitVec_eq h3]

private theorem val320_congr {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : UInt64}
    (h0 : a0.toBitVec = b0.toBitVec) (h1 : a1.toBitVec = b1.toBitVec)
    (h2 : a2.toBitVec = b2.toBitVec) (h3 : a3.toBitVec = b3.toBitVec)
    (h4 : a4.toBitVec = b4.toBitVec) :
    val320 a0 a1 a2 a3 a4 = val320 b0 b1 b2 b3 b4 := by
  rw [UInt64.eq_of_toBitVec_eq h0, UInt64.eq_of_toBitVec_eq h1,
    UInt64.eq_of_toBitVec_eq h2, UInt64.eq_of_toBitVec_eq h3,
    UInt64.eq_of_toBitVec_eq h4]

private theorem beeu_odd_add_post {x' x n : Int}
    (h_eq : x' = x + n) (hx_odd : x % 2 = 1) (hn_odd : n % 2 = 1) :
    x' % 2 = 0 ∧ x' % n = x % n ∧ x' ≤ x + n := by
  refine ⟨by omega, ?_, by omega⟩
  rw [h_eq, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

private theorem effects_all_ite_true {L : Labels} {post : MachineState → Prop} {c : Bool}
    {e1 e2 : Effects} (hc : c = true) (h : @Effects.All L post e1) :
    @Effects.All L post (if c = true then e1 else e2) := by
  simp only [hc, ↓reduceIte]; exact h

private theorem effects_all_ite_false {L : Labels} {post : MachineState → Prop} {c : Bool}
    {e1 e2 : Effects} (hc : c = false) (h : @Effects.All L post e2) :
    @Effects.All L post (if c = true then e1 else e2) := by
  simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact h

private theorem ite_eq_left_of_eq_true {α : Type _} {c : Bool} {a b : α}
    (hc : c = true) : (if c = true then a else b) = a := by
  simp only [hc, ↓reduceIte]

private theorem ite_eq_right_of_eq_false {α : Type _} {c : Bool} {a b : α}
    (hc : c = false) : (if c = true then a else b) = b := by
  simp only [hc, Bool.false_eq_true, ↓reduceIte]

private theorem sep_5_pull {A B C D E : DataMem → Prop} :
    ((A ⋆ B ⋆ C) ⋆ D ⋆ E) = (B ⋆ D ⋆ (A ⋆ C ⋆ E)) := by ac_rfl

private abbrev PreservesCore (r r₀ : Reg64s) : Prop :=
  r.SP = r₀.SP ∧ r.X29 = r₀.X29 ∧
  r.X0 = r₀.X0 ∧ r.X1 = r₀.X1 ∧ r.X2 = r₀.X2 ∧ r.X30 = r₀.X30

private abbrev PreservesA (r r₀ : Reg64s) : Prop :=
  r.X21 = r₀.X21 ∧ r.X22 = r₀.X22 ∧ r.X23 = r₀.X23 ∧ r.X24 = r₀.X24

private abbrev PreservesB (r r₀ : Reg64s) : Prop :=
  r.X25 = r₀.X25 ∧ r.X26 = r₀.X26 ∧ r.X27 = r₀.X27 ∧ r.X28 = r₀.X28

private abbrev PreservesX (r r₀ : Reg64s) : Prop :=
  r.X3 = r₀.X3 ∧ r.X4 = r₀.X4 ∧ r.X5 = r₀.X5 ∧ r.X6 = r₀.X6 ∧ r.X7 = r₀.X7

private abbrev PreservesY (r r₀ : Reg64s) : Prop :=
  r.X8 = r₀.X8 ∧ r.X9 = r₀.X9 ∧ r.X10 = r₀.X10 ∧ r.X11 = r₀.X11 ∧ r.X12 = r₀.X12

private theorem beeuN_of_core {r r₀ : Reg64s} (h : PreservesCore r r₀) : beeuN r = beeuN r₀ := by
  dsimp only [beeuN]; rw [h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]

private theorem beeuA_of_pres {r r₀ : Reg64s} (h : PreservesA r r₀) : beeuA r = beeuA r₀ := by
  dsimp only [beeuA]; rw [h.1, h.2.1, h.2.2.1, h.2.2.2]

private theorem beeuB_of_pres {r r₀ : Reg64s} (h : PreservesB r r₀) : beeuB r = beeuB r₀ := by
  dsimp only [beeuB]; rw [h.1, h.2.1, h.2.2.1, h.2.2.2]

private theorem beeuX_of_pres {r r₀ : Reg64s} (h : PreservesX r r₀) : beeuX r = beeuX r₀ := by
  dsimp only [beeuX]; rw [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]

private theorem beeuY_of_pres {r r₀ : Reg64s} (h : PreservesY r r₀) : beeuY r = beeuY r₀ := by
  dsimp only [beeuY]; rw [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]

private theorem zeroExtend_64_extractLsb'_63_ushiftRight_1 (v : BitVec 64) :
    ((v >>> 1).extractLsb' 0 63).zeroExtend 64 = v >>> 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  have hlt : v.toNat / 2 ^ 1 < 2 ^ 63 := by
    have := v.isLt; omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)]

private theorem beeu_shift_loop_X_pre_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h14 : s.regs.X14 = 0)
    (hN_odd : beeuN s.regs % 2 = 1)
    (h_xn_lt : beeuX s.regs + beeuN s.regs < 256 ^ 40) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 55 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs ∧
        st.data.regs.X13 = s.regs.X13 ∧
        st.data.regs.X14 = s.regs.X14 ∧
        beeuX st.data.regs % 2 = 0 ∧
        beeuX st.data.regs % beeuN s.regs = beeuX s.regs % beeuN s.regs ∧
        beeuX st.data.regs ≤ beeuX s.regs + beeuN s.regs)
      ⟨s, beeuExec.addrOf 48⟩ := by
  sym => kstep; tactic =>
  rename_i val
  cases h_lsb : s.regs.X3.toBitVec.getLsbD 0
  · have hcond : (val.getLsbD 0 == false) = true := by
      dsimp only [val]; rw [extractLsb'_0_64, h_lsb]; rfl
    simp only [hcond, ↓reduceIte]
    sym => kstep 0; tactic =>
    have h_mod2 := getLsbD_zero_eq_false_mod2 s.regs.X3 h_lsb
    have hN_nn : 0 ≤ beeuN s.regs := val256_nonneg s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30
    refine .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩
    · dsimp only [beeuX]; rw [val320_emod_two]; omega
    · exact Int.le_add_of_nonneg_right hN_nn
  · have hcond : (val.getLsbD 0 == false) = false := by
      dsimp only [val]; rw [extractLsb'_0_64, h_lsb]; rfl
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    sym => kstep 5; tactic =>
    have h_mod2 := getLsbD_zero_eq_true_mod2 s.regs.X3 h_lsb
    have h0 : (0 : UInt64).toNat = 0 := rfl
    have h_n320 : val320 s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 = beeuN s.regs := by
      dsimp only [beeuN, val320, val256]; rw [h14, h0]; omega
    have h_lt320 : val320 s.regs.X3 s.regs.X4 s.regs.X5 s.regs.X6 s.regs.X7 +
        val320 s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 < 256 ^ 40 := by
      rw [h_n320]; exact h_xn_lt
    have h_add := add320_val_of_lt s.regs.X3 s.regs.X4 s.regs.X5 s.regs.X6 s.regs.X7
      s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 h_lt320
    have hx_odd : beeuX s.regs % 2 = 1 := by
      dsimp only [beeuX]; rw [val320_emod_two]; omega
    refine .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
      beeu_odd_add_post ?_ hx_odd hN_odd⟩
    dsimp only [beeuX]
    dsimp only [beeuN] at h_n320
    rw [← h_n320, ← h_add]
    apply val320_congr <;>
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero,
        add0Word, add0Carry, adcWord, adcCarry]

private theorem beeu_shift1_0_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h_x13_pos : 0 < s.regs.X13.toNat)
    (h_x_even : beeuX s.regs % 2 = 0) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = (if s.regs.X13.toNat = 1 then beeuExec.addrOf 63 else beeuExec.addrOf 48) ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs ∧
        st.data.regs.X14 = s.regs.X14 ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        2 * beeuX st.data.regs = beeuX s.regs)
      ⟨s, beeuExec.addrOf 55⟩ := by
  have h_shift := shift1_val320 s.regs.X3 s.regs.X4 s.regs.X5 s.regs.X6 s.regs.X7
  have h_x3_mod : (s.regs.X3.toNat % 2 : Int) = 0 := by
    rw [← val320_emod_two s.regs.X3 s.regs.X4 s.regs.X5 s.regs.X6 s.regs.X7]; exact h_x_even
  have h_dec := toNat_sub_one_of_pos s.regs.X13 h_x13_pos
  sym => kstep; tactic =>
  rename_i res_x13
  have h_res_x13 : res_x13 = s.regs.X13.toBitVec - 1#64 := by
    dsimp +zetaDelta only
    simp only [extractLsb'_0_64, show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
  by_cases h1 : s.regs.X13.toNat = 1
  · have h_bv : s.regs.X13.toBitVec = 1#64 := BitVec.eq_of_toNat_eq h1
    have hcond : (!(res_x13 == BitVec.zero 64)) = false := by
      rw [h_res_x13, h_bv]; rfl
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    sym => kstep 0; tactic =>
    refine .done _ ⟨by simp [h1], rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
    · simp only [UInt64.toNat_ofBitVec, h_res_x13, h_bv, h1]; rfl
    · dsimp only [beeuX]
      dsimp only at h_shift
      rw [← h_shift, h_x3_mod, Int.add_zero]
      apply congrArg (2 * ·)
      apply val320_congr
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
          show (1 ≤ 63) ↔ True from by decide, ↓reduceIte]
        exact zeroExtend_64_extractLsb'_63_ushiftRight_1 _
  · have h_gt1 : 1 < s.regs.X13.toNat := by omega
    have h_nz := sub_one_beq_zero_false_of_gt_one s.regs.X13 h_gt1
    have hcond : (!(res_x13 == BitVec.zero 64)) = true := by
      rw [h_res_x13]; change (!(s.regs.X13.toBitVec - 1#64 == 0#64)) = true; rw [h_nz]; rfl
    simp only [hcond, ↓reduceIte]
    sym => kstep 0; tactic =>
    refine .done _ ⟨by simp [h1], rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
    · rw [← h_dec]; congr 1; apply UInt64.eq_of_toBitVec_eq; exact h_res_x13
    · dsimp only [beeuX]
      dsimp only at h_shift
      rw [← h_shift, h_x3_mod, Int.add_zero]
      apply congrArg (2 * ·)
      apply val320_congr
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
          show (1 ≤ 63) ↔ True from by decide, ↓reduceIte]
        exact zeroExtend_64_extractLsb'_63_ushiftRight_1 _

private theorem beeu_shift_loop_X_step_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h_x13_pos : 0 < s.regs.X13.toNat)
    (h14 : s.regs.X14 = 0)
    (hN_odd : beeuN s.regs % 2 = 1)
    (h_xn_lt : beeuX s.regs + beeuN s.regs < 256 ^ 40) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = (if s.regs.X13.toNat = 1 then beeuExec.addrOf 63 else beeuExec.addrOf 48) ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs ∧
        st.data.regs.X14 = s.regs.X14 ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        (2 * beeuX st.data.regs) % beeuN s.regs = beeuX s.regs % beeuN s.regs ∧
        2 * beeuX st.data.regs ≤ beeuX s.regs + beeuN s.regs)
      ⟨s, beeuExec.addrOf 48⟩ := by
  refine eventually_trans _ _ _ _ (beeu_shift_loop_X_pre_correct s h14 hN_odd h_xn_lt) ?_
  rintro ⟨mid, pc1⟩ ⟨hpc1, hdmem1, hcore1, hA1, hB1, hY1, hx13_1, hx14_1, heven1, hmod1, hle1⟩
  dsimp only at hpc1 hdmem1 hcore1 hA1 hB1 hY1 hx13_1 hx14_1 heven1 hmod1 hle1
  subst hpc1
  refine eventually_weaken _ _ _ _ ?_ (beeu_shift1_0_correct mid (hx13_1.symm ▸ h_x13_pos) heven1)
  rintro st ⟨hpc2, hdmem2, hcore2, hA2, hB2, hY2, hx14_2, hx13_2, h2x⟩
  rw [hx13_1] at hpc2 hx13_2
  refine ⟨hpc2, hdmem2.trans hdmem1,
    ⟨hcore2.1.trans hcore1.1, hcore2.2.1.trans hcore1.2.1, hcore2.2.2.1.trans hcore1.2.2.1,
     hcore2.2.2.2.1.trans hcore1.2.2.2.1, hcore2.2.2.2.2.1.trans hcore1.2.2.2.2.1,
     hcore2.2.2.2.2.2.trans hcore1.2.2.2.2.2⟩,
    ⟨hA2.1.trans hA1.1, hA2.2.1.trans hA1.2.1, hA2.2.2.1.trans hA1.2.2.1, hA2.2.2.2.trans hA1.2.2.2⟩,
    ⟨hB2.1.trans hB1.1, hB2.2.1.trans hB1.2.1, hB2.2.2.1.trans hB1.2.2.1, hB2.2.2.2.trans hB1.2.2.2⟩,
    ⟨hY2.1.trans hY1.1, hY2.2.1.trans hY1.2.1, hY2.2.2.1.trans hY1.2.2.1,
     hY2.2.2.2.1.trans hY1.2.2.2.1, hY2.2.2.2.2.trans hY1.2.2.2.2⟩,
    hx14_2.trans hx14_1, hx13_2, by rw [h2x, hmod1], by omega⟩

private theorem beeu_shift_loop_X_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h_x13_pos : 0 < s.regs.X13.toNat)
    (h14 : s.regs.X14 = 0)
    (hN_odd : beeuN s.regs % 2 = 1)
    (h_xn_lt : beeuX s.regs + beeuN s.regs < 256 ^ 40) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 63 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs ∧
        (((2 ^ s.regs.X13.toNat : Nat) : Int) * beeuX st.data.regs) % beeuN s.regs =
          beeuX s.regs % beeuN s.regs ∧
        beeuX st.data.regs < 256 ^ 40 / 2 ∧
        ((2 ^ s.regs.X13.toNat : Nat) : Int) * beeuX st.data.regs ≤
          beeuX s.regs + (((2 ^ s.regs.X13.toNat : Nat) : Int) - 1) * beeuN s.regs)
      ⟨s, beeuExec.addrOf 48⟩ := by
  let k₀ := s.regs.X13.toNat
  have h_N_lt : beeuN s.regs < 256 ^ 32 := val256_lt _ _ _ _
  let Q : MachineState → Prop := fun st =>
    st.pc = beeuExec.addrOf 63 ∧
    st.data.dmem = s.dmem ∧
    PreservesCore st.data.regs s.regs ∧
    PreservesA st.data.regs s.regs ∧
    PreservesB st.data.regs s.regs ∧
    PreservesY st.data.regs s.regs ∧
    (((2 ^ k₀ : Nat) : Int) * beeuX st.data.regs) % beeuN s.regs = beeuX s.regs % beeuN s.regs ∧
    beeuX st.data.regs < 256 ^ 40 / 2 ∧
    ((2 ^ k₀ : Nat) : Int) * beeuX st.data.regs ≤
      beeuX s.regs + (((2 ^ k₀ : Nat) : Int) - 1) * beeuN s.regs
  refine tailrec_loop
    (onLoop := fun (v : Nat) st =>
      st.pc = beeuExec.addrOf 48 ∧
      st.data.dmem = s.dmem ∧
      PreservesCore st.data.regs s.regs ∧
      PreservesA st.data.regs s.regs ∧
      PreservesB st.data.regs s.regs ∧
      PreservesY st.data.regs s.regs ∧
      st.data.regs.X14 = s.regs.X14 ∧
      0 < v ∧ v ≤ k₀ ∧
      st.data.regs.X13.toNat = v ∧
      beeuX st.data.regs + beeuN s.regs < 256 ^ 40 ∧
      (((2 ^ (k₀ - v) : Nat) : Int) * beeuX st.data.regs) % beeuN s.regs =
        beeuX s.regs % beeuN s.regs ∧
      ((2 ^ (k₀ - v) : Nat) : Int) * beeuX st.data.regs ≤
        beeuX s.regs + (((2 ^ (k₀ - v) : Nat) : Int) - 1) * beeuN s.regs)
    (onExit := fun _ => Q) (· < ·) Nat.lt_wfRel.wf k₀
    ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
     ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl,
     h_x13_pos, Nat.le_refl _, rfl, h_xn_lt, by simp, by simp⟩
    ?_ (fun _ h => h)
  rintro v ⟨st, pc⟩ ⟨hpc, hdmem, hcore, hA, hB, hY, hx14, hv_pos, hv_le, hx13, hxn, hinv, hbnd⟩
  dsimp only at hpc hdmem hcore hA hB hY hx14 hx13 hxn hinv hbnd
  subst hpc
  have hN_eq : beeuN st.regs = beeuN s.regs := beeuN_of_core hcore
  refine eventually_weaken _ _ _ _ ?_
    (beeu_shift_loop_X_step_correct st (hx13 ▸ hv_pos) (hx14.trans h14)
      (hN_eq.symm ▸ hN_odd) (hN_eq.symm ▸ hxn))
  rintro mid ⟨hpc', hdmem', hcore', hA', hB', hY', hx14', hx13', hmod', h2x'⟩
  rw [hx13] at hpc' hx13'
  rw [hN_eq] at hmod' h2x'
  have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ hinv hmod'
  have h_bstep := pow2_mul_bound_step (k₀ - v) _ _ _ _ hbnd h2x'
  have hcore_all : PreservesCore mid.data.regs s.regs :=
    ⟨hcore'.1.trans hcore.1, hcore'.2.1.trans hcore.2.1, hcore'.2.2.1.trans hcore.2.2.1,
     hcore'.2.2.2.1.trans hcore.2.2.2.1, hcore'.2.2.2.2.1.trans hcore.2.2.2.2.1,
     hcore'.2.2.2.2.2.trans hcore.2.2.2.2.2⟩
  have hA_all : PreservesA mid.data.regs s.regs :=
    ⟨hA'.1.trans hA.1, hA'.2.1.trans hA.2.1, hA'.2.2.1.trans hA.2.2.1, hA'.2.2.2.trans hA.2.2.2⟩
  have hB_all : PreservesB mid.data.regs s.regs :=
    ⟨hB'.1.trans hB.1, hB'.2.1.trans hB.2.1, hB'.2.2.1.trans hB.2.2.1, hB'.2.2.2.trans hB.2.2.2⟩
  have hY_all : PreservesY mid.data.regs s.regs :=
    ⟨hY'.1.trans hY.1, hY'.2.1.trans hY.2.1, hY'.2.2.1.trans hY.2.2.1,
     hY'.2.2.2.1.trans hY.2.2.2.1, hY'.2.2.2.2.trans hY.2.2.2.2⟩
  by_cases hv1 : v = 1
  · simp only [hv1, ↓reduceIte] at hpc'
    have h_k : k₀ - v + 1 = k₀ := by omega
    rw [h_k] at h_step h_bstep
    exact .break ⟨hpc', hdmem'.trans hdmem, hcore_all, hA_all, hB_all, hY_all,
      h_step, by omega, h_bstep⟩
  · simp only [hv1, ↓reduceIte] at hpc'
    have h_k : k₀ - v + 1 = k₀ - (v - 1) := by omega
    rw [h_k] at h_step h_bstep
    exact .loop (v - 1)
      ⟨hpc', hdmem'.trans hdmem, hcore_all, hA_all, hB_all, hY_all, hx14'.trans hx14,
       by omega, by omega, hx13', by omega, h_step, h_bstep⟩ (by omega) (fun _ h => h)

private theorem beeu_shift_loop_Y_pre_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h14 : s.regs.X14 = 0)
    (hN_odd : beeuN s.regs % 2 = 1)
    (h_yn_lt : beeuY s.regs + beeuN s.regs < 256 ^ 40) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 87 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesX st.data.regs s.regs ∧
        st.data.regs.X13 = s.regs.X13 ∧
        st.data.regs.X14 = s.regs.X14 ∧
        beeuY st.data.regs % 2 = 0 ∧
        beeuY st.data.regs % beeuN s.regs = beeuY s.regs % beeuN s.regs ∧
        beeuY st.data.regs ≤ beeuY s.regs + beeuN s.regs)
      ⟨s, beeuExec.addrOf 80⟩ := by
  sym => kstep; tactic =>
  rename_i val
  cases h_lsb : s.regs.X8.toBitVec.getLsbD 0
  · have hcond : (val.getLsbD 0 == false) = true := by
      dsimp only [val]; rw [extractLsb'_0_64, h_lsb]; rfl
    simp only [hcond, ↓reduceIte]
    sym => kstep 0; tactic =>
    have h_mod2 := getLsbD_zero_eq_false_mod2 s.regs.X8 h_lsb
    have hN_nn : 0 ≤ beeuN s.regs := val256_nonneg s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30
    refine .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_, rfl, ?_⟩
    · dsimp only [beeuY]; rw [val320_emod_two]; omega
    · exact Int.le_add_of_nonneg_right hN_nn
  · have hcond : (val.getLsbD 0 == false) = false := by
      dsimp only [val]; rw [extractLsb'_0_64, h_lsb]; rfl
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    sym => kstep 5; tactic =>
    have h_mod2 := getLsbD_zero_eq_true_mod2 s.regs.X8 h_lsb
    have h0 : (0 : UInt64).toNat = 0 := rfl
    have h_n320 : val320 s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 = beeuN s.regs := by
      dsimp only [beeuN, val320, val256]; rw [h14, h0]; omega
    have h_lt320 : val320 s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12 +
        val320 s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 < 256 ^ 40 := by
      rw [h_n320]; exact h_yn_lt
    have h_add := add320_val_of_lt s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12
      s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 h_lt320
    have hy_odd : beeuY s.regs % 2 = 1 := by
      dsimp only [beeuY]; rw [val320_emod_two]; omega
    refine .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
      beeu_odd_add_post ?_ hy_odd hN_odd⟩
    dsimp only [beeuY]
    dsimp only [beeuN] at h_n320
    rw [← h_n320, ← h_add]
    apply val320_congr <;>
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero,
        add0Word, add0Carry, adcWord, adcCarry]

private theorem beeu_shift1_1_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h_x13_pos : 0 < s.regs.X13.toNat)
    (h_y_even : beeuY s.regs % 2 = 0) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = (if s.regs.X13.toNat = 1 then beeuExec.addrOf 95 else beeuExec.addrOf 80) ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesX st.data.regs s.regs ∧
        st.data.regs.X14 = s.regs.X14 ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        2 * beeuY st.data.regs = beeuY s.regs)
      ⟨s, beeuExec.addrOf 87⟩ := by
  have h_shift := shift1_val320 s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12
  have h_x8_mod : (s.regs.X8.toNat % 2 : Int) = 0 := by
    rw [← val320_emod_two s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12]; exact h_y_even
  have h_dec := toNat_sub_one_of_pos s.regs.X13 h_x13_pos
  sym => kstep; tactic =>
  rename_i res_x13
  have h_res_x13 : res_x13 = s.regs.X13.toBitVec - 1#64 := by
    dsimp +zetaDelta only
    simp only [extractLsb'_0_64, show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
  by_cases h1 : s.regs.X13.toNat = 1
  · have h_bv : s.regs.X13.toBitVec = 1#64 := BitVec.eq_of_toNat_eq h1
    have hcond : (!(res_x13 == BitVec.zero 64)) = false := by
      rw [h_res_x13, h_bv]; rfl
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    sym => kstep 0; tactic =>
    refine .done _ ⟨by simp [h1], rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
    · simp only [UInt64.toNat_ofBitVec, h_res_x13, h_bv, h1]; rfl
    · dsimp only [beeuY]
      dsimp only at h_shift
      rw [← h_shift, h_x8_mod, Int.add_zero]
      apply congrArg (2 * ·)
      apply val320_congr
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
          show (1 ≤ 63) ↔ True from by decide, ↓reduceIte]
        exact zeroExtend_64_extractLsb'_63_ushiftRight_1 _
  · have h_gt1 : 1 < s.regs.X13.toNat := by omega
    have h_nz := sub_one_beq_zero_false_of_gt_one s.regs.X13 h_gt1
    have hcond : (!(res_x13 == BitVec.zero 64)) = true := by
      rw [h_res_x13]; change (!(s.regs.X13.toBitVec - 1#64 == 0#64)) = true; rw [h_nz]; rfl
    simp only [hcond, ↓reduceIte]
    sym => kstep 0; tactic =>
    refine .done _ ⟨by simp [h1], rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
    · rw [← h_dec]; congr 1; apply UInt64.eq_of_toBitVec_eq; exact h_res_x13
    · dsimp only [beeuY]
      dsimp only at h_shift
      rw [← h_shift, h_x8_mod, Int.add_zero]
      apply congrArg (2 * ·)
      apply val320_congr
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, extr1Word,
          show (1 == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte, show 64 - 1 = 63 from rfl]
      · simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
          show (1 ≤ 63) ↔ True from by decide, ↓reduceIte]
        exact zeroExtend_64_extractLsb'_63_ushiftRight_1 _

private theorem beeu_shift_loop_Y_step_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h_x13_pos : 0 < s.regs.X13.toNat)
    (h14 : s.regs.X14 = 0)
    (hN_odd : beeuN s.regs % 2 = 1)
    (h_yn_lt : beeuY s.regs + beeuN s.regs < 256 ^ 40) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = (if s.regs.X13.toNat = 1 then beeuExec.addrOf 95 else beeuExec.addrOf 80) ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesX st.data.regs s.regs ∧
        st.data.regs.X14 = s.regs.X14 ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        (2 * beeuY st.data.regs) % beeuN s.regs = beeuY s.regs % beeuN s.regs ∧
        2 * beeuY st.data.regs ≤ beeuY s.regs + beeuN s.regs)
      ⟨s, beeuExec.addrOf 80⟩ := by
  refine eventually_trans _ _ _ _ (beeu_shift_loop_Y_pre_correct s h14 hN_odd h_yn_lt) ?_
  rintro ⟨mid, pc1⟩ ⟨hpc1, hdmem1, hcore1, hA1, hB1, hX1, hx13_1, hx14_1, heven1, hmod1, hle1⟩
  dsimp only at hpc1 hdmem1 hcore1 hA1 hB1 hX1 hx13_1 hx14_1 heven1 hmod1 hle1
  subst hpc1
  refine eventually_weaken _ _ _ _ ?_ (beeu_shift1_1_correct mid (hx13_1.symm ▸ h_x13_pos) heven1)
  rintro st ⟨hpc2, hdmem2, hcore2, hA2, hB2, hX2, hx14_2, hx13_2, h2y⟩
  rw [hx13_1] at hpc2 hx13_2
  refine ⟨hpc2, hdmem2.trans hdmem1,
    ⟨hcore2.1.trans hcore1.1, hcore2.2.1.trans hcore1.2.1, hcore2.2.2.1.trans hcore1.2.2.1,
     hcore2.2.2.2.1.trans hcore1.2.2.2.1, hcore2.2.2.2.2.1.trans hcore1.2.2.2.2.1,
     hcore2.2.2.2.2.2.trans hcore1.2.2.2.2.2⟩,
    ⟨hA2.1.trans hA1.1, hA2.2.1.trans hA1.2.1, hA2.2.2.1.trans hA1.2.2.1, hA2.2.2.2.trans hA1.2.2.2⟩,
    ⟨hB2.1.trans hB1.1, hB2.2.1.trans hB1.2.1, hB2.2.2.1.trans hB1.2.2.1, hB2.2.2.2.trans hB1.2.2.2⟩,
    ⟨hX2.1.trans hX1.1, hX2.2.1.trans hX1.2.1, hX2.2.2.1.trans hX1.2.2.1,
     hX2.2.2.2.1.trans hX1.2.2.2.1, hX2.2.2.2.2.trans hX1.2.2.2.2⟩,
    hx14_2.trans hx14_1, hx13_2, by rw [h2y, hmod1], by omega⟩

private theorem beeu_shift_loop_Y_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h_x13_pos : 0 < s.regs.X13.toNat)
    (h14 : s.regs.X14 = 0)
    (hN_odd : beeuN s.regs % 2 = 1)
    (h_yn_lt : beeuY s.regs + beeuN s.regs < 256 ^ 40) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 95 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesX st.data.regs s.regs ∧
        (((2 ^ s.regs.X13.toNat : Nat) : Int) * beeuY st.data.regs) % beeuN s.regs =
          beeuY s.regs % beeuN s.regs ∧
        beeuY st.data.regs < 256 ^ 40 / 2 ∧
        ((2 ^ s.regs.X13.toNat : Nat) : Int) * beeuY st.data.regs ≤
          beeuY s.regs + (((2 ^ s.regs.X13.toNat : Nat) : Int) - 1) * beeuN s.regs)
      ⟨s, beeuExec.addrOf 80⟩ := by
  let k₀ := s.regs.X13.toNat
  have h_N_lt : beeuN s.regs < 256 ^ 32 := val256_lt _ _ _ _
  let Q : MachineState → Prop := fun st =>
    st.pc = beeuExec.addrOf 95 ∧
    st.data.dmem = s.dmem ∧
    PreservesCore st.data.regs s.regs ∧
    PreservesA st.data.regs s.regs ∧
    PreservesB st.data.regs s.regs ∧
    PreservesX st.data.regs s.regs ∧
    (((2 ^ k₀ : Nat) : Int) * beeuY st.data.regs) % beeuN s.regs = beeuY s.regs % beeuN s.regs ∧
    beeuY st.data.regs < 256 ^ 40 / 2 ∧
    ((2 ^ k₀ : Nat) : Int) * beeuY st.data.regs ≤
      beeuY s.regs + (((2 ^ k₀ : Nat) : Int) - 1) * beeuN s.regs
  refine tailrec_loop
    (onLoop := fun (v : Nat) st =>
      st.pc = beeuExec.addrOf 80 ∧
      st.data.dmem = s.dmem ∧
      PreservesCore st.data.regs s.regs ∧
      PreservesA st.data.regs s.regs ∧
      PreservesB st.data.regs s.regs ∧
      PreservesX st.data.regs s.regs ∧
      st.data.regs.X14 = s.regs.X14 ∧
      0 < v ∧ v ≤ k₀ ∧
      st.data.regs.X13.toNat = v ∧
      beeuY st.data.regs + beeuN s.regs < 256 ^ 40 ∧
      (((2 ^ (k₀ - v) : Nat) : Int) * beeuY st.data.regs) % beeuN s.regs =
        beeuY s.regs % beeuN s.regs ∧
      ((2 ^ (k₀ - v) : Nat) : Int) * beeuY st.data.regs ≤
        beeuY s.regs + (((2 ^ (k₀ - v) : Nat) : Int) - 1) * beeuN s.regs)
    (onExit := fun _ => Q) (· < ·) Nat.lt_wfRel.wf k₀
    ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
     ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl,
     h_x13_pos, Nat.le_refl _, rfl, h_yn_lt, by simp, by simp⟩
    ?_ (fun _ h => h)
  rintro v ⟨st, pc⟩ ⟨hpc, hdmem, hcore, hA, hB, hX, hx14, hv_pos, hv_le, hx13, hyn, hinv, hbnd⟩
  dsimp only at hpc hdmem hcore hA hB hX hx14 hx13 hyn hinv hbnd
  subst hpc
  have hN_eq : beeuN st.regs = beeuN s.regs := beeuN_of_core hcore
  refine eventually_weaken _ _ _ _ ?_
    (beeu_shift_loop_Y_step_correct st (hx13 ▸ hv_pos) (hx14.trans h14)
      (hN_eq.symm ▸ hN_odd) (hN_eq.symm ▸ hyn))
  rintro mid ⟨hpc', hdmem', hcore', hA', hB', hX', hx14', hx13', hmod', h2y'⟩
  rw [hx13] at hpc' hx13'
  rw [hN_eq] at hmod' h2y'
  have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ hinv hmod'
  have h_bstep := pow2_mul_bound_step (k₀ - v) _ _ _ _ hbnd h2y'
  have hcore_all : PreservesCore mid.data.regs s.regs :=
    ⟨hcore'.1.trans hcore.1, hcore'.2.1.trans hcore.2.1, hcore'.2.2.1.trans hcore.2.2.1,
     hcore'.2.2.2.1.trans hcore.2.2.2.1, hcore'.2.2.2.2.1.trans hcore.2.2.2.2.1,
     hcore'.2.2.2.2.2.trans hcore.2.2.2.2.2⟩
  have hA_all : PreservesA mid.data.regs s.regs :=
    ⟨hA'.1.trans hA.1, hA'.2.1.trans hA.2.1, hA'.2.2.1.trans hA.2.2.1, hA'.2.2.2.trans hA.2.2.2⟩
  have hB_all : PreservesB mid.data.regs s.regs :=
    ⟨hB'.1.trans hB.1, hB'.2.1.trans hB.2.1, hB'.2.2.1.trans hB.2.2.1, hB'.2.2.2.trans hB.2.2.2⟩
  have hX_all : PreservesX mid.data.regs s.regs :=
    ⟨hX'.1.trans hX.1, hX'.2.1.trans hX.2.1, hX'.2.2.1.trans hX.2.2.1,
     hX'.2.2.2.1.trans hX.2.2.2.1, hX'.2.2.2.2.trans hX.2.2.2.2⟩
  by_cases hv1 : v = 1
  · simp only [hv1, ↓reduceIte] at hpc'
    have h_k : k₀ - v + 1 = k₀ := by omega
    rw [h_k] at h_step h_bstep
    exact .break ⟨hpc', hdmem'.trans hdmem, hcore_all, hA_all, hB_all, hX_all,
      h_step, by omega, h_bstep⟩
  · simp only [hv1, ↓reduceIte] at hpc'
    have h_k : k₀ - v + 1 = k₀ - (v - 1) := by omega
    rw [h_k] at h_step h_bstep
    exact .loop (v - 1)
      ⟨hpc', hdmem'.trans hdmem, hcore_all, hA_all, hB_all, hX_all, hx14'.trans hx14,
       by omega, by omega, hx13', by omega, h_step, h_bstep⟩ (by omega) (fun _ h => h)

private theorem beeu_shift_B_header_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (hB_pos : 0 < beeuB s.regs) :
    Eventually (step1 beeuExec)
      (fun st =>
        let k := ctzClamped s.regs.X25
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesX st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs ∧
        if k = 0#64 then
          st.pc = beeuExec.addrOf 63 ∧
          beeuB st.data.regs = beeuB s.regs ∧
          beeuB s.regs % 2 = 1
        else
          st.pc = beeuExec.addrOf 48 ∧
          st.data.regs.X13.toNat = k.toNat ∧
          0 < k.toNat ∧
          st.data.regs.X14 = 0 ∧
          ((2 ^ k.toNat : Nat) : Int) * beeuB st.data.regs = beeuB s.regs ∧
          (beeuB st.data.regs % 2 = 0 → k = 63#64))
      ⟨s, beeuExec.addrOf 27⟩ := by
  have h_nz := val256_pos_or_ne_zero s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28 hB_pos
  sym => kstep; tactic =>
  -- Stopped at cbz x14, .Lbeeu_loop_end
  rename_i val_x14
  have hcbz1 : (val_x14 == 0) = false := by
    have : val_x14 = s.regs.X25.toBitVec ||| s.regs.X26.toBitVec |||
        s.regs.X27.toBitVec ||| s.regs.X28.toBitVec := by
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
    rw [this]; exact h_nz
  simp only [hcbz1, Bool.false_eq_true, ↓reduceIte]
  sym => kstep; tactic =>
  -- Stopped at cbz x13, .Lbeeu_shift_A_Y
  rename_i val_x13
  have h_x13_eq : val_x13 = ctzClamped s.regs.X25 := by
    dsimp only [ctzClamped]
    simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
      show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
  by_cases hk : ctzClamped s.regs.X25 = 0#64
  · have hcbz2 : (val_x13 == 0) = true := by rw [h_x13_eq, hk]; rfl
    simp only [hcbz2, ↓reduceIte]
    sym => kstep 0; tactic =>
    have h_odd := val256_odd_of_ctzClamped_eq_zero s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28 hk
    refine .done _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    simp only [hk, ↓reduceIte]
    exact ⟨trivial, trivial, h_odd⟩
  · have hcbz2 : (val_x13 == 0) = false := by
      rw [h_x13_eq, beq_eq_false_iff_ne]; exact hk
    simp only [hcbz2, Bool.false_eq_true, ↓reduceIte]
    sym => kstep 12; tactic =>
    have h_par := shift256_val256_even_imp_clamped s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28
    have h_shift := shift256_val256 s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28 hk
    have hk_pos : 0 < (ctzClamped s.regs.X25).toNat := by
      have : (ctzClamped s.regs.X25).toNat ≠ 0 := fun h0 => hk (BitVec.eq_of_toNat_eq h0)
      omega
    refine .done _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    simp only [hk, ↓reduceIte]
    refine ⟨trivial, ?_, hk_pos, ?_, ?_, ?_⟩
    · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, ctzClamped,
        show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl, UInt64.toNat_ofBitVec]
    · apply UInt64.eq_of_toBitVec_eq
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero, BitVec.xor_self]
      rfl
    · rw [← h_shift]
      apply congrArg (((2 ^ (ctzClamped s.regs.X25).toNat : Nat) : Int) * ·)
      apply val256_congr <;>
        simp (config := { zetaDelta := true }) only [extractLsb'_0_64, ctzClamped,
          shift256Word, shift256TopWord,
          show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero,
          show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
    · intro h_even
      apply h_par
      rw [← h_even]
      apply congrArg (· % 2)
      symm
      apply val256_congr <;>
        simp (config := { zetaDelta := true }) only [extractLsb'_0_64, ctzClamped,
          shift256Word, shift256TopWord,
          show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero,
          show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]

private theorem beeu_shift_A_header_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) :
    Eventually (step1 beeuExec)
      (fun st =>
        let k := ctzClamped s.regs.X21
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesX st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs ∧
        if k = 0#64 then
          st.pc = beeuExec.addrOf 95 ∧
          beeuA st.data.regs = beeuA s.regs ∧
          beeuA s.regs % 2 = 1
        else
          st.pc = beeuExec.addrOf 80 ∧
          st.data.regs.X13.toNat = k.toNat ∧
          0 < k.toNat ∧
          st.data.regs.X14 = 0 ∧
          ((2 ^ k.toNat : Nat) : Int) * beeuA st.data.regs = beeuA s.regs ∧
          (beeuA st.data.regs % 2 = 0 → k = 63#64))
      ⟨s, beeuExec.addrOf 63⟩ := by
  sym => kstep; tactic =>
  -- Stopped at cbz x13, .Lbeeu_update_B_X_or_A_Y
  rename_i val_x13
  have h_x13_eq : val_x13 = ctzClamped s.regs.X21 := by
    dsimp only [ctzClamped]
    simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
      show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
  by_cases hk : ctzClamped s.regs.X21 = 0#64
  · have hcbz : (val_x13 == 0) = true := by rw [h_x13_eq, hk]; rfl
    simp only [hcbz, ↓reduceIte]
    sym => kstep 0; tactic =>
    have h_odd := val256_odd_of_ctzClamped_eq_zero s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 hk
    refine .done _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    simp only [hk, ↓reduceIte]
    exact ⟨trivial, trivial, h_odd⟩
  · have hcbz : (val_x13 == 0) = false := by
      rw [h_x13_eq, beq_eq_false_iff_ne]; exact hk
    simp only [hcbz, Bool.false_eq_true, ↓reduceIte]
    sym => kstep 12; tactic =>
    have h_par := shift256_val256_even_imp_clamped s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24
    have h_shift := shift256_val256 s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 hk
    have hk_pos : 0 < (ctzClamped s.regs.X21).toNat := by
      have : (ctzClamped s.regs.X21).toNat ≠ 0 := fun h0 => hk (BitVec.eq_of_toNat_eq h0)
      omega
    refine .done _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    simp only [hk, ↓reduceIte]
    refine ⟨trivial, ?_, hk_pos, ?_, ?_, ?_⟩
    · simp (config := { zetaDelta := true }) only [extractLsb'_0_64, ctzClamped,
        show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl, UInt64.toNat_ofBitVec]
    · apply UInt64.eq_of_toBitVec_eq
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero, BitVec.xor_self]
      rfl
    · rw [← h_shift]
      apply congrArg (((2 ^ (ctzClamped s.regs.X21).toNat : Nat) : Int) * ·)
      apply val256_congr <;>
        simp (config := { zetaDelta := true }) only [extractLsb'_0_64, ctzClamped,
          shift256Word, shift256TopWord,
          show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero,
          show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
    · intro h_even
      apply h_par
      rw [← h_even]
      apply congrArg (· % 2)
      symm
      apply val256_congr <;>
        simp (config := { zetaDelta := true }) only [extractLsb'_0_64, ctzClamped,
          shift256Word, shift256TopWord,
          show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero,
          show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]

private theorem beeu_shift_B_X_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int)
    (hB_pos : 0 < beeuB s.regs)
    (hN_odd : beeuN s.regs % 2 = 1)
    (hX_lt : beeuX s.regs < 256 ^ 40 / 2)
    (h_inv : (a * beeuX s.regs - beeuB s.regs) % beeuN s.regs = 0) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 63 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs ∧
        0 < beeuB st.data.regs ∧
        beeuB st.data.regs ≤ beeuB s.regs ∧
        beeuX st.data.regs < 256 ^ 40 / 2 ∧
        (a * beeuX st.data.regs - beeuB st.data.regs) % beeuN s.regs = 0 ∧
        ∃ k : Nat, k ≤ 63 ∧
          ((2 ^ k : Nat) : Int) * beeuB st.data.regs = beeuB s.regs ∧
          ((2 ^ k : Nat) : Int) * beeuX st.data.regs ≤
            beeuX s.regs + (((2 ^ k : Nat) : Int) - 1) * beeuN s.regs ∧
          (beeuB s.regs % 2 = 0 → 1 ≤ k) ∧
          (beeuB st.data.regs % 2 = 0 → k = 63))
      ⟨s, beeuExec.addrOf 27⟩ := by
  refine eventually_trans _ _ _ _ (beeu_shift_B_header_correct s hB_pos) ?_
  rintro ⟨mid, pc1⟩ ⟨hdmem1, hcore1, hA1, hX1, hY1, h_branch⟩
  dsimp only at hdmem1 hcore1 hA1 hX1 hY1 h_branch
  by_cases hk : ctzClamped s.regs.X25 = 0#64
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨hpc1, hB1, h_odd⟩
    have hX_eq := beeuX_of_pres hX1
    exact .done _ ⟨hpc1, hdmem1, hcore1, hA1, hY1, hB1.symm ▸ hB_pos, hB1.symm ▸ Int.le_refl _,
      hX_eq.symm ▸ hX_lt, by rw [hX_eq, hB1]; exact h_inv,
      0, by omega, by rw [hB1]; simp, by rw [hX_eq]; simp, by intro h; omega,
      by rw [hB1]; intro h; omega⟩
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨hpc1, hx13, hk_pos, hx14, hB_shift, h_par⟩
    subst hpc1
    have h_N_lt : beeuN s.regs < 256 ^ 32 := val256_lt _ _ _ _
    have hN_eq := beeuN_of_core hcore1
    have hX_eq := beeuX_of_pres hX1
    have h_xn_lt : beeuX mid.regs + beeuN mid.regs < 256 ^ 40 := by
      rw [hX_eq, hN_eq]; omega
    refine eventually_weaken _ _ _ _ ?_
      (beeu_shift_loop_X_correct mid (hx13 ▸ hk_pos) hx14 (hN_eq.symm ▸ hN_odd) h_xn_lt)
    rintro fin ⟨hpc2, hdmem2, hcore2, hA2, hB2, hY2, hX_mod, hX_lt2, hX_bnd⟩
    have hB_eq := beeuB_of_pres hB2
    have hB_nn : 0 ≤ beeuB fin.data.regs := val256_nonneg _ _ _ _
    have ⟨hB'_pos, hB'_le⟩ := pos_and_le_of_pow2_mul
      (ctzClamped s.regs.X25).toNat (beeuB s.regs) (beeuB fin.data.regs)
      hB_pos hB_nn (hB_eq.symm ▸ hB_shift)
    have hk63 : (ctzClamped s.regs.X25).toNat ≤ 63 :=
      BitVec.le_def.mp (clz_reverse_or_one_le_63 s.regs.X25.toBitVec)
    rw [hx13, hN_eq, hX_eq] at hX_mod hX_bnd
    refine ⟨hpc2, hdmem2.trans hdmem1,
      ⟨hcore2.1.trans hcore1.1, hcore2.2.1.trans hcore1.2.1, hcore2.2.2.1.trans hcore1.2.2.1,
       hcore2.2.2.2.1.trans hcore1.2.2.2.1, hcore2.2.2.2.2.1.trans hcore1.2.2.2.2.1,
       hcore2.2.2.2.2.2.trans hcore1.2.2.2.2.2⟩,
      ⟨hA2.1.trans hA1.1, hA2.2.1.trans hA1.2.1, hA2.2.2.1.trans hA1.2.2.1, hA2.2.2.2.trans hA1.2.2.2⟩,
      ⟨hY2.1.trans hY1.1, hY2.2.1.trans hY1.2.1, hY2.2.2.1.trans hY1.2.2.1,
       hY2.2.2.2.1.trans hY1.2.2.2.1, hY2.2.2.2.2.trans hY1.2.2.2.2⟩,
      hB'_pos, hB'_le, hX_lt2, ?_, (ctzClamped s.regs.X25).toNat, hk63,
      hB_eq.symm ▸ hB_shift, hX_bnd, fun _ => hk_pos, ?_⟩
    · exact shift_B_X_mod_inv (ctzClamped s.regs.X25).toNat a
        (beeuB s.regs) (beeuB fin.data.regs) (beeuX s.regs) (beeuX fin.data.regs) (beeuN s.regs)
        hN_odd (hB_eq.symm ▸ hB_shift) hX_mod h_inv
    · intro h_even
      rw [hB_eq] at h_even
      exact congrArg BitVec.toNat (h_par h_even)

private theorem beeu_shift_A_Y_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int)
    (hA_pos : 0 < beeuA s.regs)
    (hN_odd : beeuN s.regs % 2 = 1)
    (hY_lt : beeuY s.regs < 256 ^ 40 / 2)
    (h_inv : (a * beeuY s.regs + beeuA s.regs) % beeuN s.regs = 0) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 95 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesB st.data.regs s.regs ∧
        PreservesX st.data.regs s.regs ∧
        0 < beeuA st.data.regs ∧
        beeuA st.data.regs ≤ beeuA s.regs ∧
        beeuY st.data.regs < 256 ^ 40 / 2 ∧
        (a * beeuY st.data.regs + beeuA st.data.regs) % beeuN s.regs = 0 ∧
        ∃ k : Nat, k ≤ 63 ∧
          ((2 ^ k : Nat) : Int) * beeuA st.data.regs = beeuA s.regs ∧
          ((2 ^ k : Nat) : Int) * beeuY st.data.regs ≤
            beeuY s.regs + (((2 ^ k : Nat) : Int) - 1) * beeuN s.regs ∧
          (beeuA s.regs % 2 = 0 → 1 ≤ k) ∧
          (beeuA st.data.regs % 2 = 0 → k = 63))
      ⟨s, beeuExec.addrOf 63⟩ := by
  refine eventually_trans _ _ _ _ (beeu_shift_A_header_correct s) ?_
  rintro ⟨mid, pc1⟩ ⟨hdmem1, hcore1, hB1, hX1, hY1, h_branch⟩
  dsimp only at hdmem1 hcore1 hB1 hX1 hY1 h_branch
  by_cases hk : ctzClamped s.regs.X21 = 0#64
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨hpc1, hA1, h_odd⟩
    have hY_eq := beeuY_of_pres hY1
    exact .done _ ⟨hpc1, hdmem1, hcore1, hB1, hX1, hA1.symm ▸ hA_pos, hA1.symm ▸ Int.le_refl _,
      hY_eq.symm ▸ hY_lt, by rw [hY_eq, hA1]; exact h_inv,
      0, by omega, by rw [hA1]; simp, by rw [hY_eq]; simp, by intro h; omega,
      by rw [hA1]; intro h; omega⟩
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨hpc1, hx13, hk_pos, hx14, hA_shift, h_par⟩
    subst hpc1
    have h_N_lt : beeuN s.regs < 256 ^ 32 := val256_lt _ _ _ _
    have hN_eq := beeuN_of_core hcore1
    have hY_eq := beeuY_of_pres hY1
    have h_yn_lt : beeuY mid.regs + beeuN mid.regs < 256 ^ 40 := by
      rw [hY_eq, hN_eq]; omega
    refine eventually_weaken _ _ _ _ ?_
      (beeu_shift_loop_Y_correct mid (hx13 ▸ hk_pos) hx14 (hN_eq.symm ▸ hN_odd) h_yn_lt)
    rintro fin ⟨hpc2, hdmem2, hcore2, hA2, hB2, hX2, hY_mod, hY_lt2, hY_bnd⟩
    have hA_eq := beeuA_of_pres hA2
    have hA_nn : 0 ≤ beeuA fin.data.regs := val256_nonneg _ _ _ _
    have ⟨hA'_pos, hA'_le⟩ := pos_and_le_of_pow2_mul
      (ctzClamped s.regs.X21).toNat (beeuA s.regs) (beeuA fin.data.regs)
      hA_pos hA_nn (hA_eq.symm ▸ hA_shift)
    have hk63 : (ctzClamped s.regs.X21).toNat ≤ 63 :=
      BitVec.le_def.mp (clz_reverse_or_one_le_63 s.regs.X21.toBitVec)
    rw [hx13, hN_eq, hY_eq] at hY_mod hY_bnd
    refine ⟨hpc2, hdmem2.trans hdmem1,
      ⟨hcore2.1.trans hcore1.1, hcore2.2.1.trans hcore1.2.1, hcore2.2.2.1.trans hcore1.2.2.1,
       hcore2.2.2.2.1.trans hcore1.2.2.2.1, hcore2.2.2.2.2.1.trans hcore1.2.2.2.2.1,
       hcore2.2.2.2.2.2.trans hcore1.2.2.2.2.2⟩,
      ⟨hB2.1.trans hB1.1, hB2.2.1.trans hB1.2.1, hB2.2.2.1.trans hB1.2.2.1, hB2.2.2.2.trans hB1.2.2.2⟩,
      ⟨hX2.1.trans hX1.1, hX2.2.1.trans hX1.2.1, hX2.2.2.1.trans hX1.2.2.1,
       hX2.2.2.2.1.trans hX1.2.2.2.1, hX2.2.2.2.2.trans hX1.2.2.2.2⟩,
      hA'_pos, hA'_le, hY_lt2, ?_, (ctzClamped s.regs.X21).toNat, hk63,
      hA_eq.symm ▸ hA_shift, hY_bnd, fun _ => hk_pos, ?_⟩
    · exact shift_A_Y_mod_inv (ctzClamped s.regs.X21).toNat a
        (beeuA s.regs) (beeuA fin.data.regs) (beeuY s.regs) (beeuY fin.data.regs) (beeuN s.regs)
        hN_odd (hA_eq.symm ▸ hA_shift) hY_mod h_inv
    · intro h_even
      rw [hA_eq] at h_even
      exact congrArg BitVec.toNat (h_par h_even)

private theorem beeu_loop_exit_when_B_zero [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (h_B_zero : beeuB s.regs = 0) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 122 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesA st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs)
      ⟨s, beeuExec.addrOf 27⟩ := by
  have ⟨h25, h26, h27, h28⟩ := val256_eq_zero_limbs s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28 h_B_zero
  sym => kstep; tactic =>
  rename_i val_x14
  have hcbz : (val_x14 == 0) = true := by
    have : val_x14 = 0#64 := by
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero, h25, h26, h27, h28]
      rfl
    rw [this]; rfl
  simp only [hcbz, ↓reduceIte]
  sym => kstep 0; tactic =>
  exact .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem beeu_update_step_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (h_xy_bound : beeuX s.regs + beeuY s.regs < 256 ^ 40) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 27 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        if beeuB s.regs ≥ beeuA s.regs then
          beeuB st.data.regs = beeuB s.regs - beeuA s.regs ∧
          beeuA st.data.regs = beeuA s.regs ∧
          beeuX st.data.regs = beeuX s.regs + beeuY s.regs ∧
          beeuY st.data.regs = beeuY s.regs
        else
          beeuB st.data.regs = beeuB s.regs ∧
          beeuA st.data.regs = beeuA s.regs - beeuB s.regs ∧
          beeuX st.data.regs = beeuX s.regs ∧
          beeuY st.data.regs = beeuY s.regs + beeuX s.regs)
      ⟨s, beeuExec.addrOf 95⟩ := by
  sym => kstep; tactic =>
  -- Stopped at bcs .Lbeeu_B_greater_than_A after 4-limb subs/sbcs (B - A)
  by_cases h_ge : beeuB s.regs ≥ beeuA s.regs
  · simp only [h_ge, ↓reduceIte]
    refine effects_all_ite_true ?_ ?_
    · have h_carry := sub256_carry_of_ge s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28
        s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 h_ge
      dsimp only [sub0Carry, sbcCarry] at h_carry
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
      exact h_carry
    · have hB' := sub256_val_of_ge s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28
        s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 h_ge
      have hX' := add320_val_of_lt s.regs.X3 s.regs.X4 s.regs.X5 s.regs.X6 s.regs.X7
        s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12 h_xy_bound
      sym => kstep 10; tactic =>
      refine .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, ?_, rfl⟩
      · rw [← hB']
        apply val256_congr <;>
          simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
            show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero, BitVec.zero_or]
      · rw [← hX']
        apply val320_congr <;>
          simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
            show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
  · simp only [h_ge, ↓reduceIte]
    have h_lt : beeuB s.regs < beeuA s.regs := Int.lt_of_not_ge h_ge
    refine effects_all_ite_false ?_ ?_
    · have h_carry := sub256_carry_of_lt s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28
        s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 h_lt
      dsimp only [sub0Carry, sbcCarry] at h_carry
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
      exact h_carry
    · have h_le : beeuA s.regs ≥ beeuB s.regs := Int.le_of_lt h_lt
      have h_yx_bound : val320 s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12 +
          val320 s.regs.X3 s.regs.X4 s.regs.X5 s.regs.X6 s.regs.X7 < 256 ^ 40 := by
        omega
      have hA' := sub256_val_of_ge s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24
        s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28 h_le
      have hY' := add320_val_of_lt s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12
        s.regs.X3 s.regs.X4 s.regs.X5 s.regs.X6 s.regs.X7 h_yx_bound
      sym => kstep 10; tactic =>
      refine .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_, rfl, ?_⟩
      · rw [← hA']
        apply val256_congr <;>
          simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
            show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
      · rw [← hY']
        apply val320_congr <;>
          simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
            show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]

private theorem beeu_loop_body_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int) (σ τ : Nat)
    (hB_pos : 0 < beeuB s.regs)
    (hI : BeeuInv a (beeuN s.regs) σ τ (beeuB s.regs) (beeuA s.regs) (beeuX s.regs) (beeuY s.regs)) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 27 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        beeuA st.data.regs ≤ beeuA s.regs ∧
        (beeuB st.data.regs + beeuA st.data.regs).toNat <
          (beeuB s.regs + beeuA s.regs).toNat ∧
        ∃ σ' τ' : Nat,
          BeeuInv a (beeuN s.regs) σ' τ' (beeuB st.data.regs) (beeuA st.data.regs)
            (beeuX st.data.regs) (beeuY st.data.regs))
      ⟨s, beeuExec.addrOf 27⟩ := by
  have hN_lt : beeuN s.regs < 256 ^ 32 := val256_lt _ _ _ _
  have hN_pos : 0 < beeuN s.regs := by have := hI.A_pos; have := hI.A_le; omega
  have hN0 : 0 ≤ beeuN s.regs := Int.le_of_lt hN_pos
  have hM0 : 0 ≤ beeuBound σ τ := Int.le_of_lt (beeuBound_pos σ τ)
  obtain ⟨hX_lt, hY_lt, hM_512⟩ := hI.bounds hB_pos hN_lt
  -- Phase 1: shift B and X.
  refine eventually_trans _ _ _ _ (beeu_shift_B_X_correct s a hB_pos hI.N_odd hX_lt hI.X_inv) ?_
  rintro ⟨st1, pc1⟩ ⟨hpc1, h1_dmem, h1_core, h1_A, h1_Y, h1_B_pos, h1_B_le, h1_X_lt, h1_X_inv,
    k₁, hk₁_le, h1_B_shift, h1_X_bnd, h1_k₁_pos, h1_clamp⟩
  dsimp only at hpc1 h1_dmem h1_core h1_A h1_Y h1_B_pos h1_B_le h1_X_lt h1_X_inv h1_B_shift h1_X_bnd h1_k₁_pos h1_clamp
  subst hpc1
  have h1_N := beeuN_of_core h1_core
  have h1_A_eq := beeuA_of_pres h1_A
  have h1_Y_eq := beeuY_of_pres h1_Y
  -- Phase 2: shift A and Y.
  refine eventually_trans _ _ _ _
    (beeu_shift_A_Y_correct st1 a (h1_A_eq.symm ▸ hI.A_pos) (h1_N.symm ▸ hI.N_odd)
      (h1_Y_eq.symm ▸ hY_lt) (by rw [h1_Y_eq, h1_A_eq, h1_N]; exact hI.Y_inv)) ?_
  rintro ⟨st2, pc2⟩ ⟨hpc2, h2_dmem, h2_core, h2_B_p, h2_X_p, h2_A_pos, h2_A_le, h2_Y_lt, h2_Y_inv,
    k₂, hk₂_le, h2_A_shift, h2_Y_bnd, h2_k₂_pos, h2_clamp⟩
  dsimp only at hpc2 h2_dmem h2_core h2_B_p h2_X_p h2_A_pos h2_A_le h2_Y_lt h2_Y_inv h2_A_shift h2_Y_bnd h2_k₂_pos h2_clamp
  subst hpc2
  have h2_B := beeuB_of_pres h2_B_p
  have h2_X := beeuX_of_pres h2_X_p
  rw [h1_A_eq] at h2_A_shift h2_k₂_pos h2_A_le
  rw [h1_Y_eq, h1_N] at h2_Y_bnd
  rw [h1_N] at h2_Y_inv
  have hX₂ : beeuX st2.regs < beeuN s.regs * (beeuBound σ τ + k₁) := by
    rw [h2_X]
    exact shift_phase_bound _ _ _ _ _ k₁ hN0 hM0 hI.X_lt hI.X_lt_odd h1_k₁_pos h1_X_bnd
  have hY₂ : beeuY st2.regs < beeuN s.regs * (beeuBound σ τ + k₂) :=
    shift_phase_bound _ _ _ _ _ k₂ hN0 hM0 hI.Y_lt hI.Y_lt_odd h2_k₂_pos h2_Y_bnd
  -- Phase 3: the update step.
  have h_xy_lt : beeuX st2.regs + beeuY st2.regs < 256 ^ 40 := by omega
  refine eventually_weaken _ _ _ _ ?_ (beeu_update_step_correct st2 h_xy_lt)
  rintro fin ⟨hpc3, h3_dmem, h3_core, h3_branch⟩
  have h2_B_pos : 0 < beeuB st2.regs := h2_B.symm ▸ h1_B_pos
  have h2_B_le : beeuB st2.regs ≤ beeuB s.regs := h2_B.symm ▸ h1_B_le
  have h2_X_inv : (a * beeuX st2.regs - beeuB st2.regs) % beeuN s.regs = 0 := by
    rw [h2_X, h2_B]; exact h1_X_inv
  have h2_X_bnd : ((2 ^ k₁ : Nat) : Int) * beeuX st2.regs ≤
      beeuX s.regs + (((2 ^ k₁ : Nat) : Int) - 1) * beeuN s.regs := h2_X ▸ h1_X_bnd
  have hI_B_le := hI.B_le
  have hI_A_le := hI.A_le
  have hI_B_nonneg := hI.B_nonneg
  have hI_A_pos := hI.A_pos
  have hg_odd : (Int.gcd (beeuA s.regs) (beeuB s.regs) : Int) % 2 = 1 := by
    rw [hI.gcd_eq]
    exact odd_of_dvd_odd _ _ hI.N_odd (Int.gcd_dvd_right a (beeuN s.regs))
  have hg1 : Int.gcd (beeuA s.regs) (beeuB st2.regs) = Int.gcd (beeuA s.regs) (beeuB s.regs) :=
    gcd_of_two_pow_mul_odd _ _ _ k₁ (by rw [h2_B]; exact h1_B_shift) hg_odd
  have hg_odd' : (Int.gcd (beeuB st2.regs) (beeuA s.regs) : Int) % 2 = 1 := by
    rw [Int.gcd_comm, hg1]; exact hg_odd
  have hg2 : Int.gcd (beeuA st2.regs) (beeuB st2.regs) = Int.gcd a (beeuN s.regs) := by
    rw [Int.gcd_comm, gcd_of_two_pow_mul_odd _ _ _ k₂ h2_A_shift hg_odd', Int.gcd_comm, hg1,
      hI.gcd_eq]
  have hM_eq := beeuBound_add σ τ k₁ k₂
  have h_parity_clamp : (beeuB st2.regs - beeuA st2.regs) % 2 = 1 ∨
      (beeuA st2.regs - beeuB st2.regs) % 2 = 1 → k₁ = 63 ∨ k₂ = 63 := by
    intro h
    have hBe : beeuB st2.regs % 2 = 0 ∨ beeuA st2.regs % 2 = 0 := by omega
    rcases hBe with hB0 | hA0
    · exact Or.inl (h1_clamp (h2_B ▸ hB0))
    · exact Or.inr (h2_clamp hA0)
  have hpow_σ : ((2 ^ (σ + k₁) : Nat) : Int) = ((2 ^ σ : Nat) : Int) * ((2 ^ k₁ : Nat) : Int) := by
    rw [Nat.pow_add, Int.natCast_mul]
  have hpow_τ : ((2 ^ (τ + k₂) : Nat) : Int) = ((2 ^ τ : Nat) : Int) * ((2 ^ k₂ : Nat) : Int) := by
    rw [Nat.pow_add, Int.natCast_mul]
  have h2σ : (0 : Int) ≤ ((2 ^ σ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2τ : (0 : Int) ≤ ((2 ^ τ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2k₁ : (0 : Int) ≤ ((2 ^ k₁ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2k₂ : (0 : Int) ≤ ((2 ^ k₂ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have hB_shifted' : ∀ B₃ : Int, B₃ ≤ beeuB st2.regs →
      ((2 ^ (σ + k₁) : Nat) : Int) * B₃ ≤ beeuN s.regs := by
    intro B₃ hB₃
    calc ((2 ^ (σ + k₁) : Nat) : Int) * B₃
        = ((2 ^ σ : Nat) : Int) * (((2 ^ k₁ : Nat) : Int) * B₃) := by rw [hpow_σ, Int.mul_assoc]
      _ ≤ ((2 ^ σ : Nat) : Int) * (((2 ^ k₁ : Nat) : Int) * beeuB st2.regs) :=
          Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hB₃ h2k₁) h2σ
      _ = ((2 ^ σ : Nat) : Int) * beeuB s.regs := by rw [h2_B, h1_B_shift]
      _ ≤ beeuN s.regs := hI.B_shifted
  have hA_shifted' : ∀ A₃ : Int, A₃ ≤ beeuA st2.regs →
      ((2 ^ (τ + k₂) : Nat) : Int) * A₃ ≤ beeuN s.regs := by
    intro A₃ hA₃
    calc ((2 ^ (τ + k₂) : Nat) : Int) * A₃
        = ((2 ^ τ : Nat) : Int) * (((2 ^ k₂ : Nat) : Int) * A₃) := by rw [hpow_τ, Int.mul_assoc]
      _ ≤ ((2 ^ τ : Nat) : Int) * (((2 ^ k₂ : Nat) : Int) * beeuA st2.regs) :=
          Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hA₃ h2k₂) h2τ
      _ = ((2 ^ τ : Nat) : Int) * beeuA s.regs := by rw [h2_A_shift]
      _ ≤ beeuN s.regs := hI.A_shifted
  have hM'0 : 0 ≤ beeuN s.regs * beeuBound (σ + k₁) (τ + k₂) :=
    Int.mul_nonneg hN0 (Int.le_of_lt (beeuBound_pos _ _))
  have hcore_all : PreservesCore fin.data.regs s.regs :=
    ⟨h3_core.1.trans (h2_core.1.trans h1_core.1),
     h3_core.2.1.trans (h2_core.2.1.trans h1_core.2.1),
     h3_core.2.2.1.trans (h2_core.2.2.1.trans h1_core.2.2.1),
     h3_core.2.2.2.1.trans (h2_core.2.2.2.1.trans h1_core.2.2.2.1),
     h3_core.2.2.2.2.1.trans (h2_core.2.2.2.2.1.trans h1_core.2.2.2.2.1),
     h3_core.2.2.2.2.2.trans (h2_core.2.2.2.2.2.trans h1_core.2.2.2.2.2)⟩
  refine ⟨hpc3, h3_dmem.trans (h2_dmem.trans h1_dmem), hcore_all, ?_, ?_, σ + k₁, τ + k₂, ?_⟩
  all_goals by_cases h_ge : beeuB st2.regs ≥ beeuA st2.regs
  all_goals simp only [h_ge, ↓reduceIte] at h3_branch
  all_goals rcases h3_branch with ⟨hB', hA', hX', hY'⟩
  · omega
  · omega
  · omega
  · omega
  · refine ⟨hI.N_odd, ?_, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA', hB', Int.gcd_sub_self_right]; exact hg2
    · have h_lin : a * beeuX fin.data.regs - beeuB fin.data.regs =
          (a * beeuX st2.regs - beeuB st2.regs) + (a * beeuY st2.regs + beeuA st2.regs) := by
        rw [hX', hB']; grind
      rw [h_lin, Int.add_emod, h2_X_inv, h2_Y_inv]; simp
    · rw [hY', hA']; exact h2_Y_inv
    · exact hB_shifted' _ (by omega)
    · exact hA_shifted' _ (by omega)
    · rw [hX']; exact update_bound_even _ _ _ _ _ k₁ k₂ hN0 hX₂ hY₂ (by omega)
    · intro h_odd; rw [hX']
      exact update_bound_clamped _ _ _ _ _ _ _ k₁ k₂ hN0 hM_512 hI.X_lt hI.Y_lt hX₂ hY₂
        h2_X_bnd h2_Y_bnd (h_parity_clamp (Or.inl (hB' ▸ h_odd))) (by omega)
    · rw [hY']
      have := bound_mono_right _ _ _ _ hN0 hY₂
        (by omega : beeuBound σ τ + k₂ ≤ beeuBound (σ + k₁) (τ + k₂))
      omega
    · intro _; rw [hY']
      exact bound_mono_right _ _ _ _ hN0 hY₂ (by omega)
  · refine ⟨hI.N_odd, ?_, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA', hB', Int.gcd_sub_self_left]; exact hg2
    · rw [hX', hB']; exact h2_X_inv
    · have h_lin : a * beeuY fin.data.regs + beeuA fin.data.regs =
          (a * beeuY st2.regs + beeuA st2.regs) + (a * beeuX st2.regs - beeuB st2.regs) := by
        rw [hY', hA']; grind
      rw [h_lin, Int.add_emod, h2_Y_inv, h2_X_inv]; simp
    · exact hB_shifted' _ (by omega)
    · exact hA_shifted' _ (by omega)
    · rw [hX']
      have := bound_mono_right _ _ _ _ hN0 hX₂
        (by omega : beeuBound σ τ + k₁ ≤ beeuBound (σ + k₁) (τ + k₂))
      omega
    · intro _; rw [hX']
      exact bound_mono_right _ _ _ _ hN0 hX₂ (by omega)
    · rw [hY']
      have := update_bound_even (beeuY st2.regs) (beeuX st2.regs) (beeuN s.regs) (beeuBound σ τ)
        (beeuBound (σ + k₁) (τ + k₂)) k₂ k₁ hN0 hY₂ hX₂ (by omega)
      omega
    · intro h_odd; rw [hY']
      have := update_bound_clamped (beeuX s.regs) (beeuX st2.regs) (beeuY s.regs) (beeuY st2.regs)
        (beeuN s.regs) (beeuBound σ τ) (beeuBound (σ + k₁) (τ + k₂)) k₁ k₂ hN0 hM_512
        hI.X_lt hI.Y_lt hX₂ hY₂ h2_X_bnd h2_Y_bnd (h_parity_clamp (Or.inr (hA' ▸ h_odd))) (by omega)
      omega

private theorem beeu_loop_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int)
    (hI : BeeuInv a (beeuN s.regs) 0 0 (beeuB s.regs) (beeuA s.regs) (beeuX s.regs) (beeuY s.regs)) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 122 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        0 < beeuA st.data.regs ∧
        beeuA st.data.regs ≤ beeuA s.regs ∧
        (a * beeuY st.data.regs + beeuA st.data.regs) % beeuN s.regs = 0 ∧
        (beeuA st.data.regs = 1 ↔ Int.gcd a (beeuN s.regs) = 1))
      ⟨s, beeuExec.addrOf 27⟩ := by
  let Q : MachineState → Prop := fun st =>
    st.pc = beeuExec.addrOf 122 ∧
    st.data.dmem = s.dmem ∧
    PreservesCore st.data.regs s.regs ∧
    0 < beeuA st.data.regs ∧
    beeuA st.data.regs ≤ beeuA s.regs ∧
    (a * beeuY st.data.regs + beeuA st.data.regs) % beeuN s.regs = 0 ∧
    (beeuA st.data.regs = 1 ↔ Int.gcd a (beeuN s.regs) = 1)
  refine tailrec_loop
    (onLoop := fun (g : Nat × Nat × Nat) st =>
      st.pc = beeuExec.addrOf 27 ∧
      st.data.dmem = s.dmem ∧
      PreservesCore st.data.regs s.regs ∧
      beeuA st.data.regs ≤ beeuA s.regs ∧
      (beeuB st.data.regs + beeuA st.data.regs).toNat = g.1 ∧
      BeeuInv a (beeuN s.regs) g.2.1 g.2.2 (beeuB st.data.regs) (beeuA st.data.regs)
        (beeuX st.data.regs) (beeuY st.data.regs))
    (onExit := fun _ => Q)
    (fun g' g => g'.1 < g.1) (InvImage.wf Prod.fst Nat.lt_wfRel.wf)
    ((beeuB s.regs + beeuA s.regs).toNat, 0, 0)
    ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, Int.le_refl _, rfl, hI⟩
    ?_ (fun _ h => h)
  rintro ⟨v, σ, τ⟩ ⟨st, pc⟩ ⟨hpc, hst_dmem, hst_core, hst_A_le, hst_v, hst_I⟩
  dsimp only at hpc hst_dmem hst_core hst_A_le hst_v hst_I
  subst hpc
  by_cases hB0 : beeuB st.regs = 0
  · refine eventually_weaken _ _ _ _ ?_ (beeu_loop_exit_when_B_zero st hB0)
    rintro fin ⟨hpc', hdmem', hcore', hA', hY'⟩
    have hA_eq := beeuA_of_pres hA'
    have hY_eq := beeuY_of_pres hY'
    refine .break ⟨hpc', hdmem'.trans hst_dmem,
      ⟨hcore'.1.trans hst_core.1, hcore'.2.1.trans hst_core.2.1,
       hcore'.2.2.1.trans hst_core.2.2.1, hcore'.2.2.2.1.trans hst_core.2.2.2.1,
       hcore'.2.2.2.2.1.trans hst_core.2.2.2.2.1, hcore'.2.2.2.2.2.trans hst_core.2.2.2.2.2⟩,
      hA_eq.symm ▸ hst_I.A_pos, hA_eq.symm ▸ hst_A_le, ?_, ?_⟩
    · rw [hY_eq, hA_eq]; exact hst_I.Y_inv
    · have hg := hst_I.gcd_eq
      rw [hB0, Int.gcd_zero] at hg
      have hA_pos := hst_I.A_pos
      rw [hA_eq]
      constructor
      · intro h; rw [← hg]; omega
      · intro h; rw [← hg] at h; omega
  · have hst_B_pos : 0 < beeuB st.regs := by have := hst_I.B_nonneg; omega
    have hN_eq := beeuN_of_core hst_core
    have hst_I' : BeeuInv a (beeuN st.regs) σ τ (beeuB st.regs) (beeuA st.regs)
        (beeuX st.regs) (beeuY st.regs) := by
      rw [hN_eq]; exact hst_I
    refine eventually_weaken _ _ _ _ ?_ (beeu_loop_body_correct st a σ τ hst_B_pos hst_I')
    rintro mid ⟨hpc', hdmem', hcore', hA_le', hlt', σ', τ', hI'⟩
    refine .loop ((beeuB mid.data.regs + beeuA mid.data.regs).toNat, σ', τ')
      ⟨hpc', hdmem'.trans hst_dmem,
       ⟨hcore'.1.trans hst_core.1, hcore'.2.1.trans hst_core.2.1,
        hcore'.2.2.1.trans hst_core.2.2.1, hcore'.2.2.2.1.trans hst_core.2.2.2.1,
        hcore'.2.2.2.2.1.trans hst_core.2.2.2.2.1, hcore'.2.2.2.2.2.trans hst_core.2.2.2.2.2⟩,
       Int.le_trans hA_le' hst_A_le, rfl, hN_eq ▸ hI'⟩ (hst_v ▸ hlt') (fun _ h => h)

/-! ### Reduction Loop, Post-Loop Store, and Top-Level Specification -/

private theorem beeu_loop_end_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs ∧
        if beeuA s.regs = 1 then
          st.pc = beeuExec.addrOf 128 ∧
          st.data.regs.X14 = 0
        else
          st.pc = beeuExec.addrOf 149)
      ⟨s, beeuExec.addrOf 122⟩ := by
  sym => kstep; tactic =>
  -- Stopped at cbnz x14, .Lbeeu_err
  by_cases hA : beeuA s.regs = 1
  · simp only [hA, ↓reduceIte]
    have ⟨h21, h22, h23, h24⟩ := val256_eq_one_limbs s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 hA
    refine effects_all_ite_false ?_ ?_
    · simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero, h21, h22, h23, h24]
      rfl
    · sym => kstep 0; tactic =>
      refine .done _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
      apply UInt64.eq_of_toBitVec_eq
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero, h21, h22, h23, h24]
      rfl
  · simp only [hA, ↓reduceIte]
    have h_nz := val256_ne_one_or_ne_zero s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 hA
    refine effects_all_ite_true ?_ ?_
    · dsimp only [bne]
      simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
      change (!((s.regs.X21.toBitVec - 1#64 ||| s.regs.X22.toBitVec |||
        s.regs.X23.toBitVec ||| s.regs.X24.toBitVec) == 0#64)) = true
      rw [h_nz]; rfl
    · sym => kstep 0; tactic =>
      exact .done _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

private theorem beeu_reduction_step_ge_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h14 : s.regs.X14 = 0)
    (h_ge : beeuY s.regs ≥ beeuN s.regs) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 128 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        st.data.regs.X14 = s.regs.X14 ∧
        beeuY st.data.regs = beeuY s.regs - beeuN s.regs)
      ⟨s, beeuExec.addrOf 128⟩ := by
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h_n320 : val320 s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 = beeuN s.regs := by
    dsimp only [beeuN, val320, val256]; rw [h14, h0]; omega
  have h_ge320 : val320 s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12 ≥
      val320 s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 := by
    rw [h_n320]; exact h_ge
  have h_carry := sub320_carry_of_ge s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12
    s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 h_ge320
  have h_sub := sub320_val_of_ge s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12
    s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 h_ge320
  dsimp only [sub0Carry, sbcCarry] at h_carry
  sym => kstep; tactic =>
  -- Stopped at bcs .Lbeeu_reduction_loop after 5-limb subs/sbcs and 5 csels
  refine effects_all_ite_true ?_ ?_
  · simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
      show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
    exact h_carry
  · sym => kstep 0; tactic =>
    refine .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
    rw [← h_n320, ← h_sub]
    apply val320_congr <;>
      (simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
        show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
       exact ite_eq_left_of_eq_true h_carry)

private theorem beeu_reduction_exit_lt [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h14 : s.regs.X14 = 0)
    (h_lt : beeuY s.regs < beeuN s.regs) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 140 ∧
        st.data.dmem = s.dmem ∧
        PreservesCore st.data.regs s.regs ∧
        PreservesY st.data.regs s.regs)
      ⟨s, beeuExec.addrOf 128⟩ := by
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h_n320 : val320 s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 = beeuN s.regs := by
    dsimp only [beeuN, val320, val256]; rw [h14, h0]; omega
  have h_lt320 : val320 s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12 <
      val320 s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 := by
    rw [h_n320]; exact h_lt
  have h_carry := sub320_carry_of_lt s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12
    s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30 s.regs.X14 h_lt320
  dsimp only [sub0Carry, sbcCarry] at h_carry
  sym => kstep; tactic =>
  refine effects_all_ite_false ?_ ?_
  · simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
      show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
    exact h_carry
  · sym => kstep 0; tactic =>
    refine .done _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (apply UInt64.eq_of_toBitVec_eq
       simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
         show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]
       exact ite_eq_right_of_eq_false h_carry)

private theorem beeu_final_sub_256 [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData)
    (h_le : beeuY256 s.regs ≤ beeuN s.regs) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 144 ∧
        st.data.dmem = s.dmem ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        val256 st.data.regs.X8 st.data.regs.X9 st.data.regs.X10 st.data.regs.X11 =
          beeuN s.regs - beeuY256 s.regs)
      ⟨s, beeuExec.addrOf 140⟩ := by
  have h_sub := sub256_val_of_ge s.regs.X0 s.regs.X1 s.regs.X2 s.regs.X30
    s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 h_le
  sym => kstep 4; tactic =>
  refine .done _ ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [← h_sub]
  apply val256_congr <;>
    simp (config := { zetaDelta := true }) only [extractLsb'_0_64,
      show (Int64.toInt 0).toNat = 0 from rfl, BitVec.shiftLeft_zero]

private theorem beeu_store_and_jump_finish [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (sp' out_p : BitVec 64) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
    (h_sp_align : sp' % 16#64 = 0#64)
    (h_sp : s.regs.SP = UInt64.ofBitVec sp')
    (h_mem : s.dmem =⋆
      Eq ((Int.toBytes 8 out_p.toInt).At (sp' + 96#64)) ⋆
      Words256At o0 o1 o2 o3 out_p ⋆ R) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 151 ∧
        st.data.regs.X0 = 1 ∧
        st.data.regs.SP = UInt64.ofBitVec sp' ∧
        st.data.regs.X29 = s.regs.X29 ∧
        (st.data.dmem =⋆
          Eq ((Int.toBytes 8 out_p.toInt).At (sp' + 96#64)) ⋆
          Words256At s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 out_p ⋆ R))
      ⟨s, beeuExec.addrOf 144⟩ := by
  rcases s with ⟨regs, status, dmem⟩
  dsimp only at h_sp h_mem ⊢
  have h_sp_bv : regs.SP.toBitVec = sp' := congrArg UInt64.toBitVec h_sp
  let P_ptr : DataMem → Prop := Eq ((Int.toBytes 8 out_p.toInt).At (sp' + 96#64))
  let W0 : DataMem → Prop := Eq ((Int.toBytes 8 o0.toBitVec.toInt).At out_p)
  let W1 : DataMem → Prop := Eq ((Int.toBytes 8 o1.toBitVec.toInt).At (out_p + 8#64))
  let W2 : DataMem → Prop := Eq ((Int.toBytes 8 o2.toBitVec.toInt).At (out_p + 16#64))
  let W3 : DataMem → Prop := Eq ((Int.toBytes 8 o3.toBitVec.toInt).At (out_p + 24#64))
  let W0' : DataMem → Prop := Eq ((Int.toBytes 8 regs.X8.toBitVec.toInt).At out_p)
  let W1' : DataMem → Prop := Eq ((Int.toBytes 8 regs.X9.toBitVec.toInt).At (out_p + 8#64))
  let W2' : DataMem → Prop := Eq ((Int.toBytes 8 regs.X10.toBitVec.toInt).At (out_p + 16#64))
  let W3' : DataMem → Prop := Eq ((Int.toBytes 8 regs.X11.toBitVec.toInt).At (out_p + 24#64))
  -- 144: ldr x3, [sp, #96]
  have hm0 : dmem =⋆ Eq ((Int.toBytes 8 out_p.toInt).At (sp' + 96#64)) ⋆
      (Words256At o0 o1 o2 o3 out_p ⋆ R) := by
    simpa only [sep_assoc] using h_mem
  refine step_ldr64_sp_offset (k := 144) rfl (Int.toBytes 8 out_p.toInt)
    (h_sp_bv.symm ▸ h_sp_align) (sp' + 96#64) (by rw [h_sp_bv]; rfl)
    (Int.toBytes_length 8 _) hm0 ?_
  dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  -- 145: stp x8, x9, [x3]
  have hm1 : dmem =⋆ W0 ⋆ W1 ⋆ (P_ptr ⋆ W2 ⋆ W3 ⋆ R) := by
    have h_flat : dmem =⋆ P_ptr ⋆ (W0 ⋆ W1 ⋆ W2 ⋆ W3) ⋆ R := h_mem
    have heq : (P_ptr ⋆ (W0 ⋆ W1 ⋆ W2 ⋆ W3) ⋆ R) = (W0 ⋆ W1 ⋆ (P_ptr ⋆ W2 ⋆ W3 ⋆ R)) := by ac_rfl
    exact heq ▸ h_flat
  refine step_stp64_offset (k := 145) rfl
    (Int.toBytes 8 o0.toBitVec.toInt) (Int.toBytes 8 o1.toBitVec.toInt)
    (fun h => by cases h) out_p (out_p + 8#64)
    (by dsimp only [RegOrSp.base, Reg64s.getRegOrSp64, Reg64s.getXReg]
        exact (BitVec.add_zero out_p).symm)
    rfl (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (by dsimp only [W0, W1] at hm1; exact hm1) ?_
  intro dmem1 hm2
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at hm2
  -- 146: stp x10, x11, [x3, #16]
  have hm3 : dmem1 =⋆ W2 ⋆ W3 ⋆ (P_ptr ⋆ W0' ⋆ W1' ⋆ R) := by
    have h_flat : dmem1 =⋆ W0' ⋆ W1' ⋆ (P_ptr ⋆ W2 ⋆ W3 ⋆ R) := hm2
    have heq : (W0' ⋆ W1' ⋆ (P_ptr ⋆ W2 ⋆ W3 ⋆ R)) = (W2 ⋆ W3 ⋆ (P_ptr ⋆ W0' ⋆ W1' ⋆ R)) := by ac_rfl
    exact heq ▸ h_flat
  refine step_stp64_offset (k := 146) rfl
    (Int.toBytes 8 o2.toBitVec.toInt) (Int.toBytes 8 o3.toBitVec.toInt)
    (fun h => by cases h) (out_p + 16#64) (out_p + 24#64)
    rfl (BitVec.add_assoc out_p 16#64 8#64).symm
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (by dsimp only [W2, W3] at hm3; exact hm3) ?_
  intro dmem2 hm4
  dsimp only [RegOrZr.base, Reg64s.getRegOrZr64, Reg64s.getXReg] at hm4
  have hm_final : dmem2 =⋆ P_ptr ⋆ (W0' ⋆ W1' ⋆ W2' ⋆ W3') ⋆ R := by
    have h_flat : dmem2 =⋆ W2' ⋆ W3' ⋆ (P_ptr ⋆ W0' ⋆ W1' ⋆ R) := hm4
    have heq : (W2' ⋆ W3' ⋆ (P_ptr ⋆ W0' ⋆ W1' ⋆ R)) = (P_ptr ⋆ (W0' ⋆ W1' ⋆ W2' ⋆ W3') ⋆ R) := by ac_rfl
    exact heq ▸ h_flat
  -- 147: mov x0, #1; 148: b .Lbeeu_finish
  sym => kstep 2; tactic =>
  exact .done _ ⟨rfl, rfl, h_sp, rfl, hm_final⟩

private theorem beeu_reduction_and_store_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (sp' out_p : BitVec 64) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
    (h_sp_align : sp' % 16#64 = 0#64)
    (h_sp : s.regs.SP = UInt64.ofBitVec sp')
    (h14 : s.regs.X14 = 0)
    (h_lt : beeuY s.regs < beeuN s.regs)
    (h_mem : s.dmem =⋆
      Eq ((Int.toBytes 8 out_p.toInt).At (sp' + 96#64)) ⋆
      Words256At o0 o1 o2 o3 out_p ⋆ R) :
    Eventually (step1 beeuExec)
      (fun st =>
        st.pc = beeuExec.addrOf 151 ∧
        st.data.regs.X0 = 1 ∧
        st.data.regs.SP = UInt64.ofBitVec sp' ∧
        st.data.regs.X29 = s.regs.X29 ∧
        ∃ w0 w1 w2 w3 : UInt64,
          val256 w0 w1 w2 w3 = beeuN s.regs - beeuY s.regs ∧
          (st.data.dmem =⋆
            Eq ((Int.toBytes 8 out_p.toInt).At (sp' + 96#64)) ⋆
            Words256At w0 w1 w2 w3 out_p ⋆ R))
      ⟨s, beeuExec.addrOf 128⟩ := by
  have h_N_lt : beeuN s.regs < 256 ^ 32 := val256_lt _ _ _ _
  have ⟨_, h_y256⟩ := val320_lt_256_pow_32 s.regs.X8 s.regs.X9 s.regs.X10 s.regs.X11 s.regs.X12
    (by dsimp only [beeuY] at h_lt; omega)
  refine eventually_trans _ _ _ _ (beeu_reduction_exit_lt s h14 h_lt) ?_
  rintro ⟨s1, pc1⟩ ⟨hpc1, hdmem1, hcore1, hY1⟩
  dsimp only at hpc1 hdmem1 hcore1 hY1
  subst hpc1
  have hN1 := beeuN_of_core hcore1
  have hY256_1 : beeuY256 s1.regs = beeuY s.regs := by
    dsimp only [beeuY256]; rw [hY1.1, hY1.2.1, hY1.2.2.1, hY1.2.2.2.1]; exact h_y256
  have h_le1 : beeuY256 s1.regs ≤ beeuN s1.regs := by rw [hY256_1, hN1]; omega
  refine eventually_trans _ _ _ _ (beeu_final_sub_256 s1 h_le1) ?_
  rintro ⟨s2, pc2⟩ ⟨hpc2, hdmem2, hsp2, hx29_2, hval2⟩
  dsimp only at hpc2 hdmem2 hsp2 hx29_2 hval2
  subst hpc2
  refine eventually_weaken _ _ _ _ ?_
    (beeu_store_and_jump_finish s2 sp' out_p o0 o1 o2 o3 R h_sp_align
      (hsp2.trans (hcore1.1.trans h_sp)) ((hdmem2.trans hdmem1).symm ▸ h_mem))
  rintro fin ⟨hpc3, hx0_3, hsp3, hx29_3, hmem3⟩
  refine ⟨hpc3, hx0_3, hsp3, hx29_3.trans (hx29_2.trans hcore1.2.1),
    s2.regs.X8, s2.regs.X9, s2.regs.X10, s2.regs.X11, ?_, hmem3⟩
  rw [hval2, hN1, hY256_1]

private theorem beeu_reduction_to_return_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (r₀ : Reg64s) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
    (h_sp_align : r₀.SP.toBitVec % 16#64 = 0#64)
    (h_sp : s.regs.SP = UInt64.ofBitVec (r₀.SP.toBitVec + 18446744073709551504#64))
    (h_x29 : s.regs.X29 = UInt64.ofBitVec (r₀.SP.toBitVec + 18446744073709551504#64))
    (h_x14 : s.regs.X14 = 0)
    (h_n_pos : 0 < beeuN s.regs)
    (h_mem : s.dmem =⋆
      BeeuStackFrame r₀ (r₀.SP.toBitVec + 18446744073709551504#64) ⋆
      Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R) :
    Eventually (step1 beeuExec)
      (fun st =>
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
        st.data.regs.X0 = 1 ∧
        st.data.regs.SP = r₀.SP ∧
        st.data.regs.X30 = r₀.X30 ∧
        CalleeSavedEq st.data.regs r₀ ∧
        ∃ w0 w1 w2 w3 : UInt64,
          val256 w0 w1 w2 w3 = beeuN s.regs - (beeuY s.regs % beeuN s.regs) ∧
          (st.data.dmem =⋆
            BeeuStackFrame r₀ sp' ⋆
            Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R))
      ⟨s, beeuExec.addrOf 128⟩ := by
  let sp' := r₀.SP.toBitVec + 18446744073709551504#64
  let Q : MachineState → Prop := fun st =>
    st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
    st.data.regs.X0 = 1 ∧
    st.data.regs.SP = r₀.SP ∧
    st.data.regs.X30 = r₀.X30 ∧
    CalleeSavedEq st.data.regs r₀ ∧
    ∃ w0 w1 w2 w3 : UInt64,
      val256 w0 w1 w2 w3 = beeuN s.regs - (beeuY s.regs % beeuN s.regs) ∧
      (st.data.dmem =⋆
        BeeuStackFrame r₀ sp' ⋆
        Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)
  refine tailrec_loop
    (onLoop := fun (v : Nat) st =>
      st.pc = beeuExec.addrOf 128 ∧
      st.data.dmem = s.dmem ∧
      PreservesCore st.data.regs s.regs ∧
      st.data.regs.X14 = 0 ∧
      beeuY st.data.regs % beeuN s.regs = beeuY s.regs % beeuN s.regs ∧
      (beeuY st.data.regs).toNat = v)
    (onExit := fun _ => Q) (· < ·) Nat.lt_wfRel.wf (beeuY s.regs).toNat
    ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, h_x14, rfl, rfl⟩
    ?_ (fun _ h => h)
  rintro v ⟨st, pc⟩ ⟨hpc, hst_dmem, hst_core, hst_x14, hst_Y_mod, hst_v⟩
  dsimp only at hpc hst_dmem hst_core hst_x14 hst_Y_mod hst_v
  subst hpc
  have hst_N := beeuN_of_core hst_core
  by_cases h_ge : beeuY st.regs ≥ beeuN st.regs
  · refine eventually_weaken _ _ _ _ ?_ (beeu_reduction_step_ge_correct st hst_x14 h_ge)
    rintro mid ⟨hpc', hdmem', hcore', hx14', hY'⟩
    have hY_nn : 0 ≤ beeuY mid.data.regs := val320_nonneg _ _ _ _ _
    have hlt : (beeuY mid.data.regs).toNat < v := by omega
    refine .loop (beeuY mid.data.regs).toNat
      ⟨hpc', hdmem'.trans hst_dmem,
       ⟨hcore'.1.trans hst_core.1, hcore'.2.1.trans hst_core.2.1,
        hcore'.2.2.1.trans hst_core.2.2.1, hcore'.2.2.2.1.trans hst_core.2.2.2.1,
        hcore'.2.2.2.2.1.trans hst_core.2.2.2.2.1, hcore'.2.2.2.2.2.trans hst_core.2.2.2.2.2⟩,
       hx14'.trans hst_x14, ?_, rfl⟩ hlt (fun _ h => h)
    rw [hY', hst_N, Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod, hst_Y_mod]
  · have h_lt : beeuY st.regs < beeuN st.regs := Int.lt_of_not_ge h_ge
    have h_sp'_align : sp' % 16#64 = 0#64 := by
      dsimp only [sp']; rw [sp_sub_112_mod_16]; exact h_sp_align
    let R_frame : DataMem → Prop :=
      BeeuSavedRegs r₀ sp' ⋆
      Eq ((Int.toBytes 8 r₀.X2.toBitVec.toInt).At (sp' + 104#64)) ⋆ R
    have h_mem_st : st.dmem =⋆
        Eq ((Int.toBytes 8 r₀.X0.toBitVec.toInt).At (sp' + 96#64)) ⋆
        Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R_frame := by
      rw [hst_dmem]
      exact sep_5_pull ▸ h_mem
    refine eventually_trans _ _ _ _
      (beeu_reduction_and_store_correct st sp' r₀.X0.toBitVec o0 o1 o2 o3 R_frame
        h_sp'_align (hst_core.1.trans h_sp) hst_x14 h_lt h_mem_st) ?_
    rintro ⟨mid, pc1⟩ ⟨hpc1, h_mid_x0, _, h_mid_x29, w0, w1, w2, w3, h_mid_val, h_mid_mem⟩
    dsimp only at hpc1 h_mid_x0 h_mid_x29 h_mid_val h_mid_mem
    subst hpc1
    have h_mid_mem' : mid.dmem =⋆
        BeeuStackFrame r₀ sp' ⋆ (Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R) := by
      have h1 : mid.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R :=
        sep_5_pull.symm ▸ h_mid_mem
      simpa only [sep_assoc] using h1
    refine eventually_weaken _ _ _ _ ?_
      (beeu_finish_correct mid r₀ (Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)
        h_sp_align (h_mid_x29.trans (hst_core.2.1.trans h_x29)) h_mid_mem')
    rintro fin ⟨hpc2, h_fin_x0, h_fin_sp, h_fin_x30, h_fin_cs, h_fin_mem⟩
    refine .break ⟨hpc2, h_fin_x0.trans h_mid_x0, h_fin_sp, h_fin_x30, h_fin_cs,
      w0, w1, w2, w3, ?_, by simpa only [sep_assoc] using h_fin_mem⟩
    have hY_nn : 0 ≤ beeuY st.regs := val320_nonneg _ _ _ _ _
    have hY_mod_eq : beeuY st.regs % beeuN s.regs = beeuY st.regs :=
      Int.emod_eq_of_lt hY_nn (hst_N ▸ h_lt)
    rw [h_mid_val, hst_N, ← hst_Y_mod, hY_mod_eq]

private theorem beeu_loop_end_to_return_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s : MachineData) (r₀ : Reg64s) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
    (h_sp_align : r₀.SP.toBitVec % 16#64 = 0#64)
    (h_sp : s.regs.SP = UInt64.ofBitVec (r₀.SP.toBitVec + 18446744073709551504#64))
    (h_x29 : s.regs.X29 = UInt64.ofBitVec (r₀.SP.toBitVec + 18446744073709551504#64))
    (h_n_pos : 0 < beeuN s.regs)
    (h_mem : s.dmem =⋆
      BeeuStackFrame r₀ (r₀.SP.toBitVec + 18446744073709551504#64) ⋆
      Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R) :
    Eventually (step1 beeuExec)
      (fun st =>
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
        st.data.regs.SP = r₀.SP ∧
        st.data.regs.X30 = r₀.X30 ∧
        CalleeSavedEq st.data.regs r₀ ∧
        if beeuA s.regs = 1 then
          st.data.regs.X0 = 1 ∧
          ∃ w0 w1 w2 w3 : UInt64,
            val256 w0 w1 w2 w3 = beeuN s.regs - (beeuY s.regs % beeuN s.regs) ∧
            (st.data.dmem =⋆
              BeeuStackFrame r₀ sp' ⋆
              Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)
        else
          st.data.regs.X0 = 0 ∧
          (st.data.dmem =⋆
            BeeuStackFrame r₀ sp' ⋆
            Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R))
      ⟨s, beeuExec.addrOf 122⟩ := by
  refine eventually_trans _ _ _ _ (beeu_loop_end_correct s) ?_
  rintro ⟨mid, pc1⟩ ⟨hdmem1, hcore1, hY1, h_branch⟩
  dsimp only at hdmem1 hcore1 hY1 h_branch
  have hN1 := beeuN_of_core hcore1
  have hY_eq := beeuY_of_pres hY1
  by_cases hA : beeuA s.regs = 1
  · simp only [hA, ↓reduceIte] at h_branch ⊢
    rcases h_branch with ⟨hpc1, h_mid_x14⟩
    subst hpc1
    refine eventually_weaken _ _ _ _ ?_
      (beeu_reduction_to_return_correct mid r₀ o0 o1 o2 o3 R h_sp_align
        (hcore1.1.trans h_sp) (hcore1.2.1.trans h_x29) h_mid_x14
        (hN1.symm ▸ h_n_pos) (hdmem1.symm ▸ h_mem))
    rintro fin ⟨hpc, hx0, hsp', hx30', hcs', w0, w1, w2, w3, hval, hmem'⟩
    rw [hN1, hY_eq] at hval
    exact ⟨hpc, hsp', hx30', hcs', hx0, w0, w1, w2, w3, hval, hmem'⟩
  · simp only [hA, ↓reduceIte] at h_branch ⊢
    subst h_branch
    have h_mem_mid : mid.dmem =⋆
        BeeuStackFrame r₀ (r₀.SP.toBitVec + 18446744073709551504#64) ⋆
        (Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R) := by
      rw [hdmem1]; simpa only [sep_assoc] using h_mem
    refine eventually_weaken _ _ _ _ ?_
      (beeu_epilogue_err_correct mid r₀ (Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R)
        h_sp_align (hcore1.2.1.trans h_x29) h_mem_mid)
    rintro fin ⟨hpc, hx0, hsp', hx30', hcs', hmem'⟩
    exact ⟨hpc, hsp', hx30', hcs', hx0, by simpa only [sep_assoc] using hmem'⟩

/-- End-to-end functional correctness of BoringSSL's `beeu_mod_inverse_vartime`:
    given a 16-byte-aligned stack with 112 bytes of frame space, 32-byte input buffers `a_bs`
    at `x1` and odd modulus `n_bs` at `x2` with `0 ≤ a ≤ n`, and a 32-byte output buffer at `x0`,
    `beeu_mod_inverse_vartime` terminates and returns to `x30` with `sp` and all callee-saved
    registers (`x19..x29`) restored, and:
    - if `gcd a n = 1`, returns `x0 = 1` and writes 256-bit `out` (`0 < out ≤ n`) to the output
      buffer such that `(a * out) % n = 1 % n` (the modular inverse of `a` modulo `n`),
    - otherwise returns `x0 = 0` with the output buffer unchanged. -/
theorem beeu_mod_inverse_vartime_correct [WellFormedLayout beeu_mod_inverse_vartime]
    (s₀ : MachineData) (stack a_bs n_bs : List UInt8) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
    (h_sp_align : s₀.regs.SP.toBitVec % 16#64 = 0#64)
    (h_stack_len : stack.length = 112)
    (h_a_len : a_bs.length = 32)
    (h_n_len : n_bs.length = 32)
    (h_a_le : Int.ofBytes a_bs ≤ Int.ofBytes n_bs)
    (h_n_pos : 0 < Int.ofBytes n_bs)
    (h_n_odd : Int.ofBytes n_bs % 2 = 1)
    (h_mem : s₀.dmem =⋆
      Eq (stack.At (s₀.regs.SP.toBitVec + 18446744073709551504#64)) ⋆
      Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
      Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆
      Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R) :
    Eventually (step1 beeu_mod_inverse_vartime.toExecutable)
      (fun st =>
        let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
        let a := Int.ofBytes a_bs
        let n := Int.ofBytes n_bs
        st.pc = Int64.ofInt s₀.regs.X30.toBitVec.toInt ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.X30 = s₀.regs.X30 ∧
        CalleeSavedEq st.data.regs s₀.regs ∧
        if Int.gcd a n = 1 then
          st.data.regs.X0 = 1 ∧
          ∃ w0 w1 w2 w3 : UInt64,
            0 < val256 w0 w1 w2 w3 ∧
            val256 w0 w1 w2 w3 ≤ n ∧
            (a * val256 w0 w1 w2 w3) % n = 1 % n ∧
            (st.data.dmem =⋆
              BeeuStackFrame s₀.regs sp' ⋆
              Words256At w0 w1 w2 w3 s₀.regs.X0.toBitVec ⋆
              Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆
              Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R)
        else
          st.data.regs.X0 = 0 ∧
          (st.data.dmem =⋆
            BeeuStackFrame s₀.regs sp' ⋆
            Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
            Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆
            Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R))
      ⟨s₀, lbl "beeu_mod_inverse_vartime"⟩ := by
  rw [lbl_entry]
  let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
  let a := Int.ofBytes a_bs
  let n := Int.ofBytes n_bs
  have h_a_nonneg : 0 ≤ a := Int.ofBytes_ge_zero a_bs
  have h_mem_pro : s₀.dmem =⋆
      Eq (stack.At sp') ⋆
      Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆
      Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆
      (Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R) := by
    have heq : (Eq (stack.At sp') ⋆ Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
        Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆ Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R) =
        (Eq (stack.At sp') ⋆ Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆
        Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆
        (Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R)) := by ac_rfl
    exact heq ▸ h_mem
  refine eventually_trans _ _ _ _
    (beeu_prologue_correct s₀ stack a_bs n_bs
      (Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R)
      h_sp_align h_stack_len h_a_len h_n_len h_mem_pro) ?_
  rintro ⟨st1, pc1⟩ ⟨hpc1, h1_sp, h1_x29, h1_B, h1_A, h1_N, h1_X, h1_Y, h1_mem⟩
  dsimp only at hpc1 h1_sp h1_x29 h1_B h1_A h1_N h1_X h1_Y h1_mem
  subst hpc1
  have h1_I : BeeuInv a (beeuN st1.regs) 0 0 (beeuB st1.regs) (beeuA st1.regs)
      (beeuX st1.regs) (beeuY st1.regs) := by
    rw [h1_B, h1_A, h1_N, h1_X, h1_Y]
    refine ⟨h_n_odd, Int.gcd_comm _ _, h_a_nonneg, h_a_le, h_n_pos, Int.le_refl _, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · change (a * 1 - a) % n = 0; simp
    · change (a * 0 + n) % n = 0; simp
    · simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul]; exact h_a_le
    · simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul]; exact Int.le_refl _
    · rw [beeuBound_zero]; omega
    · intro _; rw [beeuBound_zero]; omega
    · rw [beeuBound_zero]; omega
    · intro _; rw [beeuBound_zero]; omega
  refine eventually_trans _ _ _ _ (beeu_loop_correct st1 a h1_I) ?_
  rintro ⟨st2, pc2⟩ ⟨hpc2, h2_dmem, h2_core, _, _, h2_Y_inv, h2_gcd⟩
  dsimp only at hpc2 h2_dmem h2_core h2_Y_inv h2_gcd
  subst hpc2
  have h2_N := beeuN_of_core h2_core
  rw [h1_N] at h2_gcd
  have h2_sp_eq : st2.regs.SP = UInt64.ofBitVec sp' :=
    UInt64.eq_of_toBitVec_eq (by rw [h2_core.1]; exact h1_sp)
  have h2_x29_eq : st2.regs.X29 = UInt64.ofBitVec sp' :=
    UInt64.eq_of_toBitVec_eq (by rw [h2_core.2.1]; exact h1_x29)
  let R_in : DataMem → Prop :=
    Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆ Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R
  have h2_mem : st2.dmem =⋆
      BeeuStackFrame s₀.regs sp' ⋆
      Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R_in := by
    rw [h2_dmem]
    dsimp only [R_in]
    have heq : (BeeuStackFrame s₀.regs sp' ⋆
        Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆ Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆
        (Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R)) =
        (BeeuStackFrame s₀.regs sp' ⋆
        Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
        (Eq (a_bs.At s₀.regs.X1.toBitVec) ⋆ Eq (n_bs.At s₀.regs.X2.toBitVec) ⋆ R)) := by ac_rfl
    exact heq ▸ h1_mem
  refine eventually_weaken _ _ _ _ ?_
    (beeu_loop_end_to_return_correct st2 s₀.regs o0 o1 o2 o3 R_in
      h_sp_align h2_sp_eq h2_x29_eq (by rw [h2_N, h1_N]; exact h_n_pos) h2_mem)
  rintro fin ⟨hpc_fin, h_fin_sp, h_fin_x30, h_fin_cs, h_fin_branch⟩
  refine ⟨hpc_fin, h_fin_sp, h_fin_x30, h_fin_cs, ?_⟩
  by_cases hg : Int.gcd (Int.ofBytes a_bs) (Int.ofBytes n_bs) = 1
  · simp only [hg, ↓reduceIte]
    have hA1 : beeuA st2.regs = 1 := h2_gcd.mpr hg
    simp only [hA1, ↓reduceIte] at h_fin_branch
    rcases h_fin_branch with ⟨h_x0, w0, w1, w2, w3, h_val, h_mem'⟩
    have h_inv1 : (a * beeuY st2.regs + 1) % n = 0 := by
      rw [hA1, h1_N] at h2_Y_inv; exact h2_Y_inv
    have h_val_n : val256 w0 w1 w2 w3 = n - (beeuY st2.regs % n) := by
      rw [h2_N, h1_N] at h_val; exact h_val
    have ⟨h_out_pos, h_out_le, h_out_inv⟩ :=
      mod_inv_of_beeu_end a (beeuY st2.regs) (val256 w0 w1 w2 w3) n h_n_pos h_inv1 h_val_n
    exact ⟨h_x0, w0, w1, w2, w3, h_out_pos, h_out_le, h_out_inv,
      by dsimp only [R_in] at h_mem'; simpa only [sep_assoc] using h_mem'⟩
  · simp only [hg, ↓reduceIte]
    have hA1 : ¬ beeuA st2.regs = 1 := fun h => hg (h2_gcd.mp h)
    simp only [hA1, ↓reduceIte] at h_fin_branch
    rcases h_fin_branch with ⟨h_x0, h_mem'⟩
    exact ⟨h_x0, by dsimp only [R_in] at h_mem'; simpa only [sep_assoc] using h_mem'⟩

end Examples.P256Beeu
