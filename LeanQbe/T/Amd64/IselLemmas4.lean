module

public import LeanQbe.T.Amd64.IselLemmas3
import Kraken.X64.Parser

/-!
# x64 Scalar `GprTarget` Proofs — Part 4 (`T8`)

Functional correctness (`_root_.Program.wp`) of `opDiv`, `opAddc`, `opSubb`, and `opMulw`,
plus additional `ParserChecks` against `Kraken.X64.Parser`.
(Top-level `supportsScalarOp` 1-for-1, `x64Gpr_op_spec`, and `x64GprSpec` follow.)
-/

set_option autoImplicit false

namespace LeanQbe.T.Amd64

open LeanQbe.T

section ParserChecks
open Kraken.X64.Parser

example : ⸨prog| negb %r10b ⸩ = [ins8 (.neg (.reg (b8 .r10)))] := rfl
example : ⸨prog| sbbl $1, %eax ⸩ = [ins32 (.sbb (.reg (d .rax)) (.imm (.int64 1)))] := rfl
example : ⸨prog| adcxq %r11, %rax ⸩ = [ins (.adcx (q .rax) (.reg (q .r11)))] := rfl
example : ⸨prog| adoxl %r11d, %eax ⸩ = [ins32 (.adox (d .rax) (.reg (d .r11)))] := rfl
example : ⸨prog| mull %r11d ⸩ = [ins32 (.mul (.reg (d .r11)))] := rfl
example : ⸨prog| imull %r11d ⸩ = [ins32 (.imul1 (.reg (d .r11)))] := rfl
example : ⸨prog| divq %r11 ⸩ = [ins (.div (.reg (q .r11)))] := rfl
example : ⸨prog| idivl %r11d ⸩ = [ins32 (.idiv (.reg (d .r11)))] := rfl
example : ⸨prog| seto %al; movzbl %al, %eax ⸩ = setccMove .rax .o := rfl

end ParserChecks

@[expose] public section

/-! ## 1. BitVec / Integer Arithmetic Helpers for `div`, `adc`, `sbb`, and `mulw` -/

private theorem sshiftRight_last_eq {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.sshiftRight (w - 1) = if x.msb then BitVec.allOnes w else 0#w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  cases hi2 : decide (w - 1 + i < w)
  · have hge : ¬ (w - 1 + i < w) := by simp only [decide_eq_false_iff_not] at hi2; exact hi2
    cases x.msb <;> simp [hge, hi]
  · have hi0 : i = 0 := by simp only [decide_eq_true_eq] at hi2; omega
    subst hi0; have hm : x.msb = x.getLsbD (w - 1) := BitVec.msb_eq_getLsbD_last x
    simp only [Nat.add_zero, show w - 1 < w by omega, ↓reduceIte, ← hm]
    cases x.msb <;> simp [hi, show ¬ (w ≤ 0) by omega]

theorem concat_sshiftRight_toInt {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ((x.sshiftRight (w - 1)) ++ x).toInt = x.toInt := by
  have hext : (x.sshiftRight (w - 1)) ++ x = x.signExtend (w + w) := by
    rw [sshiftRight_last_eq hw x]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    change ((if x.msb then BitVec.allOnes w else 0#w) ++ x).getLsbD j =
      (x.signExtend (w + w)).getLsbD j
    rw [BitVec.getLsbD_append, BitVec.getLsbD_signExtend]
    simp only [hj, decide_true, Bool.true_and]
    split
    · next h => simp [h]
    · next h =>
      have hjsub : j - w < w := by omega
      cases x.msb <;> simp [hjsub]
  rw [hext, BitVec.toInt_signExtend_of_le (by omega)]

theorem sdiv_bounds {n : Nat} (hn : 1 < n) (a b : BitVec n)
    (hdef : LeanQbe.T.sdivDefined a b = true) :
    b ≠ 0#n ∧
    (-(2 ^ (n - 1) : Int) ≤ a.toInt.tdiv b.toInt ∧ a.toInt.tdiv b.toInt < (2 ^ (n - 1) : Int)) ∧
    (-(2 ^ (n - 1) : Int) ≤ a.toInt.tmod b.toInt ∧ a.toInt.tmod b.toInt < (2 ^ (n - 1) : Int)) := by
  have hb0 : b ≠ 0#n := by intro hb; subst hb; simp [LeanQbe.T.sdivDefined] at hdef
  have hnotmin : ¬ (a = BitVec.intMin n ∧ b = BitVec.allOnes n) := by
    intro ⟨ha, hb⟩; subst ha hb; simp [LeanQbe.T.sdivDefined] at hdef
  have hcast : ((2 ^ (n - 1) : Nat) : Int) = (2 ^ (n - 1) : Int) := by norm_cast
  have ha_ge : -((2 ^ (n - 1) : Nat) : Int) ≤ a.toInt := by rw [hcast]; simpa using BitVec.le_toInt a
  have ha_lt : a.toInt < ((2 ^ (n - 1) : Nat) : Int) := by rw [hcast]; exact BitVec.toInt_lt
  have hb_ge : -((2 ^ (n - 1) : Nat) : Int) ≤ b.toInt := by rw [hcast]; simpa using BitVec.le_toInt b
  have hb_lt : b.toInt < ((2 ^ (n - 1) : Nat) : Int) := by rw [hcast]; exact BitVec.toInt_lt
  have hb_ne0 : b.toInt ≠ 0 := fun h => hb0 (BitVec.toInt_inj.1 (by simpa using h))
  have hq_range : -(2 ^ (n - 1) : Int) ≤ a.toInt.tdiv b.toInt ∧ a.toInt.tdiv b.toInt < (2 ^ (n - 1) : Int) := by
    rw [← hcast]
    by_cases hneg1 : b.toInt = -1
    · have hb_ones : b = BitVec.allOnes n := BitVec.toInt_inj.1 (by simp [BitVec.toInt_allOnes, show 0 < n by omega, hneg1])
      have ha_nmin : a.toInt ≠ -((2 ^ (n - 1) : Nat) : Int) := fun ha_min => hnotmin ⟨BitVec.toInt_inj.1 (by
        rw [BitVec.toInt_intMin, ha_min, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega)), hcast]), hb_ones⟩
      rw [hneg1, Int.tdiv_neg, Int.tdiv_one]; omega
    · by_cases hpos1 : b.toInt = 1
      · rw [hpos1, Int.tdiv_one]; exact ⟨ha_ge, ha_lt⟩
      · have hq_nat : (a.toInt.tdiv b.toInt).natAbs ≤ 2 ^ (n - 1) / 2 := by
          rw [Int.natAbs_tdiv]; exact Nat.le_trans (Nat.div_le_div_left (by omega) (by decide)) (Nat.div_le_div_right (by omega))
        have hq_lt : ((a.toInt.tdiv b.toInt).natAbs : Int) < ((2 ^ (n - 1) : Nat) : Int) :=
          Int.ofNat_lt.mpr (Nat.lt_of_le_of_lt hq_nat (Nat.div_lt_self (Nat.pow_pos (by decide)) (by decide)))
        omega
  have hr_nat : ((a.toInt.tmod b.toInt).natAbs : Int) < ((2 ^ (n - 1) : Nat) : Int) := Int.ofNat_lt.mpr (by
    rw [Int.natAbs_tmod]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Int.natAbs_pos.2 hb_ne0)) (by omega))
  exact ⟨hb0, hq_range, by rw [← hcast]; omega⟩

theorem setWidth_ofInt_le {m n : Nat} (hmn : m ≤ n) (z : Int) :
    (BitVec.ofInt n z).setWidth m = BitVec.ofInt m z := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have hdvd : ((2 ^ m : Nat) : Int) ∣ ((2 ^ n : Nat) : Int) := by exact_mod_cast Nat.pow_dvd_pow 2 hmn
  have hposn : ((2 ^ n : Nat) : Int) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))
  have hposm : ((2 ^ m : Nat) : Int) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))
  rw [← Int.ofNat_inj]
  have hmod1 : (((z % ((2 ^ n : Nat) : Int)).toNat % 2 ^ m : Nat) : Int) =
      ((z % ((2 ^ n : Nat) : Int)).toNat : Int) % ((2 ^ m : Nat) : Int) := by exact_mod_cast rfl
  rw [hmod1, Int.toNat_of_nonneg (Int.emod_nonneg _ hposn), Int.toNat_of_nonneg (Int.emod_nonneg _ hposm)]
  exact Int.emod_emod_of_dvd _ hdvd

theorem cf_adc_eq {n : Nat} (a b : BitVec n) (c : Bool) :
    ((a + b + BitVec.ofNat n c.toNat).unsigned != a.unsigned + b.unsigned + (c.toNat : Int)) =
      decide (2 ^ n ≤ a.toNat + b.toNat + c.toNat) := by
  simp only [BitVec.unsigned, BitVec.toNat_add, BitVec.toNat_ofNat]
  have ha := a.isLt; have hb := b.isLt; have hc1 : c.toNat ≤ 1 := by cases c <;> decide
  by_cases hn0 : n = 0
  · subst hn0; cases c <;> simp [show a.toNat = 0 by omega, show b.toNat = 0 by omega]
  · have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow hn0 2
    rw [Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ n)]
    by_cases hge : 2 ^ n ≤ a.toNat + b.toNat + c.toNat
    · have hm : (a.toNat + b.toNat + c.toNat) % 2 ^ n = a.toNat + b.toNat + c.toNat - 2 ^ n := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      rw [hm, decide_eq_true hge, bne_iff_ne]; omega
    · rw [Nat.mod_eq_of_lt (by omega : a.toNat + b.toNat + c.toNat < 2 ^ n), decide_eq_false hge, bne_eq_false_iff_eq]; omega

theorem cf_sbb_eq {n : Nat} (a b : BitVec n) (c : Bool) :
    ((a - b - BitVec.ofNat n c.toNat).unsigned != a.unsigned - b.unsigned - (c.toNat : Int)) =
      decide (a.toNat < b.toNat + c.toNat) := by
  by_cases hn0 : n = 0
  · subst hn0; have : a = 0#0 := Subsingleton.elim _ _; have : b = 0#0 := Subsingleton.elim _ _; subst_vars; cases c <;> decide
  · let d : BitVec n := BitVec.ofNat n c.toNat; let v : BitVec n := a - b - d
    have hsum : v + (b + d) = a := by dsimp [v]; rw [BitVec.add_comm b d, ← BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.sub_add_cancel]
    have hpow : 2 ≤ 2 ^ n := Nat.le_self_pow hn0 2
    have hcn : c.toNat ≤ 1 := by cases c <;> simp
    have hdn : d.toNat = c.toNat := by dsimp [d]; simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hmod : (v.toNat + b.toNat + d.toNat) % 2 ^ n = a.toNat := by simpa [BitVec.toNat_add, Nat.add_assoc] using congrArg BitVec.toNat hsum
    have hvlt := v.isLt; have hblt := b.isLt; have halt := a.isLt
    by_cases hlt : a.toNat < b.toNat + c.toNat
    · have hne : v.unsigned ≠ a.unsigned - b.unsigned - (c.toNat : Int) := by
        change (v.toNat : Int) ≠ (a.toNat : Int) - b.toNat - c.toNat; omega
      simp only [hlt, decide_true, bne_iff_ne]; exact hne
    · rcases Nat.lt_or_ge (v.toNat + b.toNat + d.toNat) (2 ^ n) with h2 | hge'
      · have hmod2 : v.toNat + b.toNat + d.toNat = a.toNat := (Nat.mod_eq_of_lt h2).symm.trans hmod
        have hval : v.unsigned = a.unsigned - b.toNat - (c.toNat : Int) := by
          change (v.toNat : Int) = (a.toNat : Int) - b.toNat - c.toNat; omega
        simp only [hlt, decide_false, bne_eq_false_iff_eq]; exact hval
      · have hsum_eq : v.toNat + b.toNat + d.toNat - 2 ^ n = a.toNat :=
          ((Nat.mod_eq_sub_mod hge').trans (Nat.mod_eq_of_lt (by omega))).symm.trans hmod
        omega

theorem umulw_hi {n : Nat} (a b : BitVec n) :
    BitVec.ofInt n ((a.unsigned * b.unsigned) >>> n) = BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n) := by
  have hun : a.unsigned * b.unsigned = ↑(a.toNat * b.toNat) := rfl
  rw [hun]
  apply BitVec.eq_of_toNat_eq
  have hsh : ((↑(a.toNat * b.toNat) : Int) >>> n) = ↑(a.toNat * b.toNat / 2 ^ n) := by
    rw [Int.shiftRight_eq_div_pow]; norm_cast
  rw [hsh]
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  exact_mod_cast (rfl : ((a.toNat * b.toNat / 2 ^ n : Nat) : Int) % ((2 ^ n : Nat) : Int) =
    ↑(a.toNat * b.toNat / 2 ^ n % 2 ^ n))

theorem umulw_lo {n : Nat} (a b : BitVec n) :
    BitVec.ofInt n (a.unsigned * b.unsigned) = a * b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.unsigned, BitVec.toNat_ofInt, BitVec.toNat_mul]
  exact_mod_cast (rfl : ((a.toNat * b.toNat : Nat) : Int) % ((2 ^ n : Nat) : Int) =
    ↑((a.toNat * b.toNat) % 2 ^ n))

theorem imul1_low_W (w : Width) (hw : w = .W32 ∨ w = .W64) (a b : BitVec w.bits) :
    (BitVec.ofInt (w.bits * 2) (a.toInt * b.toInt)).take w.bits = a * b ∧
    ((BitVec.ofInt (w.bits * 2) (a.toInt * b.toInt)).drop w.bits).setWidth w.bits =
      (BitVec.ofInt (w.bits + w.bits) (a.toInt * b.toInt)).extractLsb' w.bits w.bits := by
  have hlo : (BitVec.ofInt (w.bits * 2) (a.toInt * b.toInt)).take w.bits = a * b := by
    have hmul : a * b = BitVec.ofInt w.bits (a.toInt * b.toInt) := by
      have := BitVec.ofInt_mul (n := w.bits) a.toInt b.toInt
      rw [BitVec.ofInt_toInt, BitVec.ofInt_toInt] at this; exact this.symm
    have htake : (BitVec.ofInt (w.bits * 2) (a.toInt * b.toInt)).take w.bits =
        (BitVec.ofInt (w.bits * 2) (a.toInt * b.toInt)).setWidth w.bits := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.take, BitVec.toNat_setWidth]
    rw [hmul, htake, setWidth_ofInt_le (by rcases hw with rfl | rfl <;> decide)]
  refine ⟨hlo, ?_⟩
  rcases hw with rfl | rfl <;> exact BitVec.setWidth_eq _

/-! ## 2. `opDiv_spec` (`udiv`/`sdiv`/`urem`/`srem` at `[8, 16, 32, 64]`) -/

private theorem fallsTo_divCore (w : Width) (hw : w = .W32 ∨ w = .W64) (isSigned : Bool) (s : MachineData)
    (va vb : BitVec w.bits) (hrax : (s.regs.get64 .rax).setWidth w.bits = va) (hr11 : (s.regs.get64 .r11).setWidth w.bits = vb)
    (hdef : if isSigned then sdivDefined va vb = true else vb ≠ 0#w.bits) :
    Directive.FallsTo (insW w (if isSigned then .idiv (.reg (regW w .r11)) else .div (.reg (regW w .r11))))
      { s with regs := s.regs.set64 .rdx (if isSigned then ((if va.msb then BitVec.allOnes w.bits else 0#w.bits).setWidth 64) else 0#64) }
      (fun s' => ∃ rax' rdx' status', rax'.setWidth w.bits = (if isSigned then va.sdiv vb else va / vb) ∧
        rdx'.setWidth w.bits = (if isSigned then va.srem vb else va % vb) ∧
        s' = { s with regs := (s.regs.set64 .rax rax').set64 .rdx rdx', status := status' }) := by
  intro _ _ _ _ _ hk
  have hr11_rdx : ((s.regs.set64 .rdx (if isSigned then (if va.msb then BitVec.allOnes w.bits else 0#w.bits).setWidth 64 else 0#64)).get64 .r11).setWidth w.bits = vb := by
    rw [Reg64s.get64_set64_of_ne _ .rdx .r11 _ (by decide), hr11]
  have hrax_rdx : ((s.regs.set64 .rdx (if isSigned then (if va.msb then BitVec.allOnes w.bits else 0#w.bits).setWidth 64 else 0#64)).get64 .rax).setWidth w.bits = va := by
    rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide), hrax]
  cases isSigned
  · simp only [Bool.false_eq_true, ↓reduceIte] at hr11_rdx hrax_rdx
    have hlo : (0#w.bits ++ va).toNat = va.toNat := by simp
    have hq_ok : BitVec.ofNat w.bits (va.toNat / vb.toNat) = va / vb := BitVec.eq_of_toNat_eq (by simp [BitVec.udiv_def])
    have hr_ok : BitVec.ofNat w.bits (va.toNat % vb.toNat) = va % vb := BitVec.eq_of_toNat_eq (by simp [BitVec.umod_def])
    have hbnz_beq : (vb == 0) = false := beq_eq_false_iff_ne.2 hdef
    have hqlt : ¬ (2 ^ w.bits ≤ va.toNat / vb.toNat) := Nat.not_le.2 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) va.isLt)
    rcases hw with rfl | rfl
    · dsimp only [Width.bits] at hlo hqlt hbnz_beq hr11_rdx hrax_rdx hq_ok hr_ok
      simp only [insW, regW, Width.bits, t_step_simp, show (Width.W32 == .W8) = false by decide,
        Bool.false_eq_true, ↓reduceIte, hr11_rdx, hrax_rdx, Reg64s.get64_set64_same,
        BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_zero, hbnz_beq, hlo, hqlt, Effects.All]
      intro st; refine hk _ ⟨(BitVec.ofNat 32 (va.toNat / vb.toNat)).setWidth 64, (BitVec.ofNat 32 (va.toNat % vb.toNat)).setWidth 64, st,
        by simp [hq_ok, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)],
        by simp [hr_ok, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)], ?_⟩
      simp only [Reg64s.set64_set64_comm _ .rdx .rax _ _ (by decide), Reg64s.set64_set64_same]
    · dsimp only [Width.bits] at hlo hqlt hbnz_beq hr11_rdx hrax_rdx hq_ok hr_ok; rw [BitVec.setWidth_eq] at hr11_rdx hrax_rdx
      simp only [insW, regW, Width.bits, t_step_simp, show (Width.W64 == .W8) = false by decide,
        Bool.false_eq_true, ↓reduceIte, hr11_rdx, hrax_rdx, Reg64s.get64_set64_same, hbnz_beq, hlo, hqlt, Effects.All]
      intro st; refine hk _ ⟨BitVec.ofNat 64 (va.toNat / vb.toNat), BitVec.ofNat 64 (va.toNat % vb.toNat), st, by simp [hq_ok], by simp [hr_ok], ?_⟩
      simp only [Reg64s.set64_set64_comm _ .rdx .rax _ _ (by decide), Reg64s.set64_set64_same]
  · simp only [↓reduceIte] at hr11_rdx hrax_rdx; have hwpos : 0 < w.bits := width_bits_pos w
    obtain ⟨hb0, ⟨hq_ge, hq_lt⟩, _⟩ := sdiv_bounds (by rcases hw with rfl | rfl <;> decide) va vb hdef
    have hn_eq : (((if va.msb then BitVec.allOnes w.bits else 0#w.bits).setWidth 64).setWidth w.bits ++ va).toInt = va.toInt := by
      rw [setWidth_64_setWidth, ← sshiftRight_last_eq hwpos va]; exact concat_sshiftRight_toInt hwpos va
    have hq_ok : BitVec.ofInt w.bits (va.toInt.tdiv vb.toInt) = va.sdiv vb := BitVec.eq_of_toInt_eq ((BitVec.toInt_ofInt _).trans (BitVec.toInt_sdiv _ _).symm)
    have hr_ok : BitVec.ofInt w.bits (va.toInt.tmod vb.toInt) = va.srem vb := by rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]
    have hguard : (vb == 0 || decide (va.toInt.tdiv vb.toInt < -2 ^ (w.bits - 1)) || decide (2 ^ (w.bits - 1) ≤ va.toInt.tdiv vb.toInt)) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not, Int.not_lt, Int.not_le]; exact ⟨⟨hb0, hq_ge⟩, hq_lt⟩
    rcases hw with rfl | rfl
    · dsimp only [Width.bits] at hguard hr11_rdx hrax_rdx hn_eq hq_ok hr_ok
      simp only [insW, regW, Width.bits, t_step_simp, ↓reduceIte, show (Width.W32 == .W8) = false by decide,
        Bool.false_eq_true, hr11_rdx, hrax_rdx, Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth, hn_eq, hguard, Effects.All]
      intro st; refine hk _ ⟨(BitVec.ofInt 32 (va.toInt.tdiv vb.toInt)).setWidth 64, (BitVec.ofInt 32 (va.toInt.tmod vb.toInt)).setWidth 64, st,
        by simp [hq_ok, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)],
        by simp [hr_ok, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)], ?_⟩
      simp only [Reg64s.set64_set64_comm _ .rdx .rax _ _ (by decide), Reg64s.set64_set64_same]
    · dsimp only [Width.bits] at hguard hr11_rdx hrax_rdx hn_eq hq_ok hr_ok; rw [BitVec.setWidth_eq] at hr11_rdx hrax_rdx hn_eq
      simp only [insW, regW, Width.bits, t_step_simp, ↓reduceIte, show (Width.W64 == .W8) = false by decide,
        Bool.false_eq_true, hr11_rdx, hrax_rdx, Reg64s.get64_set64_same, hn_eq, hguard, Effects.All]
      intro st; refine hk _ ⟨BitVec.ofInt 64 (va.toInt.tdiv vb.toInt), BitVec.ofInt 64 (va.toInt.tmod vb.toInt), st, by simp [hq_ok], by simp [hr_ok], ?_⟩
      simp only [Reg64s.set64_set64_comm _ .rdx .rax _ _ (by decide), Reg64s.set64_set64_same]

private def divExt32 (w : Width) (isSigned : Bool) (v : BitVec w.bits) : BitVec 32 :=
  if isSigned then v.signExtend 32 else v.setWidth 32

private def divArgExt (w : Width) (isSigned : Bool) (t : Reg64) : PArg Reg64 RegMm CondCode (.bits w.bits) → Option Directive
  | .gpr r => match w with
    | .W8 => some (ins32 (if isSigned then .movsx (.reg (d t)) (.reg (b8 r)) else .movzx (.reg (d t)) (.reg (b8 r))))
    | .W16 => some (ins32 (if isSigned then .movsx (.reg (d t)) (.reg (h16 r)) else .movzx (.reg (d t)) (.reg (h16 r))))
    | .W32 => some (movlD t r) | .W64 => some (movD t r)
  | .imm c => some (moviD t (if isSigned then c.signExtend 64 else c.setWidth 64))
  | .vec _ => none

private def divCoreDirs (w : Width) (isSigned : Bool) : List Directive :=
  if w == .W64 then if isSigned then [movD .rdx .rax, ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63))), ins (.idiv (.reg (q .r11)))]
    else [moviD .rdx 0, ins (.div (.reg (q .r11)))]
  else if isSigned then [movlD .rdx .rax, ins32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31))), ins32 (.idiv (.reg (d .r11)))]
    else [moviD .rdx 0, ins32 (.div (.reg (d .r11)))]

private theorem opDiv_eq_parts (w : Width) (isSigned isRem : Bool)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) :
    opDiv w isSigned isRem pa pb rd =
      (if rd == .r10 || rd == .r11 then none else do
         let da ← divArgExt w isSigned .r10 pa; let db ← divArgExt w isSigned .r11 pb
         let core := divCoreDirs w isSigned; let res : Reg64 := if isRem then .rdx else .rax
         let seq := if rd == .rax then [da, db, movD .rax .r10, movD .r10 .rdx] ++ core ++ [movD .rax res, movD .rdx .r10]
           else if rd == .rdx then [da, db, movD .rdx .rax, movD .rax .r10, movD .r10 .rdx] ++ core ++ [movD .rdx res, movD .rax .r10]
           else [da, db, movD rd .rax, movD .rax .r10, movD .r10 .rdx] ++ core ++ [movD .r11 res, movD .rdx .r10, movD .rax rd, movD rd .r11]
         some (seq, maskAll)) := by
  cases w <;> cases pa <;> cases pb <;> simp only [opDiv, divArgExt, divCoreDirs] <;> rfl

private theorem fallsTo_divArgExt (w : Width) (isSigned : Bool) (s0 : MachineData) (t : Reg64)
    (p : PArg Reg64 RegMm CondCode (.bits w.bits)) (v : BitVec w.bits) {d0 : Directive}
    (hd : divArgExt w isSigned t p = some d0) (hp0 : x64Mach.PArgHolds s0 (.bits w.bits) p v) :
    Directive.FallsTo d0 s0 (fun s' => ∃ rv : BitVec 64,
      (if w == .W64 then rv = v.setWidth 64 else rv.setWidth 32 = divExt32 w isSigned v) ∧ s' = { s0 with regs := s0.regs.set64 t rv }) := by
  have h32 : ∀ x : BitVec 32, (x.setWidth 64).setWidth 32 = x := fun x => setWidth_64_setWidth .W32 x
  cases p with
  | vec _ => cases w <;> simp [divArgExt] at hd
  | imm c0 =>
    rcases hp0 with rfl; simp only [divArgExt, Option.some.injEq] at hd; subst hd
    intro _ p0 next0 jmp0 P0 hk; refine fallsTo_moviD s0 t _ p0 next0 jmp0 P0 fun s' rfl => hk _ ⟨_, ?_, rfl⟩
    cases w <;> cases isSigned <;> dsimp only [divExt32] <;> first
      | exact BitVec.setWidth_setWidth_of_le c0 (by decide) | exact setWidth_signExtend_of_le (by decide) (by decide) c0
      | rfl | exact BitVec.eq_of_toInt_eq (BitVec.toInt_signExtend_of_le (by decide : 64 ≤ 64))
  | gpr rs =>
    have hrs := (GprHolds.bits_iff w _ _).1 hp0; intro _ p0 next0 jmp0 P0 hk
    cases w <;> cases isSigned <;> simp only [divArgExt, Option.some.injEq] at hd <;> subst hd <;> simp only [Width.bits] at hrs
    · refine fallsTo_movzx8 s0 t rs p0 next0 jmp0 P0 fun _ rfl => hk _ ⟨_, by simp [divExt32, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), hrs], rfl⟩
    · refine fallsTo_movsx8 .W32 (.inl rfl) s0 t rs p0 next0 jmp0 P0 fun _ rfl => hk _ ⟨_, by simp [divExt32, h32, hrs], rfl⟩
    · refine fallsTo_movzx16 s0 t rs p0 next0 jmp0 P0 fun _ rfl => hk _ ⟨_, by simp [divExt32, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), hrs], rfl⟩
    · refine fallsTo_movsx16 .W32 (.inl rfl) s0 t rs p0 next0 jmp0 P0 fun _ rfl => hk _ ⟨_, by simp [divExt32, h32, hrs], rfl⟩
    · refine fallsTo_movlD s0 t rs p0 next0 jmp0 P0 fun _ rfl => hk _ ⟨_, by simp [divExt32, h32, hrs, BitVec.setWidth_eq], rfl⟩
    · refine fallsTo_movlD s0 t rs p0 next0 jmp0 P0 fun _ rfl => hk _ ⟨_, ?_, rfl⟩
      simp only [show (Width.W32 == .W64) = false by decide, Bool.false_eq_true, ↓reduceIte, divExt32, BitVec.zeroExtend_eq_setWidth, h32, hrs]
      exact (BitVec.eq_of_toInt_eq (BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 32))).symm
    · refine fallsTo_movD s0 t rs p0 next0 jmp0 P0 fun _ rfl => hk _ ⟨_, by simpa [BitVec.setWidth_eq] using hrs, rfl⟩
    · refine fallsTo_movD s0 t rs p0 next0 jmp0 P0 fun _ rfl => hk _ ⟨_, by simpa [BitVec.setWidth_eq] using hrs, rfl⟩

private theorem divExt32_sub32_props (w : Width) (hw816 : w = .W8 ∨ w = .W16) (isSigned isRem : Bool) (va vb : BitVec w.bits)
    (hdef : if isSigned then sdivDefined va vb = true else vb ≠ 0#w.bits) :
    (if isSigned then sdivDefined (divExt32 w isSigned va) (divExt32 w isSigned vb) = true else divExt32 w isSigned vb ≠ 0#32) ∧
    (if isSigned then (if isRem then (divExt32 w isSigned va).srem (divExt32 w isSigned vb) else (divExt32 w isSigned va).sdiv (divExt32 w isSigned vb))
     else (if isRem then divExt32 w isSigned va % divExt32 w isSigned vb else divExt32 w isSigned va / divExt32 w isSigned vb)).setWidth w.bits =
      (if isSigned then (if isRem then va.srem vb else va.sdiv vb) else (if isRem then va % vb else va / vb)) := by
  have hwle : w.bits ≤ 32 := by rcases hw816 with rfl | rfl <;> decide
  have hpow : 2 ^ w.bits < 2 ^ 32 := by rcases hw816 with rfl | rfl <;> decide
  have ha := Nat.lt_trans va.isLt hpow; have hb := Nat.lt_trans vb.isLt hpow
  cases isSigned
  · refine ⟨fun h => hdef (BitVec.eq_of_toNat_eq (by
      have h1 := congrArg BitVec.toNat h; simp only [divExt32, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_zero] at h1
      rwa [Nat.mod_eq_of_lt hb] at h1)), ?_⟩
    have hva32 : va.toNat % 2 ^ 32 = va.toNat := Nat.mod_eq_of_lt ha; have hvb32 : vb.toNat % 2 ^ 32 = vb.toNat := Nat.mod_eq_of_lt hb
    cases isRem <;> dsimp only [divExt32] <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> apply BitVec.eq_of_toNat_eq
    · simp only [BitVec.toNat_setWidth, BitVec.udiv_def, BitVec.toNat_ofNat, hva32, hvb32]
      rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) va.isLt) hpow), Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) va.isLt)]
    · have hrem_lt : va.toNat % vb.toNat < 2 ^ w.bits :=
        Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => hdef (BitVec.eq_of_toNat_eq (by simpa using h)))) vb.isLt
      simp only [BitVec.toNat_setWidth, BitVec.umod_def, BitVec.toNat_ofNat, hva32, hvb32]
      rw [Nat.mod_eq_of_lt (Nat.lt_trans hrem_lt hpow), Nat.mod_eq_of_lt hrem_lt]
  · simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hdef
    refine ⟨?_, ?_⟩
    · simp only [divExt32, ↓reduceIte, sdivDefined, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      refine ⟨fun h => hdef.1 (BitVec.toInt_inj.1 (by have := congrArg BitVec.toInt h; rw [BitVec.toInt_signExtend_of_le hwle] at this; simpa using this)),
        Or.inl fun h1 => ?_⟩
      have h2 := congrArg BitVec.toInt h1; rw [BitVec.toInt_signExtend_of_le hwle, show (BitVec.intMin 32).toInt = -2 ^ 31 by decide] at h2
      have ha2 := BitVec.le_toInt va; rcases hw816 with rfl | rfl <;> dsimp only [Width.bits] at ha2 <;> omega
    · cases isRem <;> dsimp only [divExt32] <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · have h1 := BitVec.eq_of_toInt_eq ((BitVec.toInt_ofInt _).trans (BitVec.toInt_sdiv (va.signExtend 32) (vb.signExtend 32)).symm)
        rw [← h1, BitVec.toInt_signExtend_of_le hwle, BitVec.toInt_signExtend_of_le hwle, setWidth_ofInt_le hwle]
        exact BitVec.eq_of_toInt_eq ((BitVec.toInt_ofInt _).trans (BitVec.toInt_sdiv va vb).symm)
      · have h1 : (va.signExtend 32).srem (vb.signExtend 32) = BitVec.ofInt 32 ((va.signExtend 32).toInt.tmod (vb.signExtend 32).toInt) := by
          rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]
        rw [h1, BitVec.toInt_signExtend_of_le hwle, BitVec.toInt_signExtend_of_le hwle, setWidth_ofInt_le hwle, ← BitVec.toInt_srem, BitVec.ofInt_toInt]

private theorem divExt32_props (w : Width) (hw : w ≠ .W64) (isSigned isRem : Bool) (va vb : BitVec w.bits)
    (hdef : if isSigned then sdivDefined va vb = true else vb ≠ 0#w.bits) :
    (if isSigned then sdivDefined (divExt32 w isSigned va) (divExt32 w isSigned vb) = true else divExt32 w isSigned vb ≠ 0#32) ∧
    (if isSigned then (if isRem then (divExt32 w isSigned va).srem (divExt32 w isSigned vb) else (divExt32 w isSigned va).sdiv (divExt32 w isSigned vb))
     else (if isRem then divExt32 w isSigned va % divExt32 w isSigned vb else divExt32 w isSigned va / divExt32 w isSigned vb)).setWidth w.bits =
      (if isSigned then (if isRem then va.srem vb else va.sdiv vb) else (if isRem then va % vb else va / vb)) := by
  cases w
  · exact divExt32_sub32_props .W8 (.inl rfl) isSigned isRem va vb hdef
  · exact divExt32_sub32_props .W16 (.inr rfl) isSigned isRem va vb hdef
  · cases isSigned <;> refine ⟨by simpa [divExt32] using hdef, by cases isRem <;> simp [divExt32, BitVec.setWidth_eq]⟩
  · exact absurd rfl hw

private theorem fallsTo_sarSign (w : Width) (hw : w = .W32 ∨ w = .W64) (st0 : MachineData) (x : BitVec w.bits)
    (hrax0 : (st0.regs.get64 .rax).setWidth w.bits = x)
    (hrdx0 : st0.regs.get64 .rdx = if w == .W64 then st0.regs.get64 .rax else (((st0.regs.get64 .rax).setWidth 32).setWidth 64)) :
    Directive.FallsTo (insW w (.sar (.reg (regW w .rdx)) (.imm8 (.int64 (Int64.ofNat (w.bits - 1))))))
      st0 (fun s' => s' = { st0 with regs := st0.regs.set64 .rdx ((if x.msb then BitVec.allOnes w.bits else 0#w.bits).setWidth 64), status := s'.status }) := by
  intro _ _ _ _ _ hk; have hbit := sshiftRight_last_eq (width_bits_pos w) x
  rcases hw with rfl | rfl
  · have h32 : (x.setWidth 64).setWidth 32 = x := setWidth_64_setWidth .W32 x
    simp only [insW, regW, Width.bits, show (Width.W32 == .W64) = false by decide, Bool.false_eq_true, ↓reduceIte] at hrdx0 hrax0 hbit ⊢
    simp only [t_step_simp, hrdx0, BitVec.zeroExtend_eq_setWidth, h32, hrax0,
      show (((Int64.ofNat 31).toBitVec.take 8).toNat &&& 31) = 31 by decide,
      show (31 == 0) = false by decide, show (31 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte, Effects.All, Reg64s.set]
    intro _ _; rw [hbit]; exact hk _ rfl
  · have hrax64 : st0.regs.get64 .rax = x := by simp [Width.bits] at hrax0 ⊢; exact hrax0
    simp only [insW, regW, Width.bits, show (Width.W64 == .W64) = true by decide, ↓reduceIte] at hrdx0 hbit ⊢
    simp only [t_step_simp, hrdx0, hrax64,
      show (((Int64.ofNat 63).toBitVec.take 8).toNat &&& 63) = 63 by decide,
      show (63 == 0) = false by decide, show (63 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte, Effects.All, Reg64s.set]
    intro _ _; rw [hbit]; refine hk _ ?_; simp only [Width.bits, BitVec.setWidth_eq]

private theorem wp_divCoreRun [Host] {E : Int64 → MachineData → Prop} (w : Width) (isSigned isRem : Bool)
    (va vb : BitVec w.bits) (hdef : if isSigned then sdivDefined va vb = true else vb ≠ 0#w.bits) (st0 : MachineData)
    (ha_ok : if (w == .W64) = true then st0.regs.get64 .rax = va.setWidth 64 else (st0.regs.get64 .rax).setWidth 32 = divExt32 w isSigned va)
    (hb_ok : if (w == .W64) = true then st0.regs.get64 .r11 = vb.setWidth 64 else (st0.regs.get64 .r11).setWidth 32 = divExt32 w isSigned vb) :
    _root_.Program.wp (divCoreDirs w isSigned) (fun s' => ∃ rax' rdx' status',
      (if isRem then rdx' else rax').setWidth w.bits =
        (if isSigned then (if isRem then va.srem vb else va.sdiv vb) else (if isRem then va % vb else va / vb)) ∧
      s' = { st0 with regs := (st0.regs.set64 .rax rax').set64 .rdx rdx', status := status' }) E st0 := by
  by_cases hw64 : w = .W64
  · subst w; simp only [show (Width.W64 == .W64) = true by decide, ↓reduceIte, BitVec.setWidth_eq] at ha_ok hb_ok
    have hra : (st0.regs.get64 .rax).setWidth 64 = va := by rw [ha_ok, BitVec.setWidth_eq]
    have hrb : (st0.regs.get64 .r11).setWidth 64 = vb := by rw [hb_ok, BitVec.setWidth_eq]
    cases isSigned
    · simp only [divCoreDirs, show (Width.W64 == .W64) = true by decide, Bool.false_eq_true, ↓reduceIte]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD st0 .rdx 0)) ?_; rintro s1 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_divCore .W64 (.inr rfl) false st0 va vb hra hrb hdef)) ?_
      rintro s' ⟨a', b', st', ha, hb, hs'⟩; exact ⟨a', b', st', by cases isRem <;> simpa using (by assumption), hs'⟩
    · simp only [divCoreDirs, show (Width.W64 == .W64) = true by decide, ↓reduceIte]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD st0 .rdx .rax)) ?_; rintro s1 rfl
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_sarSign .W64 (.inr rfl) _ va
        (by rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide)]; exact hra) (by rw [Reg64s.get64_set64_same]; rfl))) ?_
      rintro s2 hs2
      have hs2' : s2 = { st0 with regs := st0.regs.set64 .rdx ((if va.msb then BitVec.allOnes 64 else 0#64).setWidth 64), status := s2.status } := by rw [hs2]; congr 1
      rw [hs2']; refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_divCore .W64 (.inr rfl) true { st0 with status := s2.status } va vb hra hrb hdef)) ?_
      rintro s' ⟨a', b', st', ha, hb, hs'⟩; exact ⟨a', b', st', by cases isRem <;> simpa using (by assumption), hs'⟩
  · have hbeq : (w == .W64) = false := by cases w <;> first | exact absurd rfl hw64 | decide
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at ha_ok hb_ok
    obtain ⟨hdef32, hres32⟩ := divExt32_props w hw64 isSigned isRem va vb hdef
    have hwle : w.bits ≤ 32 := by cases w <;> first | exact absurd rfl hw64 | decide
    have fin32 : ∀ (isS : Bool) (hds : if isS then sdivDefined (divExt32 w isSigned va) (divExt32 w isSigned vb) = true else divExt32 w isSigned vb ≠ 0#32)
        (stS : StatusFlags),
        _root_.Program.wp [insW .W32 (if isS then .idiv (.reg (regW .W32 .r11)) else .div (.reg (regW .W32 .r11)))]
          (fun s' => ∃ rax' rdx' status', (if isRem then rdx' else rax').setWidth 32 =
            (if isS then (if isRem then (divExt32 w isSigned va).srem (divExt32 w isSigned vb) else (divExt32 w isSigned va).sdiv (divExt32 w isSigned vb))
             else (if isRem then divExt32 w isSigned va % divExt32 w isSigned vb else divExt32 w isSigned va / divExt32 w isSigned vb)) ∧
            s' = { st0 with regs := (st0.regs.set64 .rax rax').set64 .rdx rdx', status := status' })
          E { st0 with regs := st0.regs.set64 .rdx (if isS then ((if (divExt32 w isSigned va).msb then BitVec.allOnes 32 else 0#32).setWidth 64) else 0#64), status := stS } := by
      intro isS hds stS; refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_divCore .W32 (.inl rfl) isS { st0 with status := stS }
        (divExt32 w isSigned va) (divExt32 w isSigned vb) ha_ok hb_ok hds)) ?_
      rintro s' ⟨a', b', st', ha, hb, hs'⟩; exact ⟨a', b', st', by cases isRem <;> simpa using (by assumption), hs'⟩
    cases isSigned
    · simp only [divCoreDirs, hbeq, Bool.false_eq_true, ↓reduceIte]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD st0 .rdx 0)) ?_; rintro s1 rfl
      exact Program.wp.mono (fin32 false hdef32 st0.status) fun s' ⟨a', b', st', hfin, hs'⟩ => ⟨a', b', st', by rw [← BitVec.setWidth_setWidth_of_le _ hwle, hfin]; exact hres32, hs'⟩
    · simp only [divCoreDirs, hbeq, Bool.false_eq_true, ↓reduceIte]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movlD st0 .rdx .rax)) ?_; rintro s1 rfl
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_sarSign .W32 (.inl rfl) _ (divExt32 w true va)
        (by rw [Reg64s.get64_set64_of_ne _ .rdx .rax _ (by decide)]; exact ha_ok) (by rw [Reg64s.get64_set64_same]; simp))) ?_
      rintro s2 hs2
      have hs2' : s2 = { st0 with regs := st0.regs.set64 .rdx ((if (divExt32 w true va).msb then BitVec.allOnes 32 else 0#32).setWidth 64), status := s2.status } := by rw [hs2]; congr 1
      rw [hs2']; exact Program.wp.mono (fin32 true hdef32 s2.status) fun s' ⟨a', b', st', hfin, hs'⟩ => ⟨a', b', st', by rw [← BitVec.setWidth_setWidth_of_le _ hwle, hfin]; exact hres32, hs'⟩

theorem opDiv_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (isSigned isRem : Bool)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec w.bits} {s : MachineData} (hc : opDiv w isSigned isRem pa pb rd = some (c, clob))
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb)
    (hdef : if isSigned then sdivDefined va vb = true else vb ≠ 0#w.bits) :
    _root_.Program.wp c (OpPost1 (.bits w.bits) rd
      (if isSigned then (if isRem then va.srem vb else va.sdiv vb) else (if isRem then va % vb else va / vb)) clob s) E s := by
  have hrd_sc := ne_of_not_mem_x64Scratch hrd; rw [opDiv_eq_parts] at hc
  have hguard : (rd == .r10 || rd == .r11) = false := by rcases hrd_sc with ⟨h1, h2⟩; cases rd <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl
  rw [hguard] at hc; simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind] at hc
  rcases Option.bind_eq_some_iff.mp hc with ⟨da, hda, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨db, hdb, h2⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨hseq, rfl⟩; rw [← hseq]
  have hp_prefix : _root_.Program.wp [da, db] (fun s2 => ∃ rv10 rv11 : BitVec 64,
      (if (w == .W64) = true then rv10 = va.setWidth 64 else rv10.setWidth 32 = divExt32 w isSigned va) ∧
      (if (w == .W64) = true then rv11 = vb.setWidth 64 else rv11.setWidth 32 = divExt32 w isSigned vb) ∧
      s2 = { s with regs := (s.regs.set64 .r10 rv10).set64 .r11 rv11 }) E s := by
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_divArgExt w isSigned s .r10 pa va hda hpa)) ?_; rintro s1 ⟨rv10, h10, rfl⟩
    have hpb1 : x64Mach.PArgHolds { s with regs := s.regs.set64 .r10 rv10 } (.bits w.bits) pb vb := by
      cases pb with | vec _ | imm _ => exact hpb | gpr rx =>
        have hrx := (ne_of_not_mem_x64Scratch (hargs rx (by simp [PArg.gprs]))).1
        dsimp only [Machine.PArgHolds, Machine.getGpr, x64Mach] at hpb ⊢; rw [Reg64s.get64_set64_of_ne _ .r10 rx _ hrx.symm]; exact hpb
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_divArgExt w isSigned _ .r11 pb vb hdb hpb1)) ?_
    rintro s2 ⟨rv11, h11, rfl⟩; exact ⟨rv10, rv11, h10, h11, rfl⟩
  have hprefix_cons : ∀ (xs : List Directive),
      (∀ rv10 rv11 : BitVec 64, (if (w == .W64) = true then rv10 = va.setWidth 64 else rv10.setWidth 32 = divExt32 w isSigned va) →
        (if (w == .W64) = true then rv11 = vb.setWidth 64 else rv11.setWidth 32 = divExt32 w isSigned vb) →
        _root_.Program.wp xs (OpPost1 (.bits w.bits) rd (if isSigned then (if isRem then va.srem vb else va.sdiv vb)
          else (if isRem then va % vb else va / vb)) maskAll s) E { s with regs := (s.regs.set64 .r10 rv10).set64 .r11 rv11 }) →
      _root_.Program.wp (da :: db :: xs) (OpPost1 (.bits w.bits) rd
        (if isSigned then (if isRem then va.srem vb else va.sdiv vb) else (if isRem then va % vb else va / vb)) maskAll s) E s := fun xs hxs => by
    change _root_.Program.wp ([da, db] ++ xs) _ E s
    exact Program.wp.append hp_prefix fun _ ⟨rv10, rv11, h10, h11, hs2⟩ => hs2 ▸ hxs rv10 rv11 h10 h11
  have movStep : ∀ (a b : Reg64) (st : MachineData) (rest : List Directive) (Q : MachineData → Prop),
      _root_.Program.wp rest Q E { st with regs := st.regs.set64 a (st.regs.get64 b) } → _root_.Program.wp (movD a b :: rest) Q E st := fun a b st rest Q h =>
    Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD st a b)) fun _ hr => hr ▸ h
  clear hc h1 hda hdb hseq hargs hpa hpb hp_prefix
  by_cases hrax : rd = .rax
  rotate_left
  by_cases hrdx : rd = .rdx
  all_goals
    first
    | (subst hrax; simp only [show (Reg64.rax == .rax) = true by decide, ↓reduceIte])
    | (subst hrdx; simp only [show (Reg64.rdx == .rax) = false by decide, show (Reg64.rdx == .rdx) = true by decide, Bool.false_eq_true, ↓reduceIte])
    | (have hrax_f : (rd == .rax) = false := by cases rd <;> first | exact absurd rfl hrax | rfl
       have hrdx_f : (rd == .rdx) = false := by cases rd <;> first | exact absurd rfl hrdx | rfl
       simp only [hrax_f, hrdx_f, Bool.false_eq_true, ↓reduceIte])
    refine hprefix_cons _ fun rv10 rv11 h10 h11 => ?_; clear hprefix_cons
    repeat' refine movStep _ _ _ _ _ ?_
    have h10' : ∀ x : BitVec 64, rv10 = x → (if (w == .W64) = true then x = va.setWidth 64 else x.setWidth 32 = divExt32 w isSigned va) := fun _ e => e ▸ h10
    have h11' : ∀ x : BitVec 64, rv11 = x → (if (w == .W64) = true then x = vb.setWidth 64 else x.setWidth 32 = divExt32 w isSigned vb) := fun _ e => e ▸ h11
    refine Program.wp.append (wp_divCoreRun w isSigned isRem va vb hdef _ ?_ ?_) ?_
    · exact h10' _ (by simp only [Reg64s.get64_set64]; grind)
    · exact h11' _ (by simp only [Reg64s.get64_set64]; grind)
    rintro _ ⟨rax', rdx', st', hres, rfl⟩
    cases isRem <;> simp only [↓reduceIte, Bool.false_eq_true] at hres ⊢
    all_goals
      repeat' refine movStep _ _ _ _ _ ?_
      clear movStep
      refine _root_.Program.wp_nil ⟨(GprHolds.bits_iff w _ _).2 ?_, rfl, x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_maskAll _ _)⟩
      · dsimp only [Machine.getGpr, x64Mach]; exact (congrArg (BitVec.setWidth w.bits) (by simp only [Reg64s.get64_set64]; grind)).trans hres
      · simp only [List.mem_cons, List.mem_nil_iff, not_or, x64Scratch] at hr
        dsimp only [Machine.getGpr, x64Mach]; simp only [Reg64s.get64_set64]; grind

/-! ## 3. `OpPost2`, `opAddc_spec`, and `opSubb_spec` -/

abbrev OpPost2 (t0 t1 : Ty) (pd0 : PDst Reg64 RegMm CondCode t0) (pd1 : PDst Reg64 RegMm CondCode t1)
    (v0 : Val t0) (v1 : Val t1) (clob : FlagMask) (s s' : MachineData) : Prop :=
  x64Mach.PDstHolds s' t0 pd0 v0 ∧ x64Mach.PDstHolds s' t1 pd1 v1 ∧ s'.dmem = s.dmem ∧
    x64Mach.Frame x64CondReads s s' (@tupDstGprs Reg64 RegMm CondCode [t0, t1] (pd0, pd1, ()) ++ x64Scratch) [] clob

theorem opPost2_fallsTo {t0 t1 : Ty} {pd0 : PDst Reg64 RegMm CondCode t0} {pd1 : PDst Reg64 RegMm CondCode t1}
    {c : List Directive} {clob : FlagMask} {s : MachineData} {v0 : Val t0} {v1 : Val t1} {P : Tup Val [t0, t1] → Prop}
    (hp : P (v0, v1, ())) (hwp : ∀ [Host] (E : Int64 → MachineData → Prop), _root_.Program.wp c (OpPost2 t0 t1 pd0 pd1 v0 v1 clob s) E s)
    {h : Host} {k : Nat} {post : MachineState → Prop} :
    x64Mach.FallsTo x64Gpr.condReads h k c (@tupDstGprs Reg64 RegMm CondCode [t0, t1] (pd0, pd1, ()) ++ x64Scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') (pd0, pd1, ()) rvs) ∧ x64Mach.mem s' = x64Mach.mem s) post := by
  refine x64_fallsTo_of_wp fun {_} _ => Program.wp.mono (hwp _) ?_
  rintro s' ⟨h0, h1, hmem, hfr⟩; exact ⟨⟨⟨(v0, v1, ()), hp, TRel.cons h0 (TRel.cons h1 .nil)⟩, hmem⟩, hfr⟩

private def x64SetupCf : PArg Reg64 RegMm CondCode .bool → Option (List Directive)
  | .flag .c => some []
  | .flag cc => some [ins8 (.setcc cc (.reg (b8 .r10))), ins8 (.neg (.reg (b8 .r10)))]
  | .gpr rc => some [ins8 (.mov (.reg (b8 .r10)) (.reg (b8 rc))), ins8 (.neg (.reg (b8 .r10)))]
  | .imm false => some [ins32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
  | .imm true => some [moviD .r10 1, ins8 (.neg (.reg (b8 .r10)))]
  | .vec _ => none

private def x64CarryOutSeq (flagCc : CondCode) : PDst Reg64 RegMm CondCode .bool → Option (List Directive)
  | .flag cc => if cc == flagCc then some [] else none
  | .gpr rc => some (setccMove rc flagCc) | .vec _ => none

private def x64AdcFallback (w : Width) (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pc : PArg Reg64 RegMm CondCode .bool)
    (rd : Reg64) (dc : PDst Reg64 RegMm CondCode .bool) : Option (List Directive × FlagMask) := do
  let setupCf ← x64SetupCf pc
  let core ← carryCore w true (fun dst src => insW w (.adc (.reg (regW w dst)) (.reg (regW w src))))
    (fun dst imm => insW w (.adc (.reg (regW w dst)) (immBitsOp w imm))) true pa pb rd
  let tail ← x64CarryOutSeq .c dc; some (setupCf ++ core ++ tail, maskAll)

private def x64DistinctDst (rd : Reg64) : PDst Reg64 RegMm CondCode .bool → Bool
  | .gpr rc => rc != rd | _ => true

private theorem opAddc_eq (w : Width) (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pc : PArg Reg64 RegMm CondCode .bool)
    (rd : Reg64) (dc : PDst Reg64 RegMm CondCode .bool) (vh : VariantHint) :
    opAddc w pa pb pc (.gpr rd) dc vh =
      (if !x64DistinctDst rd dc then none else match vh with
       | .adcx => match pc with
         | .flag .c => do
           let core ← carryCore w true (fun dst src => insW w (.adcx (regW w dst) (.reg (regW w src))))
             (fun dst _ => insW w (.adcx (regW w dst) (.reg (regW w dst)))) false pa pb rd
           let tail ← x64CarryOutSeq .c dc
           some (core ++ tail, maskCF)
         | _ => x64AdcFallback w pa pb pc rd dc
       | .adox => match pc with
         | .flag .o => do
           let core ← carryCore w true (fun dst src => insW w (.adox (regW w dst) (.reg (regW w src))))
             (fun dst _ => insW w (.adox (regW w dst) (.reg (regW w dst)))) false pa pb rd
           let tail ← x64CarryOutSeq .o dc
           some (core ++ tail, maskOF)
         | _ => x64AdcFallback w pa pb pc rd dc
       | _ => x64AdcFallback w pa pb pc rd dc) := by
  unfold opAddc; dsimp +zetaHave only
  cases vh <;> cases pc <;> (try cases ‹Bool›) <;> (try cases ‹CondCode›) <;>
    cases dc <;> simp [x64DistinctDst, x64AdcFallback, x64SetupCf, x64CarryOutSeq]

private theorem opSubb_eq (w : Width) (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pc : PArg Reg64 RegMm CondCode .bool)
    (rd : Reg64) (db : PDst Reg64 RegMm CondCode .bool) :
    opSubb w pa pb pc (.gpr rd) db =
      (if !x64DistinctDst rd db then none else do
         let setupCf ← x64SetupCf pc
         let core ← carryCore w false (fun dst src => insW w (.sbb (.reg (regW w dst)) (.reg (regW w src))))
           (fun dst imm => insW w (.sbb (.reg (regW w dst)) (immBitsOp w imm))) true pa pb rd
         let tail ← x64CarryOutSeq .c db
         some (setupCf ++ core ++ tail, maskAll)) := by
  unfold opSubb; dsimp +zetaHave only
  cases pc <;> (try cases ‹Bool›) <;> (try cases ‹CondCode›) <;>
    cases db <;> (try (rename_i cc; cases cc)) <;> simp [x64DistinctDst, x64SetupCf, x64CarryOutSeq]

private theorem setRegW_eq_st (w : Width) (s : MachineData) (d : Reg64) (v : w.type) (st : StatusFlags) :
    ∃ rv : BitVec 64, rv.setWidth w.bits = v ∧ ({ s with regs := s.regs.set (regW w d) v, status := st } : MachineData) = { s with regs := s.regs.set64 d rv, status := st } := by
  cases w <;> simp only [regW, Reg64s.set]
  · exact ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  · exact ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  · exact ⟨_, by simp [Width.bits], rfl⟩
  · exact ⟨_, rfl, rfl⟩

private theorem pargholds_set64_r10 {s : MachineData} {w : Width} {p : PArg Reg64 RegMm CondCode (.bits w.bits)}
    {v : BitVec w.bits} {rv10 : BitVec 64} {st1 : StatusFlags}
    (hp : x64Mach.PArgHolds s (.bits w.bits) p v) (hg : ∀ r ∈ p.gprs, r ∉ x64Scratch) :
    x64Mach.PArgHolds { s with regs := s.regs.set64 .r10 rv10, status := st1 } (.bits w.bits) p v := by
  cases p with | vec _ | imm _ => exact hp | gpr r =>
    have hr := (ne_of_not_mem_x64Scratch (hg r (by simp [PArg.gprs]))).1
    dsimp only [Machine.PArgHolds, Machine.getGpr, x64Mach] at hp ⊢; rw [Reg64s.get64_set64_of_ne _ .r10 r _ hr.symm]; exact hp

private theorem wp_setupCarryCf [Host] {E : Int64 → MachineData → Prop} {pc : PArg Reg64 RegMm CondCode .bool}
    {vc : Bool} {s : MachineData} {sc : List Directive} (hsc : x64SetupCf pc = some sc) (hpc : x64Mach.PArgHolds s .bool pc vc) :
    _root_.Program.wp sc (fun s' => ∃ rv10 st', st'.cf = vc ∧ s' = { s with regs := s.regs.set64 .r10 rv10, status := st' }) E s := by
  have fallsTo_negb_r10 : ∀ (st : MachineData) (b : Bool), ((st.regs.get64 .r10).setWidth 8 = BitVec.ofNat 8 b.toNat) →
      Directive.FallsTo (ins8 (.neg (.reg (b8 .r10)))) st (fun s' => ∃ rv st', st'.cf = b ∧ s' = { st with regs := st.regs.set64 .r10 rv, status := st' }) := by
    intro st b hr10 _ _ _ _ _ hk; simp only [t_step_simp, hr10, StatusFlags.from_result, Effects.All, Reg64s.set]
    exact hk _ ⟨_, _, by cases b <;> rfl, rfl⟩
  cases pc with
  | vec _ => simp [x64SetupCf] at hsc
  | imm b0 =>
    cases b0 <;> rcases hpc with rfl <;> simp only [x64SetupCf, Option.some.injEq] at hsc <;> subst hsc
    · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_clearFlags s)) ?_; rintro s' ⟨st', rfl, hcf, -⟩; exact ⟨0#64, st', hcf, rfl⟩
    · refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 1)) ?_; rintro s1 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_negb_r10 _ true (by rw [Reg64s.get64_set64_same]; rfl))) ?_
      rintro s2 ⟨rv, st', hcf, rfl⟩; exact ⟨rv, st', hcf, rfl⟩
  | gpr rc =>
    have hrc : (s.regs.get64 rc).setWidth 8 = BitVec.ofNat 8 vc.toNat := hpc
    simp only [x64SetupCf, Option.some.injEq] at hsc; subst hsc
    refine Program.wp.cons (Directive.FallsTo.wp (d := ins8 (.mov (.reg (b8 .r10)) (.reg (b8 rc)))) (s := s)
      (Q := fun s1 => ∃ rv10 : BitVec 64, rv10.setWidth 8 = BitVec.ofNat 8 vc.toNat ∧ s1 = { s with regs := s.regs.set64 .r10 rv10 })
      (by intro _ _ _ _ _ hk; simp only [t_step_simp, hrc, Reg64s.set]; exact hk _ ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩)) ?_
    rintro s1 ⟨rv10, hrv10, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_negb_r10 _ vc (by rw [Reg64s.get64_set64_same, hrv10]))) ?_
    rintro s2 ⟨rv, st', hcf, rfl⟩; exact ⟨rv, st', hcf, rfl⟩
  | flag cc =>
    have hcc : cc.interp s.status = vc := hpc
    cases cc with
    | c => simp only [x64SetupCf, Option.some.injEq] at hsc; subst hsc; exact _root_.Program.wp_nil ⟨s.regs.get64 .r10, s.status, hcc, by congr 1⟩
    | o | no | nc | z | nz | be | a | s | ns | p | np | l | ge | le | g =>
      simp only [x64SetupCf, Option.some.injEq] at hsc; subst hsc
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_setcc s _ .r10)) ?_; rintro s1 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_negb_r10 _ vc (by rw [Reg64s.get64_set64_same, replaceLow_setWidth_le (by decide), hcc]))) ?_
      rintro s2 ⟨rv, st', hcf, rfl⟩; exact ⟨rv, st', hcf, rfl⟩

private theorem wp_carryCore [Host] {E : Int64 → MachineData → Prop} (w : Width) (isComm supportsImm : Bool)
    (mkReg : Reg64 → Reg64 → Directive) (mkImm : Reg64 → BitVec w.bits → Directive)
    (evalRes : BitVec w.bits → BitVec w.bits → Bool → BitVec w.bits) (evalSt : StatusFlags → BitVec w.bits → BitVec w.bits → StatusFlags → Prop)
    (hcomm : isComm = true → ∀ a b c, evalRes a b c = evalRes b a c ∧ ∀ st st', evalSt st a b st' ↔ evalSt st b a st')
    (getFlag : StatusFlags → Bool)
    (hstepReg : ∀ (st0 : MachineData) (d sreg : Reg64) (a b : BitVec w.bits), (st0.regs.get64 d).setWidth w.bits = a → (st0.regs.get64 sreg).setWidth w.bits = b →
      Directive.FallsTo (mkReg d sreg) st0 (fun s' => ∃ rv' st', rv'.setWidth w.bits = evalRes a b (getFlag st0.status) ∧ evalSt st0.status a b st' ∧ s' = { st0 with regs := st0.regs.set64 d rv', status := st' }))
    (hstepImm : supportsImm = true → ∀ (st0 : MachineData) (d : Reg64) (a b : BitVec w.bits), (w != .W64 || fitsImm32 (b.setWidth 64)) = true →
      (st0.regs.get64 d).setWidth w.bits = a → Directive.FallsTo (mkImm d b) st0 (fun s' => ∃ rv' st', rv'.setWidth w.bits = evalRes a b (getFlag st0.status) ∧ evalSt st0.status a b st' ∧ s' = { st0 with regs := st0.regs.set64 d rv', status := st' }))
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {cr : List Directive} {va vb : BitVec w.bits} {s0 s_orig : MachineData}
    (hcr : carryCore w isComm mkReg mkImm supportsImm pa pb rd = some cr) (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s0 (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s0 (.bits w.bits) pb vb)
    (hregs0 : ∀ r, r ∉ x64Scratch → s0.regs.get64 r = s_orig.regs.get64 r) (hm0 : s0.dmem = s_orig.dmem) (hz0 : s0.zmms = s_orig.zmms) :
    _root_.Program.wp cr (fun s' => ∃ rv' st', rv'.setWidth w.bits = evalRes va vb (getFlag s0.status) ∧ evalSt s0.status va vb st' ∧
      (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s_orig.regs.get64 r) ∧ s'.regs.get64 rd = rv' ∧ s'.dmem = s_orig.dmem ∧ s'.zmms = s_orig.zmms ∧ s'.status = st') E s0 := by
  have hrd_sc := ne_of_not_mem_x64Scratch hrd
  have runRegImm : ∀ (s1 : MachineData) (ra : Reg64) (cb xa : BitVec w.bits),
      ra ≠ .r10 → (s1.regs.get64 ra).setWidth w.bits = xa → (∀ r, r ≠ rd → r ∉ x64Scratch → s1.regs.get64 r = s_orig.regs.get64 r) →
      s1.dmem = s_orig.dmem → s1.zmms = s_orig.zmms → s1.status = s0.status →
      _root_.Program.wp (let pre := if ra == rd then [] else [movW w rd ra]
         if supportsImm && (w != .W64 || fitsImm32 (cb.setWidth 64)) then pre ++ [mkImm rd cb] else [moviD .r10 (cb.setWidth 64)] ++ pre ++ [mkReg rd .r10])
        (fun s' => ∃ rv' st', rv'.setWidth w.bits = evalRes xa cb (getFlag s0.status) ∧ evalSt s0.status xa cb st' ∧
          (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s_orig.regs.get64 r) ∧ s'.regs.get64 rd = rv' ∧ s'.dmem = s_orig.dmem ∧ s'.zmms = s_orig.zmms ∧ s'.status = st') E s1 := by
    intro s1 ra cb xa hra_ne10 hra1 hr1 hm1 hz1 hst1
    have hpre_wp : ∀ (sb : MachineData), (sb.regs.get64 ra).setWidth w.bits = xa → (∀ r, r ≠ rd → r ∉ x64Scratch → sb.regs.get64 r = s_orig.regs.get64 r) →
        sb.dmem = s_orig.dmem → sb.zmms = s_orig.zmms → sb.status = s0.status →
        _root_.Program.wp (if ra == rd then [] else [movW w rd ra]) (fun sc => (sc.regs.get64 rd).setWidth w.bits = xa ∧
          (∀ r, r ≠ rd → r ∉ x64Scratch → sc.regs.get64 r = s_orig.regs.get64 r) ∧ sc.regs.get64 .r10 = sb.regs.get64 .r10 ∧ sc.dmem = s_orig.dmem ∧ sc.zmms = s_orig.zmms ∧ sc.status = s0.status) E sb := by
      intro sb hsb hfrb hmb hzb hstb; refine Program.wp.mono (wp_optMovW w sb rd ra hsb) ?_
      rintro sc ⟨hcrd, hne, hmc, hzc, hstc⟩
      exact ⟨hcrd, fun r hrd' hsc' => (hne r hrd').trans (hfrb r hrd' hsc'), hne .r10 hrd_sc.1.symm, hmc.trans hmb, hzc.trans hzb, hstc.trans hstb⟩
    by_cases him : (supportsImm && (w != .W64 || fitsImm32 (cb.setWidth 64))) = true
    · simp only [him, ↓reduceIte]; simp only [Bool.and_eq_true] at him
      refine Program.wp.append (hpre_wp s1 hra1 hr1 hm1 hz1 hst1) ?_; rintro sc ⟨hcrd, hfr, _, hmc, hzc, hstc⟩
      refine Program.wp.mono (Directive.FallsTo.wp (hstepImm him.1 sc rd xa cb him.2 hcrd)) ?_; rintro s' ⟨rv', st', hrv', hest', rfl⟩; rw [hstc] at hrv' hest'
      exact ⟨rv', st', hrv', hest', fun r hr' hsc' => (Reg64s.get64_set64_of_ne _ rd r _ hr'.symm).trans (hfr r hr' hsc'), Reg64s.get64_set64_same .., hmc, hzc, rfl⟩
    · simp only [him, Bool.false_eq_true, ↓reduceIte]
      change _root_.Program.wp (moviD .r10 (cb.setWidth 64) :: ((if ra == rd then [] else [movW w rd ra]) ++ [mkReg rd .r10])) _ E s1
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s1 .r10 (cb.setWidth 64))) ?_; rintro _ rfl
      refine Program.wp.append (hpre_wp _ (by rw [Reg64s.get64_set64_of_ne _ .r10 ra _ hra_ne10.symm, hra1])
        (fun r hrd' hsc' => by rw [Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hsc').1.symm]; exact hr1 r hrd' hsc') hm1 hz1 hst1) ?_
      rintro sc ⟨hcrd, hfr, hr10, hmc, hzc, hstc⟩
      refine Program.wp.mono (Directive.FallsTo.wp (hstepReg sc rd .r10 xa cb hcrd (by rw [hr10, Reg64s.get64_set64_same, setWidth_64_setWidth]))) ?_
      rintro s' ⟨rv', st', hrv', hest', rfl⟩; rw [hstc] at hrv' hest'
      exact ⟨rv', st', hrv', hest', fun r hr' hsc' => (Reg64s.get64_set64_of_ne _ rd r _ hr'.symm).trans (hfr r hr' hsc'), Reg64s.get64_set64_same .., hmc, hzc, rfl⟩
  have runViaR11 : ∀ (s1 : MachineData) (rb : Reg64) (a b : BitVec w.bits),
      (s1.regs.get64 .r11).setWidth w.bits = a → (s1.regs.get64 rb).setWidth w.bits = b →
      (∀ r, r ∉ x64Scratch → s1.regs.get64 r = s_orig.regs.get64 r) → s1.dmem = s_orig.dmem → s1.zmms = s_orig.zmms → s1.status = s0.status →
      _root_.Program.wp [mkReg .r11 rb, movW w rd .r11] (fun s' => ∃ rv' st', rv'.setWidth w.bits = evalRes a b (getFlag s0.status) ∧ evalSt s0.status a b st' ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s_orig.regs.get64 r) ∧ s'.regs.get64 rd = rv' ∧ s'.dmem = s_orig.dmem ∧ s'.zmms = s_orig.zmms ∧ s'.status = st') E s1 := by
    intro s1 rb a b hr11 hrb hfr1 hm1 hz1 hst1
    refine Program.wp.cons (Directive.FallsTo.wp (hstepReg s1 .r11 rb a b hr11 hrb)) ?_; rintro s2 ⟨rv2, st', hrv2, hest', rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ rd .r11)) ?_; rintro _ rfl; rw [hst1] at hrv2 hest'
    exact ⟨_, st', (setWidth_64_setWidth w _).trans hrv2, hest', fun r hr' hsc' => by
      rw [Reg64s.get64_set64_of_ne _ rd r _ hr'.symm, Reg64s.get64_set64_of_ne _ .r11 r _ (ne_of_not_mem_x64Scratch hsc').2.symm, hfr1 r hsc'],
      by rw [Reg64s.get64_set64_same, Reg64s.get64_set64_same], hm1, hz1, rfl⟩
  cases pa with
  | vec _ => simp [carryCore] at hcr
  | imm ca =>
    rcases hpa with rfl; cases pb with
    | vec _ => simp [carryCore] at hcr
    | imm cb =>
      rcases hpb with rfl; unfold carryCore at hcr; simp only [Option.some.injEq] at hcr; subst hcr
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s0 rd (ca.setWidth 64))) ?_; rintro _ rfl
      exact runRegImm _ rd cb ca hrd_sc.1 (by rw [Reg64s.get64_set64_same, setWidth_64_setWidth]) (fun r hr hsc => by rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, hregs0 r hsc]) hm0 hz0 rfl
    | gpr rb =>
      have hrb_sc := ne_of_not_mem_x64Scratch (hargs rb (by simp [PArg.gprs])); have hrb := (GprHolds.bits_iff w _ _).1 hpb; unfold carryCore at hcr; dsimp +zetaHave only at hcr
      by_cases hc : isComm = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at hcr; subst hcr; obtain ⟨heq, hest⟩ := hcomm hc ca vb (getFlag s0.status)
        refine Program.wp.mono (runRegImm s0 rb ca vb hrb_sc.1 hrb (fun r _ hsc => hregs0 r hsc) hm0 hz0 rfl) ?_
        rintro s' ⟨rv', st', hrv', hest', hfr', hrd', hm', hz', hst'⟩; exact ⟨rv', st', hrv'.trans heq.symm, (hest s0.status st').2 hest', hfr', hrd', hm', hz', hst'⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hcr; subst hcr
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s0 .r11 (ca.setWidth 64))) ?_; rintro _ rfl
        exact runViaR11 _ rb ca vb (by rw [Reg64s.get64_set64_same, setWidth_64_setWidth]) (by rw [Reg64s.get64_set64_of_ne _ .r11 rb _ hrb_sc.2.symm, hrb])
          (fun r hsc => by rw [Reg64s.get64_set64_of_ne _ .r11 r _ (ne_of_not_mem_x64Scratch hsc).2.symm, hregs0 r hsc]) hm0 hz0 rfl
  | gpr ra =>
    have hra_sc := ne_of_not_mem_x64Scratch (hargs ra (by simp [PArg.gprs])); have hra := (GprHolds.bits_iff w _ _).1 hpa
    cases pb with
    | vec _ => simp [carryCore] at hcr
    | imm cb => rcases hpb with rfl; unfold carryCore at hcr; simp only [Option.some.injEq] at hcr; subst hcr; exact runRegImm s0 ra cb va hra_sc.1 hra (fun r _ hsc => hregs0 r hsc) hm0 hz0 rfl
    | gpr rb =>
      have hrb_sc := ne_of_not_mem_x64Scratch (hargs rb (by simp [PArg.gprs])); have hrb := (GprHolds.bits_iff w _ _).1 hpb; unfold carryCore at hcr
      by_cases h1 : ra == rd
      · have := (beq_reg64_iff ra rd).1 h1; subst ra; simp only [h1, ↓reduceIte, Option.some.injEq] at hcr; subst hcr
        refine Program.wp.mono (Directive.FallsTo.wp (hstepReg s0 rd rb va vb hra hrb)) ?_; rintro s' ⟨rv', st', hrv', hest', rfl⟩
        exact ⟨rv', st', hrv', hest', fun r hr hsc => by rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, hregs0 r hsc], Reg64s.get64_set64_same .., hm0, hz0, rfl⟩
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hcr
        by_cases h2 : isComm && (rb == rd)
        · simp only [h2, ↓reduceIte, Option.some.injEq] at hcr; subst hcr; simp only [Bool.and_eq_true, beq_reg64_iff] at h2; rcases h2 with ⟨hc, rfl⟩
          obtain ⟨heq, hest⟩ := hcomm hc va vb (getFlag s0.status)
          refine Program.wp.mono (Directive.FallsTo.wp (hstepReg s0 rb ra vb va hrb hra)) ?_; rintro s' ⟨rv', st', hrv', hest', rfl⟩
          exact ⟨rv', st', hrv'.trans heq.symm, (hest s0.status st').2 hest', fun r hr hsc => by rw [Reg64s.get64_set64_of_ne _ rb r _ hr.symm, hregs0 r hsc], Reg64s.get64_set64_same .., hm0, hz0, rfl⟩
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hcr
          by_cases h3 : rb != rd
          · simp only [h3, ↓reduceIte, Option.some.injEq] at hcr; subst hcr; have hrb_rd := (bne_reg64_iff rb rd).1 h3
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW w s0 rd ra)) ?_; rintro _ rfl
            refine Program.wp.mono (Directive.FallsTo.wp (hstepReg _ rd rb va vb (by rw [Reg64s.get64_set64_same, setWidth_64_setWidth, hra])
              (by rw [Reg64s.get64_set64_of_ne _ rd rb _ hrb_rd.symm, hrb]))) ?_; rintro s' ⟨rv', st', hrv', hest', rfl⟩
            exact ⟨rv', st', hrv', hest', fun r hr hsc => by rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, Reg64s.get64_set64_of_ne _ rd r _ hr.symm, hregs0 r hsc],
              Reg64s.get64_set64_same .., hm0, hz0, rfl⟩
          · simp only [h3, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hcr; subst hcr
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW w s0 .r11 ra)) ?_; rintro _ rfl
            exact runViaR11 _ rb va vb (by rw [Reg64s.get64_set64_same, setWidth_64_setWidth, hra]) (by rw [Reg64s.get64_set64_of_ne _ .r11 rb _ hrb_sc.2.symm, hrb])
              (fun r hsc => by rw [Reg64s.get64_set64_of_ne _ .r11 r _ (ne_of_not_mem_x64Scratch hsc).2.symm, hregs0 r hsc]) hm0 hz0 rfl

private theorem wp_coutSeq [Host] {E : Int64 → MachineData → Prop} (w : Width) (flagCc : CondCode)
    {dsum : Reg64} {dc : PDst Reg64 RegMm CondCode .bool} {tl : List Directive} {clob : FlagMask} {vsum : BitVec w.bits} {vc : Bool} {s s_mid : MachineData}
    (htl : x64CarryOutSeq flagCc dc = some tl) (hdist : x64DistinctDst dsum dc = true) (hvsum : (s_mid.regs.get64 dsum).setWidth w.bits = vsum)
    (hfc : flagCc.interp s_mid.status = vc) (hregs : ∀ r, r ≠ dsum → r ∉ x64Scratch → s_mid.regs.get64 r = s.regs.get64 r)
    (hm : s_mid.dmem = s.dmem) (hz : s_mid.zmms = s.zmms) (hup : x64Mach.UpdFlags x64CondReads s s_mid clob) :
    _root_.Program.wp tl (OpPost2 (.bits w.bits) .bool (.gpr dsum) dc vsum vc clob s) E s_mid := by
  cases dc with
  | vec _ => simp [x64CarryOutSeq] at htl
  | flag cc =>
    by_cases heq : cc == flagCc
    · have := (beq_cond_iff cc flagCc).1 heq; subst cc; simp only [x64CarryOutSeq, heq, ↓reduceIte, Option.some.injEq] at htl; subst htl
      exact _root_.Program.wp_nil ⟨(GprHolds.bits_iff w _ _).2 hvsum, hfc, hm,
        x64_frame_of_eq (fun r hr => hregs r (fun h => hr (by subst h; simp [tupDstGprs])) (fun h => hr (by simp [h]))) hz hup⟩
    · simp [x64CarryOutSeq, heq] at htl
  | gpr rc =>
    have hrc_ne : rc ≠ dsum := (bne_reg64_iff rc dsum).1 hdist
    simp only [x64CarryOutSeq, Option.some.injEq] at htl; subst htl
    refine Program.wp.mono (wp_setccMove s_mid rc flagCc) ?_; rintro _ rfl
    refine ⟨(GprHolds.bits_iff w _ _).2 ?_, ?_, hm, x64_frame_of_eq (fun r hr => ?_) hz hup⟩
    · dsimp only [Machine.getGpr]; rw [Reg64s.get64_set64_of_ne _ rc dsum _ hrc_ne, hvsum]
    · simp only [Machine.PDstHolds, GprHolds, Reg64s.get64_set64_same, hfc]; cases vc <;> rfl
    · dsimp only [Machine.getGpr]; rw [Reg64s.get64_set64_of_ne _ rc r _ (fun h => hr (by subst h; simp [tupDstGprs])),
        hregs r (fun h => hr (by subst h; simp [tupDstGprs])) (fun h => hr (by simp [h]))]

private theorem wp_cfCarrySeq [Host] {E : Int64 → MachineData → Prop} (w : Width) (hw : w = .W32 ∨ w = .W64) (isSub : Bool)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {pc : PArg Reg64 RegMm CondCode .bool} {rd : Reg64} {dc : PDst Reg64 RegMm CondCode .bool}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec w.bits} {vc : Bool} {s : MachineData}
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch) (hdist : x64DistinctDst rd dc = true)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) (hpc : x64Mach.PArgHolds s .bool pc vc)
    (hc : (do
      let sc ← x64SetupCf pc
      let cr ← carryCore w (!isSub)
        (fun dst src => insW w (if isSub then .sbb (.reg (regW w dst)) (.reg (regW w src)) else .adc (.reg (regW w dst)) (.reg (regW w src))))
        (fun dst imm => insW w (if isSub then .sbb (.reg (regW w dst)) (immBitsOp w imm) else .adc (.reg (regW w dst)) (immBitsOp w imm))) true pa pb rd
      let tl ← x64CarryOutSeq .c dc
      some (sc ++ cr ++ tl, maskAll)) = some (c, clob)) :
    _root_.Program.wp c (OpPost2 (.bits w.bits) .bool (.gpr rd) dc (if isSub then va - vb - BitVec.ofNat w.bits vc.toNat else va + vb + BitVec.ofNat w.bits vc.toNat)
      (if isSub then decide (va.toNat < vb.toNat + vc.toNat) else decide (2 ^ w.bits ≤ va.toNat + vb.toNat + vc.toNat)) clob s) E s := by
  simp only [Option.bind_eq_bind] at hc
  rcases Option.bind_eq_some_iff.mp hc with ⟨sc, hsc, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨cr, hcr, h2⟩; rcases Option.bind_eq_some_iff.mp h2 with ⟨tl, htl, h3⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h3; rcases h3 with ⟨rfl, rfl⟩; rw [List.append_assoc]
  refine Program.wp.append (wp_setupCarryCf hsc hpc) ?_; rintro s1 ⟨rv10, st1, hcf1, rfl⟩
  have hpa1 := pargholds_set64_r10 hpa (fun r hr => hargs r (List.mem_append.2 (.inl hr))) (rv10 := rv10) (st1 := st1)
  have hpb1 := pargholds_set64_r10 hpb (fun r hr => hargs r (List.mem_append.2 (.inr hr))) (rv10 := rv10) (st1 := st1)
  have hcore := wp_carryCore (E := E) w (!isSub) true
    (fun dst src => insW w (if isSub then .sbb (.reg (regW w dst)) (.reg (regW w src)) else .adc (.reg (regW w dst)) (.reg (regW w src))))
    (fun dst imm => insW w (if isSub then .sbb (.reg (regW w dst)) (immBitsOp w imm) else .adc (.reg (regW w dst)) (immBitsOp w imm)))
    (fun a b c => if isSub then a - b - BitVec.ofNat w.bits c.toNat else a + b + BitVec.ofNat w.bits c.toNat)
    (fun st a b st' => st'.cf = if isSub then decide (a.toNat < b.toNat + st.cf.toNat) else decide (2 ^ w.bits ≤ a.toNat + b.toNat + st.cf.toNat))
    (fun hc a b c => by
      have his : isSub = false := by cases isSub <;> simp_all
      subst his; exact ⟨by simp [BitVec.add_comm a b], fun _ _ => by simp [Nat.add_comm a.toNat b.toNat]⟩) StatusFlags.cf
    (fun st0 d sreg a b hd hs _ _ _ _ _ hk => by
      rcases hw with rfl | rfl <;> cases isSub <;> simp only [insW, Width.bits, Bool.false_eq_true, ↓reduceIte, t_step_simp, hd, hs] <;>
        first
        | (obtain ⟨rv', hrv', heq⟩ := setRegW_eq_st _ st0 d (b + a + BitVec.ofNat _ st0.status.cf.toNat) _
           refine hk _ ⟨rv', _, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [hrv', BitVec.add_comm b a],
             by simp only [Bool.false_eq_true, ↓reduceIte, StatusFlags.from_result]; simpa [BitVec.add_comm a b, Int.add_comm a.unsigned b.unsigned] using cf_adc_eq a b st0.status.cf, heq⟩)
        | (obtain ⟨rv', hrv', heq⟩ := setRegW_eq_st _ st0 d (a - b - BitVec.ofNat _ st0.status.cf.toNat) _
           refine hk _ ⟨rv', _, by simp only [↓reduceIte, hrv'], by simp only [↓reduceIte, StatusFlags.from_result]; exact cf_sbb_eq a b st0.status.cf, heq⟩))
    (fun _ st0 d a b _ hd _ _ _ _ _ hk => by
      rcases hw with rfl | rfl <;> cases isSub <;> simp only [insW, immBitsOp, Width.bits, Bool.false_eq_true, ↓reduceIte, t_step_simp, hd, Int64.toBitVec_ofBitVec] <;>
        rw [truncate_signExtend_64 (by decide)] <;>
        first
        | (obtain ⟨rv', hrv', heq⟩ := setRegW_eq_st _ st0 d (b + a + BitVec.ofNat _ st0.status.cf.toNat) _
           refine hk _ ⟨rv', _, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [hrv', BitVec.add_comm b a],
             by simp only [Bool.false_eq_true, ↓reduceIte, StatusFlags.from_result]; simpa [BitVec.add_comm a b, Int.add_comm a.unsigned b.unsigned] using cf_adc_eq a b st0.status.cf, heq⟩)
        | (obtain ⟨rv', hrv', heq⟩ := setRegW_eq_st _ st0 d (a - b - BitVec.ofNat _ st0.status.cf.toNat) _
           refine hk _ ⟨rv', _, by simp only [↓reduceIte, hrv'], by simp only [↓reduceIte, StatusFlags.from_result]; exact cf_sbb_eq a b st0.status.cf, heq⟩))
    hcr hrd hargs hpa1 hpb1 (fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm) rfl rfl
  refine Program.wp.append hcore ?_; rintro s2 ⟨rv', st2, hrv', hest2, hfr2, hrd2, hm2, hz2, hst2⟩; rw [hcf1] at hrv' hest2
  exact wp_coutSeq w .c htl hdist (by rw [hrd2, hrv']) (by rw [hst2]; exact hest2) hfr2 hm2 hz2 (updFlags_maskAll _ _)

private theorem wp_adx_gen [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {dc : PDst Reg64 RegMm CondCode .bool} {cr tl : List Directive}
    {va vb : BitVec w.bits} {vc : Bool} {s : MachineData} (mkReg : Reg64 → Reg64 → Directive) (mkDummy : Reg64 → BitVec w.bits → Directive)
    (flagCc : CondCode) (getF : StatusFlags → Bool) (updSt : StatusFlags → Bool → StatusFlags) (clob : FlagMask)
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch) (hdist : x64DistinctDst rd dc = true)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) (hpc : getF s.status = vc)
    (hcr : carryCore w true mkReg mkDummy false pa pb rd = some cr) (htl : x64CarryOutSeq flagCc dc = some tl)
    (hstep : ∀ (st0 : MachineData) (d sreg : Reg64) (a b : BitVec w.bits), (st0.regs.get64 d).setWidth w.bits = a → (st0.regs.get64 sreg).setWidth w.bits = b →
      Directive.FallsTo (mkReg d sreg) st0 (fun s' => ∃ rv' st', rv'.setWidth w.bits = a + b + BitVec.ofNat w.bits (getF st0.status).toNat ∧
        st' = updSt st0.status (decide (2 ^ w.bits ≤ a.toNat + b.toNat + (getF st0.status).toNat)) ∧ s' = { st0 with regs := st0.regs.set64 d rv', status := st' }))
    (hgetF : ∀ st b, flagCc.interp (updSt st b) = b) (hupd : ∀ (s0 s1 : MachineData) (b : Bool), s1.status = updSt s0.status b → x64Mach.UpdFlags x64CondReads s0 s1 clob) :
    _root_.Program.wp (cr ++ tl) (OpPost2 (.bits w.bits) .bool (.gpr rd) dc (va + vb + BitVec.ofNat w.bits vc.toNat) (decide (2 ^ w.bits ≤ va.toNat + vb.toNat + vc.toNat)) clob s) E s := by
  have hcore := wp_carryCore (E := E) w true false mkReg mkDummy (fun a b c => a + b + BitVec.ofNat w.bits c.toNat)
    (fun st a b st' => st' = updSt st (decide (2 ^ w.bits ≤ a.toNat + b.toNat + (getF st).toNat)))
    (fun _ a b c => ⟨by rw [BitVec.add_comm a b], fun _ _ => by rw [Nat.add_comm a.toNat b.toNat]⟩) getF hstep (fun h => by cases h)
    hcr hrd hargs hpa hpb (fun _ _ => rfl) rfl rfl
  refine Program.wp.append hcore ?_; rintro s2 ⟨rv', st2, hrv', hest2, hfr2, hrd2, hm2, hz2, hst2⟩; rw [hpc] at hrv' hest2
  exact wp_coutSeq w flagCc htl hdist (by rw [hrd2, hrv']) (by rw [hst2, hest2, hgetF]) hfr2 hm2 hz2 (hupd s s2 _ (hst2.trans hest2))

private theorem wp_adx [Host] {E : Int64 → MachineData → Prop} (w : Width) (hw : w = .W32 ∨ w = .W64) (isCf : Bool)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {dc : PDst Reg64 RegMm CondCode .bool} {cr tl : List Directive}
    {va vb : BitVec w.bits} {vc : Bool} {s : MachineData} (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hdist : x64DistinctDst rd dc = true) (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb)
    (hpc : (if isCf then s.status.cf else s.status.of) = vc)
    (hcr : carryCore w true (fun dst src => insW w (if isCf then .adcx (regW w dst) (.reg (regW w src)) else .adox (regW w dst) (.reg (regW w src))))
      (fun dst _ => insW w (if isCf then .adcx (regW w dst) (.reg (regW w dst)) else .adox (regW w dst) (.reg (regW w dst)))) false pa pb rd = some cr)
    (htl : x64CarryOutSeq (if isCf then .c else .o) dc = some tl) :
    _root_.Program.wp (cr ++ tl) (OpPost2 (.bits w.bits) .bool (.gpr rd) dc (va + vb + BitVec.ofNat w.bits vc.toNat) (decide (2 ^ w.bits ≤ va.toNat + vb.toNat + vc.toNat))
      (if isCf then maskCF else maskOF) s) E s := by
  cases isCf <;> simp only [Bool.false_eq_true, ↓reduceIte] at hpc hcr htl ⊢ <;> first
    | refine wp_adx_gen w _ _ .o StatusFlags.of (fun st b => { st with of := b }) maskOF hrd hargs hdist hpa hpb hpc hcr htl ?_ (fun _ _ => rfl) (fun _ _ _ h => updFlags_maskOF (by rw [h]) (by rw [h]) (by rw [h]) (by rw [h]))
    | refine wp_adx_gen w _ _ .c StatusFlags.cf (fun st b => { st with cf := b }) maskCF hrd hargs hdist hpa hpb hpc hcr htl ?_ (fun _ _ => rfl) (fun _ _ _ h => updFlags_maskCF (by rw [h]) (by rw [h]) (by rw [h]) (by rw [h]))
  all_goals
    intro st0 d sreg a b hd hs _ _ _ _ _ hk; rcases hw with rfl | rfl <;> simp only [insW, regW, Width.bits] at hd hs ⊢
    · simp only [t_step_simp, Reg.interp, Reg64s.get_low32, hd, hs, Reg64s.set, BitVec.zeroExtend_eq_setWidth]
      refine hk _ ⟨_, _, by rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, BitVec.add_comm b a],
        by simp only [← cf_adc_eq a b _, BitVec.add_comm a b, Int.add_comm a.unsigned b.unsigned], rfl⟩
    · simp only [t_step_simp, Reg.interp, Reg64s.get_low64]; rw [← BitVec.setWidth_eq (st0.regs.get64 d), ← BitVec.setWidth_eq (st0.regs.get64 sreg), hd, hs]
      refine hk _ ⟨_, _, by rw [BitVec.setWidth_eq, BitVec.add_comm b a], by simp only [← cf_adc_eq a b _, BitVec.add_comm a b, Int.add_comm a.unsigned b.unsigned], rfl⟩

theorem opAddc_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (hw : w = .W32 ∨ w = .W64)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {pc : PArg Reg64 RegMm CondCode .bool} {dsum : PDst Reg64 RegMm CondCode (.bits w.bits)}
    {dc : PDst Reg64 RegMm CondCode .bool} {vh : VariantHint} {c : List Directive} {clob : FlagMask} {va vb : BitVec w.bits} {vc : Bool} {s : MachineData}
    (hc : opAddc w pa pb pc dsum dc vh = some (c, clob)) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs ++ pc.gprs, r ∉ x64Scratch)
    (hdst : ∀ r ∈ @tupDstGprs Reg64 RegMm CondCode [.bits w.bits, .bool] (dsum, dc, ()), r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) (hpc : x64Mach.PArgHolds s .bool pc vc) :
    _root_.Program.wp c (OpPost2 (.bits w.bits) .bool dsum dc (va + vb + BitVec.ofNat w.bits vc.toNat) (decide (2 ^ w.bits ≤ va.toNat + vb.toNat + vc.toNat)) clob s) E s := by
  cases dsum with
  | vec _ => simp [opAddc] at hc
  | gpr rd =>
    have hrd : rd ∉ x64Scratch := hdst rd (by simp [tupDstGprs])
    have hargs_ab : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch := fun r hr => hargs r (List.mem_append.2 (.inl hr))
    rw [opAddc_eq] at hc
    by_cases hdist : x64DistinctDst rd dc = true
    · simp only [hdist, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
      have fb : x64AdcFallback w pa pb pc rd dc = some (c, clob) → _root_.Program.wp c (OpPost2 (.bits w.bits) .bool (.gpr rd) dc
          (va + vb + BitVec.ofNat w.bits vc.toNat) (decide (2 ^ w.bits ≤ va.toNat + vb.toNat + vc.toNat)) clob s) E s :=
        fun h => wp_cfCarrySeq w hw false hrd hargs_ab hdist hpa hpb hpc h
      cases vh <;> cases pc <;> try exact fb hc
      · rename_i cc; cases cc <;> try exact fb hc
        simp only [Option.bind_eq_bind] at hc; rcases Option.bind_eq_some_iff.mp hc with ⟨cr, hcr, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨tl, htl, h2⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, rfl⟩; exact wp_adx w hw true hrd hargs_ab hdist hpa hpb hpc hcr htl
      · rename_i cc; cases cc <;> try exact fb hc
        simp only [Option.bind_eq_bind] at hc; rcases Option.bind_eq_some_iff.mp hc with ⟨cr, hcr, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨tl, htl, h2⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, rfl⟩; exact wp_adx w hw false hrd hargs_ab hdist hpa hpb hpc hcr htl
    · simp [hdist] at hc

theorem opSubb_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (hw : w = .W32 ∨ w = .W64)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {pc : PArg Reg64 RegMm CondCode .bool} {ddiff : PDst Reg64 RegMm CondCode (.bits w.bits)}
    {db : PDst Reg64 RegMm CondCode .bool} {c : List Directive} {clob : FlagMask} {va vb : BitVec w.bits} {vc : Bool} {s : MachineData}
    (hc : opSubb w pa pb pc ddiff db = some (c, clob)) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs ++ pc.gprs, r ∉ x64Scratch)
    (hdst : ∀ r ∈ @tupDstGprs Reg64 RegMm CondCode [.bits w.bits, .bool] (ddiff, db, ()), r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) (hpc : x64Mach.PArgHolds s .bool pc vc) :
    _root_.Program.wp c (OpPost2 (.bits w.bits) .bool ddiff db (va - vb - BitVec.ofNat w.bits vc.toNat) (decide (va.toNat < vb.toNat + vc.toNat)) clob s) E s := by
  cases ddiff with
  | vec _ => simp [opSubb] at hc
  | gpr rd =>
    have hrd : rd ∉ x64Scratch := hdst rd (by simp [tupDstGprs])
    have hargs_ab : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch := fun r hr => hargs r (List.mem_append.2 (.inl hr))
    rw [opSubb_eq] at hc; by_cases hdist : x64DistinctDst rd db = true
    · simp only [hdist, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc; exact wp_cfCarrySeq w hw true hrd hargs_ab hdist hpa hpb hpc hc
    · simp [hdist] at hc

/-! ## 4. `opMulw_spec` (`umulw`/`smulw` at `[32, 64]`, `.mulxFast` + `.mul`/`.imul1`) -/

private theorem fallsTo_mulx (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rlo rhi : Reg64) (va vb : BitVec w.bits)
    (hr11 : (s.regs.get64 .r11).setWidth w.bits = va)
    (hrdx : (s.regs.get64 .rdx).setWidth w.bits = vb) :
    Directive.FallsTo (insW w (.mulx (regW w rhi) (regW w rlo) (.reg (regW w .r11)))) s
      (fun s' => ∃ vlo vhi, vlo.setWidth w.bits = va * vb ∧
        vhi.setWidth w.bits = BitVec.ofNat w.bits (va.toNat * vb.toNat / 2 ^ w.bits) ∧
        s' = { s with regs := (s.regs.set64 rlo vlo).set64 rhi vhi }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [insW, regW, Width.bits, t_step_simp, Reg64s.get_low32] at hr11 hrdx ⊢
    rw [hr11, hrdx]; refine hk _ ⟨_, _, ?_, ?_, rfl⟩
    · rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, umulw_lo]
    · rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, umulw_hi]
  · simp only [insW, regW, Width.bits, t_step_simp, Reg64s.get_low64, Reg64s.set_low64] at hr11 hrdx ⊢
    rw [← BitVec.setWidth_eq (s.regs.get64 .r11), hr11, ← BitVec.setWidth_eq (s.regs.get64 .rdx), hrdx]
    exact hk _ ⟨_, _, by rw [BitVec.setWidth_eq, umulw_lo], by rw [BitVec.setWidth_eq, umulw_hi], rfl⟩

private theorem fallsTo_mulCore (w : Width) (hw : w = .W32 ∨ w = .W64) (isSigned : Bool)
    (s : MachineData) (va vb : BitVec w.bits)
    (hrax : (s.regs.get64 .rax).setWidth w.bits = va) (hr11 : (s.regs.get64 .r11).setWidth w.bits = vb) :
    Directive.FallsTo (insW w (if isSigned then .imul1 (.reg (regW w .r11)) else .mul (.reg (regW w .r11)))) s
      (fun s' => ∃ rax' rdx' status', rax'.setWidth w.bits = va * vb ∧
        rdx'.setWidth w.bits = (if isSigned then (BitVec.ofInt (w.bits + w.bits) (va.toInt * vb.toInt)).extractLsb' w.bits w.bits
                                else BitVec.ofNat w.bits (va.toNat * vb.toNat / 2 ^ w.bits)) ∧
        s' = { s with regs := (s.regs.set64 .rax rax').set64 .rdx rdx', status := status' }) := by
  intro _ _ _ _ _ hk
  cases isSigned <;> rcases hw with rfl | rfl
  · simp only [insW, regW, Width.bits, t_step_simp, Reg64s.get_low32, show (Width.W32 == .W8) = false by decide,
      Bool.false_eq_true, ↓reduceIte, Effects.All] at hrax hr11 ⊢
    rw [hrax, hr11]; intro _ _ _ _
    refine hk _ ⟨_, _, _, ?_, ?_, rfl⟩
    · simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
    · simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), umulw_hi]
  · simp only [insW, regW, Width.bits, t_step_simp, Reg64s.get_low64, Reg64s.set_low64,
      show (Width.W64 == .W8) = false by decide, Bool.false_eq_true, ↓reduceIte, Effects.All] at hrax hr11 ⊢
    rw [← BitVec.setWidth_eq (s.regs.get64 .rax), hrax, ← BitVec.setWidth_eq (s.regs.get64 .r11), hr11]
    intro _ _ _ _; exact hk _ ⟨_, _, _, by simp, by simp [umulw_hi], rfl⟩
  · obtain ⟨hlo, hhi⟩ := imul1_low_W .W32 (.inl rfl) va vb
    simp only [insW, regW, Width.bits, t_step_simp, Reg64s.get_low32, show (Width.W32 == .W8) = false by decide,
      ↓reduceIte, Effects.All] at hrax hr11 hlo hhi ⊢
    rw [hrax, hr11]; intro _ _ _ _
    refine hk _ ⟨_, _, _, ?_, ?_, rfl⟩
    · simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), hlo]
    · simp only [↓reduceIte, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
      exact (BitVec.setWidth_eq _).symm.trans hhi
  · obtain ⟨hlo, hhi⟩ := imul1_low_W .W64 (.inr rfl) va vb
    simp only [insW, regW, Width.bits, t_step_simp, Reg64s.get_low64, Reg64s.set_low64,
      show (Width.W64 == .W8) = false by decide, ↓reduceIte, Effects.All] at hrax hr11 hlo hhi ⊢
    rw [← BitVec.setWidth_eq (s.regs.get64 .rax), hrax, ← BitVec.setWidth_eq (s.regs.get64 .r11), hr11]
    intro _ _ _ _
    refine hk _ ⟨_, _, _, by simp [hlo], ?_, rfl⟩
    simp only [↓reduceIte]; exact (BitVec.setWidth_eq _).symm.trans hhi

theorem opMulw_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (hw : w = .W32 ∨ w = .W64)
    (isSigned : Bool) {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)}
    {dlo dhi : PDst Reg64 RegMm CondCode (.bits w.bits)} {vh : VariantHint}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opMulw w isSigned pa pb dlo dhi vh = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hdst : ∀ r ∈ @tupDstGprs Reg64 RegMm CondCode [.bits w.bits, .bits w.bits] (dlo, dhi, ()), r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp c (OpPost2 (.bits w.bits) (.bits w.bits) dlo dhi (va * vb)
      (if isSigned then (BitVec.ofInt (w.bits + w.bits) (va.toInt * vb.toInt)).extractLsb' w.bits w.bits
       else BitVec.ofNat w.bits (va.toNat * vb.toNat / 2 ^ w.bits)) clob s) E s := by
  cases dlo with
  | vec _ => simp [opMulw] at hc
  | gpr rlo =>
    cases dhi with
    | vec _ => simp [opMulw] at hc
    | gpr rhi =>
      have hrlo_sc := ne_of_not_mem_x64Scratch (hdst rlo (by simp [tupDstGprs]))
      have hrhi_sc := ne_of_not_mem_x64Scratch (hdst rhi (by simp [tupDstGprs]))
      unfold opMulw at hc; dsimp +zetaHave only at hc
      by_cases heq : rlo == rhi
      · simp [heq] at hc
      · have hrlo_hi : rlo ≠ rhi := fun h => heq ((beq_reg64_iff rlo rhi).2 h)
        simp only [heq, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases hmx : (!isSigned && vh == .mulxFast) = true
        · simp only [hmx, ↓reduceIte, Option.bind_eq_bind] at hc
          have his : isSigned = false := by cases isSigned <;> simp_all
          subst his; simp only [Bool.false_eq_true, ↓reduceIte]
          rcases Option.bind_eq_some_iff.mp hc with ⟨da, hda, h1⟩
          have hpb_sub : ∀ {s0 st : MachineData}, x64Mach.PArgHolds s0 (.bits w.bits) pb vb →
              ∀ t, t ∈ x64Scratch → (∀ r, r ≠ t → st.regs.get64 r = s0.regs.get64 r) → st.zmms = s0.zmms →
              x64Mach.PArgHolds st (.bits w.bits) pb vb := fun {s0 st} hp t ht hfr hzm => by
            cases pb with
            | imm _ => exact hp
            | vec _ => simpa [Machine.PArgHolds, Machine.getVec, x64Mach, hzm] using hp
            | gpr rx =>
              have hrx := hargs rx (by simp [PArg.gprs])
              dsimp only [Machine.PArgHolds, Machine.getGpr, x64Mach] at hp ⊢
              rw [hfr rx (fun h => hrx (h ▸ ht))]; exact hp
          have hfin : ∀ (loadB : List Directive),
              c = ([da] ++ (if rlo == .rdx || rhi == .rdx then [] else [movD .r10 .rdx]) ++ loadB ++
                [insW w (.mulx (regW w rhi) (regW w rlo) (.reg (regW w .r11)))] ++
                (if rlo == .rdx || rhi == .rdx then [] else [movD .rdx .r10])) → clob = maskNone →
              (∀ s2, (s2.regs.get64 .r11).setWidth w.bits = va → x64Mach.PArgHolds s2 (.bits w.bits) pb vb →
                (rlo ≠ .rdx ∧ rhi ≠ .rdx → s2.regs.get64 .r10 = s.regs.get64 .rdx) →
                (∀ r, r ≠ .r10 → r ≠ .r11 → s2.regs.get64 r = s.regs.get64 r) → s2.dmem = s.dmem → s2.zmms = s.zmms → s2.status = s.status →
                _root_.Program.wp loadB (fun s3 => (s3.regs.get64 .r11).setWidth w.bits = va ∧ (s3.regs.get64 .rdx).setWidth w.bits = vb ∧
                  (rlo ≠ .rdx ∧ rhi ≠ .rdx → s3.regs.get64 .r10 = s.regs.get64 .rdx) ∧
                  (∀ r, r ≠ .rdx → r ≠ .r10 → r ≠ .r11 → s3.regs.get64 r = s.regs.get64 r) ∧
                  s3.dmem = s.dmem ∧ s3.zmms = s.zmms ∧ s3.status = s.status) E s2) →
              _root_.Program.wp c (OpPost2 (.bits w.bits) (.bits w.bits) (.gpr rlo) (.gpr rhi) (va * vb)
                (BitVec.ofNat w.bits (va.toNat * vb.toNat / 2 ^ w.bits)) clob s) E s := by
            intro loadB rfl rfl hload_wp
            simp only [List.cons_append, List.nil_append, List.append_assoc]
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_argToBits s .r11 hda hpa)) ?_
            rintro _ ⟨rv11, hrv11, rfl⟩
            have hpb1 : x64Mach.PArgHolds { s with regs := s.regs.set64 .r11 rv11 } (.bits w.bits) pb vb :=
              hpb_sub hpb .r11 (by simp [x64Scratch]) (fun r hr => Reg64s.get64_set64_of_ne _ .r11 r _ hr.symm) rfl
            refine Program.wp.append (p := if rlo == .rdx || rhi == .rdx then [] else [movD .r10 .rdx])
              (Qp := fun s2 => (s2.regs.get64 .r11).setWidth w.bits = va ∧ x64Mach.PArgHolds s2 (.bits w.bits) pb vb ∧
                (rlo ≠ .rdx ∧ rhi ≠ .rdx → s2.regs.get64 .r10 = s.regs.get64 .rdx) ∧
                (∀ r, r ≠ .r10 → r ≠ .r11 → s2.regs.get64 r = s.regs.get64 r) ∧
                s2.dmem = s.dmem ∧ s2.zmms = s.zmms ∧ s2.status = s.status) ?_ ?_
            · by_cases hskip : rlo == .rdx || rhi == .rdx
              · simp only [hskip, ↓reduceIte]; rcases (Bool.or_eq_true _ _).mp hskip with h' | h'
                · exact _root_.Program.wp_nil ⟨by rw [Reg64s.get64_set64_same, hrv11], hpb1, fun ⟨h1', _⟩ => absurd ((beq_reg64_iff _ _).1 h') h1',
                    fun r _ h11 => Reg64s.get64_set64_of_ne _ .r11 r _ h11.symm, rfl, rfl, rfl⟩
                · exact _root_.Program.wp_nil ⟨by rw [Reg64s.get64_set64_same, hrv11], hpb1, fun ⟨_, h2'⟩ => absurd ((beq_reg64_iff _ _).1 h') h2',
                    fun r _ h11 => Reg64s.get64_set64_of_ne _ .r11 r _ h11.symm, rfl, rfl, rfl⟩
              · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
                refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movD _ .r10 .rdx)) ?_; rintro _ rfl
                exact ⟨by rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same, hrv11],
                  hpb_sub (st := _) hpb1 .r10 (by simp [x64Scratch]) (fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _ hr.symm) rfl,
                  fun _ => by rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .r11 .rdx _ (by decide)],
                  fun r h10 h11 => by rw [Reg64s.get64_set64_of_ne _ .r10 r _ h10.symm, Reg64s.get64_set64_of_ne _ .r11 r _ h11.symm], rfl, rfl, rfl⟩
            rintro s2 ⟨h11_2, hpb2, hr10_2, hfr2, hm2, hz2, hst2⟩
            refine Program.wp.append (hload_wp s2 h11_2 hpb2 hr10_2 hfr2 hm2 hz2 hst2) ?_
            rintro s3 ⟨h11_3, hrdx_3, hr10_3, hfr3, hm3, hz3, hst3⟩
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_mulx w hw s3 rlo rhi va vb h11_3 hrdx_3)) ?_
            rintro _ ⟨vlo, vhi, hvlo, hvhi, rfl⟩
            by_cases hskip : rlo == .rdx || rhi == .rdx
            · simp only [hskip, ↓reduceIte]
              refine _root_.Program.wp_nil ⟨(GprHolds.bits_iff w _ _).2 ?_, (GprHolds.bits_iff w _ _).2 ?_, hm3,
                x64_frame_of_eq (fun r hr => ?_) hz3 (updFlags_of_status_eq hst3 _)⟩
              · dsimp [Machine.getGpr]; rw [Reg64s.get64_set64_of_ne _ rhi rlo _ hrlo_hi.symm, Reg64s.get64_set64_same, hvlo]
              · dsimp [Machine.getGpr]; rw [Reg64s.get64_set64_same, hvhi]
              · simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, x64Scratch,
                  List.append_nil, List.singleton_append, List.mem_cons, List.mem_append,
                  List.mem_nil_iff, or_false, not_or] at hr
                rcases hr with ⟨⟨hr1, hr2⟩, ⟨hr10, hr11⟩⟩
                have hdr : r ≠ .rdx := fun h => by
                  subst h; rcases (Bool.or_eq_true _ _).mp hskip with h' | h' <;>
                    first | exact hr1 ((beq_reg64_iff _ _).1 h').symm | exact hr2 ((beq_reg64_iff _ _).1 h').symm
                dsimp [Machine.getGpr]; rw [Reg64s.get64_set64_of_ne _ rhi r _ (Ne.symm hr2),
                  Reg64s.get64_set64_of_ne _ rlo r _ (Ne.symm hr1), hfr3 r hdr hr10 hr11]
            · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
              have hne_rdx : rlo ≠ .rdx ∧ rhi ≠ .rdx :=
                ⟨fun h => hskip (by simp [h]), fun h => hskip (by simp [h])⟩
              refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movD _ .rdx .r10)) ?_; rintro _ rfl
              refine ⟨(GprHolds.bits_iff w _ _).2 ?_, (GprHolds.bits_iff w _ _).2 ?_, hm3,
                x64_frame_of_eq (fun r hr => ?_) hz3 (updFlags_of_status_eq hst3 _)⟩
              · dsimp [Machine.getGpr]; rw [Reg64s.get64_set64_of_ne _ .rdx rlo _ hne_rdx.1.symm,
                  Reg64s.get64_set64_of_ne _ rhi rlo _ hrlo_hi.symm, Reg64s.get64_set64_same, hvlo]
              · dsimp [Machine.getGpr]; rw [Reg64s.get64_set64_of_ne _ .rdx rhi _ hne_rdx.2.symm, Reg64s.get64_set64_same, hvhi]
              · simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, x64Scratch,
                  List.append_nil, List.singleton_append, List.mem_cons, List.mem_append,
                  List.mem_nil_iff, or_false, not_or] at hr
                rcases hr with ⟨⟨hr1, hr2⟩, ⟨hr10, hr11⟩⟩; dsimp [Machine.getGpr]
                by_cases hdr : r = .rdx
                · subst hdr; rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ rhi .r10 _ hrhi_sc.1,
                    Reg64s.get64_set64_of_ne _ rlo .r10 _ hrlo_sc.1, hr10_3 hne_rdx]
                · rw [Reg64s.get64_set64_of_ne _ .rdx r _ (Ne.symm hdr), Reg64s.get64_set64_of_ne _ rhi r _ (Ne.symm hr2),
                    Reg64s.get64_set64_of_ne _ rlo r _ (Ne.symm hr1), hfr3 r hdr hr10 hr11]
          have hfin_db : ∀ {db : Directive}, argToBits w .rdx pb = some db →
              some ([da] ++ (if rlo == .rdx || rhi == .rdx then [] else [movD .r10 .rdx]) ++ [db] ++
                [insW w (.mulx (regW w rhi) (regW w rlo) (.reg (regW w .r11)))] ++
                (if rlo == .rdx || rhi == .rdx then [] else [movD .rdx .r10]), maskNone) = some (c, clob) →
              _root_.Program.wp c (OpPost2 (.bits w.bits) (.bits w.bits) (.gpr rlo) (.gpr rhi) (va * vb)
                (BitVec.ofNat w.bits (va.toNat * vb.toNat / 2 ^ w.bits)) clob s) E s := by
            intro db hdb h2; simp only [Option.some.injEq, Prod.mk.injEq] at h2
            refine hfin [db] h2.1.symm h2.2.symm fun s2 h11 hpb2 hr10 hfr hm hz hst =>
              Program.wp.mono (Directive.FallsTo.wp (fallsTo_argToBits s2 .rdx hdb hpb2)) ?_
            rintro _ ⟨_, hrvd, rfl⟩
            exact ⟨by rw [Reg64s.get64_set64_of_ne _ .rdx .r11 _ (by decide), h11], by rw [Reg64s.get64_set64_same, hrvd],
              fun hn => by rw [Reg64s.get64_set64_of_ne _ .rdx .r10 _ (by decide), hr10 hn],
              fun r hdr h10 h11' => by rw [Reg64s.get64_set64_of_ne _ .rdx r _ hdr.symm, hfr r h10 h11'], hm, hz, hst⟩
          cases pb with
          | gpr rx =>
            cases rx <;> simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h1
            case rdx =>
              exact hfin [] h1.1.symm h1.2.symm fun s2 h11 hpb2 hr10 hfr hm hz hst =>
                _root_.Program.wp_nil ⟨h11, (GprHolds.bits_iff w _ _).1 hpb2, hr10, fun r _ => hfr r, hm, hz, hst⟩
            all_goals
              rcases Option.bind_eq_some_iff.mp h1 with ⟨db, hdb, h2⟩
              exact hfin_db hdb h2
          | imm _ | vec _ =>
            simp only [Option.bind_some] at h1
            rcases Option.bind_eq_some_iff.mp h1 with ⟨db, hdb, h2⟩
            exact hfin_db hdb h2
        · simp only [hmx, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind] at hc
          rcases Option.bind_eq_some_iff.mp hc with ⟨da, hda, h1⟩
          rcases Option.bind_eq_some_iff.mp h1 with ⟨db, hdb, h2⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨hseq, rfl⟩; rw [← hseq]
          have hp_pre : _root_.Program.wp [da, db] (fun s2 => ∃ rv10 rv11 : BitVec 64,
              rv10.setWidth w.bits = va ∧ rv11.setWidth w.bits = vb ∧
              s2 = { s with regs := (s.regs.set64 .r10 rv10).set64 .r11 rv11 }) E s := by
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_argToBits s .r10 hda hpa)) ?_
            rintro _ ⟨rv10, hrv10, rfl⟩
            have hpb1 : x64Mach.PArgHolds { s with regs := s.regs.set64 .r10 rv10 } (.bits w.bits) pb vb := by
              cases pb with | vec _ | imm _ => exact hpb | gpr rx =>
                have hrx := (ne_of_not_mem_x64Scratch (hargs rx (by simp [PArg.gprs]))).1
                dsimp only [Machine.PArgHolds, Machine.getGpr, x64Mach] at hpb ⊢
                rw [Reg64s.get64_set64_of_ne _ .r10 rx _ hrx.symm]; exact hpb
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_argToBits _ .r11 hdb hpb1)) ?_
            rintro _ ⟨rv11, hrv11, rfl⟩; exact ⟨rv10, rv11, hrv10, hrv11, rfl⟩
          have hp_cons : ∀ (xs : List Directive),
              (∀ rv10 rv11, rv10.setWidth w.bits = va → rv11.setWidth w.bits = vb →
                _root_.Program.wp xs (OpPost2 (.bits w.bits) (.bits w.bits) (.gpr rlo) (.gpr rhi) (va * vb)
                  (if isSigned then (BitVec.ofInt (w.bits + w.bits) (va.toInt * vb.toInt)).extractLsb' w.bits w.bits
                   else BitVec.ofNat w.bits (va.toNat * vb.toNat / 2 ^ w.bits)) maskAll s) E
                  { s with regs := (s.regs.set64 .r10 rv10).set64 .r11 rv11 }) →
              _root_.Program.wp (da :: db :: xs) (OpPost2 (.bits w.bits) (.bits w.bits) (.gpr rlo) (.gpr rhi) (va * vb)
                (if isSigned then (BitVec.ofInt (w.bits + w.bits) (va.toInt * vb.toInt)).extractLsb' w.bits w.bits
                 else BitVec.ofNat w.bits (va.toNat * vb.toNat / 2 ^ w.bits)) maskAll s) E s := fun xs hxs =>
            Program.wp.append (p := [da, db]) hp_pre fun _ ⟨rv10, rv11, h10, h11, hs2⟩ => hs2 ▸ hxs rv10 rv11 h10 h11
          have movStep : ∀ (a b : Reg64) (st : MachineData) (rest : List Directive) (Q : MachineData → Prop),
              _root_.Program.wp rest Q E { st with regs := st.regs.set64 a (st.regs.get64 b) } →
              _root_.Program.wp (movD a b :: rest) Q E st := fun a b st rest Q h =>
            Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD st a b)) fun _ hr => hr ▸ h
          have mulStep : ∀ (st : MachineData) (rest : List Directive) (Q : MachineData → Prop),
              (st.regs.get64 .rax).setWidth w.bits = va → (st.regs.get64 .r11).setWidth w.bits = vb →
              (∀ rax' rdx' st', rax'.setWidth w.bits = va * vb →
                rdx'.setWidth w.bits = (if isSigned then (BitVec.ofInt (w.bits + w.bits) (va.toInt * vb.toInt)).extractLsb' w.bits w.bits
                                        else BitVec.ofNat w.bits (va.toNat * vb.toNat / 2 ^ w.bits)) →
                _root_.Program.wp rest Q E { st with regs := (st.regs.set64 .rax rax').set64 .rdx rdx', status := st' }) →
              _root_.Program.wp (insW w (if isSigned then .imul1 (.reg (regW w .r11)) else .mul (.reg (regW w .r11))) :: rest) Q E st :=
            fun st rest Q ha hb h => Program.wp.cons (Directive.FallsTo.wp (fallsTo_mulCore w hw isSigned st va vb ha hb)) fun _ ⟨a', d', st', ha', hd', hr⟩ => hr ▸ h a' d' st' ha' hd'
          clear hc h1 hda hdb hseq hargs hdst hpa hpb hmx heq hp_pre
          split; rotate_left
          split; rotate_left
          split; rotate_left
          split; rotate_left
          split; rotate_left
          split
          all_goals
            simp only [Bool.and_eq_true, beq_reg64_iff, not_and] at *
            refine hp_cons _ fun rv10 rv11 h10 h11 => ?_
            clear hp_cons
            repeat' refine movStep _ _ _ _ _ ?_
            refine mulStep _ _ _ ?_ ?_ fun rax' rdx' st' ha' hd' => ?_
            · exact (congrArg (BitVec.setWidth w.bits) (by simp only [Reg64s.get64_set64]; grind)).trans h10
            · exact (congrArg (BitVec.setWidth w.bits) (by simp [Reg64s.get64_set64] <;> grind)).trans h11
            repeat' refine movStep _ _ _ _ _ ?_
            clear movStep mulStep
            refine _root_.Program.wp_nil ⟨(GprHolds.bits_iff w _ _).2 ?_, (GprHolds.bits_iff w _ _).2 ?_, rfl,
              x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_maskAll _ _)⟩
            · dsimp [Machine.getGpr]
              exact (congrArg (BitVec.setWidth w.bits) (by simp only [Reg64s.get64_set64]; grind)).trans ha'
            · dsimp [Machine.getGpr]
              exact (congrArg (BitVec.setWidth w.bits) (by simp only [Reg64s.get64_set64]; grind)).trans hd'
            · simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, List.nil_append,
                List.cons_append, List.mem_cons, List.mem_nil_iff, or_false, not_or,
                x64Scratch] at hr
              dsimp [Machine.getGpr]; simp only [Reg64s.get64_set64]; grind

end

end LeanQbe.T.Amd64
