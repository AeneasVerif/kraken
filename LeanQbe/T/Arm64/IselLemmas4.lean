module

public import LeanQbe.T.Arm64.IselLemmas3
import Kraken.AArch64.Parser

/-!
# AArch64 Scalar Instruction Selection Proofs — Part 4 (`T9`)

`armMulwOp_wp`, `armFunnelOp_wp`, top-level `armOp_spec`, `armGprSpec : GprTarget armMach armGpr armScratch`,
`armOp_noLab`, and kernel `rfl` `ParserChecks` against `Kraken.AArch64.Parser`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Double-width multiply (`armMulwOp_wp`) and funnel shift (`armFunnelOp_wp`) -/

private theorem armShiftV_wp [Host] (isLeft : Bool) (w : RegWidth) (d ra rb : XReg)
    (s : MachineData) :
    _root_.Program.wp
      [if isLeft then ins (.LSLV (zr d w) (zr ra w) (zr rb w))
       else ins (.LSRV (zr d w) (zr ra w) (zr rb w))]
      (fun s' => s' = wr s d
        ((if isLeft then
            ((s.regs.getXReg ra).toBitVec.setWidth w.bits) <<<
              (((s.regs.getXReg rb).toBitVec.setWidth w.bits).toNat % w.bits)
          else
            ((s.regs.getXReg ra).toBitVec.setWidth w.bits).ushiftRight
              (((s.regs.getXReg rb).toBitVec.setWidth w.bits).toNat % w.bits)).setWidth 64))
      (fun _ _ => False) s := by
  cases isLeft
  · cases w <;> exact armDirFallsTo_wp (d := ins (.LSRV (zr d _) (zr ra _) (zr rb _)))
      fun {_} p next jmp Q hk => by
        simp only [t_step_simp, BitVec.ushiftRight_eq, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
        exact hk _ rfl
  · cases w <;> exact armDirFallsTo_wp (d := ins (.LSLV (zr d _) (zr ra _) (zr rb _)))
      fun {_} p next jmp Q hk => by
        simp only [t_step_simp, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
        exact hk _ rfl

private theorem armOrrDir_wp [Host] (w : RegWidth) (d ra rb : XReg) (s : MachineData) :
    _root_.Program.wp [ins (.ORR_s (zr d w) (zr ra w) (sh rb))]
      (fun s' => s' = wr s d
        ((((s.regs.getXReg ra).toBitVec.setWidth w.bits) |||
          ((s.regs.getXReg rb).toBitVec.setWidth w.bits)).setWidth 64))
      (fun _ _ => False) s := by
  cases w <;>
    exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
        RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
      exact hk _ rfl

private theorem mul_lt_pow64 (a b : BitVec 32) : a.toNat * b.toNat < 2 ^ 64 := by
  have ha := a.isLt; have hb := b.isLt
  calc a.toNat * b.toNat ≤ 2 ^ 32 * b.toNat := Nat.mul_le_mul_right _ (Nat.le_of_lt ha)
    _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_left (by decide) |>.mpr hb
    _ = 2 ^ 64 := by decide

private theorem umulw32_lo (a b : BitVec 32) :
    (BitVec.ofInt 64 (a.unsigned * b.unsigned + (0#64).signed)).setWidth 32 = a * b := by
  apply BitVec.eq_of_toNat_eq
  have hlt := mul_lt_pow64 a b
  have hzero : (0#64).signed = 0 := by simp [BitVec.signed]
  rw [hzero, Int.add_zero, BitVec.unsigned, BitVec.unsigned, ← Int.natCast_mul, BitVec.ofInt_natCast]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_mul, Nat.mod_eq_of_lt hlt]

private theorem umulw32_hi (a b : BitVec 32) :
    ((BitVec.ofInt 64 (a.unsigned * b.unsigned + (0#64).signed)) >>> 32).setWidth 32 =
      BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := mul_lt_pow64 a b
  have hdiv : a.toNat * b.toNat / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul hlt
  have hzero : (0#64).signed = 0 := by simp [BitVec.signed]
  rw [hzero, Int.add_zero, BitVec.unsigned, BitVec.unsigned, ← Int.natCast_mul, BitVec.ofInt_natCast]
  simp [Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hdiv]

private theorem umulw64_hi (a b : BitVec 64) :
    (BitVec.ofInt 128 (a.unsigned * b.unsigned)).extractLsb' 64 64 =
      BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.unsigned, BitVec.unsigned, ← Int.natCast_mul, BitVec.ofInt_natCast]
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, hi, show 64 + i < 128 by omega,
    decide_true, Bool.true_and]
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

private theorem smulw32_lo (a b : BitVec 32) :
    (BitVec.ofInt 64 (a.signed * b.signed + (0#64).signed)).setWidth 32 = a * b := by
  have hzero : (0#64).signed = 0 := by simp [BitVec.signed]
  rw [hzero, Int.add_zero]
  have hlhs : (BitVec.ofInt 64 (a.signed * b.signed)).setWidth 32 =
      BitVec.ofInt 32 (a.signed * b.signed) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    have hnn1 : 0 ≤ a.signed * b.signed % ((2 ^ 64 : Nat) : Int) := Int.emod_nonneg _ (by decide)
    have hnn2 : 0 ≤ a.signed * b.signed % ((2 ^ 32 : Nat) : Int) := Int.emod_nonneg _ (by decide)
    have hdvd := Int.emod_emod_of_dvd (a.signed * b.signed) (by decide : ((2 ^ 32 : Nat) : Int) ∣ (2 ^ 64 : Nat))
    have h1 : ((a.signed * b.signed % ((2 ^ 64 : Nat) : Int)).toNat % 2 ^ 32 : Int) =
        ((a.signed * b.signed % ((2 ^ 32 : Nat) : Int)).toNat : Int) := by omega
    exact Int.ofNat.inj h1
  rw [hlhs, BitVec.signed, BitVec.signed, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

private theorem smulw32_hi (a b : BitVec 32) :
    ((BitVec.ofInt 64 (a.signed * b.signed + (0#64).signed)) >>> 32).setWidth 32 =
      (BitVec.ofInt (32 + 32) (a.toInt * b.toInt)).extractLsb' 32 32 := by
  have hzero : (0#64).signed = 0 := by simp [BitVec.signed]
  rw [hzero, Int.add_zero]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, BitVec.signed, Nat.add_comm 32 i]

private theorem fshl_zero {n : Nat} (a b : BitVec n) :
    ((a ++ b) <<< 0).extractLsb' n n = a := by
  simp only [BitVec.shiftLeft_zero]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi, show ¬(n + i < n) by omega]

private theorem fshr_zero {n : Nat} (a b : BitVec n) :
    ((a ++ b) >>> 0).extractLsb' 0 n = b := by
  simp only [BitVec.ushiftRight_zero]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

private theorem neg_mod_eq {w : RegWidth} (c : BitVec w.bits) (hc : c.toNat % w.bits ≠ 0) :
    ((-c).toNat % w.bits) = w.bits - (c.toNat % w.bits) := by
  have hlt := c.isLt
  have hc0 : c.toNat ≠ 0 := fun h => by simp [h] at hc
  cases w
  · simp only [RegWidth.bits, MemWidth.bits] at hlt hc ⊢
    rw [BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega : 2 ^ 32 - c.toNat < 2 ^ 32)]
    omega
  · simp only [RegWidth.bits, MemWidth.bits] at hlt hc ⊢
    rw [BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - c.toNat < 2 ^ 64)]
    omega

private theorem and_shiftMask_eq_zero {w : RegWidth} (c : BitVec w.bits) :
    ((c &&& BitVec.ofNat w.bits (w.bits - 1)) == 0#w.bits) = decide (c.toNat % w.bits = 0) := by
  have hk : ∀ {k : Nat} (hk : 2 ^ k = w.bits) (hltw : k ≤ w.bits)
      (hm : ∀ i < w.bits, (BitVec.ofNat w.bits (w.bits - 1)).getLsbD i = decide (i < k)),
      ((c &&& BitVec.ofNat w.bits (w.bits - 1)) = 0#w.bits ↔ c.toNat % w.bits = 0) := by
    intro k hk hltw hm
    have hsw : (c &&& BitVec.ofNat w.bits (w.bits - 1) = 0#w.bits) ↔ c.setWidth k = 0#k := by
      constructor
      · intro h0; apply BitVec.eq_of_getLsbD_eq; intro i hi
        have hlt : i < w.bits := Nat.lt_of_lt_of_le hi hltw
        have hbi := congrArg (fun z => z.getLsbD i) h0
        simp only [BitVec.getLsbD_and, hm i hlt, decide_eq_true hi, Bool.and_true, BitVec.getLsbD_zero] at hbi
        simpa [hi] using hbi
      · intro h0; apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp only [BitVec.getLsbD_and, hm i hi, BitVec.getLsbD_zero]
        by_cases hik : i < k
        · have hbi := congrArg (fun z => z.getLsbD i) h0
          simp only [BitVec.getLsbD_setWidth, hik, decide_true, Bool.true_and, BitVec.getLsbD_zero] at hbi
          simp [hbi, hik]
        · simp [hik]
    rw [hsw, ← BitVec.toNat_inj]
    simp [BitVec.toNat_setWidth, hk]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  cases w
  · refine hk (k := 5) rfl (by decide) fun i hi => ?_
    rcases Nat.lt_or_ge i 5 with h5 | h5
    · exact (by revert i h5; decide : ∀ i < 5, (BitVec.ofNat 32 31).getLsbD i = decide (i < 5)) i h5
    · simp only [RegWidth.bits, MemWidth.bits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
        decide_eq_false (by omega : ¬(i < 5))]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 31 < 2 ^ 5)
        (Nat.pow_le_pow_right (by decide) h5))
  · refine hk (k := 6) rfl (by decide) fun i hi => ?_
    rcases Nat.lt_or_ge i 6 with h6 | h6
    · exact (by revert i h6; decide : ∀ i < 6, (BitVec.ofNat 64 63).getLsbD i = decide (i < 6)) i h6
    · simp only [RegWidth.bits, MemWidth.bits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
        decide_eq_false (by omega : ¬(i < 6))]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 63 < 2 ^ 6)
        (Nat.pow_le_pow_right (by decide) h6))

private theorem armMulwPost_wp {n : Nat} (isSigned : Bool) (hn64 : n ≤ 64)
    (dlo dhi : XReg) (va vb : BitVec n) {s s₃ : MachineData}
    (hlo : (s₃.regs.getXReg dlo).toBitVec.setWidth n = va * vb)
    (hhi : (s₃.regs.getXReg dhi).toBitVec.setWidth n =
      if isSigned then (BitVec.ofInt (n + n) (va.toInt * vb.toInt)).extractLsb' n n
      else BitVec.ofNat n (va.toNat * vb.toNat / 2 ^ n))
    (hdm : s₃.dmem = s.dmem) (hst : s₃.status = s.status)
    (hkeep : ∀ r, r ∉ (.reg dlo :: .reg dhi :: armScratch) → get s₃ r = get s r) :
    (∃ rvs : Tup Val [.bits n, .bits n],
      rvs = (va * vb,
        if isSigned then (BitVec.ofInt (n + n) (va.toInt * vb.toInt)).extractLsb' n n
        else BitVec.ofNat n (va.toNat * vb.toNat / 2 ^ n), ()) ∧
      TRel (armMach.PDstHolds s₃) (as := [.bits n, .bits n])
        ((PDst.gpr (.reg dlo) : PDst Reg Empty ArmCond (.bits n)), .gpr (.reg dhi), ()) rvs) ∧
    armMach.mem s₃ = armMach.mem s ∧
    armMach.Frame armCondReads s s₃
      (tupDstGprs (ts := [.bits n, .bits n]) ((PDst.gpr (.reg dlo) : PDst Reg Empty ArmCond (.bits n)), .gpr (.reg dhi), ()) ++ armScratch)
      [] maskNone :=
  ⟨⟨(_, _, ()), rfl, .cons ⟨hn64, by simpa [Machine.PDstHolds, GprHolds, get_reg] using hlo⟩
    (.cons ⟨hn64, by simpa [Machine.PDstHolds, GprHolds, get_reg] using hhi⟩ .nil)⟩,
    hdm, armFrame_status_eq (fun r hr => hkeep r (by simpa [tupDstGprs, armScratch] using hr)) hst⟩

private theorem xreg_eq_of_bne_false {a b : XReg} (h : (a != b) = false) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem xreg_bne_self (x : XReg) : (x != x) = false := by cases x <;> rfl

private theorem status_wr (s : MachineData) (r : XReg) (v : BitVec 64) : (wr s r v).status = s.status := rfl

private theorem x16_ne_x17 : XReg.X16 ≠ XReg.X17 := by decide

theorem armMulwOp_wp [Host] (isSigned : Bool) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dlo dhi : XReg)
    {va vb : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armMulwOpIns isSigned n pa pb dlo dhi = some (c, clob))
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hd : XRegOrSp.reg dlo ∉ armScratch ∧ XRegOrSp.reg dhi ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      (∃ rvs : Tup Val [.bits n, .bits n],
        rvs = (va * vb,
          if isSigned then (BitVec.ofInt (n + n) (va.toInt * vb.toInt)).extractLsb' n n
          else BitVec.ofNat n (va.toNat * vb.toNat / 2 ^ n), ()) ∧
        TRel (armMach.PDstHolds s') (as := [.bits n, .bits n])
          ((PDst.gpr (.reg dlo) : PDst Reg Empty ArmCond (.bits n)), .gpr (.reg dhi), ()) rvs) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s'
        (tupDstGprs (ts := [.bits n, .bits n]) ((PDst.gpr (.reg dlo) : PDst Reg Empty ArmCond (.bits n)), .gpr (.reg dhi), ()) ++ armScratch)
        [] clob) (fun _ _ => False) s := by
  dsimp only [armMulwOpIns] at hc; split at hc
  · simp at hc
  · rename_i hok
    have hneq : dlo ≠ dhi := fun h => by
      subst h; have hd : (dlo == dlo) = true := by cases dlo <;> rfl
      simp [hd] at hok
    have hn' : n = 32 ∨ n = 64 := by cases h32 : (n == 32) <;> cases h64 : (n == 64) <;> simp_all
    have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl <;> decide
    have ⟨hdlo16, _⟩ := xreg_ne_scratch_of_not_mem hd.1
    simp only [bind, Option.bind_eq_some_iff] at hc
    rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, htail⟩
    have mulH_wp : ∀ (dst : XReg) (sx : MachineData),
        _root_.Program.wp [Kraken.Directive.instr (if isSigned then
            armIselInsI (.SMULH (zr dst .W64) (zr ra .W64) (zr rb .W64))
            else armIselInsI (.UMULH (zr dst .W64) (zr ra .W64) (zr rb .W64)))]
          (fun s' => s' = wr sx dst
            (if isSigned then (BitVec.ofInt 128 ((sx.regs.getXReg ra).toBitVec.signed * (sx.regs.getXReg rb).toBitVec.signed)).extractLsb' 64 64
             else BitVec.ofNat 64 ((sx.regs.getXReg ra).toBitVec.toNat * (sx.regs.getXReg rb).toBitVec.toNat / 2 ^ 64)))
          (fun _ _ => False) sx := by
      intro dst sx; cases isSigned
      · exact armDirFallsTo_wp (d := ins (.UMULH (zr dst .W64) (zr ra .W64) (zr rb .W64)))
          fun {_} p next jmp Q hk => by
            simp only [t_step_simp, BitVec.setWidth_eq, RegWidth.bits, MemWidth.bits]
            rw [show (64 + 64 : Nat) = 128 from rfl, umulw64_hi]; exact hk _ rfl
      · exact armDirFallsTo_wp (d := ins (.SMULH (zr dst .W64) (zr ra .W64) (zr rb .W64)))
          fun {_} p next jmp Q hk => by
            simp only [t_step_simp, RegWidth.bits, MemWidth.bits]; exact hk _ rfl
    have mulL_wp : ∀ (dst : XReg) (sx : MachineData),
        _root_.Program.wp [ins (.MADD (zr dst .W64) (zr ra .W64) (zr rb .W64) (xzr .W64))]
          (fun s' => s' = wr sx dst ((sx.regs.getXReg ra).toBitVec * (sx.regs.getXReg rb).toBitVec))
          (fun _ _ => False) sx := fun dst sx =>
      armDirFallsTo_wp fun {_} p next jmp Q hk => by
        simp only [t_step_simp, BitVec.add_zero, RegWidth.bits, MemWidth.bits]; exact hk _ rfl
    rcases hn' with rfl | rfl
    · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at htail
      rcases htail with ⟨rfl, rfl⟩
      simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
      refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
      rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂⟩
      simp only [emitClean_cons, emitClean_nil]
      have hmul64 : _root_.Program.wp [Kraken.Directive.instr (if isSigned then
            armIselInsI (.SMADDL (zr dlo .W64) (zr ra .W32) (zr rb .W32) (xzr .W64))
            else armIselInsI (.UMADDL (zr dlo .W64) (zr ra .W32) (zr rb .W32) (xzr .W64)))]
          (fun s' => s' = wr s₂ dlo (BitVec.ofInt 64 (if isSigned then va.signed * vb.signed + (0#64).signed
                                                     else va.unsigned * vb.unsigned + (0#64).signed)))
          (fun _ _ => False) s₂ := by
        cases isSigned
        · exact armDirFallsTo_wp (d := ins (.UMADDL (zr dlo .W64) (zr ra .W32) (zr rb .W32) (xzr .W64)))
            fun {_} p next jmp Q hk => by
              simp only [t_step_simp, hra, hrb, RegWidth.bits, MemWidth.bits]; exact hk _ rfl
        · exact armDirFallsTo_wp (d := ins (.SMADDL (zr dlo .W64) (zr ra .W32) (zr rb .W32) (xzr .W64)))
            fun {_} p next jmp Q hk => by
              simp only [t_step_simp, hra, hrb, RegWidth.bits, MemWidth.bits]; exact hk _ rfl
      refine armWp_cons hmul64 fun s₃ hs₃ => ?_
      refine armWp_mono (armDirFallsTo_wp (Q := fun s' =>
          s' = wr s₃ dhi (((s₃.regs.getXReg dlo).toBitVec >>> 32).setWidth 64))
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp]; rw [evalUBFM_32_63]; simp only [BitVec.setWidth_eq]; exact hk _ rfl)
        fun s₄ hs₄ => ?_
      subst hs₄ hs₃
      refine armMulwPost_wp isSigned hn64 dlo dhi va vb ?_ ?_ hd₂ hst₂ fun r hr => ?_
      · rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneq.symm, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec]
        cases isSigned <;> (first | exact umulw32_lo va vb | exact smulw32_lo va vb)
      · rw [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, Reg64s.getXReg_setXReg_same,
          UInt64.toBitVec_ofBitVec, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
        cases isSigned <;> (first | exact umulw32_hi va vb | exact smulw32_hi va vb)
      · have hr' : r ≠ .reg dlo ∧ r ≠ .reg dhi ∧ r ∉ armScratch := by simpa using hr
        rw [get_wr_of_ne _ dhi _ r hr'.2.1, get_wr_of_ne s₂ dlo _ r hr'.1]; exact hfr₂.1 r hr'.2.2
    · simp only [show (64 == 32) = false from rfl, Bool.false_eq_true, ↓reduceIte] at htail
      split at htail
      · rename_i hfreeH
        rcases Option.some.inj htail with ⟨rfl, rfl⟩
        have ⟨hne1, hne2⟩ : dhi ≠ ra ∧ dhi ≠ rb := by
          simp only [Bool.and_eq_true] at hfreeH
          exact ⟨fun h => by subst h; exact Bool.noConfusion ((xreg_bne_self dhi).symm.trans hfreeH.1),
                 fun h => by subst h; exact Bool.noConfusion ((xreg_bne_self dhi).symm.trans hfreeH.2)⟩
        simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
        refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
        rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂⟩
        simp only [emitClean_cons, emitClean_nil]
        simp only [BitVec.setWidth_eq] at hra hrb
        refine armWp_cons (mulH_wp dhi s₂) fun s₃ hs₃ => ?_
        refine armWp_mono (mulL_wp dlo s₃) fun s₄ hs₄ => ?_
        subst hs₄ hs₃
        refine armMulwPost_wp isSigned hn64 dlo dhi va vb ?_ ?_ hd₂ hst₂ fun r hr => ?_
        · rw [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
            Reg64s.getXReg_setXReg_of_ne _ _ _ _ hne1, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hne2,
            hra, hrb, BitVec.setWidth_eq]
        · rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneq, Reg64s.getXReg_setXReg_same,
            UInt64.toBitVec_ofBitVec, hra, hrb, BitVec.setWidth_eq]
          cases isSigned <;> rfl
        · have hr' : r ≠ .reg dlo ∧ r ≠ .reg dhi ∧ r ∉ armScratch := by simpa using hr
          rw [get_wr_of_ne _ dlo _ r hr'.1, get_wr_of_ne s₂ dhi _ r hr'.2.1]
          exact hfr₂.1 r hr'.2.2
      · split at htail
        · rename_i hfreeL
          rcases Option.some.inj htail with ⟨rfl, rfl⟩
          have ⟨hne1, hne2⟩ : dlo ≠ ra ∧ dlo ≠ rb := by
            simp only [Bool.and_eq_true] at hfreeL
            exact ⟨fun h => by subst h; exact Bool.noConfusion ((xreg_bne_self dlo).symm.trans hfreeL.1),
                   fun h => by subst h; exact Bool.noConfusion ((xreg_bne_self dlo).symm.trans hfreeL.2)⟩
          simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
          refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
          rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂⟩
          simp only [emitClean_cons, emitClean_nil]
          simp only [BitVec.setWidth_eq] at hra hrb
          refine armWp_cons (mulL_wp dlo s₂) fun s₃ hs₃ => ?_
          refine armWp_mono (mulH_wp dhi s₃) fun s₄ hs₄ => ?_
          subst hs₄ hs₃
          refine armMulwPost_wp isSigned hn64 dlo dhi va vb ?_ ?_ hd₂ hst₂ fun r hr => ?_
          · rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneq.symm, Reg64s.getXReg_setXReg_same,
              UInt64.toBitVec_ofBitVec, hra, hrb, BitVec.setWidth_eq]
          · rw [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
              Reg64s.getXReg_setXReg_of_ne _ _ _ _ hne1, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hne2,
              hra, hrb, BitVec.setWidth_eq]
            cases isSigned <;> rfl
          · have hr' : r ≠ .reg dlo ∧ r ≠ .reg dhi ∧ r ∉ armScratch := by simpa using hr
            rw [get_wr_of_ne _ dhi _ r hr'.2.1, get_wr_of_ne s₂ dlo _ r hr'.1]
            exact hfr₂.1 r hr'.2.2
        · rename_i hbusyH hbusyL
          rcases Option.some.inj htail with ⟨rfl, rfl⟩
          simp only [Bool.not_eq_true, Bool.and_eq_false_iff] at hbusyH hbusyL
          simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
          refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
          rintro s₂ ⟨hra, hrb, _, hneB, hd₂, hst₂, hfr₂⟩
          simp only [emitClean_cons, emitClean_nil]
          simp only [BitVec.setWidth_eq] at hra hrb
          have hneA : .X16 ≠ ra := by
            rcases hbusyH with h1 | h1 <;> rcases hbusyL with h2 | h2
            · exact absurd ((xreg_eq_of_bne_false h2).trans (xreg_eq_of_bne_false h1).symm) hneq
            · exact fun h => (xreg_ne_scratch_of_not_mem hd.2).1 ((xreg_eq_of_bne_false h1).trans h.symm)
            · exact fun h => hdlo16 ((xreg_eq_of_bne_false h2).trans h.symm)
            · exact absurd ((xreg_eq_of_bne_false h2).trans (xreg_eq_of_bne_false h1).symm) hneq
          refine armWp_cons (mulH_wp .X16 s₂) fun s₃ hs₃ => ?_
          refine armWp_cons (mulL_wp dlo s₃) fun s₄ hs₄ => ?_
          refine armWp_mono (armMovRegDir_wp .W64 dhi .X16 s₄) fun s₅ hs₅ => ?_
          subst hs₅ hs₄ hs₃
          refine armMulwPost_wp isSigned hn64 dlo dhi va vb ?_ ?_ hd₂ hst₂ fun r hr => ?_
          · rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneq.symm, Reg64s.getXReg_setXReg_same,
              UInt64.toBitVec_ofBitVec, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneA,
              Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneB.symm, hra, hrb, BitVec.setWidth_eq]
          · simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
            rw [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
              Reg64s.getXReg_setXReg_of_ne _ _ _ _ hdlo16,
              Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, hra, hrb]
            cases isSigned <;> rfl
          · have hr' : r ≠ .reg dlo ∧ r ≠ .reg dhi ∧ r ∉ armScratch := by simpa using hr
            rw [get_wr_of_ne _ dhi _ r hr'.2.1, get_wr_of_ne _ dlo _ r hr'.1,
              get_wr_of_ne s₂ .X16 _ r (ne_of_not_mem_armScratch hr'.2.2).1]
            exact hfr₂.1 r hr'.2.2

private theorem armAndsShiftMask_wp [Host] (w : RegWidth) (rc : XReg) {vc : BitVec w.bits}
    (sx : MachineData) (hrc : (sx.regs.getXReg rc).toBitVec.setWidth w.bits = vc) :
    _root_.Program.wp [ins (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst w.bits))]
      (fun s' => ∃ st, s' = { sx with status := st } ∧
        CondCode.EQ.interp st = decide (vc.toNat % w.bits = 0))
      (fun _ _ => False) sx := by
  have hm : (BitVec.ofInt w.bits (Int64.ofNat (w.bits - 1)).toInt) = BitVec.ofNat w.bits (w.bits - 1) := by
    cases w <;> decide
  cases w <;>
    exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp, ConstExpr.interp, armShiftMaskConst, RegWidth.bits, MemWidth.bits,
        BitVec.setWidth_eq] at hrc hm hk ⊢
      rw [hm, hrc]; exact hk _ ⟨_, rfl, by
        simpa [CondCode.interp, StatusFlags.from_result] using and_shiftMask_eq_zero vc⟩

private theorem armFunnelRes_finish {w : RegWidth} (isLeft : Bool)
    (d : XReg) (va vb vc : BitVec w.bits) {s s' : MachineData}
    (hst : CondCode.EQ.interp s'.status = decide (vc.toNat % w.bits = 0))
    (hs0 : CondCode.EQ.interp s'.status = true →
      (s'.regs.getXReg d).toBitVec.setWidth w.bits = if isLeft then va else vb)
    (hs1 : CondCode.EQ.interp s'.status = false → vc.toNat % w.bits ≠ 0 →
      (s'.regs.getXReg d).toBitVec.setWidth w.bits =
        if isLeft then (va <<< (vc.toNat % w.bits)) ||| (vb >>> (w.bits - vc.toNat % w.bits))
        else (va <<< (w.bits - vc.toNat % w.bits)) ||| (vb >>> (vc.toNat % w.bits)))
    (hz32 : w = .W32 → (s'.regs.getXReg d).toBitVec =
      ((s'.regs.getXReg d).toBitVec.setWidth 32).setWidth 64)
    (hdm : s'.dmem = s.dmem)
    (hkeep : ∀ r, r ∉ (.reg d :: armScratch) → get s' r = get s r) :
    GprHoldsZ (armMach.getGpr s' (.reg d)) w.bits
      (if isLeft then ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits
       else ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits) ∧
    armMach.mem s' = armMach.mem s ∧
    armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNZCV := by
  have hw64 : w.bits ≤ 64 := by cases w <;> decide
  have hw_pos : 0 < w.bits := by cases w <;> decide
  have hw_or : w.bits = 32 ∨ w.bits = 64 := by cases w <;> simp [RegWidth.bits, MemWidth.bits]
  have hlow : (s'.regs.getXReg d).toBitVec.setWidth w.bits =
      if isLeft then ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits
      else ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits := by
    by_cases hc0 : vc.toNat % w.bits = 0
    · have hst' : CondCode.EQ.interp s'.status = true := hst.trans (decide_eq_true hc0)
      rw [hs0 hst', hc0]
      cases isLeft
      · exact (fshr_zero va vb).symm
      · exact (fshl_zero va vb).symm
    · have hst' : CondCode.EQ.interp s'.status = false := hst.trans (decide_eq_false hc0)
      rw [hs1 hst' hc0]
      cases isLeft
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hf := evalEXTR_fshr hw_or va vb (Nat.mod_lt vc.toNat hw_pos)
        rwa [beq_false_of_ne hc0] at hf
      · exact evalEXTR_fshl hw_or va vb (Nat.mod_lt vc.toNat hw_pos)
  refine ⟨⟨⟨hw64, hlow⟩, fun hw32 => ?_⟩, hdm, armFrame_nzcv hkeep⟩
  cases w with
  | W64 => cases hw32
  | W32 => dsimp only [armMach, get_reg]; rw [hz32 rfl, hlow]

private theorem armFunnelImmImm_wp [Host] (w : RegWidth)
    (isLeft : Bool) (d rc : XReg) (va vb vc : BitVec w.bits) {s s₂ : MachineData}
    (h16 : (s₂.regs.getXReg .X16).toBitVec.setWidth w.bits = va)
    (h17 : (s₂.regs.getXReg .X17).toBitVec.setWidth w.bits = vb)
    (hrc : (s₂.regs.getXReg rc).toBitVec.setWidth w.bits = vc)
    (hd : XRegOrSp.reg d ∉ armScratch) (hrcS : XRegOrSp.reg rc ∉ armScratch)
    (hdm : s₂.dmem = s.dmem) (hkeep : ∀ r, r ∉ armScratch → get s₂ r = get s r) :
    _root_.Program.wp
      (if isLeft then
        [ins (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst w.bits)), ins (.LSLV (zr .X16 w) (zr .X16 w) (zr rc w)),
         ins (.SUB_s (zr d w) (xzr w) (sh rc)), ins (.LSRV (zr .X17 w) (zr .X17 w) (zr d w)),
         ins (.ORR_s (zr d w) (zr .X16 w) (sh .X17)), ins (.CSEL (zr d w) (zr .X16 w) (zr d w) .EQ)]
       else
        [ins (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst w.bits)), ins (.LSRV (zr .X17 w) (zr .X17 w) (zr rc w)),
         ins (.SUB_s (zr d w) (xzr w) (sh rc)), ins (.LSLV (zr .X16 w) (zr .X16 w) (zr d w)),
         ins (.ORR_s (zr d w) (zr .X17 w) (sh .X16)), ins (.CSEL (zr d w) (zr .X17 w) (zr d w) .EQ)])
      (fun s' =>
        GprHoldsZ (armMach.getGpr s' (.reg d)) w.bits
          (if isLeft then ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits
           else ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNZCV)
      (fun _ _ => False) s₂ := by
  have hw64 : w.bits ≤ 64 := by cases w <;> decide
  have ⟨hd16, hd17⟩ := xreg_ne_scratch_of_not_mem hd
  have ⟨hrc16, hrc17⟩ := xreg_ne_scratch_of_not_mem hrcS
  cases isLeft <;> dsimp only [Bool.false_eq_true, ↓reduceIte] <;>
    refine armWp_cons (armAndsShiftMask_wp w rc s₂ hrc) fun s₃ ⟨st, hstEq, hst⟩ => ?_ <;>
    subst hstEq
  · refine armWp_cons (armShiftV_wp false w .X17 .X17 rc _) fun s₄ hs₄ => ?_
    refine armWp_cons (armSubNegDir_wp w d rc s₄) fun s₅ hs₅ => ?_
    refine armWp_cons (armShiftV_wp true w .X16 .X16 d s₅) fun s₆ hs₆ => ?_
    refine armWp_cons (armOrrDir_wp w d .X17 .X16 s₆) fun s₇ hs₇ => ?_
    refine armWp_mono (armCselDir_wp w d .X17 d .EQ s₇) fun s₈ hs₈ => ?_
    subst hs₈ hs₇ hs₆ hs₅ hs₄
    refine armFunnelRes_finish false d va vb vc hst
      (fun heq => by
        have hc0 : vc.toNat % w.bits = 0 := decide_eq_true_eq.mp (hst.symm.trans heq)
        simp only [CondCode.interp] at heq
        simp [heq, hc0, BitVec.setWidth_setWidth_of_le _ hw64, BitVec.ushiftRight_eq,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hd17, Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17, h17, hrc])
      (fun hne hc0 => by
        simp only [CondCode.interp] at hne ⊢
        simp only [hne, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_setWidth_of_le _ hw64,
          BitVec.setWidth_eq, BitVec.ushiftRight_eq, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hd16, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hd17,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17, Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc17.symm, h16, h17, hrc,
          neg_mod_eq vc hc0, BitVec.or_comm])
      (fun hw => by subst hw; simp [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq])
      hdm fun r hr => ?_
    · have hr' : r ≠ .reg d ∧ r ∉ armScratch := ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1,
        get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2]; exact hkeep r hr'.2
  · refine armWp_cons (armShiftV_wp true w .X16 .X16 rc _) fun s₄ hs₄ => ?_
    refine armWp_cons (armSubNegDir_wp w d rc s₄) fun s₅ hs₅ => ?_
    refine armWp_cons (armShiftV_wp false w .X17 .X17 d s₅) fun s₆ hs₆ => ?_
    refine armWp_cons (armOrrDir_wp w d .X16 .X17 s₆) fun s₇ hs₇ => ?_
    refine armWp_mono (armCselDir_wp w d .X16 d .EQ s₇) fun s₈ hs₈ => ?_
    subst hs₈ hs₇ hs₆ hs₅ hs₄
    refine armFunnelRes_finish true d va vb vc hst
      (fun heq => by
        have hc0 : vc.toNat % w.bits = 0 := decide_eq_true_eq.mp (hst.symm.trans heq)
        simp only [CondCode.interp] at heq
        simp [heq, hc0, BitVec.setWidth_setWidth_of_le _ hw64,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hd16, Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17.symm, h16, hrc])
      (fun hne hc0 => by
        simp only [CondCode.interp] at hne ⊢
        simp only [hne, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_setWidth_of_le _ hw64,
          BitVec.setWidth_eq, BitVec.ushiftRight_eq, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hd16, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hd17,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17, Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc16.symm, h16, h17, hrc, neg_mod_eq vc hc0])
      (fun hw => by subst hw; simp [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq])
      hdm fun r hr => ?_
    · have hr' : r ≠ .reg d ∧ r ∉ armScratch := ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2,
        get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1]; exact hkeep r hr'.2

private theorem armFunnelGprB_wp [Host] (w : RegWidth)
    (isLeft : Bool) (d ra rb rc : XReg) (va vb vc : BitVec w.bits) {s s₂ : MachineData}
    (hra : (s₂.regs.getXReg ra).toBitVec.setWidth w.bits = va)
    (hrb : (s₂.regs.getXReg rb).toBitVec.setWidth w.bits = vb)
    (hrc : (s₂.regs.getXReg rc).toBitVec.setWidth w.bits = vc)
    (hneA : ra ≠ .X17) (hrbS : XRegOrSp.reg rb ∉ armScratch) (hrcS : XRegOrSp.reg rc ∉ armScratch)
    (hdm : s₂.dmem = s.dmem) (hkeep : ∀ r, r ∉ armScratch → get s₂ r = get s r) :
    _root_.Program.wp
      (if isLeft then
        [ins (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst w.bits)), ins (.SUB_s (zr .X17 w) (xzr w) (sh rc)),
         ins (.LSRV (zr .X17 w) (zr rb w) (zr .X17 w)), ins (.LSLV (zr .X16 w) (zr ra w) (zr rc w)),
         ins (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)), ins (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)]
       else
        [ins (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst w.bits)), ins (.SUB_s (zr .X17 w) (xzr w) (sh rc)),
         ins (.LSLV (zr .X17 w) (zr ra w) (zr .X17 w)), ins (.LSRV (zr .X16 w) (zr rb w) (zr rc w)),
         ins (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)), ins (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)])
      (fun s' =>
        GprHoldsZ (armMach.getGpr s' (.reg d)) w.bits
          (if isLeft then ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits
           else ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNZCV)
      (fun _ _ => False) s₂ := by
  have hw64 : w.bits ≤ 64 := by cases w <;> decide
  have hrb17 := (xreg_ne_scratch_of_not_mem hrbS).2
  have hrc17 := (xreg_ne_scratch_of_not_mem hrcS).2
  cases isLeft <;> dsimp only [Bool.false_eq_true, ↓reduceIte] <;>
    refine armWp_cons (armAndsShiftMask_wp w rc s₂ hrc) fun s₃ ⟨st, hstEq, hst⟩ => ?_ <;>
    subst hstEq
  · refine armWp_cons (armSubNegDir_wp w .X17 rc _) fun s₄ hs₄ => ?_
    refine armWp_cons (armShiftV_wp true w .X17 ra .X17 s₄) fun s₅ hs₅ => ?_
    refine armWp_cons (armShiftV_wp false w .X16 rb rc s₅) fun s₆ hs₆ => ?_
    refine armWp_cons (armOrrDir_wp w .X17 .X16 .X17 s₆) fun s₇ hs₇ => ?_
    refine armWp_mono (armCselDir_wp w d .X16 .X17 .EQ s₇) fun s₈ hs₈ => ?_
    subst hs₈ hs₇ hs₆ hs₅ hs₄
    refine armFunnelRes_finish false d va vb vc hst
      (fun heq => by
        have hc0 : vc.toNat % w.bits = 0 := decide_eq_true_eq.mp (hst.symm.trans heq)
        simp only [CondCode.interp] at heq
        simp [heq, hc0, BitVec.setWidth_setWidth_of_le _ hw64, BitVec.ushiftRight_eq,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrb17.symm, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc17.symm, hrb, hrc])
      (fun hne hc0 => by
        simp only [CondCode.interp] at hne ⊢
        simp only [hne, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_setWidth_of_le _ hw64,
          BitVec.setWidth_eq, BitVec.ushiftRight_eq, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneA.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrb17.symm, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc17.symm,
          hra, hrb, hrc, neg_mod_eq vc hc0, BitVec.or_comm])
      (fun hw => by subst hw; simp [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq])
      hdm fun r hr => ?_
    · have hr' : r ≠ .reg d ∧ r ∉ armScratch := ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2]; exact hkeep r hr'.2
  · refine armWp_cons (armSubNegDir_wp w .X17 rc _) fun s₄ hs₄ => ?_
    refine armWp_cons (armShiftV_wp false w .X17 rb .X17 s₄) fun s₅ hs₅ => ?_
    refine armWp_cons (armShiftV_wp true w .X16 ra rc s₅) fun s₆ hs₆ => ?_
    refine armWp_cons (armOrrDir_wp w .X17 .X16 .X17 s₆) fun s₇ hs₇ => ?_
    refine armWp_mono (armCselDir_wp w d .X16 .X17 .EQ s₇) fun s₈ hs₈ => ?_
    subst hs₈ hs₇ hs₆ hs₅ hs₄
    refine armFunnelRes_finish true d va vb vc hst
      (fun heq => by
        have hc0 : vc.toNat % w.bits = 0 := decide_eq_true_eq.mp (hst.symm.trans heq)
        simp only [CondCode.interp] at heq
        simp [heq, hc0, BitVec.setWidth_setWidth_of_le _ hw64,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneA.symm, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc17.symm, hra, hrc])
      (fun hne hc0 => by
        simp only [CondCode.interp] at hne ⊢
        simp only [hne, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_setWidth_of_le _ hw64,
          BitVec.setWidth_eq, BitVec.ushiftRight_eq, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hneA.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrb17.symm, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc17.symm,
          hra, hrb, hrc, neg_mod_eq vc hc0])
      (fun hw => by subst hw; simp [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq])
      hdm fun r hr => ?_
    · have hr' : r ≠ .reg d ∧ r ∉ armScratch := ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2]; exact hkeep r hr'.2

private theorem armFunnelImmB_wp [Host] (w : RegWidth)
    (isLeft : Bool) (d ra rc : XReg) (va vb vc : BitVec w.bits) {s s₂ : MachineData}
    (hra : (s₂.regs.getXReg ra).toBitVec.setWidth w.bits = va)
    (h17 : (s₂.regs.getXReg .X17).toBitVec.setWidth w.bits = vb)
    (hrc : (s₂.regs.getXReg rc).toBitVec.setWidth w.bits = vc)
    (hraS : XRegOrSp.reg ra ∉ armScratch) (hrcS : XRegOrSp.reg rc ∉ armScratch)
    (hdm : s₂.dmem = s.dmem) (hkeep : ∀ r, r ∉ armScratch → get s₂ r = get s r) :
    _root_.Program.wp
      (if isLeft then
        [ins (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst w.bits)), ins (.SUB_s (zr .X16 w) (xzr w) (sh rc)),
         ins (.LSRV (zr .X17 w) (zr .X17 w) (zr .X16 w)), ins (.LSLV (zr .X16 w) (zr ra w) (zr rc w)),
         ins (.ORR_s (zr .X17 w) (zr .X16 w) (sh .X17)), ins (.CSEL (zr d w) (zr .X16 w) (zr .X17 w) .EQ)]
       else
        [ins (.ANDS_i (xzr w) (zr rc w) (armShiftMaskConst w.bits)), ins (.SUB_s (zr .X16 w) (xzr w) (sh rc)),
         ins (.LSLV (zr .X16 w) (zr ra w) (zr .X16 w)), ins (.LSRV (zr .X17 w) (zr .X17 w) (zr rc w)),
         ins (.ORR_s (zr .X16 w) (zr .X17 w) (sh .X16)), ins (.CSEL (zr d w) (zr .X17 w) (zr .X16 w) .EQ)])
      (fun s' =>
        GprHoldsZ (armMach.getGpr s' (.reg d)) w.bits
          (if isLeft then ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits
           else ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNZCV)
      (fun _ _ => False) s₂ := by
  have hw64 : w.bits ≤ 64 := by cases w <;> decide
  have ⟨hra16, hra17⟩ := xreg_ne_scratch_of_not_mem hraS
  have ⟨hrc16, hrc17⟩ := xreg_ne_scratch_of_not_mem hrcS
  cases isLeft <;> dsimp only [Bool.false_eq_true, ↓reduceIte] <;>
    refine armWp_cons (armAndsShiftMask_wp w rc s₂ hrc) fun s₃ ⟨st, hstEq, hst⟩ => ?_ <;>
    subst hstEq
  · refine armWp_cons (armSubNegDir_wp w .X16 rc _) fun s₄ hs₄ => ?_
    refine armWp_cons (armShiftV_wp true w .X16 ra .X16 s₄) fun s₅ hs₅ => ?_
    refine armWp_cons (armShiftV_wp false w .X17 .X17 rc s₅) fun s₆ hs₆ => ?_
    refine armWp_cons (armOrrDir_wp w .X16 .X17 .X16 s₆) fun s₇ hs₇ => ?_
    refine armWp_mono (armCselDir_wp w d .X17 .X16 .EQ s₇) fun s₈ hs₈ => ?_
    subst hs₈ hs₇ hs₆ hs₅ hs₄
    refine armFunnelRes_finish false d va vb vc hst
      (fun heq => by
        have hc0 : vc.toNat % w.bits = 0 := decide_eq_true_eq.mp (hst.symm.trans heq)
        simp only [CondCode.interp] at heq
        simp [heq, hc0, BitVec.setWidth_setWidth_of_le _ hw64, BitVec.ushiftRight_eq,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc16.symm, h17, hrc])
      (fun hne hc0 => by
        simp only [CondCode.interp] at hne ⊢
        simp only [hne, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_setWidth_of_le _ hw64,
          BitVec.setWidth_eq, BitVec.ushiftRight_eq, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17, Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hra16.symm, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc16.symm,
          hra, h17, hrc, neg_mod_eq vc hc0, BitVec.or_comm])
      (fun hw => by subst hw; simp [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq])
      hdm fun r hr => ?_
    · have hr' : r ≠ .reg d ∧ r ∉ armScratch := ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1]; exact hkeep r hr'.2
  · refine armWp_cons (armSubNegDir_wp w .X16 rc _) fun s₄ hs₄ => ?_
    refine armWp_cons (armShiftV_wp false w .X17 .X17 .X16 s₄) fun s₅ hs₅ => ?_
    refine armWp_cons (armShiftV_wp true w .X16 ra rc s₅) fun s₆ hs₆ => ?_
    refine armWp_cons (armOrrDir_wp w .X17 .X16 .X17 s₆) fun s₇ hs₇ => ?_
    refine armWp_mono (armCselDir_wp w d .X16 .X17 .EQ s₇) fun s₈ hs₈ => ?_
    subst hs₈ hs₇ hs₆ hs₅ hs₄
    refine armFunnelRes_finish true d va vb vc hst
      (fun heq => by
        have hc0 : vc.toNat % w.bits = 0 := decide_eq_true_eq.mp (hst.symm.trans heq)
        simp only [CondCode.interp] at heq
        simp [heq, hc0, BitVec.setWidth_setWidth_of_le _ hw64,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17.symm, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hra17.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hra16.symm, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc17.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc16.symm, hra, hrc])
      (fun hne hc0 => by
        simp only [CondCode.interp] at hne ⊢
        simp only [hne, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_setWidth_of_le _ hw64,
          BitVec.setWidth_eq, BitVec.ushiftRight_eq, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ x16_ne_x17, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hra16.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hra17.symm, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc17.symm,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrc16.symm, hra, h17, hrc, neg_mod_eq vc hc0])
      (fun hw => by subst hw; simp [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq])
      hdm fun r hr => ?_
    · have hr' : r ≠ .reg d ∧ r ∉ armScratch := ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
      rw [get_wr_of_ne _ d _ r hr'.1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1, get_wr_of_ne _ .X17 _ r (ne_of_not_mem_armScratch hr'.2).2, get_wr_of_ne _ .X16 _ r (ne_of_not_mem_armScratch hr'.2).1]; exact hkeep r hr'.2

theorem armFunnelOp_wp [Host] (isLeft : Bool) {n : Nat}
    (pa pb pc : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {va vb vc : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armFunnelOpIns isLeft n pa pb pc d = some (c, clob))
    (hd : XRegOrSp.reg d ∉ armScratch)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hgc : ∀ r ∈ pc.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hpc : armMach.PArgHolds s (.bits n) pc vc) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n
        (if isLeft then ((va ++ vb) <<< (vc.toNat % n)).extractLsb' n n
         else ((va ++ vb) >>> (vc.toNat % n)).extractLsb' 0 n) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armFunnelOpIns] at hc; split at hc
  · simp at hc
  · rename_i hok
    have hn' : n = 32 ∨ n = 64 := by cases h32 : (n == 32) <;> cases h64 : (n == 64) <;> simp_all
    have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl <;> decide
    have hn_pos : 0 < n := by rcases hn' with rfl | rfl <;> decide
    simp only [bind, Option.bind_eq_some_iff] at hc
    rcases hc with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, htail⟩
    cases pc with
    | vec vr => exact vr.elim
    | imm cc =>
      simp only [Machine.PArgHolds] at hpc; subst hpc
      cases isLeft
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at htail
        rcases htail with ⟨rfl, rfl⟩
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
        rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
        have hklt : cc.toNat % n < n := Nat.mod_lt _ hn_pos
        rcases hn' with rfl | rfl
        · refine armWrDst_after_scratch hn64 d
            (armDirFallsTo_wp (Q := fun s' => s' = wr s₂ d ((((va ++ vb) >>> (cc.toNat % 32)).extractLsb' 0 32).setWidth 64))
              fun {_} p next jmp Q hk => by
                rw [show armWidthOf 32 = .W32 from rfl]; simp only [t_step_simp]
                dsimp only [RegWidth.bits, MemWidth.bits]
                rw [Nat.mod_eq_of_lt hklt, hra, hrb, evalEXTR_fshr (Or.inl rfl) va vb hklt]
                exact hk _ rfl) hd₂ hfr₂
            (by simp) (fun _ => rfl)
        · refine armWrDst_after_scratch hn64 d
            (armDirFallsTo_wp (Q := fun s' => s' = wr s₂ d (((va ++ vb) >>> (cc.toNat % 64)).extractLsb' 0 64))
              fun {_} p next jmp Q hk => by
                rw [show armWidthOf 64 = .W64 from rfl]; simp only [t_step_simp]
                dsimp only [RegWidth.bits, MemWidth.bits]; simp only [BitVec.setWidth_eq] at hra hrb ⊢
                rw [Nat.mod_eq_of_lt hklt, hra, hrb, evalEXTR_fshr (Or.inr rfl) va vb hklt]
                exact hk _ rfl) hd₂ hfr₂
            (by simp) (fun h => by cases h)
      · simp only [↓reduceIte] at htail
        split at htail
        · rename_i hk0; simp only [beq_iff_eq] at hk0
          rcases Option.some.inj htail with ⟨rfl, rfl⟩
          rw [emitClean_append, emitClean_cons, emitClean_nil]
          refine armWp_append (armArgIn_wp hn64 ha hpa) ?_
          rintro s₁ ⟨hra, hd₁, _, hfr₁⟩
          have hfr₁' : armMach.Frame armCondReads s s₁ armScratch [] maskNone :=
            hfr₁.weaken (fun x hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact x16_mem_scratch)
              (fun v => v.elim) rfl
          refine armWrDst_after_scratch hn64 d (armMovRegDir_wp (armWidthOf n) d ra s₁)
            hd₁ hfr₁' ?_ ?_
          · rw [hk0, fshl_zero, BitVec.setWidth_setWidth_of_le _ hn64]
            rcases hn' with rfl | rfl
            · exact hra
            · simp only [armWidthOf, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq] at hra ⊢
              exact hra
          · intro hn32; subst hn32
            rw [hk0, fshl_zero]; simpa [armWidthOf] using congrArg (BitVec.setWidth 64) hra
        · rename_i hkn0; simp only [beq_iff_eq] at hkn0
          rcases Option.some.inj htail with ⟨rfl, rfl⟩
          rw [emitClean_append, emitClean_cons, emitClean_nil]
          refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
          rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
          have hklt : cc.toNat % n < n := Nat.mod_lt _ hn_pos
          have hnk : n - cc.toNat % n < n := by omega
          have hne0 : n - cc.toNat % n ≠ 0 := by omega
          have hsub : n - (n - cc.toNat % n) = cc.toNat % n := by omega
          rcases hn' with rfl | rfl
          · refine armWrDst_after_scratch hn64 d
              (armDirFallsTo_wp (Q := fun s' => s' = wr s₂ d ((((va ++ vb) <<< (cc.toNat % 32)).extractLsb' 32 32).setWidth 64))
                fun {_} p next jmp Q hk => by
                  rw [show armWidthOf 32 = .W32 from rfl]; simp only [t_step_simp]
                  dsimp only [RegWidth.bits, MemWidth.bits]
                  rw [Nat.mod_eq_of_lt hnk, beq_false_of_ne hne0, ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
                    hsub, hra, hrb, evalEXTR_fshl (Or.inl rfl) va vb hklt]; exact hk _ rfl) hd₂ hfr₂
              (by simp) (fun _ => rfl)
          · refine armWrDst_after_scratch hn64 d
              (armDirFallsTo_wp (Q := fun s' => s' = wr s₂ d (((va ++ vb) <<< (cc.toNat % 64)).extractLsb' 64 64))
                fun {_} p next jmp Q hk => by
                  rw [show armWidthOf 64 = .W64 from rfl]; simp only [t_step_simp]
                  dsimp only [RegWidth.bits, MemWidth.bits]; simp only [BitVec.setWidth_eq] at hra hrb ⊢
                  rw [Nat.mod_eq_of_lt hnk, beq_false_of_ne hne0, ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
                    hsub, hra, hrb, evalEXTR_fshl (Or.inr rfl) va vb hklt]; exact hk _ rfl) hd₂ hfr₂
              (by simp) (fun h => by cases h)
    | gpr r => cases r with | SP => simp at htail | reg rc =>
      rcases Option.some.inj htail with ⟨rfl, rfl⟩
      have hrcS : XRegOrSp.reg rc ∉ armScratch := hgc (.reg rc) (by simp [PArg.gprs])
      have hrc0 : (s.regs.getXReg rc).toBitVec.setWidth n = vc := by simpa [Machine.PArgHolds, GprHolds, get_reg] using hpc.2
      simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
      refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
      rintro s₂ ⟨hra, hrb, hneA, _, hd₂, _, hfr₂⟩
      have hrc₂ : (s₂.regs.getXReg rc).toBitVec.setWidth n = vc := by
        have h := hfr₂.1 (.reg rc) hrcS; simpa [get_reg] using (congrArg (BitVec.setWidth n) h).trans hrc0
      have hkeep₂ : ∀ r, r ∉ armScratch → get s₂ r = get s r := fun r hr => hfr₂.1 r hr
      cases pa with
      | vec vr => exact vr.elim
      | imm _ => cases pb with
        | vec vr => exact vr.elim
        | imm _ =>
          simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at ha hb
          rcases ha with ⟨rfl, rfl⟩; rcases hb with ⟨rfl, rfl⟩
          simp only [emitClean_ite, emitClean_cons, emitClean_nil]
          rcases hn' with rfl | rfl <;>
            exact armFunnelImmImm_wp _ isLeft d rc va vb vc hra hrb hrc₂ hd hrcS hd₂ hkeep₂
        | gpr rb' => cases rb' with | SP => simp [armArgInIns] at hb | reg x =>
          simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at hb; rcases hb with ⟨rfl, rfl⟩
          simp only [emitClean_ite, emitClean_cons, emitClean_nil]
          rcases hn' with rfl | rfl <;>
            exact armFunnelGprB_wp _ isLeft d ra x rc va vb vc hra hrb hrc₂ hneA
              (hgb (.reg x) (by simp [PArg.gprs])) hrcS hd₂ hkeep₂
      | gpr ra' => cases ra' with | SP => simp [armArgInIns] at ha | reg xa => cases pb with
        | vec vr => exact vr.elim
        | imm _ =>
          simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at ha hb
          rcases ha with ⟨rfl, rfl⟩; rcases hb with ⟨rfl, rfl⟩
          simp only [emitClean_ite, emitClean_cons, emitClean_nil]
          rcases hn' with rfl | rfl <;>
            exact armFunnelImmB_wp _ isLeft d xa rc va vb vc hra hrb hrc₂
              (hga (.reg xa) (by simp [PArg.gprs])) hrcS hd₂ hkeep₂
        | gpr rb' => cases rb' with | SP => simp [armArgInIns] at hb | reg xb =>
          simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at hb; rcases hb with ⟨rfl, rfl⟩
          simp only [emitClean_ite, emitClean_cons, emitClean_nil]
          rcases hn' with rfl | rfl <;>
            exact armFunnelGprB_wp _ isLeft d ra xb rc va vb vc hra hrb hrc₂ hneA
              (hgb (.reg xb) (by simp [PArg.gprs])) hrcS hd₂ hkeep₂

/-! ## 2. Top-level `armOp_spec` and `armGprSpec` -/

private theorem mem_tupArgGprs_head {t : Ty} {ts : List Ty} {r : Reg}
    {pa : PArg Reg Empty ArmCond t} {xs : Tup (PArg Reg Empty ArmCond) ts}
    (hr : r ∈ pa.gprs) : r ∈ tupArgGprs (ts := t :: ts) (pa, xs) := by
  cases pa with
  | gpr _ => simp [PArg.gprs] at hr; simp [tupArgGprs, hr]
  | vec v => exact v.elim
  | imm _ | flag _ => simp [PArg.gprs] at hr

private theorem mem_tupArgGprs_tail {t : Ty} {ts : List Ty} {r : Reg}
    {pa : PArg Reg Empty ArmCond t} {xs : Tup (PArg Reg Empty ArmCond) ts}
    (hr : r ∈ tupArgGprs xs) : r ∈ tupArgGprs (ts := t :: ts) (pa, xs) := by
  cases pa with
  | gpr _ => simp [tupArgGprs] at hr ⊢; exact Or.inr hr
  | vec v => exact v.elim
  | imm _ | flag _ => simp [tupArgGprs] at hr ⊢; exact hr

private theorem arg2_gprs {t u : Ty} {pa : PArg Reg Empty ArmCond t} {pb : PArg Reg Empty ArmCond u}
    (h : ∀ r ∈ tupArgGprs (R := Reg) (V := Empty) (C := ArmCond) (ts := [t, u]) (pa, pb, ()), r ∉ armScratch) :
    (∀ r ∈ pa.gprs, r ∉ armScratch) ∧ (∀ r ∈ pb.gprs, r ∉ armScratch) :=
  ⟨fun _ hr => h _ (mem_tupArgGprs_head (ts := [u]) hr),
   fun _ hr => h _ (mem_tupArgGprs_tail (ts := [u]) (mem_tupArgGprs_head (ts := []) hr))⟩

private theorem arg3_gprs {t u v : Ty}
    {pa : PArg Reg Empty ArmCond t} {pb : PArg Reg Empty ArmCond u} {pc : PArg Reg Empty ArmCond v}
    (h : ∀ r ∈ tupArgGprs (R := Reg) (V := Empty) (C := ArmCond) (ts := [t, u, v]) (pa, pb, pc, ()), r ∉ armScratch) :
    (∀ r ∈ pa.gprs, r ∉ armScratch) ∧ (∀ r ∈ pb.gprs, r ∉ armScratch) ∧ (∀ r ∈ pc.gprs, r ∉ armScratch) :=
  ⟨fun _ hr => h _ (mem_tupArgGprs_head (ts := [u, v]) hr),
   fun _ hr => h _ (mem_tupArgGprs_tail (ts := [u, v]) (mem_tupArgGprs_head (ts := [v]) hr)),
   fun _ hr => h _ (mem_tupArgGprs_tail (ts := [u, v]) (mem_tupArgGprs_tail (ts := [v]) (mem_tupArgGprs_head (ts := []) hr)))⟩

private theorem dst1_gpr {t : Ty} {d : XReg}
    (h : ∀ r ∈ tupDstGprs (R := Reg) (V := Empty) (C := ArmCond) (ts := [t]) ((.gpr (.reg d)), ()), r ∉ armScratch) :
    XRegOrSp.reg d ∉ armScratch :=
  h (.reg d) (by simp [tupDstGprs])

private theorem armOp_bool_fallsTo {h : Host} {k : Nat} {sig : List Ty}
    {code : OpCode sig [.bool]} {pas : Tup (PArg Reg Empty ArmCond) sig}
    {vs : Tup Val sig} {P : Tup Val [.bool] → Prop} {s : MachineData} {post : MachineState → Prop}
    {r : XReg} {c : List Instr} {clob : FlagMask}
    (hc : armBoolOpIns code pas r = some (c, clob))
    (hdsts : ∀ x ∈ tupDstGprs (R := Reg) (V := Empty) (C := ArmCond) (ts := [.bool]) (.gpr (.reg r), ()), x ∉ armScratch)
    (hargs : ∀ x ∈ tupArgGprs pas, x ∉ armScratch)
    (hrel : TRel (armMach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    armMach.FallsTo armCondReads h k (emitClean c)
      (tupDstGprs (R := Reg) (V := Empty) (C := ArmCond) (ts := [.bool]) (.gpr (.reg r), ()) ++ armScratch)
      [] clob s (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') (.gpr (.reg r), ()) rvs) ∧ armMach.mem s' = armMach.mem s) post :=
  armFallsTo_of_wp (armWp_mono (armBoolOp_wp code pas r hc (dst1_gpr hdsts) hargs hrel hwp) fun _ ⟨hp, hm, hfr⟩ => ⟨⟨hp, hm⟩, hfr⟩)

private theorem armOp_fallsTo_bits {h : Host} {k n : Nat} {d : XReg} {c : List Directive}
    {clob : FlagMask} {s : MachineData} {val : BitVec n} {P : Tup Val [.bits n] → Prop}
    {post : MachineState → Prop}
    (hwp : @Program.wp h c (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n val ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s)
    (hP : P (val, ())) :
    armMach.FallsTo armCondReads h k c
      (tupDstGprs (R := Reg) (V := Empty) (C := ArmCond) (ts := [.bits n]) (.gpr (.reg d), ()) ++ armScratch)
      [] clob s (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') (.gpr (.reg d), ()) rvs) ∧
      armMach.mem s' = armMach.mem s) post :=
  armFallsTo_of_wp (armWp_mono hwp fun _ ⟨hg, hm, hfr⟩ =>
    ⟨⟨⟨(val, ()), hP, .cons hg.holds .nil⟩, hm⟩, by simpa [tupDstGprs] using hfr⟩)

private theorem armOp_zero32_fallsTo {h : Host} {k : Nat} {d : XReg} {c : List Directive}
    {clob : FlagMask} {s : MachineData} {val : BitVec 32} {P : Tup Val [.bits 32] → Prop}
    {post : MachineState → Prop}
    (hwp : @Program.wp h c (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) 32 val ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] clob) (fun _ _ => False) s)
    (hP : P (val, ())) :
    armMach.FallsTo armCondReads h k c (.reg d :: armScratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ armMach.getGpr s' (.reg d) = rv.setWidth 64) ∧
        armMach.mem s' = armMach.mem s) post :=
  armFallsTo_of_wp (armWp_mono hwp fun _ ⟨hg, hm, hfr⟩ =>
    ⟨⟨⟨val, hP, hg.zero32⟩, hm⟩, hfr⟩)

theorem armOp_spec {h : Host} {k : Nat} {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg Empty ArmCond) sig} {dsts : Tup (PDst Reg Empty ArmCond) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask} {vs : Tup Val sig}
    {P : Tup Val rs → Prop} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armOp code pas dsts vh = some (c, clob))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ armScratch)
    (hdsts : ∀ r ∈ tupDstGprs dsts, r ∉ armScratch)
    (hrel : TRel (armMach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    armMach.FallsTo armCondReads h k c (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (armMach.PDstHolds s') dsts rvs) ∧ armMach.mem s' = armMach.mem s)
      post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  cases code with
  | copy t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    · dsimp only [armOpIns] at hc; exact armOp_bool_fallsTo hc hdsts hargs hrel hwp
    · rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; dsimp only [armOpIns] at hc; split at hc
      · rename_i hn; simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
        exact armOp_fallsTo_bits (armCopyBits_wp hn _ hc (trel1_inv hrel)) hwp
      · cases hc
  | «and» t | «or» t | xor t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    · dsimp only [armOpIns] at hc; exact armOp_bool_fallsTo hc hdsts hargs hrel hwp
    · dsimp only [armOpIns] at hc; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      exact armOp_fallsTo_bits (armBinOp_wp _ pa pb _ hc hga hgb hpa hpb) hwp
  | add t | sub t | mul t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    dsimp only [armOpIns] at hc; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    exact armOp_fallsTo_bits (armBinOp_wp _ pa pb _ hc hga hgb hpa hpb) hwp
  | «not» t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    · dsimp only [armOpIns] at hc; exact armOp_bool_fallsTo hc hdsts hargs hrel hwp
    · rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      exact armOp_fallsTo_bits (armNotOp_wp pa _ hc (trel1_inv hrel)) hwp
  | bitcast t u htu =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try cases u
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rename_i m n; have hmn : m = n := htu; subst hmn
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; dsimp only [armOpIns] at hc; split at hc
    · rename_i hok; simp only [Bool.and_self, List.contains_eq_mem, decide_eq_true_eq] at hok
      exact armOp_fallsTo_bits (armCopyBits_wp hok _ hc (trel1_inv hrel)) (by simpa [OpCode.wp, toBits, ofBits] using hwp)
    · cases hc
  | zext m n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; exact armOp_fallsTo_bits (armZextOp_wp pa _ hc (trel1_inv hrel) hwp.1) hwp.2
  | sext m n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; exact armOp_fallsTo_bits (armSextOp_wp pa _ hc (trel1_inv hrel) hwp.1) hwp.2
  | trunc m n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; exact armOp_fallsTo_bits (armTruncOp_wp pa _ hc (trel1_inv hrel) hwp.1) hwp.2
  | ofBool n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨b, ⟨⟩⟩; exact armOp_fallsTo_bits (armOfBoolOp_wp pa _ hc (trel1_inv hrel)) hwp
  | shl t | lshr t | ashr t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    dsimp only [armOpIns] at hc; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    exact armOp_fallsTo_bits (armShiftOp_wp _ pa pb _ hc hga hgb hpa hpb) hwp
  | neg t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; exact armOp_fallsTo_bits (armNegOp_wp pa _ hc (trel1_inv hrel)) hwp
  | rotl t | rotr t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    dsimp only [armOpIns] at hc; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    exact armOp_fallsTo_bits (armRotOp_wp _ pa pb _ hc hga hgb hpa hpb) hwp
  | udiv n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    have hdiv := armDivRemOp_wp .udiv pa pb _ hc (dst1_gpr hdsts) hga hgb hpa hpb (fun h => by rcases h with h | h <;> cases h)
    simp only [armDivEval, beq_false_of_ne hwp.1, Bool.false_eq_true, ↓reduceIte] at hdiv; exact armOp_fallsTo_bits hdiv hwp.2
  | udiv0 n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    have hdiv := armDivRemOp_wp .udiv pa pb _ hc (dst1_gpr hdsts) hga hgb hpa hpb (fun h => by rcases h with h | h <;> cases h)
    have heq : armDivEval .udiv va vb = if vb = 0 then 0 else va / vb := by by_cases h : vb = 0 <;> simp [armDivEval, h]
    exact armOp_fallsTo_bits (heq ▸ hdiv) hwp
  | sdiv n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    have hb0 : vb ≠ 0 := by simp only [OpCode.wp, sdivDefined, Bool.and_eq_true, bne_iff_ne] at hwp; exact hwp.1.1
    have hdiv := armDivRemOp_wp .sdiv pa pb _ hc (dst1_gpr hdsts) hga hgb hpa hpb (fun h => by rcases h with h | h <;> cases h)
    simp only [armDivEval, beq_false_of_ne hb0, Bool.false_eq_true, ↓reduceIte] at hdiv; exact armOp_fallsTo_bits hdiv hwp.2
  | sdiv0 n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    have hdiv := armDivRemOp_wp .sdiv pa pb _ hc (dst1_gpr hdsts) hga hgb hpa hpb (fun h => by rcases h with h | h <;> cases h)
    have heq : armDivEval .sdiv va vb = if vb = 0 then 0 else va.sdiv vb := by by_cases h : vb = 0 <;> simp [armDivEval, h]
    exact armOp_fallsTo_bits (heq ▸ hdiv) hwp
  | urem n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    exact armOp_fallsTo_bits (armDivRemOp_wp .urem pa pb _ hc (dst1_gpr hdsts) hga hgb hpa hpb (fun _ => hwp.1)) hwp.2
  | srem n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    have hb0 : vb ≠ 0 := by simp only [OpCode.wp, sdivDefined, Bool.and_eq_true, bne_iff_ne] at hwp; exact hwp.1.1
    exact armOp_fallsTo_bits (armDivRemOp_wp .srem pa pb _ hc (dst1_gpr hdsts) hga hgb hpa hpb (fun _ => hb0)) hwp.2
  | bswap t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rename_i m
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; dsimp only [armOpIns] at hc; split at hc
    · cases hc
    · rename_i hok
      have hm : m = 16 ∨ m = 32 ∨ m = 64 := by cases h : ([16, 32, 64].contains m) <;> simp_all
      rcases hm with rfl | rfl | rfl <;> exact armOp_fallsTo_bits (armBswap_wp pa _ hc (trel1_inv hrel)) hwp
  | clz n | cls n | rbit n | ctz n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; dsimp only [armOpIns] at hc
    refine armOp_fallsTo_bits ?_ hwp
    first | exact armBitOp_wp .clz pa _ hc (trel1_inv hrel) | exact armBitOp_wp .cls pa _ hc (trel1_inv hrel)
          | exact armBitOp_wp .rbit pa _ hc (trel1_inv hrel) | exact armBitOp_wp .ctz pa _ hc (trel1_inv hrel)
  | cmp o t m hm =>
    subst hm; cases t <;> try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; rcases dsts with ⟨dst, ⟨⟩⟩
    have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    exact armFallsTo_of_wp (armWp_mono (armCmpOp_wp o pa pb dst hc hga hgb hdsts hpa hpb)
      fun _ ⟨hdst, hdm, hfr⟩ => ⟨⟨⟨(o.evalBits va vb, ()), hwp, .cons hdst .nil⟩, hdm⟩, hfr⟩)
  | select t =>
    rcases dsts with ⟨⟨r | _⟩ | _ | vr, ⟨⟩⟩ <;> try exact False.elim vr.elim
    all_goals try cases t
    all_goals try (dsimp only [armOpIns] at hc; cases hc)
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases vs with ⟨vc, va, vb, ⟨⟩⟩
    have ⟨hpc, hpa, hpb⟩ := trel3_inv hrel; have ⟨hgc, hga, hgb⟩ := arg3_gprs hargs
    exact armOp_fallsTo_bits (armSelectOp_wp pc pa pb _ hc hga hgb hgc hpc hpa hpb) hwp
  | addc n =>
    rcases pas with ⟨pa, pb, cin, ⟨⟩⟩; rcases vs with ⟨va, vb, vcin, ⟨⟩⟩
    rcases dsts with ⟨⟨r | _⟩ | _ | ⟨⟩, cout, ⟨⟩⟩ <;> try (dsimp only [armOpIns] at hc; cases hc)
    have ⟨hpa, hpb, hpc⟩ := trel3_inv hrel; have ⟨hga, hgb, hgc⟩ := arg3_gprs hargs
    exact armFallsTo_of_wp (armWp_mono (armAddcOp_wp pa pb cin _ cout vh hc hga hgb hgc hpa hpb hpc)
      fun _ ⟨⟨rvs, hr, htr⟩, hdm, hfr⟩ => ⟨⟨⟨rvs, hr ▸ hwp, htr⟩, hdm⟩, hfr⟩)
  | subb n =>
    rcases pas with ⟨pa, pb, bin, ⟨⟩⟩; rcases vs with ⟨va, vb, vbin, ⟨⟩⟩
    rcases dsts with ⟨⟨r | _⟩ | _ | ⟨⟩, bout, ⟨⟩⟩ <;> try (dsimp only [armOpIns] at hc; cases hc)
    have ⟨hpa, hpb, hpc⟩ := trel3_inv hrel; have ⟨hga, hgb, hgc⟩ := arg3_gprs hargs
    exact armFallsTo_of_wp (armWp_mono (armSubbOp_wp pa pb bin _ bout vh hc hga hgb hgc hpa hpb hpc)
      fun _ ⟨⟨rvs, hr, htr⟩, hdm, hfr⟩ => ⟨⟨⟨rvs, hr ▸ hwp, htr⟩, hdm⟩, hfr⟩)
  | umulw n | smulw n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases dsts with ⟨⟨dlo | _⟩ | _ | ⟨⟩, d1, ⟨⟩⟩ <;> try (dsimp only [armOpIns] at hc; cases hc)
    rcases d1 with ⟨dhi | _⟩ | _ | ⟨⟩ <;> try (dsimp only [armOpIns] at hc; cases hc)
    dsimp only [armOpIns] at hc
    have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
    have hd : XRegOrSp.reg dlo ∉ armScratch ∧ XRegOrSp.reg dhi ∉ armScratch :=
      ⟨hdsts (.reg dlo) (by simp [tupDstGprs]), hdsts (.reg dhi) (by simp [tupDstGprs])⟩
    have hmul := armMulwOp_wp _ pa pb dlo dhi hc hga hgb hd hpa hpb
    first | simp only [Bool.false_eq_true, ↓reduceIte] at hmul | simp only [↓reduceIte] at hmul
    exact armFallsTo_of_wp (armWp_mono hmul fun _ ⟨⟨rvs, hr, htr⟩, hdm, hfr⟩ => ⟨⟨⟨rvs, hr ▸ hwp, htr⟩, hdm⟩, hfr⟩)
  | fshl n | fshr n =>
    rcases dsts with ⟨⟨r | _⟩ | _ | ⟨⟩, ⟨⟩⟩ <;> try (dsimp only [armOpIns] at hc; cases hc)
    dsimp only [armOpIns] at hc; rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases vs with ⟨va, vb, vc, ⟨⟩⟩
    have ⟨hpa, hpb, hpc⟩ := trel3_inv hrel; have ⟨hga, hgb, hgc⟩ := arg3_gprs hargs
    have hf := armFunnelOp_wp _ pa pb pc _ hc (dst1_gpr hdsts) hga hgb hgc hpa hpb hpc
    first | simp only [↓reduceIte] at hf | simp only [Bool.false_eq_true, ↓reduceIte] at hf
    exact armOp_fallsTo_bits hf hwp
  | ternlog _ _ | popcnt _ | blend _ _ _ | mkpair _ _ | unpair _ _
  | shufd _ _ | shufb _ | alignr _ _ | blendw _ _ | sha256rnds2 | sha256msg1 | sha256msg2
  | fadd _ | fsub _ | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _
  | fcmp _ _ _ _ | fptoui _ _ | fptosi _ _ | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    dsimp only [armOpIns] at hc; cases hc

theorem armOp_zero32 {h : Host} {k : Nat} {sig : List Ty} {code : OpCode sig [.bits 32]}
    {pas : Tup (PArg Reg Empty ArmCond) sig} {dsts : Tup (PDst Reg Empty ArmCond) [.bits 32]}
    {rd : Reg} {vh : VariantHint} {c : List Directive} {clob : FlagMask} {vs : Tup Val sig}
    {P : Tup Val [.bits 32] → Prop} {s : MachineData} {post : MachineState → Prop}
    (_hz : armGpr.zeroUpper32Op code pas dsts = true)
    (hc_in : armGpr.op code pas dsts vh = some (c, clob))
    (hdst : dsts = (.gpr rd, ()))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ armScratch)
    (hrd : rd ∉ armScratch)
    (hrel : TRel (armMach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ armMach.getGpr s' rd = rv.setWidth 64) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  subst hdst
  cases rd with
  | SP =>
    dsimp only [armGpr, armZeroUpper32Op] at _hz
    cases _hz
  | reg d =>
    obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
    have _ := hrd
    cases code with
    | copy _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armCopyBits_wp (by decide) d hc (trel1_inv hrel)) hwp
    | bitcast t u htu =>
      cases t <;> try (dsimp only [armOpIns] at hc; cases hc)
      rename_i m
      have hm : m = 32 := htu
      subst hm
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armCopyBits_wp (by decide) d hc (trel1_inv hrel))
        (by simpa [OpCode.wp, toBits, ofBits] using hwp)
    | zext m _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armZextOp_wp pa d hc (trel1_inv hrel) hwp.1) hwp.2
    | sext m _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armSextOp_wp pa d hc (trel1_inv hrel) hwp.1) hwp.2
    | trunc m _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armTruncOp_wp pa d hc (trel1_inv hrel) hwp.1) hwp.2
    | ofBool _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨b, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armOfBoolOp_wp pa d hc (trel1_inv hrel)) hwp
    | «and» _ | «or» _ | xor _ | add _ | sub _ | mul _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      exact armOp_zero32_fallsTo (armBinOp_wp _ pa pb d hc hga hgb hpa hpb) hwp
    | «not» _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armNotOp_wp pa d hc (trel1_inv hrel)) hwp
    | neg _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armNegOp_wp pa d hc (trel1_inv hrel)) hwp
    | shl _ | lshr _ | ashr _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      exact armOp_zero32_fallsTo (armShiftOp_wp _ pa pb d hc hga hgb hpa hpb) hwp
    | rotl _ | rotr _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      exact armOp_zero32_fallsTo (armRotOp_wp _ pa pb d hc hga hgb hpa hpb) hwp
    | udiv _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      have hdiv := armDivRemOp_wp .udiv pa pb d hc hrd hga hgb hpa hpb
        (fun h => by rcases h with h | h <;> cases h)
      simp only [armDivEval, beq_false_of_ne hwp.1, Bool.false_eq_true, ↓reduceIte] at hdiv
      exact armOp_zero32_fallsTo hdiv hwp.2
    | udiv0 _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      have hdiv := armDivRemOp_wp .udiv pa pb d hc hrd hga hgb hpa hpb
        (fun h => by rcases h with h | h <;> cases h)
      have heq : armDivEval .udiv va vb = if vb = 0 then 0 else va / vb := by
        by_cases h : vb = 0 <;> simp [armDivEval, h]
      exact armOp_zero32_fallsTo (heq ▸ hdiv) hwp
    | sdiv _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      have hb0 : vb ≠ 0 := by
        simp only [OpCode.wp, sdivDefined, Bool.and_eq_true, bne_iff_ne] at hwp; exact hwp.1.1
      have hdiv := armDivRemOp_wp .sdiv pa pb d hc hrd hga hgb hpa hpb
        (fun h => by rcases h with h | h <;> cases h)
      simp only [armDivEval, beq_false_of_ne hb0, Bool.false_eq_true, ↓reduceIte] at hdiv
      exact armOp_zero32_fallsTo hdiv hwp.2
    | sdiv0 _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      have hdiv := armDivRemOp_wp .sdiv pa pb d hc hrd hga hgb hpa hpb
        (fun h => by rcases h with h | h <;> cases h)
      have heq : armDivEval .sdiv va vb = if vb = 0 then 0 else va.sdiv vb := by
        by_cases h : vb = 0 <;> simp [armDivEval, h]
      exact armOp_zero32_fallsTo (heq ▸ hdiv) hwp
    | urem _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      exact armOp_zero32_fallsTo
        (armDivRemOp_wp .urem pa pb d hc hrd hga hgb hpa hpb (fun _ => hwp.1)) hwp.2
    | srem _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      have ⟨hpa, hpb⟩ := trel2_inv hrel; have ⟨hga, hgb⟩ := arg2_gprs hargs
      have hb0 : vb ≠ 0 := by
        simp only [OpCode.wp, sdivDefined, Bool.and_eq_true, bne_iff_ne] at hwp; exact hwp.1.1
      exact armOp_zero32_fallsTo
        (armDivRemOp_wp .srem pa pb d hc hrd hga hgb hpa hpb (fun _ => hb0)) hwp.2
    | bswap _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      exact armOp_zero32_fallsTo (armBswap_wp pa d hc (trel1_inv hrel)) hwp
    | clz _ | cls _ | rbit _ | ctz _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      dsimp only [armOpIns] at hc
      refine armOp_zero32_fallsTo ?_ hwp
      first
      | exact armBitOp_wp .clz pa d hc (trel1_inv hrel)
      | exact armBitOp_wp .cls pa d hc (trel1_inv hrel)
      | exact armBitOp_wp .rbit pa d hc (trel1_inv hrel)
      | exact armBitOp_wp .ctz pa d hc (trel1_inv hrel)
    | select _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases vs with ⟨vc, va, vb, ⟨⟩⟩
      have ⟨hpc, hpa, hpb⟩ := trel3_inv hrel; have ⟨hgc, hga, hgb⟩ := arg3_gprs hargs
      exact armOp_zero32_fallsTo (armSelectOp_wp pc pa pb d hc hga hgb hgc hpc hpa hpb) hwp
    | fshl _ | fshr _ =>
      dsimp only [armOpIns] at hc
      rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases vs with ⟨va, vb, vc, ⟨⟩⟩
      have ⟨hpa, hpb, hpc⟩ := trel3_inv hrel; have ⟨hga, hgb, hgc⟩ := arg3_gprs hargs
      have hf := armFunnelOp_wp _ pa pb pc d hc hrd hga hgb hgc hpa hpb hpc
      first
      | simp only [↓reduceIte] at hf
      | simp only [Bool.false_eq_true, ↓reduceIte] at hf
      exact armOp_zero32_fallsTo hf hwp
    | cmp _ t _ hm =>
      cases t <;> cases hm <;> dsimp only [armOpIns] at hc <;> cases hc
    | ternlog _ _ | popcnt _ | blend _ _ _ | shufd _ _ | shufb _ | alignr _ _
    | blendw _ _ | fadd _ | fsub _ | fmul _ | fdiv _ | ffma _
    | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _ | fptoui _ _ | fptosi _ _ =>
      dsimp only [armOpIns] at hc; cases hc

/-- Verified AArch64 scalar `GprTarget` specification (`T9`). -/
theorem armGprSpec : GprTarget armMach armGpr armScratch where
  negCond_reads := armNegCond_reads
  negCond_eval s c := armNegCond_interp c s.status
  clearFlags_spec := @armClearFlags_spec
  mov_spec := @armMov_spec
  movi_spec := @armMovi_spec
  setcc_spec := @armSetcc_spec
  jmp_spec := @armJmp_spec
  jcc_spec := @armJcc_spec
  jnzGpr_spec := @armJnzGpr_spec
  op_spec := @armOp_spec
  load_spec := @armLoad_spec
  store_spec := @armStore_spec
  load_zero32 _ {h k rd a c clob s post v} := @armLoad_zero32 h k rd a c clob v s post
  op_zero32 := @armOp_zero32

/-! ## 3. `armOp_noLab` for downstream `Rega.LabelClean` -/

theorem armOp_noLab {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg Empty ArmCond) sig} {dsts : Tup (PDst Reg Empty ArmCond) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    (hc : armGpr.op code pas dsts vh = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

/-! ## 4. Kernel `rfl` `ParserChecks` against `Kraken.AArch64.Parser` -/

section ParserChecks
open Kraken.AArch64.Parser

theorem parser_moves_branches_rfl :
    ⸨prog|
      adds xzr, xzr, xzr
      add x0, x1, #0
      add sp, x0, #0
      csinc x0, xzr, xzr, ne
      mov x16, sp
      tbnz w16, #0, L_tgt
      b L_tgt
      b.eq L_tgt
    ⸩ =
      armGpr.clearFlags ++ armGpr.mov (.reg .X0) (.reg .X1) ++ armGpr.mov .SP (.reg .X0) ++
        armGpr.setcc (.reg .X0) .eq ++ (armGpr.jnzGpr .SP "L_tgt").1 ++ armGpr.jmp "L_tgt" ++
        armGpr.jcc .eq "L_tgt" := rfl

theorem parser_mem_sp_flag_rfl :
    ⸨prog|
      add x16, sp, #8
      ldr x0, [x16]
      csinc x17, xzr, xzr, ne
      add x16, sp, #16
      strb w17, [x16]
    ⸩ =
      (armGpr.load i64 (.reg .X0) (.baseDisp .SP 8)).elim [] Prod.fst ++
      (armGpr.store .bool (.flag .eq) (.baseDisp .SP 16)).elim [] Prod.fst := rfl

theorem parser_ops_rfl :
    ⸨prog|
      sdiv w0, w1, w2
      udiv w17, w1, w2
      msub w0, w17, w2, w1
      rev16 w0, w1
      rbit x0, x1
      clz x0, x0
      ands wzr, w3, #1
      csel x0, x1, x2, ne
      adcs x0, x1, x2
      csinc x4, xzr, xzr, cc
      sbcs w0, w1, w2
      smaddl x0, w1, w2, xzr
      ubfm x3, x0, #32, #63
      extr x0, x1, x2, #7
    ⸩ =
      (armGpr.op (.sdiv0 32) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.urem 32) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.bswap i16) (.gpr (.reg .X1), ()) (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.ctz 64) (.gpr (.reg .X1), ()) (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.select i64) (.gpr (.reg .X3), .gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.addc 64) (.gpr (.reg .X1), .gpr (.reg .X2), .flag .cs, ()) (.gpr (.reg .X0), .gpr (.reg .X4), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.subb 32) (.gpr (.reg .X1), .gpr (.reg .X2), .flag .cc, ()) (.gpr (.reg .X0), .flag .cc, ()) .default).elim [] Prod.fst ++
      (armGpr.op (.smulw 32) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), .gpr (.reg .X3), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.fshr 64) (.gpr (.reg .X1), .gpr (.reg .X2), .imm 7#64, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst := rfl

theorem parser_opt_c6_rfl :
    ⸨prog|
      movz x0, #42
      movn x0, #0x1234
      movz x0, #0x5678
      movk x0, #0x1234, lsl #32
      movn x0, #0x5678
      movk x0, #0xedc3, lsl #32
      add x0, x1, #0x123, lsl #12
      sub w0, w1, #5, lsl #12
      and w0, w1, #7
      ldr w0, [x1, x2, lsl #2]
      str x0, [x1, x2, lsl #3]
    ⸩ =
      armGpr.movi (.reg .X0) 42#64 ++
      armGpr.movi (.reg .X0) (~~~0x1234#64) ++
      armGpr.movi (.reg .X0) 0x1234_0000_5678#64 ++
      armGpr.movi (.reg .X0) (~~~0x123c_0000_5678#64) ++
      (armGpr.op (.add i64) (.gpr (.reg .X1), .imm 0x123000#64, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.sub i32) (.gpr (.reg .X1), .imm 0x5000#32, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.and i32) (.gpr (.reg .X1), .imm 7#32, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.load i32 (.reg .X0)
        (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 0)).elim [] Prod.fst ++
      (armGpr.store i64 (.gpr (.reg .X0))
        (.baseIdxDisp (.reg .X1) (.reg .X2) .s8 0)).elim [] Prod.fst := rfl

end ParserChecks

end LeanQbe.T.Arm64