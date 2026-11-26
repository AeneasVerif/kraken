module

public import LeanQbe.T.Arm64.IselLemmas30

/-!
# AArch64 Scalar Instruction Selection Proofs — Part 3.1

Weakest-precondition correctness for `armTestOp`, `armSelectOp`, `armAddcOp`, and
`armSubbOp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Bit-test and carry/borrow flag helpers -/

private theorem andi_bit0_mask {rc : BitVec 64} {b : Bool}
    (hb : rc.setWidth 8 = BitVec.ofNat 8 b.toNat) :
    rc.setWidth 32 &&& 1#32 = if b then 1#32 else 0#32 := by
  have hb0 := congrArg (fun z => z.getLsbD 0) hb
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hi0 : i = 0
  · subst hi0; simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth] at hb0 ⊢
    cases b <;> simp_all <;> decide
  · have h0 : (1#32 : BitVec 32).getLsbD i = false :=
      Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega :
              1 ≤ i)))
    cases b <;> simp [BitVec.getLsbD_and, h0]

private theorem ne_of_tstBit0 {rc : BitVec 64} {b : Bool}
    (hb : rc.setWidth 8 = BitVec.ofNat 8 b.toNat) :
    CondCode.NE.interp (StatusFlags.from_result (rc.setWidth 32 &&& 1#32) { c := false, v :=
        false }) = b := by
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
    · rw [show false.toNat = 0 from rfl]
      simp only [Nat.add_zero, ↓reduceIte, Bool.false_eq_true]; omega
    · rw [show true.toNat = 1 from rfl]; simp only [↓reduceIte]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; simp only [h, decide_false, bne_eq_false_iff_eq]
    cases c
    · rw [show false.toNat = 0 from rfl]
      simp only [Nat.add_zero, ↓reduceIte, Bool.false_eq_true]; omega
    · rw [show true.toNat = 1 from rfl]; simp only [↓reduceIte]; omega

private theorem subs_borrow_iff {n : Nat} (a b : BitVec n) :
    (!(StatusFlags.subs (a - b) a b).c) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt; have hp := Nat.two_pow_pos n
  simp only [StatusFlags.subs, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [h, decide_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    rw [show ((2 ^ n - b.toNat + a.toNat : Nat) : Int) = (2 ^ n : Nat) - (b.toNat : Int) + (a.toNat
        : Int) by omega]
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


/-! ## 2. `armTestOp`, `armSelectOp`, `armAddcOp`, and `armSubbOp` WP theorems -/

private theorem armAndsReg_wp [Host] (w : RegWidth) (rx ry : XReg) (s : MachineData) :
    _root_.Program.wp
      [ins (.ANDS_s (xzr w) (zr rx w) (sh ry))]
      (fun s' => s' = { s with
        status := StatusFlags.from_result
          ((s.regs.getXReg rx).toBitVec.setWidth w.bits &&&
            (s.regs.getXReg ry).toBitVec.setWidth w.bits)
          { c := false, v := false } })
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases w <;>
      (simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
         BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
       exact hk _ rfl)

private theorem armAndsZero_wp [Host] (w : RegWidth) (s : MachineData) :
    _root_.Program.wp
      [ins (.ANDS_s (xzr w) (xzr w) { reg := xzr w, amount := 0, shift := .LSL })]
      (fun s' => s' = { s with
        status := StatusFlags.from_result (0#w.bits) { c := false, v := false } })
      (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases w <;>
      (simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
         BitVec.shiftLeft_zero, BitVec.and_self]
       exact hk _ rfl)

private theorem armTestRegImm3264_wp [Host] {n : Nat} (hn' : n = 32 ∨ n = 64)
    (rx : XReg) (va vb vimm : BitVec n) (isSwap : Bool) (tst : List Instr) (s : MachineData)
    (hrx17 : rx ≠ .X17)
    (hvals : if isSwap then va = vimm ∧ vb = (s.regs.getXReg rx).toBitVec.setWidth n
      else va = (s.regs.getXReg rx).toBitVec.setWidth n ∧ vb = vimm)
    (hri : (let w := armWidthOf n; let c64 := vimm.setWidth 64
       if armIsValidLogicalImm w c64 then
         some [armIselInsI (.ANDS_i (xzr w) (zr rx w) (.int64 (Int64.ofBitVec c64)))]
       else if vimm == ~~~0#n then
         some [armIselInsI (.ANDS_s (xzr w) (zr rx w) (sh rx))]
       else if vimm == 0#n then
         some [armIselInsI (.ANDS_s (xzr w) (xzr w) { reg := xzr w, amount := 0, shift := .LSL })]
       else do
         let (cb, ry) ← armArgInIns .X17 (.imm vimm)
         some (cb ++ [armIselInsI (.ANDS_s (xzr w) (zr rx w) (sh ry))])) = some tst) :
    _root_.Program.wp (emitClean tst) (fun sx =>
      ∃ (w : RegWidth) (res : BitVec w.bits),
        sx.status = StatusFlags.from_result res { c := false, v := false } ∧
        (res == 0#w.bits) = ((va &&& vb) == 0#n) ∧
        sx.dmem = s.dmem ∧ armMach.Frame armCondReads s sx armScratch [] maskNZCV)
      (fun _ _ => False) s := by
  have hn64 : n ≤ 64 := by rcases hn' with rfl | rfl <;> decide
  have heqAnd : ((s.regs.getXReg rx).toBitVec.setWidth n &&& vimm) = va &&& vb := by
    cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hvals
    · rw [hvals.1, hvals.2]
    · rw [hvals.1, hvals.2, BitVec.and_comm]
  dsimp only at hri
  split at hri
  · rcases Option.some.inj hri with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armAndsImm_wp (armWidthOf n) rx (vimm.setWidth 64) s) ?_
    rintro sx rfl
    refine ⟨armWidthOf n, _, rfl, ?_, rfl, frame_setStatus _ _⟩
    rcases hn' with rfl | rfl
    · rw [show armWidthOf 32 = .W32 from rfl, RegWidth.bits, MemWidth.bits]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, heqAnd]
    · rw [show armWidthOf 64 = .W64 from rfl, RegWidth.bits, MemWidth.bits]
      simp only [BitVec.setWidth_eq] at heqAnd ⊢; rw [heqAnd]
  · split at hri
    · rename_i hones
      have hone : vimm = ~~~0#n := beq_iff_eq.mp hones
      have hand1 : ∀ z : BitVec n, z &&& ~~~0#n = z := fun z => by
        apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
      have hz0 : (s.regs.getXReg rx).toBitVec.setWidth n =
          (s.regs.getXReg rx).toBitVec.setWidth n &&& vimm := by rw [hone, hand1]
      rcases Option.some.inj hri with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armAndsReg_wp (armWidthOf n) rx rx s) ?_
      rintro sx rfl
      refine ⟨armWidthOf n, _, rfl, ?_, rfl, frame_setStatus _ _⟩
      rcases hn' with rfl | rfl
      · rw [show armWidthOf 32 = .W32 from rfl, RegWidth.bits, MemWidth.bits]
        rw [BitVec.and_self, hz0, heqAnd]
      · rw [show armWidthOf 64 = .W64 from rfl, RegWidth.bits, MemWidth.bits]
        rw [BitVec.and_self]; rw [BitVec.setWidth_eq] at hz0 heqAnd ⊢; rw [hz0, heqAnd]
    · split at hri
      · rename_i hzeros
        have hz : vimm = 0#n := beq_iff_eq.mp hzeros
        rcases Option.some.inj hri with rfl
        simp only [emitClean_cons, emitClean_nil]
        refine armWp_mono (armAndsZero_wp (armWidthOf n) s) ?_
        rintro sx rfl
        refine ⟨armWidthOf n, _, rfl, ?_, rfl, frame_setStatus _ _⟩
        rcases hn' with rfl | rfl
        · rw [show armWidthOf 32 = .W32 from rfl, RegWidth.bits, MemWidth.bits]
          rw [← heqAnd, hz, BitVec.and_zero]
        · rw [show armWidthOf 64 = .W64 from rfl, RegWidth.bits, MemWidth.bits]
          rw [← heqAnd, hz, BitVec.and_zero]
      · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at hri
        rcases hri with ⟨⟨cb, ry⟩, hb, rfl⟩
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append (armArgIn_wp hn64 (v := vimm) hb rfl) ?_
        rintro s₁ ⟨hrb₁, hd₁, _, hfr₁⟩
        have hrx₁ : (s₁.regs.getXReg rx).toBitVec.setWidth n =
            (s.regs.getXReg rx).toBitVec.setWidth n := by
          have := hfr₁.1 (.reg rx) (fun h => hrx17 (by simpa using h))
          simpa [get_reg] using congrArg (BitVec.setWidth n) this
        refine armWp_mono (armStatusScratch_after (armAndsReg_wp (armWidthOf n) rx ry s₁)
          hd₁ (hfr₁.weaken (fun _ h => by simp at h ⊢; exact Or.inr h) (fun v => v.elim) rfl)) ?_
        rintro sx ⟨hreg, hst, hdm, hfr⟩
        refine ⟨armWidthOf n, _, hst, ?_, hdm, hfr⟩
        rcases hn' with rfl | rfl
        · rw [show armWidthOf 32 = .W32 from rfl, RegWidth.bits, MemWidth.bits]
          rw [hrx₁, hrb₁, heqAnd]
        · rw [show armWidthOf 64 = .W64 from rfl, RegWidth.bits, MemWidth.bits]
          simp only [BitVec.setWidth_eq] at hrx₁ hrb₁ heqAnd ⊢; rw [hrx₁, hrb₁, heqAnd]

private theorem armTestRegImm816_wp [Host] {n : Nat} (hn' : n = 8 ∨ n = 16)
    (rx : XReg) (va vb vimm : BitVec n) (isSwap : Bool) (tst : List Instr) (s : MachineData)
    (hrx17 : rx ≠ .X17)
    (hvals : if isSwap then va = vimm ∧ vb = (s.regs.getXReg rx).toBitVec.setWidth n
      else va = (s.regs.getXReg rx).toBitVec.setWidth n ∧ vb = vimm)
    (hri : (let c64 := vimm.setWidth 64
       if armIsValidLogicalImm .W32 c64 then
         some [armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32) (.int64 (Int64.ofBitVec c64)))]
       else if vimm == 0#n then
         some [armIselInsI (.ANDS_s (xzr .W32) (xzr .W32)
           { reg := xzr .W32, amount := 0, shift := .LSL })]
       else
         some (armMovImmI .X17 c64 ++
           [armIselInsI (.ANDS_s (xzr .W32) (zr rx .W32) (sh .X17))])) = some tst) :
    _root_.Program.wp (emitClean tst) (fun sx =>
      ∃ (w : RegWidth) (res : BitVec w.bits),
        sx.status = StatusFlags.from_result res { c := false, v := false } ∧
        (res == 0#w.bits) = ((va &&& vb) == 0#n) ∧
        sx.dmem = s.dmem ∧ armMach.Frame armCondReads s sx armScratch [] maskNZCV)
      (fun _ _ => False) s := by
  have hn32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
  have heqAnd : ((s.regs.getXReg rx).toBitVec.setWidth n &&& vimm) = va &&& vb := by
    cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at hvals
    · rw [hvals.1, hvals.2]
    · rw [hvals.1, hvals.2, BitVec.and_comm]
  dsimp only at hri
  split at hri
  · rcases Option.some.inj hri with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armAndsImm_wp .W32 rx (vimm.setWidth 64) s) ?_
    rintro sx rfl
    refine ⟨.W32, _, rfl, ?_, rfl, frame_setStatus _ _⟩
    have hc32 : (vimm.setWidth 64).setWidth 32 = vimm.setWidth 32 :=
      BitVec.setWidth_setWidth_of_le _ (by decide)
    rw [RegWidth.bits, MemWidth.bits, hc32,
      subword_and_eq_zero hn32 (BitVec.setWidth_setWidth_of_le _ hn32), heqAnd]
  · split at hri
    · rename_i hzeros
      have hz : vimm = 0#n := beq_iff_eq.mp hzeros
      rcases Option.some.inj hri with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armAndsZero_wp .W32 s) ?_
      rintro sx rfl
      refine ⟨.W32, _, rfl, ?_, rfl, frame_setStatus _ _⟩
      rw [RegWidth.bits, MemWidth.bits, ← heqAnd, hz, BitVec.and_zero]
      simp
    · rcases Option.some.inj hri with rfl
      rw [emitClean_append, emitClean_cons, emitClean_nil]
      refine armWp_append (armMovImm_wp .X17 (vimm.setWidth 64) s) ?_
      rintro s₁ rfl
      refine armWp_mono (armStatusScratch_after (s := s)
        (armAndsReg_wp .W32 rx .X17 (wr s .X17 (vimm.setWidth 64)))
        rfl (frame_wr .X17 _ x17_mem_scratch maskNone)) ?_
      rintro sx ⟨_, hst, hdm, hfr⟩
      refine ⟨.W32, _, hst, ?_, hdm, hfr⟩
      simp only [RegWidth.bits, MemWidth.bits,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrx17.symm, Reg64s.getXReg_setXReg_same,
        UInt64.toBitVec_ofBitVec, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
      rw [subword_and_eq_zero hn32 (BitVec.setWidth_setWidth_of_le _ hn32), heqAnd]

private theorem armTestDirect_wp [Host] {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    (pa pb : PArg Reg Empty ArmCond (.bits n)) {va vb : BitVec n}
    {tst : List Instr} {s : MachineData}
    (ht : armTestDirectIns n pa pb = some tst)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean tst) (fun sx =>
      ∃ (w : RegWidth) (res : BitVec w.bits),
        sx.status = StatusFlags.from_result res { c := false, v := false } ∧
        (res == 0#w.bits) = ((va &&& vb) == 0#n) ∧
        sx.dmem = s.dmem ∧ armMach.Frame armCondReads s sx armScratch [] maskNZCV)
      (fun _ _ => False) s := by
  have hn64 := mem_armWidths_le_64 hn
  dsimp only [armTestDirectIns] at ht
  split at ht
  · rename_i hn3264
    have hn' : n = 32 ∨ n = 64 := by simp only [Bool.or_eq_true, beq_iff_eq] at hn3264; exact hn3264
    cases pa with
    | vec vr => exact vr.elim
    | gpr r => cases r with
      | SP => simp at ht
      | reg rx => cases pb with
        | vec vr => exact vr.elim
        | imm cy =>
          have hrx : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
          have hx17 : rx ≠ .X17 :=
            (xreg_ne_scratch_of_not_mem (hga (.reg rx) (by simp [PArg.gprs]))).2
          exact armTestRegImm3264_wp hn' rx va vb cy false tst s hx17 ⟨hrx.symm, hpb.symm⟩ ht
        | gpr r2 => cases r2 with
          | SP => simp at ht
          | reg ry =>
            rcases Option.some.inj ht with rfl
            simp only [emitClean_cons, emitClean_nil]
            have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
            have hrb : (s.regs.getXReg ry).toBitVec.setWidth n = vb := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
            refine armWp_mono (armAndsReg_wp (armWidthOf n) rx ry s) ?_
            rintro sx rfl
            refine ⟨armWidthOf n, _, rfl, ?_, rfl, frame_setStatus _ _⟩
            rcases hn' with rfl | rfl
            · rw [show armWidthOf 32 = .W32 from rfl, RegWidth.bits, MemWidth.bits]
              rw [hra, hrb]
            · rw [show armWidthOf 64 = .W64 from rfl, RegWidth.bits, MemWidth.bits]
              simp only [BitVec.setWidth_eq] at hra hrb ⊢; rw [hra, hrb]
    | imm cx => cases pb with
      | vec vr => exact vr.elim
      | gpr r2 => cases r2 with
        | SP => simp at ht
        | reg ry =>
          have hry : (s.regs.getXReg ry).toBitVec.setWidth n = vb := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
          have hy17 : ry ≠ .X17 :=
            (xreg_ne_scratch_of_not_mem (hgb (.reg ry) (by simp [PArg.gprs]))).2
          exact armTestRegImm3264_wp hn' ry va vb cx true tst s hy17 ⟨hpa.symm, hry.symm⟩ ht
      | imm cy =>
        simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at ht
        rcases ht with ⟨⟨ca, rx⟩, ha, ⟨cb, ry⟩, hb, rfl⟩
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
        rintro s₂ ⟨hra, hrb, _, _, hd₂, _, hfr₂⟩
        refine armWp_mono
          (armStatusScratch_after (armAndsReg_wp (armWidthOf n) rx ry s₂) hd₂ hfr₂) ?_
        rintro sx ⟨_, hst, hdm, hfr⟩
        refine ⟨armWidthOf n, _, hst, ?_, hdm, hfr⟩
        rcases hn' with rfl | rfl
        · rw [show armWidthOf 32 = .W32 from rfl, RegWidth.bits, MemWidth.bits]
          rw [hra, hrb]
        · rw [show armWidthOf 64 = .W64 from rfl, RegWidth.bits, MemWidth.bits]
          simp only [BitVec.setWidth_eq] at hra hrb ⊢; rw [hra, hrb]
  · rename_i hn816
    have hn' : n = 8 ∨ n = 16 := by
      rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> simp at hn816 ⊢
    have hn0 : 0 < n := by rcases hn' with rfl | rfl <;> decide
    have hn32 : n ≤ 32 := by rcases hn' with rfl | rfl <;> decide
    cases pa with
    | vec vr => exact vr.elim
    | gpr r => cases r with
      | SP => simp at ht
      | reg rx => cases pb with
        | vec vr => exact vr.elim
        | imm cy =>
          have hrx : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
          have hx17 : rx ≠ .X17 :=
            (xreg_ne_scratch_of_not_mem (hga (.reg rx) (by simp [PArg.gprs]))).2
          exact armTestRegImm816_wp hn' rx va vb cy false tst s hx17 ⟨hrx.symm, hpb.symm⟩ ht
        | gpr r2 => cases r2 with
          | SP => simp at ht
          | reg ry =>
            rcases Option.some.inj ht with rfl
            simp only [emitClean_cons, emitClean_nil]
            have hra : (s.regs.getXReg rx).toBitVec.setWidth n = va := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
            have hrb : (s.regs.getXReg ry).toBitVec.setWidth n = vb := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
            have hy16 : ry ≠ .X16 :=
              (xreg_ne_scratch_of_not_mem (hgb (.reg ry) (by simp [PArg.gprs]))).1
            refine armWp_cons (armExt32_wp false hn0 hn32 .X16 rx s va hra) ?_
            rintro s₁ rfl
            refine armWp_mono (armStatusScratch_after (s := s)
              (armAndsReg_wp .W32 .X16 ry (wr s .X16 _))
              rfl (frame_wr .X16 _ x16_mem_scratch maskNone)) ?_
            rintro sx ⟨_, hst, hdm, hfr⟩
            refine ⟨.W32, _, hst, ?_, hdm, hfr⟩
            simp only [RegWidth.bits, MemWidth.bits,
              Reg64s.getXReg_setXReg_same, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy16.symm,
              UInt64.toBitVec_ofBitVec, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
              Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_eq]
            have hrb' : (BitVec.setWidth 32 (s.regs.getXReg ry).toBitVec).setWidth n = vb := by
              rw [BitVec.setWidth_setWidth_of_le _ hn32, hrb]
            rw [BitVec.and_comm, subword_and_eq_zero hn32 hrb', BitVec.and_comm]
    | imm cx => cases pb with
      | vec vr => exact vr.elim
      | gpr r2 => cases r2 with
        | SP => simp at ht
        | reg ry =>
          have hry : (s.regs.getXReg ry).toBitVec.setWidth n = vb := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
          have hy17 : ry ≠ .X17 :=
            (xreg_ne_scratch_of_not_mem (hgb (.reg ry) (by simp [PArg.gprs]))).2
          exact armTestRegImm816_wp hn' ry va vb cx true tst s hy17 ⟨hpa.symm, hry.symm⟩ ht
      | imm cy =>
        rcases Option.some.inj ht with rfl
        rw [List.append_assoc, emitClean_append, emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append (armMovImm_wp .X16 (BitVec.setWidth 64 cx) s) ?_
        rintro s₁ rfl
        refine armWp_append (armMovImm_wp .X17 (BitVec.setWidth 64 cy) _) ?_
        rintro s₂ rfl
        have hfr₂ : armMach.Frame armCondReads s
            (wr (wr s .X16 (BitVec.setWidth 64 cx)) .X17 (BitVec.setWidth 64 cy))
            armScratch [] maskNone :=
          armFrame_scratch_trans (frame_wr .X16 _ x16_mem_scratch maskNone)
            (frame_wr .X17 _ x17_mem_scratch maskNone)
        refine armWp_mono (armStatusScratch_after (s := s)
          (armAndsReg_wp .W32 .X16 .X17 _) rfl hfr₂) ?_
        rintro sx ⟨_, hst, hdm, hfr⟩
        refine ⟨.W32, _, hst, ?_, hdm, hfr⟩
        simp only [RegWidth.bits, MemWidth.bits, Reg64s.getXReg_setXReg_of_ne _ _ _ _
            (by decide : XReg.X17 ≠ .X16), Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
        have hwa : (BitVec.setWidth 32 cx).setWidth n = va := by
          rw [BitVec.setWidth_setWidth_of_le _ hn32, BitVec.setWidth_eq, hpa]
        have hcy : cy = vb := hpb
        rw [hcy, subword_and_eq_zero hn32 hwa]

theorem armTestOp_wp [Host] (neg : Bool) {n : Nat}
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (pd : PDst Reg Empty ArmCond .bool)
    {va vb : BitVec n} {c : List Directive} {clob : FlagMask} {s : MachineData}
    (hc0 : armGpr.testOp n neg pa pb pd = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ armScratch)
    (_hd : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp c (fun s' =>
      (armMach.PDstHolds s' .bool pd
        ((if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#n) ∧
        (clob ≠ maskNone →
          (if neg then ArmCond.ne else ArmCond.eq).interp s'.status =
            (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#n)) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (pd.gprs ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  dsimp only [armGpr, armTestOp] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_left _ hr)
  have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_right _ hr)
  dsimp only [armTestOpIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    let want := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#n
    let wantCond : ArmCond := if neg then .ne else .eq
    have finishSpec : ∀ {tst : List Instr},
        _root_.Program.wp (emitClean tst) (fun sx =>
          wantCond.interp sx.status = want ∧ sx.dmem = s.dmem ∧
          armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s →
        (match pd with
          | .gpr (.reg d) => some (tst ++ [armCset64I d wantCond], maskNZCV)
          | .flag cf => if cf == wantCond then some (tst, maskNZCV) else none
          | .gpr .SP | .vec _ => none) = some (ci, clob) →
        _root_.Program.wp (emitClean ci) (fun sy =>
          (armMach.PDstHolds sy .bool pd want ∧
            (clob ≠ maskNone → wantCond.interp sy.status = want)) ∧
          armMach.mem sy = armMach.mem s ∧
          armMach.Frame armCondReads s sy (pd.gprs ++ armScratch) [] clob)
          (fun _ _ => False) s := by
      intro tst htst hfin
      cases pd with
      | vec vr => exact vr.elim
      | flag cf =>
        dsimp only at hfin; split at hfin
        · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
          rcases Option.some.inj hfin with ⟨rfl, rfl⟩
          exact armWp_mono htst fun _ ⟨hcc, hdm, hfr⟩ => ⟨⟨hcc, fun _ => hcc⟩, hdm, hfr⟩
        · cases hfin
      | gpr r => cases r with | SP => cases hfin | reg d =>
        rcases Option.some.inj hfin with ⟨rfl, rfl⟩
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append htst ?_; rintro sx ⟨hcc, hdm, hfr⟩
        refine armWp_mono (armCset64_wp d wantCond sx) ?_; rintro sy rfl
        refine ⟨⟨?_, fun _ => hcc⟩, hdm, armFrame_nzcv fun r hr => ?_⟩
        · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hcc]; cases want <;> rfl
        · have hne : r ≠ .reg d ∧ r ∉ armScratch :=
            ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
          rw [get_wr_of_ne sx d _ r hne.1]; exact hfr.1 r hne.2
    have hdir : ∀ {tst}, armTestDirectIns n pa pb = some tst →
        _root_.Program.wp (emitClean tst) (fun sx =>
          wantCond.interp sx.status = want ∧ sx.dmem = s.dmem ∧
          armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s := by
      intro tst ht
      refine armWp_mono (armTestDirect_wp hn pa pb ht hga hgb hpa hpb) ?_
      rintro sx ⟨w, res, hst, hz, hdm, hfr⟩
      exact ⟨hst ▸ testCond_eq_of_z neg res (va &&& vb) hz, hdm, hfr⟩
    cases pd with
    | vec vr => exact vr.elim
    | flag cf =>
      dsimp only at hc
      by_cases hcond : (cf == if neg then ArmCond.ne else ArmCond.eq) = true
      · simp only [hcond, ↓reduceIte] at hc
        rcases option_none_or_some (armTestDirectIns n pa pb) with hnone | ⟨tst, htst⟩
        · rw [hnone] at hc; cases hc
        · rw [htst] at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
          exact finishSpec (hdir htst) (by dsimp only [wantCond]; simp [hcond])
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hc; cases hc
    | gpr r => cases r with
      | SP => simp at hc
      | reg d =>
        cases pa with
        | vec vr => exact vr.elim
        | imm cx => cases pb with
          | vec vr => exact vr.elim
          | imm cy =>
            have hcx : cx = va := hpa; have hcy : cy = vb := hpb
            simp only [hcx, hcy] at hc
            rcases Option.some.inj hc with ⟨rfl, rfl⟩
            refine armWp_mono (armMovImm_wp d (BitVec.ofNat 64 want.toNat) s) ?_
            rintro sx rfl
            refine ⟨⟨?_, fun hne => absurd rfl hne⟩, rfl, frame_wr d _ List.mem_cons_self maskNone⟩
            have hwant : BitVec.setWidth 8 (BitVec.ofNat 64 want.toNat) =
                BitVec.ofNat 8 want.toNat := by
              generalize (want : Bool) = b; cases b <;> rfl
            simp only [Machine.PDstHolds, GprHolds, get_wr_same]
            exact hwant
          | gpr r2 =>
            rcases option_none_or_some (armTestDirectIns n (.imm cx) (.gpr r2)) with
              hnone | ⟨tst, htst⟩
            · rw [hnone] at hc; cases hc
            · rw [htst] at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
              exact finishSpec (hdir htst) rfl
        | gpr r1 =>
          rcases option_none_or_some (armTestDirectIns n (.gpr r1) pb) with
            hnone | ⟨tst, htst⟩
          · rw [hnone] at hc; cases hc
          · rw [htst] at hc; rcases Option.some.inj hc with ⟨rfl, rfl⟩
            exact finishSpec (hdir htst) rfl

private theorem getRegOrZr_low_xzr (regs : Reg64s) (w : RegWidth) :
    regs.getRegOrZr (.low .XZR w) = 0#w.bits := by
  cases w <;> rfl

private theorem armSelectDir_wp [Host] (op : Nat) (w : RegWidth) (d : XReg)
    (ra rb : XRegOrXzr) (cnd : ArmCond) (s : MachineData) :
    _root_.Program.wp [match op with
        | 0 => ins (.CSEL (zr d w) (.low ra w) (.low rb w) cnd.toKraken)
        | 1 => ins (.CSINC (zr d w) (.low ra w) (.low rb w) cnd.toKraken)
        | _ => ins (.CSINV (zr d w) (.low ra w) (.low rb w) cnd.toKraken)]
      (fun s' => s' = wr s d ((if cnd.interp s.status then s.regs.getRegOrZr (.low ra w)
        else match op with
          | 0 => s.regs.getRegOrZr (.low rb w)
          | 1 => s.regs.getRegOrZr (.low rb w) + 1#w.bits
          | _ => ~~~(s.regs.getRegOrZr (.low rb w))).setWidth 64))
      (fun _ _ => False) s := by
  rcases op with _ | _ | op <;> cases w <;>
    exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
      exact hk _ rfl

private theorem armSelectCond_wp [Host] {n : Nat} (hn : n ∈ [8, 16, 32, 64])
    (cond : ArmCond) (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg)
    {vc : Bool} {va vb : BitVec n} {c : List Instr} {s : MachineData}
    (hc : armSelectCondIns n cond pa pb d = some c) (hpc : cond.interp s.status = vc)
    (hga : ∀ r ∈ pa.gprs, r ∉ armScratch) (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ => False) s := by
  have hn64 := mem_armWidths_le_64 hn
  have hnw := mem_armWidths_le_armWidth hn
  have hnot0 : (~~~0#n) = (-1#n) := by
    rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> decide
  have fallback : (do
        let (ca, ra) ← armArgInIns .X16 pa
        let (cb, rb) ← armArgInIns .X17 pb
        some (ca ++ cb ++ [armIselInsI (.CSEL (zr d (armWidthOf n)) (zr ra (armWidthOf n))
          (zr rb (armWidthOf n)) cond.toKraken)])) = some c →
      _root_.Program.wp (emitClean c) (fun s' =>
        GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ => False) s :=
            by
    intro hfb
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at hfb
    rcases hfb with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, rfl⟩
    simp only [List.append_assoc]; rw [← List.append_assoc ca cb, emitClean_append]
    refine armWp_append (armArgs2_wp hn64 hn64 ha hb hpa hpb hga hgb) ?_
    rintro s₂ ⟨hra, hrb, _, _, hd₂, hst₂, hfr₂⟩
    simp only [emitClean_cons, emitClean_nil]
    refine armWrDst_after_scratch hn64 d
      (armCselDir_wp (armWidthOf n) d ra rb cond.toKraken s₂) hd₂ hfr₂ ?_ ?_
    · rw [show cond.toKraken.interp s₂.status = vc from hst₂ ▸ hpc]
      cases vc <;> simp only [↓reduceIte, Bool.false_eq_true, BitVec.setWidth_setWidth_of_le _ hn64]
      · rw [BitVec.setWidth_setWidth_of_le _ hnw, hrb]
      · rw [BitVec.setWidth_setWidth_of_le _ hnw, hra]
    · intro hn32; subst hn32
      rw [show cond.toKraken.interp s₂.status = vc from hst₂ ▸ hpc,
        show (armWidthOf 32).bits = 32 from rfl]
      cases vc <;> simp only [↓reduceIte, Bool.false_eq_true]
      · rw [hrb]
      · rw [hra]
  have fastRegImm : ∀ (op : Nat) (isSwap : Bool) (rx : XReg) {vr : BitVec n}
      (hrx : (s.regs.getXReg rx).toBitVec.setWidth n = vr)
      (himm : (if isSwap then va else vb) = match op with
        | 0 => 0#n | 1 => 1#n | _ => ~~~0#n)
      (hreg : (if isSwap then vb else va) = vr)
      (hc_eq : c = [match op with
        | 0 => armIselInsI (.CSEL (zr d (armWidthOf n)) (zr rx (armWidthOf n)) (xzr (armWidthOf n))
            (if isSwap then armNegCond cond else cond).toKraken)
        | 1 => armIselInsI (.CSINC (zr d (armWidthOf n)) (zr rx (armWidthOf n)) (xzr (armWidthOf n))
            (if isSwap then armNegCond cond else cond).toKraken)
        | _ => armIselInsI (.CSINV (zr d (armWidthOf n)) (zr rx (armWidthOf n)) (xzr (armWidthOf n))
            (if isSwap then armNegCond cond else cond).toKraken)]),
      _root_.Program.wp (emitClean c) (fun s' =>
        GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
        armMach.mem s' = armMach.mem s ∧
        armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ => False) s :=
            by
    intro op isSwap rx vr hrx himm hreg hceq; subst hceq
    simp only [emitClean_cons, emitClean_nil]
    have hcnd :
        (if isSwap then armNegCond cond else cond).interp s.status = if isSwap then !vc else vc :=
            by
      cases isSwap <;> simp [armNegCond_interp, hpc]
    have hrxw : (s.regs.getRegOrZr (.low (.reg rx) (armWidthOf n))).setWidth n = vr := by
      have h' : s.regs.getRegOrZr (.low (.reg rx) (armWidthOf n)) =
          (s.regs.getXReg rx).toBitVec.setWidth (armWidthOf n).bits := by
        cases armWidthOf n <;>
          (simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take];
           apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi])
      rw [h', BitVec.setWidth_setWidth_of_le _ hnw, hrx]
    have hrx32 :
        s.regs.getRegOrZr (.low (.reg rx) .W32) = (s.regs.getXReg rx).toBitVec.setWidth 32 := by
      simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
    have finishRegImm : ∀ (dir : Directive) (val64 : BitVec 64)
        (hwp : _root_.Program.wp [dir] (fun s' => s' = wr s d val64) (fun _ _ => False) s),
        val64.setWidth n = (if vc then va else vb) →
        (n = 32 → val64 = (if vc then va else vb).setWidth 64) →
        _root_.Program.wp [dir] (fun s' =>
          GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
          armMach.mem s' = armMach.mem s ∧
          armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ =>
            False) s :=
      fun _ _ hwp hv hv32 => armWrDst_of_eq hn64 d hwp hv hv32
    rcases op with _ | _ | op
    · refine finishRegImm _ _
        (armSelectDir_wp 0 (armWidthOf n) d (.reg rx) .XZR (if isSwap then armNegCond cond else
            cond) s) ?_ ?_
      · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] at himm hreg ⊢
        all_goals first
          | rw [hrxw, hreg]
          | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
             simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
      · intro hn32; subst hn32
        rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
            Bool.not_false] at himm hreg ⊢ <;>
          first | rw [hrx, hreg] | (rw [himm]; try decide)
    · refine finishRegImm _ _
        (armSelectDir_wp 1 (armWidthOf n) d (.reg rx) .XZR (if isSwap then armNegCond cond else
            cond) s) ?_ ?_
      · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] at himm hreg ⊢
        all_goals first
          | rw [hrxw, hreg]
          | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
             simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
      · intro hn32; subst hn32
        rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
            Bool.not_false] at himm hreg ⊢ <;>
          first | rw [hrx, hreg] | (rw [himm]; try decide)
    · refine finishRegImm _ _
        (armSelectDir_wp (op + 2) (armWidthOf n) d (.reg rx) .XZR
          (if isSwap then armNegCond cond else cond) s) ?_ ?_
      · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] at himm hreg ⊢
        all_goals first
          | rw [hrxw, hreg]
          | (rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;> rw [himm] <;>
             simp only [armWidthOf, RegWidth.bits, MemWidth.bits] <;> try decide)
      · intro hn32; subst hn32
        rw [show armWidthOf 32 = .W32 from rfl, hcnd, hrx32, getRegOrZr_low_xzr]
        cases isSwap <;> cases vc <;>
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true,
            Bool.not_false] at himm hreg ⊢ <;>
          first | rw [hrx, hreg] | (rw [himm]; try decide)
  cases pa with
  | vec vr => exact vr.elim
  | imm ca => cases pb with
    | vec vr => exact vr.elim
    | gpr r => cases r with
      | SP => dsimp only [armSelectCondIns] at hc; simp [armArgInIns] at hc
      | reg rb =>
        have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
        have hca : ca = va := hpa
        dsimp only [armSelectCondIns] at hc
        by_cases hc0 : ca == 0#n
        · simp only [hc0, ↓reduceIte] at hc; rcases Option.some.inj hc with rfl
          exact fastRegImm 0 true rb hrb (hca.symm.trans (beq_iff_eq.mp hc0)) rfl rfl
        · by_cases hc1 : ca == 1#n
          · simp only [hc0, hc1, Bool.false_eq_true, ↓reduceIte] at hc
            rcases Option.some.inj hc with rfl
            exact fastRegImm 1 true rb hrb (hca.symm.trans (beq_iff_eq.mp hc1)) rfl rfl
          · by_cases hcn1 : ca == ~~~0#n
            · simp only [hc0, hc1, hcn1, Bool.false_eq_true, ↓reduceIte] at hc
              rcases Option.some.inj hc with rfl
              exact fastRegImm 2 true rb hrb (hca.symm.trans (beq_iff_eq.mp hcn1)) rfl rfl
            · simp only [hc0, hc1, hcn1, Bool.false_eq_true, ↓reduceIte, bind,
                Option.bind_eq_some_iff,
                Option.some.injEq] at hc
              rcases hc with ⟨⟨ca', ra'⟩, ha, rfl⟩
              exact fallback (by rw [ha]; dsimp only [armArgInIns]; simp)
    | imm cb =>
      have hca : ca = va := hpa; have hcb : cb = vb := hpb
      dsimp only [armSelectCondIns] at hc
      by_cases heq : ca == cb
      · simp only [heq, ↓reduceIte] at hc; rcases Option.some.inj hc with rfl
        have hcae : ca = vb := (beq_iff_eq.mp heq).trans hcb
        have hv : va = vb := hca.symm.trans hcae
        rw [hcae]; simpa [hv] using armImmPool_wp hn64 d s vb
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hc
        have fastImmImm : ∀ (isInv flip : Bool),
            (va = if isInv then (if flip then ~~~0#n else 0#n) else (if flip then 1#n else 0#n)) →
            (vb = if isInv then (if flip then 0#n else ~~~0#n) else (if flip then 0#n else 1#n)) →
            c = [if isInv then
                armIselInsI (.CSINV (zr d (armWidthOf n)) (xzr (armWidthOf n)) (xzr (armWidthOf n))
                  (if flip then armNegCond cond else cond).toKraken)
              else
                armIselInsI (.CSINC (zr d (armWidthOf n)) (xzr (armWidthOf n)) (xzr (armWidthOf n))
                  (if flip then armNegCond cond else cond).toKraken)] →
            _root_.Program.wp (emitClean c) (fun s' =>
              GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
              armMach.mem s' = armMach.mem s ∧
              armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ =>
                False) s := by
          intro isInv flip hva hvb hceq; subst hceq; simp only [emitClean_cons, emitClean_nil]
          have hcnd :
              (if flip then armNegCond cond else cond).interp s.status = if flip then !vc else vc :=
                  by
            cases flip <;> simp [armNegCond_interp, hpc]
          have finishImmImm : ∀ (dir : Directive) (val64 : BitVec 64)
              (hwp : _root_.Program.wp [dir] (fun s' => s' = wr s d val64) (fun _ _ => False) s),
              val64.setWidth n = (if vc then va else vb) →
              (n = 32 → val64 = (if vc then va else vb).setWidth 64) →
              _root_.Program.wp [dir] (fun s' =>
                GprHoldsZ (armMach.getGpr s' (.reg d)) n (if vc then va else vb) ∧
                armMach.mem s' = armMach.mem s ∧
                armMach.Frame armCondReads s s' (.reg d :: armScratch) [] maskNone) (fun _ _ =>
                  False) s :=
            fun _ _ hwp hv hv32 => armWrDst_of_eq hn64 d hwp hv hv32
          cases isInv
          · refine finishImmImm _ _
              (armSelectDir_wp 1 (armWidthOf n) d .XZR .XZR (if flip then armNegCond cond else cond)
                  s) ?_ ?_
            · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
              rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                cases flip <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
                  armWidthOf, RegWidth.bits, MemWidth.bits] <;>
                first | (rw [hva]; decide) | (rw [hvb]; decide)
            · intro hn32; subst hn32
              rw [show armWidthOf 32 = .W32 from rfl, hcnd, getRegOrZr_low_xzr]
              cases flip <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
                  RegWidth.bits, MemWidth.bits] <;>
                first | (rw [hva]; decide) | (rw [hvb]; decide)
          · refine finishImmImm _ _
              (armSelectDir_wp 2 (armWidthOf n) d .XZR .XZR (if flip then armNegCond cond else cond)
                  s) ?_ ?_
            · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd, getRegOrZr_low_xzr]
              rcases mem_armWidths hn with rfl | rfl | rfl | rfl <;>
                cases flip <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
                  armWidthOf, RegWidth.bits, MemWidth.bits] <;>
                first | (rw [hva]; decide) | (rw [hvb]; decide)
            · intro hn32; subst hn32
              rw [show armWidthOf 32 = .W32 from rfl, hcnd, getRegOrZr_low_xzr]
              cases flip <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
                  RegWidth.bits, MemWidth.bits] <;>
                first | (rw [hva]; decide) | (rw [hvb]; decide)
        by_cases h10 : (ca == 1#n && cb == 0#n) = true
        · simp only [h10, ↓reduceIte] at hc; rcases Option.some.inj hc with rfl
          simp only [Bool.and_eq_true, beq_iff_eq] at h10
          exact fastImmImm false true (hca.symm.trans h10.1) (hcb.symm.trans h10.2) rfl
        · simp only [h10, Bool.false_eq_true, ↓reduceIte] at hc
          by_cases h01 : (ca == 0#n && cb == 1#n) = true
          · simp only [h01, ↓reduceIte] at hc; rcases Option.some.inj hc with rfl
            simp only [Bool.and_eq_true, beq_iff_eq] at h01
            exact fastImmImm false false (hca.symm.trans h01.1) (hcb.symm.trans h01.2) rfl
          · simp only [h01, Bool.false_eq_true, ↓reduceIte] at hc
            by_cases hn10 : (ca == ~~~0#n && cb == 0#n) = true
            · simp only [hn10, ↓reduceIte] at hc; rcases Option.some.inj hc with rfl
              simp only [Bool.and_eq_true, beq_iff_eq] at hn10
              exact fastImmImm true true (hca.symm.trans hn10.1) (hcb.symm.trans hn10.2) rfl
            · simp only [hn10, Bool.false_eq_true, ↓reduceIte] at hc
              by_cases h0n1 : (ca == 0#n && cb == ~~~0#n) = true
              · simp only [h0n1, ↓reduceIte] at hc; rcases Option.some.inj hc with rfl
                simp only [Bool.and_eq_true, beq_iff_eq] at h0n1
                exact fastImmImm true false (hca.symm.trans h0n1.1) (hcb.symm.trans h0n1.2) rfl
              · simp only [h0n1, Bool.false_eq_true, ↓reduceIte] at hc
                exact fallback hc
  | gpr r => cases r with
    | SP =>
      dsimp only [armSelectCondIns] at hc
      cases pb <;> simp [armArgInIns] at hc
    | reg ra =>
      have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
      cases pb with
      | vec vr => exact vr.elim
      | gpr _ => dsimp only [armSelectCondIns] at hc; exact fallback hc
      | imm cb =>
        have hcb : cb = vb := hpb
        dsimp only [armSelectCondIns] at hc
        by_cases hc0 : cb == 0#n
        · simp only [hc0, ↓reduceIte] at hc; rcases Option.some.inj hc with rfl
          exact fastRegImm 0 false ra hra (hcb.symm.trans (beq_iff_eq.mp hc0)) rfl rfl
        · by_cases hc1 : cb == 1#n
          · simp only [hc0, hc1, Bool.false_eq_true, ↓reduceIte] at hc
            rcases Option.some.inj hc with rfl
            exact fastRegImm 1 false ra hra (hcb.symm.trans (beq_iff_eq.mp hc1)) rfl rfl
          · by_cases hcn1 : cb == ~~~0#n
            · simp only [hc0, hc1, hcn1, Bool.false_eq_true, ↓reduceIte] at hc
              rcases Option.some.inj hc with rfl
              exact fastRegImm 2 false ra hra (hcb.symm.trans (beq_iff_eq.mp hcn1)) rfl rfl
            · simp only [hc0, hc1, hcn1, Bool.false_eq_true, ↓reduceIte, bind,
                Option.bind_eq_some_iff,
                Option.some.injEq] at hc
              rcases hc with ⟨⟨cb', rb'⟩, hb, rfl⟩
              exact fallback (by rw [hb]; dsimp only [armArgInIns]; simp)

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
    cases pc with
    | vec vr => exact vr.elim
    | imm bv =>
      simp only [Machine.PArgHolds] at hpc; subst hpc
      cases bv
      · simpa using armCopyBits_wp hn d hc hpb
      · simpa using armCopyBits_wp hn d hc hpa
    | flag cond =>
      dsimp only at hc; simp only [bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hc
      rcases hc with ⟨sel, hsel, rfl, rfl⟩
      exact armSelectCond_wp hn cond pa pb d hsel hpc hga hgb hpa hpb
    | gpr r => cases r with | SP => simp at hc | reg rc =>
      dsimp only at hc; simp only [bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hc
      rcases hc with ⟨sel, hsel, rfl, rfl⟩
      have hrc : (s.regs.getXReg rc).toBitVec.setWidth 8 = BitVec.ofNat 8 vc.toNat := by
        simpa [Machine.PArgHolds, GprHolds, get_reg] using hpc
      let st1 := StatusFlags.from_result
        ((s.regs.getXReg rc).toBitVec.setWidth 32 &&& 1#32) { c := false, v := false }
      rw [emitClean_cons]
      refine armWp_cons (armDirFallsTo_wp (Q := fun s' => s' = { s with status := st1 })
        fun {_} p next jmp Q hk => by
          simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_one, RegWidth.bits,
            MemWidth.bits]
          exact hk _ rfl) ?_
      rintro s₁ rfl
      have hpa₁ : armMach.PArgHolds { s with status := st1 } (.bits n) pa va := by
        cases pa with
        | vec vr => exact vr.elim
        | imm _ => exact hpa
        | gpr _ => exact hpa
      have hpb₁ : armMach.PArgHolds { s with status := st1 } (.bits n) pb vb := by
        cases pb with
        | vec vr => exact vr.elim
        | imm _ => exact hpb
        | gpr _ => exact hpb
      have hne1 : ArmCond.ne.interp st1 = vc := ne_of_tstBit0 hrc
      refine armWp_mono (armSelectCond_wp hn .ne pa pb d hsel hne1 hga hgb hpa₁ hpb₁) ?_
      rintro s' ⟨hg, hdm, hfr⟩
      exact ⟨hg, hdm, armFrame_nzcv fun r hr => hfr.1 r hr⟩

private theorem armAndi1Sub_wp [Host] (isSubb : Bool) (rc : XReg) {b : Bool} {s : MachineData}
    (hb : (s.regs.getXReg rc).toBitVec.setWidth 8 = BitVec.ofNat 8 b.toNat) (_hrc16 : rc ≠ .X16) :
    _root_.Program.wp
      [ins (.AND_i (.low (.reg .X16) .W32) (zr rc .W32) (.int64 1)),
       if isSubb then ins (.SUBS_s (xzr .W32) (xzr .W32) (sh .X16))
       else ins (.SUBS_e (xzr .W32) (.low (.reg .X16) .W32) (.imm { imm := .int64 1, shift :=
           .S0 }))]
      (fun s₁ => (∀ r, r ∉ armScratch → get s₁ r = get s r) ∧ s₁.dmem = s.dmem ∧
        (if isSubb then ((!s₁.status.c) = b) else (s₁.status.c = b))) (fun _ _ => False) s := by
  refine armWp_cons (armDirFallsTo_wp (Q := fun s' =>
      s' = wr s .X16 (((s.regs.getXReg rc).toBitVec.setWidth 32 &&& 1#32).setWidth 64))
    fun {_} p next jmp Q hk => by
      simp only [t_step_simp, Int64.toInt_one, RegWidth.bits, MemWidth.bits]; exact hk _ rfl)
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
    refine armWp_mono (armDirFallsTo_wp (d :=
        ins (.SUBS_e (xzr .W32) (.low (.reg .X16) .W32) (.imm { imm := .int64 1, shift := .S0 })))
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
    (hres : (s₃.regs.getXReg d).toBitVec.setWidth n = res)
        (hflag : flagCond.interp s₃.status = cflag)
    (hdm : s₃.dmem = s.dmem) (hkeep : ∀ r, r ∉ (.reg d :: armScratch) → get s₃ r = get s r) :
    _root_.Program.wp post (fun s' =>
      (∃ rvs : Tup Val [.bits n, .bool], rvs = (res, cflag, ()) ∧
        TRel (armMach.PDstHolds s') (as :=
            [.bits n, .bool]) ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout,
              ()) rvs) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s'
        (tupDstGprs (ts :=
            [.bits n, .bool]) ((PDst.gpr (.reg d) : PDst Reg Empty ArmCond (.bits n)), cout,
              ()) ++ armScratch)
        [] maskNZCV) (fun _ _ => False) s₃ := by
  have hn64 : n ≤ 64 := by rcases hn with rfl | rfl <;> decide
  rcases hp with ⟨rfl, rfl⟩ | ⟨dc, hdc, rfl, rfl⟩
  · exact armWp_nil ⟨⟨(res, cflag, ()), rfl, .cons ⟨hn64,
      by simpa [get_reg] using hres⟩ (.cons hflag .nil)⟩, hdm, armFrame_nzcv hkeep⟩
  · refine armWp_mono (armCset64_wp dc flagCond s₃) ?_; rintro s₄ rfl
    refine ⟨⟨(res, cflag, ()), rfl, .cons ?_ (.cons ?_ .nil)⟩, hdm, armFrame_nzcv fun r hr => ?_⟩
    · refine ⟨hn64, ?_⟩
      dsimp only [armMach, get_reg]
      rw [Reg64s.getXReg_setXReg_of_ne s₃.regs dc d _ hdc]
      exact hres
    · change GprHolds
        (get (wr s₃ dc (BitVec.ofNat 64 (flagCond.interp s₃.status).toNat)) (.reg dc)) .bool cflag
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
