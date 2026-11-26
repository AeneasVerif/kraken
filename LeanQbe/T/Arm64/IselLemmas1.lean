module

public import LeanQbe.T.Arm64.Isel
public import LeanQbe.T.OpsLemmas
public import LeanQbe.T.AbiLemmas
public import LeanQbe.T.Logic.MemLemmas

/-!
# AArch64 Scalar Instruction Selection Proofs — Part 1

Core `Program.wp` / `FallsTo` bridge, scratch framing, move/branch/clearFlags/load/store
`GprTarget` proofs (including arbitrary-64-bit displacements, `.SP` unaligned routing via `.X16`,
bit-0 `TBNZ` ignoring upper `.bool` garbage bits, and `.bool .flag` stores), shared bitfield /
division / carry / borrow / byte-swap arithmetic lemmas, and non-`op` `NoLab` theorems.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Framing helpers -/

theorem armFrame_upd_regs {s s' : MachineData} {gClob : List Reg} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r)
    (hflg : fClob = maskAll ∨ fClob = maskNZCV ∧
      (∀ c, FlagMask.disjoint (armCondReads c) maskNZCV = true →
        c.interp s'.status = c.interp s.status) ∨
      s'.status = s.status) :
    armMach.Frame armCondReads s s' gClob [] fClob := by
  refine ⟨hkeep, fun v => v.elim, ?_⟩
  rcases hflg with rfl | ⟨rfl, hnzcv⟩ | hst
  · intro c hdisj
    cases c <;> simp [FlagMask.disjoint, armCondReads, maskAll, maskN, maskZ, maskC, maskV] at hdisj
  · exact hnzcv
  · intro c _; simp [hst]

theorem armFrame_nzcv {s s' : MachineData} {gClob : List Reg}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r) :
    armMach.Frame armCondReads s s' gClob [] maskNZCV :=
  armFrame_upd_regs hkeep (Or.inr (Or.inl ⟨rfl, fun c hdisj => by
    cases c <;>
      simp [FlagMask.disjoint, armCondReads, maskNZCV, maskN, maskZ, maskC, maskV] at hdisj⟩))

theorem armFrame_status_eq {s s' : MachineData} {gClob : List Reg} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r) (hst : s'.status = s.status) :
    armMach.Frame armCondReads s s' gClob [] fClob :=
  armFrame_upd_regs hkeep (Or.inr (Or.inr hst))

theorem xreg_ne_scratch_of_not_mem {x : XReg} (hx : XRegOrSp.reg x ∉ armScratch) :
    x ≠ .X16 ∧ x ≠ .X17 := by
  have ⟨h1, h2⟩ := ne_of_not_mem_armScratch hx
  exact ⟨fun e => h1 (congrArg XRegOrSp.reg e), fun e => h2 (congrArg XRegOrSp.reg e)⟩

theorem frame_wr {s : MachineData} (x : XReg) (v : BitVec 64) {gClob : List Reg}
    (hx : XRegOrSp.reg x ∈ gClob) (fClob : FlagMask) :
    armMach.Frame armCondReads s (wr s x v) gClob [] fClob :=
  armFrame_status_eq (fun r hr => get_wr_of_ne s x v r fun e => hr (e ▸ hx)) rfl

theorem frame_setStatus {s : MachineData} (st : StatusFlags) (gClob : List Reg) :
    armMach.Frame armCondReads s { s with status := st } gClob [] maskNZCV :=
  armFrame_nzcv fun _ _ => rfl

/-! ## 2. Low-level directive `Program.wp` builders & operand materialization -/

@[t_step_simp]
theorem Reg64s_getXReg_setXReg_of_ne' (regs : Reg64s) (a b : XReg) (v : BitVec 64)
    (h : a ≠ b) : (regs.setXReg a v).getXReg b = regs.getXReg b :=
  Reg64s.getXReg_setXReg_of_ne regs a b v h

theorem armCset64_wp [Host] (d : XReg) (c : ArmCond) (s : MachineData) :
    _root_.Program.wp [armCset64 d c]
      (fun s' => s' = wr s d (BitVec.ofNat 64 (c.interp s.status).toNat))
      (fun _ _ => False) s := by
  refine armDirFallsTo_wp (by
    intro _ p next jmp P hk
    simp only [t_step_simp]
    rw [show (armNegCond c).toKraken.interp s.status = !(c.interp s.status) from
      armNegCond_interp c s.status]
    cases hc : c.interp s.status
    · simp only [Bool.not_false, ↓reduceIte, BitVec.setWidth_eq]
      exact hk _ (by simp [wr, hc])
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_eq]
      exact hk _ (by simp [wr, hc]))

private theorem bv64_mask16_eq {k : Nat} (hk : k < 65536) :
    BitVec.ofNat 64 k &&& 0xFFFF#64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,
    show (0xFFFF#64 : BitVec 64).toNat = 2 ^ 16 - 1 from rfl,
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.and_two_pow_sub_one_eq_mod _ 16,
    Nat.mod_eq_of_lt hk]

local macro "close_armMov_wp" hk:ident : tactic =>
  `(tactic| (
    refine armDirFallsTo_wp fun {_} p next jmp P hkP => by
      simp only [t_step_simp]
      rw [Int64.toInt_ofNat_of_lt (by omega : _ < 2 ^ 63), BitVec.ofInt_natCast, bv64_mask16_eq $hk]
      exact hkP _ rfl
  ))

private theorem armMovz_wp [Host] (d : XReg) (k : Nat) (hk : k < 65536) (sh : MovShift .W64)
    (s : MachineData) :
    _root_.Program.wp [ins (w := .W64) (.MOVZ (zr d .W64) (.int64 (Int64.ofNat k)) sh)]
      (fun s' => s' = wr s d (BitVec.ofNat 64 k <<< sh.toNat))
      (fun _ _ => False) s := by
  close_armMov_wp hk

private theorem armMovn_wp [Host] (d : XReg) (k : Nat) (hk : k < 65536) (sh : MovShift .W64)
    (s : MachineData) :
    _root_.Program.wp [ins (w := .W64) (.MOVN (zr d .W64) (.int64 (Int64.ofNat k)) sh)]
      (fun s' => s' = wr s d (~~~(BitVec.ofNat 64 k <<< sh.toNat)))
      (fun _ _ => False) s := by
  close_armMov_wp hk

private theorem armMovk_wp [Host] (d : XReg) (k : Nat) (hk : k < 65536) (sh : MovShift .W64)
    (s : MachineData) :
    _root_.Program.wp [ins (w := .W64) (.MOVK (zr d .W64) (.int64 (Int64.ofNat k)) sh)]
      (fun s' => s' = wr s d
        (((s.regs.getXReg d).toBitVec &&& ~~~(0xFFFF#64 <<< sh.toNat)) |||
          (BitVec.ofNat 64 k <<< sh.toNat)))
      (fun _ _ => False) s := by
  close_armMov_wp hk

private theorem chunk16_lt (n s : Nat) : (n >>> s) &&& 0xFFFF < 65536 := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 16]
  exact Nat.mod_lt _ (by decide)

private theorem bv64_getLsbD_testBit (v : BitVec 64) (j : Nat) :
    v.getLsbD j = v.toNat.testBit j := rfl

private theorem chunk16_getLsbD_eq (v : BitVec 64) (s i : Nat) (hi : i < 64) :
    (BitVec.ofNat 64 ((v.toNat >>> s) &&& 0xFFFF)).getLsbD i =
      if i < 16 ∧ s + i < 64 then v.getLsbD (s + i) else false := by
  rw [BitVec.getLsbD_ofNat, bv64_getLsbD_testBit]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_and, Nat.testBit_shiftRight]
  by_cases hi16 : i < 16
  · have ht : Nat.testBit 0xFFFF i = true := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> decide
    simp only [ht, Bool.and_true, hi16, true_and]
    split
    · rfl
    · rename_i hge
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.isLt
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 64 ≤ s + i)))
  · have hf : Nat.testBit 0xFFFF i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 0xFFFF < 2 ^ 16)
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 16 ≤ i)))
    simp [hf, hi16]

private theorem chunk16_zero_bit {v : BitVec 64} {s j : Nat}
    (hz : (v.toNat >>> s) &&& 0xFFFF = 0) (hj : j < 16) (hsj : s + j < 64) :
    v.getLsbD (s + j) = false := by
  have hbit := congrArg (fun x : BitVec 64 => x.getLsbD j) (congrArg (BitVec.ofNat 64) hz)
  rw [chunk16_getLsbD_eq v s j (by omega)] at hbit
  simpa [hj, hsj] using hbit

private theorem armMovz1_eq {v : BitVec 64} {k : Nat} {sh : MovShift .W64}
    (h : armNonZeroChunks v = [(k, sh)]) :
    k < 65536 ∧ BitVec.ofNat 64 k <<< sh.toNat = v := by
  dsimp only [armNonZeroChunks] at h
  let p0 := v.toNat &&& 0xFFFF
  let p1 := (v.toNat >>> 16) &&& 0xFFFF
  let p2 := (v.toNat >>> 32) &&& 0xFFFF
  let p3 := (v.toNat >>> 48) &&& 0xFFFF
  have hp0 : p0 = (v.toNat >>> 0) &&& 0xFFFF := by simp [p0]
  have hstep : ∀ {k' : Nat} {sh' : MovShift .W64},
      (p0 = k' ∧ sh' = .LSL0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0) ∨
      (p1 = k' ∧ sh' = .LSL16 ∧ p0 = 0 ∧ p2 = 0 ∧ p3 = 0) ∨
      (p2 = k' ∧ sh' = .LSL32 ∧ p0 = 0 ∧ p1 = 0 ∧ p3 = 0) ∨
      (p3 = k' ∧ sh' = .LSL48 ∧ p0 = 0 ∧ p1 = 0 ∧ p2 = 0) →
      k' < 65536 ∧ BitVec.ofNat 64 k' <<< sh'.toNat = v := by
    rintro k' sh' (⟨rfl, rfl, h1, h2, h3⟩ | ⟨rfl, rfl, h0, h2, h3⟩ |
      ⟨rfl, rfl, h0, h1, h3⟩ | ⟨rfl, rfl, h0, h1, h2⟩)
    · refine ⟨hp0 ▸ chunk16_lt v.toNat 0, BitVec.eq_of_getLsbD_eq fun i hi => ?_⟩
      simp only [MovShift.toNat, BitVec.shiftLeft_zero, hp0, chunk16_getLsbD_eq v 0 i hi,
        Nat.zero_add, hi, and_true]
      split
      · rfl
      · rename_i hge
        rcases (by omega : (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 64))
          with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have hz := chunk16_zero_bit (j := i - 16) h1 (by omega) (by omega)
          rw [show 16 + (i - 16) = i by omega] at hz; exact hz.symm
        · have hz := chunk16_zero_bit (j := i - 32) h2 (by omega) (by omega)
          rw [show 32 + (i - 32) = i by omega] at hz; exact hz.symm
        · have hz := chunk16_zero_bit (j := i - 48) h3 (by omega) (by omega)
          rw [show 48 + (i - 48) = i by omega] at hz; exact hz.symm
    · refine ⟨chunk16_lt v.toNat 16, BitVec.eq_of_getLsbD_eq fun i hi => ?_⟩
      simp only [MovShift.toNat, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
      by_cases hge : 16 ≤ i
      · have hnl : decide (i < 16) = false := decide_eq_false (by omega)
        simp only [hnl, Bool.not_false, Bool.true_and]
        rw [chunk16_getLsbD_eq v 16 (i - 16) (by omega)]
        by_cases hlt : i < 32
        · simp [show i - 16 < 16 by omega, show 16 + (i - 16) = i by omega, hi]
        · have hge' : ¬ (i - 16 < 16 ∧ 16 + (i - 16) < 64) := by omega
          simp only [hge', ↓reduceIte]
          rcases (by omega : (32 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 64)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · have hz := chunk16_zero_bit (j := i - 32) h2 (by omega) (by omega)
            rw [show 32 + (i - 32) = i by omega] at hz; exact hz.symm
          · have hz := chunk16_zero_bit (j := i - 48) h3 (by omega) (by omega)
            rw [show 48 + (i - 48) = i by omega] at hz; exact hz.symm
      · have hlt : decide (i < 16) = true := decide_eq_true (by omega)
        simp only [hlt, Bool.not_true, Bool.false_and]
        have hz := chunk16_zero_bit (j := i) (hp0 ▸ h0) (by omega) (by omega)
        simpa using hz.symm
    · refine ⟨chunk16_lt v.toNat 32, BitVec.eq_of_getLsbD_eq fun i hi => ?_⟩
      simp only [MovShift.toNat, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
      by_cases hge : 32 ≤ i
      · have hnl : decide (i < 32) = false := decide_eq_false (by omega)
        simp only [hnl, Bool.not_false, Bool.true_and]
        rw [chunk16_getLsbD_eq v 32 (i - 32) (by omega)]
        by_cases hlt : i < 48
        · simp [show i - 32 < 16 by omega, show 32 + (i - 32) = i by omega, hi]
        · have hge' : ¬ (i - 32 < 16 ∧ 32 + (i - 32) < 64) := by omega
          simp only [hge', ↓reduceIte]
          have hz := chunk16_zero_bit (j := i - 48) h3 (by omega) (by omega)
          rw [show 48 + (i - 48) = i by omega] at hz; exact hz.symm
      · have hlt : decide (i < 32) = true := decide_eq_true (by omega)
        simp only [hlt, Bool.not_true, Bool.false_and]
        rcases (by omega : i < 16 ∨ (16 ≤ i ∧ i < 32)) with hi16 | ⟨ha, hb⟩
        · have hz := chunk16_zero_bit (j := i) (hp0 ▸ h0) (by omega) (by omega)
          simpa using hz.symm
        · have hz := chunk16_zero_bit (j := i - 16) h1 (by omega) (by omega)
          rw [show 16 + (i - 16) = i by omega] at hz; exact hz.symm
    · refine ⟨chunk16_lt v.toNat 48, BitVec.eq_of_getLsbD_eq fun i hi => ?_⟩
      simp only [MovShift.toNat, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
      by_cases hge : 48 ≤ i
      · have hnl : decide (i < 48) = false := decide_eq_false (by omega)
        simp only [hnl, Bool.not_false, Bool.true_and]
        rw [chunk16_getLsbD_eq v 48 (i - 48) (by omega)]
        simp [show i - 48 < 16 by omega, show 48 + (i - 48) = i by omega, hi]
      · have hlt : decide (i < 48) = true := decide_eq_true (by omega)
        simp only [hlt, Bool.not_true, Bool.false_and]
        rcases (by omega : i < 16 ∨ (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48))
          with hi16 | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have hz := chunk16_zero_bit (j := i) (hp0 ▸ h0) (by omega) (by omega)
          simpa using hz.symm
        · have hz := chunk16_zero_bit (j := i - 16) h1 (by omega) (by omega)
          rw [show 16 + (i - 16) = i by omega] at hz; exact hz.symm
        · have hz := chunk16_zero_bit (j := i - 32) h2 (by omega) (by omega)
          rw [show 32 + (i - 32) = i by omega] at hz; exact hz.symm
  by_cases h0 : p0 = 0 <;> by_cases h1 : p1 = 0 <;>
    by_cases h2 : p2 = 0 <;> by_cases h3 : p3 = 0 <;>
    simp only [p0, p1, p2, p3] at h0 h1 h2 h3 <;>
    simp [List.filter_nil, h0, h1, h2, h3] at h
  · rcases h with ⟨rfl, rfl⟩; exact hstep (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h0, h1, h2⟩)))
  · rcases h with ⟨rfl, rfl⟩; exact hstep (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h0, h1, h3⟩)))
  · rcases h with ⟨rfl, rfl⟩; exact hstep (Or.inr (Or.inl ⟨rfl, rfl, h0, h2, h3⟩))
  · rcases h with ⟨rfl, rfl⟩; exact hstep (Or.inl ⟨rfl, rfl, h1, h2, h3⟩)

private theorem movk_pair_bits {v : BitVec 64} {s1 s2 : Nat}
    (hs1 : s1 = 0 ∨ s1 = 16 ∨ s1 = 32 ∨ s1 = 48)
    (hs2 : s2 = 0 ∨ s2 = 16 ∨ s2 = 32 ∨ s2 = 48) (hne : s1 ≠ s2)
    (hz : ∀ s, s ∈ [0, 16, 32, 48] → s ≠ s1 → s ≠ s2 → (v.toNat >>> s) &&& 0xFFFF = 0) :
    ((BitVec.ofNat 64 ((v.toNat >>> s1) &&& 0xFFFF) <<< s1) &&& ~~~(0xFFFF#64 <<< s2)) |||
      (BitVec.ofNat 64 ((v.toNat >>> s2) &&& 0xFFFF) <<< s2) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    hi, decide_true, Bool.true_and]
  have h16_bit : ∀ {j : Nat}, j < 64 → (0xFFFF#64 : BitVec 64).getLsbD j = decide (j < 16) := by
    intro j hj; by_cases hj16 : j < 16
    · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> decide
    · simp only [hj16, decide_false]; exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (by decide : 0xFFFF < 2 ^ 16)
          (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 16 ≤ j)))
  have hcase : ∀ s, (s = 0 ∨ s = 16 ∨ s = 32 ∨ s = 48) →
      (!decide (i < s) && (BitVec.ofNat 64 ((v.toNat >>> s) &&& 0xFFFF)).getLsbD (i - s)) =
        (if s ≤ i ∧ i < s + 16 then v.getLsbD i else false) := by
    intro s _
    by_cases hle : s ≤ i
    · have hnl : decide (i < s) = false := decide_eq_false (by omega)
      simp only [hnl, Bool.not_false, Bool.true_and]
      rw [chunk16_getLsbD_eq v s (i - s) (by omega)]
      by_cases hilt : i < s + 16
      · simp [hle, hilt, show i - s < 16 by omega, show s + (i - s) = i by omega, hi]
      · simp [hle, hilt, show ¬ (i - s < 16) by omega]
    · have hlt : decide (i < s) = true := decide_eq_true (by omega)
      simp [hlt, hle]
  have hmask2 :
      (!(!decide (i < s2) && (0xFFFF#64 : BitVec 64).getLsbD (i - s2))) =
        decide (¬ (s2 ≤ i ∧ i < s2 + 16)) := by
    by_cases hle : s2 ≤ i
    · have hnl : decide (i < s2) = false := decide_eq_false (by omega)
      simp only [hnl, Bool.not_false, Bool.true_and]
      rw [h16_bit (by omega)]
      by_cases hlt : i < s2 + 16
      · simp [hle, hlt, show i - s2 < 16 by omega]
      · simp [hlt, show ¬ (i - s2 < 16) by omega]
    · have hlt : decide (i < s2) = true := decide_eq_true (by omega)
      simp [hlt, hle]
  rw [hcase s1 hs1, hcase s2 hs2, hmask2]
  by_cases hi1 : s1 ≤ i ∧ i < s1 + 16 <;> by_cases hi2 : s2 ≤ i ∧ i < s2 + 16
  · exfalso
    rcases hs1 with rfl | rfl | rfl | rfl <;> rcases hs2 with rfl | rfl | rfl | rfl <;> omega
  · simp [hi1, hi2]
  · simp [hi1, hi2]
  · simp only [hi1, hi2, ↓reduceIte, Bool.false_and, Bool.false_or]
    have hs_mem : ∃ s, s ∈ [0, 16, 32, 48] ∧ s ≤ i ∧ i < s + 16 := by
      rcases (by omega : i < 16 ∨ (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 64))
        with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨0, by simp, by omega, by omega⟩
      · exact ⟨16, by simp, h1, h2⟩
      · exact ⟨32, by simp, h1, h2⟩
      · exact ⟨48, by simp, h1, h2⟩
    rcases hs_mem with ⟨s, hsm, hsl, hsu⟩
    have hns1 : s ≠ s1 := fun e => hi1 ⟨e ▸ hsl, e ▸ hsu⟩
    have hns2 : s ≠ s2 := fun e => hi2 ⟨e ▸ hsl, e ▸ hsu⟩
    have hv0 := chunk16_zero_bit (j := i - s) (hz s hsm hns1 hns2) (by omega) (by omega)
    rw [show s + (i - s) = i by omega] at hv0
    exact hv0.symm

private theorem armMovz2_eq {v : BitVec 64} {k1 k2 : Nat} {sh1 sh2 : MovShift .W64}
    (h : armNonZeroChunks v = [(k1, sh1), (k2, sh2)]) :
    k1 < 65536 ∧ k2 < 65536 ∧
      (((BitVec.ofNat 64 k1 <<< sh1.toNat) &&& ~~~(0xFFFF#64 <<< sh2.toNat)) |||
        (BitVec.ofNat 64 k2 <<< sh2.toNat)) = v := by
  dsimp only [armNonZeroChunks] at h
  let p0 := v.toNat &&& 0xFFFF
  let p1 := (v.toNat >>> 16) &&& 0xFFFF
  let p2 := (v.toNat >>> 32) &&& 0xFFFF
  let p3 := (v.toNat >>> 48) &&& 0xFFFF
  have hp0 : p0 = (v.toNat >>> 0) &&& 0xFFFF := by simp [p0]
  have go : ∀ (sh1' sh2' : MovShift .W64) (s1 s2 : Nat),
      sh1 = sh1' → sh2 = sh2' → sh1'.toNat = s1 → sh2'.toNat = s2 →
      s1 ≠ s2 → (s1 = 0 ∨ s1 = 16 ∨ s1 = 32 ∨ s1 = 48) →
      (s2 = 0 ∨ s2 = 16 ∨ s2 = 32 ∨ s2 = 48) →
      k1 = (v.toNat >>> s1) &&& 0xFFFF → k2 = (v.toNat >>> s2) &&& 0xFFFF →
      (∀ s, s ∈ [0, 16, 32, 48] → s ≠ s1 → s ≠ s2 → (v.toNat >>> s) &&& 0xFFFF = 0) →
      k1 < 65536 ∧ k2 < 65536 ∧
        (((BitVec.ofNat 64 k1 <<< sh1.toNat) &&& ~~~(0xFFFF#64 <<< sh2.toNat)) |||
          (BitVec.ofNat 64 k2 <<< sh2.toNat)) = v := by
    rintro sh1' sh2' s1 s2 rfl rfl rfl rfl hne hs1 hs2 rfl rfl hz
    exact ⟨chunk16_lt _ _, chunk16_lt _ _, movk_pair_bits hs1 hs2 hne hz⟩
  have hz_close : ∀ (s1 s2 : Nat),
      (s1 ≠ 0 → s2 ≠ 0 → p0 = 0) →
      (s1 ≠ 16 → s2 ≠ 16 → p1 = 0) →
      (s1 ≠ 32 → s2 ≠ 32 → p2 = 0) →
      (s1 ≠ 48 → s2 ≠ 48 → p3 = 0) →
      ∀ s, s ∈ [0, 16, 32, 48] → s ≠ s1 → s ≠ s2 → (v.toNat >>> s) &&& 0xFFFF = 0 := by
    intro s1 s2 z0 z1 z2 z3 s hm hn1 hn2
    rcases (by simpa using hm : s = 0 ∨ s = 16 ∨ s = 32 ∨ s = 48) with rfl | rfl | rfl | rfl
    · exact hp0 ▸ z0 hn1.symm hn2.symm
    · exact z1 hn1.symm hn2.symm
    · exact z2 hn1.symm hn2.symm
    · exact z3 hn1.symm hn2.symm
  by_cases h0 : p0 = 0 <;> by_cases h1 : p1 = 0 <;>
    by_cases h2 : p2 = 0 <;> by_cases h3 : p3 = 0 <;>
    simp only [p0, p1, p2, p3] at h0 h1 h2 h3 <;>
    simp [List.filter_nil, h0, h1, h2, h3] at h
  · rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact go .LSL32 .LSL48 32 48 rfl rfl rfl rfl (by decide) (by decide) (by decide)
      rfl rfl (hz_close 32 48 (fun _ _ => h0) (fun _ _ => h1)
        (fun e _ => absurd rfl e) (fun _ e => absurd rfl e))
  · rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact go .LSL16 .LSL48 16 48 rfl rfl rfl rfl (by decide) (by decide) (by decide)
      rfl rfl (hz_close 16 48 (fun _ _ => h0) (fun e _ => absurd rfl e)
        (fun _ _ => h2) (fun _ e => absurd rfl e))
  · rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact go .LSL16 .LSL32 16 32 rfl rfl rfl rfl (by decide) (by decide) (by decide)
      rfl rfl (hz_close 16 32 (fun _ _ => h0) (fun e _ => absurd rfl e)
        (fun _ e => absurd rfl e) (fun _ _ => h3))
  · rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact go .LSL0 .LSL48 0 48 rfl rfl rfl rfl (by decide) (by decide) (by decide)
      hp0 rfl (hz_close 0 48 (fun e _ => absurd rfl e) (fun _ _ => h1)
        (fun _ _ => h2) (fun _ e => absurd rfl e))
  · rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact go .LSL0 .LSL32 0 32 rfl rfl rfl rfl (by decide) (by decide) (by decide)
      hp0 rfl (hz_close 0 32 (fun e _ => absurd rfl e) (fun _ _ => h1)
        (fun _ e => absurd rfl e) (fun _ _ => h3))
  · rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact go .LSL0 .LSL16 0 16 rfl rfl rfl rfl (by decide) (by decide) (by decide)
      hp0 rfl (hz_close 0 16 (fun e _ => absurd rfl e) (fun _ e => absurd rfl e)
        (fun _ _ => h2) (fun _ _ => h3))

private theorem movk_not_pair_comp {c : BitVec 64} {k1 k2 s1 s2 : Nat}
    (hk2 : k2 < 65536) (hs2 : s2 < 64)
    (heq : ((BitVec.ofNat 64 k1 <<< s1) &&& ~~~(0xFFFF#64 <<< s2)) |||
      (BitVec.ofNat 64 k2 <<< s2) = ~~~c) :
    ((~~~(BitVec.ofNat 64 k1 <<< s1)) &&& ~~~(0xFFFF#64 <<< s2)) |||
      (BitVec.ofNat 64 (k2 ^^^ 0xFFFF) <<< s2) = c := by
  have hk2' : k2 ^^^ 0xFFFF < 65536 := by
    rw [← Nat.mod_eq_of_lt hk2]
    exact Nat.xor_lt_two_pow (n := 16) (Nat.mod_lt k2 (by decide)) (by decide : 0xFFFF < 2 ^ 16)
  have hbit64 : ∀ j, j < 64 → (0xFFFF#64 : BitVec 64).getLsbD j = decide (j < 16) := by
    intro j hj; by_cases hj16 : j < 16
    · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> decide
    · simp only [hj16, decide_false]; exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (by decide : 0xFFFF < 2 ^ 16)
          (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 16 ≤ j)))
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hnotc : c.getLsbD i = !(~~~c).getLsbD i := by simp [hi]
  rw [hnotc, ← heq]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    hi, decide_true, Bool.true_and]
  by_cases hle : s2 ≤ i
  · have hnl : decide (i < s2) = false := decide_eq_false (by omega)
    simp only [hnl, Bool.not_false, Bool.true_and]
    rw [hbit64 (i - s2) (by omega)]
    by_cases hij : i - s2 < 16
    · have ht : Nat.testBit 0xFFFF (i - s2) = true := by
        rcases (by omega : i - s2 = 0 ∨ i - s2 = 1 ∨ i - s2 = 2 ∨
          i - s2 = 3 ∨ i - s2 = 4 ∨ i - s2 = 5 ∨ i - s2 = 6 ∨
          i - s2 = 7 ∨ i - s2 = 8 ∨ i - s2 = 9 ∨ i - s2 = 10 ∨
          i - s2 = 11 ∨ i - s2 = 12 ∨ i - s2 = 13 ∨ i - s2 = 14 ∨
          i - s2 = 15)
          with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
      have hxor : (BitVec.ofNat 64 (k2 ^^^ 0xFFFF)).getLsbD (i - s2) =
          !(BitVec.ofNat 64 k2).getLsbD (i - s2) := by
        simp only [BitVec.getLsbD_ofNat, show i - s2 < 64 by omega, decide_true, Bool.true_and,
          Nat.testBit_xor, ht, Bool.xor_true]
      rw [hxor]
      simp [hij]
    · have hk2f : (BitVec.ofNat 64 k2).getLsbD (i - s2) = false := by
        simp only [BitVec.getLsbD_ofNat, show i - s2 < 64 by omega, decide_true, Bool.true_and]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hk2
          (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 16 ≤ i - s2)))
      have hxorf : (BitVec.ofNat 64 (k2 ^^^ 0xFFFF)).getLsbD (i - s2) = false := by
        simp only [BitVec.getLsbD_ofNat, show i - s2 < 64 by omega, decide_true, Bool.true_and]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hk2'
          (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 16 ≤ i - s2)))
      rw [hxorf, hk2f]
      simp [hij]
  · have hlt : decide (i < s2) = true := decide_eq_true (by omega)
    simp [hlt]

private theorem armOrrImm64_wp [Host] (d : XReg) (c : BitVec 64) (s : MachineData) :
    _root_.Program.wp
      [ins (.ORR_i (.low (.reg d) .W64) (xzr .W64) (.int64 (Int64.ofBitVec c)))]
      (fun s' => s' = wr s d c) (fun _ _ => False) s :=
  armDirFallsTo_wp fun {_} p next jmp P hk => by
    simp only [t_step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
    rw [ofInt_toInt_ofBitVec, BitVec.zero_or]
    exact hk _ rfl

theorem armMovImm_wp [Host] (d : XReg) (c : BitVec 64) (s : MachineData) :
    _root_.Program.wp (emitClean (armMovImmI d c))
      (fun s' => s' = wr s d c) (fun _ _ => False) s := by
  dsimp only [armMovImmI]
  split
  · rename_i hc0
    have hcz : c = 0#64 := beq_iff_eq.mp hc0
    subst hcz
    simp only [emitClean_cons, emitClean_nil]
    exact armWp_mono (armMovz_wp d 0 (by decide) .LSL0 s) fun _ hs' => by
      simpa [BitVec.shiftLeft_zero] using hs'
  · split
    · rename_i hcm1
      have hneg1 : c = ~~~0#64 := beq_iff_eq.mp hcm1
      subst hneg1
      simp only [emitClean_cons, emitClean_nil]
      exact armWp_mono (armMovn_wp d 0 (by decide) .LSL0 s) fun _ hs' => by
        simpa [BitVec.shiftLeft_zero] using hs'
    · split
      · rename_i k sh h1
        obtain ⟨hk, heq⟩ := armMovz1_eq h1
        simp only [emitClean_cons, emitClean_nil]
        exact armWp_mono (armMovz_wp d k hk sh s) fun _ hs' => by simpa [heq] using hs'
      · split
        · rename_i k sh h1
          obtain ⟨hk, heq⟩ := armMovz1_eq h1
          simp only [emitClean_cons, emitClean_nil]
          exact armWp_mono (armMovn_wp d k hk sh s) fun _ hs' => by
            rw [heq, BitVec.not_not] at hs'; exact hs'
        · split
          · simp only [emitClean_cons, emitClean_nil]
            exact armOrrImm64_wp d c s
          · split
            · rename_i k1 sh1 k2 sh2 h2
              obtain ⟨hk1, hk2, heq⟩ := armMovz2_eq h2
              simp only [emitClean_cons, emitClean_nil]
              refine armWp_cons (armMovz_wp d k1 hk1 sh1 s) ?_
              rintro s₁ rfl
              refine armWp_mono (armMovk_wp d k2 hk2 sh2 (wr s d _)) ?_
              rintro s₂ rfl
              simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, wr_wr_same, heq]
            · split
              · rename_i k1 sh1 k2 sh2 h2
                obtain ⟨hk1, hk2, heq⟩ := armMovz2_eq h2
                have hk2' : k2 ^^^ 0xFFFF < 65536 := by
                  rw [← Nat.mod_eq_of_lt hk2]
                  exact Nat.xor_lt_two_pow (n := 16) (Nat.mod_lt k2 (by decide)) (by decide)
                simp only [emitClean_cons, emitClean_nil]
                refine armWp_cons (armMovn_wp d k1 hk1 sh1 s) ?_
                rintro s₁ rfl
                refine armWp_mono (armMovk_wp d (k2 ^^^ 0xFFFF) hk2' sh2 (wr s d _)) ?_
                rintro s₂ rfl
                have hs2 : sh2.toNat < 64 := by cases sh2 <;> decide
                simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, wr_wr_same,
                  movk_not_pair_comp hk2 hs2 heq]
              · simp only [emitClean_cons, emitClean_nil]
                exact armLdrPoolBv_wp d c s

theorem armImm12_some {n : Nat} {c : BitVec n} {ei : ExtOrImmReg}
    (_hn : n ≤ 64) (h : armImm12? c = some ei) :
    ∀ w : RegWidth, ∀ [Labels] (p : Std.Rco Int64) (regs : Reg64s),
      ExtOrImmReg.interp (w := w) ei regs p = (c.setWidth n).setWidth w.bits := by
  dsimp only [armImm12?] at h
  split at h
  · rename_i hlt
    have hlt' : c.toNat < 4096 := Nat.blt_eq.mp hlt
    rcases Option.some.inj h with rfl
    intro w _ p regs
    simp only [ExtOrImmReg.interp, ConstExpr.interp, BitVec.setWidth_eq]
    rw [Int64.toInt_ofNat_of_lt (by omega : c.toNat < 2 ^ 63), BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp
  · split at h
    · rename_i hand
      simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hand
      rcases hand with ⟨hlt, hmod⟩
      rcases Option.some.inj h with rfl
      intro w _ p regs
      simp only [ExtOrImmReg.interp, ConstExpr.interp, BitVec.setWidth_eq]
      rw [Int64.toInt_ofNat_of_lt (by omega : c.toNat / 4096 < 2 ^ 63)]
      have hsh : ((c.toNat / 4096 : Nat) : Int) <<< 12 = (c.toNat : Int) := by
        rw [Int.shiftLeft_eq]
        have hmul : c.toNat / 4096 * 4096 = c.toNat := by omega
        omega
      rw [hsh, BitVec.ofInt_natCast]
      apply BitVec.eq_of_toNat_eq
      simp
    · cases h

theorem armArgIn_wp [Host] {n : Nat} (hn : n ≤ 64) {tmp : XReg}
    {pa : PArg Reg Empty ArmCond (.bits n)}
    {v : BitVec n} {s : MachineData} {ca : List Instr} {ra : XReg}
    (ha : armArgInIns tmp pa = some (ca, ra)) (hp : armMach.PArgHolds s (.bits n) pa v) :
    _root_.Program.wp (emitClean ca) (fun s' =>
      (s'.regs.getXReg ra).toBitVec.setWidth n = v ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg tmp] [] maskNone) (fun _ _ => False) s := by
  cases pa with
  | vec vr => exact vr.elim
  | gpr r =>
    cases r with
    | SP => simp [armArgInIns] at ha
    | reg x =>
      simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
      rcases ha with ⟨rfl, rfl⟩
      refine armWp_nil ⟨?_, rfl, rfl,
        Machine.Frame.refl (M := armMach) armCondReads s [.reg tmp] [] maskNone⟩
      simpa [Machine.PArgHolds, GprHolds, armMach, get_reg] using hp.2
  | imm c =>
    simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp
    refine armWp_mono (armMovImm_wp tmp (c.setWidth 64) s) ?_
    rintro s' rfl
    refine ⟨?_, rfl, rfl, frame_wr tmp (c.setWidth 64) List.mem_cons_self maskNone⟩
    rw [← get_reg, get_wr_same, BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq, hp]

theorem armBoolArgIn_wp [Host] {tmp : XReg} {pa : PArg Reg Empty ArmCond .bool}
    {b : Bool} {s : MachineData} {ca : List Instr} {ra : XReg}
    (ha : armBoolArgInIns tmp pa = some (ca, ra)) (hp : armMach.PArgHolds s .bool pa b) :
    _root_.Program.wp (emitClean ca) (fun s' =>
      (s'.regs.getXReg ra).toBitVec.setWidth 8 = BitVec.ofNat 8 b.toNat ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg tmp] [] maskNone) (fun _ _ => False) s := by
  cases pa with
  | vec vr => exact vr.elim
  | gpr r =>
    cases r with
    | SP => simp [armBoolArgInIns] at ha
    | reg x =>
      simp only [armBoolArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
      rcases ha with ⟨rfl, rfl⟩
      refine armWp_nil ⟨?_, rfl, rfl,
        Machine.Frame.refl (M := armMach) armCondReads s [.reg tmp] [] maskNone⟩
      simpa [Machine.PArgHolds, GprHolds, armMach, get_reg] using hp
  | imm cv =>
    simp only [armBoolArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp
    subst hp
    refine armWp_mono (armMovImm_wp tmp (BitVec.ofNat 64 cv.toNat) s) ?_
    rintro s' rfl
    refine ⟨?_, rfl, rfl, frame_wr tmp _ List.mem_cons_self maskNone⟩
    rw [← get_reg, get_wr_same]
    cases cv <;> rfl
  | flag cond =>
    simp only [armBoolArgInIns, Option.some.injEq, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armCset64_wp tmp cond s) ?_
    rintro s' rfl
    refine ⟨?_, rfl, rfl, frame_wr tmp _ List.mem_cons_self maskNone⟩
    rw [← get_reg, get_wr_same, hp]
    cases b <;> rfl

/-! ## 3. Non-`op` `GprTarget` specs
    (`clearFlags`, `mov`, `movi`, `setcc`, `jmp`, `jcc`, `jnzGpr`, `load`, `store`) -/

theorem armClearFlags_spec {h : Host} {k : Nat} {s : MachineData} {post : MachineState → Prop} :
    armMach.FallsTo armCondReads h k armClearFlags armScratch [] FlagMask.all s
      (fun s' => (∀ c ∈ armZeroFlags, armMach.evalCond s' c = false) ∧ s'.dmem = s.dmem) post := by
  letI := h
  refine armFallsTo_of_wp (armWp_mono (armDirFallsTo_wp (by
    intro _ p next jmp P hk
    simp only [t_step_simp, Reg64s.setRegOrZr_xzr]
    exact hk _ rfl)) ?_)
  rintro s' rfl
  refine ⟨⟨?_, rfl⟩, armFrame_upd_regs (fun _ _ => rfl) (Or.inl rfl)⟩
  intro c hc
  simp only [armZeroFlags, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [ArmCond.interp, ArmCond.toKraken,
    StatusFlags.adds, StatusFlags.from_result, BitVec.unsigned, BitVec.signed]

theorem armMov_spec {h : Host} {k : Nat} {rd rs : Reg} {s : MachineData}
    {post : MachineState → Prop} :
    armMach.FallsTo armCondReads h k (armMov rd rs) [rd] [] FlagMask.none s
      (fun s' => armMach.getGpr s' rd = armMach.getGpr s rs ∧ s'.dmem = s.dmem) post := by
  letI := h
  cases rd with
  | reg xd =>
    cases rs with
    | reg xs =>
      refine armFallsTo_of_wp (armWp_mono (armDirFallsTo_wp (by
        intro _ p next jmp P hk
        simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
          BitVec.shiftLeft_zero, BitVec.zero_or, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
        exact hk _ rfl)) ?_)
      rintro s' rfl
      refine ⟨⟨?_, rfl⟩, frame_wr xd _ List.mem_cons_self FlagMask.none⟩
      exact get_wr_same s xd _
    | SP =>
      refine armFallsTo_of_wp (armWp_mono (armDirFallsTo_wp (by
        intro _ p next jmp P hk
        simp only [t_step_simp, imm0, Int64.toInt_zero]
        rw [show BitVec.ofInt RegWidth.W64.bits 0 = 0#64 from rfl, BitVec.add_zero]
        exact hk _ rfl)) ?_)
      rintro s' rfl
      refine ⟨⟨?_, rfl⟩, armFrame_status_eq (fun r hr => ?_) rfl⟩
      · simp [get_reg, get_sp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp_sp64]
      · have hne : r ≠ .reg xd := fun e => hr (e ▸ List.mem_cons_self)
        cases r with
        | SP => simp [get_sp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
        | reg xr =>
          have hx : xd ≠ xr := fun e => hne (congrArg XRegOrSp.reg e.symm)
          simp [get_reg, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, hx]
  | SP =>
    refine armFallsTo_of_wp (armWp_mono (armDirFallsTo_wp (by
      intro _ p next jmp P hk
      simp only [t_step_simp, imm0, Int64.toInt_zero]
      rw [show BitVec.ofInt RegWidth.W64.bits 0 = 0#64 from rfl, BitVec.add_zero]
      exact hk _ rfl)) ?_)
    rintro s' rfl
    refine ⟨⟨?_, rfl⟩, armFrame_status_eq (fun r hr => ?_) rfl⟩
    · cases rs <;>
        simp [get_reg, get_sp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
          Reg64s.getRegOrSp_reg64, Reg64s.getRegOrSp_sp64]
    · have hne : r ≠ .SP := fun e => hr (e ▸ List.mem_cons_self)
      cases r with
      | SP => exact absurd rfl hne
      | reg xr => rfl

theorem armMovi_spec {h : Host} {k : Nat} {rd : Reg} {c : BitVec 64} {s : MachineData}
    {post : MachineState → Prop} :
    armMach.FallsTo armCondReads h k (armMovi rd c) (rd :: armScratch) [] FlagMask.none s
      (fun s' => armMach.getGpr s' rd = c ∧ s'.dmem = s.dmem) post := by
  letI := h
  refine armFallsTo_of_wp ?_
  cases rd with
  | reg d =>
    refine armWp_mono (armMovImm_wp d c s) ?_
    rintro s' rfl
    exact ⟨⟨get_wr_same s d c, rfl⟩, frame_wr d c List.mem_cons_self FlagMask.none⟩
  | SP =>
    dsimp only [armMovi, armMoviIns]
    rw [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append (armMovImm_wp .X16 c s) ?_
    rintro s₁ rfl
    refine armWp_mono (armMovToSp_wp .X16 (wr s .X16 c)) ?_
    rintro s' rfl
    refine ⟨⟨by simp [get_sp, get_wr_same], rfl⟩, armFrame_status_eq (fun r hr => ?_) rfl⟩
    simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
    cases r with
    | SP => exact absurd rfl hr.1
    | reg xr =>
      have hx : .X16 ≠ xr := fun e => hr.2.1 (congrArg XRegOrSp.reg e.symm)
      simp only [get_reg]
      exact congrArg UInt64.toBitVec (Reg64s.getXReg_setXReg_of_ne s.regs .X16 xr c hx)

theorem armSetcc_spec {h : Host} {k : Nat} {rd : Reg} {c : ArmCond} {s : MachineData}
    {post : MachineState → Prop} (_ : rd ∉ armScratch) :
    armMach.FallsTo armCondReads h k (armSetcc rd c) (rd :: armScratch) [] FlagMask.none s
      (fun s' => GprHolds (armMach.getGpr s' rd) .bool (armMach.evalCond s c) ∧ s'.dmem = s.dmem)
      post := by
  letI := h
  refine armFallsTo_of_wp ?_
  cases rd with
  | reg d =>
    refine armWp_mono (armCset64_wp d c s) ?_
    rintro s' rfl
    refine ⟨⟨?_, rfl⟩, frame_wr d _ List.mem_cons_self FlagMask.none⟩
    dsimp only [armMach]
    rw [get_wr_same]
    cases c.interp s.status <;> rfl
  | SP =>
    refine armWp_cons (armCset64_wp .X16 c s) ?_
    rintro s₁ rfl
    refine armWp_mono (armMovToSp_wp .X16 (wr s .X16 _)) ?_
    rintro s' rfl
    refine ⟨⟨?_, rfl⟩, armFrame_status_eq (fun r hr => ?_) rfl⟩
    · simp only [get_sp, get_wr_same, GprHolds]
      cases c.interp s.status <;> rfl
    · simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
      cases r with
      | SP => exact absurd rfl hr.1
      | reg xr =>
        have hx : .X16 ≠ xr := fun e => hr.2.1 (congrArg XRegOrSp.reg e.symm)
        simp only [get_reg]
        exact congrArg UInt64.toBitVec (Reg64s.getXReg_setXReg_of_ne s.regs .X16 xr _ hx)

theorem armJmp_spec {h : Host} {k j : Nat} {l : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (armJmp l).IsInfixAt (armMach.prog h) k)
    (hl : armMach.labelAddr h l = armMach.addrOf h j)
    (hk : ∀ s', armMach.Frame armCondReads s s' armScratch [] FlagMask.none →
      s'.dmem = s.dmem → armMach.Run h j s' post) :
    armMach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp]
  have hl' : Labels.label l = Host.addrOf j := hl
  rw [hl']
  exact hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] FlagMask.none) rfl

theorem armJcc_spec {h : Host} {k j : Nat} {c : ArmCond} {l : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (armJcc c l).IsInfixAt (armMach.prog h) k)
    (hl : armMach.labelAddr h l = armMach.addrOf h j)
    (hk : ∀ s', armMach.Frame armCondReads s s' armScratch [] FlagMask.none →
      s'.dmem = s.dmem →
      (armMach.evalCond s c = true → armMach.Run h j s' post) ∧
      (armMach.evalCond s c = false → armMach.Run h (k + (armJcc c l).length) s' post)) :
    armMach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp]
  have hrun := hk s
    (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] FlagMask.none) rfl
  have hl' : Labels.label l = Host.addrOf j := hl
  cases hev : c.interp s.status
  · simp only [hev, Bool.false_eq_true, ↓reduceIte, Effects.All]
    exact hrun.2 hev
  · simp only [hev, ↓reduceIte, Effects.All]
    rw [hl']
    exact hrun.1 hev

private theorem bool_getLsbD_zero {v : BitVec 64} {b : Bool}
    (hb : GprHolds v .bool b) : (v.setWidth 32).getLsbD 0 = b := by
  simp only [GprHolds] at hb
  have h0 : (v.setWidth 32).getLsbD 0 = (v.setWidth 8).getLsbD 0 := by simp
  rw [h0, hb]
  cases b <;> decide

theorem armJnzGpr_spec {h : Host} {k j : Nat} {r : Reg} {l : Sym} {b : Bool} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (armJnzGpr r l).1.IsInfixAt (armMach.prog h) k)
    (hl : armMach.labelAddr h l = armMach.addrOf h j)
    (_ : r ∉ armScratch) (hb : GprHolds (armMach.getGpr s r) .bool b)
    (hk : ∀ s', armMach.Frame armCondReads s s' armScratch [] (armJnzGpr r l).2 →
      s'.dmem = s.dmem →
      (b = true → armMach.Run h j s' post) ∧
      (b = false → armMach.Run h (k + (armJnzGpr r l).1.length) s' post)) :
    armMach.Run h k s post := by
  letI := h
  have hl' : Labels.label l = Host.addrOf j := hl
  cases r with
  | reg x =>
    refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
    simp only [t_step_simp]
    have hbit : ((s.regs.getXReg x).toBitVec.setWidth 32).getLsbD 0 = b :=
      bool_getLsbD_zero (by simpa [armMach, get_reg] using hb)
    have hrun := hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone) rfl
    cases b
    · simp only [hbit]; exact hrun.2 rfl
    · simp only [hbit]; rw [hl']; exact hrun.1 rfl
  | SP =>
    dsimp only [armJnzGpr, armJnzGprIns] at hc
    simp only [emitClean_cons, emitClean_nil] at hc
    rw [show [armMovToX .X16 .SP, ins (.TBNZ (zr .X16 .W32) 0 (.label l))] =
      [armMovToX .X16 .SP] ++ [ins (.TBNZ (zr .X16 .W32) 0 (.label l))] from rfl] at hc
    have hpair := hc.append
    have hrun1 : @Program.wp h [armMovToX .X16 .SP] (fun s' => s' = wr s .X16 (get s .SP))
        (fun _ _ => False) s := armMovToX_wp .X16 .SP s
    refine eventually_trans _ _ _ _ (hrun1 k hpair.1) ?_
    rintro ⟨s₁, a⟩ (⟨ha, rfl⟩ | hf)
    · dsimp only at ha; subst ha
      refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hpair.2) ?_
      simp only [t_step_simp]
      have hbit :
          (((wr s .X16 (get s .SP)).regs.getXReg .X16).toBitVec.setWidth 32).getLsbD 0 = b := by
        rw [← get_reg, get_wr_same]; exact bool_getLsbD_zero hb
      have hfr : armMach.Frame armCondReads s (wr s .X16 (get s .SP)) armScratch []
          (armJnzGpr .SP l).2 :=
        frame_wr .X16 (get s .SP) List.mem_cons_self maskNone
      have hrun := hk _ hfr rfl
      dsimp only [armMach, Machine.Run, armJnzGpr, List.length_cons, List.length_nil] at hrun
      cases b
      · simp only [hbit]
        exact hrun.2 rfl
      · simp only [hbit]; rw [hl']; exact hrun.1 rfl
    · exact False.elim hf

private theorem armAtDisp_eval [Labels] (s : MachineData) (rb : XReg) (disp : Int64)
    (p : Std.Rco Int64) :
    (armAtDisp rb disp).eval s p = ((s.regs.getXReg rb).toBitVec + disp.toBitVec, s) := by
  simp only [AddrExpr.eval, ConstExpr.interp, Reg64s.getRegOrSp_reg64, BitVec.signed,
    BitVec.ofInt_add]
  rw [← Int64.toInt_toBitVec]
  simp

private theorem armAtIdx_eval [Labels] (s : MachineData) (rb idx : XReg) (p : Std.Rco Int64) :
    (armAtIdx rb idx).eval s p =
      ((s.regs.getXReg rb).toBitVec + (s.regs.getXReg idx).toBitVec, s) := by
  simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
    Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.signed]
  exact congrArg (·, s) (ofInt_toInt_add_toNat _ _)

private theorem armAtReg_eval [Labels] (s : MachineData) (rb : XReg) (p : Std.Rco Int64) :
    (atReg rb).eval s p = ((s.regs.getXReg rb).toBitVec, s) := by
  simp only [AddrExpr.eval, ConstExpr.interp, Int64.toInt_zero, Reg64s.getRegOrSp_reg64,
    BitVec.signed, Int.add_zero, BitVec.ofInt_toInt]

private theorem bv64_take32_unsigned (v : BitVec 64) :
    (v.take 32).unsigned = ((v.setWidth 32).setWidth 64).unsigned := by
  have h32 : v.take 32 = v.setWidth 32 := by
    ext i; simp [BitVec.take]
  simp only [h32, BitVec.unsigned, BitVec.toNat_setWidth]
  have hlt : v.toNat % 2 ^ 32 < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 2 ^ 32)) (by decide : 2 ^ 32 < 2 ^ 64)
  rw [Nat.mod_eq_of_lt hlt]

private theorem armAtIdxExtScale_eval [Labels] (zextIdx : Bool) (s : MachineData)
    (rb ri : XReg) {scale : Nat} {sc : AddrScale} {amt : MemExtendAmount}
    (hamt : armMemExtendAmount scale sc = some amt) (p : Std.Rco Int64) :
    (armAtIdxExtScale zextIdx rb ri amt).eval s p =
      ((s.regs.getXReg rb).toBitVec +
        ((if zextIdx then ((s.regs.getXReg ri).toBitVec.setWidth 32).setWidth 64
          else (s.regs.getXReg ri).toBitVec) <<< sc.shift), s) := by
  have hsh0 : ∀ rbv riv : BitVec 64,
      BitVec.ofInt 64 (rbv.signed + riv.unsigned) = rbv + riv := by
    intro rbv riv
    rw [BitVec.signed, BitVec.unsigned, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast]
    congr 1
    apply BitVec.eq_of_toNat_eq; simp
  have hsh : ∀ (k : Nat) (rbv riv : BitVec 64),
      BitVec.ofInt 64 (rbv.signed + (riv.unsigned <<< k)) = rbv + (riv <<< k) := by
    intro k rbv riv
    rw [BitVec.signed, BitVec.unsigned, BitVec.ofInt_add, BitVec.ofInt_toInt]
    congr 1
  cases zextIdx <;> cases sc <;> simp only [armMemExtendAmount] at hamt
  · cases hamt
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, AddrScale.shift,
      Bool.false_eq_true, ite_false, BitVec.shiftLeft_zero]
    congr 1; exact hsh0 _ _
  · split at hamt <;> cases hamt
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, AddrScale.shift,
      Bool.false_eq_true, ite_false]
    congr 1; exact hsh 1 _ _
  · split at hamt <;> cases hamt
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, AddrScale.shift,
      Bool.false_eq_true, ite_false]
    congr 1; exact hsh 2 _ _
  · split at hamt <;> cases hamt
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, AddrScale.shift,
      Bool.false_eq_true, ite_false]
    congr 1; exact hsh 3 _ _
  · cases hamt
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, AddrScale.shift,
      BitVec.shiftLeft_zero, bv64_take32_unsigned]
    congr 1; exact hsh0 _ _
  · split at hamt <;> cases hamt
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, AddrScale.shift,
      bv64_take32_unsigned]
    congr 1; exact hsh 1 _ _
  · split at hamt <;> cases hamt
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, AddrScale.shift,
      bv64_take32_unsigned]
    congr 1; exact hsh 2 _ _
  · split at hamt <;> cases hamt
    simp only [AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend,
      Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base, AddrScale.shift,
      bv64_take32_unsigned]
    congr 1; exact hsh 3 _ _

/-- Shift amount `0..4` of an `ExtendAmount`. -/
def armExtendAmountToNat : ExtendAmount → Nat
  | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3 | .E4 => 4

theorem armAddUxtwDir_wp [Host] (d rb ri : XReg) (amt : ExtendAmount) (s : MachineData) :
    _root_.Program.wp [.instr (armAddUxtwI (.reg d) (.reg rb) ri amt)]
      (fun s' => s' = wr s d
        ((s.regs.getXReg rb).toBitVec +
          (((s.regs.getXReg ri).toBitVec.setWidth 32).setWidth 64 <<<
            armExtendAmountToNat amt)))
      (fun _ _ => False) s := by
  have hsh0 : ∀ riv : BitVec 64, BitVec.ofInt 64 riv.unsigned = riv := fun riv => by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.unsigned]
  have hsh : ∀ (k : Nat) (riv : BitVec 64),
      BitVec.ofInt 64 (riv.unsigned <<< k) = riv <<< k := by
    intro k riv
    rw [BitVec.unsigned, ← Int.natCast_shiftLeft, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft]
  refine armDirFallsTo_wp fun {_} p next jmp Q hk => by
    cases amt <;>
      (simp only [t_step_simp, ExtRegExpr.interp, BitVec.apply_extend,
         Reg64s.getRegOrSp_reg64, Reg64s.getRegOrZr64, RegOrZr.base,
         Reg64s.setRegOrSp, Reg64s.setRegOrSp64, RegWidth.bits, MemWidth.bits];
       refine hk _ ?_;
       simp [bv64_take32_unsigned, hsh, hsh0, armExtendAmountToNat])

private theorem armSetupAddr_idxShift_wp [Host] (zextIdx : Bool) (rb ri : XReg)
    (sc : AddrScale) (disp : Int64) (s : MachineData) :
    _root_.Program.wp (emitClean [armAddIdxShiftI zextIdx .X16 rb ri sc])
      (fun s' =>
        (∀ [Labels] p, (armAtDisp .X16 disp).eval s' p =
          ((s.regs.getXReg rb).toBitVec +
            ((if zextIdx then ((s.regs.getXReg ri).toBitVec.setWidth 32).setWidth 64
              else (s.regs.getXReg ri).toBitVec) <<< sc.shift) + disp.toBitVec, s')) ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
        armMach.Frame armCondReads s s' [.reg .X16] [] maskNone)
      (fun _ _ => False) s := by
  have hwp : _root_.Program.wp (emitClean [armAddIdxShiftI zextIdx .X16 rb ri sc])
      (fun s' => s' = wr s .X16
        ((s.regs.getXReg rb).toBitVec +
          ((if zextIdx then ((s.regs.getXReg ri).toBitVec.setWidth 32).setWidth 64
            else (s.regs.getXReg ri).toBitVec) <<< sc.shift)))
      (fun _ _ => False) s := by
    cases zextIdx
    · simp only [armAddIdxShiftI, Bool.false_eq_true, ↓reduceIte, emitClean_cons, emitClean_nil]
      exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
        simp only [t_step_simp, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
        rw [show (Int64.ofNat sc.shift).toInt.toNat = sc.shift by cases sc <;> decide]
        exact hk _ rfl
    · simp only [armAddIdxShiftI, ↓reduceIte, emitClean_cons, emitClean_nil]
      refine armWp_mono (armAddUxtwDir_wp .X16 rb ri (armExtendAmount sc) s) ?_
      rintro s' rfl
      have hsc : armExtendAmountToNat (armExtendAmount sc) = sc.shift := by cases sc <;> rfl
      rw [hsc]
  refine armWp_mono hwp ?_
  rintro s' rfl
  refine ⟨?_, fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
    rfl, rfl, rfl, frame_wr .X16 _ List.mem_cons_self maskNone⟩
  intro _ p
  rw [armAtDisp_eval]
  simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec]

private theorem armSetupAddr_addImm_wp [Host] (zextIdx : Bool) (rb ri : XReg) (hri16 : ri ≠ .X16)
    {scale : Nat} {sc : AddrScale} {amt : MemExtendAmount}
    (hamt : armMemExtendAmount scale sc = some amt) (disp : Int64) {addIns : Instr}
    (hadd : armAddSubImmI? false .W64 .X16 rb disp.toBitVec = some addIns)
    (s : MachineData) :
    _root_.Program.wp (emitClean [addIns]) (fun s' =>
      (∀ [Labels] p, (armAtIdxExtScale zextIdx .X16 ri amt).eval s' p =
        ((s.regs.getXReg rb).toBitVec +
          ((if zextIdx then ((s.regs.getXReg ri).toBitVec.setWidth 32).setWidth 64
            else (s.regs.getXReg ri).toBitVec) <<< sc.shift) + disp.toBitVec, s')) ∧
      (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg .X16] [] maskNone)
      (fun _ _ => False) s := by
  have hwp : _root_.Program.wp (emitClean [addIns])
      (fun s' => s' = wr s .X16 ((s.regs.getXReg rb).toBitVec + disp.toBitVec))
      (fun _ _ => False) s := by
    dsimp only [armAddSubImmI?] at hadd
    cases h1 : armImm12? disp.toBitVec with
    | some ei =>
      simp only [h1, Option.some.injEq] at hadd; subst hadd
      simp only [emitClean_cons, emitClean_nil]
      exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
        have himm := armImm12_some (by decide : 64 ≤ 64) h1 .W64 p s.regs
        dsimp only [ExtOrImmReg.interp] at himm
        simp only [↓reduceIte, Bool.false_eq_true, t_step_simp, Reg64s.setRegOrSp_reg64,
          Reg64s.getRegOrSp_reg64] at himm ⊢
        rw [himm]
        simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
        exact hk _ rfl
    | none =>
      cases h2 : armImm12? (-disp.toBitVec) with
      | none => simp [h1, h2] at hadd
      | some ei =>
        simp only [h1, h2, Option.some.injEq] at hadd; subst hadd
        simp only [emitClean_cons, emitClean_nil]
        exact armDirFallsTo_wp fun {_} p next jmp Q hk => by
          have himm := armImm12_some (by decide : 64 ≤ 64) h2 .W64 p s.regs
          dsimp only [ExtOrImmReg.interp] at himm
          simp only [↓reduceIte, Bool.false_eq_true, t_step_simp, Reg64s.setRegOrSp_reg64,
            Reg64s.getRegOrSp_reg64] at himm ⊢
          rw [himm]
          simp only [RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq, BitVec.sub_neg]
          exact hk _ rfl
  refine armWp_mono hwp ?_
  rintro s' rfl
  refine ⟨?_, fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
    rfl, rfl, rfl, frame_wr .X16 _ List.mem_cons_self maskNone⟩
  intro _ p
  rw [armAtIdxExtScale_eval zextIdx _ .X16 ri hamt p]
  simp only [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
    Reg64s.getXReg_setXReg_of_ne _ _ _ _ hri16.symm]
  congr 1
  rw [BitVec.add_assoc, BitVec.add_comm disp.toBitVec, ← BitVec.add_assoc]

private theorem armSetupIdxDisp_wp [Host] (zextIdx : Bool) (scale : Nat) (rb ri : XReg)
    (sc : AddrScale) (disp : Int64) (s : MachineData) (hri16 : ri ≠ .X16)
    (hva : armAddrIdxValid scale sc disp = true) :
    let (setup, addr) := armSetupIdxDispIns zextIdx scale rb ri sc disp
    (∃ rx, addr.base = .low (.reg rx) .W64) ∧
    _root_.Program.wp (emitClean setup) (fun s' =>
      (∀ [Labels] p, addr.eval s' p =
        ((s.regs.getXReg rb).toBitVec +
          ((if zextIdx then ((s.regs.getXReg ri).toBitVec.setWidth 32).setWidth 64
            else (s.regs.getXReg ri).toBitVec) <<< sc.shift) + disp.toBitVec, s')) ∧
      (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg .X16] [] maskNone) (fun _ _ => False) s := by
  dsimp only [armAddrIdxValid] at hva
  dsimp only [armSetupIdxDispIns]
  by_cases hdisp0 : disp == 0
  · simp only [hdisp0, ↓reduceIte]
    cases hamt : armMemExtendAmount scale sc with
    | some amt =>
      have hd : disp.toBitVec = 0#64 := by
        have := beq_iff_eq.mp hdisp0; subst this; rfl
      refine ⟨⟨rb, rfl⟩, armWp_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl,
        Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone⟩⟩
      intro _ p
      rw [armAtIdxExtScale_eval zextIdx s rb ri hamt p, hd, BitVec.add_zero]
    | none =>
      rw [beq_iff_eq] at hdisp0; subst hdisp0
      simp [hamt] at hva
  · simp only [hdisp0, Bool.false_eq_true, ↓reduceIte]
    by_cases hfit : armFitsScaledOff scale disp
    · simp only [hfit, ↓reduceIte]
      exact ⟨⟨.X16, rfl⟩, armSetupAddr_idxShift_wp zextIdx rb ri sc disp s⟩
    · simp only [hfit, Bool.false_eq_true, ↓reduceIte]
      have hidx : (armMemExtendAmount scale sc).isSome = true ∧
          ((armImm12? disp.toBitVec).isSome = true ∨
            (armImm12? (-disp.toBitVec)).isSome = true) := by
        simpa [bne, hfit, hdisp0, Bool.and_eq_true, Bool.or_eq_true] using hva
      obtain ⟨amt, hamt⟩ := Option.isSome_iff_exists.mp hidx.1
      have hadd : ∃ addIns,
          armAddSubImmI? false .W64 .X16 rb disp.toBitVec = some addIns := by
        dsimp only [armAddSubImmI?]
        rcases hidx.2 with h1 | h2
        · obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.mp h1; simp [hei]
        · obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.mp h2
          cases h1 : armImm12? disp.toBitVec <;> simp [hei]
      obtain ⟨addIns, hadd⟩ := hadd
      rw [hamt, hadd]
      exact ⟨⟨.X16, rfl⟩, armSetupAddr_addImm_wp zextIdx rb ri hri16 hamt disp hadd s⟩

theorem armSetupAddrZext_wp [Host] (scale : Nat) (base idx : Reg) (sc : AddrScale)
    (disp : Int64) (s : MachineData) (hidx : idx ∉ armScratch)
    {setup : List Instr} {addr : AddrExpr}
    (hsa : armSetupAddrZextIns scale base idx sc disp = some (setup, addr)) :
    ∃ (rb ri : XReg), base = .reg rb ∧ idx = .reg ri ∧
      (∃ rx, addr.base = .low (.reg rx) .W64) ∧
      _root_.Program.wp (emitClean setup) (fun s' =>
        (∀ [Labels] p, addr.eval s' p =
          ((s.regs.getXReg rb).toBitVec +
            (((s.regs.getXReg ri).toBitVec.setWidth 32).setWidth 64 <<< sc.shift) +
            disp.toBitVec, s')) ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
        armMach.Frame armCondReads s s' [.reg .X16] [] maskNone) (fun _ _ => False) s := by
  cases base with
  | SP => simp [armSetupAddrZextIns] at hsa
  | reg rb =>
    cases idx with
    | SP => simp [armSetupAddrZextIns] at hsa
    | reg ri =>
      dsimp only [armSetupAddrZextIns] at hsa
      split at hsa
      · rename_i hva
        simp only [Option.some.injEq] at hsa
        have hri16 : ri ≠ .X16 := (xreg_ne_scratch_of_not_mem hidx).1
        have h := armSetupIdxDisp_wp true scale rb ri sc disp s hri16 hva
        rw [hsa] at h
        exact ⟨rb, ri, rfl, rfl, h.1, h.2⟩
      · simp at hsa

theorem armSetupAddr_wp [Host] (scale : Nat) (a : AddrArg Reg) (s : MachineData)
    (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hva : armAddrValid scale a = true) :
    let (setup, addr) := armSetupAddrIns scale a
    (∃ rx, addr.base = .low (.reg rx) .W64) ∧
    _root_.Program.wp (emitClean setup) (fun s' =>
      (∀ [Labels] p, addr.eval s' p = (a.eval (get s), s')) ∧
      (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg .X16] [] maskNone) (fun _ _ => False) s := by
  cases a with
  | baseIdxDisp base idx sc disp =>
    cases base with
    | SP => simp [armAddrValid] at hva
    | reg rb =>
      cases idx with
      | SP => simp [armAddrValid] at hva
      | reg ri =>
        have hri16 : ri ≠ .X16 :=
          fun h => haregs (.reg ri) (by simp [AddrArg.regs]) (by simp [h, armScratch])
        dsimp only [armAddrValid] at hva
        dsimp only [armSetupAddrIns]
        simpa only [AddrArg.eval, get_reg, Bool.false_eq_true, ↓reduceIte] using
          armSetupIdxDisp_wp false scale rb ri sc disp s hri16 hva
  | imm addr =>
    simp only [armSetupAddrIns]
    refine ⟨⟨.X16, rfl⟩, armWp_mono (armMovImm_wp .X16 addr s) ?_⟩
    rintro s' rfl
    refine ⟨by intro _ p; rw [armAtReg_eval, ← get_reg, get_wr_same, AddrArg.eval],
      fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl, rfl, rfl,
      frame_wr .X16 addr List.mem_cons_self maskNone⟩
  | baseDisp base disp =>
    cases base with
    | reg rb =>
      have hrb16 : rb ≠ .X16 :=
        fun h => haregs (.reg rb) (by simp [AddrArg.regs]) (by simp [h, armScratch])
      dsimp only [armSetupAddrIns]
      split
      · rename_i h0
        have hd : disp.toBitVec = 0#64 := by
          have := beq_iff_eq.mp h0; subst this; rfl
        refine ⟨⟨rb, rfl⟩, armWp_nil ⟨by
            intro _ p; rw [armAtReg_eval, AddrArg.eval, hd, BitVec.add_zero, get_reg],
          fun _ _ => rfl, rfl, rfl, rfl,
          Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone⟩⟩
      · split
        · refine ⟨⟨rb, rfl⟩, armWp_nil ⟨by
              intro _ p; rw [armAtDisp_eval, AddrArg.eval, get_reg],
            fun _ _ => rfl, rfl, rfl, rfl,
            Machine.Frame.refl (M := armMach) armCondReads s [.reg .X16] [] maskNone⟩⟩
        · refine ⟨⟨rb, rfl⟩, armWp_mono (armMovImm_wp .X16 disp.toBitVec s) ?_⟩
          rintro s' rfl
          refine ⟨by
              intro _ p
              rw [armAtIdx_eval, AddrArg.eval, get_reg,
                Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrb16.symm, Reg64s.getXReg_setXReg_same],
            fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
            rfl, rfl, rfl, frame_wr .X16 _ List.mem_cons_self maskNone⟩
    | SP =>
      dsimp only [armSetupAddrIns]
      split
      · rename_i h0
        have hd : disp.toBitVec = 0#64 := by
          have := beq_iff_eq.mp h0; subst this; rfl
        simp only [emitClean_cons, emitClean_nil]
        refine ⟨⟨.X16, rfl⟩, armWp_mono (armMovToX_wp .X16 .SP s) ?_⟩
        rintro s' rfl
        refine ⟨by
            intro _ p
            rw [armAtReg_eval, AddrArg.eval, hd, BitVec.add_zero, ← get_reg, get_wr_same],
          fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
          rfl, rfl, rfl, frame_wr .X16 (get s .SP) List.mem_cons_self maskNone⟩
      · split
        · simp only [emitClean_cons, emitClean_nil]
          refine ⟨⟨.X16, rfl⟩, armWp_mono (armDirFallsTo_wp (by
            intro _ p next jmp P hk
            simp only [t_step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
              Reg64s.getRegOrSp_sp64, ConstExpr.interp, RegWidth.bits]
            rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
            exact hk _ rfl)) ?_⟩
          rintro s' rfl
          refine ⟨by
              intro _ p
              simp only [armAtReg_eval, AddrArg.eval, get_sp, Reg64s.getXReg_setXReg_same],
            fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
            rfl, rfl, rfl, frame_wr .X16 _ List.mem_cons_self maskNone⟩
        · rw [emitClean_append, emitClean_cons, emitClean_nil]
          refine ⟨⟨.X16, rfl⟩, armWp_append (armMovImm_wp .X16 disp.toBitVec s) ?_⟩
          rintro s₁ rfl
          refine armWp_mono (armDirFallsTo_wp (by
            intro _ p next jmp P hk
            simp only [t_step_simp, ExtRegExpr.interp, BitVec.apply_extend,
              Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp_sp64, RegWidth.bits,
              Reg64s.getRegOrZr64, RegOrZr.base, BitVec.unsigned]
            rw [Reg64s.getXReg_setXReg_same, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
            exact hk _ rfl)) ?_
          rintro s' rfl
          refine ⟨by
              intro _ p
              simp only [armAtReg_eval, AddrArg.eval, get_sp, Reg64s.getXReg_setXReg_same]
              rfl,
            fun x hx => by
              rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm,
                Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm],
            rfl, rfl, rfl, frame_wr .X16 _ List.mem_cons_self maskNone⟩

private theorem zeroExtend_setWidth_low {k m : Nat} (hk : k ≤ m) (hk64 : k ≤ 64) (v : BitVec k) :
    ((v.zeroExtend m).setWidth 64).setWidth k = v := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ hk64,
    BitVec.setWidth_setWidth_of_le _ hk, BitVec.setWidth_eq]

private theorem Reg64s_getXReg_setSP' (regs : Reg64s) (v : UInt64) (x : XReg) :
    ({ regs with SP := v } : Reg64s).getXReg x = regs.getXReg x := by
  cases x <;> rfl

private theorem armLoadDir_wp [Host] {t : Ty} {d : XReg} {addr : AddrExpr} {a : BitVec 64}
    {v : Val t} {s : MachineData} {dir : Instr}
    (hdir : armLoadDirI t d addr = some dir) (hnoSp : ∃ rx, addr.base = .low (.reg rx) .W64)
    (heval : ∀ [Labels] p, addr.eval s p = (a, s)) (hload : loadVal s.dmem t a = some v) :
    _root_.Program.wp [.instr dir] (fun s' =>
      ∃ w64 : BitVec 64, s' = wr s d w64 ∧ AbiGprHolds w64 t v) (fun _ _ => False) s := by
  obtain ⟨rx, hrx⟩ := hnoSp
  simp only [loadVal, Option.bind_eq_some_iff] at hload
  rcases hload with ⟨i, hi, hv⟩
  cases t with
  | bool =>
    simp only [armLoadDirI, Option.some.injEq] at hdir; subst hdir
    simp only [Ty.bytes, Ty.size] at hi
    cases hb : (i == 0 || i == 1) <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq, reduceCtorEq] at hv
    subst hv
    refine armDirFallsTo_wp (by
      intro _ p next jmp P hk
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpLoad,
        AddrExpr.checkSPAlignment, hrx, heval p, MachineData.load, MemWidth.bytes, hi,
        MachineData.setRegOrZr, setRegOrZr_zr, MemWidth.bits, RegWidth.bits, Effects.All]
      refine hk _ ⟨_, rfl, ?_⟩
      simp only [Bool.or_eq_true, beq_iff_eq] at hb
      simp only [AbiGprHolds]
      rcases hb with rfl | rfl <;> decide)
  | bits n =>
    have hns : (n = 8 ∨ n = 16) ∨ (n = 32 ∨ n = 64) := by
      rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64))
        with h | h | h | h | ⟨h1, h2, h3, h4⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exfalso; revert hdir; simp [armLoadDirI, h1, h2, h3, h4]
    rcases hns with (rfl | rfl) | (rfl | rfl) <;>
      (simp only [armLoadDirI, Option.some.injEq] at hdir; subst hdir;
       simp only [Ty.bytes, Ty.size, ofBits, Option.some.injEq] at hi hv; subst hv;
       refine armDirFallsTo_wp (by
         intro _ p next jmp P hk
         simp only [Directive.interp, Instr.interp, Operation.interp]
         try simp only [AddrOrLit.interpLoad]
         simp only [AddrExpr.interpLoad, AddrExpr.checkSPAlignment, hrx, heval p,
           MachineData.load, MemWidth.bytes, hi, MachineData.setRegOrZr, setRegOrZr_zr,
           MemWidth.bits, Effects.All]
         refine hk _ ⟨_, rfl, by decide, ?_⟩
         first
         | (rw [BitVec.zeroExtend]; exact (BitVec.setWidth_setWidth_of_le _ (by decide)).symm)
         | simp))
  | float _ | pair _ _ => simp [armLoadDirI] at hdir

private theorem armLoadTail_wp {h : Host} {k : Nat} {t : Ty} {rd : Reg} {setup : List Instr}
    {addr : AddrExpr} {effAddr : BitVec 64} {ci : List Instr} {clob : FlagMask} {v : Val t}
    {s : MachineData} {post : MachineState → Prop}
    (hc : armLoadTailIns t rd setup addr = some (ci, clob))
    (hnoSp : ∃ rx, addr.base = .low (.reg rx) .W64)
    (hwpSetup : _root_.Program.wp (emitClean setup) (fun s' =>
      (∀ [Labels] p, addr.eval s' p = (effAddr, s')) ∧
      (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg .X16] [] maskNone) (fun _ _ => False) s)
    (hv : loadVal (armMach.mem s) t effAddr = some v)
    (hclean : (emitClean (D := ConstExpr) ci).IsInfixAt (armMach.prog h) k)
    (hk : ∀ s', (AbiGprHolds (armMach.getGpr s' rd) t v ∧ armMach.mem s' = armMach.mem s) →
      armMach.Frame armCondReads s s' (rd :: armScratch) [] clob →
      armMach.Run h (k + (emitClean (D := ConstExpr) ci).length) s' post) :
    armMach.Run h k s post := by
  letI := h
  cases rd with
  | reg d =>
    simp only [armLoadTailIns, bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hc
    rcases hc with ⟨dir, hdir, rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil] at hclean hk ⊢
    refine armFallsTo_of_wp (armWp_append hwpSetup ?_) hclean hk
    rintro s₁ ⟨heval, _, _, hdmem₁, hst₁, hfr₁⟩
    refine armWp_mono (armLoadDir_wp hdir hnoSp heval (by simpa [armMach, hdmem₁] using hv)) ?_
    rintro s₂ ⟨w64, rfl, hw64⟩
    refine ⟨⟨by simpa [armMach, get_wr_same] using hw64, hdmem₁⟩, armFrame_status_eq ?_ hst₁⟩
    intro r hr
    have hnd : r ≠ .reg d := fun e => hr (e ▸ List.mem_cons_self)
    rw [get_wr_of_ne s₁ d w64 r hnd]
    exact hfr₁.1 r fun h16 => hr (by simp at h16; subst h16; simp [armScratch])
  | SP =>
    simp only [armLoadTailIns, bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hc
    rcases hc with ⟨dir, hdir, rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil] at hclean hk ⊢
    refine armFallsTo_of_wp (armWp_append hwpSetup ?_) hclean hk
    rintro s₁ ⟨heval, hx₁, _, hdmem₁, hst₁, _⟩
    refine armWp_cons (armLoadDir_wp hdir hnoSp heval (by simpa [armMach, hdmem₁] using hv)) ?_
    rintro s₂ ⟨w64, rfl, hw64⟩
    refine armWp_mono (armMovToSp_wp .X16 (wr s₁ .X16 w64)) ?_
    rintro s₃ rfl
    refine ⟨⟨?_, hdmem₁⟩, armFrame_status_eq ?_ hst₁⟩
    · simpa [armMach, get_sp, get_wr_same] using hw64
    · intro r hr
      simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
      cases r with
      | SP => exact absurd rfl hr.1
      | reg xr =>
        have hx16 : xr ≠ .X16 := fun e => hr.2.1 (congrArg XRegOrSp.reg e)
        have h1 := hx₁ xr hx16
        simp only [get_reg, Reg64s_getXReg_setSP',
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
        exact congrArg UInt64.toBitVec h1

theorem armLoad_zext (_ : armGpr.zeroExtLoad = true) {h : Host} {k : Nat} {t : Ty} {rd : Reg}
    {a : AddrArg Reg} {c : List Directive} {clob : FlagMask} {v : Val t} {s : MachineData}
    {post : MachineState → Prop} (hc_in : armLoad t rd a = some (c, clob)) (_ : rd ∉ armScratch)
    (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hv : loadVal (armMach.mem s) t (a.eval (get s)) = some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) t v ∧ armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  dsimp only [armLoadIns] at hc
  match hsc : armMemScale t with
  | none => simp [hsc] at hc
  | some scale =>
    simp only [hsc, bind, Option.bind_some] at hc
    have hva : armAddrValid scale a = true := by
      cases h : armAddrValid scale a
      · simp [h] at hc
      · rfl
    rw [show (!armAddrValid scale a) = false by simp [hva]] at hc
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    have hsetup := armSetupAddr_wp scale a s haregs hva
    generalize armSetupAddrIns scale a = sa at hc hsetup
    rcases sa with ⟨setup, addr⟩
    rcases hsetup with ⟨hnoSp, hwpSetup⟩
    exact fun hclean hk => armLoadTail_wp hc hnoSp hwpSetup hv hclean hk

theorem armLoadZextIdx_zext {h : Host} {k : Nat} {t : Ty} {rd base idx : Reg}
    {sc : AddrScale} {disp : Int64} {c : List Directive} {clob : FlagMask} {v : Val t}
    {vb : BitVec 64} {vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armLoadZextIdx t rd base idx sc disp = some (c, clob))
    (_ : rd ∉ armScratch) (hbase : base ∉ armScratch) (hidx : idx ∉ armScratch)
    (hvb : GprHolds (armMach.getGpr s base) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s idx) (.bits 32) vi)
    (hv : loadVal (armMach.mem s) t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) =
      some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => AbiGprHolds (armMach.getGpr s' rd) t v ∧ armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  dsimp only [armLoadZextIdxIns] at hc
  simp only [bind, Option.bind_eq_some_iff] at hc
  rcases hc with ⟨scale, _, ⟨setup, addr⟩, hsa, hc⟩
  obtain ⟨rb, ri, rfl, rfl, hnoSp, hwpSetup⟩ :=
    armSetupAddrZext_wp scale base idx sc disp s hidx hsa
  have hrb : (s.regs.getXReg rb).toBitVec = vb := by
    simpa [GprHolds, armMach, get_reg] using hvb.2
  have hri : (s.regs.getXReg ri).toBitVec.setWidth 32 = vi := by
    simpa [GprHolds, armMach, get_reg] using hvi.2
  rw [hrb, hri] at hwpSetup
  exact fun hclean hk => armLoadTail_wp hc hnoSp hwpSetup hv hclean hk

theorem armLoadZextIdx_spec {h : Host} {k : Nat} {t : Ty} {rd base idx : Reg}
    {sc : AddrScale} {disp : Int64} {c : List Directive} {clob : FlagMask} {v : Val t}
    {vb : BitVec 64} {vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armLoadZextIdx t rd base idx sc disp = some (c, clob))
    (hrd : rd ∉ armScratch) (hbase : base ∉ armScratch) (hidx : idx ∉ armScratch)
    (hvb : GprHolds (armMach.getGpr s base) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s idx) (.bits 32) vi)
    (hv : loadVal (armMach.mem s) t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) =
      some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => GprHolds (armMach.getGpr s' rd) t v ∧ armMach.mem s' = armMach.mem s) post :=
  fun hc hk => armLoadZextIdx_zext hc_in hrd hbase hidx hvb hvi hv hc fun s' ⟨h1, h2⟩ hfr =>
    hk s' ⟨h1.toGprHolds, h2⟩ hfr

theorem armLoadZextIdx_zero32 {h : Host} {k : Nat} {rd base idx : Reg}
    {sc : AddrScale} {disp : Int64} {c : List Directive} {clob : FlagMask}
    {v : BitVec 32} {vb : BitVec 64} {vi : BitVec 32} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armLoadZextIdx (.bits 32) rd base idx sc disp = some (c, clob))
    (hrd : rd ∉ armScratch) (hbase : base ∉ armScratch) (hidx : idx ∉ armScratch)
    (hvb : GprHolds (armMach.getGpr s base) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s idx) (.bits 32) vi)
    (hv : loadVal (armMach.mem s) (.bits 32)
      (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) = some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => armMach.getGpr s' rd = v.setWidth 64 ∧ armMach.mem s' = armMach.mem s) post :=
  fun hc hk => armLoadZextIdx_zext hc_in hrd hbase hidx hvb hvi hv hc fun s' ⟨h1, h2⟩ hfr =>
    hk s' ⟨h1.2, h2⟩ hfr

theorem armLoad_spec {h : Host} {k : Nat} {t : Ty} {rd : Reg} {a : AddrArg Reg}
    {c : List Directive} {clob : FlagMask} {v : Val t} {s : MachineData}
    {post : MachineState → Prop} (hc_in : armLoad t rd a = some (c, clob))
    (hrd : rd ∉ armScratch) (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hv : loadVal (armMach.mem s) t (a.eval (get s)) = some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => GprHolds (armMach.getGpr s' rd) t v ∧ armMach.mem s' = armMach.mem s) post :=
  fun hc hk => armLoad_zext rfl hc_in hrd haregs hv hc fun s' ⟨h1, h2⟩ hfr =>
    hk s' ⟨h1.toGprHolds, h2⟩ hfr

theorem armLoad_zero32 {h : Host} {k : Nat} {rd : Reg} {a : AddrArg Reg}
    {c : List Directive} {clob : FlagMask} {v : BitVec 32} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armLoad (.bits 32) rd a = some (c, clob)) (hrd : rd ∉ armScratch)
    (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hv : loadVal (armMach.mem s) (.bits 32) (a.eval (get s)) = some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => armMach.getGpr s' rd = v.setWidth 64 ∧ armMach.mem s' = armMach.mem s) post :=
  fun hc hk => armLoad_zext rfl hc_in hrd haregs hv hc fun s' ⟨h1, h2⟩ hfr =>
    hk s' ⟨h1.2, h2⟩ hfr

private theorem armLoadSextDir_wp [Host] {m : Nat} {d : XReg} {addr : AddrExpr} {a : BitVec 64}
    {v : BitVec m} {s : MachineData} {dir : Instr}
    (hdir : armLoadSextDirI m d addr = some dir) (hnoSp : ∃ rx, addr.base = .low (.reg rx) .W64)
    (heval : ∀ [Labels] p, addr.eval s p = (a, s)) (hload : loadVal s.dmem (.bits m) a = some v) :
    _root_.Program.wp [.instr dir]
      (fun s' => s' = wr s d (v.signExtend 64)) (fun _ _ => False) s := by
  obtain ⟨rx, hrx⟩ := hnoSp
  simp only [loadVal, Option.bind_eq_some_iff] at hload
  rcases hload with ⟨i, hi, hv⟩
  have hns : m = 8 ∨ m = 16 := by
    by_cases h8 : m = 8
    · exact Or.inl h8
    · by_cases h16 : m = 16
      · exact Or.inr h16
      · exfalso; revert hdir; simp [armLoadSextDirI]
  rcases hns with rfl | rfl <;>
    (simp only [armLoadSextDirI, Option.some.injEq] at hdir; subst hdir;
     simp only [Ty.bytes, Ty.size, ofBits, Option.some.injEq] at hi hv; subst hv;
     refine armDirFallsTo_wp (by
       intro _ p next jmp P hk
       simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpLoad,
         AddrExpr.checkSPAlignment, hrx, heval p, MachineData.load, MemWidth.bytes, hi,
         MachineData.setRegOrZr, setRegOrZr_zr, MemWidth.bits, Effects.All]
       exact hk _ rfl))

private theorem armLoadSextTail_wp {h : Host} {k m : Nat} {rd : Reg} {setup : List Instr}
    {addr : AddrExpr} {effAddr : BitVec 64} {ci : List Instr} {clob : FlagMask}
    {v : BitVec m} {s : MachineData} {post : MachineState → Prop}
    (hc : armLoadSextTailIns m rd setup addr = some (ci, clob))
    (hnoSp : ∃ rx, addr.base = .low (.reg rx) .W64)
    (hwpSetup : _root_.Program.wp (emitClean setup) (fun s' =>
      (∀ [Labels] p, addr.eval s' p = (effAddr, s')) ∧
      (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
      s'.regs.SP = s.regs.SP ∧ s'.dmem = s.dmem ∧ s'.status = s.status ∧
      armMach.Frame armCondReads s s' [.reg .X16] [] maskNone) (fun _ _ => False) s)
    (hv : loadVal (armMach.mem s) (.bits m) effAddr = some v)
    (hclean : (emitClean (D := ConstExpr) ci).IsInfixAt (armMach.prog h) k)
    (hk : ∀ s', (armMach.getGpr s' rd = v.signExtend 64 ∧ armMach.mem s' = armMach.mem s) →
      armMach.Frame armCondReads s s' (rd :: armScratch) [] clob →
      armMach.Run h (k + (emitClean (D := ConstExpr) ci).length) s' post) :
    armMach.Run h k s post := by
  letI := h
  cases rd with
  | reg d =>
    simp only [armLoadSextTailIns, bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hc
    rcases hc with ⟨dir, hdir, rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil] at hclean hk ⊢
    refine armFallsTo_of_wp (armWp_append hwpSetup ?_) hclean hk
    rintro s₁ ⟨heval, _, _, hdmem₁, hst₁, hfr₁⟩
    refine armWp_mono (armLoadSextDir_wp hdir hnoSp heval (by simpa [armMach, hdmem₁] using hv)) ?_
    rintro s₂ rfl
    refine ⟨⟨by simp [get_wr_same], hdmem₁⟩, armFrame_status_eq ?_ hst₁⟩
    intro r hr
    have hnd : r ≠ .reg d := fun e => hr (e ▸ List.mem_cons_self)
    rw [get_wr_of_ne s₁ d _ r hnd]
    exact hfr₁.1 r fun h16 => hr (by simp at h16; subst h16; simp [armScratch])
  | SP =>
    simp only [armLoadSextTailIns, bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hc
    rcases hc with ⟨dir, hdir, rfl, rfl⟩
    simp only [emitClean_append, emitClean_cons, emitClean_nil] at hclean hk ⊢
    refine armFallsTo_of_wp (armWp_append hwpSetup ?_) hclean hk
    rintro s₁ ⟨heval, hx₁, _, hdmem₁, hst₁, _⟩
    refine armWp_cons (armLoadSextDir_wp hdir hnoSp heval (by simpa [armMach, hdmem₁] using hv)) ?_
    rintro s₂ rfl
    refine armWp_mono (armMovToSp_wp .X16 (wr s₁ .X16 (v.signExtend 64))) ?_
    rintro s₃ rfl
    refine ⟨⟨by simp [get_sp, get_wr_same], hdmem₁⟩, armFrame_status_eq ?_ hst₁⟩
    intro r hr
    simp only [List.mem_cons, armScratch, List.not_mem_nil, or_false, not_or] at hr
    cases r with
    | SP => exact absurd rfl hr.1
    | reg xr =>
      have hx16 : xr ≠ .X16 := fun e => hr.2.1 (congrArg XRegOrSp.reg e)
      have h1 := hx₁ xr hx16
      simp only [get_reg, Reg64s_getXReg_setSP',
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
      exact congrArg UInt64.toBitVec h1

theorem armLoadSext_spec {h : Host} {k m n : Nat} {rd : Reg} {a : AddrArg Reg}
    {c : List Directive} {clob : FlagMask} {v : BitVec m} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armLoadSext m n rd a = some (c, clob)) (_ : rd ∉ armScratch)
    (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hv : loadVal (armMach.mem s) (.bits m) (a.eval (get s)) = some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => armMach.getGpr s' rd = v.signExtend 64 ∧ armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  have hm : m = 8 ∨ m = 16 := by
    by_cases h8 : m = 8
    · exact Or.inl h8
    · by_cases h16 : m = 16
      · exact Or.inr h16
      · exfalso; revert hc; simp [armLoadSextIns, h8, h16]
  dsimp only [armLoadSextIns] at hc
  split at hc
  · simp at hc
  · have hscEx : ∃ scale, armMemScale (.bits m) = some scale ∧
        (if (!armAddrValid scale a) = true then none
         else
           let sa := armSetupAddrIns scale a
           armLoadSextTailIns m rd sa.1 sa.2) = some (ci, clob) := by
      rcases hm with rfl | rfl <;> exact ⟨_, rfl, hc⟩
    rcases hscEx with ⟨scale, _, hc'⟩
    have hva : armAddrValid scale a = true := by
      cases h : armAddrValid scale a
      · simp [h] at hc'
      · rfl
    rw [show (!armAddrValid scale a) = false by simp [hva]] at hc'
    simp only [Bool.false_eq_true, ↓reduceIte] at hc'
    have hsetup := armSetupAddr_wp scale a s haregs hva
    generalize armSetupAddrIns scale a = sa at hc' hsetup
    rcases sa with ⟨setup, addr⟩
    rcases hsetup with ⟨hnoSp, hwpSetup⟩
    exact fun hclean hk => armLoadSextTail_wp hc' hnoSp hwpSetup hv hclean hk

theorem armLoadSextZextIdx_spec {h : Host} {k m n : Nat} {rd base idx : Reg}
    {sc : AddrScale} {disp : Int64} {c : List Directive} {clob : FlagMask} {v : BitVec m}
    {vb : BitVec 64} {vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armLoadSextZextIdx m n rd base idx sc disp = some (c, clob))
    (_ : rd ∉ armScratch) (_ : base ∉ armScratch) (hidx : idx ∉ armScratch)
    (hvb : GprHolds (armMach.getGpr s base) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s idx) (.bits 32) vi)
    (hv : loadVal (armMach.mem s) (.bits m)
      (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) = some v) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => armMach.getGpr s' rd = v.signExtend 64 ∧ armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  dsimp only [armLoadSextZextIdxIns] at hc
  split at hc
  · simp at hc
  · simp only [bind, Option.bind_eq_some_iff] at hc
    rcases hc with ⟨scale, _, ⟨setup, addr⟩, hsa, hc⟩
    obtain ⟨rb, ri, rfl, rfl, hnoSp, hwpSetup⟩ :=
      armSetupAddrZext_wp scale base idx sc disp s hidx hsa
    have hrb : (s.regs.getXReg rb).toBitVec = vb := by
      simpa [GprHolds, armMach, get_reg] using hvb.2
    have hri : (s.regs.getXReg ri).toBitVec.setWidth 32 = vi := by
      simpa [GprHolds, armMach, get_reg] using hvi.2
    rw [hrb, hri] at hwpSetup
    exact fun hclean hk => armLoadSextTail_wp hc hnoSp hwpSetup hv hclean hk

private theorem getRegOrZr_low64_reg (regs : Reg64s) (x : XReg) :
    regs.getRegOrZr (.low (.reg x) .W64) = (regs.getXReg x).toBitVec := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]

private theorem getRegOrZr_low64_xzr (regs : Reg64s) :
    regs.getRegOrZr (.low .XZR .W64) = 0#64 := rfl

private theorem getRegOrZr_low32_eq (regs : Reg64s) (rx : XRegOrXzr) :
    regs.getRegOrZr (.low rx .W32) = (regs.getRegOrZr (.low rx .W64)).setWidth 32 := by
  cases rx with
  | XZR => rfl
  | reg x =>
    rw [getRegOrZr_low64_reg]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take, hi]

private theorem armStoreValIn_wp [Host] {t : Ty} {pa : PArg Reg Empty ArmCond t}
    {v : Val t} {s : MachineData} {valSetup : List Instr} {rx : XRegOrXzr}
    (hpa : armStoreValInIns t pa = some (valSetup, rx))
    (hp : armMach.PArgHolds s t pa v)
    (hregs : ∀ r ∈ pa.gprs, r ∉ armScratch)
    (ht : t = .bool ∨ t = .bits 8 ∨ t = .bits 16 ∨ t = .bits 32 ∨ t = .bits 64) :
    _root_.Program.wp (emitClean valSetup) (fun s' =>
      rx ≠ .reg .X16 ∧
      (∃ w64 : BitVec 64, s'.regs.getRegOrZr (.low rx .W64) = w64 ∧ GprHolds w64 t v) ∧
      s'.dmem = s.dmem ∧ s'.status = s.status ∧
      (∀ x, x ≠ .X17 → s'.regs.getXReg x = s.regs.getXReg x) ∧ s'.regs.SP = s.regs.SP)
      (fun _ _ => False) s := by
  have ht' : t = .bool ∨ ∃ n, n ≤ 64 ∧ t = .bits n := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    all_goals exact Or.inr ⟨_, by decide, rfl⟩
  cases pa with
  | vec vr => exact vr.elim
  | flag cond =>
    simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
    rcases hpa with ⟨rfl, rfl⟩
    simp only [Machine.PArgHolds] at hp
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_mono (armCset64_wp .X17 cond s) ?_
    rintro s' rfl
    refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
      fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
    rw [getRegOrZr_low64_reg, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, hp]
    cases v <;> rfl
  | gpr r =>
    have hcases : (∃ x, r = .reg x ∧ valSetup = [] ∧ rx = .reg x) ∨
        (r = .SP ∧ valSetup = [armIselMovToXI .X17 .SP] ∧ rx = .reg .X17) := by
      cases r with
      | reg x =>
        rcases ht' with rfl | ⟨n, _, rfl⟩ <;>
          · simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
            exact Or.inl ⟨x, rfl, hpa.1.symm, hpa.2.symm⟩
      | SP =>
        rcases ht' with rfl | ⟨n, _, rfl⟩ <;>
          · simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
            exact Or.inr ⟨rfl, hpa.1.symm, hpa.2.symm⟩
    rcases hcases with ⟨x, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hx16 : XRegOrXzr.reg x ≠ .reg .X16 := fun h =>
        (xreg_ne_scratch_of_not_mem (hregs (.reg x) (by simp [PArg.gprs]))).1
          (by cases h; rfl)
      refine armWp_nil ⟨hx16, ⟨_, rfl, ?_⟩, rfl, rfl, fun _ _ => rfl, rfl⟩
      rw [getRegOrZr_low64_reg]
      exact hp
    · simp only [emitClean_cons, emitClean_nil]
      refine armWp_mono (armMovToX_wp .X17 .SP s) ?_
      rintro s' rfl
      refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
        fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
      rw [getRegOrZr_low64_reg, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec]
      simpa [Machine.PArgHolds, armMach, get_sp] using hp
  | imm c =>
    rcases ht' with rfl | ⟨n, hn64, rfl⟩
    · cases c
      · simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl⟩
        simp only [Machine.PArgHolds] at hp; subst hp
        refine armWp_nil ⟨by decide, ⟨0#64, by rfl, by rfl⟩, rfl, rfl, fun _ _ => rfl, rfl⟩
      · simp only [armStoreValInIns, Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl⟩
        simp only [Machine.PArgHolds] at hp; subst hp
        refine armWp_mono (armMovImm_wp .X17 1#64 s) ?_
        rintro s' rfl
        refine ⟨by decide, ⟨_, rfl, ?_⟩, rfl, rfl,
          fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
        rw [getRegOrZr_low64_reg, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec]; rfl
    · simp only [armStoreValInIns] at hpa
      split at hpa
      · rename_i hc0
        simp only [Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl⟩
        simp only [Machine.PArgHolds] at hp; subst hp
        have hc0' : c = 0#n := beq_iff_eq.mp hc0
        refine armWp_nil ⟨by decide, ⟨0#64, by rfl, hn64, ?_⟩, rfl, rfl, fun _ _ => rfl, rfl⟩
        rw [BitVec.setWidth_zero, hc0']
      · simp only [Option.some.injEq, Prod.mk.injEq] at hpa
        rcases hpa with ⟨rfl, rfl⟩
        simp only [Machine.PArgHolds] at hp; subst hp
        refine armWp_mono (armMovImm_wp .X17 (c.setWidth 64) s) ?_
        rintro s' rfl
        refine ⟨by decide, ⟨_, rfl, hn64, ?_⟩, rfl, rfl,
          fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl⟩
        rw [getRegOrZr_low64_reg, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
          BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_eq]

private theorem take_setWidth_32_low {k : Nat} (hk : k ≤ 32) (v : BitVec 64) :
    ((v.setWidth 32).take k) = v.setWidth k := by
  ext i hi; simp [BitVec.take, show (i : Nat) < 32 by omega]

private theorem armStoreDir_wp [Host] {t : Ty} {rx : XRegOrXzr} {addr : AddrExpr} {a : BitVec 64}
    {v : Val t} {s : MachineData} {dir : Instr}
    (hdir : armStoreDirI t rx addr = some dir) (hnoSp : ∃ r, addr.base = .low (.reg r) .W64)
    (heval : ∀ [Labels] p, addr.eval s p = (a, s))
    (hval : GprHolds (s.regs.getRegOrZr (.low rx .W64)) t v)
    (hok : storeOk s.dmem t a) :
    _root_.Program.wp [.instr dir] (fun s' =>
      s'.regs = s.regs ∧ s'.status = s.status ∧ s'.dmem = storeMem s.dmem t a v)
      (fun _ _ => False) s := by
  obtain ⟨r, hr⟩ := hnoSp
  rcases hok with ⟨i, hi⟩
  have h32 : s.regs.getRegOrZr (.low rx .W32) = (s.regs.getRegOrZr (.low rx .W64)).setWidth 32 :=
    getRegOrZr_low32_eq s.regs rx
  cases t with
  | bool =>
    simp only [armStoreDirI, Option.some.injEq] at hdir; subst hdir
    simp only [Ty.bytes, Ty.size] at hi
    refine armDirFallsTo_wp (by
      intro _ p next jmp P hk
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
        AddrExpr.checkSPAlignment, hr, heval p, MachineData.store, MemWidth.bytes, Effects.All]
      rw [hi]
      refine hk _ ⟨rfl, rfl, ?_⟩
      simp only [storeMem, Ty.bytes, Ty.size, toBits, GprHolds] at hval ⊢
      rw [h32, take_setWidth_32_low (by decide : 8 ≤ 32), hval]
      congr 2; cases v <;> rfl)
  | bits n =>
    have hns : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
      rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64))
        with h | h | h | h | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exfalso; revert hdir; simp [armStoreDirI, h1, h2, h3, h4]
    rcases hns with rfl | rfl | rfl | rfl <;>
      (simp only [armStoreDirI, Option.some.injEq] at hdir; subst hdir;
       simp only [Ty.bytes, Ty.size] at hi;
       refine armDirFallsTo_wp (by
         intro _ p next jmp P hk
         simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
           AddrExpr.checkSPAlignment, hr, heval p, MachineData.store, MemWidth.bytes, Effects.All]
         rw [hi]
         refine hk _ ⟨rfl, rfl, ?_⟩
         simp only [storeMem, Ty.bytes, Ty.size, toBits, GprHolds] at hval ⊢
         try rw [h32]
         try rw [take_setWidth_32_low (by decide : _ ≤ 32)]
         try (rw [BitVec.setWidth_eq] at hval)
         rw [hval.2]; rfl))
  | float _ | pair _ _ => simp [armStoreDirI] at hdir

private theorem armTy_of_armMemScale {t : Ty} {scale : Nat} (hsc : armMemScale t = some scale) :
    t = .bool ∨ t = .bits 8 ∨ t = .bits 16 ∨ t = .bits 32 ∨ t = .bits 64 := by
  match t with
  | .bool => exact Or.inl rfl
  | .bits 8 => exact Or.inr (Or.inl rfl)
  | .bits 16 => exact Or.inr (Or.inr (Or.inl rfl))
  | .bits 32 => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | .bits 64 => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | .bits n =>
    rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64))
      with hn | hn | hn | hn | ⟨h1, h2, h3, h4⟩
    · subst hn; exact Or.inr (Or.inl rfl)
    · subst hn; exact Or.inr (Or.inr (Or.inl rfl))
    · subst hn; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · subst hn; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exfalso; revert hsc; simp [armMemScale, h1, h2, h3, h4]
  | .float _ | .pair _ _ => simp [armMemScale] at hsc

theorem armStoreZextIdx_spec {h : Host} {k : Nat} {t : Ty} {pa : PArg Reg Empty ArmCond t}
    {base idx : Reg} {sc : AddrScale} {disp : Int64} {c : List Directive} {clob : FlagMask}
    {v : Val t} {vb : BitVec 64} {vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc_in : armStoreZextIdx t pa base idx sc disp = some (c, clob))
    (hpaRegs : ∀ r ∈ pa.gprs, r ∉ armScratch)
    (hbase : base ∉ armScratch) (hidx : idx ∉ armScratch)
    (hp : armMach.PArgHolds s t pa v)
    (hvb : GprHolds (armMach.getGpr s base) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s idx) (.bits 32) vi)
    (hok : storeOk (armMach.mem s) t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec)) :
    armMach.FallsTo armCondReads h k c armScratch [] clob s
      (fun s' => armMach.mem s' =
        storeMem (armMach.mem s) t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) v)
      post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  dsimp only [armStoreZextIdxIns] at hc
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hc
  rcases hc with ⟨scale, hsc, ⟨addrSetup, addr⟩, hsa, ⟨valSetup, rx⟩, hva, dir, hdir, rfl, rfl⟩
  have ht := armTy_of_armMemScale hsc
  rw [List.append_assoc]
  simp only [emitClean_append, emitClean_cons, emitClean_nil]
  refine armFallsTo_of_wp (armWp_append (armStoreValIn_wp hva hp hpaRegs ht) ?_)
  rintro s₁ ⟨hrx16, ⟨w64, hrx₁, hw64⟩, hdmem₁, hst₁, hx₁, hsp₁⟩
  obtain ⟨rb, ri, rfl, rfl, hnoSp, hwpAddr⟩ :=
    armSetupAddrZext_wp scale base idx sc disp s₁ hidx hsa
  have hrb17 : rb ≠ .X17 := (xreg_ne_scratch_of_not_mem hbase).2
  have hri17 : ri ≠ .X17 := (xreg_ne_scratch_of_not_mem hidx).2
  have hrb : (s₁.regs.getXReg rb).toBitVec = vb := by
    rw [hx₁ rb hrb17]; simpa [GprHolds, armMach, get_reg] using hvb.2
  have hri : (s₁.regs.getXReg ri).toBitVec.setWidth 32 = vi := by
    rw [hx₁ ri hri17]; simpa [GprHolds, armMach, get_reg] using hvi.2
  rw [hrb, hri] at hwpAddr
  refine armWp_append hwpAddr ?_
  rintro s₂ ⟨heval₂, hx₂, hsp₂, hdmem₂, hst₂, _⟩
  have hval₂ : GprHolds (s₂.regs.getRegOrZr (.low rx .W64)) t v := by
    cases rx with
    | XZR =>
      rw [getRegOrZr_low64_xzr]; rw [getRegOrZr_low64_xzr] at hrx₁
      rw [hrx₁]; exact hw64
    | reg rx' =>
      have hne16 : rx' ≠ .X16 := fun h => hrx16 (congrArg XRegOrXzr.reg h)
      rw [getRegOrZr_low64_reg, hx₂ rx' hne16]
      rw [getRegOrZr_low64_reg] at hrx₁
      rw [hrx₁]; exact hw64
  have hok₂ : storeOk s₂.dmem t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) := by
    rw [hdmem₂, hdmem₁]; exact hok
  refine armWp_mono (armStoreDir_wp hdir hnoSp heval₂ hval₂ hok₂) ?_
  rintro s₃ ⟨hregs₃, hst₃, hdmem₃⟩
  refine ⟨by simpa [armMach, hdmem₂, hdmem₁] using hdmem₃,
    armFrame_status_eq ?_ (by rw [hst₃, hst₂, hst₁])⟩
  intro r hr
  cases r with
  | SP => simp [get_sp, hregs₃, hsp₂, hsp₁]
  | reg x =>
    have hx16' : x ≠ .X16 := fun e => hr (by simp [e, armScratch])
    have hx17' : x ≠ .X17 := fun e => hr (by simp [e, armScratch])
    simp [get_reg, hregs₃, hx₂ x hx16', hx₁ x hx17']

theorem armStore_spec {h : Host} {k : Nat} {t : Ty} {pa : PArg Reg Empty ArmCond t}
    {a : AddrArg Reg} {c : List Directive} {clob : FlagMask} {v : Val t} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armStore t pa a = some (c, clob))
    (hregs : ∀ r ∈ pa.gprs ++ a.regs, r ∉ armScratch)
    (hp : armMach.PArgHolds s t pa v) (hok : storeOk (armMach.mem s) t (a.eval (get s))) :
    armMach.FallsTo armCondReads h k c armScratch [] clob s
      (fun s' => armMach.mem s' = storeMem (armMach.mem s) t (a.eval (get s)) v) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  dsimp only [armStoreIns] at hc
  have hscEx : ∃ scale, armMemScale t = some scale ∧
      (if (!armAddrValid scale a) = true then none
       else do
         let x ← armStoreValInIns t pa
         let dir ← armStoreDirI t x.2 (armSetupAddrIns scale a).2
         some (x.1 ++ (armSetupAddrIns scale a).1 ++ [dir], maskNone)) = some (ci, clob) := by
    cases h : armMemScale t with
    | none => simp [h] at hc
    | some sc => exact ⟨sc, rfl, by simpa [h] using hc⟩
  rcases hscEx with ⟨scale, hsc, hc'⟩
  have hvaValid : armAddrValid scale a = true := by
    cases h : armAddrValid scale a
    · simp [h] at hc'
    · rfl
  rw [show (!armAddrValid scale a) = false by simp [hvaValid]] at hc'
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at hc'
  rcases hc' with ⟨⟨valSetup, rx⟩, hva, dir, hdir, rfl, rfl⟩
  have ht := armTy_of_armMemScale hsc
  have hpaRegs : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr => hregs r (List.mem_append_left _ hr)
  have haRegs : ∀ r ∈ a.regs, r ∉ armScratch := fun r hr => hregs r (List.mem_append_right _ hr)
  rw [List.append_assoc]
  simp only [emitClean_append, emitClean_cons, emitClean_nil]
  refine armFallsTo_of_wp (armWp_append (armStoreValIn_wp hva hp hpaRegs ht) ?_)
  rintro s₁ ⟨hrx16, ⟨w64, hrx₁, hw64⟩, hdmem₁, hst₁, hx₁, hsp₁⟩
  have hsetup := armSetupAddr_wp scale a s₁ haRegs hvaValid
  generalize armSetupAddrIns scale a = sa at hdir hsetup
  rcases sa with ⟨addrSetup, addr⟩
  rcases hsetup with ⟨hnoSp, hwpAddr⟩
  have heqAddr : a.eval (get s₁) = a.eval (get s) := by
    cases a with
    | imm _ => rfl
    | baseDisp b disp =>
      simp only [AddrArg.eval]
      have hrb : b ∉ armScratch := haRegs b (by simp [AddrArg.regs])
      cases b with
      | SP => simp [get_sp, hsp₁]
      | reg rb =>
        have h17 : rb ≠ .X17 := (xreg_ne_scratch_of_not_mem hrb).2
        simp [get_reg, hx₁ rb h17]
    | baseIdxDisp b i sc disp =>
      cases b with
      | SP => simp [armAddrValid] at hvaValid
      | reg rb =>
        cases i with
        | SP => simp [armAddrValid] at hvaValid
        | reg ri =>
          have hrb : (.reg rb) ∉ armScratch := haRegs (.reg rb) (by simp [AddrArg.regs])
          have hri : (.reg ri) ∉ armScratch := haRegs (.reg ri) (by simp [AddrArg.regs])
          have hrb17 : rb ≠ .X17 := (xreg_ne_scratch_of_not_mem hrb).2
          have hri17 : ri ≠ .X17 := (xreg_ne_scratch_of_not_mem hri).2
          simp only [AddrArg.eval, get_reg, hx₁ rb hrb17, hx₁ ri hri17]
  refine armWp_append hwpAddr ?_
  rintro s₂ ⟨heval₂, hx₂, hsp₂, hdmem₂, hst₂, _⟩
  rw [heqAddr] at heval₂
  have hval₂ : GprHolds (s₂.regs.getRegOrZr (.low rx .W64)) t v := by
    cases rx with
    | XZR =>
      rw [getRegOrZr_low64_xzr]; rw [getRegOrZr_low64_xzr] at hrx₁
      rw [hrx₁]; exact hw64
    | reg rx' =>
      have hne16 : rx' ≠ .X16 := fun h => hrx16 (congrArg XRegOrXzr.reg h)
      rw [getRegOrZr_low64_reg, hx₂ rx' hne16]
      rw [getRegOrZr_low64_reg] at hrx₁
      rw [hrx₁]; exact hw64
  have hok₂ : storeOk s₂.dmem t (a.eval (get s)) := by rw [hdmem₂, hdmem₁]; exact hok
  refine armWp_mono (armStoreDir_wp hdir hnoSp heval₂ hval₂ hok₂) ?_
  rintro s₃ ⟨hregs₃, hst₃, hdmem₃⟩
  refine ⟨by simpa [armMach, hdmem₂, hdmem₁] using hdmem₃,
    armFrame_status_eq ?_ (by rw [hst₃, hst₂, hst₁])⟩
  intro r hr
  cases r with
  | SP => simp [get_sp, hregs₃, hsp₂, hsp₁]
  | reg x =>
    have hx16' : x ≠ .X16 := fun e => hr (by simp [e, armScratch])
    have hx17' : x ≠ .X17 := fun e => hr (by simp [e, armScratch])
    simp [get_reg, hregs₃, hx₂ x hx16', hx₁ x hx17']

/-! ## 4. Shared bitfield, shift/rotate, comparison, division, and carry/borrow lemmas -/

theorem evalUBFM_lsl {w : RegWidth} (x : w.type) {n : Nat} (hn : n < w.bits) :
    evalUBFM (w := w) x ((w.bits - n) % w.bits) (w.bits - 1 - n) = x <<< n := by
  cases w <;>
    simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hn ⊢ <;>
    ext i hi <;> grind

theorem evalUBFM_lsr {w : RegWidth} (x : w.type) {n : Nat} (hn : n < w.bits) :
    evalUBFM (w := w) x n (w.bits - 1) = x >>> n := by
  cases w <;>
    simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hn ⊢ <;>
    ext i hi <;> grind

theorem evalSBFM_asr {w : RegWidth} (x : w.type) {n : Nat} (hn : n < w.bits) :
    evalSBFM (w := w) x n (w.bits - 1) = x.sshiftRight n := by
  cases w <;>
    simp only [evalSBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hn ⊢ <;>
    ext i hi <;> grind

theorem evalUBFM_low {w : RegWidth} (x : w.type) {n : Nat} (hn0 : 0 < n) (hn : n ≤ w.bits) :
    evalUBFM (w := w) x 0 (n - 1) = (x.setWidth n).setWidth w.bits := by
  cases w <;>
    simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend]
      at hn0 hn ⊢ <;>
    ext i hi <;> grind

theorem evalUBFM_bit {w : RegWidth} (x : w.type) {k : Nat} (hk : k < w.bits) :
    evalUBFM (w := w) x k k = BitVec.ofNat w.bits (x.getLsbD k).toNat := by
  cases w <;>
    (simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] at hk ⊢;
     rw [Nat.mod_eq_of_lt hk]; simp only [Nat.le_refl, ↓reduceIte];
     apply BitVec.eq_of_getLsbD_eq; intro i hi
     simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
       BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, Nat.zero_add]
     by_cases hi0 : i = 0
     · subst hi0; simp [hk]; cases x[k] <;> decide
     · have hi1 : ¬ (i < 1) := by omega
       have hbi : (x.getLsbD k).toNat.testBit i = false :=
         Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
           (by cases x.getLsbD k <;> decide : (x.getLsbD k).toNat < 2 ^ 1)
           (Nat.pow_le_pow_right (by decide) (by omega)))
       simp [hi1, hbi])

theorem evalSBFM_low {w : RegWidth} (x : w.type) {n : Nat} (hn0 : 0 < n) (hn : n ≤ w.bits) :
    evalSBFM (w := w) x 0 (n - 1) = (x.setWidth n).signExtend w.bits := by
  cases w <;>
    simp only [evalSBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend]
      at hn0 hn ⊢ <;>
    ext i hi <;> grind

theorem evalUBFM_32_63 (x : BitVec 64) :
    evalUBFM (w := .W64) x 32 63 = x >>> 32 :=
  evalUBFM_lsr x (by decide)

theorem evalEXTR_rotr {w : RegWidth} (x : w.type) (k : Nat) :
    (let lsb := k % w.bits
     if lsb == 0 then x else (x <<< (w.bits - lsb)) ||| (x >>> lsb)) = x.rotateRight k := by
  cases w <;> simp only [RegWidth.bits, MemWidth.bits] <;> ext i hi <;> grind

theorem evalEXTR_fshr {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) {k : Nat} (hk : k < n) :
    (if k == 0 then b else (a <<< (n - k)) ||| (b >>> k)) = ((a ++ b) >>> k).extractLsb' 0 n := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem evalEXTR_fshl {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) {k : Nat}
    (hk : k < n) :
    (a <<< k) ||| (b >>> (n - k)) = ((a ++ b) <<< k).extractLsb' n n := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem shl_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (a : BitVec 32) (y : BitVec n) :
    (a <<< ((y.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).toNat % 32)).setWidth n =
      a.setWidth n <<< (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem lshr_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (x y : BitVec n) :
    ((x.setWidth 32).ushiftRight
      ((y.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).toNat % 32)).setWidth n =
      x >>> (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem ashr_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (x y : BitVec n) :
    ((x.signExtend 32).sshiftRight
      ((y.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).toNat % 32)).setWidth n =
      x.sshiftRight (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem rotr_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (x y : BitVec n) :
    let rep := x.setWidth 32 ||| (x.setWidth 32 <<< n)
    (rep.ushiftRight ((y.setWidth 32 &&& BitVec.ofNat 32 (n - 1)).toNat % 32)).setWidth n =
      x.rotateRight (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem rotl_subword_mask {n : Nat} (hn : n = 8 ∨ n = 16) (x y : BitVec n) :
    let rep := x.setWidth 32 ||| (x.setWidth 32 <<< n)
    let cnt := ((0#32 - y.setWidth 32) &&& BitVec.ofNat 32 (n - 1)).toNat % 32
    (rep.ushiftRight cnt).setWidth n = x.rotateLeft (y.toNat % n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

theorem armCmpCond_subs {n : Nat} (hn : n = 32 ∨ n = 64) (o : CmpOp) (x y : BitVec n) :
    (armCmpCond o).interp (StatusFlags.subs (x - y) x y) = o.evalBits x y := by
  simp only [armCmpCond, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
    StatusFlags.subs, StatusFlags.from_result, CmpOp.evalBits, BitVec.ult, BitVec.ule,
    BitVec.slt, BitVec.sle]
  rcases hn with rfl | rfl <;> cases o <;>
    grind [BitVec.unsigned, BitVec.signed]

theorem cmp_subword_unsigned {n : Nat} (hn : n = 8 ∨ n = 16) (o : CmpOp)
    (ho : armIsSignedCmp o = false) (x y : BitVec n) :
    o.evalBits (x.setWidth 32) (y.setWidth 32) = o.evalBits x y := by
  have hx := x.isLt; have hy := y.isLt
  have hinj : x.setWidth 32 = y.setWidth 32 ↔ x = y := by
    constructor
    · intro h; have := congrArg (BitVec.setWidth n) h
      rcases hn with rfl | rfl <;> simpa using this
    · rintro rfl; rfl
  rcases hn with rfl | rfl <;> cases o <;> simp only [armIsSignedCmp] at ho
  all_goals first
    | exact absurd ho (by decide)
    | (dsimp only [CmpOp.evalBits]; simp only [hinj, ne_eq])
    | (dsimp only [CmpOp.evalBits, BitVec.ult, BitVec.ule];
       simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
         Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 32)])

theorem setWidth_signExtend_self {n w : Nat} (hle : n ≤ w) (x : BitVec n) :
    (x.signExtend w).setWidth n = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
    show (i : Nat) < w by omega, decide_true, Bool.true_and, ↓reduceIte]

theorem cmp_subword_signed {n : Nat} (hn : n = 8 ∨ n = 16) (o : CmpOp)
    (ho : armIsSignedCmp o = true) (x y : BitVec n) :
    o.evalBits (x.signExtend 32) (y.signExtend 32) = o.evalBits x y := by
  have hle8 : 8 ≤ 32 := by decide
  have hle16 : 16 ≤ 32 := by decide
  rcases hn with rfl | rfl <;> cases o <;> simp only [armIsSignedCmp] at ho
  all_goals first
    | exact absurd ho (by decide)
    | simp [CmpOp.evalBits, BitVec.slt, BitVec.sle, BitVec.toInt_signExtend_of_le, hle8, hle16]

theorem umod_eq_sub {n : Nat} (a b : BitVec n) : a % b = a - (a / b) * b := by
  apply BitVec.eq_of_toNat_eq
  have h := BitVec.isLt a
  rw [BitVec.toNat_umod, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv]
  have hq : a.toNat / b.toNat * b.toNat ≤ a.toNat := Nat.div_mul_le_self _ _
  have := Nat.mod_add_div a.toNat b.toNat
  rw [Nat.mul_comm] at this
  rw [Nat.mod_eq_of_lt (a := a.toNat / b.toNat * b.toNat) (by omega)]
  rw [show 2 ^ n - a.toNat / b.toNat * b.toNat + a.toNat =
    2 ^ n + (a.toNat - a.toNat / b.toNat * b.toNat) by omega]
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (a := a.toNat - a.toNat / b.toNat * b.toNat) (by omega)]
  omega

theorem srem_eq_sub {n : Nat} (a b : BitVec n) : a.srem b = a - (a.sdiv b) * b := by
  rw [BitVec.srem_eq, BitVec.sdiv_eq]
  rcases a.msb <;> rcases b.msb <;> simp only [umod_eq_sub, BitVec.udiv_eq] <;>
    simp only [BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg, BitVec.sub_eq_add_neg,
      BitVec.neg_add]

theorem udiv_subword_32 {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    (a.setWidth 32 / b.setWidth 32).setWidth n = a / b := by
  have ha := a.isLt; have hb := b.isLt
  rcases hn with rfl | rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt (by omega : a.toNat < 4294967296),
      Nat.mod_eq_of_lt (by omega : b.toNat < 4294967296)] <;>
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha

theorem urem_subword_32 {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    (a.setWidth 32 % b.setWidth 32).setWidth n = a % b := by
  have ha := a.isLt; have hb := b.isLt
  rcases hn with rfl | rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_umod, Nat.mod_eq_of_lt (by omega : a.toNat < 4294967296),
      Nat.mod_eq_of_lt (by omega : b.toNat < 4294967296)] <;>
    (by_cases hb0 : b.toNat = 0
     · simp [hb0, ha]
     · exact Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hb0)) hb)

theorem setWidth_sub_of_le {n w : Nat} (hle : n ≤ w) (x y : BitVec w) :
    (x - y).setWidth n = x.setWidth n - y.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  rcases Nat.eq_or_lt_of_le hle with rfl | _
  · simp
  · obtain ⟨k, hk⟩ := Nat.pow_dvd_pow 2 hle
    have hx := x.isLt; have hy := y.isLt
    have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
    have hyk : y.toNat < 2 ^ n * k := hk ▸ hy
    have hqlt : y.toNat / 2 ^ n < k :=
      (Nat.mul_lt_mul_left hpow).mp (by have := Nat.mul_div_le y.toNat (2 ^ n); omega)
    have hdiv : y.toNat = 2 ^ n * (y.toNat / 2 ^ n) + y.toNat % 2 ^ n := by
      have := Nat.div_add_mod y.toNat (2 ^ n); omega
    have hsum_w : y.toNat + (2 ^ n * (k - y.toNat / 2 ^ n - 1) + (2 ^ n - y.toNat % 2 ^ n)) =
        2 ^ w := by
      have hmod := Nat.mod_lt y.toNat hpow
      have hk_rhs :
          2 ^ n * k = 2 ^ n * (k - y.toNat / 2 ^ n - 1) + 2 ^ n + 2 ^ n * (y.toNat / 2 ^ n) := by
        calc 2 ^ n * k = 2 ^ n * ((k - y.toNat / 2 ^ n - 1) + 1 + y.toNat / 2 ^ n) := by
                congr 1; omega
          _ = _ := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
    have hsub_w : 2 ^ w - y.toNat =
        2 ^ n * (k - y.toNat / 2 ^ n - 1) + (2 ^ n - y.toNat % 2 ^ n) :=
      Nat.sub_eq_of_eq_add (by omega)
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hle), hsub_w, Nat.add_assoc, Nat.mul_add_mod,
      Nat.add_mod (2 ^ n - y.toNat % 2 ^ n) x.toNat,
      Nat.add_mod (2 ^ n - y.toNat % 2 ^ n) (x.toNat % 2 ^ n),
      Nat.mod_mod]

theorem setWidth_neg_of_le {n w : Nat} (hle : n ≤ w) (x : BitVec w) :
    (-x).setWidth n = -(x.setWidth n) := by
  simpa [BitVec.zero_sub] using setWidth_sub_of_le hle 0#w x

theorem setWidth_mul_of_le {n w : Nat} (hle : n ≤ w) (x y : BitVec w) :
    (x * y).setWidth n = x.setWidth n * y.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hle), Nat.mul_mod]

theorem sdiv_subword_32 {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    ((a.signExtend 32).sdiv (b.signExtend 32)).setWidth n = a.sdiv b := by
  have hle : n ≤ 32 := by rcases hn with rfl | rfl <;> decide
  have hmsb : ∀ x : BitVec n, (x.signExtend 32).msb = x.msb := fun x => by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
    have h2 : x.msb = x.getLsbD (n - 1) := by
      rcases hn with rfl | rfl <;> exact BitVec.msb_eq_getLsbD_last x
    rw [h2]; rcases hn with rfl | rfl <;> simp
  have hpos : ∀ {x : BitVec n}, x.msb = false → x.signExtend 32 = x.setWidth 32 := fun {x} hx => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    by_cases hin : i < n
    · simp [hin]
    · have hge : x.getLsbD i = false :=
        Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hin, hx, hge]
  have hneg : ∀ {x : BitVec n}, x.msb = true → -(x.signExtend 32) = (-x).setWidth 32 :=
    fun {x} hx => by
    have hse : (x.signExtend 32).toInt = x.toInt := BitVec.toInt_signExtend_of_le hle
    have hxle := BitVec.le_toInt x
    have htoInt : (-(x.signExtend 32)).toInt = -x.toInt := by
      rw [BitVec.toInt_neg_of_ne_intMin (fun he => by
        have := congrArg BitVec.toInt he; rw [hse, BitVec.toInt_intMin] at this
        rcases hn with rfl | rfl <;> omega), hse]
    have hxn := x.isLt
    have hmdec := BitVec.msb_eq_decide x
    rw [hx] at hmdec
    have hhalf : 2 ^ (n - 1) ≤ x.toNat := by simpa using hmdec
    have hcondx := BitVec.toInt_eq_toNat_cond x
    have hxlt : x.toInt < 0 := by rcases hn with rfl | rfl <;> (split at hcondx <;> omega)
    have hx_sub : (-x.toInt).toNat = 2 ^ n - x.toNat := by
      rcases hn with rfl | rfl <;> (split at hcondx <;> omega)
    have hxne0 : x ≠ 0 := fun h0 => by subst h0; simp at hx
    have hxtoNat : x.toNat ≠ 0 := fun h0 => hxne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hneg_nat : (-(x.signExtend 32)).toNat = (-x.toInt).toNat := by
      have hcond := BitVec.toInt_eq_toNat_cond (-(x.signExtend 32))
      have hlt32 := (-(x.signExtend 32)).isLt
      rcases hn with rfl | rfl <;> (split at hcond <;> omega)
    apply BitVec.eq_of_toNat_eq
    simp [hneg_nat, hx_sub, BitVec.toNat_setWidth, BitVec.toNat_neg, hxtoNat,
      Nat.mod_eq_of_lt (by rcases hn with rfl | rfl <;> omega : 2 ^ n - x.toNat < 2 ^ 32)]
  rw [BitVec.sdiv_eq, BitVec.sdiv_eq, hmsb a, hmsb b]
  cases ha : a.msb <;> cases hb : b.msb <;>
    simp [hpos, hneg, setWidth_neg_of_le hle, udiv_subword_32 hn, ha, hb]

theorem srem_subword_32 {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    ((a.signExtend 32).srem (b.signExtend 32)).setWidth n = a.srem b := by
  have hle : n ≤ 32 := by rcases hn with rfl | rfl <;> decide
  rw [srem_eq_sub, srem_eq_sub, setWidth_sub_of_le hle, setWidth_mul_of_le hle,
    sdiv_subword_32 hn, setWidth_signExtend_self hle, setWidth_signExtend_self hle]

/-! ## 5. Non-`op` `NoLab` theorems -/

theorem armClearFlags_noLab (l : Sym) : Kraken.Directive.label l ∉ armGpr.clearFlags :=
  emitClean_noLab _ l

theorem armMov_noLab (rd rs : Reg) (l : Sym) : Kraken.Directive.label l ∉ armGpr.mov rd rs :=
  emitClean_noLab _ l

theorem armMovi_noLab (rd : Reg) (c : BitVec 64) (l : Sym) :
    Kraken.Directive.label l ∉ armGpr.movi rd c :=
  emitClean_noLab _ l

theorem armSetcc_noLab (rd : Reg) (c : ArmCond) (l : Sym) :
    Kraken.Directive.label l ∉ armGpr.setcc rd c :=
  emitClean_noLab _ l

theorem armJmp_noLab (tgt l : Sym) : Kraken.Directive.label l ∉ armGpr.jmp tgt :=
  emitClean_noLab _ l

theorem armJcc_noLab (c : ArmCond) (tgt l : Sym) : Kraken.Directive.label l ∉ armGpr.jcc c tgt :=
  emitClean_noLab _ l

theorem armJnzGpr_noLab (r : Reg) (tgt l : Sym) :
    Kraken.Directive.label l ∉ (armGpr.jnzGpr r tgt).1 :=
  emitClean_noLab _ l

theorem armLoad_noLab {t : Ty} {rd : Reg} {a : AddrArg Reg} {c : List Directive} {clob : FlagMask}
    (hc : armGpr.load t rd a = some (c, clob)) (l : Sym) : Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

theorem armLoadZextIdx_noLab {t : Ty} {rd base idx : Reg} {sc : AddrScale} {disp : Int64}
    {c : List Directive} {clob : FlagMask}
    (hc : armLoadZextIdx t rd base idx sc disp = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

theorem armLoadSext_noLab {m n : Nat} {rd : Reg} {a : AddrArg Reg} {c : List Directive}
    {clob : FlagMask} (hc : armGpr.loadSext m n rd a = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

theorem armLoadSextZextIdx_noLab {m n : Nat} {rd base idx : Reg} {sc : AddrScale}
    {disp : Int64} {c : List Directive} {clob : FlagMask}
    (hc : armLoadSextZextIdx m n rd base idx sc disp = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

theorem armStore_noLab {t : Ty} {pa : PArg Reg Empty ArmCond t} {a : AddrArg Reg}
    {c : List Directive} {clob : FlagMask} (hc : armGpr.store t pa a = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

theorem armStoreZextIdx_noLab {t : Ty} {pa : PArg Reg Empty ArmCond t} {base idx : Reg}
    {sc : AddrScale} {disp : Int64} {c : List Directive} {clob : FlagMask}
    (hc : armStoreZextIdx t pa base idx sc disp = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

theorem armTestOp_noLab {w : Nat} {neg : Bool}
    {pa pb : PArg Reg Empty ArmCond (.bits w)} {pd : PDst Reg Empty ArmCond .bool}
    {c : List Directive} {clob : FlagMask}
    (hc : armGpr.testOp w neg pa pb pd = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

end LeanQbe.T.Arm64


