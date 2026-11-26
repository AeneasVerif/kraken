module

public import LeanQbe.T.Amd64.IselLemmas2

/-!
# x64 Scalar `GprTarget` Proofs — Part 6 (`opBinLeaMul?` & `x64Gpr.testJcc`)

Verifies:
* `opBin_leaMul_z`: 1-cycle `lea` (+ optional `add`/`shl`) constant multiplication by
  `{3, 5, 6, 9, 10, 12}` at `32`-bit and `64`-bit widths, including `W32` upper-32 zeroing.
* `x64Gpr_testJcc_spec`: macro-fusable `test %r, %r; js/jns` sign-bit branches across
  `{8, 16, 32, 64}` widths and 32-bit sign checks in 64-bit registers (`0x80000000#64`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Amd64

open LeanQbe.T

public section

/-! ## 1. `opBinLeaMul?` Soundness & `W32` Upper-32 Zeroing -/

private theorem setWidth_shl_32 (v : BitVec 64) (sc : AddrScale) :
    (v <<< sc.shift).setWidth 32 = (v.setWidth 32) <<< sc.shift := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : i < 64 := by omega
  cases sc <;> simp [AddrScale.shift, hi, hi64] <;>
    first
    | (by_cases h : i < 1 <;> simp [h] <;> omega)
    | (by_cases h : i < 2 <;> simp [h] <;> omega)
    | (by_cases h : i < 3 <;> simp [h] <;> omega)

private theorem fallsTo_leaSIB_scale_z (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd ra : Reg64) (sc : AddrScale) :
    Directive.FallsTo (.instr (x64InsI w (.lea (regW w rd) (atSIB ra ra sc 0)))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits =
          (s.regs.get64 ra).setWidth w.bits + ((s.regs.get64 ra).setWidth w.bits <<< sc.shift) ∧
        (w = .W32 → rv = ((s.regs.get64 ra).setWidth w.bits +
          ((s.regs.get64 ra).setWidth w.bits <<< sc.shift)).setWidth 64) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ p _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [regW, t_step_simp, Reg64s.set]
    have hsib := atSIB_interp s.regs ra ra sc 0 p
    have hz : ((0 : Int64).toBitVec) = 0#64 := rfl
    simp only [hz, BitVec.add_zero] at hsib
    have h32 : (@AddrExpr.interp _ ⟨.W64⟩ (atSIB ra ra sc 0) s.regs p).zeroExtend 32 =
        (s.regs.get64 ra).setWidth 32 + ((s.regs.get64 ra).setWidth 32 <<< sc.shift) := by
      rw [BitVec.zeroExtend_eq_setWidth]
      have : ((@AddrExpr.interp _ ⟨.W64⟩ (atSIB ra ra sc 0) s.regs p).zeroExtend 64).setWidth
          32 = (@AddrExpr.interp _ ⟨.W64⟩ (atSIB ra ra sc 0) s.regs p).setWidth 32 := by
        rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide)]
      rw [← this, hsib, setWidth_add_le (by decide), setWidth_shl_32]
    rw [h32]
    exact hk _ ⟨_, by simp [Width.bits], (fun _ => by simp), rfl⟩
  · simp only [regW, t_step_simp, Reg64s.set, atSIB_interp]
    have hz : ((0 : Int64).toBitVec) = 0#64 := rfl
    simp only [hz, BitVec.add_zero]
    exact hk _ ⟨_, by simp [Width.bits, BitVec.setWidth_eq], (fun h => by cases h), rfl⟩

private theorem fallsTo_addSelf_z (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd : Reg64) :
    Directive.FallsTo (.instr (x64InsI w (.add (.reg (regW w rd)) (.reg (regW w rd))))) s
      (fun s' =>
        ∃ rv status, rv.setWidth w.bits =
            (s.regs.get64 rd).setWidth w.bits + (s.regs.get64 rd).setWidth w.bits ∧
          (w = .W32 → rv = ((s.regs.get64 rd).setWidth w.bits +
            (s.regs.get64 rd).setWidth w.bits).setWidth 64) ∧
          s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl <;>
    simp only [regW, t_step_simp, Reg64s.set, Effects.All, BitVec.zeroExtend_eq_setWidth]
  · exact hk _ ⟨_, _, by simp [Width.bits], (fun _ => by simp [Width.bits]), rfl⟩
  · exact hk _ ⟨_, _, by simp [Width.bits, BitVec.setWidth_eq], (fun h => by cases h), rfl⟩

private theorem fallsTo_shl2_z (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd : Reg64) :
    Directive.FallsTo (.instr (x64InsI w (.shl (.reg (regW w rd)) (.imm8 (.int64 2))))) s
      (fun s' =>
        ∃ rv status, rv.setWidth w.bits = ((s.regs.get64 rd).setWidth w.bits <<< 2) ∧
          (w = .W32 → rv = (((s.regs.get64 rd).setWidth w.bits <<< 2).setWidth 64)) ∧
          s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl <;>
    simp only [regW, t_step_simp, BitVec.zeroExtend_eq_setWidth, Effects.All, Reg64s.set]
  · have hm : ((Int64.ofInt 2).toBitVec.take 8).toNat &&& 0x1f = 2 := by decide
    try simp only [hm]
    try simp only [show ((Int64.toBitVec 2).take 8).toNat &&& 31 = 2 by decide]
    simp only [show (2 == 0) = false by decide, show (2 : Nat) < 32 by decide,
      show (2 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
    intro _af _of
    refine hk _ ⟨_, _, ?_, ?_, rfl⟩
    · simp [Width.bits]
    · intro _; simp [Width.bits]
  · have hm : ((Int64.ofInt 2).toBitVec.take 8).toNat &&& 0x3f = 2 := by decide
    try simp only [hm]
    try simp only [show ((Int64.toBitVec 2).take 8).toNat &&& 63 = 2 by decide]
    simp only [show (2 == 0) = false by decide, show (2 : Nat) < 64 by decide,
      show (2 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
    intro _af _of
    refine hk _ ⟨_, _, ?_, ?_, rfl⟩
    · simp [Width.bits, BitVec.setWidth_eq]
    · intro h; cases h

private theorem bv_mul3 {w : Width} (v : BitVec w.bits) : v + (v <<< 1) = v * 3#w.bits := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_mul,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.add_mod_mod, Nat.mul_mod_mod, show v.toNat + v.toNat * 2 ^ 1 = v.toNat * 3 by omega]

private theorem bv_mul5 {w : Width} (v : BitVec w.bits) : v + (v <<< 2) = v * 5#w.bits := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_mul,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.add_mod_mod, Nat.mul_mod_mod, show v.toNat + v.toNat * 2 ^ 2 = v.toNat * 5 by omega]

private theorem bv_mul9 {w : Width} (v : BitVec w.bits) : v + (v <<< 3) = v * 9#w.bits := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_mul,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.add_mod_mod, Nat.mul_mod_mod, show v.toNat + v.toNat * 2 ^ 3 = v.toNat * 9 by omega]

private theorem bv_mul6 {w : Width} (v : BitVec w.bits) :
    (v + (v <<< 1)) + (v + (v <<< 1)) = v * 6#w.bits := by
  rw [bv_mul3, ← BitVec.mul_add]
  congr 1; cases w <;> decide

private theorem bv_mul10 {w : Width} (v : BitVec w.bits) :
    (v + (v <<< 2)) + (v + (v <<< 2)) = v * 10#w.bits := by
  rw [bv_mul5, ← BitVec.mul_add]
  congr 1; cases w <;> decide

private theorem bv_mul12 {w : Width} (v : BitVec w.bits) :
    (v + (v <<< 1)) <<< 2 = v * 12#w.bits := by
  rw [bv_mul3]
  have h3 : 3 % 2 ^ w.bits = 3 := Nat.mod_eq_of_lt (by cases w <;> decide)
  have h12 : 12 % 2 ^ w.bits = 12 := Nat.mod_eq_of_lt (by cases w <;> decide)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    h3, h12]
  rw [Nat.mod_mul_mod, Nat.mul_assoc]

theorem opBinLeaMul_isMul {w : Width} {k : AluBinKind} {ra : Reg64} {cb : BitVec w.bits}
    {rd : Reg64} {res : List Instr × FlagMask} (h : opBinLeaMul? w k ra cb rd = some res) :
    k = .mul := by
  unfold opBinLeaMul? at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1.1
  · cases h

private theorem opBin_leaMul_one_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool)
    (w : Width) (hw : w = .W32 ∨ w = .W64) (ra rd : Reg64) (sc : AddrScale)
    (cb va : BitVec w.bits) (s : MachineData)
    (hra : (s.regs.get64 ra).setWidth w.bits = va)
    (hmul : va + (va <<< sc.shift) = va * cb) :
    _root_.Program.wp (emitClean [x64InsI w (.lea (regW w rd) (atSIB ra ra sc 0))])
      (OpPostZ z32 w rd (AluBinKind.mul.eval va cb) maskNone s) E s := by
  simp only [emitClean_cons, emitClean_nil, AluBinKind.eval]
  refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_leaSIB_scale_z w hw s rd ra sc)) ?_
  rintro s' ⟨rv, hrv, hrvz, rfl⟩
  exact OpPostZ.of_set64 (by rw [hrv, hra, hmul]) (fun _ hw' => by rw [hrvz hw', hra, hmul])
    (updFlags_of_status_eq rfl _)

private theorem opBin_leaMul_add_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool)
    (w : Width) (hw : w = .W32 ∨ w = .W64) (ra rd : Reg64) (sc : AddrScale)
    (cb va : BitVec w.bits) (s : MachineData)
    (hra : (s.regs.get64 ra).setWidth w.bits = va)
    (hmul : (va + (va <<< sc.shift)) + (va + (va <<< sc.shift)) = va * cb) :
    _root_.Program.wp
      (emitClean [x64InsI w (.lea (regW w rd) (atSIB ra ra sc 0)),
                  aluBinI w .add rd (.reg (regW w rd))])
      (OpPostZ z32 w rd (AluBinKind.mul.eval va cb) maskAll s) E s := by
  simp only [emitClean_cons, emitClean_nil, aluBinI, AluBinKind.eval]
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_leaSIB_scale_z w hw s rd ra sc)) ?_
  rintro s1 ⟨rv1, hrv1, _, rfl⟩
  refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_addSelf_z w hw _ rd)) ?_
  rintro s2 ⟨rv2, st2, hrv2, hrvz2, rfl⟩
  have hrd1 : (Reg64s.set64 s.regs rd rv1 |>.get64 rd).setWidth w.bits =
      va + (va <<< sc.shift) := by
    rw [Reg64s.get64_set64_same, hrv1, hra]
  refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv2, hrd1, hmul]),
    rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, fun _ hw' => by
    rw [Reg64s.get64_set64_same, hrvz2 hw', hrd1, hmul]⟩
  intro r hr; simp only [List.mem_cons, not_or] at hr
  rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
    Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]

private theorem opBin_leaMul_shl2_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool)
    (w : Width) (hw : w = .W32 ∨ w = .W64) (ra rd : Reg64) (va : BitVec w.bits) (s : MachineData)
    (hra : (s.regs.get64 ra).setWidth w.bits = va) :
    _root_.Program.wp
      (emitClean [x64InsI w (.lea (regW w rd) (atSIB ra ra .s2 0)),
                  x64InsI w (.shl (.reg (regW w rd)) (.imm8 (.int64 2)))])
      (OpPostZ z32 w rd (AluBinKind.mul.eval va 12#w.bits) maskAll s) E s := by
  simp only [emitClean_cons, emitClean_nil, AluBinKind.eval]
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_leaSIB_scale_z w hw s rd ra .s2)) ?_
  rintro s1 ⟨rv1, hrv1, _, rfl⟩
  refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_shl2_z w hw _ rd)) ?_
  rintro s2 ⟨rv2, st2, hrv2, hrvz2, rfl⟩
  have hmul : (va + (va <<< AddrScale.s2.shift)) <<< 2 = va * 12#w.bits := bv_mul12 va
  have hrd1 : (Reg64s.set64 s.regs rd rv1 |>.get64 rd).setWidth w.bits =
      va + (va <<< AddrScale.s2.shift) := by
    rw [Reg64s.get64_set64_same, hrv1, hra]
  refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv2, hrd1, hmul]),
    rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, fun _ hw' => by
    rw [Reg64s.get64_set64_same, hrvz2 hw', hrd1, hmul]⟩
  intro r hr; simp only [List.mem_cons, not_or] at hr
  rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
    Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]

theorem opBin_leaMul_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    (k : AluBinKind) (ra rd : Reg64) (cb va : BitVec w.bits) (s : MachineData)
    {c : List Instr} {clob : FlagMask}
    (hlea : opBinLeaMul? w k ra cb rd = some (c, clob))
    (hra : (s.regs.get64 ra).setWidth w.bits = va) :
    _root_.Program.wp (emitClean c) (OpPostZ z32 w rd (k.eval va cb) clob s) E s := by
  unfold opBinLeaMul? at hlea
  split at hlea
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_width_iff, beq_iff_eq] at hcond
    rcases hcond.1.1 with rfl
    have hw3264 : w = .W32 ∨ w = .W64 := hcond.1.2
    split at hlea
    · rename_i h3; have h3' := beq_iff_eq.mp h3; subst cb
      simp only [Option.some.injEq, Prod.mk.injEq] at hlea; rcases hlea with ⟨rfl, rfl⟩
      exact opBin_leaMul_one_z z32 w hw3264 ra rd .s2 3#w.bits va s hra (bv_mul3 va)
    · split at hlea
      · rename_i h5; have h5' := beq_iff_eq.mp h5; subst cb
        simp only [Option.some.injEq, Prod.mk.injEq] at hlea; rcases hlea with ⟨rfl, rfl⟩
        exact opBin_leaMul_one_z z32 w hw3264 ra rd .s4 5#w.bits va s hra (bv_mul5 va)
      · split at hlea
        · rename_i h9; have h9' := beq_iff_eq.mp h9; subst cb
          simp only [Option.some.injEq, Prod.mk.injEq] at hlea; rcases hlea with ⟨rfl, rfl⟩
          exact opBin_leaMul_one_z z32 w hw3264 ra rd .s8 9#w.bits va s hra (bv_mul9 va)
        · split at hlea
          · rename_i h6; have h6' := beq_iff_eq.mp h6; subst cb
            simp only [Option.some.injEq, Prod.mk.injEq] at hlea; rcases hlea with ⟨rfl, rfl⟩
            exact opBin_leaMul_add_z z32 w hw3264 ra rd .s2 6#w.bits va s hra (bv_mul6 va)
          · split at hlea
            · rename_i h10; have h10' := beq_iff_eq.mp h10; subst cb
              simp only [Option.some.injEq, Prod.mk.injEq] at hlea; rcases hlea with ⟨rfl, rfl⟩
              exact opBin_leaMul_add_z z32 w hw3264 ra rd .s4 10#w.bits va s hra (bv_mul10 va)
            · split at hlea
              · rename_i h12; have h12' := beq_iff_eq.mp h12; subst cb
                simp only [Option.some.injEq, Prod.mk.injEq] at hlea; rcases hlea with ⟨rfl, rfl⟩
                exact opBin_leaMul_shl2_z z32 w hw3264 ra rd va s hra
              · cases hlea
  · cases hlea

/-! ## 2. `x64Gpr.testJcc` (`test %r, %r; js/jns`) Soundness -/

private theorem bv_and_singleBit_eq_zero {n k : Nat} (hk : k < n) (v : BitVec n) :
    ((v &&& (1#n <<< k)) == 0#n) = !v.getLsbD k := by
  cases hbit : v.getLsbD k
  · have hzero : v &&& (1#n <<< k) = 0#n := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
      by_cases hik : i = k
      · subst hik; simp [hbit]
      · rcases Nat.lt_or_gt_of_ne hik with h | h
        · simp [Nat.not_le.mpr h]
        · simp [BitVec.getLsbD_one, show i - k ≠ 0 by omega]
    simp [hzero]
  · have hne : v &&& (1#n <<< k) ≠ 0#n := by
      intro heq
      have hg := congrArg (fun z => z.getLsbD k) heq
      have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hk, decide_true,
        Nat.lt_irrefl, Bool.true_and, Nat.sub_self, BitVec.getLsbD_one,
        hpos, BitVec.getLsbD_zero, hbit, Bool.and_true] at hg
      cases hg
    simp [hne]

private theorem signTestWidth_elim {n : Nat} {mask : BitVec n} {tw : Width}
    (h : signTestWidth? n mask = some tw) :
    tw.bits ≤ n ∧ 0 < tw.bits ∧ mask = 1#n <<< (tw.bits - 1) := by
  unfold signTestWidth? at h
  refine withWidth_elim h fun w hn hw => ?_
  subst hn; dsimp only at hw
  by_cases hs : (mask == (1#w.bits <<< (w.bits - 1))) = true
  · simp only [hs, ↓reduceIte, Option.some.injEq] at hw
    subst hw
    exact ⟨Nat.le_refl _, by cases w <;> decide, beq_iff_eq.mp hs⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hw
    cases w with
    | W64 =>
      dsimp only at hw
      by_cases hm32 : (mask == 0x80000000#64) = true
      · simp only [hm32, ↓reduceIte, Option.some.injEq] at hw
        subst hw
        exact ⟨by decide, by decide, (beq_iff_eq.mp hm32).trans (by decide)⟩
      · simp [hm32] at hw
    | W8 | W16 | W32 => simp at hw

private theorem fallsTo_test_reg_self (w : Width) (s : MachineData) (r : Reg64) :
    Directive.FallsTo (.instr (x64InsI w (.test (.reg (regW w r)) (.reg (regW w r))))) s
      (fun s' => ∃ af, s' = { s with
        status := testFlags ((s.regs.get64 r).setWidth w.bits)
          ((s.regs.get64 r).setWidth w.bits) af }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [regW, t_step_simp, Effects.All] <;> intro af <;>
    exact hk _ ⟨af, rfl⟩

theorem x64Gpr_testJcc_spec {h : x64Mach.Host} {k j : Nat} {neg : Bool} {n : Nat} {r : Reg64}
    {mask : BitVec n} {l : Sym} {c : List Directive} {clob : FlagMask} {v : BitVec n}
    {s : MachineData} {post : MachineState → Prop}
    (hins : x64Gpr.testJcc neg n r mask l = some (c, clob))
    (hc : c.IsInfixAt (x64Mach.prog h) k) (hl : x64Mach.labelAddr h l = x64Mach.addrOf h j)
    (_hr : r ∉ x64Scratch) (hv : GprHolds (x64Mach.getGpr s r) (.bits n) v)
    (hk : ∀ s', x64Mach.Frame x64Gpr.condReads s s' x64Scratch [] clob →
      x64Mach.mem s' = x64Mach.mem s →
      ((if neg then CmpOp.ne else CmpOp.eq).evalBits (v &&& mask) 0#n = true →
        x64Mach.Run h j s' post) ∧
      ((if neg then CmpOp.ne else CmpOp.eq).evalBits (v &&& mask) 0#n = false →
        x64Mach.Run h (k + c.length) s' post)) :
    x64Mach.Run h k s post := by
  letI := h
  dsimp only [x64Gpr, x64TestJcc] at hins
  obtain ⟨cins, hcins, rfl⟩ := emitCleanPair_eq_some.mp hins
  dsimp only [x64TestJccIns] at hcins
  cases hsw : signTestWidth? n mask with
  | none => simp [hsw] at hcins
  | some tw =>
    obtain ⟨hle, hpos, hmask⟩ := signTestWidth_elim hsw
    simp only [hsw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcins
    obtain ⟨rfl, rfl⟩ := hcins
    simp only [emitClean_cons, emitClean_nil] at hc hk
    have hvn : n ≤ 64 := by
      unfold signTestWidth? at hsw
      exact withWidth_elim hsw fun w hn _ => by subst hn; cases w <;> decide
    have hv_reg : (s.regs.get64 r).setWidth n = v := by
      simpa [GprHolds, x64Mach, hvn] using hv
    have htw : (s.regs.get64 r).setWidth tw.bits = v.setWidth tw.bits := by
      rw [← hv_reg, BitVec.setWidth_setWidth_of_le _ hle]
    have hw0 : _root_.Program.wp
        [.instr (x64InsI tw (.test (.reg (regW tw r)) (.reg (regW tw r))))]
        (fun s' => ∃ af, s' = { s with
          status := testFlags (v.setWidth tw.bits) (v.setWidth tw.bits) af })
        (fun _ _ => False) s := by
      simpa only [htw] using Directive.FallsTo.wp (fallsTo_test_reg_self tw s r)
    refine Program.wp.eventually hw0 (List.isInfixAt_singleton.mpr hc.cons.1) ?_
      (fun _ _ hf => hf.elim)
    rintro s1 ⟨af, rfl⟩
    refine Host.eventually_of_interp_cps hc.cons.2.cons.1 ?_
    simp only [t_step_simp, x64InsI]
    have hfr : x64Mach.Frame x64Gpr.condReads s
        { s with status := testFlags (v.setWidth tw.bits) (v.setWidth tw.bits) af }
        x64Scratch [] maskAll :=
      x64_frame_of_eq (fun _ _ => rfl) rfl (updFlags_maskAll s _)
    have hrun := hk { s with status := testFlags (v.setWidth tw.bits) (v.setWidth tw.bits) af }
      hfr rfl
    have hlab : Labels.label l = Host.addrOf j := hl
    have hbit_lt : tw.bits - 1 < n := by omega
    have hsf : (v.setWidth tw.bits).msb = v.getLsbD (tw.bits - 1) := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]
      simp [show tw.bits - 1 < tw.bits by omega]
    have hcond : (if neg then CondCode.s else CondCode.ns).interp
          (testFlags (v.setWidth tw.bits) (v.setWidth tw.bits) af) =
        (if neg then CmpOp.ne else CmpOp.eq).evalBits (v &&& mask) 0#n := by
      rw [hmask]
      have h0 : (v &&& (1#n <<< (tw.bits - 1)) = 0#n) ↔ v.getLsbD (tw.bits - 1) = false := by
        rw [← beq_iff_eq, bv_and_singleBit_eq_zero hbit_lt v]
        cases v.getLsbD (tw.bits - 1) <;> simp
      cases neg <;>
        simp [testFlags, StatusFlags.from_result, CondCode.interp, CmpOp.evalBits, h0, hsf]
    cases hres : (if neg then CmpOp.ne else CmpOp.eq).evalBits (v &&& mask) 0#n with
    | true =>
      have hcc : (if neg then CondCode.s else CondCode.ns).interp
          (testFlags (v.setWidth tw.bits) (v.setWidth tw.bits) af) = true := hcond.trans hres
      simp only [hcc, ↓reduceIte, Effects.All, hlab]
      exact hrun.1 hres
    | false =>
      have hcc : (if neg then CondCode.s else CondCode.ns).interp
          (testFlags (v.setWidth tw.bits) (v.setWidth tw.bits) af) = false := hcond.trans hres
      simp only [hcc, Bool.false_eq_true, ↓reduceIte, Effects.All]
      exact hrun.2 hres


/-! ## 5. `op_spec` Lemma: `opBin` -/

theorem AluBinKind.comm_eq {k : AluBinKind} (hk : k.isComm = true) {n : Nat} (a b : BitVec n) :
    k.eval a b = k.eval b a := by
  cases k <;> simp only [AluBinKind.isComm, AluBinKind.eval, reduceCtorEq] at hk ⊢
  · exact BitVec.add_comm a b
  · exact BitVec.and_comm a b
  · exact BitVec.or_comm a b
  · exact BitVec.xor_comm a b
  · exact BitVec.mul_comm a b

private abbrev OpPostAluZ (z32 : Bool) (w : Width) (k : AluBinKind) (rd : Reg64)
    (v : BitVec w.bits) (clob : FlagMask) (s s' : MachineData) : Prop :=
  OpPostZ z32 w rd v clob s s' ∧ (clob ≠ maskNone → AluFlagOk k w v s'.status)

private theorem opBin_regImm_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    (k : AluBinKind) (ra rd : Reg64) (cb va : BitVec w.bits) (s : MachineData)
    (hrd : rd ∉ x64Scratch) (hra_g : ra ∉ x64Scratch)
    (hra : (s.regs.get64 ra).setWidth w.bits = va) :
    let pre : List Instr := if ra == rd then [] else [movWI w rd ra]
    let pair : List Instr × FlagMask :=
      if w != .W64 || fitsImm32 (cb.setWidth 64) then
        (pre ++ [aluBinI w k rd (immBitsOp w cb)], maskAll)
      else
        ([moviI .r10 (cb.setWidth 64)] ++ pre ++ [aluBinI w k rd (.reg (regW w .r10))], maskAll)
    _root_.Program.wp (emitClean pair.1)
      (OpPostAluZ z32 w k rd (k.eval va cb) pair.2 s) E s := by
  intro pre pair
  have hrd10 := (ne_of_not_mem_x64Scratch hrd).1
  have hra10 := (ne_of_not_mem_x64Scratch hra_g).1
  dsimp only [pair, pre]
  split
  · simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    refine Program.wp.append (wp_optMovW w s rd ra hra) ?_
    rintro s1 ⟨hrd1, hr1, hm1, hz1, _⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_imm_z w k s1 rd cb)) ?_
    rintro s2 ⟨rv, st, hrv, hrvz, halu, rfl⟩
    refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩, fun _ hw => by
      rw [Reg64s.get64_set64_same, hrvz hw, hrd1]⟩, fun _ => by simpa [hrd1] using halu⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  · simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cb.setWidth 64))) ?_
    rintro s1 rfl
    have hra1 : ((s.regs.set64 .r10 (cb.setWidth 64)).get64 ra).setWidth w.bits = va := by
      rw [Reg64s.get64_set64_of_ne _ .r10 ra _ hra10.symm, hra]
    refine Program.wp.append
      (wp_optMovW w { s with regs := s.regs.set64 .r10 (cb.setWidth 64) } rd ra hra1) ?_
    rintro s2 ⟨hrd2, hr2, hm2, hz2, _⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_reg_z w k s2 rd .r10)) ?_
    rintro s3 ⟨rv, st, hrv, hrvz, halu, rfl⟩
    have h10 : (s2.regs.get64 .r10).setWidth w.bits = cb := by
      rw [hr2 .r10 hrd10.symm, Reg64s.get64_set64_same, setWidth_64_setWidth]
    refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd2, h10]),
      hm2, x64_frame_of_eq ?_ hz2 (updFlags_maskAll _ _)⟩, fun _ hw => by
      rw [Reg64s.get64_set64_same, hrvz hw, hrd2, h10]⟩, fun _ => by simpa [hrd2, h10] using halu⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr2 r hr.1,
      Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1)]

private theorem opBin_incDec_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    (k : AluBinKind) (hk : k = .add ∨ k = .sub)
    (isInc : Bool) (ra rd : Reg64) (va : BitVec w.bits) (s : MachineData)
    (hra : (s.regs.get64 ra).setWidth w.bits = va) :
    let pre : List Instr := if ra == rd then [] else [movWI w rd ra]
    let d : Instr := x64InsI w (if isInc then .inc (.reg (regW w rd)) else .dec (.reg (regW w rd)))
    let res := if isInc then va + 1#w.bits else va - 1#w.bits
    _root_.Program.wp (emitClean (pre ++ [d]))
      (OpPostAluZ z32 w k rd res maskDecInc s) E s := by
  intro pre d res; dsimp only [pre, d, res]
  simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
  refine Program.wp.append (wp_optMovW w s rd ra hra) ?_
  rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
  cases isInc
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_decW_z w s1 rd)) ?_
    rintro s2 ⟨rv, st, hrv, hrvz, hzf, hcf, rfl⟩
    refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskDecInc (by rw [hcf, hst1]))⟩, fun _ hw => by
      rw [Reg64s.get64_set64_same, hrvz hw, hrd1]⟩, fun _ => by
      rcases hk with rfl | rfl <;> simp only [AluFlagOk] <;> simpa [hrd1] using hzf⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  · simp only [↓reduceIte]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_incW_z w s1 rd)) ?_
    rintro s2 ⟨rv, st, hrv, hrvz, hzf, hcf, rfl⟩
    refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskDecInc (by rw [hcf, hst1]))⟩, fun _ hw => by
      rw [Reg64s.get64_set64_same, hrvz hw, hrd1]⟩, fun _ => by
      rcases hk with rfl | rfl <;> simp only [AluFlagOk] <;> simpa [hrd1] using hzf⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]

private theorem opBin_leaImm_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    (k : AluBinKind) (ra rd : Reg64) (cb va : BitVec w.bits) (s : MachineData)
    {c : List Instr} {clob : FlagMask}
    (hlea : opBinLeaImm? w k ra cb rd = some (c, clob))
    (hra : (s.regs.get64 ra).setWidth w.bits = va) :
    _root_.Program.wp (emitClean c) (OpPostAluZ z32 w k rd (k.eval va cb) clob s) E s := by
  unfold opBinLeaImm? at hlea
  split at hlea
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_width_iff, beq_iff_eq] at hcond
    have hw3264 : w = .W32 ∨ w = .W64 := hcond.1.1
    rcases hcond.2 with rfl | rfl
    · by_cases hfits : fitsImm32 (cb.signExtend 64) = true
      · simp only [beq_self_eq_true, ↓reduceIte, hfits, Option.some.injEq, Prod.mk.injEq] at hlea
        rcases hlea with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        have hoff : (Int64.ofBitVec (cb.signExtend 64)).toBitVec.setWidth w.bits = cb := by
          rw [Int64.toBitVec_ofBitVec, ← BitVec.truncate_eq_setWidth]
          exact truncate_signExtend_64 (width_bits_le_64 w) cb
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_leaDisp_z w hw3264 s rd ra _)) ?_
        rintro s' ⟨rv, hrv, hrvz, rfl⟩
        exact ⟨OpPostZ.of_set64 (by rw [hrv, hra, hoff]; rfl)
          (fun _ hw => by rw [hrvz hw, hra, hoff]; rfl) (updFlags_of_status_eq rfl _),
          fun h => absurd rfl h⟩
      · simp [hfits] at hlea
    · by_cases hfits : fitsImm32 ((-cb).signExtend 64) = true
      · have hne : (AluBinKind.sub == AluBinKind.add) = false := rfl
        simp only [hne, Bool.false_eq_true, ↓reduceIte, hfits,
          Option.some.injEq, Prod.mk.injEq] at hlea
        rcases hlea with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        have hoff : (Int64.ofBitVec ((-cb).signExtend 64)).toBitVec.setWidth w.bits = -cb := by
          rw [Int64.toBitVec_ofBitVec, ← BitVec.truncate_eq_setWidth]
          exact truncate_signExtend_64 (width_bits_le_64 w) (-cb)
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_leaDisp_z w hw3264 s rd ra _)) ?_
        rintro s' ⟨rv, hrv, hrvz, rfl⟩
        exact ⟨OpPostZ.of_set64
          (by rw [hrv, hra, hoff, AluBinKind.eval, BitVec.sub_eq_add_neg])
          (fun _ hw => by rw [hrvz hw, hra, hoff, AluBinKind.eval, BitVec.sub_eq_add_neg])
          (updFlags_of_status_eq rfl _), fun h => absurd rfl h⟩
      · have hne : (AluBinKind.sub == AluBinKind.add) = false := rfl
        simp [hne, hfits] at hlea
  · simp at hlea

private theorem opBin_leaReg_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    (k : AluBinKind) (ra rb rd : Reg64) (va vb : BitVec w.bits) (s : MachineData)
    {c : List Instr} {clob : FlagMask}
    (hlea : opBinLeaReg? w k ra rb rd = some (c, clob))
    (hra : (s.regs.get64 ra).setWidth w.bits = va)
    (hrb : (s.regs.get64 rb).setWidth w.bits = vb) :
    _root_.Program.wp (emitClean c) (OpPostAluZ z32 w k rd (k.eval va vb) clob s) E s := by
  unfold opBinLeaReg? at hlea
  split at hlea
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_width_iff, beq_iff_eq] at hcond
    have hk : k = .add := hcond.1.1.1
    subst hk
    have hw3264 : w = .W32 ∨ w = .W64 := hcond.1.1.2
    split at hlea
    · simp only [Option.some.injEq, Prod.mk.injEq] at hlea
      rcases hlea with ⟨rfl, rfl⟩
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_leaSIB_z w hw3264 s rd ra rb)) ?_
      rintro s' ⟨rv, hrv, hrvz, rfl⟩
      exact ⟨OpPostZ.of_set64 (by rw [hrv, hra, hrb]; rfl)
        (fun _ hw => by rw [hrvz hw, hra, hrb]; rfl) (updFlags_of_status_eq rfl _),
        fun h => absurd rfl h⟩
    · split at hlea
      · simp only [Option.some.injEq, Prod.mk.injEq] at hlea
        rcases hlea with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_leaSIB_z w hw3264 s rd rb ra)) ?_
        rintro s' ⟨rv, hrv, hrvz, rfl⟩
        exact ⟨OpPostZ.of_set64 (by rw [hrv, hra, hrb, BitVec.add_comm]; rfl)
          (fun _ hw => by rw [hrvz hw, hra, hrb, BitVec.add_comm]; rfl)
          (updFlags_of_status_eq rfl _), fun h => absurd rfl h⟩
      · simp at hlea
  · simp at hlea

private theorem opBin_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    (k : AluBinKind) {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {vh : VariantHint} {c : List Instr} {clob : FlagMask} {va vb : BitVec w.bits}
    {s : MachineData} (hz32 : z32 = true → w = .W32)
    (hc : opBinIns w k pa pb rd vh = some (c, clob))
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c) (OpPostAluZ z32 w k rd (k.eval va vb) clob s) E s := by
  have hdisp_spec (off : Int64)
      (hwf : ((w == .W32 || w == .W64) && fitsImm32 off.toBitVec) = true)
      (rb : Reg64)
      (heqv : (s.regs.get64 rb).setWidth w.bits + off.toBitVec.setWidth w.bits = k.eval va vb)
      (hc_eq : c = [x64InsI w (.lea (regW w rd) (atDisp rb off))]) (hcl : clob = maskNone) :
      _root_.Program.wp (emitClean c) (OpPostAluZ z32 w k rd (k.eval va vb) clob s) E s := by
    subst hc_eq; subst hcl
    simp only [emitClean_cons, emitClean_nil]
    have hw3264 : w = .W32 ∨ w = .W64 := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_width_iff] at hwf; exact hwf.1
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_leaDisp_z w hw3264 s rd rb off)) ?_
    rintro s' ⟨rv, hrv, hrvz, rfl⟩
    exact ⟨OpPostZ.of_set64 (by rw [hrv, heqv]) (fun _ hw => by rw [hrvz hw, heqv])
      (updFlags_of_status_eq rfl _), fun h => absurd rfl h⟩
  have himm_fb : ∀ (ra : Reg64) (cb va' : BitVec w.bits),
      ra ∉ x64Scratch → (s.regs.get64 ra).setWidth w.bits = va' →
      some ((opBinLeaImm? w k ra cb rd <|> opBinLeaMul? w k ra cb rd).getD
        (if w != .W64 || fitsImm32 (cb.setWidth 64) then
          ((if ra == rd then [] else [movWI w rd ra]) ++ [aluBinI w k rd (immBitsOp w cb)],
            maskAll)
        else
          ([moviI .r10 (cb.setWidth 64)] ++ (if ra == rd then [] else [movWI w rd ra]) ++
            [aluBinI w k rd (.reg (regW w .r10))], maskAll))) = some (c, clob) →
      _root_.Program.wp (emitClean c) (OpPostAluZ z32 w k rd (k.eval va' cb) clob s) E s := by
    intro ra cb va' hra_sc hra hm
    simp only [Option.some.injEq] at hm
    cases hlea : opBinLeaImm? w k ra cb rd with
    | some res =>
      rw [hlea] at hm; change res = (c, clob) at hm
      subst res; exact opBin_leaImm_z z32 w k ra rd cb va' s hlea hra
    | none =>
      rw [hlea] at hm
      cases hmul : opBinLeaMul? w k ra cb rd with
      | some res =>
        rw [hmul] at hm; change res = (c, clob) at hm; subst res
        have hkmul := opBinLeaMul_isMul hmul
        refine Program.wp.mono (opBin_leaMul_z z32 w k ra rd cb va' s hmul hra) ?_
        rintro s' hpost; exact ⟨hpost, fun _ => by subst hkmul; trivial⟩
      | none =>
        have hor : (none <|> (none : Option (List Instr × FlagMask))) = none := rfl
        rw [hmul, hor, Option.getD_none] at hm
        have hpair := @opBin_regImm_z _ E z32 w k ra rd cb va' s hrd hra_sc hra
        dsimp +zetaHave only at hpair; rw [hm] at hpair; exact hpair
  have hcore : ∀ (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (va vb : BitVec w.bits),
      x64Mach.PArgHolds s (.bits w.bits) pa va → x64Mach.PArgHolds s (.bits w.bits) pb vb →
      (∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch) →
      (match pa, pb with
      | .imm ca, .imm cb => some ([moviI rd ((k.eval ca cb).setWidth 64)], maskNone)
      | .gpr ra, .gpr rb =>
        if ra == rd then some ([aluBinI w k rd (.reg (regW w rb))], maskAll)
        else if k.isComm && rb == rd then some ([aluBinI w k rd (.reg (regW w ra))], maskAll)
        else if k == .sub && rb == rd then
          some ([x64InsI w (.neg (.reg (regW w rd))),
                 aluBinI w .add rd (.reg (regW w ra))], maskAll)
        else match opBinLeaReg? w k ra rb rd with
          | some res => some res
          | none =>
            if rb != rd then
              some ([movWI w rd ra, aluBinI w k rd (.reg (regW w rb))], maskAll)
            else
              some ([movWI w .r11 ra, aluBinI w k .r11 (.reg (regW w rb)),
                     movWI w rd .r11], maskAll)
      | .gpr ra, .imm cb =>
        some ((opBinLeaImm? w k ra cb rd <|> opBinLeaMul? w k ra cb rd).getD
          (if w != .W64 || fitsImm32 (cb.setWidth 64) then
            ((if ra == rd then [] else [movWI w rd ra]) ++
              [aluBinI w k rd (immBitsOp w cb)], maskAll)
          else
            ([moviI .r10 (cb.setWidth 64)] ++ (if ra == rd then [] else [movWI w rd ra]) ++
              [aluBinI w k rd (.reg (regW w .r10))], maskAll)))
      | .imm ca, .gpr rb =>
        if k == .sub && ca == 0 then
          some ((if rb == rd then [] else [movWI w rd rb]) ++
            [x64InsI w (.neg (.reg (regW w rd)))], maskAll)
        else if k.isComm then
          some ((opBinLeaImm? w k rb ca rd <|> opBinLeaMul? w k rb ca rd).getD
            (if w != .W64 || fitsImm32 (ca.setWidth 64) then
              ((if rb == rd then [] else [movWI w rd rb]) ++
                [aluBinI w k rd (immBitsOp w ca)], maskAll)
            else
              ([moviI .r10 (ca.setWidth 64)] ++ (if rb == rd then [] else [movWI w rd rb]) ++
                [aluBinI w k rd (.reg (regW w .r10))], maskAll)))
        else
          some ([moviI .r11 (ca.setWidth 64), aluBinI w .sub .r11 (.reg (regW w rb)),
                 movWI w rd .r11], maskAll)
      | _, _ => none) = some (c, clob) →
      _root_.Program.wp (emitClean c) (OpPostAluZ z32 w k rd (k.eval va vb) clob s) E s := by
    intro pa' pb' va' vb' hpa' hpb' hargs' hm
    cases pa' <;> cases pb' <;> simp only at hm <;> try contradiction
    · rename_i ra rb; have hra := hpa'.2; have hrb := hpb'.2
      by_cases h1 : ra == rd
      · have h1eq := (beq_reg64_iff ra rd).1 h1; subst ra
        simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_reg_z w k s rd rb)) ?_
        rintro s' ⟨rv, st, hrv, hrvz, halu, rfl⟩
        exact ⟨OpPostZ.of_set64 (by rw [hrv, hra, hrb]) (fun _ hw => by rw [hrvz hw, hra, hrb])
          (updFlags_maskAll _ _), fun _ => by simpa [hra, hrb] using halu⟩
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hm
        by_cases h2 : k.isComm && (rb == rd)
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          simp only [Bool.and_eq_true, beq_reg64_iff] at h2
          rcases h2 with ⟨hcomm, hrb_eq⟩; subst rb
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_reg_z w k s rd ra)) ?_
          rintro s' ⟨rv, st, hrv, hrvz, halu, rfl⟩
          exact ⟨OpPostZ.of_set64 (by rw [hrv, hrb, hra, AluBinKind.comm_eq hcomm])
            (fun _ hw => by rw [hrvz hw, hrb, hra, AluBinKind.comm_eq hcomm])
            (updFlags_maskAll _ _), fun _ => by
              simpa [hrb, hra, AluBinKind.comm_eq hcomm] using halu⟩
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hm
          by_cases h3 : (k == .sub) && (rb == rd)
          · simp only [h3, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩
            simp only [emitClean_cons, emitClean_nil]
            have h3' : k = .sub ∧ rb = rd := by cases k <;> simp_all [beq_reg64_iff]
            rcases h3' with ⟨rfl, rfl⟩
            have hra_ne : ra ≠ rb := fun h => h1 ((beq_reg64_iff ra rb).2 h)
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_negW w s rb)) ?_
            rintro s1 ⟨rv1, st1, hrv1, rfl⟩
            refine Program.wp.mono
              (Directive.FallsTo.wp (fallsTo_aluBinIns_reg_z w .add _ rb ra)) ?_
            rintro s2 ⟨rv2, st2, hrv2, hrv2z, halu, rfl⟩
            have hres : rv2.setWidth w.bits = va' - vb' := by
              rw [hrv2, Reg64s.get64_set64_same, hrv1, hrb,
                Reg64s.get64_set64_of_ne _ rb ra _ hra_ne.symm, hra, AluBinKind.eval,
                BitVec.add_comm, ← BitVec.sub_eq_add_neg]
            have hadd : rv1.setWidth w.bits +
                ((s.regs.set64 rb rv1).get64 ra).setWidth w.bits = va' - vb' := by
              rw [hrv1, hrb, Reg64s.get64_set64_of_ne _ rb ra _ hra_ne.symm, hra,
                BitVec.add_comm, ← BitVec.sub_eq_add_neg]
            refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same]; exact hres),
              rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, fun _ hw => by
              rw [Reg64s.get64_set64_same, hrv2z hw, ← hrv2, hres]; rfl⟩, fun _ => by
              simp only [AluFlagOk, AluBinKind.eval] at halu ⊢
              simp only [Reg64s.get64_set64_same] at halu
              simp only [hadd] at halu; exact halu⟩
            · intro r hr; simp only [List.mem_cons, not_or] at hr
              rw [Reg64s.get64_set64_of_ne _ rb r _ (Ne.symm hr.1),
                Reg64s.get64_set64_of_ne _ rb r _ (Ne.symm hr.1)]
          · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hm
            cases hlea : opBinLeaReg? w k ra rb rd with
            | some res =>
              rw [hlea] at hm; simp only [Option.some.injEq] at hm; subst res
              exact opBin_leaReg_z z32 w k ra rb rd va' vb' s hlea hra hrb
            | none =>
              rw [hlea] at hm; dsimp only at hm
              by_cases h4 : rb != rd
              · simp only [h4, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
                rcases hm with ⟨rfl, rfl⟩
                simp only [emitClean_cons, emitClean_nil]
                have hrb_ne := (bne_reg64_iff rb rd).1 h4
                refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW w s rd ra)) ?_
                rintro s1 rfl
                refine Program.wp.mono
                  (Directive.FallsTo.wp (fallsTo_aluBinIns_reg_z w k _ rd rb)) ?_
                rintro s2 ⟨rv2, st2, hrv2, hrv2z, halu, rfl⟩
                have hres : rv2.setWidth w.bits = k.eval va' vb' := by
                  rw [hrv2, Reg64s.get64_set64_same, setWidth_64_setWidth, hra,
                    Reg64s.get64_set64_of_ne _ rd rb _ hrb_ne.symm, hrb]
                refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same]; exact hres),
                  rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, fun _ hw => by
                  rw [Reg64s.get64_set64_same, hrv2z hw, Reg64s.get64_set64_same,
                    setWidth_64_setWidth, hra, Reg64s.get64_set64_of_ne _ rd rb _ hrb_ne.symm,
                    hrb]⟩, fun _ => by
                  simpa [Reg64s.get64_set64_same, setWidth_64_setWidth, hra,
                    Reg64s.get64_set64_of_ne _ rd rb _ hrb_ne.symm, hrb] using halu⟩
                · intro r hr; simp only [List.mem_cons, not_or] at hr
                  rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
                    Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
              · simp only [h4, Bool.false_eq_true, ↓reduceIte,
                  Option.some.injEq, Prod.mk.injEq] at hm
                rcases hm with ⟨rfl, rfl⟩
                simp only [emitClean_cons, emitClean_nil]
                have hrb11 := (ne_of_not_mem_x64Scratch (hargs' rb (by simp [PArg.gprs]))).2
                refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW w s .r11 ra)) ?_
                rintro s1 rfl
                refine Program.wp.cons
                  (Directive.FallsTo.wp (fallsTo_aluBinIns_reg_z w k _ .r11 rb)) ?_
                rintro s2 ⟨rv2, st2, hrv2, _, halu, rfl⟩
                refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ rd .r11)) ?_
                rintro s3 rfl
                have h11 : (rv2.setWidth w.bits) = k.eval va' vb' := by
                  rw [hrv2, Reg64s.get64_set64_same, setWidth_64_setWidth, hra,
                    Reg64s.get64_set64_of_ne _ .r11 rb _ hrb11.symm, hrb]
                refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by
                    rw [Reg64s.get64_set64_same, setWidth_64_setWidth,
                      Reg64s.get64_set64_same, h11]),
                  rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, fun _ hw => by
                  subst hw; rw [Reg64s.get64_set64_same, Reg64s.get64_set64_same, h11]⟩,
                  fun _ => by
                    simpa [Reg64s.get64_set64_same, setWidth_64_setWidth, hra,
                      Reg64s.get64_set64_of_ne _ .r11 rb _ hrb11.symm, hrb] using halu⟩
                · intro r hr; simp only [List.mem_cons, not_or] at hr
                  rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
                    Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
                    Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1)]
    · rename_i ra cb; rcases hpb' with rfl
      exact himm_fb ra cb va' (hargs' ra (by simp [PArg.gprs])) hpa'.2 hm
    · rename_i ca rb; rcases hpa' with rfl; have hrb := hpb'.2
      split at hm
      · rename_i hsub0
        have hsub0' : k = .sub ∧ ca = 0#w.bits := by cases k <;> simp_all [beq_iff_eq]
        rcases hsub0' with ⟨rfl, rfl⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
        simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
        rw [AluBinKind.eval, BitVec.zero_sub]
        refine Program.wp.append (wp_optMovW w s rd rb hrb) ?_
        rintro s1 ⟨hrd1, hr1, hm1, hz1, _⟩
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_negW_z w s1 rd)) ?_
        rintro s2 ⟨rv, st, hrv, hrvz, hzf, rfl⟩
        refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
          hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩, fun _ hw => by
          rw [Reg64s.get64_set64_same, hrvz hw, hrd1]⟩, fun _ => by
          simpa [AluFlagOk, hrd1] using hzf⟩
        intro r hr; simp only [List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
      · split at hm
        · rename_i hcomm
          rw [AluBinKind.comm_eq hcomm]
          exact himm_fb rb ca vb' (hargs' rb (by simp [PArg.gprs])) hrb hm
        · rename_i hnotcomm
          have hk : k = .sub := by cases k <;> simp_all [AluBinKind.isComm]
          subst hk
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          have hrb11 := (ne_of_not_mem_x64Scratch (hargs' rb (by simp [PArg.gprs]))).2
          refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r11 (ca.setWidth 64))) ?_
          rintro s1 rfl
          refine Program.wp.cons
            (Directive.FallsTo.wp (fallsTo_aluBinIns_reg_z w .sub _ .r11 rb)) ?_
          rintro s2 ⟨rv2, st2, hrv2, _, halu, rfl⟩
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ rd .r11)) ?_
          rintro s3 rfl
          have h11 : rv2.setWidth w.bits = ca - vb' := by
            rw [hrv2, Reg64s.get64_set64_same, setWidth_64_setWidth,
              Reg64s.get64_set64_of_ne _ .r11 rb _ hrb11.symm, hrb]; simp [AluBinKind.eval]
          refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by
              rw [Reg64s.get64_set64_same, setWidth_64_setWidth, Reg64s.get64_set64_same, h11]
              simp [AluBinKind.eval]),
            rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, fun _ hw => by
            subst hw; rw [Reg64s.get64_set64_same, Reg64s.get64_set64_same, h11]
            simp [AluBinKind.eval]⟩, fun _ => by
            simp only [AluFlagOk, AluBinKind.eval, Width.bits] at halu ⊢
            simp only [Reg64s.get64_set64_same, setWidth_64_setWidth,
              Reg64s.get64_set64_of_ne _ .r11 rb _ hrb11.symm, hrb] at halu
            exact halu⟩
          · intro r hr; simp only [List.mem_cons, not_or] at hr
            rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
              Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
              Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1)]
    · rename_i ca cb; rcases hpa' with rfl; rcases hpb' with rfl
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono
        (Directive.FallsTo.wp (fallsTo_moviD s rd ((k.eval ca cb).setWidth 64))) ?_
      rintro s' rfl
      exact ⟨OpPostZ.of_set64 (setWidth_64_setWidth w _) (fun _ _ => rfl)
        (updFlags_of_status_eq rfl _), fun h => absurd rfl h⟩
  unfold opBinIns at hc; dsimp +zetaHave only at hc
  cases vh with
  | default | adcx | adox | mulxFast =>
    cases pa with
    | vec _ => simp at hc
    | gpr ra =>
      cases pb with
      | vec _ => simp at hc
      | gpr rb => dsimp +zetaHave only at hc; exact hcore (.gpr ra) (.gpr rb) va vb hpa hpb hargs hc
      | imm cb => dsimp +zetaHave only at hc; exact hcore (.gpr ra) (.imm cb) va vb hpa hpb hargs hc
    | imm ca =>
      cases pb with
      | vec _ => simp at hc
      | gpr rb => dsimp +zetaHave only at hc; exact hcore (.imm ca) (.gpr rb) va vb hpa hpb hargs hc
      | imm cb => dsimp +zetaHave only at hc; exact hcore (.imm ca) (.imm cb) va vb hpa hpb hargs hc
  | disp off =>
    by_cases hwf : ((w == .W32 || w == .W64) && fitsImm32 off.toBitVec) = true
    · simp only [hwf, ↓reduceIte] at hc
      cases k <;> cases pa <;> cases pb <;> (try dsimp +zetaHave only at hc) <;> (
        try (rename_i ra rb; exact hcore (.gpr ra) (.gpr rb) va vb hpa hpb hargs hc);
        try (rename_i ra cb; exact hcore (.gpr ra) (.imm cb) va vb hpa hpb hargs hc);
        try (rename_i ca rb; exact hcore (.imm ca) (.gpr rb) va vb hpa hpb hargs hc);
        try (rename_i ca cb; exact hcore (.imm ca) (.imm cb) va vb hpa hpb hargs hc);
        try contradiction)
      · rename_i rb cb; rcases hpb with rfl
        by_cases hoff : (off.toBitVec.setWidth w.bits == cb) = true
        · simp only [hoff, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          exact hdisp_spec off hwf rb (by rw [hpa.2, beq_iff_eq.mp hoff]; rfl) hc.1.symm hc.2.symm
        · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.gpr rb) (.imm cb) va cb hpa rfl hargs hc
      · rename_i ca rb; rcases hpa with rfl
        by_cases hoff : (off.toBitVec.setWidth w.bits == ca) = true
        · simp only [hoff, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          exact hdisp_spec off hwf rb
            (by rw [hpb.2, beq_iff_eq.mp hoff, AluBinKind.eval, BitVec.add_comm])
            hc.1.symm hc.2.symm
        · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.imm ca) (.gpr rb) ca vb rfl hpb hargs hc
      · rename_i rb cb; rcases hpb with rfl
        by_cases hoff : ((-off.toBitVec).setWidth w.bits == cb) = true
        · simp only [hoff, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          have hn : off.toBitVec.setWidth w.bits = -cb := by
            rw [← beq_iff_eq.mp hoff, setWidth_neg_le (width_bits_le_64 w), BitVec.neg_neg]
          exact hdisp_spec off hwf rb
            (by rw [hpa.2, hn, AluBinKind.eval, BitVec.sub_eq_add_neg]) hc.1.symm hc.2.symm
        · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.gpr rb) (.imm cb) va cb hpa rfl hargs hc
    · simp only [hwf, Bool.false_eq_true, ↓reduceIte] at hc
      cases pa with
      | vec _ => simp at hc
      | gpr ra =>
        cases pb with
        | vec _ => simp at hc
        | gpr rb =>
          dsimp +zetaHave only at hc; exact hcore (.gpr ra) (.gpr rb) va vb hpa hpb hargs hc
        | imm cb =>
          dsimp +zetaHave only at hc; exact hcore (.gpr ra) (.imm cb) va vb hpa hpb hargs hc
      | imm ca =>
        cases pb with
        | vec _ => simp at hc
        | gpr rb =>
          dsimp +zetaHave only at hc; exact hcore (.imm ca) (.gpr rb) va vb hpa hpb hargs hc
        | imm cb =>
          dsimp +zetaHave only at hc; exact hcore (.imm ca) (.imm cb) va vb hpa hpb hargs hc
  | decInc =>
    cases k <;> cases pa <;> cases pb <;> (try dsimp +zetaHave only at hc) <;> (
      try (rename_i ra rb; exact hcore (.gpr ra) (.gpr rb) va vb hpa hpb hargs hc);
      try (rename_i ra cb; exact hcore (.gpr ra) (.imm cb) va vb hpa hpb hargs hc);
      try (rename_i ca rb; exact hcore (.imm ca) (.gpr rb) va vb hpa hpb hargs hc);
      try (rename_i ca cb; exact hcore (.imm ca) (.imm cb) va vb hpa hpb hargs hc);
      try contradiction)
    · rename_i ra cb; rcases hpb with rfl
      by_cases h1 : (cb == 1#w.bits) = true
      · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h1 with rfl
        exact opBin_incDec_z z32 w .add (Or.inl rfl) true ra rd va s hpa.2
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases h2 : (cb == -1#w.bits) = true
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h2 with rfl
          simpa [AluBinKind.eval, BitVec.sub_eq_add_neg] using
            opBin_incDec_z z32 w .add (Or.inl rfl) false ra rd va s hpa.2
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.gpr ra) (.imm cb) va cb hpa rfl hargs hc
    · rename_i ca rb; rcases hpa with rfl
      by_cases h1 : (ca == 1#w.bits) = true
      · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h1 with rfl
        simpa [AluBinKind.eval, BitVec.add_comm] using
          opBin_incDec_z z32 w .add (Or.inl rfl) true rb rd vb s hpb.2
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hc
        exact hcore (.imm ca) (.gpr rb) ca vb rfl hpb hargs hc
    · rename_i ra cb; rcases hpb with rfl
      by_cases h1 : (cb == 1#w.bits) = true
      · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h1 with rfl
        exact opBin_incDec_z z32 w .sub (Or.inr rfl) false ra rd va s hpa.2
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases h2 : (cb == -1#w.bits) = true
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h2 with rfl
          simpa [AluBinKind.eval, BitVec.sub_eq_add_neg, BitVec.neg_neg] using
            opBin_incDec_z z32 w .sub (Or.inr rfl) true ra rd va s hpa.2
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.gpr ra) (.imm cb) va cb hpa rfl hargs hc

theorem opBin_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (k : AluBinKind)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {vh : VariantHint}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opBinIns w k pa pb rd vh = some (c, clob))
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (k.eval va vb) clob s) E s :=
  Program.wp.mono (opBin_z false w k (fun h => by cases h) hc hrd hargs hpa hpb) fun _ h => h.1.1

theorem opBin_zero32_spec [Host] {E : Int64 → MachineData → Prop} (k : AluBinKind)
    {pa pb : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64} {vh : VariantHint}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec 32} {s : MachineData}
    (hc : opBinIns .W32 k pa pb rd vh = some (c, clob))
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits 32) pa va)
    (hpb : x64Mach.PArgHolds s (.bits 32) pb vb) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd (k.eval va vb) clob s) E s :=
  Program.wp.mono (opBin_z true .W32 k (fun _ => rfl) hc hrd hargs hpa hpb) fun _ h => h.1

theorem opBin_aluZero_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (k : AluBinKind)
    (hk : k ≠ .mul) (eqNe : Bool) (heq : eqNe = (k == .add || k == .sub))
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {vh : VariantHint}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hcl : clob ≠ maskNone)
    (hc : opBinIns w k pa pb rd vh = some (c, clob))
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c)
      (fun s' => OpPost1 (.bits w.bits) rd (k.eval va vb) clob s s' ∧
        (w = .W32 → x64Mach.getGpr s' rd = (k.eval va vb).setWidth 64) ∧
        FlagCmpOk x64Mach x64Gpr s' (k.eval va vb) 0#w.bits eqNe) E s := by
  have hwn : w.bits = 8 ∨ w.bits = 16 ∨ w.bits = 32 ∨ w.bits = 64 := by
    cases w <;> simp [Width.bits]
  refine Program.wp.mono
    (opBin_z (decide (w = .W32)) w k (fun h => of_decide_eq_true h) hc hrd hargs hpa hpb) ?_
  rintro s' ⟨hp, hflag⟩
  refine ⟨hp.1, fun hw => by subst hw; exact hp.2 rfl rfl, ?_⟩
  have hf := hflag hcl
  subst heq
  cases k with
  | mul => exact absurd rfl hk
  | add | sub => exact x64FlagCmpOk_of_zf hf
  | and | or | xor =>
    obtain ⟨af, hst⟩ := hf
    exact x64FlagCmpOk_of_testFlags hwn hst

end

end LeanQbe.T.Amd64
