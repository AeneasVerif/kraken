module

public import LeanQbe.T.Arm64.VllAsmArm64Lemmas0
import LeanQbe.T.Arm64.IselLemmas1
import LeanQbe.T.Arm64.FrameLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import Kraken.AArch64.WP.Control

/-!
# AArch64 `BedrockMach` L1 Assembler Simulation Proofs (`Arm64.VllAsmArm64Lemmas`)

Per-instruction and straight-line simulation proofs for `asmArm64` over Kraken AArch64:

* `asmArm64_fallsTo`: per-instruction fall-through simulation for every `Instr arm64Arch` opcode
  (including sub-word 8/16-bit ALU/cmp/test exact NZCV flags, total `AddrArg` load/store, stack
  slots/frames, `canonAbi`, `symAddr`, `pad`, `jcc`/`jnzGpr` not-taken, and `.native d`).
* `asmArm64List_fallsTo`: compositional straight-line simulation over `ExecBodyOk`.
* `asmArm64_jump`: control-flow transfer simulation for every jump opcode (`jmp`, `jcc`, `jnzGpr`,
  `call`, `icall`, `ret`, `exitJmp`, `tailJmpR`, `ijmp`, and `.native d`).

Strictly AArch64 only (zero `Amd64`/`Kraken.X64` imports, zero `@[expose]` on theorems/lemmas).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T
open LeanQbe.T.Vll

/-! ## 1. Private Per-Opcode Straight-Line WP Lemmas -/

private theorem asmMov_sub_wp [Host] (w : Width) (rd rs : Arm64.Reg)
    {sv : MachSt arm64Arch} {sm : MachineData} (hrs : rs ∉ armScratch) (hrel : arm64StateRel sv sm)
    (opI : XReg → XReg → _root_.Instr)
    (hop : ∀ (d x : XReg) (s : MachineData),
      _root_.Program.wp [.instr (opI d x)]
        (fun s' => s' = wr s d (((Arm64.get s (.reg x)).setWidth w.bits).setWidth 64))
        (fun _ _ => False) s) :
    let code : List _root_.Instr :=
      match rd, rs with
      | .reg d, .reg x => [opI d x]
      | .reg d, .SP => [armIselMovToXI d .SP, opI d d]
      | .SP, .reg x => [opI .X16 x, armIselMovToSpI .X16]
      | .SP, .SP => [armIselMovToXI .X16 .SP, opI .X16 .X16, armIselMovToSpI .X16]
    _root_.Program.wp (emitClean code)
      (fun sm' => arm64StateRel (sv.setGpr rd (((sv.gpr rs).setWidth w.bits).setWidth 64)) sm' ∧
        armMach.Frame armCondReads sm sm' (rd :: armScratch) [] maskNone)
      (fun _ _ => False) sm := by
  have hrs_eq : Arm64.get sm rs = sv.gpr rs := hrel.1 rs hrs
  cases rd <;> cases rs <;> simp only [emitClean_cons, emitClean_nil]
  · refine armWp_mono (hop _ _ sm) ?_
    rintro _ rfl
    exact stateRel_updGpr hrel _ _ (by simp [hrs_eq])
      (fun r hne _ => get_wr_of_ne _ _ _ r hne) rfl rfl
  · refine armWp_cons (armMovToX_wp _ .SP sm) ?_
    rintro _ rfl
    refine armWp_mono (hop _ _ _) ?_
    rintro _ rfl
    exact stateRel_updGpr hrel _ _ (by simp [hrs_eq])
      (fun r hne _ => by rw [get_wr_of_ne _ _ _ r hne, get_wr_of_ne _ _ _ r hne]) rfl rfl
  · refine armWp_cons (hop .X16 _ sm) ?_
    rintro _ rfl
    refine armWp_mono (armMovToSp_wp .X16 _) ?_
    rintro _ rfl
    refine stateRel_updGpr hrel .SP _ (by simp [get_sp, hrs_eq]) (fun r hne hsc => ?_) rfl rfl
    cases r with
    | SP => exact absurd rfl hne
    | reg xr =>
      have hx16 := (xreg_ne_scratch_of_not_mem hsc).1
      simp [get_reg, Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
  · refine armWp_cons (armMovToX_wp .X16 .SP sm) ?_
    rintro _ rfl
    refine armWp_cons (hop .X16 .X16 _) ?_
    rintro _ rfl
    refine armWp_mono (armMovToSp_wp .X16 _) ?_
    rintro _ rfl
    refine stateRel_updGpr hrel .SP _ (by simp [get_sp, hrs_eq]) (fun r hne hsc => ?_) rfl rfl
    cases r with
    | SP => exact absurd rfl hne
    | reg xr =>
      have hx16 := (xreg_ne_scratch_of_not_mem hsc).1
      simp [get_reg, Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]

private theorem asmMov_wp [Host] (w : Width) (rd rs : Arm64.Reg)
    {sv : MachSt arm64Arch} {sm : MachineData}
    (hrs : rs ∉ armScratch) (hrel : arm64StateRel sv sm) :
    _root_.Program.wp (emitClean (asmMovIns w rd rs))
      (fun sm' => arm64StateRel (sv.setGprW w rd ((sv.gpr rs).setWidth w.bits)) sm' ∧
        armMach.Frame armCondReads sm sm' (rd :: armScratch) [] maskNone)
      (fun _ _ => False) sm := by
  have hrs_eq : Arm64.get sm rs = sv.gpr rs := hrel.1 rs hrs
  change _root_.Program.wp _
    (fun sm' => arm64StateRel (sv.setGpr rd (((sv.gpr rs).setWidth w.bits).setWidth 64)) sm' ∧
      armMach.Frame armCondReads sm sm' (rd :: armScratch) [] maskNone) _ _
  cases w with
  | w64 =>
    have hdir : armDirFallsTo (ins (w := .W64) (.ADD_e (.low rd .W64) (.low rs .W64) imm0)) sm
        (fun s' => Arm64.get s' rd = sv.gpr rs ∧
          (∀ r, r ≠ rd → Arm64.get s' r = Arm64.get sm r) ∧
          s'.status = sm.status ∧ s'.dmem = sm.dmem) := by
      intro _ _ _ _ _ hk
      simp only [t_step_simp, imm0, Int64.toInt_zero]
      rw [show BitVec.ofInt RegWidth.W64.bits 0 = 0#64 from rfl, BitVec.add_zero]
      refine hk _ ⟨?_, fun r hr => ?_, rfl, rfl⟩
      · cases rd <;> cases rs <;>
          simp [← hrs_eq, get_reg, get_sp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
            Reg64s.getRegOrSp_reg64, Reg64s.getRegOrSp_sp64]
      · cases rd with
        | SP => cases r with | SP => exact absurd rfl hr | reg xr => rfl
        | reg xd =>
          cases r with
          | SP => simp [get_sp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
          | reg xr =>
            have hx : xd ≠ xr := fun e => hr (congrArg XRegOrSp.reg e.symm)
            simp [get_reg, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, hx]
    simp only [asmMovIns, armMovIns, emitClean_cons, emitClean_nil, Width.bits, BitVec.setWidth_eq]
    refine armWp_mono (armDirFallsTo_wp hdir) ?_
    rintro s' ⟨hrd, hk, hst, hm⟩
    exact stateRel_updGpr hrel rd (sv.gpr rs) hrd (fun r hne _ => hk r hne) hst hm
  | w32 =>
    have h := asmMov_sub_wp .w32 rd rs hrs hrel
      (fun d x => armIselInsI (.ORR_s (zr d .W32) (xzr .W32) (sh x))) fun d x s =>
      armDirFallsTo_wp fun {_} _ _ _ _ hk => by
        dsimp only [sh]
        simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
          RegWidth.bits, MemWidth.bits, BitVec.zero_or]
        exact hk _ rfl
    cases rd <;> cases rs <;> exact h
  | w8 =>
    have h := asmMov_sub_wp .w8 rd rs hrs hrel
      (fun d x => armIselInsI (.UBFM (zr d .W64) (zr x .W64) 0 7)) fun d x s =>
      armDirFallsTo_wp fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, BitVec.setWidth_eq]
        rw [evalUBFM_low (w := .W64) (n := 8) _ (by decide) (by decide)]; exact hk _ rfl
    cases rd <;> cases rs <;> exact h
  | w16 =>
    have h := asmMov_sub_wp .w16 rd rs hrs hrel
      (fun d x => armIselInsI (.UBFM (zr d .W64) (zr x .W64) 0 15)) fun d x s =>
      armDirFallsTo_wp fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, BitVec.setWidth_eq]
        rw [evalUBFM_low (w := .W64) (n := 16) _ (by decide) (by decide)]; exact hk _ rfl
    cases rd <;> cases rs <;> exact h

private theorem setWidth_64_32_sub {n : Nat} (hle : n ≤ 32) (x : BitVec n) :
    (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j
  by_cases hj : j < 64
  · by_cases h : j < n
    · simp [hj, h, show j < 32 by omega]
    · have h0 : x.getLsbD j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hj, h0]
  · simp [hj]

private theorem asmAluWideReg_wp [Host] (op : CoreAlu) (w : Width) (hw : w = .w32 ∨ w = .w64)
    (sf : Bool) (d ra rb : XReg) (s : MachineData) :
    let rw := widthToRegWidth w
    let a := (Arm64.get s (.reg ra)).setWidth w.bits
    let b := (Arm64.get s (.reg rb)).setWidth w.bits
    let res := op.eval w a b
    let st' := match op, sf with
      | .add, true => StatusFlags.adds res a b
      | .sub, true => StatusFlags.subs res a b
      | .and, true => StatusFlags.from_result res { c := false, v := false }
      | _, _ => s.status
    _root_.Program.wp [.instr (asmAluWideRegI op rw sf d ra rb)]
      (fun s' => s' = { wr s d (res.setWidth 64) with status := st' })
      (fun _ _ => False) s := by
  rcases hw with rfl | rfl <;> cases op <;> cases sf <;> (
    refine armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      dsimp only [asmAluWideRegI, widthToRegWidth, CoreAlu.eval]
      try simp only [↓reduceIte, Bool.false_eq_true]
      try dsimp only [sh]
      simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
        RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
      try rw [BitVec.add_zero]
      exact hk _ rfl)

private theorem asmAluSubNoFlags_wp [Host] (op : CoreAlu) (w : Width) (hw : w = .w8 ∨ w = .w16)
    (d ra rb : XReg) (hra17 : ra ≠ .X17) (hrb16 : rb ≠ .X16) (s : MachineData) :
    let a := (Arm64.get s (.reg ra)).setWidth w.bits
    let b := (Arm64.get s (.reg rb)).setWidth w.bits
    _root_.Program.wp (emitClean (asmAluSubNoFlagsIns op w.bits d ra rb))
      (fun s' => Arm64.get s' (.reg d) = (op.eval w a b).setWidth 64 ∧
        (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  have hn : w.bits = 8 ∨ w.bits = 16 := by rcases hw with rfl | rfl <;> simp [Width.bits]
  have hle32 : w.bits ≤ 32 := by rcases hw with rfl | rfl <;> decide
  have hle64 : w.bits ≤ 64 := by rcases hw with rfl | rfl <;> decide
  have hpos : 0 < w.bits := by rcases hw with rfl | rfl <;> decide
  have hmaskRes : ∀ (s1 : MachineData),
      _root_.Program.wp [ins (.UBFM (zr d .W64) (zr d .W64) 0 (w.bits - 1))]
        (fun s' => s' = wr s1 d (((Arm64.get s1 (.reg d)).setWidth w.bits).setWidth 64))
        (fun _ _ => False) s1 := fun s1 =>
    armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, BitVec.setWidth_eq]
      rw [evalUBFM_low (w := .W64) _ hpos hle64]; exact hk _ rfl
  have hmaskSh : ∀ (s1 : MachineData),
      _root_.Program.wp
        [ins (.AND_i (.low (.reg .X17) .W32) (zr rb .W32) (armShiftMaskConst w.bits))]
        (fun s' => s' = wr s1 .X17
          (((Arm64.get s1 (.reg rb)).setWidth 32 &&& BitVec.ofNat 32 (w.bits - 1)).setWidth 64))
        (fun _ _ => False) s1 := fun s1 =>
    armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, armShiftMaskConst, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
        RegWidth.bits, BitVec.zeroExtend]
      rw [show BitVec.ofInt 32 (Int64.ofNat (w.bits - 1)).toInt = BitVec.ofNat 32 (w.bits - 1) by
        rcases hw with rfl | rfl <;> decide]
      exact hk _ rfl
  have hmaskEq : (Arm64.get s (.reg rb)).setWidth 32 &&& BitVec.ofNat 32 (w.bits - 1) =
      ((Arm64.get s (.reg rb)).setWidth w.bits).setWidth 32 &&& BitVec.ofNat 32 (w.bits - 1) := by
    rcases hw with rfl | rfl
    · apply BitVec.eq_of_getLsbD_eq; intro i
      by_cases hi : i < 32
      · by_cases h8 : i < 8
        · simp [Width.bits, hi, h8]
        · have htb : Nat.testBit 7 i = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 7 < 2 ^ 8)
              (Nat.pow_le_pow_right (by decide) (by omega)))
          have h7 : (BitVec.ofNat 32 7).getLsbD i = false := by
            rw [BitVec.getLsbD_ofNat, htb, Bool.and_false]
          simp [Width.bits, BitVec.getLsbD_and, h7]
      · simp [hi]
    · apply BitVec.eq_of_getLsbD_eq; intro i
      by_cases hi : i < 32
      · by_cases h16 : i < 16
        · simp [Width.bits, hi, h16]
        · have htb : Nat.testBit 15 i = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 15 < 2 ^ 16)
              (Nat.pow_le_pow_right (by decide) (by omega)))
          have h15 : (BitVec.ofNat 32 15).getLsbD i = false := by
            rw [BitVec.getLsbD_ofNat, htb, Bool.and_false]
          simp [Width.bits, BitVec.getLsbD_and, h15]
      · simp [hi]
  have hbin : ∀ (e : BitVec 32 → BitVec 32 → BitVec 32) (ins1 : _root_.Instr),
      _root_.Program.wp [.instr ins1]
        (fun s' => s' = wr s d ((e ((Arm64.get s (.reg ra)).setWidth 32)
          ((Arm64.get s (.reg rb)).setWidth 32)).setWidth 64)) (fun _ _ => False) s →
      (e ((Arm64.get s (.reg ra)).setWidth 32)
        ((Arm64.get s (.reg rb)).setWidth 32)).setWidth w.bits =
        op.eval w ((Arm64.get s (.reg ra)).setWidth w.bits)
          ((Arm64.get s (.reg rb)).setWidth w.bits) →
      _root_.Program.wp (emitClean [ins1, armIselInsI (.UBFM (zr d .W64) (zr d .W64) 0
          (w.bits - 1))])
        (fun s' => Arm64.get s' (.reg d) =
            (op.eval w ((Arm64.get s (.reg ra)).setWidth w.bits)
              ((Arm64.get s (.reg rb)).setWidth w.bits)).setWidth 64 ∧
          (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
          s'.status = s.status ∧ s'.dmem = s.dmem) (fun _ _ => False) s := by
    intro e ins1 hwp1 heq
    simp only [emitClean_cons, emitClean_nil]
    refine armWp_cons hwp1 ?_
    rintro _ rfl
    refine armWp_mono (hmaskRes _) ?_
    rintro _ rfl
    refine ⟨?_, fun r hne _ => by rw [get_wr_of_ne _ _ _ r hne, get_wr_of_ne _ _ _ r hne], rfl, rfl⟩
    rw [get_wr_same, get_wr_same, BitVec.setWidth_setWidth_of_le _ hle64, heq]
  cases op with
  | add =>
    exact hbin (· + ·) _ (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      dsimp only [sh]; simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
        BitVec.shiftLeft_zero, RegWidth.bits]; exact hk _ rfl) (by
      rw [setWidth_add_of_le hle32, BitVec.setWidth_setWidth_of_le _ hle32,
        BitVec.setWidth_setWidth_of_le _ hle32]; rfl)
  | sub =>
    exact hbin (· - ·) _ (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      dsimp only [sh]; simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
        BitVec.shiftLeft_zero, RegWidth.bits]; exact hk _ rfl) (by
      rw [setWidth_sub_of_le hle32, BitVec.setWidth_setWidth_of_le _ hle32,
        BitVec.setWidth_setWidth_of_le _ hle32]; rfl)
  | and =>
    exact hbin (· &&& ·) _ (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      dsimp only [sh]; simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
        BitVec.shiftLeft_zero, RegWidth.bits]; exact hk _ rfl) (by
      rw [setWidth_and_of_le, BitVec.setWidth_setWidth_of_le _ hle32,
        BitVec.setWidth_setWidth_of_le _ hle32]; rfl)
  | or =>
    exact hbin (· ||| ·) _ (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      dsimp only [sh]; simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
        BitVec.shiftLeft_zero, RegWidth.bits]; exact hk _ rfl) (by
      rw [setWidth_or_of_le, BitVec.setWidth_setWidth_of_le _ hle32,
        BitVec.setWidth_setWidth_of_le _ hle32]; rfl)
  | xor =>
    exact hbin (· ^^^ ·) _ (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      dsimp only [sh]; simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero,
        BitVec.shiftLeft_zero, RegWidth.bits]; exact hk _ rfl) (by
      rw [setWidth_xor_of_le, BitVec.setWidth_setWidth_of_le _ hle32,
        BitVec.setWidth_setWidth_of_le _ hle32]; rfl)
  | mul =>
    exact hbin (· * ·) _ (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, RegWidth.bits, BitVec.add_zero]; exact hk _ rfl) (by
      rw [setWidth_mul_of_le hle32, BitVec.setWidth_setWidth_of_le _ hle32,
        BitVec.setWidth_setWidth_of_le _ hle32]; rfl)
  | shl =>
    simp only [asmAluSubNoFlagsIns, emitClean_cons, emitClean_nil]
    refine armWp_cons (hmaskSh s) ?_
    rintro _ rfl
    refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, RegWidth.bits, MemWidth.bits]; exact hk _ rfl) ?_
    rintro _ rfl
    refine armWp_mono (hmaskRes _) ?_
    rintro _ rfl
    refine ⟨?_, fun r hne hsc => ?_, rfl, rfl⟩
    · simp only [get_reg, Reg64s.getXReg_setXReg_same,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hra17.symm, UInt64.toBitVec_ofBitVec,
        BitVec.setWidth_setWidth_of_le _ hle64,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      rw [← get_reg, ← get_reg, hmaskEq, shl_subword_mask hn,
        BitVec.setWidth_setWidth_of_le _ hle32]; rfl
    · change Arm64.get (wr (wr (wr s .X17 _) d _) d _) r = Arm64.get s r
      rw [get_wr_of_ne _ _ _ r hne, get_wr_of_ne _ _ _ r hne,
        get_wr_of_ne _ _ _ r (ne_of_not_mem_armScratch hsc).2]
  | lshr =>
    simp only [asmAluSubNoFlagsIns, emitClean_cons, emitClean_nil]
    refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      dsimp only [armExt32I]; simp only [↓reduceIte, Bool.false_eq_true]
      simp only [t_step_simp]
      rw [evalUBFM_low (w := .W32) _ hpos hle32, ubfm_low_w32_eq hn]; exact hk _ rfl) ?_
    rintro _ rfl
    refine armWp_cons (hmaskSh _) ?_
    rintro _ rfl
    refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, RegWidth.bits, MemWidth.bits]; exact hk _ rfl) ?_
    rintro _ rfl
    refine ⟨?_, fun r hne hsc => ?_, rfl, rfl⟩
    · simp only [get_reg, Reg64s.getXReg_setXReg_same,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X17 ≠ XReg.X16),
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrb16.symm, UInt64.toBitVec_ofBitVec,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      rw [← get_reg, ← get_reg, hmaskEq]
      have hlow := lshr_subword_mask hn ((Arm64.get s (.reg ra)).setWidth w.bits)
        ((Arm64.get s (.reg rb)).setWidth w.bits)
      have hup : (((Arm64.get s (.reg ra)).setWidth w.bits).setWidth 32).ushiftRight
          ((((Arm64.get s (.reg rb)).setWidth w.bits).setWidth 32 &&&
            BitVec.ofNat 32 (w.bits - 1)).toNat % 32) =
          (((Arm64.get s (.reg ra)).setWidth w.bits) >>>
            (((Arm64.get s (.reg rb)).setWidth w.bits).toNat % w.bits)).setWidth 32 := by
        rw [← hlow]; rcases hw with rfl | rfl <;> ext i hi <;> grind
      rw [hup, setWidth_64_32_sub hle32]
      rcases hw with rfl | rfl <;> simp [CoreAlu.eval]
    · have hns := ne_of_not_mem_armScratch hsc
      change Arm64.get (wr (wr (wr s .X16 _) .X17 _) d _) r = Arm64.get s r
      rw [get_wr_of_ne _ _ _ r hne, get_wr_of_ne _ _ _ r hns.2, get_wr_of_ne _ _ _ r hns.1]
  | ashr =>
    simp only [asmAluSubNoFlagsIns, emitClean_cons, emitClean_nil]
    refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      dsimp only [armExt32I]; simp only [↓reduceIte]
      simp only [t_step_simp]
      rw [evalSBFM_low (w := .W32) _ hpos hle32, sbfm_low_w32_eq hn]; exact hk _ rfl) ?_
    rintro _ rfl
    refine armWp_cons (hmaskSh _) ?_
    rintro _ rfl
    refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, RegWidth.bits, MemWidth.bits]; exact hk _ rfl) ?_
    rintro _ rfl
    refine armWp_mono (hmaskRes _) ?_
    rintro _ rfl
    refine ⟨?_, fun r hne hsc => ?_, rfl, rfl⟩
    · simp only [get_reg, Reg64s.getXReg_setXReg_same,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X17 ≠ XReg.X16),
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrb16.symm, UInt64.toBitVec_ofBitVec,
        BitVec.setWidth_setWidth_of_le _ hle64,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      rw [← get_reg, ← get_reg, hmaskEq, ashr_subword_mask hn]; rfl
    · have hns := ne_of_not_mem_armScratch hsc
      change Arm64.get (wr (wr (wr (wr s .X16 _) .X17 _) d _) d _) r = Arm64.get s r
      rw [get_wr_of_ne _ _ _ r hne, get_wr_of_ne _ _ _ r hne,
        get_wr_of_ne _ _ _ r hns.2, get_wr_of_ne _ _ _ r hns.1]

private theorem asmAluCore_sub_addSub_wp [Host] (isSub : Bool) (w : Width) (hw : w = .w8 ∨ w = .w16)
    (d ra rb : XReg) (hrb16 : rb ≠ .X16) (s : MachineData) :
    let n := w.bits
    let a := (Arm64.get s (.reg ra)).setWidth n
    let b := (Arm64.get s (.reg rb)).setWidth n
    let res := if isSub then a - b else a + b
    let flg := if isSub then StatusFlags.subs (a - b) a b else StatusFlags.adds (a + b) a b
    _root_.Program.wp (emitClean
      [armIselInsI (.UBFM (zr .X16 .W32) (zr ra .W32) n (n - 1)),
       armIselInsI (.UBFM (zr .X17 .W32) (zr rb .W32) n (n - 1)),
       armIselInsI (if isSub then .SUBS_s (zr d .W32) (zr .X16 .W32) (sh .X17)
                    else .ADDS_s (zr d .W32) (zr .X16 .W32) (sh .X17)),
       armIselInsI (.UBFM (zr d .W32) (zr d .W32) (32 - n) 31)])
      (fun s' => Arm64.get s' (.reg d) = res.setWidth 64 ∧
        (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
        s'.status = flg ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  have hn : w.bits = 8 ∨ w.bits = 16 := by rcases hw with rfl | rfl <;> simp [Width.bits]
  have hle32 : w.bits ≤ 32 := by rcases hw with rfl | rfl <;> decide
  simp only [emitClean_cons, emitClean_nil]
  refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
    simp only [t_step_simp, ← get_reg]
    rw [evalUBFM_shl_subword hn, BitVec.setWidth_setWidth_of_le _ hle32]
    exact hk _ rfl) ?_
  rintro _ rfl
  refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
    simp only [t_step_simp, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrb16.symm, ← get_reg]
    rw [evalUBFM_shl_subword hn, BitVec.setWidth_setWidth_of_le _ hle32]
    exact hk _ rfl) ?_
  rintro _ rfl
  cases isSub <;> (
    refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [↓reduceIte, Bool.false_eq_true]
      dsimp only [sh]
      simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
        RegWidth.bits, MemWidth.bits, Reg64s.getXReg_setXReg_same,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X17 ≠ XReg.X16),
        UInt64.toBitVec_ofBitVec, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
        BitVec.setWidth_eq]
      first | (rw [adds_shl_subword hn, shl_subword_add hn]) |
              (rw [subs_shl_subword hn, shl_subword_sub hn])
      exact hk _ rfl) ?_
    rintro _ rfl
    refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      rw [evalUBFM_shr_subword hn, setWidth_64_32_sub hle32]
      exact hk _ rfl) ?_
    rintro _ rfl
    refine ⟨by simp [get_reg], fun r hne hsc => ?_, rfl, rfl⟩
    have hns := ne_of_not_mem_armScratch hsc
    change Arm64.get (wr (wr (wr (wr s .X16 _) .X17 _) d _) d _) r = Arm64.get s r
    rw [get_wr_of_ne _ _ _ r hne, get_wr_of_ne _ _ _ r hne,
      get_wr_of_ne _ _ _ r hns.2, get_wr_of_ne _ _ _ r hns.1])

private theorem asmAluCore_wp [Host] (op : CoreAlu) (w : Width) (sf : Bool)
    (d ra rb : XReg) (hra17 : ra ≠ .X17) (hrb16 : rb ≠ .X16) (s : MachineData) :
    let a := (Arm64.get s (.reg ra)).setWidth w.bits
    let b := (Arm64.get s (.reg rb)).setWidth w.bits
    _root_.Program.wp (emitClean (asmAluCoreIns op w sf d ra rb))
      (fun s' => (d ≠ .X17 → Arm64.get s' (.reg d) = (op.eval w a b).setWidth 64) ∧
        (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
        s'.status = arm64AluFlags op w sf a b s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  have hwide : ∀ (w' : Width) (hw : w' = .w32 ∨ w' = .w64),
      _root_.Program.wp (emitClean (asmAluCoreIns op w' sf d ra rb))
        (fun s' => (d ≠ .X17 → Arm64.get s' (.reg d) =
            (op.eval w' ((Arm64.get s (.reg ra)).setWidth w'.bits)
              ((Arm64.get s (.reg rb)).setWidth w'.bits)).setWidth 64) ∧
          (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
          s'.status = arm64AluFlags op w' sf ((Arm64.get s (.reg ra)).setWidth w'.bits)
            ((Arm64.get s (.reg rb)).setWidth w'.bits) s.status ∧ s'.dmem = s.dmem)
        (fun _ _ => False) s := by
    intro w' hw
    rcases hw with rfl | rfl <;> (
      cases sf with
      | false =>
        simp only [asmAluCoreIns, Bool.not_false, ↓reduceIte, emitClean_cons, emitClean_nil]
        refine armWp_mono (asmAluWideReg_wp op _ (by first | exact Or.inl rfl | exact Or.inr rfl)
          false d ra rb s) ?_
        rintro _ rfl
        exact ⟨fun _ => by simp [get_reg], fun r hne _ => get_wr_of_ne s d _ r hne,
          by cases op <;> rfl, rfl⟩
      | true =>
        cases op with
        | add | sub | and =>
          simp only [asmAluCoreIns, Bool.not_true, Bool.false_eq_true, ↓reduceIte, emitClean_cons,
            emitClean_nil]
          refine armWp_mono (asmAluWideReg_wp _ _ (by first | exact Or.inl rfl | exact Or.inr rfl)
            true d ra rb s) ?_
          rintro _ rfl
          exact ⟨fun _ => by simp [get_reg], fun r hne _ => get_wr_of_ne s d _ r hne, rfl, rfl⟩
        | or | xor | shl | lshr | ashr | mul =>
          simp only [asmAluCoreIns, Bool.not_true, Bool.false_eq_true, ↓reduceIte, emitClean_cons,
            emitClean_nil]
          refine armWp_cons (asmAluWideReg_wp _ _ (by first | exact Or.inl rfl | exact Or.inr rfl)
            true d ra rb s) ?_
          rintro _ rfl
          refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
            dsimp only [sh, widthToRegWidth]
            simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
              RegWidth.bits, MemWidth.bits, Reg64s.setRegOrZr_xzr, BitVec.and_self,
              Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec]
            first
            | rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
            | rw [BitVec.setWidth_eq]
            exact hk _ rfl) ?_
          rintro _ rfl
          exact ⟨fun _ => by simp [get_reg], fun r hne _ => get_wr_of_ne s d _ r hne, rfl, rfl⟩)
  have hsub : ∀ (w' : Width) (hw : w' = .w8 ∨ w' = .w16),
      _root_.Program.wp (emitClean (asmAluCoreIns op w' sf d ra rb))
        (fun s' => (d ≠ .X17 → Arm64.get s' (.reg d) =
            (op.eval w' ((Arm64.get s (.reg ra)).setWidth w'.bits)
              ((Arm64.get s (.reg rb)).setWidth w'.bits)).setWidth 64) ∧
          (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
          s'.status = arm64AluFlags op w' sf ((Arm64.get s (.reg ra)).setWidth w'.bits)
            ((Arm64.get s (.reg rb)).setWidth w'.bits) s.status ∧ s'.dmem = s.dmem)
        (fun _ _ => False) s := by
    intro w' hw
    have hn : w'.bits = 8 ∨ w'.bits = 16 := by rcases hw with rfl | rfl <;> simp [Width.bits]
    have hle32 : w'.bits ≤ 32 := by rcases hw with rfl | rfl <;> decide
    have hle64 : w'.bits ≤ 64 := by rcases hw with rfl | rfl <;> decide
    have hadd := asmAluCore_sub_addSub_wp false w' hw d ra rb hrb16 s
    have hsub' := asmAluCore_sub_addSub_wp true w' hw d ra rb hrb16 s
    have hnof := asmAluSubNoFlags_wp op w' hw d ra rb hra17 hrb16 s
    rcases hw with rfl | rfl <;> (
      cases sf with
      | false =>
        simp only [asmAluCoreIns, Bool.not_false, ↓reduceIte]
        refine armWp_mono hnof ?_
        rintro s' ⟨h1, h2, h3, h4⟩; exact ⟨fun _ => h1, h2, h3, h4⟩
      | true =>
        cases op with
        | add =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hadd
          simp only [asmAluCoreIns, Bool.not_true, Bool.false_eq_true, ↓reduceIte, CoreAlu.eval,
            arm64AluFlags]
          refine armWp_mono hadd ?_; rintro s' ⟨h1, h2, h3, h4⟩; exact ⟨fun _ => h1, h2, h3, h4⟩
        | sub =>
          simp only [↓reduceIte] at hsub'
          simp only [asmAluCoreIns, Bool.not_true, Bool.false_eq_true, ↓reduceIte, CoreAlu.eval,
            arm64AluFlags]
          refine armWp_mono hsub' ?_; rintro s' ⟨h1, h2, h3, h4⟩; exact ⟨fun _ => h1, h2, h3, h4⟩
        | and | or | xor | shl | lshr | ashr | mul =>
          simp only [asmAluCoreIns, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            emitClean_append, emitClean_cons, emitClean_nil]
          refine armWp_append hnof ?_
          rintro s₁ ⟨hd1, hk1, hst1, hm1⟩
          refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
            simp only [t_step_simp, ← get_reg, hd1]
            rw [evalUBFM_shl_subword hn, BitVec.setWidth_setWidth_of_le _ hle32,
              BitVec.setWidth_setWidth_of_le _ hle64, BitVec.setWidth_eq]
            exact hk _ rfl) ?_
          rintro _ rfl
          refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
            dsimp only [sh]
            simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
              RegWidth.bits, MemWidth.bits, Reg64s.setRegOrZr_xzr, BitVec.and_self,
              Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
              BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
            rw [from_result_shl_subword hn]
            exact hk _ rfl) ?_
          rintro _ rfl
          refine ⟨fun hd17 => ?_, fun r hne hsc => ?_, rfl, hm1⟩
          · change Arm64.get (wr s₁ .X17 _) (.reg d) = _
            rw [get_wr_of_ne _ _ _ _ (fun e => hd17 (XRegOrSp.reg.inj e)), hd1]
          · change Arm64.get (wr s₁ .X17 _) r = _
            rw [get_wr_of_ne _ _ _ r (ne_of_not_mem_armScratch hsc).2]
            exact hk1 r hne hsc)
  cases w with
  | w8 => exact hsub .w8 (Or.inl rfl)
  | w16 => exact hsub .w16 (Or.inr rfl)
  | w32 => exact hwide .w32 (Or.inl rfl)
  | w64 => exact hwide .w64 (Or.inr rfl)

private theorem asmAluImmFast_wp [Host] (op : CoreAlu) (w : Width) (sf : Bool) (d ra : XReg)
    (v : BitVec 64) {ci : List _root_.Instr} (hfast : asmAluImmFastIns? op w sf d ra v = some ci)
    (s : MachineData) :
    let a := (Arm64.get s (.reg ra)).setWidth w.bits
    let b := v.setWidth w.bits
    _root_.Program.wp (emitClean ci)
      (fun s' => Arm64.get s' (.reg d) = (op.eval w a b).setWidth 64 ∧
        (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
        s'.status = arm64AluFlags op w sf a b s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  have hwide : ∀ (w' : Width) (hw : w' = .w32 ∨ w' = .w64)
      (hfast' : asmAluImmFastIns? op w' sf d ra v = some ci),
      _root_.Program.wp (emitClean ci)
        (fun s' => Arm64.get s' (.reg d) =
            (op.eval w' ((Arm64.get s (.reg ra)).setWidth w'.bits) (v.setWidth w'.bits)).setWidth 64
          ∧ (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
          s'.status = arm64AluFlags op w' sf ((Arm64.get s (.reg ra)).setWidth w'.bits)
            (v.setWidth w'.bits) s.status ∧ s'.dmem = s.dmem)
        (fun _ _ => False) s := by
    intro w' hw hfast'
    cases op with
    | mul => rcases hw with rfl | rfl <;> simp [asmAluImmFastIns?] at hfast'
    | add | sub =>
      cases hi : armImm12? (v.setWidth w'.bits) with
      | none =>
        rcases hw with rfl | rfl <;> (
          dsimp only [asmAluImmFastIns?] at hfast'
          rw [hi] at hfast'
          simp at hfast')
      | some ei =>
        have himmAll : ∀ [Labels] pos regs,
            ei.interp (w := widthToRegWidth w') regs pos =
              (v.setWidth w'.bits).setWidth (widthToRegWidth w').bits :=
          fun {_} pos regs => by
            simpa [BitVec.setWidth_eq] using armImm12_some
              (by rcases hw with rfl | rfl <;> decide) hi (widthToRegWidth w') pos regs
        have htake : ∀ {m n : Nat} (x : BitVec m), x.take n = x.setWidth n := fun x => by
          apply BitVec.eq_of_getLsbD_eq; intro j; simp [BitVec.take]
        rcases hw with rfl | rfl <;> (
          simp only [asmAluImmFastIns?, hi, Option.map_some, Option.some.injEq] at hfast'
          subst hfast'
          cases sf <;> (
            simp only [↓reduceIte, Bool.false_eq_true, emitClean_cons, emitClean_nil]
            refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
              have himm := himmAll pos s.regs
              dsimp only [widthToRegWidth, Width.bits, RegWidth.bits, MemWidth.bits] at himm ⊢
              simp only [Directive.interp, Instr.interp, Operation.interp, himm,
                MachineData.setRegOrSp, MachineData.setRegOrZr, Reg64s.setRegOrSp,
                Reg64s.setRegOrSp64, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, setRegOrZr_zr,
                RegOrSp.base, htake, BitVec.zeroExtend, BitVec.setWidth_eq,
                RegWidth.bits, MemWidth.bits, Effects.All]
              exact hk _ rfl) ?_
            rintro _ rfl
            exact ⟨by simp [get_reg, CoreAlu.eval],
              fun r hne _ => get_wr_of_ne s d _ r hne, rfl, rfl⟩))
    | and =>
      have hi32 := int64_ofInt_setWidth (w := .W32) (v.setWidth 32)
      have hi64 := int64_ofInt_setWidth (w := .W64) (v.setWidth 64)
      simp only [RegWidth.bits] at hi32 hi64
      rcases hw with rfl | rfl <;> (
        dsimp only [asmAluImmFastIns?] at hfast'
        split at hfast'
        · cases sf <;> (
            simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq] at hfast'
            subst hfast'
            simp only [emitClean_cons, emitClean_nil]
            refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
              simp only [t_step_simp, widthToRegWidth, Width.bits, RegWidth.bits, MemWidth.bits,
                Reg64s.setRegOrSp, Reg64s.setRegOrSp64, BitVec.zeroExtend, hi32, hi64]
              exact hk _ rfl) ?_
            rintro _ rfl
            exact ⟨by simp [get_reg, CoreAlu.eval],
              fun r hne _ => get_wr_of_ne s d _ r hne, rfl, rfl⟩)
        · simp at hfast')
    | or | xor =>
      have hi32 := int64_ofInt_setWidth (w := .W32) (v.setWidth 32)
      have hi64 := int64_ofInt_setWidth (w := .W64) (v.setWidth 64)
      simp only [RegWidth.bits] at hi32 hi64
      rcases hw with rfl | rfl <;> (
        dsimp only [asmAluImmFastIns?] at hfast'
        split at hfast'
        · rename_i hcond
          have hsf : sf = false := by simp at hcond; exact hcond.1
          subst hsf
          simp only [Option.some.injEq] at hfast'; subst hfast'
          simp only [emitClean_cons, emitClean_nil]
          refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
            simp only [t_step_simp, widthToRegWidth, Width.bits, RegWidth.bits, MemWidth.bits,
              Reg64s.setRegOrSp, Reg64s.setRegOrSp64, BitVec.zeroExtend, hi32, hi64]
            exact hk _ rfl) ?_
          rintro _ rfl
          exact ⟨by simp [get_reg, CoreAlu.eval],
            fun r hne _ => get_wr_of_ne s d _ r hne, rfl, rfl⟩
        · simp at hfast')
    | shl =>
      rcases hw with rfl | rfl <;> (
        dsimp only [asmAluImmFastIns?] at hfast'
        split at hfast'
        · rename_i hsf
          have hsf0 : sf = false := by simpa using hsf
          subst hsf0
          simp only [Option.some.injEq] at hfast'; subst hfast'
          simp only [emitClean_cons, emitClean_nil]
          refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
            simp only [t_step_simp, widthToRegWidth, Width.bits, RegWidth.bits, MemWidth.bits]
            first
            | rw [evalUBFM_lsl (w := .W32) _ (Nat.mod_lt _ (by decide))]
            | rw [evalUBFM_lsl (w := .W64) _ (Nat.mod_lt _ (by decide))]
            exact hk _ rfl) ?_
          rintro _ rfl
          exact ⟨by
              simp only [get_reg, CoreAlu.eval, Width.bits, Reg64s.getXReg_setXReg_same,
                UInt64.toBitVec_ofBitVec, BitVec.toNat_setWidth]
              try rw [Nat.mod_mod_of_dvd v.toNat (by decide : 32 ∣ 2 ^ 32)]
              try rw [Nat.mod_mod_of_dvd v.toNat (by decide : 64 ∣ 2 ^ 64)],
            fun r hne _ => get_wr_of_ne s d _ r hne, rfl, rfl⟩
        · simp at hfast')
    | lshr =>
      rcases hw with rfl | rfl <;> (
        dsimp only [asmAluImmFastIns?] at hfast'
        split at hfast'
        · rename_i hsf
          have hsf0 : sf = false := by simpa using hsf
          subst hsf0
          simp only [Option.some.injEq] at hfast'; subst hfast'
          simp only [emitClean_cons, emitClean_nil]
          refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
            simp only [t_step_simp, widthToRegWidth, Width.bits, RegWidth.bits, MemWidth.bits]
            first
            | rw [evalUBFM_lsr (w := .W32) _ (Nat.mod_lt _ (by decide))]
            | rw [evalUBFM_lsr (w := .W64) _ (Nat.mod_lt _ (by decide))]
            exact hk _ rfl) ?_
          rintro _ rfl
          exact ⟨by
              simp only [get_reg, CoreAlu.eval, Width.bits, Reg64s.getXReg_setXReg_same,
                UInt64.toBitVec_ofBitVec, BitVec.toNat_setWidth]
              try rw [Nat.mod_mod_of_dvd v.toNat (by decide : 32 ∣ 2 ^ 32)]
              try rw [Nat.mod_mod_of_dvd v.toNat (by decide : 64 ∣ 2 ^ 64)],
            fun r hne _ => get_wr_of_ne s d _ r hne, rfl, rfl⟩
        · simp at hfast')
    | ashr =>
      rcases hw with rfl | rfl <;> (
        dsimp only [asmAluImmFastIns?] at hfast'
        split at hfast'
        · rename_i hsf
          have hsf0 : sf = false := by simpa using hsf
          subst hsf0
          simp only [Option.some.injEq] at hfast'; subst hfast'
          simp only [emitClean_cons, emitClean_nil]
          refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
            simp only [t_step_simp, widthToRegWidth, Width.bits, RegWidth.bits, MemWidth.bits]
            first
            | rw [evalSBFM_asr (w := .W32) _ (Nat.mod_lt _ (by decide))]
            | rw [evalSBFM_asr (w := .W64) _ (Nat.mod_lt _ (by decide))]
            exact hk _ rfl) ?_
          rintro _ rfl
          exact ⟨by
              simp only [get_reg, CoreAlu.eval, Width.bits, Reg64s.getXReg_setXReg_same,
                UInt64.toBitVec_ofBitVec, BitVec.toNat_setWidth]
              try rw [Nat.mod_mod_of_dvd v.toNat (by decide : 32 ∣ 2 ^ 32)]
              try rw [Nat.mod_mod_of_dvd v.toNat (by decide : 64 ∣ 2 ^ 64)],
            fun r hne _ => get_wr_of_ne s d _ r hne, rfl, rfl⟩
        · simp at hfast')
  cases w with
  | w8 | w16 => simp [asmAluImmFastIns?] at hfast
  | w32 => exact hwide .w32 (Or.inl rfl) hfast
  | w64 => exact hwide .w64 (Or.inr rfl) hfast

private theorem asmAlu_wp [Host] (op : CoreAlu) (w : Width) (rd lhs : Arm64.Reg)
    (rhs : Src arm64Arch) (sf : Bool) {sv : MachSt arm64Arch} {sm : MachineData}
    (hlhs : lhs ∉ armScratch) (hrhs : ∀ r ∈ rhs.regs, r ∉ armScratch)
    (hrel : arm64StateRel sv sm) :
    let a := (sv.gpr lhs).setWidth w.bits
    let b := rhs.evalW w sv.gpr
    _root_.Program.wp (emitClean (asmAluIns op w rd lhs rhs sf))
      (fun sm' => arm64StateRel ((sv.setGprW w rd (op.eval w a b)).setFlags
          (arm64AluFlags op w sf a b sv.flags)) sm' ∧
        armMach.Frame armCondReads sm sm' (rd :: armScratch) [] (arm64AluClob op sf))
      (fun _ _ => False) sm := by
  have haEq : (Arm64.get sm lhs).setWidth w.bits = (sv.gpr lhs).setWidth w.bits := by
    rw [hrel.1 lhs hlhs]
  have hbEq : rhs.evalW w (Arm64.get sm) = rhs.evalW w sv.gpr := by
    cases rhs with
    | imm _ => rfl
    | reg r => simp [Src.evalW, Src.eval, hrel.1 r (hrhs r List.mem_cons_self)]
  have hfOk : arm64AluFlags op w sf ((sv.gpr lhs).setWidth w.bits) (rhs.evalW w sv.gpr) sv.flags =
      sm.status ∨ arm64AluClob op sf = maskNZCV ∨ arm64AluClob op sf = maskAll := by
    cases sf
    · exact Or.inl (by simp [arm64AluFlags, hrel.2.1])
    · exact Or.inr (Or.inl rfl)
  have hfallback :
      _root_.Program.wp (emitClean (
        let (ca, ra) := armSrcToXIns .X16 lhs
        let (cb, rb) := armRhsToXIns .X17 w rhs
        match rd with
        | .reg d => ca ++ cb ++ asmAluCoreIns op w sf d ra rb
        | .SP => ca ++ cb ++ asmAluCoreIns op w sf .X16 ra rb ++ [armIselMovToSpI .X16]))
        (fun sm' => arm64StateRel ((sv.setGprW w rd
            (op.eval w ((sv.gpr lhs).setWidth w.bits) (rhs.evalW w sv.gpr))).setFlags
            (arm64AluFlags op w sf ((sv.gpr lhs).setWidth w.bits) (rhs.evalW w sv.gpr) sv.flags))
            sm' ∧
          armMach.Frame armCondReads sm sm' (rd :: armScratch) [] (arm64AluClob op sf))
        (fun _ _ => False) sm := by
    have h1 := armSrcToX_wp .X16 lhs hlhs sm
    have hra17 : (armSrcToXIns .X16 lhs).2 ≠ .X17 := h1.1 .X17 (by decide) (Or.inr rfl)
    have hrunCore : ∀ (d : XReg),
        _root_.Program.wp (emitClean ((armSrcToXIns .X16 lhs).1 ++
            (armRhsToXIns .X17 w rhs).1 ++
            asmAluCoreIns op w sf d (armSrcToXIns .X16 lhs).2 (armRhsToXIns .X17 w rhs).2))
          (fun sm' => (d ≠ .X17 → Arm64.get sm' (.reg d) =
              (op.eval w ((sv.gpr lhs).setWidth w.bits) (rhs.evalW w sv.gpr)).setWidth 64) ∧
            (∀ r, r ≠ .reg d → r ∉ armScratch → Arm64.get sm' r = Arm64.get sm r) ∧
            sm'.status = arm64AluFlags op w sf ((sv.gpr lhs).setWidth w.bits)
              (rhs.evalW w sv.gpr) sv.flags ∧ sm'.dmem = sm.dmem)
          (fun _ _ => False) sm := by
      intro d
      simp only [emitClean_append, List.append_assoc]
      refine armWp_append h1.2 ?_
      rintro s₁ ⟨hla1, hk1, hst1, hm1⟩
      have h2 := armRhsToX_wp w rhs hrhs s₁
      refine armWp_append h2.2 ?_
      rintro s₂ ⟨hrb2, hk2, hst2, hm2⟩
      have ha2 : (Arm64.get s₂ (.reg (armSrcToXIns .X16 lhs).2)).setWidth w.bits =
          (sv.gpr lhs).setWidth w.bits := by
        rw [hk2 _ (fun e => hra17 (XRegOrSp.reg.inj e)), hla1, haEq]
      have hb2 : (Arm64.get s₂ (.reg (armRhsToXIns .X17 w rhs).2)).setWidth w.bits =
          rhs.evalW w sv.gpr := by
        rw [hrb2, ← hbEq]
        cases rhs with
        | imm _ => rfl
        | reg r =>
          have hr16 := (ne_of_not_mem_armScratch (hrhs r List.mem_cons_self)).1
          simp [Src.evalW, Src.eval, hk1 r hr16]
      refine armWp_mono (asmAluCore_wp op w sf d _ _ hra17 h2.1 s₂) ?_
      rintro s₃ ⟨hd3, hk3, hst3, hm3⟩
      rw [ha2, hb2] at hd3 hst3; rw [hst2, hst1, hrel.2.1] at hst3
      refine ⟨hd3, fun r hne hsc => ?_, hst3, hm3.trans (hm2.trans hm1)⟩
      have hns := ne_of_not_mem_armScratch hsc
      rw [hk3 r hne hsc, hk2 r hns.2, hk1 r hns.1]
    cases rd with
    | reg d =>
      refine armWp_mono (hrunCore d) ?_
      rintro sm' ⟨hd, hk, hst, hm⟩
      by_cases hd17 : d = .X17
      · subst hd17
        have hkeep : ∀ r, r ∉ (.reg .X17 :: armScratch) → Arm64.get sm' r = Arm64.get sm r :=
          fun r hr => hk r (fun e => hr (by simp [e, armScratch]))
            (fun h => hr (List.mem_cons_of_mem _ h))
        refine ⟨⟨fun r hsc => ?_, hst, hm.trans hrel.2.2⟩, ?_⟩
        · have hne : r ≠ .reg .X17 := (ne_of_not_mem_armScratch hsc).2
          rw [hk r hne hsc, hrel.1 r hsc, MachSt.gpr_setFlags, MachSt.setGprW,
            MachSt.gpr_setGpr_ne _ _ hne]
        · rcases hfOk with h1 | h2 | h3
          · exact armFrame_status_eq hkeep (hst.trans h1)
          · rw [h2]; exact armFrame_nzcv hkeep
          · rw [h3]; exact armFrame_weaken_clob (armFrame_nzcv hkeep) (fun _ hm => hm)
              (Or.inr (Or.inl rfl))
      · exact stateRel_updGprFlags hrel (.reg d) _ _ _ (hd hd17) hk hst hfOk hm
    | SP =>
      rw [emitClean_append, emitClean_cons, emitClean_nil]
      refine armWp_append (hrunCore .X16) ?_
      rintro s₁ ⟨hd1, hk1, hst1, hm1⟩
      refine armWp_mono (armMovToSp_wp .X16 s₁) ?_
      rintro _ rfl
      refine stateRel_updGprFlags hrel .SP _ _ _
        (by simp [get_sp, hd1 (by decide : XReg.X16 ≠ .X17), writeSubZeroExtend])
        (fun r hne hsc => ?_) hst1 hfOk hm1
      cases r with
      | SP => exact absurd rfl hne
      | reg xr =>
        have hns := ne_of_not_mem_armScratch hsc
        rw [get_reg, Reg64s_getXReg_setSP, ← get_reg]
        exact hk1 (.reg xr) hns.1 hsc
  dsimp only [asmAluIns]
  cases rd with
  | SP => exact hfallback
  | reg d =>
    cases lhs with
    | SP => exact hfallback
    | reg ra =>
      cases rhs with
      | reg _ => exact hfallback
      | imm v =>
        cases hf : asmAluImmFastIns? op w sf d ra v with
        | none => simpa [hf] using hfallback
        | some ci =>
          simp only [hf, Option.getD_some]
          refine armWp_mono (asmAluImmFast_wp op w sf d ra v hf sm) ?_
          rintro sm' ⟨hd, hk, hst, hm⟩
          rw [haEq] at hd hst; rw [hrel.2.1] at hst
          exact stateRel_updGprFlags hrel (.reg d) _ _ _ hd hk hst hfOk hm

private theorem asmCmpTest_wp [Host] (isTest : Bool) (w : Width) (lhs : Arm64.Reg)
    (rhs : Src arm64Arch) {sv : MachSt arm64Arch} {sm : MachineData}
    (hlhs : lhs ∉ armScratch) (hrhs : ∀ r ∈ rhs.regs, r ∉ armScratch)
    (hrel : arm64StateRel sv sm) :
    let a := (sv.gpr lhs).setWidth w.bits
    let b := rhs.evalW w sv.gpr
    let f' := if isTest then arm64TestFlags w a b sv.flags else arm64CmpFlags w a b sv.flags
    _root_.Program.wp (emitClean (if isTest then asmTestIns w lhs rhs else asmCmpIns w lhs rhs))
      (fun sm' => arm64StateRel (sv.setFlags f') sm' ∧
        armMach.Frame armCondReads sm sm' armScratch [] maskNZCV)
      (fun _ _ => False) sm := by
  have haEq : (Arm64.get sm lhs).setWidth w.bits = (sv.gpr lhs).setWidth w.bits := by
    rw [hrel.1 lhs hlhs]
  have hbEq : rhs.evalW w (Arm64.get sm) = rhs.evalW w sv.gpr := by
    cases rhs with
    | imm _ => rfl
    | reg r => simp [Src.evalW, Src.eval, hrel.1 r (hrhs r List.mem_cons_self)]
  have h1 := armSrcToX_wp .X16 lhs hlhs sm
  have hra17 : (armSrcToXIns .X16 lhs).2 ≠ .X17 := h1.1 .X17 (by decide) (Or.inr rfl)
  have hwide : ∀ (w' : Width) (hw : w' = .w32 ∨ w' = .w64),
      _root_.Program.wp (emitClean (if isTest then asmTestIns w' lhs rhs else asmCmpIns w' lhs rhs))
        (fun sm' => arm64StateRel (sv.setFlags
            (if isTest then
              arm64TestFlags w' ((sv.gpr lhs).setWidth w'.bits) (rhs.evalW w' sv.gpr) sv.flags
             else arm64CmpFlags w' ((sv.gpr lhs).setWidth w'.bits) (rhs.evalW w' sv.gpr) sv.flags))
            sm' ∧ armMach.Frame armCondReads sm sm' armScratch [] maskNZCV)
        (fun _ _ => False) sm := by
    intro w' hw
    have haEq' : (Arm64.get sm lhs).setWidth w'.bits = (sv.gpr lhs).setWidth w'.bits := by
      rw [hrel.1 lhs hlhs]
    have hbEq' : rhs.evalW w' (Arm64.get sm) = rhs.evalW w' sv.gpr := by
      cases rhs with
      | imm _ => rfl
      | reg r => simp [Src.evalW, Src.eval, hrel.1 r (hrhs r List.mem_cons_self)]
    have hfb :
        _root_.Program.wp (emitClean ((armSrcToXIns .X16 lhs).1 ++
            (armRhsToXIns .X17 w' rhs).1 ++
            [armIselInsI (if isTest then .ANDS_s (xzr (widthToRegWidth w'))
                (zr (armSrcToXIns .X16 lhs).2 (widthToRegWidth w'))
                (sh (armRhsToXIns .X17 w' rhs).2)
              else .SUBS_s (xzr (widthToRegWidth w'))
                (zr (armSrcToXIns .X16 lhs).2 (widthToRegWidth w'))
                (sh (armRhsToXIns .X17 w' rhs).2))]))
          (fun sm' => arm64StateRel (sv.setFlags
              (if isTest then
                arm64TestFlags w' ((sv.gpr lhs).setWidth w'.bits) (rhs.evalW w' sv.gpr) sv.flags
               else
                arm64CmpFlags w' ((sv.gpr lhs).setWidth w'.bits) (rhs.evalW w' sv.gpr) sv.flags))
              sm' ∧ armMach.Frame armCondReads sm sm' armScratch [] maskNZCV)
          (fun _ _ => False) sm := by
      simp only [emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
      refine armWp_append h1.2 ?_
      rintro s₁ ⟨hla1, hk1, _, hm1⟩
      have h2 := armRhsToX_wp w' rhs hrhs s₁
      refine armWp_append h2.2 ?_
      rintro s₂ ⟨hrb2, hk2, _, hm2⟩
      have ha2 : (Arm64.get s₂ (.reg (armSrcToXIns .X16 lhs).2)).setWidth w'.bits =
          (sv.gpr lhs).setWidth w'.bits := by
        rw [hk2 _ (fun e => hra17 (XRegOrSp.reg.inj e)), hla1, haEq']
      have hb2 : (Arm64.get s₂ (.reg (armRhsToXIns .X17 w' rhs).2)).setWidth w'.bits =
          rhs.evalW w' sv.gpr := by
        rw [hrb2, ← hbEq']
        cases rhs with
        | imm _ => rfl
        | reg r =>
          have hr16 := (ne_of_not_mem_armScratch (hrhs r List.mem_cons_self)).1
          simp [Src.evalW, Src.eval, hk1 r hr16]
      rcases hw with rfl | rfl <;> cases isTest <;> (
        refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
          simp only [↓reduceIte, Bool.false_eq_true]
          dsimp only [sh, widthToRegWidth]
          simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
            RegWidth.bits, MemWidth.bits, Reg64s.setRegOrZr_xzr, ← get_reg]
          rw [ha2, hb2]; exact hk _ rfl) ?_
        rintro _ rfl
        exact stateRel_updFlags hrel _ maskNZCV (fun r hsc => by
          have hns := ne_of_not_mem_armScratch hsc
          exact (hk2 r hns.2).trans (hk1 r hns.1)) rfl (Or.inr (Or.inl rfl)) (hm2.trans hm1))
    cases isTest with
    | false =>
      simp only [↓reduceIte, Bool.false_eq_true] at hfb ⊢
      cases lhs with
      | SP => rcases hw with rfl | rfl <;> simpa [asmCmpIns] using hfb
      | reg ra =>
        cases rhs with
        | reg _ => rcases hw with rfl | rfl <;> simpa [asmCmpIns] using hfb
        | imm v =>
          cases hi : armImm12? (v.setWidth w'.bits) with
          | none =>
            rcases hw with rfl | rfl <;> (dsimp only [asmCmpIns]; rw [hi]; exact hfb)
          | some ei =>
            have himmAll : ∀ [Labels] pos regs,
                ei.interp (w := widthToRegWidth w') regs pos =
                  (v.setWidth w'.bits).setWidth (widthToRegWidth w').bits :=
              fun {_} pos regs => by
                simpa [BitVec.setWidth_eq] using armImm12_some
                  (by rcases hw with rfl | rfl <;> decide) hi (widthToRegWidth w') pos regs
            have htake : ∀ {m n : Nat} (x : BitVec m), x.take n = x.setWidth n := fun x => by
              apply BitVec.eq_of_getLsbD_eq; intro j; simp [BitVec.take]
            rcases hw with rfl | rfl <;> (
              dsimp only [asmCmpIns]; rw [hi]
              simp only [emitClean_cons, emitClean_nil]
              refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
                have himm := himmAll pos sm.regs
                dsimp only [widthToRegWidth, Width.bits, RegWidth.bits, MemWidth.bits] at himm ⊢
                simp only [Directive.interp, Instr.interp, Operation.interp, himm,
                  MachineData.setRegOrZr, Reg64s.setRegOrZr_xzr, Reg64s.getRegOrSp,
                  Reg64s.getRegOrSp64, RegOrSp.base, htake, BitVec.setWidth_eq,
                  RegWidth.bits, MemWidth.bits, ← get_reg, haEq', Effects.All]
                exact hk _ rfl) ?_
              rintro _ rfl
              exact stateRel_updFlags hrel _ maskNZCV (fun _ _ => rfl)
                (by simp [hrel.1 (.reg ra) hlhs, arm64CmpFlags, Src.evalW, Src.eval])
                (Or.inr (Or.inl rfl)) rfl)
    | true =>
      simp only [↓reduceIte] at hfb ⊢
      cases lhs with
      | SP => rcases hw with rfl | rfl <;> simpa [asmTestIns] using hfb
      | reg ra =>
        cases rhs with
        | reg _ => rcases hw with rfl | rfl <;> simpa [asmTestIns] using hfb
        | imm v =>
          have hi32 := int64_ofInt_setWidth (w := .W32) (v.setWidth 32)
          have hi64 := int64_ofInt_setWidth (w := .W64) (v.setWidth 64)
          simp only [RegWidth.bits] at hi32 hi64
          rcases hw with rfl | rfl <;> (
            dsimp only [asmTestIns]
            split
            · simp only [emitClean_cons, emitClean_nil]
              refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
                simp only [t_step_simp, widthToRegWidth, Width.bits, RegWidth.bits, MemWidth.bits,
                  Reg64s.setRegOrZr_xzr, ← get_reg, haEq', hi32, hi64]
                exact hk _ rfl) ?_
              rintro _ rfl
              exact stateRel_updFlags hrel _ maskNZCV (fun _ _ => rfl) rfl
                (Or.inr (Or.inl rfl)) rfl
            · simpa using hfb)
  have hsub : ∀ (w' : Width) (hw : w' = .w8 ∨ w' = .w16),
      _root_.Program.wp (emitClean (if isTest then asmTestIns w' lhs rhs else asmCmpIns w' lhs rhs))
        (fun sm' => arm64StateRel (sv.setFlags
            (if isTest then
              arm64TestFlags w' ((sv.gpr lhs).setWidth w'.bits) (rhs.evalW w' sv.gpr) sv.flags
             else arm64CmpFlags w' ((sv.gpr lhs).setWidth w'.bits) (rhs.evalW w' sv.gpr) sv.flags))
            sm' ∧ armMach.Frame armCondReads sm sm' armScratch [] maskNZCV)
        (fun _ _ => False) sm := by
    intro w' hw
    have hn : w'.bits = 8 ∨ w'.bits = 16 := by rcases hw with rfl | rfl <;> simp [Width.bits]
    have hle32 : w'.bits ≤ 32 := by rcases hw with rfl | rfl <;> decide
    have haEq' : (Arm64.get sm lhs).setWidth w'.bits = (sv.gpr lhs).setWidth w'.bits := by
      rw [hrel.1 lhs hlhs]
    have hbEq' : rhs.evalW w' (Arm64.get sm) = rhs.evalW w' sv.gpr := by
      cases rhs with
      | imm _ => rfl
      | reg r => simp [Src.evalW, Src.eval, hrel.1 r (hrhs r List.mem_cons_self)]
    have hcode : (if isTest then asmTestIns w' lhs rhs else asmCmpIns w' lhs rhs) =
        (armSrcToXIns .X16 lhs).1 ++ (armRhsToXIns .X17 w' rhs).1 ++
        [armIselInsI (.UBFM (zr .X16 .W32) (zr (armSrcToXIns .X16 lhs).2 .W32)
            w'.bits (w'.bits - 1)),
         armIselInsI (.UBFM (zr .X17 .W32) (zr (armRhsToXIns .X17 w' rhs).2 .W32)
            w'.bits (w'.bits - 1)),
         armIselInsI (if isTest then .ANDS_s (xzr .W32) (zr .X16 .W32) (sh .X17)
                      else .SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))] := by
      rcases hw with rfl | rfl <;> cases isTest <;> rfl
    rw [hcode]
    simp only [emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
    refine armWp_append h1.2 ?_
    rintro s₁ ⟨hla1, hk1, _, hm1⟩
    have h2 := armRhsToX_wp w' rhs hrhs s₁
    refine armWp_append h2.2 ?_
    rintro s₂ ⟨hrb2, hk2, _, hm2⟩
    have ha2 : (Arm64.get s₂ (.reg (armSrcToXIns .X16 lhs).2)).setWidth w'.bits =
        (sv.gpr lhs).setWidth w'.bits := by
      rw [hk2 _ (fun e => hra17 (XRegOrSp.reg.inj e)), hla1, haEq']
    have hb2 : (Arm64.get s₂ (.reg (armRhsToXIns .X17 w' rhs).2)).setWidth w'.bits =
        rhs.evalW w' sv.gpr := by
      rw [hrb2, ← hbEq']
      cases rhs with
      | imm _ => rfl
      | reg r =>
        have hr16 := (ne_of_not_mem_armScratch (hrhs r List.mem_cons_self)).1
        simp [Src.evalW, Src.eval, hk1 r hr16]
    refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, ← get_reg]
      rw [evalUBFM_shl_subword hn, BitVec.setWidth_setWidth_of_le _ hle32, ha2]
      exact hk _ rfl) ?_
    rintro _ rfl
    refine armWp_cons (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, Reg64s.getXReg_setXReg_of_ne _ _ _ _ h2.1.symm, ← get_reg]
      rw [evalUBFM_shl_subword hn, BitVec.setWidth_setWidth_of_le _ hle32, hb2]
      exact hk _ rfl) ?_
    rintro _ rfl
    cases isTest <;> (
      refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
        simp only [↓reduceIte, Bool.false_eq_true]
        dsimp only [sh]
        simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
          RegWidth.bits, MemWidth.bits, Reg64s.setRegOrZr_xzr, Reg64s.getXReg_setXReg_same,
          Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X17 ≠ XReg.X16),
          UInt64.toBitVec_ofBitVec, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
          BitVec.setWidth_eq]
        first
        | rw [subs_shl_subword hn]
        | rw [shl_subword_and hn, from_result_shl_subword hn]
        exact hk _ rfl) ?_
      rintro _ rfl
      exact stateRel_updFlags hrel _ maskNZCV (fun r hsc => by
        have hns := ne_of_not_mem_armScratch hsc
        change Arm64.get (wr (wr s₂ .X16 _) .X17 _) r = Arm64.get sm r
        rw [get_wr_of_ne _ _ _ r hns.2, get_wr_of_ne _ _ _ r hns.1, hk2 r hns.2, hk1 r hns.1])
        rfl (Or.inr (Or.inl rfl)) (hm2.trans hm1))
  cases w with
  | w8 => exact hsub .w8 (Or.inl rfl)
  | w16 => exact hsub .w16 (Or.inr rfl)
  | w32 => exact hwide .w32 (Or.inl rfl)
  | w64 => exact hwide .w64 (Or.inr rfl)

private theorem asmLoad_wp [Host] (w : Width) (ext : LoadExt) (rd : Arm64.Reg)
    (a : AddrArg Arm64.Reg) {v : BitVec w.bits} {sv : MachSt arm64Arch} {sm : MachineData}
    (haregs : ∀ r ∈ a.regs, r ∉ armScratch) (hrel : arm64StateRel sv sm)
    (hload : loadVal sv.mem w.toTy (a.eval sv.gpr) = some v) :
    _root_.Program.wp (emitClean (asmLoadIns w ext rd a))
      (fun sm' => arm64StateRel (sv.setGpr rd (ext.apply arm64Arch w (sv.gpr rd) v)) sm' ∧
        armMach.Frame armCondReads sm sm' (rd :: armScratch) [] maskNone)
      (fun _ _ => False) sm := by
  have haEq : a.eval (Arm64.get sm) = a.eval sv.gpr := by
    cases a with
    | imm _ => rfl
    | baseDisp b _ =>
      simp [AddrArg.eval, hrel.1 b (haregs b (by simp [AddrArg.regs]))]
    | baseIdxDisp b idx _ _ =>
      simp [AddrArg.eval, hrel.1 b (haregs b (by simp [AddrArg.regs])),
        hrel.1 idx (haregs idx (by simp [AddrArg.regs]))]
  have hsetup := armSetupAddrTotal_wp w.bytes a sm haregs
  dsimp only [asmLoadIns]
  generalize armSetupAddrTotalIns w.bytes a = p at hsetup ⊢
  rcases p with ⟨setup, addr⟩
  rcases hsetup with ⟨⟨rx, hrx, _⟩, _, hwpSetup⟩
  have hExtEq : ∀ (old₁ old₂ : BitVec 64),
      ext.apply arm64Arch w old₁ v = ext.apply arm64Arch w old₂ v := by
    intro _ _; cases ext <;> rfl
  cases rd with
  | reg d =>
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append hwpSetup ?_
    rintro s₁ ⟨heval, hk1, hst1, hm1⟩
    rw [haEq] at heval
    refine armWp_mono (asmLoadDir_wp w ext d addr (a.eval sv.gpr) v s₁ ⟨rx, hrx⟩ heval
      (by rw [hm1, hrel.2.2]; exact hload)) ?_
    rintro _ rfl
    rw [hExtEq (Arm64.get s₁ (.reg d)) (sv.gpr (.reg d))]
    exact stateRel_updGpr hrel (.reg d) _ (get_wr_same _ _ _)
      (fun r hne hsc => by rw [get_wr_of_ne _ _ _ r hne]; exact hk1 r hsc) hst1 hm1
  | SP =>
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append hwpSetup ?_
    rintro s₁ ⟨heval, hk1, hst1, hm1⟩
    rw [haEq] at heval
    refine armWp_cons (asmLoadDir_wp w ext .X16 addr (a.eval sv.gpr) v s₁ ⟨rx, hrx⟩ heval
      (by rw [hm1, hrel.2.2]; exact hload)) ?_
    rintro _ rfl
    refine armWp_mono (armMovToSp_wp .X16 _) ?_
    rintro _ rfl
    rw [hExtEq (Arm64.get s₁ (.reg .X16)) (sv.gpr .SP)]
    refine stateRel_updGpr hrel .SP _ (by simp [get_sp]) (fun r hne hsc => ?_) hst1 hm1
    cases r with
    | SP => exact absurd rfl hne
    | reg xr =>
      have hx16 := (xreg_ne_scratch_of_not_mem hsc).1
      rw [get_reg, Reg64s_getXReg_setSP, ← get_reg,
        get_wr_of_ne _ _ _ _ (fun e => hx16 (XRegOrSp.reg.inj e))]
      exact hk1 (.reg xr) hsc

private theorem asmStore_wp [Host] (w : Width) (rs : Arm64.Reg) (a : AddrArg Arm64.Reg)
    {sv : MachSt arm64Arch} {sm : MachineData}
    (hrs : rs ∉ armScratch) (haregs : ∀ r ∈ a.regs, r ∉ armScratch)
    (hrel : arm64StateRel sv sm) (hok : storeOk sv.mem w.toTy (a.eval sv.gpr)) :
    _root_.Program.wp (emitClean (asmStoreIns w rs a))
      (fun sm' => arm64StateRel
          (sv.setMem (storeMem sv.mem w.toTy (a.eval sv.gpr) ((sv.gpr rs).setWidth w.bits))) sm' ∧
        armMach.Frame armCondReads sm sm' armScratch [] maskNone)
      (fun _ _ => False) sm := by
  have haEq : a.eval (Arm64.get sm) = a.eval sv.gpr := by
    cases a with
    | imm _ => rfl
    | baseDisp b _ =>
      simp [AddrArg.eval, hrel.1 b (haregs b (by simp [AddrArg.regs]))]
    | baseIdxDisp b idx _ _ =>
      simp [AddrArg.eval, hrel.1 b (haregs b (by simp [AddrArg.regs])),
        hrel.1 idx (haregs idx (by simp [AddrArg.regs]))]
  have hsetup := armSetupAddrTotal_wp w.bytes a sm haregs
  dsimp only [asmStoreIns]
  generalize armSetupAddrTotalIns w.bytes a = p at hsetup ⊢
  rcases p with ⟨setup, addr⟩
  rcases hsetup with ⟨⟨rx, hrx, hrx17⟩, hoff, hwpSetup⟩
  dsimp only at hrx hoff
  cases rs with
  | reg x =>
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append hwpSetup ?_
    rintro s₁ ⟨heval, hk1, hst1, hm1⟩
    rw [haEq] at heval
    refine armWp_mono (asmStoreDir_wp w x addr (a.eval sv.gpr) s₁ ⟨rx, hrx⟩ heval
      (by rw [hm1, hrel.2.2]; exact hok)) ?_
    rintro _ rfl
    have hxEq : Arm64.get s₁ (.reg x) = sv.gpr (.reg x) := (hk1 (.reg x) hrs).trans (hrel.1 _ hrs)
    refine ⟨⟨fun r hsc => (hk1 r hsc).trans (hrel.1 r hsc), hst1.trans hrel.2.1, ?_⟩,
      armFrame_status_eq hk1 hst1⟩
    dsimp only [MachSt.setMem]; rw [hm1, hrel.2.2, hxEq]
  | SP =>
    simp only [emitClean_append, emitClean_cons, emitClean_nil]
    refine armWp_append hwpSetup ?_
    rintro s₁ ⟨heval, hk1, hst1, hm1⟩
    rw [haEq] at heval
    refine armWp_cons (armMovToX_wp .X17 .SP s₁) ?_
    rintro _ rfl
    have heval2 : ∀ [Labels] pos, addr.eval (wr s₁ .X17 (Arm64.get s₁ .SP)) pos =
        (a.eval sv.gpr, wr s₁ .X17 (Arm64.get s₁ .SP)) :=
      addrExpr_eval_wr_x17 hrx hrx17 hoff heval (Arm64.get s₁ .SP)
    refine armWp_mono (asmStoreDir_wp w .X17 addr (a.eval sv.gpr) _ ⟨rx, hrx⟩ heval2
      (by rw [dmem_wr, hm1, hrel.2.2]; exact hok)) ?_
    rintro _ rfl
    have hspEq : Arm64.get s₁ .SP = sv.gpr .SP := (hk1 .SP hrs).trans (hrel.1 _ hrs)
    have hkeep : ∀ r, r ∉ armScratch →
        Arm64.get (wr s₁ .X17 (Arm64.get s₁ .SP)) r = Arm64.get sm r :=
      fun r hsc => (get_wr_of_ne _ _ _ r (ne_of_not_mem_armScratch hsc).2).trans (hk1 r hsc)
    refine ⟨⟨fun r hsc => (hkeep r hsc).trans (hrel.1 r hsc), hst1.trans hrel.2.1, ?_⟩,
      armFrame_status_eq hkeep hst1⟩
    dsimp only [MachSt.setMem, wr]
    rw [hm1, hrel.2.2, get_reg, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, hspEq]

private theorem asmCanonAbi_wp [Host] (t : Ty) (r : Arm64.Reg) {sv : MachSt arm64Arch}
    {sm : MachineData} (hr : r ∉ armScratch)
    (ht : match t with | .bits n => n ∈ [8, 16, 32, 64] | _ => True)
    (hrel : arm64StateRel sv sm) :
    _root_.Program.wp (armCanonAbi t r).1
      (fun sm' => arm64StateRel (sv.setGpr r (canonAbiVal t (sv.gpr r))) sm' ∧
        armMach.Frame armCondReads sm sm' (r :: armScratch) [] maskNone)
      (fun _ _ => False) sm := by
  have hcanX : ∀ (x : XReg) (s : MachineData),
      _root_.Program.wp (emitClean (armCanonAbiXRegIns t x))
        (fun s' => s' = wr s x (canonAbiVal t (Arm64.get s (.reg x))))
        (fun _ _ => False) s := by
    intro x s
    cases t with
    | bool =>
      simp only [armCanonAbiXRegIns, emitClean_cons, emitClean_nil]
      exact armDirFallsTo_wp fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, BitVec.setWidth_eq]
        rw [evalUBFM_low (w := .W64) (n := 8) _ (by decide) (by decide)]; exact hk _ rfl
    | float _ | pair _ _ =>
      simp only [armCanonAbiXRegIns, emitClean_nil, canonAbiVal]
      exact armWp_nil (by cases x <;> rfl)
    | bits n =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · simp only [armCanonAbiXRegIns]
        exact armDirFallsTo_wp fun {_} _ _ _ _ hk => by
          simp only [t_step_simp, BitVec.setWidth_eq]
          rw [evalUBFM_low (w := .W64) (n := 8) _ (by decide) (by decide)]; exact hk _ rfl
      · simp only [armCanonAbiXRegIns]
        exact armDirFallsTo_wp fun {_} _ _ _ _ hk => by
          simp only [t_step_simp, BitVec.setWidth_eq]
          rw [evalUBFM_low (w := .W64) (n := 16) _ (by decide) (by decide)]; exact hk _ rfl
      · simp only [armCanonAbiXRegIns]
        exact armDirFallsTo_wp fun {_} _ _ _ _ hk => by
          dsimp only [sh]
          simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
            RegWidth.bits, MemWidth.bits, BitVec.zero_or]; exact hk _ rfl
      · simp only [armCanonAbiXRegIns, canonAbiVal, BitVec.setWidth_eq]
        exact armWp_nil (by cases x <;> rfl)
  cases r with
  | reg x =>
    dsimp only [armCanonAbi, armCanonAbiIns]
    refine armWp_mono (hcanX x sm) ?_
    rintro _ rfl
    exact stateRel_updGpr hrel (.reg x) _ (by rw [get_wr_same, hrel.1 (.reg x) hr])
      (fun q hne _ => get_wr_of_ne _ _ _ q hne) rfl rfl
  | SP =>
    have hspStep : ∀ (hcode : (armCanonAbi t .SP).1 =
        emitClean ([armMovToXI .X16 .SP] ++ armCanonAbiXRegIns t .X16 ++ [armMovToSpI .X16])),
        _root_.Program.wp (armCanonAbi t .SP).1
          (fun sm' => arm64StateRel (sv.setGpr .SP (canonAbiVal t (sv.gpr .SP))) sm' ∧
            armMach.Frame armCondReads sm sm' (.SP :: armScratch) [] maskNone)
          (fun _ _ => False) sm := by
      intro hcode
      rw [hcode]
      simp only [emitClean_append, emitClean_cons, emitClean_nil,
        List.cons_append, List.nil_append]
      refine armWp_cons (armMovToX_wp .X16 .SP sm) ?_
      rintro _ rfl
      refine armWp_append (hcanX .X16 _) ?_
      rintro _ rfl
      refine armWp_mono (armMovToSp_wp .X16 _) ?_
      rintro _ rfl
      refine stateRel_updGpr hrel .SP _ (by simp [get_sp, hrel.1 .SP hr]) (fun q hne hsc => ?_)
        rfl rfl
      cases q with
      | SP => exact absurd rfl hne
      | reg xq =>
        have hx16 := (xreg_ne_scratch_of_not_mem hsc).1
        simp [get_reg, Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
    cases t with
    | bool => exact hspStep rfl
    | float _ | pair _ _ =>
      dsimp only [armCanonAbi, armCanonAbiIns, emitClean_nil, canonAbiVal]
      exact armWp_nil (stateRel_updGpr hrel .SP _ (hrel.1 .SP hr) (fun _ _ _ => rfl) rfl rfl)
    | bits n =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hspStep rfl
      · exact hspStep rfl
      · exact hspStep rfl
      · dsimp only [armCanonAbi, armCanonAbiIns, emitClean_nil, canonAbiVal]
        rw [BitVec.setWidth_eq]
        exact armWp_nil (stateRel_updGpr hrel .SP _ (hrel.1 .SP hr) (fun _ _ _ => rfl) rfl rfl)

/-! ## 2. Top-Level Simulation (`asmArm64_fallsTo`, `asmArm64List_fallsTo`, `asmArm64_jump`) -/

private theorem asmArm64_fallsTo_wp [Host] {nextPc : BitVec 64}
    {i : Instr arm64Arch} {sv sv' : MachSt arm64Arch} {sm : MachineData}
    (hok : arm64InstrOk i sv) (hrel : arm64StateRel sv sm)
    (hstep : instrRel arm64Arch (hostSymAddr ‹Host›) nextPc i sv (.fall sv')) :
    _root_.Program.wp (asmArm64 i)
      (fun sm' => arm64StateRel sv' sm' ∧
        armMach.Frame armCondReads sm sm' (i.clobGpr ++ armScratch) [] i.clobFlags)
      (fun _ _ => False) sm := by
  have huses : ∀ r ∈ i.uses, r ∉ armScratch := hok.1.1
  cases i with
  | label l =>
    cases hstep
    exact _root_.Program.wp_label ⟨hrel, Machine.Frame.refl (M := armMach) armCondReads sm _ [] _⟩
  | pad _ =>
    cases hstep
    refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => hk sm rfl) ?_
    rintro _ rfl
    exact ⟨hrel, Machine.Frame.refl (M := armMach) armCondReads sm _ [] _⟩
  | mov w rd rs =>
    cases hstep
    exact asmMov_wp w rd rs (huses rs List.mem_cons_self) hrel
  | movi rd imm =>
    cases hstep
    cases rd with
    | reg d =>
      refine armWp_mono (armMovImm_wp d imm sm) ?_
      rintro _ rfl
      exact stateRel_updGpr hrel (.reg d) imm (get_wr_same _ _ _)
        (fun r hne _ => get_wr_of_ne _ _ _ r hne) rfl rfl
    | SP =>
      dsimp only [asmArm64, armMovi, armMoviIns]
      rw [emitClean_append, emitClean_cons, emitClean_nil]
      refine armWp_append (armMovImm_wp .X16 imm sm) ?_
      rintro _ rfl
      refine armWp_mono (armMovToSp_wp .X16 _) ?_
      rintro _ rfl
      refine stateRel_updGpr hrel .SP imm (by simp [get_sp]) (fun r hne hsc => ?_) rfl rfl
      cases r with
      | SP => exact absurd rfl hne
      | reg xr =>
        have hx16 := (xreg_ne_scratch_of_not_mem hsc).1
        simp [get_reg, Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
  | alu op w rd lhs rhs sf =>
    cases hstep
    exact asmAlu_wp op w rd lhs rhs sf (huses lhs List.mem_cons_self)
      (fun r hr => huses r (List.mem_cons_of_mem _ hr)) hrel
  | cmp w lhs rhs =>
    cases hstep
    have h := asmCmpTest_wp false w lhs rhs (huses lhs List.mem_cons_self)
      (fun r hr => huses r (List.mem_cons_of_mem _ hr)) hrel
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact h
  | test w lhs rhs =>
    cases hstep
    have h := asmCmpTest_wp true w lhs rhs (huses lhs List.mem_cons_self)
      (fun r hr => huses r (List.mem_cons_of_mem _ hr)) hrel
    simp only [↓reduceIte] at h
    exact h
  | clearFlags =>
    cases hstep
    refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, Reg64s.setRegOrZr_xzr]; exact hk _ rfl) ?_
    rintro _ rfl
    exact stateRel_updFlags hrel arm64ClearFlagsVal FlagMask.all (fun _ _ => rfl) rfl
      (Or.inr (Or.inr rfl)) rfl
  | setcc rd c =>
    cases hstep
    have hev : c.interp sm.status = c.interp sv.flags := by rw [hrel.2.1]
    have hbv : BitVec.ofNat 64 (c.interp sm.status).toNat =
        (BitVec.ofNat 8 (c.interp sv.flags).toNat).setWidth 64 := by
      rw [hev]; cases c.interp sv.flags <;> decide
    cases rd with
    | reg d =>
      dsimp only [asmArm64, armSetcc, armSetccIns, emitClean_cons, emitClean_nil]
      refine armWp_mono (armCset64_wp d c sm) ?_
      rintro _ rfl
      exact stateRel_updGpr hrel (.reg d) _ (by rw [get_wr_same, hbv]; rfl)
        (fun r hne _ => get_wr_of_ne _ _ _ r hne) rfl rfl
    | SP =>
      dsimp only [asmArm64, armSetcc, armSetccIns, emitClean_cons, emitClean_nil]
      refine armWp_cons (armCset64_wp .X16 c sm) ?_
      rintro _ rfl
      refine armWp_mono (armMovToSp_wp .X16 _) ?_
      rintro _ rfl
      refine stateRel_updGpr hrel .SP _ (by simp [get_sp, hbv, writeSubZeroExtend])
        (fun r hne hsc => ?_) rfl rfl
      cases r with
      | SP => exact absurd rfl hne
      | reg xr =>
        have hx16 := (xreg_ne_scratch_of_not_mem hsc).1
        simp [get_reg, Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
  | load w ext rd a =>
    rcases hstep with ⟨v, hld, hEq⟩; cases hEq
    exact asmLoad_wp w ext rd a huses hrel hld
  | store w rs a =>
    rcases hstep with ⟨hstOk, hEq⟩; cases hEq
    exact asmStore_wp w rs a (huses rs List.mem_cons_self)
      (fun r hr => huses r (List.mem_cons_of_mem _ hr)) hrel hstOk
  | slotSt idx rs =>
    rcases hstep with ⟨hstOk, hEq⟩; cases hEq
    have hspEq : Arm64.get sm .SP = sv.gpr .SP := hrel.1 .SP (by simp [armScratch])
    have hal : (Arm64.get sm .SP).toNat % 16 = 0 := hspEq.symm ▸ hok.2
    have hrs : rs ∉ armScratch := huses rs (by simp [Instr.uses])
    cases rs with
    | reg x =>
      refine armWp_mono (armStSpXReg_wp_direct x (8 * idx) sm
        (xreg_ne_scratch_of_not_mem hrs).1 hal (by rw [hrel.2.2, hspEq]; exact hstOk)) ?_
      rintro s' ⟨hsp', hx', hst', hd'⟩
      have hk : ∀ r, r ∉ armScratch → Arm64.get s' r = Arm64.get sm r := fun r hsc => by
        cases r with
        | SP => simp [get_sp, hsp']
        | reg y => exact congrArg UInt64.toBitVec (hx' y (xreg_ne_scratch_of_not_mem hsc).1)
      refine ⟨⟨fun r hsc => (hk r hsc).trans (hrel.1 r hsc), hst'.trans hrel.2.1, ?_⟩,
        armFrame_status_eq hk hst'⟩
      dsimp only [MachSt.setMem]; rw [hd', hrel.2.2, hspEq, hrel.1 (.reg x) hrs]
    | SP =>
      dsimp only [asmArm64, armSlotSt, armSlotStIns]
      rw [emitClean_append, emitClean_cons, emitClean_nil]
      refine armWp_cons (armMovToX_wp .X17 .SP sm) ?_
      rintro _ rfl
      refine armWp_mono (armStSpXReg_wp_direct .X17 (8 * idx) _ (by decide)
        (by simpa [get_sp] using hal)
        (by rw [dmem_wr, hrel.2.2, get_wr_of_ne sm .X17 _ .SP (by decide), hspEq]; exact hstOk)) ?_
      rintro s' ⟨hsp', hx', hst', hd'⟩
      have hk : ∀ r, r ∉ armScratch → Arm64.get s' r = Arm64.get sm r := fun r hsc => by
        cases r with
        | SP => simp [get_sp, hsp']
        | reg y =>
          have hy := xreg_ne_scratch_of_not_mem hsc
          exact congrArg UInt64.toBitVec
            ((hx' y hy.1).trans (Reg64s.getXReg_setXReg_of_ne _ _ _ _ hy.2.symm))
      refine ⟨⟨fun r hsc => (hk r hsc).trans (hrel.1 r hsc), hst'.trans hrel.2.1, ?_⟩,
        armFrame_status_eq hk hst'⟩
      dsimp only [MachSt.setMem]
      rw [hd', dmem_wr, hrel.2.2, get_wr_same, get_wr_of_ne sm .X17 _ .SP (by decide), hspEq]
  | slotLd rd idx =>
    rcases hstep with ⟨v, hld, hEq⟩; cases hEq
    have hspEq : Arm64.get sm .SP = sv.gpr .SP := hrel.1 .SP (by simp [armScratch])
    have hal : (Arm64.get sm .SP).toNat % 16 = 0 := hspEq.symm ▸ hok.2
    cases rd with
    | reg x =>
      refine armWp_mono (armLdSpXReg_wp_direct x (8 * idx) v sm hal
        (by rw [hrel.2.2, hspEq]; exact hld)) ?_
      rintro s' ⟨hsp', hx, hk', hst', hd'⟩
      refine stateRel_updGpr hrel (.reg x) v (by simp [get_reg, hx]) (fun r hne hsc => ?_)
        hst' hd'
      cases r with
      | SP => simp [get_sp, hsp']
      | reg y =>
        exact congrArg UInt64.toBitVec
          (hk' y (fun e => hne (e ▸ rfl)) (xreg_ne_scratch_of_not_mem hsc).1)
    | SP =>
      dsimp only [asmArm64, armSlotLd, armSlotLdIns]
      rw [emitClean_append, emitClean_cons, emitClean_nil]
      refine armWp_append (armLdSpXReg_wp_direct .X17 (8 * idx) v sm hal
        (by rw [hrel.2.2, hspEq]; exact hld)) ?_
      rintro s₁ ⟨_, hx17, hk1, hst1, hd1⟩
      refine armWp_mono (armMovToSp_wp .X17 s₁) ?_
      rintro _ rfl
      refine stateRel_updGpr hrel .SP v (by simp [get_sp, get_reg, hx17]) (fun r hne hsc => ?_)
        hst1 hd1
      cases r with
      | SP => exact absurd rfl hne
      | reg y =>
        have hy := xreg_ne_scratch_of_not_mem hsc
        rw [get_reg, Reg64s_getXReg_setSP]
        exact congrArg UInt64.toBitVec (hk1 y hy.2 hy.1)
  | prologue ns =>
    rcases hstep with ⟨hstOk, hEq⟩; cases hEq
    have hspEq : Arm64.get sm .SP = sv.gpr .SP := hrel.1 .SP (by simp [armScratch])
    have hal : (Arm64.get sm .SP).toNat % 16 = 0 := hspEq.symm ▸ hok.2
    dsimp only [asmArm64, armPrologue, armPrologueIns]
    rw [emitClean_append]
    refine armWp_append (armSpOp_wp_direct true (armFrameSize ns) sm) ?_
    rintro s₁ ⟨hsp1, hx1, hst1, hd1⟩
    have hsp1_eq : Arm64.get s₁ .SP = sv.gpr .SP - BitVec.ofNat 64 (armFrameSize ns) := by
      simp [get_sp, hsp1, hspEq]
    have hal1 : (Arm64.get s₁ .SP).toNat % 16 = 0 :=
      hsp1_eq ▸ aligned16_sub (hspEq ▸ hal) (armFrameSize_mod ns)
    refine armWp_mono (armStSpXReg_wp_direct .X30 (8 * ns) s₁ (by decide) hal1
      (by rw [hd1, hrel.2.2, hsp1_eq]; exact hstOk)) ?_
    rintro s' ⟨hsp2, hx2, hst2, hd2⟩
    have hk : ∀ r, r ≠ .SP → r ∉ armScratch → Arm64.get s' r = Arm64.get sm r := fun r hne hsc => by
      cases r with
      | SP => exact absurd rfl hne
      | reg y =>
        have hy16 := (xreg_ne_scratch_of_not_mem hsc).1
        exact congrArg UInt64.toBitVec ((hx2 y hy16).trans (hx1 y hy16))
    have hx30 : Arm64.get s₁ (.reg .X30) = sv.gpr (.reg .X30) := by
      rw [get_reg, hx1 .X30 (by decide), ← get_reg]
      exact hrel.1 (.reg .X30) (by simp [armScratch])
    refine ⟨⟨fun r hsc => ?_, (hst2.trans hst1).trans hrel.2.1, ?_⟩,
      armFrame_status_eq (fun r hr => by
        change r ∉ .SP :: armScratch at hr
        rw [List.mem_cons, not_or] at hr; exact hk r hr.1 hr.2) (hst2.trans hst1)⟩
    · by_cases heq : r = .SP
      · subst heq; simp [get_sp, hsp2, hsp1, hspEq]
      · rw [hk r heq hsc, hrel.1 r hsc, MachSt.gpr_setFlags, MachSt.gpr_setMem,
          MachSt.gpr_setGpr_ne _ _ heq]
    · simp only [MachSt.mem_setFlags, MachSt.mem_setMem, hd2, hd1, hrel.2.2, hsp1_eq, hx30]
  | epilogue ns =>
    rcases hstep with ⟨ra, hld, hEq⟩; cases hEq
    have hspEq : Arm64.get sm .SP = sv.gpr .SP := hrel.1 .SP (by simp [armScratch])
    have hal : (Arm64.get sm .SP).toNat % 16 = 0 := hspEq.symm ▸ hok.2
    dsimp only [asmArm64, armEpilogue, armEpilogueIns]
    rw [emitClean_append]
    refine armWp_append (armLdSpXReg_wp_direct .X30 (8 * ns) ra sm hal
      (by rw [hrel.2.2, hspEq]; exact hld)) ?_
    rintro s₁ ⟨hsp1, hx30, hx1, hst1, hd1⟩
    refine armWp_mono (armSpOp_wp_direct false (armFrameSize ns) s₁) ?_
    rintro s' ⟨hsp2, hx2, hst2, hd2⟩
    have hkeep : ∀ r, r ∉ Instr.clobGpr (A := arm64Arch) (.epilogue ns) ++ armScratch →
        Arm64.get s' r = Arm64.get sm r := fun r hr => by
      change r ∉ .SP :: .reg .X30 :: armScratch at hr
      rw [List.mem_cons, not_or, List.mem_cons, not_or] at hr
      cases r with
      | SP => exact absurd rfl hr.1
      | reg y =>
        have hy16 := (xreg_ne_scratch_of_not_mem hr.2.2).1
        have hy30 : y ≠ .X30 := fun e => hr.2.1 (e ▸ rfl)
        exact congrArg UInt64.toBitVec ((hx2 y hy16).trans (hx1 y hy30 hy16))
    refine ⟨⟨fun r hsc => ?_, (hst2.trans hst1).trans hrel.2.1,
      (hd2.trans hd1).trans hrel.2.2⟩, armFrame_status_eq hkeep (hst2.trans hst1)⟩
    by_cases hsp : r = .SP
    · subst hsp; simp only [get_sp, hsp2, hsp1, Bool.false_eq_true, ↓reduceIte,
        MachSt.gpr_setFlags, MachSt.gpr_setGpr_same]
      rw [← get_sp, hspEq]
    · by_cases hlr : r = .reg .X30
      · subst hlr; simp [get_reg, hx2 .X30 (by decide), hx30]
      · have hnot : r ∉ Instr.clobGpr (A := arm64Arch) (.epilogue ns) ++ armScratch := by
          simp [Instr.clobGpr, Instr.defs, Abi.raRegs, RaKind.raRegs, hsp, hlr, hsc]
        rw [hkeep r hnot, hrel.1 r hsc, MachSt.gpr_setFlags,
          MachSt.gpr_setGpr_ne _ _ hsp, MachSt.gpr_setGpr_ne _ _ hlr]
  | canonAbi t r =>
    cases hstep
    exact asmCanonAbi_wp t r (huses r List.mem_cons_self) (by cases t <;> exact hok.1.2) hrel
  | symAddr sym rd =>
    cases hstep
    cases rd with
    | reg x =>
      refine armWp_mono (armSymAddr_wp x sym sm) ?_
      rintro _ rfl
      exact stateRel_updGpr hrel (.reg x) _ (get_wr_same _ _ _)
        (fun r hne _ => get_wr_of_ne _ _ _ r hne) rfl rfl
    | SP =>
      dsimp only [asmArm64]
      refine armWp_append (armSymAddr_wp .X16 sym sm) ?_
      rintro _ rfl
      refine armWp_mono (armMovToSp_wp .X16 _) ?_
      rintro _ rfl
      refine stateRel_updGpr hrel .SP _ (by simp [get_sp, hostSymAddr, hostLabel])
        (fun r hne hsc => ?_) rfl rfl
      cases r with
      | SP => exact absurd rfl hne
      | reg xr =>
        have hx16 := (xreg_ne_scratch_of_not_mem hsc).1
        simp [get_reg, Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]
  | jcc c l =>
    dsimp only [instrRel] at hstep
    cases hc : c.interp sv.flags with
    | true => simp [hc] at hstep
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hstep
      subst hstep
      refine _root_.Program.wp_singleton fun k _ => ?_
      simp only [Directive.interp, Instr.interp, Operation.interp, hrel.2.1, hc,
        Bool.false_eq_true, ↓reduceIte, Effects.All]
      exact Or.inl ⟨trivial, hrel, Machine.Frame.refl (M := armMach) armCondReads sm _ [] _⟩
  | jnzGpr r l =>
    dsimp only [instrRel] at hstep
    cases hnz : ((sv.gpr r).setWidth 8 != 0#8) with
    | true => simp [hnz] at hstep
    | false =>
      simp only [hnz, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hstep
      subst hstep
      have h8 : (sv.gpr r).setWidth 8 = 0#8 := by simpa [bne] using hnz
      have hr : r ∉ armScratch := huses r List.mem_cons_self
      have hrEq : Arm64.get sm r = sv.gpr r := hrel.1 r hr
      have hcbnz : ∀ (s1 : MachineData), Arm64.get s1 (.reg .X16) = 0#64 →
          _root_.Program.wp [ins (.CBNZ (zr .X16 .W32) (.label l))]
            (fun s' => s' = s1) (fun _ _ => False) s1 := fun s1 h0 =>
        _root_.Program.wp_singleton fun k _ => by
          simp only [Directive.interp, Instr.interp, Operation.interp, getRegOrZr_zr,
            RegWidth.bits, MemWidth.bits, ← get_reg, h0, BitVec.setWidth_zero, Effects.All]
          exact Or.inl ⟨rfl, rfl⟩
      have hubfm : ∀ (x : XReg) (s1 : MachineData), (Arm64.get s1 (.reg x)).setWidth 8 = 0#8 →
          _root_.Program.wp [ins (.UBFM (zr .X16 .W32) (zr x .W32) 0 7)]
            (fun s' => s' = wr s1 .X16 0#64) (fun _ _ => False) s1 := fun x s1 h0 =>
        armDirFallsTo_wp fun {_} _ _ _ _ hk => by
          simp only [t_step_simp, RegWidth.bits, MemWidth.bits, ← get_reg]
          rw [evalUBFM_low (w := .W32) (n := 8) _ (by decide) (by decide),
            BitVec.setWidth_setWidth_of_le (Arm64.get s1 (.reg x)) (by decide : 8 ≤ 32), h0]
          exact hk _ rfl
      cases r with
      | reg x =>
        dsimp only [asmArm64, asmJnzGprIns, emitClean_cons, emitClean_nil]
        refine armWp_cons (hubfm x sm (by rw [hrEq, h8])) ?_
        rintro _ rfl
        refine armWp_mono (hcbnz _ (get_wr_same _ _ _)) ?_
        rintro _ rfl
        exact ⟨⟨fun q hsc => (get_wr_of_ne _ _ _ q (ne_of_not_mem_armScratch hsc).1).trans
            (hrel.1 q hsc), hrel.2.1, hrel.2.2⟩,
          frame_wr .X16 0#64 List.mem_cons_self maskNone⟩
      | SP =>
        dsimp only [asmArm64, asmJnzGprIns, emitClean_cons, emitClean_nil]
        refine armWp_cons (armMovToX_wp .X16 .SP sm) ?_
        rintro _ rfl
        refine armWp_cons (hubfm .X16 _ (by rw [get_wr_same, hrEq, h8])) ?_
        rintro _ rfl
        refine armWp_mono (hcbnz _ (get_wr_same _ _ _)) ?_
        rintro _ rfl
        exact ⟨⟨fun q hsc => by
            have h16 := (ne_of_not_mem_armScratch hsc).1
            rw [get_wr_of_ne _ _ _ q h16, get_wr_of_ne _ _ _ q h16]; exact hrel.1 q hsc,
            hrel.2.1, hrel.2.2⟩,
          armFrame_status_eq (fun q hsc => by
            have h16 := (ne_of_not_mem_armScratch hsc).1
            rw [get_wr_of_ne _ _ _ q h16, get_wr_of_ne _ _ _ q h16]) rfl⟩
  | jmp _ | call _ | icall _ | ret | exitJmp _ | tailJmpR _ | ijmp _ => cases hstep
  | native d =>
    rcases hstep with ⟨no, hst, hEq⟩
    cases no with
    | jump _ _ => cases hEq
    | halt _ _ => cases hEq
    | fall s1 =>
      cases hEq
      exact asmNative_fallsTo_wp huses hrel hst

/-- Per-instruction fall-through simulation for `asmArm64`: every fall-through `Vll` step under
`arm64InstrOk` and `arm64StateRel` is simulated by `asmArm64 i` with exact register/flag framing. -/
theorem asmArm64_fallsTo {h : Host} {k : Nat} {nextPc : BitVec 64}
    {i : Instr arm64Arch} {sv sv' : MachSt arm64Arch} {sm : MachineData}
    {post : MachineState → Prop}
    (hok : arm64InstrOk i sv) (hrel : arm64StateRel sv sm)
    (hstep : instrRel arm64Arch (hostSymAddr h) nextPc i sv (.fall sv')) :
    armMach.FallsTo armCondReads h k (asmArm64 i) (i.clobGpr ++ armScratch) [] i.clobFlags
      sm (fun sm' => arm64StateRel sv' sm') post :=
  letI := h; armFallsTo_of_wp (asmArm64_fallsTo_wp hok hrel hstep)

private theorem asmArm64List_fallsTo_wp [Host] {is : List (Instr arm64Arch)}
    {sv sv' : MachSt arm64Arch} {sm : MachineData}
    (hex : ExecBodyOk (hostSymAddr ‹Host›) is sv sv') (hrel : arm64StateRel sv sm) :
    _root_.Program.wp (asmArm64List is)
      (fun sm' => arm64StateRel sv' sm' ∧
        armMach.Frame armCondReads sm sm' (is.flatMap Instr.clobGpr ++ armScratch) []
          (instrListClobFlags is))
      (fun _ _ => False) sm := by
  induction hex generalizing sm with
  | nil => exact armWp_nil ⟨hrel, Machine.Frame.refl (M := armMach) armCondReads sm _ [] _⟩
  | cons hok hstep _ ih =>
    simp only [asmArm64List, List.flatMap_cons, instrListClobFlags, List.foldr_cons]
    refine armWp_append (asmArm64_fallsTo_wp hok hrel hstep) ?_
    rintro s₁ ⟨hrel1, hfr1⟩
    refine armWp_mono (ih hrel1) ?_
    rintro s₂ ⟨hrel2, hfr2⟩
    refine ⟨hrel2, armFrame_weaken_clob (armFrame_trans_or hfr1 hfr2) (fun r hr => ?_) (Or.inl rfl)⟩
    simp only [List.mem_append] at hr ⊢
    rcases hr with (h1 | h1) | (h1 | h1)
    · exact Or.inl (Or.inl h1)
    · exact Or.inr h1
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1

/-- Straight-line simulation for `asmArm64List`: any `ExecBodyOk` fall-through trace is simulated
compositionally by `asmArm64List is` preserving `arm64StateRel` and exact accumulated framing. -/
theorem asmArm64List_fallsTo {h : Host} {k : Nat}
    {is : List (Instr arm64Arch)} {sv sv' : MachSt arm64Arch} {sm : MachineData}
    {post : MachineState → Prop}
    (hex : ExecBodyOk (hostSymAddr h) is sv sv') (hrel : arm64StateRel sv sm) :
    armMach.FallsTo armCondReads h k (asmArm64List is)
      (is.flatMap Instr.clobGpr ++ armScratch) [] (instrListClobFlags is)
      sm (fun sm' => arm64StateRel sv' sm') post :=
  letI := h; armFallsTo_of_wp (asmArm64List_fallsTo_wp hex hrel)

/-- Control-flow transfer simulation for `asmArm64`: every jump outcome of `instrRel` (including
`jmp`, `jcc` taken, `jnzGpr` taken, `call`, `icall`, `ret`, `exitJmp`, `tailJmpR`, `ijmp`, and
`.native d` jumps) transfers control in Kraken AArch64 to `Int64.ofBitVec pc'` with `arm64StateRel`
and exact framing. -/
theorem asmArm64_jump {h : Host} {k : Nat}
    {i : Instr arm64Arch} {sv sv' : MachSt arm64Arch} {pc' : BitVec 64} {sm : MachineData}
    {post : MachineState → Prop}
    (hc : (asmArm64 i).IsInfixAt (armMach.prog h) k)
    (hok : arm64InstrOk i sv) (hrel : arm64StateRel sv sm)
    (hstep : instrRel arm64Arch (hostSymAddr h)
      (armMach.addrOf h (k + (asmArm64 i).length)).toBitVec i sv (.jump pc' sv'))
    (hcont : ∀ sm', arm64StateRel sv' sm' →
      armMach.Frame armCondReads sm sm' (i.clobGpr ++ armScratch) [] i.clobFlags →
      Eventually (armMach.step h) post ⟨sm', Int64.ofBitVec pc'⟩) :
    armMach.Run h k sm post := by
  letI := h
  have huses : ∀ r ∈ i.uses, r ∉ armScratch := hok.1.1
  have hLabEq : ∀ l : Sym, Labels.label l = Int64.ofBitVec (hostSymAddr h l) := fun l =>
    (Int64.ofBitVec_toBitVec (Labels.label l)).symm
  cases i with
  | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _ | test _ _ _
  | clearFlags | setcc _ _ | canonAbi _ _ | symAddr _ _ => cases hstep
  | load _ _ _ _ | slotLd _ _ | epilogue _ => rcases hstep with ⟨_, _, hEq⟩; cases hEq
  | store _ _ _ | slotSt _ _ | prologue _ => rcases hstep with ⟨_, hEq⟩; cases hEq
  | jmp l | exitJmp l =>
    cases hstep
    refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
    simp only [t_step_simp, hLabEq l]
    exact hcont sm hrel (Machine.Frame.refl (M := armMach) armCondReads sm _ [] _)
  | jcc c l =>
    dsimp only [instrRel] at hstep
    cases hev : c.interp sv.flags with
    | false => simp [hev] at hstep
    | true =>
      simp only [hev, ↓reduceIte, InstrOut.jump.injEq] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
      simp only [t_step_simp, hrel.2.1, hev, ↓reduceIte, hLabEq l]
      exact hcont sm hrel (Machine.Frame.refl (M := armMach) armCondReads sm _ [] _)
  | jnzGpr r l =>
    dsimp only [instrRel] at hstep
    cases hnz : ((sv.gpr r).setWidth 8 != 0#8) with
    | false => simp [hnz] at hstep
    | true =>
      simp only [hnz, ↓reduceIte, InstrOut.jump.injEq] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      have hr : r ∉ armScratch := huses r List.mem_cons_self
      have hrEq : Arm64.get sm r = sv.gpr r := hrel.1 r hr
      have hnz32 : (((sv.gpr r).setWidth 8).setWidth 32 != (0 : BitVec 32)) = true := by
        simp only [bne_iff_ne, ne_eq] at hnz ⊢
        intro h0
        have := congrArg (BitVec.setWidth 8) h0
        rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
        exact hnz this
      have hbr : ∀ {k' : Nat} {s1 : MachineData},
          Host.prog[k']? = some (ins (.CBNZ (zr .X16 .W32) (.label l))) →
          Arm64.get s1 (.reg .X16) = ((sv.gpr r).setWidth 8).setWidth 64 →
          arm64StateRel sv s1 →
          armMach.Frame armCondReads sm s1 armScratch [] maskNone →
          Eventually (step1 Host.exe) post ⟨s1, Host.addrOf k'⟩ := by
        intro k' s1 hk' hx16 hrel1 hfr1
        refine Host.eventually_of_interp_cps hk' ?_
        simp only [t_step_simp, RegWidth.bits, MemWidth.bits, ← get_reg, hx16,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), hnz32, ↓reduceIte, hLabEq l]
        exact hcont s1 hrel1 hfr1
      have hubfm : ∀ (x : XReg) (s1 : MachineData), Arm64.get s1 (.reg x) = sv.gpr r →
          _root_.Program.wp [ins (.UBFM (zr .X16 .W32) (zr x .W32) 0 7)]
            (fun s' => s' = wr s1 .X16 (((sv.gpr r).setWidth 8).setWidth 64))
            (fun _ _ => False) s1 := fun x s1 hEqx =>
        armDirFallsTo_wp fun {_} _ _ _ _ hk => by
          simp only [t_step_simp, RegWidth.bits, MemWidth.bits, ← get_reg, hEqx]
          rw [evalUBFM_low (w := .W32) (n := 8) _ (by decide) (by decide),
            BitVec.setWidth_setWidth_of_le (sv.gpr r) (by decide : 8 ≤ 32),
            setWidth_64_32_sub (by decide : 8 ≤ 32)]
          exact hk _ rfl
      cases r with
      | reg x =>
        dsimp only [asmArm64, asmJnzGprIns, emitClean_cons, emitClean_nil] at hc
        obtain ⟨h1, h2⟩ := List.IsInfixAt.append (a := [ins (.UBFM (zr .X16 .W32) (zr x .W32) 0 7)])
          hc
        refine eventually_trans _ _ _ _ (hubfm x sm hrEq k h1) ?_
        rintro ⟨s₁, a⟩ (⟨ha, rfl⟩ | hf)
        · dsimp only at ha; subst ha
          exact hbr (List.isInfixAt_singleton.mp h2) (get_wr_same _ _ _)
            ⟨fun q hsc => (get_wr_of_ne _ _ _ q (ne_of_not_mem_armScratch hsc).1).trans
              (hrel.1 q hsc), hrel.2.1, hrel.2.2⟩
            (frame_wr .X16 _ List.mem_cons_self maskNone)
        · exact False.elim hf
      | SP =>
        dsimp only [asmArm64, asmJnzGprIns, emitClean_cons, emitClean_nil] at hc
        obtain ⟨h1, h23⟩ := List.IsInfixAt.append (a := [armMovToX .X16 .SP]) hc
        obtain ⟨h2, h3⟩ := List.IsInfixAt.append
          (a := [ins (.UBFM (zr .X16 .W32) (zr .X16 .W32) 0 7)]) h23
        refine eventually_trans _ _ _ _ (armMovToX_wp .X16 .SP sm k h1) ?_
        rintro ⟨s₁, a₁⟩ (⟨ha₁, rfl⟩ | hf)
        · dsimp only at ha₁; subst ha₁
          refine eventually_trans _ _ _ _ (hubfm .X16 _ (by rw [get_wr_same, hrEq]) (k + 1) h2) ?_
          rintro ⟨s₂, a₂⟩ (⟨ha₂, rfl⟩ | hf)
          · dsimp only at ha₂; subst ha₂
            exact hbr (List.isInfixAt_singleton.mp h3) (get_wr_same _ _ _)
              ⟨fun q hsc => by
                have h16 := (ne_of_not_mem_armScratch hsc).1
                rw [get_wr_of_ne _ _ _ q h16, get_wr_of_ne _ _ _ q h16]; exact hrel.1 q hsc,
                hrel.2.1, hrel.2.2⟩
              (armFrame_status_eq (fun q hsc => by
                have h16 := (ne_of_not_mem_armScratch hsc).1
                rw [get_wr_of_ne _ _ _ q h16, get_wr_of_ne _ _ _ q h16]) rfl)
          · exact False.elim hf
        · exact False.elim hf
  | call sym =>
    cases hstep
    refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
    simp only [t_step_simp, Reg64s.setRegOrZr_reg64, hLabEq sym]
    rw [show BitVec.ofInt 64 (Host.addrOf (k + 1)).toInt = (Host.addrOf (k + 1)).toBitVec by
      rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]]
    refine hcont (wr sm .X30 (Host.addrOf (k + 1)).toBitVec) ?_ ?_
    · refine ⟨fun r hsc => ?_, hrel.2.1, hrel.2.2⟩
      by_cases h30 : r = .reg .X30
      · subst h30; simp [asmArm64, emitClean]
      · rw [get_wr_of_ne _ _ _ r h30, hrel.1 r hsc, MachSt.gpr_setGpr_ne _ _ h30]
    · exact frame_wr .X30 _
        (by simp [Instr.clobGpr, Instr.defs, Abi.raRegs, RaKind.raRegs]) maskNone
  | icall r =>
    cases hstep
    have hr : r ∉ armScratch := huses r List.mem_cons_self
    have hrEq : Arm64.get sm r = sv.gpr r := hrel.1 r hr
    cases r with
    | reg x =>
      refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
      simp only [t_step_simp, Reg64s.setRegOrZr_reg64, getRegOrZr_zr, RegWidth.bits,
        BitVec.setWidth_eq, ← get_reg, hrEq]
      have hra : BitVec.ofInt 64 (Host.addrOf (k + 1)).toInt = (Host.addrOf (k + 1)).toBitVec := by
        rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
      have hpc : Int64.ofInt (sv.gpr (.reg x)).signed = Int64.ofBitVec (sv.gpr (.reg x)) := by
        rw [← Int64.toBitVec_ofBitVec (sv.gpr (.reg x))]; simp [BitVec.signed]
      rw [hra, hpc]
      refine hcont (wr sm .X30 (Host.addrOf (k + 1)).toBitVec) ?_ ?_
      · refine ⟨fun q hsc => ?_, hrel.2.1, hrel.2.2⟩
        by_cases h30 : q = .reg .X30
        · subst h30; simp [asmArm64, armCallReg, armCallRegIns, emitClean]
        · rw [get_wr_of_ne _ _ _ q h30, hrel.1 q hsc, MachSt.gpr_setGpr_ne _ _ h30]
      · exact frame_wr .X30 _ (by simp [Instr.clobGpr, Instr.defs, Abi.raRegs, RaKind.raRegs])
          maskNone
    | SP =>
      dsimp only [asmArm64] at hc
      obtain ⟨h1, h2⟩ := List.IsInfixAt.append (a := [armMovToX .X16 .SP]) hc
      refine eventually_trans _ _ _ _ (armMovToX_wp .X16 .SP sm k h1) ?_
      rintro ⟨s₁, a₁⟩ (⟨ha₁, rfl⟩ | hf)
      · dsimp only at ha₁; subst ha₁
        refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp h2) ?_
        simp only [t_step_simp, Reg64s.setRegOrZr_reg64, getRegOrZr_zr, RegWidth.bits,
          BitVec.setWidth_eq, List.length_singleton, Reg64s.getXReg_setXReg_same,
          UInt64.toBitVec_ofBitVec, hrEq]
        have hra : BitVec.ofInt 64 (Host.addrOf (k + 1 + 1)).toInt =
            (Host.addrOf (k + 2)).toBitVec := by
          rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
        have hpc : Int64.ofInt (sv.gpr .SP).signed = Int64.ofBitVec (sv.gpr .SP) := by
          rw [← Int64.toBitVec_ofBitVec (sv.gpr .SP)]; simp [BitVec.signed]
        rw [hra, hpc]
        refine hcont (wr (wr sm .X16 (sv.gpr .SP)) .X30 (Host.addrOf (k + 2)).toBitVec) ?_ ?_
        · refine ⟨fun q hsc => ?_, hrel.2.1, hrel.2.2⟩
          by_cases h30 : q = .reg .X30
          · subst h30; simp [asmArm64]
          · rw [get_wr_of_ne _ _ _ q h30, get_wr_of_ne _ _ _ q (ne_of_not_mem_armScratch hsc).1,
              hrel.1 q hsc, MachSt.gpr_setGpr_ne _ _ h30]
        · refine armFrame_status_eq (fun q hq => ?_) rfl
          have h30 : q ≠ .reg .X30 := fun e => hq (by
            simp [e, Instr.clobGpr, Instr.defs, Abi.raRegs, RaKind.raRegs])
          have h16 : q ≠ .reg .X16 := fun e => hq (by simp [e, armScratch])
          rw [get_wr_of_ne _ _ _ q h30, get_wr_of_ne _ _ _ q h16]
      · exact False.elim hf
  | ret =>
    cases hstep
    have h30 : Arm64.get sm (.reg .X30) = sv.gpr (.reg .X30) :=
      hrel.1 (.reg .X30) (by simp [armScratch])
    refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
    simp only [t_step_simp, Reg64s.getRegOrZr_reg64, ← get_reg, h30]
    have hpc : Int64.ofInt (sv.gpr (.reg .X30)).signed = Int64.ofBitVec (sv.gpr (.reg .X30)) := by
      rw [← Int64.toBitVec_ofBitVec (sv.gpr (.reg .X30))]; simp [BitVec.signed]
    rw [hpc]
    exact hcont sm hrel (Machine.Frame.refl (M := armMach) armCondReads sm _ [] _)
  | tailJmpR r | ijmp r =>
    cases hstep
    have hr : r ∉ armScratch := huses r List.mem_cons_self
    have hrEq : Arm64.get sm r = sv.gpr r := hrel.1 r hr
    cases r with
    | reg x =>
      refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
      simp only [t_step_simp, getRegOrZr_zr, RegWidth.bits, BitVec.setWidth_eq, ← get_reg, hrEq]
      have hpc : Int64.ofInt (sv.gpr (.reg x)).signed = Int64.ofBitVec (sv.gpr (.reg x)) := by
        rw [← Int64.toBitVec_ofBitVec (sv.gpr (.reg x))]; simp [BitVec.signed]
      rw [hpc]
      exact hcont sm hrel (Machine.Frame.refl (M := armMach) armCondReads sm _ [] _)
    | SP =>
      dsimp only [asmArm64] at hc
      obtain ⟨h1, h2⟩ := List.IsInfixAt.append (a := [armMovToX .X16 .SP]) hc
      refine eventually_trans _ _ _ _ (armMovToX_wp .X16 .SP sm k h1) ?_
      rintro ⟨s₁, a₁⟩ (⟨ha₁, rfl⟩ | hf)
      · dsimp only at ha₁; subst ha₁
        refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp h2) ?_
        simp only [t_step_simp, getRegOrZr_zr, RegWidth.bits, BitVec.setWidth_eq,
          Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, hrEq]
        have hpc : Int64.ofInt (sv.gpr .SP).signed = Int64.ofBitVec (sv.gpr .SP) := by
          rw [← Int64.toBitVec_ofBitVec (sv.gpr .SP)]; simp [BitVec.signed]
        rw [hpc]
        exact hcont (wr sm .X16 (sv.gpr .SP))
          ⟨fun q hsc => (get_wr_of_ne _ _ _ q (ne_of_not_mem_armScratch hsc).1).trans
            (hrel.1 q hsc), hrel.2.1, hrel.2.2⟩
          (frame_wr .X16 _ List.mem_cons_self maskNone)
      · exact False.elim hf
  | native d =>
    rcases hstep with ⟨no, hst, hEq⟩
    cases no with
    | fall _ => cases hEq
    | halt _ => cases hEq
    | jump pc1 s1 =>
      cases hEq
      exact asmNative_jump_run hc huses hrel hst hcont

end LeanQbe.T.Arm64
