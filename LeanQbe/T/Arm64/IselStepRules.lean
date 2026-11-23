module

public import LeanQbe.T.IselStepAttr
public import LeanQbe.T.Arm64.Base

/-!
# Thin AArch64 `@[scoped isel_step]` Rules & `isel_arm_frame_sp`

Core address/move/ALU stepping rules over `LeanQbe.T.Arm64.Base`, registered strictly as
`@[scoped isel_step]` inside `namespace LeanQbe.T.Arm64.IselStep` (zero global `@[` attributes).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

/-! ## 1. Shared AArch64 `Frame` helpers -/

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
    cases c <;>
      simp [FlagMask.disjoint, armCondReads, maskAll, maskN, maskZ, maskC, maskV] at hdisj
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

/-! ## 2. Scoped `@[isel_step]` Primitive Rules -/

namespace IselStep

private theorem eval_add_sp_imm64 (s : MachineData) (imm : ConstExpr) (c : Int64)
    (himm : ∀ [Labels] (p : Std.Rco Int64), imm.interp p = c) :
    armDirFallsTo
      (ins (w := .W64) (.ADD_e (.low (.reg .X16) .W64) (.low .SP .W64)
        (.imm { imm := imm, shift := .S0 })))
      s
      (· = wr s .X16 (get s .SP + c.toBitVec)) := by
  intro _ p next jmp P hk
  simp only [t_step_simp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp_sp64, himm p,
    RegWidth.bits]
  rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  exact hk _ rfl

private theorem fallsTo_add_x16_sp_ext (s : MachineData) :
    armDirFallsTo
      (ins (w := .W64) (.ADD_e (.low (.reg .X16) .W64) (.low .SP .W64)
        (.ext { reg := ⟨.W64, zr .X16 .W64⟩, ext := { type := .UXTX, amount := .E0 } })))
      s
      (· = wr s .X16 (get s .SP + get s (.reg .X16))) := by
  intro _ p next jmp P hcont
  simp only [t_step_simp, ExtRegExpr.interp, BitVec.apply_extend,
    Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp_sp64, RegWidth.bits,
    Reg64s.getRegOrZr64, RegOrZr.base, BitVec.unsigned]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  exact hcont _ rfl

private theorem fallsTo_orr (w : RegWidth) (d ra rb : XReg) (s : MachineData) :
    armDirFallsTo (ins (.ORR_s (zr d w) (zr ra w) (sh rb))) s
      (· = wr s d
        ((((s.regs.getXReg ra).toBitVec.setWidth w.bits) |||
          ((s.regs.getXReg rb).toBitVec.setWidth w.bits)).setWidth 64)) := by
  intro _ p next jmp P hcont
  cases w
  · simp only [t_step_simp, sh, Int64.toInt_zero, RegWidth.bits, Int.toNat_zero,
      BitVec.shiftLeft_zero]
    exact hcont _ rfl
  · simp only [t_step_simp, sh, Int64.toInt_zero, RegWidth.bits, Int.toNat_zero,
      BitVec.shiftLeft_zero, BitVec.setWidth_eq]
    exact hcont _ rfl

@[scoped isel_step]
theorem arm_step_ldrPool_cons [Host] {d : XReg} {c : BitVec 64} {rest : List Directive}
    {s : MachineData} {Q : MachineData → Prop}
    (hk : _root_.Program.wp rest Q (fun _ _ => False) (wr s d c)) :
    _root_.Program.wp (armLdrPoolBv d c :: rest) Q (fun _ _ => False) s :=
  armWp_cons (armLdrPoolBv_wp d c s) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem arm_step_ldrPool_last [Host] {d : XReg} {c : BitVec 64}
    {s : MachineData} {Q : MachineData → Prop}
    (hk : Q (wr s d c)) :
    _root_.Program.wp [armLdrPoolBv d c] Q (fun _ _ => False) s :=
  armWp_mono (armLdrPoolBv_wp d c s) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem arm_step_movToX_cons [Host] {d : XReg} {rs : Reg} {rest : List Directive}
    {s : MachineData} {Q : MachineData → Prop}
    (hk : _root_.Program.wp rest Q (fun _ _ => False) (wr s d (get s rs))) :
    _root_.Program.wp (armMovToX d rs :: rest) Q (fun _ _ => False) s :=
  armWp_cons (armMovToX_wp d rs s) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem arm_step_movToX_last [Host] {d : XReg} {rs : Reg}
    {s : MachineData} {Q : MachineData → Prop}
    (hk : Q (wr s d (get s rs))) :
    _root_.Program.wp [armMovToX d rs] Q (fun _ _ => False) s :=
  armWp_mono (armMovToX_wp d rs s) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem arm_step_movToSp_cons [Host] {src : XReg} {rest : List Directive}
    {s : MachineData} {Q : MachineData → Prop}
    (hk : _root_.Program.wp rest Q (fun _ _ => False)
      { s with regs := { s.regs with SP := UInt64.ofBitVec (get s (.reg src)) } }) :
    _root_.Program.wp (armMovToSp src :: rest) Q (fun _ _ => False) s :=
  armWp_cons (armMovToSp_wp src s) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem arm_step_movToSp_last [Host] {src : XReg} {s : MachineData} {Q : MachineData → Prop}
    (hk : Q { s with regs := { s.regs with SP := UInt64.ofBitVec (get s (.reg src)) } }) :
    _root_.Program.wp [armMovToSp src] Q (fun _ _ => False) s :=
  armWp_mono (armMovToSp_wp src s) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem arm_step_add_sp_imm_last [Host] {c : Int64} {s : MachineData} {Q : MachineData → Prop}
    (hk : Q (wr s .X16 (get s .SP + c.toBitVec))) :
    _root_.Program.wp
      [ins (w := .W64) (.ADD_e (.low (.reg .X16) .W64) (.low .SP .W64)
        (.imm { imm := .int64 c, shift := .S0 }))]
      Q (fun _ _ => False) s :=
  armWp_mono (armDirFallsTo_wp (eval_add_sp_imm64 s (.int64 c) c (fun _ => rfl)))
    (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem arm_step_add_x16_sp_ext_last [Host] {s : MachineData} {Q : MachineData → Prop}
    (hk : Q (wr s .X16 (get s .SP + get s (.reg .X16)))) :
    _root_.Program.wp
      [ins (w := .W64) (.ADD_e (.low (.reg .X16) .W64) (.low .SP .W64)
        (.ext { reg := ⟨.W64, zr .X16 .W64⟩, ext := { type := .UXTX, amount := .E0 } }))]
      Q (fun _ _ => False) s :=
  armWp_mono (armDirFallsTo_wp (fallsTo_add_x16_sp_ext s)) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem arm_step_orr_last [Host] {w : RegWidth} {d ra rb : XReg}
    {s : MachineData} {Q : MachineData → Prop}
    (hk : Q (wr s d
      ((((s.regs.getXReg ra).toBitVec.setWidth w.bits) |||
        ((s.regs.getXReg rb).toBitVec.setWidth w.bits)).setWidth 64))) :
    _root_.Program.wp [ins (.ORR_s (zr d w) (zr ra w) (sh rb))] Q (fun _ _ => False) s :=
  armWp_mono (armDirFallsTo_wp (fallsTo_orr w d ra rb s)) (fun _ h => h ▸ hk)

private theorem getXReg_with_SP (r : Reg64s) (v : UInt64) (xr : XReg) :
    ({ r with SP := v }).getXReg xr = r.getXReg xr := by
  cases xr <;> rfl

/-- Discharge `armMach.Frame armCondReads s s' (.SP :: armScratch) [] FlagMask.none`. -/
macro "isel_arm_frame_sp" : tactic =>
  `(tactic| (
    refine LeanQbe.T.Arm64.armFrame_status_eq (fun r hr => ?_) rfl
    simp only [List.mem_cons, LeanQbe.T.Arm64.armScratch, List.not_mem_nil, or_false, not_or]
      at hr
    cases r with
    | SP => exact absurd rfl hr.1
    | reg xr =>
      have hx : XReg.X16 ≠ xr := fun e => hr.2.1 (congrArg XRegOrSp.reg e.symm)
      simp only [LeanQbe.T.Arm64.get_reg, LeanQbe.T.Arm64.wr, getXReg_with_SP]
      exact congrArg UInt64.toBitVec (Reg64s.getXReg_setXReg_of_ne _ .X16 xr _ hx)))

end IselStep

end LeanQbe.T.Arm64
