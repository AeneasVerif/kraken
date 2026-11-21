module

public import LeanQbe.T.IselStepAttr
public import LeanQbe.T.Amd64.Base

/-!
# Thin SysV x64 `@[scoped isel_step]` Rules & `isel_x64_frame_all` (`Stage 0`)

Core address/move/ALU stepping rules over `LeanQbe.T.Amd64.Base`, registered strictly as
`@[scoped isel_step]` inside `namespace LeanQbe.T.Amd64.IselStep` (zero global `@[` attributes).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

/-! ## 1. Shared x64 `Frame` & `Program.wp` step combinators -/

theorem x64_frame_of_eq {s s' : MachineData} {g : List Reg64} {f : FlagMask}
    (hregs : ∀ r, r ∉ g → s'.regs.get64 r = s.regs.get64 r)
    (hzmms : s'.zmms = s.zmms)
    (hflags : x64Mach.UpdFlags x64CondReads s s' f) :
    x64Mach.Frame x64CondReads s s' g [] f :=
  ⟨hregs, fun vr _ => by simp only [hzmms], hflags⟩

theorem updFlags_maskAll (s s' : MachineData) : x64Mach.UpdFlags x64CondReads s s' maskAll := by
  intro cc h
  cases cc <;>
    simp [x64CondReads, FlagMask.disjoint, maskAll, maskOF, maskCF, maskZF, maskSF, maskPF] at h

theorem updFlags_of_status_eq {s s' : MachineData} (h : s'.status = s.status) (m : FlagMask) :
    x64Mach.UpdFlags x64CondReads s s' m := fun _ _ => by
  simp only [h]

theorem x64_wp_step_dir [Host] {E : Int64 → MachineData → Prop}
    {dir : Directive} {rest : List Directive} {s : MachineData} {P Q : MachineData → Prop}
    (hd : Directive.FallsTo dir s P)
    (hk : ∀ s', P s' → _root_.Program.wp rest Q E s') :
    _root_.Program.wp (dir :: rest) Q E s :=
  Program.wp.cons (Directive.FallsTo.wp hd) hk

theorem x64_wp_step_last [Host] {E : Int64 → MachineData → Prop}
    {dir : Directive} {s : MachineData} {P Q : MachineData → Prop}
    (hd : Directive.FallsTo dir s P)
    (hk : ∀ s', P s' → Q s') :
    _root_.Program.wp [dir] Q E s :=
  Program.wp.mono (Directive.FallsTo.wp hd) hk

/-! ## 2. Scoped `@[isel_step]` Rules (`mov`, `movi`, `movl`, `movzx`, `add`, `sub`, `lea`) -/

namespace IselStep

private theorem fallsTo_mov64 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins (.mov (.reg (q rd)) (.reg (q rs)))) s
      (· = { s with regs := s.regs.set64 rd (s.regs.get64 rs) }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp]; exact hk _ rfl

private theorem fallsTo_movi64 (s : MachineData) (rd : Reg64) (c0 : BitVec 64) :
    Directive.FallsTo (ins (.mov (.reg (q rd)) (.imm (.int64 (Int64.ofBitVec c0))))) s
      (· = { s with regs := s.regs.set64 rd c0 }) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, Int64.toBitVec_ofBitVec, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  exact hk _ rfl

private theorem fallsTo_movl32 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins32 (.mov (.reg (d rd)) (.reg (d rs)))) s
      (· = { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 32).zeroExtend 64) }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp]; exact hk _ rfl

private theorem fallsTo_add64_reg (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins (.add (.reg (q rd)) (.reg (q rs)))) s
      (fun s' => ∃ status,
        s' = { s with regs := s.regs.set64 rd (s.regs.get64 rd + s.regs.get64 rs), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp]; rw [BitVec.add_comm]; exact hk _ ⟨_, rfl⟩

private theorem fallsTo_sub64_reg (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins (.sub (.reg (q rd)) (.reg (q rs)))) s
      (fun s' => ∃ status,
        s' = { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp]; exact hk _ ⟨_, rfl⟩

private theorem fallsTo_lea64 (s : MachineData) (rd : Reg64) (addr : AddrExpr) (a : BitVec 64)
    (ha : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a) :
    Directive.FallsTo (ins (.lea (q rd) addr)) s
      (· = { s with regs := s.regs.set64 rd a }) := by
  intro _ p _ _ _ hk; simp only [t_step_simp, ha p]; exact hk _ rfl

@[scoped isel_step]
theorem x64_step_mov_cons [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {rest : List Directive} {s : MachineData} {Q : MachineData → Prop}
    (hk : _root_.Program.wp rest Q E { s with regs := s.regs.set64 rd (s.regs.get64 rs) }) :
    _root_.Program.wp (ins (.mov (.reg (q rd)) (.reg (q rs))) :: rest) Q E s :=
  x64_wp_step_dir (fallsTo_mov64 s rd rs) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem x64_step_mov_last [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {s : MachineData} {Q : MachineData → Prop}
    (hk : Q { s with regs := s.regs.set64 rd (s.regs.get64 rs) }) :
    _root_.Program.wp [ins (.mov (.reg (q rd)) (.reg (q rs)))] Q E s :=
  x64_wp_step_last (fallsTo_mov64 s rd rs) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem x64_step_movi_cons [Host] {E : Int64 → MachineData → Prop}
    {rd : Reg64} {c0 : BitVec 64} {rest : List Directive} {s : MachineData} {Q : MachineData → Prop}
    (hk : _root_.Program.wp rest Q E { s with regs := s.regs.set64 rd c0 }) :
    _root_.Program.wp
      (ins (.mov (.reg (q rd)) (.imm (.int64 (Int64.ofBitVec c0)))) :: rest) Q E s :=
  x64_wp_step_dir (fallsTo_movi64 s rd c0) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem x64_step_movi_last [Host] {E : Int64 → MachineData → Prop}
    {rd : Reg64} {c0 : BitVec 64} {s : MachineData} {Q : MachineData → Prop}
    (hk : Q { s with regs := s.regs.set64 rd c0 }) :
    _root_.Program.wp
      [ins (.mov (.reg (q rd)) (.imm (.int64 (Int64.ofBitVec c0))))] Q E s :=
  x64_wp_step_last (fallsTo_movi64 s rd c0) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem x64_step_movl_cons [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {rest : List Directive} {s : MachineData} {Q : MachineData → Prop}
    (hk : _root_.Program.wp rest Q E
      { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 32).zeroExtend 64) }) :
    _root_.Program.wp (ins32 (.mov (.reg (d rd)) (.reg (d rs))) :: rest) Q E s :=
  x64_wp_step_dir (fallsTo_movl32 s rd rs) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem x64_step_movl_last [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {s : MachineData} {Q : MachineData → Prop}
    (hk : Q { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 32).zeroExtend 64) }) :
    _root_.Program.wp [ins32 (.mov (.reg (d rd)) (.reg (d rs)))] Q E s :=
  x64_wp_step_last (fallsTo_movl32 s rd rs) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem x64_step_add64_reg_cons [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {rest : List Directive} {s : MachineData} {Q : MachineData → Prop}
    (hk : ∀ (st : StatusFlags),
      _root_.Program.wp rest Q E
        { s with regs := s.regs.set64 rd (s.regs.get64 rd + s.regs.get64 rs), status := st }) :
    _root_.Program.wp (ins (.add (.reg (q rd)) (.reg (q rs))) :: rest) Q E s :=
  x64_wp_step_dir (fallsTo_add64_reg s rd rs) (fun _ ⟨st, heq⟩ => heq ▸ hk st)

@[scoped isel_step]
theorem x64_step_add64_reg_last [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {s : MachineData} {Q : MachineData → Prop}
    (hk : ∀ (st : StatusFlags),
      Q { s with regs := s.regs.set64 rd (s.regs.get64 rd + s.regs.get64 rs), status := st }) :
    _root_.Program.wp [ins (.add (.reg (q rd)) (.reg (q rs)))] Q E s :=
  x64_wp_step_last (fallsTo_add64_reg s rd rs) (fun _ ⟨st, heq⟩ => heq ▸ hk st)

@[scoped isel_step]
theorem x64_step_sub64_reg_cons [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {rest : List Directive} {s : MachineData} {Q : MachineData → Prop}
    (hk : ∀ (st : StatusFlags),
      _root_.Program.wp rest Q E
        { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := st }) :
    _root_.Program.wp (ins (.sub (.reg (q rd)) (.reg (q rs))) :: rest) Q E s :=
  x64_wp_step_dir (fallsTo_sub64_reg s rd rs) (fun _ ⟨st, heq⟩ => heq ▸ hk st)

@[scoped isel_step]
theorem x64_step_sub64_reg_last [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {s : MachineData} {Q : MachineData → Prop}
    (hk : ∀ (st : StatusFlags),
      Q { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := st }) :
    _root_.Program.wp [ins (.sub (.reg (q rd)) (.reg (q rs)))] Q E s :=
  x64_wp_step_last (fallsTo_sub64_reg s rd rs) (fun _ ⟨st, heq⟩ => heq ▸ hk st)

@[scoped isel_step]
theorem x64_step_lea_cons [Host] {E : Int64 → MachineData → Prop}
    {rd : Reg64} {addr : AddrExpr} {a : BitVec 64} {rest : List Directive}
    {s : MachineData} {Q : MachineData → Prop}
    (ha : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hk : _root_.Program.wp rest Q E { s with regs := s.regs.set64 rd a }) :
    _root_.Program.wp (ins (.lea (q rd) addr) :: rest) Q E s :=
  x64_wp_step_dir (fallsTo_lea64 s rd addr a ha) (fun _ h => h ▸ hk)

@[scoped isel_step]
theorem x64_step_lea_last [Host] {E : Int64 → MachineData → Prop}
    {rd : Reg64} {addr : AddrExpr} {a : BitVec 64} {s : MachineData} {Q : MachineData → Prop}
    (ha : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = a)
    (hk : Q { s with regs := s.regs.set64 rd a }) :
    _root_.Program.wp [ins (.lea (q rd) addr)] Q E s :=
  x64_wp_step_last (fallsTo_lea64 s rd addr a ha) (fun _ h => h ▸ hk)

theorem get64_ne_of_not_mem (r : Reg64) (g : List Reg64)
    (h : r ∉ g) (x : Reg64) (hx : x ∈ g) : x ≠ r :=
  fun e => h (e ▸ hx)

/-- Discharge `x64Mach.Frame x64CondReads s s' gClob [] maskAll` goals from `isel_steps`. -/
macro "isel_x64_frame_all" : tactic =>
  `(tactic| (
    refine LeanQbe.T.Amd64.x64_frame_of_eq (fun r hr => ?_) rfl
      (LeanQbe.T.Amd64.updFlags_maskAll _ _)
    dsimp only
    repeat' rw [Reg64s.get64_set64_of_ne _ _ r _
      (LeanQbe.T.Amd64.IselStep.get64_ne_of_not_mem r _ hr _
        (by simp [LeanQbe.T.Amd64.x64Scratch]))]
    all_goals try rfl))

end IselStep

end LeanQbe.T.Amd64
