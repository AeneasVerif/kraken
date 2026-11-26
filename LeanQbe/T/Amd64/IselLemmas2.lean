module

public import LeanQbe.T.Amd64.IselLemmas1

/-!
# x64 Scalar `GprTarget` Proofs — Part 2

Single-directive `Directive.FallsTo` lemmas for scalar ALU, `lea`, `inc`/`dec`, `neg`, `not`,
`cmp`, `movzx`/`movsx`, `rolw $8`, and `bswap`, plus `AllInstr` and `op_spec` proofs for:
`copy`, `bool` logic (`and`/`or`/`xor`/`not`), `ofBool`, `zext`, `sext`, `trunc`, `bswap`,
`neg`, `not`, and binary ALU (`add`/`sub`/`mul`/`and`/`or`/`xor`, `.disp`, `.decInc`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

open LeanQbe.T

/-! ## 1. Single-Directive `Directive.FallsTo` Lemmas (Part 2) -/

theorem fallsTo_movzx8 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins32 (.movzx (.reg (d rd)) (.reg (b8 rs)))) s
      (· = { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 8).setWidth 64) }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, BitVec.zeroExtend_eq_setWidth]
  rw [setWidth_32_64 (by decide)]; exact hk _ rfl

theorem fallsTo_movzx16 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins32 (.movzx (.reg (d rd)) (.reg (h16 rs)))) s
      (· = { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 16).setWidth 64) }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, BitVec.zeroExtend_eq_setWidth]
  rw [setWidth_32_64 (by decide)]; exact hk _ rfl

theorem fallsTo_movsx8 (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (insW w (.movsx (.reg (regW w rd)) (.reg (b8 rs)))) s
      (· = { s with regs :=
        s.regs.set64 rd ((((s.regs.get64 rs).setWidth 8).signExtend w.bits).setWidth 64) }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set, BitVec.zeroExtend_eq_setWidth, Width.bits]
    exact hk _ rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set, Width.bits]
    exact hk _ rfl

theorem fallsTo_movsx16 (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (insW w (.movsx (.reg (regW w rd)) (.reg (h16 rs)))) s
      (· = { s with regs :=
        s.regs.set64 rd ((((s.regs.get64 rs).setWidth 16).signExtend w.bits).setWidth 64) }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set, BitVec.zeroExtend_eq_setWidth, Width.bits]
    exact hk _ rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set, Width.bits]
    exact hk _ rfl

theorem fallsTo_movsx32 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins (.movsx (.reg (q rd)) (.reg (d rs)))) s
      (· = { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 32).signExtend 64) }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp]; exact hk _ rfl

theorem fallsTo_and8 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins8 (.and (.reg (b8 rd)) (.reg (b8 rs)))) s (fun s' =>
      ∃ status, status.zf =
          decide (((s.regs.get64 rd).setWidth 8 &&& (s.regs.get64 rs).setWidth 8) = 0#8) ∧
        s' = { s with regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow
          ((s.regs.get64 rd).setWidth 8 &&& (s.regs.get64 rs).setWidth 8)), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, Reg64s.set, Effects.All, StatusFlags.from_result]
  intro _; exact hk _ ⟨_, rfl, rfl⟩

theorem fallsTo_or8 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins8 (.or (.reg (b8 rd)) (.reg (b8 rs)))) s (fun s' =>
      ∃ status, status.zf =
          decide (((s.regs.get64 rd).setWidth 8 ||| (s.regs.get64 rs).setWidth 8) = 0#8) ∧
        s' = { s with regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow
          ((s.regs.get64 rd).setWidth 8 ||| (s.regs.get64 rs).setWidth 8)), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, Reg64s.set, Effects.All, StatusFlags.from_result]
  intro _; exact hk _ ⟨_, rfl, rfl⟩

theorem fallsTo_xor8 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins8 (.xor (.reg (b8 rd)) (.reg (b8 rs)))) s (fun s' =>
      ∃ status, status.zf =
          decide (((s.regs.get64 rd).setWidth 8 ^^^ (s.regs.get64 rs).setWidth 8) = 0#8) ∧
        s' = { s with regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow
          ((s.regs.get64 rd).setWidth 8 ^^^ (s.regs.get64 rs).setWidth 8)), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, Reg64s.set, Effects.All, StatusFlags.from_result]
  intro _; exact hk _ ⟨_, rfl, rfl⟩

theorem fallsTo_xor8_one (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (ins8 (.xor (.reg (b8 rd)) (.imm (.int64 1)))) s (fun s' =>
      ∃ status, status.zf = decide (((s.regs.get64 rd).setWidth 8 ^^^ 1#8) = 0#8) ∧
        s' = { s with regs := (s.regs.set64 rd
          ((s.regs.get64 rd).replaceLow ((s.regs.get64 rd).setWidth 8 ^^^ 1#8))), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, Reg64s.set, Effects.All, StatusFlags.from_result]
  intro _; exact hk _ ⟨_, rfl, rfl⟩

private theorem exists_setRegW_z (w : Width) (s : MachineData) (rd : Reg64) (v : w.type)
    (st : StatusFlags) :
    ∃ rv status, rv.setWidth w.bits = v ∧ (w = .W32 → rv = v.setWidth 64) ∧
      ({ s with regs := s.regs.set (regW w rd) v, status := st } : MachineData) =
        { s with regs := s.regs.set64 rd rv, status } := by
  cases w <;> simp only [regW, Reg64s.set]
  · exact ⟨_, st, replaceLow_setWidth_le (by decide) _ _, (fun h => by cases h), rfl⟩
  · exact ⟨_, st, replaceLow_setWidth_le (by decide) _ _, (fun h => by cases h), rfl⟩
  · exact ⟨_, st, by simp [Width.bits], (fun _ => by simp), rfl⟩
  · exact ⟨_, st, rfl, (fun h => by cases h), rfl⟩

theorem exists_setRegW_state (w : Width) (s : MachineData) (rd : Reg64) (v : w.type)
    (st : StatusFlags) :
    ∃ rv status, rv.setWidth w.bits = v ∧
      ({ s with regs := s.regs.set (regW w rd) v, status := st } : MachineData) =
        { s with regs := s.regs.set64 rd rv, status } :=
  let ⟨rv, st, h1, _, h2⟩ := exists_setRegW_z w s rd v st
  ⟨rv, st, h1, h2⟩

def AluFlagOk (k : AluBinKind) (w : Width) (rv : BitVec w.bits) (st : StatusFlags) : Prop :=
  match k with
  | .add | .sub => st.zf = decide (rv = 0#w.bits)
  | .and | .or | .xor => ∃ af, st = testFlags rv rv af
  | .mul => True

theorem fallsTo_negW_z (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.neg (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = -((s.regs.get64 rd).setWidth w.bits) ∧
        (w = .W32 → rv = (-((s.regs.get64 rd).setWidth w.bits)).setWidth 64) ∧
        status.zf = decide (-((s.regs.get64 rd).setWidth w.bits) = 0#w.bits) ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, regW, t_step_simp, Reg64s.set, StatusFlags.from_result] <;>
    refine hk _ ⟨_, _, ?_, ?_, rfl, rfl⟩
  · exact replaceLow_setWidth_le (by decide) _ _
  · exact fun h => by cases h
  · exact replaceLow_setWidth_le (by decide) _ _
  · exact fun h => by cases h
  · simp [Width.bits]
  · exact fun _ => by simp [Width.bits]
  · rfl
  · exact fun h => by cases h

theorem fallsTo_negW (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.neg (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = -((s.regs.get64 rd).setWidth w.bits) ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  exact fallsTo_negW_z w s rd _ _ _ _ fun s' ⟨rv, st, h1, _, _, h2⟩ => hk s' ⟨rv, st, h1, h2⟩

private theorem fallsTo_notW_z (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.not (.reg (regW w rd)))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = ~~~((s.regs.get64 rd).setWidth w.bits) ∧
        (w = .W32 → rv = (~~~((s.regs.get64 rd).setWidth w.bits)).setWidth 64) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, regW, t_step_simp, Reg64s.set]
  · exact hk _ ⟨_, replaceLow_setWidth_le (by decide) _ _, (fun h => by cases h), rfl⟩
  · exact hk _ ⟨_, replaceLow_setWidth_le (by decide) _ _, (fun h => by cases h), rfl⟩
  · exact hk _ ⟨_, by simp [Width.bits], (fun _ => by simp), rfl⟩
  · exact hk _ ⟨_, rfl, (fun h => by cases h), rfl⟩

theorem fallsTo_notW (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.not (.reg (regW w rd)))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = ~~~((s.regs.get64 rd).setWidth w.bits) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hk
  exact fallsTo_notW_z w s rd _ _ _ _ fun s' ⟨rv, h1, _, h2⟩ => hk s' ⟨rv, h1, h2⟩

theorem fallsTo_incW_z (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.inc (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = (s.regs.get64 rd).setWidth w.bits + 1#w.bits ∧
        (w = .W32 → rv = ((s.regs.get64 rd).setWidth w.bits + 1#w.bits).setWidth 64) ∧
        status.zf = decide ((s.regs.get64 rd).setWidth w.bits + 1#w.bits = 0#w.bits) ∧
        status.cf = s.status.cf ∧ s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, regW, t_step_simp, Reg64s.set, StatusFlags.from_result] <;>
    refine hk _ ⟨_, _, ?_, ?_, ?_, ?_, rfl⟩
  · rw [replaceLow_setWidth_le (by decide)]; rfl
  · exact fun h => by cases h
  · rfl
  · rfl
  · rw [replaceLow_setWidth_le (by decide)]; rfl
  · exact fun h => by cases h
  · rfl
  · rfl
  · simp [Width.bits]
  · exact fun _ => by simp [Width.bits]
  · rfl
  · rfl
  · rfl
  · exact fun h => by cases h
  · rfl
  · rfl

theorem fallsTo_incW (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.inc (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = (s.regs.get64 rd).setWidth w.bits + 1#w.bits ∧
        status.cf = s.status.cf ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  exact fallsTo_incW_z w s rd _ _ _ _ fun s' ⟨rv, st, h1, _, _, hcf, h2⟩ =>
    hk s' ⟨rv, st, h1, hcf, h2⟩

theorem fallsTo_decW_z (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.dec (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = (s.regs.get64 rd).setWidth w.bits - 1#w.bits ∧
        (w = .W32 → rv = ((s.regs.get64 rd).setWidth w.bits - 1#w.bits).setWidth 64) ∧
        status.zf = decide ((s.regs.get64 rd).setWidth w.bits - 1#w.bits = 0#w.bits) ∧
        status.cf = s.status.cf ∧ s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, regW, t_step_simp, Reg64s.set, StatusFlags.from_result] <;>
    refine hk _ ⟨_, _, ?_, ?_, ?_, ?_, rfl⟩
  · rw [replaceLow_setWidth_le (by decide)]; rfl
  · exact fun h => by cases h
  · rfl
  · rfl
  · rw [replaceLow_setWidth_le (by decide)]; rfl
  · exact fun h => by cases h
  · rfl
  · rfl
  · simp [Width.bits]
  · exact fun _ => by simp [Width.bits]
  · rfl
  · rfl
  · rfl
  · exact fun h => by cases h
  · rfl
  · rfl

theorem fallsTo_decW (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.dec (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = (s.regs.get64 rd).setWidth w.bits - 1#w.bits ∧
        status.cf = s.status.cf ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  exact fallsTo_decW_z w s rd _ _ _ _ fun s' ⟨rv, st, h1, _, _, hcf, h2⟩ =>
    hk s' ⟨rv, st, h1, hcf, h2⟩

theorem fallsTo_leaDisp_z (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rb : Reg64) (off : Int64) :
    Directive.FallsTo (insW w (.lea (regW w rd) (atDisp rb off))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = (s.regs.get64 rb).setWidth w.bits + off.toBitVec.setWidth w.bits ∧
        (w = .W32 → rv = ((s.regs.get64 rb).setWidth w.bits +
          off.toBitVec.setWidth w.bits).setWidth 64) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ p _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set]
    have hdisp := atDisp_interp s.regs rb off p
    have h32 : (@AddrExpr.interp _ ⟨.W64⟩ (atDisp rb off) s.regs p).zeroExtend 32 =
        (s.regs.get64 rb).setWidth 32 + off.toBitVec.setWidth 32 := by
      rw [BitVec.zeroExtend_eq_setWidth]
      have : ((@AddrExpr.interp _ ⟨.W64⟩ (atDisp rb off) s.regs p).zeroExtend 64).setWidth 32 =
          (@AddrExpr.interp _ ⟨.W64⟩ (atDisp rb off) s.regs p).setWidth 32 := by
        rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide)]
      rw [← this, hdisp, setWidth_add_le (by decide)]
    rw [h32]
    exact hk _ ⟨_, by simp [Width.bits], (fun _ => by simp), rfl⟩
  · simp only [insW, regW, t_step_simp, Reg64s.set, atDisp_interp]
    exact hk _ ⟨_, by simp [Width.bits, BitVec.setWidth_eq], (fun h => by cases h), rfl⟩

theorem fallsTo_leaDisp (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rb : Reg64) (off : Int64) :
    Directive.FallsTo (insW w (.lea (regW w rd) (atDisp rb off))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = (s.regs.get64 rb).setWidth w.bits + off.toBitVec.setWidth w.bits ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hk
  exact fallsTo_leaDisp_z w hw s rd rb off _ _ _ _ fun s' ⟨rv, h1, _, h2⟩ => hk s' ⟨rv, h1, h2⟩

theorem fallsTo_leaSIB_z (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rb ri : Reg64) :
    Directive.FallsTo (insW w (.lea (regW w rd) (atSIB rb ri .s1 0))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits =
          (s.regs.get64 rb).setWidth w.bits + (s.regs.get64 ri).setWidth w.bits ∧
        (w = .W32 → rv = ((s.regs.get64 rb).setWidth w.bits +
          (s.regs.get64 ri).setWidth w.bits).setWidth 64) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ p _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set]
    have hsib := atSIB_interp s.regs rb ri .s1 0 p
    have hz : ((0 : Int64).toBitVec) = 0#64 := rfl
    simp only [AddrScale.shift, BitVec.shiftLeft_zero, hz, BitVec.add_zero] at hsib
    have h32 : (@AddrExpr.interp _ ⟨.W64⟩ (atSIB rb ri .s1 0) s.regs p).zeroExtend 32 =
        (s.regs.get64 rb).setWidth 32 + (s.regs.get64 ri).setWidth 32 := by
      rw [BitVec.zeroExtend_eq_setWidth]
      have : ((@AddrExpr.interp _ ⟨.W64⟩ (atSIB rb ri .s1 0) s.regs p).zeroExtend 64).setWidth 32 =
          (@AddrExpr.interp _ ⟨.W64⟩ (atSIB rb ri .s1 0) s.regs p).setWidth 32 := by
        rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide)]
      rw [← this, hsib, setWidth_add_le (by decide)]
    rw [h32]
    exact hk _ ⟨_, by simp [Width.bits], (fun _ => by simp), rfl⟩
  · simp only [insW, regW, t_step_simp, Reg64s.set, atSIB_interp, AddrScale.shift,
      BitVec.shiftLeft_zero]
    exact hk _ ⟨_, by simp [Width.bits, BitVec.setWidth_eq], (fun h => by cases h), rfl⟩

theorem fallsTo_leaSIB (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rb ri : Reg64) :
    Directive.FallsTo (insW w (.lea (regW w rd) (atSIB rb ri .s1 0))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits =
          (s.regs.get64 rb).setWidth w.bits + (s.regs.get64 ri).setWidth w.bits ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hk
  exact fallsTo_leaSIB_z w hw s rd rb ri _ _ _ _ fun s' ⟨rv, h1, _, h2⟩ => hk s' ⟨rv, h1, h2⟩

private theorem setWidth_shiftLeft_32 (v : BitVec 64) (sc : AddrScale) :
    (v <<< sc.shift).setWidth 32 = (v.setWidth 32) <<< sc.shift := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : i < 64 := by omega
  cases sc <;> simp [AddrScale.shift, hi, hi64]
  all_goals (by_cases h : i < 1 <;> simp [h] <;> try omega)

theorem fallsTo_leaSIB_disp_z (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rb ri : Reg64) (sc : AddrScale) (off : Int64) :
    Directive.FallsTo (insW w (.lea (regW w rd) (atSIB rb ri sc off))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits =
          (s.regs.get64 rb).setWidth w.bits +
            ((s.regs.get64 ri).setWidth w.bits <<< sc.shift) + off.toBitVec.setWidth w.bits ∧
        (w = .W32 → rv = ((s.regs.get64 rb).setWidth w.bits +
          ((s.regs.get64 ri).setWidth w.bits <<< sc.shift) +
          off.toBitVec.setWidth w.bits).setWidth 64) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ p _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set]
    have hsib := atSIB_interp s.regs rb ri sc off p
    have h32 : (@AddrExpr.interp _ ⟨.W64⟩ (atSIB rb ri sc off) s.regs p).zeroExtend 32 =
        (s.regs.get64 rb).setWidth 32 + ((s.regs.get64 ri).setWidth 32 <<< sc.shift) +
          off.toBitVec.setWidth 32 := by
      rw [BitVec.zeroExtend_eq_setWidth]
      have : ((@AddrExpr.interp _ ⟨.W64⟩ (atSIB rb ri sc off) s.regs p).zeroExtend 64).setWidth
          32 = (@AddrExpr.interp _ ⟨.W64⟩ (atSIB rb ri sc off) s.regs p).setWidth 32 := by
        rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide)]
      rw [← this, hsib, setWidth_add_le (by decide), setWidth_add_le (by decide),
        setWidth_shiftLeft_32]
    rw [h32]
    exact hk _ ⟨_, by simp [Width.bits], (fun _ => by simp), rfl⟩
  · simp only [insW, regW, t_step_simp, Reg64s.set, atSIB_interp]
    exact hk _ ⟨_, by simp [Width.bits, BitVec.setWidth_eq], (fun h => by cases h), rfl⟩

theorem fallsTo_leaIdx_z (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd ri : Reg64) (sc : AddrScale) (off : Int64) :
    Directive.FallsTo (insW w (.lea (regW w rd) (atIdx ri sc off))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits =
          ((s.regs.get64 ri).setWidth w.bits <<< sc.shift) + off.toBitVec.setWidth w.bits ∧
        (w = .W32 → rv = (((s.regs.get64 ri).setWidth w.bits <<< sc.shift) +
          off.toBitVec.setWidth w.bits).setWidth 64) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ p _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set]
    have hidx := atIdx_interp s.regs ri sc off p
    have h32 : (@AddrExpr.interp _ ⟨.W64⟩ (atIdx ri sc off) s.regs p).zeroExtend 32 =
        ((s.regs.get64 ri).setWidth 32 <<< sc.shift) + off.toBitVec.setWidth 32 := by
      rw [BitVec.zeroExtend_eq_setWidth]
      have : ((@AddrExpr.interp _ ⟨.W64⟩ (atIdx ri sc off) s.regs p).zeroExtend 64).setWidth 32 =
          (@AddrExpr.interp _ ⟨.W64⟩ (atIdx ri sc off) s.regs p).setWidth 32 := by
        rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide)]
      rw [← this, hidx, setWidth_add_le (by decide), setWidth_shiftLeft_32]
    rw [h32]
    exact hk _ ⟨_, by simp [Width.bits], (fun _ => by simp), rfl⟩
  · simp only [insW, regW, t_step_simp, Reg64s.set, atIdx_interp]
    exact hk _ ⟨_, by simp [Width.bits, BitVec.setWidth_eq], (fun h => by cases h), rfl⟩

local macro "close_alu_z" : tactic => `(tactic|
  (refine ⟨_, _, ?_, ?_, ?_, rfl⟩
   · first | (rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide),
               BitVec.setWidth_eq]; done)
           | exact BitVec.setWidth_eq _
           | exact replaceLow_setWidth_le (by decide) _ _
   · exact fun h => by (cases h <;> exact BitVec.zeroExtend_eq_setWidth)
   · simp only [AluFlagOk, AluBinKind.eval, Width.bits, testFlags, BitVec.and_self]
     try (first | rfl | exact ⟨by assumption, rfl⟩ | exact ⟨_, rfl⟩ | trivial)))

theorem fallsTo_aluBinIns_reg_z (w : Width) (k : AluBinKind) (s : MachineData)
    (rd rs : Reg64) :
    Directive.FallsTo (aluBinIns w k rd (.reg (regW w rs))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = k.eval ((s.regs.get64 rd).setWidth w.bits)
        ((s.regs.get64 rs).setWidth w.bits) ∧
        (w = .W32 → rv = (k.eval ((s.regs.get64 rd).setWidth w.bits)
          ((s.regs.get64 rs).setWidth w.bits)).setWidth 64) ∧
        AluFlagOk k w (k.eval ((s.regs.get64 rd).setWidth w.bits)
          ((s.regs.get64 rs).setWidth w.bits)) status ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  cases k with
  | add =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp] <;>
      refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals rw [BitVec.add_comm]; close_alu_z
  | sub =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp] <;>
      refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals close_alu_z
  | and =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals close_alu_z
  | or =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals close_alu_z
  | xor =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals close_alu_z
  | mul =>
    cases w with
    | W8 =>
      simp only [aluBinIns, regW, t_step_simp, Reg.base, Effects.All]
      intro _ _ _ _; refine hk _ ⟨_, _, ?_, (fun h => by cases h), trivial, rfl⟩
      rw [BitVec.zeroExtend_eq_setWidth, Width.bits, BitVec.setWidth_setWidth_of_le _ (by decide),
        setWidth_mul_le (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_setWidth_of_le _ (by decide), AluBinKind.eval, BitVec.mul_comm]
    | W16 | W32 | W64 =>
      simp only [aluBinIns, regW, t_step_simp, Effects.All]
      intro _ _ _ _; refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits, BitVec.mul_comm] <;>
        close_alu_z

theorem fallsTo_aluBinIns_reg (w : Width) (k : AluBinKind) (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (aluBinIns w k rd (.reg (regW w rs))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = k.eval ((s.regs.get64 rd).setWidth w.bits)
        ((s.regs.get64 rs).setWidth w.bits) ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  exact fallsTo_aluBinIns_reg_z w k s rd rs _ _ _ _ fun s' ⟨rv, st, h1, _, _, h2⟩ =>
    hk s' ⟨rv, st, h1, h2⟩

theorem fallsTo_aluBinIns_imm_z (w : Width) (k : AluBinKind) (s : MachineData) (rd : Reg64)
    (cb : BitVec w.bits) :
    Directive.FallsTo (aluBinIns w k rd (immBitsOp w cb)) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = k.eval ((s.regs.get64 rd).setWidth w.bits) cb ∧
        (w = .W32 → rv = (k.eval ((s.regs.get64 rd).setWidth w.bits) cb).setWidth 64) ∧
        AluFlagOk k w (k.eval ((s.regs.get64 rd).setWidth w.bits) cb) status ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  have h8 : ∀ x : BitVec 8,
      BitVec.truncate 8 (Int64.ofBitVec (BitVec.signExtend 64 x)).toBitVec = x :=
    fun x => by rw [Int64.toBitVec_ofBitVec]; exact truncate_signExtend_64 (by decide) x
  have h16 : ∀ x : BitVec 16,
      BitVec.truncate 16 (Int64.ofBitVec (BitVec.signExtend 64 x)).toBitVec = x :=
    fun x => by rw [Int64.toBitVec_ofBitVec]; exact truncate_signExtend_64 (by decide) x
  have h32 : ∀ x : BitVec 32,
      BitVec.truncate 32 (Int64.ofBitVec (BitVec.signExtend 64 x)).toBitVec = x :=
    fun x => by rw [Int64.toBitVec_ofBitVec]; exact truncate_signExtend_64 (by decide) x
  have h64 : ∀ x : BitVec 64,
      BitVec.truncate 64 (Int64.ofBitVec (BitVec.signExtend 64 x)).toBitVec = x :=
    fun x => by rw [Int64.toBitVec_ofBitVec]; exact truncate_signExtend_64 (by decide) x
  cases k with
  | add =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp] <;>
      refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); rw [BitVec.add_comm]
    all_goals close_alu_z
  | sub =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp] <;>
      refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); close_alu_z
  | and =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); close_alu_z
  | or =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); close_alu_z
  | xor =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); close_alu_z
  | mul =>
    cases w with
    | W8 =>
      simp only [aluBinIns, immBitsOp, t_step_simp, Int64.toBitVec_ofBitVec, Effects.All]
      intro _ _ _ _; refine hk _ ⟨_, _, ?_, (fun h => by cases h), trivial, rfl⟩
      have hcb : (cb.signExtend 64).setWidth 8 = cb := by
        rw [← BitVec.truncate_eq_setWidth]; exact truncate_signExtend_64 (by decide) cb
      dsimp only [Width.bits, AluBinKind.eval]
      rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide),
        setWidth_mul_le (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_setWidth_of_le _ (by decide), hcb, BitVec.mul_comm]
    | W16 =>
      simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All]
      intro _ _ _ _; refine hk _ ?_; simp only [AluBinKind.eval, Width.bits]
      rw [h16, BitVec.mul_comm]; close_alu_z
    | W32 =>
      simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All]
      intro _ _ _ _; refine hk _ ?_; simp only [AluBinKind.eval, Width.bits]
      rw [h32, BitVec.mul_comm]; close_alu_z
    | W64 =>
      simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All]
      intro _ _ _ _; refine hk _ ?_; simp only [AluBinKind.eval, Width.bits]
      rw [h64, BitVec.setWidth_eq, BitVec.mul_comm]; close_alu_z

theorem fallsTo_aluBinIns_imm (w : Width) (k : AluBinKind) (s : MachineData) (rd : Reg64)
    (cb : BitVec w.bits) :
    Directive.FallsTo (aluBinIns w k rd (immBitsOp w cb)) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = k.eval ((s.regs.get64 rd).setWidth w.bits) cb ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  exact fallsTo_aluBinIns_imm_z w k s rd cb _ _ _ _ fun s' ⟨rv, st, h1, _, _, h2⟩ =>
    hk s' ⟨rv, st, h1, h2⟩

theorem fallsTo_cmp_reg (w : Width) (s : MachineData) (rx ry : Reg64) :
    Directive.FallsTo (insW w (.cmp (.reg (regW w rx)) (.reg (regW w ry)))) s
      (· = { s with status := (subFlags ((s.regs.get64 rx).setWidth w.bits)
        ((s.regs.get64 ry).setWidth w.bits)) }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, t_step_simp] <;> exact hk _ rfl

theorem fallsTo_cmp_imm (w : Width) (s : MachineData) (rx : Reg64) (cy : BitVec w.bits) :
    Directive.FallsTo (insW w (.cmp (.reg (regW w rx)) (immBitsOp w cy))) s
      (· = { s with status := (subFlags ((s.regs.get64 rx).setWidth w.bits) cy) }) := by
  intro _ _ _ _ _ hk
  have htr : (cy.signExtend 64).truncate w.bits = cy :=
    truncate_signExtend_64 (width_bits_le_64 w) cy
  cases w <;> simp only [insW, immBitsOp, t_step_simp, Int64.toBitVec_ofBitVec, htr] <;>
    exact hk _ rfl

theorem fallsTo_test_reg (w : Width) (s : MachineData) (rx ry : Reg64) :
    Directive.FallsTo (insW w (.test (.reg (regW w rx)) (.reg (regW w ry)))) s
      (fun s' => ∃ af, s' = { s with
        status := testFlags ((s.regs.get64 rx).setWidth w.bits)
          ((s.regs.get64 ry).setWidth w.bits) af }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, t_step_simp, Effects.All] <;> intro af <;>
    exact hk _ ⟨af, rfl⟩

theorem fallsTo_test_imm (w : Width) (s : MachineData) (rx : Reg64) (cy : BitVec w.bits) :
    Directive.FallsTo (insW w (.test (.reg (regW w rx)) (immBitsOp w cy))) s
      (fun s' => ∃ af, s' = { s with
        status := testFlags ((s.regs.get64 rx).setWidth w.bits) cy af }) := by
  intro _ _ _ _ _ hk
  have htr : (cy.signExtend 64).truncate w.bits = cy :=
    truncate_signExtend_64 (width_bits_le_64 w) cy
  cases w <;> simp only [insW, immBitsOp, t_step_simp, Int64.toBitVec_ofBitVec, htr,
    Effects.All] <;> intro af <;> exact hk _ ⟨af, rfl⟩

theorem fallsTo_rolw8 (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (ins16 (.rol (.reg (h16 rd)) (.imm8 (.int64 8)))) s (fun s' =>
      ∃ rv status, rv.setWidth 16 = bswapBits ((s.regs.get64 rd).setWidth 16) ∧
        status.pf = s.status.pf ∧ status.zf = s.status.zf ∧ status.sf = s.status.sf ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, ConstExpr.interp, ShiftCountExpr.interp, ShiftCountExpr.interpMasked]
  change (undefined fun _ => _).All _
  intro _of
  refine hk _ ⟨_, _, ?_, ?_, ?_, ?_, rfl⟩
  · rw [replaceLow_setWidth_le (by decide),
      show (((Int64.toBitVec 8).take 8).toNat &&& 31) = 8 from rfl, bswapBits_16]
  · rfl
  · rfl
  · rfl

theorem fallsTo_bswap32 (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (ins32 (.bswap (d rd))) s
      (· = { s with regs :=
        s.regs.set64 rd ((bswapBits ((s.regs.get64 rd).setWidth 32)).setWidth 64) }) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, Reg64s.set, BitVec.zeroExtend_eq_setWidth]
  rw [bswapBits_32]; exact hk _ rfl

theorem fallsTo_bswap64 (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (ins (.bswap (q rd))) s
      (· = { s with regs := s.regs.set64 rd (bswapBits (s.regs.get64 rd)) }) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, Reg64s.set]
  rw [bswapBits_64]; exact hk _ rfl

/-! ## 4. `op_spec` Lemmas: Copy, Bool, Conversions, `bswap`, `neg`, `not` -/

private theorem opCopyBits_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hz : z32 = true → w = .W32 ∧ pa ≠ .gpr rd)
    (hc : opCopyBitsIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ z32 w rd va clob s) E s := by
  cases pa with
  | gpr rs =>
    simp only [opCopyBitsIns] at hc; split at hc
    · rename_i hrs; have heq := (beq_reg64_iff rs rd).1 hrs; subst heq
      have hnz : z32 = false := by cases hb : z32 <;> simp_all
      subst hnz
      simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      exact _root_.Program.wp_nil ⟨⟨hpa, rfl, Machine.Frame.refl _ _ _ _ _⟩, fun h => by cases h⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w s rd rs)) ?_
      rintro s' rfl
      refine OpPostZ.of_set64 (by rw [setWidth_64_setWidth, hpa.2]) ?_
        (updFlags_of_status_eq rfl _)
      intro _ hw; subst hw; rw [hpa.2]
  | imm ca =>
    simp only [opCopyBitsIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (ca.setWidth 64))) ?_
    rintro s' rfl
    exact OpPostZ.of_set64 (setWidth_64_setWidth w ca) (fun _ _ => rfl)
      (updFlags_of_status_eq rfl _)
  | vec _ => simp [opCopyBitsIns] at hc

theorem opCopyBits_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opCopyBitsIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd va clob s) E s :=
  Program.wp.mono (opCopyBits_z false w (fun h => by cases h) hc hpa) fun _ h => h.1

theorem opCopyBits_zero32_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec 32} {s : MachineData}
    (hne : pa ≠ .gpr rd) (hc : opCopyBitsIns .W32 pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits 32) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd va clob s) E s :=
  opCopyBits_z true .W32 (fun _ => ⟨rfl, hne⟩) hc hpa

theorem opPostDst_gpr_bool {rd : Reg64} {rv : BitVec 64} {st : StatusFlags}
    {clob : FlagMask} {s : MachineData} {b : Bool}
    (hrv : rv.setWidth 8 = BitVec.ofNat 8 b.toNat)
    (hup : x64Mach.UpdFlags x64CondReads s
      { s with regs := s.regs.set64 rd rv, status := st } clob) :
    OpPostDst1 .bool (.gpr rd) b clob s { s with regs := s.regs.set64 rd rv, status := st } := by
  refine ⟨?_, rfl, x64_frame_of_eq ?_ rfl hup⟩
  · dsimp only [Machine.PDstHolds, GprHolds]; rw [Reg64s.get64_set64_same, hrv]
  · intro r hr
    simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs,
      List.singleton_append, List.mem_cons, not_or] at hr
    exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)

theorem opCopyBool_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Instr} {clob : FlagMask} {b : Bool} {s : MachineData}
    (hc : opCopyBoolIns pa pd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa b) :
    _root_.Program.wp (emitClean c) (OpPostDst1 .bool pd b clob s) E s := by
  cases pd with
  | flag _ | vec _ => simp [opCopyBoolIns] at hc
  | gpr rd =>
    cases pa with
    | gpr rs =>
      simp only [opCopyBoolIns] at hc; split at hc
      · rename_i hrs; have := (beq_reg64_iff rs rd).1 hrs; subst this
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        exact _root_.Program.wp_nil ⟨hpa, rfl, Machine.Frame.refl _ _ _ _ _⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 s rd rs)) ?_
        rintro s' rfl
        exact opPostDst_gpr_bool
          (by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]; exact hpa)
          (updFlags_of_status_eq rfl _)
    | imm b0 =>
      simp only [opCopyBoolIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono
        (Directive.FallsTo.wp (fallsTo_moviD s rd (BitVec.ofNat 64 b0.toNat))) ?_
      rintro s' rfl
      exact opPostDst_gpr_bool (by cases b0 <;> rfl) (updFlags_of_status_eq rfl _)
    | flag cc =>
      simp only [opCopyBoolIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      have hcc : cc.interp s.status = b := hpa
      refine Program.wp.mono (wp_setccOnly s rd cc) ?_
      rintro s' rfl
      exact opPostDst_gpr_bool (by rw [replaceLow_setWidth_le (by decide), hcc])
        (updFlags_of_status_eq rfl _)
    | vec _ => simp [opCopyBoolIns] at hc

theorem opCopyBool_boolFlag_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {cc : CondCode} {c : List Instr} {clob : FlagMask} {b : Bool} {s : MachineData}
    (hfl : x64BoolFlagOut (.copy .bool) (pa, ()) pd = some cc)
    (hc : opCopyBoolIns pa pd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa b) :
    _root_.Program.wp (emitClean c)
      (fun s' => OpPostDst1 .bool pd b clob s s' ∧ cc.interp s'.status = b) E s := by
  cases pd with
  | flag _ | vec _ => simp [x64BoolFlagOut] at hfl
  | gpr rd =>
    cases pa with
    | flag c0 =>
      simp only [x64BoolFlagOut, Option.some.injEq] at hfl; subst hfl
      simp only [opCopyBoolIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩
      have hcc : c0.interp s.status = b := hpa
      refine Program.wp.mono (wp_setccOnly s rd c0) ?_
      rintro s' rfl
      exact ⟨opPostDst_gpr_bool (by rw [replaceLow_setWidth_le (by decide), hcc])
        (updFlags_of_status_eq rfl _), hcc⟩
    | gpr _ | imm _ | vec _ => simp [x64BoolFlagOut] at hfl

private theorem wp_boolBinSelf [Host] {E : Int64 → MachineData → Prop} (op : Bool → Bool → Bool)
    (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (h8 : ∀ (dst src : Reg64) (s : MachineData),
      Directive.FallsTo (ins8 (insFn (.reg (b8 dst)) (.reg (b8 src)))) s (fun s' => ∃ rv status,
        (∀ a b : Bool, (s.regs.get64 dst).setWidth 8 = BitVec.ofNat 8 a.toNat →
          (s.regs.get64 src).setWidth 8 = BitVec.ofNat 8 b.toNat →
          rv.setWidth 8 = BitVec.ofNat 8 (op a b).toNat ∧
          status.zf = decide (BitVec.ofNat 8 (op a b).toNat = 0#8)) ∧
        s' = { s with regs := s.regs.set64 dst rv, status }))
    {rd : Reg64} {other : PArg Reg64 RegMm CondCode .bool} {c : List Instr} {clob : FlagMask}
    {a b : Bool} {s : MachineData}
    (hc : boolBinSelfIns insFn rd other = some (c, clob))
    (hrd_sc : rd ∉ x64Scratch)
    (hrd : (s.regs.get64 rd).setWidth 8 = BitVec.ofNat 8 a.toNat)
    (hother : x64Mach.PArgHolds s .bool other b)
    (hother_sc : ∀ r ∈ other.gprs, r ∉ x64Scratch) :
    _root_.Program.wp (emitClean c)
      (fun s' => OpPostDst1 .bool (.gpr rd) (op a b) clob s s' ∧
        CondCode.nz.interp s'.status = op a b) E s := by
  cases other with
  | vec _ => simp [boolBinSelfIns, boolArgTo8I] at hc
  | gpr rs =>
    simp only [boolBinSelfIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (h8 rd rs s)) ?_
    rintro s' ⟨rv, st', hrvs, rfl⟩
    have hrs : (s.regs.get64 rs).setWidth 8 = BitVec.ofNat 8 b.toNat := hother
    have ⟨hrv, hzf⟩ := hrvs a b hrd hrs
    refine ⟨⟨?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, ?_⟩
    · dsimp only [Machine.PDstHolds, GprHolds]
      rw [Reg64s.get64_set64_same]; exact hrv
    · intro r hr
      simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, List.cons_append,
        List.nil_append, List.mem_cons, not_or] at hr
      exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
    · simp only [CondCode.interp, hzf]; cases op a b <;> rfl
  | imm _ | flag _ =>
    simp only [boolBinSelfIns, Option.bind_eq_bind] at hc
    rcases Option.bind_eq_some_iff.mp hc with ⟨d2, hd2, hc'⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hc'
    rcases hc' with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_boolArgTo8 s .r10 hd2 hother)) ?_
    rintro s1 ⟨rv10, hrv10, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (h8 rd .r10 _)) ?_
    rintro s2 ⟨rv, st', hrvs, rfl⟩
    have hrd1 : ((s.regs.set64 .r10 rv10).get64 rd).setWidth 8 = BitVec.ofNat 8 a.toNat := by
      have hne := (ne_of_not_mem_x64Scratch hrd_sc).1
      rw [Reg64s.get64_set64_of_ne _ .r10 rd _ hne.symm, hrd]
    have hr10_1 : ((s.regs.set64 .r10 rv10).get64 .r10).setWidth 8 = BitVec.ofNat 8 b.toNat := by
      rw [Reg64s.get64_set64_same, hrv10]
    have ⟨hrv, hzf⟩ := hrvs a b hrd1 hr10_1
    refine ⟨⟨?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, ?_⟩
    · dsimp only [Machine.PDstHolds, GprHolds]
      rw [Reg64s.get64_set64_same]; exact hrv
    · intro r hr
      simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, List.cons_append,
        List.nil_append, List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1)]
    · simp only [CondCode.interp, hzf]; cases op a b <;> rfl

private theorem wp_boolBinDst [Host] {E : Int64 → MachineData → Prop} (op : Bool → Bool → Bool)
    (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (h8 : ∀ (dst src : Reg64) (s : MachineData),
      Directive.FallsTo (ins8 (insFn (.reg (b8 dst)) (.reg (b8 src)))) s (fun s' => ∃ rv status,
        (∀ a b : Bool, (s.regs.get64 dst).setWidth 8 = BitVec.ofNat 8 a.toNat →
          (s.regs.get64 src).setWidth 8 = BitVec.ofNat 8 b.toNat →
          rv.setWidth 8 = BitVec.ofNat 8 (op a b).toNat ∧
          status.zf = decide (BitVec.ofNat 8 (op a b).toNat = 0#8)) ∧
        s' = { s with regs := s.regs.set64 dst rv, status }))
    {rd : Reg64} {first second : PArg Reg64 RegMm CondCode .bool}
    {c : List Instr} {clob : FlagMask} {a b : Bool} {s : MachineData}
    (hc : boolBinDstIns insFn rd first second = some (c, clob))
    (hrd_sc : rd ∉ x64Scratch)
    (hfirst : x64Mach.PArgHolds s .bool first a) (hsecond : x64Mach.PArgHolds s .bool second b)
    (hnot_rd : rd ∉ first.gprs ++ second.gprs)
    (hargs : ∀ r ∈ first.gprs ++ second.gprs, r ∉ x64Scratch) :
    _root_.Program.wp (emitClean c)
      (fun s' => OpPostDst1 .bool (.gpr rd) (op a b) clob s s' ∧
        CondCode.nz.interp s'.status = op a b) E s := by
  simp only [boolBinDstIns, Option.bind_eq_bind] at hc
  rcases Option.bind_eq_some_iff.mp hc with ⟨d1, hd1, hc1⟩
  cases second with
  | vec _ => simp [boolArgTo8I] at hc1
  | gpr rs =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hc1
    rcases hc1 with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    have hrs_ne : rs ≠ rd := fun h => hnot_rd (by subst h; simp [PArg.gprs])
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_boolArgTo8 s rd hd1 hfirst)) ?_
    rintro s1 ⟨rv1, hrv1, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (h8 rd rs _)) ?_
    rintro s2 ⟨rv, st', hrvs, rfl⟩
    have hrd1 : ((s.regs.set64 rd rv1).get64 rd).setWidth 8 = BitVec.ofNat 8 a.toNat := by
      rw [Reg64s.get64_set64_same, hrv1]
    have hrs1 : ((s.regs.set64 rd rv1).get64 rs).setWidth 8 = BitVec.ofNat 8 b.toNat := by
      rw [Reg64s.get64_set64_of_ne _ rd rs _ hrs_ne.symm]; exact hsecond
    have ⟨hrv, hzf⟩ := hrvs a b hrd1 hrs1
    refine ⟨⟨?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, ?_⟩
    · dsimp only [Machine.PDstHolds, GprHolds]
      rw [Reg64s.get64_set64_same]; exact hrv
    · intro r hr
      simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, List.cons_append,
        List.nil_append, List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
    · simp only [CondCode.interp, hzf]; cases op a b <;> rfl
  | imm _ | flag _ =>
    rcases Option.bind_eq_some_iff.mp hc1 with ⟨d2, hd2, hc2⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hc2
    rcases hc2 with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_boolArgTo8 s rd hd1 hfirst)) ?_
    rintro s1 ⟨rv1, hrv1, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp
      (fallsTo_boolArgTo8 { s with regs := s.regs.set64 rd rv1 } .r10 hd2 hsecond)) ?_
    rintro s2 ⟨rv10, hrv10, rfl⟩
    refine Program.wp.mono (Directive.FallsTo.wp (h8 rd .r10 _)) ?_
    rintro s3 ⟨rv, st', hrvs, rfl⟩
    have hrd2 : (((s.regs.set64 rd rv1).set64 .r10 rv10).get64 rd).setWidth 8 =
        BitVec.ofNat 8 a.toNat := by
      have hne := (ne_of_not_mem_x64Scratch hrd_sc).1
      rw [Reg64s.get64_set64_of_ne _ .r10 rd _ hne.symm, Reg64s.get64_set64_same, hrv1]
    have hr10_2 : (((s.regs.set64 rd rv1).set64 .r10 rv10).get64 .r10).setWidth 8 =
        BitVec.ofNat 8 b.toNat := by
      rw [Reg64s.get64_set64_same, hrv10]
    have ⟨hrv, hzf⟩ := hrvs a b hrd2 hr10_2
    refine ⟨⟨?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, ?_⟩
    · dsimp only [Machine.PDstHolds, GprHolds]
      rw [Reg64s.get64_set64_same]; exact hrv
    · intro r hr
      simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, List.cons_append,
        List.nil_append, List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1),
        Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
    · simp only [CondCode.interp, hzf]; cases op a b <;> rfl

theorem opBoolBin_flag_spec [Host] {E : Int64 → MachineData → Prop} (op : Bool → Bool → Bool)
    (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (hcomm : ∀ x y : Bool, op x y = op y x)
    (h8 : ∀ (dst src : Reg64) (s : MachineData),
      Directive.FallsTo (ins8 (insFn (.reg (b8 dst)) (.reg (b8 src)))) s (fun s' => ∃ rv status,
        (∀ a b : Bool, (s.regs.get64 dst).setWidth 8 = BitVec.ofNat 8 a.toNat →
          (s.regs.get64 src).setWidth 8 = BitVec.ofNat 8 b.toNat →
          rv.setWidth 8 = BitVec.ofNat 8 (op a b).toNat ∧
          status.zf = decide (BitVec.ofNat 8 (op a b).toNat = 0#8)) ∧
        s' = { s with regs := s.regs.set64 dst rv, status }))
    {pa pb : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Instr} {clob : FlagMask} {a b : Bool} {s : MachineData}
    (hc : opBoolBinIns op insFn pa pb pd = some (c, clob))
    (hdst : ∀ r ∈ pd.gprs, r ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s .bool pa a) (hpb : x64Mach.PArgHolds s .bool pb b) :
    _root_.Program.wp (emitClean c)
      (fun s' => OpPostDst1 .bool pd (op a b) clob s s' ∧
        (clob ≠ maskNone → CondCode.nz.interp s'.status = op a b)) E s := by
  cases pd with
  | flag _ | vec _ => simp [opBoolBinIns] at hc
  | gpr rd =>
    have hrd_sc : rd ∉ x64Scratch := hdst rd (by simp [PDst.gprs])
    cases pa with
    | imm a0 =>
      cases pb with
      | imm b0 =>
        simp only [opBoolBinIns, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl; rcases hpb with rfl
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
        rintro s' rfl
        exact ⟨opPostDst_gpr_bool (by cases op a0 b0 <;> rfl) (updFlags_of_status_eq rfl _),
          fun h => absurd rfl h⟩
      | gpr rb =>
        simp only [opBoolBinIns] at hc
        by_cases hbr : rb == rd
        · have heq := (beq_reg64_iff rb rd).1 hbr; subst heq
          simp only [hbr, ↓reduceIte] at hc
          rw [hcomm]
          exact Program.wp.mono (wp_boolBinSelf op insFn h8 hc hrd_sc hpb hpa
            (fun r hr => hargs r (List.mem_append_left _ hr))) fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
        · simp only [hbr, Bool.false_eq_true, ↓reduceIte] at hc
          exact Program.wp.mono (wp_boolBinDst op insFn h8 hc hrd_sc hpa hpb
            (fun h => hbr ((beq_reg64_iff rb rd).2 (by simp [PArg.gprs] at h; exact h.symm))) hargs)
            fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
      | flag _ | vec _ =>
        simp only [opBoolBinIns] at hc
        exact Program.wp.mono
          (wp_boolBinDst op insFn h8 hc hrd_sc hpa hpb (by simp [PArg.gprs]) hargs)
          fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
    | flag _ | vec _ =>
      cases pb with
      | gpr rb =>
        simp only [opBoolBinIns] at hc
        by_cases hbr : rb == rd
        · have heq := (beq_reg64_iff rb rd).1 hbr; subst heq
          simp only [hbr, ↓reduceIte] at hc
          rw [hcomm]
          exact Program.wp.mono (wp_boolBinSelf op insFn h8 hc hrd_sc hpb hpa
            (fun r hr => hargs r (List.mem_append_left _ hr))) fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
        · simp only [hbr, Bool.false_eq_true, ↓reduceIte] at hc
          exact Program.wp.mono (wp_boolBinDst op insFn h8 hc hrd_sc hpa hpb
            (fun h => hbr ((beq_reg64_iff rb rd).2 (by simp [PArg.gprs] at h; exact h.symm))) hargs)
            fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
      | imm _ | flag _ | vec _ =>
        simp only [opBoolBinIns] at hc
        exact Program.wp.mono
          (wp_boolBinDst op insFn h8 hc hrd_sc hpa hpb (by simp [PArg.gprs]) hargs)
          fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
    | gpr ra =>
      simp only [opBoolBinIns] at hc
      by_cases har : ra == rd
      · have heq := (beq_reg64_iff ra rd).1 har; subst heq
        simp only [har, ↓reduceIte] at hc
        exact Program.wp.mono (wp_boolBinSelf op insFn h8 hc hrd_sc hpa hpb
          (fun r hr => hargs r (List.mem_append_right _ hr))) fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
      · simp only [har, Bool.false_eq_true, ↓reduceIte] at hc
        have hra_ne : rd ≠ ra := fun h => har ((beq_reg64_iff ra rd).2 h.symm)
        cases pb with
        | gpr rb =>
          by_cases hbr : rb == rd
          · have heq := (beq_reg64_iff rb rd).1 hbr; subst heq
            simp only [hbr, ↓reduceIte] at hc
            rw [hcomm]
            exact Program.wp.mono (wp_boolBinSelf op insFn h8 hc hrd_sc hpb hpa
              (fun r hr => hargs r (List.mem_append_left _ hr))) fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
          · simp only [hbr, Bool.false_eq_true, ↓reduceIte] at hc
            have hrb_ne : rd ≠ rb := fun h => hbr ((beq_reg64_iff rb rd).2 h.symm)
            exact Program.wp.mono (wp_boolBinDst op insFn h8 hc hrd_sc hpa hpb
              (by simp [PArg.gprs, hra_ne, hrb_ne]) hargs) fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩
        | imm _ | flag _ | vec _ =>
          rw [hcomm]
          exact Program.wp.mono (wp_boolBinDst op insFn h8 hc hrd_sc hpb hpa
            (by simp [PArg.gprs, hra_ne])
            (fun r hr => hargs r (by simp only [List.mem_append] at hr ⊢; exact hr.symm)))
            fun _ ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩

theorem opBoolBin_spec [Host] {E : Int64 → MachineData → Prop} (op : Bool → Bool → Bool)
    (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (hcomm : ∀ x y : Bool, op x y = op y x)
    (h8 : ∀ (dst src : Reg64) (s : MachineData),
      Directive.FallsTo (ins8 (insFn (.reg (b8 dst)) (.reg (b8 src)))) s (fun s' => ∃ rv status,
        (∀ a b : Bool, (s.regs.get64 dst).setWidth 8 = BitVec.ofNat 8 a.toNat →
          (s.regs.get64 src).setWidth 8 = BitVec.ofNat 8 b.toNat →
          rv.setWidth 8 = BitVec.ofNat 8 (op a b).toNat ∧
          status.zf = decide (BitVec.ofNat 8 (op a b).toNat = 0#8)) ∧
        s' = { s with regs := s.regs.set64 dst rv, status }))
    {pa pb : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Instr} {clob : FlagMask} {a b : Bool} {s : MachineData}
    (hc : opBoolBinIns op insFn pa pb pd = some (c, clob))
    (hdst : ∀ r ∈ pd.gprs, r ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s .bool pa a) (hpb : x64Mach.PArgHolds s .bool pb b) :
    _root_.Program.wp (emitClean c) (OpPostDst1 .bool pd (op a b) clob s) E s :=
  Program.wp.mono (opBoolBin_flag_spec op insFn hcomm h8 hc hdst hargs hpa hpb) fun _ h => h.1

theorem opBoolNot_boolFlag_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {cc : CondCode} {c : List Instr} {clob : FlagMask} {a : Bool} {s : MachineData}
    (hfl : x64BoolFlagOut (.not .bool) (pa, ()) pd = some cc)
    (hc : opBoolNotIns pa pd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa a) :
    _root_.Program.wp (emitClean c)
      (fun s' => OpPostDst1 .bool pd (!a) clob s s' ∧ cc.interp s'.status = !a) E s := by
  cases pd with
  | vec _ | flag _ => simp [x64BoolFlagOut] at hfl
  | gpr rd =>
    cases pa with
    | imm _ | vec _ => simp [x64BoolFlagOut] at hfl
    | flag c0 =>
      simp only [x64BoolFlagOut, Option.some.injEq] at hfl; subst hfl
      simp only [opBoolNotIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩
      have hcc : (x64NegCond c0).interp s.status = !a := by
        rw [x64NegCond_interp]; exact congrArg Bool.not hpa
      refine Program.wp.mono (wp_setccOnly s rd (x64NegCond c0)) ?_
      rintro s' rfl
      exact ⟨opPostDst_gpr_bool (by rw [replaceLow_setWidth_le (by decide), hcc])
        (updFlags_of_status_eq rfl _), hcc⟩
    | gpr rs =>
      simp only [x64BoolFlagOut, Option.some.injEq] at hfl; subst hfl
      simp only [opBoolNotIns] at hc
      by_cases hrs : rs == rd
      · have heq := (beq_reg64_iff rs rd).1 hrs; subst heq
        simp only [hrs, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_xor8_one s rs)) ?_
        rintro s1 ⟨st', hzf, rfl⟩
        have hxa : ((s.regs.get64 rs).setWidth 8 ^^^ 1#8) = BitVec.ofNat 8 (!a).toNat := by
          rw [show (s.regs.get64 rs).setWidth 8 = BitVec.ofNat 8 a.toNat from hpa]
          cases a <;> rfl
        refine ⟨⟨?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, ?_⟩
        · dsimp only [Machine.PDstHolds, GprHolds]
          rw [Reg64s.get64_set64_same, replaceLow_setWidth_le (by decide), hxa]
        · intro r hr
          simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, List.cons_append,
            List.nil_append, List.mem_cons, not_or] at hr
          exact Reg64s.get64_set64_of_ne _ rs r _ (Ne.symm hr.1)
        · simp only [CondCode.interp, hzf, hxa]; cases a <;> rfl
      · simp only [hrs, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movzx8 s rd rs)) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_xor8_one _ rd)) ?_
        rintro s2 ⟨st', hzf, rfl⟩
        have hs1 :
            (((s.regs.set64 rd (((s.regs.get64 rs).setWidth 8).setWidth 64))).get64 rd).setWidth
              8 = BitVec.ofNat 8 a.toNat := by
          rw [Reg64s.get64_set64_same,
            BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
          exact hpa
        have hxa :
            (((s.regs.set64 rd (((s.regs.get64 rs).setWidth 8).setWidth 64)).get64 rd).setWidth 8
              ^^^ 1#8) = BitVec.ofNat 8 (!a).toNat := by
          rw [hs1]; cases a <;> rfl
        refine ⟨⟨?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩, ?_⟩
        · dsimp only [Machine.PDstHolds, GprHolds]
          rw [Reg64s.get64_set64_same, replaceLow_setWidth_le (by decide), hxa]
        · intro r hr
          simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, List.cons_append,
            List.nil_append, List.mem_cons, not_or] at hr
          rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
            Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
        · simp only [CondCode.interp, hzf, hxa]; cases a <;> rfl

theorem opBoolNot_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Instr} {clob : FlagMask} {a : Bool} {s : MachineData}
    (hc : opBoolNotIns pa pd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa a) :
    _root_.Program.wp (emitClean c) (OpPostDst1 .bool pd (!a) clob s) E s := by
  cases pd with
  | vec _ => simp [opBoolNotIns] at hc
  | flag ccDst =>
    cases pa with
    | flag ccSrc =>
      simp only [opBoolNotIns] at hc
      split at hc <;> try contradiction
      rename_i hcc
      have hcc' := (beq_cond_iff ccDst (x64NegCond ccSrc)).1 hcc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩
      refine _root_.Program.wp_nil ⟨?_, rfl, Machine.Frame.refl _ _ _ _ _⟩
      dsimp only [Machine.PArgHolds, Machine.PDstHolds, x64Mach] at hpa ⊢
      rw [hcc', x64NegCond_interp, hpa]
    | _ => simp [opBoolNotIns] at hc
  | gpr rd =>
    cases pa with
    | imm b0 =>
      simp only [opBoolNotIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
      rintro s' rfl
      exact opPostDst_gpr_bool (by cases b0 <;> rfl) (updFlags_of_status_eq rfl _)
    | flag _ | gpr _ =>
      exact Program.wp.mono (opBoolNot_boolFlag_spec rfl hc hpa) fun _ h => h.1
    | vec _ => simp [opBoolNotIns] at hc

private theorem opOfBool_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    {pa : PArg Reg64 RegMm CondCode .bool} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {b : Bool} {s : MachineData}
    (hc : opOfBoolIns pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa b) :
    _root_.Program.wp (emitClean c)
      (OpPostZ z32 w rd (BitVec.ofNat w.bits b.toNat) clob s) E s := by
  cases pa with
  | gpr rs =>
    simp only [opOfBoolIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 s rd rs)) ?_
    rintro s' rfl
    exact OpPostZ.of_set64
      (by rw [hpa, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
          cases w <;> cases b <;> rfl)
      (fun _ hw => by subst hw; rw [hpa]; cases b <;> rfl)
      (updFlags_of_status_eq rfl _)
  | imm b0 =>
    simp only [opOfBoolIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (BitVec.ofNat 64 b0.toNat))) ?_
    rintro s' rfl
    exact OpPostZ.of_set64 (by cases w <;> cases b0 <;> rfl)
      (fun _ hw => by subst hw; cases b0 <;> rfl) (updFlags_of_status_eq rfl _)
  | flag cc =>
    simp only [opOfBoolIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    have hcc : cc.interp s.status = b := hpa
    refine Program.wp.mono (wp_setccMove s rd cc) ?_
    rintro s' rfl
    exact OpPostZ.of_set64 (by rw [hcc]; cases w <;> cases b <;> rfl)
      (fun _ hw => by subst hw; rw [hcc]; cases b <;> rfl) (updFlags_of_status_eq rfl _)
  | vec _ => simp [opOfBoolIns] at hc

theorem opOfBool_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode .bool} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {b : Bool} {s : MachineData}
    (hc : opOfBoolIns pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa b) :
    _root_.Program.wp (emitClean c)
      (OpPost1 (.bits w.bits) rd (BitVec.ofNat w.bits b.toNat) clob s) E s :=
  Program.wp.mono (opOfBool_z false w hc hpa) fun _ h => h.1

theorem opOfBool_zero32_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode .bool} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {b : Bool} {s : MachineData}
    (hc : opOfBoolIns pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa b) :
    _root_.Program.wp (emitClean c)
      (OpPostZ true .W32 rd (BitVec.ofNat 32 b.toNat) clob s) E s :=
  opOfBool_z true .W32 hc hpa

private theorem opExt_bounds {m n : Nat}
    (h : x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n = true) :
    (m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64) ∧
      (n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) ∧ m < n ∧ n ≤ 64 := by
  simp only [Bool.and_eq_true, x64BitWidths, List.contains_eq_mem, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false, Nat.ble_eq] at h
  refine ⟨by omega, by omega, by omega, by omega⟩

private theorem setWidth_32_64_of_le {m : Nat} (hm : m ≤ 32) (x : BitVec m) :
    x.setWidth 64 = (x.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 32 with h | h
  · simp [h]
  · simp [BitVec.getLsbD_of_ge x i (by omega)]

private theorem opZext_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (m n : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hz : z32 = true → n = 32)
    (hc : opZextIns m n pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    m ≤ n ∧ _root_.Program.wp (emitClean c)
      (fun s' => OpPost1 (.bits n) rd (va.setWidth n) clob s s' ∧
        (z32 = true → s'.regs.get64 rd = (va.setWidth n).setWidth 64)) E s := by
  cases hmnb : x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n with
  | false => unfold opZextIns at hc; rw [hmnb] at hc; cases hc
  | true =>
    obtain ⟨hm, hn, hlt, hle64⟩ := opExt_bounds hmnb
    refine ⟨Nat.le_of_lt hlt, ?_⟩
    unfold opZextIns at hc; rw [hmnb] at hc
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
    have finish (rv : BitVec 64) (hrv : rv.setWidth n = va.setWidth n)
        (hrvz : z32 = true → rv = (va.setWidth n).setWidth 64)
        {s' : MachineData} (hs' : s' = { s with regs := s.regs.set64 rd rv }) :
        OpPost1 (.bits n) rd (va.setWidth n) maskNone s s' ∧
          (z32 = true → s'.regs.get64 rd = (va.setWidth n).setWidth 64) := by
      subst hs'
      refine ⟨⟨⟨hle64, by rw [Reg64s.get64_set64_same, hrv]⟩, rfl,
        x64_frame_of_eq ?_ rfl (updFlags_of_status_eq rfl _)⟩, fun hz1 => by
        rw [Reg64s.get64_set64_same, hrvz hz1]⟩
      intro r hr; simp only [List.mem_cons, not_or] at hr
      exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
    cases pa with
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (ca.setWidth 64))) ?_
      rintro s' rfl
      refine finish _ (BitVec.setWidth_setWidth_of_le _ hle64) ?_ rfl
      intro hz1; cases hz hz1
      exact setWidth_32_64_of_le (by omega) ca
    | gpr rs =>
      rcases hm with rfl | rfl | rfl | rfl <;> try (exfalso; omega)
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 s rd rs)) ?_
        rintro s' rfl
        refine finish _ (by rw [hpa.2, BitVec.setWidth_setWidth_of_le _ hle64]) ?_ rfl
        intro hz1; cases hz hz1
        rw [hpa.2]; exact setWidth_32_64_of_le (by decide) va
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx16 s rd rs)) ?_
        rintro s' rfl
        refine finish _ (by rw [hpa.2, BitVec.setWidth_setWidth_of_le _ hle64]) ?_ rfl
        intro hz1; cases hz hz1
        rw [hpa.2]; exact setWidth_32_64_of_le (by decide) va
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movlD s rd rs)) ?_
        rintro s' rfl
        refine finish _
          (by rw [hpa.2, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ hle64])
          (fun hz1 => by cases hz hz1; omega) rfl
    | vec _ => simp at hc

theorem opZext_spec [Host] {E : Int64 → MachineData → Prop} (m n : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hc : opZextIns m n pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    m ≤ n ∧ _root_.Program.wp (emitClean c) (OpPost1 (.bits n) rd (va.setWidth n) clob s) E s :=
  let ⟨hm, hwp⟩ := opZext_z false m n (fun h => by cases h) hc hpa
  ⟨hm, Program.wp.mono hwp fun _ h => h.1⟩

theorem opZext_zero32_spec [Host] {E : Int64 → MachineData → Prop} (m : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hc : opZextIns m 32 pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd (va.setWidth 32) clob s) E s :=
  Program.wp.mono (opZext_z true m 32 (fun _ => rfl) hc hpa).2 fun _ h => ⟨h.1, fun _ _ => h.2 rfl⟩

private theorem opSext_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (m n : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hz : z32 = true → n = 32)
    (hc : opSextIns m n pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    m ≤ n ∧
      _root_.Program.wp (emitClean c)
        (fun s' => OpPost1 (.bits n) rd (va.signExtend n) clob s s' ∧
          (z32 = true → s'.regs.get64 rd = (va.signExtend n).setWidth 64)) E s := by
  cases hmnb : x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n with
  | false => unfold opSextIns at hc; rw [hmnb] at hc; cases hc
  | true =>
    obtain ⟨hm, hn, hlt, hle64⟩ := opExt_bounds hmnb
    refine ⟨Nat.le_of_lt hlt, ?_⟩
    unfold opSextIns at hc; rw [hmnb] at hc
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
    have finish (rv : BitVec 64) (hrv : rv.setWidth n = va.signExtend n)
        (hrvz : z32 = true → rv = (va.signExtend n).setWidth 64)
        {s' : MachineData} (hs' : s' = { s with regs := s.regs.set64 rd rv }) :
        OpPost1 (.bits n) rd (va.signExtend n) maskNone s s' ∧
          (z32 = true → s'.regs.get64 rd = (va.signExtend n).setWidth 64) := by
      subst hs'
      refine ⟨⟨⟨hle64, by rw [Reg64s.get64_set64_same, hrv]⟩, rfl,
        x64_frame_of_eq ?_ rfl (updFlags_of_status_eq rfl _)⟩, fun hz1 => by
        rw [Reg64s.get64_set64_same, hrvz hz1]⟩
      intro r hr; simp only [List.mem_cons, not_or] at hr
      exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
    cases pa with
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp
        (fallsTo_moviD s rd ((ca.signExtend n).setWidth 64))) ?_
      rintro s' rfl; exact finish _
        (by rw [BitVec.setWidth_setWidth_of_le _ hle64, BitVec.setWidth_eq]) (fun _ => rfl) rfl
    | gpr rs =>
      rcases hm with rfl | rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl | rfl <;>
        try (exfalso; omega)
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx8 .W32 (.inl rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish ((va.signExtend 32).setWidth 64)
          (by rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
              exact setWidth_signExtend_of_le (by decide) (by decide) va)
          (fun hz1 => by cases hz hz1) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx8 .W32 (.inl rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish ((va.signExtend 32).setWidth 64)
          (by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq])
          (fun _ => rfl) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx8 .W64 (.inr rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish (va.signExtend 64) (BitVec.setWidth_eq _) (fun hz1 => by cases hz hz1) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx16 .W32 (.inl rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish ((va.signExtend 32).setWidth 64)
          (by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq])
          (fun _ => rfl) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx16 .W64 (.inr rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish (va.signExtend 64) (BitVec.setWidth_eq _) (fun hz1 => by cases hz hz1) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx32 s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish (va.signExtend 64) (BitVec.setWidth_eq _) (fun hz1 => by cases hz hz1) hs'
    | vec _ => simp at hc

theorem opSext_spec [Host] {E : Int64 → MachineData → Prop} (m n : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hc : opSextIns m n pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    m ≤ n ∧
      _root_.Program.wp (emitClean c) (OpPost1 (.bits n) rd (va.signExtend n) clob s) E s :=
  let ⟨hm, hwp⟩ := opSext_z false m n (fun h => by cases h) hc hpa
  ⟨hm, Program.wp.mono hwp fun _ h => h.1⟩

theorem opSext_zero32_spec [Host] {E : Int64 → MachineData → Prop} (m : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hc : opSextIns m 32 pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd (va.signExtend 32) clob s) E s :=
  Program.wp.mono (opSext_z true m 32 (fun _ => rfl) hc hpa).2 fun _ h => ⟨h.1, fun _ _ => h.2 rfl⟩

theorem opTrunc_spec [Host] {E : Int64 → MachineData → Prop} (m n : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hc : opTruncIns m n pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    n ≤ m ∧ _root_.Program.wp (emitClean c) (OpPost1 (.bits n) rd (va.setWidth n) clob s) E s := by
  cases hcond : x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (n + 1) m with
  | false => unfold opTruncIns at hc; rw [hcond] at hc; cases hc
  | true =>
    have hmnb : x64BitWidths.contains n && x64BitWidths.contains m && Nat.ble (n + 1) m = true := by
      simp only [Bool.and_eq_true] at hcond ⊢; exact ⟨⟨hcond.1.2, hcond.1.1⟩, hcond.2⟩
    obtain ⟨hn, _, hlt, _⟩ := opExt_bounds hmnb
    have hle : n ≤ m := Nat.le_of_lt hlt
    refine ⟨hle, ?_⟩
    unfold opTruncIns at hc; rw [hcond] at hc
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
    have harm (w : Width) (hw : w.bits = n) (pa' : PArg Reg64 RegMm CondCode (.bits m)) :
        (match pa' with
        | .imm ca => some ([moviI rd ((ca.setWidth n).setWidth 64)], maskNone)
        | .gpr r => if r == rd then some ([], maskNone) else some ([movWI w rd r], maskNone)
        | .vec _ => none) = some (c, clob) →
        x64Mach.PArgHolds s (.bits m) pa' va →
        _root_.Program.wp (emitClean c) (OpPost1 (.bits n) rd (va.setWidth n) clob s) E s := by
      intro harm hpa'; subst hw
      cases pa' with
      | imm ca =>
        simp only [Option.some.injEq, Prod.mk.injEq] at harm
        rcases harm with ⟨rfl, rfl⟩; rcases hpa' with rfl
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono
          (Directive.FallsTo.wp (fallsTo_moviD s rd ((ca.setWidth w.bits).setWidth 64))) ?_
        rintro s' rfl
        exact OpPost1.of_set64_bits (setWidth_64_setWidth w _) (updFlags_of_status_eq rfl _)
      | gpr rs =>
        by_cases hrr : rs == rd
        · have heq := (beq_reg64_iff rs rd).1 hrr; subst rs
          simp only [hrr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at harm
          rcases harm with ⟨rfl, rfl⟩
          refine _root_.Program.wp_nil
            ⟨(GprHolds.bits_iff w _ _).2 ?_, rfl, Machine.Frame.refl _ _ _ _ _⟩
          rw [← hpa'.2, BitVec.setWidth_setWidth_of_le _ hle]
        · simp only [hrr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at harm
          rcases harm with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w s rd rs)) ?_
          rintro s' rfl
          exact OpPost1.of_set64_bits
            (by rw [setWidth_64_setWidth, ← hpa'.2, BitVec.setWidth_setWidth_of_le _ hle])
            (updFlags_of_status_eq rfl _)
      | vec _ => simp at harm
    rcases hn with rfl | rfl | rfl | rfl
    · simp only at hc; exact harm .W8 rfl pa hc hpa
    · simp only at hc; exact harm .W16 rfl pa hc hpa
    · simp only at hc; exact harm .W32 rfl pa hc hpa
    · exfalso; omega

theorem opTrunc_zero32_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode (.bits 64)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec 64} {s : MachineData}
    (hne : pa ≠ .gpr rd) (hc : opTruncIns 64 32 pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits 64) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd (va.setWidth 32) clob s) E s := by
  unfold opTruncIns at hc
  simp only [x64BitWidths, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
  cases pa with
  | vec _ => simp at hc
  | imm ca =>
    rcases hpa with rfl
    rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono
      (Directive.FallsTo.wp (fallsTo_moviD s rd ((ca.setWidth 32).setWidth 64))) ?_
    rintro s' rfl
    exact OpPostZ.of_set64 (setWidth_64_setWidth .W32 _) (fun _ _ => rfl)
      (updFlags_of_status_eq rfl _)
  | gpr rs =>
    have hrs : (rs == rd) = false := by
      cases h : (rs == rd)
      · rfl
      · exact absurd (congrArg PArg.gpr ((beq_reg64_iff rs rd).1 h)) hne
    simp only [hrs, Bool.false_eq_true, ↓reduceIte] at hc
    rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW .W32 s rd rs)) ?_
    rintro s' rfl
    have h32 : (s.regs.get64 rs).setWidth 32 = va.setWidth 32 := by
      rw [← hpa.2, BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact OpPostZ.of_set64 (by rw [setWidth_64_setWidth, h32])
      (fun _ _ => by rw [h32]) (updFlags_of_status_eq rfl _)

theorem opBswap_spec [Host] {E : Int64 → MachineData → Prop} (n : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits n)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec n} {s : MachineData}
    (hc : opBswapIns n pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits n) pa va) :
    (Ty.bits n).bswapOk = true ∧
      _root_.Program.wp (emitClean c) (OpPost1 (.bits n) rd (bswapBits va) clob s) E s := by
  have hn : n = 16 ∨ n = 32 ∨ n = 64 := by
    by_cases h16 : n = 16
    · exact Or.inl h16
    · by_cases h32 : n = 32
      · exact Or.inr (Or.inl h32)
      · by_cases h64 : n = 64
        · exact Or.inr (Or.inr h64)
        · cases pa <;> simp [opBswapIns, h16, h32, h64] at hc
  refine ⟨by rcases hn with rfl | rfl | rfl <;> rfl, ?_⟩
  rcases hn with rfl | rfl | rfl
  · cases pa with
    | imm ca =>
      simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp
      (fallsTo_moviD s rd ((bswapBits ca).setWidth 64))) ?_
      rintro s' rfl
      exact OpPost1.of_set64_bits (setWidth_64_setWidth .W16 _) (updFlags_of_status_eq rfl _)
    | gpr rs =>
      simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
      refine Program.wp.append (wp_optMovW .W16 s rd rs hpa.2) ?_
      rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_rolw8 s1 rd)) ?_
      rintro s2 ⟨rv, st, hrv, hpf, hzf, hsf, rfl⟩
      refine ⟨⟨by decide, by rw [Reg64s.get64_set64_same, hrv, hrd1]⟩,
        hm1, x64_frame_of_eq ?_ hz1 ?_⟩
      · intro r hr; simp only [List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
      · exact updFlags_maskCF_OF (by rw [hpf, hst1]) (by rw [hzf, hst1]) (by rw [hsf, hst1])
    | vec _ => simp [opBswapIns] at hc
  · cases pa with
    | imm ca =>
      simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp
      (fallsTo_moviD s rd ((bswapBits ca).setWidth 64))) ?_
      rintro s' rfl
      exact OpPost1.of_set64_bits (setWidth_64_setWidth .W32 _) (updFlags_of_status_eq rfl _)
    | gpr rs =>
      simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
      have hpre : _root_.Program.wp (if rs == rd then [] else [movlD rd rs]) (fun s1 =>
          (s1.regs.get64 rd).setWidth 32 = va ∧ (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
          s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ s1.status = s.status) E s := by
        simpa [movW, movlD] using wp_optMovW .W32 s rd rs hpa.2
      refine Program.wp.append hpre ?_
      rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_bswap32 s1 rd)) ?_
      rintro s2 rfl
      refine ⟨⟨by decide, by rw [Reg64s.get64_set64_same, setWidth_64_setWidth .W32, hrd1]⟩,
        hm1, x64_frame_of_eq ?_ hz1 (updFlags_of_status_eq hst1 _)⟩
      intro r hr; simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
    | vec _ => simp [opBswapIns] at hc
  · cases pa with
    | imm ca =>
      simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (bswapBits ca))) ?_
      rintro s' rfl
      exact OpPost1.of_set64_bits (w := .W64) (BitVec.setWidth_eq _) (updFlags_of_status_eq rfl _)
    | gpr rs =>
      simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
      have hpre : _root_.Program.wp (if rs == rd then [] else [movD rd rs]) (fun s1 =>
          (s1.regs.get64 rd).setWidth 64 = va ∧ (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
          s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ s1.status = s.status) E s := by
        simpa [movW, movD] using wp_optMovW .W64 s rd rs hpa.2
      refine Program.wp.append hpre ?_
      rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_bswap64 s1 rd)) ?_
      rintro s2 rfl
      refine ⟨⟨by decide,
          by rw [Reg64s.get64_set64_same, BitVec.setWidth_eq, ← hrd1, BitVec.setWidth_eq]⟩,
        hm1, x64_frame_of_eq ?_ hz1 (updFlags_of_status_eq hst1 _)⟩
      intro r hr; simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
    | vec _ => simp [opBswapIns] at hc

theorem opBswap_zero32_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec 32} {s : MachineData}
    (hc : opBswapIns 32 pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits 32) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd (bswapBits va) clob s) E s := by
  cases pa with
  | imm ca =>
    simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp
      (fallsTo_moviD s rd ((bswapBits ca).setWidth 64))) ?_
    rintro s' rfl
    exact OpPostZ.of_set64 (setWidth_64_setWidth .W32 _) (fun _ _ => rfl)
      (updFlags_of_status_eq rfl _)
  | gpr rs =>
    simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    have hpre : _root_.Program.wp (if rs == rd then [] else [movlD rd rs]) (fun s1 =>
        (s1.regs.get64 rd).setWidth 32 = va ∧ (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
        s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ s1.status = s.status) E s := by
      simpa [movW, movlD] using wp_optMovW .W32 s rd rs hpa.2
    refine Program.wp.append hpre ?_
    rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_bswap32 s1 rd)) ?_
    rintro s2 rfl
    refine ⟨⟨⟨by decide, by rw [Reg64s.get64_set64_same, setWidth_64_setWidth .W32, hrd1]⟩,
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_of_status_eq hst1 _)⟩, fun _ _ => by
      rw [Reg64s.get64_set64_same, hrd1]⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  | vec _ => simp [opBswapIns] at hc

private theorem opNeg_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opNegIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c)
      (fun s' => OpPostZ z32 w rd (-va) clob s s' ∧
        (clob ≠ maskNone → s'.status.zf = decide (-va = 0#w.bits))) E s := by
  cases pa with
  | imm ca =>
    simp only [opNegIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((-ca).setWidth 64))) ?_
    rintro s' rfl
    exact ⟨OpPostZ.of_set64 (setWidth_64_setWidth w _) (fun _ _ => rfl)
      (updFlags_of_status_eq rfl _), fun h => absurd rfl h⟩
  | gpr rs =>
    simp only [opNegIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    refine Program.wp.append (wp_optMovW w s rd rs hpa.2) ?_
    rintro s1 ⟨hrd1, hr1, hm1, hz1, _⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_negW_z w s1 rd)) ?_
    rintro s2 ⟨rv, st, hrv, hrvz, hzf, rfl⟩
    refine ⟨⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩, fun _ hw => by
      rw [Reg64s.get64_set64_same, hrvz hw, hrd1]⟩, fun _ => by simpa [hrd1] using hzf⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  | vec _ => simp [opNegIns] at hc

theorem opNeg_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opNegIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (-va) clob s) E s :=
  Program.wp.mono (opNeg_z false w hc hpa) fun _ h => h.1.1

theorem opNeg_zero32_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec 32} {s : MachineData}
    (hc : opNegIns .W32 pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits 32) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd (-va) clob s) E s :=
  Program.wp.mono (opNeg_z true .W32 hc hpa) fun _ h => h.1

theorem opNeg_aluZero_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hcl : clob ≠ maskNone)
    (hc : opNegIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c)
      (fun s' => OpPost1 (.bits w.bits) rd (-va) clob s s' ∧
        (w = .W32 → x64Mach.getGpr s' rd = (-va).setWidth 64) ∧
        FlagCmpOk x64Mach x64Gpr s' (-va) 0#w.bits true) E s :=
  Program.wp.mono (opNeg_z (decide (w = .W32)) w hc hpa) fun _ ⟨h1, hzf⟩ =>
    ⟨h1.1, fun hw => by subst hw; exact h1.2 rfl rfl, x64FlagCmpOk_of_zf (hzf hcl)⟩

private theorem opNot_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opNotIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ z32 w rd (~~~va) clob s) E s := by
  cases pa with
  | imm ca =>
    simp only [opNotIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((~~~ca).setWidth 64))) ?_
    rintro s' rfl
    exact OpPostZ.of_set64 (setWidth_64_setWidth w _) (fun _ _ => rfl)
      (updFlags_of_status_eq rfl _)
  | gpr rs =>
    simp only [opNotIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    refine Program.wp.append (wp_optMovW w s rd rs hpa.2) ?_
    rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_notW_z w s1 rd)) ?_
    rintro s2 ⟨rv, hrv, hrvz, rfl⟩
    refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_of_status_eq hst1 _)⟩, fun _ hw => by
      rw [Reg64s.get64_set64_same, hrvz hw, hrd1]⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  | vec _ => simp [opNotIns] at hc

theorem opNot_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opNotIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (~~~va) clob s) E s :=
  Program.wp.mono (opNot_z false w hc hpa) fun _ h => h.1

theorem opNot_zero32_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec 32} {s : MachineData}
    (hc : opNotIns .W32 pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits 32) pa va) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd (~~~va) clob s) E s :=
  opNot_z true .W32 hc hpa

end LeanQbe.T.Amd64
