module

public import LeanQbe.T.Amd64.IselLemmas1

/-!
# x64 Scalar `GprTarget` Proofs — Part 2 (`T8`)

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
      (· = { s with regs := (s.regs.set64 rd ((((s.regs.get64 rs).setWidth 8).signExtend w.bits).setWidth 64)) }) := by
  intro _ _ _ _ _ hk
  rcases hw with rfl | rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set, BitVec.zeroExtend_eq_setWidth, Width.bits]
    exact hk _ rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set, Width.bits]
    exact hk _ rfl

theorem fallsTo_movsx16 (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (insW w (.movsx (.reg (regW w rd)) (.reg (h16 rs)))) s
      (· = { s with regs := (s.regs.set64 rd ((((s.regs.get64 rs).setWidth 16).signExtend w.bits).setWidth 64)) }) := by
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
      ∃ status, s' = { s with regs := (s.regs.set64 rd
        ((s.regs.get64 rd).replaceLow ((s.regs.get64 rd).setWidth 8 &&& (s.regs.get64 rs).setWidth 8))), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, Reg64s.set, Effects.All]; intro _; exact hk _ ⟨_, rfl⟩

theorem fallsTo_or8 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins8 (.or (.reg (b8 rd)) (.reg (b8 rs)))) s (fun s' =>
      ∃ status, s' = { s with regs := (s.regs.set64 rd
        ((s.regs.get64 rd).replaceLow ((s.regs.get64 rd).setWidth 8 ||| (s.regs.get64 rs).setWidth 8))), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, Reg64s.set, Effects.All]; intro _; exact hk _ ⟨_, rfl⟩

theorem fallsTo_xor8 (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (ins8 (.xor (.reg (b8 rd)) (.reg (b8 rs)))) s (fun s' =>
      ∃ status, s' = { s with regs := (s.regs.set64 rd
        ((s.regs.get64 rd).replaceLow ((s.regs.get64 rd).setWidth 8 ^^^ (s.regs.get64 rs).setWidth 8))), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, Reg64s.set, Effects.All]; intro _; exact hk _ ⟨_, rfl⟩

theorem fallsTo_xor8_one (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (ins8 (.xor (.reg (b8 rd)) (.imm (.int64 1)))) s (fun s' =>
      ∃ status, s' = { s with regs := (s.regs.set64 rd
        ((s.regs.get64 rd).replaceLow ((s.regs.get64 rd).setWidth 8 ^^^ 1#8))), status }) := by
  intro _ _ _ _ _ hk; simp only [t_step_simp, Reg64s.set, Effects.All]; intro _; exact hk _ ⟨_, rfl⟩

theorem exists_setRegW_state (w : Width) (s : MachineData) (rd : Reg64) (v : w.type)
    (st : StatusFlags) :
    ∃ rv status, rv.setWidth w.bits = v ∧
      ({ s with regs := s.regs.set (regW w rd) v, status := st } : MachineData) =
        { s with regs := s.regs.set64 rd rv, status } := by
  cases w <;> simp only [regW, Reg64s.set]
  · exact ⟨_, st, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  · exact ⟨_, st, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  · exact ⟨_, st, by simp [Width.bits], rfl⟩
  · exact ⟨_, st, rfl, rfl⟩

theorem fallsTo_negW (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.neg (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = -((s.regs.get64 rd).setWidth w.bits) ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, regW, t_step_simp] <;> exact hk _ (exists_setRegW_state _ s rd _ _)

theorem fallsTo_notW (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.not (.reg (regW w rd)))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = ~~~((s.regs.get64 rd).setWidth w.bits) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, regW, t_step_simp, Reg64s.set]
  · exact hk _ ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  · exact hk _ ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  · exact hk _ ⟨_, by simp [Width.bits], rfl⟩
  · exact hk _ ⟨_, rfl, rfl⟩

theorem fallsTo_incW (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.inc (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = (s.regs.get64 rd).setWidth w.bits + 1#w.bits ∧
        status.cf = s.status.cf ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, regW, t_step_simp, Reg64s.set, StatusFlags.from_result] <;>
    refine hk _ ⟨_, _, ?_, ?_, rfl⟩
  · rw [replaceLow_setWidth_le (by decide)]; rfl
  · rfl
  · rw [replaceLow_setWidth_le (by decide)]; rfl
  · rfl
  · simp [Width.bits]
  · rfl
  · rfl
  · rfl

theorem fallsTo_decW (w : Width) (s : MachineData) (rd : Reg64) :
    Directive.FallsTo (insW w (.dec (.reg (regW w rd)))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = (s.regs.get64 rd).setWidth w.bits - 1#w.bits ∧
        status.cf = s.status.cf ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  cases w <;> simp only [insW, regW, t_step_simp, Reg64s.set, StatusFlags.from_result] <;>
    refine hk _ ⟨_, _, ?_, ?_, rfl⟩
  · rw [replaceLow_setWidth_le (by decide)]; rfl
  · rfl
  · rw [replaceLow_setWidth_le (by decide)]; rfl
  · rfl
  · simp [Width.bits]
  · rfl
  · rfl
  · rfl

theorem fallsTo_leaDisp (w : Width) (hw : w = .W32 ∨ w = .W64) (s : MachineData)
    (rd rb : Reg64) (off : Int64) :
    Directive.FallsTo (insW w (.lea (regW w rd) (atDisp rb off))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = (s.regs.get64 rb).setWidth w.bits + off.toBitVec.setWidth w.bits ∧
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
    exact hk _ ⟨_, by simp [Width.bits], rfl⟩
  · simp only [insW, regW, t_step_simp, Reg64s.set, atDisp_interp]
    exact hk _ ⟨_, by simp [Width.bits, BitVec.setWidth_eq], rfl⟩

theorem fallsTo_aluBinIns_reg (w : Width) (k : AluBinKind) (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (aluBinIns w k rd (.reg (regW w rs))) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = k.eval ((s.regs.get64 rd).setWidth w.bits)
        ((s.regs.get64 rs).setWidth w.bits) ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  cases k with
  | add =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp] <;>
      refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals rw [BitVec.add_comm]; exact exists_setRegW_state _ s rd _ _
  | sub =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp] <;>
      refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals exact exists_setRegW_state _ s rd _ _
  | and =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals exact exists_setRegW_state _ s rd _ _
  | or =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals exact exists_setRegW_state _ s rd _ _
  | xor =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [AluBinKind.eval, Width.bits]
    all_goals exact exists_setRegW_state _ s rd _ _
  | mul =>
    cases w with
    | W8 =>
      simp only [aluBinIns, regW, t_step_simp, Reg.base, Effects.All]
      intro _ _ _ _; refine hk _ ⟨_, _, ?_, rfl⟩
      rw [BitVec.zeroExtend_eq_setWidth, Width.bits, BitVec.setWidth_setWidth_of_le _ (by decide),
        setWidth_mul_le (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_setWidth_of_le _ (by decide), AluBinKind.eval, BitVec.mul_comm]
    | W16 | W32 | W64 =>
      simp only [aluBinIns, regW, t_step_simp, Effects.All]
      intro _ _ _ _; refine hk _ ?_; simp only [AluBinKind.eval, Width.bits, BitVec.mul_comm]
      exact exists_setRegW_state _ s rd _ _

theorem fallsTo_aluBinIns_imm (w : Width) (k : AluBinKind) (s : MachineData) (rd : Reg64)
    (cb : BitVec w.bits) :
    Directive.FallsTo (aluBinIns w k rd (immBitsOp w cb)) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = k.eval ((s.regs.get64 rd).setWidth w.bits) cb ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hk
  have h8 : ∀ (x : BitVec 8), BitVec.truncate 8 (Int64.ofBitVec (BitVec.signExtend 64 x)).toBitVec = x :=
    fun x => by rw [Int64.toBitVec_ofBitVec]; exact truncate_signExtend_64 (by decide) x
  have h16 : ∀ (x : BitVec 16), BitVec.truncate 16 (Int64.ofBitVec (BitVec.signExtend 64 x)).toBitVec = x :=
    fun x => by rw [Int64.toBitVec_ofBitVec]; exact truncate_signExtend_64 (by decide) x
  have h32 : ∀ (x : BitVec 32), BitVec.truncate 32 (Int64.ofBitVec (BitVec.signExtend 64 x)).toBitVec = x :=
    fun x => by rw [Int64.toBitVec_ofBitVec]; exact truncate_signExtend_64 (by decide) x
  have h64 : ∀ (x : BitVec 64), BitVec.truncate 64 (Int64.ofBitVec (BitVec.signExtend 64 x)).toBitVec = x :=
    fun x => by rw [Int64.toBitVec_ofBitVec]; exact truncate_signExtend_64 (by decide) x
  cases k with
  | add =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp] <;>
      refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); rw [BitVec.add_comm]; exact exists_setRegW_state _ s rd _ _
  | sub =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp] <;>
      refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); exact exists_setRegW_state _ s rd _ _
  | and =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); exact exists_setRegW_state _ s rd _ _
  | or =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); exact exists_setRegW_state _ s rd _ _
  | xor =>
    cases w <;> simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All] <;>
      intro _ <;> refine hk _ ?_ <;> simp only [Width.bits, AluBinKind.eval]
    all_goals (first | rw [h8] | rw [h16] | rw [h32] | rw [h64]); exact exists_setRegW_state _ s rd _ _
  | mul =>
    cases w with
    | W8 =>
      simp only [aluBinIns, immBitsOp, t_step_simp, Int64.toBitVec_ofBitVec, Effects.All]
      intro _ _ _ _; refine hk _ ⟨_, _, ?_, rfl⟩
      have hcb : (cb.signExtend 64).setWidth 8 = cb := by
        rw [← BitVec.truncate_eq_setWidth]; exact truncate_signExtend_64 (by decide) cb
      dsimp only [Width.bits, AluBinKind.eval]
      rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide),
        setWidth_mul_le (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_setWidth_of_le _ (by decide), hcb, BitVec.mul_comm]
    | W16 | W32 | W64 =>
      simp only [aluBinIns, immBitsOp, regW, t_step_simp, Effects.All]
      intro _ _ _ _; refine hk _ ?_; simp only [AluBinKind.eval, Width.bits]
      first
      | (rw [h16, BitVec.mul_comm]; exact exists_setRegW_state .W16 s rd _ _)
      | (rw [h32, BitVec.mul_comm]; exact exists_setRegW_state .W32 s rd _ _)
      | (rw [h64, BitVec.setWidth_eq, BitVec.mul_comm]; exact exists_setRegW_state .W64 s rd _ _)

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
      (· = { s with regs := s.regs.set64 rd ((bswapBits ((s.regs.get64 rd).setWidth 32)).setWidth 64) }) := by
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

theorem opCopyBits_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opCopyBitsIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd va clob s) E s := by
  cases pa with
  | gpr rs =>
    simp only [opCopyBitsIns] at hc; split at hc
    · rename_i hrs; have := (beq_reg64_iff rs rd).1 hrs; subst this
      simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      exact _root_.Program.wp_nil ⟨hpa, rfl, Machine.Frame.refl _ _ _ _ _⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w s rd rs)) ?_
      rintro s' rfl
      exact OpPost1.of_set64_bits (by rw [setWidth_64_setWidth, hpa.2]) (updFlags_of_status_eq rfl _)
  | imm ca =>
    simp only [opCopyBitsIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (ca.setWidth 64))) ?_
    rintro s' rfl
    exact OpPost1.of_set64_bits (setWidth_64_setWidth w ca) (updFlags_of_status_eq rfl _)
  | vec _ => simp [opCopyBitsIns] at hc

theorem opPostDst_gpr_bool {rd : Reg64} {rv : BitVec 64} {st : StatusFlags}
    {clob : FlagMask} {s : MachineData} {b : Bool}
    (hrv : rv.setWidth 8 = BitVec.ofNat 8 b.toNat)
    (hup : x64Mach.UpdFlags x64CondReads s { s with regs := s.regs.set64 rd rv, status := st } clob) :
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
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (BitVec.ofNat 64 b0.toNat))) ?_
      rintro s' rfl
      exact opPostDst_gpr_bool (by cases b0 <;> rfl) (updFlags_of_status_eq rfl _)
    | flag cc =>
      simp only [opCopyBoolIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      have hcc : cc.interp s.status = b := hpa
      refine Program.wp.mono (wp_setccMove s rd cc) ?_
      rintro s' rfl
      exact opPostDst_gpr_bool (by rw [hcc]; cases b <;> rfl) (updFlags_of_status_eq rfl _)
    | vec _ => simp [opCopyBoolIns] at hc

theorem opBoolBin_spec [Host] {E : Int64 → MachineData → Prop} (op : Bool → Bool → Bool)
    (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (h8 : ∀ (s : MachineData), Directive.FallsTo (ins8 (insFn (.reg (b8 .r11)) (.reg (b8 .r10)))) s
      (fun s' => ∃ rv status,
        (∀ a b : Bool, (s.regs.get64 .r11).setWidth 8 = BitVec.ofNat 8 a.toNat →
          (s.regs.get64 .r10).setWidth 8 = BitVec.ofNat 8 b.toNat →
          rv.setWidth 8 = BitVec.ofNat 8 (op a b).toNat) ∧
        s' = { s with regs := s.regs.set64 .r11 rv, status }))
    {pa pb : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Instr} {clob : FlagMask} {a b : Bool} {s : MachineData}
    (hc : opBoolBinIns op insFn pa pb pd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa a) (hpb : x64Mach.PArgHolds s .bool pb b)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch) :
    _root_.Program.wp (emitClean c) (OpPostDst1 .bool pd (op a b) clob s) E s := by
  cases pd with
  | flag _ | vec _ => simp [opBoolBinIns] at hc
  | gpr rd =>
    have hbody (d1 d2 : Instr) (hd1 : boolArgTo8I .r11 pa = some d1)
        (hd2 : boolArgTo8I .r10 pb = some d2)
        (heq : [d1, d2, x64InsI .W8 (insFn (.reg (b8 .r11)) (.reg (b8 .r10))),
          x64InsI .W32 (.movzx (.reg (d rd)) (.reg (b8 .r11)))] = c) (hcl : maskAll = clob) :
        _root_.Program.wp (emitClean c) (OpPostDst1 .bool (.gpr rd) (op a b) clob s) E s := by
      subst heq; subst hcl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_boolArgTo8 s .r11 hd1 hpa)) ?_
      rintro s1 ⟨rv11, hrv11, rfl⟩
      have hpb1 : x64Mach.PArgHolds { s with regs := s.regs.set64 .r11 rv11 } .bool pb b := by
        cases pb with
        | gpr rx =>
          have hrx := ne_of_not_mem_x64Scratch (hargs rx (by simp [PArg.gprs]))
          dsimp only [Machine.PArgHolds, GprHolds] at hpb ⊢
          rw [Reg64s.get64_set64_of_ne _ .r11 rx _ hrx.2.symm]
          exact hpb
        | imm _ | flag _ => exact hpb
        | vec _ => simp [boolArgTo8I] at hd2
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_boolArgTo8 _ .r10 hd2 hpb1)) ?_
      rintro s2 ⟨rv10, hrv10, rfl⟩
      refine Program.wp.cons (Directive.FallsTo.wp (h8 _)) ?_
      rintro s3 ⟨rv', st', hrvs, rfl⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 _ rd .r11)) ?_
      rintro s4 rfl
      have hr11_2 : (((s.regs.set64 .r11 rv11).set64 .r10 rv10).get64 .r11).setWidth 8 =
          BitVec.ofNat 8 a.toNat := by
        rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same, hrv11]
      have hr10_2 : (((s.regs.set64 .r11 rv11).set64 .r10 rv10).get64 .r10).setWidth 8 =
          BitVec.ofNat 8 b.toNat := by rw [Reg64s.get64_set64_same, hrv10]
      have hr11_3 : rv'.setWidth 8 = BitVec.ofNat 8 (op a b).toNat := by
        simpa [Reg64s.get64_set64_same] using hrvs a b hr11_2 hr10_2
      refine ⟨?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩
      · dsimp only [Machine.PDstHolds, GprHolds]
        rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (by decide),
          Reg64s.get64_set64_same, hr11_3, BitVec.setWidth_eq]
      · intro r hr
        simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs,
          List.singleton_append, List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
          Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
          Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1),
          Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1)]
    have hbind (hd : (boolArgTo8I .r11 pa >>= fun d1 =>
        boolArgTo8I .r10 pb >>= fun d2 =>
        some ([d1, d2, x64InsI .W8 (insFn (.reg (b8 .r11)) (.reg (b8 .r10))),
               x64InsI .W32 (.movzx (.reg (d rd)) (.reg (b8 .r11)))], maskAll)) = some (c, clob)) :
        _root_.Program.wp (emitClean c) (OpPostDst1 .bool (.gpr rd) (op a b) clob s) E s := by
      rcases Option.bind_eq_some_iff.mp hd with ⟨d1, hd1, hd'⟩
      rcases Option.bind_eq_some_iff.mp hd' with ⟨d2, hd2, hd''⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hd''
      exact hbody d1 d2 hd1 hd2 hd''.1 hd''.2
    cases pa with
    | imm a0 =>
      cases pb with
      | imm b0 =>
        simp only [opBoolBinIns, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl; rcases hpb with rfl
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
        rintro s' rfl
        exact opPostDst_gpr_bool (by cases op a0 b0 <;> rfl) (updFlags_of_status_eq rfl _)
      | gpr _ | flag _ | vec _ => exact hbind hc
    | gpr _ | flag _ | vec _ => exact hbind hc

theorem opBoolNot_spec [Host] {E : Int64 → MachineData → Prop}
    {pa : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Instr} {clob : FlagMask} {a : Bool} {s : MachineData}
    (hc : opBoolNotIns pa pd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa a) :
    _root_.Program.wp (emitClean c) (OpPostDst1 .bool pd (!a) clob s) E s := by
  cases pd with
  | flag _ | vec _ => simp [opBoolNotIns] at hc
  | gpr rd =>
    cases pa with
    | imm b0 =>
      simp only [opBoolNotIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
      rintro s' rfl
      exact opPostDst_gpr_bool (by cases b0 <;> rfl) (updFlags_of_status_eq rfl _)
    | vec _ => simp [opBoolNotIns, boolArgTo8I] at hc
    | gpr _ | flag _ =>
      simp only [opBoolNotIns, Option.bind_eq_bind] at hc
      rcases Option.bind_eq_some_iff.mp hc with ⟨d1, hd1, hc'⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hc'
      rcases hc' with ⟨rfl, rfl⟩
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_boolArgTo8 s .r11 hd1 hpa)) ?_
      rintro s1 ⟨rv11, hrv11, rfl⟩
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_xor8_one _ .r11)) ?_
      rintro s2 ⟨st', rfl⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 _ rd .r11)) ?_
      rintro s3 rfl
      have hx : (((s.regs.set64 .r11 rv11).get64 .r11).setWidth 8 ^^^ 1#8) =
          BitVec.ofNat 8 (!a).toNat := by rw [Reg64s.get64_set64_same, hrv11]; cases a <;> rfl
      refine ⟨?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩
      · dsimp only [Machine.PDstHolds, GprHolds]
        rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (by decide),
          Reg64s.get64_set64_same, replaceLow_setWidth_le (by decide), hx, BitVec.setWidth_eq]
      · intro r hr
        simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs,
          List.singleton_append, List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
          Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
          Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1)]

theorem opOfBool_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode .bool} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {b : Bool} {s : MachineData}
    (hc : opOfBoolIns pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s .bool pa b) :
    _root_.Program.wp (emitClean c)
      (OpPost1 (.bits w.bits) rd (BitVec.ofNat w.bits b.toNat) clob s) E s := by
  cases pa with
  | gpr rs =>
    simp only [opOfBoolIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 s rd rs)) ?_
    rintro s' rfl
    exact OpPost1.of_set64_bits
      (by rw [hpa, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]; cases w <;> cases b <;> rfl)
      (updFlags_of_status_eq rfl _)
  | imm b0 =>
    simp only [opOfBoolIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (BitVec.ofNat 64 b0.toNat))) ?_
    rintro s' rfl
    exact OpPost1.of_set64_bits (by cases w <;> cases b0 <;> rfl) (updFlags_of_status_eq rfl _)
  | flag cc =>
    simp only [opOfBoolIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    have hcc : cc.interp s.status = b := hpa
    refine Program.wp.mono (wp_setccMove s rd cc) ?_
    rintro s' rfl
    exact OpPost1.of_set64_bits (by rw [hcc]; cases w <;> cases b <;> rfl) (updFlags_of_status_eq rfl _)
  | vec _ => simp [opOfBoolIns] at hc

private theorem opExt_bounds {m n : Nat} (h : x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n = true) :
    (m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64) ∧ (n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) ∧ m < n ∧ n ≤ 64 := by
  simp only [Bool.and_eq_true, x64BitWidths, List.contains_eq_mem, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false, Nat.ble_eq] at h
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem opZext_spec [Host] {E : Int64 → MachineData → Prop} (m n : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hc : opZextIns m n pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    m ≤ n ∧ _root_.Program.wp (emitClean c) (OpPost1 (.bits n) rd (va.setWidth n) clob s) E s := by
  cases hmnb : x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n with
  | false => unfold opZextIns at hc; rw [hmnb] at hc; cases hc
  | true =>
    obtain ⟨hm, hn, hlt, hle64⟩ := opExt_bounds hmnb
    refine ⟨Nat.le_of_lt hlt, ?_⟩
    unfold opZextIns at hc; rw [hmnb] at hc
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
    have finish (rv : BitVec 64) (hrv : rv.setWidth n = va.setWidth n)
        {s' : MachineData} (hs' : s' = { s with regs := s.regs.set64 rd rv }) :
        OpPost1 (.bits n) rd (va.setWidth n) maskNone s s' := by
      subst hs'
      refine ⟨⟨hle64, by rw [Reg64s.get64_set64_same, hrv]⟩, rfl, x64_frame_of_eq ?_ rfl (updFlags_of_status_eq rfl _)⟩
      intro r hr; simp only [List.mem_cons, not_or] at hr; exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
    cases pa with
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (ca.setWidth 64))) ?_
      rintro s' rfl; exact finish _ (BitVec.setWidth_setWidth_of_le _ hle64) rfl
    | gpr rs =>
      rcases hm with rfl | rfl | rfl | rfl <;> try (exfalso; omega)
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx8 s rd rs)) ?_
        rintro s' rfl; exact finish _ (by rw [hpa.2, BitVec.setWidth_setWidth_of_le _ hle64]) rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movzx16 s rd rs)) ?_
        rintro s' rfl; exact finish _ (by rw [hpa.2, BitVec.setWidth_setWidth_of_le _ hle64]) rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movlD s rd rs)) ?_
        rintro s' rfl
        exact finish _ (by rw [hpa.2, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ hle64]) rfl
    | vec _ => simp at hc

theorem opSext_spec [Host] {E : Int64 → MachineData → Prop} (m n : Nat)
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec m} {s : MachineData}
    (hc : opSextIns m n pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits m) pa va) :
    m ≤ n ∧
      _root_.Program.wp (emitClean c) (OpPost1 (.bits n) rd (va.signExtend n) clob s) E s := by
  cases hmnb : x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n with
  | false => unfold opSextIns at hc; rw [hmnb] at hc; cases hc
  | true =>
    obtain ⟨hm, hn, hlt, hle64⟩ := opExt_bounds hmnb
    refine ⟨Nat.le_of_lt hlt, ?_⟩
    unfold opSextIns at hc; rw [hmnb] at hc
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
    have finish (rv : BitVec 64) (hrv : rv.setWidth n = va.signExtend n)
        {s' : MachineData} (hs' : s' = { s with regs := s.regs.set64 rd rv }) :
        OpPost1 (.bits n) rd (va.signExtend n) maskNone s s' := by
      subst hs'
      refine ⟨⟨hle64, by rw [Reg64s.get64_set64_same, hrv]⟩, rfl, x64_frame_of_eq ?_ rfl (updFlags_of_status_eq rfl _)⟩
      intro r hr; simp only [List.mem_cons, not_or] at hr; exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
    cases pa with
    | imm ca =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((ca.signExtend n).setWidth 64))) ?_
      rintro s' rfl; exact finish _ (by rw [BitVec.setWidth_setWidth_of_le _ hle64, BitVec.setWidth_eq]) rfl
    | gpr rs =>
      rcases hm with rfl | rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl | rfl <;> try (exfalso; omega)
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx8 .W32 (.inl rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish ((va.signExtend 32).setWidth 64)
          (by rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
              exact setWidth_signExtend_of_le (by decide) (by decide) va) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx8 .W32 (.inl rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish ((va.signExtend 32).setWidth 64)
          (by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx8 .W64 (.inr rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish (va.signExtend 64) (BitVec.setWidth_eq _) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx16 .W32 (.inl rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish ((va.signExtend 32).setWidth 64)
          (by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx16 .W64 (.inr rfl) s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish (va.signExtend 64) (BitVec.setWidth_eq _) hs'
      · refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movsx32 s rd rs)) ?_
        rintro s' hs'; rw [hpa.2] at hs'
        exact finish (va.signExtend 64) (BitVec.setWidth_eq _) hs'
    | vec _ => simp at hc

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
        simp only [Option.some.injEq, Prod.mk.injEq] at harm; rcases harm with ⟨rfl, rfl⟩; rcases hpa' with rfl
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((ca.setWidth w.bits).setWidth 64))) ?_
        rintro s' rfl; exact OpPost1.of_set64_bits (setWidth_64_setWidth w _) (updFlags_of_status_eq rfl _)
      | gpr rs =>
        by_cases hrr : rs == rd
        · have heq := (beq_reg64_iff rs rd).1 hrr; subst rs
          simp only [hrr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at harm; rcases harm with ⟨rfl, rfl⟩
          refine _root_.Program.wp_nil ⟨(GprHolds.bits_iff w _ _).2 ?_, rfl, Machine.Frame.refl _ _ _ _ _⟩
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
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((bswapBits ca).setWidth 64))) ?_
      rintro s' rfl; exact OpPost1.of_set64_bits (setWidth_64_setWidth .W16 _) (updFlags_of_status_eq rfl _)
    | gpr rs =>
      simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
      simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
      refine Program.wp.append (wp_optMovW .W16 s rd rs hpa.2) ?_
      rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_rolw8 s1 rd)) ?_
      rintro s2 ⟨rv, st, hrv, hpf, hzf, hsf, rfl⟩
      refine ⟨⟨by decide, by rw [Reg64s.get64_set64_same, hrv, hrd1]⟩, hm1, x64_frame_of_eq ?_ hz1 ?_⟩
      · intro r hr; simp only [List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
      · exact updFlags_maskCF_OF (by rw [hpf, hst1]) (by rw [hzf, hst1]) (by rw [hsf, hst1])
    | vec _ => simp [opBswapIns] at hc
  · cases pa with
    | imm ca =>
      simp only [opBswapIns, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((bswapBits ca).setWidth 64))) ?_
      rintro s' rfl; exact OpPost1.of_set64_bits (setWidth_64_setWidth .W32 _) (updFlags_of_status_eq rfl _)
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
      rintro s' rfl; exact OpPost1.of_set64_bits (w := .W64) (BitVec.setWidth_eq _) (updFlags_of_status_eq rfl _)
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
      refine ⟨⟨by decide, by rw [Reg64s.get64_set64_same, BitVec.setWidth_eq, ← hrd1, BitVec.setWidth_eq]⟩,
        hm1, x64_frame_of_eq ?_ hz1 (updFlags_of_status_eq hst1 _)⟩
      intro r hr; simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
    | vec _ => simp [opBswapIns] at hc

theorem opNeg_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opNegIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (-va) clob s) E s := by
  cases pa with
  | imm ca =>
    simp only [opNegIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((-ca).setWidth 64))) ?_
    rintro s' rfl; exact OpPost1.of_set64_bits (setWidth_64_setWidth w _) (updFlags_of_status_eq rfl _)
  | gpr rs =>
    simp only [opNegIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    refine Program.wp.append (wp_optMovW w s rd rs hpa.2) ?_
    rintro s1 ⟨hrd1, hr1, hm1, hz1, _⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_negW w s1 rd)) ?_
    rintro s2 ⟨rv, st, hrv, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  | vec _ => simp [opNegIns] at hc

theorem opNot_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va : BitVec w.bits} {s : MachineData}
    (hc : opNotIns w pa rd = some (c, clob))
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (~~~va) clob s) E s := by
  cases pa with
  | imm ca =>
    simp only [opNotIns, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((~~~ca).setWidth 64))) ?_
    rintro s' rfl; exact OpPost1.of_set64_bits (setWidth_64_setWidth w _) (updFlags_of_status_eq rfl _)
  | gpr rs =>
    simp only [opNotIns, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
    simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    refine Program.wp.append (wp_optMovW w s rd rs hpa.2) ?_
    rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_notW w s1 rd)) ?_
    rintro s2 ⟨rv, hrv, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_of_status_eq hst1 _)⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  | vec _ => simp [opNotIns] at hc

/-! ## 5. `op_spec` Lemma: `opBin` -/

theorem AluBinKind.comm_eq {k : AluBinKind} (hk : k.isComm = true) {n : Nat} (a b : BitVec n) :
    k.eval a b = k.eval b a := by
  cases k <;> simp only [AluBinKind.isComm, AluBinKind.eval, reduceCtorEq] at hk ⊢
  · exact BitVec.add_comm a b
  · exact BitVec.and_comm a b
  · exact BitVec.or_comm a b
  · exact BitVec.xor_comm a b
  · exact BitVec.mul_comm a b

private theorem opBin_regImm_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
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
      (OpPost1 (.bits w.bits) rd (k.eval va cb) pair.2 s) E s := by
  intro pre pair
  have hrd10 := (ne_of_not_mem_x64Scratch hrd).1
  have hra10 := (ne_of_not_mem_x64Scratch hra_g).1
  dsimp only [pair, pre]
  split
  · simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    refine Program.wp.append (wp_optMovW w s rd ra hra) ?_
    rintro s1 ⟨hrd1, hr1, hm1, hz1, _⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_imm w k s1 rd cb)) ?_
    rintro s2 ⟨rv, st, hrv, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  · simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cb.setWidth 64))) ?_
    rintro s1 rfl
    have hra1 : ((s.regs.set64 .r10 (cb.setWidth 64)).get64 ra).setWidth w.bits = va := by
      rw [Reg64s.get64_set64_of_ne _ .r10 ra _ hra10.symm, hra]
    refine Program.wp.append (wp_optMovW w { s with regs := s.regs.set64 .r10 (cb.setWidth 64) } rd ra hra1) ?_
    rintro s2 ⟨hrd2, hr2, hm2, hz2, _⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_reg w k s2 rd .r10)) ?_
    rintro s3 ⟨rv, st, hrv, rfl⟩
    have h10 : (s2.regs.get64 .r10).setWidth w.bits = cb := by
      rw [hr2 .r10 hrd10.symm, Reg64s.get64_set64_same, setWidth_64_setWidth]
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd2, h10]),
      hm2, x64_frame_of_eq ?_ hz2 (updFlags_maskAll _ _)⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr2 r hr.1,
      Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1)]

private theorem opBin_incDec_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (isInc : Bool) (ra rd : Reg64) (va : BitVec w.bits) (s : MachineData)
    (hra : (s.regs.get64 ra).setWidth w.bits = va) :
    let pre : List Instr := if ra == rd then [] else [movWI w rd ra]
    let d : Instr := x64InsI w (if isInc then .inc (.reg (regW w rd)) else .dec (.reg (regW w rd)))
    let res := if isInc then va + 1#w.bits else va - 1#w.bits
    _root_.Program.wp (emitClean (pre ++ [d]))
      (OpPost1 (.bits w.bits) rd res maskDecInc s) E s := by
  intro pre d res; dsimp only [pre, d, res]
  simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
  refine Program.wp.append (wp_optMovW w s rd ra hra) ?_
  rintro s1 ⟨hrd1, hr1, hm1, hz1, hst1⟩
  cases isInc
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_decW w s1 rd)) ?_
    rintro s2 ⟨rv, st, hrv, hcf, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskDecInc (by rw [hcf, hst1]))⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
  · simp only [↓reduceIte]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_incW w s1 rd)) ?_
    rintro s2 ⟨rv, st, hrv, hcf, rfl⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
      hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskDecInc (by rw [hcf, hst1]))⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]

theorem opBin_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (k : AluBinKind)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {vh : VariantHint}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opBinIns w k pa pb rd vh = some (c, clob))
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (k.eval va vb) clob s) E s := by
  have hdisp_spec (off : Int64) (hwf : ((w == .W32 || w == .W64) && fitsImm32 off.toBitVec) = true)
      (rb : Reg64) (heqv : (s.regs.get64 rb).setWidth w.bits + off.toBitVec.setWidth w.bits = k.eval va vb)
      (hc_eq : c = [x64InsI w (.lea (regW w rd) (atDisp rb off))]) (hcl : clob = maskNone) :
      _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (k.eval va vb) clob s) E s := by
    subst hc_eq; subst hcl
    simp only [emitClean_cons, emitClean_nil]
    have hw3264 : w = .W32 ∨ w = .W64 := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_width_iff] at hwf; exact hwf.1
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_leaDisp w hw3264 s rd rb off)) ?_
    rintro s' ⟨rv, hrv, rfl⟩; exact OpPost1.of_set64_bits (by rw [hrv, heqv]) (updFlags_of_status_eq rfl _)
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
        else if rb != rd then
          some ([movWI w rd ra, aluBinI w k rd (.reg (regW w rb))], maskAll)
        else
          some ([movWI w .r11 ra, aluBinI w k .r11 (.reg (regW w rb)), movWI w rd .r11], maskAll)
      | .gpr ra, .imm cb =>
        some (if w != .W64 || fitsImm32 (cb.setWidth 64) then
          ((if ra == rd then [] else [movWI w rd ra]) ++ [aluBinI w k rd (immBitsOp w cb)], maskAll)
        else
          ([moviI .r10 (cb.setWidth 64)] ++ (if ra == rd then [] else [movWI w rd ra]) ++
            [aluBinI w k rd (.reg (regW w .r10))], maskAll))
      | .imm ca, .gpr rb =>
        if k == .sub && ca == 0 then
          some ((if rb == rd then [] else [movWI w rd rb]) ++
            [x64InsI w (.neg (.reg (regW w rd)))], maskAll)
        else if k.isComm then
          some (if w != .W64 || fitsImm32 (ca.setWidth 64) then
            ((if rb == rd then [] else [movWI w rd rb]) ++
              [aluBinI w k rd (immBitsOp w ca)], maskAll)
          else
            ([moviI .r10 (ca.setWidth 64)] ++ (if rb == rd then [] else [movWI w rd rb]) ++
              [aluBinI w k rd (.reg (regW w .r10))], maskAll))
        else
          some ([moviI .r11 (ca.setWidth 64), aluBinI w .sub .r11 (.reg (regW w rb)),
                 movWI w rd .r11], maskAll)
      | _, _ => none) = some (c, clob) →
      _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd (k.eval va vb) clob s) E s := by
    intro pa' pb' va' vb' hpa' hpb' hargs' hm
    cases pa' <;> cases pb' <;> simp only at hm <;> try contradiction
    · rename_i ra rb; have hra := hpa'.2; have hrb := hpb'.2
      by_cases h1 : ra == rd
      · have h1eq := (beq_reg64_iff ra rd).1 h1; subst ra
        simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_reg w k s rd rb)) ?_
        rintro s' ⟨rv, st, hrv, rfl⟩; exact OpPost1.of_set64_bits (by rw [hrv, hra, hrb]) (updFlags_maskAll _ _)
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hm
        by_cases h2 : k.isComm && (rb == rd)
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          simp only [Bool.and_eq_true, beq_reg64_iff] at h2; rcases h2 with ⟨hcomm, hrb_eq⟩; subst rb
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_reg w k s rd ra)) ?_
          rintro s' ⟨rv, st, hrv, rfl⟩
          exact OpPost1.of_set64_bits (by rw [hrv, hrb, hra, AluBinKind.comm_eq hcomm]) (updFlags_maskAll _ _)
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hm
          by_cases h3 : (k == .sub) && (rb == rd)
          · simp only [h3, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
            simp only [emitClean_cons, emitClean_nil]
            have h3' : k = .sub ∧ rb = rd := by cases k <;> simp_all [beq_reg64_iff]
            rcases h3' with ⟨rfl, rfl⟩
            have hra_ne : ra ≠ rb := fun h => h1 ((beq_reg64_iff ra rb).2 h)
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_negW w s rb)) ?_
            rintro s1 ⟨rv1, st1, hrv1, rfl⟩
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_reg w .add _ rb ra)) ?_
            rintro s2 ⟨rv2, st2, hrv2, rfl⟩
            refine ⟨(GprHolds.bits_iff w _ _).2 ?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩
            · rw [Reg64s.get64_set64_same, hrv2, Reg64s.get64_set64_same, hrv1, hrb,
                Reg64s.get64_set64_of_ne _ rb ra _ hra_ne.symm, hra, AluBinKind.eval, AluBinKind.eval,
                BitVec.add_comm, ← BitVec.sub_eq_add_neg]
            · intro r hr; simp only [List.mem_cons, not_or] at hr
              rw [Reg64s.get64_set64_of_ne _ rb r _ (Ne.symm hr.1),
                Reg64s.get64_set64_of_ne _ rb r _ (Ne.symm hr.1)]
          · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hm
            by_cases h4 : rb != rd
            · simp only [h4, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
              simp only [emitClean_cons, emitClean_nil]
              have hrb_ne := (bne_reg64_iff rb rd).1 h4
              refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW w s rd ra)) ?_
              rintro s1 rfl
              refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinIns_reg w k _ rd rb)) ?_
              rintro s2 ⟨rv2, st2, hrv2, rfl⟩
              refine ⟨(GprHolds.bits_iff w _ _).2 ?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩
              · rw [Reg64s.get64_set64_same, hrv2, Reg64s.get64_set64_same, setWidth_64_setWidth,
                  hra, Reg64s.get64_set64_of_ne _ rd rb _ hrb_ne.symm, hrb]
              · intro r hr; simp only [List.mem_cons, not_or] at hr
                rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
                  Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
            · simp only [h4, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
              rcases hm with ⟨rfl, rfl⟩
              simp only [emitClean_cons, emitClean_nil]
              have hrb11 := (ne_of_not_mem_x64Scratch (hargs' rb (by simp [PArg.gprs]))).2
              refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW w s .r11 ra)) ?_
              rintro s1 rfl
              refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_aluBinIns_reg w k _ .r11 rb)) ?_
              rintro s2 ⟨rv2, st2, hrv2, rfl⟩
              refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ rd .r11)) ?_
              rintro s3 rfl
              refine ⟨(GprHolds.bits_iff w _ _).2 ?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩
              · rw [Reg64s.get64_set64_same, setWidth_64_setWidth, Reg64s.get64_set64_same, hrv2,
                  Reg64s.get64_set64_same, setWidth_64_setWidth, hra,
                  Reg64s.get64_set64_of_ne _ .r11 rb _ hrb11.symm, hrb]
              · intro r hr; simp only [List.mem_cons, not_or] at hr
                rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
                  Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
                  Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1)]
    · rename_i ra cb; rcases hpb' with rfl
      have hpair := @opBin_regImm_spec _ E w k ra rd cb va' s hrd (hargs' ra (by simp [PArg.gprs])) hpa'.2
      have hm' : _ = (c, clob) := Option.some.inj hm
      dsimp +zetaHave only at hpair; rw [hm'] at hpair; exact hpair
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
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_negW w s1 rd)) ?_
        rintro s2 ⟨rv, st, hrv, rfl⟩
        refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]),
          hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
        intro r hr; simp only [List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hr1 r hr.1]
      · split at hm
        · rename_i hcomm
          rw [AluBinKind.comm_eq hcomm]
          have hpair := @opBin_regImm_spec _ E w k rb rd ca vb' s hrd (hargs' rb (by simp [PArg.gprs])) hrb
          have hm' : _ = (c, clob) := Option.some.inj hm
          dsimp +zetaHave only at hpair; rw [hm'] at hpair; exact hpair
        · rename_i hnotcomm
          have hk : k = .sub := by cases k <;> simp_all [AluBinKind.isComm]
          subst hk
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          have hrb11 := (ne_of_not_mem_x64Scratch (hargs' rb (by simp [PArg.gprs]))).2
          refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r11 (ca.setWidth 64))) ?_
          rintro s1 rfl
          refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_aluBinIns_reg w .sub _ .r11 rb)) ?_
          rintro s2 ⟨rv2, st2, hrv2, rfl⟩
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ rd .r11)) ?_
          rintro s3 rfl
          refine ⟨(GprHolds.bits_iff w _ _).2 ?_, rfl, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩
          · rw [Reg64s.get64_set64_same, setWidth_64_setWidth, Reg64s.get64_set64_same, hrv2,
              Reg64s.get64_set64_same, setWidth_64_setWidth,
              Reg64s.get64_set64_of_ne _ .r11 rb _ hrb11.symm, hrb]
          · intro r hr; simp only [List.mem_cons, not_or] at hr
            rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
              Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1),
              Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1)]
    · rename_i ca cb; rcases hpa' with rfl; rcases hpb' with rfl
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd ((k.eval ca cb).setWidth 64))) ?_
      rintro s' rfl; exact OpPost1.of_set64_bits (setWidth_64_setWidth w _) (updFlags_of_status_eq rfl _)
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
          exact hdisp_spec off hwf rb (by rw [hpb.2, beq_iff_eq.mp hoff, AluBinKind.eval, BitVec.add_comm]) hc.1.symm hc.2.symm
        · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.imm ca) (.gpr rb) ca vb rfl hpb hargs hc
      · rename_i rb cb; rcases hpb with rfl
        by_cases hoff : ((-off.toBitVec).setWidth w.bits == cb) = true
        · simp only [hoff, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          have hn : off.toBitVec.setWidth w.bits = -cb := by
            rw [← beq_iff_eq.mp hoff, setWidth_neg_le (width_bits_le_64 w), BitVec.neg_neg]
          exact hdisp_spec off hwf rb (by rw [hpa.2, hn, AluBinKind.eval, BitVec.sub_eq_add_neg]) hc.1.symm hc.2.symm
        · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.gpr rb) (.imm cb) va cb hpa rfl hargs hc
    · simp only [hwf, Bool.false_eq_true, ↓reduceIte] at hc
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
        exact opBin_incDec_spec w true ra rd va s hpa.2
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases h2 : (cb == -1#w.bits) = true
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h2 with rfl
          simpa [AluBinKind.eval, BitVec.sub_eq_add_neg] using opBin_incDec_spec w false ra rd va s hpa.2
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.gpr ra) (.imm cb) va cb hpa rfl hargs hc
    · rename_i ca rb; rcases hpa with rfl
      by_cases h1 : (ca == 1#w.bits) = true
      · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h1 with rfl
        simpa [AluBinKind.eval, BitVec.add_comm] using opBin_incDec_spec w true rb rd vb s hpb.2
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hc
        exact hcore (.imm ca) (.gpr rb) ca vb rfl hpb hargs hc
    · rename_i ra cb; rcases hpb with rfl
      by_cases h1 : (cb == 1#w.bits) = true
      · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h1 with rfl
        exact opBin_incDec_spec w false ra rd va s hpa.2
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases h2 : (cb == -1#w.bits) = true
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩; rcases beq_iff_eq.mp h2 with rfl
          simpa [AluBinKind.eval, BitVec.sub_eq_add_neg, BitVec.neg_neg] using opBin_incDec_spec w true ra rd va s hpa.2
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hc
          exact hcore (.gpr ra) (.imm cb) va cb hpa rfl hargs hc

end LeanQbe.T.Amd64
