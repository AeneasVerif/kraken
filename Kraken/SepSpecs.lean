module

/-
The instruction dictionary of the separation-logic wp. Each spec is a triple
of one directive with a small footprint. A register write carries the
schematic post to the updated registers. A memory instruction owns the slot's
bytes, and its pure conjunct is the post entailment: the schematic post holds
of the slot as the instruction leaves it, at the registers and flags the
instruction produces. `Program.FrameWP.cons_spec` sequences the specs, and the frame
inference of Kraken/SepFrameProc.lean threads the post entailment into the
tail.

Every proof runs the same route: `Program.FrameWP.sep_intro` opens the triple under an
ambient frame, the `Mem.*_sep` lemmas of Kraken/SeparationMem.lean step the
machine memory under that frame, and the run ends at the directive's end.
-/
public import Kraken.X64.WP.Frame
public import Kraken.X64.Registers
public import Kraken.X64.Parser
public import Kraken.Specs

@[expose] public section

open Std.WP
open Lean.Order
open Kraken.X64.Parser
open scoped Program.FrameWP

/-- Rotate the middle assertion out: `P ∗ (Q ∗ R) = Q ∗ (P ∗ R)`. -/
theorem MProp.sep_left_comm {w : Nat} (P Q R : MProp w) :
    P ∗ (Q ∗ R) = Q ∗ (P ∗ R) := by
  rw [← MProp.sep_assoc, MProp.sep_comm P Q, MProp.sep_assoc]

namespace Program.FrameWP

variable [Host] [FunDecls] {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
  {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}

/-! ## Register instructions

A register instruction owns no memory: its spec carries the schematic post
to the updated registers and flags. -/

/-- Load an immediate into a 64-bit register. -/
@[spec] theorem mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun rg z f => Q () (rg.set64 r (BitVec.setWidth 64 i.toBitVec)) z f ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Effects.All, ite_true]
  exact hn _ (hpre)

/-! ## Memory instructions

The footprint is the slot's bytes `bs`, eight of them. The pure conjunct is
the post entailment: the schematic post holds of the slot as the instruction
leaves it, at the registers and flags it produces. -/

/-- Store a 64-bit register at `disp(base)`. -/
@[spec] theorem mov_store_reg_spec (b : Reg64) (d : Int64) (rs : Reg64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f =>
        ⌜(Int.toBytes 8 (r.get64 rs).toInt).AtM (r.get64 b + BitVec.ofInt 64 d.toInt)
            ⊑ Q () r z f⌝
          ⊓ bs.AtM (r.get64 b + BitVec.ofInt 64 d.toInt) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := (MProp.get_sep_apply_iff _ _ _).mp hpre
  obtain ⟨hpost, hbs⟩ := (MProp.get_meet_apply_iff _ _ mm).mp hM
  have hpost := (MProp.get_ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F).get s.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr
      ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
        Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload := Mem.loadInt_eq_of_AtM hown hlen (by decide)
  have hstore := Mem.get_AtM_sep_storeInt hown hlen (s.regs.get64 rs).toInt
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, ite_true]
  refine ?_
  rw [MProp.sep_comm] at hstore
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hstore)

/-- Add the 64-bit word at `disp(base)` to a register. The slot is unchanged;
the post holds at the new register and flags. -/
@[spec] theorem add_reg_mem_spec (rd b : Reg64) (d : Int64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun rg z _ =>
        let a := BitVec.ofInt 64 (Int.ofBytes bs)
        let bv := rg.get64 rd
        let v := a + bv
        ⌜bs.AtM (rg.get64 b + BitVec.ofInt 64 d.toInt)
            ⊑ Q () (rg.set64 rd v) z
                (StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + bv.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (bv.take 4).unsigned,
                    of := v.signed != a.signed + bv.signed })⌝
          ⊓ bs.AtM (rg.get64 b + BitVec.ofInt 64 d.toInt) ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := (MProp.get_sep_apply_iff _ _ _).mp hpre
  obtain ⟨hpost, hbs⟩ := (MProp.get_meet_apply_iff _ _ mm).mp hM
  have hpost := (MProp.get_ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F).get s.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr
      ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
        Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload := Mem.loadInt_eq_of_AtM hown hlen (by decide)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, ite_true]
  refine ?_
  rw [MProp.sep_comm] at hown
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hown)


/-! ## More instructions -/

/-- Copy a 64-bit register. -/
@[spec] theorem mov_reg_reg_spec (rd rs : Reg64) :
    ⦃ fun rg z f => Q () (rg.set64 rd (rg.get64 rs)) z f ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64,
    Effects.All, ite_true]
  exact hn _ (hpre)

/-- Exclusive-or of two 64-bit registers; the adjust flag is unspecified. -/
@[spec] theorem xor_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun rg z _ => ⨅ af : Bool, Q () (rg.set64 rd (rg.get64 rd ^^^ rg.get64 rs)) z
        (StatusFlags.from_result (rg.get64 rd ^^^ rg.get64 rs) { cf := false, of := false, af }) ⦄
      (Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64,
    Effects.All, ite_true]
  intro af
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F (iInf_le _ af)) _ hpre)

/-- Load the address `disp(base, index, 8)` into a register. -/
@[spec] theorem lea_sib_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun rg z f => Q () (rg.set64 rd (rg.get64 b + rg.get64 i * 8 + BitVec.ofInt 64 d.toInt)) z f ⦄
      (Directive.instr (.regular .W64 .W64
          (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_sib, Effects.All, ite_true]
  exact hn _ (hpre)

/-- Store an immediate at `disp(base)`. -/
@[spec] theorem mov_store_imm_spec (b : Reg64) (d : Int64) (i : Int64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f =>
        ⌜(Int.toBytes 8 (BitVec.setWidth 64 i.toBitVec).toInt).AtM
            (r.get64 b + BitVec.ofInt 64 d.toInt) ⊑ Q () r z f⌝
          ⊓ bs.AtM (r.get64 b + BitVec.ofInt 64 d.toInt) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := (MProp.get_sep_apply_iff _ _ _).mp hpre
  obtain ⟨hpost, hbs⟩ := (MProp.get_meet_apply_iff _ _ mm).mp hM
  have hpost := (MProp.get_ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F).get s.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr
      ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
        Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload := Mem.loadInt_eq_of_AtM hown hlen (by decide)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, ConstExpr.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, ite_true]
  refine ?_
  have hstore := Mem.get_AtM_sep_storeInt hown hlen ((BitVec.setWidth 64 i.toBitVec).toInt)
  rw [MProp.sep_comm] at hstore
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hstore)

/-- Store a 64-bit register at `disp(base, index, 8)`. -/
@[spec] theorem mov_store_reg_sib_spec (b i : Reg64) (d : Int64) (rs : Reg64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f =>
        ⌜(Int.toBytes 8 (r.get64 rs).toInt).AtM
            (r.get64 b + r.get64 i * 8 + BitVec.ofInt 64 d.toInt) ⊑ Q () r z f⌝
          ⊓ bs.AtM (r.get64 b + r.get64 i * 8 + BitVec.ofInt 64 d.toInt) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := (MProp.get_sep_apply_iff _ _ _).mp hpre
  obtain ⟨hpost, hbs⟩ := (MProp.get_meet_apply_iff _ _ mm).mp hM
  have hpost := (MProp.get_ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) ∗ F).get s.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr
      ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
        Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload := Mem.loadInt_eq_of_AtM hown hlen (by decide)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_sib, hload, Effects.All, ite_true]
  refine ?_
  have hstore := Mem.get_AtM_sep_storeInt hown hlen ((s.regs.get64 rs).toInt)
  rw [MProp.sep_comm] at hstore
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hstore)

/-- Load the 64-bit value at `disp(base)` into a register. -/
@[spec] theorem mov_reg_mem_spec (rd b : Reg64) (d : Int64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun rg z f =>
        ⌜bs.AtM (rg.get64 b + BitVec.ofInt 64 d.toInt)
            ⊑ Q () (rg.set64 rd (BitVec.ofInt 64 (Int.ofBytes bs))) z f⌝
          ⊓ bs.AtM (rg.get64 b + BitVec.ofInt 64 d.toInt) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := (MProp.get_sep_apply_iff _ _ _).mp hpre
  obtain ⟨hpost, hbs⟩ := (MProp.get_meet_apply_iff _ _ mm).mp hM
  have hpost := (MProp.get_ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F).get s.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr
      ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
        Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload := Mem.loadInt_eq_of_AtM hown hlen (by decide)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, ite_true]
  refine ?_
  rw [MProp.sep_comm] at hown
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hown)

/-- Load the 64-bit value at `disp(base, index, 8)` into a register. -/
@[spec] theorem mov_reg_mem_sib_spec (rd b i : Reg64) (d : Int64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun rg z f =>
        ⌜bs.AtM (rg.get64 b + rg.get64 i * 8 + BitVec.ofInt 64 d.toInt)
            ⊑ Q () (rg.set64 rd (BitVec.ofInt 64 (Int.ofBytes bs))) z f⌝
          ⊓ bs.AtM (rg.get64 b + rg.get64 i * 8 + BitVec.ofInt 64 d.toInt) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := (MProp.get_sep_apply_iff _ _ _).mp hpre
  obtain ⟨hpost, hbs⟩ := (MProp.get_meet_apply_iff _ _ mm).mp hM
  have hpost := (MProp.get_ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) ∗ F).get s.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr
      ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
        Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload := Mem.loadInt_eq_of_AtM hown hlen (by decide)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_sib, hload, Effects.All, ite_true]
  refine ?_
  rw [MProp.sep_comm] at hown
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hown)

/-! ## The stack

`push` owns the slot below the stack pointer and fills it; `pop` owns the
slot at the stack pointer and reads it. Both move the stack pointer by eight. -/

/-- Push a 64-bit register. -/
@[spec] theorem push_reg_spec (rs : Reg64) (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f =>
        ⌜(Int.toBytes 8 (r.get64 rs).toInt).AtM (r.get64 .rsp - 8#64)
            ⊑ Q () (r.set64 .rsp (r.get64 .rsp - 8#64)) z f⌝
          ⊓ bs.AtM (r.get64 .rsp - 8#64) ⦄
      (Directive.instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := (MProp.get_sep_apply_iff _ _ _).mp hpre
  obtain ⟨hpost, hbs⟩ := (MProp.get_meet_apply_iff _ _ mm).mp hM
  have hpost := (MProp.get_ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 .rsp - 8#64) ∗ F).get s.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr
      ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
        Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload := Mem.loadInt_eq_of_AtM hown hlen (by decide)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.store, Reg64s.get_low_W64, Width.bytesv_W64, hload, Effects.All, ite_true]
  refine ?_
  have hstore := Mem.get_AtM_sep_storeInt hown hlen ((s.regs.get64 rs).toInt)
  rw [MProp.sep_comm] at hstore
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hstore)

/-- Pop into a 64-bit register. -/
@[spec] theorem pop_reg_spec (rd : Reg64) (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f =>
        ⌜bs.AtM (r.get64 .rsp)
            ⊑ Q () ((r.set64 .rsp (r.get64 .rsp + 8#64)).set64 rd
                (BitVec.ofInt 64 (Int.ofBytes bs))) z f⌝
          ⊓ bs.AtM (r.get64 .rsp) ⦄
      (Directive.instr (.regular .W64 .W64 (.pop (.reg (.low rd .W64)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := (MProp.get_sep_apply_iff _ _ _).mp hpre
  obtain ⟨hpost, hbs⟩ := (MProp.get_meet_apply_iff _ _ mm).mp hM
  have hpost := (MProp.get_ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 .rsp) ∗ F).get s.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr
      ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
        Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload := Mem.loadInt_eq_of_AtM hown hlen (by decide)
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, MachineData.set,
    MachineData.setReg, Reg64s.set_low_W64, Width.bytesv_W64, hload, Effects.All, ite_true]
  refine ?_
  rw [MProp.sep_comm] at hown
  exact hn _ ((MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hown)

end Program.FrameWP
