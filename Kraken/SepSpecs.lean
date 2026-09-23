/-
The instruction dictionary of the separation-logic wp. Each spec is a triple
of one directive with a small footprint. A register write carries the
schematic post to the updated registers. A memory instruction owns the slot's
bytes, and its pure conjunct is the post entailment: the schematic post holds
of the slot as the instruction leaves it, at the registers and flags the
instruction produces. `SepWP.cons_spec` sequences the specs, and the frame
inference of Kraken/SepFrameProc.lean threads the post entailment into the
tail.

Every proof runs the same route: `SepWP.sep_intro` opens the triple under an
ambient frame, the `Mem.*_sep` lemmas of Kraken/SeparationMem.lean step the
machine memory under that frame, and the run ends at the directive's end.
-/
import Kraken.SepWP
import Kraken.X64.Registers
import Kraken.X64.Parser

open Std.WP
open Lean.Order
open Kraken.X64.Parser
open scoped SepWP

/-- The address a `disp(base)` expression computes, at 64-bit address size:
the base register plus the displacement. -/
theorem AddrExpr.zeroExtend_interp_base_disp [L : Labels] (b : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), none, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, Int.add_zero,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_toInt]

namespace SepWP

variable {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
  {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}

/-- The empty program: its wp is the postcondition. -/
@[spec] theorem nil_spec :
    ⦃ fun rg z f => Q () rg z f ⦄ ([] : Program) ⦃ Q; E ⦄ := by
  refine sep_intro fun F s hpre => ?_
  intro L ds rest pc Φ hds hQ _
  obtain rfl := List.map_eq_nil_iff.mp hds
  exact hQ s hpre

/-! ## Register instructions

A register instruction owns no memory: its spec carries the schematic post
to the updated registers and flags. -/

/-- Load an immediate into a 64-bit register. -/
@[spec] theorem mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun rg z f => Q () (rg.set64 r (BitVec.setWidth 64 i.toBitVec)) z f ⦄
      Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr (sep_intro fun F s hpre => ?_)
  intro L ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Effects.All, List.cons_append,
    List.nil_append, Directives.interp]
  exact hQ _ hpre

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
      Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64)))))
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
  intro L ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, List.cons_append, List.nil_append,
    Directives.interp]
  refine hQ _ ?_
  rw [MProp.sep_comm] at hstore
  exact (MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hstore

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
      Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩))))
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
  intro L ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, List.cons_append, List.nil_append, Directives.interp]
  refine hQ _ ?_
  rw [MProp.sep_comm] at hown
  exact (MProp.le_def _ _).mp (MProp.sep_mono_right F hpost) _ hown

end SepWP
