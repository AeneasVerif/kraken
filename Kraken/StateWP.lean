module

/-
The weakest precondition over whole machine states: `StateWP.instWP` interprets a
`Program` by its run at `MachineData → Prop`. Open it with `open scoped StateWP`.
-/
public import Kraken.ProgramRun
public import Kraken.X64.Registers
public import Kraken.KVCGen
public import Std.WP
public import Std.Tactic.Do

@[expose] public section

open Std.WP
open Lean.Order

namespace StateWP

/-- Programs interpreted by their run, at predicates over machine states. -/
scoped instance instWP [Labels] : WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans q := ⟨fun Q E s => Program.run q (Q ()) E s⟩
  trans_monotone _ := fun _ _ _ _ hE hQ _ h => Program.run_mono (hQ ()) hE h

theorem wp_apply_iff [Labels] (q : Program) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) :
    WP.wp q Q E s ↔ Program.run q (Q ()) E s := Iff.rfl

/-- Triples of one directive: the interpretation of the singleton program. -/
scoped instance [Labels] : WP Directive Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans d := WP.trans (self := instWP) [d]
  trans_monotone d := WP.trans_monotone (self := instWP) [d]

theorem triple_directive [Labels] {d : Directive} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    (⦃ P ⦄ d ⦃ Q; E ⦄) ↔ (⦃ P ⦄ [d] ⦃ Q; E ⦄) :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

variable [Labels] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] theorem nil_spec : ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain rfl := List.map_eq_nil_iff.mp hds
  exact hQ s hpre

@[spec] theorem cons_spec (d : Directive) (p : Program) :
    ⦃ WP.wp d (fun _ => WP.wp p Q E) E ⦄ (d :: p) ⦃ Q; E ⦄ :=
  ⟨fun _ h => Program.run_cons h⟩

@[spec] theorem mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Effects.All, List.cons_append,
    List.nil_append, Directives.interp]
  exact hQ _ hpre

@[spec] theorem mov_store_reg_spec (b : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s => ((Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true)
        ⊓ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
              (s.regs.get64 rs).toInt } ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := (meet_prop_eq_and _ _) ▸ hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, List.cons_append, List.nil_append,
    Directives.interp]
  exact hQ _ hpre

@[spec] theorem add_reg_mem_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s => ((Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true)
        ⊓ ∀ i, Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8 = some i →
          let a := BitVec.ofInt 64 i
          let bv := s.regs.get64 rd
          let v := a + bv
          Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned + bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned + (bv.take 4).unsigned,
                of := v.signed != a.signed + bv.signed } } ⦄
      Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := (meet_prop_eq_and _ _) ▸ hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, List.cons_append, List.nil_append, Directives.interp]
  exact hQ _ (hpre i hload)

/-- The simp set that reduces one directive of a burst. -/
local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All, List.cons_append, List.nil_append,
      Directives.interp])

@[spec] theorem label_spec (l : Label) : ⦃ fun s => Q () s ⦄ Directive.label l ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  exact hQ _ hpre

@[spec] theorem nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => Q () s ⦄ Directive.instr (.regular asz osz (.nop n)) ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  exact hQ _ hpre

@[spec] theorem sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := v.unsigned != b.unsigned - a.unsigned,
              af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
              of := v.signed != b.signed - a.signed } } ⦄
      Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  exact hQ _ hpre

@[spec] theorem mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        Q () { s with regs :=
          (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  exact hQ _ hpre

@[spec] theorem add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := s.regs.get64 r
        let v := a + b
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
              of := v.signed != a.signed + b.signed } } ⦄
      Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  exact hQ _ hpre

@[spec] theorem adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let c := s.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned + c,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
              of := v.signed != a.signed + b.signed + c } } ⦄
      Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  exact hQ _ hpre

@[spec] theorem xor_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ^^^ s.regs.get64 rs
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  intro af
  exact hQ _ (hpre af)

@[spec] theorem dec_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let v := a - 1
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := s.status.cf,
              af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
              of := v.signed != a.signed - 1 } } ⦄
      Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64))))
    ⦃ Q ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds hQ _
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  exact hQ _ hpre

@[spec] theorem jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E (label l) s ⦄
      Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction))))
    ⦃ Q; E ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  intro ds rest pc Φ hds _ hE
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  have hcancel : pc + .ofNat z + (label l - (pc + .ofNat z)) = label l := by
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  simp only [Int64.ofBitVec_toBitVec, hcancel]
  exact hE _ _ hpre

@[spec] theorem jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s => (cc.interp s.status = true → E (label l) s) ⊓ (cc.interp s.status = false → Q () s) ⦄
      Directive.instr (.regular asz osz (.jcc cc l))
    ⦃ Q; E ⦄ := by
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  obtain ⟨hjmp, hfall⟩ := (meet_prop_eq_and _ _) ▸ hpre
  intro ds rest pc Φ hds hQ hE
  obtain ⟨⟨_, z⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hds
  run_step
  cases hc : CondCode.interp cc s.status <;>
    simp only [hc, Bool.false_eq_true, ite_true, ite_false]
  · exact hQ _ (hfall hc)
  · exact hE _ _ (hjmp hc)

end StateWP

/-! ## Reading the wp back as the baseline judgment -/

open StateWP in
theorem straightlineStep_of_wp [layout : Layout] {p : Program} {s : MachineData}
    {post : MachineState → Prop}
    (h : ∀ [Labels], ⊤ ⊑ WP.wp p (fun _ s' => ∀ pc, post (s', pc)) ⊥ s) :
    straightlineStep (layout p) (s, layout.start) post :=
  Program.run_straightlineStep (of_top_le_prop (@h (Executable.labels (layout p))))
    (fun st' hq => hq st'.2)
    (fun a s' hE => ((bot_le (α := Int64 → MachineData → Prop) fun _ _ => False) a s' hE).elim)

open StateWP in
theorem eventually_straightlineStep_of_wp [layout : Layout] {p : Program} {s : MachineData}
    {post : MachineState → Prop}
    (h : ∀ [Labels], ⊤ ⊑ WP.wp p (fun _ s' => ∀ pc, post (s', pc)) ⊥ s) :
    Eventually (straightlineStep (layout p)) post (s, layout.start) :=
  .step _ _ (straightlineStep_of_wp h) fun _ h => .done _ h
