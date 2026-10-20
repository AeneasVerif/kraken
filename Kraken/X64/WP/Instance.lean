module

public import Kraken.X64.WP
public import Kraken.X64.Registers
public import Kraken.KVCGen
public import Std.WP
public import Std.Tactic.Do

open Std.WP
open Lean.Order

public theorem Int64.add_sub_self_left (a b : Int64) : a + (b - a) = b := by
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

@[expose] public def MachineData.retAddr (t : MachineData) : Option Int64 :=
  (Mem.loadInt t.dmem (t.regs.get64 .rsp) 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i))

@[grind =] public theorem MachineData.retAddr_eq (t : MachineData) :
    t.retAddr = (Mem.loadInt t.dmem (t.regs.get64 .rsp) 8).map
      (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) := rfl

namespace Program.WP

public scoped instance instWP [Host] [FunDecls] : WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans p := ⟨fun Q E s => Program.wp p (fun st => Q () st.data) (fun st => E st.pc st.data) s⟩
  trans_monotone p := fun _ _ _ _ hE hQ _ h => Program.wp_mono (fun st => hQ () st.data) (fun st => hE st.pc st.data) h

public scoped instance [Host] [FunDecls] : WP Directive Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans d := WP.trans (self := instWP) [d]
  trans_monotone d := WP.trans_monotone (self := instWP) [d]

public scoped instance [Host] [FunDecls] (p : Program) : WPConjunctive p where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ s h := by
    simp only [meet_apply, meet_prop_eq_and] at h
    show Program.wp p (fun st => (Q₁ ⊓ Q₂) () st.data) (fun st => (E₁ ⊓ E₂) st.pc st.data) s
    exact Program.wp_mono (fun _ h => by simpa only [meet_apply, meet_prop_eq_and] using h)
      (fun _ h => by simpa only [meet_apply, meet_prop_eq_and] using h) (Program.wp_and h.1 h.2)

public scoped instance [Host] [FunDecls] (d : Directive) : WPConjunctive d where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ s h := by
    simp only [meet_apply, meet_prop_eq_and] at h
    show Program.wp [d] (fun st => (Q₁ ⊓ Q₂) () st.data) (fun st => (E₁ ⊓ E₂) st.pc st.data) s
    exact Program.wp_mono (fun _ h => by simpa only [meet_apply, meet_prop_eq_and] using h)
      (fun _ h => by simpa only [meet_apply, meet_prop_eq_and] using h) (Program.wp_and h.1 h.2)

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] public theorem nil_spec : ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_nil fun _ => hq⟩

@[spec] public theorem cons_spec (d : Directive) (p : Program) [hN : NoLabels (d :: p)] :
    ⦃ WP.wp d (fun _ => WP.wp p Q E) E ⦄ (d :: p) ⦃ Q; E ⦄ :=
  ⟨fun _ hw => Program.wp_cons hN.out hw⟩

@[spec] public theorem mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Effects.All, ite_true]
  exact hn _ hpre

@[spec] public theorem mov_store_reg_spec (b : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
              (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, ite_true]
  exact hn _ hpre

@[spec] public theorem add_reg_mem_spec (rd b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true ∧
          let a := BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).get!
          let bv := s.regs.get64 rd
          let v := a + bv
          Q () { s with
            regs := s.regs.set64 rd v
            status := StatusFlags.from_result v
              { cf := v.unsigned != a.unsigned + bv.unsigned,
                af := (v.take 4).unsigned != (a.take 4).unsigned + (bv.take 4).unsigned,
                of := v.signed != a.signed + bv.signed } } ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, ite_true]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All, ite_true])

@[spec] public theorem label_spec (l : Label) :
    ⦃ fun s => Q () s ⦄ (Directive.label l) ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq⟩

@[spec] public theorem nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => Q () s ⦄ (Directive.instr (.regular asz osz (.nop n))) ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq⟩

@[spec] public theorem sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
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
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        Q () { s with regs :=
          (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      (Directive.instr (.regular asz .W64 (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by run_step; exact hn _ hq⟩

@[spec] public theorem add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
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
      (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
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
      (Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem add_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let v := a + b
        Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned + b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
              of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.add (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem cmp_reg_reg_spec (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 ra
        let b := s.regs.get64 rb
        let v := a - b
        Q () { s with
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned - b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
              of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

@[spec] public theorem test_reg_reg_spec (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 ra &&& s.regs.get64 rb
        ∀ af : Bool, Q () { s with
          status := StatusFlags.from_result v { cf := false, af, of := false } } ⦄
      (Directive.instr (.regular asz .W64
          (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  intro af
  exact hn _ (hpre af)

@[spec] public theorem mov_load_byte_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () { s with regs := s.regs.set (.low r .W8)
                              (BitVec.ofInt 8 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).get!) } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] public theorem mov_store_byte_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1
              (s.regs.get (.low r .W8)).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ hpre

@[spec] public theorem xor_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ^^^ s.regs.get64 rs
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  intro af
  exact hn _ (hpre af)

@[spec] public theorem dec_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let v := a - 1
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := s.status.cf,
              af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
              of := v.signed != a.signed - 1 } } ⦄
      (Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  run_step
  exact hn _ hpre

public theorem MachineData.not_stackBelow_self (s : MachineData) : ¬ s.StackBelow s := by
  simp [MachineData.StackBelow]

public theorem MachineData.not_stackBelow_pop (s : MachineData) :
    ¬ ({ s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) } : MachineData).StackBelow s := by
  simp only [MachineData.StackBelow, Reg64s.set64_rsp, Reg64s.get64_rsp, Int64.toBitVec_ofBitVec]
  generalize s.regs.rsp.toBitVec = x
  rw [show x - (x + 8#64) = -8#64 by bv_omega]
  decide

@[spec] public theorem jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E (label l) s ⦄
      (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))))
    ⦃ Q; E ⦄ :=
  ⟨fun s hq => Program.wp_single fun _ _ _ _ _ hj => by
    run_step
    rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
    refine hj (label l) s ?_
    rw [Executable.StepOut.of_not_below_data (MachineData.not_stackBelow_self s)]
    exact hq⟩

@[spec] public theorem jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s => (cc.interp s.status = true → E (label l) s) ∧ (cc.interp s.status = false → Q () s) ⦄
      (Directive.instr (.regular asz osz (.jcc cc l)))
    ⦃ Q; E ⦄ :=
  ⟨fun s ⟨hjmp, hfall⟩ => Program.wp_single fun _ _ _ _ hn hj => by
    run_step
    cases hc : CondCode.interp cc s.status <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · exact hn _ (hfall hc)
    · refine hj (label l) s ?_
      rw [Executable.StepOut.of_not_below_data (MachineData.not_stackBelow_self s)]
      exact hjmp hc⟩

@[spec] public theorem push_reg_spec (rs : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
                        dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.store, Reg64s.get_low_W64, Width.bytes, hload, Effects.All]
  exact hn _ hpre

@[spec] public theorem pop_reg_spec (rd : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true
        ∧ Q () { s with
            regs := (s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64)).set64 rd
              (BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64 (.pop (.reg (.low rd .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, MachineData.set,
    MachineData.setReg, Reg64s.set_low_W64, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] public theorem ret_spec (asz osz : Width) :
    ⦃ fun s => s.retAddr.isSome = true
        ∧ E s.retAddr.get! { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) } ⦄
      (Directive.instr (.regular asz osz .ret))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hexit⟩ := hpre
  obtain ⟨ra, hra⟩ := Option.isSome_iff_exists.mp hmapped
  rw [hra, Option.get!_some] at hexit
  obtain ⟨i, hi, hval⟩ : ∃ i, Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 = some i
      ∧ Int64.ofBitVec (BitVec.ofInt 64 i) = ra := by
    unfold MachineData.retAddr at hra
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 with
    | none => rw [hl] at hra; exact absurd hra (by simp)
    | some i => exact ⟨i, rfl, by rw [hl] at hra; simpa using hra⟩
  refine Program.wp_single fun _ _ _ _ _ hj => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, hi,
    Effects.All, hval]
  refine hj ra { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) } ?_
  rw [Executable.StepOut.of_not_below_data (MachineData.not_stackBelow_pop s)]
  exact hexit

end Program.WP

namespace Program.WP

public theorem step1_of_wp_at [Host] [FunDecls] {p : Program} [h : Embeds p] {s : MachineData}
    {post : @Post MachineState} (hw : WP.wp p (fun _ s' => post ⟨s', h.embedding.endAddr⟩) ⊥ s) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf h.embedding.start⟩ :=
  Program.step1_of_wp hw (fun ⟨_, _⟩ hu hq => by subst hu; exact hq)
    (fun u hE => ((bot_le (α := Int64 → MachineData → Prop) fun _ _ => False) u.pc u.data hE).elim)

public theorem step1_of_wp [Host] [FunDecls] {p : Program} {s : MachineData}
    {post : @Post MachineState} (hp : p.IsInfix Host.prog)
    (hw : WP.wp p (fun _ s' => post ⟨s', endAddr hp⟩) ⊥ s) :
    Eventually (step1 Host.exe) post ⟨s, startAddr hp⟩ :=
  @step1_of_wp_at _ _ p (Embeds.ofIsInfix hp) s post hw

end Program.WP
