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

public scoped instance instWP [Host] [BlockEntries] [FunDecls] : WP Fragment Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans q := ⟨fun Q E s => @Program.wp _ _ _ q.prog q.embeds (Q ()) E s⟩
  trans_monotone q := fun _ _ _ _ hE hQ _ h => @Program.wp_mono _ _ _ q.prog q.embeds _ _ _ _ (hQ ()) hE _ h

public scoped instance [Host] [BlockEntries] [FunDecls] : WP DirectiveAt Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans d := WP.trans (self := instWP) (@Fragment.mk _ [d.directive] d.embeds)
  trans_monotone d := WP.trans_monotone (self := instWP) (@Fragment.mk _ [d.directive] d.embeds)

variable [Host] [BlockEntries] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] public theorem nil_spec [Embeds []] : ⦃ fun s => Q () s ⦄ frag% [] ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_nil hq⟩

@[spec] public theorem cons_spec (d : Directive) (p : Program) [H : Embeds (d :: p)] [hN : _root_.NoEntries (d :: p)] :
    ⦃ haveI : Embeds [d] := .ofIsInfixAt H (List.isInfixAt_cons_head d p)
      WP.wp (DirectiveAt.mk d) (fun _ =>
        haveI : Embeds p := .ofIsInfixAt H (List.isInfixAt_cons_tail d p)
        WP.wp (frag% p) Q E) E ⦄
      frag% (d :: p) ⦃ Q; E ⦄ :=
  ⟨fun _ hw => Program.wp_cons hN.out hw⟩

@[spec] public theorem mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) [Embeds [Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i))))]] :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      DirectiveAt.mk (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Effects.All, Cls, ite_true]
  exact hpre

@[spec] public theorem mov_store_reg_spec (b : Reg64) (d : Int64) (rs : Reg64) [Embeds [Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64)))))]] :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
              (s.regs.get64 rs).toInt } ⦄
      DirectiveAt.mk (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, Cls, ite_true]
  exact hpre

@[spec] public theorem add_reg_mem_spec (rd b : Reg64) (d : Int64) [Embeds [Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩))))]] :
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
      DirectiveAt.mk (Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low_W64, Reg64s.set_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, Cls, ite_true]
  exact by rwa [hload, Option.get!_some] at hpre

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
      RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
      Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All, Cls, ite_true])

@[spec] public theorem label_spec (l : Label) [H : Embeds [.label l]] :
    ⦃ fun s => (DirectiveAt.mk (.label l)).startAddr = label l → Q () s ⦄ DirectiveAt.mk (.label l) ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single (by run_step; exact hq (Embedding.startAddr_label_cons l [] H.embedding))⟩

@[spec] public theorem nop_spec (asz osz : Width) (n : Nat) [Embeds [Directive.instr (.regular asz osz (.nop n))]] :
    ⦃ fun s => Q () s ⦄ DirectiveAt.mk (Directive.instr (.regular asz osz (.nop n))) ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single (by run_step; exact hq)⟩

@[spec] public theorem sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) [Embeds [Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i))))]] :
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
      DirectiveAt.mk (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  run_step
  exact hpre

@[spec] public theorem mulx_reg_spec (asz : Width) (hi lo rs : Reg64)
    [Embeds [Directive.instr (.regular asz .W64 (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64))))]] :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        Q () { s with regs :=
          (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      DirectiveAt.mk (Directive.instr (.regular asz .W64 (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single (by run_step; exact hq)⟩

@[spec] public theorem add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) [Embeds [Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i))))]] :
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
      DirectiveAt.mk (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  run_step
  exact hpre

@[spec] public theorem adc_reg_reg_spec (asz : Width) (rd rs : Reg64) [Embeds [Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))]] :
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
      DirectiveAt.mk (Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  run_step
  exact hpre

@[spec] public theorem add_reg_reg_spec (asz : Width) (rd rs : Reg64) [Embeds [Directive.instr (.regular asz .W64
          (.add (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))]] :
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
      DirectiveAt.mk (Directive.instr (.regular asz .W64
          (.add (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  run_step
  exact hpre

@[spec] public theorem cmp_reg_reg_spec (asz : Width) (ra rb : Reg64) [Embeds [Directive.instr (.regular asz .W64
          (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))]] :
    ⦃ fun s =>
        let a := s.regs.get64 ra
        let b := s.regs.get64 rb
        let v := a - b
        Q () { s with
          status := StatusFlags.from_result v
            { cf := v.unsigned != a.unsigned - b.unsigned,
              af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
              of := v.signed != a.signed - b.signed } } ⦄
      DirectiveAt.mk (Directive.instr (.regular asz .W64
          (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  run_step
  exact hpre

@[spec] public theorem test_reg_reg_spec (asz : Width) (ra rb : Reg64) [Embeds [Directive.instr (.regular asz .W64
          (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64)))))]] :
    ⦃ fun s =>
        let v := s.regs.get64 ra &&& s.regs.get64 rb
        ∀ af : Bool, Q () { s with
          status := StatusFlags.from_result v { cf := false, af, of := false } } ⦄
      DirectiveAt.mk (Directive.instr (.regular asz .W64
          (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  run_step
  intro af
  exact hpre af

@[spec] public theorem mov_load_byte_spec (r b : Reg64) (d : Int64) [Embeds [Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩))))]] :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () { s with regs := s.regs.set (.low r .W8)
                              (BitVec.ofInt 8 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).get!) } ⦄
      DirectiveAt.mk (Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, Cls, ite_true]
  exact by rwa [hload, Option.get!_some] at hpre

@[spec] public theorem mov_store_byte_spec (b : Reg64) (d : Int64) (r : Reg64) [Embeds [Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W8)))))]] :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1
              (s.regs.get (.low r .W8)).toInt } ⦄
      DirectiveAt.mk (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, Cls, ite_true]
  exact hpre

@[spec] public theorem xor_reg_reg_spec (asz : Width) (rd rs : Reg64) [Embeds [Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))]] :
    ⦃ fun s =>
        let v := s.regs.get64 rd ^^^ s.regs.get64 rs
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd v
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      DirectiveAt.mk (Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  run_step
  intro af
  exact hpre af

@[spec] public theorem dec_reg_spec (asz : Width) (r : Reg64) [Embeds [Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64))))]] :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let v := a - 1
        Q () { s with
          regs := s.regs.set64 r v
          status := StatusFlags.from_result v
            { cf := s.status.cf,
              af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
              of := v.signed != a.signed - 1 } } ⦄
      DirectiveAt.mk (Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single ?_
  run_step
  exact hpre

@[spec] public theorem jmp_label_spec (asz osz : Width) (l : Label)
    [Embeds [Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction))))]] :
    ⦃ fun s => ((DirectiveAt.mk (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))))).FallsThroughTo (label l) → Q () s) ∧
        (¬ (DirectiveAt.mk (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))))).FallsThroughTo (label l) →
          FunDecls.exit (fun a t => if (DirectiveAt.mk (Directive.instr (.regular asz osz
            (.jmp (.rel (.sub (.label l) .after_current_instruction)))))).FallsThroughTo a then Q () t else E a t)
            E (label l) s) ⦄
      DirectiveAt.mk (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))))
    ⦃ Q; E ⦄ :=
  ⟨fun _ hq => Program.wp_single (by
    run_step
    rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
    split
    · next h => exact hq.1 h
    · next h => exact hq.2 h)⟩

@[spec] public theorem jcc_spec (asz osz : Width) (cc : CondCode) (l : Label)
    [Embeds [Directive.instr (.regular asz osz (.jcc cc l))]] :
    ⦃ fun s => (cc.interp s.status = true →
          ((DirectiveAt.mk (Directive.instr (.regular asz osz (.jcc cc l)))).FallsThroughTo (label l) → Q () s) ∧
          (¬ (DirectiveAt.mk (Directive.instr (.regular asz osz (.jcc cc l)))).FallsThroughTo (label l) →
            FunDecls.exit (fun a t => if (DirectiveAt.mk (Directive.instr (.regular asz osz (.jcc cc l)))).FallsThroughTo a
              then Q () t else E a t) E (label l) s)) ∧
        (cc.interp s.status = false → Q () s) ⦄
      DirectiveAt.mk (Directive.instr (.regular asz osz (.jcc cc l)))
    ⦃ Q; E ⦄ :=
  ⟨fun s ⟨hjmp, hfall⟩ => Program.wp_single (by
    run_step
    cases hc : CondCode.interp cc s.status <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · simp only [Effects.All, Cls, ite_true]; exact hfall hc
    · simp only [Effects.All, Cls]
      split
      · next h => exact (hjmp hc).1 h
      · next h => exact (hjmp hc).2 h)⟩

@[spec] public theorem ret_spec (asz osz : Width) [Embeds [Directive.instr (.regular asz osz .ret)]] :
    ⦃ fun s => s.retAddr.isSome = true
        ∧ ((DirectiveAt.mk (Directive.instr (.regular asz osz .ret))).FallsThroughTo s.retAddr.get! →
            Q () { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) })
        ∧ (¬ (DirectiveAt.mk (Directive.instr (.regular asz osz .ret))).FallsThroughTo s.retAddr.get! →
            FunDecls.exit (fun a t => if (DirectiveAt.mk (Directive.instr (.regular asz osz .ret))).FallsThroughTo a
              then Q () t else E a t) E s.retAddr.get! { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) }) ⦄
      DirectiveAt.mk (Directive.instr (.regular asz osz .ret))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hfall, hexit⟩ := hpre
  obtain ⟨ra, hra⟩ := Option.isSome_iff_exists.mp hmapped
  rw [hra, Option.get!_some] at hexit hfall
  obtain ⟨i, hi, hval⟩ : ∃ i, Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 = some i
      ∧ Int64.ofBitVec (BitVec.ofInt 64 i) = ra := by
    unfold MachineData.retAddr at hra
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp) 8 with
    | none => rw [hl] at hra; exact absurd hra (by simp)
    | some i => exact ⟨i, rfl, by rw [hl] at hra; simpa using hra⟩
  refine Program.wp_single ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, hi,
    Effects.All, hval, Cls]
  split
  · next h => exact hfall h
  · next h => exact hexit h

end Program.WP

namespace Program.WP

public theorem step1_of_wp_at [Host] [BlockEntries] [FunDecls] {p : Program} [h : Embeds p] {s : MachineData}
    {post : @Post MachineState} (hw : ⊤ ⊑ WP.wp (frag% p) (fun _ s' => ∀ pc, post ⟨s', pc⟩) ⊥ s) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf h.embedding.start⟩ :=
  Program.step1_of_wp (Q := fun s' => ∀ pc, post ⟨s', pc⟩)
    (E := (⊥ : Int64 → MachineData → Prop)) (of_top_le_prop hw) (fun _ hq => hq _)
    (fun a s' hE => ((bot_le (α := Int64 → MachineData → Prop) fun _ _ => False) a s' hE).elim)

public theorem step1_of_wp [Host] [BlockEntries] [FunDecls] {p : Program} {s : MachineData}
    {post : @Post MachineState} (hp : p.IsInfix Host.prog)
    (hw : ⊤ ⊑ WP.wp (@Fragment.mk _ p (Embeds.ofIsInfix hp)) (fun _ s' => ∀ pc, post ⟨s', pc⟩) ⊥ s) :
    Eventually (step1 Host.exe) post ⟨s, startAddr hp⟩ :=
  @step1_of_wp_at _ _ _ p (Embeds.ofIsInfix hp) s post hw

end Program.WP
