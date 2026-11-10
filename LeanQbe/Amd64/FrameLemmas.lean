module

public import LeanQbe.Amd64.TargLemmas
public import LeanQbe.AbiLemmas

/-!
# x64 step lemmas for the frame directives

One lemma per frame directive of `Targ.lean` (`pushD`, `popD`, `subSpD`, `addSpD`, `stSpD`,
`ldSpD`, `callD`, `jmpD`), generic in the `Host` and the position, in continuation form.
Memory is described with `region` (owned bytes, any contents) and `word` (8 bytes holding a value).
-/

@[expose] public section

namespace LeanQbe.Amd64

section
variable [Host]

/-- `push %r` -/
theorem eventually_pushD {i : Nat} {r : Reg64} {s : MachineData} {F : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (pushD r))
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp - 8#64) 8 ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) →
      (s'.dmem =⋆ word (s.regs.get64 .rsp - 8#64) (s.regs.get64 r) ⋆ F) →
      Run (i + 1) s' post) :
    Run i s post := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps hi ?_
  simp only [pushD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, get_q, Effects.All]
  refine (store_All_of_sep _ _ .W64 _ _ _ bs F ?_ hl).mpr ?_
  · exact hbs
  exact hk _ rfl (Mem.storeInt_sep _ 8 bs F s.dmem ⟨hbs, hl⟩ _)

/-- `pop %r` -/
theorem eventually_popD {i : Nat} {r : Reg64} {v : Val} {s : MachineData} {F : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (popD r))
    (hmem : s.dmem =⋆ word (s.regs.get64 .rsp) v ⋆ F)
    (hk : ∀ s' : MachineData,
      s'.regs = (s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64)).set64 r v → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [popD, Directive.interp, Instr.interp, Operation.interp]
  refine (load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) F hmem
    (Int.toBytes_length _ _)).mpr ?_
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  simp only [MachineData.set, MachineData.setReg, set_q, Effects.All]
  rw [hv]
  exact hk _ rfl rfl

/-- `sub $c, %rsp` (flags arbitrary). -/
theorem eventually_subSpD {i : Nat} {c : Int64} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (subSpD c))
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - c.toBitVec) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [subSpD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg, Effects.All, set_q,
    get_q]
  exact hk _ (by simp) rfl

/-- `add $c, %rsp` (flags arbitrary). -/
theorem eventually_addSpD {i : Nat} {c : Int64} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (addSpD c))
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp + c.toBitVec) →
      s'.dmem = s.dmem → Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [addSpD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg, Effects.All, set_q,
    get_q]
  exact hk _ (by simp [BitVec.add_comm]) rfl

/-- `movq %rv, off(%rsp)` -/
theorem eventually_stSpD {i : Nat} {rv : Reg64} {off : Int64} {s : MachineData}
    {F : Mem 64 → Prop} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (stSpD rv off))
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp + off.toBitVec) 8 ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs →
      (s'.dmem =⋆ word (s.regs.get64 .rsp + off.toBitVec) (s.regs.get64 rv) ⋆ F) →
      Run (i + 1) s' post) :
    Run i s post := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps hi ?_
  simp only [stSpD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, get_q, AddrExpr.interp_base_disp]
  refine (store_All_of_sep _ _ .W64 _ _ _ bs F (by simpa using hbs) hl).mpr ?_
  simp only [Effects.All]
  exact hk _ rfl (Mem.storeInt_sep _ 8 bs F s.dmem ⟨hbs, hl⟩ (s.regs.get64 rv).toInt)

/-- `movq off(%rsp), %rd` -/
theorem eventually_ldSpD {i : Nat} {rd : Reg64} {off : Int64} {v : Val} {s : MachineData}
    {F : Mem 64 → Prop} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (ldSpD rd off))
    (hmem : s.dmem =⋆ word (s.regs.get64 .rsp + off.toBitVec) v ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 rd v → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [ldSpD, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, AddrExpr.interp_base_disp]
  refine (load_All_of_sep _ _ .W64 _ _ (Int.toBytes 8 v.toInt) F hmem
    (Int.toBytes_length _ _)).mpr ?_
  have hv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  simp only [MachineData.set, MachineData.setReg, set_q, Effects.All]
  rw [hv]
  exact hk _ rfl rfl

/-- `call l`, where `l` resolves to the address of directive `j`. -/
theorem eventually_callD {i j : Nat} {l : Label} {s : MachineData} {F : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (callD l)) (hj : Labels.label l = Host.addrOf j)
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp - 8#64) 8 ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) →
      (s'.dmem =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.get64 .rsp - 8#64)) ⋆ F) →
      Run j s' post) :
    Run i s post := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps hi ?_
  simp only [callD, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  refine (store_All_of_sep _ _ .W64 _ _ _ bs F ?_ hl).mpr ?_
  · exact hbs
  rw [hj, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk _ rfl (Mem.storeInt_sep _ 8 bs F s.dmem ⟨hbs, hl⟩ _)

/-- `jmp l`, where `l` resolves to the address of directive `j`. -/
theorem eventually_jmpD {i j : Nat} {l : Label} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (jmpD l)) (hj : Labels.label l = Host.addrOf j)
    (hk : Run j s post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [jmpD, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  rw [hj, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk

/-- `jmp l` to wherever `l` resolves (a tail jump, possibly out of the function). -/
theorem eventually_jmpD_any {i : Nat} {l : Label} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (jmpD l))
    (hk : Eventually (step1 Host.exe) post ⟨s, Labels.label l⟩) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [jmpD, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk

end

end LeanQbe.Amd64
