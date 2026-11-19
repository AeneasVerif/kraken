module

public import Kraken.X64.WP.Basic
public import Kraken.X64.Sep

/-!
# Control-flow step lemmas

Step lemmas, in continuation-passing form, for the control-flow instructions a compiler emits:
`jmp L`, `jmp *%r`, `jmp *a`, `jcc L`, `call L`, `call *%r`, `call *a`, and `ret`, at any
position of any `Host` program. The encodings are the ones the parser produces
(`⸨prog| jmp L ⸩ = [Directive.jmpTo "L"]` etc.).

Labels resolve to their *first* definition in the host program (`Host.label_eq_addrOf`), so every
lemma that jumps to a label takes the hypothesis `hfirst` that no earlier directive defines the same
label. Under `Host.LabelsUnique` it is `hu.first hk`.
-/

/-- `jmp L` -/
public abbrev Directive.jmpTo (L : Label) : Directive :=
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label L) .after_current_instruction))))

/-- `jmp *%r` -/
public abbrev Directive.jmpReg (r : Reg .W64) : Directive :=
  .instr (.regular .W64 .W64 (.jmp (.reg r)))

/-- `jmp *a` -/
public abbrev Directive.jmpMem (a : AddrExpr) (aw : Width := .W64) : Directive :=
  .instr (.regular aw .W64 (.jmp (.mem a)))

/-- `jcc L`, e.g. `jnz L` is `Directive.jccTo .nz L` -/
public abbrev Directive.jccTo (cc : CondCode) (L : Label) : Directive :=
  .instr (.regular .W64 .W64 (.jcc cc L))

/-- `call L` -/
public abbrev Directive.callTo (L : Label) : Directive :=
  .instr (.regular .W64 .W64 (.call (.rel (.sub (.label L) .after_current_instruction))))

/-- `call *%r` -/
public abbrev Directive.callReg (r : Reg .W64) : Directive :=
  .instr (.regular .W64 .W64 (.call (.reg r)))

/-- `call *a` -/
public abbrev Directive.callMem (a : AddrExpr) (aw : Width := .W64) : Directive :=
  .instr (.regular aw .W64 (.call (.mem a)))

/-- `ret` -/
public abbrev Directive.ret : Directive := .instr (.regular .W64 .W64 .ret)

section
variable [Host]

/-- `jmp L` at index `i`, where `L` is first defined at index `k`. -/
public theorem Host.eventually_jmp {i k : Nat} {L : Label} {post : @Post MachineState}
    {s : MachineData}
    (hi : Host.prog[i]? = some (.jmpTo L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All]
  rw [Host.label_eq_addrOf hk hfirst, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact h

/-- `jmp *%r` at index `i`, where `r` holds target address `tgt`. -/
public theorem Host.eventually_jmp_reg {i : Nat} {r : Reg .W64} {tgt : Int64}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.jmpReg r))
    (htgt : s.regs.get r = tgt.toBitVec)
    (h : Eventually (step1 Host.exe) post ⟨s, tgt⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, Effects.All,
    htgt, Int64.ofBitVec_toBitVec]
  exact h

/-- `jmp *a` at index `i`, where memory at `a` holds target address `tgt`. -/
public theorem Host.eventually_jmp_mem {i : Nat} {a : AddrExpr} {aw : Width} {tgt : Int64}
    {post : @Post MachineState} {s : MachineData} {R : DataMem → Prop}
    (hi : Host.prog[i]? = some (.jmpMem a aw))
    (hmem : s.dmem =⋆
      Eq (tgt.toUInt64.At
        ((@AddrExpr.interp _ ⟨aw⟩ a s.regs ⟨Host.addrOf i, Host.addrOf (i + 1)⟩).zeroExtend 64))
      ⋆ R)
    (h : Eventually (step1 Host.exe) post ⟨s, tgt⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, Effects.All]
  refine (load_All_of_sep _ _ .W64 _ _ tgt.toUInt64.toBytes R hmem
    (UInt64.toBytes_length _)).mpr ?_
  have htgt : BitVec.ofInt 64 (Int.ofBytes tgt.toUInt64.toBytes) = tgt.toBitVec :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl tgt.toBitVec
  simp only [Effects.All, htgt, Int64.ofBitVec_toBitVec]
  exact h

/--
`jcc cc L` at index `i`, where `L` is first defined at index `k`: continue at the label if the
condition holds in the current flags, and at the next directive otherwise.
-/
public theorem Host.eventually_jcc {i k : Nat} {cc : CondCode} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.jccTo cc L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post
      ⟨s, if cc.interp s.status then Host.addrOf k else Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All]
  rw [Host.label_eq_addrOf hk hfirst]
  split <;> simp_all [Effects.All]

/-- `jcc cc L`, taken. -/
public theorem Host.eventually_jcc_taken {i k : Nat} {cc : CondCode} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.jccTo cc L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (hcc : cc.interp s.status = true)
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ :=
  Host.eventually_jcc hi hk hfirst (by simp only [hcc, ↓reduceIte]; exact h)

/-- `jcc cc L`, not taken. Nothing is needed about the label: it may even be undefined. -/
public theorem Host.eventually_jcc_fallthrough {i : Nat} {cc : CondCode} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.jccTo cc L))
    (hcc : cc.interp s.status = false)
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All, hcc]
  exact h

/--
`call L` at index `i`, where `L` is first defined at index `k`. The 8 bytes below the stack pointer
must be owned (`old`). Afterwards they hold the return address `Host.addrOf (i + 1)`, the stack
pointer is 8 lower, the frame `R` is preserved, and control is at the label.
-/
public theorem Host.eventually_call {i k : Nat} {L : Label} {post : @Post MachineState}
    {s : MachineData} {old : List UInt8} {R : DataMem → Prop}
    (hi : Host.prog[i]? = some (.callTo L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (h : ∀ m' : DataMem,
      (m' =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) →
      Eventually (step1 Host.exe) post
        ⟨{ s with regs := { s.regs with rsp := s.regs.rsp - 8 }, dmem := m' }, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All]
  refine (store_All_of_sep _ _ .W64 _ _ _ old R ?_ hlen).mpr ?_
  · exact hmem
  rw [Host.label_eq_addrOf hk hfirst, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact h _ (Mem.storeInt_sep _ 8 old R s.dmem ⟨hmem, hlen⟩ _)

/--
`call *%r` at index `i`, where `r` holds target address `tgt` (read before `rsp` is decremented,
so `r = .rsp` is supported). The 8 bytes below `rsp` must be owned (`old`). Afterwards they hold
`Host.addrOf (i + 1)`, `rsp` is 8 lower, `R` is preserved, and control is at `tgt`.
-/
public theorem Host.eventually_call_reg {i : Nat} {r : Reg .W64} {tgt : Int64}
    {post : @Post MachineState} {s : MachineData} {old : List UInt8} {R : DataMem → Prop}
    (hi : Host.prog[i]? = some (.callReg r))
    (htgt : s.regs.get r = tgt.toBitVec)
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (h : ∀ m' : DataMem,
      (m' =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) →
      Eventually (step1 Host.exe) post
        ⟨{ s with regs := { s.regs with rsp := s.regs.rsp - 8 }, dmem := m' }, tgt⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, Effects.All,
    htgt, Int64.ofBitVec_toBitVec]
  refine (store_All_of_sep _ _ .W64 _ _ _ old R ?_ hlen).mpr ?_
  · exact hmem
  exact h _ (Mem.storeInt_sep _ 8 old R s.dmem ⟨hmem, hlen⟩ _)

/--
`call *a` at index `i`, where memory at `a` holds target address `tgt` (loaded before `rsp` is
decremented). The 8 bytes below `rsp` must be owned (`old`). Afterwards they hold
`Host.addrOf (i + 1)`, `rsp` is 8 lower, `R` is preserved, and control is at `tgt`.
-/
public theorem Host.eventually_call_mem {i : Nat} {a : AddrExpr} {aw : Width} {tgt : Int64}
    {post : @Post MachineState} {s : MachineData} {old : List UInt8}
    {Rload R : DataMem → Prop}
    (hi : Host.prog[i]? = some (.callMem a aw))
    (hload : s.dmem =⋆
      Eq (tgt.toUInt64.At
        ((@AddrExpr.interp _ ⟨aw⟩ a s.regs ⟨Host.addrOf i, Host.addrOf (i + 1)⟩).zeroExtend 64))
      ⋆ Rload)
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (h : ∀ m' : DataMem,
      (m' =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) →
      Eventually (step1 Host.exe) post
        ⟨{ s with regs := { s.regs with rsp := s.regs.rsp - 8 }, dmem := m' }, tgt⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, Effects.All]
  refine (load_All_of_sep _ _ .W64 _ _ tgt.toUInt64.toBytes Rload hload
    (UInt64.toBytes_length _)).mpr ?_
  have htgt : BitVec.ofInt 64 (Int.ofBytes tgt.toUInt64.toBytes) = tgt.toBitVec :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl tgt.toBitVec
  simp only [htgt, Int64.ofBitVec_toBitVec]
  refine (store_All_of_sep _ _ .W64 _ _ _ old R ?_ hlen).mpr ?_
  · exact hmem
  exact h _ (Mem.storeInt_sep _ 8 old R s.dmem ⟨hmem, hlen⟩ _)

/--
`ret` at index `i`. The 8 bytes at the stack pointer hold a return address `ra`. Afterwards the stack
pointer is 8 higher, memory is unchanged, and control is at `ra`.
-/
public theorem Host.eventually_ret {i : Nat} {post : @Post MachineState} {s : MachineData}
    {ra : Int64} {R : DataMem → Prop}
    (hi : Host.prog[i]? = some .ret)
    (hmem : s.dmem =⋆ Eq (ra.toUInt64.At s.regs.rsp.toBitVec) ⋆ R)
    (h : Eventually (step1 Host.exe) post
      ⟨{ s with regs := { s.regs with rsp := s.regs.rsp + 8 } }, ra⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All]
  refine (load_All_of_sep _ _ .W64 _ _ ra.toUInt64.toBytes R ?_ (UInt64.toBytes_length _)).mpr ?_
  · exact hmem
  have hra : BitVec.ofInt 64 (Int.ofBytes ra.toUInt64.toBytes) = ra.toBitVec :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl ra.toBitVec
  simp only [Effects.All]
  rw [hra, Int64.ofBitVec_toBitVec]
  exact h

end

/--
Function call at the `Program.wp` level. The callee is known through a host-level specification
that is quantified over the return address `ra`: started at its label with `ra` on the stack, it
eventually reaches `ra` in a state satisfying `Q`.
-/
public theorem Program.wp_callTo [Host] {L : Label} {kf : Nat} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} {old : List UInt8} {R : DataMem → Prop}
    (hkf : Host.prog[kf]? = some (.label L))
    (hfirst : ∀ j, j < kf → Host.prog[j]? ≠ some (.label L))
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (hcallee : ∀ (ra : Int64) (m' : DataMem),
      (m' =⋆ Eq (ra.toUInt64.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) →
      Eventually (step1 Host.exe) (fun st => st.pc = ra ∧ Q st.data)
        ⟨{ s with regs := { s.regs with rsp := s.regs.rsp - 8 }, dmem := m' }, Host.addrOf kf⟩) :
    Program.wp [.callTo L] Q E s := by
  intro k hk
  apply Host.eventually_call (List.isInfixAt_singleton.mp hk) hkf hfirst hlen hmem
  intro m' hm'
  refine eventually_weaken _ _ _ _ ?_ (hcallee (Host.addrOf (k + 1)) m' hm')
  rintro st ⟨hpc, hq⟩
  exact Or.inl ⟨hpc, hq⟩

/-- Indirect register call `call *%r` at the `Program.wp` level. -/
public theorem Program.wp_callReg [Host] {r : Reg .W64} {tgt : Int64}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {old : List UInt8} {R : DataMem → Prop}
    (htgt : s.regs.get r = tgt.toBitVec)
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (hcallee : ∀ (ra : Int64) (m' : DataMem),
      (m' =⋆ Eq (ra.toUInt64.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) →
      Eventually (step1 Host.exe) (fun st => st.pc = ra ∧ Q st.data)
        ⟨{ s with regs := { s.regs with rsp := s.regs.rsp - 8 }, dmem := m' }, tgt⟩) :
    Program.wp [.callReg r] Q E s := by
  intro k hk
  apply Host.eventually_call_reg (List.isInfixAt_singleton.mp hk) htgt hlen hmem
  intro m' hm'
  refine eventually_weaken _ _ _ _ ?_ (hcallee (Host.addrOf (k + 1)) m' hm')
  rintro st ⟨hpc, hq⟩
  exact Or.inl ⟨hpc, hq⟩
