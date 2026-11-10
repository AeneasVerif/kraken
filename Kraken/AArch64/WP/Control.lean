module

public import Kraken.AArch64.WP.Basic

/-!
# Control-flow step lemmas

Step lemmas, in continuation-passing form, for the control-flow instructions a compiler emits:
`b L`, `b.cc L`, `bl L`, `ret`, `cbz r, L` and `cbnz r, L`, at any position of any `Host` program.
The encodings are the ones the parser produces (`parseAArch64("b L") = [Directive.bTo "L"]` etc.).

Labels resolve to their *first* definition in the host program (`Host.label_eq_addrOf`), so every
lemma that jumps to a label takes the hypothesis `hfirst` that no earlier directive defines the same
label. Under `Host.LabelsUnique` it is `hu.first hk`.
-/

/-- `b L` -/
public abbrev Directive.bTo (L : Label) : Directive :=
  .instr { operation_size := .W64, operation := .B (.label L) }

/-- `b.cc L` -/
public abbrev Directive.bCondTo (cc : CondCode) (L : Label) : Directive :=
  .instr { operation_size := .W64, operation := .B_cond cc (.label L) }

/-- `bl L` -/
public abbrev Directive.blTo (L : Label) : Directive :=
  .instr { operation_size := .W64, operation := .BL (.label L) }

/-- `ret` (to `x30`) -/
public abbrev Directive.ret : Directive :=
  .instr { operation_size := .W64, operation := .RET (.low (.reg .X30) .W64) }

/-- `cbz r, L` for `r` of width `w` (`x` or `w` register) -/
public abbrev Directive.cbzTo {w : RegWidth} (r : XRegOrXzr) (L : Label) : Directive :=
  .instr { operation_size := w, operation := .CBZ (.low r w) (.label L) }

/-- `cbnz r, L` for `r` of width `w` (`x` or `w` register) -/
public abbrev Directive.cbnzTo {w : RegWidth} (r : XRegOrXzr) (L : Label) : Directive :=
  .instr { operation_size := w, operation := .CBNZ (.low r w) (.label L) }

section
variable [Host]

/-- `b L` at index `i`, where `L` is first defined at index `k`. -/
public theorem Host.eventually_b {i k : Nat} {L : Label} {post : @Post MachineState}
    {s : MachineData}
    (hi : Host.prog[i]? = some (.bTo L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, Effects.All]
  rw [Host.label_eq_addrOf hk hfirst]
  exact h

/--
`b.cc L` at index `i`, where `L` is first defined at index `k`: continue at the label if the
condition holds in the current flags, and at the next directive otherwise.
-/
public theorem Host.eventually_bCond {i k : Nat} {cc : CondCode} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.bCondTo cc L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post
      ⟨s, if cc.interp s.status then Host.addrOf k else Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, Effects.All]
  rw [Host.label_eq_addrOf hk hfirst]
  split <;> simp_all [Effects.All]

/-- `b.cc L`, taken. -/
public theorem Host.eventually_bCond_taken {i k : Nat} {cc : CondCode} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.bCondTo cc L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (hcc : cc.interp s.status = true)
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ :=
  Host.eventually_bCond hi hk hfirst (by simp only [hcc, ↓reduceIte]; exact h)

/-- `b.cc L`, not taken. Nothing is needed about the label: it may even be undefined. -/
public theorem Host.eventually_bCond_fallthrough {i : Nat} {cc : CondCode} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.bCondTo cc L))
    (hcc : cc.interp s.status = false)
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All, hcc]
  exact h

/--
`bl L` at index `i`, where `L` is first defined at index `k`: `x30` holds the return address
`Host.addrOf (i + 1)` and control is at the label. Memory is untouched.
-/
public theorem Host.eventually_bl {i k : Nat} {L : Label} {post : @Post MachineState}
    {s : MachineData}
    (hi : Host.prog[i]? = some (.blTo L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post
      ⟨{ s with regs := s.regs.setXReg .X30 (Host.addrOf (i + 1)).toBitVec }, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Effects.All]
  rw [Host.label_eq_addrOf hk hfirst]
  have hra : BitVec.ofInt 64 (Host.addrOf (i + 1)).toInt = (Host.addrOf (i + 1)).toBitVec := by
    rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  rw [hra]
  exact h

/-- `ret` at index `i`, with the return address `ra` in `x30`: control is at `ra`. -/
public theorem Host.eventually_ret {i : Nat} {post : @Post MachineState} {s : MachineData}
    {ra : Int64}
    (hi : Host.prog[i]? = some .ret)
    (hra : s.regs.X30 = ra.toUInt64)
    (h : Eventually (step1 Host.exe) post ⟨s, ra⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Reg64s.getRegOrZr,
    Reg64s.getRegOrZr64, RegOrZr.base, Reg64s.getXReg, Effects.All, hra]
  have : Int64.ofInt (BitVec.take ra.toUInt64.toBitVec 64).signed = ra := by
    simp [BitVec.take, BitVec.signed, Int64.toBitVec_toUInt64]
  rw [this]
  exact h

/--
`cbz r, L` at index `i`, where `L` is first defined at index `k`: continue at the label if `r` is
zero, and at the next directive otherwise.
-/
public theorem Host.eventually_cbz {i k : Nat} {w : RegWidth} {r : XRegOrXzr} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.cbzTo (w := w) r L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post
      ⟨s, if s.regs.getRegOrZr (.low r w) = 0 then Host.addrOf k else Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, Effects.All]
  rw [Host.label_eq_addrOf hk hfirst]
  split <;> simp_all [Effects.All]

/--
`cbnz r, L` at index `i`, where `L` is first defined at index `k`: continue at the label if `r` is
nonzero, and at the next directive otherwise.
-/
public theorem Host.eventually_cbnz {i k : Nat} {w : RegWidth} {r : XRegOrXzr} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.cbnzTo (w := w) r L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post
      ⟨s, if s.regs.getRegOrZr (.low r w) = 0 then Host.addrOf (i + 1) else Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, Effects.All]
  rw [Host.label_eq_addrOf hk hfirst]
  split <;> simp_all [Effects.All]

end
