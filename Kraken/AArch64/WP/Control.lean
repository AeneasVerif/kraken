module

public import Kraken.AArch64.WP.Basic

/-!
# Control-flow step lemmas

Step lemmas, in continuation-passing form, for the control-flow instructions a compiler emits:
`b L`, `b.cc L`, `bl L`, `br r`, `blr r`, `ret`, `cbz r, L`, `cbnz r, L`, `tbz r, #b, L`, and
`tbnz r, #b, L`, at any position of any `Host` program. The encodings are the ones the parser
produces (`⸨prog| b L ⸩ = [Directive.bTo "L"]` etc.).

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

/-- `br r` -/
public abbrev Directive.br (r : XRegOrXzr) : Directive :=
  .instr { operation_size := .W64, operation := .BR (.low r .W64) }

/-- `blr r` -/
public abbrev Directive.blr (r : XRegOrXzr) : Directive :=
  .instr { operation_size := .W64, operation := .BLR (.low r .W64) }

/-- `ret` (to `x30`) -/
public abbrev Directive.ret : Directive :=
  .instr { operation_size := .W64, operation := .RET (.low (.reg .X30) .W64) }

/-- `cbz r, L` for `r` of width `w` (`x` or `w` register) -/
public abbrev Directive.cbzTo {w : RegWidth} (r : XRegOrXzr) (L : Label) : Directive :=
  .instr { operation_size := w, operation := .CBZ (.low r w) (.label L) }

/-- `cbnz r, L` for `r` of width `w` (`x` or `w` register) -/
public abbrev Directive.cbnzTo {w : RegWidth} (r : XRegOrXzr) (L : Label) : Directive :=
  .instr { operation_size := w, operation := .CBNZ (.low r w) (.label L) }

/-- `tbz r, #bit, L` for `r` of width `w` (`x` or `w` register) -/
public abbrev Directive.tbzTo {w : RegWidth} (r : XRegOrXzr) (bit : Nat) (L : Label) : Directive :=
  .instr { operation_size := w, operation := .TBZ (.low r w) bit (.label L) }

/-- `tbnz r, #bit, L` for `r` of width `w` (`x` or `w` register) -/
public abbrev Directive.tbnzTo {w : RegWidth} (r : XRegOrXzr) (bit : Nat) (L : Label) : Directive :=
  .instr { operation_size := w, operation := .TBNZ (.low r w) bit (.label L) }

/-- `adrp xd, L` -/
public abbrev Directive.adrp (d : XReg) (L : Label) : Directive :=
  .instr { operation_size := .W64, operation := .ADRP (.low (.reg d) .W64) (.label L) }

/-- `add xd, xs, :lo12:L` -/
public abbrev Directive.addLo12 (d s : XReg) (L : Label) : Directive :=
  .instr {
    operation_size := .W64,
    operation := .ADD_e (.low (.reg d) .W64) (.low (.reg s) .W64)
      (.imm { imm := .lo12 (.label L), shift := .S0 })
  }

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

/-- `br r` at index `i`, where `r` holds target address `tgt`. -/
public theorem Host.eventually_br {i : Nat} {r : XRegOrXzr} {tgt : Int64}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.br r))
    (htgt : s.regs.getRegOrZr (.low r .W64) = tgt.toBitVec)
    (h : Eventually (step1 Host.exe) post ⟨s, tgt⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All, htgt]
  have : Int64.ofInt tgt.toBitVec.signed = tgt := by simp [BitVec.signed]
  rw [this]
  exact h

/--
`blr r` at index `i`, where `r` holds target address `tgt` (read before `x30` is updated, so
`r = .reg .X30` is supported): `x30` holds the return address `Host.addrOf (i + 1)` and control is
at `tgt`. Memory is untouched.
-/
public theorem Host.eventually_blr {i : Nat} {r : XRegOrXzr} {tgt : Int64}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.blr r))
    (htgt : s.regs.getRegOrZr (.low r .W64) = tgt.toBitVec)
    (h : Eventually (step1 Host.exe) post
      ⟨{ s with regs := s.regs.setXReg .X30 (Host.addrOf (i + 1)).toBitVec }, tgt⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setRegOrZr,
    Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Effects.All, htgt]
  have hra : BitVec.ofInt 64 (Host.addrOf (i + 1)).toInt = (Host.addrOf (i + 1)).toBitVec := by
    rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  have hpc : Int64.ofInt tgt.toBitVec.signed = tgt := by simp [BitVec.signed]
  rw [hra, hpc]
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

/-- `tbz r, #bit, L` at index `i`, where `L` is first defined at index `k`. -/
public theorem Host.eventually_tbz {i k : Nat} {w : RegWidth} {r : XRegOrXzr} {bit : Nat}
    {L : Label} {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.tbzTo (w := w) r bit L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post
      ⟨s, if (s.regs.getRegOrZr (.low r w)).getLsbD bit then Host.addrOf (i + 1)
        else Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, Effects.All]
  rw [Host.label_eq_addrOf hk hfirst]
  split <;> simp_all [Effects.All]

/-- `tbnz r, #bit, L` at index `i`, where `L` is first defined at index `k`. -/
public theorem Host.eventually_tbnz {i k : Nat} {w : RegWidth} {r : XRegOrXzr} {bit : Nat}
    {L : Label} {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.tbnzTo (w := w) r bit L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post
      ⟨s, if (s.regs.getRegOrZr (.low r w)).getLsbD bit then Host.addrOf k
        else Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, Effects.All]
  rw [Host.label_eq_addrOf hk hfirst]
  split <;> simp_all [Effects.All]

omit [Host] in
private theorem bv64_page_add_lo12 (x : BitVec 64) :
    (x &&& ~~~0xFFF#64) + (x &&& 0xFFF#64) = x := by
  have hlo : (x &&& 0xFFF#64).toNat = x.toNat % 4096 := by
    rw [BitVec.toNat_and, show (0xFFF#64 : BitVec 64).toNat = 2 ^ 12 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod _ 12]
  have hhi : (x &&& ~~~0xFFF#64).toNat = (x.toNat >>> 12) <<< 12 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [BitVec.toNat_and, Nat.testBit_and, Nat.testBit_shiftLeft,
      show (~~~0xFFF#64 : BitVec 64).toNat = (2 ^ 52 - 1) <<< 12 from rfl,
      Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hi12 : i < 12
    · have hge : decide (12 ≤ i) = false := decide_eq_false (by omega)
      simp [hge]
    · have hge : decide (12 ≤ i) = true := decide_eq_true (by omega)
      by_cases hi64 : i < 64
      · have hlt52 : decide (i - 12 < 52) = true := decide_eq_true (by omega)
        simp [hge, hlt52, Nat.testBit_shiftRight]
        congr 1; omega
      · have hx : x.toNat.testBit i = false :=
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
        have hlt52 : decide (i - 12 < 52) = false := decide_eq_false (by omega)
        have hsh : (x.toNat >>> 12).testBit (i - 12) = false := by
          rw [Nat.testBit_shiftRight]
          exact Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hx, hge, hlt52, hsh]
  have hdiv : x.toNat / 2 ^ 12 * 2 ^ 12 + x.toNat % 4096 = x.toNat := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, hhi, hlo, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    hdiv, Nat.mod_eq_of_lt x.isLt]

/-- `adrp xd, L` at index `i`: sets `xd := (Labels.label L).toBitVec &&& ~~~0xFFF#64`. -/
public theorem Host.eventually_adrp {i : Nat} {d : XReg} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.adrp d L))
    (h : Eventually (step1 Host.exe) post
      ⟨{ s with regs := s.regs.setXReg d ((Labels.label L).toBitVec &&& ~~~0xFFF#64) },
        Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.interp,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Effects.All]
  rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  exact h

/-- `add xd, xs, :lo12:L` at index `i`: adds `(Labels.label L).toBitVec &&& 0xFFF#64` to `xs`. -/
public theorem Host.eventually_addLo12 {i : Nat} {d sr : XReg} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (.addLo12 d sr L))
    (h : Eventually (step1 Host.exe) post
      ⟨{ s with
          regs := s.regs.setXReg d
            ((s.regs.getXReg sr).toBitVec + ((Labels.label L).toBitVec &&& 0xFFF#64)) },
        Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, ExtOrImmReg.interp,
    ConstExpr.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
    Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take,
    BitVec.extractLsb'_eq_self, Effects.All]
  have hval : BitVec.ofInt 64 (Int64.toInt (Labels.label L)) = (Labels.label L).toBitVec := by
    rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  have hlo : BitVec.ofInt 64
      (Int64.toInt (Int64.ofNat (((Labels.label L).toBitVec &&& 0xFFF#64).toNat))) =
      (Labels.label L).toBitVec &&& 0xFFF#64 := by
    rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
    exact (BitVec.ofNat_toNat (m := 64) _).trans (BitVec.setWidth_eq _)
  rw [hval, hlo]
  exact h

/-- `adrp xd, L; add xd, xd, :lo12:L` at `i, i + 1` materializes exact
`(Labels.label L).toBitVec`. -/
public theorem Host.eventually_adrp_add_label {i : Nat} {d : XReg} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi0 : Host.prog[i]? = some (.adrp d L))
    (hi1 : Host.prog[i + 1]? = some (.addLo12 d d L))
    (h : Eventually (step1 Host.exe) post
      ⟨{ s with regs := s.regs.setXReg d (Labels.label L).toBitVec }, Host.addrOf (i + 2)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine Host.eventually_adrp hi0 (Host.eventually_addLo12 hi1 ?_)
  have hget : ((s.regs.setXReg d ((Labels.label L).toBitVec &&& ~~~0xFFF#64)).getXReg d).toBitVec =
      (Labels.label L).toBitVec &&& ~~~0xFFF#64 := by
    cases d <;> rfl
  have hset : ((s.regs.setXReg d ((Labels.label L).toBitVec &&& ~~~0xFFF#64)).setXReg d
      (Labels.label L).toBitVec) = s.regs.setXReg d (Labels.label L).toBitVec := by
    cases d <;> rfl
  rw [hget, bv64_page_add_lo12, hset]
  exact h

end

/-- Weakest precondition for `[.adrp d L, .addLo12 d d L]` materializing
`(Labels.label L).toBitVec`. -/
public theorem Program.wp_adrp_add_label [Host] (d : XReg) (L : Label) (s : MachineData) :
    Program.wp [.adrp d L, .addLo12 d d L]
      (fun s' => s' = { s with regs := s.regs.setXReg d (Labels.label L).toBitVec })
      (fun _ _ => False) s := by
  intro k hk
  obtain ⟨hi0, hi1⟩ := List.IsInfixAt.append (a := [Directive.adrp d L]) hk
  refine Host.eventually_adrp_add_label (List.isInfixAt_singleton.mp hi0)
    (List.isInfixAt_singleton.mp hi1) ?_
  exact .done _ (Or.inl ⟨rfl, rfl⟩)
