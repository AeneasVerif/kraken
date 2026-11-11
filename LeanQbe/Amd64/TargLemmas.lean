module

public import LeanQbe.Amd64.Targ
public import LeanQbe.Amd64.IselLemmas
import Kraken.X64.Parser
import all Kraken.Separation
import all Kraken.Mem

/-!
# x64 target lemmas and the `Target` instance

Step lemmas for the control-flow and frame directives of `Targ.lean` (the operation snippets are
in `IselLemmas.lean`), generic in the `Host` and the position, in continuation form, then
`Amd64.target : Target`.

Generic control-flow lemmas come from Kraken (`Kraken/X64/WP/`, `Kraken/X64/Regs.lean`).
-/

@[expose] public section

namespace LeanQbe.Amd64

/-! ## Encodings are the parser's -/

section ParserChecks
open Kraken.X64.Parser
example : parse("test %eax, %eax
jnz L") = jnz .rax "L" := rfl
example : parse("jmp L") = jmp "L" := rfl
example : parse("ret") = ret := rfl
end ParserChecks

section
variable [Host]

theorem eventually_jmp {k j : Nat} {l : Label} {s : MachineData} {post : (MachineState → Prop)}
    (hc : (jmp l).IsInfixAt Host.prog k) (hj : Labels.label l = Host.addrOf j)
    (hk : Run j s post) :
    Run k s post := by
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All]
  rw [hj, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk

theorem eventually_jnz {k j : Nat} {r : Reg64} {l : Label} {s : MachineData}
    {post : (MachineState → Prop)}
    (hc : (jnz r l).IsInfixAt Host.prog k) (hj : Labels.label l = Host.addrOf j)
    (hk : ∀ s' : MachineData, s'.regs = s.regs → s'.dmem = s.dmem →
      (Truthy (s.regs.get64 r) → Run j s' post) ∧
      (¬ Truthy (s.regs.get64 r) → Run (k + 2) s' post)) :
    Run k s post := by
  obtain ⟨h0, hc1⟩ := hc.cons
  obtain ⟨h1, -⟩ := hc1.cons
  refine Host.eventually_of_interp_cps h0 ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Effects.All, Reg64s.get_low32]
  intro af
  refine Host.eventually_of_interp_cps h1 ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All, CondCode.interp,
    StatusFlags.from_result, BitVec.and_self]
  by_cases h0 : Truthy (s.regs.get64 r)
  · have : ((s.regs.get64 r).setWidth 32 == BitVec.zero 32) = false := by
      simpa [BitVec.zero, Truthy] using h0
    simp only [this, Bool.not_false, ↓reduceIte, Effects.All]
    rw [hj]
    refine (hk _ ?_ ?_).1 h0 <;> rfl
  · have : ((s.regs.get64 r).setWidth 32 == BitVec.zero 32) = true := by
      simpa [BitVec.zero, Truthy] using h0
    simp only [this, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Effects.All]
    refine (hk _ ?_ ?_).2 h0 <;> rfl

theorem eventually_ret {k : Nat} {s : MachineData} {ra : Int64} {R : DataMem → Prop}
    {post : (MachineState → Prop)}
    (hc : ret.IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ Eq (ra.toUInt64.At (s.regs.get64 .rsp)) ⋆ R)
    (hk : Eventually (step1 Host.exe) post
      ⟨{ s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) }, ra⟩) :
    Run k s post :=
  Host.eventually_ret (List.isInfixAt_singleton.mp hc) hmem hk

end

/-! ## Frame directives (moved from FrameLemmas.lean, written by memframe) -/

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

/-- `call l` to wherever `l` resolves (the callee need not be in a known position). -/
theorem eventually_callD_any {i : Nat} {l : Label} {s : MachineData} {F : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (callD l))
    (hmem : s.dmem =⋆ region (s.regs.get64 .rsp - 8#64) 8 ⋆ F)
    (hk : ∀ s' : MachineData, s'.regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) →
      (s'.dmem =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.get64 .rsp - 8#64)) ⋆ F) →
      Eventually (step1 Host.exe) post ⟨s', Labels.label l⟩) :
    Run i s post := by
  obtain ⟨bs, hl, hbs⟩ := region_sep_elim hmem
  refine Host.eventually_of_interp_cps hi ?_
  simp only [callD, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  refine (store_All_of_sep _ _ .W64 _ _ _ bs F ?_ hl).mpr ?_
  · exact hbs
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk _ rfl (Mem.storeInt_sep _ 8 bs F s.dmem ⟨hbs, hl⟩ _)

/-- `add %rs, %rd`: `rd := rs + rd` (flags arbitrary). -/
theorem eventually_addRR {i : Nat} {rd rs : Reg64} {s : MachineData} {post : MachineState → Prop}
    (hi : Host.prog[i]? = some (ins (.add (.reg (q rd)) (.reg (q rs)))))
    (hk : ∀ s' : MachineData,
      s'.regs = s.regs.set64 rd (s.regs.get64 rs + s.regs.get64 rd) → s'.dmem = s.dmem →
      Run (i + 1) s' post) :
    Run i s post := by
  refine Host.eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg, Effects.All, set_q, get_q]
  exact hk _ rfl rfl

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


theorem spEntry_call (sp : Val) (ns : Nat) (h : (sp + 8#64).toNat % 16 = 0) :
    (sp - BitVec.ofNat 64 (frameSize ns) - BitVec.ofNat 64 8 + 8#64).toNat % 16 = 0 := by
  have e : sp - BitVec.ofNat 64 (frameSize ns) - BitVec.ofNat 64 8 + 8#64 =
      sp - BitVec.ofNat 64 (frameSize ns) := by
    rw [BitVec.sub_add_cancel]
  rw [e]
  have hsp := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h
  simp only [frameSize, BitVec.toNat_sub, BitVec.toNat_ofNat]
  split <;> omega

theorem prologue_spec [Host] {k ns : Nat} {s : MachineData} {ra : Int64} {G : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hc : [subSpD (Int64.ofNat (frameSize ns))].IsInfixAt Host.prog k)
    (hF : frameSize ns + 8 ≤ 2 ^ 64)
    (hmem : s.dmem =⋆ Eq (ra.toUInt64.At (s.regs.get64 .rsp)) ⋆
      region (s.regs.get64 .rsp - BitVec.ofNat 64 (frameSize ns)) (frameSize ns) ⋆ G)
    (hk : ∀ s' : MachineData, s'.regs.get64 .rsp = s.regs.get64 .rsp - BitVec.ofNat 64 (frameSize ns) →
      (∀ r, r ∉ Reg64.rsp :: ([] ++ scratchRegs) → s'.regs.get64 r = s.regs.get64 r) →
      (s'.dmem =⋆ (region (s.regs.get64 .rsp - BitVec.ofNat 64 (frameSize ns) +
          BitVec.ofNat 64 (8 * ns)) (frameSize ns - 8 * ns) ⋆
          Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆
        region (s.regs.get64 .rsp - BitVec.ofNat 64 (frameSize ns)) (8 * ns) ⋆ G) →
      Run (k + 1) s' post) :
    Run k s post := by
  refine eventually_subSpD (List.isInfixAt_singleton.mp hc) fun s' hs hm => hk s' ?_ ?_ ?_
  · rw [hs, Reg64s.get64_set64_same]; simp
  · intro r hr
    rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]
  · have hle : 8 * ns ≤ frameSize ns := by simp only [frameSize]; split <;> omega
    have e : frameSize ns = 8 * ns + (frameSize ns - 8 * ns) := by omega
    rw [hm]
    rw [e, region_split (by omega), ← e] at hmem
    ac_nf at hmem ⊢

theorem epilogue_spec [Host] {k ns : Nat} {s : MachineData} {ra : Int64} {G : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hc : [addSpD (Int64.ofNat (frameSize ns))].IsInfixAt Host.prog k)
    (hmem : s.dmem =⋆ (region (s.regs.get64 .rsp + BitVec.ofNat 64 (frameSize ns) -
          BitVec.ofNat 64 (frameSize ns) + BitVec.ofNat 64 (8 * ns)) (frameSize ns - 8 * ns) ⋆
          Eq (ra.toUInt64.At (s.regs.get64 .rsp + BitVec.ofNat 64 (frameSize ns)))) ⋆ G)
    (hk : ∀ s' : MachineData, s'.regs.get64 .rsp = s.regs.get64 .rsp + BitVec.ofNat 64 (frameSize ns) →
      True →
      (∀ r, r ∉ Reg64.rsp :: ([] ++ scratchRegs) → s'.regs.get64 r = s.regs.get64 r) →
      (s'.dmem =⋆ Eq (ra.toUInt64.At (s.regs.get64 .rsp + BitVec.ofNat 64 (frameSize ns))) ⋆
        region (s.regs.get64 .rsp + BitVec.ofNat 64 (8 * ns)) (frameSize ns - 8 * ns) ⋆ G) →
      Run (k + 1) s' post) :
    Run k s post := by
  refine eventually_addSpD (List.isInfixAt_singleton.mp hc) fun s' hs hm => hk s' ?_ trivial ?_ ?_
  · rw [hs, Reg64s.get64_set64_same]; simp
  · intro r hr
    rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]
  · rw [hm]
    rw [BitVec.add_sub_cancel] at hmem
    ac_nf at hmem ⊢


/-! ## The `Target` instance -/

/-- One step of the laid-out host program `h`. -/
def hostStep (h : Host) : MachineState → (MachineState → Prop) → Prop :=
  letI := h; step1 Host.exe

/-- The address label `l` resolves to in host `h`. -/
def hostLabel (h : Host) (l : Label) : Int64 :=
  letI := h; Labels.label l

/-- Kraken x64 as a `Target`. -/
@[reducible] def target : Target where
  toIsa := isa
  MData := MachineData
  Addr := Int64
  State := MachineState
  Host := Host
  get s r := s.regs.get64 r
  mem s := s.dmem
  mkState s a := ⟨s, a⟩
  pc st := st.pc
  data st := st.data
  pc_mk _ _ := rfl
  data_mk _ _ := rfl
  mk_eta _ := rfl
  prog h := @Host.prog h
  addrOf h k := @Host.addrOf h k
  labelAddr := hostLabel
  step := hostStep
  raBytes := 8
  RetAddr sp ra := Eq (ra.toUInt64.At sp)
  raReg _ _ := True
  spEntry sp := (sp + 8#64).toNat % 16 = 0
  Saved sp ra ns := region (sp - BitVec.ofNat 64 (frameSize ns) + BitVec.ofNat 64 (8 * ns))
    (frameSize ns - 8 * ns) ⋆ Eq (ra.toUInt64.At sp)
  spOk _ := True
  sp_not_scratch := by simp
  sp_not_allocatable := by simp
  scratch_not_allocatable := by simp
  calleeSaved_not_scratch := by simp
  calleeSaved_not_allocatable := by simp
  sp_not_calleeSaved := by simp
  argRegs_not_scratch := by simp
  retRegs_not_scratch := by simp
  sp_not_retRegs := by simp
  sp_not_argRegs := by simp
  calleeSaved_not_argRegs := by simp
  calleeSaved_not_retRegs := by simp
  retAddr_region _ ra _ h := ⟨ra.toUInt64.toBytes, UInt64.toBytes_length _, h.symm⟩
  raReg_congr _ _ _ _ _ := trivial
  raReg_of_raRegs _ _ _ _ _ := trivial
  raRegs_not_allocatable := by simp
  raRegs_not_scratch := by simp
  raRegs_not_calleeSaved := by simp
  raRegs_not_argRegs := by simp
  raRegs_not_retRegs := by simp
  sp_not_raRegs := by simp
  slots_le_frameSize ns := by simp only [frameSize]; split <;> omega
  spOk_frame _ _ _ := trivial
  spEntry_call := spEntry_call
  prologue_spec {h} {_} {_} {_} {_} {_} {_} hc _ _ hF hmem hk := by
    letI := h; exact prologue_spec hc hF hmem hk
  epilogue_spec {h} {_} {_} {_} {_} {_} {_} hc _ _ hmem hk := by
    letI := h; exact epilogue_spec hc hmem hk
  slotSt_spec {h} {_} {_} {_} {_} {_} {_} hc _ _ hmem hk := by
    letI := h
    exact eventually_stSpD (List.isInfixAt_singleton.mp hc) hmem fun s' hs hm =>
      hk s' (fun r _ => by rw [hs]) hm
  slotLd_spec {h} {_} {_} {rd} {_} {_} {_} {_} hc _ hmem hk := by
    letI := h
    refine eventually_ldSpD (List.isInfixAt_singleton.mp hc) hmem fun s' hs hm =>
      hk s' ?_ (fun r hr => ?_) hm
    · show s'.regs.get64 rd = _
      rw [hs, Reg64s.get64_set64_same]
    · show s'.regs.get64 r = _
      rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]
  call_spec {h} {_} {_} {s} {_} {_} hc hmem hk := by
    letI := h
    refine eventually_callD_any (List.isInfixAt_singleton.mp hc) hmem fun s' hs hm =>
      hk s' ?_ (fun r hr => ?_) trivial ?_
    · show s'.regs.get64 .rsp = _
      rw [hs, Reg64s.get64_set64_same]
    · show s'.regs.get64 r = _
      rw [hs, Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (by simp [he])]
    · show (Eq _ ⋆ _) s'.dmem
      have e : s'.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 := by
        rw [hs, Reg64s.get64_set64_same]
      show (Eq ((Host.addrOf (_ + 1)).toUInt64.At (s'.regs.get64 .rsp)) ⋆ _) s'.dmem
      rw [e]; exact hm
  tailJmp_spec {h} {_} {_} {s} {_} hc hk := by
    letI := h
    exact eventually_jmpD_any (List.isInfixAt_singleton.mp hc) (hk s (fun _ _ => rfl) rfl)
  labelAddr_eq {h} {_} {_} hk hfirst := letI := h; Host.label_eq_addrOf hk hfirst
  label_spec {h} {_} {_} {_} {_} hi hrun := letI := h; Host.eventually_label hi hrun
  mov_spec {h} {_} {_} {_} {_} {_} hc hk := letI := h; eventually_mov hc hk
  movi_spec {h} {_} {_} {_} {_} {_} hc hk := letI := h; eventually_movi hc hk
  op_spec {h} {_} {_} {_} {_} {_} {_} {_} hop hc hvars hv hk :=
    letI := h; eventually_op hop hc hvars hv hk
  load_spec {h} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} hop hc _ hv hk :=
    letI := h; eventually_load hop hc hv hk
  store_spec {h} {_} {_} {_} {_} {_} {_} {_} hop hc hvars hok hk :=
    letI := h; eventually_store hop hc hvars hok hk
  jmp_spec {h} {_} {_} {_} {s} {_} hc hj hk :=
    letI := h; eventually_jmp hc hj (hk s (fun _ _ => rfl) rfl)
  jnz_spec {h} {_} {_} {_} {_} {_} {_} hc hj _ hk := by
    letI := h
    exact eventually_jnz hc hj fun s' hregs hmem =>
      hk s' (fun r _ => congrArg (Reg64s.get64 · r) hregs) hmem
  jnzCmp_spec {h} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} hop hc hj hvars hv hk := by
    letI := h; exact eventually_jnzCmp hop hc hj hvars hv hk
  ret_spec {h} {_} {s} {_} {_} {_} hc _ hmem hk := by
    letI := h
    refine eventually_ret hc hmem (hk _ (fun r hr => ?_) ?_ rfl)
    · exact Reg64s.get64_set64_of_ne _ _ _ _ fun he => hr (he ▸ List.mem_cons_self)
    · exact Reg64s.get64_set64_same s.regs .rsp _

/-- Labels of size 0, every other directive of size 4, from `0x1000`. -/
@[instance_reducible] def layoutOf (p : Program) : Layout :=
  { start := 0x1000, size := fun i => match p[i]? with | some (.label _) => 0 | _ => 4 }

theorem layoutOf_zero (p : Program) :
    ∀ i d, p[i]? = some d → @Kraken.Layout.size _ (layoutOf p) i = 0 → ∃ l, d = .label l := by
  intro i d hd hz
  cases d
  case label l => exact ⟨l, rfl⟩
  all_goals
    have hz' : (match p[i]? with | some (.label _) => 0 | _ => 4) = 0 := hz
    rw [hd] at hz'
    simp at hz'

private theorem sum_sized_mapIdx_le_four (sz : Nat → Nat) (hsz : ∀ i, sz i ≤ 4) :
    ∀ (xs : List Directive) (k : Nat),
      (List.map (·.size)
        (List.mapIdx (fun i d => ({ directive := d, size := sz (k + i) } : Kraken.Sized Directive)) xs)).sum ≤
        4 * xs.length
  | [], _ => by simp
  | _ :: xs, k => by
    rw [List.mapIdx_cons, List.map_cons, List.sum_cons, List.length_cons]
    have h0 : sz (k + 0) ≤ 4 := hsz (k + 0)
    have ih := sum_sized_mapIdx_le_four sz hsz xs (k + 1)
    have hconv : (List.mapIdx (fun i d => ({ directive := d, size := sz (k + (i + 1)) } : Kraken.Sized Directive)) xs) =
        (List.mapIdx (fun i d => ({ directive := d, size := sz (k + 1 + i) } : Kraken.Sized Directive)) xs) := by
      congr 1; funext i d; congr 2; omega
    rw [hconv]
    dsimp only
    omega

theorem layoutOf_small (p : Program) (h : 4 * p.length < 2 ^ 64) :
    (@Kraken.Layout.apply _ (layoutOf p) p).sizeBefore p.length < 2 ^ 64 := by
  refine Nat.lt_of_le_of_lt ?_ h
  simp only [Kraken.Executable.sizeBefore, Kraken.Layout.apply]
  rw [List.take_of_length_le (by simp)]
  simpa using sum_sized_mapIdx_le_four (fun i => @Kraken.Layout.size _ (layoutOf p) i)
    (fun i => by
      show (match p[i]? with | some (.label _) => 0 | _ => 4) ≤ 4
      split <;> decide) p 0

def labelsNodup (p : Program) : Bool :=
  decide ((p.filterMap fun | .label l => some l | _ => none).Nodup)

def targetLayout : TargetLayout target where
  labelsNodup := labelsNodup
  layoutOf prog h := .ofLayout prog (layoutOf prog) (layoutOf_zero prog) (layoutOf_small prog h)
  prog_layoutOf _ _ := rfl
  labelsUnique_layoutOf {prog} h hnd :=
    letI : Host := .ofLayout prog (layoutOf prog) (layoutOf_zero prog) (layoutOf_small prog h)
    Host.labelsUnique_of_nodup (of_decide_eq_true hnd)

/-- `n`-byte zero stack below `rsp = 0x0ff8`, return address `ra` at `0x0ff8`, and payload `bs` at `0x1000`. -/
def initMem (n : Nat) (ra : Int64) (bs : List UInt8) : Mem 64 :=
  ((stackZeros n ++ ra.toUInt64.toBytes) ++ bs).At (0x0ff8#64 - BitVec.ofNat 64 n)

theorem initMem_entry (n : Nat) (ra : Int64) (bs : List UInt8)
    (hn : n ≤ 2048) (hbs : bs.length ≤ 8192) :
    initMem n ra bs =⋆
      Eq (bs.At 0x1000#64) ⋆
      ((fun f => ∃ zs : List UInt8, zs.length = n ∧ f = zs.At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆
        Eq (ra.toUInt64.At 0x0ff8#64)) ⋆
      Std.ExtHashMap.emp := by
  have hra : ra.toUInt64.toBytes.length = 8 := UInt64.toBytes_length _
  have hzs : (stackZeros n).length = n := stackZeros_length n
  rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
  have h1 := Mem.At_append_sep (stackZeros n ++ ra.toUInt64.toBytes) bs
    (0x0ff8#64 - BitVec.ofNat 64 n)
    (by simp only [List.length_append, hzs, hra]; omega)
  have e2 : 0x0ff8#64 - BitVec.ofNat 64 n + BitVec.ofNat 64 (stackZeros n).length = 0x0ff8#64 := by
    rw [hzs, BitVec.sub_add_cancel]
  have e1 : 0x0ff8#64 - BitVec.ofNat 64 n + BitVec.ofNat 64 (stackZeros n ++ ra.toUInt64.toBytes).length =
      0x1000#64 := by
    simp only [List.length_append, hzs, hra]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e1] at h1
  have h2 := Mem.At_append_sep (stackZeros n) ra.toUInt64.toBytes (0x0ff8#64 - BitVec.ofNat 64 n)
    (by simp only [hzs, hra]; omega)
  rw [e2] at h2
  have h0 : (Eq (((stackZeros n ++ ra.toUInt64.toBytes) ++ bs).At (0x0ff8#64 - BitVec.ofNat 64 n)))
      (initMem n ra bs) := rfl
  rw [h1] at h0
  refine sep_mono (fun f hf => ?_) h0
  rw [h2] at hf
  exact sep_mono (fun f1 hf1 => ⟨stackZeros n, hzs, hf1.symm⟩) hf

theorem initMem_empty_entry (n : Nat) (ra : Int64) (hn : n ≤ 2048) :
    initMem n ra [] =⋆
      ((fun f => ∃ zs : List UInt8, zs.length = n ∧ f = zs.At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆
        Eq (ra.toUInt64.At 0x0ff8#64)) ⋆
      Std.ExtHashMap.emp := by
  have h := initMem_entry n ra [] hn (by decide)
  have hemp : Eq (([] : List UInt8).At 0x1000#64) = Std.ExtHashMap.emp := by
    funext f; simp [List.At, Std.ExtHashMap.emp]
  rwa [hemp, Std.ExtHashMap.emp_sep] at h

end LeanQbe.Amd64
