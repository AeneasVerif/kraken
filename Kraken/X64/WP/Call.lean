module

public import Kraken.X64.WP.Basic
public import Kraken.X64.Stack

/-!
# Procedures by specification

A *procedure specification* `ProcSpec e entry Pre Post` says that a run of the executable `e`
entered at `entry` in a state `t` with `Pre x ra t` reaches the address `ra` in a state `s'` with
`Post x ra t s'`. It is a proposition about the executable alone, so it can be assumed by one proof
(a caller) and established by another (the callee's), and it can be the subject of an induction.

Nothing in `ProcSpec` mentions the stack or any register: how `ra` is handed over and what the
callee must preserve is part of `Pre` and `Post`, and is fixed by a *calling convention*
(`Kraken.X64.SysV`, `Kraken.X64.Win64`). The one convention-independent fact about the x64 `call`
instruction is `MachineData.pushRa`: it stores the return address below `rsp` and moves `rsp`.
`ProcSpec.wp_call` is the rule that uses a callee's `ProcSpec`, stated at its label, at a `call`
site of a fragment.
-/

public section

/-! ## The stack at a call -/

/-- The state a `call` leaves behind: the return address `ra` stored at `rsp - 8`, and `rsp`
moved down by 8. -/
@[expose] def MachineData.pushRa (s : MachineData) (ra : Int64) : MachineData :=
  { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - Width.W64.bytesv),
           dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
             Width.W64.bytes ra.toBitVec.toInt }

@[simp] theorem MachineData.dmem_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp - 8) 8 ra.toBitVec.toInt := rfl

@[simp] theorem MachineData.get64_pushRa (s : MachineData) (ra : Int64) (r : Reg64) :
    (s.pushRa ra).regs.get64 r = if r = .rsp then s.regs.get64 .rsp - 8 else s.regs.get64 r := by
  cases r <;> simp [MachineData.pushRa, Reg64s.set64, Reg64s.get64]

@[simp] theorem MachineData.zmms_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).zmms = s.zmms := rfl

@[simp] theorem MachineData.status_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).status = s.status := rfl

@[simp] theorem MachineData.df_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).df = s.df := rfl

/-! ## Procedure specifications -/

/-- A run of `e` entered at `entry` in a state `t` with `Pre x ra t` reaches `ra` in a state `s'`
with `Post x ra t s'`. `x` is a logical variable that the call site instantiates (the argument, the
caller's memory frame). `Post` sees the entry state `t`, so that it can say which registers and
memory are as they were.

TODO: we don't use the `Layout` here, but we need it to use `step1`; we may be able to clean this up.
-/
@[expose] def Kraken.Executable.ProcSpec [_root_.Layout] (e : _root_.Executable) (entry : Int64) {α : Type}
    (Pre : α → Int64 → MachineData → Prop)
    (Post : α → Int64 → MachineData → MachineData → Prop) : Prop :=
  ∀ (x : α) (ra : Int64) (t : MachineData), Pre x ra t →
    Eventually (step1 e) (fun st => st.pc = ra ∧ Post x ra t st.data) ⟨t, entry⟩

/-! ## The call rule -/

section
variable [Host]

/-- A direct `call f` in a fragment, through the specification of the procedure at `f`: if the
return-address slot below `rsp` is mapped, the callee's precondition holds at the pushed state for
the return address `ra` (the address behind the `call`, wherever the fragment is placed), and the
callee's postcondition implies `Q`, then the fragment `[call f]` reaches its end with `Q`. -/
theorem Kraken.Executable.ProcSpec.wp_call {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} {f : Label}
    (hspec : Host.exe.ProcSpec (label f) Pre Post) {asz osz : Width} (x : α) {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData}
    (hslot : (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8) 8).isSome)
    (hpre : ∀ ra, Pre x ra (s.pushRa ra))
    (hpost : ∀ ra s', Post x ra (s.pushRa ra) s' → Q s') :
    Program.wp
      [.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction))))]
      Q E s := by
  intro k hk
  refine Host.run_cons hk ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  refine Effects.All_store hslot ?_
  simp only [Effects.All]
  have htarget : Int64.ofBitVec (Host.addrOf (k + 1) + (label f - Host.addrOf (k + 1))).toBitVec
      = label f := by
    rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  rw [htarget]
  refine eventually_weaken _ _ _ _ ?_ (hspec x (Host.addrOf (k + 1)) _ (hpre _))
  rintro ⟨s', pc⟩ ⟨hpc, hp⟩
  exact Or.inl ⟨by simpa using hpc, hpost _ _ hp⟩

/-- `wp_call` with the return-address slot given as an owned cell at the head of the caller's
memory, the form a caller's own frame usually provides. The callee's precondition may then assume
that the slot holds the return address and the rest of the memory is unchanged. -/
theorem Kraken.Executable.ProcSpec.wp_call_owned {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    {f : Label} (hspec : Host.exe.ProcSpec (label f) Pre Post) {asz osz : Width} (x : α) {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} {R : Mem 64 → Prop}
    (hmem : s.dmem =⋆ Kraken.X64.Stack.Owned 8 (s.regs.get64 .rsp - 8) ⋆ R)
    (hpre : ∀ ra, ((s.pushRa ra).dmem =⋆ Kraken.X64.Stack.RetCell ra (s.regs.get64 .rsp - 8) ⋆ R) →
      Pre x ra (s.pushRa ra))
    (hpost : ∀ ra s', Post x ra (s.pushRa ra) s' → Q s') :
    Program.wp
      [.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction))))]
      Q E s := by
  obtain ⟨bs, hbs, hmem⟩ := Kraken.X64.Stack.Owned.elim hmem
  refine hspec.wp_call x ?_ (fun ra => hpre ra (Mem.storeInt_sep _ 8 bs R _ ⟨hmem, hbs⟩ _))
    hpost
  rw [Mem.loadInt_sep bs _ 8 R _ hmem hbs (by decide)]; rfl

end
