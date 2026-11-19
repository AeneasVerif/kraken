module

public import Kraken.X64.WP.Basic
public import Kraken.X64.Stack

/-!
# Procedure specifications

A *procedure specification* `ProcSpec e entry Pre Post` says that a run of the executable `e`
entered at `entry` in a state `t` with `Pre x ra t` reaches the address `ra` in a state `s'` with
`Post x ra t s'`.

The one calling convention-independent fact about the x64 `call` instruction is `MachineData.pushRa`:
it stores the return address below `rsp` and moves `rsp`. `ProcSpec.wp_call` is the rule that uses a
callee's `ProcSpec`, stated at its label, at a `call` site of a fragment.
-/

public section

/-- The result of a successful `call` with return address `ra` on `s`. -/
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

/-- A run of `e` entered at `entry` in a state `t` with `Pre x ra t` reaches `ra` in a state `s'`
with `Post x ra t s'`. -/
@[expose] def Kraken.Executable.ProcSpec (e : _root_.Executable) (entry : Int64) {α : Type}
    (Pre : α → Int64 → MachineData → Prop)
    (Post : α → Int64 → MachineData → MachineData → Prop) : Prop :=
  ∀ (x : α) (ra : Int64) (t : MachineData), Pre x ra t →
    Eventually (step1 e) (fun st => st.pc = ra ∧ Post x ra t st.data) ⟨t, entry⟩

section
variable [Host]

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
