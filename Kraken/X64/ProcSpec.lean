module

public import Kraken.X64.OmniSemantics

/-!
# Procedure specifications

A *procedure specification* `ProcSpec e entry Pre Post` says that a run of the executable `e`
entered at `entry` in a state `t` with `Pre x ra t` reaches the address `ra` in a state `s'` with
`Post x ra t s'`.
-/

public section

/-- A run of `e` entered at `entry` in a state `t` with `Pre x ra t` reaches `ra` in a state `s'`
with `Post x ra t s'`. -/
@[expose] def Kraken.Executable.ProcSpec (e : _root_.Executable) (entry : Int64) {α : Type}
    (Pre : α → Int64 → MachineData → Prop)
    (Post : α → Int64 → MachineData → MachineData → Prop) : Prop :=
  ∀ (x : α) (ra : Int64) (t : MachineData), Pre x ra t →
    Eventually (step1 e) (fun st => st.pc = ra ∧ Post x ra t st.data) ⟨t, entry⟩
