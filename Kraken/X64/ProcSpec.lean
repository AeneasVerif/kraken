module

public import Kraken.X64.OmniSemantics

/-!
# Procedure specifications

A *procedure specification* `ProcSpec e entry ra Pre Post` says that a run of the executable `e`
entered at `entry` in a state `t` with `Pre t` reaches the address `ra` in a state `s'` with
`Post t s'`.
-/

public section

@[expose] def Kraken.Executable.ProcSpec (e : _root_.Executable) (entry ra : Int64)
    (Pre : MachineData → Prop) (Post : MachineData → MachineData → Prop) : Prop :=
  ∀ t : MachineData, Pre t →
    Eventually (step1 e) (fun st => st.pc = ra ∧ Post t st.data) ⟨t, entry⟩
