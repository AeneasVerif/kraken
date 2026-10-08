module

public import Kraken.X64.OmniSemantics

namespace Kraken.Executable

/-- The predecessor relation of the transition system induced by an executable. -/
-- This could replace `step` in the future. It doesn't rely on `Directives.interp` and
-- it is otherwise equivalent, given the usual assumptions about an `Executable`.
@[expose] public def step' (exe : Executable Directive) (st : MachineState) (P : @Post MachineState)
    : Prop :=
  match exe.fetch? st.2 with
  | none => False
  | some (d, z) =>
    let next := st.2 + .ofNat z
    haveI := Executable.labels exe
    (d.interp st.1 ⟨st.2, next⟩ (fun s => .done (s, next)) (fun a s => .done (s, a))).All P

end Kraken.Executable
