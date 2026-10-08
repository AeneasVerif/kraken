module

public import Kraken.X64.OmniSemantics

namespace Kraken.Executable

/-
# Step relation of an executable's transition system

An executable defines a transition system over machine states.

`Executable.step'` below encodes the must-predecessor relation of the transition system.
Given a set of successor machine states `post`, `exe.step' st post` holds iff
`∀ st', (st ⤳[exe] st') → st' ∈ post`.
This definition is expressed in terms of `Directive.interp`, which is considered ground truth.

Side note: Cousot calls `Executable.step'` the "dual preimage property transformer" in his
2021 book "Principles of Abstract Interpretation", as a starting point for theory exploration.
-/

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
