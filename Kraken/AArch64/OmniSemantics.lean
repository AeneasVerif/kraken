/-
Kraken AArch64 - proof infrastructure for effectful execution.

This mirrors the x86-64 proof layer over the AArch64 machine and effect types.
-/

import Kraken.OmniSemantics
import Kraken.AArch64.Semantics

/-- Every outcome allowed by an effectful AArch64 execution satisfies `post`. -/
def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v : α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

/-- One AArch64 instruction step, with all effects interpreted universally. -/
def step1 [Layout] (p : Executable) (s : MachineState)
    (post : @Post MachineState) : Prop :=
  (Executable.step p s .done).All post

/-- Straight-line AArch64 execution, with all effects interpreted universally. -/
def straightlineStep [Layout] (p : Executable) (s : MachineState)
    (post : @Post MachineState) : Prop :=
  (Executable.straightline p s .done).All post
