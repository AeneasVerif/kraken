/-
Omnisemantics for x64.
-/

import Kraken.Attribute
import Kraken.OmniSemantics
import Kraken.X64.Semantics

@[kstep] def Effects.All {α : Type} (post : α → Prop) : Effects α → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined _ β _ cont => ∀ v : β, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

/-- `All` is monotone in its postcondition. -/
theorem Effects.All.imp {α : Type} {post₁ post₂ : α → Prop} {m : Effects α}
    (h : ∀ a, post₁ a → post₂ a) : m.All post₁ → m.All post₂ := by
  induction m <;> simp only [Effects.All] <;> intro hall
  case done a => exact h a hall
  case unimplemented => exact hall
  case gp_unaligned => exact hall
  case nonmem_load => exact hall
  case nonmem_store => exact hall
  case undefined ret ih => exact fun v => ih v (hall v)
  case require_read_access _ _ _ ih => exact ih () hall
  case require_write_access _ _ _ ih => exact ih () hall
  case require_exec_access _ _ ih => exact ih () hall

/-- Universal interpretation turns effect sequencing into nested `All`. -/
theorem Effects.all_bind {α β : Type} {m : Effects α} {k : α → Effects β}
    {post : β → Prop} :
    (m.bind k).All post ↔ m.All fun a => (k a).All post := by
  induction m <;> simp [Effects.bind, Effects.All, *]

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

/-- Execute `n` applications of the existing single-step semantics. -/
def Executable.runSteps (e : Executable) : Nat → MachineState → Effects MachineState
  | 0, s => .done s
  | n + 1, s => (e.step s .done).bind (e.runSteps n)

/-- A successful batched execution is a finite `step1` execution. -/
theorem Executable.runSteps_all_eventually [Layout] (e : Executable) (n : Nat)
    (s : MachineState) (post : @Post MachineState)
    (h : (e.runSteps n s).All post) : Eventually (step1 e) post s := by
  induction n generalizing s with
  | zero => exact .done s h
  | succ n ih =>
      apply step_cps
      exact Effects.All.imp (fun mid hmid => ih mid hmid) (Effects.all_bind.mp h)

private def twoNops : Executable :=
  (0, [
    (.instr (.regular .W64 .W64 (.nop 1)), 1),
    (.instr (.regular .W64 .W64 (.nop 1)), 1)
  ])

-- `runSteps` threads the state produced by each step into the next one.
example [Layout] (s : MachineData) :
    Eventually (step1 twoNops) (fun st => st.2 = 2) (s, 0) := by
  apply Executable.runSteps_all_eventually twoNops 2
  simp [twoNops, Executable.runSteps, Executable.step,
    Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    Effects.bind, Effects.All]
