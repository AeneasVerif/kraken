module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .padding_executed _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post
  | .undefined_label _ => False

@[ksimp] theorem Effects.All_require_read_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

def step1 (e : Executable) (labels : Labels := e.labels) (s : MachineState) (post : @Post MachineState) : Prop :=
  (e.step labels s .done).All post

def straightlineStep (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

attribute [kstep] Kraken.Layout.apply Kraken.Layout.size Labels.label Labels.label?
attribute [ksimp] List.mapIdx_cons List.mapIdx_nil List.findSome?_cons List.findSome?_nil
  Kraken.Executable.withAddresses_nil Kraken.Executable.withAddresses_cons

@[ksimp] theorem Labels.label_restrict (labels : Labels) (ls : List Label) (l : Label) :
    @Labels.label? (labels.restrict ls) l = bif ls.contains l then labels l else none := by
  simp [cond_eq_ite]

attribute [kstep] RelRegOrMem.interp HAppend.hAppend Append.append List.append
attribute [ksimp] Option.isSome_some Option.isSome_none Option.getD_some Bool.cond_true Bool.cond_false

attribute [ksimp] List.contains_cons List.contains_nil Bool.true_or Bool.false_or
