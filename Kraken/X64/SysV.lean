module

public import Kraken.X64.Stack

/-!
# Procedures under the System V AMD64 calling convention

TODO: vector arguments and results, and the callee-saved control bits of MXCSR and the
x87 control word. The red zone needs no separate treatment: a leaf procedure that uses the 128
bytes below `rsp` asks for them in its reservation (`Call d` with `d ≥ 128`).

Reference: the System V Application Binary Interface, AMD64 Architecture Processor Supplement
(x86-64 psABI), https://gitlab.com/x86-psABIs/x86-64-ABI
-/

public section

open Std.ExtHashMap
open Kraken.X64.Stack

namespace Kraken.X64.SysV

/-- Callee-saved registers. Note that all zmms are caller-save. -/
abbrev SavedRegs (t s : MachineData) : Prop :=
  s.regs.rbx = t.regs.rbx ∧ s.regs.rbp = t.regs.rbp
  ∧ s.regs.r12 = t.regs.r12 ∧ s.regs.r13 = t.regs.r13
  ∧ s.regs.r14 = t.regs.r14 ∧ s.regs.r15 = t.regs.r15

/-- Conditions that hold on procedure entry directly after a call (with `d` bytes of reserved stack). -/
abbrev Call (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  EntryAligned t ∧ t.df = false
  ∧ (t.dmem =⋆ RetCell ra t.regs.rsp.toBitVec ⋆ (Reserve d t.regs.rsp.toBitVec ⋆ R))

/-- Conditions that hold immediately after the `ret` (where `t` was the state in `Call`). -/
abbrev Ret (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8 ∧ s.df = false
  ∧ SavedRegs t s
  ∧ (s.dmem =⋆ Owned 8 t.regs.rsp.toBitVec ⋆ (Reserve d t.regs.rsp.toBitVec ⋆ R))

/-- Convenience definition for the first integer argument. The rest are rsi, rdx, rcx, r8, and r9. -/
abbrev ArgU64 (t : MachineData) (n : BitVec 64) : Prop := t.regs.rdi.toBitVec = n

/-- Convenience definition for the first integer return. The second is rdx. -/
abbrev RetU64 (s : MachineData) (v : BitVec 64) : Prop := s.regs.rax.toBitVec = v

end Kraken.X64.SysV
