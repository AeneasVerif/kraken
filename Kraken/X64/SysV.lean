module

public import Kraken.X64.Stack

/-!
# Procedures under the System V AMD64 calling convention

TODO: vector arguments and results, and the callee-saved control bits of MXCSR and the
x87 control word. The red zone needs no separate treatment: a leaf procedure that uses the 128
bytes below `rsp` asks for them in its reservation (`CallPre d` with `d ≥ 128`).

Reference: the System V Application Binary Interface, AMD64 Architecture Processor Supplement
(x86-64 psABI), https://gitlab.com/x86-psABIs/x86-64-ABI
-/

public section

open Std.ExtHashMap
open Kraken.X64.Stack

namespace Kraken.X64.SysV

/-- Callee-saved registers. Note that all zmms are caller-save. -/
abbrev SavedRegs (t s : MachineData) : Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx ∧ s.regs.get64 .rbp = t.regs.get64 .rbp
  ∧ s.regs.get64 .r12 = t.regs.get64 .r12 ∧ s.regs.get64 .r13 = t.regs.get64 .r13
  ∧ s.regs.get64 .r14 = t.regs.get64 .r14 ∧ s.regs.get64 .r15 = t.regs.get64 .r15

/-- Conditions that hold on procedure entry directly after a call (with `d` bytes of reserved stack). -/
abbrev CallPre (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  EntryAligned t ∧ t.df = false
  ∧ (t.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R))

/-- Conditions that hold immediately after the `ret` (where `t` was the state in `CallPre`). -/
abbrev CallPost (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.df = false
  ∧ SavedRegs t s
  ∧ (s.dmem =⋆ Owned 8 (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R))

/-- Convenience definition for the first integer argument. The rest are rsi, rdx, rcx, r8, and r9. -/
abbrev ArgU64 (t : MachineData) (n : BitVec 64) : Prop := t.regs.get64 .rdi = n

/-- Convenience definition for the first integer return. The second is rdx. -/
abbrev RetU64 (s : MachineData) (v : BitVec 64) : Prop := s.regs.get64 .rax = v

end Kraken.X64.SysV
