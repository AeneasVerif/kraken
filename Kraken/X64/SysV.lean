module

public import Kraken.X64.Stack

/-!
# Procedures under the System V AMD64 calling convention

What a procedure specification (`Kraken.Executable.ProcSpec`, `Kraken.X64.WP.Call`) says about the
stack and the registers when the code follows the SysV convention, stated once for every procedure:

* on entry the return address is at `[rsp]` (`RetCell`), `rsp + 8` is 16-byte aligned, the
  direction flag is clear, and the caller has reserved `d` bytes of free stack below it
  (`Reserve`), not wrapping past address `0`;
* on return `rsp` is 8 above its entry value (the return address popped), the direction flag is
  clear, `rbp`, `rbx` and `r12`–`r15` hold their entry values (`SavedRegs`), and the
  return-address slot and the reservation come back as owned bytes;
* integer arguments in `rdi, rsi, rdx, rcx, r8, r9` (`ArgU64` for the first), the result in `rax`
  (`RetU64`).

`CallPre d R ra t`/`CallPost d R ra t s` are the convention's share of a procedure's pre- and
postcondition with caller's memory `R`; a procedure's specification is these plus its semantics.
The cells are shared with the other x64 conventions (`Kraken.X64.Stack`); compare
`Kraken.X64.Win64`.

Not modelled: vector arguments and results, and the callee-saved control bits of MXCSR and the
x87 control word, which `MachineData` does not have. The red zone needs no separate treatment: a leaf
procedure that uses the 128 bytes below `rsp` asks for them in its reservation (`CallPre d` with
`d ≥ 128`). The ABI's promise that signal handlers leave them alone is vacuous here, since Kraken
has no asynchronous events.
-/

public section

open Std.ExtHashMap
open Kraken.X64.Stack

namespace Kraken.X64.SysV

/-- The callee-saved general-purpose registers other than `rsp` hold their entry values. -/
abbrev SavedRegs (t s : MachineData) : Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx ∧ s.regs.get64 .rbp = t.regs.get64 .rbp
  ∧ s.regs.get64 .r12 = t.regs.get64 .r12 ∧ s.regs.get64 .r13 = t.regs.get64 .r13
  ∧ s.regs.get64 .r14 = t.regs.get64 .r14 ∧ s.regs.get64 .r15 = t.regs.get64 .r15

/-- The convention's share of a procedure's precondition, with caller's memory `R`: the stack
aligned, the direction flag clear, the return address on the stack, and `d` bytes reserved below
it, not wrapping past address `0`. -/
abbrev CallPre (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  EntryAligned t ∧ t.df = false ∧ d ≤ (t.regs.get64 .rsp).toNat
  ∧ (t.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R))

/-- The convention's share of a procedure's postcondition: the return address popped, the direction
flag clear, the callee-saved registers as they were, the reservation and the slot given back. -/
abbrev CallPost (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.df = false
  ∧ SavedRegs t s
  ∧ (s.dmem =⋆ Owned 8 (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R))

/-- A 64-bit first argument in `rdi`. -/
abbrev ArgU64 (t : MachineData) (n : BitVec 64) : Prop := t.regs.get64 .rdi = n

/-- A 64-bit result in `rax`. -/
abbrev RetU64 (s : MachineData) (v : BitVec 64) : Prop := s.regs.get64 .rax = v

end Kraken.X64.SysV
