module

public import Kraken.X64.Stack

/-!
# Procedures under the Windows x64 calling convention

TODO: vector arguments and results; the callee-saved control bits of MXCSR and the x87 control word.
Also not modelled: `__chkstk`, which applies for allocations > 4096 (we assume the pages are mapped).

References: Microsoft's x64 ABI conventions, https://learn.microsoft.com/en-us/cpp/build/x64-software-conventions,
in particular the x64 calling convention, https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention,
and, for stack probing, x64 prolog and epilog, https://learn.microsoft.com/en-us/cpp/build/prolog-and-epilog,
and the compiler's default probe threshold of 4096 bytes on x64 (`/Gs`),
https://learn.microsoft.com/en-us/cpp/build/reference/gs-control-stack-checking-calls.
("We recommend that you do not change the default value unless you know exactly why you have to change it.")
-/

public section

open Std.ExtHashMap
open Kraken.X64.Stack

namespace Kraken.X64.Win64

abbrev SavedRegs (t s : MachineData) : Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx ∧ s.regs.get64 .rbp = t.regs.get64 .rbp
  ∧ s.regs.get64 .rdi = t.regs.get64 .rdi ∧ s.regs.get64 .rsi = t.regs.get64 .rsi
  ∧ s.regs.get64 .r12 = t.regs.get64 .r12 ∧ s.regs.get64 .r13 = t.regs.get64 .r13
  ∧ s.regs.get64 .r14 = t.regs.get64 .r14 ∧ s.regs.get64 .r15 = t.regs.get64 .r15

/-- xmm0-xmm5; x,y,zmms 16-31 are caller-save, as are the upper bits of ymm0-ymm15 / zmm0-zmm15 -/
abbrev SavedXmm (t s : MachineData) : Prop :=
  s.zmms.get (.xmm .mm6) = t.zmms.get (.xmm .mm6)
  ∧ s.zmms.get (.xmm .mm7) = t.zmms.get (.xmm .mm7)
  ∧ s.zmms.get (.xmm .mm8) = t.zmms.get (.xmm .mm8)
  ∧ s.zmms.get (.xmm .mm9) = t.zmms.get (.xmm .mm9)
  ∧ s.zmms.get (.xmm .mm10) = t.zmms.get (.xmm .mm10)
  ∧ s.zmms.get (.xmm .mm11) = t.zmms.get (.xmm .mm11)
  ∧ s.zmms.get (.xmm .mm12) = t.zmms.get (.xmm .mm12)
  ∧ s.zmms.get (.xmm .mm13) = t.zmms.get (.xmm .mm13)
  ∧ s.zmms.get (.xmm .mm14) = t.zmms.get (.xmm .mm14)
  ∧ s.zmms.get (.xmm .mm15) = t.zmms.get (.xmm .mm15)

/-- Conditions that hold on procedure entry directly after a call (with `d` bytes of reserved stack).
Note the shadow space reserved above rsp. Note that the conventions appear to require df = 0 only on
entry to "C Runtime Library calls and Windows system calls". -/
abbrev CallPre (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  EntryAligned t
  ∧ (t.dmem =⋆ RetCell ra (t.regs.get64 .rsp)
      ⋆ (Shadow (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R)))

/-- Conditions that hold immediately after the `ret` (where `t` was the state in `CallPre`).
df = 0 is mandated here. -/
abbrev CallPost (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.df = false
  ∧ SavedRegs t s ∧ SavedXmm t s
  ∧ (s.dmem =⋆ Owned 8 (t.regs.get64 .rsp)
      ⋆ (Shadow (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R)))

/-- Convenience function for the first argument in `rcx`. The rest are rdx, r8, and r9. -/
abbrev ArgU64 (t : MachineData) (n : BitVec 64) : Prop := t.regs.get64 .rcx = n

/-- Convenience function for the integer return in `rax`. -/
abbrev RetU64 (s : MachineData) (v : BitVec 64) : Prop := s.regs.get64 .rax = v

end Kraken.X64.Win64
