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
  s.regs.rbx = t.regs.rbx ∧ s.regs.rbp = t.regs.rbp
  ∧ s.regs.rdi = t.regs.rdi ∧ s.regs.rsi = t.regs.rsi
  ∧ s.regs.r12 = t.regs.r12 ∧ s.regs.r13 = t.regs.r13
  ∧ s.regs.r14 = t.regs.r14 ∧ s.regs.r15 = t.regs.r15

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
Note the shadow space reserved above rsp.

Microsoft's documentation requires `df = 0` only on entry to "C Runtime Library calls and
Windows system calls", but MSVC, clang-cl and `gcc -mabi=ms` all assume `df = 0` on entry to any
procedure, so we require it here (otherwise ~every procedure would need to assume `df = 0` on its
own to satisfy `Ret`.) -/
abbrev Call (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  EntryAligned t ∧ t.df = false
  ∧ (t.dmem =⋆ RetCell ra t.regs.rsp.toBitVec
      ⋆ (Shadow t.regs.rsp.toBitVec ⋆ (Reserve d t.regs.rsp.toBitVec ⋆ R)))

/-- Conditions that hold immediately after the `ret` (where `t` was the state in `Call`).
df = 0 is mandated here. -/
abbrev Ret (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8 ∧ s.df = false
  ∧ SavedRegs t s ∧ SavedXmm t s
  ∧ (s.dmem =⋆ Owned 8 t.regs.rsp.toBitVec
      ⋆ (Shadow t.regs.rsp.toBitVec ⋆ (Reserve d t.regs.rsp.toBitVec ⋆ R)))

/-- Convenience function for the first argument in `rcx`. The rest are rdx, r8, and r9. -/
abbrev ArgU64 (t : MachineData) (n : BitVec 64) : Prop := t.regs.rcx.toBitVec = n

/-- Convenience function for the integer return in `rax`. -/
abbrev RetU64 (s : MachineData) (v : BitVec 64) : Prop := s.regs.rax.toBitVec = v

end Kraken.X64.Win64
