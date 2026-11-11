module

public import Kraken.X64.Stack

/-!
# Procedures under the Windows x64 calling convention

The Microsoft x64 convention, in the same terms as `Kraken.X64.SysV`, to show that `ProcSpec` and the
call rule `ProcSpec.wp_call` are convention-agnostic: only `Pre`/`Post` change.

* on entry the return address is at `[rsp]` (`RetCell`), `rsp + 8` is 16-byte aligned and the
  direction flag is clear, as under SysV; above it the caller has allocated 32 bytes of *shadow
  space* at `[rsp + 8, rsp + 40)` that the callee may use freely (`Shadow`); below it, `d` reserved
  bytes (`Reserve`);
* on return `rsp` is 8 above its entry value, the direction flag is clear, `rbp`, `rbx`, `rdi`,
  `rsi`, `r12`–`r15` hold their entry values, and so do `xmm6`–`xmm15` (`SavedRegs`, `SavedXmm`);
  the slot, the shadow space and the reservation come back as owned bytes;
* integer arguments in `rcx, rdx, r8, r9` (`ArgU64` for the first), the result in `rax`.

Differences from SysV, in the model: two more callee-saved general-purpose registers (`rdi`, `rsi`),
callee-saved vector state, and the shadow-space cell. Not modelled: vector arguments, arguments
beyond the fourth (which live above the shadow space), and the callee-saved control bits of MXCSR
and the x87 control word, which `MachineData` does not have. Also not modelled: stack probing. Windows
commits stack pages one guard page at a time, so a frame larger than a page must be probed in order
(`__chkstk`). Kraken has no guard pages, so for `d > 4096`, `Reserve d` is only a sound assumption if
the pages are already committed.
-/

public section

open Std.ExtHashMap
open Kraken.X64.Stack

namespace Kraken.X64.Win64

/-- The callee-saved general-purpose registers other than `rsp` hold their entry values. -/
abbrev SavedRegs (t s : MachineData) : Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx ∧ s.regs.get64 .rbp = t.regs.get64 .rbp
  ∧ s.regs.get64 .rdi = t.regs.get64 .rdi ∧ s.regs.get64 .rsi = t.regs.get64 .rsi
  ∧ s.regs.get64 .r12 = t.regs.get64 .r12 ∧ s.regs.get64 .r13 = t.regs.get64 .r13
  ∧ s.regs.get64 .r14 = t.regs.get64 .r14 ∧ s.regs.get64 .r15 = t.regs.get64 .r15

/-- `xmm6`–`xmm15` hold their entry values: the low 128 bits of `zmm6`–`zmm15`, read through the
`xmm` view. The upper bits are volatile. -/
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

/-- The convention's share of a procedure's precondition, with caller's memory `R`: the stack
aligned, the direction flag clear, the return address on the stack, the shadow space above it and
`d` bytes reserved below. -/
abbrev CallPre (d : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  EntryAligned t ∧ t.df = false
  ∧ (t.dmem =⋆ RetCell ra (t.regs.get64 .rsp)
      ⋆ (Shadow (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R)))

/-- The convention's share of a procedure's postcondition: the return address popped, the direction
flag clear, the callee-saved registers as they were, the slot, the shadow space and the reservation
given back. -/
abbrev CallPost (d : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t s : MachineData) : Prop :=
  s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.df = false
  ∧ SavedRegs t s ∧ SavedXmm t s
  ∧ (s.dmem =⋆ Owned 8 (t.regs.get64 .rsp)
      ⋆ (Shadow (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R)))

/-- A 64-bit first argument in `rcx`. -/
abbrev ArgU64 (t : MachineData) (n : BitVec 64) : Prop := t.regs.get64 .rcx = n

/-- A 64-bit result in `rax`. -/
abbrev RetU64 (s : MachineData) (v : BitVec 64) : Prop := s.regs.get64 .rax = v

end Kraken.X64.Win64
