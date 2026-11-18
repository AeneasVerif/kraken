module

import Kraken.X64.Semantics
meta import Kraken.X64.Semantics
import Kraken.X64.Parser
meta import Kraken.X64.Parser

/-! Concrete-evaluation tests of semantics that the native asm tests can't observe. -/

private partial def accessChecks :
    Effects → Option (List (Nat × Nat) × List (Nat × Nat))
  | .done _ => some ([], [])
  | .require_read_access p ok => (accessChecks (ok ())).map fun (rs, ws) => ((p.lower.val, p.upper.val) :: rs, ws)
  | .require_write_access p ok => (accessChecks (ok ())).map fun (rs, ws) => (rs, (p.lower.val, p.upper.val) :: ws)
  | _ => none

/-- 64 bytes of data memory at `0x1000`. -/
private def s : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }

#guard accessChecks (s.loadAvx 0x1000 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1010)], [])
#guard accessChecks (s.loadAvx 0x1000 .W256 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1020)], [])
#guard accessChecks (s.loadAvx 0x1000 .W512 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1040)], [])
#guard accessChecks (s.storeAvx (w := .W128) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1010)])
#guard accessChecks (s.storeAvx (w := .W256) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1020)])
#guard accessChecks (s.storeAvx (w := .W512) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1040)])

#guard ([Width.W8, .W16, .W32, .W64].all fun w =>
  accessChecks (s.load 0x1000 w fun _ s => .done ⟨s, 0⟩) ==
    some ([(0x1000, 0x1000 + w.bytes)], []) &&
  accessChecks (s.store (w := w) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
    some ([], [(0x1000, 0x1000 + w.bytes)]))

#guard accessChecks (s.loadAvx 0x1001 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1001, 0x1011)], [])
#guard match s.loadAvx 0x1001 .W128 (fun _ s => .done ⟨s, 0⟩) (checkAlign := true) with
  | .gp_unaligned addr bytes => addr == 0x1001 && bytes == 16
  | _ => false
#guard match s.storeAvx (w := .W128) 0x1001 0 (fun s => .done ⟨s, 0⟩) (checkAlign := true) with
  | .gp_unaligned addr bytes => addr == 0x1001 && bytes == 16
  | _ => false

private def wrapping : MachineData :=
  { dmem := (List.replicate 64 0).At 0xfffffffffffffff8 }

#guard accessChecks (wrapping.load 0xffffffffffffffff .W8 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0xffffffffffffffff, UInt64.size)], [])
#guard accessChecks (wrapping.loadAvx 0xfffffffffffffff8 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0xfffffffffffffff8, UInt64.size), (0, 8)], [])
#guard accessChecks (wrapping.storeAvx (w := .W128) 0xfffffffffffffff8 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0xfffffffffffffff8, UInt64.size), (0, 8)])

/-! `cld`/`std` write only the direction flag. -/

private def runOp (op : Operation .W64) (s : MachineData) : Option MachineData :=
  let : Labels := ⟨fun _ => 0⟩
  let : AddressSize := ⟨.W64⟩
  match op.interp ⟨0, 1⟩ s (fun s => .done ⟨s, 1⟩) (fun _ _ => .unimplemented "jump") with
  | .done st => some st.data
  | _ => none

/-- A state with every status flag set and some register and memory contents. -/
private def busy : MachineData :=
  { s with regs := { rax := 7 }, status := .mk true true true true true true }

#guard runOp .std busy == some { busy with df := true }
#guard runOp .cld { busy with df := true } == some busy
#guard runOp .cld busy == some busy
#guard (runOp .std busy >>= runOp .std) == some { busy with df := true }
#guard (runOp .std busy >>= runOp .cld) == some busy

/-! `div` and `idiv` raise #DE on a zero divisor or a quotient that does not fit, which the native
asm tests can't run. -/

/-- Runs `asm` from the zero state, returning the error or `rax` and `rdx`. -/
private def runDiv (asm : Program) : String ⊕ (UInt64 × UInt64) :=
  let r : Except String _ := do
    let exe := Program.fakeLayout (⸨prog| start: ⸩ ++ asm ++ ⸨prog| end: ⸩)
    let s ← Executable.eval exe ⟨{}, exe.labels.label "start"⟩ (·.pc = exe.labels.label "end")
    return (s.data.regs.rax, s.data.regs.rdx)
  match r with | .ok v => .inr v | .error e => .inl e

private def divideError : String ⊕ (UInt64 × UInt64) := .inl "#DE: Divide error"

#guard runDiv ⸨prog| movq $5, %rax; divq %rcx ⸩ == divideError
#guard runDiv ⸨prog| movq $5, %rax; idivb %cl ⸩ == divideError
#guard runDiv ⸨prog| movq $1, %rdx; movq $1, %rcx; divq %rcx ⸩ == divideError
#guard runDiv ⸨prog| movw $0x100, %ax; movb $1, %cl; divb %cl ⸩ == divideError
-- INT_MIN / -1
#guard runDiv ⸨prog| movq $-1, %rdx; movabsq $0x8000000000000000, %rax; movq $-1, %rcx; idivq %rcx ⸩ ==
  divideError
#guard runDiv ⸨prog| movw $-128, %ax; movb $-1, %cl; idivb %cl ⸩ == divideError
-- Quotients at the edge of the range
#guard runDiv ⸨prog| movq $-1, %rdx; movabsq $0x8000000000000000, %rax; movq $1, %rcx; idivq %rcx ⸩ ==
  .inr (0x8000000000000000, 0)
#guard runDiv ⸨prog| movl $0x7fffffff, %eax; movl $1, %ecx; idivl %ecx ⸩ == .inr (0x7fffffff, 0)
#guard runDiv ⸨prog| movl $0x80000000, %eax; movl $1, %ecx; idivl %ecx ⸩ == divideError
#guard runDiv ⸨prog| movq $-1, %rax; movq $-1, %rdx; movq $-1, %rcx; divq %rcx ⸩ ==
  divideError
#guard runDiv ⸨prog| movq $-2, %rdx; movq $-1, %rax; movq $-1, %rcx; divq %rcx ⸩ ==
  .inr (0xffffffffffffffff, 0xfffffffffffffffe)
-- Signs of quotient and remainder
#guard runDiv ⸨prog| movq $-7, %rax; movq $-1, %rdx; movq $2, %rcx; idivq %rcx ⸩ ==
  .inr (0xfffffffffffffffd, 0xffffffffffffffff)
#guard runDiv ⸨prog| movq $7, %rax; movq $-2, %rcx; idivq %rcx ⸩ == .inr (0xfffffffffffffffd, 1)
