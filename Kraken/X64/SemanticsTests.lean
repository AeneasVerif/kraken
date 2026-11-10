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

/-! `div` and `idiv` raise #DE on a zero divisor or a quotient that does not fit, which the native
asm tests can't run. -/

/-- Runs `asm` from the zero state, returning the error or `rax` and `rdx`. -/
private def runDiv (asm : String) : String ⊕ (UInt64 × UInt64) :=
  let r : Except String _ := do
    let exe := (← Kraken.X64.Parser.parse ("start:\n" ++ asm ++ "\nend:")).fakeLayout
    let s ← exe.eval ⟨{}, exe.labels.label "start"⟩ (·.pc = exe.labels.label "end")
    return (s.data.regs.rax, s.data.regs.rdx)
  match r with | .ok v => .inr v | .error e => .inl e

private def divideError : String ⊕ (UInt64 × UInt64) := .inl "#DE: Divide error"

#guard runDiv "movq $5, %rax\ndivq %rcx" == divideError
#guard runDiv "movq $5, %rax\nidivb %cl" == divideError
#guard runDiv "movq $1, %rdx\nmovq $1, %rcx\ndivq %rcx" == divideError
#guard runDiv "movw $0x100, %ax\nmovb $1, %cl\ndivb %cl" == divideError
-- INT_MIN / -1
#guard runDiv "movq $-1, %rdx\nmovabsq $0x8000000000000000, %rax\nmovq $-1, %rcx\nidivq %rcx" ==
  divideError
#guard runDiv "movw $-128, %ax\nmovb $-1, %cl\nidivb %cl" == divideError
-- Quotients at the edge of the range
#guard runDiv "movq $-1, %rdx\nmovabsq $0x8000000000000000, %rax\nmovq $1, %rcx\nidivq %rcx" ==
  .inr (0x8000000000000000, 0)
#guard runDiv "movl $0x7fffffff, %eax\nmovl $1, %ecx\nidivl %ecx" == .inr (0x7fffffff, 0)
#guard runDiv "movl $0x80000000, %eax\nmovl $1, %ecx\nidivl %ecx" == divideError
#guard runDiv "movq $-1, %rax\nmovq $-1, %rdx\nmovq $-1, %rcx\ndivq %rcx" ==
  divideError
#guard runDiv "movq $-2, %rdx\nmovq $-1, %rax\nmovq $-1, %rcx\ndivq %rcx" ==
  .inr (0xffffffffffffffff, 0xfffffffffffffffe)
-- Signs of quotient and remainder
#guard runDiv "movq $-7, %rax\nmovq $-1, %rdx\nmovq $2, %rcx\nidivq %rcx" ==
  .inr (0xfffffffffffffffd, 0xffffffffffffffff)
#guard runDiv "movq $7, %rax\nmovq $-2, %rcx\nidivq %rcx" == .inr (0xfffffffffffffffd, 1)
