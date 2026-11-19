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

/-! Bit-counting (`lzcnt`, `tzcnt`, `popcnt`): flag behavior and `.W8` fallback. -/

private def runOpW {w : Width} (op : Operation w) (s : MachineData) : Effects :=
  let : Labels := ⟨fun _ => 0⟩
  let : AddressSize := ⟨.W64⟩
  op.interp ⟨0, 1⟩ s (fun s => .done ⟨s, 1⟩) (fun _ _ => .unimplemented "jump")

private def detData {w : Width} (op : Operation w) (s : MachineData) : Option MachineData :=
  match runOpW op s with
  | .done st => some st.data
  | _ => none

-- `popcnt` sets ZF iff src = 0, clears CF/PF/AF/SF/OF, preserves DF, and respects register width.
#guard detData (.popcnt .rbx (.reg .rax)) busy == some {
  busy with
  regs := busy.regs.set .rbx 3,
  status := { cf := false, pf := false, af := false, zf := false, sf := false, of := false }
}

#guard detData (.popcnt .rbx (.reg .rcx)) busy == some {
  busy with
  regs := busy.regs.set .rbx 0,
  status := { cf := false, pf := false, af := false, zf := true, sf := false, of := false }
}

#guard detData (.popcnt .ebx (.reg .eax))
    { busy with regs := { rax := 0x010203040000000f, rbx := 0xffffffffffffffff } } == some {
  busy with
  regs := { rax := 0x010203040000000f, rbx := 4 },
  status := { cf := false, pf := false, af := false, zf := false, sf := false, of := false }
}

#guard detData (.popcnt .bx (.reg .ax))
    { busy with regs := { rax := 0xffff0003, rbx := 0x123456789abc0000 } } == some {
  busy with
  regs := { rax := 0xffff0003, rbx := 0x123456789abc0002 },
  status := { cf := false, pf := false, af := false, zf := false, sf := false, of := false }
}

-- Resolve all `Effects.undefined` choices with a bitmask `h` (bit 0 -> first choice, etc.).
private partial def resolveAll (h : Nat) : Effects → Option MachineData
  | .done st => some st.data
  | @Effects.undefined _ _ cont =>
    let v := UInt64.ofNat (if h &&& 1 == 1 then UInt64.size - 1 else 0)
    resolveAll (h >>> 1) (cont (NondetSupportingType.from_hash v))
  | .require_read_access _ ok => resolveAll h (ok ())
  | _ => none

-- `lzcnt` / `tzcnt` fix CF = (src == 0) and ZF = (res == 0), while PF/AF/SF/OF are undefined.
private def bitcntOk {w : Width} (op : Operation w) (s : MachineData)
    (expVal : UInt64) (expCf expZf : Bool) : Bool :=
  (List.range 16).all fun mask =>
    match resolveAll mask (runOpW op s) with
    | some d =>
      d.regs.rbx == expVal && d.status.cf == expCf && d.status.zf == expZf &&
      d.status.pf == (mask &&& 1 == 1) && d.status.af == ((mask >>> 1) &&& 1 == 1) &&
      d.status.sf == ((mask >>> 2) &&& 1 == 1) && d.status.of == ((mask >>> 3) &&& 1 == 1)
    | none => false

#guard bitcntOk (.lzcnt .rbx (.reg .rax)) { regs := { rax := 0 } } 64 true false
#guard bitcntOk (.lzcnt .rbx (.reg .rax)) { regs := { rax := 1 } } 63 false false
#guard bitcntOk (.lzcnt .rbx (.reg .rax)) { regs := { rax := 0x8000000000000000 } } 0 false true
#guard bitcntOk (.lzcnt .ebx (.reg .eax)) { regs := { rax := 0x80000000, rbx := -1 } } 0 false true
#guard bitcntOk (.lzcnt .bx (.reg .ax))
  { regs := { rax := 0, rbx := 0x12340000 } } 0x12340010 true false

#guard bitcntOk (.tzcnt .rbx (.reg .rax)) { regs := { rax := 0 } } 64 true false
#guard bitcntOk (.tzcnt .rbx (.reg .rax)) { regs := { rax := 1 } } 0 false true
#guard bitcntOk (.tzcnt .rbx (.reg .rax)) { regs := { rax := 0x8000000000000000 } } 63 false false
#guard bitcntOk (.tzcnt .ebx (.reg .eax))
  { regs := { rax := 0x80000000, rbx := -1 } } 31 false false
#guard bitcntOk (.tzcnt .bx (.reg .ax))
  { regs := { rax := 0x8000, rbx := 0x12340000 } } 0x1234000f false false

-- 8-bit fallback leaves both destination and status undefined.
#guard resolveAll 0 (runOpW (.lzcnt .bl (.reg .al)) {}) !=
  resolveAll 3 (runOpW (.lzcnt .bl (.reg .al)) {})
#guard resolveAll 0 (runOpW (.tzcnt .bl (.reg .al)) {}) !=
  resolveAll 3 (runOpW (.tzcnt .bl (.reg .al)) {})
#guard resolveAll 0 (runOpW (.popcnt .bl (.reg .al)) {}) !=
  resolveAll 3 (runOpW (.popcnt .bl (.reg .al)) {})

/-! BMI2 shifts/rotate (`shlx`, `shrx`, `sarx`, `rorx`): count masking and flag preservation. -/

#guard detData (.shlx .rbx (.reg .rax) .rcx)
  { busy with regs := { rax := 0x8000000000000001, rcx := 64 } } ==
  some { busy with regs := { rax := 0x8000000000000001, rcx := 64, rbx := 0x8000000000000001 } }

#guard detData (.shlx .ebx (.reg .eax) .ecx)
  { busy with regs := { rax := 0x1234567880000001, rcx := 31, rbx := -1 } } ==
  some { busy with regs := { rax := 0x1234567880000001, rcx := 31, rbx := 0x80000000 } }

#guard detData (.shrx .ebx (.reg .eax) .ecx)
  { busy with regs := { rax := 0x80000001, rcx := 0xff, rbx := -1 } } ==
  some { busy with regs := { rax := 0x80000001, rcx := 0xff, rbx := 1 } }

#guard detData (.sarx .ebx (.reg .eax) .ecx)
  { busy with regs := { rax := 0x80000001, rcx := 0xff, rbx := -1 } } ==
  some { busy with regs := { rax := 0x80000001, rcx := 0xff, rbx := 0xffffffff } }

#guard detData (.sarx .rbx (.reg .rax) .rcx)
  { busy with regs := { rax := 0x8000000000000001, rcx := 63 } } ==
  some { busy with regs := { rax := 0x8000000000000001, rcx := 63, rbx := 0xffffffffffffffff } }

#guard detData (.rorx .ebx (.reg .eax) (.int64 0xff))
  { busy with regs := { rax := 0x80000001, rbx := -1 } } ==
  some { busy with regs := { rax := 0x80000001, rbx := 0x00000003 } }

#guard detData (.rorx .rbx (.reg .rax) (.int64 64))
  { busy with regs := { rax := 0x0123456789abcdef } } ==
  some { busy with regs := { rax := 0x0123456789abcdef, rbx := 0x0123456789abcdef } }

-- Non-32/64 widths follow the `bswap` undefined fallback.
#guard resolveAll 0 (runOpW (.shlx .bx (.reg .ax) .cx) {}) !=
  resolveAll 1 (runOpW (.shlx .bx (.reg .ax) .cx) {})
#guard resolveAll 0 (runOpW (.shrx .bl (.reg .al) .cl) {}) !=
  resolveAll 1 (runOpW (.shrx .bl (.reg .al) .cl) {})
#guard resolveAll 0 (runOpW (.sarx .bx (.reg .ax) .cx) {}) !=
  resolveAll 1 (runOpW (.sarx .bx (.reg .ax) .cx) {})
#guard resolveAll 0 (runOpW (.rorx .bx (.reg .ax) (.int64 1)) {}) !=
  resolveAll 1 (runOpW (.rorx .bx (.reg .ax) (.int64 1)) {})
