module

import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

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
