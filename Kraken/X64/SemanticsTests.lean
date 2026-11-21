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

#guard match ConstExpr.interp (.add (.label "missing") (.int64 4)) ⟨0, 5⟩ (fun _ => .done ⟨s, 0⟩) with
  | .resolve_label l _ => l == "missing"
  | _ => false

#guard match (letI : AddressSize := ⟨.W64⟩
    Operation.interp (w := .W64) (.jcc .z "missing_target") ⟨0, 2⟩ { s with status := { s.status with zf := true } } (fun st => .done ⟨st, 2⟩) (fun a st => .done ⟨st, a⟩)) with
  | .resolve_label l _ => l == "missing_target"
  | _ => false

private def bitFlags : List StatusFlags :=
  (List.range 64).map fun n => NondetSupportingType.from_hash (UInt64.ofNat n)

#guard ([Operation.bt (.low .rax .W64) (.imm (.int64 0)),
    .bts (.low .rax .W64) (.imm (.int64 0))].all fun op =>
  let : AddressSize := ⟨.W64⟩
  match op.interp ⟨0, 1⟩ busy (fun st => .done ⟨st, 1⟩)
      (fun _ _ => .unimplemented "jump") with
  | @Effects.undefined _ .statusFlags k =>
    bitFlags.all fun flags =>
      match k flags with
      | .done st => st.data.status == { flags with cf := true, zf := busy.status.zf }
      | _ => false
  | _ => false)

#guard ([Operation.bt (.low .rax .W8) (.imm (.int64 0)),
    .bts .ah (.reg .ah)].all fun op =>
  let : AddressSize := ⟨.W64⟩
  match op.interp ⟨0, 1⟩ busy (fun st => .done ⟨st, 1⟩)
      (fun _ _ => .unimplemented "jump") with
  | .unimplemented _ => true
  | _ => false)

#guard match (letI : AddressSize := ⟨.W64⟩
    Operation.interp (.bt (.low .rax .W64) (.imm (.add (.label "offset") (.int64 1))))
      ⟨0, 1⟩ busy (fun st => .done ⟨st, 1⟩) (fun _ _ => .unimplemented "jump")) with
  | .resolve_label label _ => label == "offset"
  | _ => false

private abbrev gotLabels : Labels :=
  { label? := fun l => if l == "f" then some 0x7000 else none
    gotSlot? := fun l => if l == "f" then some 0x1000 else none }

private def gotState : MachineData :=
  { s with
    dmem := Mem.storeInt (Mem.storeInt (Mem.storeInt s.dmem 0x1000 8 0x5000)
      0x1018 8 0x6000) 0x1020 8 0x9000
    regs := { rax := 0x8000, rsp := 0x1020 } }

private def evalInstr (i : Instr) (st : MachineData := gotState)
    (labels : Labels := gotLabels) : Except String MachineState :=
  let e := Program.fakeLayout [.instr i]
  e.eval ⟨st, e.addrOf 0⟩ (fun st => st.pc != e.addrOf 0) labels

private def callResult (i : Instr) (target : Int64) (labels : Labels := gotLabels) : Bool :=
  (evalInstr i gotState labels).toOption.map (fun st =>
    st.pc == target && st.data.regs.rsp == 0x1018 &&
    (Mem.loadInt st.data.dmem 0x1018 8).map (BitVec.ofInt 64) ==
      some ((Program.fakeLayout [.instr i]).addrOf 1).toBitVec) == some true

private def gotAddr : AddrExpr :=
  { base := some .rip, idx := none, disp := .sub (.gotSlot "f") .after_current_instruction }

private def gotMov : Instr :=
  .regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.mem gotAddr))

private def gotCall : Instr := .regular .W64 .W64 (.call (.mem gotAddr))
private def gotJump : Instr := .regular .W64 .W64 (.jmp (.mem gotAddr))

#guard (evalInstr gotMov).toOption.map (·.data.regs.rax) == some 0x5000
#guard (evalInstr (.regular .W64 .W64 (.lea (.low .rax .W64) gotAddr))).toOption.map
  (·.data.regs.rax) == some 0x1000
#guard (evalInstr (.regular .W64 .W64 (.lea (.low .rax .W64)
  { base := some .rip, idx := none, disp := .sub (.label "f") .after_current_instruction }))).toOption.map
  (·.data.regs.rax) == some 0x7000
#guard (evalInstr gotJump).toOption.map (fun st =>
  st.pc == 0x5000 && st.data == gotState) == some true
#guard (evalInstr (.regular .W64 .W64 (.jmp (.reg (.low .rax .W64))))).toOption.map (fun st =>
  st.pc == 0x8000 && st.data == gotState) == some true
#guard (evalInstr (.regular .W64 .W64 (.jmp (.mem
  { base := some (.reg .rsp), idx := none })))).toOption.map (·.pc) == some 0x9000
#guard callResult gotCall 0x5000
#guard callResult (.regular .W64 .W64 (.call (.reg (.low .rax .W64)))) 0x8000
#guard callResult (.regular .W64 .W64 (.call (.reg (.low .rsp .W64)))) 0x1020
#guard callResult (.regular .W64 .W64 (.call (.mem { base := some (.reg .rsp), idx := none }))) 0x9000
#guard callResult (.regular .W64 .W64 (.call (.mem
  { base := some (.reg .rsp), idx := none, disp := .int64 (-8) }))) 0x6000
#guard callResult gotCall 0x6000 { gotLabels with gotSlot? := fun _ => some 0x1018 }

#guard match evalInstr gotMov gotState
    { gotLabels with gotSlot? := fun _ => none } with
  | .error msg => msg == "unresolved GOT slot: f"
  | .ok _ => false

#guard (evalInstr gotMov gotState
  { gotLabels with label? := fun _ => none }).toOption.map (·.data.regs.rax) == some 0x5000

#guard match (letI : AddressSize := ⟨.W64⟩
    (RegOrMem.mem gotAddr : RegOrMem .W64).interp
      gotState ⟨0x20, 0x26⟩ (fun v st => .done ⟨st.setReg (.low .rax .W64) v, 0x26⟩)) with
  | .resolve_got_slot l k =>
    l == "f" && accessChecks (k 0x1000) == some ([(0x1000, 0x1008)], [])
  | _ => false

#guard match (letI : AddressSize := ⟨.W64⟩
    (RegOrMem.mem gotAddr : RegOrMem .W64).interp
      { gotState with dmem := {} } ⟨0x20, 0x26⟩ (fun _ st => .done ⟨st, 0x26⟩)) with
  | .resolve_got_slot _ k =>
    match k 0x1000 with
    | .require_read_access _ ok =>
      match ok () with
      | .nonmem_load _ addr w _ => addr == 0x1000 && w == .W64
      | _ => false
    | _ => false
  | _ => false

#guard ([Int64.ofInt 0, 0x26, -1].all fun pc =>
  let : AddressSize := ⟨.W64⟩
  match gotAddr.interp gotState.regs ⟨0, pc⟩
      (fun addr => .done ⟨gotState.setReg (.low .rax .W64) addr, pc⟩) with
  | .resolve_got_slot l k =>
    l == "f" && [Int64.ofInt 0x1000, -8].all fun slot =>
      match k slot with
      | .done st => st.data.regs.rax.toBitVec == slot.toBitVec
      | _ => false
  | _ => false)

#guard [gotCall, gotJump].all
  (fun i => match evalInstr i gotState { gotLabels with gotSlot? := fun _ => none } with
    | .error msg => msg == "unresolved GOT slot: f"
    | .ok _ => false)

#guard
  let e := Program.fakeLayout [.instr gotMov, .instr gotJump]
  (e.eval ⟨gotState, e.addrOf 0⟩ (fun st => st.pc == 0x5000) gotLabels).toOption.map
    (fun st => st.data.regs.rax == 0x5000 && st.pc == 0x5000) == some true

#guard match ConstExpr.interp (.gotSlot "f") ⟨0x20, 0x26⟩
    (fun a => .done ⟨gotState, a⟩) with
  | .resolve_got_slot l k =>
    l == "f" && match k 0x1000 with
      | .done st => st.pc == 0x1000
      | _ => false
  | _ => false

#guard match ConstExpr.interp (.add (.gotSlot "f") (.int64 8)) ⟨0x20, 0x26⟩
    (fun a => .done ⟨gotState, a⟩) with
  | .resolve_got_slot l k =>
    l == "f" && match k 0x1000 with
      | .done st => st.pc == 0x1008
      | _ => false
  | _ => false

#guard
  let d : Directive := .word 8 (.gotSlot "missing")
  let e := Program.fakeLayout [d]
  e.program.map (·.directive) == [d] &&
    match e.eval ⟨gotState, e.startAddr⟩ (fun _ => false) with
    | .error msg => msg == s!"Unimplemented: execution reached data word at {e.startAddr}"
    | .ok _ => false
