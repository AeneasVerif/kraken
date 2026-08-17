import Kraken.X64.Semantics

/-
A dummy device that can be accessed via MMIO and can only
perform the veeery complicated operation of incrementing a
number by one.
Inspired by https://github.com/project-oak/silveroak/blob/main/firmware/IncrementWait/IncrementWaitSemantics.v
Illustrates how MMIO stores *and loads* can modify the state of an external device.

Overview of what can modify what:

                MachineData     External state
nonmem_load          N                YY
nonmem_store         Y                YY

N = No (excluded by signature of Sem.nomem_load)
Y = Yes but not illustrated in this file (would need example where mmio_store
    triggers passing owned memory to a device, or receiving it from the device)
YY = Yes and illustrated in this file

TODO: Do we want to support scenarios where an mmio_load of a done flag that
equals 1 means that the CPU acknowledges that it now knows that the device
(eg a NIC) has finished writing some buffers and therefore now these become
owned by the CPU, so MachineData.dmem becomes bigger?
If so, we'd need to change the signature of Sem.nomem_load and write more examples
until all 4 cells in the above table are YY.
-/

-- state as seen by software, not necessarily implemented like this in hardware
inductive IncrementerState
  | idle
  | busy (input : UInt32) (steps_until_done : Nat)
  | done (answer : UInt32)
  deriving Hashable

inductive Incrementer.Register | VALUE | STATUS

def VALUE_ADDR : UInt64 := 4096
def STATUS_ADDR : UInt64 := 4100

def STATUS_IDLE : UInt32 := 0
def STATUS_BUSY : UInt32 := 1
def STATUS_DONE : UInt32 := 2

def IncrementerState.read_step (s : IncrementerState) (r : Incrementer.Register)
  : Option (UInt32 × IncrementerState) :=
  match r with
  | .VALUE => match s with
    | .idle => none
    | .busy _ _ => none
    -- note how a *read* causes a state transition in the device
    | .done answer => some (answer, .idle)
  | .STATUS => match s with
    | .idle => some (STATUS_IDLE, s)
    | .busy _ _  => some (STATUS_BUSY, s)
    | .done _ => some (STATUS_DONE, s)

-- software and proofs should not depend on this number,
-- if we have nondeterminism available, we'd pick an arbitrary number here
def N_STEPS_NEEDED : Nat := 3

def IncrementerState.write_step (s : IncrementerState)
  (r : Incrementer.Register) (v : UInt32)
  : Option IncrementerState :=
  match r with
  | .VALUE => match s with
    | .idle => some (.busy v N_STEPS_NEEDED)
    | .busy _ _ => none
    | .done _ => none
  | .STATUS => none

def IncrementerState.internal_step (s : IncrementerState) : IncrementerState :=
  match s with
  | .idle => s
  | .busy input 0 => .done (input + 1)
  | .busy input (n + 1) => .busy input n
  | .done _ => s

def Incrementer.Register.of_addr (addr : UInt64) : Option Incrementer.Register :=
  if addr == VALUE_ADDR then some .VALUE
  else if addr == STATUS_ADDR then some .STATUS
  else none

structure SystemState where
  machineState : MachineState
  deviceState : IncrementerState

def handleEffects (ds : IncrementerState) (es : Effects MachineState)
    (ok : SystemState → Except String SystemState) :
    Except String SystemState :=
  match es with
  | .done ms => ok (.mk ms ds)
  | .unimplemented msg => .error msg
  | .gp_unaligned addr w => .error s!"#GP: Memory op at {repr addr} did not have mandatory alignment of {w}"
  | .require_read_access _ _ cont => handleEffects ds (cont ()) ok
  | .require_write_access _ _ cont => handleEffects ds (cont ()) ok
  | .require_exec_access _ cont => handleEffects ds (cont ()) ok
  | .nonmem_load dmem addr w cont => do
    match h: w with
    | .W8 | .W16 | .W64 => throw s!"nonmem_load of width other than 4 bytes"
    | .W32 => 
      let some r := Incrementer.Register.of_addr (UInt64.ofBitVec addr)
        | throw s!"nonmem_load at unmapped address {repr addr}"
      let some (reply, ds') := ds.read_step r
        | throw s!"Incrementer.read_step failed"
      handleEffects ds' (cont (h ▸ UInt32.toBitVec reply) dmem) ok
  | @Effects.nonmem_store _ dmem addr w v cont =>
    match w with
      | .W32 => match Incrementer.Register.of_addr (UInt64.ofBitVec addr) with
        | .some r => match ds.write_step r (UInt32.ofBitVec v) with
          | .some ds' =>
            handleEffects ds' (cont dmem) ok
          | .none => .error s!"Incrementer.write_step failed"
        | .none => .error s!"nonmem_store at unmapped address {repr addr}"
      | _ => .error s!"nonmem_store of width other than 4 bytes"
  | @Effects.undefined _ _ t cont => handleEffects ds (cont (t.from_hash (hash ds))) ok

def eval_schedule (schedule : List Bool) (e : Executable) (s : SystemState)
    : Except String SystemState :=
  match schedule with
  | device's_turn :: rest =>
    if device's_turn then
      eval_schedule rest e { s with deviceState := s.deviceState.internal_step }
    else
      handleEffects s.deviceState (Executable.step e s.machineState .done) (eval_schedule rest e)
  | .nil => .ok s
