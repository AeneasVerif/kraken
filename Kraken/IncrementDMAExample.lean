import Kraken.Semantics

/-
A dummy device that can be controlled via MMIO and can only
perform the veeery complicated operation of incrementing an
array of numbers by one.
Illustrates that in the 2x2 matrix of what effect can modify what state
(effect ∈ { nonmem_store, nonmem_load }) x (state ∈ { DeviceState, MachineState })
all the four combinations can happen:

                DeviceState     MachineState
nonmem_store         1)              2)
nonmem_load          3)              4)

1) An MMIO store sets the BUF_ADDR and BUF_SIZE registers of the Incrementer device
   and then sets the STATUS register of the Incrementer device to STATUS_BUSY.
2) This results in a change of logical ownership of the memory from BUF_ADDR to
   BUF_ADDR+BUF_SIZE: It is now owned by the Incrementer device, and we model this
   ownership change by removing it from the dmem in MachineState, and adding it
   to the state-machine state in the DeviceState.
3) The CPU then polls the STATUS register of the Incrementer device, until it
   reads STATUS_DONE. Once that's the case, it gets back the ownership of the memory
   from BUF_ADDR to BUF_ADDR+BUF_SIZE.
4) The fact that the CPU read STATUS_DONE causes the Incrementer device to go
   back into STATUS_IDLE.
-/

-- state as seen by software, not necessarily implemented like this in hardware
inductive IncrementerState
  | idle (buf_addr : Option UInt64) (buf_size : Option UInt64)
  | busy (buf_addr : UInt64) (input : List UInt8) (max_steps_until_done : Nat)
  | done (result : List UInt8)
  deriving Hashable

inductive Incrementer.Register | BUF_ADDR | BUF_SIZE | STATUS

def STATUS_REG_ADDR : UInt64 := 4096
def BUF_ADDR_REG_ADDR : UInt64 := 4104
def BUF_SIZE_REG_ADDR : UInt64 := 4112

def STATUS_IDLE : UInt64 := 0
def STATUS_BUSY : UInt64 := 1
def STATUS_DONE : UInt64 := 2

inductive IncrementerState.read_step
  (s : IncrementerState) (r : Incrementer.Register)
  (v : UInt64) (s' : IncrementerState) : Prop where -- TODO

inductive IncrementerState.write_step
  (s : IncrementerState) (r : Incrementer.Register) (v : UInt64)
  (s' : IncrementerState) : Prop where -- TODO

inductive IncrementerState.internal_step
  (s : IncrementerState)
  (s': IncrementerState) : Prop where -- TODO

def Incrementer.Register.of_addr (addr : UInt64) : Option Incrementer.Register :=
  if addr == STATUS_REG_ADDR then some .STATUS
  else if addr == BUF_ADDR_REG_ADDR then some .BUF_ADDR
  else if addr == BUF_SIZE_REG_ADDR then some .BUF_SIZE
  else none

structure SystemState where
  machineState : MachineState
  deviceState : IncrementerState

def Sem.all (s : Sem) (ds : IncrementerState) (post : SystemState → Prop) : Prop
  := by sorry
