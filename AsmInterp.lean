namespace AsmInterp

-- Registers Enumeration
inductive Reg
| rax | rbx | rcx | rdx
| rsi | rdi | rsp | rbp
| r8  | r9  | r10 | r11
| r12 | r13 | r14 | r15
deriving Repr, BEq, DecidableEq

-- Register State
structure Registers where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
deriving Repr

def Registers.get (regs : Registers) (r : Reg) : UInt64 :=
  match r with
  | .rax => regs.rax | .rbx => regs.rbx | .rcx => regs.rcx | .rdx => regs.rdx
  | .rsi => regs.rsi | .rdi => regs.rdi | .rsp => regs.rsp | .rbp => regs.rbp
  | .r8  => regs.r8  | .r9  => regs.r9  | .r10 => regs.r10 | .r11 => regs.r11
  | .r12 => regs.r12 | .r13 => regs.r13 | .r14 => regs.r14 | .r15 => regs.r15

def Registers.set (regs : Registers) (r : Reg) (v : UInt64) : Registers :=
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v } | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v } | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v } | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v } | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

-- Flags
structure Flags where
  zf : Bool := false -- Zero Flag
  sf : Bool := false -- Sign Flag
  of : Bool := false -- Overflow Flag
  cf : Bool := false -- Carry Flag
deriving Repr, BEq

-- Heap
-- Using Array for memory.
abbrev Address := UInt64
abbrev Byte := UInt8
abbrev Heap := Array Byte

-- Machine State
structure MachineState where
  regs : Registers := {}
  flags : Flags := {}
  rip : UInt64 := 0
  -- Initialize heap with 1024 bytes of 0
  heap : Heap := Array.replicate 1024 0
deriving Repr

def MachineState.getReg (s : MachineState) (r : Reg) : UInt64 :=
  s.regs.get r

def MachineState.setReg (s : MachineState) (r : Reg) (v : UInt64) : MachineState :=
  { s with regs := s.regs.set r v }

def MachineState.readMem (s : MachineState) (addr : Address) : Byte :=
  let idx := addr.toNat
  if idx < s.heap.size then
    s.heap[idx]!
  else
    0

def MachineState.writeMem (s : MachineState) (addr : Address) (val : Byte) : MachineState :=
  let idx := addr.toNat
  if idx < s.heap.size then
    { s with heap := s.heap.set! idx val }
  else
    s -- Ignore out of bounds writes for now

-- Instructions
inductive Operand
| reg (r : Reg)
| imm (v : UInt64)
| mem (addr : Address)
deriving Repr

inductive Instr
| mov (dst : Operand) (src : Operand)
| add (dst : Operand) (src : Operand)
| sub (dst : Operand) (src : Operand)
| jmp (target : UInt64)
| hlt
deriving Repr

-- Evaluation Logic
def updateFlags (res : UInt64) (_v1 : UInt64) (_v2 : UInt64) (_isSub : Bool) : Flags :=
  { zf := res == 0,
    sf := (res >>> 63) == 1,
    of := false, -- TODO: Implement proper overflow logic
    cf := false  -- TODO: Implement proper carry logic
  }

def eval_operand (s : MachineState) (o : Operand) : UInt64 :=
  match o with
  | .reg r => s.getReg r
  | .imm v => v
  | .mem a => s.readMem a |>.toUInt64

def eval (s : MachineState) (i : Instr) : MachineState :=
  match i with
  | .mov dst src =>
    let val := eval_operand s src
    match dst with
    | .reg r => { s with regs := s.regs.set r val, rip := s.rip + 1 }
    | .mem a => { s with heap := s.writeMem a val.toUInt8 |>.heap, rip := s.rip + 1 }
    | _ => s

  | .add dst src =>
    match dst with
    | .reg r =>
      let v1 := s.getReg r
      let v2 := eval_operand s src
      let res := v1 + v2
      let flags := updateFlags res v1 v2 false
      { s with regs := s.regs.set r res, flags := flags, rip := s.rip + 1 }
    | _ => s -- Only reg dst supported for now

  | .sub dst src =>
    match dst with
    | .reg r =>
      let v1 := s.getReg r
      let v2 := eval_operand s src
      let res := v1 - v2
      let flags := updateFlags res v1 v2 true
      { s with regs := s.regs.set r res, flags := flags, rip := s.rip + 1 }
    | _ => s

  | .jmp target =>
    { s with rip := target }

  | .hlt => s

end AsmInterp
