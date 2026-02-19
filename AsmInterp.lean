import Std

-- Registers Enumeration
inductive Reg
| rax | rbx | rcx | rdx
| rsi | rdi | rsp | rbp
| r8  | r9  | r10 | r11
| r12 | r13 | r14 | r15
deriving Repr, BEq, DecidableEq

-- Register State
-- We choose this representation rather than a `Fin 16 -> Word` to avoid
-- reasoning about functional modifications.
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
  of : Bool := false -- Overflow Flag
  cf : Bool := false -- Carry Flag
deriving Repr, BEq

-- Heap
-- We only reason about aligned accesses, so our map only has keys that are = 0
-- % 8. We do not make any assumptions about the memory -- reading an
-- uninitialized value results in an error.
abbrev Address := UInt64
abbrev Word := UInt64
abbrev Heap := Std.ExtHashMap Word Word

-- Machine State
structure MachineState where
  regs : Registers := {}
  flags : Flags := {}
  rip : Nat := 0
  heap : Heap := ∅ 

-- We return errors for ill-formed operations: accessing memory that has not
-- been written before (we cannot assume anything!), non-aligned loads, etc.
abbrev Result a := Except String a

def MachineState.getReg (s : MachineState) (r : Reg) : UInt64 :=
  s.regs.get r

def MachineState.setReg (s : MachineState) (r : Reg) (v : UInt64) : MachineState :=
  { s with regs := s.regs.set r v }

def MachineState.readMem (s : MachineState) (addr : Address) : Result Word :=
  if addr % 8 != 0 then
    .error s!"Out-of-bounds access (rip={repr s.rip})"
  else
    match s.heap[addr]? with
    | .some v => .ok v
    | .none => .error s!"Memory read but not written to (rip={repr s.rip}, addr={repr addr})"

def MachineState.writeMem (s : MachineState) (addr : Address) (val : Word) : Result MachineState :=
  if addr % 8 != 0 then
    .error s!"Out-of-bounds access (rip={repr s.rip})"
  else
    .ok { s with heap := s.heap.insert addr val }

-- Instructions
inductive Operand
| reg (r : Reg)
| imm (v : UInt64)
| mem (addr : Address)
deriving Repr

abbrev Label := String

inductive Instr
| mov (dst : Operand) (src : Operand)
| mulx (hi : Operand) (lo : Operand) (src1: Operand)
| adcx (dst : Operand) (src : Operand)
| adox (dst : Operand) (src : Operand)
| jnz (target : Label)
deriving Repr

def Instr.is_ctrl
  | Instr.jnz _ => true
  | _ => false

-- Evaluation Logic
def eval_operand (s : MachineState) (o : Operand) : Result UInt64 :=
  match o with
  | .reg r => .ok (s.getReg r)
  | .imm v => .ok v
  | .mem a => s.readMem a

def eval_reg_or_mem (s : MachineState) (o : Operand) : Result UInt64 :=
  match o with
  | .reg r => .ok (s.getReg r)
  | .mem a => s.readMem a
  | .imm _ => .error "Ill-formed instruction (rip={repr s.rip})"

def set_reg_or_mem (s: MachineState) (o: Operand) (v: Word): Result MachineState := do
  match o with
  | .reg r =>
      .ok (s.setReg r v)
  | .mem a =>
      let s ← s.writeMem a v
      .ok s
  | .imm _ =>
      .error "Ill-formed instruction (rip={repr s.rip})"

def set_reg (s: MachineState) (o: Operand) (v: Word): Result MachineState := do
  match o with
  | .reg r =>
      .ok (s.setReg r v)
  | .mem _
  | .imm _ =>
      .error "Ill-formed instruction (rip={repr s.rip})"

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
def eval1 (s : MachineState) (i : Instr) (h: not (i.is_ctrl)) : Result MachineState := do
  match i with
  | .mov dst src =>
      let val ← eval_operand s src
      set_reg_or_mem s dst val

  | .adcx dst src =>
      -- Some thoughts: I basically try to assert the well-formedness of
      -- instructions (by asserting that e.g. immediate operands are not
      -- allowed, or that the x64 semantics demand that the destination of adcx
      -- be a general-purpose register... so that it at least simplifies the
      -- reasoning, but realistically, since we intend to consume source
      -- assembly (possibly with an actual frontend to parse .S syntax), the
      -- assembler will enforce eventually that no such nonsensical instructions
      -- exist. Is it worth the trouble?
      let src_v ← eval_reg_or_mem s src
      let dst_v ← eval_reg_or_mem s dst
      let result := src_v.toNat + dst_v.toNat + s.flags.cf.toNat
      let carry := result >>> 64
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with cf := carry != 0 }}
      set_reg s dst result

  | .adox dst src =>
      let src_v ← eval_reg_or_mem s src
      let dst_v ← eval_reg_or_mem s dst
      let result := src_v.toNat + dst_v.toNat + s.flags.of.toNat
      let carry := result >>> 64
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with of := carry != 0 }}
      set_reg s dst result

  | .mulx hi lo src1 =>
      let src1 ← eval_reg_or_mem s src1
      let src2 ← eval_reg_or_mem s (.reg .rdx)
      let result := src1.toNat * src2.toNat
      let s ← set_reg s lo (UInt64.ofNat result)
      set_reg s hi (UInt64.ofNat (result >>> 64))

  | .jnz _ =>
      by contradiction

def ctrl (s: MachineState) (lookup: Label -> Nat) (i: Instr) (h: i.is_ctrl): Result MachineState :=
  match i with
  | .jnz l =>
      if s.flags.zf then
        .ok { s with rip := lookup l }
      else
        .ok { s with rip := s.rip + 1 }
  | _ =>
      by
        sorry

