import Std

-- FIXME -- surely something like this is in Std?

def Option.except [Pure m] [MonadExcept e m] (self: Option α) (err : e): m α :=
  match self with
  | .none => throw err
  | .some v => pure v

-- STATE, INSTRUCTIONS, LABELS

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
abbrev Heap := Std.ExtHashMap Address Word

-- Machine State
structure MachineState where
  regs : Registers := {}
  flags : Flags := {}
  rip : Nat := 0
  heap : Heap := ∅ 

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

-- HELPERS

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

def MachineState.getReg (s : MachineState) (r : Reg) : UInt64 :=
  s.regs.get r

def MachineState.setReg (s : MachineState) (r : Reg) (v : UInt64) : MachineState :=
  { s with regs := s.regs.set r v }

def MachineState.readMem [Pure m] [MonadExcept String m] (s : MachineState) (addr : Address) : m Word :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    s.heap[addr]?.except (s!"Memory read but not written to (rip={repr s.rip}, addr={repr addr})")

def MachineState.writeMem [Pure m] [MonadExcept String m] (s : MachineState) (addr : Address) (val : Word) : m MachineState :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    pure { s with heap := s.heap.insert addr val }


-- EVALUATION

def eval_operand [Pure m] [MonadExcept String m] (s : MachineState) (o : Operand) : m UInt64 :=
  match o with
  | .reg r => pure (s.getReg r)
  | .imm v => pure v
  | .mem a => s.readMem a

def eval_reg_or_mem [Pure m] [MonadExcept String m] (s : MachineState) (o : Operand) : m UInt64 :=
  match o with
  | .reg r => pure (s.getReg r)
  | .mem a => s.readMem a
  | .imm _ => throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg_or_mem [Monad m] [MonadExcept String m] (s: MachineState) (o: Operand) (v: Word): m MachineState := do
  match o with
  | .reg r =>
      pure (s.setReg r v)
  | .mem a =>
      let s ← s.writeMem a v
      pure s
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg [Pure m] [MonadExcept String m] (s: MachineState) (o: Operand) (v: Word): m MachineState :=
  match o with
  | .reg r =>
      pure (s.setReg r v)
  | .mem _
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def next (s: MachineState): MachineState := { s with rip := s.rip + 1 }

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
def strt1 [Monad m] [MonadExcept String m] (s : MachineState) (i : Instr) : m MachineState := do
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
      -- Semantics say that if hi and lo are aliased, the value written is hi
      let s ← set_reg s lo (UInt64.ofNat result)
      set_reg s hi (UInt64.ofNat (result >>> 64))
  | _ => throw "unsupported non-control instruction {repr i}"

def ctrl [Monad m] [MonadExcept String m] (s: MachineState) (lookup: Label → m Nat) (i: Instr) : m MachineState := do
  match i with
  | .jnz l =>
      if !s.flags.zf then
        let rip ← lookup l
        pure { s with rip }
      else
        pure (next s)
  | _ => throw "unsupported control instruction {repr i}"

abbrev Program := List (Option Label × Instr)

def lookup [Pure m] [MonadExcept String m] (p: Program) (l: Label): m Nat :=
  (p.findIdx? (fun (l', _) => l' = .some l)).except "Invalid label: {repr l}"

def fetch [Pure m] [MonadExcept String m] (p: Program) (s: MachineState): m (Option Label × Instr) :=
  p[s.rip]?.except "Impossible: PC outside of program bounds"

def eval1 [Monad m] [MonadExcept String m] (p: Program) (s: MachineState): m MachineState := do
  let (_, i) ← fetch p s
  if i.is_ctrl then
    let s ← ctrl s (lookup p) i
    pure s
  else
    let s ← strt1 s i
    pure (next s)

def eval (p: Program) (s: MachineState): Option MachineState := do
  let s ← (eval1 (m:=Except String) p s).toOption
  eval p s
partial_fixpoint

def step1 (p: Program) (s: MachineState) (post: _) :=
  @ExceptCpsT.runK Id Prop String MachineState (eval1 p s) "" post (fun _ => False) 

def Post := MachineState → Prop

inductive eventually (p: Program): Post → Post
  | done post initial:
      post initial →
      eventually _ post initial
  | step post initial (midset: Post):
      step1 p initial midset →
      (forall (mid: MachineState), midset mid → eventually _ post mid) →
      eventually _ post initial

theorem step_cps {p : Program} (post: Post) (initial: MachineState):
  step1 p initial (fun mid => eventually p post mid) → eventually p post initial :=
  by
    intro
    apply eventually.step
    <;> try assumption
    intro
    simp

-- TEST

def p1: Program := [
  (.none, .mov (.reg .rax) (.imm 1)),
]

example: @ExceptCpsT.runK Id Prop String MachineState (eval1 p1 {}) "" (fun s => s.regs.rax = 1) (fun _ => False) := by
  simp [Instr.is_ctrl,p1,eval1,fetch,Option.except,ExceptCpsT.runK,bind,pure]
  simp [strt1,eval_operand,set_reg_or_mem,MachineState.setReg,next,Registers.set,pure,bind]

def p2: Program := [
  (.none, .mov (.reg .rax) (.imm 1)),
  (.none, .mov (.reg .rax) (.imm 2)),
]

example: eventually p2 (fun s => s.regs.rax = 2) {} := by
  simp [p2]
  apply step_cps
  simp [step1,Instr.is_ctrl,eval1,fetch,Option.except,ExceptCpsT.runK,bind,pure]
  simp [strt1,eval_operand,set_reg_or_mem,MachineState.setReg,next,Registers.set,pure,bind]
  apply step_cps
  simp [step1,Instr.is_ctrl,eval1,fetch,Option.except,ExceptCpsT.runK,bind,pure]
  simp [strt1,eval_operand,set_reg_or_mem,MachineState.setReg,next,Registers.set,pure,bind]
  apply eventually.done
  simp

