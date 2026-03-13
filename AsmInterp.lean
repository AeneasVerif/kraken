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

instance : Repr Heap where
  reprPrec _ _ := "<opaque memory>"

-- Machine State
structure MachineState where
  regs : Registers := {}
  flags : Flags := {}
  rip : Nat := 0
  heap : Heap := ∅ 
deriving Repr

-- Instructions
inductive Operand
| reg (r : Reg)
| imm (v : UInt64)
| mem (addr : Address)
deriving Repr

abbrev Label := String

inductive Instr
| mov (dst : Operand) (src : Operand)
deriving Repr

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

def next (s: MachineState): MachineState := { s with rip := s.rip + 1 }

abbrev Program := List (Option Label × Instr)

--------------------------------------------------------------------------------
-- FIRST STYLE
--------------------------------------------------------------------------------

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

def set_reg_or_mem [Monad m] [MonadExcept String m] (s: MachineState) (o: Operand) (v: Word): m MachineState := do
  match o with
  | .reg r =>
      pure (s.setReg r v)
  | .mem a =>
      let s ← s.writeMem a v
      pure s
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def strt1 [Monad m] [MonadExcept String m] (s : MachineState) (i : Instr) : m MachineState := do
  match i with
  | .mov dst src =>
      let val ← eval_operand s src
      set_reg_or_mem s dst val

def fetch [Pure m] [MonadExcept String m] (p: Program) (s: MachineState): m (Option Label × Instr) :=
  p[s.rip]?.except "Impossible: PC outside of program bounds"

def eval1 [Monad m] [MonadExcept String m] (p: Program) (s: MachineState): m MachineState := do
  let (l, i) ← fetch p s
  match l with
  | .none =>
      let s ← strt1 s i
      pure (next s)
  | .some _ =>
      throw "Did not expect a label"

def step1 (p: Program) (s: MachineState) (post: _) :=
  @ExceptCpsT.runK Id Prop String MachineState (eval1 p s) "" post (fun _ => False) 

--------------------------------------------------------------------------------
-- SECOND STYLE
--------------------------------------------------------------------------------

class Throw α where
  throw: String → α

def throw [inst: Throw α] :=
  inst.throw

def MachineState.readMem2 [Throw α] (s : MachineState) (addr : Address) (ret: Word → α): α :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    match s.heap[addr]? with
    | .none => throw (s!"Memory read but not written to (rip={repr s.rip}, addr={repr addr})")
    | .some v => ret v

def MachineState.writeMem2 [Throw α] (s : MachineState) (addr : Address) (val : Word) (ret: MachineState → α): α :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    ret { s with heap := s.heap.insert addr val }

-- EVALUATION

def eval_operand2 [Throw α] (s : MachineState) (o : Operand) (pure: UInt64 → α): α :=
  match o with
  | .reg r => pure (s.getReg r)
  | .imm v => pure v
  | .mem a => s.readMem2 a pure

def set_reg_or_mem2 [Throw α] (s: MachineState) (o: Operand) (v: Word) (pure: MachineState → α): α :=
  match o with
  | .reg r =>
      pure (s.setReg r v)
  | .mem a =>
      s.writeMem2 a v pure
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def strt2 [Throw α] (s : MachineState) (i : Instr) (pure: MachineState → α): α :=
  match i with
  | .mov dst src =>
      eval_operand2 s src λ val =>
      set_reg_or_mem2 s dst val pure

def fetch2 [Throw α] (p: Program) (s: MachineState) (pure: (Option Label × Instr) → α): α :=
  match p[s.rip]? with
  | .none => throw "Impossible: PC outside of program bounds" 
  | .some v => pure v

def eval2 [t: Throw α] (p: Program) (s: MachineState) (pure: MachineState → α): α :=
  fetch2 p s λ (l, i) =>
  match l with
  | .none =>
      strt2 s i λ s =>
      pure (next s)
  | .some _ =>
      throw "Did not expect a label"

def step2 (p: Program) (s: MachineState) (post: _) :=
  (eval2 (t := { throw := fun _ => False }) p s) post

-- TEST

-- Example 1: single step of execution
def p1: Program := [
  (.none, .mov (.reg .rax) (.imm 1)),
]

-- First style
example: step1 p1 {} (fun s => s.regs.rax = 1) := by
  simp [step1,eval1,ExceptCpsT.runK,fetch,Option.except,bind,pure]
  /- GOAL:
  (match p1[0]? with
  | none => MonadExcept.throw "Impossible: PC outside of program bounds"
  | some v => fun x k x_1 => k v)
  Prop
  (fun a =>
    (match a.fst with
      | none => fun x k₁ k₂ => strt1 { } a.snd x (fun a => k₁ (next a)) k₂
      | some val => MonadExcept.throw "Did not expect a label")
      Prop (fun s => s.regs.rax = 1) fun x => False)
  fun x => False
  -/
  -- CANNOT BETA-REDUCE AT THIS STAGE
  sorry

example: step2 p1 {} (fun s => s.regs.rax = 1) := by
  simp [step2,eval2,fetch2]
  /- GOAL:
  match p1[0]? with
  | none => _root_.throw "Impossible: PC outside of program bounds"
  | some v =>
    match v.fst with
    | none => strt2 { } v.snd fun s => (next s).regs.rax = 1
    | some val => _root_.throw "Did not expect a label"
  -/
  -- NO NEED TO BETA-REDUCE: the head of the goal is what we want to make progress on
  sorry
