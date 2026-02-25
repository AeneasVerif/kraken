/-
Kraken - Core Assembly Interpreter Semantics

This file contains the core semantics for x86_64 assembly interpretation.
It is designed to be compatible with Lean 4.22.0.

For proofs requiring newer features (grind tactic), see AsmInterp/Proofs.lean.
For examples, see AsmInterp/Examples.lean.
-/

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

-- Operands (extended with indexed memory modes for MontMul)
-- Memory operands use WORD offsets (multiplied by 8 in code gen) for alignment
inductive Operand
| reg (r : Reg)                                          -- %rax
| imm (v : UInt64)                                       -- $42
| mem (base : Reg) (wordOffset : Int := 0)               -- 8(%rsp) = wordOffset 1
| memIdx (base : Reg) (idx : Reg) (wordOffset : Int := 0) -- (%rsi,%r15,8) + wordOffset*8
| memByte (base : Reg) (byteOffset : Int := 0)           -- Raw byte offset (for lea)
deriving Repr, BEq

instance : Coe Reg Operand where coe := Operand.reg
instance : Coe UInt64 Operand where coe := Operand.imm
attribute [coe] Operand.reg
attribute [coe] Operand.imm

abbrev Label := String

-- Instructions (extended for MontMul)
inductive Instr
  -- Arithmetic
  | add  (dst src : Operand)                   -- addq: dst += src, sets CF, ZF, OF
  | adc  (dst src : Operand)                   -- adcq: dst += src + CF, sets CF, ZF
  | adcx (dst : Operand) (src : Operand)       -- adcxq: dst += src + CF, only affects CF (ADX)
  | adox (dst : Operand) (src : Operand)       -- adoxq: dst += src + OF, only affects OF (ADX)
  | sub  (dst src : Operand)                   -- subq: dst -= src, sets CF, ZF, OF
  | sbb  (dst src : Operand)                   -- sbbq: dst -= src + CF, sets CF, ZF
  | mul  (src : Operand)                       -- mulq: rdx:rax = rax * src
  | mulx (hi lo : Operand) (src : Operand)     -- mulxq: hi:lo = rdx * src (BMI2, no flags)
  | imul (dst src : Operand)                   -- imulq: dst *= src (truncated, sets OF/CF)
  | neg  (dst : Operand)                       -- negq: dst = -dst, sets CF, ZF, OF
  | dec  (dst : Operand)                       -- decq: dst--, sets ZF (not CF!)

  -- Move/Load
  | mov  (dst src : Operand)                   -- movq
  | lea  (dst : Reg) (src : Operand)           -- leaq: dst = effective address

  -- Bitwise
  | xor  (dst src : Operand)                   -- xorq: dst ^= src, clears CF/OF, sets ZF
  | and  (dst src : Operand)                   -- andq: dst &= src, clears CF/OF, sets ZF
  | or   (dst src : Operand)                   -- orq: dst |= src, clears CF/OF, sets ZF

  -- Compare (sets flags only)
  | cmp  (a b : Operand)                       -- cmpq: compute a - b, set flags

  -- Control flow (explicit jumps - core design of Kraken)
  | jmp (target : Label)                       -- Unconditional jump
  | jz  (target : Label)                       -- Jump if ZF=1
  | jnz (target : Label)                       -- Jump if ZF=0
  | jb  (target : Label)                       -- Jump if CF=1 (unsigned below)
  | jae (target : Label)                       -- Jump if CF=0 (unsigned above or equal)
  | jne (target : Label)                       -- Alias for jnz (after cmp)
  | ja  (target : Label)                       -- Jump if CF=0 and ZF=0 (unsigned above)
  deriving Repr

def Instr.is_ctrl
  | Instr.jmp _ | Instr.jnz _ | Instr.jz _
  | Instr.jb _ | Instr.jae _ | Instr.jne _ | Instr.ja _ => true
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

class Throw α where
  throw: String → α

def throw [inst: Throw α] :=
  inst.throw

def MachineState.readMem [Throw α] (s : MachineState) (addr : Address) (ret: Word → α): α :=
  if addr % 8 != 0 then
    throw (s!"Out-of-bounds access (rip={repr s.rip})")
  else
    match s.heap[addr]? with
    | .some v => ret v
    | .none => throw (s!"Memory read but not written to (rip={repr s.rip}, addr={repr addr})")

def MachineState.writeMem [Throw α] (s : MachineState) (addr : Address) (val : Word) (ret: MachineState → α) : α :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    ret { s with heap := s.heap.insert addr val }

-- EVALUATION

-- Compute effective address for memory operand (word offsets × 8)
def effectiveAddr (s : MachineState) : Operand → UInt64
  | .mem base wordOffset =>
    let baseVal := s.getReg base
    if wordOffset >= 0 then
      baseVal + (wordOffset.toNat * 8).toUInt64
    else
      baseVal - ((-wordOffset).toNat * 8).toUInt64
  | .memIdx base idx wordOffset =>
    let baseVal := s.getReg base
    let idxVal := s.getReg idx
    let addr := baseVal + idxVal * 8  -- Fixed scale of 8
    if wordOffset >= 0 then
      addr + (wordOffset.toNat * 8).toUInt64
    else
      addr - ((-wordOffset).toNat * 8).toUInt64
  | .memByte base byteOffset =>
    let baseVal := s.getReg base
    if byteOffset >= 0 then
      baseVal + byteOffset.toNat.toUInt64
    else
      baseVal - (-byteOffset).toNat.toUInt64
  | _ => 0  -- Not a memory operand

def eval_operand [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .imm v => ret v
  | .mem _ _ => s.readMem (effectiveAddr s o) ret
  | .memIdx _ _ _ => s.readMem (effectiveAddr s o) ret
  | .memByte _ _ => s.readMem (effectiveAddr s o) ret

def eval_reg_or_mem [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .mem _ _ | .memIdx _ _ _ | .memByte _ _ => s.readMem (effectiveAddr s o) ret
  | .imm _ => throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg_or_mem [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _ _ | .memIdx _ _ _ | .memByte _ _ =>
      s.writeMem (effectiveAddr s o) v ret
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _ _ | .memIdx _ _ _  | .memByte _ _
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def next (s: MachineState): MachineState := { s with rip := s.rip + 1 }

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def strt1 [Throw α] (s : MachineState) (i : Instr) (ret: MachineState → α): α :=
  match i with
  | .mov dst src =>
      eval_operand s src (fun val =>
      set_reg_or_mem s dst val ret)

  | .add dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v.toNat + src_v.toNat
      let carry := result >>> 64
      let result64 := UInt64.ofNat result
      let zf := result64 == 0
      let cf := carry != 0
      -- OF is set if sign bits of operands are same but result sign differs
      let of := (dst_v.toInt64.toInt + src_v.toInt64.toInt >= 2^63) ||
                (dst_v.toInt64.toInt + src_v.toInt64.toInt < -2^63)
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .adc dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v.toNat + src_v.toNat + s.flags.cf.toNat
      let carry := result >>> 64
      let result64 := UInt64.ofNat result
      let zf := result64 == 0
      let cf := carry != 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { s.flags with zf, cf }})))

  | .adcx dst src =>
      -- Some thoughts: I basically try to assert the well-formedness of
      -- instructions (by asserting that e.g. immediate operands are not
      -- allowed, or that the x64 semantics demand that the destination of adcx
      -- be a general-purpose register... so that it at least simplifies the
      -- reasoning, but realistically, since we intend to consume source
      -- assembly (possibly with an actual frontend to parse .S syntax), the
      -- assembler will enforce eventually that no such nonsensical instructions
      -- exist. Is it worth the trouble?
      eval_reg_or_mem s src (fun src_v  =>
      eval_reg_or_mem s dst (fun dst_v  =>
      let result := src_v.toNat + dst_v.toNat + s.flags.cf.toNat
      let carry := result >>> 64
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with cf := carry != 0 }}
      set_reg s dst result ret))

  | .adox dst src =>
      eval_reg_or_mem s src (fun src_v  =>
      eval_reg_or_mem s dst (fun dst_v  =>
      -- TODO: figure out how to make sure that this let-binding does not get
      -- inlined, *unless* the right-hand side can be computed to a constant
      let result := src_v.toNat + dst_v.toNat + s.flags.of.toNat
      let carry := result >>> 64
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with of := carry != 0 }}
      set_reg s dst result ret))

  | .sub dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let res := (Int.ofNat dst_v.toNat) - (Int.ofNat src_v.toNat)
      let cf := res < 0
      let of := dst_v.toInt64.toInt - src_v.toInt64.toInt >= 2^63 ||
                dst_v.toInt64.toInt - src_v.toInt64.toInt < -2^63
      let result64 := UInt64.ofInt res
      let zf := result64 == 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .sbb dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let res := (Int.ofNat dst_v.toNat) - (Int.ofNat src_v.toNat) - s.flags.cf.toNat
      let cf := res < 0
      let result64 := UInt64.ofInt res
      let zf := result64 == 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { s.flags with zf, cf }})))

  | .mul src =>
      -- mulq: rdx:rax = rax * src
      eval_reg_or_mem s src (fun src_v =>
      let rax_v := s.getReg .rax
      let result := rax_v.toNat * src_v.toNat
      let lo := UInt64.ofNat result
      let hi := UInt64.ofNat (result >>> 64)
      let s := s.setReg .rax lo
      let s := s.setReg .rdx hi
      -- mul sets OF and CF if high half is non-zero
      let cf := hi != 0
      let of := hi != 0
      ret { s with flags := { s.flags with cf, of }})

  | .mulx hi lo src1 =>
      eval_reg_or_mem s src1 (fun src1_v  =>
      let src2_v := s.getReg .rdx
      let result := src1_v.toNat * src2_v.toNat
      -- Semantics say that if hi and lo are aliased, the value written is hi
      set_reg s lo (UInt64.ofNat result) (fun s  =>
      set_reg s hi (UInt64.ofNat (result >>> 64)) ret))

  | .imul dst src =>
      eval_reg_or_mem s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v.toNat * src_v.toNat
      let result64 := UInt64.ofNat result
      -- OF/CF set if result doesn't fit in 64 bits
      let overflow := result >>> 64 != 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { s.flags with cf := overflow, of := overflow }})))

  | .neg dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := 0 - dst_v
      let zf := result == 0
      let cf := dst_v != 0  -- CF is set unless operand is 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf, cf }}))

  | .dec dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v - 1
      let zf := result == 0
      -- dec does NOT affect CF (important for MontMul!)
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf }}))

  | .lea dst src =>
      -- lea computes effective address, doesn't access memory
      let addr := effectiveAddr s src
      ret (s.setReg dst addr)

  | .xor dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v ^^^ src_v
      let zf := result == 0
      -- xor clears CF and OF
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .and dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v &&& src_v
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .or dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v ||| src_v
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .cmp a b =>
      eval_reg_or_mem s a (fun a_v =>
      eval_operand s b (fun b_v =>
      let res := (Int.ofNat a_v.toNat) - (Int.ofNat b_v.toNat)
      let cf := res < 0
      let zf := res == 0
      let of := a_v.toInt64.toInt - b_v.toInt64.toInt >= 2^63 ||
                a_v.toInt64.toInt - b_v.toInt64.toInt < -2^63
      ret { s with flags := { zf, of, cf }}))

  | _ => throw s!"unsupported non-control instruction {repr i}"

def jump_if [Throw α] (s: MachineState) (b: Bool) (rip: Nat) (ret: MachineState → α): α :=
  if b then
    ret { s with rip }
  else
    ret (next s)


def ctrl [Throw α] (s: MachineState) (lookup: Label → (Nat → α) → α) (i: Instr) (ret: MachineState → α): α :=
  match i with
  | .jmp l =>
      lookup l (fun rip =>
      jump_if s True rip ret)
  | .jnz l =>
      lookup l (fun rip =>
      jump_if s (!s.flags.zf) rip ret)
  | .jz l =>
      lookup l (fun rip =>
      jump_if s s.flags.zf rip ret)
  | .jb l =>
      -- Jump if below (unsigned): CF=1
      lookup l (fun rip =>
      jump_if s s.flags.cf rip ret)
  | .jae l =>
      -- Jump if above or equal (unsigned): CF=0
      lookup l (fun rip =>
      jump_if s (!s.flags.cf) rip ret)
  | .jne l =>
      -- Alias for jnz: ZF=0
      lookup l (fun rip =>
      jump_if s (!s.flags.zf) rip ret)
  | .ja l =>
      -- Jump if above (unsigned): CF=0 AND ZF=0
      lookup l (fun rip =>
      jump_if s (!s.flags.cf && !s.flags.zf) rip ret)
  | _ => throw s!"unsupported control instruction {repr i}"

abbrev Program := List (Option Label × Instr)

def lookup [Throw α] (p: Program) (l: Label) (ret: Nat → α): α :=
  match p.findIdx? (fun (l', _) => l' = .some l) with
  | .some rip => ret rip
  | .none => throw s!"Invalid label: {repr l}"

def fetch [Throw α] (p: Program) (s: MachineState) (ret: (Option Label × Instr) → α): α :=
  match p[s.rip]? with
  | .some ins => ret ins
  | .none => throw "Impossible: PC outside of program bounds"

def eval1 [m: Throw α] (p: Program) (s: MachineState) (ret: MachineState → α): α :=
  fetch p s (fun (_, i) =>
    if i.is_ctrl then
      ctrl s (lookup p) i ret
    else
      strt1 s i (fun s =>
      ret (next s)))

def eval (p: Program) (s: MachineState): Option MachineState := do
  let s ← (eval1 (m:={ throw _ := Option.none }) p s) (fun s => .some s)
  eval p s
partial_fixpoint

def step1 (p: Program) (s: MachineState) (post: _) :=
  eval1 (m:={ throw _ := False }) p s post

def Post := MachineState → Prop

inductive eventually (prog: Program) (p: MachineState → Prop): MachineState -> Prop
  | done (initial: MachineState):
      p initial →
      eventually _ p initial
  | step (initial: MachineState):
      (mid_p: Post) ->
      step1 prog initial mid_p →
      (forall (mid: MachineState), mid_p mid → eventually _ p mid) →
      eventually _ p initial

-- TACTICS

-- NOTES: why is the right way of doing this? Ideally, we would not ask to
-- simplify anything that is not an internal definition, because it is not
-- modular. Problematic things here include, e.g., List.findIdx? (what if the
-- user uses this very function in their post-condition?).
--
-- Something equivalent to `match goal with` might work. Alternatively, we could
-- have copies of definitions, e.g. `def my_findIdx := normalize List.findIdx?`.
-- TODO: determine how to do that in Lean.
--
-- Furthermore, it would be nice to be able to specify that reducing e.g. a
-- projector should only be done if the left-hand side is not a variable.
syntax "step_one" : tactic
macro_rules
  | `(tactic|step_one) =>
  `(tactic|
    simp [
      step1,Instr.is_ctrl,eval1,fetch,
      -- works for calls to strt1
      strt1,eval_operand,eval_reg_or_mem,set_reg,set_reg_or_mem,effectiveAddr,MachineState.setReg,next,Registers.set,pure,bind,next,MachineState.getReg,Registers.get,
      -- or calls to ctrl
      ctrl,lookup,List.findIdx?,List.findIdx?.go,pure,bind,jump_if,next])
