import Std
import Lean
import Lean.Meta.Sym.Grind
open Lean Meta Sym Elab Tactic

class Throw α where
  throw: String → α

def throw [inst: Throw α] :=
  inst.throw

-- Registers Enumeration
inductive Reg
| rax | rbx | rcx | rdx
| rsi | rdi | rsp | rbp
| r8  | r9  | r10 | r11
| r12 | r13 | r14 | r15

-- Aliased 32-bit registers
| eax | ebx | ecx | edx
| esi | edi | esp | ebp

-- Aliased 16-bit registers
| ax | bx | cx | dx
| si | di | sp | bp
deriving Repr, BEq, DecidableEq

inductive Width
| W16
| W32
| W64
deriving Repr, BEq, DecidableEq

def mask16: UInt64 := 0x0000FFFF
def mask32: UInt64 := 0xFFFFFFFF
def mask64: UInt64 := -1

def Width.toNat
| W16 => 16
| W32 => 32
| W64 => 64

def Width.toMask
| W16 => mask16
| W32 => mask32
| W64 => mask64

def Reg.width
| rax | rbx | rcx | rdx
| rsi | rdi | rsp | rbp
| r8  | r9  | r10 | r11
| r12 | r13 | r14 | r15 => Width.W64

| eax | ebx | ecx | edx
| esi | edi | esp | ebp => .W32

| ax | bx | cx | dx
| si | di | sp | bp => .W16

def Reg.shrink [Throw α] (self: Reg) (w: Width) (ret: Reg → α): α :=
  match self, w with
  | .rax, .W64 => ret .rax
  | .rax, .W32 => ret .eax
  | .rax, .W16 => ret .ax
  | .eax, .W32 => ret .eax
  | .eax, .W16 => ret .ax
  | .ax, .W16 => ret .ax

  | .rbx, .W64 => ret .rbx
  | .rbx, .W32 => ret .ebx
  | .rbx, .W16 => ret .bx
  | .ebx, .W32 => ret .ebx
  | .ebx, .W16 => ret .bx
  | .bx, .W16 => ret .bx

  | .rcx, .W64 => ret .rcx
  | .rcx, .W32 => ret .ecx
  | .rcx, .W16 => ret .cx
  | .ecx, .W32 => ret .ecx
  | .ecx, .W16 => ret .cx
  | .cx, .W16 => ret .cx

  | .rdx, .W64 => ret .rdx
  | .rdx, .W32 => ret .edx
  | .rdx, .W16 => ret .dx
  | .edx, .W32 => ret .edx
  | .edx, .W16 => ret .dx
  | .dx, .W16 => ret .dx

  | .rsi, .W64 => ret .rsi
  | .rsi, .W32 => ret .esi
  | .rsi, .W16 => ret .si
  | .esi, .W32 => ret .esi
  | .esi, .W16 => ret .si
  | .si, .W16 => ret .si

  | .rdi, .W64 => ret .rdi
  | .rdi, .W32 => ret .edi
  | .rdi, .W16 => ret .di
  | .edi, .W32 => ret .edi
  | .edi, .W16 => ret .di
  | .di, .W16 => ret .di

  | .rsp, .W64 => ret .rsp
  | .rsp, .W32 => ret .esp
  | .rsp, .W16 => ret .sp
  | .esp, .W32 => ret .esp
  | .esp, .W16 => ret .sp
  | .sp, .W16 => ret .sp

  | .rbp, .W64 => ret .rbp
  | .rbp, .W32 => ret .ebp
  | .rbp, .W16 => ret .bp
  | .ebp, .W32 => ret .ebp
  | .ebp, .W16 => ret .bp
  | .bp, .W16 => ret .bp

  | _, _ => throw "64-bit only register"

-- We only track values held in the widest registers -- these are 64-bit, without any particular
-- intepretation, i.e., UInt64. However, for the computation of e.g. the overflow flag, one has to
-- intepret the value held in a potentially smaller register **as a signed integer**.
def UInt64.toIntWithWidth (self: UInt64) (w: Width): Int :=
  match w with
  | .W64 => self.toInt64.toInt
  | .W32 => (self &&& mask32).toNat.toInt32.toInt
  | .W16 => (self &&& mask16).toNat.toInt16.toInt

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
-- Immediates: we use a single Int64 type since the parser already handles
-- sign-extension from AT&T syntax. The semantic value is always 64-bit signed.
| imm (v : Int64)                                        -- $42 (signed immediate)
| mem (base : Reg) (idx : Option Reg := .none) (scale : Nat := 1) (disp : Int := 0)
  -- Standard x86: base + idx*scale + disp. E.g. 8(%rsp) = disp 8, (%rsi,%r15,8) = idx .r15
  -- Per Intel SDM Vol. 2A Section 2.1.5 (SIB byte), valid scale values are 1, 2, 4, 8.
  -- The default scale is 1 (SIB SS bits = 00). Scale must be explicit in AT&T syntax when != 1.
deriving Repr, BEq

instance : Coe Reg Operand where coe := Operand.reg
instance : Coe Int64 Operand where coe := Operand.imm
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
  | mulx (hi lo : Reg) (src : Operand)     -- mulxq: hi:lo = rdx * src (BMI2, no flags)
  | imul (dst : Reg) (src : Operand)                   -- imulq: dst *= src (truncated, sets OF/CF)
  | neg  (dst : Operand)                       -- negq: dst = -dst, sets CF, ZF, OF
  | dec  (dst : Operand)                       -- decq: dst--, sets ZF (not CF!)

  -- Move/Load
  | mov  (dst src : Operand)                   -- movq: 64-bit move (only 64-bit registers for now)
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

def read16 (x: UInt64): UInt64 := x &&& mask16
def read32 (x: UInt64): UInt64 := x &&& mask32

def Registers.get (regs : Registers) (r : Reg) : UInt64 :=
  match r with
  | .rax => regs.rax | .rbx => regs.rbx | .rcx => regs.rcx | .rdx => regs.rdx
  | .rsi => regs.rsi | .rdi => regs.rdi | .rsp => regs.rsp | .rbp => regs.rbp
  | .r8  => regs.r8  | .r9  => regs.r9  | .r10 => regs.r10 | .r11 => regs.r11
  | .r12 => regs.r12 | .r13 => regs.r13 | .r14 => regs.r14 | .r15 => regs.r15

  | .eax => read32 regs.rax | .ebx => read32 regs.rbx | .ecx => read32 regs.rcx | .edx => read32 regs.rdx
  | .esi => read32 regs.rsi | .edi => read32 regs.rdi | .esp => read32 regs.rsp | .ebp => read32 regs.rbp

  | .ax => read16 regs.rax | .bx => read16 regs.rbx | .cx => read16 regs.rcx | .dx => read16 regs.rdx
  | .si => read16 regs.rsi | .di => read16 regs.rdi | .sp => read16 regs.rsp | .bp => read16 regs.rbp

def write16 (dst: UInt64) (src: UInt64): UInt64 := 
  dst &&& ~~~mask16 ||| read16 src

def write32 (dst: UInt64) (src: UInt64): UInt64 := 
  dst &&& ~~~mask32 ||| read32 src

def Registers.set (regs : Registers) (r : Reg) (v : UInt64) : Registers :=
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v } | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v } | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v } | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v } | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

  | .eax => { regs with rax := write32 regs.rax v } | .ebx => { regs with rbx := write32 regs.rbx v } | .ecx => { regs with rcx := write32 regs.rcx v } | .edx => { regs with rdx := write32 regs.rdx v }
  | .esi => { regs with rsi := write32 regs.rsi v } | .edi => { regs with rdi := write32 regs.rdi v } | .esp => { regs with rsp := write32 regs.rsp v } | .ebp => { regs with rbp := write32 regs.rbp v }

  | .ax => { regs with rax := write16 regs.rax v } | .bx => { regs with rbx := write16 regs.rbx v } | .cx => { regs with rcx := write16 regs.rcx v } | .dx => { regs with rdx := write16 regs.rdx v }
  | .si => { regs with rsi := write16 regs.rsi v } | .di => { regs with rdi := write16 regs.rdi v } | .sp => { regs with rsp := write16 regs.rsp v } | .bp => { regs with rbp := write16 regs.rbp v }

def MachineState.getReg (s : MachineState) (r : Reg) : UInt64 :=
  s.regs.get r

def MachineState.setReg (s : MachineState) (r : Reg) (v : UInt64) : MachineState :=
  { s with regs := s.regs.set r v }

def Operand.width [Throw α] (self: Operand) (ret: Width → α): α :=
  match self with
  | reg r => ret r.width
  | mem base _ _ _ => ret base.width
  | _ => throw "Immediates do not carry a bit width"

def MachineState.readMem [Throw α] (s : MachineState) (addr : Address) (width: Width) (ret: Word → α): α :=
  if addr % 8 != 0 then
    throw (s!"Out-of-bounds access (rip={repr s.rip})")
  else
    match s.heap[addr]? with
    | .some v => ret (v &&& width.toMask) -- little-endian
    | .none => throw (s!"Memory read but not written to (rip={repr s.rip}, addr={repr addr})")

def MachineState.writeMem [Throw α] (s : MachineState) (addr : Address) (w: Width) (val : Word) (ret: MachineState → α) : α :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else if w != .W64 then
    throw s!"TODO: figure out what we do here"
  else
    ret { s with heap := s.heap.insert addr val }

-- Convert Int64 immediate to UInt64 for execution
-- This is a direct conversion since the parser already handled sign-extension
@[simp] def eval_imm (v : Int64) : UInt64 := v.toUInt64

@[simp] theorem Int64_toUInt64_zero : Int64.toUInt64 0 = 0 := by native_decide
@[simp] theorem Int64_toUInt64_one : Int64.toUInt64 1 = 1 := by native_decide
@[simp] theorem Int64_toUInt64_two : Int64.toUInt64 2 = 2 := by native_decide
@[simp] theorem Int64_toUInt64_zero_toNat : (Int64.toUInt64 0).toNat = 0 := by native_decide
@[simp] theorem Int64_toUInt64_one_toNat : (Int64.toUInt64 1).toNat = 1 := by native_decide
@[simp] theorem Int64_toUInt64_two_toNat : (Int64.toUInt64 2).toNat = 2 := by native_decide

-- UInt64.ofInt (k : Int) ≠ 0 when k is a natural number with k < 2^64 and k ≠ 0
-- This proof uses only core Lean lemmas (no Batteries/Mathlib)
theorem UInt64_ofInt_natCast_ne_zero (k : Nat) (h_lt : k < 2^64) (h_ne : k ≠ 0) :
    UInt64.ofInt (k : Int) ≠ 0 := by
  simp only [UInt64.ofInt, ne_eq]
  intro h
  have h1 := congrArg UInt64.toNat h
  simp only [UInt64.toNat_ofNat] at h1
  -- Int mod to Nat conversion
  have h_klt : (k : Int) < 2^64 := Int.ofNat_lt.mpr h_lt
  have h_mod : (↑k : Int) % (2^64 : Int) = k := Int.emod_eq_of_lt (Int.natCast_nonneg k) h_klt
  conv at h1 => lhs; rw [show (↑k : Int) % (2^64 : Int) = ↑k from h_mod]
  simp only [Int.toNat_natCast] at h1
  -- h1: (UInt64.ofNat k).toNat = 0 % 2^64
  have h2 : (UInt64.ofNat k).toNat = k % 2^64 := UInt64.toNat_ofNat
  have hkmod : k % 2^64 = k := Nat.mod_eq_of_lt h_lt
  have hzero : (0 : Nat) % 2^64 = 0 := Nat.zero_mod (2^64)
  rw [h2, hkmod, hzero] at h1
  exact h_ne h1



-- Compute effective address: base + idx*scale + disp. Per the Intel manual:
-- - if the effective address is computed in a larger size than the destination operand, the bits
--   are simply clamped (this is the behavior of setReg for e.g. eax -- no action needed here)
-- - if the effective address is computed in a smaller size than the destination operand, then it is
--   zero-extended (in other words, upper bits are discarded)
def effective_addr [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → Width → α): α :=
  match o with
  | .mem base idx scale disp =>
    -- ASSUME: base.width == idx.width (TODO: check)
    let idxVal := match idx with | .some r => s.getReg r | .none => 0
    ret (((s.getReg base) + idxVal * scale.toUInt64 + UInt64.ofInt disp) &&& base.width.toMask) base.width
  | _ => throw "effective_addr called on non-memory operand"

def eval_operand [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .imm v => ret (eval_imm v)
  | .mem _ _ _ _ => effective_addr s o (fun addr w => s.readMem addr w ret)

def eval_reg_or_mem [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → Width → α): α :=
  match o with
  | .reg r => ret (s.getReg r) r.width
  | .mem _ _ _ _ => effective_addr s o (fun addr w => s.readMem addr w (fun word => ret word w))
  | .imm _ => throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg_or_mem [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _ _ _ _ =>
      effective_addr s o (fun addr w => s.writeMem addr w v ret)
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _ _ _ _
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"


def next (s: MachineState): MachineState := { s with rip := s.rip + 1 }

-- Signed overflow detection for addition: true if result overflows Int64 range
def add_overflow (w: Width) (a b : UInt64) : Bool :=
  let sum := a.toIntWithWidth w + b.toIntWithWidth w
  sum >= 2^(w.toNat - 1) || sum < -2^(w.toNat - 1)

-- Addition with carry: dst + src + carry_in
-- Returns (result, zf, cf, of)
def add_with_carry (w: Width) (dst src : UInt64) (carry_in : Nat) : UInt64 × Bool × Bool × Bool :=
  let result := dst.toNat + src.toNat + carry_in
  let carry := result >>> w.toNat
  let result64 := UInt64.ofNat result
  let zf := result64 == 0
  let cf := carry != 0
  let of := add_overflow w dst src
  (result64, zf, cf, of)

-- Signed overflow detection for subtraction: true if result overflows Int64 range
def sub_overflow (w: Width) (a b : UInt64) : Bool :=
  let diff := a.toIntWithWidth w - b.toIntWithWidth w
  diff >= 2^(w.toNat - 1) || diff < -2^(w.toNat - 1)

-- Subtraction with borrow: dst - src - carry_in
-- Returns (result, zf, cf, of)
def sub_with_borrow (w: Width) (dst src : UInt64) (carry_in : Nat) : UInt64 × Bool × Bool × Bool :=
  let res := (Int.ofNat dst.toNat) - (Int.ofNat src.toNat) - carry_in
  let cf := res < 0
  let of := sub_overflow w dst src
  let result64 := UInt64.ofInt res
  let zf := result64 == 0
  (result64, zf, cf, of)

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
      eval_reg_or_mem s dst (fun dst_v w =>
      let (result64, zf, cf, of) := add_with_carry w dst_v src_v 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .adc dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v w =>
      let (result64, zf, cf, of) := add_with_carry w dst_v src_v s.flags.cf.toNat
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .adcx dst src =>
      -- Some thoughts: I basically try to assert the well-formedness of
      -- instructions (by asserting that e.g. immediate operands are not
      -- allowed, or that the x64 semantics demand that the destination of adcx
      -- be a general-purpose register... so that it at least simplifies the
      -- reasoning, but realistically, since we intend to consume source
      -- assembly (possibly with an actual frontend to parse .S syntax), the
      -- assembler will enforce eventually that no such nonsensical instructions
      -- exist. Is it worth the trouble?
      eval_reg_or_mem s src (fun src_v w =>
      eval_reg_or_mem s dst (fun dst_v _ =>
      let result := src_v.toNat + dst_v.toNat + s.flags.cf.toNat
      let carry := result >>> w.toNat
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with cf := carry != 0 }}
      set_reg s dst result ret))

  | .adox dst src =>
      eval_reg_or_mem s src (fun src_v w =>
      eval_reg_or_mem s dst (fun dst_v _ =>
      -- TODO: figure out how to make sure that this let-binding does not get
      -- inlined, *unless* the right-hand side can be computed to a constant
      let result := src_v.toNat + dst_v.toNat + s.flags.of.toNat
      let carry := result >>> w.toNat
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with of := carry != 0 }}
      set_reg s dst result ret))

  | .sub dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v w =>
      let (result64, zf, cf, of) := sub_with_borrow w dst_v src_v 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .sbb dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v w =>
      let (result64, zf, cf, _of) := sub_with_borrow w dst_v src_v s.flags.cf.toNat
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { s.flags with zf, cf }})))

  | .mul src =>
      -- mulq: rdx:rax = rax * src
      eval_reg_or_mem s src (fun src_v w =>
      let rax_v := s.getReg .rax
      let result := rax_v.toNat * src_v.toNat
      let lo := (UInt64.ofNat result) &&& w.toMask
      let hi := UInt64.ofNat (result >>> w.toNat)
      Reg.shrink .rax w (fun r_lo =>
      Reg.shrink .rdx w (fun r_hi =>
      let s := s.setReg r_lo lo
      let s := s.setReg r_hi hi
      -- mul sets OF and CF if high half is non-zero
      let cf := hi != 0
      let of := hi != 0
      ret { s with flags := { s.flags with cf, of }})))

  | .mulx r_hi r_lo src1 =>
      eval_reg_or_mem s src1 (fun src1_v w =>
      let src2_v := s.getReg .rdx
      let result := src1_v.toNat * src2_v.toNat
      let lo := (UInt64.ofNat result) &&& w.toMask
      let hi := UInt64.ofNat (result >>> w.toNat)
      -- Semantics say that if hi and lo are aliased, the value written is hi
      Reg.shrink r_lo w (fun r_lo =>
      Reg.shrink r_hi w (fun r_hi =>
      set_reg s r_lo lo (fun s  =>
      set_reg s r_hi hi ret))))

  | .imul r_dst src =>
      eval_reg_or_mem s src (fun src_v _ =>
      eval_reg_or_mem s (.reg r_dst) (fun dst_v w => -- instruction homogenous
      let result := dst_v.toIntWithWidth w * src_v.toIntWithWidth w
      let result64 := UInt64.ofInt result
      -- OF/CF set if result doesn't fit in 64 bits (TODO: is this the same as what the manual
      -- says?)
      let overflow := result >>> w.toNat != 0
      r_dst.shrink w (fun r_dst =>
      set_reg_or_mem s r_dst result64 (fun s =>
      ret { s with flags := { s.flags with cf := overflow, of := overflow }}))))

  | .neg dst =>
      eval_reg_or_mem s dst (fun dst_v _ =>
      let result := 0 - dst_v
      let zf := result == 0
      let cf := dst_v != 0  -- CF is set unless operand is 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf, cf }}))

  | .dec dst =>
      eval_reg_or_mem s dst (fun dst_v w =>
      let result := dst_v - 1
      let zf := result == 0
      let of := sub_overflow w dst_v 1
      -- dec does NOT affect CF
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf, of }}))

  | .lea dst src =>
      -- lea computes effective address, doesn't access memory
      -- see comment in effective_addr for zero-extension
      effective_addr s src (fun addr _ => ret (s.setReg dst addr))

  | .xor dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v _ =>
      let result := dst_v ^^^ src_v
      let zf := result == 0
      -- xor clears CF and OF
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .and dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v _ =>
      let result := dst_v &&& src_v
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .or dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v _ =>
      let result := dst_v ||| src_v
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .cmp a b =>
      eval_reg_or_mem s a (fun a_v w =>
      eval_operand s b (fun b_v =>
      let res := (Int.ofNat a_v.toNat) - (Int.ofNat b_v.toNat)
      let cf := res < 0
      let zf := res == 0
      let of := sub_overflow w a_v b_v
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

def Post := MachineState → Prop

def step1 (p: Program) (s: MachineState) (post: Post) :=
  eval1 (m:={ throw _ := False }) p s post

inductive eventually (prog: Program) (p: MachineState → Prop): MachineState -> Prop
  | done (initial: MachineState):
      p initial →
      eventually _ p initial
  | step (initial: MachineState):
      (mid_p: Post) ->
      step1 prog initial mid_p →
      (forall (mid: MachineState), mid_p mid → eventually _ p mid) →
      eventually _ p initial

theorem step_cps {p : Program} (post: Post) (initial: MachineState):
  step1 p initial (fun mid => eventually p post mid) → eventually p post initial :=
  by
    intro
    apply eventually.step
    <;> try assumption
    grind

theorem eventually_trans (program: Program) (p q: Post) (initial: MachineState)
  (e: eventually program p initial)
  (h: forall s, p s → eventually program q s):
    eventually program q initial
  := by
    induction e with
    | done =>
        grind
    | step initial mid_p step pred ind_h =>
        apply eventually.step
        <;> assumption -- Q: why does `grind` not work here?

theorem eventually_weaken (program: Program) (p q: Post)
  (h: forall s, p s → q s):
    eventually program p initial → eventually program q initial
  := by
    intro hp
    induction ih: hp -- Q: why does this not work with `induction ... with`?
    . apply eventually.done
      grind
    . apply eventually.step
      <;> try assumption
      grind

-- TEST

-- Example 1: single step of execution
def p1: Program := [
  (.none, .mov (Reg.rax) (.imm 1)),
]

-- OLD: doing things with a heavy-handed `simp`
example: step1 p1 {} (fun s => s.regs.rax = 1) := by
  simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next]
  simp [MachineState.setReg,Registers.set]

-- Example 2: fine-grained tactics to step through the goal without un-necessary
-- steps, and relying only on low-level tactics

-- STEP TACTIC: reduce a match
syntax "step_match" : tactic
macro_rules
  | `(tactic|step_match) =>
  `(tactic|
    -- JP: looks like reducing a match needs both beta and iota?
    -- the match in the goal below does not reduce properly if I remove beta := true
    dsimp (config := { beta := true, zeta := false, iota := true, proj := false, eta := false })
  )

def p11: Program := [
  (.none, .mov (.reg .rbx) (.imm 2)),    -- rbx := 2
  (.none, .adcx (.reg .rax) (.reg .rbx)) -- rax := rax + rbx
]

def sapply (lem : Name) (mvarId : MVarId) : SymM (List (MVarId)) := do
  let rule ← mkBackwardRuleFromDecl lem
  let .goals gs ← rule.apply mvarId | failure
  return gs

-- STEP TACTIC: one step of execution
syntax "step_cps" : tactic
macro_rules
  | `(tactic|step_cps) =>
  `(tactic|
    run_tac liftMetaTactic (λ g => SymM.run (sapply `step_cps g))
  )

-- STEP TACTIC: reduce the lookup of the next instruction
-- TODO: bail if the state's .rip is not a constant
syntax "step_instr" : tactic
macro_rules
  | `(tactic|step_instr) =>
  `(tactic|
    delta step1 eval1 fetch;
    dsimp only [List.findIdx?,List.findIdx,getElem?,List.get?Internal];
    dsimp only [Instr.is_ctrl];
    dsimp only [Bool.false_eq_true, ↓dreduceIte]; -- special simproc for if https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean#L25-L40
    delta next
  )

example (s_old: MachineState) (h_bound: (s_old.getReg .rax).toNat + 2 < 2^64):
    eventually p11 (fun s => (s.getReg .rax).toNat = (s_old.getReg .rax).toNat + 2) {s_old with rip := 0}
  := by
    delta p11
    -- First instruction
    step_cps
    step_instr

    delta strt1
    step_match
    delta eval_operand eval_imm
    step_match
    delta set_reg_or_mem
    step_match
    delta MachineState.setReg
    dsimp (config := { beta := false, zeta := false, iota := true, proj := true, eta := false })

    step_cps
    step_instr
    delta strt1
    step_match
    delta eval_reg_or_mem
    step_match
    dsimp (config := { beta := false, zeta := false, iota := true, proj := true, eta := false })
    -- NOTE: we still have nice let-bindings in the goal!
    delta MachineState.getReg Registers.get
    step_match
    -- JP: do we want rewrite rules here of the form:
    --   (s.setReg r1 v).getReg r1 == v
    --   (s.setReg r1 v).getReg r2 == s.getReg r2
    -- I also feel like there are too many helpers for getReg/setReg -- perhaps
    -- they need to be simplified.

    -- delta MachineState.setReg
    -- delta Registers.set
    -- dsimp (config := { beta := true, zeta := false, iota := false, proj := true, eta := false })
    sorry


def p2: Program := [
  (.some "start", .mov (.reg .rax) (.imm 1)),
  (.none,         .jz "start"),
  (.none,         .mov (.reg .rax) (.imm 2)),
]

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
      strt1,eval_operand,eval_reg_or_mem,set_reg,set_reg_or_mem,effective_addr,eval_imm,sub_with_borrow,add_with_carry,sub_overflow,add_overflow,MachineState.setReg,next,Registers.set,pure,bind,next,MachineState.getReg,Registers.get,
      -- or calls to ctrl
      ctrl,lookup,List.findIdx?,List.findIdx?.go,pure,bind,jump_if,next] <;> try native_decide)

-- Example 2: stepping through both straightline and control instructions
example: eventually p2 (fun s => s.regs.rax = 2) {} := by
  simp [p2]

  apply step_cps
  step_one

  apply step_cps
  step_one

  apply step_cps
  step_one

  apply eventually.done
  simp

-- A loop down to 0
theorem reg_dec_loop (prog: Program) (post: Post) (initial: MachineState) (invariant: Nat → Post) (n: Nat):
  -- if:
  -- invariant holds before entering the loop
  invariant n initial ∧
  -- final iteration allows proving `post`
  (forall state, invariant 0 state → eventually prog post state) ∧
  -- while iterating, we eventually re-establish the invariant
  (forall state k, k ≠ 0 → invariant k state → eventually prog (invariant (k - 1)) state) →
  -- then: we can prove the post
  eventually prog post initial
  := by
    intro misc
    rcases misc with ⟨ initial_invariant, case_zero, case_nonzero ⟩
    if n = 0 then
      apply case_zero
      grind
    else
      apply eventually_trans prog (invariant (n - 1)) post
      grind
      intros srec _
      apply reg_dec_loop prog post srec invariant (n - 1)
      grind

-- Example 3: a loop
def p3: Program := [
  -- (.none,         .mov (.reg .rbx) (.imm 4)),                -- rbx: loop counter = 4
  (.none,         .mov (.reg .rdx) (.imm 2)),                -- rdx: current result = 2
  (.some "start", .sub (.reg .rbx) (.imm 0)),                -- TEST: zf = (rbx == 0)
  (.none        , .jz "end"),                                  -- end loop if rbx == 0 (a.k.a. "while rbx >= 0")
  (.none        , .mulx .rax .rdx (.reg .rdx)),             -- BODY: rdx := rdx * rdx
  (.none,         .sub (.reg .rbx) (.imm 1)),                -- rbx -= 1
  (.none,         .jmp "start"),                               -- go back to test & loop body
  (.some "end",   .mov (.reg .rax) (.imm 0)),                -- meaningless -- just want the label to be well-defined
  -- result is 2^16, in rdx
]

-- Need to do something for when we have reached the end of the instruction list
-- maybe a special state! Right now this returns `none` because we eventually
-- hit the final instruction and then rip is out of bounds.
#eval (eval p3 {})

def p3_spec (s: MachineState): Nat := 2^(2^s.regs.rbx.toNat)

set_option maxHeartbeats 1000000 in
theorem p3_correct (initial: MachineState):
    p3_spec initial < 2^64 →
    initial.rip = 0 →
    eventually p3 (fun s => s.regs.rdx.toNat == p3_spec initial ∧ s.regs.rax == 0) initial :=
  by
    intros h_bounds h_rip
    simp [p3]
    -- First step sets rdx = 2
    apply step_cps
    step_one
    rw [h_rip]
    clear h_rip
    simp

    -- Loop invariant introduction
    apply reg_dec_loop p3 _ _ (fun i s => s.rip = 1 ∧ s.regs.rbx.toNat = i ∧ i ≤ initial.regs.rbx.toNat ∧ s.regs.rdx.toNat = 2^(2^(initial.regs.rbx.toNat - i))) initial.regs.rbx.toNat
    constructor
    . simp
    . constructor
      -- Invariant at index 0 ==> post
      . intros state inv
        rcases inv with ⟨ h_rip, h_rbx_zero, h_rbx_le, h_inv ⟩
        -- Step through a few program steps
        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp
        apply step_cps
        step_one
        have : state.regs.rbx.toNat = 0 := by grind
        simp [this]
        apply step_cps
        step_one
        apply eventually.done
        simp
        -- Now functional correctness for initial invariant
        simp [p3_spec]
        grind

      -- Invariant preserved
      . intro state k h_k_nonzero inv
        rcases inv with ⟨ h_rip, h_rbx_is_k, h_rbx_le, h_inv ⟩

        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp

        apply step_cps
        step_one
        have h_k_ne : k ≠ 0 := by grind
        -- state.regs.rbx.toNat = k and toNat < 2^64 for UInt64
        have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (state.regs.rbx.toNat_lt)
        -- Simplify all the Int64.toUInt64 terms
        simp_all only [ne_eq, not_false_eq_true]
        -- Prove the if-condition is false: UInt64.ofInt ↑k ≠ 0 when k ≠ 0
        have h_cond : UInt64.ofInt (k : Int) ≠ 0 := UInt64_ofInt_natCast_ne_zero k h_k_lt h_k_ne
        rw [if_neg h_cond]




        apply step_cps
        step_one
        simp [Reg.width,Reg.shrink] 
        apply step_cps
        step_one
        apply step_cps
        step_one
        apply eventually.done

        -- Goals for invariant preservation
        constructor
        . simp -- back to correct address
        . match h_state:state.regs.rbx, h_init:initial.regs.rbx with
          | ⟨v_s⟩, ⟨v_i⟩ =>
            have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (by rw [h_state]; exact v_s.isLt)
            have h_init_lt : v_i.toNat < 2^64 := v_i.isLt
            simp [h_state, h_init, p3_spec, Width.toMask, mask64, UInt64.ofInt, UInt64.ofNat, UInt64.toNat_ofNat] at *
            constructor
            . omega
            . constructor
              . omega
              . rw [h_inv]
                have h_vi_k : v_i.toNat - (k - 1) = (v_i.toNat - k) + 1 := by omega
                rw [h_vi_k, Nat.mod_eq_of_lt]
                . rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                . apply Nat.lt_of_le_of_lt _ h_bounds
                  rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                  apply Nat.pow_le_pow_right (by decide)
                  apply Nat.pow_le_pow_right (by decide)
                  omega


