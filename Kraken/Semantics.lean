/-
Kraken - x86_64 Assembly Interpreter Semantics

Core semantics for the assembly interpreter.
Compatible with Lean 4.22.0+.

For theorems, see Kraken/Theorems.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Std
import Lean.Elab.Tactic.Grind

-- ============================================================================
-- Width Type
-- ============================================================================

/-- Operand width for multi-width instructions. -/
inductive Width | W8 | W16 | W32 | W64
  deriving Repr, BEq, DecidableEq

def Width.toNat : Width → Nat
  | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64

/-- Mask for extracting the low bits of the specified width. -/
def Width.toMask : Width → UInt64
  | W8  => 0xFF
  | W16 => 0xFFFF
  | W32 => 0xFFFFFFFF
  | W64 => 0xFFFFFFFFFFFFFFFF

-- ============================================================================
-- Registers Enumeration (extended with aliases)
-- ============================================================================

/-- x86-64 registers including aliased sub-registers.
    - 64-bit: rax, rbx, ..., r15
    - 32-bit: eax, ebx, ..., r15d (zero-extend on write per Intel SDM)
    - 16-bit: ax, bx, ..., r15w (preserve upper bits on write)
    - 8-bit low: al, bl, ..., r15b (preserve upper bits on write)
 -/
inductive Reg
  -- 64-bit registers
  | rax | rbx | rcx | rdx
  | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  -- 32-bit aliases (zero-extend to 64-bit on write)
  | eax | ebx | ecx | edx
  | esi | edi | esp | ebp
  | r8d | r9d | r10d | r11d
  | r12d | r13d | r14d | r15d
  -- 16-bit aliases (preserve upper 48 bits on write)
  | ax | bx | cx | dx
  | si | di | sp | bp
  | r8w | r9w | r10w | r11w
  | r12w | r13w | r14w | r15w
  -- 8-bit low aliases (preserve upper 56 bits on write)
  | al | bl | cl | dl
  | sil | dil | spl | bpl
  | r8b | r9b | r10b | r11b
  | r12b | r13b | r14b | r15b
  deriving Repr, BEq, DecidableEq

/-- Get the width of a register. -/
@[simp] def Reg.width : Reg → Width
  | rax | rbx | rcx | rdx | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15 => .W64
  | eax | ebx | ecx | edx | esi | edi | esp | ebp
  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d => .W32
  | ax | bx | cx | dx | si | di | sp | bp
  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w => .W16
  | al | bl | cl | dl | sil | dil | spl | bpl
  | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b => .W8

/-- Get the 64-bit base register for any alias. -/
@[simp] def Reg.base : Reg → Reg
  | rax | eax | ax | al => .rax | rbx | ebx | bx | bl => .rbx
  | rcx | ecx | cx | cl => .rcx | rdx | edx | dx | dl => .rdx
  | rsi | esi | si | sil => .rsi | rdi | edi | di | dil => .rdi
  | rsp | esp | sp | spl => .rsp | rbp | ebp | bp | bpl => .rbp
  | r8  | r8d  | r8w  | r8b  => .r8  | r9  | r9d  | r9w  | r9b  => .r9
  | r10 | r10d | r10w | r10b => .r10 | r11 | r11d | r11w | r11b => .r11
  | r12 | r12d | r12w | r12b => .r12 | r13 | r13d | r13w | r13b => .r13
  | r14 | r14d | r14w | r14b => .r14 | r15 | r15d | r15w | r15b => .r15

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

-- Condition codes for conditional jumps
inductive CondCode
| z    -- Zero (ZF=1)
| nz   -- Not Zero (ZF=0)
| b    -- Below/Carry (CF=1)
| ae   -- Above or Equal (CF=0)
| a    -- Above (CF=0 ∧ ZF=0)
| be   -- Below or Equal (CF=1 ∨ ZF=1)
deriving Repr, BEq, DecidableEq

-- Instructions (extended for scalar crypto benchmarks)
inductive Instr
  -- Arithmetic (64-bit)
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

  -- Arithmetic (32-bit, zero-extend results)
  | addl (dst src : Operand)                   -- addl: 32-bit add, zero-extends
  | subl (dst src : Operand)                   -- subl: 32-bit subtract, zero-extends
  | negl (dst : Operand)                       -- negl: 32-bit negate, zero-extends
  | notl (dst : Operand)                       -- notl: 32-bit bitwise NOT, zero-extends
  | decl (dst : Operand)                       -- decl: 32-bit decrement, zero-extends

  -- Move/Load
  | mov   (dst src : Operand)                  -- movq/movabs: 64-bit move
  | movl  (dst src : Operand)                  -- movl: 32-bit move, zero-extends to 64-bit
  | movw  (dst src : Operand)                  -- movw: 16-bit move, preserves upper bits
  | movzbl (dst src : Operand)                 -- movzbl: byte to 32-bit zero-extend (then to 64)
  | movzwl (dst src : Operand)                 -- movzwl: word to 32-bit zero-extend
  | movzbq (dst src : Operand)                 -- movzbq: byte to 64-bit zero-extend
  | lea   (dst : Reg) (src : Operand)          -- leaq: dst = effective address
  | leal  (dst : Reg) (src : Operand)          -- leal: 32-bit lea, zero-extends

  -- Shifts (64-bit)
  | shl  (dst count : Operand)                 -- shlq: logical shift left
  | shr  (dst count : Operand)                 -- shrq: logical shift right
  | sar  (dst count : Operand)                 -- sarq: arithmetic shift right
  | shld (dst src count : Operand)             -- shldq: double-precision shift left
  | shrd (dst src count : Operand)             -- shrdq: double-precision shift right

  -- Shifts (32-bit, zero-extend results)
  | shll (dst count : Operand)                 -- shll: 32-bit shift left
  | shrl (dst count : Operand)                 -- shrl: 32-bit shift right

  -- Rotates (64-bit)
  | rol  (dst count : Operand)                 -- rolq: rotate left
  | ror  (dst count : Operand)                 -- rorq: rotate right

  -- Rotates (32-bit, zero-extend results)
  | roll (dst count : Operand)                 -- roll: 32-bit rotate left
  | rorl (dst count : Operand)                 -- rorl: 32-bit rotate right

  -- Byte swap
  | bswap  (dst : Operand)                     -- bswapq: 64-bit byte swap
  | bswapl (dst : Operand)                     -- bswapl: 32-bit byte swap

  -- Bitwise (64-bit)
  | xor  (dst src : Operand)                   -- xorq: dst ^= src, clears CF/OF, sets ZF
  | and  (dst src : Operand)                   -- andq: dst &= src, clears CF/OF, sets ZF
  | or   (dst src : Operand)                   -- orq: dst |= src, clears CF/OF, sets ZF

  -- Bitwise (32-bit, zero-extend results)
  | xorl (dst src : Operand)                   -- xorl: 32-bit XOR
  | andl (dst src : Operand)                   -- andl: 32-bit AND
  | orl  (dst src : Operand)                   -- orl: 32-bit OR

  -- Test (AND but discard result, set flags)
  | test (a b : Operand)                       -- testq: a AND b, set flags
  | testb (a b : Operand)                      -- testb: 8-bit test

  -- Compare (sets flags only)
  | cmp  (a b : Operand)                       -- cmpq: compute a - b, set flags
  | cmpl (a b : Operand)                       -- cmpl: 32-bit compare
  | cmpb (a b : Operand)                       -- cmpb: byte compare

  -- Stack operations
  | push (src : Operand)                       -- pushq: RSP -= 8, [RSP] = src
  | pop  (dst : Operand)                       -- popq: dst = [RSP], RSP += 8

  -- Set byte on condition
  | setc  (dst : Operand)                      -- setc/setb: set byte to 1 if CF=1, else 0
  | setnc (dst : Operand)                      -- setnc/setae: set byte to 1 if CF=0, else 0

  -- Conditional move (64-bit)
  | cmovc (dst src : Operand)                  -- cmovcq: move if CF=1
  | cmove (dst src : Operand)                  -- cmoveq: move if ZF=1

  -- Control flow
  | jmp (target : Label)                       -- Unconditional jump
  | ret                                        -- Return from function
  -- Conditional jump: jcc (condition code, target)
  -- Mapping from AT&T syntax to CondCode:
  --   AT&T    CondCode   Condition          Flags tested
  --   ----    --------   ---------          ------------
  --   jz      .z         Zero               ZF=1
  --   jnz     .nz        Not Zero           ZF=0
  --   je      .z         Equal (alias)      ZF=1
  --   jne     .nz        Not Equal (alias)  ZF=0
  --   jb      .b         Below (unsigned)   CF=1
  --   jc      .b         Carry (alias)      CF=1
  --   jnc     .ae        Not Carry (alias)  CF=0
  --   jae     .ae        Above/Equal        CF=0
  --   ja      .a         Above (unsigned)   CF=0 ∧ ZF=0
  --   jbe     .be        Below/Equal        CF=1 ∨ ZF=1
  | jcc (cc : CondCode) (target : Label)

  -- No operation (x86 NOP instruction)
  -- Per Intel SDM: performs no operation. Used for padding or as placeholder.
  | nop
  deriving Repr

def Instr.is_ctrl
  | Instr.jmp _ | Instr.jcc _ _ | Instr.ret => true
  | _ => false

-- ============================================================================
-- Register Access
-- ============================================================================

/-- Read low 8 bits. -/
@[simp] def mask8 (x : UInt64) : UInt64 := x &&& 0xFF

/-- Read low 16 bits. -/
@[simp] def mask16 (x : UInt64) : UInt64 := x &&& 0xFFFF

/-- Read low 32 bits. -/
@[simp] def mask32 (x : UInt64) : UInt64 := x &&& 0xFFFFFFFF

/-- Write to low 8 bits, preserving upper 56. -/
@[inline] def write8 (dst src : UInt64) : UInt64 :=
  (dst &&& 0xFFFFFFFFFFFFFF00) ||| mask8 src

/-- Write to low 16 bits, preserving upper 48. -/
@[inline] def write16 (dst src : UInt64) : UInt64 :=
  (dst &&& 0xFFFFFFFFFFFF0000) ||| mask16 src

/-- Get the raw 64-bit value for a base register (internal use). -/
@[simp] def Registers.getRaw (regs : Registers) (r : Reg) : UInt64 :=
  match r.base with
  | .rax => regs.rax | .rbx => regs.rbx | .rcx => regs.rcx | .rdx => regs.rdx
  | .rsi => regs.rsi | .rdi => regs.rdi | .rsp => regs.rsp | .rbp => regs.rbp
  | .r8  => regs.r8  | .r9  => regs.r9  | .r10 => regs.r10 | .r11 => regs.r11
  | .r12 => regs.r12 | .r13 => regs.r13 | .r14 => regs.r14 | .r15 => regs.r15
  | _ => 0  -- Unreachable for base registers

/-- Set the raw 64-bit value for a base register (internal use). -/
@[simp] def Registers.setRaw (regs : Registers) (r : Reg) (v : UInt64) : Registers :=
  match r.base with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }
  | _ => regs  -- Unreachable for base registers

/-- Get a register value with appropriate masking for aliased registers.
    Returns the value as seen through the register's width. -/
def Registers.get (regs : Registers) (r : Reg) : UInt64 :=
  match r with
  -- 64-bit registers: direct read
  | .rax => regs.rax | .rbx => regs.rbx | .rcx => regs.rcx | .rdx => regs.rdx
  | .rsi => regs.rsi | .rdi => regs.rdi | .rsp => regs.rsp | .rbp => regs.rbp
  | .r8  => regs.r8  | .r9  => regs.r9  | .r10 => regs.r10 | .r11 => regs.r11
  | .r12 => regs.r12 | .r13 => regs.r13 | .r14 => regs.r14 | .r15 => regs.r15
  -- 32-bit: mask to 32 bits
  | .eax => mask32 regs.rax | .ebx => mask32 regs.rbx
  | .ecx => mask32 regs.rcx | .edx => mask32 regs.rdx
  | .esi => mask32 regs.rsi | .edi => mask32 regs.rdi
  | .esp => mask32 regs.rsp | .ebp => mask32 regs.rbp
  | .r8d  => mask32 regs.r8  | .r9d  => mask32 regs.r9
  | .r10d => mask32 regs.r10 | .r11d => mask32 regs.r11
  | .r12d => mask32 regs.r12 | .r13d => mask32 regs.r13
  | .r14d => mask32 regs.r14 | .r15d => mask32 regs.r15
  -- 16-bit: mask to 16 bits
  | .ax => mask16 regs.rax | .bx => mask16 regs.rbx
  | .cx => mask16 regs.rcx | .dx => mask16 regs.rdx
  | .si => mask16 regs.rsi | .di => mask16 regs.rdi
  | .sp => mask16 regs.rsp | .bp => mask16 regs.rbp
  | .r8w  => mask16 regs.r8  | .r9w  => mask16 regs.r9
  | .r10w => mask16 regs.r10 | .r11w => mask16 regs.r11
  | .r12w => mask16 regs.r12 | .r13w => mask16 regs.r13
  | .r14w => mask16 regs.r14 | .r15w => mask16 regs.r15
  -- 8-bit: mask to 8 bits
  | .al => mask8 regs.rax | .bl => mask8 regs.rbx
  | .cl => mask8 regs.rcx | .dl => mask8 regs.rdx
  | .sil => mask8 regs.rsi | .dil => mask8 regs.rdi
  | .spl => mask8 regs.rsp | .bpl => mask8 regs.rbp
  | .r8b  => mask8 regs.r8  | .r9b  => mask8 regs.r9
  | .r10b => mask8 regs.r10 | .r11b => mask8 regs.r11
  | .r12b => mask8 regs.r12 | .r13b => mask8 regs.r13
  | .r14b => mask8 regs.r14 | .r15b => mask8 regs.r15

/-- Set a register value with appropriate aliasing behavior:
    - 64-bit: direct write
    - 32-bit: zero-extends to 64-bit (clears upper 32 bits) per Intel SDM
    - 16-bit: preserves upper 48 bits
    - 8-bit: preserves upper 56 bits -/
def Registers.set (regs : Registers) (r : Reg) (v : UInt64) : Registers :=
  match r with
  -- 64-bit registers: direct write
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }
  -- 32-bit: zero-extend
  | .eax => { regs with rax := mask32 v } | .ebx => { regs with rbx := mask32 v }
  | .ecx => { regs with rcx := mask32 v } | .edx => { regs with rdx := mask32 v }
  | .esi => { regs with rsi := mask32 v } | .edi => { regs with rdi := mask32 v }
  | .esp => { regs with rsp := mask32 v } | .ebp => { regs with rbp := mask32 v }
  | .r8d  => { regs with r8  := mask32 v } | .r9d  => { regs with r9  := mask32 v }
  | .r10d => { regs with r10 := mask32 v } | .r11d => { regs with r11 := mask32 v }
  | .r12d => { regs with r12 := mask32 v } | .r13d => { regs with r13 := mask32 v }
  | .r14d => { regs with r14 := mask32 v } | .r15d => { regs with r15 := mask32 v }
  -- 16-bit: preserve upper bits
  | .ax => { regs with rax := write16 regs.rax v } | .bx => { regs with rbx := write16 regs.rbx v }
  | .cx => { regs with rcx := write16 regs.rcx v } | .dx => { regs with rdx := write16 regs.rdx v }
  | .si => { regs with rsi := write16 regs.rsi v } | .di => { regs with rdi := write16 regs.rdi v }
  | .sp => { regs with rsp := write16 regs.rsp v } | .bp => { regs with rbp := write16 regs.rbp v }
  | .r8w  => { regs with r8  := write16 regs.r8 v }  | .r9w  => { regs with r9  := write16 regs.r9 v }
  | .r10w => { regs with r10 := write16 regs.r10 v } | .r11w => { regs with r11 := write16 regs.r11 v }
  | .r12w => { regs with r12 := write16 regs.r12 v } | .r13w => { regs with r13 := write16 regs.r13 v }
  | .r14w => { regs with r14 := write16 regs.r14 v } | .r15w => { regs with r15 := write16 regs.r15 v }
  -- 8-bit: preserve upper bits
  | .al => { regs with rax := write8 regs.rax v } | .bl => { regs with rbx := write8 regs.rbx v }
  | .cl => { regs with rcx := write8 regs.rcx v } | .dl => { regs with rdx := write8 regs.rdx v }
  | .sil => { regs with rsi := write8 regs.rsi v } | .dil => { regs with rdi := write8 regs.rdi v }
  | .spl => { regs with rsp := write8 regs.rsp v } | .bpl => { regs with rbp := write8 regs.rbp v }
  | .r8b  => { regs with r8  := write8 regs.r8 v }  | .r9b  => { regs with r9  := write8 regs.r9 v }
  | .r10b => { regs with r10 := write8 regs.r10 v } | .r11b => { regs with r11 := write8 regs.r11 v }
  | .r12b => { regs with r12 := write8 regs.r12 v } | .r13b => { regs with r13 := write8 regs.r13 v }
  | .r14b => { regs with r14 := write8 regs.r14 v } | .r15b => { regs with r15 := write8 regs.r15 v }

def MachineState.getReg (s : MachineState) (r : Reg) : UInt64 :=
  s.regs.get r

def MachineState.setReg (s : MachineState) (r : Reg) (v : UInt64) : MachineState :=
  { s with regs := s.regs.set r v }

class Throw (α : Type _) where
  throw: String → α

def throw {α} [inst: Throw α] :=
  inst.throw

def MachineState.readMem {α} [Throw α] (s : MachineState) (addr : Address) (ret: Word → α): α :=
  if addr % 8 != 0 then
    throw (s!"Out-of-bounds access (rip={repr s.rip})")
  else
    match s.heap[addr]? with
    | .some v => ret v
    | .none => throw (s!"Memory read but not written to (rip={repr s.rip}, addr={repr addr})")

def MachineState.writeMem {α} [Throw α] (s : MachineState) (addr : Address) (val : Word) (ret: MachineState → α) : α :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    ret { s with heap := s.heap.insert addr val }

-- Sign-extension helpers: use standard integer type conversions
-- Strategy: truncate to input size → signed Int conversion → convert to UInt64
-- This avoids branching on sign bit and is more proof-friendly.

-- 8-bit sign extension: UInt64 → UInt8 → Int8 → Int → UInt64
@[simp] def sign_extend_8_to_64 (v : UInt64) : UInt64 :=
  let truncated : UInt8 := v.toUInt8
  let signed : Int := truncated.toInt8.toInt
  UInt64.ofInt signed

-- 16-bit sign extension: UInt64 → UInt16 → Int16 → Int → UInt64
@[simp] def sign_extend_16_to_64 (v : UInt64) : UInt64 :=
  let truncated : UInt16 := v.toUInt16
  let signed : Int := truncated.toInt16.toInt
  UInt64.ofInt signed

-- 32-bit sign extension: UInt64 → UInt32 → Int32 → Int → UInt64
@[simp] def sign_extend_32_to_64 (v : UInt64) : UInt64 :=
  let truncated : UInt32 := v.toUInt32
  let signed : Int := truncated.toInt32.toInt
  UInt64.ofInt signed

-- Zero-extension helpers: truncate to input size, then widen (unsigned)
-- Upper bits are implicitly zero when converting smaller unsigned to larger

@[simp] def zero_extend_8_to_64 (v : UInt64) : UInt64 := v.toUInt8.toUInt64
@[simp] def zero_extend_16_to_64 (v : UInt64) : UInt64 := v.toUInt16.toUInt64
@[simp] def zero_extend_32_to_64 (v : UInt64) : UInt64 := v.toUInt32.toUInt64

-- Partial register write helpers: merge new value into existing register
-- These preserve upper bits of dst and write lower bits from src
@[simp] def write_low_8 (dst src : UInt64) : UInt64 := (dst &&& 0xFFFFFFFFFFFFFF00) ||| zero_extend_8_to_64 src
@[simp] def write_low_16 (dst src : UInt64) : UInt64 := (dst &&& 0xFFFFFFFFFFFF0000) ||| zero_extend_16_to_64 src
-- movl zero-extends, so it's just zero_extend_32_to_64 (no preservation)

-- Convert Int64 immediate to UInt64
@[simp] def eval_imm (v : Int64) : UInt64 := v.toUInt64




-- Compute effective address: base + idx*scale + disp
def effective_addr {α} [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .mem base idx scale disp =>
    let idxVal := match idx with | .some r => s.getReg r | .none => 0
    ret ((s.getReg base) + idxVal * scale.toUInt64 + UInt64.ofInt disp)
  | _ => throw "effective_addr called on non-memory operand"

def eval_operand {α} [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .imm v => ret (eval_imm v)
  | .mem _ _ _ _ => effective_addr s o (fun addr => s.readMem addr ret)

def eval_reg_or_mem {α} [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .mem _ _ _ _ => effective_addr s o (fun addr => s.readMem addr ret)
  | .imm _ => throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg_or_mem {α} [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _ _ _ _ =>
      effective_addr s o (fun addr => s.writeMem addr v ret)
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg {α} [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _ _ _ _
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"


def next (s: MachineState): MachineState := { s with rip := s.rip + 1 }

-- Signed overflow detection for addition with carry: compare unbounded Int sum to truncated Int64 result
-- Overflow occurs iff the unbounded sum differs from the signed interpretation of the truncated result
-- Per Intel SDM, OF reflects the full operation including carry-in
def add_overflow_with_carry (a b : UInt64) (carry_in : Nat) : Bool :=
  let unbounded := a.toInt64.toInt + b.toInt64.toInt + carry_in
  let result := UInt64.ofNat (a.toNat + b.toNat + carry_in)
  let truncated := result.toInt64.toInt
  unbounded != truncated

-- Addition with carry: dst + src + carry_in
-- Returns (result, zf, cf, of)
def add_with_carry (dst src : UInt64) (carry_in : Nat) : UInt64 × Bool × Bool × Bool :=
  let unbounded := dst.toNat + src.toNat + carry_in
  let result64 := UInt64.ofNat unbounded
  let zf := result64 == 0
  let cf := unbounded >= 2^64  -- Carry if result doesn't fit in 64 bits
  let of := add_overflow_with_carry dst src carry_in
  (result64, zf, cf, of)

-- Signed overflow detection for subtraction with borrow: compare unbounded Int diff to truncated Int64 result
-- Per Intel SDM, OF reflects the full operation including borrow-in
def sub_overflow_with_borrow (a b : UInt64) (borrow_in : Nat) : Bool :=
  let unbounded := a.toInt64.toInt - b.toInt64.toInt - borrow_in
  let result := UInt64.ofInt (a.toNat - b.toNat - borrow_in)
  let truncated := result.toInt64.toInt
  unbounded != truncated

-- Subtraction with borrow: dst - src - carry_in
-- Returns (result, zf, cf, of)
def sub_with_borrow (dst src : UInt64) (carry_in : Nat) : UInt64 × Bool × Bool × Bool :=
  -- Use Int to handle negative results correctly (Nat subtraction saturates to 0)
  let unbounded : Int := dst.toNat - src.toNat - carry_in
  let result64 := UInt64.ofInt unbounded
  let zf := result64 == 0
  let cf := src.toNat + carry_in > dst.toNat  -- Borrow if src+carry > dst (unsigned)
  let of := sub_overflow_with_borrow dst src carry_in
  (result64, zf, cf, of)

-- Backward-compatible aliases (used in step_one tactic simp set and CMP instruction)
def add_overflow (a b : UInt64) : Bool := add_overflow_with_carry a b 0
def sub_overflow (a b : UInt64) : Bool := sub_overflow_with_borrow a b 0

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def strt1 {α} [Throw α] (s : MachineState) (i : Instr) (ret: MachineState → α): α :=
  match i with
  | .mov dst src =>
      -- 64-bit move (movq/movabs): direct copy of evaluated value
      -- For immediates, Int64.toUInt64 already gives the correct 64-bit value
      eval_operand s src (fun val =>
      set_reg_or_mem s dst val ret)

  | .movl dst src =>
      -- 32-bit move: ZERO-extends to 64-bit (clears upper 32 bits)
      eval_operand s src (fun val =>
      set_reg_or_mem s dst (zero_extend_32_to_64 val) ret)

  | .add dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let (result64, zf, cf, of) := add_with_carry dst_v src_v 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .adc dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let (result64, zf, cf, of) := add_with_carry dst_v src_v s.flags.cf.toNat
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
      let (result64, zf, cf, of) := sub_with_borrow dst_v src_v 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .sbb dst src =>
      -- Per Intel SDM: OF, SF, ZF, AF, PF, and CF flags are set according to the result
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let (result64, zf, cf, of) := sub_with_borrow dst_v src_v s.flags.cf.toNat
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .mul src =>
      -- mulq (64-bit only): RDX:RAX = RAX * src
      -- Note: Other widths (mulb/mulw/mull) would need separate instruction variants
      -- since they read from AL/AX/EAX and write to AX/DX:AX/EDX:EAX respectively.
      -- The parser validates that operands are 64-bit. See: https://www.felixcloutier.com/x86/mul
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
      -- imulq (64-bit only): Two-operand form DEST := truncate(DEST × SRC) (signed)
      -- SRC can be immediate, register, or memory. DEST is register/memory (treated as source too)
      -- Note: Other widths (imulb/imulw/imull) would need different truncation/sign-extension.
      -- See: https://www.felixcloutier.com/x86/imul
      -- OF/CF set when signed result doesn't fit in destination size
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v.toInt64.toInt * src_v.toInt64.toInt
      let result64 := UInt64.ofInt result
      -- OF/CF set if sign-extended truncated result differs from full result
      let signExtended := result64.toInt64.toInt
      let overflow := result != signExtended
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { s.flags with cf := overflow, of := overflow }})))

  | .neg dst =>
      -- Per Intel SDM: CF set unless operand is 0; OF set according to result
      -- OF is set when negating the most negative value (INT64_MIN)
      eval_reg_or_mem s dst (fun dst_v =>
      -- Two's complement negation: negate via Int64 to ensure correct wrapping
      let result := (-(dst_v.toInt64)).toUInt64
      let zf := result == 0
      let cf := dst_v != 0  -- CF is set unless operand is 0
      let of := dst_v == 0x8000000000000000  -- OF set when negating INT64_MIN
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf, cf, of }}))

  | .dec dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v - 1
      let zf := result == 0
      -- Signed overflow occurs when decrementing INT64_MIN (produces positive result)
      let of := dst_v == 0x8000000000000000
      -- dec does NOT affect CF
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf, of }}))

  | .lea dst src =>
      -- lea computes effective address, doesn't access memory
      effective_addr s src (fun addr => ret (s.setReg dst addr))

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
      let of := sub_overflow a_v b_v
      ret { s with flags := { zf, of, cf }}))

  -- ============================================================================
  -- 32-bit arithmetic operations (zero-extend results to 64-bit)
  -- ============================================================================

  | .addl dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let src32 := mask32 src_v
      let dst32 := mask32 dst_v
      let result := dst32.toNat + src32.toNat
      let result32 := UInt64.ofNat (result % (2^32))
      let zf := result32 == 0
      let cf := result >= 2^32
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { zf, cf, of := false }})))

  | .subl dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let src32 := mask32 src_v
      let dst32 := mask32 dst_v
      let result := (dst32.toNat : Int) - (src32.toNat : Int)
      let result32 := UInt64.ofNat ((result.toNat) % (2^32))
      let zf := result32 == 0
      let cf := result < 0
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { zf, cf, of := false }})))

  | .negl dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let dst32 := mask32 dst_v
      let result32 := UInt64.ofNat ((2^32 - dst32.toNat) % (2^32))
      let zf := result32 == 0
      let cf := dst32 != 0
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { zf, cf, of := false }}))

  | .notl dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result32 := mask32 (~~~dst_v)
      set_reg_or_mem s dst result32 ret)

  | .decl dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let dst32 := mask32 dst_v
      let result32 := UInt64.ofNat ((dst32.toNat + 2^32 - 1) % (2^32))
      let zf := result32 == 0
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { s.flags with zf }}))

  -- ============================================================================
  -- Move/Load variants
  -- ============================================================================

  | .movw dst src =>
      -- 16-bit move, preserves upper bits (handled by Registers.set for 16-bit regs)
      eval_operand s src (fun val =>
      set_reg_or_mem s dst (mask16 val) ret)

  | .movzbl dst src =>
      -- Zero-extend byte to 32-bit (then to 64-bit per x86-64 convention)
      eval_operand s src (fun val =>
      set_reg_or_mem s dst (mask8 val) ret)

  | .movzwl dst src =>
      -- Zero-extend word to 32-bit (then to 64-bit)
      eval_operand s src (fun val =>
      set_reg_or_mem s dst (mask16 val) ret)

  | .movzbq dst src =>
      -- Zero-extend byte to 64-bit
      eval_operand s src (fun val =>
      set_reg_or_mem s dst (mask8 val) ret)

  | .leal dst src =>
      -- 32-bit lea, zero-extends result
      effective_addr s src (fun addr =>
      ret (s.setReg dst (mask32 addr)))

  -- ============================================================================
  -- Shift instructions
  -- ============================================================================

  | .shl dst count =>
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 64  -- x86 masks shift count
      let result := dst_v <<< cnt_masked.toUInt64
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf }})))

  | .shr dst count =>
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 64
      let result := dst_v >>> cnt_masked.toUInt64
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf }})))

  | .sar dst count =>
      -- Arithmetic right shift (sign-extending)
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 64
      let result := UInt64.ofInt (dst_v.toInt64.toInt >>> cnt_masked)
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf }})))

  | .shll dst count =>
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 32
      let result32 := mask32 (dst_v <<< cnt_masked.toUInt64)
      let zf := result32 == 0
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { s.flags with zf }})))

  | .shrl dst count =>
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 32
      let result32 := mask32 (mask32 dst_v >>> cnt_masked.toUInt64)
      let zf := result32 == 0
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { s.flags with zf }})))

  | .shld dst src count =>
      -- Double-precision shift left: shift dst left by count, fill low bits from src high bits
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 64
      let result := if cnt_masked == 0 then dst_v
                    else (dst_v <<< cnt_masked.toUInt64) ||| (src_v >>> (64 - cnt_masked).toUInt64)
      set_reg_or_mem s dst result ret)))

  | .shrd dst src count =>
      -- Double-precision shift right: shift dst right by count, fill high bits from src low bits
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 64
      let result := if cnt_masked == 0 then dst_v
                    else (dst_v >>> cnt_masked.toUInt64) ||| (src_v <<< (64 - cnt_masked).toUInt64)
      set_reg_or_mem s dst result ret)))

  -- ============================================================================
  -- Rotate instructions
  -- ============================================================================

  | .rol dst count =>
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 64
      let result := (dst_v <<< cnt_masked.toUInt64) ||| (dst_v >>> (64 - cnt_masked).toUInt64)
      -- Per Intel SDM: CF = bit 0 of result (the bit that rotated from MSB to LSB)
      let cf := (result &&& 1) != 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with cf }})))

  | .ror dst count =>
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let cnt_masked := cnt.toNat % 64
      let result := (dst_v >>> cnt_masked.toUInt64) ||| (dst_v <<< (64 - cnt_masked).toUInt64)
      -- Per Intel SDM: CF = MSB of result (the bit that rotated from LSB to MSB)
      let cf := (result >>> 63) != 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with cf }})))

  | .roll dst count =>
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let dst32 := mask32 dst_v
      let cnt_masked := cnt.toNat % 32
      let result32 := mask32 ((dst32 <<< cnt_masked.toUInt64) ||| (dst32 >>> (32 - cnt_masked).toUInt64))
      set_reg_or_mem s dst result32 ret))

  | .rorl dst count =>
      eval_operand s count (fun cnt =>
      eval_reg_or_mem s dst (fun dst_v =>
      let dst32 := mask32 dst_v
      let cnt_masked := cnt.toNat % 32
      let result32 := mask32 ((dst32 >>> cnt_masked.toUInt64) ||| (dst32 <<< (32 - cnt_masked).toUInt64))
      set_reg_or_mem s dst result32 ret))

  -- ============================================================================
  -- Byte swap
  -- ============================================================================

  | .bswap dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let b0 := (dst_v >>> 0)  &&& 0xFF
      let b1 := (dst_v >>> 8)  &&& 0xFF
      let b2 := (dst_v >>> 16) &&& 0xFF
      let b3 := (dst_v >>> 24) &&& 0xFF
      let b4 := (dst_v >>> 32) &&& 0xFF
      let b5 := (dst_v >>> 40) &&& 0xFF
      let b6 := (dst_v >>> 48) &&& 0xFF
      let b7 := (dst_v >>> 56) &&& 0xFF
      let result := (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
                    (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7
      set_reg_or_mem s dst result ret)

  | .bswapl dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let b0 := (dst_v >>> 0)  &&& 0xFF
      let b1 := (dst_v >>> 8)  &&& 0xFF
      let b2 := (dst_v >>> 16) &&& 0xFF
      let b3 := (dst_v >>> 24) &&& 0xFF
      let result32 := (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3
      set_reg_or_mem s dst result32 ret)

  -- ============================================================================
  -- 32-bit bitwise operations
  -- ============================================================================

  | .xorl dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result32 := mask32 (dst_v ^^^ src_v)
      let zf := result32 == 0
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .andl dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result32 := mask32 (dst_v &&& src_v)
      let zf := result32 == 0
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .orl dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result32 := mask32 (dst_v ||| src_v)
      let zf := result32 == 0
      set_reg_or_mem s dst result32 (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  -- ============================================================================
  -- Test and compare variants
  -- ============================================================================

  | .test a b =>
      eval_reg_or_mem s a (fun a_v =>
      eval_operand s b (fun b_v =>
      let result := a_v &&& b_v
      let zf := result == 0
      ret { s with flags := { zf, of := false, cf := false }}))

  | .testb a b =>
      -- 8-bit test: AND the low 8 bits, set flags
      eval_reg_or_mem s a (fun a_v =>
      eval_operand s b (fun b_v =>
      let a8 := mask8 a_v
      let b8 := mask8 b_v
      let result := a8 &&& b8
      let zf := result == 0
      ret { s with flags := { zf, of := false, cf := false }}))

  | .cmpl a b =>
      eval_reg_or_mem s a (fun a_v =>
      eval_operand s b (fun b_v =>
      let a32 := mask32 a_v
      let b32 := mask32 b_v
      let res := (Int.ofNat a32.toNat) - (Int.ofNat b32.toNat)
      let cf := res < 0
      let zf := res == 0
      ret { s with flags := { zf, cf, of := false }}))

  | .cmpb a b =>
      eval_reg_or_mem s a (fun a_v =>
      eval_operand s b (fun b_v =>
      let a8 := mask8 a_v
      let b8 := mask8 b_v
      let res := (Int.ofNat a8.toNat) - (Int.ofNat b8.toNat)
      let cf := res < 0
      let zf := res == 0
      ret { s with flags := { zf, cf, of := false }}))

  -- ============================================================================
  -- Set byte on condition
  -- ============================================================================

  | .setc dst =>
      -- Set byte to 1 if CF=1, else 0
      let val : UInt64 := if s.flags.cf then 1 else 0
      set_reg_or_mem s dst val ret

  | .setnc dst =>
      -- Set byte to 1 if CF=0, else 0
      let val : UInt64 := if !s.flags.cf then 1 else 0
      set_reg_or_mem s dst val ret

  -- ============================================================================
  -- Conditional moves
  -- ============================================================================

  | .cmovc dst src =>
      if s.flags.cf then
        eval_operand s src (fun src_v =>
        set_reg_or_mem s dst src_v ret)
      else ret s

  | .cmove dst src =>
      if s.flags.zf then
        eval_operand s src (fun src_v =>
        set_reg_or_mem s dst src_v ret)
      else ret s

  -- ============================================================================
  -- Stack operations and return
  -- ============================================================================

  | .push src =>
      eval_operand s src (fun val =>
      let newRsp := s.getReg .rsp - 8
      let s := s.setReg .rsp newRsp
      s.writeMem newRsp val (fun s => ret s))

  | .pop dst =>
      let rsp := s.getReg .rsp
      s.readMem rsp (fun val =>
      let s := s.setReg .rsp (rsp + 8)
      set_reg_or_mem s dst val ret)

  | .ret =>
      -- Pop return address from stack and jump to it
      let rsp := s.getReg .rsp
      s.readMem rsp (fun retAddr =>
      let s := s.setReg .rsp (rsp + 8)
      ret { s with rip := retAddr.toNat })

  | .nop =>
      -- NOP: No operation. Does nothing, just advances to next instruction.
      ret s

  | _ => throw s!"unsupported non-control instruction {repr i}"

def jump_if {α} [Throw α] (s: MachineState) (b: Bool) (rip: Nat) (ret: MachineState → α): α :=
  if b then
    ret { s with rip }
  else
    ret (next s)


def ctrl {α} [Throw α] (s: MachineState) (lookup: Label → (Nat → α) → α) (i: Instr) (ret: MachineState → α): α :=
  match i with
  | .jmp l =>
      lookup l (fun rip =>
      jump_if s True rip ret)
  | .jcc cc l =>
      lookup l (fun rip =>
      let cond := match cc with
        | .z  => s.flags.zf           -- Zero: ZF=1
        | .nz => !s.flags.zf          -- Not Zero: ZF=0
        | .b  => s.flags.cf           -- Below: CF=1
        | .ae => !s.flags.cf          -- Above/Equal: CF=0
        | .a  => !s.flags.cf && !s.flags.zf  -- Above: CF=0 ∧ ZF=0
        | .be => s.flags.cf || s.flags.zf    -- Below/Equal: CF=1 ∨ ZF=1
      jump_if s cond rip ret)
  | _ => throw s!"unsupported control instruction {repr i}"

abbrev Program := List (Option Label × Instr)

def lookup {α} [Throw α] (p: Program) (l: Label) (ret: Nat → α): α :=
  match p.findIdx? (fun (l', _) => l' = .some l) with
  | .some rip => ret rip
  | .none => throw s!"Invalid label: {repr l}"

def fetch {α} [Throw α] (p: Program) (s: MachineState) (ret: (Option Label × Instr) → α): α :=
  match p[s.rip]? with
  | .some ins => ret ins
  | .none => throw "Impossible: PC outside of program bounds"

def eval1 {α} [m: Throw α] (p: Program) (s: MachineState) (ret: MachineState → α): α :=
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
