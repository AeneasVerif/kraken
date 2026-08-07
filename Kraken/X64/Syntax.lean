import Lean
import Std

inductive Width | W8 | W16 | W32 | W64 deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString Width where
  toString | .W8 => "w8" | .W16 => "w16" | .W32 => "w32" | .W64 => "w64"

namespace Width
@[simp, reducible] def bits : Width → Nat | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
@[simp, reducible] def bytes : Width → Nat | W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8
abbrev bytesv (w : Width) {n} : BitVec n := BitVec.ofNat n w.bytes
abbrev type (w : Width) : Type := BitVec w.bits
instance {w : Width} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end Width

unif_hint (w : Width) where
  w =?= Width.W8 |- Width.type w =?= BitVec 8

unif_hint (w : Width) where
  w =?= Width.W16 |- Width.type w =?= BitVec 16

unif_hint (w : Width) where
  w =?= Width.W32 |- Width.type w =?= BitVec 32

unif_hint (w : Width) where
  w =?= Width.W64 |- Width.type w =?= BitVec 64

inductive AvxWidth | W128 | W256 | W512 deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString AvxWidth where
  toString |.W128 => "w128" | .W256 => "w256" | .W512 => "w512"

namespace AvxWidth
@[simp, reducible] def bits : AvxWidth → Nat | W128 => 128 | W256 => 256 | W512 => 512
@[simp, reducible] def bytes : AvxWidth → Nat | W128 => 16 | W256 => 32 | W512 => 64
abbrev bytesv (w : AvxWidth) {n} : BitVec n := BitVec.ofNat n w.bytes
abbrev type (w : AvxWidth) : Type := BitVec w.bits
instance {w : AvxWidth} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end AvxWidth

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W128 |- AvxWidth.type w =?= BitVec 128

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W256 |- AvxWidth.type w =?= BitVec 256

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W512 |- AvxWidth.type w =?= BitVec 512

inductive RegMm
  | mm0  | mm1  | mm2  | mm3
  | mm4  | mm5  | mm6  | mm7
  | mm8  | mm9  | mm10 | mm11
  | mm12 | mm13 | mm14 | mm15
  | mm16 | mm17 | mm18 | mm19
  | mm20 | mm21 | mm22 | mm23
  | mm24 | mm25 | mm26 | mm27
  | mm28 | mm29 | mm30 | mm31
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Reg64
  | rax | rbx | rcx | rdx
  | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Reg : Width → Type
  | low (_ : Reg64) (w : Width) : Reg w
  | ah : Reg .W8 | bh : Reg .W8 | ch : Reg .W8| dh : Reg .W8
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive AvxReg : AvxWidth → Type
  | xmm (_ : RegMm) : AvxReg AvxWidth.W128
  | ymm (_ : RegMm) : AvxReg AvxWidth.W256
  | zmm (_ : RegMm) : AvxReg AvxWidth.W512
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev Label := String

inductive ConstExpr
  | label (_ : Label)
  | int64 (_ : Int64)
  | before_current_instruction | after_current_instruction
  | add (_ _ : ConstExpr) | sub (_ _ : ConstExpr)
  -- Careful adding operations here! Need to match overflow behavior of all
  -- assemblers we want compatibility with. We assume oversized literals error;
  -- clang and gcc seem to always use 64-bit arithmetic (MCValue has an int64).
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance : Coe Label ConstExpr where coe := .label
instance : Coe Int64 ConstExpr where coe := .int64
attribute [coe] ConstExpr.label
attribute [coe] ConstExpr.int64

structure RegW where (w : Width) (reg : Reg w)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr, Hashable, Lean.ToExpr

structure AvxRegW where (w : AvxWidth) (reg : AvxReg w)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr, Hashable, Lean.ToExpr

-- For address expressions, the width of the register is determined only by the
-- instruction-wide address prefix. Concretely:
-- * movb $2 (%eax) denotes moving a single byte (operand width) into the memory
--   location at the 32-bit address stored in %eax (address width) -- note that
--   there is inference here!
-- * addr32 movb $2 (%rax) means the exact same thing, so the `addr32` prefix
--   acts as an instruction-wide override (at least for Clang; GCC rejects this)
--
-- Note that by doing so, we faithfully model two key things
-- * high byte registers cannot appear within memory operands:
--   test.S:1:11: error: invalid base+index expression
--   movb $2, (%ah)
-- * the operand encoding in the instruction encoding does not actually contain
--   a width -- it's all in the instruction-wide address size, modeled via the
--   `AddressSize` type class, below.
--
-- Implementation-wise, this means that our parser *will* have to do some amount
-- of type inference.
inductive RegOrRip where | reg (_ : Reg64) | rip : RegOrRip
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure AddrIndex where
  reg : Reg64
  scale: Width
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure AddrExpr where
  base : Option RegOrRip
  idx : Option AddrIndex
  disp : ConstExpr := .int64 0
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

class AddressSize where address_size : Width
export AddressSize (address_size)

inductive RegOrMem w | reg (r : Reg w) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe AddrExpr (RegOrMem w) where coe := RegOrMem.mem
attribute [coe] RegOrMem.mem
instance {w} : Coe (Reg w) (RegOrMem w) where coe := .reg
attribute [coe] RegOrMem.reg
abbrev Dst := RegOrMem

inductive AvxRegOrMem (w : AvxWidth) | avx (r : AvxReg w) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe AddrExpr (AvxRegOrMem w) where coe := AvxRegOrMem.mem
attribute [coe] AvxRegOrMem.mem
instance {w} : Coe (AvxReg w) (AvxRegOrMem w) where coe := .avx
attribute [coe] AvxRegOrMem.avx
abbrev AvxDst := AvxRegOrMem

inductive Operand w | regOrMem (_ : RegOrMem w) | imm (v : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe (RegOrMem w) (Operand w) where coe := .regOrMem
attribute [coe] Operand.regOrMem
instance {w} : Coe ConstExpr (Operand w) where coe := Operand.imm
attribute [coe] Operand.imm
abbrev Operand.reg {w} (r : Reg w) : Operand w := regOrMem (.reg r)
abbrev Operand.mem {w} (m : AddrExpr) : Operand w := regOrMem (.mem m)

-- TODO: We could remove this and use AvxRegOrMem directly.
inductive AvxOperand (w : AvxWidth) | regOrMem (_ : AvxRegOrMem w)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe (AvxRegOrMem w) (AvxOperand w) where coe := .regOrMem
attribute [coe] AvxOperand.regOrMem
abbrev AvxOperand.avx {w} (r : AvxReg w) : AvxOperand w := regOrMem (.avx r)
abbrev AvxOperand.mem {w} (m : AddrExpr) : AvxOperand w := regOrMem (.mem m)

inductive CondCode | z | nz | c | nc | a | be
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
abbrev CondCode.e := CondCode.z
abbrev CondCode.ne := CondCode.nz
abbrev CondCode.b := CondCode.c
abbrev CondCode.ae := CondCode.nc

inductive ShiftCountExpr | cl | imm8 (v : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive RelRegOrMem | rel (_ : ConstExpr) | reg (r : Reg .W64) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Operation (w : Width)
  -- Data movement
  | mov (_ : Dst w) (src : Operand w)
  | movsx {w'} (_ : Dst w) (src : RegOrMem w') -- {_ : w'.bits < w.bits ∧ w'.bits < 32}
  | movzx {w'} (_ : Dst w) (src : RegOrMem w') -- {_ : w'.bits < w.bits ∧ w'.bits < 32}
  | push (src : Operand w)
  | pop  (_ : Dst w)
  | setcc (_ : CondCode) (_ : Dst w) -- {_ : w = .W8}
  | cmovcc (_ : CondCode) (_ : Reg w) (src : RegOrMem w)
  -- Arithmetic
  | lea (_ : Reg w) (src : AddrExpr) -- {_ : 16 <= w.bits}
  | add  (_ : Dst w) (src : Operand w)
  | adc  (_ : Dst w) (src : Operand w)
  | adcx (_ : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  | adox (dst : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  | inc  (_ : RegOrMem w)
  | dec  (_ : RegOrMem w)
  | neg  (_ : RegOrMem w)
  | sub  (_ : Dst w) (src : Operand w)
  | sbb  (_ : Dst w) (src : Operand w)
  | cmp  (a : RegOrMem w) (b : Operand w)
  | mul  (src : RegOrMem w)
  | mulx (hi lo : Reg w) (src : RegOrMem w) -- {_ : 32 <= w.bits}
  -- imul1 and imul collectively describe variants of the same
  -- syntax level `imul` instruction, where imul1 is the 1-operand case
  | imul1 (src : RegOrMem w)
  | imul (_ : Option (Dst w)) (src1 : RegOrMem w) (src2 : Operand w)
  -- Bitwise
  | test (a : RegOrMem w) (b : Operand w)
  | and  (_ : Dst w) (src : Operand w)
  | not  (_ : Dst w)
  | or   (_ : Dst w) (src : Operand w)
  | xor  (_ : Dst w) (src : Operand w)
  | shl  (_ : Dst w) (_ : ShiftCountExpr)
  | shr  (_ : Dst w) (_ : ShiftCountExpr)
  | sar  (_ : Dst w) (_ : ShiftCountExpr)
  | shld (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr) -- {_ : 16 <= w.bits}
  | shrd (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr) -- {_ : 16 <= w.bits}
  | rol  (_ : Dst w) (_ : ShiftCountExpr)
  | ror  (_ : Dst w) (_ : ShiftCountExpr)
  | rcl  (_ : Dst w) (_ : ShiftCountExpr)
  | rcr  (_ : Dst w) (_ : ShiftCountExpr)
  | bswap  (dst : Reg w) -- (_ : w = .W32 ∨ w = .W64)
  -- Control flow
  | jcc (cc : CondCode) (target : Label)
  | jmp (target : RelRegOrMem)
  | call (target : RelRegOrMem)
  | ret
  | nop (length : Nat)
  -- TODO: optiona third argument, with the caveat that `.align 16,,0` is valid
  -- syntax
  | nopalign (alignment : Nat) (pad : Option Nat)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

-- The non-v* variants take SSE registers only.
-- TODO: AVX512 extensions (write-masking, ...)
inductive AvxOperation (w : AvxWidth)
  | movups (_ : AvxDst w) (src : AvxRegOrMem w)
  | vmovups (_ : AvxDst w) (src : AvxRegOrMem w)
  | movaps (_ : AvxDst w) (src : AvxRegOrMem w)
  | subps (_ : AvxDst w) (src : AvxRegOrMem w)
  | addps (_ : AvxDst w) (src : AvxRegOrMem w)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

inductive Instr
  | regular (address_size : Width) (operation_size : Width) (operation : Operation operation_size)
  | avx (address_size : Width) (operation_size : AvxWidth) (operation : AvxOperation operation_size)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

instance [AddressSize] {w : Width} : CoeOut (Operation w) Instr where
  coe op := Instr.regular address_size w op

instance [AddressSize] {w : AvxWidth} : CoeOut (AvxOperation w) Instr where
  coe op := Instr.avx address_size w op

instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray
inductive Directive
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (_ : ByteArray)
  deriving BEq, DecidableEq, Repr, Hashable, Lean.ToExpr

abbrev Program := List Directive
abbrev Executable := Int64 × List (Directive × Nat) -- start and sizes

namespace Reg
@[match_pattern] abbrev rax := low .rax .W64
@[match_pattern] abbrev rbx := low .rbx .W64
@[match_pattern] abbrev rcx := low .rcx .W64
@[match_pattern] abbrev rdx := low .rdx .W64
@[match_pattern] abbrev rsi := low .rsi .W64
@[match_pattern] abbrev rdi := low .rdi .W64
@[match_pattern] abbrev rsp := low .rsp .W64
@[match_pattern] abbrev rbp := low .rbp .W64
@[match_pattern] abbrev r8  := low .r8  .W64
@[match_pattern] abbrev r9  := low .r9  .W64
@[match_pattern] abbrev r10 := low .r10 .W64
@[match_pattern] abbrev r11 := low .r11 .W64
@[match_pattern] abbrev r12 := low .r12 .W64
@[match_pattern] abbrev r13 := low .r13 .W64
@[match_pattern] abbrev r14 := low .r14 .W64
@[match_pattern] abbrev r15 := low .r15 .W64

@[match_pattern] abbrev eax  := low .rax .W32
@[match_pattern] abbrev ebx  := low .rbx .W32
@[match_pattern] abbrev ecx  := low .rcx .W32
@[match_pattern] abbrev edx  := low .rdx .W32
@[match_pattern] abbrev esi  := low .rsi .W32
@[match_pattern] abbrev edi  := low .rdi .W32
@[match_pattern] abbrev esp  := low .rsp .W32
@[match_pattern] abbrev ebp  := low .rbp .W32
@[match_pattern] abbrev r8d  := low .r8  .W32
@[match_pattern] abbrev r9d  := low .r9  .W32
@[match_pattern] abbrev r10d := low .r10 .W32
@[match_pattern] abbrev r11d := low .r11 .W32
@[match_pattern] abbrev r12d := low .r12 .W32
@[match_pattern] abbrev r13d := low .r13 .W32
@[match_pattern] abbrev r14d := low .r14 .W32
@[match_pattern] abbrev r15d := low .r15 .W32

@[match_pattern] abbrev ax   := low .rax .W16
@[match_pattern] abbrev bx   := low .rbx .W16
@[match_pattern] abbrev cx   := low .rcx .W16
@[match_pattern] abbrev dx   := low .rdx .W16
@[match_pattern] abbrev si   := low .rsi .W16
@[match_pattern] abbrev di   := low .rdi .W16
@[match_pattern] abbrev sp   := low .rsp .W16
@[match_pattern] abbrev bp   := low .rbp .W16
@[match_pattern] abbrev r8w  := low .r8  .W16
@[match_pattern] abbrev r9w  := low .r9  .W16
@[match_pattern] abbrev r10w := low .r10 .W16
@[match_pattern] abbrev r11w := low .r11 .W16
@[match_pattern] abbrev r12w := low .r12 .W16
@[match_pattern] abbrev r13w := low .r13 .W16
@[match_pattern] abbrev r14w := low .r14 .W16
@[match_pattern] abbrev r15w := low .r15 .W16

@[match_pattern] abbrev al   := low .rax .W8
@[match_pattern] abbrev bl   := low .rbx .W8
@[match_pattern] abbrev cl   := low .rcx .W8
@[match_pattern] abbrev dl   := low .rdx .W8
@[match_pattern] abbrev sil  := low .rsi .W8
@[match_pattern] abbrev dil  := low .rdi .W8
@[match_pattern] abbrev spl  := low .rsp .W8
@[match_pattern] abbrev bpl  := low .rbp .W8
@[match_pattern] abbrev r8b  := low .r8  .W8
@[match_pattern] abbrev r9b  := low .r9  .W8
@[match_pattern] abbrev r10b := low .r10 .W8
@[match_pattern] abbrev r11b := low .r11 .W8
@[match_pattern] abbrev r12b := low .r12 .W8
@[match_pattern] abbrev r13b := low .r13 .W8
@[match_pattern] abbrev r14b := low .r14 .W8
@[match_pattern] abbrev r15b := low .r15 .W8
end Reg
