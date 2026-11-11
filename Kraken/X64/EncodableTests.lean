module

/-
  Hand-picked instructions on both sides of each `Instr.encodable` boundary.
  `KrakenRunnerX64 --encodable` checks the predicate against `as` on random instructions.
-/

import Kraken.X64.Encodable
meta import Kraken.X64.Encodable
import Kraken.X64.Parser
meta import Kraken.X64.Parser

open Kraken.X64.Parser

/-- Whether the instruction that `s` parses to is encodable. -/
def enc (s : String) : Option Bool :=
  match parse s with
  | .ok [.instr i] => some i.encodable
  | _ => none

def encodable (ss : List String) : Bool := ss.all (enc · == some true)
def notEncodable (ss : List String) : Bool := ss.all (enc · == some false)

-- Register numbers: legacy SSE and VEX-only forms reach 0–15, EVEX forms 0–31.
#guard encodable ["paddd %xmm15, %xmm1", "vpand %xmm15, %xmm1, %xmm2", "vmovdqu %ymm15, %ymm1",
  "vpaddd %xmm31, %xmm1, %xmm2", "vmovdqu32 %ymm16, %ymm1", "vmovd %eax, %xmm16"]
#guard notEncodable ["paddd %xmm16, %xmm1", "vpand %xmm16, %xmm1, %xmm2",
  "vmovdqu %ymm16, %ymm1", "vperm2i128 $1, %ymm16, %ymm1, %ymm2"]

-- Widths each mnemonic exists at.
#guard encodable ["vperm2i128 $1, %ymm1, %ymm2, %ymm3", "vpand %ymm1, %ymm2, %ymm3",
  "vpaddd %zmm1, %zmm2, %zmm3", "bswap %eax", "pushw %ax", "pushq %rax", "imulw %ax, %bx"]
#guard notEncodable ["paddd %ymm1, %ymm2", "bswap %ax", "pushl %eax", "imulb %al, %bl"]

-- Operand kinds: one memory operand at most, a register where the encoding has no memory form.
#guard encodable ["addq (%rax), %rbx", "movups %xmm1, (%rax)", "vpaddd (%rax), %ymm1, %ymm2",
  "imull $3, (%rax), %ebx", "movsx %ax, %ax"]
#guard notEncodable ["vpaddd %ymm0, (%rax), %ymm2"]

-- Immediates: sign-extended 32 bits at 64 bits, else truncated; `movabs` into a register.
#guard encodable ["addq $2147483647, %rax", "addq $-2147483648, %rax",
  "addl $4294967295, %eax", "addl $-4294967295, %eax", "addb $255, %al", "addb $-255, %al",
  "addb $65535, %al", "movq $9223372036854775807, %rax", "pushq $-2147483648"]
#guard notEncodable ["addq $2147483648, %rax", "addq $-2147483649, %rax",
  "addl $4294967296, %eax", "addb $256, %al", "addb $-256, %al", "addb $65280, %al",
  "movq $2147483648, (%rax)", "pushq $2147483648"]

-- Byte immediates: unsigned for most, signed or unsigned for some.
#guard encodable ["shlq $255, %rax", "rolq $-128, %rax", "shlb $-255, %al",
  "pshufd $-128, %xmm1, %xmm2", "psrld $255, %xmm1", "palignr $255, %xmm1, %xmm2"]
#guard notEncodable ["shlq $256, %rax", "shlq $-1, %rax", "rolq $-129, %rax",
  "pshufd $256, %xmm1, %xmm2", "psrld $-1, %xmm1", "palignr $-1, %xmm1, %xmm2"]

-- Displacements: signed 32 bits, any 32 bits at a 32-bit address, any 64 bits for `movabs`.
#guard encodable ["movq 2147483647(%rax), %rbx", "movl 4294967295(%eax), %ebx",
  "leal 4294967295(%rax), %ebx", "movq 9223372036854775807, %rax", "movq 2147483647, %rbx",
  "movq 8(%rip), %rax", "movq sym(%rip), %rax", "movq sym+8(%rax), %rbx"]
#guard notEncodable ["movq 2147483648(%rax), %rbx", "movl 4294967296(%eax), %ebx",
  "leaq 4294967295(%rax), %rbx", "movq 2147483648, %rbx", "movq (%rax,%rsp,1), %rbx"]

-- `ah`, `bh`, `ch`, `dh` with an operand that needs a REX prefix.
#guard encodable ["movb %ah, %bl", "movb %ah, (%rax)", "movzbl %ah, %eax", "movb %ah, 8(%rip)"]
#guard notEncodable ["movb %ah, %sil", "movb %ah, %r8b", "movb %ah, (%r8)",
  "addb %ah, (%rax,%r9)", "movzbq %ah, %rax"]

-- Symbols: one label plus or minus a literal; the linker checks that it fits.
#guard encodable ["movq $sym, %rax", "movq $sym+8, %rax", "addb $sym-1, %al", "jmp foo", "jne foo"]
#guard notEncodable ["movq $a-b, %rax"]

-- Address size: 64 or 32 bits, and only where the printer shows it.
#guard encodable ["movb $1, (%eax)", "addr32 rep movsb", "rep stosq"]

-- Branches, `nop` and alignment.
#guard encodable ["jmp %rax", "call 8(%rax)", "nop", ".align 16", ".align 16, 0x90"]
#guard notEncodable ["nop 5", ".align 16, 0", ".align 3"]

-- Forms the parser does not produce.
#guard
  let rax : AddrExpr := { base := some (.reg .rax), idx := none }
  let rbx : AddrExpr := { base := some (.reg .rbx), idx := none }
  let abs : AddrExpr := { base := none, idx := none, disp := .int64 8 }
  let idxOnly : AddrExpr := { base := none, idx := some ⟨.rax, .W64⟩ }
  let x1 := AvxReg.xmm .mm1
  let z1 := AvxReg.zmm .mm1
  [ Instr.avx .W64 .W128 (.vperm2i128 (.avx x1) (.avx x1) (.avx x1) (.int64 1)),
    Instr.avx .W64 .W512 (.vpand (.avx z1) (.avx z1) (.avx z1)),
    Instr.avx .W64 .W128 (.vinserti64x4 (.avx x1) (.avx x1) (.avx (.ymm .mm1)) (.int64 1)),
    Instr.regular .W64 .W64 (.add (.mem rax) (.regOrMem (.mem rbx))),
    Instr.regular .W64 .W16 (.movsx (.reg (.low .rax .W16)) (.mem rax : RegOrMem .W16)),
    -- 16-bit addressing, and a 32-bit absolute address, which prints as a 64-bit one.
    Instr.regular .W16 .W8 (.mov (.mem rax) (.imm (.int64 1))),
    Instr.regular .W32 .W64 (.inc (.mem abs)),
    Instr.regular .W16 .W8 (.movs false),
    Instr.regular .W64 .W64 (.inc (.mem idxOnly)),
    Instr.regular .W64 .W64 (.jcc .z "9x"),
    Instr.regular .W64 .W64 (.mov (.reg .rax) (.imm .before_current_instruction)) ].all
    (!·.encodable)

-- The address size does not matter without a memory operand.
#guard (Instr.regular .W16 .W64 (.add (.reg .rax) (.imm (.int64 1)))).encodable
#guard (Instr.regular .W64 .W64 (.inc (.mem { base := none, idx := none, disp := .int64 8 })))
  |>.encodable
