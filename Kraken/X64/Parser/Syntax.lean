module

public import Kraken.Parser
public meta import Kraken.Parser

open Lean Kraken.Parser

namespace Kraken.X64.Parser

-- ============================================================================
-- Operand Syntax Categories & Productions
-- ============================================================================

/-- X64 assembly identifier (`main`, `and`, `.LBB0_1`, `aa.1.aa.1`, `.L.str.1.llvm.12345`). -/
declare_syntax_cat x64_ident
syntax asmIdentToken : x64_ident

/-- X64 constant expression (signed or unsigned integer, symbol with `+` or `-` offset). -/
declare_syntax_cat x64_const
syntax num : x64_const
syntax "-" num : x64_const
syntax "+" num : x64_const
syntax x64_ident "+" num : x64_const
syntax x64_ident "-" num : x64_const
syntax x64_ident : x64_const

/-- X64 general-purpose register name (`rax`..`r15`, `eax`..`r15d`, `ax`..`r15w`, `al`..`r15b`, `ah`..`dh`). -/
declare_syntax_cat x64_reg_name (behavior := both)

declare_affixes reg_legacy_16
  | /-- Accumulator register. -/       "ax"
  | /-- Base register. -/              "bx"
  | /-- Counter register. -/           "cx"
  | /-- Data register. -/              "dx"
  | /-- Source index register. -/      "si"
  | /-- Destination index register. -/ "di"
  | /-- Stack pointer register. -/     "sp"
  | /-- Base pointer register. -/      "bp"

declare_affixes reg_ext_widths
  | /-- Full 64 bits. -/  ""
  | /-- Lower 32 bits. -/ "d"
  | /-- Lower 16 bits. -/ "w"
  | /-- Lower 8 bits. -/  "b"

declare_affixes reg_abcd_sub
  | /-- Lower 16 bits. -/                                  "x"
  | /-- Lower 8 bits. -/                                   "l"
  | /-- Upper 8 bits of the lower 16 bits (bits 8–15). -/  "h"

declare_affixes reg_index_sub
  | /-- Lower 16 bits. -/ ""
  | /-- Lower 8 bits. -/  "l"

/-- Full 64-bit general-purpose register. -/
syntax_affixed (suffixes := reg_legacy_16) "r" : x64_reg_name
/-- Lower 32-bit subregister. -/
syntax_affixed (suffixes := reg_legacy_16) "e" : x64_reg_name

/-- Extended general-purpose register (`r8`). -/
syntax_affixed (suffixes := reg_ext_widths) "r8" : x64_reg_name
/-- Extended general-purpose register (`r9`). -/
syntax_affixed (suffixes := reg_ext_widths) "r9" : x64_reg_name
/-- Extended general-purpose register (`r10`). -/
syntax_affixed (suffixes := reg_ext_widths) "r10" : x64_reg_name
/-- Extended general-purpose register (`r11`). -/
syntax_affixed (suffixes := reg_ext_widths) "r11" : x64_reg_name
/-- Extended general-purpose register (`r12`). -/
syntax_affixed (suffixes := reg_ext_widths) "r12" : x64_reg_name
/-- Extended general-purpose register (`r13`). -/
syntax_affixed (suffixes := reg_ext_widths) "r13" : x64_reg_name
/-- Extended general-purpose register (`r14`). -/
syntax_affixed (suffixes := reg_ext_widths) "r14" : x64_reg_name
/-- Extended general-purpose register (`r15`). -/
syntax_affixed (suffixes := reg_ext_widths) "r15" : x64_reg_name

/-- Subregister of accumulator register (`rax`). -/
syntax_affixed (suffixes := reg_abcd_sub) "a" : x64_reg_name
/-- Subregister of base register (`rbx`). -/
syntax_affixed (suffixes := reg_abcd_sub) "b" : x64_reg_name
/-- Subregister of counter register (`rcx`). -/
syntax_affixed (suffixes := reg_abcd_sub) "c" : x64_reg_name
/-- Subregister of data register (`rdx`). -/
syntax_affixed (suffixes := reg_abcd_sub) "d" : x64_reg_name

/-- Subregister of source index register (`rsi`). -/
syntax_affixed (suffixes := reg_index_sub) "si" : x64_reg_name
/-- Subregister of destination index register (`rdi`). -/
syntax_affixed (suffixes := reg_index_sub) "di" : x64_reg_name
/-- Subregister of stack pointer register (`rsp`). -/
syntax_affixed (suffixes := reg_index_sub) "sp" : x64_reg_name
/-- Subregister of base pointer register (`rbp`). -/
syntax_affixed (suffixes := reg_index_sub) "bp" : x64_reg_name
/-- Register antiquotation -/
syntax "❰" term "❱" : x64_reg_name

/-- X64 general-purpose register operand (`%rax`..`%r15`, `%eax`..`%r15d`, `%ax`..`%r15w`, `%al`..`%r15b`, `%ah`..`%dh`). -/
declare_syntax_cat x64_reg
syntax "%" noWs x64_reg_name : x64_reg

/-- X64 memory base register (`%rip` or a general-purpose register). -/
declare_syntax_cat x64_reg_or_rip
syntax "%" noWs &"rip" : x64_reg_or_rip
syntax x64_reg : x64_reg_or_rip

/-- X64 AVX vector register name (`xmm0`..`xmm31`, `ymm0`..`ymm31`, `zmm0`..`zmm31`). -/
declare_syntax_cat x64_avx_reg_name (behavior := both)

declare_affixes avx_indices
  | "0"  | "1"  | "2"  | "3"  | "4"  | "5"  | "6"  | "7"
  | "8"  | "9"  | "10" | "11" | "12" | "13" | "14" | "15"
  | "16" | "17" | "18" | "19" | "20" | "21" | "22" | "23"
  | "24" | "25" | "26" | "27" | "28" | "29" | "30" | "31"

/-- 128-bit XMM vector register. -/
syntax_affixed (suffixes := avx_indices) "xmm" : x64_avx_reg_name
/-- 256-bit YMM vector register. -/
syntax_affixed (suffixes := avx_indices) "ymm" : x64_avx_reg_name
/-- 512-bit ZMM vector register. -/
syntax_affixed (suffixes := avx_indices) "zmm" : x64_avx_reg_name
/-- Avx register antiquotation -/
syntax "❰" term "❱" : x64_avx_reg_name

/-- X64 AVX vector register operand (`%xmm0`..`%xmm31`, `%ymm0`..`%ymm31`, `%zmm0`..`%zmm31`). -/
declare_syntax_cat x64_avx_reg
syntax "%" noWs x64_avx_reg_name : x64_avx_reg

/-- X64 immediate operand (`$42`, `$-1`, `$sym`, `$sym+8`). -/
declare_syntax_cat x64_imm
syntax "$" x64_const : x64_imm

/-- X64 shift count operand (`$imm` or `%cl`). -/
declare_syntax_cat x64_shift_count
syntax x64_imm : x64_shift_count
syntax "%" noWs &"cl" : x64_shift_count

/-- X64 memory addressing operand (`disp(%base, %idx, scale)` or bare displacement). -/
declare_syntax_cat x64_mem
syntax (x64_const)? "(" x64_reg_or_rip ("," x64_reg ("," num)?)? ")" : x64_mem
syntax x64_const : x64_mem

declare_syntax_cat x64_reg_or_mem
syntax x64_reg : x64_reg_or_mem
syntax x64_mem : x64_reg_or_mem

/-- X64 general instruction operand (register, immediate, memory, or Lean term antiquotation). -/
declare_syntax_cat x64_operand
syntax x64_reg_or_mem : x64_operand
syntax x64_imm : x64_operand
syntax "❰" term "❱" : x64_operand
/-- Symbolic immediate with an offset (`$sym+8`, `$sym-8`). Lean parses `$sym` as an antiquotation node
    of this category rather than as an `x64_imm`, so the offset has to be attached here instead of in
    `x64_const`; the elaborator requires the left operand to be such a `$sym` node. -/
syntax x64_operand "+" num : x64_operand
syntax x64_operand "-" num : x64_operand

/-- X64 AVX instruction operand (AVX register or memory). -/
declare_syntax_cat x64_avx_operand
syntax x64_avx_reg : x64_avx_operand
syntax x64_mem     : x64_avx_operand
syntax "❰" term "❱" : x64_avx_operand

-- ============================================================================
-- Instruction Suffix Sets & Mnemonic Categories
-- ============================================================================

declare_affixes lq
  | /-- Operand width inferred from operands. -/ ""
  | /-- 32-bit (doubleword) operand width. -/    "l"
  | /-- 64-bit (quadword) operand width. -/      "q"

declare_affixes wlq extends lq
  | /-- 16-bit (word) operand width. -/          "w"

declare_affixes bwlq extends wlq
  | /-- 8-bit (byte) operand width. -/           "b"

declare_affixes cc
  | /-- Condition: zero (`ZF = 1`; alias of `e`). -/                                      "z"
  | /-- Condition: equal (`ZF = 1`; alias of `z`). -/                                     "e"
  | /-- Condition: not zero (`ZF = 0`; alias of `ne`). -/                                 "nz"
  | /-- Condition: not equal (`ZF = 0`; alias of `nz`). -/                                "ne"
  | /-- Condition: below, unsigned (`CF = 1`; alias of `c`, `nae`). -/                    "b"
  | /-- Condition: carry (`CF = 1`; alias of `b`, `nae`). -/                              "c"
  | /-- Condition: not above or equal, unsigned (`CF = 1`; alias of `b`, `c`). -/         "nae"
  | /-- Condition: above or equal, unsigned (`CF = 0`; alias of `nc`, `nb`). -/           "ae"
  | /-- Condition: not carry (`CF = 0`; alias of `ae`, `nb`). -/                          "nc"
  | /-- Condition: not below, unsigned (`CF = 0`; alias of `ae`, `nc`). -/                "nb"
  | /-- Condition: above, unsigned (`CF = 0` and `ZF = 0`; alias of `nbe`). -/            "a"
  | /-- Condition: not below or equal, unsigned (`CF = 0` and `ZF = 0`; alias of `a`). -/ "nbe"
  | /-- Condition: below or equal, unsigned (`CF = 1` or `ZF = 1`; alias of `na`). -/     "be"
  | /-- Condition: not above, unsigned (`CF = 1` or `ZF = 1`; alias of `be`). -/          "na"
  | /-- Condition: less, signed (`SF ≠ OF`; alias of `nge`). -/                           "l"
  | /-- Condition: not greater or equal, signed (`SF ≠ OF`; alias of `l`). -/             "nge"
  | /-- Condition: less or equal, signed (`ZF = 1` or `SF ≠ OF`; alias of `ng`). -/       "le"
  | /-- Condition: not greater, signed (`ZF = 1` or `SF ≠ OF`; alias of `le`). -/         "ng"

declare_affixes ext_z
  | /-- 8-bit (byte) source to 16-bit (word) destination. -/              "bw"
  | /-- 8-bit (byte) source to 32-bit (doubleword) destination. -/        "bl"
  | /-- 8-bit (byte) source to 64-bit (quadword) destination. -/          "bq"
  | /-- 16-bit (word) source to 32-bit (doubleword) destination. -/       "wl"
  | /-- 16-bit (word) source to 64-bit (quadword) destination. -/         "wq"

declare_affixes ext_s extends ext_z
  | /-- 32-bit (doubleword) source to 64-bit (quadword) destination (alias of `xd`). -/ "lq"
  | /-- 32-bit (doubleword) source to 64-bit (quadword) destination (alias of `lq`). -/ "xd"

declare_affixes avx_ps
  | /-- Packed single-precision floating-point (32-bit lanes). -/         "ps"

/-- Binary ALU/move mnemonics taking `(src : Operand, dst : RegOrMem)`. -/
declare_syntax_cat x64_bin_op (behavior := both)
/-- Integer addition (`dst ← dst + src`). -/
syntax_affixed (suffixes := bwlq) "add" : x64_bin_op
/-- Integer addition with carry (`dst ← dst + src + CF`). -/
syntax_affixed (suffixes := bwlq) "adc" : x64_bin_op
/-- Integer subtraction (`dst ← dst - src`). -/
syntax_affixed (suffixes := bwlq) "sub" : x64_bin_op
/-- Integer subtraction with borrow (`dst ← dst - (src + CF)`). -/
syntax_affixed (suffixes := bwlq) "sbb" : x64_bin_op
/-- Move data (`dst ← src`). -/
syntax_affixed (suffixes := bwlq) "mov" : x64_bin_op
/-- Move 64-bit immediate or data (`dst ← src`). -/
syntax_affixed (suffixes := bwlq) "movabs" : x64_bin_op
/-- Bitwise exclusive OR (`dst ← dst ^ src`). -/
syntax_affixed (suffixes := bwlq) "xor" : x64_bin_op
/-- Bitwise logical AND (`dst ← dst & src`). -/
syntax_affixed (suffixes := bwlq) "and" : x64_bin_op
/-- Bitwise inclusive OR (`dst ← dst | src`). -/
syntax_affixed (suffixes := bwlq) "or" : x64_bin_op
/-- Compare two operands (`dst - src`, setting flags). -/
syntax_affixed (suffixes := bwlq) "cmp" : x64_bin_op
/-- Logical compare (`dst & src`, setting flags). -/
syntax_affixed (suffixes := bwlq) "test" : x64_bin_op

/-- Binary carry-chain mnemonics (`adcx*`, `adox*`) taking `(src : RegOrMem, dst : Reg)`. -/
declare_syntax_cat x64_rm_reg_op (behavior := both)
/-- Unsigned integer addition with carry flag (`CF`). -/
syntax_affixed (suffixes := lq) "adcx" : x64_rm_reg_op
/-- Unsigned integer addition with overflow flag (`OF`). -/
syntax_affixed (suffixes := lq) "adox" : x64_rm_reg_op

/-- Conditional move (`cmov<cc>`) mnemonics taking `(src : RegOrMem, dst : Reg)`. -/
declare_syntax_cat x64_cmov_op (behavior := both)
/-- Conditional move if condition holds. -/
syntax_affixed (suffixes := cc) "cmov" : x64_cmov_op

/-- Unary arithmetic/bitwise mnemonics taking `(dst : RegOrMem)`. -/
declare_syntax_cat x64_unary_op (behavior := both)
/-- Unsigned multiply (`%rdx:%rax ← %rax * src`). -/
syntax_affixed (suffixes := bwlq) "mul" : x64_unary_op
/-- Two's complement negation (`dst ← -dst`). -/
syntax_affixed (suffixes := bwlq) "neg" : x64_unary_op
/-- Decrement by 1 (`dst ← dst - 1`). -/
syntax_affixed (suffixes := bwlq) "dec" : x64_unary_op
/-- Increment by 1 (`dst ← dst + 1`). -/
syntax_affixed (suffixes := bwlq) "inc" : x64_unary_op
/-- Bitwise one's complement (`dst ← ~dst`). -/
syntax_affixed (suffixes := bwlq) "not" : x64_unary_op

/-- Conditional byte-set (`set<cc>`) mnemonics taking `(dst : RegOrMem)`. -/
declare_syntax_cat x64_set_op (behavior := both)
/-- Set byte to 1 if condition holds, 0 otherwise. -/
syntax_affixed (suffixes := cc) "set" : x64_set_op

/-- Signed multiply (`imul*`) mnemonics (1-, 2-, or 3-operand forms). -/
declare_syntax_cat x64_imul_op (behavior := both)
/-- Signed multiply. -/
syntax_affixed (suffixes := bwlq) "imul" : x64_imul_op

/-- BMI2 unsigned multiply (`mulx*`) mnemonics (3-operand form). -/
declare_syntax_cat x64_mulx_op (behavior := both)
/-- Unsigned multiply without affecting flags (`hi:lo ← %rdx * src`). -/
syntax_affixed (suffixes := lq) "mulx" : x64_mulx_op

/-- Sign- and zero-extending move mnemonics with explicit source and destination widths. -/
declare_syntax_cat x64_ext_mov_op (behavior := both)
/-- Move with sign extension. -/
syntax_affixed (suffixes := ext_s) "movs" : x64_ext_mov_op
/-- Move with zero extension. -/
syntax_affixed (suffixes := ext_z) "movz" : x64_ext_mov_op

/-- Load effective address (`lea*`) mnemonics. -/
declare_syntax_cat x64_lea_op (behavior := both)
/-- Load effective address (`dst ← addr(src)`). -/
syntax_affixed (suffixes := bwlq) "lea" : x64_lea_op

/-- AVX vector instruction mnemonics. -/
declare_syntax_cat x64_avx_op (behavior := both)
/-- Move unaligned packed values. -/
syntax_affixed (suffixes := avx_ps) "movu" : x64_avx_op
/-- AVX move unaligned packed values. -/
syntax_affixed (suffixes := avx_ps) "vmovu" : x64_avx_op
/-- Move aligned packed values. -/
syntax_affixed (suffixes := avx_ps) "mova" : x64_avx_op
/-- Add packed floating-point values. -/
syntax_affixed (suffixes := avx_ps) "add" : x64_avx_op
/-- Subtract packed floating-point values. -/
syntax_affixed (suffixes := avx_ps) "sub" : x64_avx_op

/-- Shift and rotate mnemonics (1- or 2-operand forms). -/
declare_syntax_cat x64_shift_op (behavior := both)
/-- Shift logical left. -/
syntax_affixed (suffixes := bwlq) "shl" : x64_shift_op
/-- Shift arithmetic left. -/
syntax_affixed (suffixes := bwlq) "sal" : x64_shift_op
/-- Shift logical right. -/
syntax_affixed (suffixes := bwlq) "shr" : x64_shift_op
/-- Shift arithmetic right. -/
syntax_affixed (suffixes := bwlq) "sar" : x64_shift_op
/-- Rotate left. -/
syntax_affixed (suffixes := bwlq) "rol" : x64_shift_op
/-- Rotate right. -/
syntax_affixed (suffixes := bwlq) "ror" : x64_shift_op
/-- Rotate through carry left. -/
syntax_affixed (suffixes := bwlq) "rcl" : x64_shift_op
/-- Rotate through carry right. -/
syntax_affixed (suffixes := bwlq) "rcr" : x64_shift_op

/-- Double-precision shift (`shld*`, `shrd*`) mnemonics (3-operand form). -/
declare_syntax_cat x64_shd_op (behavior := both)
/-- Double-precision shift left. -/
syntax_affixed (suffixes := wlq) "shld" : x64_shd_op
/-- Double-precision shift right. -/
syntax_affixed (suffixes := wlq) "shrd" : x64_shd_op

/-- Byte swap (`bswap*`) mnemonics (1 register operand). -/
declare_syntax_cat x64_bswap_op (behavior := both)
/-- Byte-order swap (endianness reversal). -/
syntax_affixed (suffixes := lq) "bswap" : x64_bswap_op

/-- Stack push (`push*`) mnemonics (1 operand). -/
declare_syntax_cat x64_push_op (behavior := both)
/-- Push operand onto stack. -/
syntax_affixed (suffixes := bwlq) "push" : x64_push_op

/-- Stack pop (`pop*`) mnemonics (1 operand). -/
declare_syntax_cat x64_pop_op (behavior := both)
/-- Pop value from stack into operand. -/
syntax_affixed (suffixes := bwlq) "pop" : x64_pop_op

/-- Conditional jump (`j<cc>`) mnemonics taking a target label. -/
declare_syntax_cat x64_jcc_op (behavior := both)
/-- Conditional relative jump to label if condition holds. -/
syntax_affixed (suffixes := cc) "j" : x64_jcc_op

-- ============================================================================
-- Instruction, Directive & Program Syntax
-- ============================================================================

/-- X64 instruction statement with instruction-specific arity and operand categories. -/
declare_syntax_cat x64_instr (behavior := both)
syntax withPosition(".align" lineEq num ("," lineEq num)?) : x64_instr
syntax withPosition(x64_bin_op lineEq x64_operand "," lineEq x64_operand) : x64_instr
syntax withPosition(x64_rm_reg_op lineEq x64_operand "," lineEq x64_reg) : x64_instr
syntax withPosition(x64_cmov_op lineEq x64_operand "," lineEq x64_reg) : x64_instr
syntax withPosition(x64_unary_op lineEq x64_operand) : x64_instr
syntax withPosition(x64_set_op lineEq x64_operand) : x64_instr
syntax withPosition(x64_imul_op lineEq x64_operand) : x64_instr
syntax withPosition(x64_imul_op lineEq x64_operand "," lineEq x64_operand) : x64_instr
syntax withPosition(x64_imul_op lineEq x64_operand "," lineEq x64_operand "," lineEq x64_reg) : x64_instr
syntax withPosition(x64_mulx_op lineEq x64_operand "," lineEq x64_reg "," lineEq x64_reg) : x64_instr
syntax withPosition(&"movsx" lineEq x64_reg "," lineEq x64_reg) : x64_instr
syntax withPosition(&"movzx" lineEq x64_reg "," lineEq x64_reg) : x64_instr
syntax withPosition(x64_ext_mov_op lineEq x64_operand "," lineEq x64_reg) : x64_instr
syntax withPosition(x64_lea_op lineEq x64_mem "," lineEq x64_reg) : x64_instr
syntax withPosition(x64_avx_op lineEq x64_avx_operand "," lineEq x64_avx_operand) : x64_instr
syntax withPosition(x64_shift_op lineEq x64_operand) : x64_instr
syntax withPosition(x64_shift_op lineEq x64_shift_count "," lineEq x64_operand) : x64_instr
syntax withPosition(x64_shd_op lineEq x64_shift_count "," lineEq x64_reg "," lineEq x64_operand) : x64_instr
syntax withPosition(x64_bswap_op lineEq x64_reg) : x64_instr
syntax withPosition(x64_push_op lineEq x64_operand) : x64_instr
syntax withPosition(x64_pop_op lineEq x64_operand) : x64_instr
syntax &"ret"  : x64_instr
syntax &"retq" : x64_instr
syntax withPosition(&"call"  lineEq x64_operand) : x64_instr
syntax withPosition(&"callq" lineEq x64_operand) : x64_instr
syntax withPosition(&"jmp"   lineEq x64_operand) : x64_instr
syntax withPosition(&"jmpq"  lineEq x64_operand) : x64_instr
syntax &"nop" : x64_instr
syntax withPosition(&"nop" lineEq num) : x64_instr
syntax withPosition(x64_jcc_op lineEq x64_ident) : x64_instr

/-- X64 directive (label declaration, instruction, or Lean term antiquotation). -/
declare_syntax_cat x64_directive (behavior := both)
syntax withPosition(atomic(x64_ident lineEq ":")) ";"? : x64_directive
syntax x64_instr ";" : x64_directive
syntax withPosition(x64_instr notFollowedBy(lineEq (x64_ident <|> "," <|> x64_operand))) : x64_directive
syntax "❰" term "❱" ";"? : x64_directive

/-- X64 assembly program (sequence of directives). -/
declare_syntax_cat x64_prog (behavior := both)
syntax x64_directive* : x64_prog

end Kraken.X64.Parser
