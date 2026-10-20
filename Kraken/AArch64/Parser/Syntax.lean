module

public import Kraken.Parser
public meta import Kraken.Parser

open Lean Kraken.Parser

namespace Kraken.AArch64.Parser

-- ============================================================================
-- Operand Syntax Categories & Productions
-- ============================================================================

/-- AArch64 general-purpose register (`x0`..`x30`, `w0`..`w30`, `xzr`, `wzr`, `sp`, `wsp`, `lr`). -/
declare_syntax_cat aarch64_reg (behavior := both)

declare_affixes reg_idx
  | "0"  | "1"  | "2"  | "3"  | "4"  | "5"  | "6"  | "7"
  | "8"  | "9"  | "10" | "11" | "12" | "13" | "14" | "15"
  | "16" | "17" | "18" | "19" | "20" | "21" | "22" | "23"
  | "24" | "25" | "26" | "27" | "28" | "29" | "30"
  | /-- Zero register (reads as zero, discards writes). -/ "zr"

/-- 64-bit register. -/
syntax_affixed (suffixes := reg_idx) "x" : aarch64_reg
/-- 32-bit register (lower half of the corresponding 64-bit register). -/
syntax_affixed (suffixes := reg_idx) "w" : aarch64_reg
/-- 64-bit stack pointer. -/
syntax &"sp" : aarch64_reg
/-- 32-bit stack pointer (lower half of `sp`). -/
syntax &"wsp" : aarch64_reg
/-- Link register (alias of `x30`). -/
syntax &"lr" : aarch64_reg

/-- AArch64 assembly identifier other than a register name (`main`, `.LBB0_1`, `aa.1.aa.1`,
    `.L.str.1.llvm.12345`). -/
declare_syntax_cat aarch64_ident
syntax notFollowedBy(aarch64_reg) asmIdentToken : aarch64_ident

/-- AArch64 integer literal with optional sign (`16`, `-8`, `+8`, `0x10`). -/
declare_syntax_cat aarch64_int
syntax num : aarch64_int
syntax "-" num : aarch64_int
syntax "+" num : aarch64_int

/-- AArch64 integer immediate: integer literal with optional `#` prefix (`#16`, `16`, `#-8`). -/
declare_syntax_cat aarch64_imm
syntax "#"? aarch64_int : aarch64_imm

/-- AArch64 constant expression: integer immediate, relocation modifier applied to a symbol
    (`:lo12:sym`, `#:pg_hi21:sym`), or symbol. -/
declare_syntax_cat aarch64_const
syntax aarch64_imm : aarch64_const
syntax "#"? ":" aarch64_ident ":" aarch64_ident : aarch64_const
syntax aarch64_ident : aarch64_const

declare_affixes signedness
  | /-- Signed. -/   "s"
  | /-- Unsigned. -/ "u"

declare_affixes shift_kind
  | /-- Logical shift left. -/      "lsl"
  | /-- Logical shift right. -/     "lsr"
  | /-- Arithmetic shift right. -/  "asr"
  | /-- Rotate right. -/            "ror"

declare_affixes ext_width
  | /-- Byte (8 bits). -/      "b"
  | /-- Halfword (16 bits). -/ "h"
  | /-- Word (32 bits). -/     "w"

declare_affixes ext_width_x extends ext_width
  | /-- Doubleword (64 bits). -/ "x"

/-- Shift or extend keyword applied to a register or immediate operand. -/
declare_syntax_cat aarch64_modifier_kind (behavior := both)
syntax_affixed (suffixes := shift_kind) : aarch64_modifier_kind
/-- Extend the register before use. -/
syntax_affixed (prefixes := signedness) (suffixes := ext_width_x) "xt" : aarch64_modifier_kind

/-- Shift or extend modifier with optional amount (`lsl #2`, `uxtw`, `sxtw #3`). -/
declare_syntax_cat aarch64_modifier
syntax aarch64_modifier_kind (aarch64_imm)? : aarch64_modifier

/-- AArch64 memory addressing operand. -/
declare_syntax_cat aarch64_mem
/-- Base register with optional immediate offset (`[Xn]`, `[Xn, #imm]`). -/
syntax "[" aarch64_reg ("," aarch64_const)? "]" : aarch64_mem
/-- Pre-indexed immediate offset with writeback (`[Xn, #imm]!`). -/
syntax "[" aarch64_reg "," aarch64_const "]" "!" : aarch64_mem
/-- Post-indexed immediate offset with writeback (`[Xn], #imm`). -/
syntax withPosition("[" aarch64_reg "]" "," lineEq aarch64_const) : aarch64_mem
/-- Register offset with optional extend (`[Xn, Xm]`, `[Xn, Xm, lsl #3]`, `[Xn, Wm, uxtw #2]`). -/
syntax "[" aarch64_reg "," aarch64_reg ("," aarch64_modifier)? "]" : aarch64_mem

/-- PC-relative load source: literal pool constant (`=expr`) or label. -/
declare_syntax_cat aarch64_lit
syntax "=" aarch64_const : aarch64_lit
syntax aarch64_ident : aarch64_lit

/-- Load source operand: memory address or PC-relative literal. -/
declare_syntax_cat aarch64_load_src
syntax aarch64_mem : aarch64_load_src
syntax aarch64_lit : aarch64_load_src

/-- Flexible source operand: constant (`#imm`, `:lo12:sym`), optionally shifted constant
    (`#imm, lsl #12`), or register with optional shift/extend (`Rm`, `Rm, lsl #2`, `Wm, uxtw #2`). -/
declare_syntax_cat aarch64_src
syntax aarch64_const ("," aarch64_modifier)? : aarch64_src
syntax aarch64_reg ("," aarch64_modifier)? : aarch64_src

/-- Register or integer immediate operand. -/
declare_syntax_cat aarch64_reg_or_imm
syntax aarch64_reg : aarch64_reg_or_imm
syntax aarch64_imm : aarch64_reg_or_imm

declare_affixes cond
  | /-- Equal (`Z = 1`). -/                                                 "eq"
  | /-- Not equal (`Z = 0`). -/                                             "ne"
  | /-- Carry set / unsigned higher or same (`C = 1`; alias of `hs`). -/    "cs"
  | /-- Unsigned higher or same (`C = 1`; alias of `cs`). -/                "hs"
  | /-- Carry clear / unsigned lower (`C = 0`; alias of `lo`). -/           "cc"
  | /-- Unsigned lower (`C = 0`; alias of `cc`). -/                         "lo"
  | /-- Minus / negative (`N = 1`). -/                                      "mi"
  | /-- Plus / positive or zero (`N = 0`). -/                               "pl"
  | /-- Overflow set (`V = 1`). -/                                          "vs"
  | /-- Overflow clear (`V = 0`). -/                                        "vc"
  | /-- Unsigned higher (`C = 1` and `Z = 0`). -/                           "hi"
  | /-- Unsigned lower or same (`C = 0` or `Z = 1`). -/                     "ls"
  | /-- Signed greater than or equal (`N = V`). -/                          "ge"
  | /-- Signed less than (`N ≠ V`). -/                                      "lt"
  | /-- Signed greater than (`Z = 0` and `N = V`). -/                       "gt"
  | /-- Signed less than or equal (`Z = 1` or `N ≠ V`). -/                  "le"
  | /-- Always. -/                                                          "al"
  | /-- Never (behaves as always). -/                                       "nv"

/-- Condition code operand. -/
declare_syntax_cat aarch64_cond (behavior := both)
syntax_affixed (suffixes := cond) : aarch64_cond

-- ============================================================================
-- Instruction Suffix Sets & Mnemonic Categories
-- ============================================================================

declare_affixes flags
  | /-- Does not set the condition flags. -/ ""
  | /-- Sets the condition flags (`NZCV`). -/ "s"

declare_affixes ld_size
  | /-- Register-sized access. -/                                        ""
  | /-- Unsigned byte, zero-extended into a 32-bit register. -/          "b"
  | /-- Unsigned halfword, zero-extended into a 32-bit register. -/      "h"
  | /-- Signed byte, sign-extended. -/                                   "sb"
  | /-- Signed halfword, sign-extended. -/                               "sh"
  | /-- Signed word, sign-extended into a 64-bit register. -/            "sw"

declare_affixes st_size
  | /-- Register-sized access. -/ ""
  | /-- Low byte. -/              "b"
  | /-- Low halfword. -/          "h"

declare_affixes zero_test
  | /-- Taken when the tested value is zero. -/     "z"
  | /-- Taken when the tested value is non-zero. -/ "nz"

declare_affixes rev_width
  | /-- Whole register. -/                                     ""
  | /-- Each 16-bit halfword. -/                               "16"
  | /-- Each 32-bit word (64-bit registers only). -/           "32"
  | /-- Whole 64-bit register (alias of `rev` on `Xd`). -/     "64"

declare_affixes movw_kind
  | /-- Zeroing the other bits. -/            "z"
  | /-- Keeping the other bits. -/            "k"
  | /-- Inverting the result (`NOT`). -/      "n"

/-- Single-register load mnemonics taking `(Rt, address or literal)`. -/
declare_syntax_cat aarch64_ldr_op (behavior := both)
/-- Load register (scaled unsigned offset, pre/post-indexed, register offset, or PC-relative literal). -/
syntax_affixed (suffixes := ld_size) "ldr" : aarch64_ldr_op

/-- Single-register unscaled load mnemonics taking `(Rt, [Xn, #simm9])`. -/
declare_syntax_cat aarch64_ldur_op (behavior := both)
/-- Load register with unscaled signed 9-bit offset. -/
syntax_affixed (suffixes := ld_size) "ldur" : aarch64_ldur_op

/-- Single-register store mnemonics taking `(Rt, address)`. -/
declare_syntax_cat aarch64_str_op (behavior := both)
/-- Store register (scaled unsigned offset, pre/post-indexed, or register offset). -/
syntax_affixed (suffixes := st_size) "str" : aarch64_str_op

/-- Single-register unscaled store mnemonics taking `(Rt, [Xn, #simm9])`. -/
declare_syntax_cat aarch64_stur_op (behavior := both)
/-- Store register with unscaled signed 9-bit offset. -/
syntax_affixed (suffixes := st_size) "stur" : aarch64_stur_op

/-- Register-pair load/store mnemonics taking `(Rt1, Rt2, address)`. -/
declare_syntax_cat aarch64_pair_op (behavior := both)
/-- Load pair of registers. -/
syntax &"ldp" : aarch64_pair_op
/-- Load pair of signed words, sign-extended into 64-bit registers. -/
syntax &"ldpsw" : aarch64_pair_op
/-- Store pair of registers. -/
syntax &"stp" : aarch64_pair_op

/-- Add/subtract mnemonics taking `(Rd, Rn, flexible source)`. -/
declare_syntax_cat aarch64_arith_op (behavior := both)
/-- Add (`Rd ← Rn + src`). -/
syntax_affixed (suffixes := flags) "add" : aarch64_arith_op
/-- Subtract (`Rd ← Rn - src`). -/
syntax_affixed (suffixes := flags) "sub" : aarch64_arith_op

/-- Compare mnemonics taking `(Rn, flexible source)`. -/
declare_syntax_cat aarch64_cmp_op (behavior := both)
/-- Compare (`Rn - src`, setting the flags; alias of `subs xzr, Rn, src`). -/
syntax &"cmp" : aarch64_cmp_op
/-- Compare negative (`Rn + src`, setting the flags; alias of `adds xzr, Rn, src`). -/
syntax &"cmn" : aarch64_cmp_op

/-- Negate/invert mnemonics taking `(Rd, shifted register)`. -/
declare_syntax_cat aarch64_unary_op (behavior := both)
/-- Negate (`Rd ← -Rm`; alias of `sub Rd, xzr, Rm`). -/
syntax_affixed (suffixes := flags) "neg" : aarch64_unary_op
/-- Bitwise NOT (`Rd ← ~Rm`; alias of `orn Rd, xzr, Rm`). -/
syntax &"mvn" : aarch64_unary_op

/-- Bitwise logical mnemonics taking `(Rd, Rn, bitmask immediate or shifted register)`. -/
declare_syntax_cat aarch64_logic_op (behavior := both)
/-- Bitwise AND (`Rd ← Rn & src`). -/
syntax_affixed (suffixes := flags) "and" : aarch64_logic_op
/-- Bitwise bit clear (`Rd ← Rn & ~Rm`). -/
syntax_affixed (suffixes := flags) "bic" : aarch64_logic_op
/-- Bitwise OR (`Rd ← Rn | src`). -/
syntax &"orr" : aarch64_logic_op
/-- Bitwise OR NOT (`Rd ← Rn | ~Rm`). -/
syntax &"orn" : aarch64_logic_op
/-- Bitwise exclusive OR (`Rd ← Rn ^ src`). -/
syntax &"eor" : aarch64_logic_op
/-- Bitwise exclusive OR NOT (`Rd ← Rn ^ ~Rm`). -/
syntax &"eon" : aarch64_logic_op

/-- Three-register mnemonics taking `(Rd, Rn, Rm)`. -/
declare_syntax_cat aarch64_rrr_op (behavior := both)
/-- Add with carry (`Rd ← Rn + Rm + C`). -/
syntax_affixed (suffixes := flags) "adc" : aarch64_rrr_op
/-- Subtract with carry (`Rd ← Rn - Rm - ~C`). -/
syntax_affixed (suffixes := flags) "sbc" : aarch64_rrr_op
/-- Divide. -/
syntax_affixed (prefixes := signedness) "div" : aarch64_rrr_op
/-- Multiply (alias of `madd Rd, Rn, Rm, xzr`). -/
syntax &"mul" : aarch64_rrr_op
/-- Multiply-negate (alias of `msub Rd, Rn, Rm, xzr`). -/
syntax &"mneg" : aarch64_rrr_op
/-- Multiply high (upper 64 bits of the 128-bit product). -/
syntax_affixed (prefixes := signedness) "mulh" : aarch64_rrr_op
/-- Logical shift left by register. -/
syntax &"lslv" : aarch64_rrr_op
/-- Logical shift right by register. -/
syntax &"lsrv" : aarch64_rrr_op
/-- Arithmetic shift right by register. -/
syntax &"asrv" : aarch64_rrr_op
/-- Rotate right by register. -/
syntax &"rorv" : aarch64_rrr_op

/-- Multiply-accumulate mnemonics taking `(Rd, Rn, Rm, Ra)`. -/
declare_syntax_cat aarch64_madd_op (behavior := both)
/-- Multiply-add (`Rd ← Ra + Rn * Rm`). -/
syntax &"madd" : aarch64_madd_op
/-- Multiply-subtract (`Rd ← Ra - Rn * Rm`). -/
syntax &"msub" : aarch64_madd_op

/-- Widening multiply-accumulate mnemonics taking `(Xd, Wn, Wm, Xa)`. -/
declare_syntax_cat aarch64_maddl_op (behavior := both)
/-- Multiply-add long (`Xd ← Xa + Wn * Wm`). -/
syntax_affixed (prefixes := signedness) "maddl" : aarch64_maddl_op
/-- Multiply-subtract long (`Xd ← Xa - Wn * Wm`). -/
syntax_affixed (prefixes := signedness) "msubl" : aarch64_maddl_op

/-- Widening multiply mnemonics taking `(Xd, Wn, Wm)`. -/
declare_syntax_cat aarch64_mull_op (behavior := both)
/-- Multiply long (alias of `maddl Xd, Wn, Wm, xzr`). -/
syntax_affixed (prefixes := signedness) "mull" : aarch64_mull_op
/-- Multiply-negate long (alias of `msubl Xd, Wn, Wm, xzr`). -/
syntax_affixed (prefixes := signedness) "mnegl" : aarch64_mull_op

/-- Two-register bit manipulation mnemonics taking `(Rd, Rn)`. -/
declare_syntax_cat aarch64_rr_op (behavior := both)
/-- Count leading zeros. -/
syntax &"clz" : aarch64_rr_op
/-- Count leading sign bits. -/
syntax &"cls" : aarch64_rr_op
/-- Reverse bits. -/
syntax &"rbit" : aarch64_rr_op
/-- Reverse bytes. -/
syntax_affixed (suffixes := rev_width) "rev" : aarch64_rr_op

/-- Sign/zero extension mnemonics taking `(Rd, Wn)`. -/
declare_syntax_cat aarch64_extend_op (behavior := both)
/-- Extend into a wider register. -/
syntax_affixed (prefixes := signedness) (suffixes := ext_width) "xt" : aarch64_extend_op

/-- Shift/rotate mnemonics taking `(Rd, Rn, Rm or #imm)`. -/
declare_syntax_cat aarch64_shift_op (behavior := both)
syntax_affixed (suffixes := shift_kind) : aarch64_shift_op

declare_affixes bitfield_fill
  | /-- Other destination bits are left unchanged. -/ ""
  | /-- Other destination bits are sign-filled. -/     "s"
  | /-- Other destination bits are zero-filled. -/     "u"

/-- Bitfield mnemonics taking `(Rd, Rn, #imm, #imm)`. -/
declare_syntax_cat aarch64_bitfield_op (behavior := both)
/-- Bitfield move (`immr`, `imms`). -/
syntax_affixed (prefixes := bitfield_fill) "bfm" : aarch64_bitfield_op
/-- Bitfield extract (`lsb`, `width`). -/
syntax_affixed (prefixes := signedness) "bfx" : aarch64_bitfield_op
/-- Bitfield extract and insert at low end (`lsb`, `width`). -/
syntax &"bfxil" : aarch64_bitfield_op
/-- Bitfield insert (`lsb`, `width`). -/
syntax &"bfi" : aarch64_bitfield_op
/-- Bitfield insert in zeros (`lsb`, `width`). -/
syntax_affixed (prefixes := signedness) "bfiz" : aarch64_bitfield_op

/-- Conditional select mnemonics taking `(Rd, Rn, Rm, cond)`. -/
declare_syntax_cat aarch64_csel_op (behavior := both)
/-- Conditional select (`Rd ← cond ? Rn : Rm`). -/
syntax &"csel" : aarch64_csel_op
/-- Conditional select increment (`Rd ← cond ? Rn : Rm + 1`). -/
syntax &"csinc" : aarch64_csel_op
/-- Conditional select invert (`Rd ← cond ? Rn : ~Rm`). -/
syntax &"csinv" : aarch64_csel_op
/-- Conditional select negate (`Rd ← cond ? Rn : -Rm`). -/
syntax &"csneg" : aarch64_csel_op

/-- Conditional increment/invert/negate mnemonics taking `(Rd, Rn, cond)`. -/
declare_syntax_cat aarch64_cinc_op (behavior := both)
/-- Conditional increment (`Rd ← cond ? Rn + 1 : Rn`). -/
syntax &"cinc" : aarch64_cinc_op
/-- Conditional invert (`Rd ← cond ? ~Rn : Rn`). -/
syntax &"cinv" : aarch64_cinc_op
/-- Conditional negate (`Rd ← cond ? -Rn : Rn`). -/
syntax &"cneg" : aarch64_cinc_op

/-- Conditional set mnemonics taking `(Rd, cond)`. -/
declare_syntax_cat aarch64_cset_op (behavior := both)
/-- Conditional set (`Rd ← cond ? 1 : 0`). -/
syntax &"cset" : aarch64_cset_op
/-- Conditional set mask (`Rd ← cond ? -1 : 0`). -/
syntax &"csetm" : aarch64_cset_op

/-- Conditional compare mnemonics taking `(Rn, Rm or #imm, #nzcv, cond)`. -/
declare_syntax_cat aarch64_ccmp_op (behavior := both)
/-- Conditional compare (flags of `Rn - src` if `cond` holds, else `nzcv`). -/
syntax &"ccmp" : aarch64_ccmp_op
/-- Conditional compare negative (flags of `Rn + src` if `cond` holds, else `nzcv`). -/
syntax &"ccmn" : aarch64_ccmp_op

/-- Move wide mnemonics taking `(Rd, #imm16{, lsl #shift})`. -/
declare_syntax_cat aarch64_movw_op (behavior := both)
/-- Move a 16-bit immediate shifted into position. -/
syntax_affixed (suffixes := movw_kind) "mov" : aarch64_movw_op

/-- PC-relative address mnemonics taking `(Xd, label)`. -/
declare_syntax_cat aarch64_adr_op (behavior := both)
/-- Form PC-relative address (`±1 MB`). -/
syntax &"adr" : aarch64_adr_op
/-- Form PC-relative address of a 4 KB page (`±4 GB`). -/
syntax &"adrp" : aarch64_adr_op

/-- Unconditional branch mnemonics taking a target label or offset. -/
declare_syntax_cat aarch64_b_op (behavior := both)
/-- Branch. -/
syntax &"b" : aarch64_b_op
/-- Branch with link (`lr ← return address`). -/
syntax &"bl" : aarch64_b_op

/-- Indirect branch mnemonics taking a target register. -/
declare_syntax_cat aarch64_br_op (behavior := both)
/-- Branch to register. -/
syntax &"br" : aarch64_br_op
/-- Branch with link to register (`lr ← return address`). -/
syntax &"blr" : aarch64_br_op

/-- Compare-and-branch mnemonics taking `(Rt, label)`. -/
declare_syntax_cat aarch64_cbz_op (behavior := both)
/-- Compare register with zero and branch. -/
syntax_affixed (suffixes := zero_test) "cb" : aarch64_cbz_op

/-- Test-bit-and-branch mnemonics taking `(Rt, #bit, label)`. -/
declare_syntax_cat aarch64_tbz_op (behavior := both)
/-- Test a bit of the register and branch. -/
syntax_affixed (suffixes := zero_test) "tb" : aarch64_tbz_op

/-- Conditional branch mnemonics taking a target label or offset. -/
declare_syntax_cat aarch64_bcond_op (behavior := both)
/-- Conditional branch. -/
syntax_affixed (suffixes := cond) "b." : aarch64_bcond_op
/-- Conditional branch (undotted alias of `b.<cond>`). -/
syntax_affixed (suffixes := cond) "b" : aarch64_bcond_op

-- ============================================================================
-- Instruction, Directive & Program Syntax
-- ============================================================================

/-- AArch64 instruction statement with instruction-specific arity and operand categories. -/
declare_syntax_cat aarch64_instr (behavior := both)
syntax withPosition(aarch64_ldr_op lineEq aarch64_reg "," lineEq aarch64_load_src) : aarch64_instr
syntax withPosition(aarch64_ldur_op lineEq aarch64_reg "," lineEq aarch64_mem) : aarch64_instr
syntax withPosition(aarch64_str_op lineEq aarch64_reg "," lineEq aarch64_mem) : aarch64_instr
syntax withPosition(aarch64_stur_op lineEq aarch64_reg "," lineEq aarch64_mem) : aarch64_instr
syntax withPosition(aarch64_pair_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_mem) : aarch64_instr
syntax withPosition(aarch64_arith_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_src) : aarch64_instr
syntax withPosition(aarch64_cmp_op lineEq aarch64_reg "," lineEq aarch64_src) : aarch64_instr
syntax withPosition(aarch64_unary_op lineEq aarch64_reg "," lineEq aarch64_src) : aarch64_instr
syntax withPosition(aarch64_logic_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_src) : aarch64_instr
syntax withPosition(&"tst" lineEq aarch64_reg "," lineEq aarch64_src) : aarch64_instr
syntax withPosition(aarch64_rrr_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg) : aarch64_instr
syntax withPosition(aarch64_madd_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg) : aarch64_instr
syntax withPosition(aarch64_maddl_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg) : aarch64_instr
syntax withPosition(aarch64_mull_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg) : aarch64_instr
syntax withPosition(aarch64_rr_op lineEq aarch64_reg "," lineEq aarch64_reg) : aarch64_instr
syntax withPosition(aarch64_extend_op lineEq aarch64_reg "," lineEq aarch64_reg) : aarch64_instr
syntax withPosition(aarch64_shift_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg_or_imm) : aarch64_instr
syntax withPosition(&"extr" lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_imm) : aarch64_instr
syntax withPosition(aarch64_bitfield_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_imm "," lineEq aarch64_imm) : aarch64_instr
syntax withPosition(aarch64_csel_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_cond) : aarch64_instr
syntax withPosition(aarch64_cinc_op lineEq aarch64_reg "," lineEq aarch64_reg "," lineEq aarch64_cond) : aarch64_instr
syntax withPosition(aarch64_cset_op lineEq aarch64_reg "," lineEq aarch64_cond) : aarch64_instr
syntax withPosition(aarch64_ccmp_op lineEq aarch64_reg "," lineEq aarch64_reg_or_imm "," lineEq aarch64_imm "," lineEq aarch64_cond) : aarch64_instr
syntax withPosition(&"mov" lineEq aarch64_reg "," lineEq aarch64_reg_or_imm) : aarch64_instr
syntax withPosition(aarch64_movw_op lineEq aarch64_reg "," lineEq aarch64_const ("," lineEq aarch64_modifier)?) : aarch64_instr
syntax withPosition(aarch64_adr_op lineEq aarch64_reg "," lineEq aarch64_const) : aarch64_instr
syntax withPosition(aarch64_b_op lineEq aarch64_const) : aarch64_instr
syntax withPosition(aarch64_br_op lineEq aarch64_reg) : aarch64_instr
syntax withPosition(&"ret" (lineEq aarch64_reg)?) : aarch64_instr
syntax withPosition(aarch64_cbz_op lineEq aarch64_reg "," lineEq aarch64_const) : aarch64_instr
syntax withPosition(aarch64_tbz_op lineEq aarch64_reg "," lineEq aarch64_imm "," lineEq aarch64_const) : aarch64_instr
syntax withPosition(aarch64_bcond_op lineEq aarch64_const) : aarch64_instr
syntax &"nop" : aarch64_instr
syntax "${" term "}" : aarch64_instr

/-- AArch64 directive (label declaration, instruction, or Lean term antiquotation). -/
declare_syntax_cat aarch64_directive
syntax atomic(aarch64_ident ":") : aarch64_directive
syntax withPosition(aarch64_instr notFollowedBy(lineEq (aarch64_ident <|> "," <|> aarch64_imm))) : aarch64_directive
syntax "${" term "}" : aarch64_directive

/-- AArch64 assembly program (sequence of directives). -/
declare_syntax_cat aarch64_prog
syntax aarch64_directive* : aarch64_prog

end Kraken.AArch64.Parser
