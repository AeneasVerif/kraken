module

public import Lean

open Lean Parser

namespace Kraken.AArch64.Parser

-- ============================================================================
-- Lexical Token Scanner
-- ============================================================================

public meta section

/-- AArch64 assembly identifier (`[a-zA-Z_.][a-zA-Z0-9_.]*`), defined via Lean's character combinators. -/
def aarch64IdentToken : Parser := {
  fn := rawFn (satisfyFn (fun c => c.isAlpha || c == '_' || c == '.') "identifier" >>
               takeWhileFn (fun c => c.isAlphanum || c == '_' || c == '.'))
              (trailingWs := true)
}

@[combinator_formatter aarch64IdentToken]
def aarch64IdentToken.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer aarch64IdentToken]
def aarch64IdentToken.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken

end

-- ============================================================================
-- Syntax Categories & Productions
-- ============================================================================

/-- AArch64 assembly identifier (`main`, `b.eq`, `.LBB0_1`, `aa.1.aa.1`, `.L.str.1.llvm.12345`). -/
declare_syntax_cat aarch64_ident
syntax aarch64IdentToken : aarch64_ident

/-- AArch64 register (`x0`..`x30`, `lr`, `w0`..`w30`, `sp`, `wsp`, `xzr`, `wzr`). -/
declare_syntax_cat aarch64_reg
-- 64-bit general-purpose registers & alias
syntax "x0"  : aarch64_reg
syntax "x1"  : aarch64_reg
syntax "x2"  : aarch64_reg
syntax "x3"  : aarch64_reg
syntax "x4"  : aarch64_reg
syntax "x5"  : aarch64_reg
syntax "x6"  : aarch64_reg
syntax "x7"  : aarch64_reg
syntax "x8"  : aarch64_reg
syntax "x9"  : aarch64_reg
syntax "x10" : aarch64_reg
syntax "x11" : aarch64_reg
syntax "x12" : aarch64_reg
syntax "x13" : aarch64_reg
syntax "x14" : aarch64_reg
syntax "x15" : aarch64_reg
syntax "x16" : aarch64_reg
syntax "x17" : aarch64_reg
syntax "x18" : aarch64_reg
syntax "x19" : aarch64_reg
syntax "x20" : aarch64_reg
syntax "x21" : aarch64_reg
syntax "x22" : aarch64_reg
syntax "x23" : aarch64_reg
syntax "x24" : aarch64_reg
syntax "x25" : aarch64_reg
syntax "x26" : aarch64_reg
syntax "x27" : aarch64_reg
syntax "x28" : aarch64_reg
syntax "x29" : aarch64_reg
syntax "x30" : aarch64_reg
syntax "lr"  : aarch64_reg
-- 32-bit general-purpose registers
syntax "w0"  : aarch64_reg
syntax "w1"  : aarch64_reg
syntax "w2"  : aarch64_reg
syntax "w3"  : aarch64_reg
syntax "w4"  : aarch64_reg
syntax "w5"  : aarch64_reg
syntax "w6"  : aarch64_reg
syntax "w7"  : aarch64_reg
syntax "w8"  : aarch64_reg
syntax "w9"  : aarch64_reg
syntax "w10" : aarch64_reg
syntax "w11" : aarch64_reg
syntax "w12" : aarch64_reg
syntax "w13" : aarch64_reg
syntax "w14" : aarch64_reg
syntax "w15" : aarch64_reg
syntax "w16" : aarch64_reg
syntax "w17" : aarch64_reg
syntax "w18" : aarch64_reg
syntax "w19" : aarch64_reg
syntax "w20" : aarch64_reg
syntax "w21" : aarch64_reg
syntax "w22" : aarch64_reg
syntax "w23" : aarch64_reg
syntax "w24" : aarch64_reg
syntax "w25" : aarch64_reg
syntax "w26" : aarch64_reg
syntax "w27" : aarch64_reg
syntax "w28" : aarch64_reg
syntax "w29" : aarch64_reg
syntax "w30" : aarch64_reg
-- Stack pointer & zero registers
syntax "sp"  : aarch64_reg
syntax "wsp" : aarch64_reg
syntax "xzr" : aarch64_reg
syntax "wzr" : aarch64_reg

/-- AArch64 constant expression (signed/unsigned integer, relocation modifier, or non-register symbol). -/
declare_syntax_cat aarch64_const
syntax num : aarch64_const
syntax "#" num : aarch64_const
syntax "-" num : aarch64_const
syntax "#" "-" num : aarch64_const
syntax "+" num : aarch64_const
syntax "#" "+" num : aarch64_const
syntax ":" aarch64_ident ":" aarch64_const : aarch64_const
syntax "#" ":" aarch64_ident ":" aarch64_const : aarch64_const
syntax notFollowedBy(aarch64_reg) aarch64_ident : aarch64_const

/-- AArch64 bracketed memory addressing operand (`[base]`, `[base, #imm]!`, `[base], #imm`, `[base, Rm, ext #amt]`). -/
declare_syntax_cat aarch64_mem
syntax withPosition("[" aarch64_reg "]" "," lineEq aarch64_const) : aarch64_mem
syntax "[" aarch64_reg "]" : aarch64_mem
syntax "[" aarch64_reg "," aarch64_reg "," aarch64_ident "," aarch64_const "]" : aarch64_mem
syntax "[" aarch64_reg "," aarch64_reg "," aarch64_ident aarch64_const "]" : aarch64_mem
syntax "[" aarch64_reg "," aarch64_reg "," aarch64_ident "]" : aarch64_mem
syntax "[" aarch64_reg "," aarch64_reg "]" : aarch64_mem
syntax "[" aarch64_reg "," aarch64_const "]" "!" : aarch64_mem
syntax "[" aarch64_reg "," aarch64_const "]" : aarch64_mem

/-- AArch64 instruction operand (register, memory operand, literal pool `=expr`, shift/extend modifier, constant, or Lean antiquotation). -/
declare_syntax_cat aarch64_operand
syntax aarch64_mem : aarch64_operand
syntax "=" aarch64_const : aarch64_operand
syntax withPosition(notFollowedBy(aarch64_reg) aarch64_ident lineEq aarch64_const) : aarch64_operand
syntax aarch64_reg : aarch64_operand
syntax aarch64_const : aarch64_operand
syntax "${" term "}" : aarch64_operand

/-- AArch64 instruction statement. -/
declare_syntax_cat aarch64_instr
syntax withPosition(aarch64_ident notFollowedBy(":") (lineEq aarch64_operand),* notFollowedBy(lineEq aarch64_ident)) : aarch64_instr
syntax "${" term "}" : aarch64_instr

/-- AArch64 directive (label declaration, instruction, or Lean term antiquotation). -/
declare_syntax_cat aarch64_directive
syntax aarch64_ident ":" : aarch64_directive
syntax aarch64_instr : aarch64_directive
syntax "${" term "}" : aarch64_directive

/-- AArch64 assembly program (sequence of directives). -/
declare_syntax_cat aarch64_prog
syntax aarch64_directive* : aarch64_prog

end Kraken.AArch64.Parser
