module

public import Lean

open Lean Parser

namespace Kraken.X64.Parser

-- ============================================================================
-- Lexical Token Scanner
-- ============================================================================

public meta section

/-- X64 assembly identifier (`[a-zA-Z_.][a-zA-Z0-9_.]*`), defined via Lean's character combinators. -/
def x64IdentToken : Parser := {
  fn := rawFn (satisfyFn (fun c => c.isAlpha || c == '_' || c == '.') "identifier" >>
               takeWhileFn (fun c => c.isAlphanum || c == '_' || c == '.'))
              (trailingWs := true)
}

@[combinator_formatter x64IdentToken]
def x64IdentToken.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer x64IdentToken]
def x64IdentToken.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken

end

-- ============================================================================
-- Syntax Categories & Productions
-- ============================================================================

/-- X64 assembly identifier (`main`, `and`, `.LBB0_1`, `aa.1.aa.1`, `.L.str.1.llvm.12345`). -/
declare_syntax_cat x64_ident
syntax x64IdentToken : x64_ident

/-- X64 constant expression (signed or unsigned integer, symbol with `+` or `-` offset). -/
declare_syntax_cat x64_const
syntax num : x64_const
syntax "-" num : x64_const
syntax "+" num : x64_const
syntax x64_ident "+" num : x64_const
syntax x64_ident "-" num : x64_const
syntax x64_ident : x64_const

/-- X64 register operand (`%rax`, `%eax`, `%ax`, `%al`, `%ah`, `%rip`, `%xmm0`..`%zmm31`). -/
declare_syntax_cat x64_reg
-- 64-bit general-purpose registers
syntax "%rax" : x64_reg
syntax "%rbx" : x64_reg
syntax "%rcx" : x64_reg
syntax "%rdx" : x64_reg
syntax "%rsi" : x64_reg
syntax "%rdi" : x64_reg
syntax "%rsp" : x64_reg
syntax "%rbp" : x64_reg
syntax "%r8"  : x64_reg
syntax "%r9"  : x64_reg
syntax "%r10" : x64_reg
syntax "%r11" : x64_reg
syntax "%r12" : x64_reg
syntax "%r13" : x64_reg
syntax "%r14" : x64_reg
syntax "%r15" : x64_reg
-- 32-bit general-purpose aliases
syntax "%eax" : x64_reg
syntax "%ebx" : x64_reg
syntax "%ecx" : x64_reg
syntax "%edx" : x64_reg
syntax "%esi" : x64_reg
syntax "%edi" : x64_reg
syntax "%esp" : x64_reg
syntax "%ebp" : x64_reg
syntax "%r8d"  : x64_reg
syntax "%r9d"  : x64_reg
syntax "%r10d" : x64_reg
syntax "%r11d" : x64_reg
syntax "%r12d" : x64_reg
syntax "%r13d" : x64_reg
syntax "%r14d" : x64_reg
syntax "%r15d" : x64_reg
-- 16-bit general-purpose aliases
syntax "%ax" : x64_reg
syntax "%bx" : x64_reg
syntax "%cx" : x64_reg
syntax "%dx" : x64_reg
syntax "%si" : x64_reg
syntax "%di" : x64_reg
syntax "%sp" : x64_reg
syntax "%bp" : x64_reg
syntax "%r8w"  : x64_reg
syntax "%r9w"  : x64_reg
syntax "%r10w" : x64_reg
syntax "%r11w" : x64_reg
syntax "%r12w" : x64_reg
syntax "%r13w" : x64_reg
syntax "%r14w" : x64_reg
syntax "%r15w" : x64_reg
-- 8-bit low general-purpose aliases
syntax "%al"  : x64_reg
syntax "%bl"  : x64_reg
syntax "%cl"  : x64_reg
syntax "%dl"  : x64_reg
syntax "%sil" : x64_reg
syntax "%dil" : x64_reg
syntax "%spl" : x64_reg
syntax "%bpl" : x64_reg
syntax "%r8b"  : x64_reg
syntax "%r9b"  : x64_reg
syntax "%r10b" : x64_reg
syntax "%r11b" : x64_reg
syntax "%r12b" : x64_reg
syntax "%r13b" : x64_reg
syntax "%r14b" : x64_reg
syntax "%r15b" : x64_reg
-- 8-bit high general-purpose aliases
syntax "%ah" : x64_reg
syntax "%bh" : x64_reg
syntax "%ch" : x64_reg
syntax "%dh" : x64_reg
-- Instruction pointer register
syntax "%rip" : x64_reg
-- 128-bit XMM registers (`%xmm0`..`%xmm31`)
syntax "%xmm0"  : x64_reg
syntax "%xmm1"  : x64_reg
syntax "%xmm2"  : x64_reg
syntax "%xmm3"  : x64_reg
syntax "%xmm4"  : x64_reg
syntax "%xmm5"  : x64_reg
syntax "%xmm6"  : x64_reg
syntax "%xmm7"  : x64_reg
syntax "%xmm8"  : x64_reg
syntax "%xmm9"  : x64_reg
syntax "%xmm10" : x64_reg
syntax "%xmm11" : x64_reg
syntax "%xmm12" : x64_reg
syntax "%xmm13" : x64_reg
syntax "%xmm14" : x64_reg
syntax "%xmm15" : x64_reg
syntax "%xmm16" : x64_reg
syntax "%xmm17" : x64_reg
syntax "%xmm18" : x64_reg
syntax "%xmm19" : x64_reg
syntax "%xmm20" : x64_reg
syntax "%xmm21" : x64_reg
syntax "%xmm22" : x64_reg
syntax "%xmm23" : x64_reg
syntax "%xmm24" : x64_reg
syntax "%xmm25" : x64_reg
syntax "%xmm26" : x64_reg
syntax "%xmm27" : x64_reg
syntax "%xmm28" : x64_reg
syntax "%xmm29" : x64_reg
syntax "%xmm30" : x64_reg
syntax "%xmm31" : x64_reg
-- 256-bit YMM registers (`%ymm0`..`%ymm31`)
syntax "%ymm0"  : x64_reg
syntax "%ymm1"  : x64_reg
syntax "%ymm2"  : x64_reg
syntax "%ymm3"  : x64_reg
syntax "%ymm4"  : x64_reg
syntax "%ymm5"  : x64_reg
syntax "%ymm6"  : x64_reg
syntax "%ymm7"  : x64_reg
syntax "%ymm8"  : x64_reg
syntax "%ymm9"  : x64_reg
syntax "%ymm10" : x64_reg
syntax "%ymm11" : x64_reg
syntax "%ymm12" : x64_reg
syntax "%ymm13" : x64_reg
syntax "%ymm14" : x64_reg
syntax "%ymm15" : x64_reg
syntax "%ymm16" : x64_reg
syntax "%ymm17" : x64_reg
syntax "%ymm18" : x64_reg
syntax "%ymm19" : x64_reg
syntax "%ymm20" : x64_reg
syntax "%ymm21" : x64_reg
syntax "%ymm22" : x64_reg
syntax "%ymm23" : x64_reg
syntax "%ymm24" : x64_reg
syntax "%ymm25" : x64_reg
syntax "%ymm26" : x64_reg
syntax "%ymm27" : x64_reg
syntax "%ymm28" : x64_reg
syntax "%ymm29" : x64_reg
syntax "%ymm30" : x64_reg
syntax "%ymm31" : x64_reg
-- 512-bit ZMM registers (`%zmm0`..`%zmm31`)
syntax "%zmm0"  : x64_reg
syntax "%zmm1"  : x64_reg
syntax "%zmm2"  : x64_reg
syntax "%zmm3"  : x64_reg
syntax "%zmm4"  : x64_reg
syntax "%zmm5"  : x64_reg
syntax "%zmm6"  : x64_reg
syntax "%zmm7"  : x64_reg
syntax "%zmm8"  : x64_reg
syntax "%zmm9"  : x64_reg
syntax "%zmm10" : x64_reg
syntax "%zmm11" : x64_reg
syntax "%zmm12" : x64_reg
syntax "%zmm13" : x64_reg
syntax "%zmm14" : x64_reg
syntax "%zmm15" : x64_reg
syntax "%zmm16" : x64_reg
syntax "%zmm17" : x64_reg
syntax "%zmm18" : x64_reg
syntax "%zmm19" : x64_reg
syntax "%zmm20" : x64_reg
syntax "%zmm21" : x64_reg
syntax "%zmm22" : x64_reg
syntax "%zmm23" : x64_reg
syntax "%zmm24" : x64_reg
syntax "%zmm25" : x64_reg
syntax "%zmm26" : x64_reg
syntax "%zmm27" : x64_reg
syntax "%zmm28" : x64_reg
syntax "%zmm29" : x64_reg
syntax "%zmm30" : x64_reg
syntax "%zmm31" : x64_reg

/-- X64 immediate operand (`$42`, `$-1`, `$sym`, `$sym+8`). -/
declare_syntax_cat x64_imm
syntax "$" x64_const : x64_imm

/-- X64 memory addressing operand (`disp(%base, %idx, scale)` or bare displacement). -/
declare_syntax_cat x64_mem
syntax "(" x64_reg ")" : x64_mem
syntax x64_const "(" x64_reg ")" : x64_mem
syntax "(" x64_reg "," x64_reg ")" : x64_mem
syntax x64_const "(" x64_reg "," x64_reg ")" : x64_mem
syntax "(" x64_reg "," x64_reg "," num ")" : x64_mem
syntax x64_const "(" x64_reg "," x64_reg "," num ")" : x64_mem
syntax x64_const : x64_mem

/-- X64 general instruction operand (register, immediate, memory, or Lean term antiquotation). -/
declare_syntax_cat x64_operand
syntax x64_reg : x64_operand
syntax x64_imm : x64_operand
syntax "${" term "}" : x64_operand
syntax x64_mem : x64_operand
syntax x64_operand "+" num : x64_operand
syntax x64_operand "-" num : x64_operand

/-- X64 instruction statement. -/
declare_syntax_cat x64_instr
syntax withPosition(x64_ident notFollowedBy(":") (lineEq x64_operand),*) : x64_instr
syntax "${" term "}" : x64_instr

/-- X64 directive (label declaration, instruction, or Lean term antiquotation). -/
declare_syntax_cat x64_directive
syntax x64_ident ":" : x64_directive
syntax x64_ident ":" ";" : x64_directive
syntax x64_instr ";" : x64_directive
syntax withPosition(x64_instr notFollowedBy(lineEq x64_ident)) : x64_directive
syntax "${" term "}" ";" : x64_directive
syntax "${" term "}" : x64_directive

/-- X64 assembly program (sequence of directives). -/
declare_syntax_cat x64_prog
syntax x64_directive* : x64_prog

end Kraken.X64.Parser
