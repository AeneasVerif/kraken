module

public import Kraken.X64.Parser.Syntax
public meta import Kraken.X64.Parser.Syntax
public import Kraken.X64.Parser.Elab
public meta import Kraken.X64.Parser.Elab
public import Kraken.X64.Parser.Delab
public meta import Kraken.X64.Parser.Delab

namespace Kraken.X64.Parser

open Lean Elab Term Kraken.Parser

/-- Inline unquoted X64 assembly directive elaborator (`⸨dir| ... ⸩`). -/
elab_rules : term
  | `(⸨dir| $d:x64_directive⸩) => elabDirective d

macro_rules
  | `(⸨dir $n | $dir:x64_directive⸩) =>
    `({directive := ⸨dir| $dir⸩, size := Kraken.Layout.size _root_.Instr _root_.ConstExpr $n : Kraken.Sized _root_.Directive})

/-- Inline unquoted X64 assembly block elaborator (`⸨prog| ...⸩`). -/
elab_rules : term
  | `(⸨prog| $p:x64_prog⸩) => elabProgram p

/-- Standalone embeddings of the elements of a program:
    * `⸨instr| ... ⸩ : Instr`
    * `⸨operand| ... ⸩ : Operand w`
    * `⸨mem| ... ⸩ : AddrExpr`. An `AddrExpr` only holds 64-bit registers: the address width that the
      registers of a memory operand determine (`0(%eax)` is a 32-bit address) is part of the
      instruction (`Instr.regular`), so it is dropped here, and `⸨mem| 0(%eax) ⸩ = ⸨mem| 0(%rax) ⸩`.
    * `⸨reg| ... ⸩ : Reg w` for general-purpose registers and `AvxReg w` for AVX registers
    * `⸨const| ... ⸩ : ConstExpr`

    Width-indexed results take their width from their registers, from the type of an antiquotation, or
    else from the expected type (`(⸨operand| $1 ⸩ : Operand .W64)`). -/
elab_rules : term <= expectedType?
  | `(⸨instr| $i:x64_instr ⸩) => do ensureHasType expectedType? (← elabInstr i)
  | `(⸨operand| $o:x64_operand ⸩) => elabEmbedding Width (elabOperand o) expectedType?
  | `(⸨mem| $m:x64_mem ⸩) => elabEmbedding Width (elabMem m) expectedType? (widthIndexed := false)
  | `(⸨reg| $r:x64_reg ⸩) => elabEmbedding Width (elabReg r) expectedType?
  | `(⸨reg| $r:x64_avx_reg ⸩) => elabEmbedding AvxWidth (elabAvxReg r) expectedType?
  | `(⸨const| $c:x64_const ⸩) => do ensureHasType expectedType? (← elabConstExpr c)

/-- Read an X64 assembly file, strip assembler directives, parse via `runParserCategory`,
    and elaborate into a Kraken `Program`. -/
elab "include_x64" path:str : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabX64 (stripDirectives content)

end Kraken.X64.Parser
