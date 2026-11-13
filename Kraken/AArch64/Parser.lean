module

public import Kraken.AArch64.Parser.Syntax
public meta import Kraken.AArch64.Parser.Syntax
public import Kraken.AArch64.Parser.Elab
public meta import Kraken.AArch64.Parser.Elab
public import Kraken.AArch64.Parser.Delab
public meta import Kraken.AArch64.Parser.Delab

/-!
AArch64 assembly parser and embedded Lean syntax (`⸨prog| ...⸩`, `⸨dir| ... ⸩`, `⸨dir n | ... ⸩`).

See `Kraken.AArch64.Parser.Syntax` for the grammar and `Kraken.AArch64.Parser.Elab` for operand-width
inference, antiquotation types, and elaborator disambiguation rules.
-/

namespace Kraken.AArch64.Parser

open Lean Elab Term Kraken.Parser

/-- Inline unquoted AArch64 assembly directive elaborator (`⸨dir| ... ⸩`). -/
elab_rules : term
  | `(⸨dir| $d:aarch64_directive⸩) => elabDirective d

macro_rules
  | `(⸨dir $n | $dir:aarch64_directive⸩) =>
    `({directive := ⸨dir| $dir⸩, size := Kraken.Layout.size _root_.Instr _root_.ConstExpr $n : Kraken.Sized _root_.Directive})

/-- Inline unquoted AArch64 assembly block elaborator (`⸨prog| ...⸩`). -/
elab_rules : term
  | `(⸨prog| $p:aarch64_prog⸩) => elabProgram p

/-- Standalone embeddings of the elements of a program:
    * `⸨instr| ... ⸩ : Instr`
    * `⸨mem| ... ⸩ : AddrExpr`, or `UnscaledAddrExpr` (`ldur`/`stur` operands) when that is the expected
      type. See `elabAddrExpr` for how an `AddrExpr` is elaborated without knowing its access size.
    * `⸨reg| ... ⸩ : RegOrZr w`, or `RegOrSp w` for `sp`/`wsp` or when that is the expected type
    * `⸨const| ... ⸩ : ConstExpr`
    * `⸨cc| ... ⸩ : CondCode`

    Registers take their width from their name, from the type of an antiquotation, or else from the
    expected type. -/
elab_rules : term <= expectedType?
  | `(⸨instr| $i:aarch64_instr ⸩) => do
    let i ← i.raw.replaceM resolveRegOrConstChoice
    ensureHasType expectedType? (← (elabInstr ⟨i⟩).run')
  | `(⸨mem| $m:aarch64_mem ⸩) => do
    let m : TSyntax `aarch64_mem := ⟨← m.raw.replaceM resolveRegOrConstChoice⟩
    if ← isAppOfType ``UnscaledAddrExpr expectedType? then
      elabEmbedding (elabUnscaledMem m) expectedType? (widthIndexed := false)
    else
      elabEmbedding (elabAddrExpr m) expectedType? (widthIndexed := false)
  | `(⸨reg| $r:aarch64_reg ⸩) => do
    let sp := isSpSyntax r || (← isAppOfType ``RegOrSp expectedType?)
    elabEmbedding (elabReg r sp) expectedType?
  | `(⸨const| $c:aarch64_const ⸩) => do ensureHasType expectedType? (← elabConst c)
  | `(⸨cc| $c:aarch64_cond ⸩) => do ensureHasType expectedType? (← elabCond c)

/-- Read an AArch64 assembly file, strip assembler directives, parse via `runParserCategory`,
    and elaborate into a Kraken `Program`. -/
elab "include_aarch64 " path:str : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabAArch64 (stripDirectives content)

/-- Function-call style `include_aarch64("path")` alias. -/
elab "include_aarch64(" path:str ")" : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabAArch64 (stripDirectives content)
end Kraken.AArch64.Parser
