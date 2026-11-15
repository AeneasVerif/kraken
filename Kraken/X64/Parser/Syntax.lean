module

public import Kraken.Parser
public meta import Kraken.Parser
public import Kraken.CatNotation
public meta import Kraken.CatNotation
public import Kraken.X64.Syntax
public meta import Kraken.X64.Syntax

/-!
The parts of the X64 syntax that are not written with `notation ... in c` (see
`Kraken/X64/Parser/design.md`): identifiers, constants, `disp(%rip)` memory operands and relative
jump targets (issue 5), and the syntax categories that the rules in `Kraken.X64.Parser.Rules` use.

The elaborators of these categories are in `Kraken.X64.Parser.Elab` and their delaborators in
`Kraken.X64.Parser.Delab`. They connect to `notation ... in c` through the names it looks up:
`c.entry` (the embedding of category `c`), and the builders `c.entry.mk`, `c.escape.mk` and
`c.ofIdent`.
-/

open Lean Kraken.Parser

-- The categories, kinds and builders are not in a namespace: `notation ... in c` looks them up
-- by the category's name.
public meta section

-- ============================================================================
-- Identifiers and constants
-- ============================================================================

/-- X64 assembly identifier (`main`, `and`, `.LBB0_1`, `aa.1.aa.1`, `.L.str.1.llvm.12345`). -/
declare_syntax_cat x64_ident
syntax asmIdentToken : x64_ident
/-- Label antiquotation -/
syntax (name := x64_ident.escape) (priority := low) "❰" term "❱" : x64_ident

/-- X64 constant expression (signed or unsigned integer, symbol with `+` or `-` offset). -/
declare_syntax_cat x64_const
syntax (name := x64_const.num) num : x64_const
syntax (name := x64_const.neg) "-" num : x64_const
syntax (name := x64_const.pos) "+" num : x64_const
syntax (name := x64_const.add) x64_ident "+" num : x64_const
syntax (name := x64_const.sub) x64_ident "-" num : x64_const
syntax (name := x64_const.diff) x64_ident "-" x64_ident : x64_const
syntax (name := x64_const.label) x64_ident : x64_const
/-- Constant expression antiquotation -/
syntax (name := x64_const.escape) (priority := default - 1) "❰" term "❱" : x64_const

/-- Embedding of constant expressions (`⸨const| lbl+8 ⸩ : ConstExpr`). -/
syntax (name := x64_const.entry) "⸨const| " x64_const " ⸩" : term

def x64_const.entry.mk (c : Syntax) : Syntax :=
  mkNode ``x64_const.entry #[mkAtom "⸨const| ", c, mkAtom " ⸩"]
def x64_const.escape.mk (t : Syntax) : Syntax :=
  mkNode ``x64_const.escape #[mkAtom "❰", t, mkAtom "❱"]
def x64_ident.escape.mk (t : Syntax) : Syntax :=
  mkNode ``x64_ident.escape #[mkAtom "❰", t, mkAtom "❱"]
/-- A label (a string, shown as an identifier by `notation ... in c`) as an `x64_ident`. -/
def x64_ident.ofIdent (id : Syntax) : Syntax :=
  mkNode ``x64_ident_ #[mkAtom (id.getId.toString (escape := false))]

-- ============================================================================
-- Categories used by the rules
-- ============================================================================

/-! One category per operation width for registers, register-or-memory operands, operands and
operations (issue 8); these are declared in `Rules.lean`. -/

declare_syntax_cat x64_base
declare_syntax_cat x64_index
declare_syntax_cat x64_memory
declare_syntax_cat x64_shift_count
declare_syntax_cat x64_jump_target

/-- `disp(%rip)`: a numeral is the displacement itself, any other constant an address, from
which the address of the next instruction is subtracted (issue 5). -/
syntax (name := x64_memory.rip) (x64_const)? "(" "%" noWs &"rip" ")" : x64_memory

/-- A label as a jump target, relative to the next instruction. -/
syntax (name := x64_jump_target.rel) x64_ident : x64_jump_target

end
