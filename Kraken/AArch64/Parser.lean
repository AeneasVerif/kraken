module

public import Kraken.AArch64.Parser.Basic
public meta import Kraken.AArch64.Parser.Basic
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
