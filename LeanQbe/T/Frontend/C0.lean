module

public import LeanQbe.T.Frontend.C0.Syntax
public import LeanQbe.T.Frontend.C0.Parser
public import LeanQbe.T.Frontend.C0.Layout
public import LeanQbe.T.Frontend.C0.Lower
public import LeanQbe.T.Frontend.C0.Elab

/-!
# C0 Frontend for `LeanQbe.T` (`X0-core`)

Umbrella module re-exporting the untrusted, shape-stable, PHOAS-first C0 frontend:
* `Syntax`: C0 AST
* `Parser`: `parseC0 : String → Except String C0.TranslationUnit`
* `Layout`: SysV LP64 struct, union, and LSB-first bitfield layout
* `Lower`: shape-stable SSA/join-point lowering & `#c0_shape` metadata
* `Elab`: direct PHOAS `Lean.Expr` elaborator, `c0_decl!`, `c0_file!`, and `#c0_shape`
-/
