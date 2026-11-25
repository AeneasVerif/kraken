module

public import LeanQbe.T.Frontend.C0.Syntax
public import LeanQbe.T.Frontend.C0.Lexer
public import LeanQbe.T.Frontend.C0.Parser
public import LeanQbe.T.Frontend.C0.Layout
public import LeanQbe.T.Frontend.C0.Lower
public import LeanQbe.T.Frontend.C0.Elab
public import LeanQbe.T.Frontend.C0.ToFlat
public import LeanQbe.T.Frontend.C0.LayoutElab

set_option autoImplicit false

/-!
# C0 Frontend for `LeanQbe.T`

Umbrella module re-exporting the untrusted, shape-stable, PHOAS-first C0 frontend:
* `Syntax`: C0 AST
* `Lexer`: C0 tokenizer, preprocessor (`#define` incl. parameterized/variadic, `#undef`,
  `#if`/`#ifdef`/`#ifndef`, `#include`, `#pragma c0_*`)
* `Parser`: `parseC0 : String → Std.HashMap String String → Except String C0.TranslationUnit`
* `Layout`: SysV LP64 struct, union, LSB-first bitfield layout, `offsetof`, `_Static_assert`
* `Lower`: shape-stable SSA/join-point lowering, `#c0_shape` metadata, and `promoteExitCalls`
* `Elab`: direct PHOAS `Lean.Expr` elaborator, `c0_header!`, `c0_decl!`, `c0_file!`,
  `#c0_shape`, `#c0_audit`
* `ToFlat`: `LExpr → TFlat` bridge (`LFlatCtx`, `TFlatFn`, `compileC0Source`)
* `LayoutElab`: `c0_layout_lemmas!` struct footprints and `c0_load`/`c0_store` field lemmas
-/
