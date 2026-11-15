module

public import Kraken.X64.Parser.Syntax
public meta import Kraken.X64.Parser.Syntax
public meta import Lean

/-!
Elaborators of the X64 syntax categories that are not written with `notation ... in c`:
identifiers, constants, `disp(%rip)` memory operands and relative jump targets (issue 5 of
`Kraken/X64/Parser/design.md`). The rules of `Kraken.X64.Parser.Rules` substitute nodes of these
categories into their right-hand sides, so each of their syntax kinds has a term elaborator.
-/

namespace Kraken.X64.Parser
open Lean Meta Elab Kraken.Parser
open Term hiding mkConst  -- `mkConst` is the pure `Lean.mkConst`, not the environment lookup `Term.mkConst`

public meta section

/-- Elaborate the term `t` of an antiquotation at the type `ty` expected by its position. -/
def elabAntiquot (t : Term) (ty : Expr) : TermElabM Expr :=
  withoutErrToSorry <| withSynthesize <| elabTermEnsuringType t ty

/-- Elaborate an `x64_ident` syntax node into an `Expr` of type `Label`. -/
def elabIdent (stx : TSyntax `x64_ident) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_ident| ❰ $t ❱) => elabAntiquot t (mkConst ``Label)
  | _ => return toExpr (← getAsmIdent stx)

def elabConstExprIdent (id : TSyntax `x64_ident) : TermElabM Expr :=
  return (mkApp (mkConst ``ConstExpr.label) <| ← elabIdent id)

/-- Elaborate an `x64_const` syntax node into an `Expr` of type `ConstExpr`. -/
def elabConstExpr (stx : TSyntax `x64_const) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_const| ❰ $t ❱) => elabAntiquot t (mkConst ``ConstExpr)
  | `(x64_const| +$n:num)
  | `(x64_const| $n:num) =>
    let i ← Int64.ofNatNoOverflow n.getNat
    pure (toExpr (ConstExpr.int64 i))
  | `(x64_const| -$n:num) =>
    let i ← Int64.ofIntNoOverflow (-(Int.ofNat n.getNat))
    pure (toExpr (ConstExpr.int64 i))
  | `(x64_const| $id:x64_ident + $n:num) =>
    let s ← elabConstExprIdent id
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    pure (mkApp2 (mkConst ``ConstExpr.add) s (toExpr (ConstExpr.int64 i)))
  | `(x64_const| $id:x64_ident - $n:num) =>
    let s ← elabConstExprIdent id
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    pure (mkApp2 (mkConst ``ConstExpr.sub) s (toExpr (ConstExpr.int64 i)))
  | `(x64_const| $a:x64_ident - $b:x64_ident) =>
    pure (mkApp2 (mkConst ``ConstExpr.sub) (← elabConstExprIdent a) (← elabConstExprIdent b))
  | `(x64_const| $id:x64_ident) =>
    elabConstExprIdent id
  | _ => throwError "invalid constant expression"

@[term_elab x64_ident_, term_elab x64_ident.escape]
def elabIdentTerm : TermElab := fun stx _ => elabIdent ⟨stx⟩

@[term_elab x64_const.num, term_elab x64_const.neg, term_elab x64_const.pos,
  term_elab x64_const.add, term_elab x64_const.sub, term_elab x64_const.diff,
  term_elab x64_const.label, term_elab x64_const.escape]
def elabConstTerm : TermElab := fun stx _ => elabConstExpr ⟨stx⟩

@[term_elab x64_const.entry]
def elabConstEntry : TermElab := fun stx _ => elabConstExpr ⟨stx[1]⟩

/-- `disp(%rip)`: a numeral is the displacement itself; any other constant is an address, from
which the address of the next instruction is subtracted. -/
@[term_elab x64_memory.rip]
def elabRipMemory : TermElab := fun stx _ => withRef stx do
  let disp ← match stx[0].getOptional? with
    | some d =>
      let d ← elabConstExpr ⟨d⟩
      if d.isAppOfArity ``ConstExpr.int64 1 then pure d
      else pure (mkApp2 (mkConst ``ConstExpr.sub) d (mkConst ``ConstExpr.after_current_instruction))
    | none => pure (toExpr (ConstExpr.int64 0))
  return mkApp3 (mkConst ``AddrExpr.mk) (toExpr (some RegOrRip.rip))
    (toExpr (none : Option AddrIndex)) disp

/-- A label as a jump target, relative to the next instruction. -/
@[term_elab x64_jump_target.rel]
def elabRelTarget : TermElab := fun stx _ => withRef stx do
  let lbl ← elabIdent ⟨stx[0]⟩
  return mkApp (mkConst ``RelRegOrMem.rel) <|
    mkApp2 (mkConst ``ConstExpr.sub) (mkApp (mkConst ``ConstExpr.label) lbl)
      (mkConst ``ConstExpr.after_current_instruction)

end

end Kraken.X64.Parser
