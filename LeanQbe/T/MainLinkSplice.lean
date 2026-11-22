module

public import LeanQbe.T.MainLink
public meta import Lean
public meta import LeanQbe.T.MainLink

/-!
# Meta Chunk Literal Splicing (`splice_chunk_literals`)

Command elaborator evaluating `compileModule` and `sigBoundsOf` in the meta interpreter via
`Lean.ToExpr` + `unsafe evalExpr` and emitting pure literal kernel definitions for `code`,
`bounds`, and `sigBounds`. Used alongside `compileCheckedLit` in `MainLink.lean` so downstream
`sigBounds`, `checkLink`, and `checkLinkList` inspect pure literals and never re-evaluate
`compileModule` in the kernel. Kept separate from `MainLink.lean` so `MainLink` stays
`Lean`-meta-free.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section
open Lean Elab Command Term Meta

instance : Lean.ToExpr Fmt where
  toTypeExpr := mkConst ``LeanQbe.T.Fmt
  toExpr
    | .h => mkConst ``LeanQbe.T.Fmt.h
    | .s => mkConst ``LeanQbe.T.Fmt.s
    | .d => mkConst ``LeanQbe.T.Fmt.d
    | .q => mkConst ``LeanQbe.T.Fmt.q

partial def tyToExpr : Ty → Lean.Expr
  | .bool => mkConst ``LeanQbe.T.Ty.bool
  | .bits n => mkApp (mkConst ``LeanQbe.T.Ty.bits) (mkNatLit n)
  | .float f => mkApp (mkConst ``LeanQbe.T.Ty.float) (Lean.toExpr f)
  | .pair a b => mkApp2 (mkConst ``LeanQbe.T.Ty.pair) (tyToExpr a) (tyToExpr b)

instance : Lean.ToExpr Ty where
  toTypeExpr := mkConst ``LeanQbe.T.Ty
  toExpr := tyToExpr

def evalChunkLiterals (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fs : List Fn) (hints : List I.Hints)
    [Lean.ToExpr (List I.Directive)] :
    Except String (List Lean.Expr) := do
  let (code, bounds) ← compileModule I lt raBytes extCallees exits nX fs hints
  let sigs := sigBoundsOf lt fs bounds
  pure [Lean.toExpr code, Lean.toExpr bounds, Lean.toExpr sigs]

private def addLitDef (declNm : Name) (ty val : Lean.Expr) : CoreM Unit := do
  let decl := Declaration.defnDecl {
    name := declNm, levelParams := [], type := ty, value := val,
    hints := .abbrev, safety := .safe }
  addDecl decl (forceExpose := true)
  compileDecl decl

/-- `splice_chunk_literals codeId boundsId sigsId isa lt raBytes ext exits nX fs hints`
evaluates `compileModule` and `sigBoundsOf` in the meta interpreter and adds three safe literal
kernel definitions (`codeId : List isa.Directive`, `boundsId : List (Sym × Nat)`,
`sigsId : List (SigEntry × Nat)`). -/
elab "splice_chunk_literals " codeId:ident boundsId:ident sigsId:ident
    isaT:term:arg ltT:term:arg raT:term:arg extT:term:arg exitsT:term:arg
    nXT:term:arg fnsT:term:arg hintsT:term:arg : command => do
  let ns ← getCurrNamespace
  let (codeTy, boundsTy, sigsTy, res) ← liftTermElabM do
    let isaE ← elabTerm isaT (some (mkConst ``LeanQbe.T.Isa))
    let ltE ← elabTerm ltT (some (mkConst ``LeanQbe.T.LegalTarget))
    let raE ← elabTerm raT (some (mkConst ``Nat))
    let sigEntryNatTy :=
      mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``LeanQbe.T.SigEntry) (mkConst ``Nat)
    let extE ← elabTerm extT (some (mkApp (mkConst ``List [.zero]) sigEntryNatTy))
    let exitsE ← elabTerm exitsT
      (some (mkApp (mkConst ``List [.zero]) (mkConst ``LeanQbe.T.Sym)))
    let nXE ← elabTerm nXT (some (mkConst ``Nat))
    let fnsE ← elabTerm fnsT
      (some (mkApp (mkConst ``List [.zero]) (mkConst ``LeanQbe.T.Fn)))
    let regTy ← whnf (mkApp (mkConst ``LeanQbe.T.Isa.Reg) isaE)
    let vregTy ← whnf (mkApp (mkConst ``LeanQbe.T.Isa.VReg) isaE)
    let condTy ← whnf (mkApp (mkConst ``LeanQbe.T.Isa.Cond) isaE)
    let hintTy := mkApp3 (mkConst ``LeanQbe.T.Hints) regTy vregTy condTy
    let hintsE ← elabTerm hintsT (some (mkApp (mkConst ``List [.zero]) hintTy))
    let dirTy ← whnf (mkApp (mkConst ``LeanQbe.T.Isa.Directive) isaE)
    let listDirTy := mkApp (mkConst ``List [.zero]) dirTy
    let toExprInst ← synthInstance (mkApp (mkConst ``Lean.ToExpr [.zero]) listDirTy)
    synthesizeSyntheticMVarsNoPostponing
    let callE ← instantiateMVars (mkAppN (mkConst ``LeanQbe.T.evalChunkLiterals)
      #[isaE, ltE, raE, extE, exitsE, nXE, fnsE, hintsE, toExprInst])
    let outTy := mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``String)
      (mkApp (mkConst ``List [.zero]) (mkConst ``Lean.Expr))
    let evalRes ← unsafe evalExpr (Except String (List Lean.Expr)) outTy callE
    let cTy ← instantiateMVars
      (mkApp (mkConst ``List [.zero]) (mkApp (mkConst ``LeanQbe.T.Isa.Directive) isaE))
    let symNatTy := mkApp2 (mkConst ``Prod [.zero, .zero])
      (mkConst ``LeanQbe.T.Sym) (mkConst ``Nat)
    let bTy := mkApp (mkConst ``List [.zero]) symNatTy
    let sTy := mkApp (mkConst ``List [.zero]) sigEntryNatTy
    return (cTy, bTy, sTy, evalRes)
  match res with
  | .error e => throwError "splice_chunk_literals: {e}"
  | .ok [codeLit, boundsLit, sigsLit] =>
    liftCoreM do
      addLitDef (ns ++ codeId.getId) codeTy codeLit
      addLitDef (ns ++ boundsId.getId) boundsTy boundsLit
      addLitDef (ns ++ sigsId.getId) sigsTy sigsLit
  | .ok _ => throwError "splice_chunk_literals: unexpected evaluation result"

end

end LeanQbe.T
