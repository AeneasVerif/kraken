module

public import LeanQbe.T.Main
public meta import Lean

/-!
# Meta Hint Splicing (`splice_module_hints`)

Command elaborator evaluating `fns.map (Fn.computeHints isa lt)` in the meta interpreter via
`Lean.ToExpr` + `unsafe evalExpr` and adding the resulting literal hint list as a safe kernel
definition. Kept separate from `LeanQbe.T.MainLemmas` so `MainLemmas` stays `Lean`-meta-free.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

meta section
open Lean Elab Command Term Meta

instance : Lean.ToExpr Empty where
  toTypeExpr := Lean.mkConst ``Empty
  toExpr e := e.elim

/-- `splice_module_hints name isa lt fns` evaluates `fns.map (Fn.computeHints isa lt)` in the
meta interpreter using `Lean.ToExpr` and adds the resulting literal hint list as a safe kernel
definition `name : List isa.Hints`. -/
elab "splice_module_hints " hName:ident isaT:term:arg ltT:term:arg fnsT:term:arg : command => do
  let hDeclNm := (← getCurrNamespace) ++ hName.getId
  let (hTy, hExpr) ← liftTermElabM do
    let isaE ← elabTerm isaT (some (mkConst ``LeanQbe.T.Isa))
    let ltE ← elabTerm ltT (some (mkConst ``LeanQbe.T.LegalTarget))
    let fnListTy := mkApp (mkConst ``List [0]) (mkConst ``LeanQbe.T.Fn)
    let fnsE ← elabTerm fnsT (some fnListTy)
    let regTy ← whnf (mkApp (mkConst ``LeanQbe.T.Isa.Reg) isaE)
    let vregTy ← whnf (mkApp (mkConst ``LeanQbe.T.Isa.VReg) isaE)
    let condTy ← whnf (mkApp (mkConst ``LeanQbe.T.Isa.Cond) isaE)
    let hintTy := mkApp3 (mkConst ``LeanQbe.T.Hints) regTy vregTy condTy
    let listHintsTy := mkApp (mkConst ``List [0]) hintTy
    let compFn ← mkAppM ``LeanQbe.T.Fn.computeHints #[isaE, ltE]
    let mapTerm ← mkAppM ``List.map #[compFn, fnsE]
    let typedMap ← mkExpectedTypeHint mapTerm listHintsTy
    let toExprInst ← synthInstance (mkApp (mkConst ``Lean.ToExpr [0]) listHintsTy)
    let toExprTerm := mkApp3 (mkConst ``Lean.toExpr [0]) listHintsTy toExprInst typedMap
    let hLit ← unsafe evalExpr Lean.Expr (mkConst ``Lean.Expr) toExprTerm
    let outTy := mkApp (mkConst ``List [0]) (mkApp (mkConst ``LeanQbe.T.Isa.Hints) isaE)
    return (outTy, hLit)
  liftCoreM do
    let hDecl := Declaration.defnDecl {
      name := hDeclNm, levelParams := [], type := hTy, value := hExpr,
      hints := .abbrev, safety := .safe }
    addDecl hDecl (forceExpose := true)
    compileDecl hDecl

end

end LeanQbe.T
