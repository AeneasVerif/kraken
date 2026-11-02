module

public meta import Lean

public meta section
open Lean

syntax (name := eval_expr) "eval% " term : term
@[term_elab eval_expr]
unsafe def elabEvalExpr : Elab.Term.TermElab :=
  fun stx expectedType? => do
  let e ← Elab.Term.elabTerm stx[1] expectedType?
  let e ← instantiateMVars e
  let toExprCall ← Meta.mkAppM ``Lean.toExpr #[e]
  let e_reduced ← Meta.evalExpr Expr (.const ``Lean.Expr []) toExprCall
  return e_reduced
