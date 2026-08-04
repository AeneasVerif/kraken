import Lean.Elab.Tactic
import Lean.Meta.Sym.SymM
import Kraken.Separation

open Lean Elab Tactic Meta
open Lean.Meta.Sym (SymM)

namespace Std.ExtHashMap

variable {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]

private theorem foldr_sep_append (xs ys : List (ExtHashMap key value → Prop)) :
    xs.foldr sep emp ⋆ ys.foldr sep emp = (xs ++ ys).foldr sep emp := by
  induction xs with
  | nil => simpa only [List.foldr, List.nil_append] using emp_sep (ys.foldr sep emp)
  | cons x xs ih => simpa only [List.foldr, List.cons_append] using
      (sep_assoc x (xs.foldr sep emp) (ys.foldr sep emp)).trans (congrArg (sep x) ih)

theorem foldr_sep_perm {xs ys : List (ExtHashMap key value → Prop)}
    (h : xs.Perm ys) : xs.foldr sep emp = ys.foldr sep emp := by
  apply h.foldr_eq'
  intros
  apply sep_comm_l

/--
The shallow syntax used by `ecancel`: only the separating conjunction spine is
reified; atoms remain ordinary Lean expressions.
-/
inductive SepTree (α : Type) where
  | emp
  | atom (a : α)
  | sep (left right : SepTree α)

namespace SepTree

variable {α : Type}

def flatten : SepTree α → List α
  | .emp => []
  | .atom a => [a]
  | .sep left right => flatten left ++ flatten right

def denote : SepTree (ExtHashMap key value → Prop) → ExtHashMap key value → Prop
  | .emp => Std.ExtHashMap.emp
  | .atom a => a
  | .sep left right => denote left ⋆ denote right

theorem denote_eq_foldr (tree : SepTree (ExtHashMap key value → Prop)) :
    denote tree =
      (flatten tree).foldr Std.ExtHashMap.sep Std.ExtHashMap.emp := by
  induction tree with
  | emp => rfl
  | atom a => exact (sep_emp a).symm
  | sep left right ihLeft ihRight =>
    simp only [denote, flatten]
    rw [ihLeft, ihRight, foldr_sep_append]

end SepTree

end Std.ExtHashMap

namespace Kraken.Tactic

private instance : MonadBacktrack Meta.SavedState SymM where
  saveState := Meta.saveState
  restoreState state := state.restore

private partial def denoteClauses (predType : Expr) : List Expr → SymM Expr
  | [] => withLocalDeclD `m predType.bindingDomain! fun m => do
      let body ← mkAppM ``Std.ExtHashMap.emp #[m]
      mkLambdaFVars #[m] body (etaReduce := true)
  | p :: ps => do
    let rest ← denoteClauses predType ps
    mkAppM ``Std.ExtHashMap.sep #[p, rest]

private structure Reification where
  tree : Expr
  clauses : List Expr

private partial def reify (predType e : Expr) : SymM Reification := do
  let e ← instantiateMVars e
  if e.getAppFn.constName? == some ``Std.ExtHashMap.emp then
    return {
      tree := mkApp (mkConst ``Std.ExtHashMap.SepTree.emp) predType
      clauses := []
    }
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p ← reify predType args[args.size - 2]!
    let q ← reify predType args[args.size - 1]!
    return {
      tree := mkApp3 (mkConst ``Std.ExtHashMap.SepTree.sep) predType p.tree q.tree
      clauses := p.clauses ++ q.clauses
    }
  return {
    tree := mkApp2 (mkConst ``Std.ExtHashMap.SepTree.atom) predType e
    clauses := [e]
  }

private def assignNaked (predType : Expr) (lhs rhs : List Expr) : SymM Bool := do
  let [.mvar mvarId] := lhs | return false
  isDefEq (.mvar mvarId) (← denoteClauses predType rhs)

private partial def cancelClauses (predType : Expr) (lhs rhs : List Expr) : SymM Bool := do
  if lhs.isEmpty && rhs.isEmpty then return true
  for i in List.range lhs.length do
    for j in List.range rhs.length do
      let l := lhs[i]!
      let r := rhs[j]!
      let matched ← commitWhen do
        isDefEq l r <&&> cancelClauses predType (lhs.eraseIdx i) (rhs.eraseIdx j)
      if matched then return true
  assignNaked predType lhs rhs <||> assignNaked predType rhs lhs

private partial def mkPermProof (predType : Expr) : List Expr → List Expr → SymM (Option Expr)
  | [], [] => do
    let nil ← mkListLit predType []
    return some (← mkAppM ``List.Perm.refl #[nil])
  | x :: xs, ys => do
    let some i ← ys.toArray.findIdxM? (fun y => isDefEq x y) | return none
    let before := ys.take i
    let after := ys.drop (i + 1)
    let some tailProof ← mkPermProof predType xs (before ++ after) | return none
    let before ← mkListLit predType before
    let after ← mkListLit predType after
    return some (← mkAppOptM ``List.perm_cons_append_cons
      #[none, none, some before, some after, some x, some tailProof])
  | _, _ => return none

private def solveSepEq (lhs rhs : Expr) : SymM (Option Expr) := do
  let predType ← inferType lhs
  let lhsBefore ← reify predType lhs
  let rhsBefore ← reify predType rhs
  unless ← cancelClauses predType lhsBefore.clauses rhsBefore.clauses do return none

  -- Evar assignments can expose new separating conjunctions. Reify again so
  -- the proof certificate describes the instantiated spatial expressions.
  let lhsAfter ← reify predType lhs
  let rhsAfter ← reify predType rhs
  let some permProof ← mkPermProof predType lhsAfter.clauses rhsAfter.clauses
    | return none
  let lhsProof ← mkAppM ``Std.ExtHashMap.SepTree.denote_eq_foldr #[lhsAfter.tree]
  let rhsProof ← mkAppM ``Std.ExtHashMap.SepTree.denote_eq_foldr #[rhsAfter.tree]
  let permProof ← mkAppM ``Std.ExtHashMap.foldr_sep_perm #[permProof]
  let proof ← mkEqTrans lhsProof permProof
  return some (← mkEqTrans proof (← mkEqSymm rhsProof))

private def solveFromHypothesis (target : Expr) (localDecl : LocalDecl) : SymM (Option Expr) := do
  let hypType := localDecl.type
  unless hypType.isApp do return none
  let targetFn := target.appFn!
  let targetArg := target.appArg!
  let hypFn := hypType.appFn!
  let hypArg := hypType.appArg!
  unless ← isDefEq targetArg hypArg do return none
  let some hSeps ← solveSepEq hypFn targetFn | return none
  let hFunEq ← mkAppM ``congrFun #[hSeps, targetArg]
  return some (← mkAppM ``Eq.mp #[hFunEq, localDecl.toExpr])

syntax (name := ecancel) "ecancel" : tactic

@[tactic ecancel]
def evalEcancel : Tactic :=
  fun _stx : Syntax => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  -- Existential witnesses introduced by tactics are synthetic-opaque goals;
  -- `ecancel` intentionally instantiates them as part of cancellation.
  let solved ← withConfig (fun config => { config with assignSyntheticOpaque := true }) do
    SymM.run do
      if target.isAppOfArity ``Eq 3 then
        let args := target.getAppArgs
        if let some proof ← solveSepEq args[1]! args[2]! then
          goal.assign proof
          return true
      for localDecl in ← getLCtx do
        if let some proof ← solveFromHypothesis target localDecl then
          goal.assign proof
          return true
      return false
  unless solved do
    throwError "ecancel: could not automatically solve goal {target}"
end Kraken.Tactic
