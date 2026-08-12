import Lean.Elab.Tactic
import Lean.Meta.Tactic.AC
import Kraken.Separation

open Lean Elab Tactic Meta

namespace Kraken.Tactic

private partial def denoteClauses (predType : Expr) : List Expr → MetaM Expr
  | [] => withLocalDeclD `m predType.bindingDomain! fun m => do
      let body ← mkAppM ``Std.ExtHashMap.emp #[m]
      mkLambdaFVars #[m] body (etaReduce := true)
  | p :: ps => do
    let rest ← denoteClauses predType ps
    mkAppM ``Std.ExtHashMap.sep #[p, rest]

private partial def reifyClauses (e : Expr) : MetaM (List Expr) := do
  let e ← instantiateMVars e
  if e.getAppFn.constName? == some ``Std.ExtHashMap.emp then
    return []
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p ← reifyClauses args[args.size - 2]!
    let q ← reifyClauses args[args.size - 1]!
    return p ++ q
  return [e]

private def assignNaked (predType : Expr) (lhs rhs : List Expr) : MetaM Bool := do
  let [.mvar mvarId] := lhs | return false
  isDefEq (.mvar mvarId) (← denoteClauses predType rhs)

private def reduceProjectionApp (e : Expr) : MetaM Expr := do
  let some declName := e.getAppFn.constName? | return e
  let some info ← getProjectionFnInfo? declName | return e
  if info.fromClass then return e
  let some unfolded ← unfoldDefinition? e | return e
  let some fn ← reduceProj? unfolded.getAppFn | return e
  return mkAppN fn unfolded.getAppArgs

-- fuel: bound definitional unfolding to avoid expensive general reduction.
private partial def matchClosed (lhs rhs : Expr) (fuel : Nat := 2) : MetaM Bool := do
  let lhs ← reduceProjectionApp lhs
  let rhs ← reduceProjectionApp rhs
  if lhs == rhs then return true
  if lhs.getAppFn == rhs.getAppFn then
    let lhsArgs := lhs.getAppArgs
    let rhsArgs := rhs.getAppArgs
    unless lhsArgs.size == rhsArgs.size do return false
    for lhsArg in lhsArgs, rhsArg in rhsArgs do
      unless ← matchClosed lhsArg rhsArg fuel do return false
    return true
  if fuel == 0 then return false
  if let some lhs ← unfoldDefinition? lhs then
    if ← matchClosed lhs rhs (fuel - 1) then return true
  if let some rhs ← unfoldDefinition? rhs then
    if ← matchClosed lhs rhs (fuel - 1) then return true
  return false

private def matchAtom (lhs rhs : Expr) : MetaM Bool := do
  if lhs == rhs then return true
  if lhs.hasExprMVar || rhs.hasExprMVar then isDefEq lhs rhs
  else matchClosed lhs rhs

private def isNakedMVar : Expr → Bool
  | .mvar _ => true
  | _ => false

-- Closed clauses can be cancelled greedily: unlike clauses containing
-- metavariables, matching them cannot constrain a later cancellation choice.
private partial def cancelClosedClauses : List Expr → List Expr → MetaM (List Expr × List Expr)
  | [], rhs => return ([], rhs)
  | l :: ls, rhs => do
    if l.hasExprMVar then
      let (ls, rhs) ← cancelClosedClauses ls rhs
      return (l :: ls, rhs)
    let some j ← rhs.toArray.findIdxM? (fun r => do
        if r.hasExprMVar then return false
        matchClosed l r) | do
      let (ls, rhs) ← cancelClosedClauses ls rhs
      return (l :: ls, rhs)
    cancelClosedClauses ls (rhs.eraseIdx j)

private partial def cancelClauses (predType : Expr) (lhs rhs : List Expr) : MetaM Bool := do
  let (lhs, rhs) ← cancelClosedClauses lhs rhs
  if lhs.isEmpty && rhs.isEmpty then return true
  for i in List.range lhs.length do
    for j in List.range rhs.length do
      let l := lhs[i]!
      let r := rhs[j]!
      -- Closed matches have already been removed. A naked metavariable is
      -- reserved for assignment to the conjunction of all remaining clauses
      -- below.
      if (l.hasExprMVar || r.hasExprMVar) && !isNakedMVar l && !isNakedMVar r then
        let matched ← commitWhen do
          unless ← matchAtom l r do return false
          -- Matching may instantiate metavariables in the remaining clauses.
          let lhs ← (lhs.eraseIdx i).mapM instantiateMVars
          let rhs ← (rhs.eraseIdx j).mapM instantiateMVars
          cancelClauses predType lhs rhs
        if matched then return true
  assignNaked predType lhs rhs <||> assignNaked predType rhs lhs

private partial def alignClauses : List Expr → List Expr → MetaM (Option (List Expr))
  | [], [] => return some []
  | lhs, r :: rs => do
    let some i ← lhs.toArray.findIdxM? (fun l => matchAtom l r) | return none
    let some rest ← alignClauses (lhs.eraseIdx i) rs | return none
    return some (lhs[i]! :: rest)
  | _, _ => return none

/--
Rebuilds `e` while preserving its sep/emp tree structure and replacing each
atomic leaf, from left to right, with the next entry in `clauses`.
Returns none if there are not enough clauses to replace every atomic leaf.
Returns some (rebuilt expr, unused clauses) otherwise.
-/
private partial def canonicalize (e : Expr) (clauses : List Expr) :
    MetaM (Option (Expr × List Expr)) := do
  let e ← instantiateMVars e
  if e.getAppFn.constName? == some ``Std.ExtHashMap.emp then
    return some (e, clauses)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let some (p, clauses) ← canonicalize args[args.size - 2]! clauses | return none
    let some (q, clauses) ← canonicalize args[args.size - 1]! clauses | return none
    return some (← mkAppM ``Std.ExtHashMap.sep #[p, q], clauses)
  return match clauses with
  | c :: clauses => some (c, clauses)
  | [] => none

private def proveSeqEq (lhs rhs : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    let lhsClauses ← reifyClauses lhs
    let rhsClauses ← reifyClauses rhs
    let some rhsClauses ← alignClauses lhsClauses rhsClauses | return none
    let some (lhs, []) ← canonicalize lhs lhsClauses | return none
    let some (rhs, []) ← canonicalize rhs rhsClauses | return none
    let proof ← mkFreshExprMVar (← mkEq lhs rhs)
    Lean.Meta.AC.rewriteUnnormalizedRefl proof.mvarId!
    return some (← instantiateMVars proof)

private def solveSepEq (lhs rhs : Expr) : MetaM (Option Expr) := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then
    return some (← mkEqRefl lhs)
  let predType ← inferType lhs
  let lhsClauses ← reifyClauses lhs
  let rhsClauses ← reifyClauses rhs
  unless ← cancelClauses predType lhsClauses rhsClauses do return none
  proveSeqEq lhs rhs

private def solveFromHypothesis (target : Expr) (localDecl : LocalDecl) : MetaM (Option Expr) := do
  let target ← instantiateMVars target
  let hypType ← instantiateMVars localDecl.type
  unless hypType.isApp do return none
  let targetFn := target.appFn!
  let targetArg := target.appArg!
  let hypFn := hypType.appFn!
  let hypArg := hypType.appArg!
  unless ← matchAtom (← reduceProjectionApp targetArg) (← reduceProjectionApp hypArg) do
    return none
  let some hSeps ← solveSepEq hypFn targetFn | return none
  let hFunEq ← mkAppM ``congrFun #[hSeps, hypArg]
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
    if target.isAppOfArity ``Eq 3 then
      let args := target.getAppArgs
      if let some proof ← solveSepEq args[1]! args[2]! then
        goal.assign proof
        return true
    for localDecl? in (← getLCtx).decls.toArray.reverse do
      if let some localDecl := localDecl? then
        if let some proof ← solveFromHypothesis target localDecl then
          goal.assign proof
          return true
    return false
  unless solved do
    throwError "ecancel: could not automatically solve goal {target}"
end Kraken.Tactic
