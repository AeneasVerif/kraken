import Lean
import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Sym.Grind
open Lean Meta Elab Tactic

syntax (name := symKTest) "ktest " : grind

-- TODO: surely there must be a helper for this
partial def openLetBinders {α : Type} (e : Expr) (k : Array Expr → Expr → Grind.GrindM α) : Grind.GrindM α := do
  match e with
  | .letE n t v b _ =>
    Meta.withLetDecl n t v fun fvar =>
      openLetBinders (b.instantiate1 fvar) fun fvars body =>
        k (#[fvar] ++ fvars) body
  | _ => k #[] e

@[grind_tactic symKTest]
def symktest : Grind.GrindTactic :=
  fun _stx : Syntax => do

  let gGoal : Grind.Goal ← Grind.getMainGoal
  let mvarId := gGoal.mvarId

  let simpResult ← Grind.liftGrindM do
    let target ← mvarId.getType
    openLetBinders target fun fvars body => do
      logInfo m!"goal: {body}"
      -- Build equality theorems for each let-bound variable
      let mut letThms : Array Sym.Simp.Theorem := #[]
      for fvar in fvars do
        let fvarId := fvar.fvarId!
        let localDecl ← fvarId.getDecl
        if let some val := localDecl.value? true then
          let eqType ← Meta.mkEq fvar val
          let refl ← Meta.mkEqRefl fvar
          let proof := mkApp2 (mkConst ``id [Level.zero]) eqType refl
          let pattern : Sym.Pattern := {
            levelParams := []
            varTypes := #[]
            varInfos? := none
            pattern := fvar
            fnInfos := {}
            checkTypeMask? := none
          }
          let thm : Sym.Simp.Theorem := { expr := proof, pattern := pattern, rhs := val, perm := false }
          letThms := letThms.push thm

      -- Build simproc combining declNames and letThms
      let declNames := [ ``UInt64.ofBitVec_sub, ``UInt64.ofBitVec_toBitVec, ``eq_self ].toArray
      let mut thms : Sym.Simp.Theorems := {}
      for declName in declNames do
        thms := thms.insert (← Sym.Simp.mkTheoremFromDecl declName)
      for thm in letThms do
        thms := thms.insert thm

      let rw := thms.rewrite Sym.Simp.dischargeSimpSelf
      let methods : Sym.Simp.Methods := {
        post := rw.andThen Sym.Simp.evalGround
      }

      -- Create sub-goal for body
      let mvarExpr ← mkFreshExprSyntheticOpaqueMVar body
      let mvarId' := mvarExpr.mvarId!
      let res ← Sym.simpGoal mvarId' methods
      match res with
      | .closed =>
        let proof ← instantiateMVars mvarExpr
        let fullProof ← mkLetFVars fvars proof
        mvarId.assign fullProof
        pure Sym.SimpGoalResult.closed
      | .goal mvarNew =>
        let proof ← instantiateMVars mvarExpr
        let fullProof ← mkLetFVars fvars proof
        mvarId.assign fullProof
        let newTarget ← mvarNew.getType
        let fullNewTarget ← mkLetFVars fvars newTarget
        let mvarExprFinal ← mkFreshExprSyntheticOpaqueMVar fullNewTarget
        mvarNew.assign mvarExprFinal
        pure (.goal mvarExprFinal.mvarId!)
      | .noProgress =>
        pure .noProgress

  match simpResult with
  | .noProgress => throwError "no progress"
  | .closed => Grind.setGoals []
  | .goal newMVarId =>
    Grind.setGoals [ { gGoal with mvarId := newMVarId } ]

def f (x: Nat) := x + 1

theorem dummy: f 1 = 2 := by rfl

theorem repro (rsp: UInt64):
    let rsp1 := rsp.toBitVec - 8#64
    let x := 2
    ({ toBitVec := rsp1 }: UInt64) = { toBitVec := rsp.toBitVec } - { toBitVec := 8#64 } ∧
    f 1 = x
:= by
  sym =>
  ktest
  tactic =>
  rw [dummy]
  trivial
