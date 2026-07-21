import Lean
import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Sym.Grind
open Lean Meta Elab Tactic

syntax (name := symKTest) "ktest " : grind

@[grind_tactic symKTest]
def evalSymApplyConj : Grind.GrindTactic :=
  fun _stx : Syntax => do

  let declNames := [ ``UInt64.ofBitVec_sub ].toArray
  let rw ← Sym.mkSimprocFor declNames Sym.Simp.dischargeSimpSelf
  let methods: Sym.Simp.Methods := {
     post := rw.andThen Sym.Simp.evalGround
   }

  let gGoal : Grind.Goal ← Grind.getMainGoal
  let mvarId := gGoal.mvarId

  let simpResult ← Grind.liftGrindM (Sym.simpGoal mvarId methods)
  let mvarId ← Grind.liftGrindM (match simpResult with
    | .noProgress => throwError "no progress"
    | .goal mvarId => pure mvarId
    | .closed => throwError "unexpected")

  Grind.setGoals [ { gGoal with mvarId } ]

theorem repro (rsp: UInt64):
    let rsp1 := rsp.toBitVec - 8#64
    ({ toBitVec := rsp1 }: UInt64) = { toBitVec := rsp.toBitVec } - { toBitVec := 8#64 }
:= by
  sym =>
  ktest
  tactic =>
  sorry
