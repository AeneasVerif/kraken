/-
Kraken - Proof Tactics

Tactics for stepping through assembly proofs.
Requires Lean 4.28.0+ for SymM infrastructure.

For semantics, see AsmInterp/Semantics.lean.
For examples, see AsmInterp/Examples.lean.
-/

import Lean
import Lean.Meta.Sym.Grind
import AsmInterp.Semantics

open Lean Meta Sym Elab Tactic

-- STEP TACTIC: reduce a match
syntax "step_match" : tactic
macro_rules
  | `(tactic|step_match) =>
  `(tactic|
    -- JP: looks like reducing a match needs both beta and iota?
    -- the match in the goal below does not reduce properly if I remove beta := true
    dsimp (config := { beta := true, zeta := false, iota := true, proj := false, eta := false })
  )

def sapply (lem : Name) (mvarId : MVarId) : SymM (List (MVarId)) := do
  let rule ← mkBackwardRuleFromDecl lem
  let .goals gs ← rule.apply mvarId | failure
  return gs

-- STEP TACTIC: one step of execution
syntax "step_cps" : tactic
macro_rules
  | `(tactic|step_cps) =>
  `(tactic|
    run_tac liftMetaTactic (λ g => SymM.run (sapply `step_cps g))
  )

-- STEP TACTIC: reduce the lookup of the next instruction
-- TODO: bail if the state's .rip is not a constant
syntax "step_instr" : tactic
macro_rules
  | `(tactic|step_instr) =>
  `(tactic|
    delta step1 eval1 fetch;
    dsimp only [List.findIdx?,List.findIdx,getElem?,List.get?Internal];
    dsimp only [Instr.is_ctrl];
    dsimp only [Bool.false_eq_true, ↓dreduceIte]; -- special simproc for if https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean#L25-L40
    delta next
  )

-- NOTES: why is the right way of doing this? Ideally, we would not ask to
-- simplify anything that is not an internal definition, because it is not
-- modular. Problematic things here include, e.g., List.findIdx? (what if the
-- user uses this very function in their post-condition?).
--
-- Something equivalent to `match goal with` might work. Alternatively, we could
-- have copies of definitions, e.g. `def my_findIdx := normalize List.findIdx?`.
-- TODO: determine how to do that in Lean.
--
-- Furthermore, it would be nice to be able to specify that reducing e.g. a
-- projector should only be done if the left-hand side is not a variable.
syntax "step_one" : tactic
macro_rules
  | `(tactic|step_one) =>
  `(tactic|
    simp [
      step1,Instr.is_ctrl,eval1,fetch,
      -- works for calls to strt1
      strt1,eval_operand,eval_reg_or_mem,set_reg,set_reg_or_mem,effective_addr,Operand.imm64,sign_extend_imm,sub_with_borrow,add_with_carry,sub_overflow,add_overflow,MachineState.setReg,next,Registers.set,pure,bind,next,MachineState.getReg,Registers.get,
      -- or calls to ctrl
      ctrl,lookup,List.findIdx?,List.findIdx?.go,pure,bind,jump_if,next] <;> try native_decide)
