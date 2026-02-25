/-
Kraken - Example Programs

Test programs demonstrating the assembly interpreter.
Requires Lean 4.28.0+ for SymM and full proof infrastructure.

For the core semantics, see AsmInterp/Core.lean.
For proof theorems, see AsmInterp/Core.lean.
-/

import Lean.Meta.Sym.Grind
import AsmInterp.Core

open Lean Meta Sym Elab Tactic

-- TEST

-- Example 1: single step of execution
def p1: Program := [
  (.none, .mov (Reg.rax) (1:UInt64)),
]

-- Useful to debug the step_by tactic
example: step1 p1 {} (fun s => s.regs.rax = 1) := by
  simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,set_reg_or_mem,next]
  simp [MachineState.setReg,Registers.set]

def p11: Program := [
  (.none, .mov (.reg .rbx) (.imm 2)),    -- rbx := 2
  (.none, .adcx (.reg .rax) (.reg .rbx)) -- rax := rax + rbx
]

def sapply (lem : Name) (mvarId : MVarId) : SymM (List (MVarId)) := do
  let rule ← mkBackwardRuleFromDecl lem
  let .goals gs ← rule.apply mvarId | failure
  return gs

example (s_old: MachineState) (h_bound: (s_old.getReg .rax).toNat + 2 < 2^64):
    eventually p11 (fun s => (s.getReg .rax).toNat = (s_old.getReg .rax).toNat + 2) {s_old with rip := 0}
  := by
    apply step_cps
    simp [p11]
    delta step1 eval1 fetch bind pure
    dsimp only [List.findIdx?,List.findIdx,getElem?,List.get?Internal]
    dsimp only [Instr.is_ctrl]
    dsimp only [Bool.false_eq_true, ↓dreduceIte] -- special simproc for if https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean#L25-L40
    delta next
    delta strt1
    dsimp (config := { beta := true, zeta := false, iota := true, proj := false, eta := false })
    delta eval_operand
    dsimp (config := { beta := true, zeta := false, iota := true, proj := false, eta := false })
    delta set_reg_or_mem
    dsimp (config := { beta := true, zeta := false, iota := true, proj := false, eta := false })
    run_tac liftMetaTactic (λ g => SymM.run (sapply ``step_cps g))
    delta step1 eval1 fetch
    dsimp (config := { beta := true, zeta := false, iota := false, proj := false, eta := false })
    delta MachineState.setReg
    -- delta Registers.set
    -- dsimp (config := { beta := true, zeta := false, iota := false, proj := true, eta := false })
    sorry


def p2: Program := [
  (.some "start", .mov (.reg .rax) (.imm 1)),
  (.none,         .jz "start"),
  (.none,         .mov (.reg .rax) (.imm 2)),
]

-- Example 2: stepping through both straightline and control instructions
example: eventually p2 (fun s => s.regs.rax = 2) {} := by
  simp [p2]

  apply step_cps
  step_one

  apply step_cps
  step_one

  apply step_cps
  step_one

  apply eventually.done
  simp

-- Example 3: a loop
def p3: Program := [
  -- (.none,         .mov (.reg .rbx) (.imm 4)),                 -- rbx: loop counter = 4
  (.none,         .mov (.reg .rdx) (.imm 2)),                 -- rdx: current result = 2
  (.some "start", .sub (.reg .rbx) (.imm 0)),                 -- TEST: zf = (rbx == 0)
  (.none        , .jz "end"),                                 -- end loop if rbx == 0 (a.k.a. "while rbx >= 0")
  (.none        , .mulx (.reg .rax) (.reg .rdx) (.reg .rdx)), -- BODY: rdx := rdx * rdx
  (.none,         .sub (.reg .rbx) (.imm 1)),                 -- rbx -= 1
  (.none,         .jmp "start"),                              -- go back to test & loop body
  (.some "end",   .mov (.reg .rax) (.imm 0)),                 -- meaningless -- just want the label to be well-defined
  -- result is 2^16, in rdx
]

-- Need to do something for when we have reached the end of the instruction list
-- maybe a special state! Right now this returns `none` because we eventually
-- hit the final instruction and then rip is out of bounds.
#eval (eval p3 {})

def p3_spec (s: MachineState): Nat := 2^(2^s.regs.rbx.toNat)

-- NOTE: This proof was broken by the flag semantics changes to support more instructions.
-- It was already incomplete (had sorry statements). Full rewrite needed.
theorem p3_correct (initial: MachineState):
    p3_spec initial < 2^64 →
    initial.rip = 0 →
    eventually p3 (fun s => s.regs.rdx.toNat == p3_spec initial ∧ s.regs.rax == 0) initial := by
  sorry
