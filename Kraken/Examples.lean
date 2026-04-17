/-
Kraken - Example Programs

Test programs demonstrating the assembly interpreter.
Compatible with Lean 4.22.0+.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.Tactics
import Kraken.Parser
import Kraken.Eval

open Kraken.Parser

def p1 := eval% parse! "start: mov $1, %rax"

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) :=
  sorry

-- Super-simple example to debug tactics
example [layout : Layout] s : step1 (layout p1) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  dsimp only [p1]
  dsimp only [step1,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  dsimp only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp]
  dsimp only [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp]
  simp (ground:=True)
  simp

  /- simp [Instr.interp,Operation.interp,Operand.interp,MachineData.set] -/
  /- simp [MachineData.setReg,Reg64s.set,Reg64s.set64,ConstExpr.interp] -/
  /- simp [Width.bits] -/

  /- simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next,MachineState.setReg,Registers.set] -/

open Lean Meta Elab Tactic

-- a very simple set function that replaces every occurence of a term in goal with a fresh identifier
-- i am probably missing a lot of nuances here
def set_simple (mvarId : MVarId) (t : Expr): MetaM MVarId := do
  mvarId.withContext do
    let target ← mvarId.getType
    let type ← inferType t
    let lctx ← getLCtx
    let name := lctx.getUnusedName `x

    let (fvarId, mvarId) ← (← mvarId.define name type t).intro name

    mvarId.withContext do
      let newTarget := target.replace fun e =>
        if e == t then some (mkFVar fvarId) else none
      mvarId.replaceTargetDefEq newTarget

def abstractTailMeta (mvarId : MVarId) (typeName : Expr) : MetaM MVarId := do
  mvarId.withContext do
    let target ← mvarId.getType

    let some consExpr := target.find? fun e =>
      e.isAppOfArity ``List.cons 3 && e.getArg! 0 == typeName
      | throwError "No non-empty list of type {typeName} found"
    let tail := consExpr.getArg! 2

    set_simple mvarId tail

elab "set_simple " t:term : tactic => do
  let mvarId ← getMainGoal
  let term ← elabTerm t none
  let newMvarId ← set_simple mvarId term
  replaceMainGoal [newMvarId]

elab "abstract_tail " t:term : tactic => do
  let mvarId ← getMainGoal
  let targetType ← elabTerm t none
  let newMvarId ← abstractTailMeta mvarId targetType
  replaceMainGoal [newMvarId]

def swap : Program := eval% parse! "
    xor %rbx, %rax
    xor %rax, %rbx
    xor %rbx, %rax"

theorem swap_correct [layout : Layout] (s : MachineData) :
      Executable.straightline (layout swap) (s, layout.start)
      (fun s' =>
          s'.1.regs.get Reg.rax = s.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = s.regs.get Reg.rax)
      := by
  -- Necessary starting work to unfold the layout and move to the start.
  set_simple s
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  delta swap
  dsimp only [Executable.straightline, Directives.interp]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]

  -- step 1
  abstract_tail (Directive × Nat)
  dsimp (zeta:=false) [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,ConstExpr.interp,RegOrMem.interp,Reg.interp,Reg64s.get,Reg.base,Reg.offset,MachineData.set,MachineData.setReg,Reg64s.set,Width.type,Width.bits]
  intro v1 af1 status1
  dsimp [x_1]; clear x_1

  -- step 2
  abstract_tail (Directive × Nat)
  dsimp (zeta:=false) [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,ConstExpr.interp,RegOrMem.interp,Reg.interp,Reg64s.get,Reg.base,Reg.offset,MachineData.set,MachineData.setReg,Reg64s.set,Width.type,Width.bits]
  intro v2 af2 status2
  dsimp [x_1]; clear x_1

  -- step 3
  dsimp (zeta:=false) [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,ConstExpr.interp,RegOrMem.interp,Reg.interp,Reg64s.get,Reg.base,Reg.offset,MachineData.set,MachineData.setReg,Reg64s.set,Width.type,Width.bits]
  intro v3 af3

  -- postcondition
  dsimp [v1,v2,v3]
  dsimp [MachineData.setReg, Reg64s.set, Reg64s.set64,  Reg64s.get64]
  dsimp only [BitVec.drop, BitVec.take, Width.bits]
  bv_decide

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := eval% [
  .Label "start",
  .Instr ⟨ .W64, .W64, .mov Reg.rax (.imm (.Int64 1)) ⟩,
  .Instr ⟨ .W64, .W64, .xor Reg.rax Reg.rax ⟩,
  .Instr ⟨ .W64, .W64, .jcc .nz "start" ⟩,
  .Instr ⟨ .W64, .W64, .mov Reg.rax (.imm (.Int64 2)) ⟩,
]
def p2' : Program := eval% parse! "
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax"

-- Example 2: stepping through both straightline and control instructions
example [layout : Layout] (s : MachineData): eventually (layout p2) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  dsimp [p2]
  apply step_cps
  dsimp only [step1,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  dsimp only [Directives.interp,Directive.interp,Instr.interp,Operation.interp,Operand.interp,RegOrMem.interp]
  dsimp only [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp,CondCode.interp,StatusFlags.from_result]
  simp only [Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.truncate_eq_setWidth, BitVec.xor_self, BitVec.zero_eq,
    BEq.rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.setWidth_zero, BitVec.msb_zero]
  dsimp [undefined,Undefined.undefined]; intros _af
  apply eventually.done
  simp (ground:=True)

-- Example 3 commented out until we figure out how to parse concrete syntax.
/- def p3: Program := parse! "
init:
  mov $2 %rdx             # rdx: current result = 2
start:
  sub $0 %rbx             # TEST: zf = (rbx == 0)
  jz _end                 # end loop if rbx == 0 (a.k.a. « while rbx >= 0 »)
  .mulx %rdx %rdx %rax    # BODY: rdx := rdx * rdx
  sub 1 %rbx              # rbx -= 1
  jmp start               # go back to test & loop body
_end:
  nop
"

def p3_spec (s: MachineState): Nat := 2^(2^s.1.regs.rbx.toNat)

set_option maxHeartbeats 4000000 in
theorem p3_correct [Layout] (initial: MachineState):
    p3_spec initial < 2^64 →
    (layout ("init", 0) = initial.2) →
    eventually p3 (fun s => s.1.regs.rdx.toNat == p3_spec initial ∧ s.1.regs.rax == 0) initial :=
  by
  sorry -- simp times out due to larger Reg enum (64 constructors with aliased registers) -/
  /-
    intros h_bounds h_rip
    simp [p3]
    -- First step sets rdx = 2
    apply step_cps
    step_one
    rw [h_rip]
    clear h_rip
    simp

    -- Loop invariant introduction
    apply reg_dec_loop p3 _ _ (fun i s => s.rip = 1 ∧ s.regs.rbx.toNat = i ∧ i ≤ initial.regs.rbx.toNat ∧ s.regs.rdx.toNat = 2^(2^(initial.regs.rbx.toNat - i))) initial.regs.rbx.toNat
    constructor
    . simp
    . constructor
      -- Invariant at index 0 ==> post
      . intros state inv
        rcases inv with ⟨ h_rip, h_rbx_zero, h_rbx_le, h_inv ⟩
        -- Step through a few program steps
        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp
        apply step_cps
        step_one
        have : state.regs.rbx.toNat = 0 := by grind
        simp [this]
        apply step_cps
        step_one
        apply eventually.done
        simp
        -- Now functional correctness for initial invariant
        simp [p3_spec]
        grind

      -- Invariant preserved
      . intro state k h_k_nonzero inv
        rcases inv with ⟨ h_rip, h_rbx_is_k, h_rbx_le, h_inv ⟩

        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp

        apply step_cps
        step_one
        have h_k_ne : k ≠ 0 := by grind
        -- state.regs.rbx.toNat = k and toNat < 2^64 for UInt64
        have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (state.regs.rbx.toNat_lt)
        -- Simplify all the Int64.toUInt64 terms
        simp_all only [ne_eq, not_false_eq_true]
        -- Prove the if-condition is false: UInt64.ofInt ↑k ≠ 0 when k ≠ 0
        have h_cond : UInt64.ofInt (k : Int) ≠ 0 := UInt64_ofInt_natCast_ne_zero k h_k_lt h_k_ne
        rw [if_neg h_cond]




        apply step_cps
        step_one
        apply step_cps
        step_one
        apply step_cps
        step_one
        apply eventually.done

        -- Goals for invariant preservation
        constructor
        . simp -- back to correct address
        . match h_state:state.regs.rbx, h_init:initial.regs.rbx with
          | ⟨v_s⟩, ⟨v_i⟩ =>
            have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (by rw [h_state]; exact v_s.isLt)
            have h_init_lt : v_i.toNat < 2^64 := v_i.isLt
            simp [h_state, h_init, p3_spec, Reg.width, UInt64.ofInt, UInt64.ofNat, UInt64.toNat_ofNat] at *
            constructor
            . omega
            . constructor
              . omega
              . rw [h_inv]
                have h_vi_k : v_i.toNat - (k - 1) = (v_i.toNat - k) + 1 := by omega
                rw [h_vi_k, Nat.mod_eq_of_lt]
                . rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                . apply Nat.lt_of_le_of_lt _ h_bounds
                  rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                  apply Nat.pow_le_pow_right (by decide)
                  apply Nat.pow_le_pow_right (by decide)
                  omega
  -/
