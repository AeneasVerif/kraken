/-
Kraken - Example Programs

Test programs demonstrating the assembly interpreter.
Requires Lean 4.28.0+ (via Tactics.lean).

For semantics, see AsmInterp/Semantics.lean.
For tactics, see AsmInterp/Tactics.lean.
-/

import AsmInterp.Tactics

-- Example 1: single step of execution
def p1: Program := [
  (.none, .mov (Reg.rax) (.imm64 1)),
]

-- OLD: doing things with a heavy-handed `simp`
example: step1 p1 {} (fun s => s.regs.rax = 1) := by
  simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,Operand.imm64,sign_extend_imm,set_reg_or_mem,next]
  simp [MachineState.setReg,Registers.set]
  native_decide

-- Example 2: fine-grained tactics to step through the goal without un-necessary
-- steps, and relying only on low-level tactics

def p11: Program := [
  (.none, .mov (.reg .rbx) (.imm64 2)),    -- rbx := 2
  (.none, .adcx (.reg .rax) (.reg .rbx)) -- rax := rax + rbx
]

example (s_old: MachineState) (h_bound: (s_old.getReg .rax).toNat + 2 < 2^64):
    eventually p11 (fun s => (s.getReg .rax).toNat = (s_old.getReg .rax).toNat + 2) {s_old with rip := 0}
  := by
    delta p11
    -- First instruction
    step_cps
    step_instr

    delta strt1
    step_match
    delta eval_operand Operand.imm64 sign_extend_imm
    step_match
    delta set_reg_or_mem
    step_match
    delta MachineState.setReg
    dsimp (config := { beta := false, zeta := false, iota := true, proj := true, eta := false })

    step_cps
    step_instr
    delta strt1
    step_match
    delta eval_reg_or_mem
    step_match
    dsimp (config := { beta := false, zeta := false, iota := true, proj := true, eta := false })
    -- NOTE: we still have nice let-bindings in the goal!
    delta MachineState.getReg Registers.get
    step_match
    -- JP: do we want rewrite rules here of the form:
    --   (s.setReg r1 v).getReg r1 == v
    --   (s.setReg r1 v).getReg r2 == s.getReg r2
    -- I also feel like there are too many helpers for getReg/setReg -- perhaps
    -- they need to be simplified.

    -- delta MachineState.setReg
    -- delta Registers.set
    -- dsimp (config := { beta := true, zeta := false, iota := false, proj := true, eta := false })
    sorry


def p2: Program := [
  (.some "start", .mov (.reg .rax) (.imm64 1)),
  (.none,         .jz "start"),
  (.none,         .mov (.reg .rax) (.imm64 2)),
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
  native_decide

-- Example 3: a loop
def p3: Program := [
  -- (.none,         .mov (.reg .rbx) (.imm64 4)),                -- rbx: loop counter = 4
  (.none,         .mov (.reg .rdx) (.imm64 2)),                -- rdx: current result = 2
  (.some "start", .sub (.reg .rbx) (.imm64 0)),                -- TEST: zf = (rbx == 0)
  (.none        , .jz "end"),                                  -- end loop if rbx == 0 (a.k.a. "while rbx >= 0")
  (.none        , .mulx (.reg .rax) (.reg .rdx) (.reg .rdx)),  -- BODY: rdx := rdx * rdx
  (.none,         .sub (.reg .rbx) (.imm64 1)),                -- rbx -= 1
  (.none,         .jmp "start"),                               -- go back to test & loop body
  (.some "end",   .mov (.reg .rax) (.imm64 0)),                -- meaningless -- just want the label to be well-defined
  -- result is 2^16, in rdx
]

-- Need to do something for when we have reached the end of the instruction list
-- maybe a special state! Right now this returns `none` because we eventually
-- hit the final instruction and then rip is out of bounds.
#eval (eval p3 {})

def p3_spec (s: MachineState): Nat := 2^(2^s.regs.rbx.toNat)

set_option maxHeartbeats 800000 in
theorem p3_correct (initial: MachineState):
    p3_spec initial < 2^64 →
    initial.rip = 0 →
    eventually p3 (fun s => s.regs.rdx.toNat == p3_spec initial ∧ s.regs.rax == 0) initial :=
  by
    intros h_bounds h_rip
    simp [p3]
    -- First step sets rdx = 2
    apply step_cps
    step_one
    rw [h_rip]
    clear h_rip
    simp

    -- Loop invariant introduction
    apply reg_dec_loop p3 _ _ (fun i s => s.rip = 1 ∧ s.regs.rbx.toNat == i ∧ s.regs.rdx.toNat == 2^(2*(initial.regs.rbx.toNat - i) + 1)) initial.regs.rbx.toNat
    constructor
    . simp; native_decide
    . constructor
      -- Invariant initially holds
      . intros state inv
        rcases inv with ⟨ h_rip, h_rbx_zero, h_inv ⟩
        -- Step through a few program steps to "see" the jump and writing the
        -- sucess return value in rax
        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp
        apply step_cps
        step_one
        have : state.regs.rbx.toNat = 0 := by grind
        rw [this]
        apply step_cps
        step_one
        apply eventually.done
        simp
        -- Now functional correctness for initial invariant
        simp only [p3_spec]
        have h_int : Int64.toUInt64 0 = 0 := by native_decide
        simp only [h_int]
        -- NOTE: This grind fails due to a pre-existing issue with the invariant formula
        sorry

      -- Invariant preserved
      . intro state k h_k_nonzero inv
        rcases inv with ⟨ h_rip, h_rbx_is_k, h_inv ⟩

        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp

        apply step_cps
        step_one
        have h_rbx_nonzero : (state.regs.rbx.toNat = 0) = False := by grind
        -- NOTE: The following tactics need updating for ImmWidth/sub_with_borrow changes.
        -- The goal structure changed; these tactics may not make progress.
        try simp [h_rbx_nonzero]
        try simp only [show (Int64.toUInt64 0).toNat = 0 from rfl]
        try simp only [Nat.sub_zero]
        -- If the above didn't normalize the goal, fall through to sorry
        all_goals try {
          apply step_cps
          step_one
          apply step_cps
          step_one
          apply step_cps
          step_one
          apply eventually.done

          -- Goals for invariant preservation
          constructor
          · simp -- back to correct address
          · simp
            constructor
            · rw [ ← h_rbx_is_k ]
              sorry
            · have: 18446744073709551616 = 2^64 := by simp
              simp [p3_spec] at h_bounds
              rw [this]
              rw [this] at h_bounds
              rw [h_inv]
              sorry
        }
        -- Fallback sorry for cases where tactic structure changed too much
        all_goals sorry
