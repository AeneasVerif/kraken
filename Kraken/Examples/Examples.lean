/-
Kraken - Example Programs

This demonstrates our proof style using the `kstep` stepping tactic that
advances through ASM instructions. This is a work in progress, and is the result
of several experiments, which can be found in the Git history at revision
a556993a and earlier.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.Tactics
import Kraken.Parser
import Kraken.Eval
import Kraken.Theorems

open Kraken.Parser

--------------------------------------------------------------------------------

def p1 := parse("start: mov $1, %rax")

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) := by
  induction prog <;> simp [Executable.directivesFromAddress,Executable.withAddresses,Layout.apply]
    
-- Super-simple example to debug tactics
example [layout : Layout] s : straightlineStep (layout p1) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  dsimp only [p1]
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  sym =>
  kstep (alignedLoadsAndStores := true)
  tactic =>
  decide

  /- simp [Instr.interp,Operation.interp,Operand.interp,MachineData.set] -/
  /- simp [MachineData.setReg,Reg64s.set,Reg64s.set64,ConstExpr.interp] -/
  /- simp [Width.bits] -/

  /- simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next,MachineState.setReg,Registers.set] -/

def swap : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax")

theorem swap_correct [layout : Layout] (d : MachineData) :
      Eventually (straightlineStep (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  dsimp [swap]
  apply step_cps
  dsimp only [straightlineStep, Executable.straightline, Directives.interp]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]

  sym =>
  kstep
  tactic =>
  simp (zeta:=false) -- TODO: figure out why `simp` gives us two `Eventually`s
  lift_lets
  intros
  constructor
  <;> apply Eventually.done
  <;> bv_decide

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := parse("
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax")

-- Example 2: stepping through both straightline and control instructions
example [layout : Layout] (s : MachineData): Eventually (straightlineStep (layout p2)) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  dsimp [p2]
  apply step_cps
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  sym =>
  kstep
  tactic =>
  lift_lets
  -- TODO: I would like `kstep` to do this automatically
  intros v1 v2 v status
  -- TODO: I would like `kstep` to try `decide`-ing conditionals that block reduction (or `grind`-ing)
  have: v1 = 0 := by decide
  simp [this]

  sym =>
  kstep
  tactic =>
  apply Eventually.done
  bv_decide

-- Example 3, more sophisticated

-- TODO: restore p3

def p3: Program := parse("
init:
  mov $2, %rdx             # rdx: current result = 2
start:
  sub $0, %rbx             # TEST: zf = (rbx == 0)
  jz _end                 # end loop if rbx == 0 (a.k.a. « while rbx >= 0 »)
  mulx %rdx, %rdx, %rax    # BODY: rdx := rdx * rdx
  sub $1, %rbx              # rbx -= 1
  jmp start               # go back to test & loop body
_end:
  nop
")

def p3_spec (s: MachineData): Nat := 2^(2^s.regs.rbx.toNat)

set_option maxHeartbeats 4000000 in
theorem p3_correct [layout: Layout] (s: MachineData):
    p3_spec s < 2^64 →
    Eventually (straightlineStep (layout p3)) (fun s => s.1.regs.rdx.toNat = p3_spec s.1 ∧ s.1.regs.rax = 0) (s, layout.start) :=
  by
    intros h_bounds
    dsimp [p3]
    apply step_cps
    dsimp only [straightlineStep,Executable.straightline]
    rw [Executable.directivesFromStart]
    simp [List.mapIdx,List.mapIdx.go]

    -- TODO: resume fixing this example once
    -- https://leanprover.zulipchat.com/#narrow/channel/594054-SymM-users/topic/kernel.20error.20with.20SymM/with/601889305
    -- is fixed (Lean bug)

    -- sym =>
    -- kstep
    -- intros
    
    sorry

/-     intros h_bounds h_rip
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
                  omega -/

def p4 := eval% parse("start: mov $2, %rax
dec %rax")

-- Super-simple example to debug tactics
example [layout : Layout] s : straightlineStep (layout p4) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p4
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  -- TODO: this preamble above is a good form for what we need (although I'd
  -- also like registers to be exploded). Can we move it to a tactic? Like
  -- `kprologue p4` or something. I did not manage because of the =>, and I got
  -- into a rabbit hole of syntax macros and weird syntactic classes (elimExpr
  -- vs ident) and gave up.

  sym =>
  kstep
  intros
  tactic =>
  decide

/- Examples -/

def p5 := parse("start: mov $2, %rax
dec %rax
start2:
dec %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.all true -/

example [layout : Layout] s : straightlineStep (layout p5) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax =>
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p5
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  -- TODO: same remark, lift this preamble

  sym => 
  kstep
  tactic =>
  bv_decide

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.coercions false -/
/- set_option pp.all true -/


example [layout : Layout] (s: MachineData)
  (hAlign: s.regs.rsp % 8 = 0)
  (hContains: forall x, x ∈ s.dmem)
  : straightlineStep (layout p6) (s, layout.start) (fun s' => s'.1.regs.rax = s.regs.rax) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  let ss := s
  change (straightlineStep _ (ss, _) _)
  cases s with | mk regs flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp_old rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  simp at hAlign
  simp at hContains
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p6
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]

  -- An example of how to do some memory reasoning.

  sym => 
  kstep
  tactic =>
  lift_lets
  intros rsp_store v
  -- TODO: I would like kstep to try to decide this automatically
  have: rsp_store % 8 = 0 := by bv_decide
  rw [simpleAlignedStore64]
  <;> try grind
  sym =>
  kstep
  tactic =>
  lift_lets
  intros rsp
  intros
  rw [simpleAlignedLoad64]
  <;> try grind
  sym =>
  kstep
  tactic =>
  intros
  simp [rsp]

/- def bigp := parseFile("./ecc-secp521r1-modp.S") -/

/- set_option maxRecDepth 4000 -/
/- set_option maxHeartbeats 2000000 -/

/- example [layout : Layout] s -/ 
/-   (hAlign: s.regs.rsp % 8 = 0) -/
/-   (hContains: forall x, x ∈ s.dmem) -/
/- : straightlineStep (layout bigp) (s, layout.start) (fun s => s.1.regs.rax = 0) := by -/
/-   -- Refine the state to make registers apparent -- note that `cases` consumes -/
/-   -- the hypothesis, and substitutes it, so we make a copy of it to have a -/
/-   -- refined state in the hypotheses, not the goal. -/
/-   let ss := s -/
/-   change (straightlineStep _ (ss, _) _) -/
/-   cases s with | mk regs flags mem => -/
/-   cases regs with | mk rax => -/
/-   -- Rewrite the program to make layout, addresses, etc. apparent -/
/-   delta bigp -/
/-   dsimp only [straightlineStep,Executable.straightline] -/
/-   rw [Executable.directivesFromStart] -/
/-   simp [List.mapIdx,List.mapIdx.go] -/

/-   sym => -/ 
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro rsp_store -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedStore64] -/
/-   <;> try grind -/

/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   have: rsp_store % 8 = 0 := by bv_decide -/
/-   rw [simpleAlignedLoad64] -/
/-   <;> try grind -/

/-   rotate_right 1 -/
/-   . sorry -- need additional alignment hypotheses here -/
/-   sym => -/
/-   kstep -/
/-   tactic => -/
/-   intro count -/
/-   have: count ≠ 0 := by bv_decide -/
/-   simp [this] -/
  
/-   sym => -/
/-   kstep -/
/-   intro -/
/-   tactic => -/
/-   have : count = 55 := by decide -/
/-   simp [this] -/
  
/-   sym => -/
/-   kstep -/
/-   intros -/
/-   kstep -/
/-   sorry -/
  /- tactic => -/
  /- lift_lets -/
  /- revert -/
  /- sorry -/

