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

def swap : Program := eval% parse! "
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax"

syntax "step1" : tactic
macro_rules
  | `(tactic|step1) =>
  `(tactic|
    generalize hp: _::_ = p;

    cases p with
    | nil => contradiction
    | cons hd tl => ?_;

    injection hp with h_hd h_tl;
    rw [← h_hd];
    simp [Directives.interp, Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp];
    intro _af;
    rw [← h_tl];
    clear h_hd hd h_tl tl)

syntax "step2" term: tactic
macro_rules
  | `(tactic|step2 $program) =>
  `(tactic| (
  have h_layout: $program = ?_ := by assumption
  let tl: List (Directive×Nat) := ?_
  have : $program = ?hd :: tl := by
    simp [h_layout]
    constructor <;> rfl
  clear this

  -- Get a definitional equality hypothesis for `tl`, to put the equality in a nice form.
  have h_tl: tl = ?_ := by simp [tl]; rfl
  rw [← h_tl] at h_layout

  rw [h_layout]
  clear h_layout

  simp [Directives.interp, Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp]
))

theorem swap_correct [layout : Layout] (d : MachineData) :
      eventually (layout swap)
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  -- We want to avoid substituting swap eagerly (say, with `simp [swap]`) because it is a large
  -- term. Instead, get the definitional equality for `swap` and use that to rewrite in specific
  -- locations.
  have h: swap = ?_ := by dsimp [swap]; rfl

  -- We use the eventually.step case: we need to straightline over the instructions
  apply step_cps
  dsimp only [step1, Executable.straightline]
  -- This is where we need to avoid a `simp [swap]`. Instead, reason about the value of the concrete
  -- layout.
  have h_layout: (layout.apply swap).directivesFromAddress Layout.start = ?_ := by
    rw [Executable.directivesFromStart]
  rw (occs := .pos [2]) [h] at h_layout
  clear h
  simp [List.mapIdx, List.mapIdx.go] at h_layout
  -- We had to do this because `List.mapIdx.go` is written in tail-recursive style, meaning we have
  -- to compute the whole layout ahead of time. TODO: figure out if a dumb-style List.map would
  -- allow us to name swap.hd and swap.tl right here.

  step2 ((layout.apply swap).directivesFromAddress Layout.start)
  clear h_layout
  rename_i tl h_tl
  step2 tl
  rename_i tl h_tl
  step2 tl

  intros _af _af _af

  dsimp [MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64]

  apply eventually.done
  /- simp (ground:=True) -/
  dsimp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset]
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
