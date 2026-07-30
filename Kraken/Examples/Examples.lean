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
import Kraken.X64Sep

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
  sym => kstep; tactic =>
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
  sym => kstep; tactic =>
  simp (zeta:=false) -- TODO: figure out why `simp` gives us two `Eventually`s
  -- lift_lets
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
  intros v
  simp
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
  -- intros
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
  sym => kstep; tactic =>
  bv_decide

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.coercions false -/
/- set_option pp.all true -/

attribute [ksimp]
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.ofNat_uInt64ToNat
  BitVec.reduceOfInt
  BitVec.setWidth_eq
  Int.add_zero
  Int.reduceBmod
  Int.reduceNeg
  Int64.reduceToInt
  Int64.toInt_neg
  Nat.reducePow
  Nat.shiftRight_zero
  Nat.sub_zero
  UInt64.ofBitVec_add
  UInt64.ofBitVec_ofNat
  UInt64.ofBitVec_sub
  UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

theorem p6_correct [layout : Layout] (s₀ : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 8#64)) ⋆ R) :
    Eventually (straightlineStep (layout p6))
      (fun s' => s'.1.regs.rax = s₀.regs.rax ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply step_cps
  let ss := s₀
  change (straightlineStep _ (ss, _) _)
  cases s₀ with | mk regs flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs : stack.length = 8 := h_len
  -- Rewrite the program to make layout, addresses, etc. apparent
  delta p6
  dsimp only [straightlineStep,Executable.straightline]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx,List.mapIdx.go]
  simp at h_mem
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 stack R mem ⟨h_mem, h_bs⟩ rax.toBitVec.toInt
  sym =>
  kstep
  tactic =>
  -- NOTE: this rw currently succeeds only if kstep performs zeta, which in
  -- turns unlocks more `ksimp` lemmas; barring that, we have a unification
  -- problem (even though the call to MachineData.store *is* truly in the goal!)
  -- TODO: backward lemma (in our goal)
  -- rw [store_sep]
  -- case h_mem => exact h_mem
  -- case h_len => exact h_bs
  -- NOTE: adding a let-binding in store_sep does not seem to give us a nice
  -- name for the new memory
  -- kstep
  -- NOTE: the post- of store_sep uses dmem := Mem.storeInt ... -- this is a
  -- concrete value, not a separation logic predicate, so we lift a concrete
  -- definition to a SL assertion via storeInt_sep
  -- TODO: forward lemma (needed for the subgoal)
  -- rw [load_sep]
  -- done
  -- case h_mem => simp; exact h_mem1
  -- case h_len => exact Int.toBytes_length 8 _
  apply Eventually.done
  simp only [and_true]
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]

-- def bigp := parseFile("./ecc-secp521r1-modp.S")

/- set_option maxRecDepth 4000 -/
/- set_option maxHeartbeats 2000000 -/

-- example [layout : Layout] s
--   (hAlign: s.regs.rsp % 8 = 0)
--   (hContains: forall x, x ∈ s.dmem)
-- : straightlineStep (layout bigp) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
--   -- Refine the state to make registers apparent -- note that `cases` consumes
--   -- the hypothesis, and substitutes it, so we make a copy of it to have a
--   -- refined state in the hypotheses, not the goal.
--   let ss := s
--   change (straightlineStep _ (ss, _) _)
--   cases s with | mk regs flags mem =>
--   cases regs with | mk rax =>
--   -- Rewrite the program to make layout, addresses, etc. apparent
--   delta bigp
--   dsimp only [straightlineStep,Executable.straightline]
--   rw [Executable.directivesFromStart]
--   simp [List.mapIdx,List.mapIdx.go]
--   kstep
--   done



open Std
open Std.ExtHashMap

theorem BitVec.take_all {w : Nat} (x : BitVec w) : x.take w = x := by
  simp [BitVec.take]

def move_2_regs_to_heap := parse("
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
")

theorem move_2_regs_to_heap_correct [layout : Layout] (s₀ : MachineData)
  (v1 v2 : UInt64)
  (R : DataMem → Prop)
  (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2.At (s₀.regs.rdi.toBitVec + 8#64)) ⋆ R)
  : Eventually (straightlineStep (layout move_2_regs_to_heap))
      (fun s' =>
        s'.1.regs.r12 = s₀.regs.rax ∧
        s'.1.regs.r13 = s₀.regs.rcx ∧
        s'.1.regs.rdi = s₀.regs.rdi)
      (s₀, layout.start) := by
  apply step_cps
  cases s₀ with | mk regs flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs1 : v1.toBytes.length = 8 := UInt64.toBytes_length v1
  have h_bs2 : v2.toBytes.length = 8 := UInt64.toBytes_length v2
  rw [sep_assoc] at h_mem
  dsimp only [straightlineStep, Executable.straightline]
  dsimp only [move_2_regs_to_heap]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  sym => kstep; tactic =>
  simp [AddrExpr.interp, ConstExpr.interp, Reg64s.get64, Width.bits, BitVec.toAddressSize, BitVec.signed, BitVec.take_all, BitVec.ofInt_toInt]
  have h_mem1 := Mem.storeInt_sep rdi.toBitVec 8 v1.toBytes (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ R) mem ⟨h_mem, h_bs1⟩ rax.toBitVec.toInt
  rw [store_sep]
  case h_mem => exact h_mem
  case h_len => exact h_bs1
  replace h_mem1 : (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem1
  sym => kstep; tactic =>
  simp [AddrExpr.interp, ConstExpr.interp, Reg64s.get64, Width.bits, BitVec.toAddressSize, BitVec.signed, BitVec.take_all, BitVec.ofInt_add, BitVec.ofInt_toInt]
  have h_mem2 := Mem.storeInt_sep (rdi.toBitVec + 8#64) 8 v2.toBytes _ _ ⟨h_mem1, h_bs2⟩ rcx.toBitVec.toInt
  rw [store_sep]
  case h_mem => exact h_mem1
  case h_len => exact h_bs2
  replace h_mem2 : (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi) ⋆ (Eq ((Int.toBytes 8 rcx.toBitVec.toInt).At (rdi.toBitVec + 8#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2
  sym => kstep; tactic =>
  simp [AddrExpr.interp, ConstExpr.interp, Reg64s.get64, Width.bits, BitVec.toAddressSize, BitVec.signed, BitVec.take_all, BitVec.ofInt_toInt]
  rw [load_sep]
  case h_mem => exact h_mem2
  case h_len => exact Int.toBytes_length 8 _
  replace h_mem2 : (Eq ((Int.toBytes 8 rcx.toBitVec.toInt).At (rdi.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi.toBitVec) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2
  sym => kstep; tactic =>
  simp [AddrExpr.interp, ConstExpr.interp, Reg64s.get64, Width.bits, BitVec.toAddressSize, BitVec.signed, BitVec.take_all, BitVec.ofInt_add, BitVec.ofInt_toInt]
  rw [load_sep]
  case h_mem => exact h_mem2
  case h_len => exact Int.toBytes_length 8 _
  apply Eventually.done
  dsimp [UInt64.toBitVec]
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  exact ⟨rfl, rfl, rfl⟩

def sib_example := parse("
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax
")

theorem sib_example_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdi.toBitVec + s₀.regs.r15.toBitVec * 8#64)) ⋆ R) :
    Eventually (straightlineStep (layout sib_example))
      (fun s' => s'.1.regs.rax = 42)
      (s₀, layout.start) := by
  apply step_cps
  cases s₀ with | mk regs flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  dsimp only [straightlineStep, Executable.straightline]
  dsimp only [sib_example]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  sym => kstep; tactic =>
  simp [AddrExpr.interp, ConstExpr.interp, Reg64s.get64, Width.bits, Width.bytes, BitVec.toAddressSize, BitVec.signed, BitVec.take_all, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [store_sep]
  case h_mem => exact h_mem
  case h_len => exact h_bs
  sym => kstep; tactic =>
  simp [AddrExpr.interp, ConstExpr.interp, Reg64s.get64, Width.bits, Width.bytes, BitVec.toAddressSize, BitVec.signed, BitVec.take_all, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  have h_mem' := Mem.storeInt_sep (rdi.toBitVec + r15.toBitVec * 8#64) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
  rw [load_sep]
  case h_mem => exact h_mem'
  case h_len => exact by decide
  sym =>
  tactic =>
  apply Eventually.done
  rfl

def alu_mem_example := parse("
    movq $42, %rax
    movq %rax, 136(%rdx)
    movq $100, %rcx
    addq 136(%rdx), %rcx
")

theorem alu_mem_example_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (straightlineStep (layout alu_mem_example))
      (fun s' => s'.1.regs.rcx = 142)
      (s₀, layout.start) := by
  apply step_cps
  cases s₀ with | mk regs flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  dsimp only [straightlineStep, Executable.straightline]
  dsimp only [alu_mem_example]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  sym => kstep; tactic =>
  simp [AddrExpr.interp, ConstExpr.interp, Reg64s.get64, Width.bits, BitVec.toAddressSize, BitVec.signed, BitVec.take_all, BitVec.ofInt_add, BitVec.ofInt_toInt]
  have h_mem1 := Mem.storeInt_sep (rdx.toBitVec + 136#64) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
  rw [store_sep]
  case h_mem => exact h_mem
  case h_len => exact h_bs
  sym => kstep; tactic =>
  simp [AddrExpr.interp, ConstExpr.interp, Reg64s.get64, Width.bits, BitVec.toAddressSize, BitVec.signed, BitVec.take_all, BitVec.ofInt_add, BitVec.ofInt_toInt]
  rw [load_sep]
  case h_mem => exact h_mem1
  case h_len => exact Int.toBytes_length 8 _
  sym => kstep; tactic =>
  apply Eventually.done
  dsimp [UInt64.toBitVec]
  change (100 : UInt64) + { toBitVec := BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (42#64).toInt)) } = (142 : UInt64)
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rfl

def dynamic_stack_example := parse("
    movq $99, -8(%rsp)
    movq %rsp, %rbp
    leaq -1024(%rsp, %r9, 8), %rsp
    movq $42, %rax
    movq %rax, 16(%rsp, %r15, 8)
    movq $0, %rax
    movq 16(%rsp, %r15, 8), %rax
    movq %rbp, %rsp
    movq -8(%rsp), %rbx
")

theorem dynamic_stack_example_correct [layout : Layout] (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) R
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (straightlineStep (layout dynamic_stack_example))
      (fun s' => s'.1.regs.rax = 42 ∧ s'.1.regs.rbx = 99 ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply step_cps
  let ss := s₀
  change (straightlineStep _ (ss, _) _)
  cases s₀ with | mk regs flags mem =>
  cases regs with | mk rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 =>
  have h_bs : stack.length = 1024 := lstack
  have h_take_drop : stack = stack.take 1016 ++ stack.drop 1016 := by exact (List.take_append_drop 1016 stack).symm
  rw [h_take_drop] at h_mem
  have h_len_take : (stack.take 1016).length = 1016 := by
    rw [List.length_take]
    rw [h_bs]
    rfl
  have h_len_drop : (stack.drop 1016).length = 8 := by
    rw [List.length_drop]
    rw [h_bs]
  have h_At_append := Mem.At_append_sep (w := 64) (stack.take 1016) (stack.drop 1016) (rsp.toBitVec - 1024#64) (by
    rw [h_len_take, h_len_drop]
    decide)
  change (Eq ((stack.take 1016 ++ stack.drop 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem at h_mem
  rw [h_At_append] at h_mem
  rw [sep_assoc] at h_mem
  dsimp only [straightlineStep, Executable.straightline]
  dsimp only [dynamic_stack_example]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  sym => kstep; tactic =>
  simp only [BitVec.ofNat_uInt64ToNat,
    Int64.reduceToInt, Int.reduceNeg, Int.reduceBmod,
    BitVec.reduceOfInt, BitVec.setWidth_eq]
  have h_addr_eq : rsp.toBitVec - 1024#64 + BitVec.ofNat 64 (stack.take 1016).length = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8) := by
    rw [h_len_take]
    change rsp.toBitVec - 1024#64 + 1016#64 = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)
    bv_decide
  rw [h_addr_eq] at h_mem
  replace h_mem : (Eq ((stack.drop 1016).At (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8))) ⋆ (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)) 8 (stack.drop 1016) (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem ⟨h_mem, h_len_drop⟩ 99
  rw [store_sep ss]
  case h_mem => exact h_mem
  case h_len => exact h_len_drop
  sym =>
  kstep
  -- FIXME: kstep here takes too long
  sorry
