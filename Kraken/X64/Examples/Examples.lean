module

/-
Kraken - Example Programs

This demonstrates our proof style using the `kstep` stepping tactic that
advances through ASM instructions. This is a work in progress, and is the result
of several experiments, which can be found in the Git history at revision
a556993a and earlier.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.Eval
import Kraken.SeparationTactics
import Kraken.Tactics
import Std.Tactic.BVDecide
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
import Kraken.X64.Semantics
meta import Kraken.X64.Semantics
import Kraken.X64.Sep

open Kraken.X64.Parser

--------------------------------------------------------------------------------

def p1 := ⸨prog| start: mov $1, %rax ⸩

-- Super-simple example to debug tactics
example [layout : WellFormedLayout p1] s :
    Eventually (step1 p1.toExecutable)
      (fun s => s.pc = p1.toExecutable.addrOf p1.length ∧ s.1.regs.rax = 1) ⟨s, layout.start⟩ := by
  kprologue p1 with s
  sym => kstep; tactic =>
  exact .done _ ⟨rfl, rfl⟩
  /- simp [Instr.interp,Operation.interp,Operand.interp,MachineData.set] -/
  /- simp [MachineData.setReg,Reg64s.set,Reg64s.set64,ConstExpr.interp] -/
  /- simp [Width.bits] -/
  /- simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next,MachineState.setReg,Registers.set] -/

def swap : Program := ⸨prog|
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax⸩

theorem swap_correct [layout : WellFormedLayout swap] (d : MachineData) :
    Eventually (step1 swap.toExecutable)
      (fun s' =>
        s'.pc = swap.toExecutable.addrOf swap.length ∧
        s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
        s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      ⟨d, layout.start⟩ := by
  kprologue swap with d
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  grind

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := ⸨prog|
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax⸩

-- Example 2: stepping through both straightline and control instructions
example [layout : WellFormedLayout p2] (s : MachineData) :
    Eventually (step1 p2.toExecutable)
      (fun s => s.pc = p2.toExecutable.addrOf p2.length ∧ s.1.regs.rax = 2) ⟨s, layout.start⟩ := by
  kprologue p2 with s
  sym =>
  kstep
  tactic =>
  -- TODO: would be nice to have these simp steps be part of kstep
  rename_i v status
  have: v = 0 := by grind
  simp [this]
  sym =>
  kstep
  tactic =>
  refine .done _ ⟨rfl, ?_⟩
  dsimp only
  bv_decide

def p2_jump : Program := ⸨prog|
  mov $2, %rax
loop:
  sub $1, %rax
  jnz loop
  mov $42, %rax⸩

-- Example 2b: taking a jump to an internal label once, then falling through
example [layout : WellFormedLayout p2_jump] (s : MachineData) :
    Eventually (step1 p2_jump.toExecutable)
      (fun s => s.pc = p2_jump.toExecutable.addrOf p2_jump.length ∧ s.1.regs.rax = 42)
      ⟨s, layout.start⟩ := by
  kprologue p2_jump with s
  sym => kstep; tactic =>
  rename_i v status
  have : v = 1 := by grind
  simp [this]
  sym => kstep; tactic =>
  rename_i v' status'
  have : v' = 0 := by grind
  simp [this]
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  dsimp only
  bv_decide

-- Example 3, more sophisticated

-- TODO: restore p3

def p3: Program := ⸨prog|
init:
  mov $2, %rdx             -- rdx: current result = 2
start:
  sub $0, %rbx             -- TEST: zf = (rbx == 0)
  jz _end                 -- end loop if rbx == 0 (a.k.a. « while rbx >= 0 »)
  mulx %rdx, %rdx, %rax    -- BODY: rdx := rdx * rdx
  sub $1, %rbx              -- rbx -= 1
  jmp start               -- go back to test & loop body
_end:
  nop⸩

def p3_spec (s: MachineData): Nat := 2^(2^s.regs.rbx.toNat)

set_option maxHeartbeats 4000000 in
theorem p3_correct [layout : WellFormedLayout p3] (s : MachineData) :
    p3_spec s < 2 ^ 64 →
    Eventually (step1 p3.toExecutable)
      (fun s => s.pc = p3.toExecutable.addrOf p3.length ∧
        s.1.regs.rdx.toNat = p3_spec s.1 ∧ s.1.regs.rax = 0)
      ⟨s, layout.start⟩ := by
  intros h_bounds
  kprologue p3 with s

  sym =>
  -- kstep 3
  -- tactic =>
  -- apply reg_dec_loop
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

def p4 := eval% ⸨prog|start: mov $2, %rax
dec %rax⸩

-- Super-simple example to debug tactics
example [layout : WellFormedLayout p4] s :
    Eventually (step1 p4.toExecutable)
      (fun s => s.pc = p4.toExecutable.addrOf p4.length ∧ s.1.regs.rax = 1) ⟨s, layout.start⟩ := by
  kprologue p4 with s
  sym =>
  kstep
  -- intros
  tactic =>
  exact .done _ ⟨rfl, rfl⟩

/- Examples -/

def p5 := ⸨prog|start: mov $2, %rax
dec %rax
start2:
dec %rax⸩

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.all true -/

example [layout : WellFormedLayout p5] s :
    Eventually (step1 p5.toExecutable)
      (fun s => s.pc = p5.toExecutable.addrOf p5.length ∧ s.1.regs.rax = 0) ⟨s, layout.start⟩ := by
  kprologue p5 with s
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  dsimp only
  bv_decide

def p6 := ⸨prog|push %rax
mov $0, %rax
pop %rax⸩

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.coercions false -/
/- set_option pp.all true -/

attribute [ksimp]
  BitVec.add_zero
  BitVec.ofInt_add
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq
  Int.add_zero
  Int64.toInt_neg
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

theorem p6_correct [layout : WellFormedLayout p6] (s₀ : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 8#64)) ⋆ R) :
    Eventually (step1 p6.toExecutable)
      (fun s' => s'.pc = p6.toExecutable.addrOf p6.length ∧
        s'.1.regs.rax = s₀.regs.rax ∧ s'.1.regs.rsp = s₀.regs.rsp)
      ⟨s₀, layout.start⟩ := by
  kprologue p6 with s₀
  have h_bs : stack.length = 8 := h_len
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 stack R mem ⟨h_mem, h_bs⟩ rax.toBitVec.toInt
  sym =>
  kstep
  tactic =>
  refine .done _ ⟨rfl, ?_⟩
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp (config := { zetaDelta := true }) only [show (OfNat.ofNat 8 : UInt64) = 8 from rfl]
  bv_decide

-- A data word whose value is a label difference. `jmp done` keeps execution off the word.
def p7 : Program := ⸨prog|
start:
  nop 5
  nop 3
end:
  movl size(%rip), %eax
  jmp done
size:
  .long end - start
done:
⸩

/--
`p7` loads the word at `size`, whose value is the label difference `end - start`, kept symbolic.
The hypothesis `h_mem` says the loader put that value in memory: nothing in this framework links
the program text to memory yet, so it is assumed.
-/
theorem p7_correct [layout : WellFormedLayout p7] (s₀ : MachineData) (R : DataMem → Prop)
    (h_mem : letI := Executable.labels p7.toExecutable
      s₀.dmem =⋆ Eq ((Int.toBytes 4 (label "end" - label "start").toInt).At (label "size").toBitVec) ⋆ R) :
    Eventually (step1 p7.toExecutable)
      (fun s' => letI := Executable.labels p7.toExecutable
        s'.pc = p7.toExecutable.addrOf p7.length ∧
        s'.1.regs.rax = UInt64.ofBitVec (((label "end" - label "start").toBitVec.setWidth 32).setWidth 64))
      ⟨s₀, layout.start⟩ := by
  have h_addr (X Y : Int64) :
      (BitVec.ofInt 64 X.toInt + BitVec.ofInt 64 0 + BitVec.ofInt 64 (Y - X).toInt).setWidth 64
        = Y.toBitVec := by
    simp only [BitVec.setWidth_eq, Int64.toInt, BitVec.ofInt_toInt, Int64.toBitVec_sub]
    grind
  have h_val (v : Int64) :
      BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v.toInt)) = v.toBitVec.setWidth 32 := by
    rw [ofBytes_toBytes, Int.take, show 8 * 4 = 32 from rfl, Int64.toInt,
      ← BitVec.signExtend_eq_setWidth_of_le _ (by decide)]
    simp [BitVec.ofInt, BitVec.signExtend]
  kprologue p7 with s₀
  sym =>
  kstep
  case h_mem => tactic => dsimp only; rw [h_addr]; exact h_mem
  case h_len => exact Int.toBytes_length 4 _
  kstep
  tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp only [h_val, Int64.toBitVec_sub]

-- The same run under `fakeLayout`, where the nops take 5 + 3 bytes. The eval plays the loader: it
-- stores the word's value at `size`.
/-- info: Except.ok 8 -/
#guard_msgs in
#eval
  let exe := p7.fakeLayout
  let := exe.labels
  let word : Int64 := label "end" - label "start"
  let data : MachineData := { dmem := Mem.storeInt {} (label "size").toBitVec 4 word.toInt }
  (Executable.eval exe {data, pc := label "start"} (fun st => st.pc = label "done")).bind
    (fun s => .ok s.1.regs.rax)

-- def bigp := parseFile("./ecc-secp521r1-modp.S")

/- set_option maxRecDepth 4000 -/
/- set_option maxHeartbeats 2000000 -/

-- example [layout : WellFormedLayout bigp] s
--   (hAlign: s.regs.rsp % 8 = 0)
--   (hContains: forall x, x ∈ s.dmem)
-- : Eventually (step1 bigp.toExecutable) (fun s => s.1.regs.rax = 0) ⟨s, layout.start⟩ := by
--   kprologue bigp with s
--   sym =>
--   kstep
--   done


open Std
open Std.ExtHashMap

def move_2_regs_to_heap := ⸨prog|
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
⸩

theorem move_2_regs_to_heap_correct [layout : WellFormedLayout move_2_regs_to_heap]
    (s₀ : MachineData) (v1 v2 : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆
      Eq (v2.At (s₀.regs.rdi.toBitVec + 8#64)) ⋆ R) :
    Eventually (step1 move_2_regs_to_heap.toExecutable)
      (fun s' =>
        s'.pc = move_2_regs_to_heap.toExecutable.addrOf move_2_regs_to_heap.length ∧
        s'.1.regs.r12 = s₀.regs.rax ∧
        s'.1.regs.r13 = s₀.regs.rcx ∧
        s'.1.regs.rdi = s₀.regs.rdi)
      ⟨s₀, layout.start⟩ := by
  kprologue move_2_regs_to_heap with s₀

  have h_bs1 : v1.toBytes.length = 8 := UInt64.toBytes_length v1
  have h_bs2 : v2.toBytes.length = 8 := UInt64.toBytes_length v2
  have h_mem1 := Mem.storeInt_sep rdi.toBitVec 8 v1.toBytes (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ R) mem ⟨by ecancel, h_bs1⟩ rax.toBitVec.toInt
  have h_mem1' : (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem1
  have h_mem2 := Mem.storeInt_sep (rdi.toBitVec + 8#64) 8 v2.toBytes _ _ ⟨h_mem1', h_bs2⟩ rcx.toBitVec.toInt
  have h_mem2' : (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi) ⋆ (Eq ((Int.toBytes 8 rcx.toBitVec.toInt).At (rdi.toBitVec + 8#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2
  have h_mem2'' : (Eq ((Int.toBytes 8 rcx.toBitVec.toInt).At (rdi.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi.toBitVec) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2'
  simp at h_mem
  sym =>
  -- TODO: these would be prime examples for cancellation!
  -- TODO: the kstep tactic is supposed to apply `exact`, but `exact` only applies after `simp`, so
  -- clearly, stuff is missing from the simp-set in `kstep`
  kstep
  case h_mem => tactic => simp; ecancel
  case h_len => exact h_bs1
  kstep
  case h_mem => tactic => simp; exact h_mem1'
  case h_len => exact h_bs2
  kstep
  case h_mem => tactic => simp; exact h_mem2'
  case h_len => tactic => rfl
  kstep
  case h_mem => tactic => simp; exact h_mem2''
  case h_len => tactic => rfl
  kstep
  tactic =>
  apply Eventually.done
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  exact ⟨rfl, rfl, rfl, rfl⟩

def sib_example := ⸨prog|
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax⸩

-- FIXME: I had to replace `s₀.regs.r15.toBitVec * 8#64` with `BitVec.ofInt 64
-- (s₀.regs.r15.toBitVec.toInt * 8)` to make the example go through. Why?
theorem sib_example_correct [layout : WellFormedLayout sib_example] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdi.toBitVec + BitVec.ofInt 64 (s₀.regs.r15.toBitVec.toInt * 8))) ⋆ R) :
    Eventually (step1 sib_example.toExecutable)
      (fun s' => s'.pc = sib_example.toExecutable.addrOf sib_example.length ∧ s'.1.regs.rax = 42)
      ⟨s₀, layout.start⟩ := by
  kprologue sib_example with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem
  have h_mem' := Mem.storeInt_sep (rdi.toBitVec + BitVec.ofInt 64 (r15.toBitVec.toInt * 8)) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic => simp; exact h_mem'
  case h_len => exact by decide
  kstep
  tactic =>
  exact .done _ ⟨rfl, rfl⟩

def alu_mem_example := ⸨prog|
    movq $42, %rax
    movq %rax, 136(%rdx)
    movq $100, %rcx
    addq 136(%rdx), %rcx⸩

theorem alu_mem_example_correct [layout : WellFormedLayout alu_mem_example] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (step1 alu_mem_example.toExecutable)
      (fun s' => s'.pc = alu_mem_example.toExecutable.addrOf alu_mem_example.length ∧
        s'.1.regs.rcx = 142)
      ⟨s₀, layout.start⟩ := by
  kprologue alu_mem_example with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  have h_mem1 := Mem.storeInt_sep (rdx.toBitVec + 136#64) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic => simp; exact h_mem1
  case h_len => exact Int.toBytes_length 8 _
  kstep
  tactic =>
  refine .done _ ⟨rfl, ?_⟩
  dsimp [UInt64.toBitVec]
  change (100 : UInt64) + { toBitVec := BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (42#64).toInt)) } = (142 : UInt64)
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rfl

def dynamic_stack_example := ⸨prog|
    movq $99, -8(%rsp)
    movq %rsp, %rbp
    leaq -1024(%rsp, %r9, 8), %rsp
    movq $42, %rax
    movq %rax, 16(%rsp, %r15, 8)
    movq $0, %rax
    movq 16(%rsp, %r15, 8), %rax
    movq %rbp, %rsp
    movq -8(%rsp), %rbx⸩

theorem dynamic_stack_example_correct [layout : WellFormedLayout dynamic_stack_example]
    (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) R
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (step1 dynamic_stack_example.toExecutable)
      (fun s' => s'.pc = dynamic_stack_example.toExecutable.addrOf dynamic_stack_example.length ∧
        s'.1.regs.rax = 42 ∧ s'.1.regs.rbx = 99 ∧ s'.1.regs.rsp = s₀.regs.rsp)
      ⟨s₀, layout.start⟩ := by
  kprologue dynamic_stack_example with s₀
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
  have h_addr_eq : rsp.toBitVec - 1024#64 + BitVec.ofNat 64 (stack.take 1016).length = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8) := by
    rw [h_len_take]
    change rsp.toBitVec - 1024#64 + 1016#64 = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)
    bv_decide
  rw [h_addr_eq] at h_mem
  replace h_mem : (Eq ((stack.drop 1016).At (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8))) ⋆ (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)) 8 (stack.drop 1016) (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem ⟨h_mem, h_len_drop⟩ 99

  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_len_drop
  sorry
  -- kstep
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- -- FIXME: kstep here takes too long
  -- done
