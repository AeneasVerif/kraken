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
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.Semantics
import Kraken.X64.Sep

open Kraken.X64.Parser

attribute [ksimp]
  BitVec.add_zero
  BitVec.sub_zero
  BitVec.ofInt_add
  BitVec.ofInt_ofNat
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

--------------------------------------------------------------------------------

def p1 := parse("start: mov $1, %rax")

-- Super-simple example to debug tactics
example [layout : Layout] (hwf : (layout p1).WellFormed) s :
    Eventually (step1 (layout p1)) (fun s => s.1.regs.rax = 1) (s, layout.start) := by
  apply eventually_straightlineStep (layout p1) hwf
  kprologue p1 with s
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

theorem swap_correct [layout : Layout] (hwf : (layout swap).WellFormed) (d : MachineData) :
      Eventually (step1 (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  apply eventually_straightlineStep_cps (layout swap) hwf
  kprologue swap with d
  sym => kstep; tactic =>
  apply Eventually.done
  grind

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := parse("
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax")

-- Example 2: stepping through both straightline and control instructions
example [layout : Layout] (hwf : (layout p2).WellFormed) (s : MachineData) :
    Eventually (step1 (layout p2)) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  apply eventually_straightlineStep_cps (layout p2) hwf
  kprologue p2 with s
  sym =>
  kstep
  tactic =>
  -- TODO: would be nice to have these simp steps be part of kstep
  rename_i v v1 status
  have: v = 0 := by grind
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

private theorem int64_rel_jmp_target (u tgt : Int64) :
    Int64.ofBitVec (u + (tgt - u)).toBitVec = tgt := by
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_ofBitVec, Int64.toBitVec_add, Int64.toBitVec_sub]
  bv_decide

private theorem uint64_sub_one_toNat {v : Nat} (hv0 : v ≠ 0) (hv_lt : v < 2 ^ 64) :
    (UInt64.ofBitVec (BitVec.ofNat 64 v - 1#64)).toNat = v - 1 := by
  simp only [UInt64.toNat_ofBitVec, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hv_lt]
  omega

private theorem p3_pow_step {n v : Nat} (hv0 : v ≠ 0) (hle : v ≤ n) (hb : 2 ^ 2 ^ n < 2 ^ 64) :
    2 ^ 2 ^ (n - v) * 2 ^ 2 ^ (n - v) = 2 ^ 2 ^ (n - (v - 1)) ∧
    2 ^ 2 ^ (n - (v - 1)) < 2 ^ 64 := by
  have h_sub : n - v + 1 = n - (v - 1) := by omega
  have h_eq : 2 ^ 2 ^ (n - v) * 2 ^ 2 ^ (n - v) = 2 ^ 2 ^ (n - (v - 1)) := by
    rw [← Nat.pow_add, ← Nat.two_mul, Nat.mul_comm 2 (2 ^ (n - v)), ← Nat.pow_succ, Nat.succ_eq_add_one, h_sub]
  have h_le_n : n - (v - 1) ≤ n := by omega
  have h_mono : 2 ^ 2 ^ (n - (v - 1)) ≤ 2 ^ 2 ^ n :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) h_le_n)
  exact ⟨h_eq, Nat.lt_of_le_of_lt h_mono hb⟩

private theorem uint64_ofInt_nat_toNat {m : Nat} (hm : m < 2 ^ 64) :
    (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofNat m))).toNat = m ∧
    UInt64.ofBitVec (BitVec.ofInt 64 ((Int.ofNat m) >>> 64)) = 0 := by
  have h_bv : BitVec.ofInt 64 (Int.ofNat m) = BitVec.ofNat 64 m := BitVec.ofInt_ofNat 64 m
  have h_shift : (Int.ofNat m) >>> (64 : Nat) = 0 := by
    change Int.ofNat (m >>> 64) = 0
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hm]
    rfl
  refine ⟨?_, ?_⟩
  · simp only [h_bv, UInt64.toNat_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  · rw [h_shift]
    rfl

set_option maxHeartbeats 4000000 in
theorem p3_correct [layout: Layout] (h : (layout p3).WellFormed)
    (hsz : Int64.ofNat (layout.size 1) ≠ 0) (s : MachineData)
    (hrax : s.regs.rax = 0) (hb : p3_spec s < 2^64) :
    Eventually (step1 (layout p3))
      (fun s' => s'.1.regs.rdx.toNat = p3_spec s ∧ s'.1.regs.rax = 0)
      (s, layout.start) := by
  let pc_start := layout.start + Int64.ofNat (layout.size 0) + Int64.ofNat (layout.size 1)
  have h_from_start : (layout p3).directivesFromAddress pc_start =
      ((p3.mapIdx (fun i d => (d, layout.size i))).drop 2) :=
    h.directivesFromAddress_drop2 hsz
  simp [p3, List.mapIdx, List.mapIdx.go] at h_from_start
  apply eventually_straightlineStep_cps (layout p3) h
  kprologue p3 with s
  sym =>
  kstep 2
  tactic =>
  rw [← h_from_start]
  dsimp only [p3_spec] at hb
  apply tailrec_loop_straightline (layout p3) h
    (fun s' => s'.1.regs.rdx.toNat = 2 ^ (2 ^ rbx.toNat) ∧ s'.1.regs.rax = 0)
    (_, pc_start)
    (fun v st =>
      st.2 = pc_start ∧
      st.1.regs.rbx.toNat = v ∧
      v ≤ rbx.toNat ∧
      st.1.regs.rdx.toNat = 2 ^ (2 ^ (rbx.toNat - v)) ∧
      st.1.regs.rax = 0)
    rbx.toNat
  · refine ⟨rfl, rfl, Nat.le_refl _, ?_, hrax⟩
    simp
    rfl
  · intro v state ⟨hpc, hrbx, hle, hrdx, hrax_st⟩
    obtain ⟨⟨⟨rax', rbx', rcx', rdx', rsi', rdi', rsp', rbp', r8', r9', r10', r11', r12', r13', r14', r15'⟩, zmms', flags', mem'⟩, pc'⟩ := state
    dsimp only at hpc hrbx hrdx hrax_st
    subst hpc
    delta p3
    dsimp only [straightlineStep, Executable.straightline]
    rw [h_from_start]
    sym =>
    kstep
    tactic =>
    rename_i v_sub status
    have hv_lt : v < 2 ^ 64 := hrbx ▸ rbx'.toBitVec.isLt
    have hv_sub : v_sub = BitVec.ofNat 64 v := by simp [v_sub, ← hrbx]
    by_cases hv0 : v = 0
    · have h_cond : (v_sub == BitVec.zero 64) = true := by rw [hv_sub, hv0]; rfl
      simp only [h_cond, ↓reduceIte, Effects.All]
      exact Or.inl ⟨by rw [hrdx, hv0, Nat.sub_zero], hrax_st⟩
    · have h_cond : (v_sub == BitVec.zero 64) = false := by
        rw [hv_sub]
        apply Bool.eq_false_iff.mpr
        intro h_eq
        have h_nat := congrArg BitVec.toNat ( beq_iff_eq.mp h_eq )
        simp only [BitVec.toNat_ofNat, BitVec.zero, Nat.mod_eq_of_lt hv_lt] at h_nat
        exact hv0 h_nat
      simp only [h_cond, Bool.false_eq_true, ↓reduceIte]
      sym =>
      kstep
      tactic =>
      rename_i b_mul v_mul s_lo s_hi v_dec status_dec
      have hrdx_lt : 2 ^ 2 ^ (rbx.toNat - v) < 18446744073709551616 := hrdx ▸ rdx'.toBitVec.isLt
      have hb_mul : b_mul = rdx'.toBitVec := by simp [b_mul]
      obtain ⟨h_pow_eq, h_pow_lt⟩ := p3_pow_step hv0 hle hb
      have hv_mul : v_mul = Int.ofNat (2 ^ 2 ^ (rbx.toNat - (v - 1))) := by
        simp [v_mul, hb_mul, BitVec.unsigned, hrdx, Nat.mod_eq_of_lt hrdx_lt]
        exact_mod_cast h_pow_eq
      have hv_dec : v_dec = BitVec.ofNat 64 v - 1#64 := by
        have hv_lt' : v < 18446744073709551616 := hv_lt
        simp [v_dec, hv_sub, Nat.mod_eq_of_lt hv_lt']
      obtain ⟨h_rdx_next, h_rax_next⟩ := uint64_ofInt_nat_toNat h_pow_lt
      refine Or.inr ⟨v - 1, ⟨?_, ?_, by omega, ?_, ?_⟩, by omega⟩
      · rw [int64_rel_jmp_target]
        rfl
      · rw [hv_dec]
        exact uint64_sub_one_toNat hv0 hv_lt
      · rw [hv_mul]
        exact h_rdx_next
      · rw [hv_mul]
        exact h_rax_next

def p4 := eval% parse("start: mov $2, %rax
dec %rax")

-- Super-simple example to debug tactics
example [layout : Layout] (hwf : (layout p4).WellFormed) s :
    Eventually (step1 (layout p4)) (fun s => s.1.regs.rax = 1) (s, layout.start) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  apply eventually_straightlineStep (layout p4) hwf
  kprologue p4 with s
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

example [layout : Layout] (hwf : (layout p5).WellFormed) s :
    Eventually (step1 (layout p5)) (fun s => s.1.regs.rax = 0) (s, layout.start) := by
  -- Refine the state to make registers apparent -- note that `cases` consumes
  -- the hypothesis, and substitutes it, so we make a copy of it to have a
  -- refined state in the hypotheses, not the goal.
  apply eventually_straightlineStep (layout p5) hwf
  kprologue p5 with s
  sym => kstep; tactic =>
  bv_decide

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.coercions false -/
/- set_option pp.all true -/

theorem p6_correct [layout : Layout] (hwf : (layout p6).WellFormed) (s₀ : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 8#64)) ⋆ R) :
    Eventually (step1 (layout p6))
      (fun s' => s'.1.regs.rax = s₀.regs.rax ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply eventually_straightlineStep_cps (layout p6) hwf
  kprologue p6 with s₀
  have h_bs : stack.length = 8 := h_len
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 stack R mem ⟨h_mem, h_bs⟩ rax.toBitVec.toInt
  sym =>
  kstep
  tactic =>
  apply Eventually.done
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  bv_decide

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
--   sym =>
--   kstep
--   done


open Std
open Std.ExtHashMap

def move_2_regs_to_heap := parse("
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
")

theorem move_2_regs_to_heap_correct [layout : Layout] (hwf : (layout move_2_regs_to_heap).WellFormed) (s₀ : MachineData)
  (v1 v2 : UInt64)
  (R : DataMem → Prop)
  (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2.At (s₀.regs.rdi.toBitVec + 8#64)) ⋆ R)
  : Eventually (step1 (layout move_2_regs_to_heap))
      (fun s' =>
        s'.1.regs.r12 = s₀.regs.rax ∧
        s'.1.regs.r13 = s₀.regs.rcx ∧
        s'.1.regs.rdi = s₀.regs.rdi)
      (s₀, layout.start) := by
  apply eventually_straightlineStep_cps (layout move_2_regs_to_heap) hwf
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
  exact ⟨rfl, rfl, rfl⟩

def sib_example := parse("
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax
")

-- FIXME: I had to replace `s₀.regs.r15.toBitVec * 8#64` with `BitVec.ofInt 64
-- (s₀.regs.r15.toBitVec.toInt * 8)` to make the example go through. Why?
theorem sib_example_correct [layout : Layout] (hwf : (layout sib_example).WellFormed) (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdi.toBitVec + BitVec.ofInt 64 (s₀.regs.r15.toBitVec.toInt * 8))) ⋆ R) :
    Eventually (step1 (layout sib_example))
      (fun s' => s'.1.regs.rax = 42)
      (s₀, layout.start) := by
  apply eventually_straightlineStep_cps (layout sib_example) hwf
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
  case h_len => exact Int.toBytes_length 8 _
  kstep
  tactic =>
  apply Eventually.done
  rfl

def alu_mem_example := parse("
    movq $42, %rax
    movq %rax, 136(%rdx)
    movq $100, %rcx
    addq 136(%rdx), %rcx
")

theorem alu_mem_example_correct [layout : Layout] (hwf : (layout alu_mem_example).WellFormed) (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (step1 (layout alu_mem_example))
      (fun s' => s'.1.regs.rcx = 142)
      (s₀, layout.start) := by
  apply eventually_straightlineStep_cps (layout alu_mem_example) hwf
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

theorem dynamic_stack_example_correct [layout : Layout] (hwf : (layout dynamic_stack_example).WellFormed) (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) R
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (step1 (layout dynamic_stack_example))
      (fun s' => s'.1.regs.rax = 42 ∧ s'.1.regs.rbx = 99 ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply eventually_straightlineStep_cps (layout dynamic_stack_example) hwf
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
