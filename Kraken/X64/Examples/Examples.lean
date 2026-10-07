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
public import Kraken.ToBytes
import Kraken.Layout
import Std.Tactic.BVDecide
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
import Kraken.X64.Semantics
import Kraken.X64.Sep

open Kraken.X64.Parser

attribute [grind =] Int64.toBitVec_ofBitVec

attribute [ksimp]
  BitVec.add_zero
  BitVec.sub_zero
  BitVec.ofInt_add
  BitVec.ofInt_int64ToInt
  BitVec.ofInt_ofBytes_toBytes_64
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_toNat
  BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq
  BitVec.xor_self
  BitVec.zero_eq
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

@[ksimp]
theorem setWidth_add_address_size_W64 (a b : BitVec (AddressSize.mk Width.W64).address_size.bits) :
    BitVec.setWidth 64 (a + b) = BitVec.setWidth 64 a + BitVec.setWidth 64 b := rfl

@[ksimp]
theorem setWidth_ofInt_address_size_W64 (i : Int) :
    BitVec.setWidth 64 (BitVec.ofInt (AddressSize.mk Width.W64).address_size.bits i) = BitVec.ofInt 64 i := rfl

@[ksimp]
theorem setWidth_ofNat_address_size_W64 (n : Nat) :
    BitVec.setWidth 64 (BitVec.ofNat (AddressSize.mk Width.W64).address_size.bits n) = BitVec.ofNat 64 n := rfl

@[ksimp]
theorem toInt_ofNat_address_size_W64 (n : Nat) :
    (BitVec.ofNat (AddressSize.mk Width.W64).address_size.bits n).toInt = (BitVec.ofNat 64 n).toInt := rfl

@[ksimp]
theorem natCast_8 : ((8 : Nat) : Int) = (8 : Int) := rfl

--------------------------------------------------------------------------------

def p1 := parse("start: mov $1, %rax")

-- Super-simple example to debug tactics
example [layout : Layout] (hwf : (layout p1).WellFormed) s :
    Eventually (step1 (layout p1)) (fun s => s.1.regs.rax = 1) (s, layout.start) := by
  kprologue p1 with s
  sym => kstep ( debug := true ); tactic => apply Eventually.done; grind

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
  kprologue swap with d
  sym => kstep; tactic => intros; apply Eventually.done; grind

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
  kprologue p2 with s
  sym => kstep; tactic => intros; apply Eventually.done; grind

-- Example 3, more sophisticated

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

@[grind =]
def p3_spec (s: MachineData): Nat := 2^(2^s.regs.rbx.toNat)

@[ksimp, grind =]
private theorem int64_rel_jmp_target (u tgt : Int64) :
    Int64.ofBitVec (u + (tgt - u)).toBitVec = tgt := by
  grind

private theorem p3_pow_step {n v : Nat} (hv0 : v ≠ 0) (hle : v ≤ n) (hb : 2 ^ 2 ^ n < 2 ^ 64) :
    let prod := (BitVec.ofNat 64 (2 ^ 2 ^ (n - v))).unsigned * (BitVec.ofNat 64 (2 ^ 2 ^ (n - v))).unsigned
    (UInt64.ofBitVec (BitVec.ofNat 64 v - 1#64)).toNat = v - 1 ∧
    v - 1 ≤ n ∧
    v - 1 < v ∧
    (UInt64.ofBitVec (BitVec.ofInt 64 prod)).toNat = 2 ^ 2 ^ (n - (v - 1)) ∧
    UInt64.ofBitVec (BitVec.ofInt 64 (prod >>> 64)) = 0 := by
  have : n < 6 := by
    have := fun (h : 6 ≤ n) => Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pow_le_pow_right (by decide : 0 < 2) h)
    grind
  rcases (by grind : (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) ∧ (v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5)) with
    ⟨rfl | rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl | rfl⟩ <;> (first | decide | grind)

grind_pattern p3_pow_step =>
  (BitVec.ofNat 64 (2 ^ 2 ^ (n - v))).unsigned * (BitVec.ofNat 64 (2 ^ 2 ^ (n - v))).unsigned

theorem p3_correct [layout: Layout] (h : (layout p3).WellFormed)
    (hlayout : layout.Valid p3) (s : MachineData)
    (hrax : s.regs.rax = 0) (hb : p3_spec s < 2^64) :
    Eventually (step1 (layout p3))
      (fun s' => s'.1.regs.rdx.toNat = p3_spec s ∧ s'.1.regs.rax = 0)
      (s, layout.start) := by
  let pc_start := layout.start + Int64.ofNat (layout.size 0) + Int64.ofNat (layout.size 1)
  kprologue p3 with s
  sym =>
  kstep 1
  tactic =>
  apply tailrec_loop_straightline _ h
    (fun s' => s'.1.regs.rdx.toNat = 2 ^ (2 ^ rbx.toNat) ∧ s'.1.regs.rax = 0)
    (_, pc_start)
    (fun v st =>
      st.2 = pc_start ∧
      st.1.regs.rbx.toNat = v ∧
      v ≤ rbx.toNat ∧
      st.1.regs.rdx.toNat = 2 ^ (2 ^ (rbx.toNat - v)) ∧
      st.1.regs.rax = 0)
    rbx.toNat
  · grind
  · rintro v ⟨⟨⟨rax', rbx', rcx', rdx', rsi', rdi', rsp', rbp', r8', r9', r10', r11', r12', r13', r14', r15'⟩, zmms', flags', mem'⟩, pc'⟩ ⟨rfl, hrbx, hle, hrdx, hrax_st⟩
    dsimp only [pc_start] at *
    by_cases hv0 : v = 0
    · subst hv0
      sym => kstep; tactic => apply Eventually.done; grind
    · have h_cond : (BitVec.ofNat 64 v == 0#64) = false := by grind
      sym => kstep; tactic => apply Eventually.done; grind

def p4 := eval% parse("start: mov $2, %rax
dec %rax")

-- Super-simple example to debug tactics
example [layout : Layout] (hwf : (layout p4).WellFormed) s :
    Eventually (step1 (layout p4)) (fun s => s.1.regs.rax = 1) (s, layout.start) := by
  kprologue p4 with s
  sym => kstep; tactic => apply Eventually.done; grind

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
  kprologue p5 with s
  sym => kstep; tactic => apply Eventually.done; grind

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
  kprologue p6 with s₀
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 stack R mem ⟨h_mem, h_len⟩ rax.toBitVec.toInt
  sym => kstep; tactic => apply Eventually.done; grind

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
  kprologue move_2_regs_to_heap with s₀
  have h_mem1 := Mem.storeInt_sep rdi.toBitVec 8 v1.toBytes (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ R) mem ⟨by ecancel, by grind⟩ rax.toBitVec.toInt
  have h_mem2 := Mem.storeInt_sep (rdi.toBitVec + 8#64) 8 v2.toBytes (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi.toBitVec) ⋆ R) _ ⟨by ecancel, by grind⟩ rcx.toBitVec.toInt
  sym => kstep; tactic => apply Eventually.done; grind

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
  kprologue sib_example with s₀
  have h_mem' := Mem.storeInt_sep (rdi.toBitVec + BitVec.ofInt 64 (r15.toBitVec.toInt * 8)) 8 v.toBytes R mem ⟨h_mem, by grind⟩ 42
  sym => kstep; tactic => apply Eventually.done; grind

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
  kprologue alu_mem_example with s₀
  have h_mem1 := Mem.storeInt_sep (rdx.toBitVec + 136#64) 8 v.toBytes R mem ⟨h_mem, by grind⟩ 42
  sym => kstep; tactic => apply Eventually.done; grind

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
  kprologue dynamic_stack_example with s₀
  rw [(List.take_append_drop 1016 stack).symm] at h_mem
  have h_At_append := Mem.At_append_sep (w := 64) (stack.take 1016) (stack.drop 1016) (rsp.toBitVec - 1024#64) (by grind)
  change (Eq ((stack.take 1016 ++ stack.drop 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem at h_mem
  have h_addr_eq : rsp.toBitVec - 1024#64 + BitVec.ofNat 64 (stack.take 1016).length = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8) := by grind
  rw [h_At_append, h_addr_eq] at h_mem
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)) 8 (stack.drop 1016) (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem ⟨by ecancel, by grind⟩ 99

  sym =>
  kstep
  case bs => exact []
  case R => exact R
  case h_mem => tactic => sorry
  case h_len => tactic => sorry
  sorry
  -- kstep
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- -- FIXME: kstep here takes too long
  -- done
