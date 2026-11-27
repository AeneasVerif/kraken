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
import Kraken.X64.Semantics
meta import Kraken.X64.Semantics
import Kraken.X64.Sep

open Kraken (Layout)
open Kraken.X64.Parser

--------------------------------------------------------------------------------

def p1 : Program := ⸨prog| start: mov $1, %rax ⸩

-- Super-simple example to debug tactics
example (layout : Layout) [p1.AssemblableWith layout] s :
    Eventually (step1 (layout.apply p1))
      (fun s => s.pc = (layout.apply p1).addrOf p1.length ∧ s.1.regs.rax = 1) ⟨s, layout.start⟩ := by
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

theorem swap_correct (layout : Layout) [swap.AssemblableWith layout] (d : MachineData) :
    Eventually (step1 (layout.apply swap))
      (fun s' =>
        s'.pc = (layout.apply swap).addrOf swap.length ∧
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
example (layout : Layout) [p2.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply p2))
      (fun s => s.pc = (layout.apply p2).addrOf p2.length ∧ s.1.regs.rax = 2) ⟨s, layout.start⟩ := by
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
example (layout : Layout) [p2_jump.AssemblableWith layout] (s : MachineData) :
    Eventually (step1 (layout.apply p2_jump))
      (fun s => s.pc = (layout.apply p2_jump).addrOf p2_jump.length ∧ s.1.regs.rax = 42)
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

def p3: Program := ⸨prog|
init:
  mov $2, %rdx             -- rdx: current result = 2
start:
  sub $0, %rbx             -- TEST: zf = (rbx == 0)
  jz _end                 -- end loop if rbx == 0
  mulx %rdx, %rdx, %rax    -- BODY: rdx := rdx * rdx
  sub $1, %rbx              -- rbx -= 1
  jmp start               -- go back to test & loop body
_end:
  nop⸩

def p3_spec (s: MachineData): Nat := 2^(2^s.regs.rbx.toNat)

theorem p3_correct (layout : Layout) [p3.AssemblableWith layout] (s : MachineData) :
    p3_spec s < 2 ^ 64 →
    Eventually (step1 (layout.apply p3))
      (fun s' => s'.pc = (layout.apply p3).addrOf p3.length ∧
        s'.1.regs.rdx.toNat = p3_spec s ∧
        (0 < s.regs.rbx.toNat → s'.1.regs.rax = 0))
      ⟨s, layout.start⟩ := by
  intro h_bounds
  unfold p3_spec at h_bounds ⊢
  change Eventually (step1 (layout.apply p3)) _ ⟨s, (layout.apply p3).startAddr⟩
  rw [← Kraken.Executable.addrOf_zero]
  sym => kstep 1; tactic =>
  refine tailrec_loop
    (onLoop := fun i st =>
      st.pc = (layout.apply p3).addrOf 2 ∧
      st.1.regs.rbx.toNat = i ∧
      i ≤ s.regs.rbx.toNat ∧
      st.1.regs.rdx.toNat = 2 ^ (2 ^ (s.regs.rbx.toNat - i)) ∧
      (i < s.regs.rbx.toNat → st.1.regs.rax = 0))
    (onExit := fun _ st =>
      st.pc = (layout.apply p3).addrOf p3.length ∧
      st.1.regs.rdx.toNat = 2 ^ 2 ^ s.regs.rbx.toNat ∧
      (0 < s.regs.rbx.toNat → st.1.regs.rax = 0))
    (· < ·) Nat.lt_wfRel.wf s.regs.rbx.toNat ?_ ?_ (fun _ h => h)
  · exact ⟨rfl, rfl, Nat.le_refl _, by rw [Nat.sub_self]; rfl, fun h => absurd h (Nat.lt_irrefl _)⟩
  · rintro k ⟨d, pc⟩ ⟨hpc, h_rbx_k, h_k_le, h_rdx, h_rax⟩
    dsimp only at hpc h_rbx_k h_rdx h_rax
    subst hpc
    by_cases hk : k = 0
    · subst hk
      sym => kstep 2; tactic =>
      rename_i v status
      have hv : v = 0 := by grind
      simp [hv]
      sym => kstep; tactic =>
      exact .done _ (.break ⟨rfl, by simpa using h_rdx, h_rax⟩)
    · sym => kstep 2; tactic =>
      rename_i v status
      have hzf : (v == BitVec.zero 64) = false := by grind
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      sym => kstep 3; tactic =>
      rename_i b_mul v_mul _ _ v_sub status'
      have h_pow_eq : d.regs.rdx.toNat * d.regs.rdx.toNat = 2 ^ 2 ^ (s.regs.rbx.toNat - (k - 1)) := by
        rw [h_rdx, show s.regs.rbx.toNat - (k - 1) = (s.regs.rbx.toNat - k) + 1 by omega]
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
      have h_prod_lt : d.regs.rdx.toNat * d.regs.rdx.toNat < 2 ^ 64 := by
        rw [h_pow_eq]
        refine Nat.lt_of_le_of_lt ?_ h_bounds
        apply Nat.pow_le_pow_right (by decide)
        apply Nat.pow_le_pow_right (by decide)
        omega
      have hv_mul : v_mul = ↑(d.regs.rdx.toNat * d.regs.rdx.toNat) := by
        dsimp [v_mul, b_mul, BitVec.unsigned] <;> grind
      refine .done _ (.loop (k - 1) ⟨rfl, ?_, by omega, ?_, ?_⟩ (by omega) (fun _ h => h))
      · grind
      · dsimp only
        rw [hv_mul, ← h_pow_eq]
        change (BitVec.ofNat 64 (d.regs.rdx.toNat * d.regs.rdx.toNat)).toNat =
          d.regs.rdx.toNat * d.regs.rdx.toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_prod_lt]
      · intro _
        dsimp only
        rw [hv_mul]
        change ({ toBitVec := BitVec.ofNat 64 ((d.regs.rdx.toNat * d.regs.rdx.toNat) >>> 64) } : UInt64) = 0
        have h_shr : (d.regs.rdx.toNat * d.regs.rdx.toNat) >>> 64 = 0 :=
          Nat.shiftRight_eq_div_pow _ _ ▸ Nat.div_eq_of_lt h_prod_lt
        rw [h_shr]
        rfl

def p4 : Program := eval% ⸨prog|start: mov $2, %rax
dec %rax⸩

-- Super-simple example to debug tactics
example (layout : Layout) [p4.AssemblableWith layout] s :
    Eventually (step1 (layout.apply p4))
      (fun s => s.pc = (layout.apply p4).addrOf p4.length ∧ s.1.regs.rax = 1) ⟨s, layout.start⟩ := by
  kprologue p4 with s
  sym =>
  kstep
  -- intros
  tactic =>
  exact .done _ ⟨rfl, rfl⟩

/- Examples -/

def p5 : Program := ⸨prog|start: mov $2, %rax
dec %rax
start2:
dec %rax⸩

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.all true -/

example (layout : Layout) [p5.AssemblableWith layout] s :
    Eventually (step1 (layout.apply p5))
      (fun s => s.pc = (layout.apply p5).addrOf p5.length ∧ s.1.regs.rax = 0) ⟨s, layout.start⟩ := by
  kprologue p5 with s
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  dsimp only
  bv_decide

def p6 : Program := ⸨prog|push %rax
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

theorem p6_correct (layout : Layout) [p6.AssemblableWith layout] (s₀ : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 8#64)) ⋆ R) :
    Eventually (step1 (layout.apply p6))
      (fun s' => s'.pc = (layout.apply p6).addrOf p6.length ∧
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
theorem p7_correct (layout : Layout) [p7.AssemblableWith layout] (s₀ : MachineData) (R : DataMem → Prop)
    (h_mem : let := Executable.labels (layout.apply p7)
      s₀.dmem =⋆ Eq ((Int.toBytes 4 (label! "end" - label! "start").toInt).At (label! "size").toBitVec) ⋆ R) :
    Eventually (step1 (layout.apply p7))
      (fun s' => let := Executable.labels (layout.apply p7)
        s'.pc = (layout.apply p7).addrOf p7.length ∧
        s'.1.regs.rax = UInt64.ofBitVec (((label! "end" - label! "start").toBitVec.setWidth 32).setWidth 64))
      ⟨s₀, layout.start⟩ := by
  have h_addr (X Y : Int64) :
      (BitVec.ofInt 64 X.toInt + BitVec.ofInt 64 (Y - X).toInt).setWidth 64
        = Y.toBitVec := by
    simp only [BitVec.setWidth_eq, Int64.toInt, BitVec.ofInt_toInt, Int64.toBitVec_sub]
    grind
  have h_val (v : Int64) :
      BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v.toInt)) = v.toBitVec.setWidth 32 := by
    rw [ofBytes_toBytes, Int.take, show 8 * 4 = 32 from rfl, Int64.toInt,
      ← BitVec.signExtend_eq_setWidth_of_le _ (by decide)]
    simp [BitVec.ofInt, BitVec.signExtend]
  have h_size : @Labels.label? (Executable.labels (layout.apply p7)) "size" = some ((layout.apply p7).addrOf 6) :=
    label?_eq_some_addrOf (p := p7) (l := layout) rfl
  kprologue p7 with s₀
  sym =>
  kstep
  case h_mem => tactic => dsimp only; rw [h_addr, ← Labels.label!_of_label? h_size]; exact h_mem
  case h_len => exact Int.toBytes_length 4 _
  kstep
  tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp only [h_val, Int64.toBitVec_sub,
    Labels.label!_of_label? (label?_eq_some_addrOf (p := p7) (l := layout) (lbl := "end") rfl),
    Labels.label!_of_label? (label?_eq_some_addrOf (p := p7) (l := layout) (lbl := "start") rfl)]

-- The same run under `fakeLayout`, where the nops take 5 + 3 bytes. The eval plays the loader: it
-- stores the word's value at `size`.
/-- info: Except.ok 8 -/
#guard_msgs in
#eval
  let exe := p7.fakeLayout
  let := exe.labels
  let word : Int64 := label! "end" - label! "start"
  let data : MachineData := { dmem := Mem.storeInt {} (label! "size").toBitVec 4 word.toInt }
  (Executable.eval exe {data, pc := label! "start"} (fun st => st.pc = label! "done")).bind
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

def move_2_regs_to_heap : Program := ⸨prog|
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
⸩

theorem move_2_regs_to_heap_correct (layout : Layout) [move_2_regs_to_heap.AssemblableWith layout]
    (s₀ : MachineData) (v1 v2 : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆
      Eq (v2.At (s₀.regs.rdi.toBitVec + 8#64)) ⋆ R) :
    Eventually (step1 (layout.apply move_2_regs_to_heap))
      (fun s' =>
        s'.pc = (layout.apply move_2_regs_to_heap).addrOf move_2_regs_to_heap.length ∧
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

def sib_example : Program := ⸨prog|
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax⸩

-- FIXME: I had to replace `s₀.regs.r15.toBitVec * 8#64` with `BitVec.ofInt 64
-- (s₀.regs.r15.toBitVec.toInt * 8)` to make the example go through. Why?
theorem sib_example_correct (layout : Layout) [sib_example.AssemblableWith layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdi.toBitVec + BitVec.ofInt 64 (s₀.regs.r15.toBitVec.toInt * 8))) ⋆ R) :
    Eventually (step1 (layout.apply sib_example))
      (fun s' => s'.pc = (layout.apply sib_example).addrOf sib_example.length ∧ s'.1.regs.rax = 42)
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

def alu_mem_example : Program := ⸨prog|
    movq $42, %rax
    movq %rax, 136(%rdx)
    movq $100, %rcx
    addq 136(%rdx), %rcx⸩

theorem alu_mem_example_correct (layout : Layout) [alu_mem_example.AssemblableWith layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (step1 (layout.apply alu_mem_example))
      (fun s' => s'.pc = (layout.apply alu_mem_example).addrOf alu_mem_example.length ∧
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

def dynamic_stack_example : Program := ⸨prog|
    movq $99, -8(%rsp)
    movq %rsp, %rbp
    leaq -1024(%rsp, %r9, 8), %rsp
    movq $42, %rax
    movq %rax, 16(%rsp, %r15, 8)
    movq $0, %rax
    movq 16(%rsp, %r15, 8), %rax
    movq %rbp, %rsp
    movq -8(%rsp), %rbx⸩

theorem dynamic_stack_example_correct (layout : Layout) [dynamic_stack_example.AssemblableWith layout]
    (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) R
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (step1 (layout.apply dynamic_stack_example))
      (fun s' => s'.pc = (layout.apply dynamic_stack_example).addrOf dynamic_stack_example.length ∧
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
