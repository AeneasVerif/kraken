module

/-
Kraken AArch64 - Example Programs

Demonstrates AArch64 proofs using the `kstep` stepping tactic.
-/

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.AArch64.Sep
import Kraken.Eval
import Kraken.SeparationTactics
import Kraken.Tactics
import Std.Tactic.BVDecide


open Kraken.AArch64
open Kraken.AArch64.Parser

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

--------------------------------------------------------------------------------

-- Register swap example using XOR
def swap : Program := ⸨prog|
  eor x0, x0, x1
  eor x1, x0, x1
  eor x0, x0, x1
⸩

theorem swap_correct [layout : WellFormedLayout swap] (d : MachineData) :
    Eventually (step1 swap.toExecutable)
      (fun s' =>
        s'.pc = swap.toExecutable.addrOf swap.length ∧
        s'.1.regs.getRegOrZr .X0 = d.regs.getRegOrZr .X1 ∧
        s'.1.regs.getRegOrZr .X1 = d.regs.getRegOrZr .X0)
      ⟨d, layout.start⟩ := by
  kprologue swap with d
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  grind

-- Example 3: Multi-instruction arithmetic and shift pipeline
def arith_shift : Program := ⸨prog|
  add x0, x1, #42
  lsl x2, x0, #2
  sub x3, x2, x0
⸩

theorem arith_shift_correct [layout : WellFormedLayout arith_shift] (d : MachineData) :
    Eventually (step1 arith_shift.toExecutable)
      (fun s' =>
        s'.pc = arith_shift.toExecutable.addrOf arith_shift.length ∧
        s'.1.regs.getRegOrZr .X3 = 3 * (d.regs.getRegOrZr .X1 + 42))
      ⟨d, layout.start⟩ := by
  kprologue arith_shift with d
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 42) = 42#64 from rfl,
    show (Int64.toInt 0).toNat = 0 from rfl]
  bv_decide

-- Example 4: Stepping through control flow (branch not taken)
def controlflow : Program := ⸨prog|
start:
  mov x0, #1
  eor x0, x0, x0
  cbnz x0, start
  mov x1, #42
⸩

theorem p4_correct [layout : WellFormedLayout controlflow] (d : MachineData) :
    Eventually (step1 controlflow.toExecutable)
      (fun s' => s'.pc = controlflow.toExecutable.addrOf controlflow.length ∧ s'.1.regs.X1 = 42)
      ⟨d, layout.start⟩ := by
  kprologue controlflow with d
  sym => kstep; tactic =>
  rename_i v v1
  have : v1 = 0 := by grind
  simp [this]
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 42) = 42#64 from rfl]
  bv_decide

-- Example 4b: Stepping through a taken branch to an internal label, then falling through
def controlflow_jump : Program := ⸨prog|
  mov x0, #2
loop:
  sub x0, x0, #1
  cbnz x0, loop
  mov x1, #42
⸩

theorem controlflow_jump_correct [layout : WellFormedLayout controlflow_jump] (d : MachineData) :
    Eventually (step1 controlflow_jump.toExecutable)
      (fun s' => s'.pc = controlflow_jump.toExecutable.addrOf controlflow_jump.length ∧ s'.1.regs.X1 = 42)
      ⟨d, layout.start⟩ := by
  kprologue controlflow_jump with d
  sym => kstep; tactic =>
  rename_i v v1
  have : v1 = 1 := by grind
  simp [this]
  sym => kstep; tactic =>
  rename_i v2
  have : v2 = 0 := by grind
  simp [this]
  sym => kstep; tactic =>
  refine .done _ ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [show BitVec.ofInt 64 (Int64.toInt 42) = 42#64 from rfl]
  bv_decide

-- Example 5: Storing and loading registers to/from memory
open Std
open Std.ExtHashMap

def move_2_regs_to_heap : Program := ⸨prog|
    str x0, [x2]
    str x1, [x2, #8]
    ldr x3, [x2]
    ldr x4, [x2, #8]
⸩

theorem move_2_regs_to_heap_correct [layout : WellFormedLayout move_2_regs_to_heap]
    (s₀ : MachineData)
    (v1 v2 : UInt64)
    (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.X2.toBitVec) ⋆ Eq (v2.At (s₀.regs.X2.toBitVec + 8#64)) ⋆ R) :
    Eventually (step1 move_2_regs_to_heap.toExecutable)
      (fun s' =>
        s'.pc = move_2_regs_to_heap.toExecutable.addrOf move_2_regs_to_heap.length ∧
        s'.1.regs.X3 = s₀.regs.X0 ∧
        s'.1.regs.X4 = s₀.regs.X1 ∧
        s'.1.regs.X2 = s₀.regs.X2)
      ⟨s₀, layout.start⟩ := by
  kprologue move_2_regs_to_heap with s₀

  have h_bs1 : v1.toBytes.length = 8 := UInt64.toBytes_length v1
  have h_bs2 : v2.toBytes.length = 8 := UInt64.toBytes_length v2
  have h_mem1 := Mem.storeInt_sep X2.toBitVec 8 v1.toBytes (Eq (v2.At (X2.toBitVec + 8#64)) ⋆ R) mem ⟨by ecancel, h_bs1⟩ X0.toBitVec.toInt
  have h_mem1' : (Eq (v2.At (X2.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 X0.toBitVec.toInt).At X2) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem1
  have h_mem2 := Mem.storeInt_sep (X2.toBitVec + 8#64) 8 v2.toBytes _ _ ⟨h_mem1', h_bs2⟩ X1.toBitVec.toInt
  have h_mem2' : (Eq ((Int.toBytes 8 X0.toBitVec.toInt).At X2) ⋆ (Eq ((Int.toBytes 8 X1.toBitVec.toInt).At (X2.toBitVec + 8#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2
  have h_mem2'' : (Eq ((Int.toBytes 8 X1.toBitVec.toInt).At (X2.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 X0.toBitVec.toInt).At X2.toBitVec) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2'
  simp at h_mem
  sym =>
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

-- Example 6: Memory access with shifted register offset [x1, x2, lsl #3]
def reg_offset_example : Program := ⸨prog|
    mov x0, #42
    str x0, [x1, x2, lsl #3]
    mov x0, #0
    ldr x3, [x1, x2, lsl #3]
⸩

theorem reg_offset_example_correct [layout : WellFormedLayout reg_offset_example]
    (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.X1.toBitVec + BitVec.ofInt 64 (s₀.regs.X2.toBitVec.toNat <<< 3))) ⋆ R) :
    Eventually (step1 reg_offset_example.toExecutable)
      (fun s' => s'.pc = reg_offset_example.toExecutable.addrOf reg_offset_example.length ∧
        s'.1.regs.X3 = 42)
      ⟨s₀, layout.start⟩ := by
  kprologue reg_offset_example with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem
  have h_mem' := Mem.storeInt_sep (X1.toBitVec + BitVec.ofInt 64 (X2.toBitVec.toNat <<< 3)) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
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
