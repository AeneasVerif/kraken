import Kraken.AArch64.Parser
import Kraken.AArch64.Tactics
import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Sep

open Kraken.AArch64.Parser

-- Example 1: Straightline arithmetic in AArch64
def addTriple : Program := parseAArch64("
  add x0, x1, #10
  add x0, x0, x2
")

theorem addTriple_correct [layout : Layout] (d : MachineData) :
      Eventually (straightlineStep (layout addTriple))
      (fun s' =>
          (s'.1.regs.getRegOrZr .X0 : BitVec 64) =
          d.regs.getRegOrZr .X1 + 10 + d.regs.getRegOrZr .X2)
      (d, layout.start) := by
  dsimp [addTriple]
  apply step_cps
  dsimp only [straightlineStep, Executable.straightline, Directives.interp]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]

  sym =>
  kstep_aarch64
  tactic =>
  simp
  sym =>
  kstep_aarch64
  tactic =>
  apply Eventually.done
  simp

  bv_decide

-- Example 2: Stack store and load using SP, requiring SP 16-byte alignment
def spCopy : Program := parseAArch64("
  str x1, [sp]
  ldr x0, [sp]
")

theorem spCopy_correct [layout : Layout] (d : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (hAligned : d.regs.SP.toBitVec % 16#64 = 0#64)
    (h_mem : d.dmem =⋆ Eq (stack.At d.regs.SP.toBitVec) ⋆ R) :
      Eventually (straightlineStep (layout spCopy))
      (fun s' =>
          (s'.1.regs.getRegOrZr .X0 : BitVec 64) =
          d.regs.getRegOrZr .X1)
      (d, layout.start) := by
  have hsp : BitVec.ofNat 64 (d.regs.SP.toBitVec.toNat >>> 0) = d.regs.SP.toBitVec := by dsimp; exact BitVec.ofNat_toNat 64 _
  have haddr : BitVec.ofInt 64 (d.regs.SP.toBitVec.signed + Int64.toInt 0) = d.regs.SP.toBitVec := by
    dsimp [BitVec.signed]; rw [Int.add_zero]; exact BitVec.ofInt_toInt
  have hval : BitVec.ofNat 64 (d.regs.X1.toBitVec.toNat >>> 0) = d.regs.X1.toBitVec := by dsimp; exact BitVec.ofNat_toNat 64 _
  dsimp [spCopy]
  apply step_cps
  dsimp only [straightlineStep, Executable.straightline, Directives.interp]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]

  sym =>
  kstep_aarch64
  tactic =>
  split <;> try grind
  rw [hsp, haddr, hval]
  have h_mem1 := Mem.storeInt_sep d.regs.SP.toBitVec 8 stack R d.dmem ⟨h_mem, h_len⟩ d.regs.X1.toBitVec.toInt
  rw [store_sep (h_mem := h_mem)]
  case h_len => exact h_len

  sym =>
  kstep_aarch64
  tactic =>
  split <;> try grind
  rw [hsp, haddr]
  rw [load_sep (h_mem := h_mem1)]
  case h_len => exact Int.toBytes_length 8 _

  sym =>
  kstep_aarch64
  tactic =>
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, hval]

-- Example 3: ADDS with flag setting
def addsExample : Program := parseAArch64("
  adds x0, x1, #10
")

theorem addsExample_correct [layout : Layout] (d : MachineData) :
      Eventually (straightlineStep (layout addsExample))
      (fun s' =>
          (s'.1.regs.getRegOrZr .X0 : BitVec 64) =
          d.regs.getRegOrZr .X1 + 10 ∧
          s'.1.status = StatusFlags.from_result (d.regs.getRegOrZr .X1 + 10 : BitVec 64) {
            c := (d.regs.getRegOrZr .X1 + 10 : BitVec 64).unsigned != (d.regs.getRegOrZr .X1 : BitVec 64).unsigned + 10,
            v := (d.regs.getRegOrZr .X1 + 10 : BitVec 64).signed != (d.regs.getRegOrZr .X1 : BitVec 64).signed + 10 })
      (d, layout.start) := by
  have h1 : (10#64).unsigned = 10 := by rfl
  have h2 : (10#64).signed = 10 := by rfl
  dsimp [addsExample]
  apply step_cps
  dsimp only [straightlineStep, Executable.straightline, Directives.interp]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]

  sym =>
  kstep_aarch64
  tactic =>
  apply Eventually.done
  simp [h1, h2]
