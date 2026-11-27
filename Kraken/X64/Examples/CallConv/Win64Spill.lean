module

import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.X64.Sep
public import Kraken.X64.ProcSpec
public import Kraken.X64.Win64

/-!
# A Windows x64 procedure whose correctness depends on stack alignment

`win64_spill` copies `xmm0` to `xmm1` through a 16-byte stack slot with `movaps`, which faults
(`#GP`) on an address that is not 16-byte aligned. It allocates 24 bytes, so the slot at the new
`rsp` is aligned exactly when `rsp + 8` was aligned on entry.
-/

open Kraken (Layout)
open Kraken.X64
open Kraken.X64.Parser
open Kraken.X64.Stack
open Kraken.X64.Win64
open Std.ExtHashMap

public section

namespace CallConv.Win64Spill

def prog : Program := ⸨prog|
win64_spill:
  subq $24, %rsp
  movaps %xmm0, (%rsp)
  movaps (%rsp), %xmm1
  addq $24, %rsp
  ret⸩

/-- The procedure's 24-byte reservation: the aligned 16-byte slot and 8 bytes of padding. -/
theorem reserve24_eq (r : BitVec 64) :
    Reserve 24 r = Owned 16 (r - 24) ⋆ Owned 8 (r - 8) := by
  rw [Reserve, show (24 : Nat) = 16 + 8 from rfl, Owned.split 16 8 _ (by omega)]
  congr 2 <;> bv_omega

variable (layout : Layout) [prog.AssemblableWith layout]

theorem spill_spec (R : Mem 64 → Prop) (ra : Int64) :
    (layout.apply prog).ProcSpec
      (@Labels.label! (Executable.labels (layout.apply prog)) "win64_spill") ra
      (fun t => Win64.Call 24 R ra t)
      (fun t s => Win64.Ret 24 R ra t s ∧ s.zmms.get (.xmm .mm1) = t.zmms.get (.xmm .mm0)) := by
  rw [Labels.label!_of_label? (label?_eq_some_addrOf (p := prog) (l := layout) (k := 0) rfl)]
  rintro t ⟨hal, hdf, hmem⟩
  rw [reserve24_eq, sep_assoc, sep_comm_l (Shadow _) (Owned 16 _),
    sep_comm_l (RetCell _ _) (Owned 16 _)] at hmem
  obtain ⟨bs, hbs, hmem⟩ := Owned.elim hmem
  have ex : ∀ x : BitVec 64, BitVec.extractLsb' 0 64 x = x := fun x => by ext i; simp
  have hal' : t.regs.rsp.toBitVec.toNat % 16 = 8 := hal
  have haligned : isAligned AvxWidth.W128.bytes (t.regs.rsp.toBitVec - 24) := by
    simp only [isAligned, AvxWidth.bytes, beq_iff_eq]; bv_omega
  have hslot := Mem.loadInt_sep bs _ 16 _ _ hmem hbs (by decide)
  have hmem' := Mem.storeInt_sep _ 16 bs _ _ ⟨hmem, hbs⟩ (t.zmms.get (AvxReg.xmm .mm0)).toInt
  have hval := Mem.loadInt_sep _ _ 16 _ _ hmem' (Int.toBytes_length _ _) (by decide)
  sym =>
  kstep 2
  tactic =>
  -- `kstep` does not step AVX instructions yet: step `movaps %xmm0, (%rsp)` by hand.
  simp only [AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy]
  simp (config := { zetaDelta := true }) only [AddrExpr.interp, ConstExpr.interp]
  simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, Reg64s.get64,
    BitVec.toAddressSize, BitVec.signed, BitVec.take, Int.add_zero, BitVec.ofInt_toInt, ex,
    Width.bits, Int64.toInt_zero]
  refine @Effects.All_storeAvx (Executable.labels (layout.apply prog)) _ _ _ _ _ _ _ _
    (fun _ => haligned)
    (show Mem.loadInt t.dmem (t.regs.rsp.toBitVec - 24) 16 = _ from hslot) ?_
  simp only [Effects.All]
  sym =>
  kstep 1
  tactic =>
  -- `movaps (%rsp), %xmm1`
  simp only [AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy]
  simp (config := { zetaDelta := true }) only [AddrExpr.interp, ConstExpr.interp]
  simp only [BitVec.setWidth_eq, Reg64s.get64, BitVec.toAddressSize, BitVec.signed,
    BitVec.take, Int.add_zero, BitVec.ofInt_toInt, ex, Width.bits, Int64.toInt_zero]
  refine @Effects.All_loadAvx (Executable.labels (layout.apply prog)) _ _ _ _ _ _ _
    (fun _ => haligned)
    (show Mem.loadInt (Mem.storeInt t.dmem (t.regs.rsp.toBitVec - 24) 16
      (t.zmms.get (AvxReg.xmm .mm0)).toInt) (t.regs.rsp.toBitVec - 24) 16 = _ from hval) ?_
  simp only [Effects.All, MachineData.setAvxLegacyReg]
  rw [show BitVec.ofInt AvxWidth.W128.bits
      (Int.ofBytes (Int.toBytes 16 (t.zmms.get (AvxReg.xmm .mm0)).toInt))
    = t.zmms.get (AvxReg.xmm .mm0) from BitVec.ofInt_ofBytes_toBytes 128 16 rfl _]
  have hret := hmem'
  rw [sep_comm_l] at hret
  have eret : 24#64 + (t.regs.rsp.toBitVec - 24#64) = t.regs.rsp.toBitVec := by bv_omega
  sym =>
  kstep
  case h_mem => tactic =>
    rename_i v st r
    have hr : r = t.regs.rsp.toBitVec := by
      simp only [r, v, BitVec.ofNat_toNat, BitVec.setWidth_eq, Nat.shiftRight_zero]
      bv_omega
    rw [hr]
    exact hret
  case h_len => exact Int.toBytes_length _ _
  kstep 0
  tactic =>
  rename_i v st r
  have hr : r = t.regs.rsp.toBitVec := by
    simp only [r, v, BitVec.ofNat_toNat, BitVec.setWidth_eq, Nat.shiftRight_zero]
    bv_omega
  have hxmm1 : ∀ (o : BitVec 512) (v : BitVec 128),
      (BitVec.setWidth 512 (BitVec.extractLsb' 128 384 o ++ v)).extractLsb' 0 128 = v := by
    intro o v; ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
      Nat.zero_add, hi, ite_true, BitVec.getLsbD_eq_getElem hi]
    rw [decide_eq_true (Nat.lt_trans hi (by decide : 128 < 512)), Bool.true_and]
  refine Eventually.done _ ⟨?_, ⟨?_, hdf, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · show r + 8 = _
    rw [hr]
  iterate 10
    · simp [RegZmms.setLegacy, RegZmms.set512, RegZmms.get, RegZmms.get512, AvxReg.base]
  · refine Owned.intro (sep_mono (fun _ h => h) (fun m hm => ?_) hret) (Int.toBytes_length _ _)
    rw [sep_comm_l] at hm
    refine sep_mono (fun _ h => h) (fun m' hm' => ?_) hm
    show (Reserve 24 _ ⋆ R) m'
    rw [reserve24_eq, sep_assoc]
    exact Owned.intro hm' (Int.toBytes_length _ _)
  · simp only [RegZmms.setLegacy, RegZmms.set512, RegZmms.get, RegZmms.get512, AvxReg.base,
      BitVec.replaceLow, BitVec.take, BitVec.drop, AvxWidth.bits]
    exact hxmm1 _ _

end CallConv.Win64Spill
