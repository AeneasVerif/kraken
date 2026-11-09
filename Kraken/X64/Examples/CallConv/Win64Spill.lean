module

import Kraken.X64.Parser
public import Kraken.X64.WP.Call
import Kraken.X64.Examples.CallConv.RunStep
public import Kraken.Win64

/-!
# A Windows x64 procedure whose correctness depends on stack alignment

`win64_spill` copies `xmm0` to `xmm1` through a 16-byte stack slot with `movaps`, which faults
(`#GP`) on an address that is not 16-byte aligned. It allocates 24 bytes, so the slot at the new
`rsp` is aligned exactly when `rsp + 8` was aligned on entry: the `EntryAligned` conjunct of
`Win64.CallPre` is what the proof of `spill_spec` uses for the two `movaps`.
-/

open Kraken.X64.Parser
open Kraken.Stack
open Kraken.Win64
open Std.ExtHashMap

public section

namespace CallConv.Win64Spill

def spill_body : Program := parse("
win64_spill:
  subq $24, %rsp
  movaps %xmm0, (%rsp)
  movaps (%rsp), %xmm1
  addq $24, %rsp
  ret
")

/-- A procedure entered with `rsp + 8` aligned that moves `rsp` down by 24 has `rsp` aligned. -/
private theorem aligned_sub_24 {r : BitVec 64} (h : r.toNat % 16 = 8) : (r - 24).toNat % 16 = 0 := by
  bv_omega

private theorem add_sub_cancel_left (d r : BitVec 64) : d + (r - d) = r := by bv_omega

/-- The procedure's 24-byte reservation: the aligned 16-byte slot and 8 bytes of padding. -/
theorem reserve24_eq {r : BitVec 64} (h : 24 ≤ r.toNat) :
    Reserve 24 r = Owned 16 (r - 24) ⋆ Owned 8 (r - 8) := by
  have h1 := Owned.split 16 8 (r - .ofNat 64 24) (by omega)
  simp only [Nat.reduceAdd] at h1
  have e : r - BitVec.ofNat 64 24 + BitVec.ofNat 64 16 = r - 8 := by bv_omega
  rw [Reserve_eq 24 r h, h1, e]
  rfl

variable [Host]

theorem spill_spec {j : Nat} (hj : spill_body.IsInfixAt Host.prog j) :
    Host.exe.ProcSpec (Host.addrOf j)
      (fun (R : Mem 64 → Prop) ra t => CallPre 24 R ra t)
      (fun R ra t s => CallPost 24 R ra t s
        ∧ s.zmms.get (.xmm .mm1) = t.zmms.get (.xmm .mm0)) := by
  rintro R ra t ⟨hal, hdf, hmem⟩
  have h1 := hj.cons.2
  have h2 := h1.cons.2
  have h3 := h2.cons.2
  have h4 := h3.cons.2
  have h5 := h4.cons.2
  -- the slot to the head of the tree
  have hle := Reserve.le_third hmem
  rw [reserve24_eq hle, sep_assoc, sep_comm_l (Shadow _) (Owned 16 _),
    sep_comm_l (RetCell _ _) (Owned 16 _)] at hmem
  obtain ⟨bs, hbs, hmem⟩ := Owned.elim hmem
  have hslot := Mem.loadInt_sep bs _ 16 _ _ hmem hbs (by decide)
  have haligned : isAligned AvxWidth.W128.bytes (t.regs.get64 .rsp - 24) := by
    unfold isAligned; rw [beq_iff_eq]; exact aligned_sub_24 hal
  have e24 : BitVec.truncate Width.W64.bits (Int64.toBitVec 24) = 24 := rfl
  have e0 : ∀ x : BitVec 64, x + Int64.toBitVec 0 = x := BitVec.add_zero
  run_step hj
  -- subq $24, %rsp
  run_step h1 [e24]
  -- movaps %xmm0, (%rsp)
  run_step h2 [AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy,
      AddrExpr.interp_reg_disp, e0]
  refine Effects.All_storeAvx (fun _ => haligned) (by simp only []; rw [hslot]; rfl) ?_
  simp only [Effects.All]
  have hmem' := Mem.storeInt_sep _ 16 bs _ _ ⟨hmem, hbs⟩ (t.zmms.get (AvxReg.xmm .mm0)).toInt
  have hval := Mem.loadInt_sep _ _ 16 _ _ hmem' (Int.toBytes_length _ _) (by decide)
  -- movaps (%rsp), %xmm1
  run_step h3 [AvxOperation.interp, AvxRegOrMem.interp, MachineData.setAvxLegacy,
      AddrExpr.interp_reg_disp, e0]
  refine Effects.All_loadAvx (fun _ => haligned) hval ?_
  simp only [Effects.All, MachineData.setAvxLegacyReg]
  rw [show BitVec.ofInt AvxWidth.W128.bits
      (Int.ofBytes (Int.toBytes 16 (t.zmms.get (AvxReg.xmm .mm0)).toInt))
    = t.zmms.get (AvxReg.xmm .mm0) from BitVec.ofInt_ofBytes_toBytes 128 16 rfl _]
  -- addq $24, %rsp
  run_step h4 [e24, add_sub_cancel_left]
  -- ret
  rw [sep_comm_l] at hmem'
  have hret := Mem.loadInt_sep _ _ 8 _ _ hmem' (Int.toBytes_length _ _) (by decide)
  run_step h5
  refine Effects.All_load (w := .W64) hret ?_
  simp only [Effects.All]
  refine Eventually.done _ ⟨?_, ?_, ?_⟩
  · show Int64.ofBitVec (BitVec.ofInt 64 _) = ra
    rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · refine ⟨?_, hdf, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    any_goals simp [Reg64s.get64_set64, RegZmms.setLegacy, RegZmms.set512, RegZmms.get,
      RegZmms.get512, AvxReg.base]
    refine Owned.intro (sep_mono (fun _ h => h) (fun m hm => ?_) hmem') (Int.toBytes_length _ _)
    rw [sep_comm_l] at hm
    refine sep_mono (fun _ h => h) (fun m' hm' => ?_) hm
    rw [reserve24_eq hle, sep_assoc]
    exact Owned.intro hm' (Int.toBytes_length _ _)
  · show (t.zmms.setLegacy (AvxReg.xmm .mm1) (t.zmms.get (AvxReg.xmm .mm0))).get (AvxReg.xmm .mm1)
      = t.zmms.get (AvxReg.xmm .mm0)
    exact RegZmms.get_setLegacy_xmm_self _ _ _

end CallConv.Win64Spill
