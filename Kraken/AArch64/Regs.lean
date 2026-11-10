module

public import Kraken.AArch64.Semantics

/-!
# Lemmas about the general-purpose register file
-/

@[expose] public section

namespace Reg64s

variable (regs : Reg64s) (r r' : XReg) (v v' : BitVec 64)

@[simp] theorem getXReg_setXReg_same : (regs.setXReg r v).getXReg r = UInt64.ofBitVec v := by
  cases r <;> rfl

@[simp] theorem getXReg_setXReg_of_ne (h : r ≠ r') :
    (regs.setXReg r v).getXReg r' = regs.getXReg r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

theorem getXReg_setXReg :
    (regs.setXReg r v).getXReg r' = if r = r' then UInt64.ofBitVec v else regs.getXReg r' := by
  split
  · subst r'; exact getXReg_setXReg_same ..
  · exact getXReg_setXReg_of_ne _ _ _ _ ‹_›

@[simp] theorem setXReg_setXReg_same : (regs.setXReg r v).setXReg r v' = regs.setXReg r v' := by
  cases r <;> rfl

theorem setXReg_setXReg_comm (h : r ≠ r') :
    (regs.setXReg r v).setXReg r' v' = (regs.setXReg r' v').setXReg r v := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

@[simp] theorem setXReg_getXReg_self : regs.setXReg r (regs.getXReg r).toBitVec = regs := by
  cases r <;> simp [Reg64s.setXReg, Reg64s.getXReg]

@[simp] theorem SP_setXReg : (regs.setXReg r v).SP = regs.SP := by
  cases r <;> rfl

@[simp] theorem getRegOrZr_reg64 :
    regs.getRegOrZr (.low (.reg r) .W64) = (regs.getXReg r).toBitVec := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]

@[simp] theorem getRegOrZr_reg32 :
    regs.getRegOrZr (.low (.reg r) .W32) = (regs.getXReg r).toBitVec.setWidth 32 := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]
  rfl

@[simp] theorem getRegOrZr_xzr {w : RegWidth} : regs.getRegOrZr (.low .XZR w) = 0 := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]

@[simp] theorem setRegOrZr_reg64 : regs.setRegOrZr (.low (.reg r) .W64) v = regs.setXReg r v := rfl

@[simp] theorem setRegOrZr_reg32 (v : BitVec 32) :
    regs.setRegOrZr (.low (.reg r) .W32) v = regs.setXReg r (v.zeroExtend 64) := rfl

@[simp] theorem setRegOrZr_xzr {w : RegWidth} (v : w.type) : regs.setRegOrZr (.low .XZR w) v = regs := by
  cases w <;> rfl

@[simp] theorem getRegOrSp_reg64 :
    regs.getRegOrSp (.low (.reg r) .W64) = (regs.getXReg r).toBitVec := by
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take]

@[simp] theorem getRegOrSp_sp64 : regs.getRegOrSp (.low .SP .W64) = regs.SP.toBitVec := by
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take]

@[simp] theorem setRegOrSp_reg64 : regs.setRegOrSp (.low (.reg r) .W64) v = regs.setXReg r v := rfl

@[simp] theorem setRegOrSp_sp64 :
    regs.setRegOrSp (.low .SP .W64) v = { regs with SP := UInt64.ofBitVec v } := rfl

end Reg64s
