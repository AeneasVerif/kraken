module

public import Kraken.X64.Semantics

/-!
# Lemmas about the general-purpose register file
-/

@[expose] public section

namespace Reg64s

variable (regs : Reg64s) (r r' : Reg64) (v v' : BitVec 64)

@[simp] theorem get_low64 : regs.get (.low r .W64) = regs.get64 r := by
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset]

@[simp] theorem get_low32 : regs.get (.low r .W32) = (regs.get64 r).setWidth 32 := by
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset]
  rfl

@[simp] theorem set_low64 : regs.set (.low r .W64) v = regs.set64 r v := rfl

@[simp] theorem set_low32 (v : BitVec 32) :
    regs.set (.low r .W32) v = regs.set64 r (v.zeroExtend 64) := rfl

@[simp] theorem get64_set64_same : (regs.set64 r v).get64 r = v := by
  cases r <;> rfl

@[simp] theorem get64_set64_of_ne (h : r ≠ r') : (regs.set64 r v).get64 r' = regs.get64 r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

theorem get64_set64 : (regs.set64 r v).get64 r' = if r = r' then v else regs.get64 r' := by
  split
  · subst r'; exact get64_set64_same ..
  · exact get64_set64_of_ne _ _ _ _ ‹_›

@[simp] theorem set64_set64_same : (regs.set64 r v).set64 r v' = regs.set64 r v' := by
  cases r <;> rfl

theorem set64_set64_comm (h : r ≠ r') :
    (regs.set64 r v).set64 r' v' = (regs.set64 r' v').set64 r v := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

@[simp] theorem set64_get64_self : regs.set64 r (regs.get64 r) = regs := by
  cases r <;> simp [Reg64s.set64, Reg64s.get64]

theorem ext_get64 {regs regs' : Reg64s} (h : ∀ r, regs.get64 r = regs'.get64 r) : regs = regs' := by
  have h' := fun r => congrArg UInt64.ofBitVec (h r)
  cases regs; cases regs'
  simp only [Reg64s.get64, UInt64.ofBitVec_toBitVec] at h'
  simp only [Reg64s.mk.injEq]
  exact ⟨h' .rax, h' .rbx, h' .rcx, h' .rdx, h' .rsi, h' .rdi, h' .rsp, h' .rbp,
    h' .r8, h' .r9, h' .r10, h' .r11, h' .r12, h' .r13, h' .r14, h' .r15⟩

end Reg64s

/-- The address `disp(%r)` with 64-bit addressing. -/
@[simp] theorem AddrExpr.interp_base_disp [Labels] (r : Reg64) (d : Int64) (regs : Reg64s)
    (p : Std.Rco Int64) :
    @AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := none, disp := .int64 d } regs p =
      regs.get64 r + d.toBitVec := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, ConstExpr.interp, BitVec.signed,
    Int.add_zero]
  rw [BitVec.ofInt_add]
  show BitVec.ofInt 64 (BitVec.extractLsb' 0 64 (regs.get64 r)).toInt +
    BitVec.ofInt 64 d.toBitVec.toInt = _
  simp only [BitVec.ofInt_toInt]
  congr 1
  exact BitVec.extractLsb'_eq_self
