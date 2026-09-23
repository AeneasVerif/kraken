/-
Register reads and writes at named registers. A read of a named register is
the field, a `.low r .W64` access is the 64-bit access, and a write to a
named register is a structure update. `vcgen` folds the register state with
the write equations, so a read after a block of writes is a projection of
one register literal.
-/
import Kraken.X64.Semantics

/-! ## Reading a named register, one lemma per field -/

@[simp, grind =] theorem Reg64s.get64_rax (s : Reg64s) : s.get64 .rax = s.rax.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rbx (s : Reg64s) : s.get64 .rbx = s.rbx.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rcx (s : Reg64s) : s.get64 .rcx = s.rcx.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rdx (s : Reg64s) : s.get64 .rdx = s.rdx.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rsi (s : Reg64s) : s.get64 .rsi = s.rsi.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rdi (s : Reg64s) : s.get64 .rdi = s.rdi.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rsp (s : Reg64s) : s.get64 .rsp = s.rsp.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rbp (s : Reg64s) : s.get64 .rbp = s.rbp.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r8 (s : Reg64s) : s.get64 .r8 = s.r8.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r9 (s : Reg64s) : s.get64 .r9 = s.r9.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r10 (s : Reg64s) : s.get64 .r10 = s.r10.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r11 (s : Reg64s) : s.get64 .r11 = s.r11.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r12 (s : Reg64s) : s.get64 .r12 = s.r12.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r13 (s : Reg64s) : s.get64 .r13 = s.r13.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r14 (s : Reg64s) : s.get64 .r14 = s.r14.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r15 (s : Reg64s) : s.get64 .r15 = s.r15.toBitVec := rfl

/-! ## The 64-bit access of a register -/

@[simp, grind =] theorem Reg64s.get_low_W64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

@[simp, grind =] theorem Reg64s.set_low_W64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    Reg64s.set s (.low r .W64) v = s.set64 r v := rfl

/-! ## A write to a named register as a structure update

`vcgen` rewrites the register state it threads with these equations, so a
block of writes folds into one register literal and every later read is a
projection of that literal. -/

theorem Reg64s.set64_rax (s : Reg64s) (v : BitVec 64) :
    s.set64 .rax v = { s with rax := .ofBitVec v } := rfl
theorem Reg64s.set64_rbx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rbx v = { s with rbx := .ofBitVec v } := rfl
theorem Reg64s.set64_rcx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rcx v = { s with rcx := .ofBitVec v } := rfl
theorem Reg64s.set64_rdx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rdx v = { s with rdx := .ofBitVec v } := rfl
theorem Reg64s.set64_rsi (s : Reg64s) (v : BitVec 64) :
    s.set64 .rsi v = { s with rsi := .ofBitVec v } := rfl
theorem Reg64s.set64_rdi (s : Reg64s) (v : BitVec 64) :
    s.set64 .rdi v = { s with rdi := .ofBitVec v } := rfl
theorem Reg64s.set64_rsp (s : Reg64s) (v : BitVec 64) :
    s.set64 .rsp v = { s with rsp := .ofBitVec v } := rfl
theorem Reg64s.set64_rbp (s : Reg64s) (v : BitVec 64) :
    s.set64 .rbp v = { s with rbp := .ofBitVec v } := rfl
theorem Reg64s.set64_r8 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r8 v = { s with r8 := .ofBitVec v } := rfl
theorem Reg64s.set64_r9 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r9 v = { s with r9 := .ofBitVec v } := rfl
theorem Reg64s.set64_r10 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r10 v = { s with r10 := .ofBitVec v } := rfl
theorem Reg64s.set64_r11 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r11 v = { s with r11 := .ofBitVec v } := rfl
theorem Reg64s.set64_r12 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r12 v = { s with r12 := .ofBitVec v } := rfl
theorem Reg64s.set64_r13 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r13 v = { s with r13 := .ofBitVec v } := rfl
theorem Reg64s.set64_r14 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r14 v = { s with r14 := .ofBitVec v } := rfl
theorem Reg64s.set64_r15 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r15 v = { s with r15 := .ofBitVec v } := rfl
