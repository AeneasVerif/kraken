module

public import Kraken.X64.Semantics

@[simp, grind =] public theorem Reg64s.get64_rax (s : Reg64s) : s.get64 .rax = s.rax.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_rbx (s : Reg64s) : s.get64 .rbx = s.rbx.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_rcx (s : Reg64s) : s.get64 .rcx = s.rcx.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_rdx (s : Reg64s) : s.get64 .rdx = s.rdx.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_rsi (s : Reg64s) : s.get64 .rsi = s.rsi.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_rdi (s : Reg64s) : s.get64 .rdi = s.rdi.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_rsp (s : Reg64s) : s.get64 .rsp = s.rsp.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_rbp (s : Reg64s) : s.get64 .rbp = s.rbp.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_r8 (s : Reg64s) : s.get64 .r8 = s.r8.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_r9 (s : Reg64s) : s.get64 .r9 = s.r9.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_r10 (s : Reg64s) : s.get64 .r10 = s.r10.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_r11 (s : Reg64s) : s.get64 .r11 = s.r11.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_r12 (s : Reg64s) : s.get64 .r12 = s.r12.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_r13 (s : Reg64s) : s.get64 .r13 = s.r13.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_r14 (s : Reg64s) : s.get64 .r14 = s.r14.toBitVec := rfl
@[simp, grind =] public theorem Reg64s.get64_r15 (s : Reg64s) : s.get64 .r15 = s.r15.toBitVec := rfl

@[simp, grind =] public theorem Reg64s.get_low_W64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

@[simp, grind =] public theorem Reg64s.set_low_W64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    Reg64s.set s (.low r .W64) v = s.set64 r v := rfl

public theorem Reg64s.set_low_W32 (s : Reg64s) (r : Reg64) (v : BitVec 32) :
    Reg64s.set s (.low r .W32) v = s.set64 r (v.zeroExtend 64) := rfl

public theorem Reg64s.set_low_W16 (s : Reg64s) (r : Reg64) (v : BitVec 16) :
    Reg64s.set s (.low r .W16) v = s.set64 r ((s.get64 r).replaceLow v) := rfl

public theorem Reg64s.set_low_W8 (s : Reg64s) (r : Reg64) (v : BitVec 8) :
    Reg64s.set s (.low r .W8) v = s.set64 r ((s.get64 r).replaceLow v) := rfl

public theorem Reg64s.set_ah (s : Reg64s) (v : BitVec 8) :
    Reg64s.set s .ah v = s.set64 .rax ((s.get64 .rax).replaceLow (BitVec.append v (s.get (.low .rax .W8)))) := rfl

public theorem Reg64s.set_bh (s : Reg64s) (v : BitVec 8) :
    Reg64s.set s .bh v = s.set64 .rbx ((s.get64 .rbx).replaceLow (BitVec.append v (s.get (.low .rbx .W8)))) := rfl

public theorem Reg64s.set_ch (s : Reg64s) (v : BitVec 8) :
    Reg64s.set s .ch v = s.set64 .rcx ((s.get64 .rcx).replaceLow (BitVec.append v (s.get (.low .rcx .W8)))) := rfl

public theorem Reg64s.set_dh (s : Reg64s) (v : BitVec 8) :
    Reg64s.set s .dh v = s.set64 .rdx ((s.get64 .rdx).replaceLow (BitVec.append v (s.get (.low .rdx .W8)))) := rfl

public theorem Reg64s.get_low_W32 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W32) = (s.get64 r).take 32 := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

public theorem Reg64s.get_low_W16 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W16) = (s.get64 r).take 16 := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

public theorem Reg64s.get_low_W8 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W8) = (s.get64 r).take 8 := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

private theorem BitVec.take_replaceLow {w n : Nat} (x : BitVec w) (v : BitVec n) (h : n ≤ w) :
    (x.replaceLow v).take n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.replaceLow, BitVec.take, BitVec.getLsbD_append, hi, show i < w by omega]

public theorem BitVec.take_replaceLow_8 (x : BitVec 64) (v : BitVec 8) : (x.replaceLow v).take 8 = v :=
  BitVec.take_replaceLow x v (by decide)

public theorem BitVec.take_replaceLow_16 (x : BitVec 64) (v : BitVec 16) : (x.replaceLow v).take 16 = v :=
  BitVec.take_replaceLow x v (by decide)

public theorem BitVec.take_zeroExtend_32 (v : BitVec 32) : (v.zeroExtend 64).take 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.take, hi]
  omega

public theorem Reg64s.set64_rax (s : Reg64s) (v : BitVec 64) :
    s.set64 .rax v = { s with rax := .ofBitVec v } := rfl
public theorem Reg64s.set64_rbx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rbx v = { s with rbx := .ofBitVec v } := rfl
public theorem Reg64s.set64_rcx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rcx v = { s with rcx := .ofBitVec v } := rfl
public theorem Reg64s.set64_rdx (s : Reg64s) (v : BitVec 64) :
    s.set64 .rdx v = { s with rdx := .ofBitVec v } := rfl
public theorem Reg64s.set64_rsi (s : Reg64s) (v : BitVec 64) :
    s.set64 .rsi v = { s with rsi := .ofBitVec v } := rfl
public theorem Reg64s.set64_rdi (s : Reg64s) (v : BitVec 64) :
    s.set64 .rdi v = { s with rdi := .ofBitVec v } := rfl
public theorem Reg64s.set64_rsp (s : Reg64s) (v : BitVec 64) :
    s.set64 .rsp v = { s with rsp := .ofBitVec v } := rfl
public theorem Reg64s.set64_rbp (s : Reg64s) (v : BitVec 64) :
    s.set64 .rbp v = { s with rbp := .ofBitVec v } := rfl
public theorem Reg64s.set64_r8 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r8 v = { s with r8 := .ofBitVec v } := rfl
public theorem Reg64s.set64_r9 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r9 v = { s with r9 := .ofBitVec v } := rfl
public theorem Reg64s.set64_r10 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r10 v = { s with r10 := .ofBitVec v } := rfl
public theorem Reg64s.set64_r11 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r11 v = { s with r11 := .ofBitVec v } := rfl
public theorem Reg64s.set64_r12 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r12 v = { s with r12 := .ofBitVec v } := rfl
public theorem Reg64s.set64_r13 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r13 v = { s with r13 := .ofBitVec v } := rfl
public theorem Reg64s.set64_r14 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r14 v = { s with r14 := .ofBitVec v } := rfl
public theorem Reg64s.set64_r15 (s : Reg64s) (v : BitVec 64) :
    s.set64 .r15 v = { s with r15 := .ofBitVec v } := rfl

@[simp] public theorem Reg64s.rax_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rax = a0 := rfl
@[simp] public theorem Reg64s.rbx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rbx = a1 := rfl
@[simp] public theorem Reg64s.rcx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rcx = a2 := rfl
@[simp] public theorem Reg64s.rdx_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rdx = a3 := rfl
@[simp] public theorem Reg64s.rsi_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rsi = a4 := rfl
@[simp] public theorem Reg64s.rdi_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rdi = a5 := rfl
@[simp] public theorem Reg64s.rsp_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rsp = a6 := rfl
@[simp] public theorem Reg64s.rbp_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).rbp = a7 := rfl
@[simp] public theorem Reg64s.r8_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r8 = a8 := rfl
@[simp] public theorem Reg64s.r9_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r9 = a9 := rfl
@[simp] public theorem Reg64s.r10_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r10 = a10 := rfl
@[simp] public theorem Reg64s.r11_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r11 = a11 := rfl
@[simp] public theorem Reg64s.r12_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r12 = a12 := rfl
@[simp] public theorem Reg64s.r13_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r13 = a13 := rfl
@[simp] public theorem Reg64s.r14_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r14 = a14 := rfl
@[simp] public theorem Reg64s.r15_mk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    (Reg64s.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).r15 = a15 := rfl

@[simp] public theorem MachineData.regs_mk (r z st d) : (MachineData.mk r z st d).regs = r := rfl
@[simp] public theorem MachineData.dmem_mk (r z st d) : (MachineData.mk r z st d).dmem = d := rfl
@[simp] public theorem MachineData.status_mk (r z st d) : (MachineData.mk r z st d).status = st := rfl
@[simp] public theorem MachineData.zmms_mk (r z st d) : (MachineData.mk r z st d).zmms = z := rfl

@[simp] public theorem BitVec.unsigned_eq {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl

@[simp, grind =] public theorem StatusFlags.cf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).cf = f.cf := rfl

@[simp] public theorem StatusFlags.from_result.Remaining.cf_mk (c a o : Bool) :
    (StatusFlags.from_result.Remaining.mk c a o).cf = c := rfl

@[simp, grind =] public theorem StatusFlags.zf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).zf = (v == BitVec.zero w) := rfl

@[simp, grind =] public theorem CondCode.interp_z (s : StatusFlags) :
    CondCode.z.interp s = s.zf := rfl
@[simp, grind =] public theorem CondCode.interp_nz (s : StatusFlags) :
    CondCode.nz.interp s = !s.zf := rfl
@[simp, grind =] public theorem CondCode.interp_c (s : StatusFlags) :
    CondCode.c.interp s = s.cf := rfl
@[simp, grind =] public theorem CondCode.interp_nc (s : StatusFlags) :
    CondCode.nc.interp s = !s.cf := rfl
@[simp, grind =] public theorem CondCode.interp_a (s : StatusFlags) :
    CondCode.a.interp s = (!s.cf && !s.zf) := rfl
@[simp, grind =] public theorem CondCode.interp_be (s : StatusFlags) :
    CondCode.be.interp s = (s.cf || s.zf) := rfl

public theorem AddrExpr.zeroExtend_interp_base_disp [L : Labels] (b : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), none, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, Int.add_zero,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_toInt]

