module

public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.Amd64.IselVec
public import LeanQbe.T.Amd64.Frame
public import LeanQbe.T.Main
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Legal
public import LeanQbe.T.FlatLemmas
meta import LeanQbe.T.Amd64.Isel
meta import LeanQbe.T.Amd64.IselVec
meta import LeanQbe.T.Amd64.Frame
meta import LeanQbe.T.Main
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Legal

/-!
# Verification Tests & Audit for `LeanQbe.T.Amd64`

Standalone x86-64 backend suite (no legacy untyped-IR imports). Verifies:
1. All three width/semantic edge cases on `x64Gpr` and `x64GprSpec`:
   - Pitfall (a): `.bool` upper-bit garbage (`0xdeadbeef_0000ff00#64` vs `0xdeadbeef_0000ff01#64`),
     byte-width `testb` / `movzbl` / `movb`, and `loadVal` rejecting non-`{0,1}` bytes.
   - Pitfall (b): `.bits n` (`n ∈ {8, 16, 32}`) upper-bit garbage handling across `cmp`, shifts,
     rotates, `udiv`/`sdiv`, `zext`/`sext`, and `bswap` (`[16, 32, 64]`).
   - Pitfall (c): Kraken X64 shift-count masking (`& 7` / `& 15` on variable 8/16-bit shifts,
     immediate modulo `n`, and rotate demonic `OF` clobber).
2. Scalar opcode, `VariantHint` (`disp`, `decInc`, `adcx`, `adox`, `mulxFast`), and addressing
   coverage, plus explicit rejection checks (`supportsScalarOp = false`, `op = none`).
3. End-to-end `Fn.backendOk = true` via `t_kernel_rfl` on `LegalTarget.x64 []`-legalized
   `Bignum` (`mul4x4`, `addMod25519`, `subMod25519`) and all 6 functions in `lratBytesFns`.
4. Axiom audit (`#print axioms`) confirming only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Amd64IselTest

open LeanQbe.T
open LeanQbe.T.Amd64

/-! ## 1. Pitfall (a): `.bool` upper-bit garbage & byte-exact lowering -/

theorem bool_gprHolds_upper_garbage :
    GprHolds 0xdeadbeef_0000ff00#64 .bool false ∧
    GprHolds 0xdeadbeef_0000ff01#64 .bool true :=
  ⟨rfl, rfl⟩

theorem jnzGpr_uses_testb_rfl :
    x64Gpr.jnzGpr .rax "L" =
      ([ins8 (.test (.reg (b8 .rax)) (.reg (b8 .rax))), ins (.jcc .nz "L")], maskAll) :=
  rfl

theorem select_bool_gpr_uses_testb_rfl :
    x64Gpr.op (.select i64) (.gpr .rcx, .gpr .rax, .gpr .rdx, ()) (.gpr .rdx, ()) .default =
      some ([ins8 (.test (.reg (b8 .rcx)) (.reg (b8 .rcx))),
             ins (.cmovcc .nz (q .rdx) (.reg (q .rax)))], maskAll) :=
  rfl

theorem ofBool_uses_movzbl_rfl :
    x64Gpr.op (.ofBool 64) (.gpr .rax, ()) (.gpr .rdx, ()) .default =
      some ([ins32 (.movzx (.reg (d .rdx)) (.reg (b8 .rax)))], maskNone) :=
  rfl

theorem bool_and_uses_b8_rfl :
    x64Gpr.op (.and .bool) (.gpr .rax, .gpr .rcx, ()) (.gpr .rdx, ()) .default =
      some ([ins8 (.mov (.reg (b8 .rdx)) (.reg (b8 .rax))),
             ins8 (.and (.reg (b8 .rdx)) (.reg (b8 .rcx)))], maskAll) ∧
    x64Gpr.op (.and .bool) (.gpr .rdx, .flag .z, ()) (.gpr .rdx, ()) .default =
      some ([ins8 (.setcc .z (.reg (b8 .r10))),
             ins8 (.and (.reg (b8 .rdx)) (.reg (b8 .r10)))], maskAll) ∧
    x64Gpr.op (.and .bool) (.gpr .rax, .flag .z, ()) (.gpr .rdx, ()) .default =
      some ([ins8 (.setcc .z (.reg (b8 .rdx))),
             ins8 (.and (.reg (b8 .rdx)) (.reg (b8 .rax)))], maskAll) :=
  ⟨rfl, rfl, rfl⟩

theorem addc_gpr_carry_in_out_rfl :
    x64Gpr.op (.addc 64) (.gpr .rax, .gpr .rsi, .gpr .rcx, ()) (.gpr .rax, .gpr .rdx, ()) .default =
      some ([ins8 (.mov (.reg (b8 .r10)) (.reg (b8 .rcx))),
             ins8 (.neg (.reg (b8 .r10))),
             ins (.adc (.reg (q .rax)) (.reg (q .rsi))),
             ins8 (.setcc .c (.reg (b8 .rdx))),
             ins32 (.movzx (.reg (d .rdx)) (.reg (b8 .rdx)))], maskAll) :=
  rfl

theorem load_store_bool_byte_exact_rfl :
    x64Gpr.load .bool .rax (.baseDisp .rdi 0) =
      some ([ins32 (.movzx (.reg (d .rax)) (.mem (atReg .rdi) : RegOrMem .W8))], maskNone) ∧
    x64Gpr.store .bool (.gpr .rax) (.baseDisp .rdi 0) =
      some ([ins8 (.mov (.mem (atReg .rdi)) (.reg (b8 .rax)))], maskNone) :=
  ⟨rfl, rfl⟩

theorem loadVal_bool_checks (m : Mem 64) (a : BitVec 64) :
    (m.loadInt a 1 = some 0 → loadVal m .bool a = some false) ∧
    (m.loadInt a 1 = some 1 → loadVal m .bool a = some true) ∧
    (m.loadInt a 1 = some 2 → loadVal m .bool a = none) ∧
    (m.loadInt a 1 = some 255 → loadVal m .bool a = none) :=
  ⟨fun h => by simp [loadVal, Ty.bytes, Ty.size, h],
   fun h => by simp [loadVal, Ty.bytes, Ty.size, h],
   fun h => by simp [loadVal, Ty.bytes, Ty.size, h],
   fun h => by simp [loadVal, Ty.bytes, Ty.size, h]⟩

theorem pitfall_a_bool_jnz_spec {h : x64Mach.Host} {k j : Nat} {l : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (x64Gpr.jnzGpr .rax l).1.IsInfixAt (x64Mach.prog h) k)
    (hj : x64Mach.labelAddr h l = x64Mach.addrOf h j)
    (hr : s.regs.get64 .rax = 0xdeadbeef_0000ff00#64)
    (hk : ∀ s', x64Mach.Frame x64Gpr.condReads s s' x64Scratch [] (x64Gpr.jnzGpr .rax l).2 →
      x64Mach.mem s' = x64Mach.mem s → x64Mach.Run h (k + (x64Gpr.jnzGpr .rax l).1.length) s' post) :
    x64Mach.Run h k s post := by
  have hgpr : GprHolds (x64Mach.getGpr s .rax) .bool false := by
    dsimp [x64Mach, Machine.getGpr]; rw [hr]; rfl
  exact x64GprSpec.jnzGpr_spec hc hj (by simp [x64Scratch]) hgpr fun s' hfr hm =>
    ⟨fun h => absurd h Bool.false_ne_true, fun _ => hk s' hfr hm⟩

theorem pitfall_a_ofBool_spec {h : x64Mach.Host} {k : Nat} {s : MachineData} {post : MachineState → Prop}
    (hr : s.regs.get64 .rax = 0xdeadbeef_0000ff01#64)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.ofBool 64) (.gpr .rax, ()) (.gpr .rdx, ()) .default = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c [.rdx, .r10, .r11] [] clob s
      (fun s' => GprHolds (s'.regs.get64 .rdx) i64 1#64 ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s .bool (.gpr .rax) true := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr]; rw [hr]; rfl
  have hwp : (OpCode.ofBool 64).wp (true, ()) (fun (r : Tup Val [i64]) => r.1 = 1#64) := rfl
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha .nil) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

/-! ## 2. Pitfall (b): `.bits n` upper-bit garbage (`n ∈ {8, 16, 32}`) -/

theorem bits_gprHolds_upper_garbage :
    GprHolds 0xdeadbeef_cafeba05#64 i8 0x05#8 ∧
    GprHolds 0xdeadbeef_cafeba05#64 i16 0xba05#16 ∧
    GprHolds 0xdeadbeef_12345678#64 i32 0x12345678#32 :=
  ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩

theorem width_exact_ops_rfl :
    x64Gpr.op (.cmp .ult i8) (.gpr .rax, .gpr .rsi, ()) (.flag .c, ()) .default =
      some ([ins8 (.cmp (.reg (b8 .rax)) (.reg (b8 .rsi)))], maskAll) ∧
    x64Gpr.op (.udiv 8) (.gpr .rax, .gpr .rcx, ()) (.gpr .rsi, ()) .default =
      some ([ins32 (.movzx (.reg (d .r10)) (.reg (b8 .rax))),
             ins32 (.movzx (.reg (d .r11)) (.reg (b8 .rcx))),
             movD .rsi .rax, movD .rax .r10, movD .r10 .rdx,
             ins32 (.xor (.reg (d .rdx)) (.reg (d .rdx))), ins32 (.div (.reg (d .r11))),
             movD .r11 .rax, movD .rdx .r10, movD .rax .rsi,
             ins32 (.mov (.reg (d .rsi)) (.regOrMem (.reg (d .r11))))], maskAll) ∧
    x64Gpr.op (.sext 8 64) (.gpr .rax, ()) (.gpr .rdx, ()) .default =
      some ([ins (.movsx (.reg (q .rdx)) (.reg (b8 .rax)))], maskNone) ∧
    x64Gpr.op (.zext 16 64) (.gpr .rax, ()) (.gpr .rdx, ()) .default =
      some ([ins32 (.movzx (.reg (d .rdx)) (.reg (h16 .rax)))], maskNone) ∧
    x64Gpr.op (.bswap i16) (.gpr .rax, ()) (.gpr .rdx, ()) .default =
      some ([movW .W16 .rdx .rax, ins16 (.rol (.reg (h16 .rdx)) (.imm8 (.int64 8)))], maskCF ||| maskOF) ∧
    x64Gpr.op (.bswap i32) (.gpr .rax, ()) (.gpr .rax, ()) .default =
      some ([ins32 (.bswap (d .rax))], maskNone) ∧
    x64Gpr.op (.bswap i64) (.gpr .rax, ()) (.gpr .rax, ()) .default =
      some ([ins (.bswap (q .rax))], maskNone) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Pitfall (c): Kraken X64 shift-count masking & rotate demonic `OF` -/

theorem shift_mask_trap_rfl :
    x64Gpr.op (.shl i8) (.gpr .rax, .gpr .rcx, ()) (.gpr .rdx, ()) .default =
      some ([movW .W8 .r11 .rax, movD .r10 .rcx,
             ins32 (.and (.reg (d .rcx)) (.imm (.int64 7))),
             ins8 (.shl (.reg (b8 .r11)) .cl),
             movD .rcx .r10, movW .W8 .rdx .r11], maskAll) ∧
    x64Gpr.op (.ashr i16) (.gpr .rax, .gpr .rcx, ()) (.gpr .rdx, ()) .default =
      some ([movW .W16 .r11 .rax, movD .r10 .rcx,
             ins32 (.and (.reg (d .rcx)) (.imm (.int64 15))),
             ins16 (.sar (.reg (h16 .r11)) .cl),
             movD .rcx .r10, movW .W16 .rdx .r11], maskAll) ∧
    x64Gpr.op (.shl i8) (.gpr .rax, .imm 9#8, ()) (.gpr .rax, ()) .default =
      some ([ins8 (.shl (.reg (b8 .rax)) (.imm8 (.int64 1)))], maskAll) ∧
    x64Gpr.op (.lshr i16) (.gpr .rax, .imm 16#16, ()) (.gpr .rdx, ()) .default =
      some ([movW .W16 .rdx .rax], maskNone) ∧
    x64Gpr.op (.rotl i16) (.gpr .rax, .imm 5#16, ()) (.gpr .rax, ()) .default =
      some ([ins16 (.rol (.reg (h16 .rax)) (.imm8 (.int64 5)))], maskCF ||| maskOF) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3b. BMI2 Flag-Free Shifts/Rotates & Native Bit-Counting -/

theorem bmi2_shifts_rotates_rfl :
    x64Gpr.op (.shl i64) (.gpr .rax, .gpr .rcx, ()) (.gpr .rdx, ()) .default =
      some ([ins (.shlx (q .rdx) (.reg (q .rax)) (q .rcx))], maskNone) ∧
    x64Gpr.op (.lshr i32) (.gpr .rax, .gpr .rsi, ()) (.gpr .rax, ()) .default =
      some ([ins32 (.shrx (d .rax) (.reg (d .rax)) (d .rsi))], maskNone) ∧
    x64Gpr.op (.ashr i64) (.imm 99#64, .gpr .rsi, ()) (.gpr .rdx, ()) .default =
      some ([moviD .r11 99, ins (.sarx (q .rdx) (.reg (q .r11)) (q .rsi))], maskNone) ∧
    x64Gpr.op (.rotl i64) (.gpr .rax, .imm 5#64, ()) (.gpr .rdx, ()) .default =
      some ([ins (.rorx (q .rdx) (.reg (q .rax)) (.int64 59))], maskNone) ∧
    x64Gpr.op (.rotr i32) (.gpr .rax, .imm 7#32, ()) (.gpr .rax, ()) .default =
      some ([ins32 (.rorx (d .rax) (.reg (d .rax)) (.int64 7))], maskNone) ∧
    x64Gpr.op (.rotl i32) (.imm 0x12340000#32, .imm 16#32, ()) (.gpr .rax, ()) .default =
      some ([moviD .rax 0x1234], maskNone) ∧
    x64Gpr.op (.rotl i64) (.gpr .rax, .gpr .rcx, ()) (.gpr .rdx, ()) .default =
      some ([movW .W64 .r11 .rax, movD .r10 .rcx,
             ins (.rol (.reg (q .r11)) .cl),
             movD .rcx .r10, movW .W64 .rdx .r11], maskCF ||| maskOF) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bitcnt_lowering_rfl :
    x64Gpr.op (.clz 8) (.imm 0x0f#8, ()) (.gpr .rax, ()) .default =
      some ([moviD .rax 4], maskNone) ∧
    x64Gpr.op (.cls 16) (.imm 0xffe0#16, ()) (.gpr .rax, ()) .default =
      some ([moviD .rax 10], maskNone) ∧
    x64Gpr.op (.ctz 16) (.imm 0x0100#16, ()) (.gpr .rax, ()) .default =
      some ([moviD .rax 8], maskNone) ∧
    x64Gpr.op (.popcnt 16) (.imm 0x5555#16, ()) (.gpr .rax, ()) .default =
      some ([moviD .rax 8], maskNone) ∧
    x64Gpr.op (.popcnt 8) (.gpr .rax, ()) (.gpr .rdx, ()) .default =
      some ([movW .W8 .rdx .rax, ins32 (.popcnt (d .rdx) (.reg (d .rdx)))], maskAll) ∧
    x64Gpr.op (.popcnt 64) (.gpr .rsi, ()) (.gpr .rax, ()) .default =
      some ([ins (.popcnt (q .rax) (.reg (q .rsi)))], maskAll) ∧
    x64Gpr.op (.clz 16) (.gpr .rax, ()) (.gpr .rax, ()) .default =
      some ([movW .W16 .rax .rax, ins32 (.lzcnt (d .rax) (.reg (d .rax))),
             aluBinIns .W32 .sub .rax (immBitsOp .W32 16#32)], maskAll) ∧
    x64Gpr.op (.clz 32) (.gpr .rsi, ()) (.gpr .rax, ()) .default =
      some ([ins32 (.lzcnt (d .rax) (.reg (d .rsi)))], maskAll) ∧
    x64Gpr.op (.ctz 8) (.gpr .rax, ()) (.gpr .rdx, ()) .default =
      some ([movW .W8 .rdx .rax,
             aluBinIns .W32 .or .rdx (immBitsOp .W32 256#32),
             ins32 (.tzcnt (d .rdx) (.reg (d .rdx)))], maskAll) ∧
    x64Gpr.op (.ctz 64) (.gpr .rsi, ()) (.gpr .rax, ()) .default =
      some ([ins (.tzcnt (q .rax) (.reg (q .rsi)))], maskAll) ∧
    x64Gpr.op (.cls 32) (.gpr .rax, ()) (.gpr .rax, ()) .default =
      some ([movW .W32 .r11 .rax,
             ins32 (.sar (.reg (d .r11)) (.imm8 (.int64 31))),
             aluBinIns .W32 .xor .r11 (.reg (d .rax)),
             ins32 (.lzcnt (d .rax) (.reg (d .r11))),
             ins32 (.dec (.reg (d .rax)))], maskAll) ∧
    x64Gpr.op (.cls 8) (.gpr .rax, ()) (.gpr .rax, ()) .default =
      some ([ins32 (.movsx (.reg (d .rax)) (.reg (b8 .rax))),
             movlD .r11 .rax,
             ins32 (.sar (.reg (d .r11)) (.imm8 (.int64 31))),
             aluBinIns .W32 .xor .rax (.reg (d .r11)),
             ins32 (.lzcnt (d .rax) (.reg (d .rax))),
             aluBinIns .W32 .sub .rax (immBitsOp .W32 25#32)], maskAll) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#guard x64Gpr.op (.ctz 32) (.imm 0x00000100#32, ()) (.gpr .rax, ()) .default ==
  some ([moviD .rax 8], maskNone)

#guard x64Gpr.op (.popcnt 64) (.imm 0x000000ff_000000ff#64, ()) (.gpr .rax, ()) .default ==
  some ([moviD .rax 16], maskNone)

theorem bmi2_shlx64_flags_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {post : MachineState → Prop}
    (ha0 : s.regs.get64 .rax = 0x00000000_00000003#64)
    (hb0 : s.regs.get64 .rcx = 0xdeadbeef_00000004#64)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.shl i64) (.gpr .rax, .gpr .rcx, ()) (.gpr .rdx, ()) .default =
      some (c, clob)) :
    clob = maskNone ∧
    x64Mach.FallsTo x64Gpr.condReads h k c [.rdx, .r10, .r11] [] maskNone s
      (fun s' => GprHolds (s'.regs.get64 .rdx) i64 0x30#64 ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i64 (.gpr .rax) 0x03#64 := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [ha0]; exact ⟨by decide, rfl⟩
  have hb : x64Mach.PArgHolds s i64 (.gpr .rcx) 0xdeadbeef_00000004#64 := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [hb0]; exact ⟨by decide, rfl⟩
  have hwp : (OpCode.shl i64).wp (0x03#64, 0xdeadbeef_00000004#64, ())
      (fun (r : Tup Val [i64]) => r.1 = 0x30#64) := rfl
  have hclob : clob = maskNone := by
    cases ((rfl : x64Gpr.op (.shl i64) (.gpr .rax, .gpr .rcx, ()) (.gpr .rdx, ()) .default =
      some ([ins (.shlx (q .rdx) (.reg (q .rax)) (q .rcx))], maskNone)).symm.trans hc); rfl
  subst hclob; refine ⟨rfl, ?_⟩
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha (TRel.cons hb .nil)) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

theorem bmi2_rorx32_flags_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {post : MachineState → Prop}
    (ha0 : s.regs.get64 .rax = 0xdeadbeef_12345678#64)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.rotl i32) (.gpr .rax, .imm 8#32, ()) (.gpr .rdx, ()) .default =
      some (c, clob)) :
    clob = maskNone ∧
    x64Mach.FallsTo x64Gpr.condReads h k c [.rdx, .r10, .r11] [] maskNone s
      (fun s' => GprHolds (s'.regs.get64 .rdx) i32 0x34567812#32 ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i32 (.gpr .rax) 0x12345678#32 := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]
    rw [ha0]; exact ⟨by decide, rfl⟩
  have hb : x64Mach.PArgHolds s i32 (.imm 8#32) 8#32 := rfl
  have hwp : (OpCode.rotl i32).wp (0x12345678#32, 8#32, ())
      (fun (r : Tup Val [i32]) => r.1 = 0x34567812#32) := rfl
  have hclob : clob = maskNone := by
    cases ((rfl : x64Gpr.op (.rotl i32) (.gpr .rax, .imm 8#32, ()) (.gpr .rdx, ()) .default =
      some ([ins32 (.rorx (d .rdx) (.reg (d .rax)) (.int64 24))], maskNone)).symm.trans hc); rfl
  subst hclob; refine ⟨rfl, ?_⟩
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha (TRel.cons hb .nil)) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

theorem bitcnt_clz8_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {post : MachineState → Prop}
    (ha0 : s.regs.get64 .rax = 0xdeadbeef_ffffff0f#64)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.clz 8) (.gpr .rax, ()) (.gpr .rdx, ()) .default = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c [.rdx, .r10, .r11] [] clob s
      (fun s' => GprHolds (s'.regs.get64 .rdx) i8 4#8 ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i8 (.gpr .rax) 0x0f#8 := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]
    rw [ha0]; exact ⟨by decide, rfl⟩
  have hwp : (OpCode.clz 8).wp (0x0f#8, ()) (fun (r : Tup Val [i8]) => r.1 = 4#8) := rfl
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha .nil) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

theorem bitcnt_cls16_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {post : MachineState → Prop}
    (ha0 : s.regs.get64 .rax = 0xdeadbeef_0000ffe0#64)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.cls 16) (.gpr .rax, ()) (.gpr .rdx, ()) .default = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c [.rdx, .r10, .r11] [] clob s
      (fun s' => GprHolds (s'.regs.get64 .rdx) i16 10#16 ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i16 (.gpr .rax) 0xffe0#16 := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]
    rw [ha0]; exact ⟨by decide, rfl⟩
  have hwp : (OpCode.cls 16).wp (0xffe0#16, ()) (fun (r : Tup Val [i16]) => r.1 = 10#16) := rfl
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha .nil) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

theorem bitcnt_ctz32_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {va : BitVec 32} {post : MachineState → Prop}
    (ha0 : (s.regs.get64 .rax).setWidth 32 = va)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.ctz 32) (.gpr .rax, ()) (.gpr .rdx, ()) .default = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c [.rdx, .r10, .r11] [] clob s
      (fun s' => GprHolds (s'.regs.get64 .rdx) i32 va.reverse.clz ∧ s'.dmem = s.dmem)
      post := by
  have ha : x64Mach.PArgHolds s i32 (.gpr .rax) va := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]
    exact ⟨by decide, ha0⟩
  have hwp : (OpCode.ctz 32).wp (va, ())
      (fun (r : Tup Val [i32]) => r.1 = va.reverse.clz) := rfl
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha .nil) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

theorem bitcnt_popcnt64_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {va : BitVec 64} {post : MachineState → Prop}
    (ha0 : s.regs.get64 .rax = va)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.popcnt 64) (.gpr .rax, ()) (.gpr .rdx, ()) .default = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c [.rdx, .r10, .r11] [] clob s
      (fun s' => GprHolds (s'.regs.get64 .rdx) i64 va.cpop ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i64 (.gpr .rax) va := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]
    rw [ha0]; exact ⟨by decide, rfl⟩
  have hwp : (OpCode.popcnt 64).wp (va, ()) (fun (r : Tup Val [i64]) => r.1 = va.cpop) := rfl
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha .nil) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

theorem pitfall_c_var_shl8_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {post : MachineState → Prop}
    (ha0 : s.regs.get64 .rax = 0xdeadbeef_cafeba03#64)
    (hb0 : s.regs.get64 .rcx = 0x00000000_00000009#64)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.shl i8) (.gpr .rax, .gpr .rcx, ()) (.gpr .rdx, ()) .default = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c [.rdx, .r10, .r11] [] clob s
      (fun s' => GprHolds (s'.regs.get64 .rdx) i8 0x06#8 ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i8 (.gpr .rax) 0x03#8 := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [ha0]; exact ⟨by decide, rfl⟩
  have hb : x64Mach.PArgHolds s i8 (.gpr .rcx) 0x09#8 := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [hb0]; exact ⟨by decide, rfl⟩
  have hwp : (OpCode.shl i8).wp (0x03#8, 0x09#8, ()) (fun (r : Tup Val [i8]) => r.1 = 0x06#8) := rfl
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha (TRel.cons hb .nil)) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

/-! ## 4. Additional `VariantHint`s, Multi-Limb Ops, and Explicit Rejections -/

theorem hints_and_wide_ops_rfl :
    x64Gpr.op (.add i64) (.gpr .rbx, .imm 16#64, ()) (.gpr .rax, ()) (.disp 16) =
      some ([ins (.lea (q .rax) (atDisp .rbx 16))], maskNone) ∧
    x64Gpr.op (.sub i32) (.gpr .rax, .imm 1#32, ()) (.gpr .rax, ()) .decInc =
      some ([ins32 (.dec (.reg (d .rax)))], maskDecInc) ∧
    x64Gpr.op (.addc 64) (.gpr .rax, .gpr .rsi, .flag .c, ()) (.gpr .rax, .flag .c, ()) .adcx =
      some ([ins (.adcx (q .rax) (.reg (q .rsi)))], maskCF) ∧
    x64Gpr.op (.addc 64) (.gpr .rbx, .gpr .rdi, .flag .o, ()) (.gpr .rbx, .flag .o, ()) .adox =
      some ([ins (.adox (q .rbx) (.reg (q .rdi)))], maskOF) ∧
    x64Gpr.op (.umulw 64) (.gpr .rax, .gpr .rdx, ()) (.gpr .r8, .gpr .r9, ()) .mulxFast =
      some ([movW .W64 .r11 .rax, movD .r10 .rdx,
             ins (.mulx (q .r9) (q .r8) (.reg (q .r11))), movD .rdx .r10], maskNone) ∧
    x64Gpr.op (.fshl 64) (.gpr .rax, .gpr .rsi, .imm 8#64, ()) (.gpr .rax, ()) .default =
      some ([movW .W64 .r11 .rax, movW .W64 .r10 .rsi,
             ins (.shld (.reg (q .r11)) (q .r10) (.imm8 (.int64 8))), movW .W64 .rax .r11], maskAll) ∧
    x64Gpr.load i64 .rax (.baseDisp .rdi 24) =
      some ([ins (.mov (.reg (q .rax)) (.mem (atDisp .rdi 24)))], maskNone) ∧
    x64Gpr.store i32 (.imm 7#32) (.baseDisp .rdi 0) =
      some ([ins32 (.mov (.mem (atReg .rdi)) (immBitsOp .W32 7#32))], maskNone) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sib_addressing_rfl :
    x64Gpr.load i8 .rax (.baseIdxDisp .rdi .rsi .s1 0) =
      some ([ins32 (.movzx (.reg (d .rax)) (.mem (atSIB .rdi .rsi .s1 0) : RegOrMem .W8))],
        maskNone) ∧
    x64Gpr.load i16 .rax (.baseIdxDisp .rdi .rsi .s2 (-4)) =
      some ([ins32 (.movzx (.reg (d .rax)) (.mem (atSIB .rdi .rsi .s2 (-4)) : RegOrMem .W16))],
        maskNone) ∧
    x64Gpr.load i32 .rax (.baseIdxDisp .rdi .rsi .s4 12) =
      some ([ins32 (.mov (.reg (d .rax)) (.mem (atSIB .rdi .rsi .s4 12)))], maskNone) ∧
    x64Gpr.store i64 (.gpr .rbx) (.baseIdxDisp .rdi .rsi .s8 24) =
      some ([ins (.mov (.mem (atSIB .rdi .rsi .s8 24)) (.reg (q .rbx)))], maskNone) ∧
    x64Gpr.load i64 .rax (.baseIdxDisp .rdi .rsi .s8 (Int64.ofInt (2 ^ 32))) =
      some ([moviD .r10 (BitVec.ofNat 64 (2 ^ 32)),
             ins (.lea (q .r10) (atSIB .rdi .r10 .s1 0)),
             ins (.mov (.reg (q .rax)) (.mem (atSIB .r10 .rsi .s8 0)))], maskNone) ∧
    x64Vec.vload v4i32 .mm0 (.baseIdxDisp .rdi .rsi .s4 16) =
      some ([x64VmemDir true .w128 .mm0 (atSIB .rdi .rsi .s4 16)], maskNone) ∧
    x64Vec.vstore v4i32 .mm1 (.baseIdxDisp .rdi .rsi .s8 (-32)) =
      some ([x64VmemDir false .w128 .mm1 (atSIB .rdi .rsi .s8 (-32))], maskNone) ∧
    x64Gpr.load i32 .rax (.baseIdxDisp .rdi .rsp .s4 0) = none ∧
    x64Gpr.store i64 (.gpr .rax) (.baseIdxDisp .rdi .rsp .s8 8) = none ∧
    x64Vec.vload v4i32 .mm0 (.baseIdxDisp .rdi .rsp .s4 0) = none ∧
    x64Vec.vstore v4i32 .mm0 (.baseIdxDisp .rdi .rsp .s4 0) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sib_load32_spec {h : x64Mach.Host} {k : Nat} {s : MachineData} {v : BitVec 32}
    {post : MachineState → Prop}
    (hlv : loadVal s.dmem i32
      (s.regs.get64 .rdi + (s.regs.get64 .rsi <<< 2) + 12#64) = some v)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.load i32 .rax (.baseIdxDisp .rdi .rsi .s4 12) = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c (.rax :: x64Scratch) [] clob s
      (fun s' => GprHolds (s'.regs.get64 .rax) i32 v ∧ s'.dmem = s.dmem) post :=
  x64GprSpec.load_spec hc (by simp [x64Scratch]) (by simp [AddrArg.regs, x64Scratch]) hlv

theorem lea_nondestructive_rfl :
    x64Gpr.op (.add i64) (.gpr .rdi, .gpr .rsi, ()) (.gpr .rax, ()) .default =
      some ([ins (.lea (q .rax) (atSIB .rdi .rsi .s1 0))], maskNone) ∧
    x64Gpr.op (.add i32) (.gpr .rdi, .gpr .rsp, ()) (.gpr .rax, ()) .default =
      some ([ins32 (.lea (d .rax) (atSIB .rsp .rdi .s1 0))], maskNone) ∧
    x64Gpr.op (.add i64) (.gpr .rdi, .imm 12#64, ()) (.gpr .rax, ()) .default =
      some ([ins (.lea (q .rax) (atDisp .rdi 12))], maskNone) ∧
    x64Gpr.op (.sub i32) (.gpr .rdi, .imm 1#32, ()) (.gpr .rax, ()) .default =
      some ([ins32 (.lea (d .rax) (atDisp .rdi (-1)))], maskNone) ∧
    x64Gpr.op (.add i64) (.imm 8#64, .gpr .rdi, ()) (.gpr .rax, ()) .default =
      some ([ins (.lea (q .rax) (atDisp .rdi 8))], maskNone) ∧
    x64Gpr.op (.add i64) (.gpr .rax, .imm 1#64, ()) (.gpr .rax, ()) .default =
      some ([aluBinIns .W64 .add .rax (immBitsOp .W64 1#64)], maskAll) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lea_nondestructive_add_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {va vb : BitVec 64} {post : MachineState → Prop}
    (ha0 : s.regs.get64 .rdi = va) (hb0 : s.regs.get64 .rsi = vb)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.add i64) (.gpr .rdi, .gpr .rsi, ()) (.gpr .rax, ()) .default =
      some (c, clob)) :
    clob = maskNone ∧
    x64Mach.FallsTo x64Gpr.condReads h k c [.rax, .r10, .r11] [] maskNone s
      (fun s' => GprHolds (s'.regs.get64 .rax) i64 (va + vb) ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i64 (.gpr .rdi) va := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [ha0]; exact ⟨by decide, rfl⟩
  have hb : x64Mach.PArgHolds s i64 (.gpr .rsi) vb := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [hb0]; exact ⟨by decide, rfl⟩
  have hcl : clob = maskNone := by
    cases ((rfl : x64Gpr.op (.add i64) (.gpr .rdi, .gpr .rsi, ()) (.gpr .rax, ()) .default =
      some ([ins (.lea (q .rax) (atSIB .rdi .rsi .s1 0))], maskNone)).symm.trans hc); rfl
  subst hcl; refine ⟨rfl, ?_⟩
  have hwp : (OpCode.add i64).wp (va, vb, ()) (fun (r : Tup Val [i64]) => r.1 = va + vb) := rfl
  have hspec := x64GprSpec.op_spec (h := h) (k := k) (post := post) hc
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupDstGprs, x64Scratch])
    (TRel.cons ha (TRel.cons hb .nil)) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨⟨rv, ()⟩, hrv, hdst⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; cases hdst with | cons hd _ => exact hcont s' ⟨hd, hm⟩ hfr

theorem zero32_load_op_rfl :
    x64Gpr.zeroUpper32Load = true ∧
    x64Gpr.zeroUpper32Op (.add i32) (.gpr .rdi, .gpr .rsi, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.and i32) (.gpr .rax, .imm 15#32, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.lshr i32) (.gpr .rax, .imm 1#32, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.lshr i32) (.gpr .rax, .imm 0#32, ()) (.gpr .rax, ()) = false ∧
    x64Gpr.zeroUpper32Op (.trunc 64 32) (.gpr .rdi, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.trunc 64 32) (.gpr .rax, ()) (.gpr .rax, ()) = false ∧
    x64Gpr.zeroUpper32Op (.clz 32) (.gpr .rdi, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.ctz 32) (.gpr .rdi, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.popcnt 32) (.gpr .rdi, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.udiv 32) (.gpr .rdi, .gpr .rsi, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.fshl 32) (.gpr .rdi, .gpr .rsi, .imm 3#32, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.select i32) (.flag .z, .gpr .rdi, .gpr .rsi, ()) (.gpr .rax, ()) = true ∧
    x64Gpr.zeroUpper32Op (.copy i32) (.gpr .rax, ()) (.gpr .rax, ()) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zero32_load_spec {h : x64Mach.Host} {k : Nat} {s : MachineData} {v : BitVec 32}
    {post : MachineState → Prop}
    (hlv : loadVal s.dmem i32 (s.regs.get64 .rdi + 8#64) = some v)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.load i32 .rax (.baseDisp .rdi 8) = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c (.rax :: x64Scratch) [] clob s
      (fun s' => s'.regs.get64 .rax = v.setWidth 64 ∧ s'.dmem = s.dmem) post :=
  x64GprSpec.load_zero32 rfl hc (by simp [x64Scratch]) (by simp [AddrArg.regs, x64Scratch]) hlv

theorem zero32_add_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {va vb : BitVec 32} {post : MachineState → Prop}
    (ha0 : (s.regs.get64 .rdi).setWidth 32 = va)
    (hb0 : (s.regs.get64 .rsi).setWidth 32 = vb)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.op (.add i32) (.gpr .rdi, .gpr .rsi, ()) (.gpr .rax, ()) .default =
      some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c (.rax :: x64Scratch) [] clob s
      (fun s' => s'.regs.get64 .rax = (va + vb).setWidth 64 ∧ s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i32 (.gpr .rdi) va := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [ha0]; exact ⟨by decide, rfl⟩
  have hb : x64Mach.PArgHolds s i32 (.gpr .rsi) vb := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [hb0]; exact ⟨by decide, rfl⟩
  have hwp : (OpCode.add i32).wp (va, vb, ()) (fun (r : Tup Val [i32]) => r.1 = va + vb) := rfl
  have hspec := x64GprSpec.op_zero32 (h := h) (k := k) (post := post) rfl hc rfl
    (by simp [tupArgGprs, x64Scratch]) (by simp [x64Scratch])
    (TRel.cons ha (TRel.cons hb .nil)) hwp
  intro hinf hcont
  refine hspec hinf fun s' ⟨⟨rv, hrv, hreg⟩, hm⟩ hfr => ?_
  dsimp at hrv; subst hrv; exact hcont s' ⟨hreg, hm⟩ hfr

theorem unsupported_ops_rejected_rfl :
    x64Gpr.supportsScalarOp (.rbit 64) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.udiv0 64) (.var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.sdiv0 64) (.var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.fadd f64) (.var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.bswap i8) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.addc 16) (.var (), .var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.fshl 16) (.var (), .var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.bitcast v4i32 v4i32 rfl) (.var (), ()) = false ∧
    x64Gpr.op (.rbit 64) (.gpr .rax, ()) (.gpr .rdx, ()) .default = none ∧
    x64Gpr.op (.udiv0 64) (.gpr .rax, .gpr .rsi, ()) (.gpr .rdx, ()) .default = none ∧
    (∀ v0 v1 v2 : RegMm, x64Gpr.op (.fadd f64) (.vec v0, .vec v1, ()) (.vec v2, ()) .default = none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

/-! ## 5. Scalar `Isa` & Kernel `Fn.backendOk` on Legalized `Bignum` & `LratBytes` -/

/-- Empty scalar-only `VecIsa` over `RegMm` for testing `x64Gpr` inside `Isa`. -/
def testEmptyVecIsa : VecIsa Reg64 RegMm CondCode Directive where
  vecScratch := []
  vecAllocatable := []
  vecArgRegs := []
  vecRetRegs := []
  isAbiVec _ := false
  vecSlotWidth _ := none
  vmov _ _ _ := []
  vmovi _ _ _ := none
  vslotSt _ _ _ := []
  vslotLd _ _ _ := []
  vop _ _ _ _ := none
  vload _ _ _ := none
  vstore _ _ _ := none
  supportsVecOp _ _ := false

/-- Minimal SysV scalar `FrameIsa` (6 GPR args, 2 GPR returns, `x64Scratch := [.r10, .r11]`). -/
def testSysVFrameIsa : FrameIsa Reg64 Directive where
  label := Kraken.Directive.label
  sp := .rsp
  scratch := x64Scratch
  allocatable := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]
  calleeSaved := [.rbx, .rbp, .r12, .r13, .r14, .r15]
  raRegs := []
  argRegs := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
  retRegs := [.rax, .rdx]
  bitWidths := [8, 16, 32, 64]
  raBytes := 8
  frameSize ns := 8 * ns
  prologue _ := ([], maskNone)
  epilogue _ := ([], maskNone)
  slotSt _ _ := []
  slotLd _ _ := []
  canonAbi _ _ := ([], maskNone)
  call _ := []
  exitJmp _ := []
  ret := [ins .ret]

/-- Scalar x64 `Isa` driven by the verified `x64Gpr`. -/
def testX64Isa : Isa where
  Reg := Reg64
  VReg := RegMm
  Cond := CondCode
  Directive := Directive
  gpr := x64Gpr
  vec := testEmptyVecIsa
  frame := testSysVFrameIsa

abbrev scalarX64Legal : LegalTarget := LegalTarget.x64 []

theorem bignum_mul4x4_backendOk :
    (Fn.legal scalarX64Legal ⟨"mul4x4", [i64, i64, i64], [], Examples.Bignum.mul4x4⟩).backendOk testX64Isa = true := by
  t_kernel_rfl

theorem bignum_addMod25519_backendOk :
    (Fn.legal scalarX64Legal ⟨"addMod25519", [i64, i64, i64], [], Examples.Bignum.addMod25519⟩).backendOk testX64Isa = true := by
  t_kernel_rfl

theorem bignum_subMod25519_backendOk :
    (Fn.legal scalarX64Legal ⟨"subMod25519", [i64, i64, i64], [], Examples.Bignum.subMod25519⟩).backendOk testX64Isa = true := by
  t_kernel_rfl

theorem lratBytes_all_backendOk :
    Examples.LratBytes.lratBytesFns.all (fun fn => (fn.legal scalarX64Legal).backendOk testX64Isa) = true := by
  t_kernel_rfl

theorem lratBytes_names_verified :
    Examples.LratBytes.lratBytesFns.map Fn.name =
      ["lb_parse_dimacs_header", "lb_parse_dimacs_body", "lb_read_add_lits",
       "lb_rup_check", "lb_check_prf", "lrat_check_bytes"] := by
  t_kernel_rfl

def supportedBitcntFn : Fn := ⟨"ok_bitcnt", [i8, i16, i32, i64], [i64],
  fun _ _ (a, b, c, d, ()) =>
    .let_ ⟨.clz 8, (.var a, ())⟩ fun (r1, ()) =>
    .let_ ⟨.cls 16, (.var b, ())⟩ fun (r2, ()) =>
    .let_ ⟨.ctz 32, (.var c, ())⟩ fun (r3, ()) =>
    .let_ ⟨.popcnt 64, (.var d, ())⟩ fun (r4, ()) =>
    .let_ ⟨.zext 8 64, (.var r1, ())⟩ fun (z1, ()) =>
    .let_ ⟨.zext 16 64, (.var r2, ())⟩ fun (z2, ()) =>
    .let_ ⟨.zext 32 64, (.var r3, ())⟩ fun (z3, ()) =>
    .let_ ⟨.add i64, (.var z1, .var z2, ())⟩ fun (s1, ()) =>
    .let_ ⟨.add i64, (.var z3, .var r4, ())⟩ fun (s2, ()) =>
    .let_ ⟨.add i64, (.var s1, .var s2, ())⟩ fun (s3, ()) =>
    .ret (.var s3, ())⟩

theorem backendOk_accepts_bitcnt : supportedBitcntFn.backendOk testX64Isa = true := by t_kernel_rfl

def unsupportedRbitFn : Fn := ⟨"bad_rbit", [i64], [i64], fun _ _ (a, ()) =>
  .let_ ⟨.rbit 64, (.var a, ())⟩ fun (r, ()) => .ret (.var r, ())⟩

theorem backendOk_rejects_rbit : unsupportedRbitFn.backendOk testX64Isa = false := by t_kernel_rfl

/-! ## 5b. Full `x64Gpr` + `x64Vec` + `x64Frame` `Bignum` Regression -/

/-- Full x64 `Isa` combining `x64Gpr`, `x64Vec`, and `x64Frame`. -/
@[expose] meta def fullX64Isa : Isa where
  Reg := Reg64
  VReg := RegMm
  Cond := CondCode
  Directive := Directive
  gpr := x64Gpr
  vec := x64Vec
  frame := x64Frame

meta def x64CompileMod (m : Module) : Except String (List Directive × List (Sym × Nat)) :=
  let hs := m.fns.map (Fn.computeHints fullX64Isa (LegalTarget.x64))
  compileModule fullX64Isa (LegalTarget.x64) fullX64Isa.frame.raBytes [] m.exits 0 m.fns hs

meta def isMulxDir : Directive → Bool
  | .instr (.regular _ _ (.mulx _ _ _)) => true
  | _ => false

meta def isCarryFlagOpDir : Directive → Bool
  | .instr (.regular _ _ (.adcx _ _)) => true
  | .instr (.regular _ _ (.adox _ _)) => true
  | _ => false

meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true
  | _ => false

#guard (x64CompileMod Examples.Bignum.mul4x4Module).isOk = true
#guard (x64CompileMod Examples.Bignum.addMod25519Module).isOk = true
#guard (x64CompileMod Examples.Bignum.subMod25519Module).isOk = true

#guard
  let code := extractCode (x64CompileMod Examples.Bignum.mul4x4Module)
  let mulxs := (code.filter isMulxDir).length
  let carries := (code.filter isCarryFlagOpDir).length
  let setccs := (code.filter isSetccDir).length
  mulxs > 0 && carries > 0 && setccs == 0

/-! ## 5c. Flag/Mem Compare (`test`, `cmpMem`, `testMem`, `movl`, `.not .bool`) & Leaf Frame -/

theorem c4c_opt_encodings_rfl :
    x64Gpr.op (.cmp .eq i64) (.gpr .rax, .imm 0#64, ()) (.flag .z, ()) .default =
      some ([ins (.test (.reg (q .rax)) (.reg (q .rax)))], maskAll) ∧
    x64Gpr.op (.cmp .slt i32) (.imm 0#32, .gpr .rax, ()) (.flag .g, ()) .default =
      some ([ins32 (.test (.reg (d .rax)) (.reg (d .rax)))], maskAll) ∧
    x64Gpr.op (.not .bool) (.flag .z, ()) (.flag .nz, ()) .default =
      some ([], maskNone) ∧
    x64Gpr.movi .rax 42#64 =
      [ins32 (.mov (.reg (d .rax)) (.imm (.int64 (Int64.ofBitVec 42#64))))] ∧
    x64Gpr.movi .rax (BitVec.ofNat 64 (2 ^ 32)) =
      [ins (.mov (.reg (q .rax)) (.imm (.int64 (Int64.ofBitVec (BitVec.ofNat 64 (2 ^ 32))))))] ∧
    x64Gpr.testOp 32 true (.gpr .rax) (.imm 0x80000000#32) (.flag .nz) =
      some ([ins32 (.test (.reg (d .rax)) (immBitsOp .W32 0x80000000#32))], maskAll) ∧
    x64Gpr.cmpMem .sgt 8 (.baseIdxDisp .rdi .rsi .s1 0) (.imm 0#8) (.flag .g) =
      some ([ins8 (.cmp (.mem (atSIB .rdi .rsi .s1 0)) (immBitsOp .W8 0#8))], maskAll) ∧
    x64Gpr.testMem 32 false (.baseIdxDisp .rdi .rsi .s4 0) (.imm 1#32) (.flag .z) =
      some ([ins32 (.test (.mem (atSIB .rdi .rsi .s4 0)) (immBitsOp .W32 1#32))], maskAll) ∧
    x64Frame.leafZeroFrame = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem c4c_testOp_spec {h : x64Mach.Host} {k : Nat} {s : MachineData} {va : BitVec 32}
    {post : MachineState → Prop}
    (ha0 : (s.regs.get64 .rax).setWidth 32 = va)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.testOp 32 true (.gpr .rax) (.imm 0x80000000#32) (.flag .nz) = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c x64Scratch [] clob s
      (fun s' => x64Mach.evalCond s' .nz = CmpOp.ne.evalBits (va &&& 0x80000000#32) 0#32 ∧
        s'.dmem = s.dmem) post := by
  have ha : x64Mach.PArgHolds s i32 (.gpr .rax) va := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]; rw [ha0]; exact ⟨by decide, rfl⟩
  exact x64GprSpec.testOp_spec (h := h) (k := k) (post := post) hc
    (by simp [PArg.gprs, x64Scratch]) (by simp [PDst.gprs]) ha rfl

theorem c4c_cmpMem_b8_spec {h : x64Mach.Host} {k : Nat} {s : MachineData} {va : BitVec 8}
    {post : MachineState → Prop}
    (hlv : loadVal s.dmem i8 (s.regs.get64 .rdi + (s.regs.get64 .rsi <<< 0) + 0#64) = some va)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.cmpMem .sgt 8 (.baseIdxDisp .rdi .rsi .s1 0) (.imm 0#8) (.flag .g) =
      some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c x64Scratch [] clob s
      (fun s' => x64Mach.evalCond s' .g = CmpOp.sgt.evalBits va 0#8 ∧ s'.dmem = s.dmem) post :=
  x64GprSpec.cmpMem_spec (h := h) (k := k) (post := post) hc
    (by simp [AddrArg.regs, PArg.gprs, x64Scratch]) (by simp [PDst.gprs]) hlv rfl

theorem c4c_testMem_32_spec {h : x64Mach.Host} {k : Nat} {s : MachineData} {va : BitVec 32}
    {post : MachineState → Prop}
    (hlv : loadVal s.dmem i32 (s.regs.get64 .rdi + (s.regs.get64 .rsi <<< 2) + 0#64) = some va)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.testMem 32 false (.baseIdxDisp .rdi .rsi .s4 0) (.imm 1#32) (.flag .z) =
      some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c x64Scratch [] clob s
      (fun s' => x64Mach.evalCond s' .z = CmpOp.eq.evalBits (va &&& 1#32) 0#32 ∧
        s'.dmem = s.dmem) post :=
  x64GprSpec.testMem_spec (h := h) (k := k) (post := post) hc
    (by simp [AddrArg.regs, PArg.gprs, x64Scratch]) (by simp [PDst.gprs]) hlv rfl

/-! ## 6. Axiom Audit -/

#print axioms x64GprSpec
#print axioms x64Gpr_op_spec
#print axioms x64Op_supportsScalarOp
#print axioms x64SupportsScalarOp_complete
#print axioms x64Gpr_op_noLab
#print axioms x64Gpr_testOp_noLab
#print axioms x64Gpr_cmpMem_noLab
#print axioms x64Gpr_testMem_noLab
#print axioms x64Gpr_clearFlags_noLab
#print axioms x64Gpr_mov_noLab
#print axioms x64Gpr_movi_noLab
#print axioms x64Gpr_setcc_noLab
#print axioms x64Gpr_jmp_noLab
#print axioms x64Gpr_jcc_noLab
#print axioms x64Gpr_jnzGpr_noLab
#print axioms x64Gpr_load_noLab
#print axioms x64Gpr_store_noLab
#print axioms sib_load32_spec
#print axioms lea_nondestructive_add_spec
#print axioms zero32_load_op_rfl
#print axioms zero32_load_spec
#print axioms zero32_add_spec
#print axioms c4c_opt_encodings_rfl
#print axioms c4c_testOp_spec
#print axioms c4c_cmpMem_b8_spec
#print axioms c4c_testMem_32_spec
#print axioms bignum_mul4x4_backendOk
#print axioms bignum_addMod25519_backendOk
#print axioms bignum_subMod25519_backendOk
#print axioms lratBytes_all_backendOk
#print axioms pitfall_a_bool_jnz_spec
#print axioms pitfall_a_ofBool_spec
#print axioms pitfall_c_var_shl8_spec
#print axioms bmi2_shlx64_flags_spec
#print axioms bmi2_rorx32_flags_spec
#print axioms bitcnt_clz8_spec
#print axioms bitcnt_cls16_spec
#print axioms bitcnt_ctz32_spec
#print axioms bitcnt_popcnt64_spec
#print axioms loadVal_bool_checks
#print axioms backendOk_accepts_bitcnt
#print axioms backendOk_rejects_rbit

end LeanQbeTest.T.Amd64IselTest
end
