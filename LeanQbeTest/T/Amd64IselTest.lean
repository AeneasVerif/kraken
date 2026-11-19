module

public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Legal
public import LeanQbe.T.FlatLemmas

/-!
# Verification Tests & Audit for `LeanQbe.T.Amd64` (`T8`)

Zero E1 imports (`G5`). Verifies:
1. All three `T8` width/semantic traps on `x64Gpr` and `x64GprSpec`:
   - Pitfall (a): `.bool` upper-bit garbage (`0xdeadbeef_0000ff00#64` vs `0xdeadbeef_0000ff01#64`),
     byte-width `testb` / `movzbl` / `movb`, and `loadVal` rejecting non-`{0,1}` bytes.
   - Pitfall (b): `.bits n` (`n ∈ {8, 16, 32}`) upper-bit garbage handling across `cmp`, shifts,
     rotates, `udiv`/`sdiv`, `zext`/`sext`, and `bswap` (`[16, 32, 64]`).
   - Pitfall (c): Kraken X64 shift-count masking (`& 7` / `& 15` on variable 8/16-bit shifts,
     immediate modulo `n`, and rotate demonic `OF` clobber).
2. Full `T8` opcode, `VariantHint` (`disp`, `decInc`, `adcx`, `adox`, `mulxFast`), and addressing
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
      some ([ins8 (.mov (.reg (b8 .r11)) (.reg (b8 .rax))),
             ins8 (.mov (.reg (b8 .r10)) (.reg (b8 .rcx))),
             ins8 (.and (.reg (b8 .r11)) (.reg (b8 .r10))),
             ins32 (.movzx (.reg (d .rdx)) (.reg (b8 .r11)))], maskAll) :=
  rfl

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
             moviD .rdx 0, ins32 (.div (.reg (d .r11))),
             movD .r11 .rax, movD .rdx .r10, movD .rax .rsi, movD .rsi .r11], maskAll) ∧
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
    x64Gpr.op (.rotl i64) (.gpr .rax, .imm 5#64, ()) (.gpr .rax, ()) .default =
      some ([ins (.rol (.reg (q .rax)) (.imm8 (.int64 5)))], maskCF ||| maskOF) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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

/-! ## 4. Additional `T8` Hints, Multi-Limb Ops, and Explicit Rejections -/

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

theorem unsupported_ops_rejected_rfl :
    x64Gpr.supportsScalarOp (.clz 64) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.cls 64) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.rbit 64) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.ctz 64) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.popcnt 64) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.udiv0 64) (.var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.sdiv0 64) (.var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.fadd f64) (.var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.bswap i8) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.addc 16) (.var (), .var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.fshl 16) (.var (), .var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.bitcast v4i32 v4i32 rfl) (.var (), ()) = false ∧
    x64Gpr.op (.clz 64) (.gpr .rax, ()) (.gpr .rdx, ()) .default = none ∧
    x64Gpr.op (.popcnt 64) (.gpr .rax, ()) (.gpr .rdx, ()) .default = none ∧
    x64Gpr.op (.udiv0 64) (.gpr .rax, .gpr .rsi, ()) (.gpr .rdx, ()) .default = none ∧
    (∀ v0 v1 v2 : RegMm, x64Gpr.op (.fadd f64) (.vec v0, .vec v1, ()) (.vec v2, ()) .default = none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

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

def unsupportedClzFn : Fn := ⟨"bad_clz", [i64], [i64], fun _ _ (a, ()) =>
  .let_ ⟨.clz 64, (.var a, ())⟩ fun (r, ()) => .ret (.var r, ())⟩

theorem backendOk_rejects_clz : unsupportedClzFn.backendOk testX64Isa = false := by t_kernel_rfl

/-! ## 6. Axiom Audit -/

#print axioms x64GprSpec
#print axioms x64Gpr_op_spec
#print axioms x64Op_supportsScalarOp
#print axioms x64SupportsScalarOp_complete
#print axioms x64Gpr_op_noLab
#print axioms x64Gpr_clearFlags_noLab
#print axioms x64Gpr_mov_noLab
#print axioms x64Gpr_movi_noLab
#print axioms x64Gpr_setcc_noLab
#print axioms x64Gpr_jmp_noLab
#print axioms x64Gpr_jcc_noLab
#print axioms x64Gpr_jnzGpr_noLab
#print axioms x64Gpr_load_noLab
#print axioms x64Gpr_store_noLab
#print axioms bignum_mul4x4_backendOk
#print axioms bignum_addMod25519_backendOk
#print axioms bignum_subMod25519_backendOk
#print axioms lratBytes_all_backendOk
#print axioms pitfall_a_bool_jnz_spec
#print axioms pitfall_a_ofBool_spec
#print axioms pitfall_c_var_shl8_spec
#print axioms loadVal_bool_checks
#print axioms backendOk_rejects_clz

end LeanQbeTest.T.Amd64IselTest
end
