module

public import LeanQbe.T.Amd64.Isel
public import LeanQbe.T.OpsLemmas
public import LeanQbe.T.TargetLemmas
import Kraken.X64.Parser

/-!
# Typed x64 Scalar Instruction Selection: Foundations & Non-`op` Specs (`T8`)

Part 1 of the verification of `x64Gpr`:
* `ParserChecks`: `rfl` checks against `Kraken.X64.Parser` covering every emitted directive form.
* `NoLab`: `AllInstr` and `∀ l, Kraken.Directive.label l ∉ ...` lemmas for `x64Gpr` generators.
* Shared BitVec, `Reg64s`, `GprHolds`, `UpdFlags`, `subFlags` (8/16/32/64), and `loadVal`/`storeMem`
  helper lemmas.
* Core `Directive.FallsTo` → `x64Mach.FallsTo` combinators and proofs of `negCond_reads`,
  `negCond_eval`, `clearFlags_spec`, `mov_spec`, `movi_spec`, `setcc_spec`, `jmp_spec`, `jcc_spec`,
  `jnzGpr_spec`, `load_spec`, and `store_spec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Amd64

/-! ## 1. `ParserChecks` (`rfl` against `Kraken.X64.Parser`) -/

section ParserChecks
open Kraken.X64.Parser

-- Moves, immediates, and extensions
example : ⸨prog| mov %rsi, %rax ⸩ = [movD .rax .rsi] := rfl
example : ⸨prog| movl %esi, %eax ⸩ = [movlD .rax .rsi] := rfl
example : ⸨prog| mov $5, %rax ⸩ = [moviD .rax 5] := rfl
example : ⸨prog| mov $-1, %rax ⸩ = [moviD .rax (-1)] := rfl
example : ⸨prog| movzbl %sil, %eax ⸩ = [movW .W8 .rax .rsi] := rfl
example : ⸨prog| movzwl %si, %eax ⸩ = [movW .W16 .rax .rsi] := rfl
example : ⸨prog| movl %esi, %eax ⸩ = [movW .W32 .rax .rsi] := rfl
example : ⸨prog| mov %rsi, %rax ⸩ = [movW .W64 .rax .rsi] := rfl
example : ⸨prog| movb %sil, %r10b ⸩ = [ins8 (.mov (.reg (b8 .r10)) (.reg (b8 .rsi)))] := rfl
example : ⸨prog| movzbl %r11b, %esi ⸩ = [ins32 (.movzx (.reg (d .rsi)) (.reg (b8 .r11)))] := rfl
example : ⸨prog| movzwl %r11w, %esi ⸩ = [ins32 (.movzx (.reg (d .rsi)) (.reg (h16 .r11)))] := rfl
example : ⸨prog| movsbq %sil, %rax ⸩ = [ins (.movsx (.reg (q .rax)) (.reg (b8 .rsi)))] := rfl
example : ⸨prog| movsbl %sil, %eax ⸩ = [ins32 (.movsx (.reg (d .rax)) (.reg (b8 .rsi)))] := rfl
example : ⸨prog| movswq %si, %rax ⸩ = [ins (.movsx (.reg (q .rax)) (.reg (h16 .rsi)))] := rfl
example : ⸨prog| movswl %si, %eax ⸩ = [ins32 (.movsx (.reg (d .rax)) (.reg (h16 .rsi)))] := rfl
example : ⸨prog| movslq %esi, %rax ⸩ = [ins (.movsx (.reg (q .rax)) (.reg (d .rsi)))] := rfl

-- Control flow, flag clearing, and tests
example : ⸨prog| xorl %r10d, %r10d ⸩ = x64Gpr.clearFlags := rfl
example : ⸨prog| jmp L0 ⸩ = x64Gpr.jmp "L0" := rfl
example : ⸨prog| jnz L0 ⸩ = x64Gpr.jcc .nz "L0" := rfl
example : ⸨prog| je L0 ⸩ = x64Gpr.jcc .z "L0" := rfl
example : ⸨prog| jl L0 ⸩ = x64Gpr.jcc .l "L0" := rfl
example : ⸨prog| jb L0 ⸩ = x64Gpr.jcc .c "L0" := rfl
example : ⸨prog| testb %al, %al; jnz L0 ⸩ = (x64Gpr.jnzGpr .rax "L0").1 := rfl
example : ⸨prog| sete %al; movzbl %al, %eax ⸩ = x64Gpr.setcc .rax .z := rfl
example : ⸨prog| setne %al; movzbl %al, %eax ⸩ = x64Gpr.setcc .rax .nz := rfl
example : ⸨prog| setb %al; movzbl %al, %eax ⸩ = x64Gpr.setcc .rax .c := rfl
example : ⸨prog| seto %al; movzbl %al, %eax ⸩ = x64Gpr.setcc .rax .o := rfl
example : ⸨prog| setle %al; movzbl %al, %eax ⸩ = x64Gpr.setcc .rax .le := rfl
example : ⸨prog| setg %al; movzbl %al, %eax ⸩ = x64Gpr.setcc .rax .g := rfl

-- Binary/unary ALU, LEA, inc/dec, and bswap
example : ⸨prog| addb %sil, %al ⸩ = [aluBinIns .W8 .add .rax (.reg (b8 .rsi))] := rfl
example : ⸨prog| subw %si, %ax ⸩ = [aluBinIns .W16 .sub .rax (.reg (h16 .rsi))] := rfl
example : ⸨prog| andl %esi, %eax ⸩ = [aluBinIns .W32 .and .rax (.reg (d .rsi))] := rfl
example : ⸨prog| orq %rsi, %rax ⸩ = [aluBinIns .W64 .or .rax (.reg (q .rsi))] := rfl
example : ⸨prog| xorq $7, %rax ⸩ = [aluBinIns .W64 .xor .rax (immBitsOp .W64 7)] := rfl
example : ⸨prog| imull %esi, %eax ⸩ = [aluBinIns .W8 .mul .rax (.reg (b8 .rsi))] := rfl
example : ⸨prog| imulw %si, %ax ⸩ = [aluBinIns .W16 .mul .rax (.reg (h16 .rsi))] := rfl
example : ⸨prog| imull $3, %eax ⸩ = [aluBinIns .W8 .mul .rax (.imm (.int64 3))] := rfl
example : ⸨prog| imulq %rsi, %rax ⸩ = [aluBinIns .W64 .mul .rax (.reg (q .rsi))] := rfl
example : ⸨prog| negb %al ⸩ = [ins8 (.neg (.reg (b8 .rax)))] := rfl
example : ⸨prog| notq %rax ⸩ = [ins (.not (.reg (q .rax)))] := rfl
example : ⸨prog| incl %eax ⸩ = [ins32 (.inc (.reg (d .rax)))] := rfl
example : ⸨prog| decq %rax ⸩ = [ins (.dec (.reg (q .rax)))] := rfl
example : ⸨prog| leal 8(%rax), %ecx ⸩ = [ins32 (.lea (d .rcx) (atDisp .rax 8))] := rfl
example : ⸨prog| leaq -16(%rbp), %rax ⸩ = [ins (.lea (q .rax) (atDisp .rbp (-16)))] := rfl
example : ⸨prog| rolw $8, %ax ⸩ = [ins16 (.rol (.reg (h16 .rax)) (.imm8 (.int64 8)))] := rfl
example : ⸨prog| bswapl %eax ⸩ = [ins32 (.bswap (d .rax))] := rfl
example : ⸨prog| bswapq %rax ⸩ = [ins (.bswap (q .rax))] := rfl

-- Shifts, rotates, funnel shifts, and masking
example : ⸨prog| shlb %cl, %r11b ⸩ = [ins8 (.shl (.reg (b8 .r11)) .cl)] := rfl
example : ⸨prog| shrw %cl, %r11w ⸩ = [ins16 (.shr (.reg (h16 .r11)) .cl)] := rfl
example : ⸨prog| sarl $3, %eax ⸩ = [ins32 (.sar (.reg (d .rax)) (.imm8 (.int64 3)))] := rfl
example : ⸨prog| rolq $5, %rax ⸩ = [ins (.rol (.reg (q .rax)) (.imm8 (.int64 5)))] := rfl
example : ⸨prog| rorq %cl, %r11 ⸩ = [ins (.ror (.reg (q .r11)) .cl)] := rfl
example : ⸨prog| andl $7, %ecx ⸩ = shiftMaskRcx .W8 := rfl
example : ⸨prog| andl $15, %ecx ⸩ = shiftMaskRcx .W16 := rfl
example : ⸨prog| shldl %cl, %r10d, %r11d ⸩ =
    [ins32 (.shld (.reg (d .r11)) (d .r10) .cl)] := rfl
example : ⸨prog| shrdq $4, %r10, %r11 ⸩ =
    [ins (.shrd (.reg (q .r11)) (q .r10) (.imm8 (.int64 4)))] := rfl

-- Compare, cmov, carry/borrow, wide multiply, and divide
example : ⸨prog| cmpb %sil, %al ⸩ = [ins8 (.cmp (.reg (b8 .rax)) (.reg (b8 .rsi)))] := rfl
example : ⸨prog| cmpl $42, %eax ⸩ = [ins32 (.cmp (.reg (d .rax)) (.imm (.int64 42)))] := rfl
example : ⸨prog| cmovnzl %esi, %eax ⸩ = [ins32 (.cmovcc .nz (d .rax) (.reg (d .rsi)))] := rfl
example : ⸨prog| cmovlq %rsi, %rax ⸩ = [ins (.cmovcc .l (q .rax) (.reg (q .rsi)))] := rfl
example : ⸨prog| adcl %esi, %eax ⸩ = [ins32 (.adc (.reg (d .rax)) (.reg (d .rsi)))] := rfl
example : ⸨prog| adcxl %esi, %eax ⸩ = [ins32 (.adcx (d .rax) (.reg (d .rsi)))] := rfl
example : ⸨prog| adoxq %rsi, %rax ⸩ = [ins (.adox (q .rax) (.reg (q .rsi)))] := rfl
example : ⸨prog| sbbq $1, %rax ⸩ = [ins (.sbb (.reg (q .rax)) (.imm (.int64 1)))] := rfl
example : ⸨prog| mulq %r11 ⸩ = [ins (.mul (.reg (q .r11)))] := rfl
example : ⸨prog| imulq %r11 ⸩ = [ins (.imul1 (.reg (q .r11)))] := rfl
example : ⸨prog| mulxl %r11d, %eax, %edx ⸩ =
    [ins32 (.mulx (d .rdx) (d .rax) (.reg (d .r11)))] := rfl
example : ⸨prog| mulxq %r11, %rax, %rdx ⸩ =
    [ins (.mulx (q .rdx) (q .rax) (.reg (q .r11)))] := rfl
example : ⸨prog| divl %r11d ⸩ = [ins32 (.div (.reg (d .r11)))] := rfl
example : ⸨prog| idivq %r11 ⸩ = [ins (.idiv (.reg (q .r11)))] := rfl
example : ⸨prog| sarl $31, %edx ⸩ = [ins32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31)))] := rfl
example : ⸨prog| sarq $63, %rdx ⸩ = [ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63)))] := rfl

-- Loads and stores
example : ⸨prog| movzbl (%rdx), %eax ⸩ = ((x64Load .bool .rax (.baseDisp .rdx 0)).get rfl).1 := rfl
example : ⸨prog| movzwl 8(%rdx), %eax ⸩ =
    ((x64Load (.bits 16) .rax (.baseDisp .rdx 8)).get rfl).1 := rfl
example : ⸨prog| movl (%rdx), %eax ⸩ =
    ((x64Load (.bits 32) .rax (.baseDisp .rdx 0)).get rfl).1 := rfl
example : ⸨prog| movq -8(%rdx), %rax ⸩ =
    ((x64Load (.bits 64) .rax (.baseDisp .rdx (-8))).get rfl).1 := rfl
example : ⸨prog| movb %sil, (%rdx) ⸩ =
    ((x64Store .bool (.gpr .rsi) (.baseDisp .rdx 0)).get rfl).1 := rfl
example : ⸨prog| movb $1, (%rdx) ⸩ =
    ((x64Store .bool (.imm true) (.baseDisp .rdx 0)).get rfl).1 := rfl
example : ⸨prog| movw %si, (%rdx) ⸩ =
    ((x64Store (.bits 16) (.gpr .rsi) (.baseDisp .rdx 0)).get rfl).1 := rfl
example : ⸨prog| movl $42, 8(%rdx) ⸩ =
    ((x64Store (.bits 32) (.imm 42#32) (.baseDisp .rdx 8)).get rfl).1 := rfl
example : ⸨prog| movq %rsi, (%rdx) ⸩ =
    ((x64Store (.bits 64) (.gpr .rsi) (.baseDisp .rdx 0)).get rfl).1 := rfl

end ParserChecks

@[expose] public section

/-! ## 2. Width Eliminators and `NoLab` (`Kraken.Directive.label l ∉ ...`) -/

theorem withWidth_elim {F : Nat → Type} {α : Type} {n : Nat} {x : F n}
    {k : (w : Width) → F w.bits → Option α} {res : α} {P : Prop}
    (h : withWidth n x k = some res)
    (hk : ∀ (w : Width) (hn : n = w.bits), k w (hn ▸ x) = some res → P) : P := by
  rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64)) with
    rfl | rfl | rfl | rfl | ⟨h8, h16, h32, h64⟩
  · exact hk .W8 rfl h
  · exact hk .W16 rfl h
  · exact hk .W32 rfl h
  · exact hk .W64 rfl h
  · unfold withWidth at h
    split at h <;> first | contradiction | exact False.elim (Option.noConfusion h)

theorem withWideWidth_elim {F : Nat → Type} {α : Type} {n : Nat} {x : F n}
    {k : (w : Width) → F w.bits → Option α} {res : α} {P : Prop}
    (h : withWideWidth n x k = some res)
    (hk : ∀ (w : Width) (hn : n = w.bits), k w (hn ▸ x) = some res → P) : P := by
  rcases (by omega : n = 32 ∨ n = 64 ∨ (n ≠ 32 ∧ n ≠ 64)) with
    rfl | rfl | ⟨h32, h64⟩
  · exact hk .W32 rfl h
  · exact hk .W64 rfl h
  · unfold withWideWidth at h
    split at h <;> first | contradiction | exact False.elim (Option.noConfusion h)

theorem x64Gpr_clearFlags_noLab : ∀ l, Kraken.Directive.label l ∉ x64Gpr.clearFlags :=
  emitClean_noLab _
theorem x64Gpr_mov_noLab (rd rs : Reg64) : ∀ l, Kraken.Directive.label l ∉ x64Gpr.mov rd rs :=
  emitClean_noLab _
theorem x64Gpr_movi_noLab (rd : Reg64) (c : BitVec 64) :
    ∀ l, Kraken.Directive.label l ∉ x64Gpr.movi rd c :=
  emitClean_noLab _
theorem x64Gpr_setcc_noLab (rd : Reg64) (cc : CondCode) :
    ∀ l, Kraken.Directive.label l ∉ x64Gpr.setcc rd cc :=
  emitClean_noLab _
theorem x64Gpr_jmp_noLab (lbl : Sym) : ∀ l, Kraken.Directive.label l ∉ x64Gpr.jmp lbl :=
  emitClean_noLab _
theorem x64Gpr_jcc_noLab (cc : CondCode) (lbl : Sym) :
    ∀ l, Kraken.Directive.label l ∉ x64Gpr.jcc cc lbl :=
  emitClean_noLab _
theorem x64Gpr_jnzGpr_noLab (r : Reg64) (lbl : Sym) :
    ∀ l, Kraken.Directive.label l ∉ (x64Gpr.jnzGpr r lbl).1 :=
  emitClean_noLab _
theorem x64Gpr_load_noLab {t : Ty} {rd : Reg64} {a : AddrArg Reg64} {c : List Directive}
    {clob : FlagMask} (h : x64Gpr.load t rd a = some (c, clob)) :
    ∀ l, Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab h
theorem x64Gpr_store_noLab {t : Ty} {pa : PArg Reg64 RegMm CondCode t} {a : AddrArg Reg64}
    {c : List Directive} {clob : FlagMask} (h : x64Gpr.store t pa a = some (c, clob)) :
    ∀ l, Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab h

/-! ## 3. Shared BitVec, Register, Flag-Frame, `subFlags`, and Memory Helpers -/

theorem width_bits_le_64 (w : Width) : w.bits ≤ 64 := by cases w <;> decide
theorem width_bits_pos (w : Width) : 0 < w.bits := by cases w <;> decide

theorem GprHolds.bits_iff (w : Width) (rv : BitVec 64) (v : BitVec w.bits) :
    GprHolds rv (.bits w.bits) v ↔ rv.setWidth w.bits = v := by
  cases w <;> simp [GprHolds, Width.bits]

theorem GprHolds.of_eq {rv : BitVec 64} {w : Width} {v : BitVec w.bits}
    (h : rv.setWidth w.bits = v) : GprHolds rv (.bits w.bits) v :=
  (GprHolds.bits_iff w rv v).2 h

theorem GprHolds.setWidth_bits {rv : BitVec 64} {w : Width} {v : BitVec w.bits}
    (h : GprHolds rv (.bits w.bits) v) : rv.setWidth w.bits = v :=
  (GprHolds.bits_iff w rv v).1 h

theorem GprHolds.bool_iff (rv : BitVec 64) (b : Bool) :
    GprHolds rv .bool b ↔ rv.setWidth 8 = BitVec.ofNat 8 b.toNat := Iff.rfl

theorem setWidth_64_setWidth (w : Width) (x : BitVec w.bits) :
    (x.setWidth 64).setWidth w.bits = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w), BitVec.setWidth_eq]

theorem replaceLow_setWidth_le {n : Nat} (hn : n ≤ 64) (old : BitVec 64) (v : BitVec n) :
    (old.replaceLow v).setWidth n = v := by
  ext i hi
  simp only [BitVec.replaceLow, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth]
  have h1 : i < 64 := by omega
  simp [h1, hi, BitVec.getLsbD_append]

@[t_step_simp]
theorem get_regW (w : Width) (regs : Reg64s) (r : Reg64) :
    regs.get (regW w r) = (regs.get64 r).setWidth w.bits := by
  cases w <;> simp [regW, t_step_simp]

theorem set_regW_get64_same (w : Width) (regs : Reg64s) (r : Reg64) (v : w.type) :
    ((regs.set (regW w r) v).get64 r).setWidth w.bits = v := by
  cases w with
  | W8 =>
    show ((regs.set64 r ((regs.get64 r).replaceLow v)).get64 r).setWidth 8 = v
    rw [Reg64s.get64_set64_same, replaceLow_setWidth_le (by decide)]
  | W16 =>
    show ((regs.set64 r ((regs.get64 r).replaceLow v)).get64 r).setWidth 16 = v
    rw [Reg64s.get64_set64_same, replaceLow_setWidth_le (by decide)]
  | W32 =>
    simp [regW, Reg64s.set_low32, Reg64s.get64_set64_same, Width.bits]
  | W64 =>
    simp [regW, Reg64s.set_low64, Reg64s.get64_set64_same, Width.bits]

theorem set_regW_get64_ne (w : Width) (regs : Reg64s) {r r' : Reg64} (v : w.type) (hne : r ≠ r') :
    (regs.set (regW w r) v).get64 r' = regs.get64 r' := by
  cases w <;> simp [regW, Reg64s.set, Reg64s.get64_set64_of_ne _ r r' _ hne]

theorem fitsImm32_spec {c : BitVec 64} (_h : fitsImm32 c = true) :
    (Int64.ofBitVec c).toBitVec = c := by
  simp [Int64.toBitVec_ofBitVec]

theorem truncate_signExtend_64 {n : Nat} (hn : n ≤ 64) (c : BitVec n) :
    (c.signExtend 64).truncate n = c := by
  rw [BitVec.truncate_eq_setWidth]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : (i : Nat) < 64 := Nat.lt_of_lt_of_le hi hn
  simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
  rw [BitVec.getLsbD_signExtend]
  simp [hi, hi64]

theorem setWidth_32_64 {n : Nat} (hn : n ≤ 32) (x : BitVec n) :
    (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases Nat.lt_or_ge i 32 with hlt | hge
  · simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, decide_eq_true hlt, Bool.true_and]
  · have hge' : ¬ (i : Nat) < 32 := by omega
    simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, decide_false, Bool.true_and,
      hge', Bool.false_and]
    exact (BitVec.getLsbD_of_ge x i (by omega)).symm

theorem immBitsOp_interp [Labels] (w : Width) (c : BitVec w.bits) (s : MachineData)
    (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :
    (@Operand.interp w _ ⟨.W64⟩ (immBitsOp w c) s p ret) = ret c s := by
  dsimp only [immBitsOp, Operand.interp, ConstExpr.interp]
  rw [Int64.toBitVec_ofBitVec, truncate_signExtend_64 (width_bits_le_64 w)]

theorem updFlags_maskAll (s s' : MachineData) : x64Mach.UpdFlags x64CondReads s s' maskAll := by
  intro cc h
  cases cc <;> simp [x64CondReads, FlagMask.disjoint, maskAll, maskOF, maskCF, maskZF, maskSF, maskPF] at h

theorem updFlags_of_status_eq {s s' : MachineData} (h : s'.status = s.status) (m : FlagMask) :
    x64Mach.UpdFlags x64CondReads s s' m := fun cc _ => by
  simp only [h]

theorem updFlags_maskDecInc {s s' : MachineData} (hcf : s'.status.cf = s.status.cf) :
    x64Mach.UpdFlags x64CondReads s s' maskDecInc := by
  refine keepsFlags_of_bits (fun _ => hcf) ?_ ?_ ?_ ?_ <;>
    (intro hb; simp [maskDecInc, maskPF, maskAF, maskZF, maskSF, maskOF] at hb)

theorem updFlags_maskCF_OF {s s' : MachineData}
    (hpf : s'.status.pf = s.status.pf) (hzf : s'.status.zf = s.status.zf)
    (hsf : s'.status.sf = s.status.sf) :
    x64Mach.UpdFlags x64CondReads s s' (maskCF ||| maskOF) := by
  refine keepsFlags_of_bits ?_ (fun _ => hpf) (fun _ => hzf) (fun _ => hsf) ?_ <;>
    (intro hb; simp [maskCF, maskOF] at hb)

theorem updFlags_maskCF {s s' : MachineData}
    (hpf : s'.status.pf = s.status.pf) (hzf : s'.status.zf = s.status.zf)
    (hsf : s'.status.sf = s.status.sf) (hof : s'.status.of = s.status.of) :
    x64Mach.UpdFlags x64CondReads s s' maskCF := by
  refine keepsFlags_of_bits ?_ (fun _ => hpf) (fun _ => hzf) (fun _ => hsf) (fun _ => hof)
  intro hb; simp [maskCF] at hb

theorem updFlags_maskOF {s s' : MachineData}
    (hcf : s'.status.cf = s.status.cf) (hpf : s'.status.pf = s.status.pf)
    (hzf : s'.status.zf = s.status.zf) (hsf : s'.status.sf = s.status.sf) :
    x64Mach.UpdFlags x64CondReads s s' maskOF := by
  refine keepsFlags_of_bits (fun _ => hcf) (fun _ => hpf) (fun _ => hzf) (fun _ => hsf) ?_
  intro hb; simp [maskOF] at hb

/-- Flags computed by Kraken's `cmp` for `a - b` at width `n`. -/
def subFlags {n : Nat} (a b : BitVec n) : StatusFlags :=
  StatusFlags.from_result (a - b)
    { cf := (a - b).unsigned != a.unsigned - b.unsigned,
      af := ((a - b).take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := (a - b).signed != a.signed - b.signed }

private theorem subFlags_cf {n : Nat} (x y : BitVec n) :
    (subFlags x y).cf = x.ult y := by
  simp only [subFlags, StatusFlags.from_result, BitVec.unsigned, BitVec.ult]
  have hx := x.isLt; have hy := y.isLt
  have hsub : (x - y).toNat = (2 ^ n - y.toNat + x.toNat) % 2 ^ n := BitVec.toNat_sub x y
  by_cases hlt : x.toNat < y.toNat
  · have hmod : (2 ^ n - y.toNat + x.toNat) % 2 ^ n = 2 ^ n + x.toNat - y.toNat := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hsub, hmod, decide_eq_true hlt]
    simp only [bne_iff_ne, ne_eq]
    omega
  · have hmod : (2 ^ n - y.toNat + x.toNat) % 2 ^ n = x.toNat - y.toNat := by
      have : 2 ^ n - y.toNat + x.toNat = 2 ^ n + (x.toNat - y.toNat) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, hmod, decide_eq_false hlt, bne_eq_false_iff_eq]
    omega

private theorem subFlags_zf {n : Nat} (x y : BitVec n) :
    (subFlags x y).zf = decide (x = y) := by
  simp only [subFlags, StatusFlags.from_result, BitVec.zero]
  by_cases heq : x = y
  · subst heq; simp [BitVec.sub_self]
  · have hne : x - y ≠ 0#n := fun h => by
      have he : x = y := by rw [← BitVec.sub_add_cancel x y, h, BitVec.zero_add]
      exact heq he
    simp [heq, hne]

private theorem two_pow_coe {n : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) :
    ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) ∧
      ((2 ^ (n - 1) : Nat) : Int) = (2 : Int) ^ (n - 1) := by
  rcases hn with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

private theorem int_add_emod_self (d m : Int) : (d + m) % m = d % m := by
  rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

private theorem bmod_two_pow (m : Nat) (H : Int) (hm : (m : Int) = 2 * H) (hpos : 0 < H)
    (d : Int) (hd1 : -(2 * H) < d) (hd2 : d < 2 * H) :
    (decide (d.bmod m < 0) != (d.bmod m != d)) = decide (d < 0) := by
  have hpow2 : ((m : Int) + 1) / 2 = H := by omega
  have hbmod : d.bmod m =
      if d < -H then d + 2 * H else if H ≤ d then d - 2 * H else d := by
    rw [Int.bmod_def, hpow2, hm]
    by_cases hlt : d < -H
    · have hmod : d % (2 * H) = d + 2 * H := by
        rw [← int_add_emod_self d (2 * H)]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      simp only [hlt, ↓reduceIte, hmod]
      split
      · rfl
      · exfalso; omega
    · by_cases hge : H ≤ d
      · have hmod : d % (2 * H) = d := Int.emod_eq_of_lt (by omega) (by omega)
        simp only [hlt, hge, ↓reduceIte, hmod]
        split
        · exfalso; omega
        · rfl
      · by_cases h0 : 0 ≤ d
        · have hmod : d % (2 * H) = d := Int.emod_eq_of_lt h0 (by omega)
          simp only [hlt, hge, ↓reduceIte, hmod]
          split
          · rfl
          · exfalso; omega
        · have hmod : d % (2 * H) = d + 2 * H := by
            rw [← int_add_emod_self d (2 * H)]
            exact Int.emod_eq_of_lt (by omega) (by omega)
          simp only [hlt, hge, ↓reduceIte, hmod]
          split
          · exfalso; omega
          · omega
  rw [hbmod]
  by_cases hlt : d < -H
  · have hn0 : ¬ (d + 2 * H < 0) := by omega
    have hne : d + 2 * H ≠ d := by omega
    simp only [hlt, ↓reduceIte, hn0, decide_false, Bool.false_bne]
    simpa [show d < 0 by omega] using hne
  · by_cases hge : H ≤ d
    · have hn0 : d - 2 * H < 0 := by omega
      have hne : d - 2 * H ≠ d := by omega
      simp only [hlt, hge, ↓reduceIte, hn0, decide_true, Bool.true_bne]
      simpa [show ¬ d < 0 by omega] using hne
    · simp only [hlt, hge, ↓reduceIte, bne_self_eq_false, Bool.bne_false]

private theorem subFlags_l {n : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x y : BitVec n) :
    ((subFlags x y).sf != (subFlags x y).of) = x.slt y := by
  simp only [subFlags, StatusFlags.from_result, BitVec.signed, BitVec.slt]
  rw [BitVec.msb_eq_toInt, BitVec.toInt_sub]
  obtain ⟨hpow, hcoe⟩ := two_pow_coe hn
  have hpos : (0 : Int) < ((2 ^ (n - 1) : Nat) : Int) := by
    exact_mod_cast Nat.pow_pos (a := 2) (n := n - 1) (by decide)
  have hx := @BitVec.le_toInt n x
  have hx2 := @BitVec.toInt_lt n x
  have hy := @BitVec.le_toInt n y
  have hy2 := @BitVec.toInt_lt n y
  rw [← hcoe] at hx hx2 hy hy2
  have heq := bmod_two_pow (2 ^ n) ((2 ^ (n - 1) : Nat) : Int) hpow hpos
    (x.toInt - y.toInt) (by omega) (by omega)
  by_cases hlt : x.toInt < y.toInt
  · have hlt' : x.toInt - y.toInt < 0 := by omega
    simpa [hlt, hlt'] using heq
  · have hlt' : ¬ x.toInt - y.toInt < 0 := by omega
    simpa [hlt, hlt'] using heq

theorem cond_subFlags {n : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (co : CmpOp)
    (x y : BitVec n) :
    (condOf co).interp (subFlags x y) = co.evalBits x y := by
  have hcf := subFlags_cf x y
  have hzf := subFlags_zf x y
  have hl := subFlags_l hn x y
  have hbeq : ((subFlags x y).sf == (subFlags x y).of) = !((subFlags x y).sf != (subFlags x y).of) := by
    cases (subFlags x y).sf <;> cases (subFlags x y).of <;> rfl
  have hne : (!decide (x = y)) = decide (x ≠ y) := by by_cases h : x = y <;> simp [h]
  have hule : (x.ult y || decide (x = y)) = x.ule y := by
    simp only [BitVec.ult, BitVec.ule]
    by_cases hlt : x.toNat < y.toNat <;> by_cases hle : x.toNat ≤ y.toNat <;> by_cases heq : x = y
    all_goals first | (simp [hlt, hle, heq]; done) | (subst heq; omega) |
      (exact absurd (BitVec.eq_of_toNat_eq (by omega)) heq) | omega
  have hugt : (!x.ult y && !decide (x = y)) = y.ult x := by
    simp only [BitVec.ult]
    by_cases hlt1 : x.toNat < y.toNat <;> by_cases hlt2 : y.toNat < x.toNat <;> by_cases heq : x = y
    all_goals first | (simp [hlt1, hlt2, heq]; done) | (subst heq; omega) |
      (exact absurd (BitVec.eq_of_toNat_eq (by omega)) heq) | omega
  have huge : (!x.ult y) = y.ule x := by
    simp only [BitVec.ult, BitVec.ule]
    by_cases hlt : x.toNat < y.toNat <;> by_cases hle : y.toNat ≤ x.toNat <;>
      first | (simp [hlt, hle]; done) | omega
  have hsle : (x.slt y || decide (x = y)) = x.sle y := by
    simp only [BitVec.slt, BitVec.sle]
    by_cases hlt : x.toInt < y.toInt <;> by_cases hle : x.toInt ≤ y.toInt <;> by_cases heq : x = y
    all_goals first | (simp [hlt, hle, heq]; done) | (subst heq; omega) |
      (exact absurd (BitVec.eq_of_toInt_eq (by omega)) heq) | omega
  have hsgt : (!decide (x = y) && !x.slt y) = y.slt x := by
    simp only [BitVec.slt]
    by_cases hlt1 : x.toInt < y.toInt <;> by_cases hlt2 : y.toInt < x.toInt <;> by_cases heq : x = y
    all_goals first | (simp [hlt1, hlt2, heq]; done) | (subst heq; omega) |
      (exact absurd (BitVec.eq_of_toInt_eq (by omega)) heq) | omega
  have hsge : (!x.slt y) = y.sle x := by
    simp only [BitVec.slt, BitVec.sle]
    by_cases hlt : x.toInt < y.toInt <;> by_cases hle : y.toInt ≤ x.toInt <;>
      first | (simp [hlt, hle]; done) | omega
  cases co <;>
    simp only [condOf, CondCode.interp, CmpOp.evalBits, hcf, hzf, hbeq, hl]
  · exact hne
  · exact hule
  · exact hugt
  · exact huge
  · exact hsle
  · exact hsgt
  · exact hsge

theorem loadVal_bool_spec {m : Mem 64} {a : BitVec 64} {b : Bool}
    (h : loadVal m .bool a = some b) :
    ∃ i : Int, m.loadInt a 1 = some i ∧ (i = 0 ∨ i = 1) ∧ b = (i == 1) := by
  simp only [loadVal, Ty.bytes, Ty.size] at h
  cases hl : m.loadInt a 1 with
  | none => simp [hl] at h
  | some i =>
    simp only [hl, Option.bind_some] at h
    split at h
    · rename_i h01
      simp only [Option.some.injEq] at h
      simp only [Bool.or_eq_true, beq_iff_eq] at h01
      exact ⟨i, rfl, h01, h.symm⟩
    · simp at h

theorem loadVal_bits_spec {m : Mem 64} {n : Nat} {a : BitVec 64} {v : BitVec n}
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (h : loadVal m (.bits n) a = some v) :
    ∃ i : Int, m.loadInt a (n / 8) = some i ∧ v = BitVec.ofInt n i := by
  have hb : (Ty.bits n).bytes = n / 8 := by rcases hn with rfl | rfl | rfl | rfl <;> decide
  simp only [loadVal, hb] at h
  cases hl : m.loadInt a (n / 8) with
  | none => simp [hl] at h
  | some i =>
    simp only [hl, Option.bind_some, Option.some.injEq] at h
    exact ⟨i, rfl, h.symm⟩

theorem storeMem_bool_eq (m : Mem 64) (a : BitVec 64) (b : Bool) :
    storeMem m .bool a b = Mem.storeInt m a 1 (BitVec.ofNat 8 b.toNat).toInt := by
  cases b <;> rfl

theorem storeMem_bits_eq (m : Mem 64) {n : Nat}
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (a : BitVec 64) (v : BitVec n) :
    storeMem m (.bits n) a v = Mem.storeInt m a (n / 8) v.toInt := by
  rcases hn with rfl | rfl | rfl | rfl <;>
    simp [storeMem, Ty.bytes, Ty.size, toBits]

/-! ## 4. `Directive.FallsTo` / `x64Mach.FallsTo` Combinators and Primitive Directives -/

theorem x64_frame_of_eq {s s' : MachineData} {g : List Reg64} {f : FlagMask}
    (hregs : ∀ r, r ∉ g → s'.regs.get64 r = s.regs.get64 r)
    (hzmms : s'.zmms = s.zmms)
    (hflags : x64Mach.UpdFlags x64CondReads s s' f) :
    x64Mach.Frame x64CondReads s s' g [] f :=
  ⟨hregs, fun vr _ => by simp only [hzmms], hflags⟩

theorem x64_fallsTo_of_wp {c : List Directive} {g : List Reg64} {f : FlagMask}
    {s : MachineData} {Q : MachineData → Prop}
    (hwp : ∀ [Host] (E : Int64 → MachineData → Prop),
      _root_.Program.wp c (fun s' => Q s' ∧ x64Mach.Frame x64CondReads s s' g [] f) E s)
    {h : Host} {k : Nat} {post : MachineState → Prop} :
    x64Mach.FallsTo x64CondReads h k c g [] f s Q post :=
  fun hinf hcont =>
    Program.wp.eventually (@hwp h (fun _ _ => False)) hinf
      (fun s' ⟨hq, hf⟩ => hcont s' hq hf) (fun _ _ hf => hf.elim)

/-- Single-directive `FallsTo` bridge directly to `x64Mach.FallsTo`. -/
theorem dir_to_x64FallsTo {dir : Directive} {g : List Reg64} {f : FlagMask}
    {s : MachineData} {Q P : MachineData → Prop}
    (hd : Directive.FallsTo dir s Q)
    (hqp : ∀ s', Q s' → P s' ∧ x64Mach.Frame x64CondReads s s' g [] f)
    {h : Host} {k : Nat} {post : MachineState → Prop} :
    x64Mach.FallsTo x64CondReads h k [dir] g [] f s P post :=
  x64_fallsTo_of_wp fun {_} _ => Program.wp.mono (Directive.FallsTo.wp hd) hqp

theorem fallsTo_movD (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (movD rd rs) s
      (· = { s with regs := s.regs.set64 rd (s.regs.get64 rs) }) := by
  intro _ _ _ _ _ hk
  simp only [movD, t_step_simp]
  exact hk _ rfl

theorem fallsTo_movlD (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (movlD rd rs) s
      (· = { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 32).zeroExtend 64) }) := by
  intro _ _ _ _ _ hk
  simp only [movlD, t_step_simp]
  exact hk _ rfl

theorem fallsTo_moviD (s : MachineData) (rd : Reg64) (c0 : BitVec 64) :
    Directive.FallsTo (moviD rd c0) s (· = { s with regs := s.regs.set64 rd c0 }) := by
  intro _ _ _ _ _ hk
  simp only [moviD, t_step_simp, ConstExpr.interp, Int64.toBitVec_ofBitVec, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_eq]
  exact hk _ rfl

theorem fallsTo_movW (w : Width) (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (movW w rd rs) s
      (· = { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth w.bits).setWidth 64) }) := by
  intro _ _ _ _ _ hk
  cases w with
  | W8 | W16 =>
    simp only [movW, t_step_simp, BitVec.zeroExtend_eq_setWidth, Width.bits]
    rw [setWidth_32_64 (by decide)]
    exact hk _ rfl
  | W32 =>
    simp only [movW, t_step_simp, BitVec.zeroExtend_eq_setWidth, Width.bits]
    exact hk _ rfl
  | W64 =>
    simp only [movW, t_step_simp]
    refine hk _ ?_
    simp [Width.bits, BitVec.setWidth_eq]

theorem fallsTo_argToBits {w : Width} (s : MachineData) (rd : Reg64)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {v : BitVec w.bits} {dir : Instr}
    (hd : argToBitsI w rd pa = some dir) (hpa : x64Mach.PArgHolds s (.bits w.bits) pa v) :
    Directive.FallsTo (.instr dir) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = v ∧ s' = { s with regs := s.regs.set64 rd rv }) := by
  cases pa with
  | gpr rs =>
    simp only [argToBitsI, Option.some.injEq] at hd; subst hd
    have hrs : (s.regs.get64 rs).setWidth w.bits = v := (GprHolds.bits_iff w _ _).1 hpa
    intro _ _ _ _ _ hk
    refine fallsTo_movW w s rd rs _ _ _ _ ?_
    rintro s' rfl
    exact hk _ ⟨_, by rw [setWidth_64_setWidth, hrs], rfl⟩
  | imm c0 =>
    simp only [argToBitsI, Option.some.injEq] at hd; subst hd
    simp only [Machine.PArgHolds] at hpa; subst hpa
    intro _ _ _ _ _ hk
    refine fallsTo_moviD s rd (c0.setWidth 64) _ _ _ _ ?_
    rintro s' rfl
    exact hk _ ⟨c0.setWidth 64, setWidth_64_setWidth w c0, rfl⟩
  | vec _ => simp [argToBitsI] at hd

theorem fallsTo_setcc (s : MachineData) (cc : CondCode) (rd : Reg64) :
    Directive.FallsTo (ins8 (.setcc cc (.reg (b8 rd)))) s
      (· = { s with regs := (s.regs.set64 rd
        ((s.regs.get64 rd).replaceLow (BitVec.ofNat 8 (cc.interp s.status).toNat))) }) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, Reg64s.set]
  exact hk _ rfl

theorem wp_setccMove [Host] {E : Int64 → MachineData → Prop} (s : MachineData)
    (rd : Reg64) (cc : CondCode) :
    _root_.Program.wp (setccMove rd cc)
      (· = { s with regs := s.regs.set64 rd (BitVec.ofNat 64 (cc.interp s.status).toNat) })
      E s := by
  simp only [setccMove, setccMoveIns, emitClean_cons, emitClean_nil]
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_setcc s cc rd)) ?_
  rintro s1 rfl
  refine _root_.Program.wp_singleton ?_
  intro k _
  simp only [t_step_simp]
  rw [Reg64s.get64_set64_same, replaceLow_setWidth_le (by decide), BitVec.zeroExtend_eq_setWidth,
    Reg64s.set64_set64_same]
  have h64 : (((BitVec.ofNat 8 (cc.interp s.status).toNat).setWidth 32).setWidth 64) =
      BitVec.ofNat 64 (cc.interp s.status).toNat := by
    cases cc.interp s.status <;> rfl
  rw [h64]
  exact Or.inl ⟨trivial, rfl⟩

theorem fallsTo_boolArgTo8 (s : MachineData) (rd : Reg64)
    {pa : PArg Reg64 RegMm CondCode .bool} {b : Bool} {dir : Instr}
    (hd : boolArgTo8I rd pa = some dir) (hpa : x64Mach.PArgHolds s .bool pa b) :
    Directive.FallsTo (.instr dir) s (fun s' =>
      ∃ rv, rv.setWidth 8 = BitVec.ofNat 8 b.toNat ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  cases pa with
  | gpr rs =>
    simp only [boolArgTo8I, Option.some.injEq] at hd; subst hd
    have hrs : (s.regs.get64 rs).setWidth 8 = BitVec.ofNat 8 b.toNat := hpa
    intro _ _ _ _ _ hk
    simp only [t_step_simp, hrs, Reg64s.set]
    exact hk _ ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  | imm b0 =>
    simp only [boolArgTo8I, Option.some.injEq] at hd; subst hd
    simp only [Machine.PArgHolds] at hpa; subst hpa
    intro _ _ _ _ _ hk
    refine fallsTo_moviD s rd (BitVec.ofNat 64 b0.toNat) _ _ _ _ ?_
    rintro s' rfl
    exact hk _ ⟨BitVec.ofNat 64 b0.toNat, by cases b0 <;> rfl, rfl⟩
  | flag cc =>
    simp only [boolArgTo8I, Option.some.injEq] at hd; subst hd
    have hcc : cc.interp s.status = b := hpa
    intro _ _ _ _ _ hk
    refine fallsTo_setcc s cc rd _ _ _ _ ?_
    rintro s' rfl
    rw [hcc]
    exact hk _ ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  | vec _ => simp [boolArgTo8I] at hd

theorem fallsTo_clearFlags (s : MachineData) :
    Directive.FallsTo (ins32 (.xor (.reg (d .r10)) (.reg (d .r10)))) s (fun s' =>
      ∃ status, s' = { s with regs := s.regs.set64 .r10 0#64, status } ∧
        status.cf = false ∧ status.of = false) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, StatusFlags.from_result, Effects.All]
  intro af
  have hzero : ((s.regs.get64 .r10).setWidth 32 ^^^ (s.regs.get64 .r10).setWidth 32) = 0#32 := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
  rw [hzero, BitVec.zeroExtend_eq_setWidth]
  exact hk _ ⟨_, rfl, rfl, rfl⟩

theorem fallsTo_testb_self (s : MachineData) (r : Reg64) {b : Bool}
    (hb : GprHolds (s.regs.get64 r) .bool b) :
    Directive.FallsTo (ins8 (.test (.reg (b8 r)) (.reg (b8 r)))) s (fun s' =>
      ∃ status, s' = { s with status } ∧ CondCode.nz.interp status = b) := by
  intro _ _ _ _ _ hk
  have hr8 : (s.regs.get64 r).setWidth 8 = BitVec.ofNat 8 b.toNat := hb
  simp only [t_step_simp, hr8, StatusFlags.from_result, Effects.All]
  intro af
  refine hk _ ⟨_, rfl, ?_⟩
  cases b <;> rfl

theorem wp_addrToExpr [Host] {E : Int64 → MachineData → Prop} (s s₀ : MachineData)
    (a : AddrArg Reg64) (ha : ∀ r ∈ a.regs, r ∉ x64Scratch)
    (hr : ∀ r ∈ a.regs, s.regs.get64 r = s₀.regs.get64 r) :
    _root_.Program.wp (addrToExpr a).1 (fun s' =>
      s'.regs.get64 .r11 = s.regs.get64 .r11 ∧
      (∀ r, r ≠ .r10 → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
      (∀ (regs' : Reg64s), (∀ r ∈ .r10 :: a.regs, regs'.get64 r = s'.regs.get64 r) →
        ∀ [Labels] (p : Std.Rco Int64),
          (@AddrExpr.interp _ ⟨.W64⟩ (addrToExpr a).2.1 regs' p).zeroExtend 64 =
            a.eval (s₀.regs.get64)) ∧
      x64Mach.UpdFlags x64CondReads s s' (addrToExpr a).2.2) E s := by
  cases a with
  | baseDisp r off =>
    have hnr := ne_of_not_mem_x64Scratch (ha r (by simp [AddrArg.regs]))
    have hr' : s.regs.get64 r = s₀.regs.get64 r := hr r (by simp [AddrArg.regs])
    simp only [addrToExpr, addrToExprIns]
    split
    · rename_i h0
      have hoff : off = 0 := beq_iff_eq.mp h0
      refine _root_.Program.wp_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, ?_, updFlags_of_status_eq rfl _⟩
      intro regs' hregs _ p
      have hrr : regs'.get64 r = s.regs.get64 r := hregs r (by simp [AddrArg.regs])
      rw [atReg_interp, hrr, hr', hoff]
      simp [AddrArg.eval]
    · split
      · refine _root_.Program.wp_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, ?_, updFlags_of_status_eq rfl _⟩
        intro regs' hregs _ p
        have hrr : regs'.get64 r = s.regs.get64 r := hregs r (by simp [AddrArg.regs])
        rw [AddrExpr.interp_base_disp, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq, hrr, hr']
        rfl
      · refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 off.toBitVec)) ?_
        rintro s1 rfl
        refine _root_.Program.wp_singleton fun k _ => ?_
        have hs1r : (s.regs.set64 .r10 off.toBitVec).get64 r = s.regs.get64 r :=
          Reg64s.get64_set64_of_ne _ .r10 r _ hnr.1.symm
        simp only [t_step_simp, Reg64s.get64_set64_same, hs1r, hr']
        refine Or.inl ⟨trivial, ?_, ?_, trivial, trivial, ?_, updFlags_maskAll s _⟩
        · rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide),
              Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide)]
        · intro r' hne
          rw [Reg64s.get64_set64_of_ne _ .r10 r' _ hne.symm,
            Reg64s.get64_set64_of_ne _ .r10 r' _ hne.symm]
        · intro regs' hregs _ p
          exact hregs .r10 (by simp) ▸ (by rw [Reg64s.get64_set64_same]; rfl)
  | imm addr =>
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 addr)) ?_
    rintro s1 rfl
    refine _root_.Program.wp_nil ⟨Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide),
      fun r' hne => Reg64s.get64_set64_of_ne _ .r10 r' _ hne.symm,
      rfl, rfl, ?_, updFlags_of_status_eq rfl _⟩
    intro regs' hregs inst p
    letI := inst
    have hr10 : regs'.get64 .r10 = addr := by
      rw [hregs .r10 (by simp), Reg64s.get64_set64_same]
    exact (atReg_interp regs' .r10 p).trans hr10

/-! ## 5. Non-`op` `GprTarget` Specifications -/

theorem x64Gpr_negCond_reads (cc : CondCode) :
    x64Gpr.condReads (x64Gpr.negCond cc) = x64Gpr.condReads cc :=
  x64NegCond_reads cc

theorem x64Gpr_negCond_eval (s : MachineData) (cc : CondCode) :
    x64Mach.evalCond s (x64Gpr.negCond cc) = !x64Mach.evalCond s cc :=
  x64NegCond_interp cc s.status

theorem x64Gpr_clearFlags_spec {h : Host} {k : Nat} {s : MachineData}
    {post : MachineState → Prop} :
    x64Mach.FallsTo x64Gpr.condReads h k x64Gpr.clearFlags x64Scratch [] FlagMask.all s
      (fun s' => (∀ cc ∈ x64Gpr.zeroFlags, x64Mach.evalCond s' cc = false) ∧ s'.dmem = s.dmem)
      post := by
  refine dir_to_x64FallsTo (fallsTo_clearFlags s) ?_
  rintro s' ⟨st, rfl, hcf, hof⟩
  refine ⟨⟨?_, rfl⟩, x64_frame_of_eq ?_ rfl (updFlags_maskAll _ _)⟩
  · intro cc hc
    simp only [x64Gpr, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [CondCode.interp, hcf, hof]
  · intro r hr
    exact Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm

theorem x64Gpr_mov_spec {h : Host} {k : Nat} {rd rs : Reg64} {s : MachineData}
    {post : MachineState → Prop} :
    x64Mach.FallsTo x64Gpr.condReads h k (x64Gpr.mov rd rs) [rd] [] FlagMask.none s
      (fun s' => s'.regs.get64 rd = s.regs.get64 rs ∧ s'.dmem = s.dmem) post := by
  refine dir_to_x64FallsTo (fallsTo_movD s rd rs) ?_
  rintro s' rfl
  refine ⟨⟨Reg64s.get64_set64_same .., rfl⟩, x64_frame_of_eq ?_ rfl (updFlags_of_status_eq rfl _)⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr)

theorem x64Gpr_movi_spec {h : Host} {k : Nat} {rd : Reg64} {c0 : BitVec 64} {s : MachineData}
    {post : MachineState → Prop} :
    x64Mach.FallsTo x64Gpr.condReads h k (x64Gpr.movi rd c0) (rd :: x64Scratch) [] FlagMask.none s
      (fun s' => s'.regs.get64 rd = c0 ∧ s'.dmem = s.dmem) post := by
  refine dir_to_x64FallsTo (fallsTo_moviD s rd c0) ?_
  rintro s' rfl
  refine ⟨⟨Reg64s.get64_set64_same .., rfl⟩, x64_frame_of_eq ?_ rfl (updFlags_of_status_eq rfl _)⟩
  intro r hr
  simp only [List.mem_cons, not_or] at hr
  exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)

theorem x64Gpr_setcc_spec {h : Host} {k : Nat} {rd : Reg64} {cc : CondCode} {s : MachineData}
    {post : MachineState → Prop} (_hrd : rd ∉ x64Scratch) :
    x64Mach.FallsTo x64Gpr.condReads h k (x64Gpr.setcc rd cc) (rd :: x64Scratch) [] FlagMask.none s
      (fun s' => GprHolds (s'.regs.get64 rd) .bool (x64Mach.evalCond s cc) ∧ s'.dmem = s.dmem)
      post := by
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  refine Program.wp.mono (wp_setccMove s rd cc) ?_
  rintro s' rfl
  refine ⟨⟨?_, rfl⟩, x64_frame_of_eq ?_ rfl (updFlags_of_status_eq rfl _)⟩
  · simp only [GprHolds, Reg64s.get64_set64_same]
    cases cc.interp s.status <;> rfl
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)

theorem x64Gpr_jmp_spec {h : Host} {k j : Nat} {l : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (x64Gpr.jmp l).IsInfixAt (x64Mach.prog h) k)
    (hj : x64Mach.labelAddr h l = x64Mach.addrOf h j)
    (hk : ∀ s', x64Mach.Frame x64Gpr.condReads s s' x64Scratch [] FlagMask.none →
      x64Mach.mem s' = x64Mach.mem s → x64Mach.Run h j s' post) :
    x64Mach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp]
  have hlab : Labels.label l = Host.addrOf j := hj
  rw [hlab, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact hk s (Machine.Frame.refl _ _ _ _ _) rfl

theorem x64Gpr_jcc_spec {h : Host} {k j : Nat} {cc : CondCode} {l : Sym} {s : MachineData}
    {post : MachineState → Prop}
    (hc : (x64Gpr.jcc cc l).IsInfixAt (x64Mach.prog h) k)
    (hj : x64Mach.labelAddr h l = x64Mach.addrOf h j)
    (hk : ∀ s', x64Mach.Frame x64Gpr.condReads s s' x64Scratch [] FlagMask.none →
      x64Mach.mem s' = x64Mach.mem s →
      (x64Mach.evalCond s cc = true → x64Mach.Run h j s' post) ∧
      (x64Mach.evalCond s cc = false → x64Mach.Run h (k + (x64Gpr.jcc cc l).length) s' post)) :
    x64Mach.Run h k s post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp]
  have hlab : Labels.label l = Host.addrOf j := hj
  have hrun := hk s (Machine.Frame.refl _ _ _ _ _) rfl
  cases hcc : cc.interp s.status with
  | true =>
    simp only [↓reduceIte, Effects.All, hlab]
    exact hrun.1 hcc
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    exact hrun.2 hcc

theorem x64Gpr_jnzGpr_spec {h : Host} {k j : Nat} {r : Reg64} {l : Sym} {b : Bool}
    {s : MachineData} {post : MachineState → Prop}
    (hc : (x64Gpr.jnzGpr r l).1.IsInfixAt (x64Mach.prog h) k)
    (hj : x64Mach.labelAddr h l = x64Mach.addrOf h j)
    (_hr : r ∉ x64Scratch)
    (hb : GprHolds (x64Mach.getGpr s r) .bool b)
    (hk : ∀ s', x64Mach.Frame x64Gpr.condReads s s' x64Scratch [] (x64Gpr.jnzGpr r l).2 →
      x64Mach.mem s' = x64Mach.mem s →
      (b = true → x64Mach.Run h j s' post) ∧
      (b = false → x64Mach.Run h (k + (x64Gpr.jnzGpr r l).1.length) s' post)) :
    x64Mach.Run h k s post := by
  letI := h
  have hw0 : _root_.Program.wp [ins8 (.test (.reg (b8 r)) (.reg (b8 r)))]
      (fun s' => ∃ status, s' = { s with status } ∧ CondCode.nz.interp status = b)
      (fun _ _ => False) s :=
    Directive.FallsTo.wp (fallsTo_testb_self s r hb)
  refine Program.wp.eventually hw0 (List.isInfixAt_singleton.mpr hc.cons.1) ?_ (fun _ _ hf => hf.elim)
  rintro s1 ⟨st, rfl, hnz⟩
  refine Host.eventually_of_interp_cps hc.cons.2.cons.1 ?_
  simp only [t_step_simp]
  have hfr : x64Mach.Frame x64Gpr.condReads s { s with status := st } x64Scratch [] maskAll :=
    x64_frame_of_eq (fun _ _ => rfl) rfl (updFlags_maskAll s _)
  have hrun := hk { s with status := st } hfr rfl
  have hlab : Labels.label l = Host.addrOf j := hj
  cases b with
  | true =>
    simp only [hnz, ↓reduceIte, Effects.All, hlab]
    exact hrun.1 rfl
  | false =>
    simp only [hnz, Bool.false_eq_true, ↓reduceIte, Effects.All]
    exact hrun.2 rfl

private def loadTailDir (t : Ty) (rd : Reg64) (addr : AddrExpr) (dir : Directive) : Prop :=
  match t with
  | .bool | .bits 8 => dir = ins32 (.movzx (.reg (d rd)) (.mem addr : RegOrMem .W8))
  | .bits 16 => dir = ins32 (.movzx (.reg (d rd)) (.mem addr : RegOrMem .W16))
  | .bits 32 => dir = ins32 (.mov (.reg (d rd)) (.mem addr))
  | .bits 64 => dir = ins (.mov (.reg (q rd)) (.mem addr))
  | _ => False

private theorem wp_load_tail [Host] {E : Int64 → MachineData → Prop} (s : MachineData) (t : Ty)
    (rd : Reg64) (addr : AddrExpr) (addrVal : BitVec 64) (v : Val t)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem t addrVal = some v)
    (dir : Directive) (hd : loadTailDir t rd addr dir) :
    _root_.Program.wp [dir] (fun s' =>
      GprHolds (s'.regs.get64 rd) t v ∧
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧ s'.status = s.status) E s := by
  cases t with
  | bool =>
    dsimp only [loadTailDir] at hd; subst hd
    obtain ⟨i, hi, h01, rfl⟩ := loadVal_bool_spec hlv
    refine _root_.Program.wp_singleton fun k _ => ?_
    simp only [t_step_simp, MachineData.load, Effects.All_require_read_access, Width.bytes,
      haddr, hi]
    refine Or.inl ⟨trivial, ⟨?_, fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
      trivial, trivial, trivial⟩⟩
    simp only [GprHolds, Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth]
    rcases h01 with rfl | rfl <;> rfl
  | bits n =>
    rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64)) with
      rfl | rfl | rfl | rfl | hne
    · dsimp only [loadTailDir] at hd; subst hd
      obtain ⟨i, hi, rfl⟩ := loadVal_bits_spec (Or.inl rfl) hlv
      refine _root_.Program.wp_singleton fun k _ => ?_
      simp only [t_step_simp, MachineData.load, Effects.All_require_read_access, Width.bytes,
        haddr, hi]
      refine Or.inl ⟨trivial, ⟨(GprHolds.bits_iff .W8 _ _).2 ?_,
        fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, trivial, trivial, trivial⟩⟩
      simp only [Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth, Width.bits]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_eq]
    · dsimp only [loadTailDir] at hd; subst hd
      obtain ⟨i, hi, rfl⟩ := loadVal_bits_spec (Or.inr (Or.inl rfl)) hlv
      refine _root_.Program.wp_singleton fun k _ => ?_
      simp only [t_step_simp, MachineData.load, Effects.All_require_read_access, Width.bytes,
        haddr, hi]
      refine Or.inl ⟨trivial, ⟨(GprHolds.bits_iff .W16 _ _).2 ?_,
        fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, trivial, trivial, trivial⟩⟩
      simp only [Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth, Width.bits]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_eq]
    · dsimp only [loadTailDir] at hd; subst hd
      obtain ⟨i, hi, rfl⟩ := loadVal_bits_spec (Or.inr (Or.inr (Or.inl rfl))) hlv
      refine _root_.Program.wp_singleton fun k _ => ?_
      simp only [t_step_simp, MachineData.load, Effects.All_require_read_access, Width.bytes,
        haddr, hi]
      refine Or.inl ⟨trivial, ⟨(GprHolds.bits_iff .W32 _ _).2 ?_,
        fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, trivial, trivial, trivial⟩⟩
      simp only [Reg64s.get64_set64_same, BitVec.zeroExtend_eq_setWidth, Width.bits]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    · dsimp only [loadTailDir] at hd; subst hd
      obtain ⟨i, hi, rfl⟩ := loadVal_bits_spec (Or.inr (Or.inr (Or.inr rfl))) hlv
      refine _root_.Program.wp_singleton fun k _ => ?_
      simp only [t_step_simp, MachineData.load, Effects.All_require_read_access, Width.bytes,
        haddr, hi]
      refine Or.inl ⟨trivial, ⟨(GprHolds.bits_iff .W64 _ _).2 ?_,
        fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, trivial, trivial, trivial⟩⟩
      simp only [Reg64s.get64_set64_same, Width.bits, BitVec.setWidth_eq]
    · simp [loadTailDir, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2] at hd
  | float _ | pair _ _ => cases hd

theorem x64Gpr_load_spec {h : Host} {k : Nat} {t : Ty} {rd : Reg64} {a : AddrArg Reg64}
    {c : List Directive} {clob : FlagMask} {v : Val t} {s : MachineData}
    {post : MachineState → Prop}
    (hl0 : x64Gpr.load t rd a = some (c, clob))
    (hrd : rd ∉ x64Scratch) (ha : ∀ r ∈ a.regs, r ∉ x64Scratch)
    (hlv : loadVal s.dmem t (a.eval s.regs.get64) = some v) :
    x64Mach.FallsTo x64Gpr.condReads h k c (rd :: x64Scratch) [] clob s
      (fun s' => GprHolds (s'.regs.get64 rd) t v ∧ s'.dmem = s.dmem) post := by
  have _ := hrd
  dsimp only [x64Gpr, x64Load] at hl0
  obtain ⟨ci, hl, rfl⟩ := emitCleanPair_eq_some.mp hl0
  have htail : ∃ d_last, emitClean ci = (addrToExpr a).1 ++ [d_last] ∧
      clob = (addrToExpr a).2.2 ∧ loadTailDir t rd (addrToExpr a).2.1 d_last := by
    cases t with
    | bool =>
      simp only [x64LoadIns, Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      exact ⟨_, by simp [addrToExpr, emitClean_append, emitClean_cons, emitClean_nil], rfl, rfl⟩
    | bits n =>
      rcases (by omega : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64)) with
        rfl | rfl | rfl | rfl | hne <;>
        simp only [x64LoadIns, Option.some.injEq, Prod.mk.injEq] at hl
      · rcases hl with ⟨rfl, rfl⟩
        exact ⟨_, by simp [addrToExpr, emitClean_append, emitClean_cons, emitClean_nil], rfl, rfl⟩
      · rcases hl with ⟨rfl, rfl⟩
        exact ⟨_, by simp [addrToExpr, emitClean_append, emitClean_cons, emitClean_nil], rfl, rfl⟩
      · rcases hl with ⟨rfl, rfl⟩
        exact ⟨_, by simp [addrToExpr, emitClean_append, emitClean_cons, emitClean_nil], rfl, rfl⟩
      · rcases hl with ⟨rfl, rfl⟩
        exact ⟨_, by simp [addrToExpr, emitClean_append, emitClean_cons, emitClean_nil], rfl, rfl⟩
      · simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2] at hl
    | float _ | pair _ _ => simp [x64LoadIns] at hl
  obtain ⟨d_last, hci_eq, rfl, hdl⟩ := htail
  rw [hci_eq]
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
  rintro s1 ⟨_, hr1, hm1, hz1, haddr1, hf1⟩
  refine Program.wp.mono (wp_load_tail s1 t rd _ (a.eval s.regs.get64) v
    (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv) d_last hdl) ?_
  rintro s2 ⟨hhold, hr2, hm2, hz2, hst2⟩
  refine ⟨⟨hhold, hm2.trans hm1⟩, x64_frame_of_eq ?_ (hz2.trans hz1) ?_⟩
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    rw [hr2 r hr.1, hr1 r hr.2.1]
  · intro cc hdisj
    simp only [hst2]
    exact hf1 cc hdisj

theorem x64Gpr_store_spec {h : Host} {k : Nat} {t : Ty} {pa : PArg Reg64 RegMm CondCode t}
    {a : AddrArg Reg64} {c : List Directive} {clob : FlagMask} {v : Val t} {s : MachineData}
    {post : MachineState → Prop}
    (hs0 : x64Gpr.store t pa a = some (c, clob))
    (hregs : ∀ r ∈ pa.gprs ++ a.regs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s t pa v)
    (hok : storeOk s.dmem t (a.eval s.regs.get64)) :
    x64Mach.FallsTo x64Gpr.condReads h k c x64Scratch [] clob s
      (fun s' => s'.dmem = storeMem s.dmem t (a.eval s.regs.get64) v) post := by
  have ha : ∀ r ∈ a.regs, r ∉ x64Scratch := fun r hr => hregs r (List.mem_append_right _ hr)
  obtain ⟨iload, hload⟩ := hok
  dsimp only [x64Gpr, x64Store] at hs0
  obtain ⟨ci, hs, rfl⟩ := emitCleanPair_eq_some.mp hs0
  cases t with
  | bool =>
    have hload1 : s.dmem.loadInt (a.eval s.regs.get64) 1 = some iload := hload
    rw [storeMem_bool_eq]
    cases pa with
    | gpr rx =>
      simp only [x64StoreIns, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      simp only [emitClean_append, emitClean_cons, emitClean_nil]
      have hrx : rx ≠ .r10 ∧ rx ≠ .r11 :=
        ne_of_not_mem_x64Scratch (hregs rx (by simp [PArg.gprs]))
      have hrx8 : (s.regs.get64 rx).setWidth 8 = BitVec.ofNat 8 v.toNat := hpa
      refine x64_fallsTo_of_wp fun {_} _ => ?_
      refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
      rintro s1 ⟨_, hr1, hm1, hz1, haddr1, hf1⟩
      dsimp only [addrToExpr] at haddr1
      refine _root_.Program.wp_singleton fun k' _ => ?_
      have hs1x : (s1.regs.get64 rx).setWidth 8 = BitVec.ofNat 8 v.toNat := by
        rw [hr1 rx hrx.1, hrx8]
      simp only [t_step_simp, MachineData.store, Effects.All_require_write_access, Width.bytes,
        haddr1 s1.regs (fun _ _ => rfl), hm1, hload1, hs1x]
      exact Or.inl ⟨trivial, trivial, x64_frame_of_eq (fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1)
        hz1 hf1⟩
    | imm b0 =>
      simp only [x64StoreIns, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      rcases hpa with rfl
      simp only [emitClean_append, emitClean_cons, emitClean_nil]
      refine x64_fallsTo_of_wp fun {_} _ => ?_
      refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
      rintro s1 ⟨_, hr1, hm1, hz1, haddr1, hf1⟩
      dsimp only [addrToExpr] at haddr1
      refine _root_.Program.wp_singleton fun k' _ => ?_
      have htrunc : (Int64.ofNat b0.toNat).toBitVec.truncate 8 = BitVec.ofNat 8 b0.toNat := by
        cases b0 <;> rfl
      simp only [t_step_simp, ConstExpr.interp, MachineData.store, Effects.All_require_write_access,
        Width.bytes, haddr1 s1.regs (fun _ _ => rfl), hm1, hload1, htrunc]
      exact Or.inl ⟨trivial, trivial, x64_frame_of_eq (fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1)
        hz1 hf1⟩
    | flag cc =>
      simp only [x64StoreIns, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      simp only [emitClean_cons, emitClean_append, emitClean_nil]
      have hcc : cc.interp s.status = v := hpa
      refine x64_fallsTo_of_wp fun {_} _ => ?_
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_setcc s cc .r11)) ?_
      rintro s1 rfl
      have hr1a : ∀ w r, r ∈ a.regs → (s.regs.set64 .r11 w).get64 r = s.regs.get64 r := fun w r hr =>
        Reg64s.get64_set64_of_ne _ .r11 r _ (ne_of_not_mem_x64Scratch (ha r hr)).2.symm
      refine Program.wp.append (wp_addrToExpr _ s a ha (hr1a _)) ?_
      rintro s2 ⟨hr2_11, hr2, hm2, hz2, haddr2, hf2⟩
      dsimp only [addrToExpr] at haddr2
      refine _root_.Program.wp_singleton fun k' _ => ?_
      have hs2_11 : (s2.regs.get64 .r11).setWidth 8 = BitVec.ofNat 8 v.toNat := by
        rw [hr2_11, Reg64s.get64_set64_same, replaceLow_setWidth_le (by decide), hcc]
      simp only [t_step_simp, MachineData.store, Effects.All_require_write_access, Width.bytes,
        haddr2 s2.regs (fun _ _ => rfl), hm2, hload1, hs2_11]
      refine Or.inl ⟨trivial, trivial, x64_frame_of_eq ?_ hz2 hf2⟩
      intro r hr
      have hne := ne_of_not_mem_x64Scratch hr
      rw [hr2 r hne.1, Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
    | vec _ => simp [x64StoreIns] at hs
  | bits n =>
    simp only [x64StoreIns] at hs
    refine withWidth_elim hs fun w hn hw => ?_
    subst hn
    have hwn : w.bits = 8 ∨ w.bits = 16 ∨ w.bits = 32 ∨ w.bits = 64 := by
      cases w <;> simp [Width.bits]
    rw [storeMem_bits_eq s.dmem hwn]
    have hb : (Ty.bits w.bits).bytes = w.bytes := by cases w <;> decide
    have hwdiv : w.bits / 8 = w.bytes := by cases w <;> decide
    rw [hb] at hload
    rw [hwdiv]
    cases pa with
    | gpr rx =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩
      simp only [emitClean_append, emitClean_cons, emitClean_nil]
      have hrx : rx ≠ .r10 ∧ rx ≠ .r11 :=
        ne_of_not_mem_x64Scratch (hregs rx (by simp [PArg.gprs]))
      have hrxw : (s.regs.get64 rx).setWidth w.bits = v := (GprHolds.bits_iff w _ _).1 hpa
      refine x64_fallsTo_of_wp fun {_} _ => ?_
      refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
      rintro s1 ⟨_, hr1, hm1, hz1, haddr1, hf1⟩
      dsimp only [addrToExpr] at haddr1
      refine _root_.Program.wp_singleton fun k' _ => ?_
      have hs1x : (s1.regs.get64 rx).setWidth w.bits = v := by rw [hr1 rx hrx.1, hrxw]
      have haddr_eq := haddr1 s1.regs (fun _ _ => rfl)
      cases w <;>
        simp only [t_step_simp, MachineData.store, Effects.All_require_write_access,
          haddr_eq, hm1, hload, hs1x] <;>
        exact Or.inl ⟨trivial, trivial, x64_frame_of_eq
          (fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1) hz1 hf1⟩
    | imm c0 =>
      rcases hpa with rfl
      dsimp only at hw
      split at hw
      · simp only [Option.some.injEq, Prod.mk.injEq] at hw
        rcases hw with ⟨rfl, rfl⟩
        simp only [emitClean_append, emitClean_cons, emitClean_nil]
        refine x64_fallsTo_of_wp fun {_} _ => ?_
        refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
        rintro s1 ⟨_, hr1, hm1, hz1, haddr1, hf1⟩
        dsimp only [addrToExpr] at haddr1
        refine _root_.Program.wp_singleton fun k' _ => ?_
        have haddr_eq := haddr1 s1.regs (fun _ _ => rfl)
        have htr : (c0.signExtend 64).truncate w.bits = c0 :=
          truncate_signExtend_64 (width_bits_le_64 w) c0
        cases w <;>
          simp only [immBitsOp, t_step_simp, Int64.toBitVec_ofBitVec,
            htr, MachineData.store, Effects.All_require_write_access,
            haddr_eq, hm1, hload] <;>
          exact Or.inl ⟨trivial, trivial, x64_frame_of_eq
            (fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1) hz1 hf1⟩
      · rename_i hnofit
        have hw64 : w = .W64 := by
          cases w with
          | W8 | W16 | W32 => exact absurd rfl hnofit
          | W64 => rfl
        subst hw64
        simp only [Width.bits, BitVec.setWidth_eq, Option.some.injEq, Prod.mk.injEq] at hw
        rcases hw with ⟨rfl, rfl⟩
        simp only [emitClean_append, emitClean_cons, emitClean_nil]
        refine x64_fallsTo_of_wp fun {_} _ => ?_
        refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
        rintro s1 ⟨_, hr1, hm1, hz1, haddr1, hf1⟩
        dsimp only [addrToExpr] at haddr1
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s1 .r11 c0)) ?_
        rintro s2 rfl
        refine _root_.Program.wp_singleton fun k' _ => ?_
        have hregs_agree : ∀ r ∈ .r10 :: a.regs, (s1.regs.set64 .r11 c0).get64 r = s1.regs.get64 r := by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact Reg64s.get64_set64_of_ne _ .r11 .r10 _ (by decide)
          · exact Reg64s.get64_set64_of_ne _ .r11 r _ (ne_of_not_mem_x64Scratch (ha r hr)).2.symm
        have haddr_eq := haddr1 (s1.regs.set64 .r11 c0) hregs_agree
        simp only [t_step_simp, MachineData.store, Effects.All_require_write_access,
          haddr_eq, hm1, hload, Reg64s.get64_set64_same, Width.bits]
        refine Or.inl ⟨trivial, trivial, x64_frame_of_eq ?_ hz1 hf1⟩
        intro r hr
        have hne := ne_of_not_mem_x64Scratch hr
        rw [Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm, hr1 r hne.1]
    | vec _ => simp at hw
  | float _ | pair _ _ => simp [x64StoreIns] at hs

/-! ## 6. Shared `BEq`, `BitVec`, `bswap`, `atDisp`, and `OpPost` Combinators (`IselLemmas2`–`3`) -/

@[simp] theorem beq_reg64_iff (r1 r2 : Reg64) : (r1 == r2) = true ↔ r1 = r2 := by
  cases r1 <;> cases r2 <;> decide

@[simp] theorem bne_reg64_iff (r1 r2 : Reg64) : (r1 != r2) = true ↔ r1 ≠ r2 := by
  cases r1 <;> cases r2 <;> decide

@[simp] theorem beq_cond_iff (c1 c2 : CondCode) : (c1 == c2) = true ↔ c1 = c2 := by
  cases c1 <;> cases c2 <;> decide

@[simp] theorem beq_width_iff (w1 w2 : Width) : (w1 == w2) = true ↔ w1 = w2 := by
  cases w1 <;> cases w2 <;> decide

theorem setWidth_mul_le {m n : Nat} (hmn : m ≤ n) (x y : BitVec n) :
    (x * y).setWidth m = x.setWidth m * y.setWidth m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul]
  have hdiv : 2 ^ m ∣ 2 ^ n := Nat.pow_dvd_pow 2 hmn
  rw [Nat.mod_mod_of_dvd _ hdiv, Nat.mul_mod]

theorem setWidth_add_le {m n : Nat} (hmn : m ≤ n) (x y : BitVec n) :
    (x + y).setWidth m = x.setWidth m + y.setWidth m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  have hdiv : 2 ^ m ∣ 2 ^ n := Nat.pow_dvd_pow 2 hmn
  rw [Nat.mod_mod_of_dvd _ hdiv, Nat.add_mod]

private theorem bv_sub_eq_of_add_eq {m : Nat} {x y z : BitVec m} (h : y + x = z) :
    y = z - x := by
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_sub] at h1 ⊢
  have hy := y.isLt; have hx := x.isLt; have hz := z.isLt
  rcases Nat.lt_or_ge (y.toNat + x.toNat) (2 ^ m) with hlt | hge
  · have hzx : z.toNat = y.toNat + x.toNat := by rw [← h1, Nat.mod_eq_of_lt hlt]
    have hadd : 2 ^ m - x.toNat + z.toNat = 2 ^ m + y.toNat := by omega
    rw [hadd, Nat.add_mod_left, Nat.mod_eq_of_lt hy]
  · have hmod : (y.toNat + x.toNat) % 2 ^ m = y.toNat + x.toNat - 2 ^ m := by
      have heq : y.toNat + x.toNat = 2 ^ m + (y.toNat + x.toNat - 2 ^ m) := by omega
      calc (y.toNat + x.toNat) % 2 ^ m
          = (2 ^ m + (y.toNat + x.toNat - 2 ^ m)) % 2 ^ m := congrArg (· % 2 ^ m) heq
        _ = (y.toNat + x.toNat - 2 ^ m) % 2 ^ m := Nat.add_mod_left ..
        _ = y.toNat + x.toNat - 2 ^ m := Nat.mod_eq_of_lt (by omega)
    have hzx : z.toNat = y.toNat + x.toNat - 2 ^ m := by rw [← h1, hmod]
    have hadd : 2 ^ m - x.toNat + z.toNat = y.toNat := by omega
    rw [hadd, Nat.mod_eq_of_lt hy]

theorem setWidth_sub_le {m n : Nat} (hmn : m ≤ n) (x y : BitVec n) :
    (x - y).setWidth m = x.setWidth m - y.setWidth m := by
  apply bv_sub_eq_of_add_eq
  rw [← setWidth_add_le hmn, BitVec.sub_add_cancel]

theorem setWidth_neg_le {m n : Nat} (hmn : m ≤ n) (x : BitVec n) :
    (-x).setWidth m = -(x.setWidth m) := by
  have hz : ∀ {k : Nat} (u : BitVec k), 0#k - u = -u := fun {k} u => by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_neg]
  rw [← hz x, setWidth_sub_le hmn, BitVec.setWidth_zero, hz]

theorem setWidth_signExtend_of_le {m n k : Nat} (_hmn : m ≤ n) (hnk : n ≤ k) (v : BitVec m) :
    (v.signExtend k).setWidth n = v.signExtend n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hik : (i : Nat) < k := Nat.lt_of_lt_of_le hi hnk
  simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
    BitVec.getLsbD_signExtend, decide_eq_true hik]

theorem bswap_go_getLsbD {w : Nat} (x : BitVec w) :
    ∀ (m i : Nat), i < 8 * m →
      (bswapBits.go x m).getLsbD i = x.getLsbD (8 * (m - 1 - i / 8) + i % 8) := by
  intro m
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    have heq : bswapBits.go x (m + 1) =
        (bswapBits.go x m ++ x.extractLsb' (8 * m) 8).cast (by omega) := rfl
    rw [heq, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hlt : i < 8
    · have hdiv : i / 8 = 0 := Nat.div_eq_of_lt hlt
      have hmod : i % 8 = i := Nat.mod_eq_of_lt hlt
      simp [hlt, hdiv, hmod]
    · have hj : i - 8 < 8 * m := by omega
      simp only [hlt, ↓reduceIte, ih (i - 8) hj]
      have h1 : m + 1 - 1 - i / 8 = m - 1 - (i - 8) / 8 := by omega
      have h2 : i % 8 = (i - 8) % 8 := by omega
      rw [h1, h2]

theorem bswapBits_16 (x : BitVec 16) : x.rotateLeft 8 = bswapBits x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [bswapBits, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
    bswap_go_getLsbD x 2 i hi, BitVec.getLsbD_rotateLeft]
  rcases Nat.lt_or_ge i 8 with h1 | h1
  · have hge : ¬ 8 ≤ i := by omega
    have hq : i / 8 = 0 := by omega
    have hr : i % 8 = i := by omega
    simp [hge, hq, hr]
  · have hlt : ¬ i < 8 := by omega
    have hq : i / 8 = 1 := by omega
    have hr : i % 8 = i - 8 := by omega
    simp [hlt, hq, hr]

private theorem getLsbD_append_lt {m n : Nat} (a : BitVec m) (b : BitVec n) {i : Nat} (hi : i < n) :
    (a ++ b).getLsbD i = b.getLsbD i := by
  simp [BitVec.getLsbD_append, hi]

private theorem getLsbD_append_ge {m n : Nat} (a : BitVec m) (b : BitVec n) {i : Nat} (hi : n ≤ i) :
    (a ++ b).getLsbD i = a.getLsbD (i - n) := by
  simp [BitVec.getLsbD_append, show ¬ i < n by omega]

private theorem getLsbD_take_lt {n k i : Nat} (x : BitVec n) (hi : i < k) :
    (x.take k).getLsbD i = x.getLsbD i := by
  simp [BitVec.take, hi]

private theorem getLsbD_drop_lt {n k i : Nat} (x : BitVec n) (hi : i < n - k) :
    (x.drop k).getLsbD i = x.getLsbD (k + i) := by
  simp [BitVec.drop, hi]

private theorem getLsbD_extract_lt {n k len i : Nat} (x : BitVec n) (hi : i < len) :
    (x.extractLsb' k len).getLsbD i = x.getLsbD (k + i) := by
  simp [hi]

theorem bswapBits_32 (x : BitVec 32) :
    ((x.take 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.drop 24).setWidth 32) =
      bswapBits x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bswapBits, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, bswap_go_getLsbD x 4 i hi]
  rcases Nat.lt_or_ge i 8 with h0 | h0
  · rw [getLsbD_append_lt _ _ h0, getLsbD_drop_lt _ (by omega)]; congr 1; omega
  · rw [getLsbD_append_ge _ _ (by omega)]
    rcases Nat.lt_or_ge i 16 with h1 | h1
    · rw [getLsbD_append_lt _ _ (by omega), getLsbD_extract_lt _ (by omega)]; congr 1; omega
    · rw [getLsbD_append_ge _ _ (by omega)]
      rcases Nat.lt_or_ge i 24 with h2 | h2
      · rw [getLsbD_append_lt _ _ (by omega), getLsbD_extract_lt _ (by omega)]; congr 1; omega
      · rw [getLsbD_append_ge _ _ (by omega), getLsbD_take_lt _ (by omega)]; congr 1; omega

theorem bswapBits_64 (x : BitVec 64) :
    ((x.take 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
      x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.drop 56).setWidth 64) =
      bswapBits x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bswapBits, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, bswap_go_getLsbD x 8 i hi]
  rcases Nat.lt_or_ge i 8 with h0 | h0
  · rw [getLsbD_append_lt _ _ h0, getLsbD_drop_lt _ (by omega)]; congr 1; omega
  · rw [getLsbD_append_ge _ _ (by omega)]
    rcases Nat.lt_or_ge i 16 with h1 | h1
    · rw [getLsbD_append_lt _ _ (by omega), getLsbD_extract_lt _ (by omega)]; congr 1; omega
    · rw [getLsbD_append_ge _ _ (by omega)]
      rcases Nat.lt_or_ge i 24 with h2 | h2
      · rw [getLsbD_append_lt _ _ (by omega), getLsbD_extract_lt _ (by omega)]; congr 1; omega
      · rw [getLsbD_append_ge _ _ (by omega)]
        rcases Nat.lt_or_ge i 32 with h3 | h3
        · rw [getLsbD_append_lt _ _ (by omega), getLsbD_extract_lt _ (by omega)]; congr 1; omega
        · rw [getLsbD_append_ge _ _ (by omega)]
          rcases Nat.lt_or_ge i 40 with h4 | h4
          · rw [getLsbD_append_lt _ _ (by omega), getLsbD_extract_lt _ (by omega)]; congr 1; omega
          · rw [getLsbD_append_ge _ _ (by omega)]
            rcases Nat.lt_or_ge i 48 with h5 | h5
            · rw [getLsbD_append_lt _ _ (by omega), getLsbD_extract_lt _ (by omega)]; congr 1; omega
            · rw [getLsbD_append_ge _ _ (by omega)]
              rcases Nat.lt_or_ge i 56 with h6 | h6
              · rw [getLsbD_append_lt _ _ (by omega), getLsbD_extract_lt _ (by omega)]; congr 1; omega
              · rw [getLsbD_append_ge _ _ (by omega), getLsbD_take_lt _ (by omega)]; congr 1; omega

theorem atDisp_interp [Labels] (regs : Reg64s) (rb : Reg64) (off : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ (atDisp rb off) regs p).zeroExtend 64 =
      regs.get64 rb + off.toBitVec := by
  rw [AddrExpr.interp_base_disp]
  simp [BitVec.setWidth_eq]

/-- Standard single-GPR fallthrough postcondition for `x64Op`. -/
abbrev OpPost1 (t : Ty) (rd : Reg64) (v : Val t) (clob : FlagMask) (s s' : MachineData) : Prop :=
  GprHolds (s'.regs.get64 rd) t v ∧ s'.dmem = s.dmem ∧
    x64Mach.Frame x64CondReads s s' (rd :: x64Scratch) [] clob

theorem opPost1_fallsTo {t : Ty} {rd : Reg64} {c : List Directive} {clob : FlagMask}
    {s : MachineData} {v : Val t} {P : Tup Val [t] → Prop} (hp : P (v, ()))
    (hwp : ∀ [Host] (E : Int64 → MachineData → Prop),
      _root_.Program.wp c (OpPost1 t rd v clob s) E s)
    {h : Host} {k : Nat} {post : MachineState → Prop} :
    x64Mach.FallsTo x64Gpr.condReads h k c
      (@tupDstGprs Reg64 RegMm CondCode [t] (.gpr rd, ()) ++ x64Scratch)
      [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') (.gpr rd, ()) rvs) ∧
        x64Mach.mem s' = x64Mach.mem s)
      post := by
  refine x64_fallsTo_of_wp fun {_} _ => Program.wp.mono (hwp _) ?_
  rintro s' ⟨hhold, hmem, hfr⟩
  exact ⟨⟨⟨(v, ()), hp, TRel.cons hhold .nil⟩, hmem⟩, hfr⟩

/-- Single-destination (`PDst` `.gpr` or `.flag`) fallthrough postcondition for `x64Op`. -/
abbrev OpPostDst1 (t : Ty) (pd : PDst Reg64 RegMm CondCode t) (v : Val t) (clob : FlagMask)
    (s s' : MachineData) : Prop :=
  x64Mach.PDstHolds s' t pd v ∧ s'.dmem = s.dmem ∧
    x64Mach.Frame x64CondReads s s' (@tupDstGprs Reg64 RegMm CondCode [t] (pd, ()) ++ x64Scratch) [] clob

theorem opPostDst1_fallsTo {t : Ty} {pd : PDst Reg64 RegMm CondCode t} {c : List Directive}
    {clob : FlagMask} {s : MachineData} {v : Val t} {P : Tup Val [t] → Prop} (hp : P (v, ()))
    (hwp : ∀ [Host] (E : Int64 → MachineData → Prop),
      _root_.Program.wp c (OpPostDst1 t pd v clob s) E s)
    {h : Host} {k : Nat} {post : MachineState → Prop} :
    x64Mach.FallsTo x64Gpr.condReads h k c
      (@tupDstGprs Reg64 RegMm CondCode [t] (pd, ()) ++ x64Scratch)
      [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') (pd, ()) rvs) ∧
        x64Mach.mem s' = x64Mach.mem s)
      post := by
  refine x64_fallsTo_of_wp fun {_} _ => Program.wp.mono (hwp _) ?_
  rintro s' ⟨hhold, hmem, hfr⟩
  exact ⟨⟨⟨(v, ()), hp, TRel.cons hhold .nil⟩, hmem⟩, hfr⟩

theorem OpPost1.of_set64_bits {w : Width} {rd : Reg64} {rv : BitVec 64} {st : StatusFlags}
    {clob : FlagMask} {s : MachineData} {v : BitVec w.bits}
    (hrv : rv.setWidth w.bits = v)
    (hup : x64Mach.UpdFlags x64CondReads s { s with regs := s.regs.set64 rd rv, status := st } clob) :
    OpPost1 (.bits w.bits) rd v clob s { s with regs := s.regs.set64 rd rv, status := st } := by
  refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv]), rfl,
    x64_frame_of_eq ?_ rfl hup⟩
  intro r hr; simp only [List.mem_cons, not_or] at hr
  exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)

theorem wp_optMovW [Host] {E : Int64 → MachineData → Prop} (w : Width) (s : MachineData)
    (rd rs : Reg64) {va : BitVec w.bits} (hrs : (s.regs.get64 rs).setWidth w.bits = va) :
    _root_.Program.wp (if rs == rd then [] else [movW w rd rs]) (fun s1 =>
      (s1.regs.get64 rd).setWidth w.bits = va ∧
      (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
      s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ s1.status = s.status) E s := by
  by_cases hrr : rs == rd
  · have heq := (beq_reg64_iff rs rd).1 hrr; subst heq
    simp only [hrr, ↓reduceIte]
    exact _root_.Program.wp_nil ⟨hrs, fun _ _ => rfl, rfl, rfl, rfl⟩
  · simp only [hrr, Bool.false_eq_true, ↓reduceIte]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w s rd rs)) ?_
    rintro s1 rfl
    refine ⟨?_, fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl, rfl⟩
    rw [Reg64s.get64_set64_same, setWidth_64_setWidth, hrs]

end

end LeanQbe.T.Amd64

