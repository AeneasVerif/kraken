module

public import LeanQbe.T.Amd64.VllAsmX64
public import LeanQbe.T.Vll.Sem
import LeanQbe.T.Amd64.IselStepRules
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.AbiLemmas
import Kraken.X64.Parser

/-!
# Assembler Verification Part 0: ALU, Native, and Simulation Core (`Amd64.VllAsmX64Lemmas0`)

Core foundations for `LeanQbe.T.Amd64.VllAsmX64Lemmas`:
* `ParserChecks`: `rfl` conformance against `Kraken.X64.Parser`.
* `hostSymAddr`, `SimState`, `SimExact`, `nextFlagMask`, `nextFlagMaskList`, `VllStepPre`,
  `VllFallPre`, `VllListPre`.
* Sub-word (`writeSubX64`) and status-flag bridges.
* Full `.alu` simulation (`asmX64_alu_fallsTo`), `.cmp`/`.test`/`.clearFlags`/`.setcc`/`.load`/
  `.mov` simulation, `.jnzGpr` conditional branch simulation (`asmX64_jnzGpr_run`), and
  `.native` escape-hatch simulation (`asmX64_native_fallsTo`, `asmX64_native_jump`).

Zero `Arm64`/`Kraken.AArch64` imports, zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll
open Std Std.ExtHashMap

/-! ## 1. `ParserChecks` (`rfl` against `Kraken.X64.Parser`) -/

section ParserChecks
open Kraken.X64.Parser

example : ⸨prog| movq %rsi, %rax ⸩ = asmX64 (.mov .w64 .rax .rsi) := rfl
example : ⸨prog| movl %esi, %eax ⸩ = asmX64 (.mov .w32 .rax .rsi) := rfl
example : ⸨prog| movw %si, %ax ⸩ = asmX64 (.mov .w16 .rax .rsi) := rfl
example : ⸨prog| movb %sil, %al ⸩ = asmX64 (.mov .w8 .rax .rsi) := rfl
example : ⸨prog| movl $42, %eax ⸩ = asmX64 (.movi .rax 42) := rfl
example : ⸨prog| mov $0x100000000, %rax ⸩ = asmX64 (.movi .rax 0x100000000) := rfl
example : ⸨prog| leaq (%rsi,%rdx,1), %rax ⸩ =
    asmX64 (.alu .add .w64 .rax .rsi (.reg .rdx) false) := rfl
example : ⸨prog| addq %rdx, %rax ⸩ =
    asmX64 (.alu .add .w64 .rax .rax (.reg .rdx) true) := rfl
example : ⸨prog| subl %edx, %eax ⸩ =
    asmX64 (.alu .sub .w32 .rax .rax (.reg .rdx) true) := rfl
example : ⸨prog| shlxq %rdx, %rsi, %rax ⸩ =
    asmX64 (.alu .shl .w64 .rax .rsi (.reg .rdx) false) := rfl
example : ⸨prog| xorl %r10d, %r10d ⸩ = asmX64 .clearFlags := rfl
example : ⸨prog| sete %al ⸩ = asmX64 (.setcc .rax .z) := rfl
example : ⸨prog| cmpl $7, %eax ⸩ = asmX64 (.cmp .w32 .rax (.imm 7)) := rfl
example : ⸨prog| testq %rsi, %rax ⸩ = asmX64 (.test .w64 .rax (.reg .rsi)) := rfl
example : ⸨prog| movb (%rsi), %al ⸩ = asmX64 (.load .w8 .sub .rax (.baseDisp .rsi 0)) := rfl
example : ⸨prog| movslq (%rsi), %rax ⸩ = asmX64 (.load .w32 .sx .rax (.baseDisp .rsi 0)) := rfl
example : ⸨prog| movq %rsi, 8(%rdi) ⸩ = asmX64 (.store .w64 .rsi (.baseDisp .rdi 8)) := rfl
example : ⸨prog| movq %rax, 16(%rsp) ⸩ = asmX64 (.slotSt 2 .rax) := rfl
example : ⸨prog| movq 16(%rsp), %rax ⸩ = asmX64 (.slotLd .rax 2) := rfl
example : ⸨prog| subq $8, %rsp ⸩ = asmX64 (.prologue 0) := rfl
example : ⸨prog| addq $8, %rsp ⸩ = asmX64 (.epilogue 0) := rfl
example : ⸨prog| movzbl %dil, %edi ⸩ = asmX64 (.canonAbi i8 .rdi) := rfl
example : ⸨prog| jmp L0 ⸩ = asmX64 (.jmp "L0") := rfl
example : ⸨prog| jnz L0 ⸩ = asmX64 (.jcc .nz "L0") := rfl
example : ⸨prog| testb %al, %al; jnz L0 ⸩ = asmX64 (.jnzGpr .rax "L0") := rfl
example : ⸨prog| call f ⸩ = asmX64 (.call "f") := rfl
example : ⸨prog| call *%rax ⸩ = asmX64 (.icall .rax) := rfl
example : ⸨prog| ret ⸩ = asmX64 .ret := rfl
example : ⸨prog| jmp exit_fn ⸩ = asmX64 (.exitJmp "exit_fn") := rfl
example : ⸨prog| jmp *%rcx ⸩ = asmX64 (.tailJmpR .rcx) := rfl
example : ⸨prog| leaq g(%rip), %rax ⸩ = asmX64 (.symAddr "g" .rax) := rfl
example : ⸨prog| jmp *%rdx ⸩ = asmX64 (.ijmp .rdx) := rfl
example : ⸨prog| nop ⸩ = asmX64 (.pad .endbr) := rfl

end ParserChecks

public section

/-! ## 2. Simulation State, Preconditions, and Flag Masks -/

/-- 64-bit symbol address resolved by Kraken `Host` `h`. -/
@[expose] def hostSymAddr (h : Host) (l : Sym) : BitVec 64 :=
  (hostLabel h l).toBitVec

/-- Architectural state simulation relation between L1 `MachSt x64Arch` and Kraken `MachineData`:
off-scratch GPRs, all 512-bit ZMM vectors, memory `dmem`, and status flags disjoint from
`fMask` coincide. -/
@[expose] def SimState (fMask : FlagMask) (sv : MachSt x64Arch) (sk : MachineData) : Prop :=
  (∀ r, r ∉ x64Scratch → sk.regs.get64 r = sv.gpr r) ∧
  (∀ vr, sk.zmms.get512 vr = sv.vreg vr) ∧
  sk.dmem = sv.mem ∧
  ∀ cc : CondCode, FlagMask.disjoint (x64CondReads cc) fMask = true →
    cc.interp sk.status = cc.interp sv.flags

/-- Exact state agreement on every GPR (including `.r10`/`.r11`), ZMM, memory, and flag. -/
@[expose] def SimExact (sv : MachSt x64Arch) (sk : MachineData) : Prop :=
  (∀ r, sk.regs.get64 r = sv.gpr r) ∧
  (∀ vr, sk.zmms.get512 vr = sv.vreg vr) ∧
  sk.dmem = sv.mem ∧
  ∀ cc : CondCode, cc.interp sk.status = cc.interp sv.flags

theorem SimExact.toSimState {sv : MachSt x64Arch} {sk : MachineData}
    (h : SimExact sv sk) (fMask : FlagMask) : SimState fMask sv sk :=
  ⟨fun r _ => h.1 r, h.2.1, h.2.2.1, fun cc _ => h.2.2.2 cc⟩

/-- Next flag agreement mask after executing `i` given previous mask `fMask`. -/
@[expose] def nextFlagMask : Instr x64Arch → FlagMask → FlagMask
  | .alu _ _ _ _ _ true | .cmp _ _ _ | .test _ _ _ | .clearFlags | .jnzGpr _ _
  | .native _ => fun _ => maskNone
  | .alu _ _ _ _ _ false | .prologue _ | .epilogue _ => fun _ => maskAll
  | _ => fun m => m

/-- Flag agreement mask after straight-line instruction list `is`. -/
@[expose] def nextFlagMaskList (is : List (Instr x64Arch)) (fMask : FlagMask) : FlagMask :=
  is.foldl (fun m i => nextFlagMask i m) fMask

/-- Per-instruction execution precondition unifying straight-line and control instructions. -/
@[expose] def VllStepPre (h : Host) (k : Nat) (fMask : FlagMask)
    (sv : MachSt x64Arch) (sk : MachineData) : Instr x64Arch → Prop
  | .native d =>
    SimExact sv sk ∧
    (letI := h; (d.interp sk ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
      (fun _ => .done ⟨sk, 0⟩) (fun _ _ => .done ⟨sk, 0⟩)).All (fun _ => True))
  | i =>
    (∀ r ∈ i.uses ++ i.defs, r ∉ x64Scratch) ∧
    match i with
    | .setcc _ cc | .jcc cc _ => FlagMask.disjoint (x64CondReads cc) fMask = true
    | .load w _ _ addr =>
      x64AddrValid addr = true ∧
      ∃ v : BitVec w.bits, loadVal sv.mem w.toTy (addr.eval sv.gpr) = some v
    | .store w _ addr =>
      x64AddrValid addr = true ∧ storeOk sv.mem w.toTy (addr.eval sv.gpr)
    | .slotSt idx _ => storeOk sv.mem i64 (sv.gpr .rsp + BitVec.ofNat 64 (8 * idx))
    | .slotLd _ idx =>
      ∃ v : BitVec 64, loadVal sv.mem i64 (sv.gpr .rsp + BitVec.ofNat 64 (8 * idx)) = some v
    | .canonAbi t _ => match t with | .bits n => n ∈ x64Arch.abi.bitWidths | _ => True
    | .call _ | .icall _ => storeOk sv.mem i64 (sv.gpr .rsp - 8#64)
    | .ret => ∃ ra : BitVec 64, loadVal sv.mem i64 (sv.gpr .rsp) = some ra
    | _ => True

/-- Straight-line instruction precondition forbidding jumps, halts, and control transfers. -/
@[expose] def VllFallPre (h : Host) (k : Nat) (fMask : FlagMask)
    (sv : MachSt x64Arch) (sk : MachineData) : Instr x64Arch → Prop
  | .native d =>
    SimExact sv sk ∧
    (letI := h; (d.interp sk ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
      (fun s1 => .done ⟨s1, 0⟩) (fun _ _ => .unimplemented "jmp")).All (fun _ => True))
  | i => i.isStraightLine = true ∧ VllStepPre h k fMask sv sk i

/-- Inductive straight-line execution precondition across a sequence of `Instr x64Arch`. -/
@[expose] def VllListPre (h : Host) :
    Nat → FlagMask → MachSt x64Arch → MachineData → List (Instr x64Arch) → Prop
  | _, _, _, _, [] => True
  | k, fMask, sv, sk, i :: is =>
    VllFallPre h k fMask sv sk i ∧
    ∀ sv' sk',
      instrRel x64Arch (hostSymAddr h) 0#64 i sv (.fall sv') →
      SimState (nextFlagMask i fMask) sv' sk' →
      x64Mach.Frame x64CondReads sk sk' (i.defs ++ x64Scratch) i.clobVec i.clobFlags →
      VllListPre h (k + (asmX64 i).length) (nextFlagMask i fMask) sv' sk' is

theorem SimState_mono {f₁ f₂ : FlagMask} {sv : MachSt x64Arch} {sk : MachineData}
    (hsub : f₁ &&& ~~~f₂ = 0#8) (h : SimState f₁ sv sk) : SimState f₂ sv sk :=
  ⟨h.1, h.2.1, h.2.2.1, fun cc hdisj => h.2.2.2 cc (FlagMask.disjoint_of_sub hsub hdisj)⟩

theorem SimState_maskAll {sv : MachSt x64Arch} {sk : MachineData}
    (hr : ∀ r, r ∉ x64Scratch → sk.regs.get64 r = sv.gpr r)
    (hv : ∀ vr, sk.zmms.get512 vr = sv.vreg vr)
    (hm : sk.dmem = sv.mem) : SimState maskAll sv sk :=
  ⟨hr, hv, hm, fun cc h => by
    cases cc <;> simp [x64CondReads, FlagMask.disjoint, maskAll, maskOF, maskCF,
      maskZF, maskSF, maskPF] at h⟩

/-! ## 3. Private Sub-Word and Status-Flag Bridges -/

private theorem not_mask_getLsbD_iff {k i : Nat} (hk : k ≤ 64) (hi : i < 64) :
    (~~~BitVec.ofNat 64 (2 ^ k - 1)).getLsbD i = !decide (i < k) := by
  rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_not, BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat]
  have hlt : 2 ^ k - 1 < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos k) (by decide))
      (Nat.pow_le_pow_right (by decide) hk)
  rw [Nat.mod_eq_of_lt hlt, Nat.testBit_two_pow_sub_one]

private theorem getLsbD_of_ge {m : Nat} (v : BitVec m) {i : Nat} (hi : m ≤ i) :
    v.getLsbD i = false := by
  change v.toNat.testBit i = false
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hi))

private theorem getLsbD_replaceLow {old : BitVec 64} {n : Nat} (hn : n ≤ 64) (new : BitVec n)
    {i : Nat} (hi : i < 64) :
    (old.replaceLow new).getLsbD i = if i < n then new.getLsbD i else old.getLsbD i := by
  simp only [BitVec.replaceLow, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
  change (old.drop n ++ new).getLsbD i = _
  rw [BitVec.getLsbD_append]
  split
  · rfl
  · simp [BitVec.drop, show i - n < 64 - n by omega, show n + (i - n) = i by omega]

theorem replaceLow_8_eq_writeSubX64 (old : BitVec 64) (v : BitVec 8) :
    old.replaceLow v = writeSubX64 .w8 old v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_replaceLow (by decide) v hi]
  simp only [writeSubX64, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    decide_eq_true hi, Bool.true_and]
  have hmask : (~~~0xFF#64 : BitVec 64).getLsbD i = !decide (i < 8) :=
    not_mask_getLsbD_iff (k := 8) (by decide) hi
  rw [hmask]
  by_cases hi8 : i < 8
  · simp [hi8]
  · have hv : v.getLsbD i = false := getLsbD_of_ge v (by omega)
    simp [hi8, hv]

theorem replaceLow_16_eq_writeSubX64 (old : BitVec 64) (v : BitVec 16) :
    old.replaceLow v = writeSubX64 .w16 old v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_replaceLow (by decide) v hi]
  simp only [writeSubX64, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    decide_eq_true hi, Bool.true_and]
  have hmask : (~~~0xFFFF#64 : BitVec 64).getLsbD i = !decide (i < 16) :=
    not_mask_getLsbD_iff (k := 16) (by decide) hi
  rw [hmask]
  by_cases hi16 : i < 16
  · simp [hi16]
  · have hv : v.getLsbD i = false := getLsbD_of_ge v (by omega)
    simp [hi16, hv]

theorem writeSubX64_idem (w : Vll.Width) (old : BitVec 64) (v₁ v₂ : BitVec w.bits) :
    writeSubX64 w (writeSubX64 w old v₁) v₂ = writeSubX64 w old v₂ := by
  cases w with
  | w8 =>
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [writeSubX64, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
      decide_eq_true hi, Bool.true_and]
    have hnot : (~~~0xFF#64 : BitVec 64).getLsbD i = !decide (i < 8) :=
      not_mask_getLsbD_iff (k := 8) (by decide) hi
    rw [hnot]
    by_cases hi8 : i < 8
    · simp [hi8]
    · have hle : Vll.Width.w8.bits ≤ i := by change 8 ≤ i; omega
      simp [hi8, getLsbD_of_ge v₁ hle, getLsbD_of_ge v₂ hle]
  | w16 =>
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [writeSubX64, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
      decide_eq_true hi, Bool.true_and]
    have hnot : (~~~0xFFFF#64 : BitVec 64).getLsbD i = !decide (i < 16) :=
      not_mask_getLsbD_iff (k := 16) (by decide) hi
    rw [hnot]
    by_cases hi16 : i < 16
    · simp [hi16]
    · have hle : Vll.Width.w16.bits ≤ i := by change 16 ≤ i; omega
      simp [hi16, getLsbD_of_ge v₁ hle, getLsbD_of_ge v₂ hle]
  | w32 | w64 => rfl

theorem cond_statusFlags_of_fields {s₁ s₂ : StatusFlags}
    (hcf : s₁.cf = s₂.cf) (hpf : s₁.pf = s₂.pf) (hzf : s₁.zf = s₂.zf)
    (hsf : s₁.sf = s₂.sf) (hof : s₁.of = s₂.of) (cc : CondCode) :
    cc.interp s₁ = cc.interp s₂ := by
  cases cc <;> simp [CondCode.interp, hcf, hpf, hzf, hsf, hof]

private theorem cond_clearFlags_eq (af : Bool) (cc : CondCode) :
    cc.interp (StatusFlags.from_result 0#32 { cf := false, af, of := false }) =
      cc.interp x64ClearFlagsVal := by
  cases cc <;> simp [CondCode.interp, StatusFlags.from_result, x64ClearFlagsVal] <;> decide

private theorem cond_cmpFlags_eq (w : Vll.Width) (a b : BitVec w.bits) (f : StatusFlags)
    (cc : CondCode) :
    cc.interp (subFlags a b) = cc.interp (x64CmpFlags w a b f) := by
  apply cond_statusFlags_of_fields rfl rfl rfl rfl rfl

private theorem cond_testFlags_eq (w : Vll.Width) (a b : BitVec w.bits) (f : StatusFlags)
    (af : Bool) (cc : CondCode) :
    cc.interp (testFlags a b af) = cc.interp (x64TestFlags w a b f) := by
  apply cond_statusFlags_of_fields rfl rfl rfl rfl rfl

private theorem cond_jnzGprFlags_eq (v : BitVec 64) (f : StatusFlags) (af : Bool)
    (cc : CondCode) :
    cc.interp (testFlags (v.setWidth 8) (v.setWidth 8) af) =
      cc.interp (x64JnzGprFlags v f) := by
  cases cc <;> simp [CondCode.interp, testFlags, x64JnzGprFlags, StatusFlags.from_result,
    BitVec.and_self]

private theorem simState_after_step {fMask fMask' : FlagMask} {sv sv' : MachSt x64Arch}
    {sk sk' : MachineData} (hsim : SimState fMask sv sk)
    (hgpr : ∀ r, r ∉ x64Scratch → sk'.regs.get64 r = sv'.gpr r)
    (hvec : sk'.zmms = sk.zmms) (hmem : sk'.dmem = sv'.mem)
    (hflg : ∀ cc : CondCode, FlagMask.disjoint (x64CondReads cc) fMask' = true →
      cc.interp sk'.status = cc.interp sv'.flags)
    (hvreg : ∀ vr, sv'.vreg vr = sv.vreg vr) :
    SimState fMask' sv' sk' :=
  ⟨hgpr, fun vr => by rw [hvec, hvreg]; exact hsim.2.1 vr, hmem, hflg⟩

private theorem frame_of_gpr_set {s s' : MachineData} {gClob : List Reg64} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → s'.regs.get64 r = s.regs.get64 r)
    (hzm : s'.zmms = s.zmms) (hflg : x64Mach.UpdFlags x64CondReads s s' fClob) :
    x64Mach.Frame x64CondReads s s' gClob [] fClob :=
  ⟨hkeep, fun vr _ => by simp [hzm], hflg⟩

theorem fallsTo_movSubW (w : Vll.Width) (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (.instr (movSubWI w.toX64 rd rs)) s
      (· = { s with regs := s.regs.set64 rd (writeSubX64 w (s.regs.get64 rd)
        ((s.regs.get64 rs).setWidth w.bits)) }) := by
  intro _ _ _ _ _ hk
  cases w
  · simp only [movSubWI, Vll.Width.toX64, regW, t_step_simp, Reg64s.set,
      replaceLow_8_eq_writeSubX64]
    exact hk _ rfl
  · simp only [movSubWI, Vll.Width.toX64, regW, t_step_simp, Reg64s.set,
      replaceLow_16_eq_writeSubX64]
    exact hk _ rfl
  · simp only [movSubWI, Vll.Width.toX64, regW, t_step_simp, Reg64s.set]
    simpa [writeSubX64, BitVec.zeroExtend_eq_setWidth] using hk _ rfl
  · simp only [movSubWI, Vll.Width.toX64, regW, t_step_simp, Reg64s.set]
    simpa [writeSubX64, BitVec.setWidth_eq] using hk _ rfl

/-! ## 4. Continuation Transport for `.native` (`EffectsSim4`) -/

private inductive EffectsSim4
    (n₁ : MachineData → Effects) (j₁ : Int64 → MachineData → Effects)
    (n₂ : MachineData → Effects) (j₂ : Int64 → MachineData → Effects)
    (n₃ : MachineData → Effects) (j₃ : Int64 → MachineData → Effects)
    (n₄ : MachineData → Effects) (j₄ : Int64 → MachineData → Effects) :
    Effects → Effects → Effects → Effects → Prop where
  | fall {s'} : EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (n₁ s') (n₂ s') (n₃ s') (n₄ s')
  | jump {a s'} : EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (j₁ a s') (j₂ a s') (j₃ a s') (j₄ a s')
  | fail {e₁ e₂ e₃ e₄} : (∀ P, ¬e₁.All P) → EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ e₁ e₂ e₃ e₄
  | undef {α} [NondetSupportingType α] {c₁ c₂ c₃ c₄ : α → Effects} :
      (∀ v, EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (c₁ v) (c₂ v) (c₃ v) (c₄ v)) →
      EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
        (.undefined c₁) (.undefined c₂) (.undefined c₃) (.undefined c₄)
  | rread {sp} {k₁ k₂ k₃ k₄ : Unit → Effects} :
      EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (k₁ ()) (k₂ ()) (k₃ ()) (k₄ ()) →
      EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
        (.require_read_access sp k₁) (.require_read_access sp k₂)
        (.require_read_access sp k₃) (.require_read_access sp k₄)
  | rwrite {sp} {k₁ k₂ k₃ k₄ : Unit → Effects} :
      EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (k₁ ()) (k₂ ()) (k₃ ()) (k₄ ()) →
      EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
        (.require_write_access sp k₁) (.require_write_access sp k₂)
        (.require_write_access sp k₃) (.require_write_access sp k₄)
  | rexec {p} {k₁ k₂ k₃ k₄ : Unit → Effects} :
      EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (k₁ ()) (k₂ ()) (k₃ ()) (k₄ ()) →
      EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
        (.require_exec_access p k₁) (.require_exec_access p k₂)
        (.require_exec_access p k₃) (.require_exec_access p k₄)

private theorem effectsSim4_lift {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄}
    {e₀₂ e₀₃ e₁ e₂ e₃ e₄ : Effects}
    (hsim : EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ e₁ e₂ e₃ e₄)
    (hl₂ : ∀ {st}, EffectsReaches e₂ st → EffectsReaches e₀₂ st)
    (hl₃ : ∀ {st}, EffectsReaches e₃ st → EffectsReaches e₀₃ st)
    {P₁ P₄ : MachineState → Prop} (hall : e₁.All P₁)
    (hf : ∀ s', (n₁ s').All P₁ →
      (∀ {st}, EffectsReaches (n₂ s') st → EffectsReaches e₀₂ st) → (n₄ s').All P₄)
    (hj : ∀ a s', (j₁ a s').All P₁ →
      (∀ {st}, EffectsReaches (j₃ a s') st → EffectsReaches e₀₃ st) → (j₄ a s').All P₄) :
    e₄.All P₄ := by
  induction hsim generalizing e₀₂ e₀₃ with
  | fall => exact hf _ hall hl₂
  | jump => exact hj _ _ hall hl₃
  | fail hn => exact False.elim (hn P₁ hall)
  | undef _ ih =>
    exact fun v => ih v (fun hr => hl₂ (.undefined hr)) (fun hr => hl₃ (.undefined hr)) (hall v)
      hf hj
  | rread _ ih =>
    exact ih (fun hr => hl₂ (.require_read hr)) (fun hr => hl₃ (.require_read hr)) hall hf hj
  | rwrite _ ih =>
    exact ih (fun hr => hl₂ (.require_write hr)) (fun hr => hl₃ (.require_write hr)) hall hf hj
  | rexec _ ih =>
    exact ih (fun hr => hl₂ (.require_exec hr)) (fun hr => hl₃ (.require_exec hr)) hall hf hj

private theorem sim4_require_read {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} (addr : BitVec 64) (bytes : UInt64)
    {k₁ k₂ k₃ k₄ : Unit → Effects}
    (h : EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (k₁ ()) (k₂ ()) (k₃ ()) (k₄ ())) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (require_access require_read_access addr bytes k₁)
      (require_access require_read_access addr bytes k₂)
      (require_access require_read_access addr bytes k₃)
      (require_access require_read_access addr bytes k₄) := by
  dsimp only [require_access]; split
  · exact .rread h
  · exact .rread (.rread h)

private theorem sim4_require_write {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} (addr : BitVec 64) (bytes : UInt64)
    {k₁ k₂ k₃ k₄ : Unit → Effects}
    (h : EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (k₁ ()) (k₂ ()) (k₃ ()) (k₄ ())) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (require_access require_write_access addr bytes k₁)
      (require_access require_write_access addr bytes k₂)
      (require_access require_write_access addr bytes k₃)
      (require_access require_write_access addr bytes k₄) := by
  dsimp only [require_access]; split
  · exact .rwrite h
  · exact .rwrite (.rwrite h)

private theorem sim4_load {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {s : MachineData} {a : BitVec 64}
    {w : _root_.Width} {r₁ r₂ r₃ r₄ : w.type → MachineData → Effects}
    (h : ∀ v s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ v s') (r₂ v s') (r₃ v s') (r₄ v s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (s.load a w r₁) (s.load a w r₂) (s.load a w r₃) (s.load a w r₄) := by
  dsimp only [MachineData.load]
  refine sim4_require_read _ _ ?_
  cases Mem.loadInt s.dmem a w.bytes
  · exact .fail fun P hp => hp
  · exact h _ s

private theorem sim4_store {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {s : MachineData} {a : BitVec 64}
    {w : _root_.Width} {v : w.type} {r₁ r₂ r₃ r₄ : MachineData → Effects}
    (h : ∀ s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ s') (r₂ s') (r₃ s') (r₄ s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (s.store a v r₁) (s.store a v r₂) (s.store a v r₃) (s.store a v r₄) := by
  dsimp only [MachineData.store]
  refine sim4_require_write _ _ ?_
  cases Mem.loadInt s.dmem a w.bytes
  · exact .fail fun P hp => hp
  · exact h _

private theorem sim4_rm [Labels] [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {w : _root_.Width}
    {rm : RegOrMem w} {s : MachineData} {p : Std.Rco Int64}
    {r₁ r₂ r₃ r₄ : w.type → MachineData → Effects}
    (h : ∀ v s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ v s') (r₂ v s') (r₃ v s') (r₄ v s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (rm.interp s p r₁) (rm.interp s p r₂) (rm.interp s p r₃) (rm.interp s p r₄) := by
  cases rm with | reg _ => exact h _ _ | mem _ => exact sim4_load h

private theorem sim4_opnd [Labels] [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {w : _root_.Width}
    {o : Operand w} {s : MachineData} {p : Std.Rco Int64}
    {r₁ r₂ r₃ r₄ : w.type → MachineData → Effects}
    (h : ∀ v s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ v s') (r₂ v s') (r₃ v s') (r₄ v s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (o.interp s p r₁) (o.interp s p r₂) (o.interp s p r₃) (o.interp s p r₄) := by
  cases o with | regOrMem _ => exact sim4_rm h | imm _ => exact h _ _

private theorem sim4_rrm [Labels] [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {rm : RelRegOrMem}
    {s : MachineData} {p : Std.Rco Int64}
    {r₁ r₂ r₃ r₄ : BitVec 64 → MachineData → Effects}
    (h : ∀ v s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ v s') (r₂ v s') (r₃ v s') (r₄ v s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (rm.interp s p r₁) (rm.interp s p r₂) (rm.interp s p r₃) (rm.interp s p r₄) := by
  cases rm with | rel _ | reg _ => exact h _ _ | mem _ => exact sim4_load h

private theorem sim4_set [Labels] [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {w : _root_.Width}
    (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64)
    {r₁ r₂ r₃ r₄ : MachineData → Effects}
    (h : ∀ s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ s') (r₂ s') (r₃ s') (r₄ s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (s.set d v p r₁) (s.set d v p r₂) (s.set d v p r₃) (s.set d v p r₄) := by
  cases d with | reg _ => exact h _ | mem _ => exact sim4_store h

private theorem sim4_avxRm [Labels] [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {w : AvxWidth}
    {rm : AvxRegOrMem w} {s : MachineData} {p : Std.Rco Int64}
    {r₁ r₂ r₃ r₄ : w.type → MachineData → Effects} {chk : Bool}
    (h : ∀ v s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ v s') (r₂ v s') (r₃ v s') (r₄ v s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (rm.interp s p r₁ chk) (rm.interp s p r₂ chk)
      (rm.interp s p r₃ chk) (rm.interp s p r₄ chk) := by
  cases rm with
  | avx _ => exact h _ _
  | mem _ =>
    dsimp only [AvxRegOrMem.interp, MachineData.loadAvx]; split
    · exact .fail fun P hp => hp
    · refine sim4_require_read _ _ ?_
      cases Mem.loadInt s.dmem _ _
      · exact .fail fun P hp => hp
      · exact h _ s

private theorem sim4_setAvxCore [Labels] [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {aw : AvxWidth}
    (leg : Bool) (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64)
    {r₁ r₂ r₃ r₄ : MachineData → Effects} (chk : Bool)
    (h : ∀ s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ s') (r₂ s') (r₃ s') (r₄ s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (if leg then s.setAvxLegacy d v p r₁ chk else s.setAvx d v p r₁ chk)
      (if leg then s.setAvxLegacy d v p r₂ chk else s.setAvx d v p r₂ chk)
      (if leg then s.setAvxLegacy d v p r₃ chk else s.setAvx d v p r₃ chk)
      (if leg then s.setAvxLegacy d v p r₄ chk else s.setAvx d v p r₄ chk) := by
  cases d with
  | avx _ => cases leg <;> exact h _
  | mem _ =>
    cases leg <;>
      simp only [MachineData.setAvxLegacy, MachineData.setAvx, MachineData.storeAvx,
        Bool.false_eq_true, ↓reduceIte] <;>
      split <;>
      first
      | exact .fail fun P hp => hp
      | (refine sim4_require_write _ _ ?_
         cases Mem.loadInt s.dmem _ _
         · exact .fail fun P hp => hp
         · exact h _)

private theorem sim4_setAvx [Labels] [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄} {aw : AvxWidth}
    (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64)
    {r₁ r₂ r₃ r₄ : MachineData → Effects} (chk : Bool)
    (h : ∀ s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ s') (r₂ s') (r₃ s') (r₄ s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (s.setAvx d v p r₁ chk) (s.setAvx d v p r₂ chk)
      (s.setAvx d v p r₃ chk) (s.setAvx d v p r₄ chk) :=
  sim4_setAvxCore false s d v p chk h

private theorem sim4_setAvxLegacy [Labels] [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄}
    {aw : AvxWidth} (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64)
    {r₁ r₂ r₃ r₄ : MachineData → Effects} (chk : Bool)
    (h : ∀ s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ s') (r₂ s') (r₃ s') (r₄ s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (s.setAvxLegacy d v p r₁ chk) (s.setAvxLegacy d v p r₂ chk)
      (s.setAvxLegacy d v p r₃ chk) (s.setAvxLegacy d v p r₄ chk) :=
  sim4_setAvxCore true s d v p chk h

private theorem sim4_repString [AddressSize] {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄}
    {step : MachineData → (MachineData → Effects) → Effects}
    (hstep : ∀ s (r₁ r₂ r₃ r₄ : MachineData → Effects),
      (∀ s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ s') (r₂ s') (r₃ s') (r₄ s')) →
      EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
        (step s r₁) (step s r₂) (step s r₃) (step s r₄))
    (rs : List Reg64) (s : MachineData) {r₁ r₂ r₃ r₄ : MachineData → Effects}
    (h : ∀ s', EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (r₁ s') (r₂ s') (r₃ s') (r₄ s')) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (MachineData.repString step rs s r₁) (MachineData.repString step rs s r₂)
      (MachineData.repString step rs s r₃) (MachineData.repString step rs s r₄) := by
  dsimp only [MachineData.repString]; split
  · exact .undef fun _ => h _
  · suffices ∀ c s0,
        EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
          (MachineData.repeatString step c s0 r₁) (MachineData.repeatString step c s0 r₂)
          (MachineData.repeatString step c s0 r₃) (MachineData.repeatString step c s0 r₄) from
      this _ s
    intro c; induction c with
    | zero => intro _; exact h _
    | succ _ ih => intro _; exact hstep _ _ _ _ _ fun _ => ih _

private theorem sim4_undef {n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ α} {inst : NondetSupportingType α}
    {c₁ c₂ c₃ c₄ : α → Effects}
    (h : ∀ v, EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄ (c₁ v) (c₂ v) (c₃ v) (c₄ v)) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (@Effects.undefined α inst c₁) (@Effects.undefined α inst c₂)
      (@Effects.undefined α inst c₃) (@Effects.undefined α inst c₄) :=
  EffectsSim4.undef h

private theorem avx_interp_sim4 [Labels] (asz : _root_.Width) (w : AvxWidth)
    (aop : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
    (n₁ n₂ n₃ n₄ : MachineData → Effects) (j₁ j₂ j₃ j₄ : Int64 → MachineData → Effects) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (_root_.Directive.interp (.instr (.avx asz w aop)) s p n₁ j₁)
      (_root_.Directive.interp (.instr (.avx asz w aop)) s p n₂ j₂)
      (_root_.Directive.interp (.instr (.avx asz w aop)) s p n₃ j₃)
      (_root_.Directive.interp (.instr (.avx asz w aop)) s p n₄ j₄) := by
  refine .rexec ?_
  letI : AddressSize := ⟨asz⟩
  cases aop with
  | vmovIn _ _ _ => dsimp only [AvxOperation.interp]; exact sim4_rm fun _ _ => .fall
  | vmovOut _ dst _ =>
    cases dst with
    | reg _ => exact .fall
    | mem _ => exact sim4_store fun _ => .fall
  | vmovq _ _ | vzeroupper => exact .fall
  | vmovups d _ | vmovdqu d _ | vmovdqu32 d _ | vmovdqa32 d _
  | vprord d _ _ | vpsrld d _ _ =>
    dsimp only [AvxOperation.interp]
    exact sim4_avxRm fun _ _ => sim4_setAvx _ d _ p _ fun _ => .fall
  | vpaddd d _ _ =>
    dsimp only [AvxOperation.interp]
    exact sim4_avxRm fun _ _ => sim4_avxRm fun _ _ =>
      sim4_setAvx _ d _ p _ fun _ => .fall
  | vpternlogd d _ _ _ =>
    dsimp only [AvxOperation.interp]
    exact sim4_avxRm fun _ _ => sim4_avxRm fun _ _ => sim4_avxRm fun _ _ =>
      sim4_setAvx _ d _ p _ fun _ => .fall
  | movups d _ | movaps d _ | movdqu d _ | movdqa d _ | pshufd d _ _ =>
    dsimp only [AvxOperation.interp]
    exact sim4_avxRm fun _ _ => sim4_setAvxLegacy _ d _ p _ fun _ => .fall
  | subps d _ | addps d _ | paddd d _ | pshufb d _ | palignr d _ _ | pblendw d _ _
  | sha256rnds2 d _ | sha256msg1 d _ | sha256msg2 d _ =>
    dsimp only [AvxOperation.interp]
    exact sim4_avxRm fun _ _ => sim4_avxRm fun _ _ =>
      sim4_setAvxLegacy _ d _ p _ fun _ => .fall

private def isOpHi : ∀ {w : _root_.Width}, Operation w → Bool
  | _, .cld | _, .std | _, .nop _ | _, .nopalign _ _ | _, .lea _ _
  | _, .setcc _ _ | _, .push _ | _, .pop _ | _, .cmovcc _ _ _ | _, .mulx _ _ _
  | _, .adcx _ _ | _, .adox _ _ | _, .cmp _ _ | _, .test _ _ | _, .mov _ _
  | _, .movsx _ _ | _, .movzx _ _ | _, .not _ | _, .inc _ | _, .dec _ | _, .neg _
  | _, .add _ _ | _, .adc _ _ | _, .sub _ _ | _, .sbb _ _
  | _, .and _ _ | _, .or _ _ | _, .xor _ _ => true
  | _, _ => false

private theorem op_interp_sim4_lo [Labels] [AddressSize] {w : _root_.Width} (op : Operation w)
    (h : isOpHi op = false) (p : Std.Rco Int64) (s : MachineData)
    (n₁ n₂ n₃ n₄ : MachineData → Effects) (j₁ j₂ j₃ j₄ : Int64 → MachineData → Effects) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (op.interp p s n₁ j₁) (op.interp p s n₂ j₂)
      (op.interp p s n₃ j₃) (op.interp p s n₄ j₄) := by
  cases op with
  | jcc _ _ => dsimp only [Operation.interp]; split; exact .jump; exact .fall
  | jmp _ | call _ | ret =>
    dsimp only [Operation.interp]
    repeat first | apply sim4_rrm; intro _ _ | apply sim4_load; intro _ _ |
      apply sim4_store; intro _
    exact .jump
  | movs _ =>
    dsimp only [Operation.interp]; split
    · refine sim4_repString (fun _ _ _ _ _ h1 => ?_) _ s fun _ => .fall
      apply sim4_load; intro _ _; apply sim4_store; intro _; exact h1 _
    · apply sim4_load; intro _ _; apply sim4_store; intro _; exact .fall
  | stos _ =>
    dsimp only [Operation.interp]; split
    · refine sim4_repString (fun _ _ _ _ _ h1 => ?_) _ s fun _ => .fall
      apply sim4_store; intro _; exact h1 _
    · apply sim4_store; intro _; exact .fall
  | div _ | idiv _ =>
    cases w <;>
      simp only [Operation.interp, show (_root_.Width.W8 == .W8) = true from rfl,
        show (_root_.Width.W16 == .W8) = false from rfl,
        show (_root_.Width.W32 == .W8) = false from rfl,
        show (_root_.Width.W64 == .W8) = false from rfl, Bool.false_eq_true, ↓reduceIte] <;>
      apply sim4_rm <;> intro _ _ <;> split <;>
      first | exact .fail fun P hp => hp | exact .undef fun _ => .fall
  | mul _ | imul1 _ =>
    dsimp only [Operation.interp]; apply sim4_rm; intro _ _
    exact .undef fun _ => .undef fun _ => .undef fun _ => .undef fun _ => .fall
  | imul _ _ _ =>
    dsimp only [Operation.interp]; apply sim4_rm; intro _ _; apply sim4_opnd; intro _ _
    apply sim4_set; intro _
    exact .undef fun _ => .undef fun _ => .undef fun _ => .undef fun _ => .fall
  | shl _ _ | shr _ _ | sar _ _ | shld _ _ _ | shrd _ _ _
  | rol _ _ | ror _ _ | rcr _ _ | rcl _ _ =>
    dsimp only [Operation.interp, Reg.interp]
    repeat (first
      | apply sim4_rm; intro _ _
      | exact sim4_set _ _ _ p fun _ => .fall
      | apply EffectsSim4.undef; intro _
      | exact .fail fun P hp => hp
      | dsimp only
      | split)
  | bswap _ =>
    cases w <;> dsimp only [Operation.interp] <;>
      first | exact .fall | exact sim4_undef fun _ => .fall
  | lzcnt _ _ | tzcnt _ _ =>
    cases w <;> dsimp only [Operation.interp] <;>
      first
      | exact sim4_undef fun _ => sim4_undef fun _ => .fall
      | exact sim4_rm fun _ _ => sim4_undef fun _ =>
          sim4_undef fun _ => sim4_undef fun _ => sim4_undef fun _ => .fall
  | popcnt _ _ =>
    cases w <;> dsimp only [Operation.interp] <;>
      first
      | exact sim4_undef fun _ => sim4_undef fun _ => .fall
      | exact sim4_rm fun _ _ => .fall
  | rorx _ _ _ | shlx _ _ _ | shrx _ _ _ | sarx _ _ _ =>
    cases w <;> dsimp only [Operation.interp] <;>
      first | exact sim4_undef fun _ => .fall | exact sim4_rm fun _ _ => .fall
  | _ => exact Bool.noConfusion h

private theorem op_interp_sim4_hi [Labels] [AddressSize] {w : _root_.Width} (op : Operation w)
    (h : isOpHi op = true) (p : Std.Rco Int64) (s : MachineData)
    (n₁ n₂ n₃ n₄ : MachineData → Effects) (j₁ j₂ j₃ j₄ : Int64 → MachineData → Effects) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (op.interp p s n₁ j₁) (op.interp p s n₂ j₂)
      (op.interp p s n₃ j₃) (op.interp p s n₄ j₄) := by
  cases op with
  | cld | std | nop _ | nopalign _ _ | lea _ _ => exact .fall
  | setcc _ _ => dsimp only [Operation.interp]; exact sim4_set _ _ _ p fun _ => .fall
  | push _ => dsimp only [Operation.interp]; exact sim4_opnd fun _ _ => sim4_store fun _ => .fall
  | pop _ =>
    dsimp only [Operation.interp]; exact sim4_load fun _ _ => sim4_set _ _ _ p fun _ => .fall
  | cmovcc _ _ _ | mulx _ _ _ =>
    dsimp only [Operation.interp]; apply sim4_rm; intro _ _; exact .fall
  | adcx _ _ | adox _ _ =>
    dsimp only [Operation.interp, Reg.interp]; apply sim4_rm; intro _ _; exact .fall
  | cmp _ _ =>
    dsimp only [Operation.interp]
    apply sim4_rm; intro _ _; apply sim4_opnd; intro _ _; exact .fall
  | test _ _ =>
    dsimp only [Operation.interp]
    apply sim4_rm; intro _ _; apply sim4_opnd; intro _ _; exact .undef fun _ => .fall
  | mov _ _ =>
    dsimp only [Operation.interp]; apply sim4_opnd; intro _ _; apply sim4_set; intro _; exact .fall
  | movsx _ _ | movzx _ _ =>
    dsimp only [Operation.interp]; apply sim4_rm; intro _ _; apply sim4_set; intro _; exact .fall
  | not _ | inc _ | dec _ | neg _ =>
    dsimp only [Operation.interp]; apply sim4_rm; intro _ _; apply sim4_set; intro _; exact .fall
  | add _ _ | adc _ _ | sub _ _ | sbb _ _ =>
    dsimp only [Operation.interp]
    apply sim4_opnd; intro _ _; apply sim4_rm; intro _ _; apply sim4_set; intro _; exact .fall
  | and _ _ | or _ _ | xor _ _ =>
    dsimp only [Operation.interp]
    apply sim4_rm; intro _ _; apply sim4_opnd; intro _ _
    apply EffectsSim4.undef; intro _; apply sim4_set; intro _; exact .fall
  | _ => exact Bool.noConfusion h

private theorem dir_interp_sim4 [Labels] (d : _root_.Directive) (p : Std.Rco Int64)
    (s : MachineData) (n₁ n₂ n₃ n₄ : MachineData → Effects)
    (j₁ j₂ j₃ j₄ : Int64 → MachineData → Effects) :
    EffectsSim4 n₁ j₁ n₂ j₂ n₃ j₃ n₄ j₄
      (d.interp s p n₁ j₁) (d.interp s p n₂ j₂) (d.interp s p n₃ j₃) (d.interp s p n₄ j₄) := by
  cases d with
  | label _ => exact .fall
  | byteArray bs => dsimp only [Directive.interp]; split; exact .fall; exact .fail fun P hp => hp
  | word bytes _ =>
    dsimp only [Directive.interp]; cases bytes; exact .fall; exact .fail fun P hp => hp
  | instr i =>
    cases i with
    | avx asz w aop => exact avx_interp_sim4 asz w aop p s n₁ n₂ n₃ n₄ j₁ j₂ j₃ j₄
    | regular asz w op =>
      refine .rexec ?_
      letI : AddressSize := ⟨asz⟩
      cases h : isOpHi op
      · exact op_interp_sim4_lo op h p s n₁ n₂ n₃ n₄ j₁ j₂ j₃ j₄
      · exact op_interp_sim4_hi op h p s n₁ n₂ n₃ n₄ j₁ j₂ j₃ j₄

/-! ## 5. Public Non-ALU & Control Simulation Theorems -/

theorem asmX64_mov_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {w : Vll.Width} {rd rs : Reg64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch) (hrs : rs ∉ x64Scratch) :
    let sv' := sv.setGprW w rd ((sv.gpr rs).setWidth w.bits)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.mov w rd rs)) [rd] [] maskNone sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.mov w rd rs)).length)).toBitVec
          (.mov w rd rs) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  intro sv'
  refine dir_to_x64FallsTo (fallsTo_movSubW w sk rd rs) ?_
  rintro sk' rfl
  refine ⟨⟨rfl, simState_after_step hsim (fun r hr => ?_) rfl hsim.2.2.1
      (fun cc hc => hsim.2.2.2 cc hc) (fun _ => rfl)⟩,
    frame_of_gpr_set (fun r hr => Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm (by simpa using hr)))
      rfl (updFlags_of_status_eq rfl _)⟩
  by_cases hrr : r = rd
  · subst hrr; simp [Reg64s.get64_set64_same, hsim.1 r hr, hsim.1 rs hrs, sv', x64Arch]
  · simp [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hrr), hsim.1 r hr, sv', hrr]

theorem asmX64_cmp_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {w : Vll.Width}
    {lhs : Reg64} {rhs : Src x64Arch} {sv : MachSt x64Arch} {sk : MachineData}
    {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hlhs : lhs ∉ x64Scratch)
    (hrhs : ∀ rs, rhs = .reg rs → rs ∉ x64Scratch) :
    let sv' :=
      sv.setFlags (x64CmpFlags w ((sv.gpr lhs).setWidth w.bits) (rhs.evalW w sv.gpr) sv.flags)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.cmp w lhs rhs)) x64Scratch [] maskAll sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.cmp w lhs rhs)).length)).toBitVec
          (.cmp w lhs rhs) sv (.fall sv') ∧
        SimState maskNone sv' sk') post := by
  intro sv'
  have hlhs10 := (ne_of_not_mem_x64Scratch hlhs).1
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  have finish : ∀ (st : StatusFlags),
      (∀ cc : CondCode, cc.interp st = cc.interp (subFlags ((sv.gpr lhs).setWidth w.bits)
        (rhs.evalW w sv.gpr))) →
      ({ sk with status := st } : MachineData) = { sk with status := st } →
      (instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.cmp w lhs rhs)).length)).toBitVec
          (.cmp w lhs rhs) sv (.fall sv') ∧
        SimState maskNone sv' { sk with status := st }) ∧
      x64Mach.Frame x64CondReads sk { sk with status := st } x64Scratch [] maskAll :=
    fun st hcc _ =>
    ⟨⟨rfl, hsim.1, hsim.2.1, hsim.2.2.1,
        fun cc _ => (hcc cc).trans (cond_cmpFlags_eq w _ _ sv.flags cc)⟩,
      x64_frame_of_eq (fun _ _ => rfl) rfl (updFlags_maskAll _ _)⟩
  cases rhs with
  | reg rs =>
    have hrs := hsim.1 rs (hrhs rs rfl)
    simp only [asmX64, srcToPArg, cmpDirectIns, Option.getD_some, emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w.toX64 sk lhs rs)) ?_
    rintro sk' rfl
    exact finish _ (fun cc => by
      cases w <;> simp [Vll.Width.toX64, Vll.Width.bits, hsim.1 lhs hlhs, hrs,
        Src.evalW, Src.eval]) rfl
  | imm imm =>
    simp only [asmX64, srcToPArg, cmpDirectIns, cmpRegImmIns, Option.getD_some]
    by_cases hz : (imm.setWidth w.toX64.bits == 0#w.toX64.bits) = true
    · have hz0 : imm.setWidth w.bits = 0#w.bits := by
        have := beq_iff_eq.mp hz; cases w <;> exact this
      simp only [hz, ↓reduceIte, emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg w.toX64 sk lhs lhs)) ?_
      rintro sk' ⟨af, rfl⟩
      refine finish _ (fun cc => ?_) rfl
      have hsub := cond_testFlags_self ((sv.gpr lhs).setWidth w.bits) af cc
      cases w <;> simp_all [Vll.Width.toX64, Vll.Width.bits, hsim.1 lhs hlhs, Src.evalW, Src.eval]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp
          (fallsTo_cmp_imm w.toX64 sk lhs (imm.setWidth w.toX64.bits))) ?_
        rintro sk' rfl
        exact finish _ (fun cc => by
          cases w <;> simp [Vll.Width.toX64, Vll.Width.bits, hsim.1 lhs hlhs,
            Src.evalW, Src.eval]) rfl
      · rename_i hnofit
        have hw64 : w = .w64 := by
          cases w with
          | w64 => rfl
          | w8 | w16 | w32 =>
            exact False.elim (hnofit (by simp only [Vll.Width.toX64,
              show (_root_.Width.W8 != .W64) = true from by decide,
              show (_root_.Width.W16 != .W64) = true from by decide,
              show (_root_.Width.W32 != .W64) = true from by decide, Bool.true_or]))
        subst hw64
        simp only [Vll.Width.toX64, BitVec.setWidth_eq, emitClean_cons, emitClean_nil]
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD sk .r10 imm)) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg .W64 _ lhs .r10)) ?_
        rintro s2 rfl
        have hl10 : (sk.regs.set64 .r10 imm).get64 lhs = sv.gpr lhs :=
          (Reg64s.get64_set64_of_ne _ .r10 lhs _ hlhs10.symm).trans (hsim.1 lhs hlhs)
        refine ⟨⟨rfl, fun r hr => ?_, hsim.2.1, hsim.2.2.1, fun cc _ => by
            dsimp only [sv']
            simpa [Vll.Width.bits, BitVec.setWidth_eq, hl10, Reg64s.get64_set64_same,
              Src.evalW, Src.eval] using cond_cmpFlags_eq .w64 (sv.gpr lhs) imm sv.flags cc⟩,
          x64_frame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
            (ne_of_not_mem_x64Scratch hr).1.symm) rfl (updFlags_maskAll _ _)⟩
        exact (Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm).trans
          (hsim.1 r hr)

theorem asmX64_test_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {w : Vll.Width}
    {lhs : Reg64} {rhs : Src x64Arch} {sv : MachSt x64Arch} {sk : MachineData}
    {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hlhs : lhs ∉ x64Scratch)
    (hrhs : ∀ rs, rhs = .reg rs → rs ∉ x64Scratch) :
    let sv' :=
      sv.setFlags (x64TestFlags w ((sv.gpr lhs).setWidth w.bits) (rhs.evalW w sv.gpr) sv.flags)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.test w lhs rhs)) x64Scratch [] maskAll sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.test w lhs rhs)).length)).toBitVec
          (.test w lhs rhs) sv (.fall sv') ∧
        SimState maskNone sv' sk') post := by
  intro sv'
  have hlhs10 := (ne_of_not_mem_x64Scratch hlhs).1
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  cases rhs with
  | reg rs =>
    have hrs := hsim.1 rs (hrhs rs rfl)
    simp only [asmX64, srcToPArg, testDirectIns, Option.getD_some, emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg w.toX64 sk lhs rs)) ?_
    rintro sk' ⟨af, rfl⟩
    refine ⟨⟨rfl, hsim.1, hsim.2.1, hsim.2.2.1, fun cc _ => by
        dsimp only [sv']; rw [hsim.1 lhs hlhs, hrs]
        simp only [MachSt.flags_setFlags, Vll.Width.toX64, _root_.Width.bits, Vll.Width.bits,
          Src.evalW, Src.eval]
        cases w with
        | w8 =>
          exact cond_testFlags_eq .w8 ((sv.gpr lhs).setWidth 8) ((sv.gpr rs).setWidth 8)
            sv.flags af cc
        | w16 =>
          exact cond_testFlags_eq .w16 ((sv.gpr lhs).setWidth 16) ((sv.gpr rs).setWidth 16)
            sv.flags af cc
        | w32 =>
          exact cond_testFlags_eq .w32 ((sv.gpr lhs).setWidth 32) ((sv.gpr rs).setWidth 32)
            sv.flags af cc
        | w64 =>
          exact cond_testFlags_eq .w64 ((sv.gpr lhs).setWidth 64) ((sv.gpr rs).setWidth 64)
            sv.flags af cc⟩,
      x64_frame_of_eq (fun _ _ => rfl) rfl (updFlags_maskAll _ _)⟩
  | imm imm =>
    simp only [asmX64, srcToPArg, testDirectIns, Option.getD_some]
    split
    · simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp
        (fallsTo_test_imm w.toX64 sk lhs (imm.setWidth w.toX64.bits))) ?_
      rintro sk' ⟨af, rfl⟩
      refine ⟨⟨rfl, hsim.1, hsim.2.1, hsim.2.2.1, fun cc _ => by
          dsimp only [sv']; rw [hsim.1 lhs hlhs]
          simp only [MachSt.flags_setFlags, Vll.Width.toX64, _root_.Width.bits, Vll.Width.bits,
            Src.evalW, Src.eval]
          cases w with
          | w8 =>
            exact cond_testFlags_eq .w8 ((sv.gpr lhs).setWidth 8) (imm.setWidth 8) sv.flags af cc
          | w16 =>
            exact cond_testFlags_eq .w16 ((sv.gpr lhs).setWidth 16) (imm.setWidth 16)
              sv.flags af cc
          | w32 =>
            exact cond_testFlags_eq .w32 ((sv.gpr lhs).setWidth 32) (imm.setWidth 32)
              sv.flags af cc
          | w64 =>
            exact cond_testFlags_eq .w64 ((sv.gpr lhs).setWidth 64) (imm.setWidth 64)
              sv.flags af cc⟩,
        x64_frame_of_eq (fun _ _ => rfl) rfl (updFlags_maskAll _ _)⟩
    · rename_i hnofit
      have hw64 : w = .w64 := by
        cases w with
        | w64 => rfl
        | w8 | w16 | w32 =>
          exact False.elim (hnofit (by simp only [Vll.Width.toX64,
            show (_root_.Width.W8 != .W64) = true from by decide,
            show (_root_.Width.W16 != .W64) = true from by decide,
            show (_root_.Width.W32 != .W64) = true from by decide, Bool.true_or]))
      subst hw64
      simp only [Vll.Width.toX64, BitVec.setWidth_eq, emitClean_cons, emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD sk .r10 imm)) ?_
      rintro s1 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg .W64 _ lhs .r10)) ?_
      rintro s2 ⟨af, rfl⟩
      have hl10 : (sk.regs.set64 .r10 imm).get64 lhs = sv.gpr lhs :=
        (Reg64s.get64_set64_of_ne _ .r10 lhs _ hlhs10.symm).trans (hsim.1 lhs hlhs)
      refine ⟨⟨rfl, fun r hr =>
          (Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm).trans
            (hsim.1 r hr), hsim.2.1, hsim.2.2.1, fun cc _ => by
          dsimp only [sv']
          simpa [Vll.Width.bits, BitVec.setWidth_eq, hl10, Reg64s.get64_set64_same,
            Src.evalW, Src.eval] using cond_testFlags_eq .w64 (sv.gpr lhs) imm sv.flags af cc⟩,
        x64_frame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
          (ne_of_not_mem_x64Scratch hr).1.symm) rfl (updFlags_maskAll _ _)⟩

theorem asmX64_clearFlags_fallsTo {h : Host} {k : Nat} {fMask : FlagMask}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) :
    let sv' := sv.setFlags x64ClearFlagsVal
    x64Mach.FallsTo x64CondReads h k (asmX64 .clearFlags) x64Scratch [] maskAll sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 .clearFlags).length)).toBitVec .clearFlags sv (.fall sv') ∧
        SimState maskNone sv' sk') post := by
  intro sv'
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  dsimp only [asmX64, x64Gpr, emitClean, x64InsI]
  refine _root_.Program.wp_singleton fun _ _ => ?_
  simp only [t_step_simp, Effects.All]; intro af
  have hz0 : ((sk.regs.get64 .r10).setWidth 32 ^^^ (sk.regs.get64 .r10).setWidth 32) = 0#32 := by
    apply BitVec.eq_of_getElem_eq; intro i _; simp
  rw [hz0]
  refine Or.inl ⟨trivial, ⟨⟨rfl, fun r hr =>
      (Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm).trans
        (hsim.1 r hr), hsim.2.1, hsim.2.2.1, fun cc _ => cond_clearFlags_eq af cc⟩,
    x64_frame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
      (ne_of_not_mem_x64Scratch hr).1.symm) rfl (updFlags_maskAll _ _)⟩⟩

theorem asmX64_setcc_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {rd : Reg64} {cc : CondCode}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch)
    (hflg : FlagMask.disjoint (x64CondReads cc) fMask = true) :
    let sv' := sv.setGprW .w8 rd (BitVec.ofNat 8 (cc.interp sv.flags).toNat)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.setcc rd cc)) (rd :: x64Scratch) [] maskNone sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.setcc rd cc)).length)).toBitVec
          (.setcc rd cc) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  intro sv'
  have _ := hrd
  refine x64_fallsTo_of_wp fun {_} _ => Program.wp.mono (wp_setccOnly sk rd cc) ?_
  rintro sk' rfl
  have hcc := hsim.2.2.2 cc hflg
  refine ⟨⟨rfl, fun r hr => ?_, hsim.2.1, hsim.2.2.1, fun cc' hc => hsim.2.2.2 cc' hc⟩,
    x64_frame_of_eq (fun r hr => Reg64s.get64_set64_of_ne _ rd r _
      (fun e => hr (List.mem_cons.mpr (.inl e.symm)))) rfl (updFlags_of_status_eq rfl _)⟩
  by_cases hrr : r = rd
  · subst hrr
    simp [sv', Reg64s.get64_set64_same, replaceLow_8_eq_writeSubX64, hsim.1 r hr, hcc, x64Arch]
  · simp [sv', hrr, Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hrr), hsim.1 r hr]

private theorem asmX64_load_sub_post {fMask : FlagMask} {w : Vll.Width}
    {rd : Reg64} {addr : AddrArg Reg64} {sv : MachSt x64Arch} {sk s1 : MachineData}
    {regs' : Reg64s} {sym : Sym → BitVec 64} {nextPc : BitVec 64} {v : BitVec w.bits} {pc' : Int64}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch)
    (hr1 : ∀ r, r ≠ .r10 → s1.regs.get64 r = sk.regs.get64 r) (hz1 : s1.zmms = sk.zmms)
    (hf1 : x64Mach.UpdFlags x64CondReads sk s1 maskNone)
    (hv : loadVal sv.mem w.toTy (addr.eval sv.gpr) = some v)
    (hset : regs'.get64 rd = writeSubX64 w (s1.regs.get64 rd) v)
    (hkeep : ∀ r, r ≠ rd → regs'.get64 r = s1.regs.get64 r) :
    pc' = pc' ∧
      (∃ sv', instrRel x64Arch sym nextPc (.load w .sub rd addr) sv (.fall sv') ∧
        SimState fMask sv' { s1 with regs := regs', dmem := sk.dmem }) ∧
      x64Mach.Frame x64CondReads sk { s1 with regs := regs', dmem := sk.dmem }
        (rd :: x64Scratch) [] maskNone := by
  have hrd10 := (ne_of_not_mem_x64Scratch hrd).1
  let sv' := sv.setGpr rd (LoadExt.sub.apply x64Arch w (sv.gpr rd) v)
  refine ⟨rfl, ⟨sv', ⟨v, hv, rfl⟩, fun r hr => ?_, fun vr => by simp [sv', hz1, hsim.2.1 vr],
      hsim.2.2.1, fun cc hc => (hf1 cc (FlagMask.disjoint_none _)).trans (hsim.2.2.2 cc hc)⟩,
    x64_frame_of_eq (fun r hr => ?_) hz1 (fun cc hc => hf1 cc (FlagMask.disjoint_none _))⟩
  · by_cases hrr : r = rd
    · subst r
      simp only [sv', MachSt.gpr_setGpr_same, LoadExt.apply, x64Arch, hset, hr1 rd hrd10,
        hsim.1 rd hrd]
    · dsimp only [sv']
      rw [MachSt.gpr_setGpr_ne _ _ hrr, hkeep r hrr, hr1 r (ne_of_not_mem_x64Scratch hr).1,
        hsim.1 r hr]
  · simp only [List.mem_cons, not_or] at hr
    rw [hkeep r hr.1, hr1 r hr.2.1]

private theorem asmX64_load_sub816_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} (w : Vll.Width)
    (hw : w = .w8 ∨ w = .w16) {rd : Reg64} {addr : AddrArg Reg64} {sv : MachSt x64Arch}
    {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch)
    (ha : ∀ r ∈ addr.regs, r ∉ x64Scratch) (hval : x64AddrValid addr = true)
    {v : BitVec w.bits} (hv : loadVal sv.mem w.toTy (addr.eval sv.gpr) = some v)
    (hload : loadVal sk.dmem w.toTy (addr.eval sk.regs.get64) = some v)
    (hae_clob : (addrToExprIns addr).2.2 = maskNone) :
    x64Mach.FallsTo x64CondReads h k (asmX64 (.load w .sub rd addr))
      (rd :: x64Scratch) [] maskNone sk
      (fun sk' => ∃ sv', instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.load w .sub rd addr)).length)).toBitVec
          (.load w .sub rd addr) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  have hae_eq : asmX64 (.load w .sub rd addr) = (addrToExpr addr).1 ++
      [insW w.toX64 (.mov (.reg (regW w.toX64 rd)) (.mem (addrToExpr addr).2.1))] := by
    rcases hw with rfl | rfl <;> simp [asmX64, hval]
  rw [hae_eq]
  have ha_clob : (addrToExpr addr).2.2 = maskNone := by simp only [addrToExpr, hae_clob]
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  refine Program.wp.append (wp_addrToExpr sk sk addr ha fun _ _ => rfl) ?_
  rintro s1 ⟨_, hr1, hm1, hz1, haddr1, hf1⟩
  refine Program.wp.mono (Q := fun s2 =>
      (∃ sv', instrRel x64Arch (hostSymAddr h)
        (Host.addrOf (k + ((addrToExpr addr).1 ++
          [insW w.toX64 (.mov (.reg (regW w.toX64 rd))
            (.mem (addrToExpr addr).2.1))]).length)).toBitVec
        (.load w .sub rd addr) sv (.fall sv') ∧ SimState fMask sv' s2) ∧
      x64Mach.Frame x64CondReads sk s2 (rd :: x64Scratch) [] maskNone)
    (_root_.Program.wp_singleton fun _ _ => ?_) (fun _ h => h)
  rcases hw with rfl | rfl
  · obtain ⟨i, hi, rfl⟩ := loadVal_width_spec .W8 (hm1 ▸ hload)
    simp only [insW, regW, t_step_simp, MachineData.load, Effects.All_require_read_access,
      haddr1 s1.regs (fun _ _ => rfl), hm1, Vll.Width.toX64, _root_.Width.bytes, _root_.Width.bits]
    rw [hm1] at hi; rw [hi]
    refine Or.inl ?_
    refine @asmX64_load_sub_post fMask .w8 rd addr sv sk s1 _ _ _ _ _
      hsim hrd hr1 hz1 (ha_clob ▸ hf1) hv ?_ ?_
    · simp only [Reg64s.set, Reg64s.get64_set64_same, replaceLow_8_eq_writeSubX64]
    · exact fun r hrr => Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hrr)
  · obtain ⟨i, hi, rfl⟩ := loadVal_width_spec .W16 (hm1 ▸ hload)
    simp only [insW, regW, t_step_simp, MachineData.load, Effects.All_require_read_access,
      haddr1 s1.regs (fun _ _ => rfl), hm1, Vll.Width.toX64, _root_.Width.bytes, _root_.Width.bits]
    rw [hm1] at hi; rw [hi]
    refine Or.inl ?_
    refine @asmX64_load_sub_post fMask .w16 rd addr sv sk s1 _ _ _ _ _
      hsim hrd hr1 hz1 (ha_clob ▸ hf1) hv ?_ ?_
    · simp only [Reg64s.set, Reg64s.get64_set64_same, replaceLow_16_eq_writeSubX64]
    · exact fun r hrr => Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hrr)

theorem asmX64_load_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {w : Vll.Width} {ext : LoadExt}
    {rd : Reg64} {addr : AddrArg Reg64} {sv : MachSt x64Arch} {sk : MachineData}
    {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch)
    (ha : ∀ r ∈ addr.regs, r ∉ x64Scratch) (hval : x64AddrValid addr = true)
    (hld : ∃ v : BitVec w.bits, loadVal sv.mem w.toTy (addr.eval sv.gpr) = some v) :
    x64Mach.FallsTo x64CondReads h k (asmX64 (.load w ext rd addr))
      (rd :: x64Scratch) [] maskNone sk
      (fun sk' => ∃ sv', instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.load w ext rd addr)).length)).toBitVec
          (.load w ext rd addr) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  obtain ⟨v, hv⟩ := hld
  have heval : addr.eval sk.regs.get64 = addr.eval sv.gpr := by
    cases addr with
    | baseDisp rb d => simp [AddrArg.eval, hsim.1 rb (ha rb (by simp [AddrArg.regs]))]
    | baseIdxDisp rb ri sc d =>
      simp [AddrArg.eval, hsim.1 rb (ha rb (by simp [AddrArg.regs])),
        hsim.1 ri (ha ri (by simp [AddrArg.regs]))]
    | imm a => rfl
  have hload : loadVal sk.dmem w.toTy (addr.eval sk.regs.get64) = some v := by
    rw [hsim.2.2.1, heval]; exact hv
  have hae_clob : (addrToExprIns addr).2.2 = maskNone := by
    cases addr
    · dsimp only [addrToExprIns]; split; rfl; split <;> rfl
    · dsimp only [addrToExprIns]; split <;> rfl
    · rfl
  have hzx_some : ∀ (w' : Vll.Width), ∃ c, x64Load w'.toTy rd addr = some (c, maskNone) := by
    intro w'
    cases w' <;> cases addr <;>
      simp_all [Vll.Width.toTy, x64Load, x64LoadIns, emitCleanPair, Option.map_some, addrToExprIns]
    all_goals (split; exact ⟨_, rfl⟩; try (split <;> exact ⟨_, rfl⟩))
  have hsx_some : ∀ (w' : Vll.Width) (hne : w' ≠ .w64),
      ∃ c, x64LoadSext w'.bits 64 rd addr = some (c, maskNone) := by
    intro w' hne
    cases w' with
    | w64 => exact absurd rfl hne
    | w8 | w16 | w32 =>
      cases addr <;>
        simp_all [Vll.Width.bits, x64LoadSext, x64LoadSextIns, emitCleanPair, addrToExprIns]
      all_goals (split; exact ⟨_, rfl⟩; try (split <;> exact ⟨_, rfl⟩))
  have of_zext : ∀ {c : List _root_.Directive} (hl : x64Load w.toTy rd addr = some (c, maskNone))
      (hext : ext.apply x64Arch w (sv.gpr rd) v = v.setWidth 64),
      x64Mach.FallsTo x64CondReads h k c (rd :: x64Scratch) [] maskNone sk
        (fun sk' => ∃ sv', instrRel x64Arch (hostSymAddr h)
            (Host.addrOf (k + c.length)).toBitVec (.load w ext rd addr) sv (.fall sv') ∧
          SimState fMask sv' sk') post := by
    intro c hl hext hinf hcont
    exact x64Gpr_load_zext hl hrd ha hload hinf fun sk' ⟨hhold, hmem⟩ hfr => by
      have h64 : sk'.regs.get64 rd = v.setWidth 64 := by
        cases w <;> simp [AbiGprHolds] at hhold <;> first | exact hhold | exact hhold.2
      let sv' := sv.setGpr rd (ext.apply x64Arch w (sv.gpr rd) v)
      refine hcont sk' ⟨sv', ⟨v, hv, rfl⟩, fun r hr => ?_, fun vr =>
          (hfr.2.1 vr (by simp)).trans (hsim.2.1 vr), hmem.trans hsim.2.2.1,
          fun cc hc => (hfr.2.2 cc (FlagMask.disjoint_none _)).trans
            (hsim.2.2.2 cc hc)⟩ hfr
      by_cases hrr : r = rd
      · subst hrr; simp [sv', h64, hext]
      · dsimp only [sv']; rw [MachSt.gpr_setGpr_ne _ _ hrr]
        exact (hfr.1 r (by simp [List.mem_cons, hrr, hr])).trans (hsim.1 r hr)
  cases ext with
  | zx =>
    obtain ⟨c, hl⟩ := hzx_some w
    simpa [asmX64, hl] using of_zext hl rfl
  | sx =>
    have of_sx : ∀ (hne : w ≠ .w64) {c : List _root_.Directive}
        (hl : x64LoadSext w.bits 64 rd addr = some (c, maskNone)),
        x64Mach.FallsTo x64CondReads h k c (rd :: x64Scratch) [] maskNone sk
          (fun sk' => ∃ sv', instrRel x64Arch (hostSymAddr h)
              (Host.addrOf (k + c.length)).toBitVec (.load w .sx rd addr) sv (.fall sv') ∧
            SimState fMask sv' sk') post := by
      intro _ c hl hinf hcont
      exact x64Gpr_loadSext_spec hl hrd ha hload hinf fun sk' ⟨h64, hmem⟩ hfr => by
        let sv' := sv.setGpr rd (LoadExt.sx.apply x64Arch _ (sv.gpr rd) v)
        refine hcont sk' ⟨sv', ⟨v, hv, rfl⟩, fun r hr => ?_, fun vr =>
            (hfr.2.1 vr (by simp)).trans (hsim.2.1 vr), hmem.trans hsim.2.2.1,
            fun cc hc => (hfr.2.2 cc (FlagMask.disjoint_none _)).trans
              (hsim.2.2.2 cc hc)⟩ hfr
        by_cases hrr : r = rd
        · subst hrr; simp [sv', h64, LoadExt.apply]
        · dsimp only [sv']; rw [MachSt.gpr_setGpr_ne _ _ hrr]
          exact (hfr.1 r (by simp [List.mem_cons, hrr, hr])).trans (hsim.1 r hr)
    cases w with
    | w64 =>
      obtain ⟨c, hl⟩ := hzx_some .w64
      simpa [asmX64, Vll.Width.toTy, hl] using
        of_zext hl (by simp [LoadExt.apply, BitVec.setWidth_eq])
    | w8 =>
      obtain ⟨c, hl⟩ := hsx_some .w8 (by decide)
      simpa [asmX64, hl] using of_sx (by decide) hl
    | w16 =>
      obtain ⟨c, hl⟩ := hsx_some .w16 (by decide)
      simpa [asmX64, hl] using of_sx (by decide) hl
    | w32 =>
      obtain ⟨c, hl⟩ := hsx_some .w32 (by decide)
      simpa [asmX64, hl] using of_sx (by decide) hl
  | sub =>
    cases w with
    | w32 =>
      obtain ⟨c, hl⟩ := hzx_some .w32
      simpa [asmX64, hl] using of_zext hl (by simp [LoadExt.apply, writeSubX64])
    | w64 =>
      obtain ⟨c, hl⟩ := hzx_some .w64
      simpa [asmX64, hl] using of_zext hl (by simp [LoadExt.apply, writeSubX64])
    | w8 => exact asmX64_load_sub816_fallsTo .w8 (.inl rfl) hsim hrd ha hval hv hload hae_clob
    | w16 => exact asmX64_load_sub816_fallsTo .w16 (.inr rfl) hsim hrd ha hval hv hload hae_clob

theorem asmX64_native_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {d : _root_.Directive}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hpre : VllFallPre h k fMask sv sk (.native d)) :
    x64Mach.FallsTo x64CondReads h k (asmX64 (.native d))
      ((Instr.native d : Instr x64Arch).defs ++ x64Scratch)
      (Instr.native d : Instr x64Arch).clobVec
      (Instr.native d : Instr x64Arch).clobFlags sk
      (fun sk' => ∃ sv', instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.native d)).length)).toBitVec (.native d) sv (.fall sv') ∧
        SimState maskNone sv' sk') post := by
  obtain ⟨hex, hall⟩ := hpre
  letI := h
  intro hc hcont
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  have hsim := dir_interp_sim4 d ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ sk
    (fun s1 => .done ⟨s1, 0⟩) (fun s1 => .done ⟨s1, 0⟩)
    (fun _ => .unimplemented "fall") (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩)
    (fun _ _ => .unimplemented "jmp") (fun _ _ => .unimplemented "jmp")
    (fun a s1 => .done ⟨s1, a⟩) (fun a s' => .done ⟨s', a⟩)
  refine effectsSim4_lift hsim (fun hr => hr) (fun hr => hr) hall ?_ ?_
  · intro s' _ hre
    have hns : x64NativeStep d (hostSymAddr h) sv (.fall (krakenToMachData s')) :=
      ⟨sk, ⟨Host.addrOf k, Host.addrOf (k + 1)⟩, hex.1, hex.2.1, hex.2.2.2, hex.2.2.1,
        s', hre .done, rfl⟩
    have hsnd := @x64Arch_nativeEffectSound d (hostSymAddr h) sv
      (.fall (krakenToMachData s')) hns
    have hfr : x64Mach.Frame x64CondReads sk s'
        ((Instr.native d : Instr x64Arch).defs ++ x64Scratch)
        (Instr.native d : Instr x64Arch).clobVec
        (Instr.native d : Instr x64Arch).clobFlags := by
      refine ⟨fun r hr => ?_, fun vr hvr => ?_, fun cc hc => ?_⟩
      · exact (hsnd.1 r fun hmem => hr (List.mem_append_left _ hmem)).trans (hex.1 r).symm
      · exact (hsnd.2.1 vr hvr).trans (hex.2.1 vr).symm
      · exact (hsnd.2.2.1 cc hc).trans (hex.2.2.2 cc).symm
    have hsim' : SimState maskNone (krakenToMachData s') s' :=
      ⟨fun _ _ => rfl, fun _ => rfl, rfl, fun _ _ => rfl⟩
    change Eventually (step1 Host.exe) post ⟨s', Host.addrOf (k + 1)⟩
    have hrun := hcont s' ⟨krakenToMachData s', ⟨.fall _, hns, rfl⟩, hsim'⟩ hfr
    rw [show k + (asmX64 (.native d)).length = k + 1 from rfl] at hrun
    exact hrun
  · intro _ _ hf; exact False.elim hf

theorem asmX64_native_jump {h : Host} {k : Nat} {fMask : FlagMask} {d : _root_.Directive}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.native d)).IsInfixAt Host.prog k)
    (hpre : VllStepPre h k fMask sv sk (.native d))
    (hfall : ∀ sv' sk',
      instrRel x64Arch (hostSymAddr h) (Host.addrOf (k + 1)).toBitVec (.native d) sv (.fall sv') →
      SimState maskNone sv' sk' →
      x64Mach.Frame x64CondReads sk sk'
        ((Instr.native d : Instr x64Arch).defs ++ x64Scratch)
        (Instr.native d : Instr x64Arch).clobVec
        (Instr.native d : Instr x64Arch).clobFlags →
      x64Mach.Run h (k + 1) sk' post)
    (hjump : ∀ pc' sv' sk',
      instrRel x64Arch (hostSymAddr h) (Host.addrOf (k + 1)).toBitVec
        (.native d) sv (.jump pc' sv') →
      SimState maskNone sv' sk' →
      x64Mach.Frame x64CondReads sk sk'
        ((Instr.native d : Instr x64Arch).defs ++ x64Scratch)
        (Instr.native d : Instr x64Arch).clobVec
        (Instr.native d : Instr x64Arch).clobFlags →
      Eventually (step1 Host.exe) post ⟨sk', Int64.ofBitVec pc'⟩) :
    x64Mach.Run h k sk post := by
  obtain ⟨hex, hall⟩ := hpre
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  have hsim := dir_interp_sim4 d ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ sk
    (fun _ => .done ⟨sk, 0⟩) (fun s1 => .done ⟨s1, 0⟩)
    (fun _ => .unimplemented "fall") (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩)
    (fun _ _ => .done ⟨sk, 0⟩) (fun _ _ => .unimplemented "jmp")
    (fun a s1 => .done ⟨s1, a⟩) (fun a s' => .done ⟨s', a⟩)
  refine effectsSim4_lift hsim (fun hr => hr) (fun hr => hr) hall ?_ ?_
  · intro s' _ hre
    have hns : x64NativeStep d (hostSymAddr h) sv (.fall (krakenToMachData s')) :=
      ⟨sk, ⟨Host.addrOf k, Host.addrOf (k + 1)⟩, hex.1, hex.2.1, hex.2.2.2, hex.2.2.1,
        s', hre .done, rfl⟩
    have hsnd := @x64Arch_nativeEffectSound d (hostSymAddr h) sv
      (.fall (krakenToMachData s')) hns
    have hfr : x64Mach.Frame x64CondReads sk s'
        ((Instr.native d : Instr x64Arch).defs ++ x64Scratch)
        (Instr.native d : Instr x64Arch).clobVec
        (Instr.native d : Instr x64Arch).clobFlags :=
      ⟨fun r hr => (hsnd.1 r fun hmem => hr (List.mem_append_left _ hmem)).trans (hex.1 r).symm,
       fun vr hvr => (hsnd.2.1 vr hvr).trans (hex.2.1 vr).symm,
       fun cc hc => (hsnd.2.2.1 cc hc).trans (hex.2.2.2 cc).symm⟩
    have hsim' : SimState maskNone (krakenToMachData s') s' :=
      ⟨fun _ _ => rfl, fun _ => rfl, rfl, fun _ _ => rfl⟩
    exact hfall _ s' ⟨.fall _, hns, rfl⟩ hsim' hfr
  · intro a s' _ hre
    have ha_eq : Int64.ofBitVec a.toBitVec = a := Int64.ofBitVec_toBitVec a
    have hns : x64NativeStep d (hostSymAddr h) sv (.jump a.toBitVec (krakenToMachData s')) :=
      ⟨sk, ⟨Host.addrOf k, Host.addrOf (k + 1)⟩, hex.1, hex.2.1, hex.2.2.2, hex.2.2.1,
        s', by rw [ha_eq]; exact hre .done, rfl⟩
    have hsnd := @x64Arch_nativeEffectSound d (hostSymAddr h) sv
      (.jump a.toBitVec (krakenToMachData s')) hns
    have hfr : x64Mach.Frame x64CondReads sk s'
        ((Instr.native d : Instr x64Arch).defs ++ x64Scratch)
        (Instr.native d : Instr x64Arch).clobVec
        (Instr.native d : Instr x64Arch).clobFlags :=
      ⟨fun r hr => (hsnd.1 r fun hmem => hr (List.mem_append_left _ hmem)).trans (hex.1 r).symm,
       fun vr hvr => (hsnd.2.1 vr hvr).trans (hex.2.1 vr).symm,
       fun cc hc => (hsnd.2.2.1 cc hc).trans (hex.2.2.2 cc).symm⟩
    have hsim' : SimState maskNone (krakenToMachData s') s' :=
      ⟨fun _ _ => rfl, fun _ => rfl, rfl, fun _ _ => rfl⟩
    change Eventually (step1 Host.exe) post ⟨s', a⟩
    have hstep := hjump a.toBitVec _ s' ⟨.jump _ _, hns, rfl⟩ hsim' hfr
    simpa only [Int64.ofBitVec_toBitVec] using hstep

theorem asmX64_jnzGpr_run {h : Host} {k : Nat} {fMask : FlagMask} {r : Reg64} {l : Sym}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.jnzGpr r l)).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk) (hr : r ∉ x64Scratch)
    (hfall : let sv' := sv.setFlags (x64JnzGprFlags (sv.gpr r) sv.flags)
      ∀ sk', (sv.gpr r).setWidth 8 = 0#8 →
        SimState maskNone sv' sk' →
        x64Mach.Frame x64CondReads sk sk' x64Scratch [] maskAll →
        x64Mach.Run h (k + 2) sk' post)
    (hjump : let sv' := sv.setFlags (x64JnzGprFlags (sv.gpr r) sv.flags)
      ∀ sk', (sv.gpr r).setWidth 8 ≠ 0#8 →
        SimState maskNone sv' sk' →
        x64Mach.Frame x64CondReads sk sk' x64Scratch [] maskAll →
        Eventually (step1 Host.exe) post ⟨sk', Int64.ofBitVec (hostSymAddr h l)⟩) :
    x64Mach.Run h k sk post := by
  letI := h
  let sv' := sv.setFlags (x64JnzGprFlags (sv.gpr r) sv.flags)
  have ht : _root_.Program.wp [ins8 (.test (.reg (b8 r)) (.reg (b8 r)))]
      (fun sk1 => ∃ af, let st := testFlags ((sv.gpr r).setWidth 8) ((sv.gpr r).setWidth 8) af
        sk1 = { sk with status := st }) (fun _ _ => False) sk := by
    refine Directive.FallsTo.wp ?_
    intro _ _ _ _ _ hk
    simp only [t_step_simp, Effects.All, hsim.1 r hr]; intro af; exact hk _ ⟨af, rfl⟩
  have hc' :
      [ins8 (.test (.reg (b8 r)) (.reg (b8 r))), ins (.jcc .nz l)].IsInfixAt Host.prog k := by
    simpa [asmX64, x64JnzGpr, emitClean] using hc
  refine Program.wp.eventually ht (List.isInfixAt_singleton.mpr hc'.cons.1) ?_
    (fun _ _ hf => hf.elim)
  rintro s1 ⟨af, rfl⟩
  let st := testFlags ((sv.gpr r).setWidth 8) ((sv.gpr r).setWidth 8) af
  have hsim1 : SimState maskNone sv' { sk with status := st } :=
    ⟨hsim.1, hsim.2.1, hsim.2.2.1, fun cc _ => cond_jnzGprFlags_eq (sv.gpr r) sv.flags af cc⟩
  have hfr1 : x64Mach.Frame x64CondReads sk { sk with status := st } x64Scratch [] maskAll :=
    x64_frame_of_eq (fun _ _ => rfl) rfl (updFlags_maskAll _ _)
  refine Host.eventually_of_interp_cps hc'.cons.2.cons.1 ?_
  simp only [t_step_simp]
  have hlab : Labels.label l = Int64.ofBitVec (hostSymAddr h l) :=
    (Int64.ofBitVec_toBitVec (hostLabel h l)).symm
  by_cases h0 : (sv.gpr r).setWidth 8 = 0#8
  · have hcc : CondCode.nz.interp (testFlags ((sv.gpr r).setWidth 8) ((sv.gpr r).setWidth 8) af) =
        false := by
      simp [testFlags, StatusFlags.from_result, CondCode.interp, BitVec.and_self, h0, BitVec.zero]
    simp only [hcc, Bool.false_eq_true, ↓reduceIte, Effects.All, List.length_singleton]
    rw [show k + 1 + 1 = k + 2 from by omega]
    exact hfall _ h0 hsim1 hfr1
  · have hcc : CondCode.nz.interp (testFlags ((sv.gpr r).setWidth 8) ((sv.gpr r).setWidth 8) af) =
        true := by
      simp [testFlags, StatusFlags.from_result, CondCode.interp, BitVec.and_self, h0, BitVec.zero]
    simp only [hcc, ↓reduceIte, Effects.All, hlab]
    exact hjump _ h0 hsim1 hfr1

end

end LeanQbe.T.Amd64
