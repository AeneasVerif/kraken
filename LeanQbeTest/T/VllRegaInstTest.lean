module

public import LeanQbe.T.Vll.RegaInst
public import LeanQbe.T.Spill
public import LeanQbe.T.FlatLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.TargetLemmas
meta import LeanQbe.T.Vll.Arch
meta import LeanQbe.T.Vll.Syntax
meta import LeanQbe.T.Vll.Sem
meta import LeanQbe.T.Vll.RegaInst0
meta import LeanQbe.T.Vll.RegaInst
meta import LeanQbe.T.RegaDefs
meta import LeanQbe.T.Spill

/-!
# Tests for Target-Neutral `Rega` Instantiation on `BedrockMach` L1 (`VllRegaInstTest`)

Exercises:
1. Two concrete 64-bit `Arch` instances (`miniArch` with `.linkReg .lr` + `writeSubZeroExtend`,
   and `miniStackArch` with `.stack` + `writeSubX64`), both with full 10-way `CmpOp` flags,
   instantiating `VllPolicy.core`, `vllTarget`, and `vllLabelClean_core`.
2. Lowering concrete multi-block `Fn`s (leaf arithmetic/conversions/loads/stores, diamond branch,
   triangular loop with flags/branches, helper callee, and multi-call caller exercising stack slots
   and callee-saved registers) via `Spill.hints` + `vllLowerFn` on BOTH `miniTarget` and
   `miniStackTarget`, checking pure first-class `Instr` emission (`0` `.native` instructions).
3. Kernel-verified end-to-end `vllLowerFn_correct` → `Target.FnSpec` theorems on leaf, multi-block
   loop, linked caller+callee (with stack slots/callee-saved), and `.stack` target.
4. `#print axioms` checks confirming `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.VllRegaInstTest

open LeanQbe.T
open LeanQbe.T.Vll

/-! ## 1. Concrete 64-Bit Link-Register & Stack Architectures -/

inductive MiniReg where
  | r0 | r1 | r2 | r3 | r4 | r5 | s0 | s1 | t0 | t1 | sp | lr
  deriving DecidableEq, Repr, Inhabited

inductive MiniCond where
  | eq | ne | ult | uge | ugt | ule | slt | sge | sgt | sle
  deriving DecidableEq, Repr, Inhabited

structure MiniFlags where
  z : Bool
  ul : Bool
  ug : Bool
  sl : Bool
  sg : Bool
  deriving DecidableEq, Repr, Inhabited

@[expose] def miniFrameSize (ns : Nat) : Nat :=
  (8 * ns + 8 + 15) / 16 * 16

@[expose] def miniStackFrameSize (ns : Nat) : Nat :=
  8 * ns + (if ns % 2 == 0 then 8 else 0)

@[expose] def miniCondReads : MiniCond → FlagMask
  | .eq  | .ne  => 0x01#8
  | .ult | .uge => 0x02#8
  | .ugt | .ule => 0x04#8
  | .slt | .sge => 0x08#8
  | .sgt | .sle => 0x10#8

@[expose] def miniNegCond : MiniCond → MiniCond
  | .eq  => .ne  | .ne  => .eq
  | .ult => .uge | .uge => .ult
  | .ugt => .ule | .ule => .ugt
  | .slt => .sge | .sge => .slt
  | .sgt => .sle | .sle => .sgt

@[expose] def miniEvalCond (f : MiniFlags) : MiniCond → Bool
  | .eq  => f.z  | .ne  => !f.z
  | .ult => f.ul | .uge => !f.ul
  | .ugt => f.ug | .ule => !f.ug
  | .slt => f.sl | .sge => !f.sl
  | .sgt => f.sg | .sle => !f.sg

@[expose] def miniCondOfCmp? : CmpOp → Option MiniCond
  | .eq  => some .eq  | .ne  => some .ne
  | .ult => some .ult | .ule => some .ule
  | .ugt => some .ugt | .uge => some .uge
  | .slt => some .slt | .sle => some .sle
  | .sgt => some .sgt | .sge => some .sge

@[expose] def miniCmpFlagsList : List MiniCond :=
  [.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge]

@[expose, reducible] def miniArch : Arch where
  Reg := MiniReg
  VReg := Empty
  Cond := MiniCond
  Flags := MiniFlags
  Native := Empty
  abi := {
    sp := .sp
    raKind := .linkReg .lr
    scratch := [.t0, .t1]
    allocatable := [.r0, .r1, .r2, .r3, .r4, .r5]
    callerSaved := [.r0, .r1, .r2, .r3, .r4, .r5, .t0, .t1]
    calleeSaved := [.s0, .s1]
    argRegs := [.r0, .r1, .r2]
    retRegs := [.r0, .r1]
    stackAlign := 16
    pcAlign := 4
    pcName := "pc"
    frameSize := miniFrameSize
    spEntry := fun sp => sp.toNat % 16 = 0
    spOk := fun sp => sp.toNat % 16 = 0
    prologueClob := FlagMask.none
    epilogueClob := FlagMask.none
  }
  writeSub := writeSubZeroExtend
  condReads := miniCondReads
  negCond := miniNegCond
  evalCond := miniEvalCond
  zeroFlags := [.eq]
  clearFlagsVal := ⟨false, false, false, false, false⟩
  cmpClob := 0x1F#8
  cmpFlags := fun _ a b _ => ⟨a == b, a.ult b, b.ult a, a.slt b, b.slt a⟩
  testClob := 0x01#8
  testFlags := fun w a b f => { f with z := (a &&& b) == 0#w.bits }
  nativeStep := fun d => d.elim
  nativeEffect := fun d => d.elim

theorem miniArch_wf : miniArch.Wf where
  sp_disj := by dsimp only [miniArch, Abi.raRegs, RaKind.raRegs]; decide
  scratch_disj := by
    intro r hr
    simp only [miniArch, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  cs_disj := by
    intro r hr
    simp only [miniArch, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  ra_disj := by
    intro r hr
    simp only [miniArch, Abi.raRegs, RaKind.raRegs, List.mem_singleton] at hr
    subst hr; decide
  argRegs_nodup := by decide
  retRegs_nodup := by decide
  callerSaved_sub := by
    intro r hr
    simp only [miniArch, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  align_pos := by simp
  slots_le_frameSize := fun ns => by dsimp only [miniArch, miniFrameSize]; omega
  linkReg_frameSize := fun _ _ ns => by dsimp only [miniArch, miniFrameSize]; omega
  spOk_frame := fun sp ns hsp => by
    dsimp only [miniArch] at hsp ⊢
    exact aligned16_sub hsp (by dsimp only [miniFrameSize]; omega)
  spEntry_call := fun sp ns hsp => by
    dsimp only [miniArch, Abi.raBytes, RaKind.raBytes] at hsp ⊢
    rw [BitVec.sub_zero]
    exact aligned16_sub hsp (by dsimp only [miniFrameSize]; omega)
  writeSub_setWidth := writeSubZeroExtend_setWidth
  writeSub_w64 := writeSubZeroExtend_w64
  negCond_reads := fun c => by cases c <;> rfl
  negCond_eval := fun f c => by cases f; cases c <;> simp [miniNegCond, miniEvalCond]
  clearFlags_zero := by
    intro c hc; simp only [miniArch, List.mem_singleton] at hc; subst hc; rfl
  aluFlags_frame := fun _ _ _ _ _ _ _ _ => rfl
  cmpFlags_frame := fun _ _ _ _ c hc => by
    cases c <;> simp [miniCondReads, FlagMask.disjoint] at hc
  testFlags_frame := fun _ _ _ _ c hc => by
    cases c <;> simp [miniCondReads, miniEvalCond, FlagMask.disjoint] at hc ⊢
  jnzGprFlags_frame := fun _ _ _ _ => rfl
  prologueFlags_frame := fun _ _ _ _ => rfl
  epilogueFlags_frame := fun _ _ _ _ => rfl
  canonAbiFlags_frame := fun _ _ _ _ => rfl

theorem miniCmpFlags_spec :
    ∀ co cc (w : Width) (a b : BitVec w.bits) f,
      miniCondOfCmp? co = some cc →
      miniArch.evalCond (miniArch.cmpFlags w a b f) cc = co.evalBits a b := by
  intro co cc w a b f h
  cases co <;> simp only [miniCondOfCmp?, Option.some.injEq] at h <;> subst h <;>
    simp only [miniEvalCond, CmpOp.evalBits, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle]
  · by_cases he : a = b <;> simp [he]
  · by_cases he : a = b <;> simp [he]
  · rw [← decide_not]; simp only [decide_eq_decide]; omega
  · rw [← decide_not]; simp only [decide_eq_decide]; omega
  · rw [← decide_not]; simp only [decide_eq_decide]; omega
  · rw [← decide_not]; simp only [decide_eq_decide]; omega

theorem miniClearFlags_frame :
    ∀ (f : miniArch.Flags) (c : miniArch.Cond),
      FlagMask.disjoint (miniArch.condReads c) FlagMask.all = true →
      miniArch.evalCond miniArch.clearFlagsVal c = miniArch.evalCond f c :=
  clearFlags_frame_of_nonzero (A := miniArch) (fun c => by cases c <;> decide)

@[expose] def miniPolicy : VllPolicy miniArch :=
  VllPolicy.core miniArch id miniClearFlags_frame miniCondOfCmp? miniCmpFlagsList miniCmpFlags_spec

@[expose] def miniIsa : Isa := vllIsa miniArch miniPolicy

@[expose] def miniTarget : Target := vllTarget miniArch miniArch_wf miniPolicy

theorem miniLabelClean : Rega.LabelClean miniIsa :=
  vllLabelClean_core miniArch id miniClearFlags_frame miniCondOfCmp? miniCmpFlagsList
    miniCmpFlags_spec

@[expose, reducible] def miniStackArch : Arch :=
  { miniArch with
    abi := { miniArch.abi with
      raKind := .stack
      frameSize := miniStackFrameSize
      spEntry := fun sp => (sp + 8#64).toNat % 16 = 0
      spOk := fun _ => True
      prologueClob := FlagMask.all
      epilogueClob := FlagMask.all
    }
    writeSub := writeSubX64
  }

theorem miniStackArch_wf : miniStackArch.Wf where
  sp_disj := by dsimp only [miniStackArch, miniArch, Abi.raRegs, RaKind.raRegs]; decide
  scratch_disj := miniArch_wf.scratch_disj
  cs_disj := miniArch_wf.cs_disj
  ra_disj := by
    intro r hr; simp only [miniStackArch, Abi.raRegs, RaKind.raRegs, List.not_mem_nil] at hr
  argRegs_nodup := miniArch_wf.argRegs_nodup
  retRegs_nodup := miniArch_wf.retRegs_nodup
  callerSaved_sub := miniArch_wf.callerSaved_sub
  align_pos := miniArch_wf.align_pos
  slots_le_frameSize := fun ns => by
    dsimp only [miniStackArch, miniStackFrameSize]; split <;> omega
  linkReg_frameSize := fun _ h => by simp [miniStackArch] at h
  spOk_frame := fun _ _ _ => trivial
  spEntry_call := fun sp ns hsp => by
    dsimp only [miniStackArch, Abi.raBytes, RaKind.raBytes] at hsp ⊢
    have hmod : miniStackFrameSize ns % 16 = 8 := by
      dsimp only [miniStackFrameSize]
      rcases Nat.mod_two_eq_zero_or_one ns with h | h <;> simp [h] <;> omega
    exact aligned16_add8_sub_call hsp hmod
  writeSub_setWidth := writeSubX64_setWidth
  writeSub_w64 := writeSubX64_w64
  negCond_reads := miniArch_wf.negCond_reads
  negCond_eval := miniArch_wf.negCond_eval
  clearFlags_zero := miniArch_wf.clearFlags_zero
  aluFlags_frame := miniArch_wf.aluFlags_frame
  cmpFlags_frame := miniArch_wf.cmpFlags_frame
  testFlags_frame := miniArch_wf.testFlags_frame
  jnzGprFlags_frame := miniArch_wf.jnzGprFlags_frame
  prologueFlags_frame := fun _ _ _ _ => rfl
  epilogueFlags_frame := fun _ _ _ _ => rfl
  canonAbiFlags_frame := miniArch_wf.canonAbiFlags_frame

@[expose] def miniStackPolicy : VllPolicy miniStackArch :=
  VllPolicy.core miniStackArch id miniClearFlags_frame miniCondOfCmp? miniCmpFlagsList
    miniCmpFlags_spec

@[expose] def miniStackIsa : Isa := vllIsa miniStackArch miniStackPolicy

@[expose] def miniStackTarget : Target :=
  vllTarget miniStackArch miniStackArch_wf miniStackPolicy

theorem miniStackLabelClean : Rega.LabelClean miniStackIsa :=
  vllLabelClean_core miniStackArch id miniClearFlags_frame miniCondOfCmp? miniCmpFlagsList
    miniCmpFlags_spec

/-! ## 2. Concrete Multi-Block `Fn` Suite (Arithmetic, Mem, Branches, Loops, Calls, Slots) -/

/-- Leaf scalar arithmetic, shifts, conversions (`zext`/`sext`/`trunc`), and `i8` load/store. -/
@[expose] def fnArithMem : Fn := ⟨"arithMem", [i64, i64, i32], [i64], fun _ _ (p, x, y, ()) =>
  .load i8 (.var p) fun b =>
  .let_ (op1 (.zext 8 32) (.var b)) fun (bz, ()) =>
  .let_ (op2 (.add i32) (.var bz) (.var y)) fun (s32, ()) =>
  .let_ (op1 (.sext 32 64) (.var s32)) fun (s64, ()) =>
  .let_ (op2 (.xor i64) (.var s64) (.var x)) fun (xr, ()) =>
  .let_ (op2 (.shl i64) (.var xr) (.imm 1)) fun (sh, ()) =>
  .let_ (op1 (.trunc 64 8) (.var sh)) fun (lo, ()) =>
  .store (.var lo) (.var p) (
  .let_ (op1 (.neg i64) (.var sh)) fun (ng, ()) =>
  .ret (.var ng, ()))⟩

/-- Diamond branch with `cmp ult` → `jcc` and parameterized join block. -/
@[expose] def fnDiamond : Fn := ⟨"diamond", [i64, i64], [i64], fun _ _ (a, b, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) =>
      .let_ (op2 (.add i64) (.var r) (.imm 1)) fun (r1, ()) => .ret (.var r1, ())) .nil)
    (fun (join, ()) =>
      .let_ (op2 (.ult i64) (.var a) (.var b)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.sub i64) (.var b) (.var a)) fun (d, ()) => .jump join (.var d, ()))
        (.let_ (op2 (.sub i64) (.var a) (.var b)) fun (d, ()) => .jump join (.var d, ())))⟩

/-- Multi-block triangular sum loop (`n + (n-1) + … + 1`) exercising flags and back-edge. -/
@[expose] def fnTriSum : Fn := ⟨"triSum", [i64], [i64], fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
      .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
      .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c, ()) =>
      .jnz (.var c) (.jump loop (.var i', .var acc', ())) (.ret (.var acc', ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))⟩

/-- Helper callee: `inc(y) = y + 1`. -/
@[expose] def fnInc : Fn := ⟨"inc", [i64], [i64], fun _ _ (y, ()) =>
  .let_ (op2 (.add i64) (.var y) (.imm 1)) fun (r, ()) => .ret (.var r, ())⟩

/-- Caller invoking `inc` twice with 4 live values (forces callee-saved + stack slots). -/
@[expose] def fnCallSlots : Fn := ⟨"callSlots", [i64, i64, i64], [i64], fun _ _ (a, b, c, ()) =>
  .let_ (op2 (.add i64) (.var a) (.var b)) fun (ab, ()) =>
  .let_ (op2 (.xor i64) (.var b) (.var c)) fun (bc, ()) =>
  .let_ (op2 (.sub i64) (.var c) (.var a)) fun (ca, ()) =>
  .call "inc" (as := [i64]) (bs := [i64]) (.var a, ()) fun (r1, ()) =>
  .call "inc" (as := [i64]) (bs := [i64]) (.var r1, ()) fun (r2, ()) =>
  .let_ (op2 (.add i64) (.var r2) (.var ab)) fun (t1, ()) =>
  .let_ (op2 (.add i64) (.var t1) (.var bc)) fun (t2, ()) =>
  .let_ (op2 (.add i64) (.var t2) (.var ca)) fun (t3, ()) =>
  .let_ (op2 (.add i64) (.var t3) (.var b)) fun (t4, ()) =>
  .ret (.var t4, ())⟩

/-- Compact caller calling `inc` with a live value across the call (for linked `FnSpec` proof). -/
@[expose] def fnCallPair : Fn := ⟨"callPair", [i64, i64], [i64], fun _ _ (a, b, ()) =>
  .call "inc" (as := [i64]) (bs := [i64]) (.var a, ()) fun (r, ()) =>
  .let_ (op2 (.add i64) (.var r) (.var b)) fun (s, ()) =>
  .ret (.var s, ())⟩

@[expose] def extInc : Rega.Ext := { callees := [("inc", [i64], [i64])] }

/-! ## 3. `#guard` Compilation Checks with `Spill.hints` on `.linkReg` and `.stack` -/

private meta def hasNative {A : Arch} (c : List (Instr A)) : Bool :=
  c.any fun | .native _ => true | _ => false

private meta def lowerWithSpill (A : Arch) (P : VllPolicy A) (E : Rega.Ext) (f : Fn) :
    Except String (List (Instr A)) :=
  vllLowerFn A P (Spill.hints (vllIsa A P) f) E f

#guard match lowerWithSpill miniArch miniPolicy {} fnArithMem with
  | .ok c => !c.isEmpty && !hasNative c &&
      c.any (fun | .load .. => true | _ => false) &&
      c.any (fun | .store .. => true | _ => false)
  | .error _ => false

#guard match lowerWithSpill miniArch miniPolicy {} fnDiamond with
  | .ok c => !c.isEmpty && !hasNative c &&
      c.any (fun | .cmp .. => true | _ => false) &&
      c.any (fun | .jcc .. => true | _ => false)
  | .error _ => false

#guard match lowerWithSpill miniArch miniPolicy {} fnTriSum with
  | .ok c => !c.isEmpty && !hasNative c &&
      c.any (fun | .cmp .. => true | _ => false) &&
      c.any (fun | .jcc .. => true | _ => false)
  | .error _ => false

#guard match lowerWithSpill miniArch miniPolicy {} fnInc with
  | .ok c => !c.isEmpty && !hasNative c
  | .error _ => false

#guard match lowerWithSpill miniArch miniPolicy extInc fnCallSlots with
  | .ok c => !c.isEmpty && !hasNative c &&
      c.any (fun | .call "inc" => true | _ => false) &&
      c.any (fun | .slotSt .. => true | _ => false) &&
      c.any (fun | .slotLd .. => true | _ => false)
  | .error _ => false

#guard match lowerWithSpill miniArch miniPolicy extInc fnCallPair with
  | .ok c => !c.isEmpty && !hasNative c &&
      c.any (fun | .call "inc" => true | _ => false)
  | .error _ => false

#guard (Spill.hints miniIsa fnCallSlots).totalSlots > 0

#guard (lowerWithSpill miniStackArch miniStackPolicy {} fnArithMem).isOk
#guard (lowerWithSpill miniStackArch miniStackPolicy {} fnDiamond).isOk
#guard (lowerWithSpill miniStackArch miniStackPolicy {} fnTriSum).isOk
#guard (lowerWithSpill miniStackArch miniStackPolicy extInc fnCallSlots).isOk
#guard (lowerWithSpill miniStackArch miniStackPolicy extInc fnCallPair).isOk

/-! ## 4. Kernel-Verified End-to-End `vllLowerFn_correct` → `Target.FnSpec` -/

@[expose] def trieOf {α : Type} (xs : List (Nat × α)) : Trie α :=
  xs.foldl (fun t (k, v) => t.insert k v) .empty

@[expose] def okCode {A : Arch} (e : Except String (List (Instr A))) : List (Instr A) :=
  match e with | .ok c => c | .error _ => []

private theorem okCode_eq {A : Arch} {e : Except String (List (Instr A))} (h : e.isOk = true) :
    e = .ok (okCode e) := by
  cases e with
  | error _ => cases h
  | ok _ => rfl

@[expose] def hintsArithMem : Hints MiniReg Empty MiniCond where
  dest := trieOf [(3, .gpr .r0), (4, .gpr .r0), (5, .gpr .r0), (6, .gpr .r0),
    (7, .gpr .r0), (8, .gpr .r0), (9, .gpr .r1), (10, .gpr .r0)]
  pre := trieOf [(0, { clearFlags := false, moves := [.mov .r3 .r0] })]
  deferLea := trieOf [(2, true)]

@[expose] def hintsDiamond : Hints MiniReg Empty MiniCond where
  dest := trieOf [(2, .flag .ult), (3, .gpr .r0), (4, .gpr .r0), (6, .gpr .r0)]
  entry := trieOf [(0, { live := [], ploc := [.gpr .r0] })]
  deferJnz := trieOf [(0, true)]

@[expose] def hintsTriSum : Hints MiniReg Empty MiniCond where
  dest := trieOf [(3, .gpr .r1), (4, .gpr .r0), (5, .flag .ne)]
  entry := trieOf [(0, { live := [], ploc := [.gpr .r0, .gpr .r1] })]
  invertJnz := trieOf [(4, true)]
  deferJnz := trieOf [(3, true)]

@[expose] def hintsInc : Hints MiniReg Empty MiniCond where
  dest := trieOf [(1, .gpr .r0)]

@[expose] def hintsCallSlots : Hints MiniReg Empty MiniCond where
  dest := trieOf [(3, .gpr .r1), (4, .gpr .r3), (5, .gpr .r2),
    (8, .gpr .r0), (9, .gpr .r0), (10, .gpr .r0), (11, .gpr .r0)]
  pre := trieOf [
    (0, { clearFlags := false, moves := [.mov .s0 .r1] }),
    (3, { clearFlags := false, moves := [.st 2 .r2, .st 1 .r3, .st 0 .r1] }),
    (5, { clearFlags := false, moves := [.ld .r1 0] }),
    (6, { clearFlags := false, moves := [.ld .r1 1] }),
    (7, { clearFlags := false, moves := [.ld .r2 2] })]
  deferLea := trieOf [(5, true), (6, true), (7, true)]
  nslots := 3
  saved := [.s0]

@[expose] def codeArithMem : List (Instr miniArch) :=
  okCode (vllLowerFn miniArch miniPolicy hintsArithMem {} fnArithMem)

@[expose] def codeDiamond : List (Instr miniArch) :=
  okCode (vllLowerFn miniArch miniPolicy hintsDiamond {} fnDiamond)

@[expose] def codeTriSum : List (Instr miniArch) :=
  okCode (vllLowerFn miniArch miniPolicy hintsTriSum {} fnTriSum)

@[expose] def codeInc : List (Instr miniArch) :=
  okCode (vllLowerFn miniArch miniPolicy hintsInc {} fnInc)

@[expose] def codeCallSlots : List (Instr miniArch) :=
  okCode (vllLowerFn miniArch miniPolicy hintsCallSlots extInc fnCallSlots)

@[expose] def codeTriSumStack : List (Instr miniStackArch) :=
  okCode (vllLowerFn miniStackArch miniStackPolicy hintsTriSum {} fnTriSum)

theorem arithMem_wf : fnArithMem.Wf := by unfold Fn.Wf; t_wf_reify
theorem diamond_wf : fnDiamond.Wf := by unfold Fn.Wf; t_wf_reify
theorem triSum_wf : fnTriSum.Wf := by unfold Fn.Wf; t_wf_reify
theorem inc_wf : fnInc.Wf := by unfold Fn.Wf; t_wf_reify
theorem callSlots_wf : fnCallSlots.Wf := by unfold Fn.Wf; t_wf_reify

theorem arithMem_lower :
    vllLowerFn miniArch miniPolicy hintsArithMem {} fnArithMem = .ok codeArithMem :=
  okCode_eq rfl

theorem diamond_lower :
    vllLowerFn miniArch miniPolicy hintsDiamond {} fnDiamond = .ok codeDiamond :=
  okCode_eq rfl

theorem triSum_lower :
    vllLowerFn miniArch miniPolicy hintsTriSum {} fnTriSum = .ok codeTriSum :=
  okCode_eq rfl

theorem inc_lower :
    vllLowerFn miniArch miniPolicy hintsInc {} fnInc = .ok codeInc :=
  okCode_eq rfl

theorem callSlots_lower :
    vllLowerFn miniArch miniPolicy hintsCallSlots extInc fnCallSlots = .ok codeCallSlots :=
  okCode_eq rfl

theorem triSumStack_lower :
    vllLowerFn miniStackArch miniStackPolicy hintsTriSum {} fnTriSum = .ok codeTriSumStack :=
  okCode_eq rfl

@[expose] def hostArithMem : VllHost miniArch :=
  mkVllHost miniArch codeArithMem (by decide)

@[expose] def hostDiamond : VllHost miniArch :=
  mkVllHost miniArch codeDiamond (by decide)

@[expose] def hostTriSum : VllHost miniArch :=
  mkVllHost miniArch codeTriSum (by decide)

@[expose] def hostCallSlots : VllHost miniArch :=
  mkVllHost miniArch (codeInc ++ codeCallSlots) (by decide)

@[expose] def hostTriSumStack : VllHost miniStackArch :=
  mkVllHost miniStackArch codeTriSumStack (by decide)

private theorem miniHooksNoLab : VllHooksNoLab miniArch miniPolicy.hooks where
  vmov _ d _ := d.elim
  vmovi _ d _ _ _ := d.elim
  vslotSt _ _ s := s.elim
  vslotLd _ d _ := d.elim
  vop _ _ _ _ _ _ h := nomatch h
  vload _ d _ _ _ _ := d.elim
  vstore _ s _ _ _ _ := s.elim

private theorem miniStackHooksNoLab : VllHooksNoLab miniStackArch miniStackPolicy.hooks where
  vmov _ d _ := d.elim
  vmovi _ d _ _ _ := d.elim
  vslotSt _ _ s := s.elim
  vslotLd _ d _ := d.elim
  vop _ _ _ _ _ _ h := nomatch h
  vload _ d _ _ _ _ := d.elim
  vstore _ s _ _ _ _ := s.elim

private theorem head_inc_ne_callSlots {l : Sym}
    (h1 : l = "inc" ∨ ∃ j, l = Rega.lname "inc" j)
    (h2 : l = "callSlots" ∨ ∃ j, l = Rega.lname "callSlots" j) : False := by
  have hc1 : l.toList.head? = some 'i' := by
    rcases h1 with rfl | ⟨j, rfl⟩
    · rfl
    · simp [Rega.lname, String.toList_append]
  have hc2 : l.toList.head? = some 'c' := by
    rcases h2 with rfl | ⟨j, rfl⟩
    · rfl
    · simp [Rega.lname, String.toList_append]
  rw [hc1] at hc2
  cases hc2

private theorem hostCallSlots_labelsUnique : miniTarget.LabelsUnique hostCallSlots := by
  intro i j l hi hj
  have hi' : (codeInc ++ codeCallSlots)[i]? = some (.label l) := hi
  have hj' : (codeInc ++ codeCallSlots)[j]? = some (.label l) := hj
  by_cases hi1 : i < codeInc.length <;> by_cases hj1 : j < codeInc.length
  · rw [List.getElem?_append_left hi1] at hi'
    rw [List.getElem?_append_left hj1] at hj'
    exact Rega.lowerFn_labelsUnique miniLabelClean inc_lower i j l hi' hj'
  · rw [List.getElem?_append_left hi1] at hi'
    rw [List.getElem?_append_right (Nat.le_of_not_lt hj1)] at hj'
    exact absurd (vllLowerFn_label_mem miniArch miniPolicy miniHooksNoLab callSlots_lower hj')
      (fun h2 => head_inc_ne_callSlots
        (vllLowerFn_label_mem miniArch miniPolicy miniHooksNoLab inc_lower hi') h2)
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi1)] at hi'
    rw [List.getElem?_append_left hj1] at hj'
    exact absurd (vllLowerFn_label_mem miniArch miniPolicy miniHooksNoLab callSlots_lower hi')
      (fun h2 => head_inc_ne_callSlots
        (vllLowerFn_label_mem miniArch miniPolicy miniHooksNoLab inc_lower hj') h2)
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi1)] at hi'
    rw [List.getElem?_append_right (Nat.le_of_not_lt hj1)] at hj'
    have heq := Rega.lowerFn_labelsUnique miniLabelClean callSlots_lower
      (i - codeInc.length) (j - codeInc.length) l hi' hj'
    omega

theorem arithMem_correct (Γ : Env) :
    miniTarget.FnSpec hostArithMem fnArithMem.name (Func.spec Γ fnArithMem.body) 16 0 :=
  vllLowerFn_correct miniArch miniArch_wf miniPolicy hostArithMem hintsArithMem {} fnArithMem
    Γ 16 0 (fun _ => 0) (k₀ := 0) arithMem_wf arithMem_lower ⟨[], List.append_nil _⟩
    (vllLowerFn_labelsUnique miniArch miniArch_wf miniPolicy miniHooksNoLab arithMem_lower _)
    (by decide) (by decide) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

theorem diamond_correct (Γ : Env) :
    miniTarget.FnSpec hostDiamond fnDiamond.name (Func.spec Γ fnDiamond.body) 16 0 :=
  vllLowerFn_correct miniArch miniArch_wf miniPolicy hostDiamond hintsDiamond {} fnDiamond
    Γ 16 0 (fun _ => 0) (k₀ := 0) diamond_wf diamond_lower ⟨[], List.append_nil _⟩
    (vllLowerFn_labelsUnique miniArch miniArch_wf miniPolicy miniHooksNoLab diamond_lower _)
    (by decide) (by decide) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

theorem triSum_correct (Γ : Env) :
    miniTarget.FnSpec hostTriSum fnTriSum.name (Func.spec Γ fnTriSum.body) 16 0 :=
  vllLowerFn_correct miniArch miniArch_wf miniPolicy hostTriSum hintsTriSum {} fnTriSum
    Γ 16 0 (fun _ => 0) (k₀ := 0) triSum_wf triSum_lower ⟨[], List.append_nil _⟩
    (vllLowerFn_labelsUnique miniArch miniArch_wf miniPolicy miniHooksNoLab triSum_lower _)
    (by decide) (by decide) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

theorem inc_correct (Γ : Env) :
    miniTarget.FnSpec hostCallSlots fnInc.name (Func.spec Γ fnInc.body) 16 0 :=
  vllLowerFn_correct miniArch miniArch_wf miniPolicy hostCallSlots hintsInc {} fnInc
    Γ 16 0 (fun _ => 0) (k₀ := 0) inc_wf inc_lower ⟨codeCallSlots, rfl⟩ hostCallSlots_labelsUnique
    (by decide) (by decide) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

/-- End-to-end linked caller+callee soundness on `miniTarget`: `fnCallSlots` makes two calls to
`fnInc` while keeping 4 live values across calls via 3 stack slots and callee-saved `.s0`. -/
theorem callSlots_correct (Γ : Env) (hΓ : Γ "inc" [i64] [i64] = Func.spec Γ fnInc.body) :
    miniTarget.FnSpec hostCallSlots fnCallSlots.name (Func.spec Γ fnCallSlots.body) 64 0 := by
  refine vllLowerFn_correct miniArch miniArch_wf miniPolicy hostCallSlots hintsCallSlots extInc
    fnCallSlots Γ 64 0 (fun _ => 16) (k₀ := codeInc.length) callSlots_wf callSlots_lower
    ⟨[], by simp [hostCallSlots, mkVllHost]⟩ hostCallSlots_labelsUnique
    (by decide) (by decide) ?_ (fun _ h => nomatch h)
  intro g as bs hg
  simp only [extInc, List.mem_singleton, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl, rfl⟩ := hg
  refine ⟨?_, by decide⟩
  rw [hΓ]
  exact inc_correct Γ

/-- End-to-end loop soundness on `.stack` return convention (`miniStackTarget` + `writeSubX64`). -/
theorem triSum_stack_correct (Γ : Env) :
    miniStackTarget.FnSpec hostTriSumStack fnTriSum.name (Func.spec Γ fnTriSum.body) 8 0 :=
  vllLowerFn_correct miniStackArch miniStackArch_wf miniStackPolicy hostTriSumStack hintsTriSum {}
    fnTriSum Γ 8 0 (fun _ => 0) (k₀ := 0) triSum_wf triSumStack_lower ⟨[], List.append_nil _⟩
    (vllLowerFn_labelsUnique miniStackArch miniStackArch_wf miniStackPolicy miniStackHooksNoLab
      triSumStack_lower _)
    (by decide) (by decide) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)

end LeanQbeTest.T.VllRegaInstTest

/-! ## 5. Standard-Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Vll.vllCoreOp_spec
#print axioms LeanQbe.T.Vll.vllCoreLoad_spec
#print axioms LeanQbe.T.Vll.vllCoreLoad_zx_zext
#print axioms LeanQbe.T.Vll.vllCoreLoad_zx_zero32
#print axioms LeanQbe.T.Vll.vllCoreStore_spec
#print axioms LeanQbe.T.Vll.vllCoreOp_noLab
#print axioms LeanQbe.T.Vll.vllCoreLoad_noLab
#print axioms LeanQbe.T.Vll.vllCoreStore_noLab
#print axioms LeanQbe.T.Vll.vllEmptyVecTarget
#print axioms LeanQbe.T.Vll.vllGprTarget
#print axioms LeanQbe.T.Vll.vllFrameSpecWith
#print axioms LeanQbe.T.Vll.vllFrameTargetWith
#print axioms LeanQbe.T.Vll.vllTarget
#print axioms LeanQbe.T.Vll.vllLowerFn_correct
#print axioms LeanQbe.T.Vll.vllLabelClean
#print axioms LeanQbe.T.Vll.vllLabelClean_core
#print axioms LeanQbe.T.Vll.vllLowerFn_labelsUnique
#print axioms LeanQbeTest.T.VllRegaInstTest.miniArch_wf
#print axioms LeanQbeTest.T.VllRegaInstTest.miniStackArch_wf
#print axioms LeanQbeTest.T.VllRegaInstTest.arithMem_correct
#print axioms LeanQbeTest.T.VllRegaInstTest.diamond_correct
#print axioms LeanQbeTest.T.VllRegaInstTest.triSum_correct
#print axioms LeanQbeTest.T.VllRegaInstTest.inc_correct
#print axioms LeanQbeTest.T.VllRegaInstTest.callSlots_correct
#print axioms LeanQbeTest.T.VllRegaInstTest.triSum_stack_correct
