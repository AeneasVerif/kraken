module

public import LeanQbe.T.Unified.CfgRecoveryBridge
public import LeanQbe.T.Logic.ProofKit
public import LeanQbe.T.BedrockWord.Core
import LeanQbe.T.BedrockWord.Ops
import LeanQbe.T.OpsLemmas
import LeanQbe.T.MainLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.Unified.CfgRecovery
public meta import LeanQbe.T.Unified.CfgContify
public meta import LeanQbe.T.BedrockWord.Core

/-!
# Stage-2 Generic Fixtures, End-to-End Proofs & Isolation Audit (`BedrockCfgStage2Test`)

Arch-free Stage-2 test suite and shared fixtures for `LeanQbe.T.Unified.CfgRecoveryBridge`
(paired with `BedrockCfgStage2X64Test` and `BedrockCfgStage2Arm64Test`):

1. **Example 1 (`ex1`):** 3-bit tagging, flagless `OpCode.select`, speculative `guarded` bailout
   to residual cold block `ex1_cold` in `wRes`.
2. **Example 2a (`ex2a`):** Bounded stride-8 jump table (`EdgeKind.strideTable`).
3. **Example 2b (`ex2b`):** Dual-return `rp + 8` contified helper + caller multi-region DAG.
4. **Example 3 (`ex3`):** `threadedVM` indirect dispatch over the SAME `CodeMap` via BOTH
   `EdgeKind.memTableRo` (guarded by `WitRoOk`) AND `EdgeKind.memTableGuarded`.
5. **Example 6 (`ex6`):** Stage-1 `whileM` loop calling `.contified false` `raw_step` helper,
   flowing into mutual `even`/`odd` parity recursion.
6. Generic `TargetInit` runner helpers + MetaM arch-isolation audit (`0` Kraken/Amd64/Arm64 and
   `0` public `*Lemmas*` leaks in `LeanQbe.T.Unified.CfgRecoveryBridge`) + `check_std_axioms!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.BedrockCfgStage2Test

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Xcap
open LeanQbe.T.BedrockWord
open LeanQbe.T.Unified
open LeanQbe.T.ProofKit

def mkEntry (nm : Sym) (addr : BitVec 64) (b : BlockP) : CodeEntry :=
  ⟨nm, addr, reifyBlock b⟩

/-! ## §1. Example 1: Tagging, Flagless `select`, Speculative `guarded` + Cold `wRes` -/

def bEx1Entry : BlockP := fun _ r =>
  .letOp2 (.cmp .eq i64) (.var r.r1) (.imm 0#64) fun c =>
  .codeAddr "ex1_hot_a" fun pa =>
  .codeAddr "ex1_hot_b" fun pb =>
  .letOp3 (.select i64) (.var c) (.var pa) (.var pb) fun tgt =>
  .ijmp (.var tgt) r.keep

theorem bEx1Entry_wf : bEx1Entry.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .codeAddr _ fun _ _ => .codeAddr _ fun _ _ => ?_
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip])) (.cons (.var (by simp [Tup.zip]))
    (.cons (.var (by simp [Tup.zip])) .nil)))) fun _ _ => ?_
  exact .ijmp (.var (by simp [Tup.zip]))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bEx1HotA : BlockP := fun _ r =>
  .codeAddr "ex1_join" fun pj =>
  .letOp2 (.or i64) (.var pj) (.imm 1#64) fun tagged =>
  .letOp2 (.and i64) (.var tagged) (.imm (~~~7#64)) fun untagged =>
  .ijmp (.var untagged) r.keep

theorem bEx1HotA_wf : bEx1HotA.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .codeAddr _ fun _ _ => ?_
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip])) (.cons (.imm _) .nil))) fun _ _ => ?_
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip])) (.cons (.imm _) .nil))) fun _ _ => ?_
  exact .ijmp (.var (by simp [Tup.zip]))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bEx1Join : BlockP := fun _ r => .ijmp (.var r.r2) r.keep

theorem bEx1Join_wf : bEx1Join.Wf := by
  intro V₁ V₂ r₁ r₂
  exact .ijmp (.var (by simp [Tup.zip, RegsV.toTup]))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmEx1 : CodeMap :=
  [ mkEntry "ex1_entry" 0#64 bEx1Entry,
    mkEntry "ex1_hot_a" 8#64 bEx1HotA,
    mkEntry "ex1_hot_b" 16#64 (fun _ _ => .halt (.imm 7#64)),
    mkEntry "ex1_join" 24#64 bEx1Join,
    mkEntry "ex1_fast" 32#64 (fun _ _ => .halt (.imm 42#64)),
    mkEntry "ex1_cold" 40#64 (fun _ r => .halt (.var r.r3)) ]

def ex1Rw : RegionWitness :=
  { name := "ex1_main"
    entryPc := 0#64
    abi := .retEnvelope
    tree := [.leaf 0#64, .leaf 8#64, .leaf 16#64, .leaf 24#64, .leaf 32#64]
    edges := [ ⟨0#64, [], .select 8#64 16#64⟩,
               ⟨8#64, [], .direct 24#64⟩,
               ⟨24#64, [], .guarded [32#64]⟩ ]
    retainFallbacks := false }

def ex1Wit : CfgWitness := ⟨[ex1Rw]⟩
def ex1Fns : List Fn := [liftRegion cmEx1 ex1Rw]
def ex1Res : CodeMap := [mkEntry "ex1_cold" 40#64 (fun _ r => .halt (.var r.r3))]

theorem ex1_check : ex1Wit.check cmEx1 = true := by
  dsimp only [ex1Wit, CfgWitness.check, CfgWitness.checkAux, RegionWitness.check,
    RegionWitness.allPcs]
  have h1 : ex1Rw.tree.flatMap GroupTree.allPcs = [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [ex1Rw, GroupTree.allPcs]
  have h2 : List.flatMap RegionWitness.allPcs [ex1Rw] = [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [RegionWitness.allPcs, h1]
  rw [h1, h2]
  exact Eq.refl true

theorem ex1_res_eq : residualCodeMap cmEx1 ex1Wit = ex1Res := by
  have h1 : List.flatMap RegionWitness.allPcs
      (List.filter (fun r => !r.retainFallbacks) ex1Wit.regions) =
      [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [ex1Wit, ex1Rw, RegionWitness.allPcs, GroupTree.allPcs]
  dsimp only [residualCodeMap]
  rw [h1]
  simp [ex1Wit, ex1Rw, cmEx1, ex1Res, mkEntry]

theorem ex1_lift_eq : checkAndLiftWitness cmEx1 ex1Wit = .ok (ex1Fns, ex1Res) := by
  dsimp only [checkAndLiftWitness]
  rw [ex1_check, ex1_res_eq]
  rfl

theorem ex1_drop_pc :
    ∀ rw ∈ ex1Wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → pc ≠ 40#64 := by
  intro rw hRw _ pc hPc _ h40
  simp only [ex1Wit, List.mem_singleton] at hRw
  subst hRw; subst h40
  simp [ex1Rw, RegionWitness.allPcs, GroupTree.allPcs] at hPc

theorem ex1_res_closed {T : Target} (C : AddrCodec T) (host : T.mach.Host) (lt : LegalTarget)
    (nX : Nat) (H_mach : T.mach.State → Prop) (bound : Sym → Nat)
    (hCold : ∀ pc st, (pc = 40#64 → st.regs.r3 = 42#64) →
      embedTargetSafe T C host lt (fun c _ => c = 42#64) nX H_mach
        (witEntries ex1Wit bound) (fun _ _ => True) (fun pc st => pc = 40#64 → st.regs.r3 = 42#64)
        pc st) :
    SpecsClosed ex1Res cmEx1.symEnv
      (embedTargetSafe T C host lt (fun c _ => c = 42#64) nX H_mach
        (witEntries ex1Wit bound) (fun _ _ => True)
        (fun pc st => pc = 40#64 → st.regs.r3 = 42#64)) (fun c _ => c = 42#64) := by
  intro pc b hlu st hbp
  dsimp only [ex1Res, CodeMap.lookupAddr, mkEntry] at hlu
  split at hlu
  · rename_i hEq
    cases hlu
    have hpc : 40#64 = pc := beq_iff_eq.1 hEq
    subst hpc
    dsimp only [BlockFlat.wp, denoteArg, pushRegsV, Regs.toRegsV, RegsV.toTup, pushTup] at hbp
    exact hCold 40#64 st (fun _ => hbp)
  · cases hlu

theorem ex1_cm_wp_hot (r₀ : Regs) (m : Mem 64) (h1 : r₀.r1 = 1#64) :
    cmEx1.wp (fun c _ => c = 7#64 ∨ c = 42#64) 0#64 ⟨r₀, m⟩ := by
  intro Ψ hCl
  have h16 : cmEx1.lookupAddr 16#64 = some (reifyBlock fun _ _ => .halt (.imm 7#64)) := by
    t_kernel_rfl
  have hDone : Ψ 16#64 ⟨r₀, m⟩ := hCl 16#64 _ h16 ⟨r₀, m⟩ (Or.inl rfl)
  have hReg : ({ r₀ with r1 := 1#64 } : Regs) = r₀ := by
    cases r₀; simp at h1; subst h1; rfl
  refine hCl.applyP (by t_kernel_rfl : cmEx1.lookupAddr 0#64 = some (reifyBlock bEx1Entry))
    bEx1Entry_wf ?_
  dsimp only [bEx1Entry, BlockP.wp, BlockB.wp, op2, op3, Op.wp, OpCode.wp, evalOpCode,
    liftCmp, CmpOp.evalBits, CmpOp.evalBool, Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
  rw [h1]
  refine ⟨8#64, by t_kernel_rfl, 16#64, by t_kernel_rfl, ?_⟩
  have hEq0 : (1#64 == 0#64) = false := by decide
  simpa [hEq0, hReg] using hDone

theorem ex1_cm_wp_fast (r₀ : Regs) (m : Mem 64) (h1 : r₀.r1 = 0#64) (h2 : r₀.r2 = 32#64) :
    cmEx1.wp (fun c _ => c = 7#64 ∨ c = 42#64) 0#64 ⟨r₀, m⟩ := by
  intro Ψ hCl
  have h32 : cmEx1.lookupAddr 32#64 = some (reifyBlock fun _ _ => .halt (.imm 42#64)) := by
    t_kernel_rfl
  have hDone : Ψ 32#64 ⟨r₀, m⟩ := hCl 32#64 _ h32 ⟨r₀, m⟩ (Or.inr rfl)
  have hReg2 : ({ r₀ with r2 := 32#64 } : Regs) = r₀ := by
    cases r₀; simp at h2; subst h2; rfl
  have hReg1 : ({ r₀ with r1 := 0#64 } : Regs) = r₀ := by
    cases r₀; simp at h1; subst h1; rfl
  have hJ : Ψ 24#64 ⟨r₀, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx1.lookupAddr 24#64 = some (reifyBlock bEx1Join))
      bEx1Join_wf ?_
    dsimp only [bEx1Join, BlockP.wp, BlockB.wp, Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval]
    rw [h2]; simpa [hReg2] using hDone
  have hA : Ψ 8#64 ⟨r₀, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx1.lookupAddr 8#64 = some (reifyBlock bEx1HotA))
      bEx1HotA_wf ?_
    dsimp only [bEx1HotA, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, lift2,
      Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
    refine ⟨24#64, by t_kernel_rfl, ?_⟩
    have hTag : ((24#64 ||| 1#64) &&& ~~~7#64) = 24#64 := by decide
    have hId : ({ r₀ with sp := r₀.sp } : Regs) = r₀ := by cases r₀; rfl
    simpa [hTag, hId] using hJ
  refine hCl.applyP (by t_kernel_rfl : cmEx1.lookupAddr 0#64 = some (reifyBlock bEx1Entry))
    bEx1Entry_wf ?_
  dsimp only [bEx1Entry, BlockP.wp, BlockB.wp, op2, op3, Op.wp, OpCode.wp, evalOpCode,
    liftCmp, CmpOp.evalBits, CmpOp.evalBool, Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
  rw [h1]
  refine ⟨8#64, by t_kernel_rfl, 16#64, by t_kernel_rfl, ?_⟩
  have hEq0 : (0#64 == 0#64) = true := by decide
  simpa [hEq0, hReg1] using hA

/-! ## §2. Example 2a: Bounded Stride-8 Padded Jump Table -/

def bEx2aEntry : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.var r.r1) (.imm 2#64) fun c =>
  .jnz (.var c)
    (.letOp2 (.shl i64) (.var r.r1) (.imm 3#64) fun off =>
     .codeAddr "ex2a_pad0" fun base =>
     .letOp2 (.add i64) (.var base) (.var off) fun tgt =>
     .ijmp (.var tgt) r.keep)
    (.halt (.imm 99#64))

theorem bEx2aEntry_wf : bEx2aEntry.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .jnz (.var (by simp [Tup.zip])) ?_ (.halt (.imm _))
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .codeAddr _ fun _ _ => ?_
  refine .let_ (.mk _ (.cons (.var (by simp)) (.cons (.var (by simp [Tup.zip])) .nil)))
    fun _ _ => ?_
  exact .ijmp (.var (by simp [Tup.zip]))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmEx2a : CodeMap :=
  [ mkEntry "ex2a_entry" 0#64 bEx2aEntry,
    mkEntry "ex2a_pad0" 8#64 (fun _ _ => .halt (.imm 10#64)),
    mkEntry "ex2a_pad1" 16#64 (fun _ _ => .halt (.imm 20#64)) ]

def ex2aRw : RegionWitness :=
  { name := "ex2a_stride"
    entryPc := 0#64
    abi := .retEnvelope
    tree := [.leaf 0#64, .leaf 8#64, .leaf 16#64]
    edges := [⟨0#64, [true], .strideTable 8#64 [8#64, 16#64] false⟩]
    retainFallbacks := false }

def ex2aWit : CfgWitness := ⟨[ex2aRw]⟩
def ex2aFns : List Fn := [liftRegion cmEx2a ex2aRw]

theorem ex2a_check : ex2aWit.check cmEx2a = true := by
  dsimp only [ex2aWit, CfgWitness.check, CfgWitness.checkAux, RegionWitness.check,
    RegionWitness.allPcs]
  have h1 : ex2aRw.tree.flatMap GroupTree.allPcs = [0#64, 8#64, 16#64] := by
    simp [ex2aRw, GroupTree.allPcs]
  have h2 : List.flatMap RegionWitness.allPcs [ex2aRw] = [0#64, 8#64, 16#64] := by
    simp [RegionWitness.allPcs, h1]
  rw [h1, h2]
  exact Eq.refl true

theorem ex2a_res_eq : residualCodeMap cmEx2a ex2aWit = [] := by
  have h1 : List.flatMap RegionWitness.allPcs
      (List.filter (fun r => !r.retainFallbacks) ex2aWit.regions) = [0#64, 8#64, 16#64] := by
    simp [ex2aWit, ex2aRw, RegionWitness.allPcs, GroupTree.allPcs]
  dsimp only [residualCodeMap]
  rw [h1]
  simp [ex2aWit, ex2aRw, cmEx2a, mkEntry]

theorem ex2a_lift_eq : checkAndLiftWitness cmEx2a ex2aWit = .ok (ex2aFns, []) := by
  dsimp only [checkAndLiftWitness]
  rw [ex2a_check, ex2a_res_eq]
  rfl

theorem ex2a_cm_wp_1 (r₀ : Regs) (m : Mem 64) (h1 : r₀.r1 = 1#64) :
    cmEx2a.wp (fun c _ => c = 10#64 ∨ c = 20#64 ∨ c = 99#64) 0#64 ⟨r₀, m⟩ := by
  intro Ψ hCl
  have h16 : cmEx2a.lookupAddr 16#64 = some (reifyBlock fun _ _ => .halt (.imm 20#64)) := by
    t_kernel_rfl
  have hDone : Ψ 16#64 ⟨r₀, m⟩ := hCl 16#64 _ h16 ⟨r₀, m⟩ (Or.inr (Or.inl rfl))
  have hReg : ({ r₀ with r1 := 1#64 } : Regs) = r₀ := by
    cases r₀; simp at h1; subst h1; rfl
  refine hCl.applyP (by t_kernel_rfl : cmEx2a.lookupAddr 0#64 = some (reifyBlock bEx2aEntry))
    bEx2aEntry_wf ?_
  dsimp only [bEx2aEntry, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode,
    liftCmp, CmpOp.evalBits, CmpOp.evalBool, lift2, Arg.val, Regs.toRegsV, RegsV.keep,
    RegsExpr.eval, vals]
  rw [h1]
  refine ⟨fun _ => ⟨8#64, by t_kernel_rfl, ?_⟩, fun hF => by
    have hUlt : BitVec.ult 1#64 2#64 = true := by decide
    simp [hUlt] at hF⟩
  have hTgt : (8#64 + (1#64 <<< (3#64 : BitVec 64).toNat % 64) : BitVec 64) = 16#64 := by decide
  simpa [hTgt, hReg] using hDone

/-! ## §3. Example 2b: Dual-Return `rp + 8` Contified Helper + Caller DAG -/

def bEx2bProbe : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.var r.r1) (.var r.r2) fun underflow =>
  .jnz (.var underflow)
    (.letOp2 (.add i64) (.var r.rp) (.imm 8#64) fun altRp =>
     .ijmp (.var altRp) r.keep)
    (.letOp2 (.sub i64) (.var r.r1) (.var r.r2) fun diff =>
     .ijmp (.var r.rp) { r.keep with rv := .var diff })

theorem bEx2bProbe_wf : bEx2bProbe.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
    (.cons (.var (by simp [Tup.zip, RegsV.toTup])) .nil)))
    fun _ _ => .jnz (.var (by simp [Tup.zip])) ?_ ?_
  · refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
      fun _ _ => .ijmp (.var (by simp [Tup.zip]))
        ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
         .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
         .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩
  · refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.var (by simp [Tup.zip, RegsV.toTup])) .nil))) fun _ _ =>
      .ijmp (.var (by simp [Tup.zip, RegsV.toTup]))
        ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
         .var (by simp [Tup.zip]), .var (by simp [Tup.zip, RegsV.toTup]),
         .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bEx2bCaller : BlockP := fun _ r =>
  .codeAddr "ex2b_ok" fun okPc =>
  .jmpSym "ex2b_probe" { r.keep with rp := .var okPc }

theorem bEx2bCaller_wf : bEx2bCaller.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .codeAddr _ fun _ _ => .codeAddr _ fun _ _ => .ijmp (.var (by simp [Tup.zip]))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmEx2b : CodeMap :=
  [ mkEntry "ex2b_probe" 0#64 bEx2bProbe,
    mkEntry "ex2b_caller" 8#64 bEx2bCaller,
    mkEntry "ex2b_ok" 16#64 (fun _ r => .halt (.var r.rv)),
    mkEntry "ex2b_err" 24#64 (fun _ _ => .halt (.imm 999#64)) ]

def ex2bProbeRw : RegionWitness :=
  { name := "ex2b_probe"
    entryPc := 0#64
    abi := .contified true
    tree := [.leaf 0#64]
    edges := [⟨0#64, [true], .contRet true⟩, ⟨0#64, [false], .contRet false⟩]
    retainFallbacks := false }

def ex2bCallerRw : RegionWitness :=
  { name := "ex2b_caller"
    entryPc := 8#64
    abi := .retEnvelope
    tree := [.leaf 8#64, .leaf 16#64, .leaf 24#64]
    edges := [⟨8#64, [], .contCall "ex2b_probe" 0#64 true 16#64 (some 24#64)⟩]
    retainFallbacks := false }

def ex2bWit : CfgWitness := ⟨[ex2bProbeRw, ex2bCallerRw]⟩
def ex2bFns : List Fn := [liftRegion cmEx2b ex2bProbeRw, liftRegion cmEx2b ex2bCallerRw]

theorem ex2b_check : ex2bWit.check cmEx2b = true := by
  dsimp only [ex2bWit, CfgWitness.check, CfgWitness.checkAux, RegionWitness.check,
    RegionWitness.allPcs]
  have h1 : ex2bProbeRw.tree.flatMap GroupTree.allPcs = [0#64] := by
    simp [ex2bProbeRw, GroupTree.allPcs]
  have h2 : ex2bCallerRw.tree.flatMap GroupTree.allPcs = [8#64, 16#64, 24#64] := by
    simp [ex2bCallerRw, GroupTree.allPcs]
  have htot : [ex2bProbeRw, ex2bCallerRw].flatMap RegionWitness.allPcs =
      [0#64, 8#64, 16#64, 24#64] := by
    simp [RegionWitness.allPcs, h1, h2]
  rw [htot, h1, h2]
  exact Eq.refl true

theorem ex2b_res_eq : residualCodeMap cmEx2b ex2bWit = [] := by
  have h1 : List.flatMap RegionWitness.allPcs
      (List.filter (fun r => !r.retainFallbacks) ex2bWit.regions) =
      [0#64, 8#64, 16#64, 24#64] := by
    simp [ex2bWit, ex2bProbeRw, ex2bCallerRw, RegionWitness.allPcs, GroupTree.allPcs]
  dsimp only [residualCodeMap]
  rw [h1]
  simp [ex2bWit, ex2bProbeRw, ex2bCallerRw, cmEx2b, mkEntry]

theorem ex2b_lift_eq : checkAndLiftWitness cmEx2b ex2bWit = .ok (ex2bFns, []) := by
  dsimp only [checkAndLiftWitness]
  rw [ex2b_check, ex2b_res_eq]
  rfl

theorem ex2b_cm_wp (r₀ : Regs) (m : Mem 64) :
    cmEx2b.wp (fun c _ => c = (r₀.r1 - r₀.r2) ∨ c = 999#64) 8#64 ⟨r₀, m⟩ := by
  intro Ψ hCl
  have h16 : cmEx2b.lookupAddr 16#64 = some (reifyBlock fun _ r => .halt (.var r.rv)) := by
    t_kernel_rfl
  have h24 : cmEx2b.lookupAddr 24#64 = some (reifyBlock fun _ _ => .halt (.imm 999#64)) := by
    t_kernel_rfl
  have hOk : Ψ 16#64 ⟨{ r₀ with rp := 16#64, rv := r₀.r1 - r₀.r2 }, m⟩ :=
    hCl 16#64 _ h16 ⟨{ r₀ with rp := 16#64, rv := r₀.r1 - r₀.r2 }, m⟩ (Or.inl rfl)
  have hErr : Ψ 24#64 ⟨{ r₀ with rp := 16#64 }, m⟩ :=
    hCl 24#64 _ h24 ⟨{ r₀ with rp := 16#64 }, m⟩ (Or.inr rfl)
  have hProbe : Ψ 0#64 ⟨{ r₀ with rp := 16#64 }, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx2b.lookupAddr 0#64 = some (reifyBlock bEx2bProbe))
      bEx2bProbe_wf ?_
    dsimp only [bEx2bProbe, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, lift2,
      Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · have hAdd : (16#64 + 8#64 : BitVec 64) = 24#64 := by decide
      simpa [hAdd] using hErr
    · simpa using hOk
  refine hCl.applyP (by t_kernel_rfl : cmEx2b.lookupAddr 8#64 = some (reifyBlock bEx2bCaller))
    bEx2bCaller_wf ?_
  dsimp only [bEx2bCaller, BlockP.wp, BlockB.wp, CodeMap.symEnv, Arg.val,
    Regs.toRegsV, RegsV.keep, RegsExpr.eval]
  exact ⟨16#64, by t_kernel_rfl, 0#64, by t_kernel_rfl, hProbe⟩

/-! ## §4. Example 3: Shared `threadedVM` via BOTH `.memTableRo` and `.memTableGuarded` -/

def bEx3Dispatch : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.var r.r1) (.imm 2#64) fun c =>
  .jnz (.var c)
    (.letOp2 (.shl i64) (.var r.r1) (.imm 3#64) fun off =>
     .letOp2 (.add i64) (.imm 0x1000#64) (.var off) fun slot =>
     .load i64 (.var slot) fun tgt => .ijmp (.var tgt) r.keep)
    (.halt (.imm 99#64))

theorem bEx3Dispatch_wf : bEx3Dispatch.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .jnz (.var (by simp [Tup.zip])) ?_ (.halt (.imm _))
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .let_ (.mk _ (.cons (.imm _) (.cons (.var (by simp [Tup.zip])) .nil))) fun _ _ =>
    .load _ (.var (by simp [Tup.zip])) fun _ _ => .ijmp (.var (by simp [Tup.zip]))
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmEx3Vm : CodeMap :=
  [ mkEntry "ex3_dispatch" 0#64 bEx3Dispatch,
    mkEntry "ex3_op0" 8#64 (fun _ _ => .halt (.imm 100#64)),
    mkEntry "ex3_op1" 16#64 (fun _ _ => .halt (.imm 200#64)) ]

def ex3TableBytes : List UInt8 :=
  Int.toBytes 8 (8#64 : BitVec 64).toInt ++ Int.toBytes 8 (16#64 : BitVec 64).toInt

theorem ex3TableBytes_len : ex3TableBytes.length = 16 := rfl

def ex3RoRw : RegionWitness :=
  { name := "ex3_vm_ro"
    entryPc := 0#64
    abi := .retEnvelope
    tree := [.leaf 0#64, .leaf 8#64, .leaf 16#64]
    edges := [⟨0#64, [true], .memTableRo 0x1000#64 [8#64, 16#64] false⟩]
    retainFallbacks := false }

def ex3RoWit : CfgWitness := ⟨[ex3RoRw]⟩
def ex3RoFns : List Fn := [liftRegion cmEx3Vm ex3RoRw]

def ex3GuardedRw : RegionWitness :=
  { name := "ex3_vm_guarded"
    entryPc := 0#64
    abi := .retEnvelope
    tree := [.leaf 0#64, .leaf 8#64, .leaf 16#64]
    edges := [⟨0#64, [true], .memTableGuarded 0x1000#64 [8#64, 16#64]⟩]
    retainFallbacks := false }

def ex3GuardedWit : CfgWitness := ⟨[ex3GuardedRw]⟩
def ex3GuardedFns : List Fn := [liftRegion cmEx3Vm ex3GuardedRw]

theorem ex3_ro_check : ex3RoWit.check cmEx3Vm = true := by
  dsimp only [ex3RoWit, CfgWitness.check, CfgWitness.checkAux, RegionWitness.check,
    RegionWitness.allPcs]
  have h1 : ex3RoRw.tree.flatMap GroupTree.allPcs = [0#64, 8#64, 16#64] := by
    simp [ex3RoRw, GroupTree.allPcs]
  have h2 : List.flatMap RegionWitness.allPcs [ex3RoRw] = [0#64, 8#64, 16#64] := by
    simp [RegionWitness.allPcs, h1]
  have h3 : ex3RoRw.allPcs = [0#64, 8#64, 16#64] := by
    simp [RegionWitness.allPcs, h1]
  rw [h1, h2]
  dsimp only [ex3RoRw, checkGroupNodes, checkGroupNode, checkBlockLeaves, RegionWitness.roSafe]
  simp only [RegionWitness.allPcs, GroupTree.allPcs, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  exact Eq.refl true

theorem ex3_guarded_check : ex3GuardedWit.check cmEx3Vm = true := by
  dsimp only [ex3GuardedWit, CfgWitness.check, CfgWitness.checkAux, RegionWitness.check,
    RegionWitness.allPcs]
  have h1 : ex3GuardedRw.tree.flatMap GroupTree.allPcs = [0#64, 8#64, 16#64] := by
    simp [ex3GuardedRw, GroupTree.allPcs]
  have h2 : List.flatMap RegionWitness.allPcs [ex3GuardedRw] = [0#64, 8#64, 16#64] := by
    simp [RegionWitness.allPcs, h1]
  rw [h1, h2]
  exact Eq.refl true

theorem ex3_ro_res_eq : residualCodeMap cmEx3Vm ex3RoWit = [] := by
  have h1 : List.flatMap RegionWitness.allPcs
      (List.filter (fun r => !r.retainFallbacks) ex3RoWit.regions) = [0#64, 8#64, 16#64] := by
    simp [ex3RoWit, ex3RoRw, RegionWitness.allPcs, GroupTree.allPcs]
  dsimp only [residualCodeMap]
  rw [h1]
  simp [ex3RoWit, ex3RoRw, cmEx3Vm, mkEntry]

theorem ex3_guarded_res_eq : residualCodeMap cmEx3Vm ex3GuardedWit = [] := by
  have h1 : List.flatMap RegionWitness.allPcs
      (List.filter (fun r => !r.retainFallbacks) ex3GuardedWit.regions) =
      [0#64, 8#64, 16#64] := by
    simp [ex3GuardedWit, ex3GuardedRw, RegionWitness.allPcs, GroupTree.allPcs]
  dsimp only [residualCodeMap]
  rw [h1]
  simp [ex3GuardedWit, ex3GuardedRw, cmEx3Vm, mkEntry]

theorem ex3_ro_lift_eq : checkAndLiftWitness cmEx3Vm ex3RoWit = .ok (ex3RoFns, []) := by
  dsimp only [checkAndLiftWitness]
  rw [ex3_ro_check, ex3_ro_res_eq]
  rfl

theorem ex3_guarded_lift_eq :
    checkAndLiftWitness cmEx3Vm ex3GuardedWit = .ok (ex3GuardedFns, []) := by
  dsimp only [checkAndLiftWitness]
  rw [ex3_guarded_check, ex3_guarded_res_eq]
  rfl

private theorem ex3_tableMem_eq :
    storeMem (storeMem (∅ : Mem 64) i64 0x1000#64 (8#64 : BitVec 64)) i64 0x1008#64
        (16#64 : BitVec 64) =
      ex3TableBytes.At 0x1000#64 := by
  have hb8 : (Int.toBytes 8 (8#64 : BitVec 64).toInt).length = 8 := Int.toBytes_length _ _
  have ha : (0x1000#64 : BitVec 64) + BitVec.ofNat 64
      (Int.toBytes 8 (8#64 : BitVec 64).toInt).length = 0x1008#64 := by
    rw [hb8]; decide
  dsimp only [storeMem, Mem.storeInt, Mem.storeBytes, toBits, Ty.bytes, Ty.size, ex3TableBytes]
  simp only [BitVec.setWidth_eq]
  rw [List.At_append _ _ 0x1000#64 (by simp [Int.toBytes_length]), ha]
  ext k
  simp [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]

theorem ex3_witRoOk : WitRoOk ex3RoWit (ex3TableBytes.At 0x1000#64) := by
  intro rw hRw ew hew
  simp only [ex3RoWit, List.mem_singleton] at hRw
  subst hRw
  simp only [ex3RoRw, List.mem_singleton] at hew
  subst hew
  intro k hk
  rw [← ex3_tableMem_eq]
  match k, hk with
  | 0, _ =>
      have hneq : ∀ (i j : Nat), i < i64.bytes → j < i64.bytes →
          (0x1000#64 : BitVec 64) + BitVec.ofNat 64 j ≠ 0x1008#64 + BitVec.ofNat 64 i := by
        intro i j hi hj heq
        simp only [Ty.bytes, Ty.size] at hi hj
        have h2 := congrArg BitVec.toNat heq
        simp [BitVec.toNat_add] at h2
        omega
      have hStep := loadVal_storeMem_disjoint
        (storeMem (∅ : Mem 64) i64 0x1000#64 (8#64 : BitVec 64))
        i64 i64 0x1008#64 0x1000#64 (16#64 : BitVec 64) hneq
      simpa [Nat.mul_zero, BitVec.add_zero] using hStep.trans
        (loadVal_storeMem (∅ : Mem 64) i64 0x1000#64 (8#64 : BitVec 64) (by decide))
  | 1, _ =>
      have ha : (0x1000#64 : BitVec 64) + BitVec.ofNat 64 (8 * 1) = 0x1008#64 := by decide
      simpa [ha] using loadVal_storeMem
        (storeMem (∅ : Mem 64) i64 0x1000#64 (8#64 : BitVec 64)) i64 0x1008#64 (16#64 : BitVec 64)
        (by decide)
  | n + 2, h =>
      exfalso; dsimp only [List.length] at h; omega

theorem ex3_cm_wp_0 (r₀ : Regs) (h0 : r₀.r1 = 0#64) :
    cmEx3Vm.wp (fun c _ => c = 100#64 ∨ c = 200#64 ∨ c = 99#64) 0#64
      ⟨r₀, ex3TableBytes.At 0x1000#64⟩ := by
  intro Ψ hCl
  have h8 : cmEx3Vm.lookupAddr 8#64 = some (reifyBlock fun _ _ => .halt (.imm 100#64)) := by
    t_kernel_rfl
  have hDone : Ψ 8#64 ⟨r₀, ex3TableBytes.At 0x1000#64⟩ :=
    hCl 8#64 _ h8 ⟨r₀, ex3TableBytes.At 0x1000#64⟩ (Or.inl rfl)
  have hReg : ({ r₀ with r1 := 0#64 } : Regs) = r₀ := by
    cases r₀; simp at h0; subst h0; rfl
  refine hCl.applyP (by t_kernel_rfl : cmEx3Vm.lookupAddr 0#64 = some (reifyBlock bEx3Dispatch))
    bEx3Dispatch_wf ?_
  dsimp only [bEx3Dispatch, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode,
    liftCmp, CmpOp.evalBits, CmpOp.evalBool, lift2, Arg.val, Regs.toRegsV, RegsV.keep,
    RegsExpr.eval, vals]
  rw [h0]
  refine ⟨fun _ => ?_, fun hF => by
    have hUlt : BitVec.ult 0#64 2#64 = true := by decide
    simp [hUlt] at hF⟩
  have hSlot : (0x1000#64 + (0#64 : BitVec 64) <<< ((3#64 : BitVec 64).toNat % 64) : BitVec 64) =
      0x1000#64 := by decide
  have hLd : loadVal (ex3TableBytes.At 0x1000#64) i64 0x1000#64 = some 8#64 :=
    ex3_witRoOk ex3RoRw List.mem_cons_self _ List.mem_cons_self 0 (by decide)
  simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte]
  rw [hSlot]
  exact ⟨8#64, hLd, by simpa [hReg] using hDone⟩

/-! ## §5. Example 6: Stage-1 `whileM` (`contified false` `raw_step` + mutual `even`/`odd`) -/

def bEx6RawStep : BlockP := fun _ r =>
  .letOp2 (.sub i64) (.var r.r2) (.imm 1#64) fun r2' =>
  .letOp2 (.add i64) (.var r.rv) (.imm 1#64) fun rv' =>
  .ijmp (.var r.rp) { r.keep with r2 := .var r2', rv := .var rv' }

theorem bEx6RawStep_wf : bEx6RawStep.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .ijmp (.var (by simp [Tup.zip, RegsV.toTup]))
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bEx6While : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.imm 0#64) (.var r.r2) fun c =>
  .jnz (.var c) (.ijmp (.imm 16#64) r.keep) (.ijmp (.imm 24#64) r.keep)

theorem bEx6While_wf : bEx6While.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.imm _) (.cons (.var (by simp [Tup.zip, RegsV.toTup])) .nil)))
    fun _ _ => .jnz (.var (by simp [Tup.zip])) ?_ ?_
  · exact .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩
  · exact .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bEx6Step : BlockP := fun _ r =>
  .codeAddr "ex6_while" fun retPc =>
  .jmpSym "ex6_raw_step" { r.keep with rp := .var retPc }

theorem bEx6Step_wf : bEx6Step.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .codeAddr _ fun _ _ => .codeAddr _ fun _ _ => .ijmp (.var (by simp [Tup.zip]))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bEx6Even : BlockP := fun _ r =>
  .letOp2 (.cmp .eq i64) (.var r.r1) (.imm 0#64) fun z =>
  .jnz (.var z) (.halt (.var r.rv))
    (.letOp2 (.sub i64) (.var r.r1) (.imm 1#64) fun n' =>
     .ijmp (.imm 32#64) { r.keep with r1 := .var n' })

theorem bEx6Even_wf : bEx6Even.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .jnz (.var (by simp [Tup.zip]))
      (.halt (.var (by simp [Tup.zip, RegsV.toTup]))) ?_
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bEx6Odd : BlockP := fun _ r =>
  .letOp2 (.cmp .eq i64) (.var r.r1) (.imm 0#64) fun z =>
  .jnz (.var z) (.halt (.imm 0#64))
    (.letOp2 (.sub i64) (.var r.r1) (.imm 1#64) fun n' =>
     .ijmp (.imm 24#64) { r.keep with r1 := .var n' })

theorem bEx6Odd_wf : bEx6Odd.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .jnz (.var (by simp [Tup.zip])) (.halt (.imm _)) ?_
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup])) (.cons (.imm _) .nil)))
    fun _ _ => .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmEx6 : CodeMap :=
  [ mkEntry "ex6_raw_step" 0#64 bEx6RawStep,
    mkEntry "ex6_while" 8#64 bEx6While,
    mkEntry "ex6_step" 16#64 bEx6Step,
    mkEntry "ex6_even" 24#64 bEx6Even,
    mkEntry "ex6_odd" 32#64 bEx6Odd ]

def ex6HelperCr : ContifyRegion :=
  { name := "ex6_raw_step"
    entryPc := 0#64
    abi := .contified false
    tree := [.leaf 0#64]
    edges := [⟨0#64, [], .contRet false⟩]
    retainFallbacks := false }

def ex6MainCr : ContifyRegion :=
  { name := "ex6_while_even"
    entryPc := 8#64
    abi := .retEnvelope
    tree :=
      [ .loop 8#64 [.leaf 8#64, .leaf 16#64],
        .loop 24#64 [.leaf 24#64, .leaf 32#64] ]
    edges :=
      [ ⟨8#64, [true], .direct 16#64⟩,
        ⟨8#64, [false], .direct 24#64⟩,
        ⟨16#64, [], .contCall "ex6_raw_step" 0#64 false 8#64 none⟩,
        ⟨24#64, [false], .direct 32#64⟩,
        ⟨32#64, [false], .direct 24#64⟩ ]
    retainFallbacks := false }

def ex6Wit : ContifyWitness := ⟨[ex6HelperCr, ex6MainCr]⟩
def ex6Fns : List Fn := [liftContifyRegion cmEx6 ex6HelperCr, liftContifyRegion cmEx6 ex6MainCr]

theorem ex6_check : ex6Wit.check cmEx6 = true := by
  dsimp only [ex6Wit, ContifyWitness.check, ContifyWitness.checkAux, ContifyRegion.check,
    ContifyRegion.allPcs]
  have h1 : ex6HelperCr.tree.flatMap GroupTree.allPcs = [0#64] := by
    simp [ex6HelperCr, GroupTree.allPcs]
  have h2 : ex6MainCr.tree.flatMap GroupTree.allPcs = [8#64, 16#64, 24#64, 32#64] := by
    simp [ex6MainCr, GroupTree.allPcs]
  have htot : [ex6HelperCr, ex6MainCr].flatMap ContifyRegion.allPcs =
      [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [ContifyRegion.allPcs, h1, h2]
  have hmeta : ex6HelperCr.toCalleeMeta? cmEx6 [] =
      some ⟨"ex6_raw_step", 0#64, false, regionMemFree cmEx6 [] ex6HelperCr⟩ := by
    simp [ContifyRegion.toCalleeMeta?, ex6HelperCr]
  rw [htot, h1, h2, hmeta]
  exact Eq.refl true

theorem ex6_res_eq : residualContifyCodeMap cmEx6 ex6Wit = [] := by
  have h1 : List.flatMap ContifyRegion.allPcs
      (List.filter (fun r => !r.retainFallbacks) ex6Wit.regions) =
      [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [ex6Wit, ex6HelperCr, ex6MainCr, ContifyRegion.allPcs, GroupTree.allPcs]
  dsimp only [residualContifyCodeMap]
  rw [h1]
  simp [ex6Wit, ex6HelperCr, ex6MainCr, cmEx6, mkEntry]

theorem ex6_lift_eq : checkAndLiftContify cmEx6 ex6Wit = .ok (ex6Fns, []) := by
  dsimp only [checkAndLiftContify]
  rw [ex6_check, ex6_res_eq]
  rfl

theorem ex6_cm_wp_n2_k1 (r₀ : Regs) (m : Mem 64) (hr1 : r₀.r1 = 2#64) (hr2 : r₀.r2 = 1#64)
    (hrv : r₀.rv = 40#64) :
    cmEx6.wp (fun c _ => c = 41#64) 8#64 ⟨r₀, m⟩ := by
  intro Ψ hCl
  let rEnd : Regs := { r₀ with sp := r₀.sp, rp := 8#64, rv := 41#64, r1 := 0#64, r2 := 0#64 }
  have hEven0 : Ψ 24#64 ⟨rEnd, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx6.lookupAddr 24#64 = some (reifyBlock bEx6Even))
      bEx6Even_wf ?_
    dsimp only [bEx6Even, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode,
      liftCmp, CmpOp.evalBits, CmpOp.evalBool,
      Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals, rEnd]
    refine ⟨fun _ => rfl, fun hF => absurd hF (by decide)⟩
  have hOdd1 : Ψ 32#64 ⟨{ rEnd with r1 := 1#64 }, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx6.lookupAddr 32#64 = some (reifyBlock bEx6Odd))
      bEx6Odd_wf ?_
    dsimp only [bEx6Odd, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode,
      liftCmp, CmpOp.evalBits, CmpOp.evalBool,
      lift2, Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
    refine ⟨fun hT => absurd hT (by decide), fun _ => ?_⟩
    have hSub : (1#64 - 1#64 : BitVec 64) = 0#64 := by decide
    simpa [rEnd, hSub] using hEven0
  have hEven2 : Ψ 24#64 ⟨{ rEnd with r1 := 2#64 }, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx6.lookupAddr 24#64 = some (reifyBlock bEx6Even))
      bEx6Even_wf ?_
    dsimp only [bEx6Even, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode,
      liftCmp, CmpOp.evalBits, CmpOp.evalBool,
      lift2, Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
    refine ⟨fun hT => absurd hT (by decide), fun _ => ?_⟩
    have hSub : (2#64 - 1#64 : BitVec 64) = 1#64 := by decide
    simpa [rEnd, hSub] using hOdd1
  have hWhile0 : Ψ 8#64 ⟨{ rEnd with r1 := 2#64 }, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx6.lookupAddr 8#64 = some (reifyBlock bEx6While))
      bEx6While_wf ?_
    dsimp only [bEx6While, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode,
      liftCmp, CmpOp.evalBits, CmpOp.evalBool, Arg.val, Regs.toRegsV, RegsV.keep,
      RegsExpr.eval, vals, rEnd]
    have hUlt : BitVec.ult 0#64 0#64 = false := by decide
    refine ⟨fun hT => by simp [hUlt] at hT, fun _ => hEven2⟩
  have hRaw : Ψ 0#64 ⟨{ r₀ with rp := 8#64, r1 := 2#64, r2 := 1#64, rv := 40#64 }, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx6.lookupAddr 0#64 = some (reifyBlock bEx6RawStep))
      bEx6RawStep_wf ?_
    dsimp only [bEx6RawStep, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode,
      lift2, Arg.val, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
    have hSub : (1#64 - 1#64 : BitVec 64) = 0#64 := by decide
    have hAdd : (40#64 + 1#64 : BitVec 64) = 41#64 := by decide
    simpa [rEnd, hSub, hAdd] using hWhile0
  have hStep : Ψ 16#64 ⟨{ r₀ with r1 := 2#64, r2 := 1#64, rv := 40#64 }, m⟩ := by
    refine hCl.applyP (by t_kernel_rfl : cmEx6.lookupAddr 16#64 = some (reifyBlock bEx6Step))
      bEx6Step_wf ?_
    dsimp only [bEx6Step, BlockP.wp, BlockB.wp, CodeMap.symEnv, Arg.val,
      Regs.toRegsV, RegsV.keep, RegsExpr.eval]
    exact ⟨8#64, by t_kernel_rfl, 0#64, by t_kernel_rfl, hRaw⟩
  have hReg : ({ r₀ with r1 := 2#64, r2 := 1#64, rv := 40#64 } : Regs) = r₀ := by
    cases r₀; simp at hr1 hr2 hrv; subst hr1; subst hr2; subst hrv; rfl
  refine hCl.applyP (by t_kernel_rfl : cmEx6.lookupAddr 8#64 = some (reifyBlock bEx6While))
    bEx6While_wf ?_
  dsimp only [bEx6While, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode,
    liftCmp, CmpOp.evalBits, CmpOp.evalBool, Arg.val, Regs.toRegsV, RegsV.keep,
    RegsExpr.eval, vals]
  rw [hr1, hr2, hrv]
  refine ⟨fun _ => by simpa [hReg] using hStep, fun hF => by
    have hUlt : BitVec.ult 0#64 1#64 = true := by decide
    simp [hUlt] at hF⟩

/-! ## §6. Generic `TargetInit` Concrete Runner Helpers -/

private theorem argsIn_eq_of_eq {T : Target} {s : T.mach.MData} {as bs : List Ty}
    (h : as = bs) {a : Tup Val as} {b : Tup Val bs}
    (hv : cast (congrArg (Tup Val) h) a = b) (ha : T.ArgsIn a s) : T.ArgsIn b s := by
  subst h; cases hv; exact ha

private theorem initState_eq_of_eq {T : Target} {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) (n : Nat) (bs : List UInt8)
    {as bsTy : List Ty} (h : as = bsTy) {a : Tup Val as} {b : Tup Val bsTy}
    (hv : cast (congrArg (Tup Val) h) a = b) :
    I.initState n bs a = I.initState n bs b := by
  subst h; cases hv; rfl

theorem run_stage0_of_init {T : Target} (C : AddrCodec T) {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {lt : LegalTarget}
    {cm : CodeMap} {wit : CfgWitness} {H : HaltPost} {H_mach : T.mach.State → Prop}
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftWitness cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
        (fun _ _ => True) Ψ_res) H)
    (hDrop : ∀ rw ∈ wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ st, Ψ_res pc st)
    {rw : RegionWitness} (hRw : rw ∈ wit.regions) {r₀ : BedrockWord.Regs}
    (bsMem : List UInt8) (hbs : bsMem.length ≤ maxMem)
    (hreg : lt.legalSig regSig = regSig)
    (hencreg : ∀ r : Tup Val regSig,
      cast (congrArg (Tup Val) hreg) (encodeTup lt regSig r) = r)
    (hargs : (T.toIsa.assignArgs regSig).isSome = true)
    (hl64 : lt.legalSig [i64] = [i64])
    (henc64 : ∀ c : BitVec 64, cast (congrArg (Tup Val) hl64) (encodeTup lt [i64] (c, ())) =
      (c, ()))
    (hWp : cm.wp H rw.entryPc ⟨r₀, bsMem.At 0x1000#64⟩)
    (hret : cptr (TargetSafe T C M.host H_mach) (C.toBits I.ra0) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig rw.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val rw.abi.retSig, encodeTup lt rw.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState rw.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
            (fun _ _ => True) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored (I.initState (M.bound rw.name) bsMem r₀.toRegsV.toTup) s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound rw.name) ⋆ Std.ExtHashMap.emp)))
    (hexit : ∀ c m' stExit,
      H c m' → T.Defined M.host haltSym →
      T.mach.pc stExit = T.mach.labelAddr M.host haltSym →
      T.mach.getGpr (T.mach.data stExit) I.arg0 = c →
      Eventually (T.mach.step M.host) H_mach stExit)
    (hNoRo : wit.hasMemTableRo = false := by decide)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host) H_mach
      (T.mach.mkState (I.initState (M.bound rw.name) bsMem r₀.toRegsV.toTup)
        (T.mach.labelAddr M.host rw.name)) := by
  have hInit := initState_eq_of_eq I (M.bound rw.name) bsMem hreg (hencreg r₀.toRegsV.toTup)
  rw [← hInit]
  have hret' : cptr (TargetSafe T C M.host H_mach) (C.toBits I.ra0) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig rw.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val rw.abi.retSig, encodeTup lt rw.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState rw.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
            (fun _ _ => True) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored (I.initState (M.bound rw.name) bsMem
          (encodeTup lt regSig r₀.toRegsV.toTup)) s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound rw.name) ⋆ Std.ExtHashMap.emp)) := by
    simpa [hInit] using hret
  have hargs' : (T.toIsa.assignArgs (lt.legalSig regSig)).isSome = true := by rwa [hreg]
  have hmem := I.mem_entry (M.bound rw.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup)
    (Nat.le_trans (M.bound_le_max rw.name) hbound) hbs
  rw [← I.get_sp (M.bound rw.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup)] at hmem
  refine recoverCfg_run_compiled C hLift M Ψ_res hRes hDrop hRw hWp
    (I.initState (M.bound rw.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup))
    I.ra0 Std.ExtHashMap.emp
    (I.argsIn _ _ _ hargs') (I.raReg _ _ _) (by rw [I.get_sp]; exact I.spEntry) hmem
    (by rwa [I.get_sp]) ?_ hNoRo
  intro c m' stExit hH hDef hPc hArg _ _
  exact hexit c m' stExit hH hDef hPc
    (I.argsIn_singleton c (T.mach.data stExit) (argsIn_eq_of_eq hl64 (henc64 c) hArg))

theorem run_stage0_ro_of_init {T : Target} (C : AddrCodec T) {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {lt : LegalTarget}
    {cm : CodeMap} {wit : CfgWitness} {H : HaltPost} {H_mach : T.mach.State → Prop}
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftWitness cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
        (roPcGuard wit) Ψ_res) H)
    (hDrop : ∀ rw ∈ wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ st, Ψ_res pc st)
    {rw : RegionWitness} (hRw : rw ∈ wit.regions) {r₀ : BedrockWord.Regs}
    (bsMem : List UInt8) (hbs : bsMem.length ≤ maxMem)
    (hRo : roPcGuard wit rw.entryPc (bsMem.At 0x1000#64))
    (hreg : lt.legalSig regSig = regSig)
    (hencreg : ∀ r : Tup Val regSig,
      cast (congrArg (Tup Val) hreg) (encodeTup lt regSig r) = r)
    (hargs : (T.toIsa.assignArgs regSig).isSome = true)
    (hl64 : lt.legalSig [i64] = [i64])
    (henc64 : ∀ c : BitVec 64, cast (congrArg (Tup Val) hl64) (encodeTup lt [i64] (c, ())) =
      (c, ()))
    (hWp : cm.wp H rw.entryPc ⟨r₀, bsMem.At 0x1000#64⟩)
    (hret : cptr (TargetSafe T C M.host H_mach) (C.toBits I.ra0) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig rw.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val rw.abi.retSig, encodeTup lt rw.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState rw.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
            (roPcGuard wit) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored (I.initState (M.bound rw.name) bsMem r₀.toRegsV.toTup) s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound rw.name) ⋆ Std.ExtHashMap.emp)))
    (hexit : ∀ c m' stExit,
      H c m' → T.Defined M.host haltSym →
      T.mach.pc stExit = T.mach.labelAddr M.host haltSym →
      T.mach.getGpr (T.mach.data stExit) I.arg0 = c →
      Eventually (T.mach.step M.host) H_mach stExit)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host) H_mach
      (T.mach.mkState (I.initState (M.bound rw.name) bsMem r₀.toRegsV.toTup)
        (T.mach.labelAddr M.host rw.name)) := by
  have hInit := initState_eq_of_eq I (M.bound rw.name) bsMem hreg (hencreg r₀.toRegsV.toTup)
  rw [← hInit]
  have hret' : cptr (TargetSafe T C M.host H_mach) (C.toBits I.ra0) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig rw.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val rw.abi.retSig, encodeTup lt rw.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState rw.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
            (roPcGuard wit) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored (I.initState (M.bound rw.name) bsMem
          (encodeTup lt regSig r₀.toRegsV.toTup)) s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound rw.name) ⋆ Std.ExtHashMap.emp)) := by
    simpa [hInit] using hret
  have hargs' : (T.toIsa.assignArgs (lt.legalSig regSig)).isSome = true := by rwa [hreg]
  have hmem := I.mem_entry (M.bound rw.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup)
    (Nat.le_trans (M.bound_le_max rw.name) hbound) hbs
  rw [← I.get_sp (M.bound rw.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup)] at hmem
  refine recoverCfg_ro_run_compiled C hLift M Ψ_res hRes hDrop hRw hRo hWp
    (I.initState (M.bound rw.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup))
    I.ra0 Std.ExtHashMap.emp
    (I.argsIn _ _ _ hargs') (I.raReg _ _ _) (by rw [I.get_sp]; exact I.spEntry) hmem
    (by rwa [I.get_sp]) ?_
  intro c m' stExit hH hDef hPc hArg _ _
  exact hexit c m' stExit hH hDef hPc
    (I.argsIn_singleton c (T.mach.data stExit) (argsIn_eq_of_eq hl64 (henc64 c) hArg))

theorem run_stage1_of_init {T : Target} (C : AddrCodec T) {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {lt : LegalTarget}
    {cm : CodeMap} {wit : ContifyWitness} {H : HaltPost} {H_mach : T.mach.State → Prop}
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftContify cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hPriv : ∀ cr ∈ wit.regions, ∀ (r₀ : BedrockWord.Regs) (m₀ : Mem 64),
      (∃ b, cm.lookupAddr cr.entryPc = some b ∧
        b.wp cm.symEnv (fun _ _ => True) H (pushRegsV r₀.toRegsV) m₀) →
      cr.privFrame.numSlots > 0 →
      cr.privFrame.numSlots ≤ 64 ∧ ∀ k < cr.privFrame.numSlots, storeOk m₀ i64 (slotAddr r₀.sp k))
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
        (fun _ _ => True) Ψ_res) H)
    (hDrop : ∀ cr ∈ wit.regions, cr.retainFallbacks = false →
      ∀ pc ∈ cr.allPcs, pc ≠ cr.entryPc → ∀ st, Ψ_res pc st)
    {cr : ContifyRegion} (hCr : cr ∈ wit.regions) {r₀ : BedrockWord.Regs}
    (bsMem : List UInt8) (hbs : bsMem.length ≤ maxMem)
    (hreg : lt.legalSig regSig = regSig)
    (hencreg : ∀ r : Tup Val regSig,
      cast (congrArg (Tup Val) hreg) (encodeTup lt regSig r) = r)
    (hargs : (T.toIsa.assignArgs regSig).isSome = true)
    (hl64 : lt.legalSig [i64] = [i64])
    (henc64 : ∀ c : BitVec 64, cast (congrArg (Tup Val) hl64) (encodeTup lt [i64] (c, ())) =
      (c, ()))
    (hWp : cm.wp H cr.entryPc ⟨r₀, bsMem.At 0x1000#64⟩)
    (hret : cptr (TargetSafe T C M.host H_mach) (C.toBits I.ra0) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig cr.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val cr.abi.retSig, encodeTup lt cr.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState cr.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
            (fun _ _ => True) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored (I.initState (M.bound cr.name) bsMem r₀.toRegsV.toTup) s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound cr.name) ⋆ Std.ExtHashMap.emp)))
    (hexit : ∀ c m' stExit,
      H c m' → T.Defined M.host haltSym →
      T.mach.pc stExit = T.mach.labelAddr M.host haltSym →
      T.mach.getGpr (T.mach.data stExit) I.arg0 = c →
      Eventually (T.mach.step M.host) H_mach stExit)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host) H_mach
      (T.mach.mkState (I.initState (M.bound cr.name) bsMem r₀.toRegsV.toTup)
        (T.mach.labelAddr M.host cr.name)) := by
  have hInit := initState_eq_of_eq I (M.bound cr.name) bsMem hreg (hencreg r₀.toRegsV.toTup)
  rw [← hInit]
  have hret' : cptr (TargetSafe T C M.host H_mach) (C.toBits I.ra0) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig cr.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val cr.abi.retSig, encodeTup lt cr.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState cr.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
            (fun _ _ => True) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored (I.initState (M.bound cr.name) bsMem
          (encodeTup lt regSig r₀.toRegsV.toTup)) s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound cr.name) ⋆ Std.ExtHashMap.emp)) := by
    simpa [hInit] using hret
  have hargs' : (T.toIsa.assignArgs (lt.legalSig regSig)).isSome = true := by rwa [hreg]
  have hmem := I.mem_entry (M.bound cr.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup)
    (Nat.le_trans (M.bound_le_max cr.name) hbound) hbs
  rw [← I.get_sp (M.bound cr.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup)] at hmem
  refine recoverCfg_contify_run_compiled C hLift M Ψ_res hPriv hRes hDrop hCr hWp
    (I.initState (M.bound cr.name) bsMem (encodeTup lt regSig r₀.toRegsV.toTup))
    I.ra0 Std.ExtHashMap.emp
    (I.argsIn _ _ _ hargs') (I.raReg _ _ _) (by rw [I.get_sp]; exact I.spEntry) hmem
    (by rwa [I.get_sp]) ?_
  intro c m' stExit hH hDef hPc hArg _ _
  exact hexit c m' stExit hH hDef hPc
    (I.argsIn_singleton c (T.mach.data stExit) (argsIn_eq_of_eq hl64 (henc64 c) hArg))

/-! ## §7. Kernel `std3` Axiom Audit & MetaM Arch-Isolation Audit -/

check_std_axioms!
  LeanQbe.T.Unified.abiNextPcAndState
  LeanQbe.T.Unified.embedTargetSafe_unfold
  LeanQbe.T.Unified.embedTargetSafe_fold
  LeanQbe.T.Unified.embedTargetSafe_entry
  LeanQbe.T.Unified.embedTargetSafe_res
  LeanQbe.T.Unified.recoverCfg_compiled_sound
  LeanQbe.T.Unified.recoverCfg_ro_compiled_sound
  LeanQbe.T.Unified.recoverCfg_contify_compiled_sound
  LeanQbe.T.Unified.recoverCfg_run_compiled
  LeanQbe.T.Unified.recoverCfg_ro_run_compiled
  LeanQbe.T.Unified.recoverCfg_contify_run_compiled
  LeanQbeTest.T.BedrockCfgStage2Test.ex1_lift_eq
  LeanQbeTest.T.BedrockCfgStage2Test.ex1_cm_wp_hot
  LeanQbeTest.T.BedrockCfgStage2Test.ex1_cm_wp_fast
  LeanQbeTest.T.BedrockCfgStage2Test.ex2a_lift_eq
  LeanQbeTest.T.BedrockCfgStage2Test.ex2a_cm_wp_1
  LeanQbeTest.T.BedrockCfgStage2Test.ex2b_lift_eq
  LeanQbeTest.T.BedrockCfgStage2Test.ex2b_cm_wp
  LeanQbeTest.T.BedrockCfgStage2Test.ex3_ro_lift_eq
  LeanQbeTest.T.BedrockCfgStage2Test.ex3_guarded_lift_eq
  LeanQbeTest.T.BedrockCfgStage2Test.ex3_witRoOk
  LeanQbeTest.T.BedrockCfgStage2Test.ex3_cm_wp_0
  LeanQbeTest.T.BedrockCfgStage2Test.ex6_lift_eq
  LeanQbeTest.T.BedrockCfgStage2Test.ex6_cm_wp_n2_k1
  LeanQbeTest.T.BedrockCfgStage2Test.run_stage0_of_init
  LeanQbeTest.T.BedrockCfgStage2Test.run_stage0_ro_of_init
  LeanQbeTest.T.BedrockCfgStage2Test.run_stage1_of_init

meta section

open Lean

private def isArchMod (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Kraken.X64" || s.startsWith "Kraken.AArch64" ||
  s.startsWith "LeanQbe.T.Amd64" || s.startsWith "LeanQbe.T.Arm64"

#eval show MetaM Unit from do
  let env ← importModules #[{ module := `LeanQbe.T.Unified.CfgRecoveryBridge }] {}
  let bad := env.header.moduleNames.filter isArchMod
  if !bad.isEmpty then
    throwError "CfgRecoveryBridge import closure leaks arch module(s): {bad.toList}"

end

end LeanQbeTest.T.BedrockCfgStage2Test
