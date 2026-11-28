module

import LeanQbe.T.Unified.CfgRecoveryBridge
import LeanQbe.T.MainCertProof
import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.MainSplice
import LeanQbe.T.Logic.ProofKit
import LeanQbeTest.T.BedrockCfgStage2Test
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.MemLemmas
meta import Lean
import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Unified.CfgRecovery
meta import LeanQbe.T.Unified.CfgContify
meta import LeanQbe.T.BedrockWord.Core
meta import LeanQbeTest.T.BedrockCfgStage2Test

/-!
# Concrete AAPCS64 Arm64 Stage-2 CFG Recovery Bridge Tests (`BedrockCfgStage2Arm64Test`)

Compiles Examples 1, 2a, 2b, 3 (`.memTableRo` & `.memTableGuarded`), and 6 (Stage-1 `whileM` +
`raw_step` + mutual `even`/`odd`) to concrete `armTarget` binaries via `Compiled`, instantiates
`recoverCfg_ro_compiled_sound`, and `recoverCfg_contify_compiled_sound`, executes concrete
`armTarget.mach.step` runs via `run_stage0_of_init` / `run_stage0_ro_of_init` /
`run_stage1_of_init`, and audits `check_std_axioms!`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BedrockCfgStage2Arm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Xcap LeanQbe.T.BedrockWord
open LeanQbe.T.Unified LeanQbe.T.ProofKit Kraken
open LeanQbeTest.T.BedrockCfgStage2Test

def armCodec : AddrCodec armTarget where
  toBits := Int64.toBitVec
  ofBits := Int64.ofBitVec
  of_to := Int64.ofBitVec_toBitVec

/-! ## §1. Compiled Arm64 Modules for Examples 1, 2a, 2b, 3 (`memTableRo` & `memTableGuarded`), 6 -/

splice_module_hints armEx1Hints armTarget.toIsa armLegalTarget ex1Fns
splice_chunk_literals armEx1Code armEx1Bounds armEx1Sigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  [] [haltSym] 0 ex1Fns armEx1Hints

theorem armEx1_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      [] [haltSym] 0 ex1Fns armEx1Hints = .ok (armEx1Code, armEx1Bounds) := by
  t_kernel_rfl

theorem armEx1_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      armEx1Code armEx1Bounds (ex1Fns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

def armEx1Compiled :
    Compiled armTarget armLegalTarget [] [haltSym] 0 ex1Fns armEx1Hints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    [] [haltSym] 0 ex1Fns armEx1Hints 2048 armEx1Code armEx1Bounds armEx1_cm armEx1_meta

splice_module_hints armEx2aHints armTarget.toIsa armLegalTarget ex2aFns
splice_chunk_literals armEx2aCode armEx2aBounds armEx2aSigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  [] [haltSym] 0 ex2aFns armEx2aHints

theorem armEx2a_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      [] [haltSym] 0 ex2aFns armEx2aHints = .ok (armEx2aCode, armEx2aBounds) := by
  t_kernel_rfl

theorem armEx2a_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      armEx2aCode armEx2aBounds (ex2aFns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

def armEx2aCompiled :
    Compiled armTarget armLegalTarget [] [haltSym] 0 ex2aFns armEx2aHints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    [] [haltSym] 0 ex2aFns armEx2aHints 2048 armEx2aCode armEx2aBounds armEx2a_cm armEx2a_meta

splice_module_hints armEx2bHints armTarget.toIsa armLegalTarget ex2bFns
splice_chunk_literals armEx2bCode armEx2bBounds armEx2bSigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  [] [haltSym] 0 ex2bFns armEx2bHints

theorem armEx2b_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      [] [haltSym] 0 ex2bFns armEx2bHints = .ok (armEx2bCode, armEx2bBounds) := by
  t_kernel_rfl

theorem armEx2b_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      armEx2bCode armEx2bBounds (ex2bFns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

def armEx2bCompiled :
    Compiled armTarget armLegalTarget [] [haltSym] 0 ex2bFns armEx2bHints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    [] [haltSym] 0 ex2bFns armEx2bHints 2048 armEx2bCode armEx2bBounds armEx2b_cm armEx2b_meta

splice_module_hints armEx3RoHints armTarget.toIsa armLegalTarget ex3RoFns
splice_chunk_literals armEx3RoCode armEx3RoBounds armEx3RoSigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  [] [haltSym] 0 ex3RoFns armEx3RoHints

theorem armEx3Ro_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      [] [haltSym] 0 ex3RoFns armEx3RoHints = .ok (armEx3RoCode, armEx3RoBounds) := by
  t_kernel_rfl

theorem armEx3Ro_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      armEx3RoCode armEx3RoBounds (ex3RoFns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

def armEx3RoCompiled :
    Compiled armTarget armLegalTarget [] [haltSym] 0 ex3RoFns armEx3RoHints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    [] [haltSym] 0 ex3RoFns armEx3RoHints 2048
    armEx3RoCode armEx3RoBounds armEx3Ro_cm armEx3Ro_meta

splice_module_hints armEx3GuardedHints armTarget.toIsa armLegalTarget ex3GuardedFns
splice_chunk_literals armEx3GuardedCode armEx3GuardedBounds armEx3GuardedSigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  [] [haltSym] 0 ex3GuardedFns armEx3GuardedHints

theorem armEx3Guarded_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      [] [haltSym] 0 ex3GuardedFns armEx3GuardedHints =
      .ok (armEx3GuardedCode, armEx3GuardedBounds) := by
  t_kernel_rfl

theorem armEx3Guarded_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      armEx3GuardedCode armEx3GuardedBounds (ex3GuardedFns.map Fn.name) [haltSym] 2048 =
      true := by
  t_kernel_rfl

def armEx3GuardedCompiled :
    Compiled armTarget armLegalTarget [] [haltSym] 0 ex3GuardedFns armEx3GuardedHints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    [] [haltSym] 0 ex3GuardedFns armEx3GuardedHints 2048
    armEx3GuardedCode armEx3GuardedBounds armEx3Guarded_cm armEx3Guarded_meta

splice_module_hints armEx6Hints armTarget.toIsa armLegalTarget ex6Fns
splice_chunk_literals armEx6Code armEx6Bounds armEx6Sigs
  armTarget.toIsa armLegalTarget armTarget.frame.raBytes
  [] [haltSym] 0 ex6Fns armEx6Hints

theorem armEx6_cm :
    compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      [] [haltSym] 0 ex6Fns armEx6Hints = .ok (armEx6Code, armEx6Bounds) := by
  t_kernel_rfl

theorem armEx6_meta :
    checkCompileLit armTarget.frame.label armLayout.progSmall
      armEx6Code armEx6Bounds (ex6Fns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

def armEx6Compiled :
    Compiled armTarget armLegalTarget [] [haltSym] 0 ex6Fns armEx6Hints 2048 :=
  compileCheckedLit armTarget armLayout armLegalTarget armLabelClean
    [] [haltSym] 0 ex6Fns armEx6Hints 2048 armEx6Code armEx6Bounds armEx6_cm armEx6_meta

/-! ## §2. Concrete Arm64 Machine Execution Theorems (`Eventually armTarget.mach.step`) -/

private theorem ex1_res_closed_arm (H_mach : armTarget.mach.State → Prop) :
    SpecsClosed ex1Res cmEx1.symEnv
      (embedTargetSafe armTarget armCodec armEx1Compiled.host armLegalTarget
        (fun c _ => c = 7#64 ∨ c = 42#64) 0 H_mach (witEntries ex1Wit armEx1Compiled.bound)
        (fun _ _ => True)
        (fun pc st => pc = 40#64 → st.regs.r3 = 7#64 ∨ st.regs.r3 = 42#64))
      (fun c _ => c = 7#64 ∨ c = 42#64) := by
  intro pc b hlu st hbp
  dsimp only [ex1Res, CodeMap.lookupAddr, mkEntry] at hlu
  split at hlu
  · rename_i hEq
    cases hlu
    have hpc : 40#64 = pc := beq_iff_eq.1 hEq
    subst hpc
    dsimp only [BlockFlat.wp, denoteArg, pushRegsV, Regs.toRegsV, RegsV.toTup, pushTup] at hbp
    apply embedTargetSafe_fold
    refine ⟨fun e he heq _ => ?_, fun _ _ => hbp⟩
    exfalso
    rcases List.mem_map.1 he with ⟨rw', hMem, rfl⟩
    simp only [ex1Wit, List.mem_singleton] at hMem
    subst hMem
    cases heq
  · cases hlu

private theorem ex1_drop_arm :
    ∀ rw ∈ ex1Wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ (st : BedrockWord.State),
        pc = 40#64 → st.regs.r3 = 7#64 ∨ st.regs.r3 = 42#64 :=
  fun rw hRw hRet pc hPc hNe _ h40 => absurd h40 (ex1_drop_pc rw hRw hRet pc hPc hNe)

theorem armEx1_run_fast :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 0#64, r2 := 32#64, r3 := 42#64 }
    let H_mach : armTarget.mach.State → Prop := fun st =>
      (st.pc = armTarget.mach.labelAddr armEx1Compiled.host haltSym ∧
        (get st.data (.reg .X0) = 7#64 ∨ get st.data (.reg .X0) = 42#64)) ∨
      st.pc = armInit.ra0
    Eventually (armTarget.mach.step armEx1Compiled.host) H_mach
      (armTarget.mach.mkState
        (armInit.initState (armEx1Compiled.bound ex1Rw.name) [] r₀.toRegsV.toTup)
        (armTarget.mach.labelAddr armEx1Compiled.host ex1Rw.name)) := by
  intro r₀ H_mach
  refine run_stage0_of_init armCodec armInit ex1_lift_eq armEx1Compiled
    (fun pc st => pc = 40#64 → st.regs.r3 = 7#64 ∨ st.regs.r3 = 42#64)
    (ex1_res_closed_arm H_mach) ex1_drop_arm
    List.mem_cons_self [] (by decide) rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex1_cm_wp_fast r₀ ([].At 0x1000#64) rfl rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change Arm64.get stExit.data (.reg .X0) = c at hArg; rw [hArg]; exact hH⟩))

theorem armEx2a_run_pad1 :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 1#64, r2 := 0#64, r3 := 0#64 }
    let H_mach : armTarget.mach.State → Prop := fun st =>
      (st.pc = armTarget.mach.labelAddr armEx2aCompiled.host haltSym ∧
        (get st.data (.reg .X0) = 10#64 ∨ get st.data (.reg .X0) = 20#64 ∨
          get st.data (.reg .X0) = 99#64)) ∨
      st.pc = armInit.ra0
    Eventually (armTarget.mach.step armEx2aCompiled.host) H_mach
      (armTarget.mach.mkState
        (armInit.initState (armEx2aCompiled.bound ex2aRw.name) [] r₀.toRegsV.toTup)
        (armTarget.mach.labelAddr armEx2aCompiled.host ex2aRw.name)) := by
  intro r₀ H_mach
  refine run_stage0_of_init armCodec armInit ex2a_lift_eq armEx2aCompiled
    (fun _ _ => True) (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    List.mem_cons_self [] (by decide) rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex2a_cm_wp_1 r₀ ([].At 0x1000#64) rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change Arm64.get stExit.data (.reg .X0) = c at hArg; rw [hArg]; exact hH⟩))

theorem armEx2b_run_caller :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 30#64, r2 := 10#64, r3 := 0#64 }
    let H_mach : armTarget.mach.State → Prop := fun st =>
      (st.pc = armTarget.mach.labelAddr armEx2bCompiled.host haltSym ∧
        (get st.data (.reg .X0) = 20#64 ∨ get st.data (.reg .X0) = 999#64)) ∨
      st.pc = armInit.ra0
    Eventually (armTarget.mach.step armEx2bCompiled.host) H_mach
      (armTarget.mach.mkState
        (armInit.initState (armEx2bCompiled.bound ex2bCallerRw.name) [] r₀.toRegsV.toTup)
        (armTarget.mach.labelAddr armEx2bCompiled.host ex2bCallerRw.name)) := by
  intro r₀ H_mach
  refine run_stage0_of_init armCodec armInit ex2b_lift_eq armEx2bCompiled
    (fun _ _ => True) (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    (List.mem_cons_of_mem _ List.mem_cons_self) [] (by decide)
    rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex2b_cm_wp r₀ ([].At 0x1000#64))
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change Arm64.get stExit.data (.reg .X0) = c at hArg
      have hSub : (r₀.r1 - r₀.r2 : BitVec 64) = 20#64 := by dsimp [r₀]
      rw [hArg]; simpa [hSub] using hH⟩))

theorem armEx3Ro_run_op0 :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 0#64, r2 := 0#64, r3 := 0#64 }
    let H_mach : armTarget.mach.State → Prop := fun st =>
      (st.pc = armTarget.mach.labelAddr armEx3RoCompiled.host haltSym ∧
        (get st.data (.reg .X0) = 100#64 ∨ get st.data (.reg .X0) = 200#64 ∨
          get st.data (.reg .X0) = 99#64)) ∨
      st.pc = armInit.ra0
    Eventually (armTarget.mach.step armEx3RoCompiled.host) H_mach
      (armTarget.mach.mkState
        (armInit.initState (armEx3RoCompiled.bound ex3RoRw.name) ex3TableBytes r₀.toRegsV.toTup)
        (armTarget.mach.labelAddr armEx3RoCompiled.host ex3RoRw.name)) := by
  intro r₀ H_mach
  refine run_stage0_ro_of_init armCodec armInit ex3_ro_lift_eq armEx3RoCompiled
    (fun _ _ => True) (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    List.mem_cons_self ex3TableBytes (by decide) (fun _ => ex3_witRoOk)
    rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl) (ex3_cm_wp_0 r₀ rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change Arm64.get stExit.data (.reg .X0) = c at hArg; rw [hArg]; exact hH⟩))

theorem armEx3Guarded_run_op0 :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 0#64, r2 := 0#64, r3 := 0#64 }
    let H_mach : armTarget.mach.State → Prop := fun st =>
      (st.pc = armTarget.mach.labelAddr armEx3GuardedCompiled.host haltSym ∧
        (get st.data (.reg .X0) = 100#64 ∨ get st.data (.reg .X0) = 200#64 ∨
          get st.data (.reg .X0) = 99#64)) ∨
      st.pc = armInit.ra0
    Eventually (armTarget.mach.step armEx3GuardedCompiled.host) H_mach
      (armTarget.mach.mkState
        (armInit.initState (armEx3GuardedCompiled.bound ex3GuardedRw.name)
          ex3TableBytes r₀.toRegsV.toTup)
        (armTarget.mach.labelAddr armEx3GuardedCompiled.host ex3GuardedRw.name)) := by
  intro r₀ H_mach
  refine run_stage0_of_init armCodec armInit ex3_guarded_lift_eq armEx3GuardedCompiled
    (fun _ _ => True) (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    List.mem_cons_self ex3TableBytes (by decide)
    rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex3_cm_wp_0 r₀ rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change Arm64.get stExit.data (.reg .X0) = c at hArg; rw [hArg]; exact hH⟩))

theorem armEx6_run_while_even :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 40#64, r1 := 2#64, r2 := 1#64, r3 := 0#64 }
    let H_mach : armTarget.mach.State → Prop := fun st =>
      (st.pc = armTarget.mach.labelAddr armEx6Compiled.host haltSym ∧
        get st.data (.reg .X0) = 41#64) ∨
      st.pc = armInit.ra0
    Eventually (armTarget.mach.step armEx6Compiled.host) H_mach
      (armTarget.mach.mkState
        (armInit.initState (armEx6Compiled.bound ex6MainCr.name) [] r₀.toRegsV.toTup)
        (armTarget.mach.labelAddr armEx6Compiled.host ex6MainCr.name)) := by
  intro r₀ H_mach
  refine run_stage1_of_init armCodec armInit ex6_lift_eq armEx6Compiled
    (fun _ _ => True)
    (fun cr hCr _ _ _ hSlots => by
      rcases List.mem_cons.mp hCr with rfl | hCr'
      · simp [ex6HelperCr] at hSlots
      · rcases List.mem_cons.mp hCr' with rfl | hN
        · simp [ex6MainCr] at hSlots
        · nomatch hN)
    (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    (List.mem_cons_of_mem _ List.mem_cons_self) [] (by decide)
    rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex6_cm_wp_n2_k1 r₀ ([].At 0x1000#64) rfl rfl rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change Arm64.get stExit.data (.reg .X0) = c at hArg; rw [hArg]; exact hH⟩))

/-! ## §3. `std3` Kernel Axiom Audit -/

check_std_axioms!
  LeanQbeTest.T.BedrockCfgStage2Arm64Test.armEx1_run_fast
  LeanQbeTest.T.BedrockCfgStage2Arm64Test.armEx2a_run_pad1
  LeanQbeTest.T.BedrockCfgStage2Arm64Test.armEx2b_run_caller
  LeanQbeTest.T.BedrockCfgStage2Arm64Test.armEx3Ro_run_op0
  LeanQbeTest.T.BedrockCfgStage2Arm64Test.armEx3Guarded_run_op0
  LeanQbeTest.T.BedrockCfgStage2Arm64Test.armEx6_run_while_even

end LeanQbeTest.T.BedrockCfgStage2Arm64Test