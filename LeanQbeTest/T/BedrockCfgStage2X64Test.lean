module

public import LeanQbe.T.Unified.CfgRecoveryBridge
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainSplice
public import LeanQbe.T.Logic.ProofKit
public import LeanQbeTest.T.BedrockCfgStage2Test
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.MemLemmas
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Unified.CfgRecovery
public meta import LeanQbe.T.Unified.CfgContify
public meta import LeanQbe.T.BedrockWord.Core
public meta import LeanQbeTest.T.BedrockCfgStage2Test

/-!
# Concrete SysV x86-64 Stage-2 CFG Recovery Bridge Tests (`BedrockCfgStage2X64Test`)

Compiles Examples 1, 2a, 2b, 3 (`.memTableRo` & `.memTableGuarded`), and 6 (Stage-1 `whileM` +
`raw_step` + mutual `even`/`odd`) to concrete `x64Target` binaries via `Compiled`, instantiates
`recoverCfg_ro_compiled_sound`, and `recoverCfg_contify_compiled_sound`, executes concrete
`x64Target.mach.step` runs via `run_stage0_of_init` / `run_stage0_ro_of_init` /
`run_stage1_of_init`, and audits `check_std_axioms!`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BedrockCfgStage2X64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Xcap LeanQbe.T.BedrockWord
open LeanQbe.T.Unified LeanQbe.T.ProofKit Kraken
open LeanQbeTest.T.BedrockCfgStage2Test

@[expose] def x64Codec : AddrCodec x64Target where
  toBits := Int64.toBitVec
  ofBits := Int64.ofBitVec
  of_to := Int64.ofBitVec_toBitVec

/-! ## §1. Compiled x64 Modules for Examples 1, 2a, 2b, 3 (`memTableRo` & `memTableGuarded`), 6 -/

splice_module_hints x64Ex1Hints x64Target.toIsa x64LegalTarget ex1Fns
splice_chunk_literals x64Ex1Code x64Ex1Bounds x64Ex1Sigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  [] [haltSym] 0 ex1Fns x64Ex1Hints

theorem x64Ex1_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      [] [haltSym] 0 ex1Fns x64Ex1Hints = .ok (x64Ex1Code, x64Ex1Bounds) := by
  t_kernel_rfl

theorem x64Ex1_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      x64Ex1Code x64Ex1Bounds (ex1Fns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

@[expose] def x64Ex1Compiled :
    Compiled x64Target x64LegalTarget [] [haltSym] 0 ex1Fns x64Ex1Hints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    [] [haltSym] 0 ex1Fns x64Ex1Hints 2048 x64Ex1Code x64Ex1Bounds x64Ex1_cm x64Ex1_meta

splice_module_hints x64Ex2aHints x64Target.toIsa x64LegalTarget ex2aFns
splice_chunk_literals x64Ex2aCode x64Ex2aBounds x64Ex2aSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  [] [haltSym] 0 ex2aFns x64Ex2aHints

theorem x64Ex2a_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      [] [haltSym] 0 ex2aFns x64Ex2aHints = .ok (x64Ex2aCode, x64Ex2aBounds) := by
  t_kernel_rfl

theorem x64Ex2a_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      x64Ex2aCode x64Ex2aBounds (ex2aFns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

@[expose] def x64Ex2aCompiled :
    Compiled x64Target x64LegalTarget [] [haltSym] 0 ex2aFns x64Ex2aHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    [] [haltSym] 0 ex2aFns x64Ex2aHints 2048 x64Ex2aCode x64Ex2aBounds x64Ex2a_cm x64Ex2a_meta

splice_module_hints x64Ex2bHints x64Target.toIsa x64LegalTarget ex2bFns
splice_chunk_literals x64Ex2bCode x64Ex2bBounds x64Ex2bSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  [] [haltSym] 0 ex2bFns x64Ex2bHints

theorem x64Ex2b_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      [] [haltSym] 0 ex2bFns x64Ex2bHints = .ok (x64Ex2bCode, x64Ex2bBounds) := by
  t_kernel_rfl

theorem x64Ex2b_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      x64Ex2bCode x64Ex2bBounds (ex2bFns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

@[expose] def x64Ex2bCompiled :
    Compiled x64Target x64LegalTarget [] [haltSym] 0 ex2bFns x64Ex2bHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    [] [haltSym] 0 ex2bFns x64Ex2bHints 2048 x64Ex2bCode x64Ex2bBounds x64Ex2b_cm x64Ex2b_meta

splice_module_hints x64Ex3RoHints x64Target.toIsa x64LegalTarget ex3RoFns
splice_chunk_literals x64Ex3RoCode x64Ex3RoBounds x64Ex3RoSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  [] [haltSym] 0 ex3RoFns x64Ex3RoHints

theorem x64Ex3Ro_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      [] [haltSym] 0 ex3RoFns x64Ex3RoHints = .ok (x64Ex3RoCode, x64Ex3RoBounds) := by
  t_kernel_rfl

theorem x64Ex3Ro_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      x64Ex3RoCode x64Ex3RoBounds (ex3RoFns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

@[expose] def x64Ex3RoCompiled :
    Compiled x64Target x64LegalTarget [] [haltSym] 0 ex3RoFns x64Ex3RoHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    [] [haltSym] 0 ex3RoFns x64Ex3RoHints 2048
    x64Ex3RoCode x64Ex3RoBounds x64Ex3Ro_cm x64Ex3Ro_meta

splice_module_hints x64Ex3GuardedHints x64Target.toIsa x64LegalTarget ex3GuardedFns
splice_chunk_literals x64Ex3GuardedCode x64Ex3GuardedBounds x64Ex3GuardedSigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  [] [haltSym] 0 ex3GuardedFns x64Ex3GuardedHints

theorem x64Ex3Guarded_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      [] [haltSym] 0 ex3GuardedFns x64Ex3GuardedHints =
      .ok (x64Ex3GuardedCode, x64Ex3GuardedBounds) := by
  t_kernel_rfl

theorem x64Ex3Guarded_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      x64Ex3GuardedCode x64Ex3GuardedBounds (ex3GuardedFns.map Fn.name) [haltSym] 2048 =
      true := by
  t_kernel_rfl

@[expose] def x64Ex3GuardedCompiled :
    Compiled x64Target x64LegalTarget [] [haltSym] 0 ex3GuardedFns x64Ex3GuardedHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    [] [haltSym] 0 ex3GuardedFns x64Ex3GuardedHints 2048
    x64Ex3GuardedCode x64Ex3GuardedBounds x64Ex3Guarded_cm x64Ex3Guarded_meta

splice_module_hints x64Ex6Hints x64Target.toIsa x64LegalTarget ex6Fns
splice_chunk_literals x64Ex6Code x64Ex6Bounds x64Ex6Sigs
  x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
  [] [haltSym] 0 ex6Fns x64Ex6Hints

theorem x64Ex6_cm :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      [] [haltSym] 0 ex6Fns x64Ex6Hints = .ok (x64Ex6Code, x64Ex6Bounds) := by
  t_kernel_rfl

theorem x64Ex6_meta :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      x64Ex6Code x64Ex6Bounds (ex6Fns.map Fn.name) [haltSym] 2048 = true := by
  t_kernel_rfl

@[expose] def x64Ex6Compiled :
    Compiled x64Target x64LegalTarget [] [haltSym] 0 ex6Fns x64Ex6Hints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean
    [] [haltSym] 0 ex6Fns x64Ex6Hints 2048 x64Ex6Code x64Ex6Bounds x64Ex6_cm x64Ex6_meta

/-! ## §2. Concrete x64 Machine Execution Theorems (`Eventually x64Target.mach.step`) -/

private theorem ex1_res_closed_x64 (H_mach : x64Target.mach.State → Prop) :
    SpecsClosed ex1Res cmEx1.symEnv
      (embedTargetSafe x64Target x64Codec x64Ex1Compiled.host x64LegalTarget
        (fun c _ => c = 7#64 ∨ c = 42#64) 0 H_mach (witEntries ex1Wit x64Ex1Compiled.bound)
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

private theorem ex1_drop_x64 :
    ∀ rw ∈ ex1Wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ (st : BedrockWord.State),
        pc = 40#64 → st.regs.r3 = 7#64 ∨ st.regs.r3 = 42#64 :=
  fun rw hRw hRet pc hPc hNe _ h40 => absurd h40 (ex1_drop_pc rw hRw hRet pc hPc hNe)

theorem x64Ex1_run_fast :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 0#64, r2 := 32#64, r3 := 42#64 }
    let H_mach : x64Target.mach.State → Prop := fun st =>
      (st.pc = x64Target.mach.labelAddr x64Ex1Compiled.host haltSym ∧
        (st.data.regs.get64 .rdi = 7#64 ∨ st.data.regs.get64 .rdi = 42#64)) ∨
      st.pc = x64Init.ra0
    Eventually (x64Target.mach.step x64Ex1Compiled.host) H_mach
      (x64Target.mach.mkState
        (x64Init.initState (x64Ex1Compiled.bound ex1Rw.name) [] r₀.toRegsV.toTup)
        (x64Target.mach.labelAddr x64Ex1Compiled.host ex1Rw.name)) := by
  intro r₀ H_mach
  refine run_stage0_of_init x64Codec x64Init ex1_lift_eq x64Ex1Compiled
    (fun pc st => pc = 40#64 → st.regs.r3 = 7#64 ∨ st.regs.r3 = 42#64)
    (ex1_res_closed_x64 H_mach) ex1_drop_x64
    List.mem_cons_self [] (by decide) rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex1_cm_wp_fast r₀ ([].At 0x1000#64) rfl rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change stExit.data.regs.get64 .rdi = c at hArg; rw [hArg]; exact hH⟩))

theorem x64Ex2a_run_pad1 :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 1#64, r2 := 0#64, r3 := 0#64 }
    let H_mach : x64Target.mach.State → Prop := fun st =>
      (st.pc = x64Target.mach.labelAddr x64Ex2aCompiled.host haltSym ∧
        (st.data.regs.get64 .rdi = 10#64 ∨ st.data.regs.get64 .rdi = 20#64 ∨
          st.data.regs.get64 .rdi = 99#64)) ∨
      st.pc = x64Init.ra0
    Eventually (x64Target.mach.step x64Ex2aCompiled.host) H_mach
      (x64Target.mach.mkState
        (x64Init.initState (x64Ex2aCompiled.bound ex2aRw.name) [] r₀.toRegsV.toTup)
        (x64Target.mach.labelAddr x64Ex2aCompiled.host ex2aRw.name)) := by
  intro r₀ H_mach
  refine run_stage0_of_init x64Codec x64Init ex2a_lift_eq x64Ex2aCompiled
    (fun _ _ => True) (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    List.mem_cons_self [] (by decide) rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex2a_cm_wp_1 r₀ ([].At 0x1000#64) rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change stExit.data.regs.get64 .rdi = c at hArg; rw [hArg]; exact hH⟩))

theorem x64Ex2b_run_caller :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 30#64, r2 := 10#64, r3 := 0#64 }
    let H_mach : x64Target.mach.State → Prop := fun st =>
      (st.pc = x64Target.mach.labelAddr x64Ex2bCompiled.host haltSym ∧
        (st.data.regs.get64 .rdi = 20#64 ∨ st.data.regs.get64 .rdi = 999#64)) ∨
      st.pc = x64Init.ra0
    Eventually (x64Target.mach.step x64Ex2bCompiled.host) H_mach
      (x64Target.mach.mkState
        (x64Init.initState (x64Ex2bCompiled.bound ex2bCallerRw.name) [] r₀.toRegsV.toTup)
        (x64Target.mach.labelAddr x64Ex2bCompiled.host ex2bCallerRw.name)) := by
  intro r₀ H_mach
  refine run_stage0_of_init x64Codec x64Init ex2b_lift_eq x64Ex2bCompiled
    (fun _ _ => True) (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    (List.mem_cons_of_mem _ List.mem_cons_self) [] (by decide)
    rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex2b_cm_wp r₀ ([].At 0x1000#64))
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change stExit.data.regs.get64 .rdi = c at hArg
      have hSub : (r₀.r1 - r₀.r2 : BitVec 64) = 20#64 := by dsimp [r₀]
      rw [hArg]; simpa [hSub] using hH⟩))

theorem x64Ex3Ro_run_op0 :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 0#64, r2 := 0#64, r3 := 0#64 }
    let H_mach : x64Target.mach.State → Prop := fun st =>
      (st.pc = x64Target.mach.labelAddr x64Ex3RoCompiled.host haltSym ∧
        (st.data.regs.get64 .rdi = 100#64 ∨ st.data.regs.get64 .rdi = 200#64 ∨
          st.data.regs.get64 .rdi = 99#64)) ∨
      st.pc = x64Init.ra0
    Eventually (x64Target.mach.step x64Ex3RoCompiled.host) H_mach
      (x64Target.mach.mkState
        (x64Init.initState (x64Ex3RoCompiled.bound ex3RoRw.name) ex3TableBytes r₀.toRegsV.toTup)
        (x64Target.mach.labelAddr x64Ex3RoCompiled.host ex3RoRw.name)) := by
  intro r₀ H_mach
  refine run_stage0_ro_of_init x64Codec x64Init ex3_ro_lift_eq x64Ex3RoCompiled
    (fun _ _ => True) (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    List.mem_cons_self ex3TableBytes (by decide) (fun _ => ex3_witRoOk)
    rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl) (ex3_cm_wp_0 r₀ rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change stExit.data.regs.get64 .rdi = c at hArg; rw [hArg]; exact hH⟩))

theorem x64Ex3Guarded_run_op0 :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 0#64, r1 := 0#64, r2 := 0#64, r3 := 0#64 }
    let H_mach : x64Target.mach.State → Prop := fun st =>
      (st.pc = x64Target.mach.labelAddr x64Ex3GuardedCompiled.host haltSym ∧
        (st.data.regs.get64 .rdi = 100#64 ∨ st.data.regs.get64 .rdi = 200#64 ∨
          st.data.regs.get64 .rdi = 99#64)) ∨
      st.pc = x64Init.ra0
    Eventually (x64Target.mach.step x64Ex3GuardedCompiled.host) H_mach
      (x64Target.mach.mkState
        (x64Init.initState (x64Ex3GuardedCompiled.bound ex3GuardedRw.name)
          ex3TableBytes r₀.toRegsV.toTup)
        (x64Target.mach.labelAddr x64Ex3GuardedCompiled.host ex3GuardedRw.name)) := by
  intro r₀ H_mach
  refine run_stage0_of_init x64Codec x64Init ex3_guarded_lift_eq x64Ex3GuardedCompiled
    (fun _ _ => True) (fun _ _ h => nomatch h) (fun _ _ _ _ _ _ _ => trivial)
    List.mem_cons_self ex3TableBytes (by decide)
    rfl (fun _ => rfl) (by decide) rfl (fun _ => rfl)
    (ex3_cm_wp_0 r₀ rfl)
    (fun s' _ => TargetSafe.done_toBits (Or.inr rfl))
    (fun c m' stExit hH _ hPc hArg => .done stExit (Or.inl ⟨hPc, by
      change stExit.data.regs.get64 .rdi = c at hArg; rw [hArg]; exact hH⟩))

theorem x64Ex6_run_while_even :
    let r₀ : BedrockWord.Regs :=
      { sp := 0#64, rp := 0#64, rv := 40#64, r1 := 2#64, r2 := 1#64, r3 := 0#64 }
    let H_mach : x64Target.mach.State → Prop := fun st =>
      (st.pc = x64Target.mach.labelAddr x64Ex6Compiled.host haltSym ∧
        st.data.regs.get64 .rdi = 41#64) ∨
      st.pc = x64Init.ra0
    Eventually (x64Target.mach.step x64Ex6Compiled.host) H_mach
      (x64Target.mach.mkState
        (x64Init.initState (x64Ex6Compiled.bound ex6MainCr.name) [] r₀.toRegsV.toTup)
        (x64Target.mach.labelAddr x64Ex6Compiled.host ex6MainCr.name)) := by
  intro r₀ H_mach
  refine run_stage1_of_init x64Codec x64Init ex6_lift_eq x64Ex6Compiled
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
      change stExit.data.regs.get64 .rdi = c at hArg; rw [hArg]; exact hH⟩))

/-! ## §3. `std3` Kernel Axiom Audit -/

check_std_axioms!
  LeanQbeTest.T.BedrockCfgStage2X64Test.x64Ex1_run_fast
  LeanQbeTest.T.BedrockCfgStage2X64Test.x64Ex2a_run_pad1
  LeanQbeTest.T.BedrockCfgStage2X64Test.x64Ex2b_run_caller
  LeanQbeTest.T.BedrockCfgStage2X64Test.x64Ex3Ro_run_op0
  LeanQbeTest.T.BedrockCfgStage2X64Test.x64Ex3Guarded_run_op0
  LeanQbeTest.T.BedrockCfgStage2X64Test.x64Ex6_run_while_even

end LeanQbeTest.T.BedrockCfgStage2X64Test