module

public import LeanQbe.T.Unified.Frontend.Lcnf
public import LeanQbe.T.LeanLCNF.Demo
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.FlatLemmas
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.Spill
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.Unified.Frontend.Lcnf
public meta import LeanQbe.T.LeanLCNF.Lower1
public meta import LeanQbe.T.LeanLCNF.Demo
public meta import LeanQbe.T.LeanLCNF.LcnfC0Rt
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Amd64.TargLemmas
public meta import LeanQbe.T.Spill
public meta import Kraken.X64.Syntax

/-!
# Tests for `LeanLCNF` Direct Unified Frontend (`LeanQbe.T.Unified.Frontend.Lcnf`)

Verifies Phase U1b end-to-end without editing any existing `LeanLCNF` / `Unified` / `Amd64` /
`Arm64` source files:
1. Arch-isolation `#eval` audit: `LeanQbe.T.Unified.Frontend.Lcnf` transitively imports zero
   `Kraken.X64`, `Kraken.AArch64`, `LeanQbe.T.Amd64`, `LeanQbe.T.Arm64`, or `Bootstrap0` modules;
   this x64 test module imports zero `Kraken.AArch64` / `LeanQbe.T.Arm64` modules.
2. `Demo.lcnfProgram` + `lcnfFrontend`: `caps := {}`, `.direct` routing, `lcnfFrontend_mapM`,
   and `lcnfModMid` succeeding across both `x64LegalTarget` and `LegalTarget.aarch64` (`arm64`),
   plus `unified lcnfFrontend x64LegalTarget (lcnfTargetBackend ...)` on representative functions.
3. Multi-function acyclic `LcModule` (`mixStep` + `mixPair` matching `lcnf_of_lean!`): kernel
   `ModuleOk`, `lcnfTfsMid_wf`, `checkCompile` + `compileChecked`, `lcnf_unified_moduleOk_fnSpec`,
   `lcnfModule_compiled_fnSpec_src`, and concrete `x64Init` execution (`mixPair 7 = 26`).
4. `rtR0Mod` + `rtC0Env`: `compile_linked_chunks!` + `lcnfRtR0_compiled_fnSpec_src` across all
   R0 runtime primitives, and clean `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.UnifiedLcnfTest

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Unified LeanQbe.T.Amd64

/-! ## 1. Architecture & Layer Isolation Checks -/

#eval show IO Unit from do
  let lcnfEnv ← Lean.importModules #[{ module := `LeanQbe.T.Unified.Frontend.Lcnf }] {}
  let lcnfMods := lcnfEnv.allImportedModuleNames
  let forbiddenPrefixes := [
    "Kraken.X64", "Kraken.AArch64",
    "LeanQbe.T.Amd64", "LeanQbe.T.Arm64",
    "LeanQbe.T.Unified.Frontend.Bootstrap0"
  ]
  let leaks := lcnfMods.filter fun m =>
    let s := m.toString
    forbiddenPrefixes.any fun p => s.startsWith p
  if !leaks.isEmpty then
    throw <| IO.userError s!"Arch/Boot0 import leak in Frontend.Lcnf: {leaks.toList}"
  IO.println s!"OK: Frontend.Lcnf transitive imports={lcnfMods.size}, leaks=0"

#eval show Lean.CoreM Unit from do
  let curMods := (← Lean.getEnv).allImportedModuleNames
  let armLeaks := curMods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.AArch64" || s.startsWith "LeanQbe.T.Arm64"
  if !armLeaks.isEmpty then
    throwError "UnifiedLcnfTest leaked Arm64 import: {armLeaks.toList}"

/-! ## 2. `Demo.lcnfProgram`, `lcnfFrontend`, and Shared `midEnd` (`x64` & `aarch64`) -/

#eval show IO Unit from do
  let demoTfs ← IO.ofExcept (lowerModule Demo.lcnfProgram)
  if demoTfs.length < 80 then
    throw <| IO.userError s!"Expected >= 80 Demo TFlatFns, got {demoTfs.length}"
  let demoMod := lcnfModule demoTfs
  if !demoMod.checkNamesNodup then
    throw <| IO.userError "Demo lcnfModule failed checkNamesNodup"
  for tf in demoTfs do
    if route (lcnfFrontend.caps tf) != .direct then
      throw <| IO.userError s!"Non-direct route on {tf.name}"
  let .ok ssaFns := lcnfFrontend.lower.mapM demoTfs
    | throw <| IO.userError "lcnfFrontend.lower.mapM failed on Demo.lcnfProgram"
  if ssaFns.map Fn.name != demoMod.fns.map Fn.name then
    throw <| IO.userError "lcnfFrontend.lower.mapM name mismatch against lcnfModule"
  let .ok midX64 := lcnfModMid x64LegalTarget Demo.lcnfProgram
    | throw <| IO.userError "lcnfModMid x64LegalTarget failed on Demo.lcnfProgram"
  let .ok midArm := lcnfModMid LegalTarget.aarch64 Demo.lcnfProgram
    | throw <| IO.userError "lcnfModMid LegalTarget.aarch64 failed on Demo.lcnfProgram"
  if midX64.length != demoTfs.length || midArm.length != demoTfs.length then
    throw <| IO.userError "lcnfModMid count mismatch on Demo.lcnfProgram"
  let backendX64 := lcnfTargetBackend x64Target (fun fn => Spill.hints x64Target.toIsa fn)
  let pipelineX64 := unified lcnfFrontend x64LegalTarget backendX64
  let sampleNames := [
    "l_LeanQbe_T_LeanLCNF_Demo_konst__redArg",
    "l_LeanQbe_T_LeanLCNF_Demo_hasEmpty",
    "l_LeanQbe_T_LeanLCNF_Demo_weight",
    "l_LeanQbe_T_LeanLCNF_Probe_resetDec",
    "l_LeanQbe_T_LeanLCNF_Probe_reuse",
    "lcnf_apply_1", "lcnf_apply_2", "lcnf_apply_3"
  ]
  for nm in sampleNames do
    let some tf := demoTfs.find? (·.name == nm)
      | throw <| IO.userError s!"Missing sample Demo fn {nm}"
    let ds ← IO.ofExcept (pipelineX64.run tf)
    if ds.isEmpty then
      throw <| IO.userError s!"Empty directive stream for {nm}"
  IO.println s!"OK: Demo.lcnfProgram ({demoTfs.length} fns) passed x64 + aarch64 + backend samples"

/-! ## 3. Multi-Function Acyclic `LcModule` End-to-End Verification & Execution -/

def mixStep (a b : UInt64) : UInt64 := (a + b) ^^^ (a * 3)
def mixPair (x : UInt64) : UInt64 := mixStep x (x + 1)

lcnf_of_lean! sampleU64Mod [mixStep, mixPair]

@[expose] def mixStepSpec (a b : BitVec 64) : BitVec 64 := (a + b) ^^^ (a * 3#64)
@[expose] def mixPairSpec (x : BitVec 64) : BitVec 64 := mixStepSpec x (x + 1#64)

@[expose] def mixStepTf : Frontend.C0.TFlatFn :=
  ⟨"l_mixStep", [i64, i64], [i64],
    .let_ (op2 (.add i64) (.var 1) (.var 0)) <|
    .let_ (op2 (.mul i64) (.var 2) (.imm 3#64)) <|
    .let_ (op2 (.xor i64) (.var 1) (.var 0)) <|
    .ret (.var 0, ())⟩

@[expose] def mixPairTf : Frontend.C0.TFlatFn :=
  ⟨"l_mixPair", [i64], [i64],
    .let_ (op2 (.add i64) (.var 0) (.imm 1#64)) <|
    .call "l_mixStep" (as := [i64, i64]) [i64] (.var 1, .var 0, ()) <|
    .ret (.var 0, ())⟩

@[expose] def u64Tfs : List Frontend.C0.TFlatFn := [mixStepTf, mixPairTf]

#eval show IO Unit from do
  let lowered ← IO.ofExcept (lowerModule sampleU64Mod)
  let expected :=
    ["l_LeanQbeTest_T_UnifiedLcnfTest_mixStep", "l_LeanQbeTest_T_UnifiedLcnfTest_mixPair"]
  if lowered.map (fun tf => tf.name) != expected then
    throw <| IO.userError s!"Unexpected sampleU64Mod names: {lowered.map (·.name)}"
  if !(lcnfModule lowered).checkAcyclic then
    throw <| IO.userError "lowered sampleU64Mod not acyclic"
  let .ok midX64 := lcnfModMid x64LegalTarget sampleU64Mod
    | throw <| IO.userError "lcnfModMid x64 failed on sampleU64Mod"
  let .ok midArm := lcnfModMid LegalTarget.aarch64 sampleU64Mod
    | throw <| IO.userError "lcnfModMid arm64 failed on sampleU64Mod"
  if midX64.length != 2 || midArm.length != 2 then
    throw <| IO.userError "sampleU64Mod mid count mismatch"

@[expose] def u64Env : Env
  | "l_mixStep", [.bits 64, .bits 64], [.bits 64], (a, b, ()), _, Q, _ =>
      ∀ m', Q (mixStepSpec a b, ()) m'
  | "l_mixPair", [.bits 64], [.bits 64], (x, ()), _, Q, _ =>
      ∀ m', Q (mixPairSpec x, ()) m'
  | _, _, _, _, _, _, _ => False

theorem u64Mod_acyclic : (lcnfModule u64Tfs).checkAcyclic = true := by
  rfl

theorem u64Mod_ok : ModuleOk u64Env (lcnfModule u64Tfs) := by
  refine Module.moduleOk_of_checkAcyclic u64Mod_acyclic (lcnfModule_wf u64Tfs) ?_
  intro fn hmem xs m Q X hc
  dsimp only [lcnfModule, lcnfTModule, LeanLRC.tflatFnsToFns, u64Tfs] at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · rcases xs with ⟨a, b, ⟨⟩⟩
    exact hc m
  · rcases List.mem_cons.mp hmem' with rfl | hnil
    · rcases xs with ⟨x, ⟨⟩⟩
      refine ⟨fun res _ => res = (mixStepSpec x (x + 1#64), ()), X, fun _ => rfl, ?_,
        fun _ _ _ _ hx => hx⟩
      rintro res m' rfl
      exact hc m'
    · nomatch hnil

theorem u64Mod_frontend_mapM_wf :
    ∀ fn ∈ (lcnfModule u64Tfs).fns, fn.Wf := by
  have hmap : lcnfFrontend.lower.mapM u64Tfs = .ok (lcnfModule u64Tfs).fns :=
    lcnfFrontend_mapM u64Tfs
  exact lcnfFrontend_mapM_wf u64Tfs hmap

@[expose] def mixStepHints : x64Target.toIsa.Hints where
  dest :=
    .node none
      (.node none
        (.node (some (.gpr .rdi)) .empty .empty)
        .empty)
      (.node (some (.gpr .rsi))
        (.node (some (.gpr .rsi)) .empty .empty)
        .empty)

@[expose] def mixPairHints : x64Target.toIsa.Hints where
  dest :=
    .node none
      (.node (some (.gpr .rsi)) .empty .empty)
      .empty

@[expose] def u64Hints : List x64Target.toIsa.Hints := [mixStepHints, mixPairHints]

theorem u64Mod_mid_x64_wf :
    ∀ q ∈ (lcnfModule u64Tfs).fns.map (·.mid x64LegalTarget), q.Wf := by
  have hwf := u64Mod_frontend_mapM_wf
  intro q hq
  rcases List.mem_map.mp hq with ⟨fn, hfn, rfl⟩
  exact fn_mid_wf (hwf fn hfn)

theorem u64Mod_mid_arm_wf :
    ∀ q ∈ (lcnfModule u64Tfs).fns.map (·.mid LegalTarget.aarch64), q.Wf := by
  have hwf := u64Mod_frontend_mapM_wf
  intro q hq
  rcases List.mem_map.mp hq with ⟨fn, hfn, rfl⟩
  exact fn_mid_wf (hwf fn hfn)

theorem u64Compiled_check :
    checkCompile x64Target x64Layout x64LegalTarget [] rtExitSyms 0
      (lcnfModule u64Tfs).fns u64Hints 2048 = true := by
  t_kernel_rfl

noncomputable def u64Compiled :
    Compiled x64Target x64LegalTarget [] rtExitSyms 0 (lcnfModule u64Tfs).fns u64Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean [] rtExitSyms 0
    (lcnfModule u64Tfs).fns u64Hints 2048 u64Compiled_check

theorem u64_mixPair_compiled_fnSpec_src :
    x64Target.Defined u64Compiled.host "l_mixPair" ∧
    x64Target.FnSpec u64Compiled.host "l_mixPair"
      (fun args m Q X => u64Env "l_mixPair" [i64] [i64] args m Q
        (fun g cs xs m' =>
          X g (x64LegalTarget.legalSig cs) (encodeTup x64LegalTarget cs xs) m'))
      (u64Compiled.bound "l_mixPair") 0 := by
  have htf : mixPairTf ∈ u64Tfs := List.mem_cons_of_mem _ List.mem_cons_self
  exact lcnfModule_compiled_fnSpec_src u64Compiled u64Env u64Mod_acyclic u64Mod_ok
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩ htf rfl rfl

theorem u64_mixPair_runs_26 :
    Eventually (x64Target.mach.step u64Compiled.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 26#64)
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64]) (u64Compiled.bound "l_mixPair") [] (7#64, ()))
        (x64Target.mach.labelAddr u64Compiled.host "l_mixPair")) := by
  have htf : mixPairTf ∈ u64Tfs := List.mem_cons_of_mem _ List.mem_cons_self
  have hmem0 : ([] : List UInt8).length ≤ 8192 := by decide
  have hargs : (x64Target.toIsa.assignArgs [i64]).isSome = true := by rfl
  let Q : Post [i64] := fun rets _ => rets = (26#64, ())
  let X : XPost := fun _ _ _ _ => False
  have hspec : u64Env "l_mixPair" [i64] [i64] (7#64, ()) (List.At [] 0x1000#64) Q
      (fun g cs xs m' => X g (x64LegalTarget.legalSig cs) (encodeTup x64LegalTarget cs xs) m') :=
    fun _ => rfl
  refine lcnfModule_compiled_run_fnSpec x64Init u64Compiled u64Env u64Mod_acyclic u64Mod_ok
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩ htf rfl rfl
    [] (7#64, ()) hmem0 hargs hspec ?_ (by omega)
  rintro st (⟨hpc, rets, m', hQ, hrets, _⟩ | ⟨_, _, _, _, hX, _⟩)
  · have hret : rets = (26#64, ()) := hQ
    subst hret
    exact ⟨hpc, x64Init.retsIn_singleton 26#64 _ hrets⟩
  · exact hX.elim

@[expose] def u64HintPick (fn : Fn) : x64Target.toIsa.Hints :=
  if fn.name == "l_mixStep" then mixStepHints else mixPairHints

theorem u64_mixStep_supports :
    (mixStepTf.toFn.earlyOpt).body.supportsSource x64LegalTarget = true := by
  t_kernel_rfl

theorem u64_mixStep_unified_eq :
    (unified lcnfFrontend x64LegalTarget (lcnfTargetBackend x64Target u64HintPick)).run mixStepTf =
      Rega.lowerFn x64Target.toIsa mixStepHints (mixStepTf.toFn.mid x64LegalTarget).ext
        (mixStepTf.toFn.mid x64LegalTarget) := by
  rw [unified_eq_legacy]
  dsimp only [lcnfFrontend, lcnfLower, bindE, legacyMid, lcnfTargetBackend]
  simp only [u64_mixStep_supports, ↓reduceIte]
  rfl

theorem u64_mixStep_unified_noExit
    (h : x64Target.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat)
    (ds : List x64Target.Directive)
    (hrun : (unified lcnfFrontend x64LegalTarget
      (lcnfTargetBackend x64Target u64HintPick)).run mixStepTf = .ok ds)
    (hinf : ds.IsInfixAt (x64Target.mach.prog h) k₀) (hu : x64Target.LabelsUnique h)
    (hfr : Rega.effFrame x64Target.toIsa (u64HintPick (mixStepTf.toFn.mid x64LegalTarget))
      (mixStepTf.toFn.mid x64LegalTarget).ext ≤ n)
    (hn : n + x64Target.frame.raBytes ≤ 2 ^ 64) :
    x64Target.Defined h "l_mixStep" ∧
    x64Target.FnSpec h "l_mixStep" (u64Env "l_mixStep" [i64, i64] [i64]) n nX := by
  have htf : mixStepTf ∈ u64Tfs := List.mem_cons_self
  have hcalEmpty : (mixStepTf.toFn.mid x64LegalTarget).ext.callees = [] := by
    t_kernel_rfl
  have hexEmpty : (mixStepTf.toFn.mid x64LegalTarget).ext.exits = [] := by
    t_kernel_rfl
  refine lcnf_unified_moduleOk_fnSpec_noExit x64Target x64LegalTarget u64HintPick u64Mod_ok htf ds
    hrun h k₀ n nX bound hinf hu hfr hn ?_ ?_ rfl rfl ?_
  · intro g as bs hcal
    rw [hcalEmpty] at hcal
    nomatch hcal
  · intro g hex
    rw [hexEmpty] at hex
    nomatch hex
  · intro args m Q X _ hC
    exact hC

/-! ## 4. Runtime Module `rtR0Mod` + `rtC0Env` (`Compiled` & `FnSpec`) -/

#eval show IO Unit from do
  if !rtR0Mod.fns.all (fun f => (f.earlyOpt).body.supportsSource LegalTarget.aarch64) then
    throw <| IO.userError "rtR0Mod contains function unsupported by LegalTarget.aarch64"

compile_linked_chunks! rtR0Cert
  x64Target x64Layout x64LegalTarget x64LabelClean rtR0Mod 5 (exits := rtExitSyms)

noncomputable def rtR0Compiled :
    Compiled x64Target x64LegalTarget [] rtExitSyms 0 rtR0Mod.fns
      (chunksHints rtR0Cert.chunks) (chunksMaxBound rtR0Cert.chunks) :=
  rtR0Cert.fns_eq ▸ rtR0Cert.compiled

theorem rtR0_all_fnSpec {fn : Fn} (hfn : fn ∈ rtR0Mod.fns) :
    x64Target.Defined rtR0Compiled.host fn.name ∧
    x64Target.FnSpec rtR0Compiled.host fn.name
      (legalEnv x64LegalTarget (Env.ofModule rtR0Mod rtC0Env) fn.name
        (x64LegalTarget.legalSig fn.as) (x64LegalTarget.legalSig fn.rs))
      (rtR0Compiled.bound fn.name) 0 :=
  lcnfRtR0_compiled_fnSpec rtR0Compiled hfn

theorem rtR0_alloc_fnSpec_src :
    x64Target.Defined rtR0Compiled.host "lcnf_alloc" ∧
    x64Target.FnSpec rtR0Compiled.host "lcnf_alloc"
      (fun args m Q X => rtC0Env "lcnf_alloc" [i64, i64] [i64] args m Q
        (fun g cs xs m' =>
          X g (x64LegalTarget.legalSig cs) (encodeTup x64LegalTarget cs xs) m'))
      (rtR0Compiled.bound "lcnf_alloc") 0 := by
  have hmem : rtR0Mod.fns[0] ∈ rtR0Mod.fns := List.getElem_mem (by decide)
  exact lcnfRtR0_compiled_fnSpec_src rtR0Compiled hmem rfl rfl

theorem rtR0_clo_under_fnSpec_src :
    x64Target.Defined rtR0Compiled.host "lcnf_clo_under" ∧
    x64Target.FnSpec rtR0Compiled.host "lcnf_clo_under"
      (fun args m Q X => rtC0Env "lcnf_clo_under" [i64, i64, i64] [i64] args m Q
        (fun g cs xs m' =>
          X g (x64LegalTarget.legalSig cs) (encodeTup x64LegalTarget cs xs) m'))
      (rtR0Compiled.bound "lcnf_clo_under") 0 := by
  have hmem : rtR0Mod.fns[4] ∈ rtR0Mod.fns := List.getElem_mem (by decide)
  exact lcnfRtR0_compiled_fnSpec_src rtR0Compiled hmem rfl rfl

#print axioms u64Mod_ok
#print axioms u64_mixPair_compiled_fnSpec_src
#print axioms u64_mixPair_runs_26
#print axioms u64_mixStep_unified_noExit
#print axioms rtR0_all_fnSpec
#print axioms rtR0_alloc_fnSpec_src
#print axioms rtR0_clo_under_fnSpec_src

end LeanQbeTest.T.UnifiedLcnfTest
