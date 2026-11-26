module

public import LeanQbe.T.Arm64.LcnfC0LoopDemoCertArm64
meta import Lean
meta import LeanQbe.T.Arm64.LcnfC0LoopDemoCertArm64

/-!
# Verification Suite for AAPCS64 AArch64 `FactLoop` Certificate (`LcnfC0LoopDemoCertArm64`)

1. Architecture-isolation `#eval` audit (zero `Kraken.X64` / `LeanQbe.T.Amd64` imports).
2. Kernel `#guard` and legal-signature checks across all `88` functions of `factLoopLinkedMod`.
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0LoopDemoArm64Test

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let x64 := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64.isEmpty then
    throwError "LcnfC0LoopDemoArm64Test leaked X64 imports: {x64.toList}"

#guard factLoopLinkedMod.fns.length == 88
#guard factLoopLinkedMod.externs.isEmpty
#guard factLoopLinkedMod.exits == rtExitSyms
#guard factLoopLinkedMod.checkAcyclic
#guard checkLegalSigAll armLegalTarget factLoopLinkedMod.fns
#guard rtC0CoreArm64AllExt.length == 86

theorem test_arm64_bounds :
    factLoopArm64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" ≤ 2048 ∧
      factLoopArm64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factAcc" ≤ 2048 :=
  ⟨factLoopArm64Cert_maxBound, factLoopArm64Cert_factAcc_bound⟩

#print axioms factLoopArm64Cert_maxBound
#print axioms factLoopArm64Cert_factAcc_bound
#print axioms factLoopLinkedMod_arm64_legalSig
#print axioms factLoopArm64_factStr_fnSpec
#print axioms factLoopArm64_fact25_run
#print axioms test_arm64_bounds

end LeanQbeTest.T.LcnfC0LoopDemoArm64Test
