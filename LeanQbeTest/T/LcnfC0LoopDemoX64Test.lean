module

import LeanQbe.T.Amd64.LcnfC0LoopDemoCertX64
meta import Lean
meta import LeanQbe.T.Amd64.LcnfC0LoopDemoCertX64

/-!
# Verification Suite for SysV x86-64 `FactLoop` Certificate (`LcnfC0LoopDemoCertX64`)

1. Architecture-isolation `#eval` audit (zero `Kraken.AArch64` / `LeanQbe.T.Arm64` imports).
2. Kernel `#guard` and legal-signature checks across all `82` functions of `factLoopLinkedMod`.
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LcnfC0LoopDemoX64Test

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let arm := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.AArch64" || s.startsWith "LeanQbe.T.Arm64"
  if !arm.isEmpty then
    throwError "LcnfC0LoopDemoX64Test leaked Arm64 imports: {arm.toList}"

#guard factLoopLinkedMod.fns.length == 82
#guard factLoopLinkedMod.externs.isEmpty
#guard factLoopLinkedMod.exits == rtExitSyms
#guard factLoopLinkedMod.checkAcyclic
#guard checkLegalSigAll x64LegalTarget factLoopLinkedMod.fns
#guard rtC0CoreAllExt.length == 80

theorem test_x64_bounds :
    factLoopX64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" ≤ 2048 ∧
      factLoopX64Cert.bound "l_LeanQbe_T_LeanLCNF_FactLoop_factAcc" ≤ 2048 :=
  ⟨factLoopX64Cert_maxBound, factLoopX64Cert_factAcc_bound⟩

#print axioms factLoopX64Cert_maxBound
#print axioms factLoopX64Cert_factAcc_bound
#print axioms factLoopLinkedMod_x64_legalSig
#print axioms factLoopX64_factStr_fnSpec
#print axioms factLoopX64_fact25_run
#print axioms test_x64_bounds

end LeanQbeTest.T.LcnfC0LoopDemoX64Test
