module

public import LeanQbe.T.Arm64.LcnfC0MutRecDemoCertArm64
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo

/-!
# Verification Suite for AAPCS64 AArch64 Mutual 2-Function SCC (`LcnfC0MutRecDemoCertArm64`)

1. Architecture-isolation `#eval` audit (`0` `Kraken.X64` / `LeanQbe.T.Amd64` imports).
2. Structural guards verifying genuine 2-function mutual recursion (`roseSum → forestSum`,
   `forestSum → {roseSum, forestSum}`), single-chunk `.recBudgetSCC` compilation (`numChunks = 1`),
   depth `D = 16` / bound `1040 ≤ 2048`, and fail-closed budget rejection (`maxFrame < 48`,
   `minEntry < 272`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0MutRecDemoArm64Test

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let x64 := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64.isEmpty then
    throwError "LcnfC0MutRecDemoArm64Test leaked X64/Amd64 imports: {x64.toList}"

#guard mutRecDemoLcMod.decls.length == 2
#guard mutRecDemoTfs.length == 2
#guard mutRecDemoLinkedMod.fns.length == 82
#guard mutRecDemoLinkedMod.externs.isEmpty
#guard mutRecDemoLinkedMod.exits == ["lcnf_panic"]
#guard mutRecDemoRoseFn.callees.any (fun s => s.1 == mutRecDemoForestName)
#guard !(mutRecDemoRoseFn.callees.any (fun s => s.1 == mutRecDemoRoseName))
#guard mutRecDemoRoseFn.callees.any (fun s => s.1 == "lcnf_nat_slow")
#guard mutRecDemoRoseFn.callees.any (fun s => s.1 == "lcnf_dec_ref_cold")
#guard mutRecDemoForestFn.callees.any (fun s => s.1 == mutRecDemoRoseName)
#guard mutRecDemoForestFn.callees.any (fun s => s.1 == mutRecDemoForestName)
#guard mutRecDemoForestFn.callees.any (fun s => s.1 == "lcnf_nat_slow")
#guard mutRecDemoForestFn.callees.any (fun s => s.1 == "lcnf_dec_ref_cold")
#guard !mutRecDemoProgMod.checkAcyclic
#guard LinkRec.checkCyclic
  ⟨mutRecDemoProgMod.fns, externsOfSigs (rtC0CoreMod.fns.map Fn.sig), rtExitSyms⟩
#guard checkLegalSigAll armLegalTarget mutRecDemoProgMod.fns
example : MutRecDemo.roseDepth sampleRose = 7 := rfl
example : MutRecDemo.forestDepth sampleForest = 6 := rfl
example : MutRecDemo.roseSum sampleRose = 90 := rfl
example : MutRecDemo.forestSum sampleForest = 80 := rfl
example : boxNat 90 = 181#64 := rfl
example : boxNat 80 = 161#64 := rfl

-- Fail-closed budget checks on `armTarget` (`forestSum`: `maxFrame = 48`, `minEntry = 272`).
#eval show Lean.CoreM Unit from do
  let rtSigs := rtC0CoreMod.fns.map Fn.sig
  let badFrame : List BudgetFn :=
    [⟨mutRecDemoRoseFn, 40, 272⟩, ⟨mutRecDemoForestFn, 40, 272⟩]
  let badEntry : List BudgetFn :=
    [⟨mutRecDemoRoseFn, 48, 264⟩, ⟨mutRecDemoForestFn, 48, 264⟩]
  if (evalLinkedBudgetSccChunks armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      rtC0CoreArm64AllExt rtSigs rtExitSyms 64 badFrame 1 1040 0
      mutRecDemoExportBounds).toOption.isSome then
    throwError "expected maxFrame=40 < 48 rejection on arm64 for mutual SCC"
  if (evalLinkedBudgetSccChunks armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      rtC0CoreArm64AllExt rtSigs rtExitSyms 64 badEntry 1 1040 0
      mutRecDemoExportBounds).toOption.isSome then
    throwError "expected minEntry=264 < 272 rejection on arm64 for mutual SCC"

#print axioms LeanQbe.T.LeanLCNF.mutRec_budgetSemScc
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64ProgCert
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64Cert
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64ProgCert_numChunks
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64Cert_roseSum_bound
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64Cert_forestSum_bound
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64_roseSum_fnSpec
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64_forestSum_fnSpec
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64_roseSum_sample_run
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64_forestSum_sample_run
#print axioms LeanQbe.T.Arm64.mutRecDemoArm64_forestSum_nil_run

end LeanQbeTest.T.LcnfC0MutRecDemoArm64Test
