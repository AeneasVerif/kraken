module

public import LeanQbe.T.Amd64.LcnfC0MutRecDemoCertX64
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo

/-!
# Verification Suite for SysV x86-64 Mutual 2-Function SCC (`LcnfC0MutRecDemoCertX64`)

1. Architecture-isolation `#eval` audit (`0` `Kraken.AArch64` / `LeanQbe.T.Arm64` imports).
2. Structural guards verifying genuine 2-function mutual recursion (`roseSum → forestSum`,
   `forestSum → {roseSum, forestSum}`), single-chunk `.recBudgetSCC` compilation (`numChunks = 1`),
   depth `D = 16` / bound `1040 ≤ 2048`, and fail-closed budget rejection (`maxFrame < 48`,
   `minEntry < 272`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0MutRecDemoX64Test

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let arm := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.AArch64" || s.startsWith "LeanQbe.T.Arm64"
  if !arm.isEmpty then
    throwError "LcnfC0MutRecDemoX64Test leaked Arm64 imports: {arm.toList}"

#guard mutRecDemoLcMod.decls.length == 2
#guard mutRecDemoTfs.length == 2
#guard mutRecDemoLinkedMod.fns.length == 88
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
#guard checkLegalSigAll x64LegalTarget mutRecDemoProgMod.fns
example : MutRecDemo.roseDepth sampleRose = 7 := rfl
example : MutRecDemo.forestDepth sampleForest = 6 := rfl
example : MutRecDemo.roseSum sampleRose = 90 := rfl
example : MutRecDemo.forestSum sampleForest = 80 := rfl
example : boxNat 90 = 181#64 := rfl
example : boxNat 80 = 161#64 := rfl

-- Fail-closed budget checks on `x64Target` (`forestSum`: `maxFrame = 48`, `minEntry = 272`).
#eval show Lean.CoreM Unit from do
  let rtSigs := rtC0CoreMod.fns.map Fn.sig
  let badFrame : List BudgetFn :=
    [⟨mutRecDemoRoseFn, 40, 272⟩, ⟨mutRecDemoForestFn, 40, 272⟩]
  let badEntry : List BudgetFn :=
    [⟨mutRecDemoRoseFn, 48, 264⟩, ⟨mutRecDemoForestFn, 48, 264⟩]
  if (evalLinkedBudgetSccChunks x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      rtC0CoreAllExt rtSigs rtExitSyms 64 badFrame 1 1040 0
      mutRecDemoExportBounds).toOption.isSome then
    throwError "expected maxFrame=40 < 48 rejection on x64 for mutual SCC"
  if (evalLinkedBudgetSccChunks x64Target.toIsa x64LegalTarget x64Target.frame.raBytes
      rtC0CoreAllExt rtSigs rtExitSyms 64 badEntry 1 1040 0
      mutRecDemoExportBounds).toOption.isSome then
    throwError "expected minEntry=264 < 272 rejection on x64 for mutual SCC"

#print axioms LeanQbe.T.LeanLCNF.mutRec_budgetSemScc
#print axioms LeanQbe.T.Amd64.mutRecDemoX64ProgCert
#print axioms LeanQbe.T.Amd64.mutRecDemoX64Cert
#print axioms LeanQbe.T.Amd64.mutRecDemoX64ProgCert_numChunks
#print axioms LeanQbe.T.Amd64.mutRecDemoX64Cert_roseSum_bound
#print axioms LeanQbe.T.Amd64.mutRecDemoX64Cert_forestSum_bound
#print axioms LeanQbe.T.Amd64.mutRecDemoX64_roseSum_fnSpec
#print axioms LeanQbe.T.Amd64.mutRecDemoX64_forestSum_fnSpec
#print axioms LeanQbe.T.Amd64.mutRecDemoX64_roseSum_sample_run
#print axioms LeanQbe.T.Amd64.mutRecDemoX64_forestSum_sample_run
#print axioms LeanQbe.T.Amd64.mutRecDemoX64_forestSum_nil_run

end LeanQbeTest.T.LcnfC0MutRecDemoX64Test
