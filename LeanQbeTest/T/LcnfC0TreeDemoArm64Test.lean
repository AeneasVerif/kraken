module

public import LeanQbe.T.Arm64.LcnfC0TreeDemoCertArm64
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo

/-!
# Verification Suite for AAPCS64 AArch64 Binary-Tree Recursion (`LcnfC0TreeDemoCertArm64`)

1. Architecture-isolation `#eval` audit (`0` `Kraken.X64` / `LeanQbe.T.Amd64` imports).
2. Structural guards verifying genuine two-branch non-tail self-recursive `.call` SCC lowering
   for both `TreeDemo.treeSum` and `TreeDemo.treeSize`, exact depth `D = 16` / bound
   `1040 ≤ 2048`, and fail-closed budget rejection (`maxFrame < 48`, `minEntry < 272`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0TreeDemoArm64Test

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let x64 := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64.isEmpty then
    throwError "LcnfC0TreeDemoArm64Test leaked X64/Amd64 imports: {x64.toList}"

#guard treeDemoLcMod.decls.length == 2
#guard treeDemoTfs.length == 2
#guard treeDemoLinkedMod.fns.length == 88
#guard treeDemoLinkedMod.externs.isEmpty
#guard treeDemoLinkedMod.exits == ["lcnf_panic"]
#guard !(hasSelfTail "LeanQbe.T.LeanLCNF.TreeDemo.treeSum" 1 treeDemoLcMod.decls[0]!.body)
#guard !(hasSelfTail "LeanQbe.T.LeanLCNF.TreeDemo.treeSize" 1 treeDemoLcMod.decls[1]!.body)
#guard treeDemoSumFn.callees.any (fun s => s.1 == treeDemoSumName)
#guard treeDemoSumFn.callees.any (fun s => s.1 == "lcnf_nat_slow")
#guard treeDemoSumFn.callees.any (fun s => s.1 == "lcnf_dec_ref_cold")
#guard treeDemoSizeFn.callees.any (fun s => s.1 == treeDemoSizeName)
#guard treeDemoSizeFn.callees.any (fun s => s.1 == "lcnf_nat_slow")
#guard treeDemoSizeFn.callees.any (fun s => s.1 == "lcnf_dec_ref_cold")
#guard !treeDemoProgMod.checkAcyclic
#guard LinkRec.checkCyclic
  ⟨treeDemoProgMod.fns, externsOfSigs (rtC0CoreMod.fns.map Fn.sig), rtExitSyms⟩
#guard checkLegalSigAll armLegalTarget treeDemoProgMod.fns
example : sampleTree.depth = 3 := rfl
example : TreeDemo.treeSum sampleTree = 65 := rfl
example : TreeDemo.treeSize sampleTree = 4 := rfl
example : boxNat 65 = 131#64 := rfl
example : boxNat 4 = 9#64 := rfl

-- Fail-closed budget checks on `armTarget` (`effFrame + raBytes = 48`, `lcnf_nat_slow = 224`).
#eval show Lean.CoreM Unit from do
  let rtSigs := rtC0CoreMod.fns.map Fn.sig
  for (nm, fn) in [(treeDemoSumName, treeDemoSumFn), (treeDemoSizeName, treeDemoSizeFn)] do
    let badFrame : List BudgetFn := [⟨fn, 40, 272⟩]
    let badEntry : List BudgetFn := [⟨fn, 48, 264⟩]
    if (evalLinkedBudgetSccChunks armTarget.toIsa armLegalTarget armTarget.frame.raBytes
        rtC0CoreArm64AllExt rtSigs rtExitSyms 64 badFrame 1 1040 0
        [(nm, 1040)]).toOption.isSome then
      throwError "expected maxFrame=40 < 48 rejection on arm64 for {nm}"
    if (evalLinkedBudgetSccChunks armTarget.toIsa armLegalTarget armTarget.frame.raBytes
        rtC0CoreArm64AllExt rtSigs rtExitSyms 64 badEntry 1 1040 0
        [(nm, 1040)]).toOption.isSome then
      throwError "expected minEntry=264 < 272 rejection on arm64 for {nm}"

#print axioms LeanQbe.T.LeanLCNF.treeSum_budgetSemScc
#print axioms LeanQbe.T.LeanLCNF.treeSize_budgetSemScc
#print axioms LeanQbe.T.Arm64.treeDemoArm64ProgCert
#print axioms LeanQbe.T.Arm64.treeDemoArm64Cert
#print axioms LeanQbe.T.Arm64.treeDemoArm64Cert_treeSum_bound
#print axioms LeanQbe.T.Arm64.treeDemoArm64Cert_treeSize_bound
#print axioms LeanQbe.T.Arm64.treeDemoArm64_treeSum_fnSpec
#print axioms LeanQbe.T.Arm64.treeDemoArm64_treeSize_fnSpec
#print axioms LeanQbe.T.Arm64.treeDemoArm64_treeSum_sample_run
#print axioms LeanQbe.T.Arm64.treeDemoArm64_treeSum_leaf_run
#print axioms LeanQbe.T.Arm64.treeDemoArm64_treeSize_sample_run
#print axioms LeanQbe.T.Arm64.treeDemoArm64_treeSize_leaf_run

end LeanQbeTest.T.LcnfC0TreeDemoArm64Test
