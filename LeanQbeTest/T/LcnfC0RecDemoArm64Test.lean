module

public import LeanQbe.T.Arm64.LcnfC0RecDemoCertArm64
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0RecDemo

/-!
# Verification Suite for AAPCS64 AArch64 Recursive `RecDemo.listSum` (`LcnfC0RecDemoCertArm64`)

1. Architecture-isolation `#eval` audit (`0` `Kraken.X64` / `LeanQbe.T.Amd64` imports).
2. Structural guards verifying genuine non-tail self-recursive `.call` SCC lowering, exact
   depth `D = 16` / bound `768 ≤ 2048`, and fail-closed budget rejection (`maxFrame < 32`,
   `minEntry < 256`).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfC0RecDemoArm64Test

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let x64 := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64.isEmpty then
    throwError "LcnfC0RecDemoArm64Test leaked X64/Amd64 imports: {x64.toList}"

#guard recDemoLcMod.decls.length == 1
#guard recDemoTfs.length == 1
#guard recDemoLinkedMod.fns.length == 87
#guard recDemoLinkedMod.externs.isEmpty
#guard recDemoLinkedMod.exits == ["lcnf_panic"]
#guard !(hasSelfTail "LeanQbe.T.LeanLCNF.RecDemo.listSum" 1 recDemoLcMod.decls[0]!.body)
#guard recDemoListSumFn.callees.any (fun s => s.1 == recDemoListSumName)
#guard recDemoListSumFn.callees.any (fun s => s.1 == "lcnf_nat_slow")
#guard recDemoListSumFn.callees.any (fun s => s.1 == "lcnf_dec_ref_cold")
#guard !recDemoProgMod.checkAcyclic
#guard LinkRec.checkCyclic
  ⟨recDemoProgMod.fns, externsOfSigs (rtC0CoreMod.fns.map Fn.sig), rtExitSyms⟩
#guard checkLegalSigAll armLegalTarget recDemoProgMod.fns
#guard RecDemo.listSum [10, 20, 30] == 60
example : boxNat 60 = 121#64 := rfl

-- Fail-closed budget checks on `armTarget` (`effFrame + raBytes = 32`, `lcnf_nat_slow = 224`).
#eval show Lean.CoreM Unit from do
  let rtSigs := rtC0CoreMod.fns.map Fn.sig
  let badFrame : List BudgetFn := [⟨recDemoListSumFn, 24, 256⟩]
  let badEntry : List BudgetFn := [⟨recDemoListSumFn, 32, 248⟩]
  if (evalLinkedBudgetSccChunks armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      rtC0CoreArm64AllExt rtSigs rtExitSyms 64 badFrame 1 768 0
      [(recDemoListSumName, 768)]).toOption.isSome then
    throwError "expected maxFrame=24 < 32 rejection on arm64"
  if (evalLinkedBudgetSccChunks armTarget.toIsa armLegalTarget armTarget.frame.raBytes
      rtC0CoreArm64AllExt rtSigs rtExitSyms 64 badEntry 1 768 0
      [(recDemoListSumName, 768)]).toOption.isSome then
    throwError "expected minEntry=248 < 256 rejection on arm64"

#print axioms LeanQbe.T.LeanLCNF.listSum_budgetSemScc
#print axioms LeanQbe.T.Arm64.recDemoArm64ProgCert
#print axioms LeanQbe.T.Arm64.recDemoArm64Cert
#print axioms LeanQbe.T.Arm64.recDemoArm64Cert_listSum_bound
#print axioms LeanQbe.T.Arm64.recDemoArm64_listSum_fnSpec
#print axioms LeanQbe.T.Arm64.recDemoArm64_listSum_10_20_30_run
#print axioms LeanQbe.T.Arm64.recDemoArm64_listSum_nil_run

end LeanQbeTest.T.LcnfC0RecDemoArm64Test
