module

public import LeanQbeTest.T.LcnfE2EDemos
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public import LeanQbe.T.Arm64.LcnfC0RecDemoCertArm64
public import LeanQbe.T.Arm64.LcnfC0TreeDemoCertArm64
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainCertFlat
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public meta import LeanQbeTest.T.LcnfE2EDemos
public meta import LeanQbe.T.LeanLCNF.LcnfC0LinkKit
public meta import Kraken.AArch64.Syntax

/-!
# End-to-End AAPCS64 Arm64 `lean_fn_compiled` Certificates (`LcnfE2ECertArm64`)

Concrete AArch64 native machine-code compilation theorems instantiated from the target-parametric
proofs in `LcnfE2EDemos` while reusing pre-verified `rtC0CoreArm64Cert`, `recDemoArm64Cert`, and
`treeDemoArm64Cert` with ZERO runtime recompilation and ZERO hand-written Tier-H or Tier-T WP:

1. `e2eAddNatArm64_fnSpec` (`E2EAddNat.addNat`, `lean_fn_compiled_acyclic`)
2. `e2eFactAccArm64_fnSpec` (`E2EFactAcc.factAcc`, `lean_fn_compiled_loop`)
3. `e2eListSumArm64_fnSpec` (`RecDemo.listSum`, `lean_fn_compiled_scc` reusing `recDemoArm64Cert`)
4. `e2eTreeSumArm64_fnSpec` & `e2eTreeSizeArm64_fnSpec` (`TreeDemo.{treeSum,treeSize}`, reusing
   `treeDemoArm64Cert`)
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfE2ECertArm64

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.LeanLCNF.Sem LeanQbe.T.Arm64
open LeanQbeTest.T.LcnfE2EDemos Kraken

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for m in env.allImportedModuleNames do
    let s := m.toString
    if s.startsWith "LeanQbe.T.Amd64" || s.startsWith "Kraken.X64" then
      throwError "arch isolation violation: Arm64 cert imported {s}"

/-! ## 1. `E2EAddNat.addNat` (`lean_fn_compiled_acyclic` + `linkRtC0Cert rtC0CoreArm64Cert`) -/

compile_linked_chunks! e2eAddNatArm64ProgCert armTarget armLayout armLegalTarget armLabelClean
  (lcnfProgMod e2eAddNatTfs) 1 (ext := rtC0CoreArm64AllExt) (exits := rtExitSyms) (nX := 64)
  (maxBound := 2048) (maxDirs := 600) (flat := true)

noncomputable def e2eAddNatArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      e2eAddNatLinkedMod [] rtExitSyms 64 2048 :=
  linkRtC0Cert rtC0CoreArm64Cert e2eAddNatArm64ProgCert (by t_kernel_rfl)

theorem e2eAddNatLinkedMod_arm64_legalSig :
    LegalSigAll armLegalTarget e2eAddNatLinkedMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-- Closed AArch64 machine-code theorem for extracted `E2EAddNat.addNat`. -/
theorem e2eAddNatArm64_fnSpec :
    armTarget.Defined e2eAddNatArm64Cert.host e2eAddNatName ∧
      armTarget.FnSpec e2eAddNatArm64Cert.host e2eAddNatName
        (encSpec2 (e2eAddNatLcMod.decls[0])
          (fun a b _ _ _ => E2EAddNat.addNat a b < 2 ^ 63) E2EAddNat.addNat)
        (e2eAddNatArm64Cert.bound e2eAddNatName) 64 :=
  e2eAddNat_compiled e2eAddNatArm64Cert e2eAddNatLinkedMod_arm64_legalSig

/-! ## 2. `E2EFactAcc.factAcc` (`lean_fn_compiled_loop` + `linkRtC0Cert rtC0CoreArm64Cert`) -/

compile_linked_chunks! e2eFactAccArm64ProgCert armTarget armLayout armLegalTarget armLabelClean
  (lcnfProgMod e2eFactAccTfs) 1 (ext := rtC0CoreArm64AllExt) (exits := rtExitSyms) (nX := 64)
  (maxBound := 2048) (maxDirs := 600) (flat := true)

noncomputable def e2eFactAccArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      e2eFactAccLinkedMod [] rtExitSyms 64 2048 :=
  linkRtC0Cert rtC0CoreArm64Cert e2eFactAccArm64ProgCert (by t_kernel_rfl)

theorem e2eFactAccLinkedMod_arm64_legalSig :
    LegalSigAll armLegalTarget e2eFactAccLinkedMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-- Closed AArch64 machine-code theorem for extracted `E2EFactAcc.factAcc` (`k = 20`). -/
theorem e2eFactAccArm64_fnSpec :
    armTarget.Defined e2eFactAccArm64Cert.host e2eFactAccName ∧
      armTarget.FnSpec e2eFactAccArm64Cert.host e2eFactAccName
        (encSpec2 (e2eFactAccLcMod.decls[0])
          (fun n acc _ _ _ =>
            n ≤ 20 ∧ n < 2 ^ 63 ∧ acc < 2 ^ 63 ∧ E2EFactAcc.factAcc n acc < 2 ^ 63)
          E2EFactAcc.factAcc)
        (e2eFactAccArm64Cert.bound e2eFactAccName) 64 :=
  e2eFactAcc_compiled e2eFactAccArm64Cert e2eFactAccLinkedMod_arm64_legalSig 20

/-! ## 3. Reusing `recDemoArm64Cert` & `treeDemoArm64Cert` (Zero Recompilation) -/

/-- Closed AArch64 `lean_fn_compiled_scc` theorem for `RecDemo.listSum` reusing
`recDemoArm64Cert`. -/
theorem e2eListSumArm64_fnSpec :
    armTarget.Defined recDemoArm64Cert.host recDemoListSumName ∧
      armTarget.FnSpec recDemoArm64Cert.host recDemoListSumName
        (encSpec1 (recDemoLcMod.decls[0])
          (fun xs _ _ _ => xs.length < recDemoDepthBudget ∧ RecDemo.listSum xs < 2 ^ 63)
          RecDemo.listSum)
        (recDemoArm64Cert.bound recDemoListSumName) 64 :=
  recDemo_listSum_compiled recDemoArm64Cert rtC0CoreArm64Cert rtC0CoreSccCertArm64.callsCheck
    ⟨_, _, _, _, _, rfl⟩ recDemoLinkedMod_fns_wf
    (by rw [recDemoArm64Cert_listSum_bound]; decide) (by decide) (by decide)

/-- Closed AArch64 `lean_fn_compiled_scc` theorem for `TreeDemo.treeSum` reusing
`treeDemoArm64Cert`. -/
theorem e2eTreeSumArm64_fnSpec :
    armTarget.Defined treeDemoArm64Cert.host treeDemoSumName ∧
      armTarget.FnSpec treeDemoArm64Cert.host treeDemoSumName
        (encSpec1 (treeDemoLcMod.decls[0])
          (fun t _ _ _ => t.depth < treeDemoDepthBudget ∧ TreeDemo.treeSum t < 2 ^ 63)
          TreeDemo.treeSum)
        (treeDemoArm64Cert.bound treeDemoSumName) 64 :=
  treeDemo_treeSum_compiled treeDemoArm64Cert rtC0CoreArm64Cert rtC0CoreSccCertArm64.callsCheck
    ⟨_, _, _, _, _, _, _, _, rfl⟩ treeDemoLinkedMod_fns_wf
    (by rw [treeDemoArm64Cert_treeSum_bound]; decide) (by decide) (by decide)

/-- Closed AArch64 `lean_fn_compiled_scc` theorem for `TreeDemo.treeSize` reusing
`treeDemoArm64Cert`. -/
theorem e2eTreeSizeArm64_fnSpec :
    armTarget.Defined treeDemoArm64Cert.host treeDemoSizeName ∧
      armTarget.FnSpec treeDemoArm64Cert.host treeDemoSizeName
        (encSpec1 (treeDemoLcMod.decls[1])
          (fun t _ _ _ => t.depth < treeDemoDepthBudget ∧ TreeDemo.treeSize t < 2 ^ 63)
          TreeDemo.treeSize)
        (treeDemoArm64Cert.bound treeDemoSizeName) 64 :=
  treeDemo_treeSize_compiled treeDemoArm64Cert rtC0CoreArm64Cert rtC0CoreSccCertArm64.callsCheck
    ⟨_, _, _, _, _, rfl⟩ treeDemoLinkedMod_fns_wf
    (by rw [treeDemoArm64Cert_treeSize_bound]; decide) (by decide) (by decide)

#print axioms e2eAddNatArm64_fnSpec
#print axioms e2eFactAccArm64_fnSpec
#print axioms e2eListSumArm64_fnSpec
#print axioms e2eTreeSumArm64_fnSpec
#print axioms e2eTreeSizeArm64_fnSpec

end LeanQbeTest.T.LcnfE2ECertArm64
