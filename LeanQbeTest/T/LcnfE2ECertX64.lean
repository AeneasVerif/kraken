module

import LeanQbeTest.T.LcnfE2EDemos
import LeanQbe.T.Amd64.LcnfC0FullCertX64
import LeanQbe.T.Amd64.LcnfC0RecDemoCertX64
import LeanQbe.T.Amd64.LcnfC0TreeDemoCertX64
import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.MainCertFlat
meta import Lean
import LeanQbe.T.MainCertElab
import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64
meta import LeanQbeTest.T.LcnfE2EDemos
meta import LeanQbe.T.LeanLCNF.LcnfC0LinkKit
meta import Kraken.X64.Syntax

/-!
# End-to-End SysV x86-64 `lean_fn_compiled` Certificates (`LcnfE2ECertX64`)

Concrete x86-64 native machine-code compilation theorems instantiated from the target-parametric
proofs in `LcnfE2EDemos` while reusing pre-verified `rtC0CoreCert`, `recDemoX64Cert`, and
`treeDemoX64Cert` with ZERO runtime recompilation and ZERO hand-written Tier-H or Tier-T WP:

1. `e2eAddNatX64_fnSpec` (`E2EAddNat.addNat`, `lean_fn_compiled_acyclic`)
2. `e2eFactAccX64_fnSpec` (`E2EFactAcc.factAcc`, `lean_fn_compiled_loop`)
3. `e2eListSumX64_fnSpec` (`RecDemo.listSum`, `lean_fn_compiled_scc` reusing `recDemoX64Cert`)
4. `e2eTreeSumX64_fnSpec` & `e2eTreeSizeX64_fnSpec` (`TreeDemo.{treeSum,treeSize}`, reusing
   `treeDemoX64Cert`)
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LcnfE2ECertX64

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.LeanLCNF.Sem LeanQbe.T.Amd64
open LeanQbeTest.T.LcnfE2EDemos Kraken

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for m in env.allImportedModuleNames do
    let s := m.toString
    if s.startsWith "LeanQbe.T.Arm64" || s.startsWith "Kraken.AArch64" then
      throwError "arch isolation violation: x86-64 cert imported {s}"

/-! ## 1. `E2EAddNat.addNat` (`lean_fn_compiled_acyclic` + `linkRtC0Cert rtC0CoreCert`) -/

compile_linked_chunks! e2eAddNatX64ProgCert x64Target x64Layout x64LegalTarget x64LabelClean
  (lcnfProgMod e2eAddNatTfs) 1 (ext := rtC0CoreAllExt) (exits := rtExitSyms) (nX := 64)
  (maxBound := 2048) (maxDirs := 600) (flat := true)

noncomputable def e2eAddNatX64Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      e2eAddNatLinkedMod [] rtExitSyms 64 2048 :=
  linkRtC0Cert rtC0CoreCert e2eAddNatX64ProgCert (by t_kernel_rfl)

theorem e2eAddNatLinkedMod_x64_legalSig :
    LegalSigAll x64LegalTarget e2eAddNatLinkedMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-- Closed x86-64 machine-code theorem for extracted `E2EAddNat.addNat`. -/
theorem e2eAddNatX64_fnSpec :
    x64Target.Defined e2eAddNatX64Cert.host e2eAddNatName ∧
      x64Target.FnSpec e2eAddNatX64Cert.host e2eAddNatName
        (encSpec2 (e2eAddNatLcMod.decls[0])
          (fun a b _ _ _ => E2EAddNat.addNat a b < 2 ^ 63) E2EAddNat.addNat)
        (e2eAddNatX64Cert.bound e2eAddNatName) 64 :=
  e2eAddNat_compiled e2eAddNatX64Cert e2eAddNatLinkedMod_x64_legalSig

/-! ## 2. `E2EFactAcc.factAcc` (`lean_fn_compiled_loop` + `linkRtC0Cert rtC0CoreCert`) -/

compile_linked_chunks! e2eFactAccX64ProgCert x64Target x64Layout x64LegalTarget x64LabelClean
  (lcnfProgMod e2eFactAccTfs) 1 (ext := rtC0CoreAllExt) (exits := rtExitSyms) (nX := 64)
  (maxBound := 2048) (maxDirs := 600) (flat := true)

noncomputable def e2eFactAccX64Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      e2eFactAccLinkedMod [] rtExitSyms 64 2048 :=
  linkRtC0Cert rtC0CoreCert e2eFactAccX64ProgCert (by t_kernel_rfl)

theorem e2eFactAccLinkedMod_x64_legalSig :
    LegalSigAll x64LegalTarget e2eFactAccLinkedMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-- Closed x86-64 machine-code theorem for extracted `E2EFactAcc.factAcc` (`k = 20`). -/
theorem e2eFactAccX64_fnSpec :
    x64Target.Defined e2eFactAccX64Cert.host e2eFactAccName ∧
      x64Target.FnSpec e2eFactAccX64Cert.host e2eFactAccName
        (encSpec2 (e2eFactAccLcMod.decls[0])
          (fun n acc _ _ _ =>
            n ≤ 20 ∧ n < 2 ^ 63 ∧ acc < 2 ^ 63 ∧ E2EFactAcc.factAcc n acc < 2 ^ 63)
          E2EFactAcc.factAcc)
        (e2eFactAccX64Cert.bound e2eFactAccName) 64 :=
  e2eFactAcc_compiled e2eFactAccX64Cert e2eFactAccLinkedMod_x64_legalSig 20

/-! ## 3. Reusing `recDemoX64Cert` & `treeDemoX64Cert` (Zero Recompilation) -/

/-- Closed x86-64 `lean_fn_compiled_scc` theorem for `RecDemo.listSum` reusing `recDemoX64Cert`. -/
theorem e2eListSumX64_fnSpec :
    x64Target.Defined recDemoX64Cert.host recDemoListSumName ∧
      x64Target.FnSpec recDemoX64Cert.host recDemoListSumName
        (encSpec1 (recDemoLcMod.decls[0])
          (fun xs _ _ _ => xs.length < recDemoDepthBudget ∧ RecDemo.listSum xs < 2 ^ 63)
          RecDemo.listSum)
        (recDemoX64Cert.bound recDemoListSumName) 64 :=
  recDemo_listSum_compiled recDemoX64Cert rtC0CoreCert rtC0CoreSccCertX64.callsCheck
    ⟨_, _, _, _, _, rfl⟩ recDemoLinkedMod_fns_wf
    (by rw [recDemoX64Cert_listSum_bound]; decide) (by decide) (by decide)

/-- Closed x86-64 `lean_fn_compiled_scc` theorem for `TreeDemo.treeSum` reusing
`treeDemoX64Cert`. -/
theorem e2eTreeSumX64_fnSpec :
    x64Target.Defined treeDemoX64Cert.host treeDemoSumName ∧
      x64Target.FnSpec treeDemoX64Cert.host treeDemoSumName
        (encSpec1 (treeDemoLcMod.decls[0])
          (fun t _ _ _ => t.depth < treeDemoDepthBudget ∧ TreeDemo.treeSum t < 2 ^ 63)
          TreeDemo.treeSum)
        (treeDemoX64Cert.bound treeDemoSumName) 64 :=
  treeDemo_treeSum_compiled treeDemoX64Cert rtC0CoreCert rtC0CoreSccCertX64.callsCheck
    ⟨_, _, _, _, _, _, _, _, rfl⟩ treeDemoLinkedMod_fns_wf
    (by rw [treeDemoX64Cert_treeSum_bound]; decide) (by decide) (by decide)

/-- Closed x86-64 `lean_fn_compiled_scc` theorem for `TreeDemo.treeSize` reusing
`treeDemoX64Cert`. -/
theorem e2eTreeSizeX64_fnSpec :
    x64Target.Defined treeDemoX64Cert.host treeDemoSizeName ∧
      x64Target.FnSpec treeDemoX64Cert.host treeDemoSizeName
        (encSpec1 (treeDemoLcMod.decls[1])
          (fun t _ _ _ => t.depth < treeDemoDepthBudget ∧ TreeDemo.treeSize t < 2 ^ 63)
          TreeDemo.treeSize)
        (treeDemoX64Cert.bound treeDemoSizeName) 64 :=
  treeDemo_treeSize_compiled treeDemoX64Cert rtC0CoreCert rtC0CoreSccCertX64.callsCheck
    ⟨_, _, _, _, _, rfl⟩ treeDemoLinkedMod_fns_wf
    (by rw [treeDemoX64Cert_treeSize_bound]; decide) (by decide) (by decide)

#print axioms e2eAddNatX64_fnSpec
#print axioms e2eFactAccX64_fnSpec
#print axioms e2eListSumX64_fnSpec
#print axioms e2eTreeSumX64_fnSpec
#print axioms e2eTreeSizeX64_fnSpec

end LeanQbeTest.T.LcnfE2ECertX64
