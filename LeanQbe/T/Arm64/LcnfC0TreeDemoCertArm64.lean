module

public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0TreeDemoProof
public import LeanQbe.T.MainCertScc
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo

/-!
# AAPCS64 AArch64 `compile_linked_budget_scc!` Certificate for `TreeDemo.{treeSum, treeSize}`

First AAPCS64 AArch64 (`armTarget`) non-linear (two-branch) structurally recursive Lean `LCNF`
program certified through `compile_linked_budget_scc!` (`maxFrame = 48`, `minEntry = 272`,
depth `D = 16`, `exportBound = 1040 ≤ 2048`) and compositionally appended onto
`LinkedCertScc.ofLinkedCert rtC0CoreArm64Cert` (`86` pure-C0 runtime functions,
`exits = ["lcnf_panic"]`, `nX = 64`, `0` externs):

1. `treeDemoArm64ProgCert`: `2`-chunk `.recBudgetSCC` user certificate (`treeSum`, `treeSize`)
   with `ext := rtC0CoreArm64AllExt`.
2. `treeDemoArm64Cert`: closed `88`-function `LinkedCertScc` (`maxBound = 2048`,
   `bound treeDemoSumName = 1040`, `bound treeDemoSizeName = 1040`).
3. `treeDemoArm64_treeSum_fnSpec` & `treeDemoArm64_treeSize_fnSpec`: source-level
   `armTarget.Defined` + `armTarget.FnSpec` via `LinkedCertScc.fnSpec_host_src_of_le`.
4. `treeDemoArm64_treeSum_sample_run`, `treeDemoArm64_treeSum_leaf_run`,
   `treeDemoArm64_treeSize_sample_run`, & `treeDemoArm64_treeSize_leaf_run`: closed concrete
   AArch64 `Eventually` machine execution witnesses (`sampleTree → 65` / `4`, `leaf → 0`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

/-! ## 1. `compile_linked_budget_scc!` & Compositional `LinkedCertScc.append` -/

compile_linked_budget_scc! treeDemoArm64ProgCert armTarget armLayout armLegalTarget armLabelClean
  treeDemoBudgetMod 1 (maxBound := treeDemoExportBound)
  (exportBounds := treeDemoExportBounds)
  (ext := rtC0CoreArm64AllExt) (extSigs := rtC0CoreMod.fns.map Fn.sig)
  (exits := rtExitSyms) (nX := 64) (flat := true)

/-- Lift of the `86`-function acyclic runtime `rtC0CoreArm64Cert` into `LinkedCertScc`. -/
@[expose] noncomputable def treeDemoRtSccCertArm64 :
    LinkedCertScc armTarget armLayout armLegalTarget armLabelClean
      rtC0CoreMod [] rtExitSyms 64 2048 [] :=
  LinkedCertScc.ofLinkedCert rtC0CoreArm64Cert rfl (by t_kernel_rfl)

/-- Full `88`-function AAPCS64 AArch64 `LinkedCertScc` combining `rtC0CoreArm64Cert` (`86` fns)
and `treeDemoArm64ProgCert` (`2` `.recBudgetSCC` fns, `bound = 1040`, `maxBound = 2048`). -/
@[expose] noncomputable def treeDemoArm64Cert :
    LinkedCertScc armTarget armLayout armLegalTarget armLabelClean
      treeDemoLinkedMod [] rtExitSyms 64 (Nat.max 2048 treeDemoExportBound) [] :=
  treeDemoRtSccCertArm64.append treeDemoArm64ProgCert rfl (by t_kernel_rfl) (by t_kernel_rfl)

theorem treeDemoArm64ProgCert_numChunks : treeDemoArm64ProgCert.numChunks = 2 := rfl

theorem treeDemoArm64Cert_treeSum_bound :
    treeDemoArm64Cert.bound treeDemoSumName = 1040 := rfl

theorem treeDemoArm64Cert_treeSize_bound :
    treeDemoArm64Cert.bound treeDemoSizeName = 1040 := rfl

/-! ## 2. Semantic Bridges & `armTarget.FnSpec` (`fnSpec_host_src_of_le`) -/

private theorem treeDemoArm64Cert_chunksShape : TreeDemoChunksShape treeDemoArm64Cert :=
  ⟨treeDemoRtSccCertArm64.chunks, _, _, _, _, _, _, rfl⟩

theorem treeDemoArm64_treeSum_sem :
    ∀ xs m Q X, treeSumSpec treeDemoDepthBudget xs m Q X →
      treeDemoArm64Cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSumName [i64, i64] [i64]
        xs m Q X :=
  treeDemoCert_treeSum_sem treeDemoArm64Cert treeDemoArm64Cert_chunksShape

theorem treeDemoArm64_treeSize_sem :
    ∀ xs m Q X, treeSizeSpec treeDemoDepthBudget xs m Q X →
      treeDemoArm64Cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSizeName [i64, i64] [i64]
        xs m Q X :=
  treeDemoCert_treeSize_sem treeDemoArm64Cert treeDemoArm64Cert_chunksShape

theorem treeDemoArm64_treeSum_fnSpec :
    armTarget.Defined treeDemoArm64Cert.host treeDemoSumName ∧
      armTarget.FnSpec treeDemoArm64Cert.host treeDemoSumName (treeSumSpec treeDemoDepthBudget)
        (treeDemoArm64Cert.bound treeDemoSumName) 64 :=
  treeDemoCert_treeSum_fnSpec treeDemoArm64Cert (by decide) (by decide) treeDemoArm64_treeSum_sem

theorem treeDemoArm64_treeSize_fnSpec :
    armTarget.Defined treeDemoArm64Cert.host treeDemoSizeName ∧
      armTarget.FnSpec treeDemoArm64Cert.host treeDemoSizeName (treeSizeSpec treeDemoDepthBudget)
        (treeDemoArm64Cert.bound treeDemoSizeName) 64 :=
  treeDemoCert_treeSize_fnSpec treeDemoArm64Cert (by decide) (by decide) treeDemoArm64_treeSize_sem

/-! ## 3. Closed Concrete AArch64 `Eventually` Execution Witnesses -/

/-- Closed AArch64 machine execution of `TreeDemo.treeSum` on asymmetric `sampleTree`
(`node 10 (node 20 leaf (node 5 leaf leaf)) (node 30 leaf leaf)`, `128` bytes @ `0x1000#64`),
returning `boxNat 65 = 131#64` in `X0` (`XPost := False`). -/
theorem treeDemoArm64_treeSum_sample_run :
    letI : Host := treeDemoArm64Cert.host
    Eventually (step1 treeDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 65)
      ⟨armInit.initState (as := [i64, i64]) (treeDemoArm64Cert.bound treeDemoSumName)
          sampleTreeBytes (0#64, 0x1000#64, ()),
        Labels.label treeDemoSumName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ =>
      ⟨hpc, by simpa [armInit, get_reg, sampleTree, TreeDemo.treeSum] using hx0⟩)
    (treeDemoCert_treeSum_eventually treeDemoArm64Cert armInit (by decide) (by decide) (by decide)
      treeDemoArm64_treeSum_sem sampleTreeBytes 0#64 0x1000#64 sampleTree
      (by rw [sampleTreeBytes_length]; decide) (by decide) (by decide) sampleTree_treeNatAt
      (by decide))

/-- Closed AArch64 machine execution of `TreeDemo.treeSum` on `Tree.leaf` (`1#64`),
returning `boxNat 0 = 1#64` in `X0`. -/
theorem treeDemoArm64_treeSum_leaf_run :
    letI : Host := treeDemoArm64Cert.host
    Eventually (step1 treeDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 0)
      ⟨armInit.initState (as := [i64, i64]) (treeDemoArm64Cert.bound treeDemoSumName)
          [] (0#64, 1#64, ()),
        Labels.label treeDemoSumName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ => ⟨hpc, by simpa [armInit, get_reg, TreeDemo.treeSum] using hx0⟩)
    (treeDemoCert_treeSum_eventually treeDemoArm64Cert armInit (by decide) (by decide) (by decide)
      treeDemoArm64_treeSum_sem [] 0#64 1#64 .leaf
      (by decide) (by decide) (by decide) sampleTreeLeaf_treeNatAt (by decide))

/-- Closed AArch64 machine execution of `TreeDemo.treeSize` on asymmetric `sampleTree`
(`128` bytes @ `0x1000#64`), returning `boxNat 4 = 9#64` in `X0`. -/
theorem treeDemoArm64_treeSize_sample_run :
    letI : Host := treeDemoArm64Cert.host
    Eventually (step1 treeDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 4)
      ⟨armInit.initState (as := [i64, i64]) (treeDemoArm64Cert.bound treeDemoSizeName)
          sampleTreeBytes (0#64, 0x1000#64, ()),
        Labels.label treeDemoSizeName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ =>
      ⟨hpc, by simpa [armInit, get_reg, sampleTree, TreeDemo.treeSize] using hx0⟩)
    (treeDemoCert_treeSize_eventually treeDemoArm64Cert armInit (by decide) (by decide) (by decide)
      treeDemoArm64_treeSize_sem sampleTreeBytes 0#64 0x1000#64 sampleTree
      (by rw [sampleTreeBytes_length]; decide) (by decide) (by decide) sampleTree_treeNatAt
      (by decide))

/-- Closed AArch64 machine execution of `TreeDemo.treeSize` on `Tree.leaf` (`1#64`),
returning `boxNat 0 = 1#64` in `X0`. -/
theorem treeDemoArm64_treeSize_leaf_run :
    letI : Host := treeDemoArm64Cert.host
    Eventually (step1 treeDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 0)
      ⟨armInit.initState (as := [i64, i64]) (treeDemoArm64Cert.bound treeDemoSizeName)
          [] (0#64, 1#64, ()),
        Labels.label treeDemoSizeName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ => ⟨hpc, by simpa [armInit, get_reg, TreeDemo.treeSize] using hx0⟩)
    (treeDemoCert_treeSize_eventually treeDemoArm64Cert armInit (by decide) (by decide) (by decide)
      treeDemoArm64_treeSize_sem [] 0#64 1#64 .leaf
      (by decide) (by decide) (by decide) sampleTreeLeaf_treeNatAt (by decide))

end LeanQbe.T.Arm64
