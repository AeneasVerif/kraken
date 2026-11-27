module

public import LeanQbe.T.Amd64.LcnfC0FullCertX64
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0TreeDemoProof
public import LeanQbe.T.MainCertScc
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo

/-!
# SysV x86-64 `compile_linked_budget_scc!` Certificate for `TreeDemo.{treeSum, treeSize}`

First SysV x86-64 (`x64Target`) non-linear (two-branch) structurally recursive Lean `LCNF`
program certified through `compile_linked_budget_scc!` (`maxFrame = 48`, `minEntry = 272`,
depth `D = 16`, `exportBound = 1040 ≤ 2048`) and compositionally appended onto
`LinkedCertScc.ofLinkedCert rtC0CoreCert` (`86` pure-C0 runtime functions,
`exits = ["lcnf_panic"]`, `nX = 64`, `0` externs):

1. `treeDemoX64ProgCert`: `2`-chunk `.recBudgetSCC` user certificate (`treeSum`, `treeSize`)
   with `ext := rtC0CoreAllExt`.
2. `treeDemoX64Cert`: closed `88`-function `LinkedCertScc` (`maxBound = 2048`,
   `bound treeDemoSumName = 1040`, `bound treeDemoSizeName = 1040`).
3. `treeDemoX64_treeSum_fnSpec` & `treeDemoX64_treeSize_fnSpec`: source-level `x64Target.Defined`
   + `x64Target.FnSpec` via `LinkedCertScc.fnSpec_host_src_of_le`.
4. `treeDemoX64_treeSum_sample_run`, `treeDemoX64_treeSum_leaf_run`,
   `treeDemoX64_treeSize_sample_run`, & `treeDemoX64_treeSize_leaf_run`: closed concrete x86-64
   `Eventually` machine execution witnesses (`sampleTree → 65` / `4`, `leaf → 0`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

/-! ## 1. `compile_linked_budget_scc!` & Compositional `LinkedCertScc.append` -/

compile_linked_budget_scc! treeDemoX64ProgCert x64Target x64Layout x64LegalTarget x64LabelClean
  treeDemoBudgetMod 1 (maxBound := treeDemoExportBound)
  (exportBounds := treeDemoExportBounds)
  (ext := rtC0CoreAllExt) (extSigs := rtC0CoreMod.fns.map Fn.sig)
  (exits := rtExitSyms) (nX := 64) (flat := true)

/-- Lift of the `86`-function acyclic runtime `rtC0CoreCert` into `LinkedCertScc`. -/
@[expose] noncomputable def treeDemoRtSccCertX64 :
    LinkedCertScc x64Target x64Layout x64LegalTarget x64LabelClean
      rtC0CoreMod [] rtExitSyms 64 2048 [] :=
  LinkedCertScc.ofLinkedCert rtC0CoreCert rfl (by t_kernel_rfl)

/-- Full `88`-function SysV x86-64 `LinkedCertScc` combining `rtC0CoreCert` (`86` fns) and
`treeDemoX64ProgCert` (`2` `.recBudgetSCC` fns, `bound = 1040`, `maxBound = 2048`). -/
@[expose] noncomputable def treeDemoX64Cert :
    LinkedCertScc x64Target x64Layout x64LegalTarget x64LabelClean
      treeDemoLinkedMod [] rtExitSyms 64 (Nat.max 2048 treeDemoExportBound) [] :=
  treeDemoRtSccCertX64.append treeDemoX64ProgCert rfl (by t_kernel_rfl) (by t_kernel_rfl)

theorem treeDemoX64ProgCert_numChunks : treeDemoX64ProgCert.numChunks = 2 := rfl

theorem treeDemoX64Cert_treeSum_bound :
    treeDemoX64Cert.bound treeDemoSumName = 1040 := rfl

theorem treeDemoX64Cert_treeSize_bound :
    treeDemoX64Cert.bound treeDemoSizeName = 1040 := rfl

/-! ## 2. Semantic Bridges & `x64Target.FnSpec` (`fnSpec_host_src_of_le`) -/

private theorem treeDemoX64Cert_chunksShape : TreeDemoChunksShape treeDemoX64Cert :=
  ⟨treeDemoRtSccCertX64.chunks, _, _, _, _, _, _, rfl⟩

theorem treeDemoX64_treeSum_sem :
    ∀ xs m Q X, treeSumSpec treeDemoDepthBudget xs m Q X →
      treeDemoX64Cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSumName [i64, i64] [i64]
        xs m Q X :=
  treeDemoCert_treeSum_sem treeDemoX64Cert treeDemoX64Cert_chunksShape

theorem treeDemoX64_treeSize_sem :
    ∀ xs m Q X, treeSizeSpec treeDemoDepthBudget xs m Q X →
      treeDemoX64Cert.sem (fun _ _ _ _ _ _ _ => False) treeDemoSizeName [i64, i64] [i64]
        xs m Q X :=
  treeDemoCert_treeSize_sem treeDemoX64Cert treeDemoX64Cert_chunksShape

theorem treeDemoX64_treeSum_fnSpec :
    x64Target.Defined treeDemoX64Cert.host treeDemoSumName ∧
      x64Target.FnSpec treeDemoX64Cert.host treeDemoSumName (treeSumSpec treeDemoDepthBudget)
        (treeDemoX64Cert.bound treeDemoSumName) 64 :=
  treeDemoCert_treeSum_fnSpec treeDemoX64Cert (by decide) (by decide) treeDemoX64_treeSum_sem

theorem treeDemoX64_treeSize_fnSpec :
    x64Target.Defined treeDemoX64Cert.host treeDemoSizeName ∧
      x64Target.FnSpec treeDemoX64Cert.host treeDemoSizeName (treeSizeSpec treeDemoDepthBudget)
        (treeDemoX64Cert.bound treeDemoSizeName) 64 :=
  treeDemoCert_treeSize_fnSpec treeDemoX64Cert (by decide) (by decide) treeDemoX64_treeSize_sem

/-! ## 3. Closed Concrete x86-64 `Eventually` Execution Witnesses -/

/-- Closed x86-64 machine execution of `TreeDemo.treeSum` on asymmetric `sampleTree`
(`node 10 (node 20 leaf (node 5 leaf leaf)) (node 30 leaf leaf)`, `128` bytes @ `0x1000#64`),
returning `boxNat 65 = 131#64` in `%rax` (`XPost := False`). -/
theorem treeDemoX64_treeSum_sample_run :
    letI : Host := treeDemoX64Cert.host
    Eventually (step1 treeDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 65)
      ⟨x64Init.initState (as := [i64, i64]) (treeDemoX64Cert.bound treeDemoSumName)
          sampleTreeBytes (0#64, 0x1000#64, ()),
        Labels.label treeDemoSumName⟩ :=
  treeDemoCert_treeSum_eventually treeDemoX64Cert x64Init (by decide) (by decide) (by decide)
    treeDemoX64_treeSum_sem sampleTreeBytes 0#64 0x1000#64 sampleTree
    (by rw [sampleTreeBytes_length]; decide) (by decide) (by decide) sampleTree_treeNatAt
    (by decide)

/-- Closed x86-64 machine execution of `TreeDemo.treeSum` on `Tree.leaf` (`1#64`),
returning `boxNat 0 = 1#64` in `%rax`. -/
theorem treeDemoX64_treeSum_leaf_run :
    letI : Host := treeDemoX64Cert.host
    Eventually (step1 treeDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 0)
      ⟨x64Init.initState (as := [i64, i64]) (treeDemoX64Cert.bound treeDemoSumName)
          [] (0#64, 1#64, ()),
        Labels.label treeDemoSumName⟩ :=
  treeDemoCert_treeSum_eventually treeDemoX64Cert x64Init (by decide) (by decide) (by decide)
    treeDemoX64_treeSum_sem [] 0#64 1#64 .leaf
    (by decide) (by decide) (by decide) sampleTreeLeaf_treeNatAt (by decide)

/-- Closed x86-64 machine execution of `TreeDemo.treeSize` on asymmetric `sampleTree`
(`128` bytes @ `0x1000#64`), returning `boxNat 4 = 9#64` in `%rax`. -/
theorem treeDemoX64_treeSize_sample_run :
    letI : Host := treeDemoX64Cert.host
    Eventually (step1 treeDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 4)
      ⟨x64Init.initState (as := [i64, i64]) (treeDemoX64Cert.bound treeDemoSizeName)
          sampleTreeBytes (0#64, 0x1000#64, ()),
        Labels.label treeDemoSizeName⟩ :=
  treeDemoCert_treeSize_eventually treeDemoX64Cert x64Init (by decide) (by decide) (by decide)
    treeDemoX64_treeSize_sem sampleTreeBytes 0#64 0x1000#64 sampleTree
    (by rw [sampleTreeBytes_length]; decide) (by decide) (by decide) sampleTree_treeNatAt
    (by decide)

/-- Closed x86-64 machine execution of `TreeDemo.treeSize` on `Tree.leaf` (`1#64`),
returning `boxNat 0 = 1#64` in `%rax`. -/
theorem treeDemoX64_treeSize_leaf_run :
    letI : Host := treeDemoX64Cert.host
    Eventually (step1 treeDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 0)
      ⟨x64Init.initState (as := [i64, i64]) (treeDemoX64Cert.bound treeDemoSizeName)
          [] (0#64, 1#64, ()),
        Labels.label treeDemoSizeName⟩ :=
  treeDemoCert_treeSize_eventually treeDemoX64Cert x64Init (by decide) (by decide) (by decide)
    treeDemoX64_treeSize_sem [] 0#64 1#64 .leaf
    (by decide) (by decide) (by decide) sampleTreeLeaf_treeNatAt (by decide)

end LeanQbe.T.Amd64
