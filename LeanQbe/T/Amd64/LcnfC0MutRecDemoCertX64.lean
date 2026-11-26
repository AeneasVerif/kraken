module

public import LeanQbe.T.Amd64.LcnfC0FullCertX64
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemoProof
public import LeanQbe.T.MainCertScc
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo

/-!
# SysV x86-64 `compile_linked_budget_scc!` Certificate for Mutual `{roseSum, forestSum}` SCC

First SysV x86-64 (`x64Target`) multi-function mutually-recursive Lean `LCNF` SCC certified as a
**single 2-function `.recBudgetSCC` chunk** (`maxFrame = 48`, `minEntry = 272`, depth `D = 16`,
`exportBound = 1040 ≤ 2048`) and appended onto `LinkedCertScc.ofLinkedCert rtC0CoreCert` (`86`
pure-C0 runtime functions, `exits = ["lcnf_panic"]`, `nX = 64`, `0` externs):

1. `mutRecDemoX64ProgCert`: `1`-chunk 2-function `.recBudgetSCC` user certificate (`roseSum`,
   `forestSum`) with `ext := rtC0CoreAllExt`.
2. `mutRecDemoX64Cert`: closed `88`-function `LinkedCertScc` (`maxBound = 2048`,
   `bound mutRecDemoRoseName = 1040`, `bound mutRecDemoForestName = 1040`).
3. `mutRecDemoX64_roseSum_fnSpec` & `mutRecDemoX64_forestSum_fnSpec`: source-level `FnSpec`.
4. `mutRecDemoX64_roseSum_sample_run`, `mutRecDemoX64_forestSum_sample_run`, &
   `mutRecDemoX64_forestSum_nil_run`: closed concrete x86-64 `Eventually` runs (`90`, `80`, `0`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

/-! ## 1. `compile_linked_budget_scc!` & Compositional `LinkedCertScc.append` -/

compile_linked_budget_scc! mutRecDemoX64ProgCert x64Target x64Layout x64LegalTarget x64LabelClean
  mutRecDemoBudgetMod 1 (maxBound := mutRecDemoExportBound)
  (exportBounds := mutRecDemoExportBounds)
  (ext := rtC0CoreAllExt) (extSigs := rtC0CoreMod.fns.map Fn.sig)
  (exits := rtExitSyms) (nX := 64)

/-- Lift of the `86`-function acyclic runtime `rtC0CoreCert` into `LinkedCertScc`. -/
@[expose] noncomputable def mutRecDemoRtSccCertX64 :
    LinkedCertScc x64Target x64Layout x64LegalTarget x64LabelClean
      rtC0CoreMod [] rtExitSyms 64 2048 [] :=
  LinkedCertScc.ofLinkedCert rtC0CoreCert rfl (by t_kernel_rfl)

/-- Full `88`-function SysV x86-64 `LinkedCertScc` combining `rtC0CoreCert` (`86` fns) and
`mutRecDemoX64ProgCert` (`1` 2-fn `.recBudgetSCC` chunk, `bound = 1040`, `maxBound = 2048`). -/
@[expose] noncomputable def mutRecDemoX64Cert :
    LinkedCertScc x64Target x64Layout x64LegalTarget x64LabelClean
      mutRecDemoLinkedMod [] rtExitSyms 64 (Nat.max 2048 mutRecDemoExportBound) [] :=
  mutRecDemoRtSccCertX64.append mutRecDemoX64ProgCert rfl (by t_kernel_rfl) (by t_kernel_rfl)

theorem mutRecDemoX64ProgCert_numChunks : mutRecDemoX64ProgCert.numChunks = 1 := rfl

theorem mutRecDemoX64Cert_roseSum_bound :
    mutRecDemoX64Cert.bound mutRecDemoRoseName = 1040 := rfl

theorem mutRecDemoX64Cert_forestSum_bound :
    mutRecDemoX64Cert.bound mutRecDemoForestName = 1040 := rfl

/-! ## 2. Semantic Bridges & `x64Target.FnSpec` (`fnSpec_host_src_of_le`) -/

private theorem mutRecDemoX64Cert_chunksShape : MutRecDemoChunksShape mutRecDemoX64Cert :=
  ⟨mutRecDemoRtSccCertX64.chunks, _, _, _, rfl⟩

theorem mutRecDemoX64_roseSum_sem :
    ∀ xs m Q X, roseSumSpec mutRecDemoDepthBudget xs m Q X →
      mutRecDemoX64Cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoRoseName [i64, i64] [i64]
        xs m Q X :=
  mutRecDemoCert_roseSum_sem mutRecDemoX64Cert mutRecDemoX64Cert_chunksShape

theorem mutRecDemoX64_forestSum_sem :
    ∀ xs m Q X, forestSumSpec mutRecDemoDepthBudget xs m Q X →
      mutRecDemoX64Cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoForestName [i64, i64] [i64]
        xs m Q X :=
  mutRecDemoCert_forestSum_sem mutRecDemoX64Cert mutRecDemoX64Cert_chunksShape

theorem mutRecDemoX64_roseSum_fnSpec :
    x64Target.Defined mutRecDemoX64Cert.host mutRecDemoRoseName ∧
      x64Target.FnSpec mutRecDemoX64Cert.host mutRecDemoRoseName
        (roseSumSpec mutRecDemoDepthBudget) (mutRecDemoX64Cert.bound mutRecDemoRoseName) 64 :=
  mutRecDemoCert_roseSum_fnSpec mutRecDemoX64Cert (by decide) (by decide) mutRecDemoX64_roseSum_sem

theorem mutRecDemoX64_forestSum_fnSpec :
    x64Target.Defined mutRecDemoX64Cert.host mutRecDemoForestName ∧
      x64Target.FnSpec mutRecDemoX64Cert.host mutRecDemoForestName
        (forestSumSpec mutRecDemoDepthBudget) (mutRecDemoX64Cert.bound mutRecDemoForestName) 64 :=
  mutRecDemoCert_forestSum_fnSpec mutRecDemoX64Cert (by decide) (by decide)
    mutRecDemoX64_forestSum_sem

/-! ## 3. Closed Concrete x86-64 `Eventually` Execution Witnesses -/

/-- Closed x86-64 execution of `MutRecDemo.roseSum` on nested 3-level `sampleRose`
(`312` bytes @ `0x1000#64`), returning `boxNat 90 = 181#64` in `%rax`. -/
theorem mutRecDemoX64_roseSum_sample_run :
    letI : Host := mutRecDemoX64Cert.host
    Eventually (step1 mutRecDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 90)
      ⟨x64Init.initState (as := [i64, i64]) (mutRecDemoX64Cert.bound mutRecDemoRoseName)
          sampleRoseBytes (0#64, 0x1000#64, ()),
        Labels.label mutRecDemoRoseName⟩ :=
  mutRecDemoCert_roseSum_eventually mutRecDemoX64Cert x64Init (by decide) (by decide) (by decide)
    mutRecDemoX64_roseSum_sem sampleRoseBytes 0#64 0x1000#64 sampleRose
    (by rw [sampleRoseBytes_length]; decide) (by decide) (by decide) sampleRose_roseNatAt
    (by decide)

/-- Closed x86-64 execution of `MutRecDemo.forestSum` on `sampleForest` at `0x1018#64` inside
`sampleRoseBytes`, returning `boxNat 80 = 161#64` in `%rax`. -/
theorem mutRecDemoX64_forestSum_sample_run :
    letI : Host := mutRecDemoX64Cert.host
    Eventually (step1 mutRecDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 80)
      ⟨x64Init.initState (as := [i64, i64]) (mutRecDemoX64Cert.bound mutRecDemoForestName)
          sampleRoseBytes (0#64, 0x1018#64, ()),
        Labels.label mutRecDemoForestName⟩ :=
  mutRecDemoCert_forestSum_eventually mutRecDemoX64Cert x64Init (by decide) (by decide) (by decide)
    mutRecDemoX64_forestSum_sem sampleRoseBytes 0#64 0x1018#64 sampleForest
    (roseNodeAt 0x1000#64 (boxNat 10) 0x1018#64)
    (by rw [sampleRoseBytes_length]; decide) (by decide) (by decide) sampleRose_forestNatAt
    (by decide)

/-- Closed x86-64 execution of `MutRecDemo.forestSum` on `Forest.nil` (`1#64`),
returning `boxNat 0 = 1#64` in `%rax`. -/
theorem mutRecDemoX64_forestSum_nil_run :
    letI : Host := mutRecDemoX64Cert.host
    Eventually (step1 mutRecDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 0)
      ⟨x64Init.initState (as := [i64, i64]) (mutRecDemoX64Cert.bound mutRecDemoForestName)
          [] (0#64, 1#64, ()),
        Labels.label mutRecDemoForestName⟩ :=
  mutRecDemoCert_forestSum_eventually mutRecDemoX64Cert x64Init (by decide) (by decide) (by decide)
    mutRecDemoX64_forestSum_sem [] 0#64 1#64 .nil Std.ExtHashMap.emp
    (by decide) (by decide) (by decide) sampleForestNil_forestNatAt (by decide)

end LeanQbe.T.Amd64
