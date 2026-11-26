module

public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemoProof
public import LeanQbe.T.MainCertScc
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo

/-!
# AAPCS64 AArch64 `compile_linked_budget_scc!` Certificate for Mutual `{roseSum, forestSum}` SCC

First AAPCS64 AArch64 (`armTarget`) multi-function mutually-recursive Lean `LCNF` SCC certified as
a **single 2-function `.recBudgetSCC` chunk** (`maxFrame = 48`, `minEntry = 272`, depth `D = 16`,
`exportBound = 1040 ≤ 2048`) and appended onto `LinkedCertScc.ofLinkedCert rtC0CoreArm64Cert`
(`86` pure-C0 runtime functions, `exits = ["lcnf_panic"]`, `nX = 64`, `0` externs):

1. `mutRecDemoArm64ProgCert`: `1`-chunk 2-function `.recBudgetSCC` user certificate (`roseSum`,
   `forestSum`) with `ext := rtC0CoreArm64AllExt`.
2. `mutRecDemoArm64Cert`: closed `88`-function `LinkedCertScc` (`maxBound = 2048`,
   `bound mutRecDemoRoseName = 1040`, `bound mutRecDemoForestName = 1040`).
3. `mutRecDemoArm64_roseSum_fnSpec` & `mutRecDemoArm64_forestSum_fnSpec`: source-level `FnSpec`.
4. `mutRecDemoArm64_roseSum_sample_run`, `mutRecDemoArm64_forestSum_sample_run`, &
   `mutRecDemoArm64_forestSum_nil_run`: closed concrete AArch64 `Eventually` runs (`90`, `80`, `0`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

/-! ## 1. `compile_linked_budget_scc!` & Compositional `LinkedCertScc.append` -/

compile_linked_budget_scc! mutRecDemoArm64ProgCert armTarget armLayout armLegalTarget armLabelClean
  mutRecDemoBudgetMod 1 (maxBound := mutRecDemoExportBound)
  (exportBounds := mutRecDemoExportBounds)
  (ext := rtC0CoreArm64AllExt) (extSigs := rtC0CoreMod.fns.map Fn.sig)
  (exits := rtExitSyms) (nX := 64)

/-- Lift of the `86`-function acyclic runtime `rtC0CoreArm64Cert` into `LinkedCertScc`. -/
@[expose] noncomputable def mutRecDemoRtSccCertArm64 :
    LinkedCertScc armTarget armLayout armLegalTarget armLabelClean
      rtC0CoreMod [] rtExitSyms 64 2048 [] :=
  LinkedCertScc.ofLinkedCert rtC0CoreArm64Cert rfl (by t_kernel_rfl)

/-- Full `88`-function AAPCS64 AArch64 `LinkedCertScc` combining `rtC0CoreArm64Cert` (`86` fns)
and `mutRecDemoArm64ProgCert` (`1` 2-fn `.recBudgetSCC` chunk, `bound = 1040`, `maxBound = 2048`).
-/
@[expose] noncomputable def mutRecDemoArm64Cert :
    LinkedCertScc armTarget armLayout armLegalTarget armLabelClean
      mutRecDemoLinkedMod [] rtExitSyms 64 (Nat.max 2048 mutRecDemoExportBound) [] :=
  mutRecDemoRtSccCertArm64.append mutRecDemoArm64ProgCert rfl (by t_kernel_rfl) (by t_kernel_rfl)

theorem mutRecDemoArm64ProgCert_numChunks : mutRecDemoArm64ProgCert.numChunks = 1 := rfl

theorem mutRecDemoArm64Cert_roseSum_bound :
    mutRecDemoArm64Cert.bound mutRecDemoRoseName = 1040 := rfl

theorem mutRecDemoArm64Cert_forestSum_bound :
    mutRecDemoArm64Cert.bound mutRecDemoForestName = 1040 := rfl

/-! ## 2. Semantic Bridges & `armTarget.FnSpec` (`fnSpec_host_src_of_le`) -/

private theorem mutRecDemoArm64Cert_chunksShape : MutRecDemoChunksShape mutRecDemoArm64Cert :=
  ⟨mutRecDemoRtSccCertArm64.chunks, _, _, _, rfl⟩

theorem mutRecDemoArm64_roseSum_sem :
    ∀ xs m Q X, roseSumSpec mutRecDemoDepthBudget xs m Q X →
      mutRecDemoArm64Cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoRoseName [i64, i64] [i64]
        xs m Q X :=
  mutRecDemoCert_roseSum_sem mutRecDemoArm64Cert mutRecDemoArm64Cert_chunksShape

theorem mutRecDemoArm64_forestSum_sem :
    ∀ xs m Q X, forestSumSpec mutRecDemoDepthBudget xs m Q X →
      mutRecDemoArm64Cert.sem (fun _ _ _ _ _ _ _ => False) mutRecDemoForestName [i64, i64] [i64]
        xs m Q X :=
  mutRecDemoCert_forestSum_sem mutRecDemoArm64Cert mutRecDemoArm64Cert_chunksShape

theorem mutRecDemoArm64_roseSum_fnSpec :
    armTarget.Defined mutRecDemoArm64Cert.host mutRecDemoRoseName ∧
      armTarget.FnSpec mutRecDemoArm64Cert.host mutRecDemoRoseName
        (roseSumSpec mutRecDemoDepthBudget) (mutRecDemoArm64Cert.bound mutRecDemoRoseName) 64 :=
  mutRecDemoCert_roseSum_fnSpec mutRecDemoArm64Cert (by decide) (by decide)
    mutRecDemoArm64_roseSum_sem

theorem mutRecDemoArm64_forestSum_fnSpec :
    armTarget.Defined mutRecDemoArm64Cert.host mutRecDemoForestName ∧
      armTarget.FnSpec mutRecDemoArm64Cert.host mutRecDemoForestName
        (forestSumSpec mutRecDemoDepthBudget)
        (mutRecDemoArm64Cert.bound mutRecDemoForestName) 64 :=
  mutRecDemoCert_forestSum_fnSpec mutRecDemoArm64Cert (by decide) (by decide)
    mutRecDemoArm64_forestSum_sem

/-! ## 3. Closed Concrete AArch64 `Eventually` Execution Witnesses -/

/-- Closed AArch64 execution of `MutRecDemo.roseSum` on nested 3-level `sampleRose`
(`312` bytes @ `0x1000#64`), returning `boxNat 90 = 181#64` in `X0`. -/
theorem mutRecDemoArm64_roseSum_sample_run :
    letI : Host := mutRecDemoArm64Cert.host
    Eventually (step1 mutRecDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 90)
      ⟨armInit.initState (as := [i64, i64]) (mutRecDemoArm64Cert.bound mutRecDemoRoseName)
          sampleRoseBytes (0#64, 0x1000#64, ()),
        Labels.label mutRecDemoRoseName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ =>
      ⟨hpc, by simpa [armInit, get_reg, sampleRose, sampleForest, MutRecDemo.roseSum,
        MutRecDemo.forestSum] using hx0⟩)
    (mutRecDemoCert_roseSum_eventually mutRecDemoArm64Cert armInit (by decide) (by decide)
      (by decide) mutRecDemoArm64_roseSum_sem sampleRoseBytes 0#64 0x1000#64 sampleRose
      (by rw [sampleRoseBytes_length]; decide) (by decide) (by decide) sampleRose_roseNatAt
      (by decide))

/-- Closed AArch64 execution of `MutRecDemo.forestSum` on `sampleForest` at `0x1018#64` inside
`sampleRoseBytes`, returning `boxNat 80 = 161#64` in `X0`. -/
theorem mutRecDemoArm64_forestSum_sample_run :
    letI : Host := mutRecDemoArm64Cert.host
    Eventually (step1 mutRecDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 80)
      ⟨armInit.initState (as := [i64, i64]) (mutRecDemoArm64Cert.bound mutRecDemoForestName)
          sampleRoseBytes (0#64, 0x1018#64, ()),
        Labels.label mutRecDemoForestName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ =>
      ⟨hpc, by simpa [armInit, get_reg, sampleForest, MutRecDemo.roseSum,
        MutRecDemo.forestSum] using hx0⟩)
    (mutRecDemoCert_forestSum_eventually mutRecDemoArm64Cert armInit (by decide) (by decide)
      (by decide) mutRecDemoArm64_forestSum_sem sampleRoseBytes 0#64 0x1018#64 sampleForest
      (roseNodeAt 0x1000#64 (boxNat 10) 0x1018#64)
      (by rw [sampleRoseBytes_length]; decide) (by decide) (by decide) sampleRose_forestNatAt
      (by decide))

/-- Closed AArch64 execution of `MutRecDemo.forestSum` on `Forest.nil` (`1#64`),
returning `boxNat 0 = 1#64` in `X0`. -/
theorem mutRecDemoArm64_forestSum_nil_run :
    letI : Host := mutRecDemoArm64Cert.host
    Eventually (step1 mutRecDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 0)
      ⟨armInit.initState (as := [i64, i64]) (mutRecDemoArm64Cert.bound mutRecDemoForestName)
          [] (0#64, 1#64, ()),
        Labels.label mutRecDemoForestName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ => ⟨hpc, by simpa [armInit, get_reg, MutRecDemo.forestSum] using hx0⟩)
    (mutRecDemoCert_forestSum_eventually mutRecDemoArm64Cert armInit (by decide) (by decide)
      (by decide) mutRecDemoArm64_forestSum_sem [] 0#64 1#64 .nil Std.ExtHashMap.emp
      (by decide) (by decide) (by decide) sampleForestNil_forestNatAt (by decide))

end LeanQbe.T.Arm64
