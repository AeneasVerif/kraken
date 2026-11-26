module

public import LeanQbe.T.Arm64.LcnfC0FullCertArm64
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0RecDemoProof
public import LeanQbe.T.MainCertScc
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.LcnfC0FullCertArm64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0RecDemo

/-!
# AAPCS64 AArch64 `compile_linked_budget_scc!` Certificate for `RecDemo.listSum`

First real-target (`armTarget`) structurally recursive Lean `LCNF` program certified through
`compile_linked_budget_scc!` (`maxFrame = 32`, `minEntry = 256`, depth `D = 16`,
`exportBound = 768 ≤ 2048`) and compositionally appended onto `LinkedCertScc.ofLinkedCert
rtC0CoreArm64Cert` (`86` pure-C0 runtime functions, `exits = ["lcnf_panic"]`, `nX = 64`):

1. `recDemoArm64ProgCert`: `1`-chunk `.recBudgetSCC` user certificate with
   `ext := rtC0CoreArm64AllExt`.
2. `recDemoArm64Cert`: closed `87`-function `LinkedCertScc` (`maxBound = 2048`,
   `bound recDemoListSumName = 768`).
3. `recDemoArm64_listSum_fnSpec`: source-level `armTarget.Defined` + `armTarget.FnSpec` via
   `LinkedCertScc.fnSpec_host_src_of_le`.
4. `recDemoArm64_listSum_10_20_30_run` & `recDemoArm64_listSum_nil_run`: closed concrete AArch64
   `Eventually` machine execution witnesses (`[10, 20, 30] → boxNat 60 = 121#64`, `[] → 1#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

/-! ## 1. `compile_linked_budget_scc!` & Compositional `LinkedCertScc.append` -/

compile_linked_budget_scc! recDemoArm64ProgCert armTarget armLayout armLegalTarget armLabelClean
  recDemoBudgetMod 1 (maxBound := recDemoExportBound)
  (exportBounds := [(recDemoListSumName, recDemoExportBound)])
  (ext := rtC0CoreArm64AllExt) (extSigs := rtC0CoreMod.fns.map Fn.sig)
  (exits := rtExitSyms) (nX := 64)

/-- Lift of the `86`-function acyclic runtime `rtC0CoreArm64Cert` into `LinkedCertScc`. -/
@[expose] noncomputable def rtC0CoreSccCertArm64 :
    LinkedCertScc armTarget armLayout armLegalTarget armLabelClean
      rtC0CoreMod [] rtExitSyms 64 2048 [] :=
  LinkedCertScc.ofLinkedCert rtC0CoreArm64Cert rfl (by t_kernel_rfl)

/-- Full `87`-function AAPCS64 AArch64 `LinkedCertScc` combining `rtC0CoreArm64Cert` (`86` fns)
and `recDemoArm64ProgCert` (`1` `.recBudgetSCC` fn, `bound = 768`, `maxBound = 2048`). -/
@[expose] noncomputable def recDemoArm64Cert :
    LinkedCertScc armTarget armLayout armLegalTarget armLabelClean
      recDemoLinkedMod [] rtExitSyms 64 (Nat.max 2048 recDemoExportBound) [] :=
  rtC0CoreSccCertArm64.append recDemoArm64ProgCert rfl (by t_kernel_rfl) (by t_kernel_rfl)

theorem recDemoArm64ProgCert_numChunks : recDemoArm64ProgCert.numChunks = 1 := rfl

theorem recDemoArm64Cert_listSum_bound :
    recDemoArm64Cert.bound recDemoListSumName = 768 := rfl

/-! ## 2. Semantic Bridge & `armTarget.FnSpec` (`fnSpec_host_src_of_le`) -/

theorem recDemoArm64_listSum_sem :
    ∀ xs m Q X, listSumSpec recDemoDepthBudget xs m Q X →
      recDemoArm64Cert.sem (fun _ _ _ _ _ _ _ => False) recDemoListSumName [i64, i64] [i64]
        xs m Q X :=
  recDemoCert_listSum_sem recDemoArm64Cert ⟨rtC0CoreSccCertArm64.chunks, _, _, _, rfl⟩

theorem recDemoArm64_listSum_fnSpec :
    armTarget.Defined recDemoArm64Cert.host recDemoListSumName ∧
      armTarget.FnSpec recDemoArm64Cert.host recDemoListSumName (listSumSpec recDemoDepthBudget)
        (recDemoArm64Cert.bound recDemoListSumName) 64 :=
  recDemoCert_listSum_fnSpec recDemoArm64Cert (by decide) (by decide) recDemoArm64_listSum_sem

/-! ## 3. Closed Concrete AArch64 `Eventually` Execution Witnesses -/

/-- Closed AArch64 machine execution (`Eventually (step1 recDemoArm64Cert.host.exe)`) of
`RecDemo.listSum` on concrete `[10, 20, 30]` (`72` bytes @ `0x1000#64`), returning
`boxNat 60 = 121#64` in `X0` (`XPost := False`). -/
theorem recDemoArm64_listSum_10_20_30_run :
    letI : Host := recDemoArm64Cert.host
    Eventually (step1 recDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 60)
      ⟨armInit.initState (as := [i64, i64]) (recDemoArm64Cert.bound recDemoListSumName)
          recList3Bytes (0#64, 0x1000#64, ()),
        Labels.label recDemoListSumName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ => ⟨hpc, by simpa [armInit, get_reg, RecDemo.listSum] using hx0⟩)
    (recDemoCert_listSum_eventually recDemoArm64Cert armInit (by decide) (by decide) (by decide)
      recDemoArm64_listSum_sem recList3Bytes 0#64 0x1000#64 [10, 20, 30]
      (by rw [recList3Bytes_length]; decide) (by decide) (by decide) recList3_listNatAt
      (by decide))

/-- Closed AArch64 machine execution (`Eventually (step1 recDemoArm64Cert.host.exe)`) of
`RecDemo.listSum` on `[]` (`1#64`), returning `boxNat 0 = 1#64` in `X0`. -/
theorem recDemoArm64_listSum_nil_run :
    letI : Host := recDemoArm64Cert.host
    Eventually (step1 recDemoArm64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = boxNat 0)
      ⟨armInit.initState (as := [i64, i64]) (recDemoArm64Cert.bound recDemoListSumName)
          [] (0#64, 1#64, ()),
        Labels.label recDemoListSumName⟩ :=
  eventually_weaken _ _ _ _
    (fun st ⟨hpc, hx0⟩ => ⟨hpc, by simpa [armInit, get_reg, RecDemo.listSum] using hx0⟩)
    (recDemoCert_listSum_eventually recDemoArm64Cert armInit (by decide) (by decide) (by decide)
      recDemoArm64_listSum_sem [] 0#64 1#64 []
      (by decide) (by decide) (by decide) recListNil_listNatAt (by decide))

end LeanQbe.T.Arm64
