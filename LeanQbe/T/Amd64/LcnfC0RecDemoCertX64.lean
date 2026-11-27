module

public import LeanQbe.T.Amd64.LcnfC0FullCertX64
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0RecDemoProof
public import LeanQbe.T.MainCertScc
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.LeanLCNF.LcnfC0RecDemo

/-!
# SysV x86-64 `compile_linked_budget_scc!` Certificate for `RecDemo.listSum`

First real-target (`x64Target`) structurally recursive Lean `LCNF` program certified through
`compile_linked_budget_scc!` (`maxFrame = 32`, `minEntry = 256`, depth `D = 16`,
`exportBound = 768 ≤ 2048`) and compositionally appended onto `LinkedCertScc.ofLinkedCert
rtC0CoreCert` (`86` pure-C0 runtime functions, `exits = ["lcnf_panic"]`, `nX = 64`):

1. `recDemoX64ProgCert`: `1`-chunk `.recBudgetSCC` user certificate with `ext := rtC0CoreAllExt`.
2. `recDemoX64Cert`: closed `87`-function `LinkedCertScc` (`maxBound = 2048`,
   `bound recDemoListSumName = 768`).
3. `recDemoX64_listSum_fnSpec`: source-level `x64Target.Defined` + `x64Target.FnSpec` via
   `LinkedCertScc.fnSpec_host_src_of_le`.
4. `recDemoX64_listSum_10_20_30_run` & `recDemoX64_listSum_nil_run`: closed concrete x86-64
   `Eventually` machine execution witnesses (`[10, 20, 30] → boxNat 60 = 121#64`, `[] → 1#64`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF Kraken

/-! ## 1. `compile_linked_budget_scc!` & Compositional `LinkedCertScc.append` -/

compile_linked_budget_scc! recDemoX64ProgCert x64Target x64Layout x64LegalTarget x64LabelClean
  recDemoBudgetMod 1 (maxBound := recDemoExportBound)
  (exportBounds := [(recDemoListSumName, recDemoExportBound)])
  (ext := rtC0CoreAllExt) (extSigs := rtC0CoreMod.fns.map Fn.sig)
  (exits := rtExitSyms) (nX := 64) (flat := true)

/-- Lift of the `86`-function acyclic runtime `rtC0CoreCert` into `LinkedCertScc`. -/
@[expose] noncomputable def rtC0CoreSccCertX64 :
    LinkedCertScc x64Target x64Layout x64LegalTarget x64LabelClean
      rtC0CoreMod [] rtExitSyms 64 2048 [] :=
  LinkedCertScc.ofLinkedCert rtC0CoreCert rfl (by t_kernel_rfl)

/-- Full `87`-function SysV x86-64 `LinkedCertScc` combining `rtC0CoreCert` (`86` fns) and
`recDemoX64ProgCert` (`1` `.recBudgetSCC` fn, `bound = 768`, `maxBound = 2048`). -/
@[expose] noncomputable def recDemoX64Cert :
    LinkedCertScc x64Target x64Layout x64LegalTarget x64LabelClean
      recDemoLinkedMod [] rtExitSyms 64 (Nat.max 2048 recDemoExportBound) [] :=
  rtC0CoreSccCertX64.append recDemoX64ProgCert rfl (by t_kernel_rfl) (by t_kernel_rfl)

theorem recDemoX64ProgCert_numChunks : recDemoX64ProgCert.numChunks = 1 := rfl

theorem recDemoX64Cert_listSum_bound :
    recDemoX64Cert.bound recDemoListSumName = 768 := rfl

/-! ## 2. Semantic Bridge & `x64Target.FnSpec` (`fnSpec_host_src_of_le`) -/

theorem recDemoX64_listSum_sem :
    ∀ xs m Q X, listSumSpec recDemoDepthBudget xs m Q X →
      recDemoX64Cert.sem (fun _ _ _ _ _ _ _ => False) recDemoListSumName [i64, i64] [i64]
        xs m Q X :=
  recDemoCert_listSum_sem recDemoX64Cert ⟨rtC0CoreSccCertX64.chunks, _, _, _, rfl⟩

theorem recDemoX64_listSum_fnSpec :
    x64Target.Defined recDemoX64Cert.host recDemoListSumName ∧
      x64Target.FnSpec recDemoX64Cert.host recDemoListSumName (listSumSpec recDemoDepthBudget)
        (recDemoX64Cert.bound recDemoListSumName) 64 :=
  recDemoCert_listSum_fnSpec recDemoX64Cert (by decide) (by decide) recDemoX64_listSum_sem

/-! ## 3. Closed Concrete x86-64 `Eventually` Execution Witnesses -/

/-- Closed x86-64 machine execution (`Eventually (step1 recDemoX64Cert.host.exe)`) of
`RecDemo.listSum` on concrete `[10, 20, 30]` (`72` bytes @ `0x1000#64`), returning
`boxNat 60 = 121#64` in `%rax` (`XPost := False`). -/
theorem recDemoX64_listSum_10_20_30_run :
    letI : Host := recDemoX64Cert.host
    Eventually (step1 recDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 60)
      ⟨x64Init.initState (as := [i64, i64]) (recDemoX64Cert.bound recDemoListSumName)
          recList3Bytes (0#64, 0x1000#64, ()),
        Labels.label recDemoListSumName⟩ :=
  recDemoCert_listSum_eventually recDemoX64Cert x64Init (by decide) (by decide) (by decide)
    recDemoX64_listSum_sem recList3Bytes 0#64 0x1000#64 [10, 20, 30]
    (by rw [recList3Bytes_length]; decide) (by decide) (by decide) recList3_listNatAt (by decide)

/-- Closed x86-64 machine execution (`Eventually (step1 recDemoX64Cert.host.exe)`) of
`RecDemo.listSum` on `[]` (`1#64`), returning `boxNat 0 = 1#64` in `%rax`. -/
theorem recDemoX64_listSum_nil_run :
    letI : Host := recDemoX64Cert.host
    Eventually (step1 recDemoX64Cert.host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = boxNat 0)
      ⟨x64Init.initState (as := [i64, i64]) (recDemoX64Cert.bound recDemoListSumName)
          [] (0#64, 1#64, ()),
        Labels.label recDemoListSumName⟩ :=
  recDemoCert_listSum_eventually recDemoX64Cert x64Init (by decide) (by decide) (by decide)
    recDemoX64_listSum_sem [] 0#64 1#64 []
    (by decide) (by decide) (by decide) recListNil_listNatAt (by decide)

end LeanQbe.T.Amd64
