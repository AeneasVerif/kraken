module

public import LeanQbe.T.Amd64.KissatM6Cert
public import LeanQbe.T.Amd64.KissatM6CertLink
public import LeanQbe.T.Examples.Kissat.FullM6Proof
import LeanQbe.T.Examples.Kissat.FullM6SatSound
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.Logic.MemLemmas
import Std.Sat.CNF.Basic
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM6 (`382` fns) Unconditional SysV x64 Theorems

Combines `KissatM6Cert.m6Cert` and `KissatM6CertLink` with `FullM6Proof` contracts
(`m6CoreEnv_moduleOk`, `m6CoreEnv_noExit`) to establish unconditional SysV x64 UNSAT soundness
(`Eventually (step1 Host.exe)` + `cnf.Unsat`) and both arbitrary-host and concrete-host UNSAT
non-vacuity (`XPost := False`, standard axioms).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM6

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM6 LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6CertLink Kraken
open LeanQbe.T.Examples.Kissat.FullM6Hdr LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Orch LeanQbe.T.Examples.Kissat.FullM6Proof
open LeanQbe.T.Examples.Kissat.FullM6InlPolicy

/-- Compiled `LinkedCert` for `m6Module.optInlinePolicy m6InlPolicy` (`382` functions) on SysV x64.
-/
@[reducible] noncomputable def kissatM6_compiled_x64 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (m6Module.optInlinePolicy m6InlPolicy) :=
  KissatM6Cert.m6Cert

/-- Unconditional whole-module `Defined` + `FnSpec` for all `382` functions in `m6Module` under
`m6CoreEnv` on SysV x64. -/
theorem m6_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM6_compiled_x64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m6Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name
        (m6CoreEnv f.name f.as f.rs)
        (kissatM6_compiled_x64.bound f.name) 0 :=
  KissatM6CertLink.mk_module_fnspec m6CoreEnv m6CoreEnv_moduleOk
    (fun g _ => m6CoreEnv_noExit g.name g.as g.rs)
    k₀ hc hu hf

private theorem solve_in_m6Module :
    m6oSolveBytesFn ∈ m6Module.fns :=
  m6oSolveBytesFn_mem

private theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}
    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by
  have hm := sep_mono (Q := Q)
    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h
  rw [sep_ex_l] at hm
  obtain ⟨m, hm'⟩ := hm
  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩

def m6NvWorkLen : Nat := 6144

def m6NvPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate m6NvWorkLen 0

theorem m6NvPayload_length (cnfBytes : List UInt8) :
    (m6NvPayload cnfBytes).length = cnfBytes.length + m6NvWorkLen := by
  simp only [m6NvPayload, List.length_append, List.length_replicate]

theorem m6NvPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 2048) :
    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) m6NvWorkLen)
      ((m6NvPayload cnfBytes).At nvM6CnfPtr) :=
  nv_sep_append rfl
    (by unfold m6NvWorkLen; rw [List.length_replicate]; omega)
    rfl ⟨List.replicate m6NvWorkLen 0, List.length_replicate, rfl⟩

theorem m6Nv_unsat_bound :
    fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 ≤ m6NvWorkLen := by
  unfold m6NvWorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes
    u32FullBytes fullMinDepthOf
  decide

section Unsat

variable [hh : Host] (k₀ : Nat)
  (hc : kissatM6_compiled_x64.code.IsInfixAt Host.prog k₀)
  (hu : Host.LabelsUnique)
  (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
  (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
  (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
  (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
  (hrdi : s.regs.get64 .rdi = cnf_ptr)
  (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
  (hrdx : s.regs.get64 .rdx = work_ptr)
  (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
  (hr8 : s.regs.get64 .r8 = fuel)
  (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
  (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
    (region (s.regs.get64 .rsp - BitVec.ofNat 64
        (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
      (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆
      cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem)
include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
  hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- End-to-end SysV x64 UNSAT soundness + framing for `m6Module` (`432`-word `FullM6Hdr`). -/
theorem m6_solve_bytes_unsat_x64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
            ((kissatM6_compiled_x64.bound "kissat_solve_bytes") + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn := (m6_module_fnspec k₀ hc hu solve_in_m6Module).2
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      ((region (s.regs.get64 .rsp - BitVec.ofNat 64
          (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R)) s.dmem := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64
          (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem := by
    rw [sep_assoc]; exact hm_dmem
  have hspec : m6CoreEnv "kissat_solve_bytes"
      [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    m6CoreEnv_solve_bytes_iff.mpr
      (fullM6SolveBytesCoreModelSpec_intro (R := emp) hcfit hwfit
        (by rw [sep_emp]; exact hm_in)
        (fun _ _ hdom hu _ _ hm' =>
          by rw [sep_emp] at hm'; exact ⟨hdom, hu, hm'⟩))
  refine eventually_weaken _ _ _ _ ?_
    (KissatM6CertLink.solve_x64_of_fnspec hfn cnf_ptr _ work_ptr _ fuel
      hspec s ra R hrdi hrsi hrdx hrcx hr8 hsp hm_dmem')
  rintro st ⟨hpc, hcal, hrsp, m', ⟨hdom, hu', hm'⟩, hst⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hcal, hrsp, hst'⟩

/-- Answer-only SysV x64 UNSAT soundness corollary for `m6Module`. -/
theorem kissat_m6_x64_unsat_correct :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (m6_solve_bytes_unsat_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)

end Unsat

/-- Concrete SysV x64 UNSAT non-vacuity for `m6Module` on `432`-word `FullM6Hdr`
(`nvM6UnsatBytes`, `6144`-byte workspace, `fuel = 16`). -/
theorem m6_x64_unsat_nonvacuous
    [hh : Host] (k₀ : Nat)
    (hc : kissatM6_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      s.regs.get64 .rdi = cnf_ptr ∧
      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧
      s.regs.get64 .rdx = work_ptr ∧
      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧
      s.regs.get64 .r8 = fuel ∧
      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        (region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatM6_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : x64Target.FnSpec hh "kissat_solve_bytes"
      (m6CoreEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (kissatM6_compiled_x64.bound "kissat_solve_bytes") 0 :=
    (m6_module_fnspec k₀ hc hu solve_in_m6Module).2
  let b := kissatM6_compiled_x64.bound "kissat_solve_bytes"
  let bs := m6NvPayload nvM6UnsatBytes
  let s := x64Init.initState (as := [i64, i64, i64, i64, i64]) b bs
    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
  have h1 := x64InitMem_entry b 0x1234 bs (kissatM6_compiled_x64.bound_le_max _)
    (by rw [m6NvPayload_length]; unfold m6NvWorkLen; decide)
  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ x64Target.Entry 0x0ff8#64 0x1234 b ⋆ emp at h1
  dsimp only [Target.Entry, x64Target, x64FrameTarget, x64FramePreds] at h1
  have h1' : (Eq (bs.At 0x1000#64) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) (0x1234 : Int64).toBitVec) ⋆ emp) s.dmem := by
    rw [show s.regs.get64 .rsp = 0x0ff8#64 from rfl]; exact h1
  have hdm : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      region nvM6UnsatWorkPtr m6NvWorkLen ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) (0x1234 : Int64).toBitVec) ⋆ emp) s.dmem := by
    refine sep_mono (Q := emp)
      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))
        (fun _ heq => heq ▸ m6NvPayload_sep nvM6UnsatBytes (by decide))) h1'
  have hhsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 := by
    rw [show s.regs.get64 .rsp = 0x0ff8#64 from rfl]; decide
  refine ⟨nvM6CnfPtr, nvM6UnsatWorkPtr, 16#64, nvM6UnsatBytes, m6NvWorkLen,
    s, 0x1234, emp, by decide, by decide, rfl, rfl, rfl, rfl, rfl,
    hhsp, hdm, ?_⟩
  have hspec : m6CoreEnv "kissat_solve_bytes"
      [i64, i64, i64, i64, i64] [i64]
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
      (bs.At 0x1000#64) (fun r _ => r.fst = 20#64 ∧ nvM6UnsatCnf.Unsat)
      (fun _ _ _ _ => False) :=
    m6CoreEnv_solve_bytes_iff.mpr
      (fullM6SolveBytesCoreModelSpec_intro (R := emp) (by decide) (by decide)
        (by
          rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
          exact m6NvPayload_sep nvM6UnsatBytes (by decide))
        (fun _ _ _ _ _ htr _ =>
          ⟨htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
            (by decide) nvM6Unsat_header nvM6Unsat_unitTrace, nvM6UnsatCnf_unsat⟩))
  have hev := KissatM6CertLink.solve_x64_of_fnspec hfn nvM6CnfPtr _
    nvM6UnsatWorkPtr _ 16#64 hspec s 0x1234 emp
    rfl rfl rfl rfl rfl hhsp h1'
  exact eventually_weaken _ _ _ _
    (fun _ ⟨hpc, _, _, _, ⟨h20, huns⟩, _⟩ =>
      ⟨hpc, h20, nvM6UnsatCnf, parseDimacs_nvM6UnsatBytes, huns⟩)
    hev

/-- Closed concrete-host SysV x64 UNSAT execution witness on `kissatM6_compiled_x64.host`
(`432`-word `FullM6Hdr`). -/
theorem m6_x64_run_unsat :
    Eventually (x64Target.mach.step kissatM6_compiled_x64.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          x64Target.Exit x64Init.sp0
            (kissatM6_compiled_x64.bound "kissat_solve_bytes") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i64, i64, i64])
          (kissatM6_compiled_x64.bound "kissat_solve_bytes")
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (x64Target.mach.labelAddr kissatM6_compiled_x64.host "kissat_solve_bytes")) := by
  refine kissatM6_compiled_x64.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy x64Init
    m6CoreEnv m6CoreEnv_moduleOk
    m6_legalSig solve_in_m6Module rfl
    (m6CoreEnv_noExit "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
    (m6NvPayload nvM6UnsatBytes)
    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
    20#64
    (fun m' => nvM6UnsatCnf.Unsat ∧
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
        region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m')
    (by rw [m6NvPayload_length]; unfold m6NvWorkLen; decide) rfl
    (Q := fun r m' => r = (20#64, ()) ∧ nvM6UnsatCnf.Unsat ∧
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
        region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m')
    ?_ (fun _ _ h => h) (by decide)
  exact m6CoreEnv_solve_bytes_iff.mpr
    (fullM6SolveBytesCoreModelSpec_intro (R := emp) (by decide) (by decide)
      (by
        rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
        exact m6NvPayload_sep nvM6UnsatBytes (by decide))
      (fun _ m' _ _ _ htr hm' =>
        ⟨congrArg (·, ()) (htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
          (by decide) nvM6Unsat_header nvM6Unsat_unitTrace),
         nvM6UnsatCnf_unsat, hm'⟩))

#print axioms kissatM6_compiled_x64
#print axioms m6_module_fnspec
#print axioms m6_solve_bytes_unsat_x64
#print axioms kissat_m6_x64_unsat_correct
#print axioms m6_x64_unsat_nonvacuous
#print axioms m6_x64_run_unsat

end LeanQbe.T.Amd64.KissatM6
