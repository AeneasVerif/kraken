module

public import LeanQbe.T.Arm64.KissatM7FidelityCert
public import LeanQbe.T.Arm64.KissatM7FidelityCertLink
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Logic.MemLemmas
import Std.Sat.CNF.Basic
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM7Fidelity (`413` fns) Unconditional AAPCS64 Arm64 Theorems

Combines `KissatM7FidelityCert.m7FidelityCert` and `KissatM7FidelityCertLink` with solver proof
contracts.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM7Fidelity

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM7Fidelity LeanQbe.T.Arm64
open LeanQbe.T.Arm64.KissatM7FidelityCertLink Kraken LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM7InlPolicy

/-- Compiled `LinkedCert` for `m7FidelityModule.optInlinePolicy m7InlPolicy` (`413` functions) on
AAPCS64 Arm64. -/
@[reducible] noncomputable def kissatM7Fidelity_compiled_arm64 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (m7FidelityModule.optInlinePolicy m7InlPolicy) :=
  KissatM7FidelityCert.m7FidelityCert

/-- Unconditional whole-module `Defined` + `FnSpec` for all `413` functions in `m7FidelityModule`
under `m7FidelityEnv` on AAPCS64 Arm64. -/
theorem m7Fidelity_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m7FidelityModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (m7FidelityEnv f.name f.as f.rs)
        (kissatM7Fidelity_compiled_arm64.bound f.name) 0 :=
  KissatM7FidelityCertLink.mk_module_fnspec m7FidelityEnv m7Fidelity_moduleOk
    (fun g _ => m7FidelityEnv_noExit g.name g.as g.rs) k₀ hc hu hf

theorem solve_in_m7FidelityModule :
    FullM6Orch.m6oSolveBytesFn ∈ m7FidelityModule.fns :=
  m7Fidelity_solveBytes_mem

theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}
    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by
  have hm := sep_mono (Q := Q)
    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h
  rw [sep_ex_l] at hm
  obtain ⟨m, hm'⟩ := hm
  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩

def m7FidelityNvWorkLen : Nat := 6144

theorem m7FidelityNvWorkLen_eq : m7FidelityNvWorkLen = 6144 := by
  unfold m7FidelityNvWorkLen; rfl

def m7FidelityNvPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate m7FidelityNvWorkLen 0

theorem m7FidelityNvPayload_eq (cnfBytes : List UInt8) :
    m7FidelityNvPayload cnfBytes = cnfBytes ++ List.replicate 6144 0 := by
  unfold m7FidelityNvPayload m7FidelityNvWorkLen; rfl

theorem m7FidelityNvPayload_length (cnfBytes : List UInt8) :
    (m7FidelityNvPayload cnfBytes).length = cnfBytes.length + m7FidelityNvWorkLen := by
  simp only [m7FidelityNvPayload, List.length_append, List.length_replicate]

theorem m7FidelityNvPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 2048) :
    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) m7FidelityNvWorkLen)
      ((m7FidelityNvPayload cnfBytes).At nvM6CnfPtr) :=
  nv_sep_append rfl
    (by unfold m7FidelityNvWorkLen; rw [List.length_replicate]; omega)
    rfl ⟨List.replicate m7FidelityNvWorkLen 0, List.length_replicate, rfl⟩

theorem m7FidelityNv_unsat_bound :
    fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 ≤ m7FidelityNvWorkLen := by
  unfold m7FidelityNvWorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes
    u32FullBytes fullMinDepthOf
  decide

section Unsat

variable [hh : Host] (k₀ : Nat)
  (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀)
  (hu : Host.LabelsUnique)
  (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
  (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
  (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
  (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
  (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
  (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
  (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
  (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
  (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
  (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
  (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
    region (s.regs.SP.toBitVec - BitVec.ofNat 64
        (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
      (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem)
include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
  hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- Unconditional end-to-end AAPCS64 Arm64 UNSAT soundness + framing for `m7FidelityModule`
(`432`-word `FullM6Hdr`). -/
theorem m7Fidelity_solve_bytes_unsat_arm64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
            .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn := (m7Fidelity_module_fnspec k₀ hc hu solve_in_m7FidelityModule).2
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)) s.dmem := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem := by
    rw [sep_assoc]; exact hm_dmem
  have hspec : m7FidelityEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    m7FidelityEnv_solve_bytes_iff.mpr
      (m7FidSolveBytesSpec_intro (R := emp) hcfit hwfit
        (by rw [sep_emp]; exact hm_in)
        (fun _ _ hdom hu _ hm' =>
          by rw [sep_emp] at hm'; exact ⟨hdom, hu, hm'⟩))
  refine eventually_weaken _ _ _ _ ?_
    (KissatM7FidelityCertLink.solve_arm64_of_fnspec hfn cnf_ptr _ work_ptr _ fuel
      hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hm_dmem')
  rintro st ⟨hpc, hcal, hsp', m', ⟨hdom, hu', hm'⟩, hst⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hcal, hsp', hst'⟩

/-- Answer-only AAPCS64 Arm64 UNSAT soundness corollary for `m7FidelityModule`. -/
theorem kissat_m7Fidelity_arm64_unsat_correct :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (m7Fidelity_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

theorem ax_unsat :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
            .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m7Fidelity_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

theorem ax_unsat_sound :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  kissat_m7Fidelity_arm64_unsat_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

end Unsat

/-- Unconditional concrete AAPCS64 Arm64 UNSAT non-vacuity for `m7FidelityModule` on `432`-word
`FullM6Hdr` (`nvM6UnsatBytes`, `6144`-byte workspace, `fuel = 16`). -/
theorem m7Fidelity_arm64_unsat_nonvacuous [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - BitVec.ofNat 64
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : armTarget.FnSpec hh "kissat_solve_bytes"
      (m7FidelityEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") 0 :=
    (KissatM7FidelityCertLink.mk_module_fnspec m7FidelityEnv m7Fidelity_moduleOk
      (fun g _ => m7FidelityEnv_noExit g.name g.as g.rs) k₀ hc hu solve_in_m7FidelityModule).2
  let b := kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"
  let bs := m7FidelityNvPayload nvM6UnsatBytes
  let s := armInit.initState (as := [i64, i64, i64, i64, i64]) b bs
    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 m7FidelityNvWorkLen, 16#64, ())
  have h1 := armInitMem_entry b bs (kissatM7Fidelity_compiled_arm64.bound_le_max _)
    (by rw [m7FidelityNvPayload_length]; unfold m7FidelityNvWorkLen; decide)
  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 b ⋆ emp at h1
  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds] at h1
  simp only [region_zero, sep_emp] at h1
  have h1' : (Eq (bs.At 0x1000#64) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem := by
    rw [show s.regs.SP.toBitVec = 0x1000#64 from rfl]; simpa [sep_emp] using h1
  have hdm : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      region nvM6UnsatWorkPtr m7FidelityNvWorkLen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem :=
    sep_mono (Q := emp)
      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))
        (fun _ heq => heq ▸ m7FidelityNvPayload_sep nvM6UnsatBytes (by decide))) h1'
  have hhsp : s.regs.SP.toNat % 16 = 0 := by rw [show s.regs.SP = 4096 from rfl]; decide
  refine ⟨nvM6CnfPtr, nvM6UnsatWorkPtr, 16#64, nvM6UnsatBytes, m7FidelityNvWorkLen,
    s, 0x1234, emp, by decide, by decide, rfl, rfl, rfl, rfl, rfl,
    rfl,
    hhsp, hdm, ?_⟩
  have hspec : m7FidelityEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 m7FidelityNvWorkLen, 16#64, ())
      (bs.At 0x1000#64) (fun r _ => r.fst = 20#64 ∧ nvM6UnsatCnf.Unsat)
      (fun _ _ _ _ => False) :=
    m7FidelityEnv_solve_bytes_iff.mpr
      (m7FidSolveBytesSpec_intro (R := emp) (by decide) (by decide)
        (by
          rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
          exact m7FidelityNvPayload_sep nvM6UnsatBytes (by decide))
        (fun _ _ _ _ htr _ =>
          ⟨htr 1 2 9 (by decide) (by decide) (by decide) m7FidelityNv_unsat_bound
            (by decide) nvM6Unsat_header nvM6Unsat_unitTrace, nvM6UnsatCnf_unsat⟩))
  have hev := KissatM7FidelityCertLink.solve_arm64_of_fnspec hfn nvM6CnfPtr _
    nvM6UnsatWorkPtr _ 16#64 hspec s 0x1234 emp
    rfl rfl rfl rfl rfl rfl hhsp h1'
  exact eventually_weaken _ _ _ _
    (fun _ ⟨hpc, _, _, _, ⟨h20, huns⟩, _⟩ =>
      ⟨hpc, h20, nvM6UnsatCnf, parseDimacs_nvM6UnsatBytes, huns⟩)
    hev

/-- Closed concrete-host AAPCS64 Arm64 UNSAT execution witness on
`kissatM7Fidelity_compiled_arm64.host` (`432`-word `FullM6Hdr`). -/
theorem m7Fidelity_arm64_run_unsat :
    Eventually (armTarget.mach.step kissatM7Fidelity_compiled_arm64.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m7FidelityNvWorkLen ⋆ emp) m') ⋆
          armTarget.Exit armInit.sp0
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64, i64, i64])
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes")
          (m7FidelityNvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m7FidelityNvWorkLen, 16#64, ()))
        (armTarget.mach.labelAddr kissatM7Fidelity_compiled_arm64.host "kissat_solve_bytes")) := by
  refine kissatM7Fidelity_compiled_arm64.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy
    armInit
    m7FidelityEnv m7Fidelity_moduleOk m7Fidelity_legalSig solve_in_m7FidelityModule rfl
    (m7FidelityEnv_noExit "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
    (m7FidelityNvPayload nvM6UnsatBytes)
    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 m7FidelityNvWorkLen, 16#64, ())
    20#64
    (fun m' => nvM6UnsatCnf.Unsat ∧
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
        region nvM6UnsatWorkPtr m7FidelityNvWorkLen ⋆ emp) m')
    (by rw [m7FidelityNvPayload_length]; unfold m7FidelityNvWorkLen; decide) rfl
    (Q := fun r m' => r = (20#64, ()) ∧ nvM6UnsatCnf.Unsat ∧
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
        region nvM6UnsatWorkPtr m7FidelityNvWorkLen ⋆ emp) m')
    ?_ (fun _ _ h => h) (by decide)
  exact m7FidelityEnv_solve_bytes_iff.mpr
    (m7FidSolveBytesSpec_intro (R := emp) (by decide) (by decide)
      (by
        rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
        exact m7FidelityNvPayload_sep nvM6UnsatBytes (by decide))
      (fun _ m' _ _ htr hm' =>
        ⟨congrArg (·, ()) (htr 1 2 9 (by decide) (by decide) (by decide) m7FidelityNv_unsat_bound
          (by decide) nvM6Unsat_header nvM6Unsat_unitTrace),
         nvM6UnsatCnf_unsat, hm'⟩))

theorem ax_unsat_nv [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - BitVec.ofNat 64
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  m7Fidelity_arm64_unsat_nonvacuous k₀ hc hu

theorem ax_run_unsat :
    Eventually (armTarget.mach.step kissatM7Fidelity_compiled_arm64.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m7FidelityNvWorkLen ⋆ emp) m') ⋆
          armTarget.Exit armInit.sp0
            (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64, i64, i64])
          (kissatM7Fidelity_compiled_arm64.bound "kissat_solve_bytes")
          (m7FidelityNvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m7FidelityNvWorkLen, 16#64, ()))
        (armTarget.mach.labelAddr kissatM7Fidelity_compiled_arm64.host "kissat_solve_bytes")) :=
  m7Fidelity_arm64_run_unsat

noncomputable abbrev ax_compiled := kissatM7Fidelity_compiled_arm64

theorem ax_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM7Fidelity_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m7FidelityModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (m7FidelityEnv f.name f.as f.rs)
        (kissatM7Fidelity_compiled_arm64.bound f.name) 0 :=
  m7Fidelity_module_fnspec k₀ hc hu hf

#print axioms ax_compiled
#print axioms ax_fnspec
#print axioms ax_unsat
#print axioms ax_unsat_sound
#print axioms ax_unsat_nv
#print axioms ax_run_unsat

end LeanQbe.T.Arm64.KissatM7Fidelity
