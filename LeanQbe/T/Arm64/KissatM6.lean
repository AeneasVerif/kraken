module

public import LeanQbe.T.Arm64.KissatM6Cert
public import LeanQbe.T.Arm64.KissatM6CertLink
public import LeanQbe.T.Examples.Kissat.FullM6Proof
public import LeanQbe.T.Examples.Kissat.FullM6InlPolicy
import LeanQbe.T.Examples.Kissat.FullM6SatSound
import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.Logic.MemLemmas
import Std.Sat.CNF.Basic
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM6 (`382` fns) UNSAT Soundness & Non-Vacuity: AAPCS64 Arm64

Combines `KissatM6Cert.m6Cert` and `KissatM6CertLink` with `FullM6Proof`'s parameterized
UNSAT-only contracts (`mkM6Env`, `mkM6Env_core_moduleOk`, `mkM6Env_noExit`), closing
immediately once `FullM6OrchProof0..1` supplies the `24`-fn prefix `tPfx`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM6

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM6 LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM6CertLink Kraken
open LeanQbe.T.Examples.Kissat.FullM6Hdr LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Orch LeanQbe.T.Examples.Kissat.FullM6Proof
open LeanQbe.T.Examples.Kissat.FullM6InlPolicy

/-- Compiled `LinkedCert` for `m6Module.optInlinePolicy m6InlPolicy` (`382` functions) on AAPCS64
Arm64. -/
noncomputable def kissatM6_compiled_arm64 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (m6Module.optInlinePolicy m6InlPolicy) :=
  KissatM6Cert.m6Cert

/-- Whole-module `Defined` + `FnSpec` for all `382` functions in `m6Module` under
`mkM6Env tPfx fullM6SolveBytesCoreModelSpec` on AAPCS64 Arm64. -/
theorem m6_module_fnspec
    (tPfx : List SpecEntry)
    (hN : tPfx.all SpecEntry.noExit = true)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X)
    [hh : Host] (k₀ : Nat)
    (hc : kissatM6_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m6Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name
        (mkM6Env tPfx fullM6SolveBytesCoreModelSpec f.name f.as f.rs)
        (kissatM6_compiled_arm64.bound f.name) 0 :=
  KissatM6CertLink.mk_module_fnspec (mkM6Env tPfx fullM6SolveBytesCoreModelSpec)
    (mkM6Env_core_moduleOk tPfx hS hP hO hK)
    (fun g _ => mkM6Env_noExit tPfx fullM6SolveBytesCoreModelSpec hN g.name g.as g.rs)
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

private theorem m6NvPayload_length (cnfBytes : List UInt8) :
    (m6NvPayload cnfBytes).length = cnfBytes.length + m6NvWorkLen := by
  simp only [m6NvPayload, List.length_append, List.length_replicate]

private theorem m6NvPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 2048) :
    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) m6NvWorkLen)
      ((m6NvPayload cnfBytes).At nvM6CnfPtr) :=
  nv_sep_append rfl
    (by unfold m6NvWorkLen; rw [List.length_replicate]; omega)
    rfl ⟨List.replicate m6NvWorkLen 0, List.length_replicate, rfl⟩

private theorem m6Nv_unsat_bound :
    fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 ≤ m6NvWorkLen := by
  unfold m6NvWorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes
    u32FullBytes fullMinDepthOf
  decide

section Unsat

variable (tPfx : List SpecEntry)
  (hN : tPfx.all SpecEntry.noExit = true)
  (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
  (hP : M6OrchPfxTblSpecs tPfx)
  (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
  (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
    mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X)
  [hh : Host] (k₀ : Nat)
  (hc : kissatM6_compiled_arm64.code.IsInfixAt Host.prog k₀)
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
        (kissatM6_compiled_arm64.bound "kissat_solve_bytes"))
      (kissatM6_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem)
include hN hS hP hO hK hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
  hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- End-to-end AAPCS64 Arm64 UNSAT soundness + framing for `m6Module` (`432`-word `FullM6Hdr`). -/
theorem m6_solve_bytes_unsat_arm64 :
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
              (kissatM6_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM6_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn := (m6_module_fnspec tPfx hN hS hP hO hK k₀ hc hu solve_in_m6Module).2
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM6_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM6_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)) s.dmem := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM6_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM6_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem := by
    rw [sep_assoc]; exact hm_dmem
  have hspec : mkM6Env tPfx fullM6SolveBytesCoreModelSpec "kissat_solve_bytes"
      [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    (mkM6Env_solve_bytes_iff tPfx fullM6SolveBytesCoreModelSpec hS).mpr
      (fullM6SolveBytesCoreModelSpec_intro (R := emp) hcfit hwfit
        (by rw [sep_emp]; exact hm_in)
        (fun _ _ hdom hu _ _ hm' =>
          by rw [sep_emp] at hm'; exact ⟨hdom, hu, hm'⟩))
  refine eventually_weaken _ _ _ _ ?_
    (KissatM6CertLink.solve_arm64_of_fnspec hfn cnf_ptr _ work_ptr _ fuel
      hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hm_dmem')
  rintro st ⟨hpc, hcal, hsp', m', ⟨hdom, hu', hm'⟩, hst⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hcal, hsp', hst'⟩

/-- Answer-only AAPCS64 Arm64 UNSAT soundness corollary for `m6Module`. -/
theorem kissat_m6_arm64_unsat_correct :
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
    (m6_solve_bytes_unsat_arm64 tPfx hN hS hP hO hK k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

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
  kissat_m6_arm64_unsat_correct tPfx hN hS hP hO hK k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
    hcfit hwfit s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

end Unsat

/-- Concrete AAPCS64 Arm64 UNSAT non-vacuity for `m6Module` on `432`-word `FullM6Hdr`
(`nvM6UnsatBytes`, `6144`-byte workspace, `fuel = 16`). -/
theorem m6_arm64_unsat_nonvacuous
    (tPfx : List SpecEntry)
    (hN : tPfx.all SpecEntry.noExit = true)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X)
    [hh : Host] (k₀ : Nat)
    (hc : kissatM6_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
            (kissatM6_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM6_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : armTarget.FnSpec hh "kissat_solve_bytes"
      (mkM6Env tPfx fullM6SolveBytesCoreModelSpec "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64])
      (kissatM6_compiled_arm64.bound "kissat_solve_bytes") 0 :=
    (m6_module_fnspec tPfx hN hS hP hO hK k₀ hc hu solve_in_m6Module).2
  let b := kissatM6_compiled_arm64.bound "kissat_solve_bytes"
  let bs := m6NvPayload nvM6UnsatBytes
  let s := armInit.initState (as := [i64, i64, i64, i64, i64]) b bs
    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
  have h1 := armInitMem_entry b bs (kissatM6_compiled_arm64.bound_le_max _)
    (by rw [m6NvPayload_length]; unfold m6NvWorkLen; decide)
  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 b ⋆ emp at h1
  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds] at h1
  simp only [region_zero, sep_emp] at h1
  have h1' : (Eq (bs.At 0x1000#64) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem := by
    rw [show s.regs.SP.toBitVec = 0x1000#64 from rfl]; simpa [sep_emp] using h1
  have hdm : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      region nvM6UnsatWorkPtr m6NvWorkLen ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem :=
    sep_mono (Q := emp)
      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))
        (fun _ heq => heq ▸ m6NvPayload_sep nvM6UnsatBytes (by decide))) h1'
  have hhsp : s.regs.SP.toNat % 16 = 0 := by rw [show s.regs.SP = 4096 from rfl]; decide
  refine ⟨nvM6CnfPtr, nvM6UnsatWorkPtr, 16#64, nvM6UnsatBytes, m6NvWorkLen,
    s, 0x1234, emp, by decide, by decide, rfl, rfl, rfl, rfl, rfl,
    rfl,
    hhsp, hdm, ?_⟩
  have hspec : mkM6Env tPfx fullM6SolveBytesCoreModelSpec "kissat_solve_bytes"
      [i64, i64, i64, i64, i64] [i64]
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
      (bs.At 0x1000#64) (fun r _ => r.fst = 20#64 ∧ nvM6UnsatCnf.Unsat)
      (fun _ _ _ _ => False) :=
    (mkM6Env_solve_bytes_iff tPfx fullM6SolveBytesCoreModelSpec hS).mpr
      (fullM6SolveBytesCoreModelSpec_intro (R := emp) (by decide) (by decide)
        (by
          rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
          exact m6NvPayload_sep nvM6UnsatBytes (by decide))
        (fun _ _ _ _ _ htr _ =>
          ⟨htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
            (by decide) nvM6Unsat_header nvM6Unsat_unitTrace, nvM6UnsatCnf_unsat⟩))
  have hev := KissatM6CertLink.solve_arm64_of_fnspec hfn nvM6CnfPtr _
    nvM6UnsatWorkPtr _ 16#64 hspec s 0x1234 emp
    rfl rfl rfl rfl rfl rfl hhsp h1'
  exact eventually_weaken _ _ _ _
    (fun _ ⟨hpc, _, _, _, ⟨h20, huns⟩, _⟩ =>
      ⟨hpc, h20, nvM6UnsatCnf, parseDimacs_nvM6UnsatBytes, huns⟩)
    hev

/-- Closed concrete-host AAPCS64 Arm64 UNSAT execution witness on `kissatM6_compiled_arm64.host`
(`432`-word `FullM6Hdr`). -/
theorem m6_arm64_run_unsat
    (tPfx : List SpecEntry)
    (hN : tPfx.all SpecEntry.noExit = true)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X) :
    Eventually (armTarget.mach.step kissatM6_compiled_arm64.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          armTarget.Exit armInit.sp0
            (kissatM6_compiled_arm64.bound "kissat_solve_bytes") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64, i64, i64])
          (kissatM6_compiled_arm64.bound "kissat_solve_bytes")
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (armTarget.mach.labelAddr kissatM6_compiled_arm64.host "kissat_solve_bytes")) := by
  refine kissatM6_compiled_arm64.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy armInit
    (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (mkM6Env_core_moduleOk tPfx hS hP hO hK)
    m6_legalSig solve_in_m6Module rfl
    (mkM6Env_noExit tPfx fullM6SolveBytesCoreModelSpec hN
      "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
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
  exact (mkM6Env_solve_bytes_iff tPfx fullM6SolveBytesCoreModelSpec hS).mpr
    (fullM6SolveBytesCoreModelSpec_intro (R := emp) (by decide) (by decide)
      (by
        rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
        exact m6NvPayload_sep nvM6UnsatBytes (by decide))
      (fun _ m' _ _ _ htr hm' =>
        ⟨congrArg (·, ()) (htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
          (by decide) nvM6Unsat_header nvM6Unsat_unitTrace),
         nvM6UnsatCnf_unsat, hm'⟩))

#print axioms kissatM6_compiled_arm64
#print axioms m6_module_fnspec
#print axioms m6_solve_bytes_unsat_arm64
#print axioms ax_unsat_sound
#print axioms m6_arm64_unsat_nonvacuous
#print axioms m6_arm64_run_unsat

end LeanQbe.T.Arm64.KissatM6
