module

public import LeanQbe.T.Arm64.KissatM5Cert
public import LeanQbe.T.Arm64.KissatM5CertLink
public import LeanQbe.T.Examples.Kissat.FullM5Proof
import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.Logic.MemLemmas
import Std.Sat.CNF.Basic
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM5 (`270` fns, `InlinePolicy.b5`) Unconditional AAPCS64 Arm64 Theorems

Combines `KissatM5Cert.m5Cert` (`FullM5.m5Module.optInlinePolicy InlinePolicy.b5`) and
`KissatM5CertLink` with `FullM5Proof` contracts (`m5Env_moduleOk`, `m5UnsatEnv_moduleOk`) to
establish unconditional AAPCS64 Arm64 UNSAT soundness (`Eventually (step1 Host.exe)` + `cnf.Unsat`)
and both arbitrary-host and concrete-host UNSAT non-vacuity (`XPost := False`, standard axioms).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM5

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM5 LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM5CertLink Kraken
open LeanQbe.T.Examples.Kissat.Full
  (fullSolveBytesSpec fullUnsatWitnessSpec fullPayload fullPayload_length fullPayload_sep
    fullNvUnsatBytes fullNvUnsatCnf fullNvCnfPtr fullNvWorkPtr parseDimacs_fullNvUnsatBytes)

/-- Compiled `InlinePolicy.b5` `LinkedCert` for `m5Module` (`270` functions) on AAPCS64 Arm64. -/
@[reducible] noncomputable def kissatM5_compiled_arm64 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (m5Module.optInlinePolicy InlinePolicy.b5) :=
  KissatM5Cert.m5Cert

/-- Unconditional whole-module `Defined` + `FnSpec` for all `270` functions in `m5Module`
compiled under `InlinePolicy.b5` against `m5Env` on AAPCS64 Arm64. -/
theorem m5_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM5_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m5Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (m5Env f.name f.as f.rs)
        (kissatM5_compiled_arm64.bound f.name) 0 :=
  KissatM5CertLink.mk_module_fnspec m5Env m5Env_moduleOk
    (fun g _ => m5Env_noExit g.name g.as g.rs) k₀ hc hu hf

private theorem solve_in_m5Module :
    m5SolveBytesFwdFn ∈ m5Module.fns := by
  exact List.mem_of_getElem?
    (by t_kernel_rfl : (m5Module.fns)[269]? = some m5SolveBytesFwdFn)

private theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}
    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by
  have hm := sep_mono (Q := Q)
    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h
  rw [sep_ex_l] at hm
  obtain ⟨m, hm'⟩ := hm
  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩

section Unsat

variable [hh : Host] (k₀ : Nat)
  (hc : kissatM5_compiled_arm64.code.IsInfixAt Host.prog k₀)
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
        (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
      (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem)
include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
  hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- Unconditional AAPCS64 Arm64 UNSAT soundness + framing for `InlinePolicy.b5` `m5Module`.
-/
theorem m5_solve_bytes_unsat_arm64 :
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
              (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn := (m5_module_fnspec k₀ hc hu solve_in_m5Module).2
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)) s.dmem := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem := by
    rw [sep_assoc]; exact hm_dmem
  have hspec : m5Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    m5Env_solve_bytes
      ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit,
        by rw [sep_emp]; exact hm_in,
        fun _ _ h u' m' =>
          by rw [sep_emp] at m'; exact ⟨h, u', m'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (KissatM5CertLink.solve_arm64_of_fnspec hfn cnf_ptr _ work_ptr _ fuel
      hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hm_dmem')
  rintro st ⟨hpc, hcal, hsp', m', ⟨hdom, hu', hm'⟩, hst⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hcal, hsp', hst'⟩

/-- Answer-only AAPCS64 Arm64 UNSAT soundness corollary for `InlinePolicy.b5` `m5Module`. -/
theorem kissat_m5_arm64_unsat_correct :
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
    (m5_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

end Unsat

/-- Unconditional concrete AAPCS64 Arm64 UNSAT non-vacuity for `InlinePolicy.b5` `FullM5.m5Module`
(`270` fns): there exists a well-formed call on `fullNvUnsatBytes` (`4096`-byte workspace,
`fuel = 16`) that returns `X0 = 20#64` with `parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`. -/
theorem m5_arm64_unsat_nonvacuous [hh : Host] (k₀ : Nat)
    (hc : kissatM5_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
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
            (kissatM5_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : armTarget.FnSpec hh "kissat_solve_bytes"
      (m5UnsatEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (kissatM5_compiled_arm64.bound "kissat_solve_bytes") 0 :=
    (KissatM5CertLink.mk_module_fnspec m5UnsatEnv m5UnsatEnv_moduleOk
      (fun g _ => m5UnsatEnv_noExit g.name g.as g.rs) k₀ hc hu solve_in_m5Module).2
  let b := kissatM5_compiled_arm64.bound "kissat_solve_bytes"
  let bs := fullPayload fullNvUnsatBytes
  let s := armInitState b bs (as := [i64, i64, i64, i64, i64])
    (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
      fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ())
  have h1 := armInitMem_entry b bs (kissatM5_compiled_arm64.bound_le_max _)
    (by rw [fullPayload_length]; decide)
  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 b ⋆ emp at h1
  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds] at h1
  simp only [region_zero, sep_emp] at h1
  have h1' : (Eq (bs.At 0x1000#64) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem := by
    rw [show s.regs.SP.toBitVec = 0x1000#64 from rfl]; simpa [sep_emp] using h1
  have hdm : (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
      region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem :=
    sep_mono (Q := emp)
      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))
        (fun _ heq => heq ▸ fullPayload_sep fullNvUnsatBytes (by decide))) h1'
  have hhsp : s.regs.SP.toNat % 16 = 0 := by rw [show s.regs.SP = 4096 from rfl]; decide
  refine ⟨fullNvCnfPtr, fullNvWorkPtr fullNvUnsatBytes, 16#64, fullNvUnsatBytes, 4096,
    s, 0x1234, emp, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, hhsp, hdm, ?_⟩
  have hspec : m5UnsatEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ())
      (bs.At 0x1000#64) (fun r _ => r.fst = 20#64 ∧ fullNvUnsatCnf.Unsat)
      (fun _ _ _ _ => False) :=
    m5UnsatEnv_solve_bytes
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ huns _ => ⟨rfl, huns⟩⟩
  have hev := KissatM5CertLink.solve_arm64_of_fnspec hfn fullNvCnfPtr _
    (fullNvWorkPtr fullNvUnsatBytes) _ 16#64 hspec s 0x1234 emp
    rfl rfl rfl rfl rfl rfl hhsp h1'
  exact eventually_weaken _ _ _ _
    (fun _ ⟨hpc, _, _, _, ⟨h20, huns⟩, _⟩ =>
      ⟨hpc, h20, fullNvUnsatCnf, parseDimacs_fullNvUnsatBytes, huns⟩)
    hev

/-- Closed concrete-host AAPCS64 Arm64 execution witness on `kissatM5_compiled_arm64.host` via
`MainCertInline.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy` (`XPost := False`). -/
theorem m5_arm64_run_unsat :
    Eventually (armTarget.mach.step kissatM5_compiled_arm64.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 20#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (fun m' => fullNvUnsatCnf.Unsat ∧
            (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
              region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m') ⋆
          armTarget.Exit armInit.sp0
            (kissatM5_compiled_arm64.bound "kissat_solve_bytes") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64, i64, i64])
          (kissatM5_compiled_arm64.bound "kissat_solve_bytes")
          (fullPayload fullNvUnsatBytes)
          (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
            fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()))
        (armTarget.mach.labelAddr kissatM5_compiled_arm64.host "kissat_solve_bytes")) := by
  refine kissatM5_compiled_arm64.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy armInit
    m5UnsatEnv m5UnsatEnv_moduleOk m5_legalSig solve_in_m5Module rfl
    (m5UnsatEnv_noExit "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
    (fullPayload fullNvUnsatBytes)
    (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
      fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ())
    20#64
    (fun m' => fullNvUnsatCnf.Unsat ∧
      (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
        region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
    (by rw [fullPayload_length]; decide) rfl
    (Q := fun r m' => r = (20#64, ()) ∧ fullNvUnsatCnf.Unsat ∧
      (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
        region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
    ?_ (fun _ _ h => h) (by decide)
  exact m5UnsatEnv_solve_bytes
    ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
      fun _ huns hm' => ⟨rfl, huns, hm'⟩⟩

#print axioms kissatM5_compiled_arm64
#print axioms m5_module_fnspec
#print axioms m5_solve_bytes_unsat_arm64
#print axioms kissat_m5_arm64_unsat_correct
#print axioms m5_arm64_unsat_nonvacuous
#print axioms m5_arm64_run_unsat

end LeanQbe.T.Arm64.KissatM5
