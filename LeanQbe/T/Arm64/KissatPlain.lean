module

public import LeanQbe.T.Arm64.KissatPlainCert
public import LeanQbe.T.Examples.Kissat.PlainLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# End-to-End AAPCS64 Arm64 Native Correctness for Kissat `D-Plain` (`Stage 3`)

Combines the kernel-checked `59`-function native AArch64 compilation certificate
(`LeanQbe.T.Arm64.KissatPlainCert.plainCert`) with the `59`-function `plainEnv` soundness proof
(`plainEnv_sound`, `plainEnv_moduleOk`):
* `module_fnspec`: closed `Defined` + `FnSpec` for all 59 functions in `plainModule`;
* `solve_arm64_correct`: closed end-to-end Kraken-AArch64 correctness (`0 | 10 | 20`, UNSAT `20`,
  SAT `10`, callee-saved registers `X19..X29`, `SP`, read-only DIMACS bytes, restored `region`);
* `solve_arm64_sound`: concise soundness corollary;
* `arm64_unsat_nonvacuous`, `arm64_sat_nonvacuous`: concrete executions on `plainCert.host` via
  `armInit`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatPlainCert Kraken

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `plainModule` under `plainEnv` on `armTarget`. -/
theorem module_fnspec (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (plainEnv f.name f.as f.rs) (plainCert.bound f.name) 0 :=
  mk_module_fnspec plainEnv plainEnv_sound (fun _ _ => plainEnv_noExit _ _ _) k₀ hc hu hf

private theorem mk_entry_fnspec
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hsound : ∀ f ∈ plainFns, ∀ args m Q X,
      mkPlainEnv mainSpec f.name f.as f.rs args m Q X →
      Func.wp (mkPlainEnv mainSpec) f.body args m Q X)
    (hno : ∀ xs m Q X, mainSpec xs m Q X → mainSpec xs m Q (fun _ _ _ _ => False))
    (k₀ : Nat) (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    armTarget.FnSpec hh "kissat_solve_bytes" mainSpec
      (plainCert.bound "kissat_solve_bytes") 0 :=
  Target.FnSpec.of_spec armTarget
    (mk_module_fnspec (mkPlainEnv mainSpec) hsound
      (fun g _ => mkPlainEnv_noExit mainSpec g.name g.as g.rs) k₀ hc hu
      (f := Plain.kissat_solve_bytes) (by simp [plainModule, plainFns, plain2_fns])).2
    (mkPlainEnv_solve_bytes mainSpec hno)

/-- Closed end-to-end AAPCS64 Arm64 native machine-code correctness of `plainModule`
(`kissat_solve_bytes`): terminates cleanly, returns `X0 ∈ {0, 10, 20}` certifying UNSAT (`20`)
and SAT (`10`), preserves callee-saved registers `X19..X29`, `SP`, and read-only DIMACS bytes, and
restores `region work_ptr wlen`. -/
theorem solve_arm64_correct (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
        (plainCert.bound "kissat_solve_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
            (plainCert.bound "kissat_solve_bytes") ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
        (plainCert.bound "kissat_solve_bytes") ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn : armTarget.FnSpec hh "kissat_solve_bytes" plainSolveBytesSpec
      (plainCert.bound "kissat_solve_bytes") 0 :=
    mk_entry_fnspec plainSolveBytesSpec plainEnv_sound (fun _ _ _ _ h => h) k₀ hc hu
  have hspec : plainSolveBytesSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit, by rwa [sep_emp],
      fun _ _ hdom hu' hs hm' => ⟨hdom, hu', hs, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (solve_arm64_of_fnspec hfn cnf_ptr (BitVec.ofNat 64 cnfBytes.length)
      work_ptr (BitVec.ofNat 64 wlen) fuel hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', m', ⟨hdom, hu', hs, hm'⟩, hmem'⟩
  exact ⟨hpc, hdom, hu', hs, hcs, hsp',
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem'⟩

/-- Concise AAPCS64 Arm64 soundness corollary of `solve_arm64_correct`. -/
theorem solve_arm64_sound (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
        (plainCert.bound "kissat_solve_bytes") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hdom, hu', hs, _⟩ => ⟨hpc, hdom, hu', hs⟩)
    (solve_arm64_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

end Generic

/-! ## Concrete AArch64 Non-Vacuous Executions in `plainCert.host` (`X0 = 20` and `X0 = 10`) -/

abbrev plainHost : Host := plainCert.host
attribute [local instance] plainHost

def plainArgs (cnfBytes : List UInt8) : Tup Val [i64, i64, i64, i64, i64] :=
  (plainNvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
    plainNvWorkPtr cnfBytes, 2048#64, 16#64, ())

def plainMachState (cnfBytes : List UInt8) : MachineData :=
  armInit.initState (as := [i64, i64, i64, i64, i64])
    (plainCert.bound "kissat_solve_bytes")
    (plainPayload cnfBytes) (plainArgs cnfBytes)

def plainUnsatState0 : MachineData :=
  plainMachState plainNvUnsatBytes

/-- Concrete UNSAT execution of compiled `kissat_solve_bytes` on Kraken AArch64 (`X0 = 20`). -/
theorem arm64_unsat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧ plainNvUnsatCnf.Unsat)
      ⟨plainUnsatState0, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : armTarget.FnSpec plainHost "kissat_solve_bytes" plainUnsatWitnessSpec
      (plainCert.bound "kissat_solve_bytes") 0 :=
    mk_entry_fnspec plainUnsatWitnessSpec plainUnsatEnv_sound (fun _ _ _ _ h => h)
      0 plainCert.code_infix_host plainCert.labelsUnique
  have hspec : plainUnsatWitnessSpec (plainArgs plainNvUnsatBytes)
      ((plainPayload plainNvUnsatBytes).At 0x1000#64)
      (fun rs _ => rs = (20#64, ()) ∧ plainNvUnsatCnf.Unsat) (fun _ _ _ _ => False) :=
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact plainPayload_sep plainNvUnsatBytes (by decide),
      fun _ hu _ => ⟨rfl, hu⟩⟩
  refine plainCert.run_fnSpec armInit hfn (plainPayload plainNvUnsatBytes)
    (plainArgs plainNvUnsatBytes)
    (by simp [plainPayload_length, plainNvUnsatBytes]) (by decide) hspec ?_
  rintro st (⟨hpc, _, _, ⟨rfl, hu⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, hu⟩
    simpa [armInit, get_reg] using armInit.retsIn_singleton 20#64 _ hrets
  · exact hx.elim

def plainSatState0 : MachineData :=
  plainMachState plainNvSatBytes

/-- Concrete SAT execution of compiled `kissat_solve_bytes` on Kraken AArch64 (`X0 = 10`). -/
theorem arm64_sat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 10#64 ∧
        ¬ plainNvSatCnf.Unsat ∧ ∃ α, plainNvSatCnf.Sat α)
      ⟨plainSatState0, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : armTarget.FnSpec plainHost "kissat_solve_bytes" plainSatWitnessSpec
      (plainCert.bound "kissat_solve_bytes") 0 :=
    mk_entry_fnspec plainSatWitnessSpec plainSatEnv_sound (fun _ _ _ _ h => h)
      0 plainCert.code_infix_host plainCert.labelsUnique
  have hspec : plainSatWitnessSpec (plainArgs plainNvSatBytes)
      ((plainPayload plainNvSatBytes).At 0x1000#64)
      (fun rs _ => rs = (10#64, ()) ∧ ¬ plainNvSatCnf.Unsat ∧ ∃ α, plainNvSatCnf.Sat α)
      (fun _ _ _ _ => False) :=
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact plainPayload_sep plainNvSatBytes (by decide),
      fun _ hnu hsat _ => ⟨rfl, hnu, hsat⟩⟩
  refine plainCert.run_fnSpec armInit hfn (plainPayload plainNvSatBytes)
    (plainArgs plainNvSatBytes)
    (by simp [plainPayload_length, plainNvSatBytes]) (by decide) hspec ?_
  rintro st (⟨hpc, _, _, ⟨rfl, hnu, hsat⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · refine ⟨hpc, ?_, hnu, hsat⟩
    simpa [armInit, get_reg] using armInit.retsIn_singleton 10#64 _ hrets
  · exact hx.elim

#guard plainFns.length == 59
#guard plainModule.checkAcyclic == true

#print axioms module_fnspec
#print axioms solve_arm64_correct
#print axioms solve_arm64_sound
#print axioms arm64_unsat_nonvacuous
#print axioms arm64_sat_nonvacuous

end LeanQbe.T.Arm64.KissatPlain
