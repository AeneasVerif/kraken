module

public import LeanQbe.T.Amd64.KissatPlainCert
public import LeanQbe.T.Examples.Kissat.PlainLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.AbiLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# End-to-End SysV x64 Native Correctness for Kissat `D-Plain` (`Stage 3`)

Combines the kernel-checked `59`-function native x64 compilation certificate
(`LeanQbe.T.Amd64.KissatPlainCert.plainCert`) with the `59`-function `plainEnv` soundness proof
(`plainEnv_sound`, `plainEnv_moduleOk`):
* `module_fnspec`: closed `Defined` + `FnSpec` for all 59 functions in `plainModule`;
* `solve_x64_correct`: closed end-to-end Kraken-x64 correctness (`0 | 10 | 20`, UNSAT `20`,
  SAT `10`, callee-saved registers, `rsp`, read-only DIMACS bytes, restored `region`);
* `solve_x64_sound`: concise soundness corollary;
* `x64_unsat_nonvacuous`, `x64_sat_nonvacuous`: concrete executions on `plainCert.host` via
  `x64Init`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatPlain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatPlainCert Kraken

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `plainModule` under `plainEnv` on `x64Target`. -/
theorem module_fnspec (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (plainEnv f.name f.as f.rs) (plainCert.bound f.name) 0 :=
  mk_module_fnspec plainEnv plainEnv_sound (fun _ _ => plainEnv_noExit _ _ _) k₀ hc hu hf

private theorem mk_entry_fnspec
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hsound : ∀ f ∈ plainFns, ∀ args m Q X,
      mkPlainEnv mainSpec f.name f.as f.rs args m Q X →
      Func.wp (mkPlainEnv mainSpec) f.body args m Q X)
    (hno : ∀ xs m Q X, mainSpec xs m Q X → mainSpec xs m Q (fun _ _ _ _ => False))
    (k₀ : Nat) (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    x64Target.FnSpec hh "kissat_solve_bytes" mainSpec
      (plainCert.bound "kissat_solve_bytes") 0 :=
  Target.FnSpec.of_spec x64Target
    (mk_module_fnspec (mkPlainEnv mainSpec) hsound
      (fun g _ => mkPlainEnv_noExit mainSpec g.name g.as g.rs) k₀ hc hu
      (f := Plain.kissat_solve_bytes) (by simp [plainModule, plainFns, plain2_fns])).2
    (mkPlainEnv_solve_bytes mainSpec hno)

/-- Closed end-to-end SysV x64 native machine-code correctness of `plainModule`
(`kissat_solve_bytes`): terminates cleanly, returns `rax ∈ {0, 10, 20}` certifying UNSAT (`20`)
and SAT (`10`), preserves callee-saved registers, `rsp`, and read-only DIMACS bytes, and restores
`region work_ptr wlen`. -/
theorem solve_x64_correct (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
          (plainCert.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (st.data.regs.get64 .rax = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
            (plainCert.bound "kissat_solve_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
          (plainCert.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn : x64Target.FnSpec hh "kissat_solve_bytes" plainSolveBytesSpec
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
    (solve_x64_of_fnspec hfn cnf_ptr (BitVec.ofNat 64 cnfBytes.length)
      work_ptr (BitVec.ofNat 64 wlen) fuel hspec s ra R hrdi hrsi hrdx hrcx hr8 hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', m', ⟨hdom, hu', hs, hm'⟩, hmem'⟩
  exact ⟨hpc, hdom, hu', hs, hcs, hsp',
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem'⟩

/-- Concise SysV x64 soundness corollary of `solve_x64_correct`. -/
theorem solve_x64_sound (k₀ : Nat)
    (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
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
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (plainCert.bound "kissat_solve_bytes"))
          (plainCert.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (st.data.regs.get64 .rax = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hdom, hu', hs, _⟩ => ⟨hpc, hdom, hu', hs⟩)
    (solve_x64_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      hrdi hrsi hrdx hrcx hr8 hsp hmem)

end Generic

/-! ## Concrete SysV x64 Non-Vacuous Executions in `plainCert.host` (`rax = 20` and `rax = 10`) -/

noncomputable abbrev plainHost : Host := plainCert.host
attribute [local instance] plainHost

def plainArgs (cnfBytes : List UInt8) : Tup Val [i64, i64, i64, i64, i64] :=
  (plainNvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
    plainNvWorkPtr cnfBytes, 2048#64, 16#64, ())

noncomputable def plainMachState (cnfBytes : List UInt8) : MachineData :=
  x64Init.initState (as := [i64, i64, i64, i64, i64])
    (plainCert.bound "kissat_solve_bytes")
    (plainPayload cnfBytes) (plainArgs cnfBytes)

noncomputable def plainUnsatState0 : MachineData :=
  plainMachState plainNvUnsatBytes

/-- Concrete UNSAT execution of compiled `kissat_solve_bytes` on Kraken x64 (`rax = 20`). -/
theorem x64_unsat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 20#64 ∧ plainNvUnsatCnf.Unsat)
      ⟨plainUnsatState0, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : x64Target.FnSpec plainHost "kissat_solve_bytes" plainUnsatWitnessSpec
      (plainCert.bound "kissat_solve_bytes") 0 :=
    mk_entry_fnspec plainUnsatWitnessSpec plainUnsatEnv_sound (fun _ _ _ _ h => h)
      0 plainCert.code_infix_host plainCert.labelsUnique
  have hspec : plainUnsatWitnessSpec (plainArgs plainNvUnsatBytes)
      ((plainPayload plainNvUnsatBytes).At 0x1000#64)
      (fun rs _ => rs = (20#64, ()) ∧ plainNvUnsatCnf.Unsat) (fun _ _ _ _ => False) :=
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact plainPayload_sep plainNvUnsatBytes (by decide),
      fun _ hu _ => ⟨rfl, hu⟩⟩
  refine plainCert.run_fnSpec x64Init hfn (plainPayload plainNvUnsatBytes)
    (plainArgs plainNvUnsatBytes)
    (by simp [plainPayload_length, plainNvUnsatBytes]) (by decide) hspec ?_
  rintro st (⟨hpc, _, _, ⟨rfl, hu⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, x64Init.retsIn_singleton 20#64 _ hrets, hu⟩
  · exact hx.elim

noncomputable def plainSatState0 : MachineData :=
  plainMachState plainNvSatBytes

/-- Concrete SAT execution of compiled `kissat_solve_bytes` on Kraken x64 (`rax = 10`). -/
theorem x64_sat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 10#64 ∧
        ¬ plainNvSatCnf.Unsat ∧ ∃ α, plainNvSatCnf.Sat α)
      ⟨plainSatState0, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : x64Target.FnSpec plainHost "kissat_solve_bytes" plainSatWitnessSpec
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
  refine plainCert.run_fnSpec x64Init hfn (plainPayload plainNvSatBytes)
    (plainArgs plainNvSatBytes)
    (by simp [plainPayload_length, plainNvSatBytes]) (by decide) hspec ?_
  rintro st (⟨hpc, _, _, ⟨rfl, hnu, hsat⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, x64Init.retsIn_singleton 10#64 _ hrets, hnu, hsat⟩
  · exact hx.elim

#guard plainFns.length == 59
#guard plainModule.checkAcyclic == true

#print axioms module_fnspec
#print axioms solve_x64_correct
#print axioms solve_x64_sound
#print axioms x64_unsat_nonvacuous
#print axioms x64_sat_nonvacuous

end LeanQbe.T.Amd64.KissatPlain
