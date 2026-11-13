module

public import LeanQbe.Arm64.Abi
public import LeanQbe.Examples.LratTrimCheckLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# LRAT-trim checker (`lratTrimFns`) on AArch64

Instantiates the target-generic 5-function LRAT-trim module `lratTrimFns` on `Arm64.target`
via a single kernel evaluation (`compileChecked ... (by kernel_rfl)`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.LratTrim

open LeanQbe LeanQbe.LratRup LeanQbe.LratTrim Arm64 Kraken
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal Kraken.Bedrock2.Test

/-- Single kernel evaluation of the compiler on `lratTrimFns` for AArch64. -/
def compiled : Compiled target [] ["lrat_fail"] 0 lratTrimFns :=
  compileChecked target targetLayout [] ["lrat_fail"] 0 lratTrimFns 2048 (by kernel_rfl)

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `lratTrimFns` against `lratEnv` on `Arm64.target`. -/
theorem lrat_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail")
    {nm : String} (hnm : nm ∈ lratTrimFns.map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (lratEnv nm) (compiled.bound nm) 0 :=
  lrat_fnSpec compiled hh k₀ hc hu hfail hnm

/-- Closed `FnSpec` for every function in `lratTrimFns` against `lratAcceptEnv` on `Arm64.target`. -/
theorem lrat_module_accepts_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail")
    {nm : String} (hnm : nm ∈ lratTrimFns.map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (lratAcceptEnv nm) (compiled.bound nm) 0 :=
  lrat_accepts_fnSpec compiled hh k₀ hc hu hfail hnm

/-- End-to-end correctness of compiled `br_check_proof` on Kraken AArch64. -/
theorem checkProof_arm64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail")
    {max_var n : Nat} {st_ptr : BitVec 64} {k₀_fields : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List Val} {cnf₀ : CNF Nat}
    {clauses : List (CNF.Clause Nat)} {litsTable anteTable : List (List Val)}
    {P_ro : Mem 64 → Prop} {m : Mem 64}
    (pre : CheckProofPre max_var n st_ptr k₀_fields usedWords litsPtrs antePtrs trail_free0 cnf₀
      clauses litsTable anteTable P_ro m)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = st_ptr)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "br_check_proof" ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "br_check_proof"))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧ cnf₀.Unsat ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP ∧
          ∃ m' k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m' ∧
            (st.data.dmem =⋆ Eq m' ⋆
              (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "br_check_proof" ∧
                  f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 (compiled.bound "br_check_proof"))) ⋆ R)) ∨
        (st.pc = Labels.label "lrat_fail" ∧ st.data.regs.SP.toNat % 16 = 0))
      ⟨s, Labels.label "br_check_proof"⟩ := by
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨f_m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩ := hmem
  let Q : LeanQbe.Post := fun rets m' =>
    rets = [] ∧ (∃ k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m') ∧ cnf₀.Unsat
  let X : XPost := fun g _ _ => g = "lrat_fail"
  have hspec : checkProofSpec [st_ptr] m Q X :=
    ⟨max_var, n, st_ptr, k₀_fields, usedWords, litsPtrs, antePtrs, trail_free0, cnf₀,
      clauses, litsTable, anteTable, P_ro, rfl, pre,
      fun _ hinv hunsat => ⟨rfl, hinv, hunsat⟩, fun _ _ => rfl⟩
  have hargs : target.ArgsIn [st_ptr] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hx0]
  have hf := (lrat_module_fnspec k₀ hc hu hfail (nm := "br_check_proof") (by decide)).2
    [st_ptr] m Q X hspec s ra R hargs hra hsp
    (by
      simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
      exact ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩)
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, ⟨k', hinv'⟩, hunsat⟩, -, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', as', m', rfl, _, hpc, _, hspE, _⟩)
  · rw [Target.Exit] at hm'
    refine Or.inl ⟨hpc, hunsat, fun r hr => ?_, ?_, m', k', hinv',
      sep_mono (fun _ => sep_mono (fun _ h => h)) hm'⟩
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
  · exact Or.inr ⟨hpc, hspE⟩

end Generic

/-! ## Concrete AArch64 executions in `compiled.host` -/

abbrev lratHost : Host := compiled.host
attribute [local instance] lratHost

def lratState0 : MachineData :=
  initState (compiled.bound "br_check_proof") nvCheckBytes [0x1000]

theorem checkProof_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = 0x1234 ∧ (CNF.empty : CNF Nat).Unsat) ∨
        st.pc = Labels.label "lrat_fail")
      ⟨lratState0, Labels.label "br_check_proof"⟩ :=
  checkProof_nonvacuous_witness targetInit compiled

def lratAcceptState0 : MachineData :=
  initState (compiled.bound "br_check_proof") nvAcceptBytes [0x1000]

/-- Concrete accepting execution of compiled `br_check_proof` on Kraken AArch64. -/
theorem checkProof_arm64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ nvAcceptCnf.Unsat)
      ⟨lratAcceptState0, Labels.label "br_check_proof"⟩ :=
  checkProof_accepts_witness targetInit compiled

end LeanQbe.Arm64.LratTrim
