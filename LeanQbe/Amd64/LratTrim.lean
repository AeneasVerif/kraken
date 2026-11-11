module

public import LeanQbe.Amd64.TargLemmas
public import LeanQbe.Examples.LratTrimCheckLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# LRAT-trim checker (`lratTrimFns`) on x64

Instantiates the target-generic 5-function LRAT-trim module `lratTrimFns` on `Amd64.target`
via a single kernel evaluation (`compileChecked ... (by kernel_rfl)`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Amd64.LratTrim

open LeanQbe LeanQbe.LratRup LeanQbe.LratTrim Amd64 Kraken
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal Kraken.Bedrock2.Test

/-- Single kernel evaluation of the compiler on `lratTrimFns` for x64. -/
def compiled : Compiled target [] ["lrat_fail"] 0 lratTrimFns :=
  compileChecked target targetLayout [] ["lrat_fail"] 0 lratTrimFns 2048 (by kernel_rfl)

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `lratTrimFns` against `lratEnv` on `Amd64.target`. -/
theorem lrat_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail")
    {nm : String} (hnm : nm ∈ lratTrimFns.map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (lratEnv nm) (compiled.bound nm) 0 :=
  lrat_fnSpec compiled hh k₀ hc hu hfail hnm

/-- Closed `FnSpec` for every function in `lratTrimFns` against `lratAcceptEnv` on `Amd64.target`. -/
theorem lrat_module_accepts_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail")
    {nm : String} (hnm : nm ∈ lratTrimFns.map Fn.name) :
    target.Defined hh nm ∧ target.FnSpec hh nm (lratAcceptEnv nm) (compiled.bound nm) 0 :=
  lrat_accepts_fnSpec compiled hh k₀ hc hu hfail hnm

/-- End-to-end correctness of compiled `br_check_proof` on Kraken x64. -/
theorem checkProof_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail")
    {max_var n : Nat} {st_ptr : BitVec 64} {k₀_fields : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List Val} {cnf₀ : CNF Nat}
    {clauses : List (CNF.Clause Nat)} {litsTable anteTable : List (List Val)}
    {P_ro : Mem 64 → Prop} {m : Mem 64}
    (pre : CheckProofPre max_var n st_ptr k₀_fields usedWords litsPtrs antePtrs trail_free0 cnf₀
      clauses litsTable anteTable P_ro m)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = st_ptr)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = compiled.bound "br_check_proof" ∧
          f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "br_check_proof"))) ⋆
        Eq (ra.toUInt64.At (s.regs.get64 .rsp))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧ cnf₀.Unsat ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
          ∃ m' k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m' ∧
            (st.data.dmem =⋆ Eq m' ⋆
              (fun f => ∃ bs : List UInt8, bs.length = compiled.bound "br_check_proof" + 8 ∧
                  f = bs.At (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "br_check_proof"))) ⋆ R)) ∨
        (st.pc = Labels.label "lrat_fail" ∧ (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0))
      ⟨s, Labels.label "br_check_proof"⟩ := by
  let Q : LeanQbe.Post := fun rets m' =>
    rets = [] ∧ (∃ k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m') ∧ cnf₀.Unsat
  let X : XPost := fun g _ _ => g = "lrat_fail"
  have hspec : checkProofSpec [st_ptr] m Q X :=
    ⟨max_var, n, st_ptr, k₀_fields, usedWords, litsPtrs, antePtrs, trail_free0, cnf₀,
      clauses, litsTable, anteTable, P_ro, rfl, pre,
      fun _ hinv hunsat => ⟨rfl, hinv, hunsat⟩, fun _ _ => rfl⟩
  have hargs : target.ArgsIn [st_ptr] s := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, hrdi]
  have hf := (lrat_module_fnspec k₀ hc hu hfail (nm := "br_check_proof") (by decide)).2
    [st_ptr] m Q X hspec s ra R hargs trivial hsp hmem
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, ⟨k', hinv'⟩, hunsat⟩, -, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', as', m', rfl, _, hpc, _, hspE, _⟩)
  · exact Or.inl ⟨hpc, hunsat, fun r hr => hcs r hr, hsp', m', k', hinv', hm'⟩
  · exact Or.inr ⟨hpc, hspE⟩

end Generic

/-! ## Concrete x64 executions in `compiled.host` -/

abbrev lratHost : Host := compiled.host
attribute [local instance] lratHost

def lratState0 : MachineData :=
  { regs := { rdi := 0x1000, rsp := 0x0ff8 },
    dmem := initMem (compiled.bound "br_check_proof") 0x1234 nvCheckBytes }

theorem checkProof_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = 0x1234 ∧ (CNF.empty : CNF Nat).Unsat) ∨
        st.pc = Labels.label "lrat_fail")
      ⟨lratState0, Labels.label "br_check_proof"⟩ := by
  have hnv_len : nvCheckBytes.length ≤ 8192 := by
    simp [nvCheckBytes, bytesN_length, KernelFields.toList]
  have hmem : lratState0.dmem =⋆ Eq (nvCheckBytes.At 0x1000#64) ⋆
      ((fun f => ∃ bs : List UInt8, bs.length = compiled.bound "br_check_proof" ∧
          f = bs.At (lratState0.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "br_check_proof"))) ⋆
        Eq ((0x1234 : Int64).toUInt64.At (lratState0.regs.get64 .rsp))) ⋆
      Std.ExtHashMap.emp :=
    initMem_entry (compiled.bound "br_check_proof") 0x1234 nvCheckBytes
      (compiled.bound_le_max "br_check_proof") hnv_len
  have hfail : target.Defined lratHost "lrat_fail" :=
    compiled.defined_exit_host (by simp)
  have h := checkProof_x64_correct 0 compiled.code_infix_host compiled.labelsUnique hfail
    nvCheck_pre lratState0 0x1234 Std.ExtHashMap.emp rfl (by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, hunsat, -⟩ | ⟨hpc, -⟩)
  · exact Or.inl ⟨hpc, hunsat⟩
  · exact Or.inr hpc

def lratAcceptState0 : MachineData :=
  { regs := { rdi := 0x1000, rsp := 0x0ff8 },
    dmem := initMem (compiled.bound "br_check_proof") 0x1234 nvAcceptBytes }

/-- Concrete accepting execution of compiled `br_check_proof` on Kraken x64. -/
theorem checkProof_x64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ nvAcceptCnf.Unsat)
      ⟨lratAcceptState0, Labels.label "br_check_proof"⟩ := by
  have hacc_len : nvAcceptBytes.length ≤ 8192 := by
    have := nvAcceptBytes_length; omega
  have hmem : target.mem lratAcceptState0 =⋆ Eq (nvAcceptBytes.At 0x1000#64) ⋆
      target.Entry (target.get lratAcceptState0 target.sp) (0x1234 : Int64)
        (compiled.bound "br_check_proof") ⋆
      Std.ExtHashMap.emp :=
    initMem_entry (compiled.bound "br_check_proof") 0x1234 nvAcceptBytes
      (compiled.bound_le_max "br_check_proof") hacc_len
  have hfail : target.Defined lratHost "lrat_fail" :=
    compiled.defined_exit_host (by simp)
  have hrdi : lratAcceptState0.regs.get64 .rdi = 0x1000#64 := rfl
  have hargs : target.ArgsIn [0x1000#64] lratAcceptState0 := by
    simp [Target.ArgsIn, Target.ValsIn, target, isa, hrdi]
  have hsp : (lratAcceptState0.regs.get64 .rsp + 8#64).toNat % 16 = 0 := by decide
  have hspec : lratAcceptEnv "br_check_proof" [0x1000#64] (nvAcceptBytes.At 0x1000#64)
      (fun rs m' => rs = [] ∧ nvAcceptMem nvAcceptK2 Std.ExtHashMap.emp m' ∧ nvAcceptCnf.Unsat)
      (fun _ _ _ => False) := by
    simpa [lratAcceptEnv] using checkProof_accepts_nonvacuous
  have hf := (lrat_module_accepts_fnspec 0 compiled.code_infix_host compiled.labelsUnique hfail
      (nm := "br_check_proof") (by decide)).2
    [0x1000#64] (nvAcceptBytes.At 0x1000#64) _ _ hspec
    lratAcceptState0 0x1234 Std.ExtHashMap.emp hargs trivial hsp hmem
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, _, _, ⟨_, _, hunsat⟩, -⟩ | ⟨_, _, _, hx, _⟩)
  · exact ⟨hpc, hunsat⟩
  · exact hx.elim

end LeanQbe.Amd64.LratTrim
