module

public import LeanQbe.T.Amd64.KissatAbi
public import LeanQbe.T.Examples.Kissat.KissatPlainCertCommon
public import LeanQbe.T.Amd64.KissatPlainCert1
public import LeanQbe.T.Amd64.KissatPlainCert2
public import LeanQbe.T.Amd64.KissatPlainCert3
public import LeanQbe.T.Amd64.KissatPlainCert4
public import LeanQbe.T.Amd64.KissatPlainCert5
public import LeanQbe.T.Amd64.KissatPlainCert6
meta import Lean
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat `D-Plain` Compilation Certificate on SysV x64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatPlainCert

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.KissatPlainCertCommon
open LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Amd64.KissatPlainCert1 LeanQbe.T.Amd64.KissatPlainCert2
open LeanQbe.T.Amd64.KissatPlainCert3 LeanQbe.T.Amd64.KissatPlainCert4
open LeanQbe.T.Amd64.KissatPlainCert5 LeanQbe.T.Amd64.KissatPlainCert6

/-- Full 59-function kernel-checked native x64 compilation certificate for `plainModule`. -/
@[expose] noncomputable def plainCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      plainModule [] [] 0 2048 :=
  mkPlainCertTree rfl rfl rfl rfl rfl rfl cert1 cert2 cert3 cert4 cert5 cert6
    (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)

private theorem plain_legalSig_check :
    checkLegalSigAll x64LegalTarget plainModule.fns = true := by t_kernel_rfl

/-- Every function in `plainModule` has identity legalization on `x64LegalTarget`. -/
theorem plain_legalSig : LegalSigAll x64LegalTarget plainModule.fns :=
  legalSigAll_of_check plain_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `plainModule` on `x64Target`. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ plainFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ plainFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (Γ f.name f.as f.rs) (plainCert.bound f.name) 0 :=
  plain_mk_module_fnspec plainCert plain_legalSig hh Γ hsound hnoex k₀ hc hu hf

/-- Lifting any `FnSpec` for `"kissat_solve_bytes"` to Kraken-x64 `Eventually`. -/
theorem solve_x64_of_fnspec {b : Nat}
    {spec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hfnspec : x64Target.FnSpec hh "kissat_solve_bytes" spec b 0)
    (cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64)
    {m : Mem 64} {Q : Post [i64]}
    (hspec : spec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q
      (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = cnf_len)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = work_len)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ m', Q (st.data.regs.get64 .rax, ()) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, ⟨hcs, hsp'⟩, m', hQ, hm'⟩ =>
      ⟨hpc, hcs, hsp', m', hQ, hm'⟩)
    (solve_of_abi_fnspec x64KissatAbi hh "kissat_solve_bytes" hfnspec
      cnf_ptr cnf_len work_ptr work_len fuel hspec s ra R ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

end Generic

#guard plainFns.length == 59

end LeanQbe.T.Amd64.KissatPlainCert
