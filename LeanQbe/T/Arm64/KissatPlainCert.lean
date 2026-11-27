module

public import LeanQbe.T.Arm64.KissatAbi
public import LeanQbe.T.Examples.Kissat.KissatPlainCertCommon
public import LeanQbe.T.Arm64.KissatPlainCert1
public import LeanQbe.T.Arm64.KissatPlainCert2
public import LeanQbe.T.Arm64.KissatPlainCert3
public import LeanQbe.T.Arm64.KissatPlainCert4
public import LeanQbe.T.Arm64.KissatPlainCert5
public import LeanQbe.T.Arm64.KissatPlainCert6
meta import Lean
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat `D-Plain` (`plainModule`) Compilation Certificate on AAPCS64 Arm64
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatPlainCert

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.KissatPlainCertCommon
open LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Arm64.KissatPlainCert1 LeanQbe.T.Arm64.KissatPlainCert2
open LeanQbe.T.Arm64.KissatPlainCert3 LeanQbe.T.Arm64.KissatPlainCert4
open LeanQbe.T.Arm64.KissatPlainCert5 LeanQbe.T.Arm64.KissatPlainCert6

/-- Full 59-function kernel-checked native AArch64 compilation certificate for `plainModule`. -/
@[expose] noncomputable def plainCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      plainModule [] [] 0 2048 :=
  mkPlainCertTree rfl rfl rfl rfl rfl rfl cert1 cert2 cert3 cert4 cert5 cert6
    (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)

private theorem plain_legalSig_check :
    checkLegalSigAll armLegalTarget plainModule.fns = true := by t_kernel_rfl

/-- Every function in `plainModule` has identity legalization on `armLegalTarget`. -/
theorem plain_legalSig : LegalSigAll armLegalTarget plainModule.fns :=
  legalSigAll_of_check plain_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `plainModule` on `armTarget`. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ plainFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ plainFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (plainCert.bound f.name) 0 :=
  plain_mk_module_fnspec plainCert plain_legalSig hh Γ hsound hnoex k₀ hc hu hf

/-- Lifting any `FnSpec` for `"kissat_solve_bytes"` to Kraken-AArch64 `Eventually`. -/
theorem solve_arm64_of_fnspec {b : Nat}
    {spec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hfnspec : armTarget.FnSpec hh "kissat_solve_bytes" spec b 0)
    (cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64)
    {m : Mem 64} {Q : Post [i64]}
    (hspec : spec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q
      (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = cnf_len)
    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = work_len)
    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆ region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m', Q ((st.data.regs.getXReg .X0).toBitVec, ()) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, ⟨hcs, hsp'⟩, m', hQ, hm'⟩ =>
      ⟨hpc, hcs, hsp', m', hQ, hm'⟩)
    (solve_of_abi_fnspec arm64KissatAbi hh "kissat_solve_bytes" hfnspec
      cnf_ptr cnf_len work_ptr work_len fuel hspec s ra R
      ⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩ hmem)

end Generic

#guard plainFns.length == 59

end LeanQbe.T.Arm64.KissatPlainCert
