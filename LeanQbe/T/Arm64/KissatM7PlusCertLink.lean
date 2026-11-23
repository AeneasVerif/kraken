module

public import LeanQbe.T.Arm64.KissatM7PlusCert
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM7Plus Legal-Sig & Host Linking Helpers on AAPCS64 Arm64

Exports `m7Plus_legalSig`, `mk_module_fnspec`, and `solve_arm64_of_fnspec` over
`LeanQbe.T.Arm64.KissatM7PlusCert.m7PlusCert`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM7PlusCertLink

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM7PlusCert LeanQbe.T.Examples.Kissat.FullM7Plus
open Kraken

private theorem m7Plus_legalSig_check :
    checkLegalSigAll armLegalTarget m7PlusFns = true := by
  t_kernel_rfl

/-- All `410` function signatures in `m7PlusFns` satisfy `armLegalTarget.legalSig`. -/
theorem m7Plus_legalSig : LegalSigAll armLegalTarget m7PlusFns :=
  legalSigAll_of_check m7Plus_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `m7PlusModule` compiled under
`m7InlPolicy` on `armTarget`, lifted from source `ModuleOk Γ m7PlusModule`.
-/
theorem mk_module_fnspec (Γ : Env)
    (hM : ModuleOk Γ m7PlusModule)
    (hnoex : ∀ g ∈ m7PlusFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : m7PlusCert.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m7PlusModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (m7PlusCert.bound f.name) 0 :=
  m7PlusCert.fnSpec_noExit_of_legalSigAll_optInlinePolicy hh Γ k₀ hc hu
    hM m7Plus_legalSig hf (hnoex f hf)

/-- Lifting any `FnSpec` for `"kissat_solve_bytes"` at stack bound `b` and contract
`spec` to Kraken-AArch64 `Eventually` via `arm64_of_returns`. -/
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
    (hmem : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
            .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m', Q ((st.data.regs.getXReg .X0).toBitVec, ()) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hargs : armTarget.ArgsIn (as := [i64, i64, i64, i64, i64])
      (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) s :=
    ⟨_, rfl,
      .cons ⟨by decide, by dsimp only [get_reg]; exact hx0⟩
        (.cons ⟨by decide, by dsimp only [get_reg]; exact hx1⟩
          (.cons ⟨by decide, by dsimp only [get_reg]; exact hx2⟩
            (.cons ⟨by decide, by dsimp only [get_reg]; exact hx3⟩
              (.cons ⟨by decide, by dsimp only [get_reg]; exact hx4⟩ .nil))))⟩
  refine eventually_weaken _ _ _ _ ?_
    (arm64_of_returns hfnspec hspec s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcal, hsp', rets, m', hQ, hrets, hm'⟩
  rcases rets with ⟨r, ⟨⟩⟩
  have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by
    exact armInit.retsIn_singleton r st.data hrets
  rw [hx0']
  exact ⟨hpc, hcal, hsp', m', hQ, hm'⟩

theorem ax_solve {b : Nat}
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
    (hmem : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
            .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ m', Q ((st.data.regs.getXReg .X0).toBitVec, ()) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  solve_arm64_of_fnspec hfnspec cnf_ptr cnf_len work_ptr work_len fuel
    hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem

end Generic

#print axioms m7Plus_legalSig
#print axioms mk_module_fnspec
#print axioms ax_solve

end LeanQbe.T.Arm64.KissatM7PlusCertLink
