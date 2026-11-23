module

public import LeanQbe.T.Amd64.KissatM7PlusCert
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM7Plus Legal-Sig & Host Linking Helpers on SysV x64

Exports `m7Plus_legalSig`, `mk_module_fnspec`, and `solve_x64_of_fnspec` over
`LeanQbe.T.Amd64.KissatM7PlusCert.m7PlusCert`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM7PlusCertLink

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM7PlusCert LeanQbe.T.Examples.Kissat.FullM7Plus
open Kraken

private theorem m7Plus_legalSig_check :
    checkLegalSigAll x64LegalTarget m7PlusFns = true := by
  t_kernel_rfl

/-- All `410` function signatures in `m7PlusFns` satisfy `x64LegalTarget.legalSig`. -/
theorem m7Plus_legalSig : LegalSigAll x64LegalTarget m7PlusFns :=
  legalSigAll_of_check m7Plus_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `m7PlusModule` compiled under
`m7InlPolicy` on `x64Target`, lifted from source `ModuleOk Γ m7PlusModule`.
-/
theorem mk_module_fnspec (Γ : Env)
    (hM : ModuleOk Γ m7PlusModule)
    (hnoex : ∀ g ∈ m7PlusFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : m7PlusCert.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m7PlusModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (Γ f.name f.as f.rs) (m7PlusCert.bound f.name) 0 :=
  m7PlusCert.fnSpec_noExit_of_legalSigAll_optInlinePolicy hh Γ k₀ hc hu
    hM m7Plus_legalSig hf (hnoex f hf)

/-- Lifting any `FnSpec` for `"kissat_solve_bytes"` at stack bound `b` and contract
`spec` to Kraken-x64 `Eventually` via `x64_of_returns`. -/
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
  have hargs : x64Target.ArgsIn (as := [i64, i64, i64, i64, i64])
      (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) s :=
    ⟨_, rfl,
      .cons ⟨by decide, by simpa using hrdi⟩
        (.cons ⟨by decide, by simpa using hrsi⟩
          (.cons ⟨by decide, by simpa using hrdx⟩
            (.cons ⟨by decide, by simpa using hrcx⟩
              (.cons ⟨by decide, by simpa using hr8⟩ .nil))))⟩
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns hfnspec hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, m', hQ, hrets, hm'⟩
  rcases rets with ⟨r, ⟨⟩⟩
  have hrax : st.data.regs.get64 .rax = r :=
    x64Init.retsIn_singleton r st.data hrets
  rw [hrax]
  exact ⟨hpc, hcs, hsp', m', hQ, hm'⟩

theorem ax_solve {b : Nat}
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
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  solve_x64_of_fnspec hfnspec cnf_ptr cnf_len work_ptr work_len fuel
    hspec s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem

end Generic

#print axioms m7Plus_legalSig
#print axioms mk_module_fnspec
#print axioms ax_solve

end LeanQbe.T.Amd64.KissatM7PlusCertLink
