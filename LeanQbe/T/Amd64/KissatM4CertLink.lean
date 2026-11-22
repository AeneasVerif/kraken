module

public import LeanQbe.T.Amd64.KissatM4Cert
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM4 Legal-Sig & Host Linking Helpers on SysV x64

Exports `m4_legalSig`, `mk_module_fnspec`, and `solve_x64_of_fnspec` over
`LeanQbe.T.Amd64.KissatM4Cert.m4Cert`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM4CertLink

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM4Cert LeanQbe.T.Examples.Kissat.FullM4 Kraken

private theorem m4_legalSig_check :
    checkLegalSigAll x64LegalTarget m4Fns = true := by
  t_kernel_rfl

/-- All `231` function signatures in `m4Fns` satisfy `x64LegalTarget.legalSig`. -/
theorem m4_legalSig : LegalSigAll x64LegalTarget m4Fns :=
  legalSigAll_of_check m4_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `m4Module` on `x64Target`, parameterized over a
sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ m4Fns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ m4Fns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : m4Cert.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m4Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (Γ f.name f.as f.rs) (m4Cert.bound f.name) 0 :=
  m4Cert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    m4_acyclic m4Fns_wf m4_legalSig hsound hf (hnoex f hf)

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

end Generic

#print axioms m4_legalSig
#print axioms mk_module_fnspec
#print axioms solve_x64_of_fnspec

end LeanQbe.T.Amd64.KissatM4CertLink
