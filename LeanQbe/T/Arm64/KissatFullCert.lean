module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Arm64.KissatFullCert1
public import LeanQbe.T.Arm64.KissatFullCert2
public import LeanQbe.T.Arm64.KissatFullCert3
public import LeanQbe.T.Arm64.KissatFullCert4
public import LeanQbe.T.Arm64.KissatFullCert5
public import LeanQbe.T.Arm64.KissatFullCert6
public import LeanQbe.T.Arm64.KissatFullCert7
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Kissat `D-Full` Native Compilation Certificate on AAPCS64 Arm64

Combines the 7 parallel kernel-checked compilation slices (`KissatFullCert1`..`KissatFullCert7`)
via `LinkedCert.append` into `fullCert` over `LeanQbe.T.Examples.Kissat.Full.fullModule` (`166`
functions), and exports `full_legalSig`, generic `(Γ : Env)` `mk_module_fnspec`, and
`solve_arm64_of_fnspec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full Kraken
open LeanQbe.T.Arm64.KissatFullCert1 LeanQbe.T.Arm64.KissatFullCert2
open LeanQbe.T.Arm64.KissatFullCert3 LeanQbe.T.Arm64.KissatFullCert4
open LeanQbe.T.Arm64.KissatFullCert5 LeanQbe.T.Arm64.KissatFullCert6
open LeanQbe.T.Arm64.KissatFullCert7

/-- Prefix sub-module `[0, 67)`. -/
def pref2Mod : Module := { fns := fullFns.take 67 }

/-- Prefix sub-module `[0, 88)`. -/
def pref3Mod : Module := { fns := fullFns.take 88 }

/-- Prefix sub-module `[0, 111)`. -/
def pref4Mod : Module := { fns := fullFns.take 111 }

/-- Prefix sub-module `[0, 128)`. -/
def pref5Mod : Module := { fns := fullFns.take 128 }

/-- Prefix sub-module `[0, 147)`. -/
def pref6Mod : Module := { fns := fullFns.take 147 }

/-- Linked certificate for prefix `[0, 67)`. -/
noncomputable def cert12 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := fullFns) (i := 38) (j := 29))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 88)`. -/
noncomputable def cert123 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref3Mod [] [] 0 2048 :=
  cert12.append cert3 (by exact List.take_add (l := fullFns) (i := 67) (j := 21))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 111)`. -/
noncomputable def cert1234 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref4Mod [] [] 0 2048 :=
  cert123.append cert4 (by exact List.take_add (l := fullFns) (i := 88) (j := 23))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 128)`. -/
noncomputable def cert12345 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref5Mod [] [] 0 2048 :=
  cert1234.append cert5 (by exact List.take_add (l := fullFns) (i := 111) (j := 17))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 147)`. -/
noncomputable def cert123456 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref6Mod [] [] 0 2048 :=
  cert12345.append cert6 (by exact List.take_add (l := fullFns) (i := 128) (j := 19))
    (by t_kernel_rfl)

/-- Full kernel-checked native compilation certificate covering all `166` functions in
`fullModule` on AAPCS64 Arm64. -/
noncomputable def fullCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean fullModule [] [] 0 2048 :=
  cert123456.append cert7 (by exact (List.take_append_drop 147 fullFns).symm) (by t_kernel_rfl)

private theorem full_legalSig_check :
    checkLegalSigAll armLegalTarget fullFns = true := by
  t_kernel_rfl

/-- All `166` function signatures in `fullFns` satisfy `armLegalTarget.legalSig`. -/
theorem full_legalSig : LegalSigAll armLegalTarget fullFns :=
  legalSigAll_of_check full_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `fullModule` on `armTarget`, parameterized over a
sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ fullFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ fullFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : fullCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fullModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (fullCert.bound f.name) 0 :=
  fullCert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    full_acyclic fullFns_wf full_legalSig hsound hf (hnoex f hf)

/-- Lifting any `FnSpec` for `"kissat_solve_bytes"` at stack bound `b` and abstract contract
`spec` to a concrete Kraken-AArch64 `Eventually` statement via `arm64_of_returns`. -/
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
  have hargs : armTarget.ArgsIn (as := [i64, i64, i64, i64, i64])
      (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) s :=
    ⟨_, rfl,
      .cons ⟨by decide, by simpa [get_reg] using hx0⟩
        (.cons ⟨by decide, by simpa [get_reg] using hx1⟩
          (.cons ⟨by decide, by simpa [get_reg] using hx2⟩
            (.cons ⟨by decide, by simpa [get_reg] using hx3⟩
              (.cons ⟨by decide, by simpa [get_reg] using hx4⟩ .nil))))⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfnspec hspec s ra R hargs hra hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, m', hQ, hrets, hm'⟩
  rcases rets with ⟨r, ⟨⟩⟩
  have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton r st.data hrets
  rw [hx0']
  exact ⟨hpc, hcs, hsp', m', hQ, hm'⟩

end Generic

end LeanQbe.T.Arm64.KissatFullCert
