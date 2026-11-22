module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Arm64.KissatPlainCert1
public import LeanQbe.T.Arm64.KissatPlainCert2
public import LeanQbe.T.Arm64.KissatPlainCert3
public import LeanQbe.T.Arm64.KissatPlainCert4
public import LeanQbe.T.Arm64.KissatPlainCert5
public import LeanQbe.T.Arm64.KissatPlainCert6
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat `D-Plain` (`plainModule`) Compilation Certificate on AAPCS64 Arm64 (`Stage 3`)

Combines the 6 parallel kernel-checked slices (`KissatPlainCert1`..`KissatPlainCert6`) via
`LinkedCert.append` into `plainCert` over `LeanQbe.T.Examples.Kissat.Plain.plainModule` (`59`
functions) on `armTarget` (`armLegalTarget`, `armLayout`, `armLabelClean`):
* `plainCert : LinkedCert armTarget ... plainModule [] [] 0 2048`;
* `plain_legalSig : LegalSigAll armLegalTarget plainModule.fns`;
* `mk_module_fnspec`: generic `(Γ : Env)` `Defined` + `FnSpec` over arbitrary `Host`;
* `solve_arm64_of_fnspec`: lifts `"kissat_solve_bytes"` `FnSpec` to Kraken AArch64 `Eventually`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatPlainCert

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Arm64.KissatPlainCert1 LeanQbe.T.Arm64.KissatPlainCert2
open LeanQbe.T.Arm64.KissatPlainCert3 LeanQbe.T.Arm64.KissatPlainCert4
open LeanQbe.T.Arm64.KissatPlainCert5 LeanQbe.T.Arm64.KissatPlainCert6

/-- Prefix sub-module `[0, 29)`. -/
def pref2Mod : Module := { fns := plainFns.take 29 }

/-- Prefix sub-module `[0, 40)`. -/
def pref3Mod : Module := { fns := plainFns.take 40 }

/-- Prefix sub-module `[0, 47)`. -/
def pref4Mod : Module := { fns := plainFns.take 47 }

/-- Prefix sub-module `[0, 52)`. -/
def pref5Mod : Module := { fns := plainFns.take 52 }

/-- Linked certificate for prefix `[0, 29)`. -/
noncomputable def pref2Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := plainFns) (i := 15) (j := 14))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 40)`. -/
noncomputable def pref3Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref3Mod [] [] 0 2048 :=
  pref2Cert.append cert3 (by exact List.take_add (l := plainFns) (i := 29) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 47)`. -/
noncomputable def pref4Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref4Mod [] [] 0 2048 :=
  pref3Cert.append cert4 (by exact List.take_add (l := plainFns) (i := 40) (j := 7))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 52)`. -/
noncomputable def pref5Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref5Mod [] [] 0 2048 :=
  pref4Cert.append cert5 (by exact List.take_add (l := plainFns) (i := 47) (j := 5))
    (by t_kernel_rfl)

/-- Full 59-function kernel-checked native AArch64 compilation certificate for `plainModule`. -/
noncomputable def plainCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      plainModule [] [] 0 2048 :=
  pref5Cert.append cert6 (by exact (List.take_append_drop 52 plainFns).symm)
    (by t_kernel_rfl)

private theorem plain_legalSig_check :
    checkLegalSigAll armLegalTarget plainModule.fns = true := by
  t_kernel_rfl

/-- Every function in `plainModule` has identity legalization on `armLegalTarget`. -/
theorem plain_legalSig : LegalSigAll armLegalTarget plainModule.fns :=
  legalSigAll_of_check plain_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `plainModule` on `armTarget`, parameterized
over a sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ plainFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ plainFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : plainCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (plainCert.bound f.name) 0 :=
  plainCert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    plain_acyclic plainFns_wf plain_legalSig hsound hf (hnoex f hf)

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

#guard plainFns.length == 59

#print axioms plainCert
#print axioms plain_legalSig
#print axioms mk_module_fnspec
#print axioms solve_arm64_of_fnspec

end LeanQbe.T.Arm64.KissatPlainCert
