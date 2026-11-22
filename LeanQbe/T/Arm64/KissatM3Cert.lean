module

public import LeanQbe.T.Arm64.KissatM3Cert1a
public import LeanQbe.T.Arm64.KissatM3Cert1b
public import LeanQbe.T.Arm64.KissatM3Cert1c
public import LeanQbe.T.Arm64.KissatM3Cert2a
public import LeanQbe.T.Arm64.KissatM3Cert2b
public import LeanQbe.T.Arm64.KissatM3Cert3
public import LeanQbe.T.Arm64.KissatM3Cert4
public import LeanQbe.T.Arm64.KissatM3Cert5
public import LeanQbe.T.Arm64.KissatM3Cert6
public import LeanQbe.T.Arm64.KissatM3Cert7
public import LeanQbe.T.Arm64.KissatM3Cert8
public import LeanQbe.T.Arm64.KissatM3Cert9
public import LeanQbe.T.Arm64.KissatM3Cert10
public import LeanQbe.T.Arm64.KissatM3Cert11
public import LeanQbe.T.Arm64.KissatM3Cert12
public import LeanQbe.T.Arm64.KissatM3Cert13
public import LeanQbe.T.Arm64.KissatM3Cert14
public import LeanQbe.T.Arm64.KissatM3Cert15
public import LeanQbe.T.Arm64.KissatM3Cert16
public import LeanQbe.T.Arm64.KissatM3Cert17a
public import LeanQbe.T.Arm64.KissatM3Cert17b
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Native Compilation Certificate on AAPCS64 Arm64

Combines all 21 parallel kernel-checked slices (`KissatM3Cert1a`..`1c`, `2a`..`2b`,
`KissatM3Cert3`..`KissatM3Cert16`, `17a`..`17b`) via `LinkedCert.append` into `m3Cert` over
`LeanQbe.T.Examples.Kissat.FullM3.m3Module` (`204` functions), exporting `m3_legalSig`,
generic `(Γ : Env)` `mk_module_fnspec`, and `solve_arm64_of_fnspec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3 Kraken
open LeanQbe.T.Arm64.KissatM3Cert1a LeanQbe.T.Arm64.KissatM3Cert1b
open LeanQbe.T.Arm64.KissatM3Cert1c LeanQbe.T.Arm64.KissatM3Cert2a
open LeanQbe.T.Arm64.KissatM3Cert2b
open LeanQbe.T.Arm64.KissatM3Cert3 LeanQbe.T.Arm64.KissatM3Cert4
open LeanQbe.T.Arm64.KissatM3Cert5 LeanQbe.T.Arm64.KissatM3Cert6
open LeanQbe.T.Arm64.KissatM3Cert7 LeanQbe.T.Arm64.KissatM3Cert8
open LeanQbe.T.Arm64.KissatM3Cert9 LeanQbe.T.Arm64.KissatM3Cert10
open LeanQbe.T.Arm64.KissatM3Cert11 LeanQbe.T.Arm64.KissatM3Cert12
open LeanQbe.T.Arm64.KissatM3Cert13 LeanQbe.T.Arm64.KissatM3Cert14
open LeanQbe.T.Arm64.KissatM3Cert15 LeanQbe.T.Arm64.KissatM3Cert16
open LeanQbe.T.Arm64.KissatM3Cert17a LeanQbe.T.Arm64.KissatM3Cert17b

/-- Prefix sub-module `[0, 32)`. -/
def pref1bMod : Module := { fns := m3Fns.take 32 }

/-- Prefix sub-module `[0, 47)`. -/
def pref1cMod : Module := { fns := m3Fns.take 47 }

/-- Prefix sub-module `[0, 48)`. -/
def pref2aMod : Module := { fns := m3Fns.take 48 }

/-- Prefix sub-module `[0, 59)`. -/
def pref2Mod : Module := { fns := m3Fns.take 59 }

/-- Prefix sub-module `[0, 68)`. -/
def pref3Mod : Module := { fns := m3Fns.take 68 }

/-- Prefix sub-module `[0, 80)`. -/
def pref4Mod : Module := { fns := m3Fns.take 80 }

/-- Prefix sub-module `[0, 91)`. -/
def pref5Mod : Module := { fns := m3Fns.take 91 }

/-- Prefix sub-module `[0, 103)`. -/
def pref6Mod : Module := { fns := m3Fns.take 103 }

/-- Prefix sub-module `[0, 111)`. -/
def pref7Mod : Module := { fns := m3Fns.take 111 }

/-- Prefix sub-module `[0, 119)`. -/
def pref8Mod : Module := { fns := m3Fns.take 119 }

/-- Prefix sub-module `[0, 129)`. -/
def pref9Mod : Module := { fns := m3Fns.take 129 }

/-- Prefix sub-module `[0, 140)`. -/
def pref10Mod : Module := { fns := m3Fns.take 140 }

/-- Prefix sub-module `[0, 152)`. -/
def pref11Mod : Module := { fns := m3Fns.take 152 }

/-- Prefix sub-module `[0, 158)`. -/
def pref12Mod : Module := { fns := m3Fns.take 158 }

/-- Prefix sub-module `[0, 167)`. -/
def pref13Mod : Module := { fns := m3Fns.take 167 }

/-- Prefix sub-module `[0, 175)`. -/
def pref14Mod : Module := { fns := m3Fns.take 175 }

/-- Prefix sub-module `[0, 183)`. -/
def pref15Mod : Module := { fns := m3Fns.take 183 }

/-- Prefix sub-module `[0, 195)`. -/
def pref16Mod : Module := { fns := m3Fns.take 195 }

/-- Prefix sub-module `[0, 199)`. -/
def pref17aMod : Module := { fns := m3Fns.take 199 }

/-- Linked certificate for prefix `[0, 32)`. -/
def pref1bCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref1bMod [] [] 0 2048 :=
  cert1a.append cert1b (by exact List.take_add (l := m3Fns) (i := 16) (j := 16))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 47)`. -/
def pref1cCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref1cMod [] [] 0 2048 :=
  pref1bCert.append cert1c (by exact List.take_add (l := m3Fns) (i := 32) (j := 15))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 48)`. -/
def pref2aCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref2aMod [] [] 0 2048 :=
  pref1cCert.append cert2a (by exact List.take_add (l := m3Fns) (i := 47) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 59)`. -/
def pref2Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref2Mod [] [] 0 2048 :=
  pref2aCert.append cert2b (by exact List.take_add (l := m3Fns) (i := 48) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 68)`. -/
def pref3Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref3Mod [] [] 0 2048 :=
  pref2Cert.append cert3 (by exact List.take_add (l := m3Fns) (i := 59) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 80)`. -/
def pref4Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref4Mod [] [] 0 2048 :=
  pref3Cert.append cert4 (by exact List.take_add (l := m3Fns) (i := 68) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 91)`. -/
def pref5Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref5Mod [] [] 0 2048 :=
  pref4Cert.append cert5 (by exact List.take_add (l := m3Fns) (i := 80) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 103)`. -/
def pref6Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref6Mod [] [] 0 2048 :=
  pref5Cert.append cert6 (by exact List.take_add (l := m3Fns) (i := 91) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 111)`. -/
def pref7Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref7Mod [] [] 0 2048 :=
  pref6Cert.append cert7 (by exact List.take_add (l := m3Fns) (i := 103) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 119)`. -/
def pref8Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref8Mod [] [] 0 2048 :=
  pref7Cert.append cert8 (by exact List.take_add (l := m3Fns) (i := 111) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 129)`. -/
def pref9Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref9Mod [] [] 0 2048 :=
  pref8Cert.append cert9 (by exact List.take_add (l := m3Fns) (i := 119) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 140)`. -/
def pref10Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref10Mod [] [] 0 2048 :=
  pref9Cert.append cert10 (by exact List.take_add (l := m3Fns) (i := 129) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 152)`. -/
def pref11Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref11Mod [] [] 0 2048 :=
  pref10Cert.append cert11 (by exact List.take_add (l := m3Fns) (i := 140) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 158)`. -/
def pref12Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref12Mod [] [] 0 2048 :=
  pref11Cert.append cert12 (by exact List.take_add (l := m3Fns) (i := 152) (j := 6))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 167)`. -/
def pref13Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref13Mod [] [] 0 2048 :=
  pref12Cert.append cert13 (by exact List.take_add (l := m3Fns) (i := 158) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 175)`. -/
def pref14Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref14Mod [] [] 0 2048 :=
  pref13Cert.append cert14 (by exact List.take_add (l := m3Fns) (i := 167) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 183)`. -/
def pref15Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref15Mod [] [] 0 2048 :=
  pref14Cert.append cert15 (by exact List.take_add (l := m3Fns) (i := 175) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 195)`. -/
def pref16Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref16Mod [] [] 0 2048 :=
  pref15Cert.append cert16 (by exact List.take_add (l := m3Fns) (i := 183) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 199)`. -/
def pref17aCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref17aMod [] [] 0 2048 :=
  pref16Cert.append cert17a (by exact List.take_add (l := m3Fns) (i := 195) (j := 4))
    (by t_kernel_rfl)

/-- Full kernel-checked native compilation certificate covering all `204` functions in
`m3Module` on AAPCS64 Arm64. -/
def m3Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean m3Module [] [] 0 2048 :=
  pref17aCert.append cert17b (by exact (List.take_append_drop 199 m3Fns).symm)
    (by t_kernel_rfl)

private theorem m3_legalSig_check :
    checkLegalSigAll armLegalTarget m3Fns = true := by
  t_kernel_rfl

/-- All `204` function signatures in `m3Fns` satisfy `armLegalTarget.legalSig`. -/
theorem m3_legalSig : LegalSigAll armLegalTarget m3Fns :=
  legalSigAll_of_check m3_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `m3Module` on `armTarget`, parameterized over a
sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ m3Fns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ m3Fns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : m3Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m3Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (m3Cert.bound f.name) 0 :=
  m3Cert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    m3_acyclic m3Fns_wf m3_legalSig hsound hf (hnoex f hf)

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
  rintro st ⟨hpc, hcal, hsp', rets, m', hQ, hrets, hm'⟩
  rcases rets with ⟨r, ⟨⟩⟩
  have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton r st.data hrets
  rw [hx0']
  exact ⟨hpc, hcal, hsp', m', hQ, hm'⟩

end Generic

end LeanQbe.T.Arm64.KissatM3Cert
