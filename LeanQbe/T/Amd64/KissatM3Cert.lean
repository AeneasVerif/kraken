module

public import LeanQbe.T.Amd64.KissatM3Cert1
public import LeanQbe.T.Amd64.KissatM3Cert2
public import LeanQbe.T.Amd64.KissatM3Cert3
public import LeanQbe.T.Amd64.KissatM3Cert4
public import LeanQbe.T.Amd64.KissatM3Cert5
public import LeanQbe.T.Amd64.KissatM3Cert6
public import LeanQbe.T.Amd64.KissatM3Cert7
public import LeanQbe.T.Amd64.KissatM3Cert8
public import LeanQbe.T.Amd64.KissatM3Cert9
public import LeanQbe.T.Amd64.KissatM3Cert10
public import LeanQbe.T.Amd64.KissatM3Cert11
public import LeanQbe.T.Amd64.KissatM3Cert12
public import LeanQbe.T.Amd64.KissatM3Cert13
public import LeanQbe.T.Amd64.KissatM3Cert14
public import LeanQbe.T.Amd64.KissatM3Cert15
public import LeanQbe.T.Amd64.KissatM3Cert16
public import LeanQbe.T.Amd64.KissatM3Cert17
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Native Compilation Certificate on SysV x64

Reuses `KissatFastCert1` + `KissatFastCert2` (`45` / `44` unchanged functions) via `KissatM3Cert1`
and combines all 16 parallel kernel-checked slices (`KissatM3Cert2`..`KissatM3Cert17`) via
`LinkedCert.append` into `m3Cert` over `LeanQbe.T.Examples.Kissat.FullM3.m3Module` (`204`
functions), exporting `m3_legalSig`, generic `(Γ : Env)` `mk_module_fnspec`, and
`solve_x64_of_fnspec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3 Kraken
open LeanQbe.T.Amd64.KissatM3Cert1 LeanQbe.T.Amd64.KissatM3Cert2
open LeanQbe.T.Amd64.KissatM3Cert3 LeanQbe.T.Amd64.KissatM3Cert4
open LeanQbe.T.Amd64.KissatM3Cert5 LeanQbe.T.Amd64.KissatM3Cert6
open LeanQbe.T.Amd64.KissatM3Cert7 LeanQbe.T.Amd64.KissatM3Cert8
open LeanQbe.T.Amd64.KissatM3Cert9 LeanQbe.T.Amd64.KissatM3Cert10
open LeanQbe.T.Amd64.KissatM3Cert11 LeanQbe.T.Amd64.KissatM3Cert12
open LeanQbe.T.Amd64.KissatM3Cert13 LeanQbe.T.Amd64.KissatM3Cert14
open LeanQbe.T.Amd64.KissatM3Cert15 LeanQbe.T.Amd64.KissatM3Cert16
open LeanQbe.T.Amd64.KissatM3Cert17

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

/-- Linked certificate for prefix `[0, 59)`. -/
def pref2Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := m3Fns) (i := 47) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 68)`. -/
def pref3Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref3Mod [] [] 0 2048 :=
  pref2Cert.append cert3 (by exact List.take_add (l := m3Fns) (i := 59) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 80)`. -/
def pref4Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref4Mod [] [] 0 2048 :=
  pref3Cert.append cert4 (by exact List.take_add (l := m3Fns) (i := 68) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 91)`. -/
def pref5Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref5Mod [] [] 0 2048 :=
  pref4Cert.append cert5 (by exact List.take_add (l := m3Fns) (i := 80) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 103)`. -/
def pref6Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref6Mod [] [] 0 2048 :=
  pref5Cert.append cert6 (by exact List.take_add (l := m3Fns) (i := 91) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 111)`. -/
def pref7Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref7Mod [] [] 0 2048 :=
  pref6Cert.append cert7 (by exact List.take_add (l := m3Fns) (i := 103) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 119)`. -/
def pref8Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref8Mod [] [] 0 2048 :=
  pref7Cert.append cert8 (by exact List.take_add (l := m3Fns) (i := 111) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 129)`. -/
def pref9Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref9Mod [] [] 0 2048 :=
  pref8Cert.append cert9 (by exact List.take_add (l := m3Fns) (i := 119) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 140)`. -/
def pref10Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref10Mod [] [] 0 2048 :=
  pref9Cert.append cert10 (by exact List.take_add (l := m3Fns) (i := 129) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 152)`. -/
def pref11Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref11Mod [] [] 0 2048 :=
  pref10Cert.append cert11 (by exact List.take_add (l := m3Fns) (i := 140) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 158)`. -/
def pref12Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref12Mod [] [] 0 2048 :=
  pref11Cert.append cert12 (by exact List.take_add (l := m3Fns) (i := 152) (j := 6))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 167)`. -/
def pref13Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref13Mod [] [] 0 2048 :=
  pref12Cert.append cert13 (by exact List.take_add (l := m3Fns) (i := 158) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 175)`. -/
def pref14Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref14Mod [] [] 0 2048 :=
  pref13Cert.append cert14 (by exact List.take_add (l := m3Fns) (i := 167) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 183)`. -/
def pref15Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref15Mod [] [] 0 2048 :=
  pref14Cert.append cert15 (by exact List.take_add (l := m3Fns) (i := 175) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 195)`. -/
def pref16Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref16Mod [] [] 0 2048 :=
  pref15Cert.append cert16 (by exact List.take_add (l := m3Fns) (i := 183) (j := 12))
    (by t_kernel_rfl)

/-- Full kernel-checked native compilation certificate covering all `204` functions in
`m3Module` on SysV x64. -/
def m3Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean m3Module [] [] 0 2048 :=
  pref16Cert.append cert17 (by exact (List.take_append_drop 195 m3Fns).symm)
    (by t_kernel_rfl)

private theorem m3_legalSig_check :
    checkLegalSigAll x64LegalTarget m3Fns = true := by
  t_kernel_rfl

/-- All `204` function signatures in `m3Fns` satisfy `x64LegalTarget.legalSig`. -/
theorem m3_legalSig : LegalSigAll x64LegalTarget m3Fns :=
  legalSigAll_of_check m3_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `m3Module` on `x64Target`, parameterized over a
sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ m3Fns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ m3Fns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : m3Cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m3Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (Γ f.name f.as f.rs) (m3Cert.bound f.name) 0 :=
  m3Cert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    m3_acyclic m3Fns_wf m3_legalSig hsound hf (hnoex f hf)

/-- Lifting any `FnSpec` for `"kissat_solve_bytes"` at stack bound `b` and abstract contract
`spec` to a concrete Kraken-x64 `Eventually` statement via `x64_of_returns`. -/
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
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfnspec hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', rets, m', hQ, hrets, hm'⟩
  rcases rets with ⟨r, ⟨⟩⟩
  have hrax : st.data.regs.get64 .rax = r := x64Init.retsIn_singleton r st.data hrets
  rw [hrax]
  exact ⟨hpc, hcs, hsp', m', hQ, hm'⟩

end Generic

end LeanQbe.T.Amd64.KissatM3Cert
