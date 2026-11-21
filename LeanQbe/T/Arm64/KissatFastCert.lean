module

public import LeanQbe.T.Arm64.KissatFastCert1
public import LeanQbe.T.Arm64.KissatFastCert2
public import LeanQbe.T.Arm64.KissatFastCert3
public import LeanQbe.T.Arm64.KissatFastCert4
public import LeanQbe.T.Arm64.KissatFastCert5
public import LeanQbe.T.Arm64.KissatFastCert6
public import LeanQbe.T.Arm64.KissatFastCert7
public import LeanQbe.T.Arm64.KissatFastCert8
public import LeanQbe.T.Arm64.KissatFastCert9
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Native Compilation Certificate on AAPCS64 Arm64

Reuses `KissatFullCert1.cert1` for prefix `[0, 36)` via `KissatFastCert1` and combines all 8
parallel kernel-checked slices (`KissatFastCert2`..`KissatFastCert9`) via `LinkedCert.append`
into `fastCert` over `LeanQbe.T.Examples.Kissat.FullFast.fastModule` (`196` functions),
exporting `fast_legalSig`, generic `(Γ : Env)` `mk_module_fnspec`, and `solve_arm64_of_fnspec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast Kraken
open LeanQbe.T.Arm64.KissatFastCert1 LeanQbe.T.Arm64.KissatFastCert2
open LeanQbe.T.Arm64.KissatFastCert3 LeanQbe.T.Arm64.KissatFastCert4
open LeanQbe.T.Arm64.KissatFastCert5 LeanQbe.T.Arm64.KissatFastCert6
open LeanQbe.T.Arm64.KissatFastCert7 LeanQbe.T.Arm64.KissatFastCert8
open LeanQbe.T.Arm64.KissatFastCert9

/-- Prefix sub-module `[0, 56)`. -/
def pref2Mod : Module := { fns := fastFns.take 56 }

/-- Prefix sub-module `[0, 78)`. -/
def pref3Mod : Module := { fns := fastFns.take 78 }

/-- Prefix sub-module `[0, 100)`. -/
def pref4Mod : Module := { fns := fastFns.take 100 }

/-- Prefix sub-module `[0, 122)`. -/
def pref5Mod : Module := { fns := fastFns.take 122 }

/-- Prefix sub-module `[0, 144)`. -/
def pref6Mod : Module := { fns := fastFns.take 144 }

/-- Prefix sub-module `[0, 166)`. -/
def pref7Mod : Module := { fns := fastFns.take 166 }

/-- Prefix sub-module `[0, 184)`. -/
def pref8Mod : Module := { fns := fastFns.take 184 }

/-- Linked certificate for prefix `[0, 56)`. -/
def cert12 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := fastFns) (i := 36) (j := 20))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 78)`. -/
def cert123 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref3Mod [] [] 0 2048 :=
  cert12.append cert3 (by exact List.take_add (l := fastFns) (i := 56) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 100)`. -/
def cert1234 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref4Mod [] [] 0 2048 :=
  cert123.append cert4 (by exact List.take_add (l := fastFns) (i := 78) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 122)`. -/
def cert12345 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref5Mod [] [] 0 2048 :=
  cert1234.append cert5 (by exact List.take_add (l := fastFns) (i := 100) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 144)`. -/
def cert123456 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref6Mod [] [] 0 2048 :=
  cert12345.append cert6 (by exact List.take_add (l := fastFns) (i := 122) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 166)`. -/
def cert1234567 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref7Mod [] [] 0 2048 :=
  cert123456.append cert7 (by exact List.take_add (l := fastFns) (i := 144) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 184)`. -/
def cert12345678 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref8Mod [] [] 0 2048 :=
  cert1234567.append cert8 (by exact List.take_add (l := fastFns) (i := 166) (j := 18))
    (by t_kernel_rfl)

/-- Full kernel-checked native compilation certificate covering all `196` functions in
`fastModule` on AAPCS64 Arm64. -/
def fastCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean fastModule [] [] 0 2048 :=
  cert12345678.append cert9 (by exact (List.take_append_drop 184 fastFns).symm)
    (by t_kernel_rfl)

private theorem fast_legalSig_check :
    checkLegalSigAll armLegalTarget fastFns = true := by
  t_kernel_rfl

/-- All `196` function signatures in `fastFns` satisfy `armLegalTarget.legalSig`. -/
theorem fast_legalSig : LegalSigAll armLegalTarget fastFns :=
  legalSigAll_of_check fast_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `fastModule` on `armTarget`, parameterized over a
sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ fastFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ fastFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : fastCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fastModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (fastCert.bound f.name) 0 :=
  fastCert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    fast_acyclic fastFns_wf fast_legalSig hsound hf (hnoex f hf)

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

end LeanQbe.T.Arm64.KissatFastCert
