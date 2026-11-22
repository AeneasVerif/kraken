module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Amd64.KissatFastCert1
public import LeanQbe.T.Amd64.KissatFastCert2
public import LeanQbe.T.Amd64.KissatFastCert3
public import LeanQbe.T.Amd64.KissatFastCert4
public import LeanQbe.T.Amd64.KissatFastCert5
public import LeanQbe.T.Amd64.KissatFastCert6
public import LeanQbe.T.Amd64.KissatFastCert7
public import LeanQbe.T.Amd64.KissatFastCert8
public import LeanQbe.T.Amd64.KissatFastCert9
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Native Compilation Certificate on SysV x64

Reuses `KissatFullCert1.cert1` for prefix `[0, 36)` via `KissatFastCert1` and combines all 8
parallel kernel-checked slices (`KissatFastCert2`..`KissatFastCert9`) via `LinkedCert.append`
into `fastCert` over `LeanQbe.T.Examples.Kissat.FullFast.fastModule` (`196` functions),
exporting `fast_legalSig`, generic `(Γ : Env)` `mk_module_fnspec`, and `solve_x64_of_fnspec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFast Kraken
open LeanQbe.T.Amd64.KissatFastCert1 LeanQbe.T.Amd64.KissatFastCert2
open LeanQbe.T.Amd64.KissatFastCert3 LeanQbe.T.Amd64.KissatFastCert4
open LeanQbe.T.Amd64.KissatFastCert5 LeanQbe.T.Amd64.KissatFastCert6
open LeanQbe.T.Amd64.KissatFastCert7 LeanQbe.T.Amd64.KissatFastCert8
open LeanQbe.T.Amd64.KissatFastCert9

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
noncomputable def cert12 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := fastFns) (i := 36) (j := 20))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 78)`. -/
noncomputable def cert123 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref3Mod [] [] 0 2048 :=
  cert12.append cert3 (by exact List.take_add (l := fastFns) (i := 56) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 100)`. -/
noncomputable def cert1234 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref4Mod [] [] 0 2048 :=
  cert123.append cert4 (by exact List.take_add (l := fastFns) (i := 78) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 122)`. -/
noncomputable def cert12345 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref5Mod [] [] 0 2048 :=
  cert1234.append cert5 (by exact List.take_add (l := fastFns) (i := 100) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 144)`. -/
noncomputable def cert123456 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref6Mod [] [] 0 2048 :=
  cert12345.append cert6 (by exact List.take_add (l := fastFns) (i := 122) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 166)`. -/
noncomputable def cert1234567 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref7Mod [] [] 0 2048 :=
  cert123456.append cert7 (by exact List.take_add (l := fastFns) (i := 144) (j := 22))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 184)`. -/
noncomputable def cert12345678 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref8Mod [] [] 0 2048 :=
  cert1234567.append cert8 (by exact List.take_add (l := fastFns) (i := 166) (j := 18))
    (by t_kernel_rfl)

/-- Full kernel-checked native compilation certificate covering all `196` functions in
`fastModule` on SysV x64. -/
noncomputable def fastCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean fastModule [] [] 0 2048 :=
  cert12345678.append cert9 (by exact (List.take_append_drop 184 fastFns).symm)
    (by t_kernel_rfl)

private theorem fast_legalSig_check :
    checkLegalSigAll x64LegalTarget fastFns = true := by
  t_kernel_rfl

/-- All `196` function signatures in `fastFns` satisfy `x64LegalTarget.legalSig`. -/
theorem fast_legalSig : LegalSigAll x64LegalTarget fastFns :=
  legalSigAll_of_check fast_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `fastModule` on `x64Target`, parameterized over a
sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ fastFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ fastFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : fastCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ fastModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (Γ f.name f.as f.rs) (fastCert.bound f.name) 0 :=
  fastCert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    fast_acyclic fastFns_wf fast_legalSig hsound hf (hnoex f hf)

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

end LeanQbe.T.Amd64.KissatFastCert
