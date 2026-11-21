module

public import LeanQbe.T.Arm64.KissatFullCert1
public import LeanQbe.T.Arm64.KissatFastSchedCert2
public import LeanQbe.T.Arm64.KissatFastSchedCert3
public import LeanQbe.T.Arm64.KissatFastSchedCert4
public import LeanQbe.T.Arm64.KissatFastSchedCert5
public import LeanQbe.T.Arm64.KissatFastSchedCert6
public import LeanQbe.T.Arm64.KissatFastSchedCert7
public import LeanQbe.T.Examples.Kissat.FullFastSched
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Native Compilation Certificate on AAPCS64 Arm64

Reuses `KissatFullCert1.cert1` for the unchanged prefix `[0, 38)` and combines the 6 parallel
kernel-checked compilation slices (`KissatFastSchedCert2`..`KissatFastSchedCert7`) via
`LinkedCert.append` into `schedCert` over `LeanQbe.T.Examples.Kissat.FullFastSched.schedModule`
(`173` functions), exporting `sched_legalSig`, generic `(Γ : Env)` `mk_module_fnspec`, and
`solve_arm64_of_fnspec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastSchedCert

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFastSched Kraken
open LeanQbe.T.Arm64.KissatFullCert1
open LeanQbe.T.Arm64.KissatFastSchedCert2 LeanQbe.T.Arm64.KissatFastSchedCert3
open LeanQbe.T.Arm64.KissatFastSchedCert4 LeanQbe.T.Arm64.KissatFastSchedCert5
open LeanQbe.T.Arm64.KissatFastSchedCert6 LeanQbe.T.Arm64.KissatFastSchedCert7

private theorem take38_eq :
    schedSplicedFns.take 38 = LeanQbe.T.Examples.Kissat.Full.fullFns.take 38 := by
  have h57 : (LeanQbe.T.Examples.Kissat.Full.fullFns.take 57).length = 57 := by t_kernel_rfl
  change (LeanQbe.T.Examples.Kissat.Full.fullFns.take 57 ++ _).take 38 =
    LeanQbe.T.Examples.Kissat.Full.fullFns.take 38
  rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_eq_left (by omega)]

/-- Prefix sub-module `[0, 61)`. -/
def pref2Mod : Module := { fns := schedSplicedFns.take 61 }

/-- Prefix sub-module `[0, 84)`. -/
def pref3Mod : Module := { fns := schedSplicedFns.take 84 }

/-- Prefix sub-module `[0, 107)`. -/
def pref4Mod : Module := { fns := schedSplicedFns.take 107 }

/-- Prefix sub-module `[0, 130)`. -/
def pref5Mod : Module := { fns := schedSplicedFns.take 130 }

/-- Prefix sub-module `[0, 152)`. -/
def pref6Mod : Module := { fns := schedSplicedFns.take 152 }

/-- Linked certificate for prefix `[0, 61)` reusing `KissatFullCert1.cert1`. -/
def cert12 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by
    change schedSplicedFns.take 61 =
      LeanQbe.T.Examples.Kissat.Full.fullFns.take 38 ++ (schedSplicedFns.drop 38).take 23
    rw [← take38_eq]
    exact List.take_add (l := schedSplicedFns) (i := 38) (j := 23))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 84)`. -/
def cert123 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref3Mod [] [] 0 2048 :=
  cert12.append cert3 (by exact List.take_add (l := schedSplicedFns) (i := 61) (j := 23))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 107)`. -/
def cert1234 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref4Mod [] [] 0 2048 :=
  cert123.append cert4 (by exact List.take_add (l := schedSplicedFns) (i := 84) (j := 23))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 130)`. -/
def cert12345 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref5Mod [] [] 0 2048 :=
  cert1234.append cert5 (by exact List.take_add (l := schedSplicedFns) (i := 107) (j := 23))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 152)`. -/
def cert123456 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref6Mod [] [] 0 2048 :=
  cert12345.append cert6 (by exact List.take_add (l := schedSplicedFns) (i := 130) (j := 22))
    (by t_kernel_rfl)

/-- Full kernel-checked native compilation certificate covering all `173` functions in
`schedModule` on AAPCS64 Arm64. -/
def schedCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean schedModule [] [] 0 2048 :=
  cert123456.append cert7 (by exact (List.take_append_drop 152 schedSplicedFns).symm)
    (by t_kernel_rfl)

private theorem sched_legalSig_check :
    checkLegalSigAll armLegalTarget schedSplicedFns = true := by
  t_kernel_rfl

/-- All `173` function signatures in `schedSplicedFns` satisfy `armLegalTarget.legalSig`. -/
theorem sched_legalSig : LegalSigAll armLegalTarget schedSplicedFns :=
  legalSigAll_of_check sched_legalSig_check

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `schedModule` on `armTarget`, parameterized over a
sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ schedSplicedFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ schedSplicedFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : schedCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ schedModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (schedCert.bound f.name) 0 :=
  schedCert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    sched_acyclic schedSplicedFns_wf sched_legalSig hsound hf (hnoex f hf)

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

end LeanQbe.T.Arm64.KissatFastSchedCert
