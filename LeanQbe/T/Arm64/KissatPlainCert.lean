module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Arm64.KissatPlainCert1
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Arm64.KissatPlainCert1

/-!
# Kissat `D-Plain` C0 SAT Solver (`plainModule`) Compilation Certificate on AArch64 (`Stage 3`)

Compiles and links the 59-function typed-IR Kissat `D-Plain` module `plainModule`
(`dimacs_fns ++ plain1_fns ++ plain2_fns`) on `armTarget` (`armLegalTarget`, `armLayout`,
`armLabelClean`) by appending `KissatPlainCert1.plainPart1` (`plain1Module`) and `plainPart2`
(`plain2_fns`) via `LinkedCert.append`:
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
open LeanQbe.T.Arm64.KissatPlainCert1

/-- Tail module consisting of the 20 functions in `plain2_fns`. -/
def plain2Module : Module :=
  { fns := plain2_fns, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! plainPart2
  armTarget armLayout armLegalTarget armLabelClean plain2Module 4
  (ext := plainPart1.exportedExt) (maxDirs := 450)

/-- Full 59-function kernel-checked native AArch64 compilation certificate for `plainModule`. -/
def plainCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      plainModule [] [] 0 2048 :=
  plainPart1.append plainPart2 rfl (by t_kernel_rfl)

/-- Every function in `plainModule` has identity legalization on `armLegalTarget`. -/
theorem plain_legalSig : LegalSigAll armLegalTarget plainModule.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

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

#guard plain1Module.fns.length == 39
#guard plain2Module.fns.length == 20
#guard plainFns.length == 59

#print axioms plainCert
#print axioms plain_legalSig
#print axioms mk_module_fnspec
#print axioms solve_arm64_of_fnspec

end LeanQbe.T.Arm64.KissatPlainCert
