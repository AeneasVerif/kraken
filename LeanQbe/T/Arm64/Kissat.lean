module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.Solver
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Solver

/-!
# Kissat `D-Min` C0 SAT Solver (`kissatFns`) on AArch64 (`X1` Stage B)

Instantiates the 25-function typed-IR Kissat SAT solver module `kissatModule`
(`dimacs_fns ++ solver_fns`) on `armTarget` (`armLegalTarget`, `armLayout`, `armLabelClean`) with:
* `kissatHints` via `splice_module_hints`;
* `compiled_check : checkCompile ... = true` proved in a single kernel reduction (`t_kernel_rfl`);
* `kissatFns_supportsSource` and `kissatFns_legalSig` over all 25 functions;
* `mk_kissat_module_fnspec` parameterized over arbitrary sound `Γ : Env` and `Host` instances;
* `kissat_solve_bytes_arm64_of_fnspec` lifting an abstract `"kissat_solve_bytes"` `FnSpec` to a
  closed Kraken-AArch64 `Eventually` theorem via `arm64_of_returns`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.Kissat

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Arm64 Kraken

splice_module_hints kissatHints (armTarget.toIsa) armLegalTarget kissatFns

theorem compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 kissatFns kissatHints 2048 =
      true := by
  t_kernel_rfl

/-- Single kernel evaluation of the compiler on `kissatFns` (25 functions) for AArch64. -/
def compiled : Compiled armTarget armLegalTarget [] [] 0 kissatFns kissatHints 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean [] [] 0
    kissatFns kissatHints 2048 compiled_check

private theorem kissatFns_supportsSource_all :
    kissatFns.all (fun f => (f.earlyOpt).body.supportsSource armLegalTarget) = true := by
  t_kernel_rfl

theorem kissatFns_supportsSource :
    ∀ f ∈ kissatModule.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true :=
  supportsAll_to_forall kissatFns_supportsSource_all

private theorem kissatFns_legalSig_all :
    kissatFns.all (fun f =>
      (armLegalTarget.legalSig f.as == f.as) &&
      (armLegalTarget.legalSig f.rs == f.rs)) = true := by
  t_kernel_rfl

theorem kissatFns_legalSig :
    ∀ f ∈ kissatFns,
      armLegalTarget.legalSig f.as = f.as ∧ armLegalTarget.legalSig f.rs = f.rs := by
  intro f hf
  have h := List.all_eq_true.mp kissatFns_legalSig_all f hf
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `kissatModule` on `armTarget`, parameterized
over a sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_kissat_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ kissatFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ kissatFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ kissatModule.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (Γ f.name f.as f.rs) (compiled.bound f.name) 0 :=
  have ⟨has, hrs⟩ := kissatFns_legalSig f hf
  compiled.fnSpec_noExit_id kissatModule rfl hh Γ k₀ hc hu
    kissatModule_checkAcyclic kissatFns_wf kissatFns_supportsSource hsound hf
    has hrs (hnoex f hf)

/-- Lifting any `FnSpec` for `"kissat_solve_bytes"` at stack bound `b` and abstract contract
`spec` to a concrete Kraken-AArch64 `Eventually` statement via `arm64_of_returns`. -/
theorem kissat_solve_bytes_arm64_of_fnspec {b : Nat}
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

#guard kissatFns.length == 25
#guard compiled.bound "kissat_solve_bytes" <= 2048
#guard kissatFns.all (fun f => compiled.bound f.name <= 2048)
#guard kissatFns.all (fun f =>
  letI := compiled.host
  Host.prog.any fun | .label l => l == f.name | _ => false)

#print axioms compiled_check
#print axioms compiled
#print axioms mk_kissat_module_fnspec
#print axioms kissat_solve_bytes_arm64_of_fnspec

end LeanQbe.T.Arm64.Kissat
