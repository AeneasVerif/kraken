module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.Solver
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Solver

/-!
# Kissat `D-Min` C0 SAT Solver (`kissatFns`) on SysV x64 (`X1` Stage B)

Instantiates the 25-function typed-IR Kissat SAT solver module `kissatModule`
(`dimacs_fns ++ solver_fns`) on `x64Target` (`x64LegalTarget`, `x64Layout`, `x64LabelClean`) with:
* `kissatHints` via `splice_module_hints`;
* `compiled_check : checkCompile ... = true` proved in a single kernel reduction (`t_kernel_rfl`);
* `kissatFns_supportsSource` and `kissatFns_legalSig` over all 25 functions;
* `mk_kissat_module_fnspec` parameterized over arbitrary sound `Γ : Env` and `Host` instances;
* `kissat_solve_bytes_x64_of_fnspec` lifting an abstract `"kissat_solve_bytes"` `FnSpec` to a
  closed Kraken-x64 `Eventually` theorem via `x64_of_returns`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.Kissat

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Amd64 Kraken

splice_module_hints kissatHints (x64Target.toIsa) x64LegalTarget kissatFns

theorem compiled_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 kissatFns kissatHints 2048 =
      true := by
  t_kernel_rfl

/-- Single kernel evaluation of the compiler on `kissatFns` (25 functions) for SysV x64. -/
def compiled : Compiled x64Target x64LegalTarget [] [] 0 kissatFns kissatHints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean [] [] 0
    kissatFns kissatHints 2048 compiled_check

private theorem kissatFns_supportsSource_all :
    kissatFns.all (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

theorem kissatFns_supportsSource :
    ∀ f ∈ kissatModule.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  supportsAll_to_forall kissatFns_supportsSource_all

private theorem kissatFns_legalSig_all :
    kissatFns.all (fun f =>
      (x64LegalTarget.legalSig f.as == f.as) &&
      (x64LegalTarget.legalSig f.rs == f.rs)) = true := by
  t_kernel_rfl

theorem kissatFns_legalSig :
    ∀ f ∈ kissatFns,
      x64LegalTarget.legalSig f.as = f.as ∧ x64LegalTarget.legalSig f.rs = f.rs := by
  intro f hf
  have h := List.all_eq_true.mp kissatFns_legalSig_all f hf
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

section Generic
variable [hh : Host]

/-- Generic `FnSpec` for every function in `kissatModule` on `x64Target`, parameterized
over a sound environment `Γ` whose contracts ignore exit continuations. -/
theorem mk_kissat_module_fnspec (Γ : Env)
    (hsound : ∀ f ∈ kissatFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ kissatFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ kissatModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (Γ f.name f.as f.rs) (compiled.bound f.name) 0 :=
  have ⟨has, hrs⟩ := kissatFns_legalSig f hf
  compiled.fnSpec_noExit_id kissatModule rfl hh Γ k₀ hc hu
    kissatModule_checkAcyclic kissatFns_wf kissatFns_supportsSource hsound hf
    has hrs (hnoex f hf)

/-- Lifting any `FnSpec` for `"kissat_solve_bytes"` at stack bound `b` and abstract contract
`spec` to a concrete Kraken-x64 `Eventually` statement via `x64_of_returns`. -/
theorem kissat_solve_bytes_x64_of_fnspec {b : Nat}
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

#guard kissatFns.length == 25
#guard compiled.bound "kissat_solve_bytes" <= 2048
#guard kissatFns.all (fun f => compiled.bound f.name <= 2048)
#guard kissatFns.all (fun f =>
  letI := compiled.host
  Host.prog.any fun | .label l => l == f.name | _ => false)

#print axioms compiled_check
#print axioms compiled
#print axioms mk_kissat_module_fnspec
#print axioms kissat_solve_bytes_x64_of_fnspec

end LeanQbe.T.Amd64.Kissat
