module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.SolverLemmas
import LeanQbe.T.Logic.MemLemmas
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Solver

/-!
# Kissat `D-Min` C0 SAT Solver (`kissatFns`) on SysV x64 (`X1` Stage B)

Instantiates the 25-function typed-IR Kissat SAT solver module `kissatModule`
(`dimacs_fns ++ solver_fns`) on `x64Target` (`x64LegalTarget`, `x64Layout`, `x64LabelClean`) with:
* `kissatCert` via chunked `compile_linked_chunks!` (eliminating monolithic kernel peak RSS);
* `kissatHints`, `compiled_check : checkCompile ... = true`, and literal-backed `compiled`
  derived directly from `kissatCert`;
* `kissatFns_supportsSource` and `kissatFns_legalSig` over all 25 functions;
* `mk_kissat_module_fnspec` and closed `kissat_module_fnspec` over arbitrary `Host` instances;
* closed Kraken-x64 `Eventually` theorems `kissat_solve_bytes_x64_of_fnspec`,
  `kissat_solve_bytes_x64_correct`, and `kissat_solve_bytes_x64_sound`;
* concrete non-vacuous UNSAT (`rax = 20` + `nvUnsatCnf.Unsat`) and SAT (`rax = 10` +
  `¬ nvSatCnf.Unsat ∧ ∃ α, nvSatCnf.Sat α`) execution witnesses on `compiled.host` via `x64Init`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.Kissat

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.LratBytes LeanQbe.T.Amd64 Kraken

open scoped LeanQbe.T in
compile_linked_chunks! kissatCert
  x64Target x64Layout x64LegalTarget x64LabelClean kissatModule 1

/-- Concatenated register-allocation hints across all chunks of `kissatCert`. -/
def kissatHints : List x64Target.toIsa.Hints :=
  chunksHints kissatCert.chunks

theorem compiled_compileModule :
    compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0
      kissatFns kissatHints = .ok (kissatCert.code, kissatCert.bounds) := by
  rw [show kissatFns = chunksFns kissatCert.chunks from kissatCert.fns_eq]
  exact kissatCert.compiled.compileModule_eq

private theorem lookupFnBound_of_mem_nodup :
    ∀ {bs : List (Sym × Nat)} {nm : Sym} {b : Nat},
      (bs.map Prod.fst).Nodup → (nm, b) ∈ bs → lookupFnBound bs nm = some b
  | [], _, _, _, h => nomatch h
  | (k, v) :: bs, nm, b, hnd, hmem => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [lookupFnBound, List.find?]
    rcases List.mem_cons.mp hmem with ⟨rfl, rfl⟩ | hmem'
    · simp
    · have hne : (k == nm) = false := beq_false_of_ne fun e =>
        hnd.1 (e ▸ List.mem_map_of_mem (f := Prod.fst) hmem')
      simp only [hne]
      exact lookupFnBound_of_mem_nodup hnd.2 hmem'

theorem compiled_checkLit :
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      kissatCert.code kissatCert.bounds (kissatFns.map Fn.name) [] 2048 = true := by
  have hlink := kissatCert.linkCheck
  simp only [checkLinkList, Bool.and_eq_true] at hlink
  have hfns : kissatFns = chunksFns kissatCert.chunks := kissatCert.fns_eq
  have hnd : (kissatCert.compiled.bounds.map Prod.fst).Nodup := by
    rw [compileModule_bounds_names kissatCert.compiled.compileModule_eq]
    exact (List.nodup_append.mp (checkLinkList_parts kissatCert.linkCheck).2.2.2.1).1
  simp only [checkCompileLit, checkCompileResult, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hfns]; exact hlink.1.1.1.2
  · rw [hfns]; exact hlink.1.2
  · exact hlink.2
  · refine List.all_eq_true.mpr fun p hp => Nat.ble_eq.mpr ?_
    have hlk := lookupFnBound_of_mem_nodup hnd hp
    have hle := kissatCert.bound_le_max p.1
    simpa [LinkedCert.bound, Compiled.bound, hlk] using hle
  · rw [hfns]
    refine List.all_eq_true.mpr fun nm hnm => ?_
    cases hlk : lookupFnBound kissatCert.bounds nm with
    | some _ => rfl
    | none =>
      simp only [lookupFnBound, Option.map_eq_none_iff, List.find?_eq_none] at hlk
      exact absurd (beq_self_eq_true nm) (hlk _ (kissatCert.compiled.bound_mem hnm))

theorem compiled_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 kissatFns kissatHints 2048 =
      true := by
  unfold checkCompile
  rw [compiled_compileModule]
  exact compiled_checkLit

/-- Chunk-linked literal-backed compilation certificate on `kissatFns` (25 functions) for
SysV x64. -/
def compiled : Compiled x64Target x64LegalTarget [] [] 0 kissatFns kissatHints 2048 :=
  compileCheckedLit x64Target x64Layout x64LegalTarget x64LabelClean [] [] 0
    kissatFns kissatHints 2048 kissatCert.code kissatCert.bounds
    compiled_compileModule compiled_checkLit

theorem kissatFns_supportsSource :
    ∀ f ∈ kissatModule.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  kissatCert.supportsAll

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

/-- Closed `FnSpec` for every function in `kissatModule` under `kissatEnv` on `x64Target`. -/
theorem kissat_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ kissatModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (kissatEnv f.name f.as f.rs) (compiled.bound f.name) 0 :=
  mk_kissat_module_fnspec kissatEnv kissatEnv_sound kissatEnv_noExit k₀ hc hu hf

private theorem mk_kissat_entry_fnspec
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hsound : ∀ f ∈ kissatFns, ∀ args m Q X,
      mkKissatEnv mainSpec f.name f.as f.rs args m Q X →
      Func.wp (mkKissatEnv mainSpec) f.body args m Q X)
    (hnoex : ∀ g ∈ kissatFns, ∀ args m Q X X',
      mkKissatEnv mainSpec g.name g.as g.rs args m Q X →
      mkKissatEnv mainSpec g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    x64Target.FnSpec hh "kissat_solve_bytes" mainSpec
      (compiled.bound "kissat_solve_bytes") 0 := by
  simpa [mkKissatEnv, kissat_solve_bytes] using
    (mk_kissat_module_fnspec (mkKissatEnv mainSpec) hsound hnoex k₀ hc hu
      (f := kissat_solve_bytes) (by simp [kissatModule, kissatFns, solver_fns])).2

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

/-- Closed end-to-end correctness of compiled `kissat_solve_bytes` on SysV x64: terminates
cleanly, preserves callee-saved registers and read-only DIMACS bytes, restores workspace
`region work_ptr wlen`, returns `rax ∈ {0, 10, 20}`, and certifies UNSAT (`20`) and SAT (`10`). -/
theorem kissat_solve_bytes_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "kissat_solve_bytes"))
          (compiled.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (st.data.regs.get64 .rax = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "kissat_solve_bytes"))
            (compiled.bound "kissat_solve_bytes" + 8) ⋆ R))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "kissat_solve_bytes"))
          (compiled.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn : x64Target.FnSpec hh "kissat_solve_bytes" kissatSolveBytesSpec
      (compiled.bound "kissat_solve_bytes") 0 :=
    mk_kissat_entry_fnspec kissatSolveBytesSpec kissatEnv_sound kissatEnv_noExit k₀ hc hu
  have hspec : kissatSolveBytesSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit, by rwa [sep_emp],
      fun _ _ hdom hu hs hm' => ⟨hdom, hu, hs, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (kissat_solve_bytes_x64_of_fnspec hfn cnf_ptr (BitVec.ofNat 64 cnfBytes.length)
      work_ptr (BitVec.ofNat 64 wlen) fuel hspec s ra R hrdi hrsi hrdx hrcx hr8 hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', m', ⟨hdom, hu, hs, hm'⟩, hmem'⟩
  exact ⟨hpc, hdom, hu, hs, hcs, hsp',
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem'⟩

/-- Trivial-postcondition end-to-end Kraken-x64 soundness corollary for `kissat_solve_bytes`. -/
theorem kissat_solve_bytes_x64_sound (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "kissat_solve_bytes"))
          (compiled.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (st.data.regs.get64 .rax = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hdom, hu, hs, _⟩ => ⟨hpc, hdom, hu, hs⟩)
    (kissat_solve_bytes_x64_correct k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)

end Generic

/-! ## Concrete SysV x64 Non-Vacuous Executions in `compiled.host` (`rax = 20` and `rax = 10`) -/

abbrev kissatHost : Host := compiled.host
attribute [local instance] kissatHost

def kissatArgs (cnfBytes : List UInt8) : Tup Val [i64, i64, i64, i64, i64] :=
  (kissatNvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
    kissatNvWorkPtr cnfBytes, 512#64, 16#64, ())

def kissatState (cnfBytes : List UInt8) : MachineData :=
  x64Init.initState (as := [i64, i64, i64, i64, i64])
    (compiled.bound "kissat_solve_bytes")
    (kissatPayload cnfBytes) (kissatArgs cnfBytes)

def kissatUnsatState0 : MachineData :=
  kissatState nvUnsatBytes

/-- Concrete UNSAT execution of compiled `kissat_solve_bytes` on Kraken x64 (`rax = 20`). -/
theorem kissat_x64_unsat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 20#64 ∧ nvUnsatCnf.Unsat)
      ⟨kissatUnsatState0, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : x64Target.FnSpec kissatHost "kissat_solve_bytes" kissatSolveBytesUnsatWitnessSpec
      (compiled.bound "kissat_solve_bytes") 0 :=
    mk_kissat_entry_fnspec kissatSolveBytesUnsatWitnessSpec kissatUnsatWitnessEnv_sound
      kissatUnsatWitnessEnv_noExit 0 compiled.code_infix_host compiled.labelsUnique
  have hspec : kissatSolveBytesUnsatWitnessSpec (kissatArgs nvUnsatBytes)
      ((kissatPayload nvUnsatBytes).At 0x1000#64)
      (fun rs _ => rs = (20#64, ()) ∧ nvUnsatCnf.Unsat) (fun _ _ _ _ => False) :=
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact kissatPayload_sep nvUnsatBytes (by decide),
      fun _ hu _ => ⟨rfl, hu⟩⟩
  refine x64Init.run_fnSpec compiled hfn (kissatPayload nvUnsatBytes) (kissatArgs nvUnsatBytes)
    (by simp [kissatPayload_length, nvUnsatBytes]) (by decide) hspec ?_
  rintro st (⟨hpc, _, _, ⟨rfl, hu⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, x64Init.retsIn_singleton 20#64 _ hrets, hu⟩
  · exact hx.elim

def kissatSatState0 : MachineData :=
  kissatState nvSatBytes

/-- Concrete SAT execution of compiled `kissat_solve_bytes` on Kraken x64 (`rax = 10`). -/
theorem kissat_x64_sat_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 10#64 ∧
        ¬ nvSatCnf.Unsat ∧ ∃ α, nvSatCnf.Sat α)
      ⟨kissatSatState0, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : x64Target.FnSpec kissatHost "kissat_solve_bytes" kissatSolveBytesSatWitnessSpec
      (compiled.bound "kissat_solve_bytes") 0 :=
    mk_kissat_entry_fnspec kissatSolveBytesSatWitnessSpec kissatSatWitnessEnv_sound
      kissatSatWitnessEnv_noExit 0 compiled.code_infix_host compiled.labelsUnique
  have hspec : kissatSolveBytesSatWitnessSpec (kissatArgs nvSatBytes)
      ((kissatPayload nvSatBytes).At 0x1000#64)
      (fun rs _ => rs = (10#64, ()) ∧ ¬ nvSatCnf.Unsat ∧ ∃ α, nvSatCnf.Sat α)
      (fun _ _ _ _ => False) :=
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact kissatPayload_sep nvSatBytes (by decide),
      fun _ hnu hsat _ => ⟨rfl, hnu, hsat⟩⟩
  refine x64Init.run_fnSpec compiled hfn (kissatPayload nvSatBytes) (kissatArgs nvSatBytes)
    (by simp [kissatPayload_length, nvSatBytes]) (by decide) hspec ?_
  rintro st (⟨hpc, _, _, ⟨rfl, hnu, hsat⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, x64Init.retsIn_singleton 10#64 _ hrets, hnu, hsat⟩
  · exact hx.elim

#guard kissatFns.length == 25

#print axioms compiled_check
#print axioms compiled
#print axioms mk_kissat_module_fnspec
#print axioms kissat_module_fnspec
#print axioms kissat_solve_bytes_x64_of_fnspec
#print axioms kissat_solve_bytes_x64_correct
#print axioms kissat_solve_bytes_x64_sound
#print axioms kissat_x64_unsat_nonvacuous
#print axioms kissat_x64_sat_nonvacuous

end LeanQbe.T.Amd64.Kissat
