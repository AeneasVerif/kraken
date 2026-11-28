module

import LeanQbe.T.MainCertProof
import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.BenchmarkCertKit
import LeanQbeTest.T.Common.Fixtures
import LeanQbe.T.FlatLemmas
meta import Lean
import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbeTest.T.Common.Fixtures

/-!
# Chunked Native Compilation Certificate Test on SysV x64 (`MainCert`)

Tests `LeanQbe.T.MainCert` (`LinkedCert` + `compile_linked_chunks!`) end-to-end on `x64Target`
(`x64LegalTarget`, `x64Layout`, `x64LabelClean`, `x64Init`):
1. Compiles a 6-function callee-first module (`certMod`) across 3 chunks (`K = 2`) and 2 chunks
   (`K = 4`), exercising cross-chunk calls (chunk 2 → chunk 1 and chunk 2 → chunk 0), intra-chunk
   calls, and memory-mutating (`cell64`) + pure functions.
2. Tests optional clauses (`maxBound := 1024`, `exits := ["bail"]`, `nX := 32`), non-empty
   `ext := ...`, and empty-module compilation.
3. Proves whole-module arbitrary-`Host` `FnSpec` via `cert.fnSpec_noExit_of_legalSigAll`,
   linked-host `FnSpec` via `cert.fnSpec_host_of_legalSigAll` (`linkCompiledList_fnSpec`),
   concrete Kraken x64 `Eventually (step1 Host.exe)` via `x64_of_returns`, and closed execution
   witnesses via `cert.eventually_ret1_sep_i64` (`rax = 75`, `cell64 0x1000 21`).
4. Audits single-line `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.MainCertTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbeTest.T.Common.Fixtures

theorem certMod_legalSig : LegalSigAll x64LegalTarget certMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-! ## 2. Chunked native certificates via `compile_linked_chunks!` -/

compile_linked_chunks! x64Cert3
  x64Target x64Layout x64LegalTarget x64LabelClean certMod 2

compile_linked_chunks! x64Cert2
  x64Target x64Layout x64LegalTarget x64LabelClean certMod 4

compile_linked_chunks! x64ExitCert
  x64Target x64Layout x64LegalTarget x64LabelClean exitMod 1
  (maxBound := 1024) (exits := ["bail"]) (nX := 32)

compile_linked_chunks! x64EmptyCert
  x64Target x64Layout x64LegalTarget x64LabelClean emptyMod 4

compile_linked_chunks! x64ExtCert
  x64Target x64Layout x64LegalTarget x64LabelClean extSubMod 1
  (ext := extCalleesSample)

compile_linked_chunks! x64AdaptiveCert
  x64Target x64Layout x64LegalTarget x64LabelClean certMod 6 (maxDirs := 20)

compile_linked_chunks! x64Part1
  x64Target x64Layout x64LegalTarget x64LabelClean part1Mod 2
  (compileExt := true)

compile_linked_chunks! x64Part2
  x64Target x64Layout x64LegalTarget x64LabelClean part2Mod 2
  (ext := x64Part1.exportedExt)

noncomputable def x64AppendedCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean certMod [] [] 0
      (Nat.max 2048 2048) :=
  x64Part1.append x64Part2 rfl (by t_kernel_rfl)

theorem x64Cert3_chunks : x64Cert3.numChunks = 3 := rfl
theorem x64Cert2_chunks : x64Cert2.numChunks = 2 := rfl
theorem x64ExitCert_chunks : x64ExitCert.numChunks = 2 := rfl
theorem x64EmptyCert_chunks : x64EmptyCert.numChunks = 1 := rfl
theorem x64ExtCert_chunks : x64ExtCert.numChunks = 2 := rfl
theorem x64Appended_chunks : x64AppendedCert.numChunks = 4 := rfl
theorem x64Adaptive_ge : 2 ≤ x64AdaptiveCert.numChunks := by decide

theorem x64Cert3_bound_le : x64Cert3.bound "main_entry" ≤ 2048 :=
  x64Cert3.bound_le_max "main_entry"

theorem x64Cert3_bound_fn_idx :
    x64Cert3.bound (certMod.fns[5]).name =
      (x64Cert3.bounds[5]'(by rw [x64Cert3.bounds_length]; decide)).2 :=
  x64Cert3.bound_at_fn_idx (by decide) (by decide)

theorem x64Cert3_bound_at_idx :
    x64Cert3.bound (x64Cert3.bounds[5]).1 = (x64Cert3.bounds[5]).2 :=
  x64Cert3.bound_at_idx (by decide) (by decide)

/-! ## 3. Whole-module `FnSpec` & concrete Kraken x64 `Eventually` theorems -/

/-- Arbitrary-`Host` whole-module `FnSpec` via `LinkedCert.fnSpec_noExit_of_legalSigAll`. -/
theorem x64_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : x64Cert3.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ certMod.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (certΓ f.name f.as f.rs) (x64Cert3.bound f.name) 0 :=
  x64Cert3.fnSpec_noExit_of_legalSigAll hh certΓ k₀ hc hu
    certMod_acyclic certMod_wf certMod_legalSig certMod_wp hf (certΓ_noExit f.name f.as f.rs)

/-- Linked-host `FnSpec` for `main_entry` via `linkCompiledList_fnSpec`. -/
theorem x64_main_fnSpec :
    x64Target.Defined x64Cert3.host "main_entry" ∧
      x64Target.FnSpec x64Cert3.host "main_entry" mainSpec
        (x64Cert3.bound "main_entry") 0 :=
  x64Cert3.fnSpec_host_of_legalSigAll certΓ certMod_acyclic certMod_wf certMod_legalSig
    certMod_wp (f := fnMain) fnMain_mem_certMod (certΓ_noExit "main_entry" [i64, i64] [i64])

/-- Indexed linked-host `FnSpec` for `main_entry` (index 5) via `fnSpec_host_sig_idx`. -/
theorem x64_main_fnSpec_idx :
    x64Target.Defined x64Cert3.host (certMod.fns[5]).name ∧
      x64Target.FnSpec x64Cert3.host (certMod.fns[5]).name
        (certΓ (certMod.fns[5]).name (certMod.fns[5]).as (certMod.fns[5]).rs)
        (x64Cert3.bound (certMod.fns[5]).name) 0 :=
  x64Cert3.fnSpec_host_sig_idx certΓ certMod_acyclic certMod_wf
    certMod_legalSig certMod_wp (by decide)
    (certΓ_noExit (certMod.fns[5]).name (certMod.fns[5]).as (certMod.fns[5]).rs)

/-- Arbitrary-`Host` concrete Kraken x64 `Eventually (step1 Host.exe)` theorem for `main_entry`. -/
theorem x64_main_eventually [hh : Host] (k₀ : Nat)
    (hc : x64Cert3.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p v d : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = p) (hrsi : s.regs.get64 .rsi = d)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64Cert3.bound "main_entry"))
          (x64Cert3.bound "main_entry") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        st.data.regs.get64 .rax = mainVal v d ∧
        (st.data.dmem =⋆ cell64 p (pairMem v d) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64Cert3.bound "main_entry"))
            (x64Cert3.bound "main_entry" + 8) ⋆ R))
      ⟨s, Labels.label "main_entry"⟩ := by
  obtain ⟨m, hm, hmEq⟩ := BenchmarkCertKit.sep_extract_eq hmem
  have hfn : x64Target.FnSpec hh "main_entry" mainSpec (x64Cert3.bound "main_entry") 0 :=
    (x64_module_fnspec k₀ hc hu (f := fnMain) fnMain_mem_certMod).2
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (p, d, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, show s.regs.get64 .rdi = BitVec.setWidth 64 p from hrdi⟩
      (.cons ⟨by decide, show s.regs.get64 .rsi = BitVec.setWidth 64 d from hrsi⟩ .nil)⟩
  have hspec : mainSpec (p, d, ()) m
      (fun (r, ()) m' => r = mainVal v d ∧ cell64 p (pairMem v d) m') (fun _ _ _ _ => False) :=
    ⟨v, emp, by rwa [sep_emp], fun _ hm' => ⟨rfl, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfn hspec s ra R hargs hsp hmEq)
  rintro st ⟨hpc, _, _, ⟨r, ⟨⟩⟩, m', ⟨rfl, hm'⟩, hrets, hmem'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (mainVal v d) st.data hrets,
    sep_mono (fun _ => sep_mono (fun _ e => by cases e; exact hm')) hmem'⟩

def initMemBytes : List UInt8 := bytes64 [10#64]

private theorem initMemBytes_len : initMemBytes.length ≤ 8192 := by decide

private theorem initMemBytes_cell : (cell64 0x1000#64 10#64 ⋆ emp) (initMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [10#64] (by decide)
  exact h

/-- Concrete end-to-end x64 execution witness on `x64Cert3.host` via `eventually_ret1_sep_i64`
(`main_entry(0x1000, 5) = 75`, updating `cell64 0x1000 21`). -/
theorem x64_run_main_sep :
    Eventually (x64Target.mach.step x64Cert3.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 75#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64Cert3.bound "main_entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64Cert3.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr x64Cert3.host "main_entry")) := by
  refine x64Cert3.eventually_ret1_sep_i64 x64Init certΓ certMod_acyclic certMod_wf certMod_wp
    (f := fnMain) fnMain_mem_certMod rfl rfl rfl (certΓ_noExit "main_entry" [i64, i64] [i64])
    initMemBytes (0x1000#64, 5#64, ()) 75#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  show (cell64 0x1000#64 21#64 ⋆ emp) m'
  have : pairMem 10#64 5#64 = 21#64 := rfl
  rw [← this]
  exact hm'

/-- Concrete execution witness on `x64Cert3.host` via indexed `eventually_ret1_sep_idx`. -/
theorem x64_run_main_sep_idx :
    Eventually (x64Target.mach.step x64Cert3.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 75#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64Cert3.bound "main_entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64Cert3.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr x64Cert3.host "main_entry")) := by
  refine x64Cert3.eventually_ret1_sep_idx x64Init certΓ certMod_acyclic certMod_wf
    certMod_wp (i := 5) (by decide) rfl rfl rfl (certΓ_noExit "main_entry" [i64, i64] [i64])
    initMemBytes (0x1000#64, 5#64, ()) 75#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  show (cell64 0x1000#64 21#64 ⋆ emp) m'
  have : pairMem 10#64 5#64 = 21#64 := rfl
  rw [← this]
  exact hm'

/-- Concrete 2-chunk (`K = 4`) x64 execution witness on `x64Cert2.host`. -/
theorem x64_cert2_run_sep :
    Eventually (x64Target.mach.step x64Cert2.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 75#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64Cert2.bound "main_entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64Cert2.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr x64Cert2.host "main_entry")) := by
  refine x64Cert2.eventually_ret1_sep_i64 x64Init certΓ certMod_acyclic certMod_wf certMod_wp
    (f := fnMain) fnMain_mem_certMod rfl rfl rfl (certΓ_noExit "main_entry" [i64, i64] [i64])
    initMemBytes (0x1000#64, 5#64, ()) 75#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  show (cell64 0x1000#64 21#64 ⋆ emp) m'
  have : pairMem 10#64 5#64 = 21#64 := rfl
  rw [← this]
  exact hm'

/-- Concrete appended-cert (`LinkedCert.append`) x64 execution witness on `x64AppendedCert.host`. -/
theorem x64_appended_run_sep :
    Eventually (x64Target.mach.step x64AppendedCert.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 75#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64AppendedCert.bound "main_entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64AppendedCert.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr x64AppendedCert.host "main_entry")) := by
  refine x64AppendedCert.eventually_ret1_sep_i64 x64Init certΓ certMod_acyclic
    certMod_wf certMod_wp (f := fnMain) fnMain_mem_certMod rfl
    rfl rfl (certΓ_noExit "main_entry" [i64, i64] [i64]) initMemBytes (0x1000#64, 5#64, ())
    75#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  show (cell64 0x1000#64 21#64 ⋆ emp) m'
  have : pairMem 10#64 5#64 = 21#64 := rfl
  rw [← this]
  exact hm'

/-! ## 4. Axiom Audit -/

#print axioms LeanQbe.T.LinkedCert.bound_at_fn_idx
#print axioms LeanQbe.T.LinkedCert.bound_at_idx
#print axioms LeanQbe.T.LinkedCert.fnSpec
#print axioms LeanQbe.T.LinkedCert.fnSpec_linked
#print axioms LeanQbe.T.LinkedCert.fnSpec_host
#print axioms LeanQbe.T.LinkedCert.fnSpec_host_src
#print axioms LeanQbe.T.LinkedCert.fnSpec_host_src_at_idx
#print axioms LeanQbe.T.LinkedCert.fnSpec_host_sig_idx
#print axioms LeanQbe.T.LinkedCert.fnSpec_noExit_id
#print axioms LeanQbe.T.LinkedCert.fnSpec_noExit_sig_idx
#print axioms LeanQbe.T.LinkedCert.eventually_fnSpec
#print axioms LeanQbe.T.LinkedCert.eventually_fnSpec_at_idx
#print axioms LeanQbe.T.LinkedCert.eventually_ret1_sep_i64
#print axioms LeanQbe.T.LinkedCert.eventually_ret1_sep_idx
#print axioms LeanQbe.T.LinkedCert.eventually_ret1_sep_sig_idx
#print axioms LeanQbe.T.LinkedCert.eventually_ret1_i64
#print axioms LeanQbe.T.LinkedCert.eventually_ret1_idx
#print axioms LeanQbe.T.LinkedCert.append
#print axioms x64Cert3
#print axioms x64Cert2
#print axioms x64ExitCert
#print axioms x64EmptyCert
#print axioms x64ExtCert
#print axioms x64AdaptiveCert
#print axioms x64AppendedCert
#print axioms x64_module_fnspec
#print axioms x64_main_fnSpec
#print axioms x64_main_fnSpec_idx
#print axioms x64_main_eventually
#print axioms x64_run_main_sep
#print axioms x64_run_main_sep_idx
#print axioms x64_cert2_run_sep
#print axioms x64_appended_run_sep

end LeanQbeTest.T.MainCertTest
