/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.KissatM4
public import LeanQbe.T.Examples.Kissat.FullSatSound
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM4 (`231` fns) Unconditional SysV x64 UNSAT + SAT Soundness & Model Extraction

Zero-recompilation additive layer over `LeanQbe.T.Amd64.KissatM4Cert.m4Cert` and
`KissatM4CertLink.mk_module_fnspec` (x86-64 only; never imports AArch64):

- `m4_sound_module_fnspec`: unconditional `Defined` + `FnSpec` under `m4SoundEnv` (`231/231`).
- `m4_solve_bytes_model_x64`: `Eventually (step1 Host.exe)` with `rax = 20 → cnf.Unsat` and
  `rax = 10 → cnf.Sat (readModelFromWork st.data.dmem work_ptr)` plus exact register/memory
  framing.
- `m4_solve_bytes_sound_x64`: existential SAT + UNSAT soundness with exact framing.
- `m4_solve_bytes_model_only_x64` / `m4_solve_bytes_sound_only_x64`: answer-only corollaries.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM4Sound

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM4 LeanQbe.T.Amd64.KissatM4CertLink Kraken

/-- Unconditional whole-module `Defined` + `FnSpec` for all `231` functions in `m4Module` under
`m4SoundEnv` (UNSAT + constructive SAT model soundness) on SysV x64. -/
theorem m4_sound_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM4_compiled_x64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m4Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (m4SoundEnv f.name f.as f.rs)
        (kissatM4_compiled_x64.bound f.name) 0 :=
  KissatM4CertLink.mk_module_fnspec m4SoundEnv
    (fun g hg args m Q X hs => by
      obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg
      exact (m4SoundEnv_moduleOk.fnsOk pre g post hsp).2.2 args m Q X hs)
    (fun g _ => m4SoundEnv_noExit g.name g.as g.rs) k₀ hc hu hf

private theorem solve_in_m4Module :
    m4SolveBytesFn ∈ m4Module.fns :=
  List.mem_of_getElem? (by t_kernel_rfl : (m4Module.fns)[230]? = some m4SolveBytesFn)

private theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}
    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by
  have hm := sep_mono (Q := Q)
    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h
  rw [sep_ex_l] at hm
  obtain ⟨m, hm'⟩ := hm
  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩

section Sound

variable [hh : Host] (k₀ : Nat)
  (hc : kissatM4_compiled_x64.code.IsInfixAt Host.prog k₀)
  (hu : Host.LabelsUnique)
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
  (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
    (region (s.regs.get64 .rsp - BitVec.ofNat 64
        (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
      (kissatM4_compiled_x64.bound "kissat_solve_bytes") ⋆
      cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem)
include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
  hrdi hrsi hrdx hrcx hr8 hsp hmem

/-- Unconditional end-to-end SysV x64 UNSAT + constructive SAT model soundness for `m4Module`:
`rax = 20` certifies `cnf.Unsat` and `rax = 10` certifies that `readModelFromWork st.data.dmem
work_ptr` satisfies `cnf`, with exact callee-saved register and memory framing. -/
theorem m4_solve_bytes_model_x64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (st.data.regs.get64 .rax = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            cnf.Sat (readModelFromWork st.data.dmem work_ptr)) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM4_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn := (m4_sound_module_fnspec k₀ hc hu solve_in_m4Module).2
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      ((region (s.regs.get64 .rsp - BitVec.ofNat 64
          (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM4_compiled_x64.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R)) s.dmem := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64
          (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM4_compiled_x64.bound "kissat_solve_bytes") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem := by
    rw [sep_assoc]; exact hm_dmem
  have hspec : m4SoundEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r.fst = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →
            cnf.Sat (readModelFromWork M work_ptr)) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    m4SoundEnv_solve_bytes_model
      (fullSolveBytesModelSpec_intro (R := emp) hcfit hwfit
        (by rw [sep_emp]; exact hm_in)
        (fun _ _ hdom hu hmod hm' => by rw [sep_emp] at hm'; exact ⟨hdom, hu, hmod, hm'⟩))
  refine eventually_weaken _ _ _ _ ?_
    (KissatM4CertLink.solve_x64_of_fnspec hfn cnf_ptr _ work_ptr _ fuel
      hspec s ra R hrdi hrsi hrdx hrcx hr8 hsp hm_dmem')
  rintro st ⟨hpc, hcal, hrsp, m', ⟨hdom, hu', hmod, hm'⟩, hst⟩
  have hst_frame : (Eq m' ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64
          (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
        (kissatM4_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)) st.data.dmem := by
    rw [← sep_assoc]; exact hst
  have hsat_st : st.data.regs.get64 .rax = 10#64 →
      ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        cnf.Sat (readModelFromWork st.data.dmem work_ptr) := by
    intro h10
    obtain ⟨cnf, hparse, hf⟩ := hmod h10
    exact ⟨cnf, hparse, hf _ st.data.dmem hst_frame⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hsat_st, hcal, hrsp, hst'⟩

/-- Unconditional end-to-end SysV x64 UNSAT + existential SAT soundness for `m4Module` with
exact register and memory framing. -/
theorem m4_solve_bytes_sound_x64 :
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
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatM4_compiled_x64.bound "kissat_solve_bytes"))
            (kissatM4_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', hmod, hcal, hrsp, hmem'⟩ =>
      ⟨hpc, hdom, hu', fun h10 =>
        let ⟨cnf, hp, hsat⟩ := hmod h10
        ⟨cnf, hp, cnf_not_unsat_of_sat hsat⟩, hcal, hrsp, hmem'⟩)
    (m4_solve_bytes_model_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)

/-- Answer-only SysV x64 UNSAT + constructive SAT model soundness corollary for `m4Module`. -/
theorem m4_solve_bytes_model_only_x64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (st.data.regs.get64 .rax = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            cnf.Sat (readModelFromWork st.data.dmem work_ptr)))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (m4_solve_bytes_model_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)

/-- Answer-only SysV x64 UNSAT + existential SAT soundness corollary for `m4Module`. -/
theorem m4_solve_bytes_sound_only_x64 :
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
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (m4_solve_bytes_sound_x64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)

end Sound

end LeanQbe.T.Amd64.KissatM4Sound
