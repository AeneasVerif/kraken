/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Arm64.KissatM4
public import LeanQbe.T.Examples.Kissat.FullSatSound
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM4 (`231` fns) Unconditional AAPCS64 Arm64 UNSAT + SAT Soundness & Model Extraction

Zero-recompilation additive layer over `LeanQbe.T.Arm64.KissatM4Cert.m4Cert` and
`KissatM4CertLink.mk_module_fnspec` (AArch64 only; never imports x86-64):

- `m4_sound_module_fnspec`: unconditional `Defined` + `FnSpec` under `m4SoundEnv` (`231/231`).
- `m4_solve_bytes_model_arm64`: `Eventually (step1 Host.exe)` with `X0 = 20 → cnf.Unsat` and
  `X0 = 10 → cnf.Sat (readModelFromWork st.data.dmem work_ptr)` plus exact register/memory
  framing.
- `m4_solve_bytes_sound_arm64`: existential SAT + UNSAT soundness with exact framing.
- `m4_solve_bytes_model_only_arm64` / `m4_solve_bytes_sound_only_arm64`: answer-only corollaries.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM4Sound

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4 LeanQbe.T.Arm64.KissatM4CertLink Kraken

/-- Unconditional whole-module `Defined` + `FnSpec` for all `231` functions in `m4Module` under
`m4SoundEnv` (UNSAT + constructive SAT model soundness) on AAPCS64 Arm64. -/
theorem m4_sound_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM4_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m4Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (m4SoundEnv f.name f.as f.rs)
        (kissatM4_compiled_arm64.bound f.name) 0 :=
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
  (hc : kissatM4_compiled_arm64.code.IsInfixAt Host.prog k₀)
  (hu : Host.LabelsUnique)
  (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
  (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
  (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
  (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
  (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
  (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
  (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)
  (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)
  (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)
  (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
  (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
    region (s.regs.SP.toBitVec - BitVec.ofNat 64
        (kissatM4_compiled_arm64.bound "kissat_solve_bytes"))
      (kissatM4_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem)
include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
  hx0 hx1 hx2 hx3 hx4 hra hsp hmem

/-- Unconditional end-to-end AAPCS64 Arm64 UNSAT + constructive SAT model soundness for
`m4Module`: `X0 = 20` certifies `cnf.Unsat` and `X0 = 10` certifies that
`readModelFromWork st.data.dmem work_ptr` satisfies `cnf`, with exact register/memory framing. -/
theorem m4_solve_bytes_model_arm64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            cnf.Sat (readModelFromWork st.data.dmem work_ptr)) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
            .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatM4_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM4_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn := (m4_sound_module_fnspec k₀ hc hu solve_in_m4Module).2
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM4_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM4_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)) s.dmem := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM4_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM4_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem := by
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
    (KissatM4CertLink.solve_arm64_of_fnspec hfn cnf_ptr _ work_ptr _ fuel
      hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hm_dmem')
  rintro st ⟨hpc, hcal, hsp', m', ⟨hdom, hu', hmod, hm'⟩, hst⟩
  have hst_frame : (Eq m' ⋆
      (region (s.regs.SP.toBitVec - BitVec.ofNat 64
          (kissatM4_compiled_arm64.bound "kissat_solve_bytes"))
        (kissatM4_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)) st.data.dmem := by
    rw [← sep_assoc]; exact hst
  have hsat_st : (st.data.regs.getXReg .X0).toBitVec = 10#64 →
      ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        cnf.Sat (readModelFromWork st.data.dmem work_ptr) := by
    intro h10
    obtain ⟨cnf, hparse, hf⟩ := hmod h10
    exact ⟨cnf, hparse, hf _ st.data.dmem hst_frame⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hsat_st, hcal, hsp', hst'⟩

/-- Unconditional end-to-end AAPCS64 Arm64 UNSAT + existential SAT soundness for `m4Module` with
exact register and memory framing. -/
theorem m4_solve_bytes_sound_arm64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
            .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64
              (kissatM4_compiled_arm64.bound "kissat_solve_bytes"))
            (kissatM4_compiled_arm64.bound "kissat_solve_bytes") ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', hmod, hcal, hsp', hmem'⟩ =>
      ⟨hpc, hdom, hu', fun h10 =>
        let ⟨cnf, hp, hsat⟩ := hmod h10
        ⟨cnf, hp, cnf_not_unsat_of_sat hsat⟩, hcal, hsp', hmem'⟩)
    (m4_solve_bytes_model_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

/-- Answer-only AAPCS64 Arm64 UNSAT + constructive SAT model soundness corollary for `m4Module`. -/
theorem m4_solve_bytes_model_only_arm64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            cnf.Sat (readModelFromWork st.data.dmem work_ptr)))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (m4_solve_bytes_model_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

/-- Answer-only AAPCS64 Arm64 UNSAT + existential SAT soundness corollary for `m4Module`. -/
theorem m4_solve_bytes_sound_only_arm64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (m4_solve_bytes_sound_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

end Sound

end LeanQbe.T.Arm64.KissatM4Sound
