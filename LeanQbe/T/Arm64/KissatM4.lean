module

public import LeanQbe.T.Arm64.KissatM4Cert
public import LeanQbe.T.Arm64.KissatM4CertLink
public import LeanQbe.T.Examples.Kissat.FullM4Proof
import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.Logic.MemLemmas
import Std.Sat.CNF.Basic
import Kraken.Mem
import Kraken.Separation

/-!
# KissatM4 (`231` fns) Unconditional AAPCS64 Arm64 Theorems

Combines `KissatM4Cert.m4Cert` and `KissatM4CertLink` with solver proof contracts.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullM4 LeanQbe.T.Arm64 LeanQbe.T.Arm64.KissatM4CertLink Kraken
open LeanQbe.T.Examples.Kissat.Full

/-- Compiled `LinkedCert` for `m4Module` (`231` functions) on AAPCS64 Arm64. -/
@[reducible] noncomputable def kissatM4_compiled_arm64 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean m4Module :=
  KissatM4Cert.m4Cert

/-- Unconditional whole-module `Defined` + `FnSpec` for all `231` functions in `m4Module` under
`m4Env` on AAPCS64 Arm64. -/
theorem m4_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : kissatM4_compiled_arm64.code.IsInfixAt Host.prog k₀)
    (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ m4Module.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (m4Env f.name f.as f.rs)
        (kissatM4_compiled_arm64.bound f.name) 0 :=
  KissatM4CertLink.mk_module_fnspec m4Env
    (fun g hg args m Q X hs => by
      obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg
      exact (m4Env_moduleOk.fnsOk pre g post hsp).2.2 args m Q X hs)
    (fun g _ => m4Env_noExit g.name g.as g.rs) k₀ hc hu hf

private theorem solve_in_m4Module :
    m4SolveBytesFn ∈ m4Module.fns := by
  exact List.mem_of_getElem?
    (by t_kernel_rfl : (m4Module.fns)[230]? = some m4SolveBytesFn)

private theorem m4Env_names_eq
    (spec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m4SpecTable spec).map SpecEntry.name = m4Fns.map Fn.name := by
  have h := congrArg (List.map Prod.fst) (m4SpecTable_sigs spec)
  simp only [List.map_map] at h; exact h

private theorem m4Fns_nodup : (m4Fns.map Fn.name).Nodup :=
  (List.nodup_append.mp m4Env_moduleOk.nodup).1

private theorem m4SpecTable_nodup
    (spec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m4SpecTable spec).map SpecEntry.name).Nodup :=
  Eq.mp (congrArg List.Nodup (m4Env_names_eq spec).symm) m4Fns_nodup

private theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}
    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by
  have hm := sep_mono (Q := Q)
    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h
  rw [sep_ex_l] at hm
  obtain ⟨m, hm'⟩ := hm
  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩

section Unsat

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

/-- Unconditional end-to-end AAPCS64 Arm64 UNSAT soundness for `m4Module`. -/
theorem m4_solve_bytes_unsat_arm64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
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
  have hfn := (m4_module_fnspec k₀ hc hu solve_in_m4Module).2
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
  have hspec : m4Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    Env.ofTable_of_mem
      (List.mem_of_getElem? (rfl : (m4SpecTable _)[230]? = some _))
      (m4SpecTable_nodup fullSolveBytesSpec)
      ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit,
        by rw [sep_emp]; exact hm_in,
        fun _ _ h u' m' =>
          by rw [sep_emp] at m'; exact ⟨h, u', m'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (KissatM4CertLink.solve_arm64_of_fnspec hfn cnf_ptr _ work_ptr _ fuel
      hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hm_dmem')
  rintro st ⟨hpc, hcal, hsp', m', ⟨hdom, hu', hm'⟩, hst⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hcal, hsp', hst'⟩

/-- Answer-only AAPCS64 Arm64 UNSAT soundness corollary for `m4Module`. -/
theorem m4_solve_bytes_unsat_sound_arm64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (m4_solve_bytes_unsat_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

theorem ax_unsat_sound :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨
          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  (m4_solve_bytes_unsat_sound_arm64 k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
    s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)

end Unsat

/-- Unconditional concrete AAPCS64 Arm64 UNSAT non-vacuity for `FullM4.m4Module` (`231` fns):
there exists a well-formed call on `fullNvUnsatBytes` (`4096`-byte workspace, `fuel = 16`)
that returns `X0 = 20#64` with `parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`. -/
theorem m4_arm64_unsat_nonvacuous [hh : Host] (k₀ : Nat)
    (hc : kissatM4_compiled_arm64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧
      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧
      (s.regs.getXReg .X2).toBitVec = work_ptr ∧
      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧
      (s.regs.getXReg .X4).toBitVec = fuel ∧
      s.regs.X30 = ra.toUInt64 ∧
      s.regs.SP.toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        region (s.regs.SP.toBitVec - BitVec.ofNat 64
            (kissatM4_compiled_arm64.bound "kissat_solve_bytes"))
          (kissatM4_compiled_arm64.bound "kissat_solve_bytes") ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn : armTarget.FnSpec hh "kissat_solve_bytes"
      (m4UnsatEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (kissatM4_compiled_arm64.bound "kissat_solve_bytes") 0 :=
    (KissatM4CertLink.mk_module_fnspec m4UnsatEnv
      (fun g hg args m Q X hs => by
        obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg
        exact (m4UnsatEnv_moduleOk.fnsOk pre g post hsp).2.2 args m Q X hs)
      (fun g _ => m4UnsatEnv_noExit g.name g.as g.rs) k₀ hc hu solve_in_m4Module).2
  let b := kissatM4_compiled_arm64.bound "kissat_solve_bytes"
  let bs := fullPayload fullNvUnsatBytes
  let s := armInitState b bs (as := [i64, i64, i64, i64, i64])
    (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
      fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ())
  have h1 := armInitMem_entry b bs (kissatM4_compiled_arm64.bound_le_max _)
    (by rw [fullPayload_length]; decide)
  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 b ⋆ emp at h1
  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds] at h1
  simp only [region_zero, sep_emp] at h1
  have h1' : (Eq (bs.At 0x1000#64) ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem := by
    rw [show s.regs.SP.toBitVec = 0x1000#64 from rfl]; simpa [sep_emp] using h1
  have hdm : (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
      region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem :=
    sep_mono (Q := emp)
      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))
        (fun _ heq => heq ▸ fullPayload_sep fullNvUnsatBytes (by decide))) h1'
  have hhsp : s.regs.SP.toNat % 16 = 0 := by rw [show s.regs.SP = 4096 from rfl]; decide
  refine ⟨fullNvCnfPtr, fullNvWorkPtr fullNvUnsatBytes, 16#64, fullNvUnsatBytes, 4096,
    s, 0x1234, emp, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, hhsp, hdm, ?_⟩
  have hspec : m4UnsatEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ())
      (bs.At 0x1000#64) (fun r _ => r.fst = 20#64 ∧ fullNvUnsatCnf.Unsat)
      (fun _ _ _ _ => False) :=
    Env.ofTable_of_mem
      (List.mem_of_getElem? (rfl : (m4SpecTable _)[230]? = some _))
      (m4SpecTable_nodup fullUnsatWitnessSpec)
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ huns _ => ⟨rfl, huns⟩⟩
  have hev := KissatM4CertLink.solve_arm64_of_fnspec hfn fullNvCnfPtr _
    (fullNvWorkPtr fullNvUnsatBytes) _ 16#64 hspec s 0x1234 emp
    rfl rfl rfl rfl rfl rfl hhsp h1'
  exact eventually_weaken _ _ _ _
    (fun _ ⟨hpc, _, _, _, ⟨h20, huns⟩, _⟩ =>
      ⟨hpc, h20, fullNvUnsatCnf, parseDimacs_fullNvUnsatBytes, huns⟩)
    hev

#print axioms kissatM4_compiled_arm64
#print axioms m4_module_fnspec
#print axioms m4_solve_bytes_unsat_arm64
#print axioms ax_unsat_sound
#print axioms m4_arm64_unsat_nonvacuous

end LeanQbe.T.Arm64.KissatM4
