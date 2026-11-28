module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Examples.Kissat.KissatAbiCommon
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv1
public import LeanQbe.T.Logic.MemLemmas
public import Std.Sat.CNF.Basic
public import Kraken.Mem
public import Kraken.Separation

/-!
# Arch-Free Kissat Certificate & ABI Deduplication Infrastructure (`KissatCertCommon`)

Centralizes architecture-independent helpers and generic UNSAT linking/top-level proof combinators
used by M8+ generated certificates (`Amd64.KissatAbi` / `Arm64.KissatAbi`, `0` dual-arch):
1. Deduplicated `m6Nv*` payload/bound helpers and `sep_exists_eq`.
2. `ArchKissatAbi`: ISA-agnostic ABI bridge over `Target` and `TargetInit`.
3. `solve_of_abi_fnspec`: generic `FnSpec` -> `Eventually (A.T.mach.step hh)` lift.
4. `KissatUnsatPkg` and generic `module_fnspec_of_abi`, `solve_bytes_unsat_of_abi`,
   `unsat_correct_of_abi`, `unsat_nonvacuous_of_abi`, `run_unsat_of_abi`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.KissatCertCommon

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken

/-! ## 1. Deduplicated `Mem` & `M6Nv` Payload Helpers (`Proof.Spec.SatNv1` + `KissatAbiCommon`) -/

export LeanQbe.T.Examples.Kissat.Proof.Spec
  ( m6NvWorkLen m6NvWorkLen_eq m6NvPayload m6NvPayload_eq m6NvPayload_length
    m6NvPayload_sep m6Nv_unsat_bound CommonUnsatSolveReq KissatUnsatPkg )

/-! ## 2. Generic Arch-Free `KissatUnsatPkg` & Top-Level UNSAT Theorems -/

theorem module_fnspec_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧
      A.T.FnSpec hh f.name (P.env f.name f.as f.rs) (cert.bound f.name) 0 :=
  cert.fnSpec_noExit_of_legalSigAll_optInlinePolicy hh P.env k₀ hc hu
    P.moduleOk hleg hf (P.noExit f hf)

private theorem entryFn_spec_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0 := by
  have hmem : ∀ f ∈ P.mod.fns,
      f.name = P.entryFn ∧ f.as = [i64, i64, i64, i64, i64] ∧ f.rs = [i64] →
      A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
        (cert.bound P.entryFn) 0 := by
    rintro ⟨nm, as, rs, body⟩ hf ⟨rfl, rfl, rfl⟩
    exact (module_fnspec_of_abi A P cert hleg hh k₀ hc hu hf).2
  exact hmem P.entryFn_fn P.entry_mem P.entryFn_sig

theorem solve_bytes_unsat_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0#64 ∨
          A.retGpr (A.T.mach.data st) = 10#64 ∨
          A.retGpr (A.T.mach.data st) = 20#64) ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        A.calleeSpOk s (A.T.mach.data st) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          A.exitFrame s (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) := by
  have hfn := entryFn_spec_of_abi A P cert hleg hh k₀ hc hu
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (A.entryFrame s ra (cert.bound P.entryFn) ⋆ R)) (A.T.mach.mem s) := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆ A.entryFrame s ra (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem s) := by
    rw [sep_assoc]; exact hm_dmem
  have hspec : P.env P.entryFn [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) := by
    refine P.solve_intro (R := emp) hcfit hwfit (by rw [sep_emp]; exact hm_in) ?_
    intro r m' hdom hu _ hm'
    rw [sep_emp] at hm'
    exact ⟨hdom, hu, hm'⟩
  refine eventually_weaken _ _ _ _ ?_
    (solve_of_abi_fnspec A hh P.entryFn hfn cnf_ptr _ work_ptr _ fuel hspec s ra R
      hargs hsp hm_dmem')
  rintro st ⟨hpc, hcal, m', ⟨hdom, hu', hm'⟩, hst⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hcal, hst'⟩

theorem unsat_correct_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0#64 ∨
          A.retGpr (A.T.mach.data st) = 10#64 ∨
          A.retGpr (A.T.mach.data st) = 20#64) ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (solve_bytes_unsat_of_abi A P cert hleg hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hargs hsp hmem)

theorem unsat_nonvacuous_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
        (BitVec.ofNat 64 wlen) fuel ∧
      A.stackPre s ra ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        A.entryFrame s ra (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem s) ∧
      Eventually (A.T.mach.step hh)
        (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) := by
  have hfn := entryFn_spec_of_abi A P cert hleg hh k₀ hc hu
  let b := cert.bound P.entryFn
  let bs := m6NvPayload nvM6UnsatBytes
  let args : Tup Val [i64, i64, i64, i64, i64] :=
    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
  let s := A.init.initState (as := [i64, i64, i64, i64, i64]) b bs args
  have hcb_len : nvM6UnsatBytes.length ≤ 2048 := by decide
  have hbs_len : bs.length ≤ 8192 := by
    rw [m6NvPayload_length, m6NvWorkLen_eq]
    exact Nat.add_le_add_right hcb_len 6144
  have h1 := A.init.mem_entry b bs args
    (Nat.le_trans (cert.bound_le_max _) A.maxStack_ge)
    (Nat.le_trans hbs_len A.maxMem_ge)
  rw [← A.init.get_sp b bs args] at h1
  have h1' : (Eq (bs.At 0x1000#64) ⋆ A.entryFrame s A.init.ra0 b ⋆ emp) (A.T.mach.mem s) :=
    sep_mono_mid (fun _ he => A.entryFrame_of_entry he) h1
  have hdm : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      region nvM6UnsatWorkPtr m6NvWorkLen ⋆
      A.entryFrame s A.init.ra0 b ⋆ emp) (A.T.mach.mem s) := by
    refine sep_mono (fun _ => sep_mono (fun _ heq => ?_)) h1'
    rw [← heq, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
    exact m6NvPayload_sep nvM6UnsatBytes hcb_len
  have hargs := A.init_args5 b bs nvM6CnfPtr (BitVec.ofNat 64 nvM6UnsatBytes.length)
    nvM6UnsatWorkPtr (BitVec.ofNat 64 m6NvWorkLen) 16#64
  have hsp := A.init_stackPre b bs args
  refine ⟨nvM6CnfPtr, nvM6UnsatWorkPtr, 16#64, nvM6UnsatBytes, m6NvWorkLen,
    s, A.init.ra0, emp, by decide, by decide, hargs, hsp, hdm, ?_⟩
  have hspec : P.env P.entryFn [i64, i64, i64, i64, i64] [i64]
      args (bs.At 0x1000#64) (fun r _ => r.fst = 20#64 ∧ nvM6UnsatCnf.Unsat)
      (fun _ _ _ _ => False) := by
    refine P.solve_intro (R := emp) (by decide) (by decide) ?_ ?_
    · rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
      exact m6NvPayload_sep nvM6UnsatBytes (by decide)
    · intro r _ _ _ htr _
      exact ⟨htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
        (by decide) nvM6Unsat_header nvM6Unsat_unitTrace, nvM6UnsatCnf_unsat⟩
  have hev := solve_of_abi_fnspec A hh P.entryFn hfn nvM6CnfPtr _
    nvM6UnsatWorkPtr _ 16#64 hspec s A.init.ra0 emp hargs hsp h1'
  exact eventually_weaken _ _ _ _
    (fun _ ⟨hpc, _, _, ⟨h20, huns⟩, _⟩ =>
      ⟨hpc, h20, nvM6UnsatCnf, parseDimacs_nvM6UnsatBytes, huns⟩)
    hev

theorem run_unsat_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns) :
    Eventually (A.T.mach.step cert.host)
      (fun st =>
        A.T.mach.pc st = A.init.ra0 ∧
        A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          A.T.Exit A.init.sp0 (cert.bound P.entryFn) ⋆ emp))
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64])
          (cert.bound P.entryFn)
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr cert.host P.entryFn)) := by
  have ⟨locs, hlocs, _⟩ := A.argsIn_of_args5 (A.init_args5 0 [] 0#64 0#64 0#64 0#64 0#64)
  have hassign : (A.T.toIsa.assignArgs [i64, i64, i64, i64, i64]).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨locs, hlocs⟩
  have hcb_len : nvM6UnsatBytes.length ≤ 2048 := by decide
  have hbs_len : (m6NvPayload nvM6UnsatBytes).length ≤ 8192 := by
    rw [m6NvPayload_length, m6NvWorkLen_eq]
    exact Nat.add_le_add_right hcb_len 6144
  have hrun : ∀ f ∈ P.mod.fns,
      f.name = P.entryFn ∧ f.as = [i64, i64, i64, i64, i64] ∧ f.rs = [i64] →
      Eventually (A.T.mach.step cert.host)
        (fun st =>
          A.T.mach.pc st = A.init.ra0 ∧
          A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆
            (fun m' => nvM6UnsatCnf.Unsat ∧
              (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
                region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
            A.T.Exit A.init.sp0 (cert.bound P.entryFn) ⋆ emp))
        (A.T.mach.mkState
          (A.init.initState (as := [i64, i64, i64, i64, i64])
            (cert.bound P.entryFn)
            (m6NvPayload nvM6UnsatBytes)
            (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
              nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
          (A.T.mach.labelAddr cert.host P.entryFn)) := by
    rintro ⟨nm, as, rs, body⟩ hfn_mem ⟨rfl, rfl, rfl⟩
    refine cert.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy
      A.init
      P.env P.moduleOk hleg hfn_mem rfl
      (P.noExit ⟨P.entryFn, [i64, i64, i64, i64, i64], [i64], body⟩ hfn_mem)
      (m6NvPayload nvM6UnsatBytes)
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
      20#64
      (fun m' => nvM6UnsatCnf.Unsat ∧
        (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
          region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m')
      (Nat.le_trans hbs_len A.maxMem_ge)
      hassign
      (Q := fun r m' => r = (20#64, ()) ∧ nvM6UnsatCnf.Unsat ∧
        (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
          region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m')
      ?_ (fun _ _ h => h) A.maxStack_ge
    refine P.solve_intro (R := emp) (by decide) (by decide) ?_ ?_
    · rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
      exact m6NvPayload_sep nvM6UnsatBytes hcb_len
    · intro _ m' _ _ htr hm'
      exact ⟨congrArg (·, ()) (htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
        (by decide) nvM6Unsat_header nvM6Unsat_unitTrace), nvM6UnsatCnf_unsat, hm'⟩
  exact hrun P.entryFn_fn P.entry_mem P.entryFn_sig

end LeanQbe.T.Examples.Kissat.KissatCertCommon
