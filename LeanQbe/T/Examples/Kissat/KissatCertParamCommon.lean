/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineProof
public import LeanQbe.T.Examples.Kissat.KissatCertCommon
import LeanQbe.T.AbiLemmas

/-!
# Parameterized Tier-1 Kissat Proof Combinators (`KissatCertParamCommon`)

Pure `Lean`-meta-free bridge layering `MainCertInlineProof` onto `KissatCertCommon` without
invalidating `FullFidelityAssemblyUtil` / `Step1..7Proof`:
* Whole-module `FnSpec` bridges (`module_fnspec_maxB_of_abi`, `module_fnspec_of_compile`,
  `module_fnspec_of_compile_maxB`).
* Fixed-`2048B` `LinkedCert` UNSAT combinators (`*_maxB_of_abi`, `run_unsat_maxB_of_abi`).
* Raw `compileModuleOptInlinePolicy`-parameterized exact-bound & fixed-`maxB` UNSAT soundness,
  non-vacuity, and closed-host `run_unsat` combinators.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.KissatCertParamCommon

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open Kraken

theorem module_fnspec_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧
      A.T.FnSpec hh f.name (P.env f.name f.as f.rs) 2048 0 :=
  have ⟨hdef, hfn⟩ := module_fnspec_of_abi A P cert hleg hh k₀ hc hu hf
  ⟨hdef, Target.FnSpec.mono_stack A.T hfn (cert.bound_le_max f.name) hmax⟩

theorem module_fnspec_of_compile (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) {b : Nat} (hb : (f.name, b) ∈ bounds) :
    A.T.Defined hh f.name ∧ A.T.FnSpec hh f.name (P.env f.name f.as f.rs) b 0 :=
  fnSpec_of_compileModuleOptInlinePolicy hh k₀ hcm hc hu P.moduleOk hleg hf (P.noExit f hf) hb

theorem module_fnspec_of_compile_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    {maxB : Nat} (hble : ∀ p ∈ bounds, p.2 ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64)
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧ A.T.FnSpec hh f.name (P.env f.name f.as f.rs) maxB 0 :=
  fnSpec_maxB_of_compileModuleOptInlinePolicy hh k₀ hcm hc hu P.moduleOk hleg hf
    (P.noExit f hf) hble hmax

private theorem entryFn_spec_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0 := by
  have hmem : ∀ f ∈ P.mod.fns,
      f.name = P.entryFn ∧ f.as = [i64, i64, i64, i64, i64] ∧ f.rs = [i64] →
      A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
        (cert.bound P.entryFn) 0 := by
    rintro ⟨nm, as, rs, body⟩ hf ⟨rfl, rfl, rfl⟩
    exact (cert.fnSpec_noExit_id_optInlinePolicy hh P.env k₀ hc hu P.moduleOk hf
      has hrs (P.noExit _ hf)).2
  exact hmem P.entryFn_fn P.entry_mem P.entryFn_sig

private theorem entryFn_spec_of_compile (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64]) b 0 := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts P.moduleOk
  have hsupp : ∀ g ∈ (P.mod.optInlinePolicy P.inlPolicy).fns,
      (g.earlyOpt).body.supportsSource A.lt = true :=
    Compiled.compileModule_supportsSource hcm
  have hMnd : (P.mod.fns.map Fn.name).Nodup := by
    simp only [Module.checkAcyclic, Bool.and_eq_true] at hacyc
    exact (List.nodup_append.mp (P.mod.namesNodup_of_checkNamesNodup hacyc.1)).1
  have hsig : ∀ f ∈ P.mod.fns,
      f.name = P.entryFn ∧ f.as = [i64, i64, i64, i64, i64] ∧ f.rs = [i64] →
      A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64]) b 0 := by
    rintro ⟨nm, as, rs, body⟩ hf ⟨rfl, rfl, rfl⟩
    obtain ⟨f', hf', hnm, _, hspec⟩ :=
      compile_sound_optInlinePolicy A.T hh A.lt P.mod P.env [] [] 0 P.inlPolicy
        hints code bounds k₀ hcm hc hu hacyc hwf hsupp hwp
        (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
        (fun _ h => nomatch h) (P.entryFn, b) hb
    have heqf : f' = ⟨P.entryFn, [i64, i64, i64, i64, i64], [i64], body⟩ :=
      fn_eq_of_mem_fns hMnd hf' hf hnm.symm
    subst heqf
    exact fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
      (List.mem_append_left _ (List.mem_map_of_mem hf)) (P.noExit _ hf) hspec
  exact hsig P.entryFn_fn P.entry_mem P.entryFn_sig

private theorem solve_bytes_unsat_of_fnspec (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hh : A.T.mach.Host) {b : Nat}
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64]) b 0)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra b ⋆ R) (A.T.mach.mem s)) :
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
          A.exitFrame s b ⋆ R) (A.T.mach.mem (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) := by
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (A.entryFrame s ra b ⋆ R)) (A.T.mach.mem s) := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆ A.entryFrame s ra b ⋆ R) (A.T.mach.mem s) := by
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

private theorem unsat_nonvacuous_of_fnspec (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hh : A.T.mach.Host) {b : Nat}
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64]) b 0)
    (hb_stack : b ≤ A.maxStack) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
        (BitVec.ofNat 64 wlen) fuel ∧
      A.stackPre s ra ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        A.entryFrame s ra b ⋆ R) (A.T.mach.mem s) ∧
      Eventually (A.T.mach.step hh)
        (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) := by
  let bs := m6NvPayload nvM6UnsatBytes
  let args : Tup Val [i64, i64, i64, i64, i64] :=
    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
  let s := A.init.initState (as := [i64, i64, i64, i64, i64]) b bs args
  have hcb_len : nvM6UnsatBytes.length ≤ 2048 := by decide
  have hbs_len : bs.length ≤ 8192 := by
    rw [m6NvPayload_length, m6NvWorkLen_eq]
    exact Nat.add_le_add_right hcb_len 6144
  have h1 := A.init.mem_entry b bs args hb_stack (Nat.le_trans hbs_len A.maxMem_ge)
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

private theorem run_unsat_of_fnspec (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hh : A.T.mach.Host) {b : Nat}
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64]) b 0)
    (hb_stack : b ≤ A.maxStack) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = A.init.ra0 ∧
        A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          A.T.Exit A.init.sp0 b ⋆ emp))
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64]) b
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr hh P.entryFn)) := by
  have ⟨locs, hlocs, _⟩ := A.argsIn_of_args5 (A.init_args5 0 [] 0#64 0#64 0#64 0#64 0#64)
  have hassign : (A.T.toIsa.assignArgs [i64, i64, i64, i64, i64]).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨locs, hlocs⟩
  have hcb_len : nvM6UnsatBytes.length ≤ 2048 := by decide
  have hbs_len : (m6NvPayload nvM6UnsatBytes).length ≤ 8192 := by
    rw [m6NvPayload_length, m6NvWorkLen_eq]
    exact Nat.add_le_add_right hcb_len 6144
  refine run_ret1_sep_i64_at A.init hh hfn hb_stack
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
    ?_ (fun _ _ h => h)
  refine P.solve_intro (R := emp) (by decide) (by decide) ?_ ?_
  · rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
    exact m6NvPayload_sep nvM6UnsatBytes hcb_len
  · intro _ m' _ _ htr hm'
    exact ⟨congrArg (·, ()) (htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
      (by decide) nvM6Unsat_header nvM6Unsat_unitTrace), nvM6UnsatCnf_unsat, hm'⟩

/-! ### Exact-Bound & Fixed-`2048` `LinkedCert` Entry Combinators -/

theorem solve_bytes_unsat_entry_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
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
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  solve_bytes_unsat_of_fnspec A P hh (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

theorem unsat_correct_entry_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
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
    (solve_bytes_unsat_entry_of_abi A P cert has hrs hh k₀ hc hu cnf_ptr work_ptr fuel
      cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem)

theorem unsat_nonvacuous_entry_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
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
        (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  unsat_nonvacuous_of_fnspec A P hh (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu)
    (Nat.le_trans (cert.bound_le_max _) A.maxStack_ge)

theorem run_unsat_entry_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64]) :
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
        (A.T.mach.labelAddr cert.host P.entryFn)) :=
  run_unsat_of_fnspec A P cert.host
    (entryFn_spec_of_abi A P cert has hrs cert.host 0 cert.code_infix_host cert.labelsUnique)
    (Nat.le_trans (cert.bound_le_max _) A.maxStack_ge)

theorem solve_bytes_unsat_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
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
      A.entryFrame s ra 2048 ⋆ R) (A.T.mach.mem s)) :
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
          A.exitFrame s 2048 ⋆ R) (A.T.mach.mem (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  solve_bytes_unsat_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu)
      (cert.bound_le_max _) hmax)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

theorem unsat_correct_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
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
      A.entryFrame s ra 2048 ⋆ R) (A.T.mach.mem s)) :
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
    (solve_bytes_unsat_maxB_of_abi A P cert has hrs hmax hh k₀ hc hu cnf_ptr work_ptr fuel
      cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem)

theorem unsat_nonvacuous_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
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
        A.entryFrame s ra 2048 ⋆ R) (A.T.mach.mem s) ∧
      Eventually (A.T.mach.step hh)
        (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  unsat_nonvacuous_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu)
      (cert.bound_le_max _) hmax)
    A.maxStack_ge

theorem run_unsat_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide) :
    Eventually (A.T.mach.step cert.host)
      (fun st =>
        A.T.mach.pc st = A.init.ra0 ∧
        A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          A.T.Exit A.init.sp0 2048 ⋆ emp))
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64]) 2048
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr cert.host P.entryFn)) :=
  run_unsat_of_fnspec A P cert.host
    (Target.FnSpec.mono_stack A.T
      (entryFn_spec_of_abi A P cert has hrs cert.host 0 cert.code_infix_host cert.labelsUnique)
      (cert.bound_le_max _) hmax)
    A.maxStack_ge

/-! ### Raw `compileModuleOptInlinePolicy` Exact-Bound & Fixed-`maxB` Theorems -/

theorem solve_bytes_unsat_of_compile (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra b ⋆ R) (A.T.mach.mem s)) :
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
          A.exitFrame s b ⋆ R) (A.T.mach.mem (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  solve_bytes_unsat_of_fnspec A P hh
    (entryFn_spec_of_compile A P has hrs hints code bounds hcm hb hh k₀ hc hu)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

theorem unsat_correct_of_compile (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra b ⋆ R) (A.T.mach.mem s)) :
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
    (solve_bytes_unsat_of_compile A P has hrs hints code bounds hcm hb hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem)

theorem unsat_nonvacuous_of_compile (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds) (hb_stack : b ≤ A.maxStack)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
        (BitVec.ofNat 64 wlen) fuel ∧
      A.stackPre s ra ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        A.entryFrame s ra b ⋆ R) (A.T.mach.mem s) ∧
      Eventually (A.T.mach.step hh)
        (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  unsat_nonvacuous_of_fnspec A P hh
    (entryFn_spec_of_compile A P has hrs hints code bounds hcm hb hh k₀ hc hu) hb_stack

theorem solve_bytes_unsat_of_compile_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b maxB : Nat} (hb : (P.entryFn, b) ∈ bounds) (hble : b ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra maxB ⋆ R) (A.T.mach.mem s)) :
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
          A.exitFrame s maxB ⋆ R) (A.T.mach.mem (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  solve_bytes_unsat_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T
      (entryFn_spec_of_compile A P has hrs hints code bounds hcm hb hh k₀ hc hu) hble hmax)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

theorem unsat_correct_of_compile_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b maxB : Nat} (hb : (P.entryFn, b) ∈ bounds) (hble : b ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra maxB ⋆ R) (A.T.mach.mem s)) :
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
    (solve_bytes_unsat_of_compile_maxB A P has hrs hints code bounds hcm hb hble hmax hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem)

theorem unsat_nonvacuous_of_compile_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b maxB : Nat} (hb : (P.entryFn, b) ∈ bounds) (hble : b ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64) (hmstack : maxB ≤ A.maxStack)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
        (BitVec.ofNat 64 wlen) fuel ∧
      A.stackPre s ra ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        A.entryFrame s ra maxB ⋆ R) (A.T.mach.mem s) ∧
      Eventually (A.T.mach.step hh)
        (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  unsat_nonvacuous_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T
      (entryFn_spec_of_compile A P has hrs hints code bounds hcm hb hh k₀ hc hu) hble hmax)
    hmstack

theorem run_unsat_of_compile_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b maxB : Nat} (hb : (P.entryFn, b) ∈ bounds) (hble : b ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64) (hmstack : maxB ≤ A.maxStack)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = A.init.ra0 ∧
        A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          A.T.Exit A.init.sp0 maxB ⋆ emp))
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64]) maxB
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr hh P.entryFn)) :=
  run_unsat_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T
      (entryFn_spec_of_compile A P has hrs hints code bounds hcm hb hh k₀ hc hu) hble hmax)
    hmstack

end LeanQbe.T.Examples.Kissat.KissatCertParamCommon
