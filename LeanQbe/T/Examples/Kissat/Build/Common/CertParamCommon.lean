/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineProof
public import LeanQbe.T.Examples.Kissat.KissatAbiCommon
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv1
import LeanQbe.T.AbiLemmas

/-!
# Legacy-Free Parameterized Kissat Proof Combinators (`Build.Common.CertParamCommon`)

Clean, `Full*`-free, `PatchModule`-free, `Solver`-free target-parametric UNSAT soundness &
concrete `Mem 64` non-vacuity combinators parameterized strictly over
`Proof.Spec.KissatUnsatPkg` and `KissatCertCommon.ArchKissatAbi`:
1. **`FnSpec`-level combinators** (`*_of_fnspec`): work for any compiled module `M'` whose
   entry `FnSpec` refines `pkg.mod`.
2. **Generic `Module` / `LinkedCert` combinators** (`*_of_cert`, `*_of_cert_moduleOk`,
   `*_of_compile_mod`): work seamlessly for ANY compiled module `M'` whose `fnSpec` refines
   `pkg.mod` (both `pkg.mod.optInlinePolicy pkg.inlPolicy` and `InlinePlan` `M.inlinePlan plan`).
3. **`optInlinePolicy` specializations**: 1:1 drop-in parity for `LinkedCert` and raw
   `compileModuleOptInlinePolicy` (both exact `cert.bound` / `b` and fixed `maxB`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Common.CertParamCommon

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken

/-! ## 1. `FnSpec`-Level UNSAT Soundness & Concrete `Mem 64` NV Combinators -/

/-- Lift an arbitrary `A.T.FnSpec` for `P.entryFn` to machine-code UNSAT soundness + framing. -/
theorem solve_bytes_unsat_of_fnspec (A : ArchKissatAbi) (P : KissatUnsatPkg)
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
  obtain ⟨m, hm_in, hm_dmem⟩ := KissatCertCommon.sep_exists_eq hm0
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

/-- Answer-only projection of `solve_bytes_unsat_of_fnspec`. -/
theorem unsat_correct_of_fnspec (A : ArchKissatAbi) (P : KissatUnsatPkg)
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
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (solve_bytes_unsat_of_fnspec A P hh hfn cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hargs hsp hmem)

/-- Lift an arbitrary `A.T.FnSpec` for `P.entryFn` to concrete `Mem 64` UNSAT non-vacuity. -/
theorem unsat_nonvacuous_of_fnspec (A : ArchKissatAbi) (P : KissatUnsatPkg)
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

/-- Lift an arbitrary `A.T.FnSpec` for `P.entryFn` to closed `A.init` host UNSAT execution. -/
theorem run_unsat_of_fnspec (A : ArchKissatAbi) (P : KissatUnsatPkg)
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

/-! ## 2. Generic `M' : Module` & `FnSpec`-Refining `LinkedCert` Combinators -/

private theorem mem_fns_of_sigs_eq {fs₁ fs₂ : List Fn} (hsigs : fs₁.map Fn.sig = fs₂.map Fn.sig)
    {f : Fn} (hf : f ∈ fs₁) :
    ∃ f' ∈ fs₂, f'.name = f.name ∧ f'.as = f.as ∧ f'.rs = f.rs := by
  obtain ⟨f', hf', heq⟩ := List.mem_map.mp (hsigs ▸ List.mem_map_of_mem hf)
  simp only [Fn.sig, Prod.mk.injEq] at heq
  exact ⟨f', hf', heq.1, heq.2.1, heq.2.2⟩

private theorem noExit_of_fn_sig (P : KissatUnsatPkg) {f f' : Fn} (hf : f ∈ P.mod.fns)
    (hnm : f'.name = f.name) (has : f'.as = f.as) (hrs : f'.rs = f.rs) :
    InlNoExit P.env f' := by
  rcases f with ⟨nm, as, rs, fbody⟩
  rcases f' with ⟨nm', as', rs', _⟩
  dsimp only at hnm has hrs
  subst hnm; subst has; subst hrs
  exact P.noExit ⟨nm', as', rs', fbody⟩ hf

/-- Derive whole-module `Defined ∧ FnSpec` for every `f ∈ P.mod.fns` from ANY compiled module
`M'` satisfying `ModuleOk P.env M'` and matching `P.mod.fns` signatures (e.g. `optInlinePolicy`
or `InlinePlan`). -/
theorem module_fnspec_of_cert_moduleOk (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB)
    (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (hleg : LegalSigAll A.lt P.mod.fns) (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧
      A.T.FnSpec hh f.name (P.env f.name f.as f.rs) (cert.bound f.name) 0 := by
  obtain ⟨f', hf', hnm, has_eq, hrs_eq⟩ := mem_fns_of_sigs_eq hsigs.symm hf
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM'
  have ⟨hasL, hrsL⟩ := hleg f hf
  have hnoex : InlNoExit P.env f' := noExit_of_fn_sig P hf hnm has_eq hrs_eq
  have hspec := cert.fnSpec_noExit_id hh P.env k₀ hc hu hacyc hwf hwp hf'
    (has_eq ▸ hasL) (hrs_eq ▸ hrsL) hnoex
  rcases f with ⟨nm, as, rs, _⟩
  rcases f' with ⟨nm', as', rs', _⟩
  dsimp only at hnm has_eq hrs_eq
  subst hnm; subst has_eq; subst hrs_eq
  exact hspec

/-- Fixed-`tgtB` stack-monotonic variant of `module_fnspec_of_cert_moduleOk`. -/
theorem module_fnspec_maxB_of_cert_moduleOk (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB tgtB : Nat} (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB)
    (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (hleg : LegalSigAll A.lt P.mod.fns) (hble : maxB ≤ tgtB := by omega)
    (hmax : tgtB + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧ A.T.FnSpec hh f.name (P.env f.name f.as f.rs) tgtB 0 :=
  have ⟨hdef, hfn⟩ := module_fnspec_of_cert_moduleOk A P cert hM' hsigs hleg hh k₀ hc hu hf
  ⟨hdef, Target.FnSpec.mono_stack A.T hfn (Nat.le_trans (cert.bound_le_max f.name) hble) hmax⟩

/-- Extract `A.T.FnSpec` for `P.entryFn` from ANY `LinkedCert` over `M'` with `ModuleOk P.env M'`
and matching entry signature. -/
theorem entryFn_spec_of_cert_moduleOk (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB)
    (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64]) (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0 := by
  obtain ⟨f', hf', hnm, has_eq, hrs_eq⟩ := mem_fns_of_sigs_eq hsigs.symm P.entry_mem
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM'
  have hnoex : InlNoExit P.env f' := noExit_of_fn_sig P P.entry_mem hnm has_eq hrs_eq
  have hnm' : f'.name = P.entryFn := hnm.trans P.entryFn_sig.1
  have has' : f'.as = [i64, i64, i64, i64, i64] := has_eq.trans P.entryFn_sig.2.1
  have hrs' : f'.rs = [i64] := hrs_eq.trans P.entryFn_sig.2.2
  have hspec := (cert.fnSpec_noExit_id hh P.env k₀ hc hu hacyc hwf hwp hf'
    (has' ▸ has) (hrs' ▸ hrs) hnoex).2
  rcases f' with ⟨nm', as', rs', _⟩
  dsimp only at hnm' has' hrs'
  subst hnm'; subst has'; subst hrs'
  exact hspec

/-- Extract `A.T.Defined ∧ A.T.FnSpec` for any `f ∈ P.mod.fns` from raw `compileModule` over
ANY `M' : Module` satisfying `ModuleOk P.env M'` and matching `P.mod.fns` signatures. -/
theorem module_fnspec_of_compile_mod (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M')
    (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig) (hleg : LegalSigAll A.lt P.mod.fns)
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) {b : Nat} (hb : (f.name, b) ∈ bounds) :
    A.T.Defined hh f.name ∧ A.T.FnSpec hh f.name (P.env f.name f.as f.rs) b 0 := by
  obtain ⟨f', hf', hnm, has_eq, hrs_eq⟩ := mem_fns_of_sigs_eq hsigs.symm hf
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM'
  have hsupp : ∀ g ∈ M'.fns, (g.earlyOpt).body.supportsSource A.lt = true :=
    Compiled.compileModule_supportsSource hcm
  have hnd : (M'.fns.map Fn.name).Nodup := (List.nodup_append.mp hM'.nodup).1
  obtain ⟨g, hg, hgnm, hdef, hspec⟩ :=
    compile_sound A.T hh A.lt M' P.env [] [] 0 hints code bounds k₀ hcm hc hu
      hacyc hwf hsupp hwp (fun _ h => nomatch h)
      ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩ (fun _ h => nomatch h) (f.name, b) hb
  dsimp only at hgnm hdef hspec
  have heqf : g = f' := fn_eq_of_mem_fns hnd hg hf' (hgnm.symm.trans hnm.symm)
  subst heqf
  have ⟨hasL, hrsL⟩ := hleg f hf
  have hnoex : InlNoExit P.env g := noExit_of_fn_sig P hf hnm has_eq hrs_eq
  rw [hgnm] at hdef hspec
  have hfn := fnSpec_of_legalEnv_legalSig_eq_noExit (has_eq ▸ hasL) (hrs_eq ▸ hrsL)
    (List.mem_append_left _ (List.mem_map_of_mem hf')) hnoex hspec
  rcases f with ⟨nm, as, rs, _⟩
  rcases g with ⟨nm', as', rs', _⟩
  dsimp only at hnm has_eq hrs_eq
  subst hnm; subst has_eq; subst hrs_eq
  exact ⟨hdef, hfn⟩

/-- Fixed-`maxB` raw `compileModule` `Defined ∧ FnSpec` for ANY `M'` refining `P.mod`. -/
theorem module_fnspec_maxB_of_compile_mod (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M')
    (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig) (hleg : LegalSigAll A.lt P.mod.fns)
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    {maxB : Nat} (hble : ∀ p ∈ bounds, p.2 ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64)
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧ A.T.FnSpec hh f.name (P.env f.name f.as f.rs) maxB 0 := by
  have hbn : bounds.map Prod.fst = M'.fns.map Fn.name := compileModule_bounds_names hcm
  have hnames : M'.fns.map Fn.name = P.mod.fns.map Fn.name := by
    have h := congrArg (List.map Prod.fst) hsigs
    simpa [Fn.sig, List.map_map, Function.comp_def] using h
  have hmem : f.name ∈ bounds.map Prod.fst := hbn ▸ hnames ▸ List.mem_map_of_mem hf
  obtain ⟨⟨_, b⟩, hb, hnm⟩ := List.mem_map.mp hmem
  dsimp only at hnm
  subst hnm
  obtain ⟨hdef, hspec⟩ :=
    module_fnspec_of_compile_mod A P hM' hsigs hleg hints code bounds hcm hh k₀ hc hu hf hb
  exact ⟨hdef, Target.FnSpec.mono_stack A.T hspec (hble (f.name, b) hb) hmax⟩

/-- Extract `A.T.FnSpec` for `P.entryFn` from raw `compileModule` over ANY `M'` with
`ModuleOk P.env M'` and matching signatures. -/
theorem entryFn_spec_of_compile_mod (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds) (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64]) b 0 := by
  obtain ⟨f', hf', hnm, has_eq, hrs_eq⟩ := mem_fns_of_sigs_eq hsigs.symm P.entry_mem
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM'
  have hsupp : ∀ g ∈ M'.fns, (g.earlyOpt).body.supportsSource A.lt = true :=
    Compiled.compileModule_supportsSource hcm
  have hnd : (M'.fns.map Fn.name).Nodup := (List.nodup_append.mp hM'.nodup).1
  obtain ⟨g, hg, hgnm, _, hspec⟩ :=
    compile_sound A.T hh A.lt M' P.env [] [] 0 hints code bounds k₀ hcm hc hu
      hacyc hwf hsupp hwp (fun _ h => nomatch h)
      ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩ (fun _ h => nomatch h) (P.entryFn, b) hb
  dsimp only at hgnm hspec
  have hnm' : f'.name = P.entryFn := hnm.trans P.entryFn_sig.1
  have has' : f'.as = [i64, i64, i64, i64, i64] := has_eq.trans P.entryFn_sig.2.1
  have hrs' : f'.rs = [i64] := hrs_eq.trans P.entryFn_sig.2.2
  have heqf : g = f' := fn_eq_of_mem_fns hnd hg hf' (hgnm.symm.trans hnm'.symm)
  subst heqf
  have hnoex : InlNoExit P.env g := noExit_of_fn_sig P P.entry_mem hnm has_eq hrs_eq
  rw [hgnm] at hspec
  have hfn := fnSpec_of_legalEnv_legalSig_eq_noExit (has' ▸ has) (hrs' ▸ hrs)
    (List.mem_append_left _ (List.mem_map_of_mem hf')) hnoex hspec
  rcases g with ⟨nm', as', rs', _⟩
  dsimp only at hnm' has' hrs'
  subst hnm'; subst has'; subst hrs'
  exact hfn

/-! ### Generic `LinkedCert` UNSAT Combinators (Arbitrary `M'` Refining `P.entryFn`) -/

/-- Exact-bound UNSAT soundness + framing for ANY `cert : LinkedCert ... M'` given `hfn`
refining `P.entryFn`. -/
theorem solve_bytes_unsat_entry_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB)
    (hh : A.T.mach.Host)
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0)
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
  solve_bytes_unsat_of_fnspec A P hh hfn cnf_ptr work_ptr fuel cnfBytes wlen
    hcfit hwfit s ra R hargs hsp hmem

/-- Answer-only UNSAT soundness for ANY `cert : LinkedCert ... M'` given `hfn`. -/
theorem unsat_correct_entry_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB)
    (hh : A.T.mach.Host)
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0)
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
  unsat_correct_of_fnspec A P hh hfn cnf_ptr work_ptr fuel cnfBytes wlen
    hcfit hwfit s ra R hargs hsp hmem

/-- Exact-bound concrete `Mem 64` UNSAT non-vacuity for ANY `cert : LinkedCert ... M'`. -/
theorem unsat_nonvacuous_entry_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB)
    (hh : A.T.mach.Host)
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0)
    (hbound : maxB ≤ A.maxStack := by omega) :
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
  unsat_nonvacuous_of_fnspec A P hh hfn (Nat.le_trans (cert.bound_le_max _) hbound)

/-- Exact-bound closed-host `A.init` UNSAT execution for ANY `cert : LinkedCert ... M'`. -/
theorem run_unsat_entry_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB)
    (hfn : A.T.FnSpec cert.host P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0)
    (hbound : maxB ≤ A.maxStack := by omega) :
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
          (cert.bound P.entryFn) (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr cert.host P.entryFn)) :=
  run_unsat_of_fnspec A P cert.host hfn (Nat.le_trans (cert.bound_le_max _) hbound)

/-- Fixed-`tgtB` UNSAT soundness + framing for ANY `cert : LinkedCert ... M'`. -/
theorem solve_bytes_unsat_maxB_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (tgtB : Nat := 2048)
    (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB) (hh : A.T.mach.Host)
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0)
    (hble : maxB ≤ tgtB := by omega)
    (hmax : tgtB + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra tgtB ⋆ R) (A.T.mach.mem s)) :
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
          A.exitFrame s tgtB ⋆ R) (A.T.mach.mem (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  solve_bytes_unsat_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T hfn (Nat.le_trans (cert.bound_le_max _) hble) hmax)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Fixed-`tgtB` answer-only UNSAT soundness for ANY `cert : LinkedCert ... M'`. -/
theorem unsat_correct_maxB_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (tgtB : Nat := 2048)
    (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB) (hh : A.T.mach.Host)
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0)
    (hble : maxB ≤ tgtB := by omega)
    (hmax : tgtB + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra tgtB ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0#64 ∨
          A.retGpr (A.T.mach.data st) = 10#64 ∨
          A.retGpr (A.T.mach.data st) = 20#64) ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  unsat_correct_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T hfn (Nat.le_trans (cert.bound_le_max _) hble) hmax)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Fixed-`tgtB` concrete `Mem 64` UNSAT non-vacuity for ANY `cert : LinkedCert ... M'`. -/
theorem unsat_nonvacuous_maxB_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (tgtB : Nat := 2048)
    (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB) (hh : A.T.mach.Host)
    (hfn : A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0)
    (hble : maxB ≤ tgtB := by omega)
    (hmax : tgtB + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
    (hmstack : tgtB ≤ A.maxStack := by omega) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
        (BitVec.ofNat 64 wlen) fuel ∧
      A.stackPre s ra ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        A.entryFrame s ra tgtB ⋆ R) (A.T.mach.mem s) ∧
      Eventually (A.T.mach.step hh)
        (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  unsat_nonvacuous_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T hfn (Nat.le_trans (cert.bound_le_max _) hble) hmax)
    hmstack

/-- Fixed-`tgtB` closed-host `A.init` UNSAT execution for ANY `cert : LinkedCert ... M'`. -/
theorem run_unsat_maxB_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} {maxB : Nat} (tgtB : Nat := 2048)
    (cert : LinkedCert A.T A.L A.lt A.hcl M' [] [] 0 maxB)
    (hfn : A.T.FnSpec cert.host P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0)
    (hble : maxB ≤ tgtB := by omega)
    (hmax : tgtB + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
    (hmstack : tgtB ≤ A.maxStack := by omega) :
    Eventually (A.T.mach.step cert.host)
      (fun st =>
        A.T.mach.pc st = A.init.ra0 ∧
        A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          A.T.Exit A.init.sp0 tgtB ⋆ emp))
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64]) tgtB
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr cert.host P.entryFn)) :=
  run_unsat_of_fnspec A P cert.host
    (Target.FnSpec.mono_stack A.T hfn (Nat.le_trans (cert.bound_le_max _) hble) hmax)
    hmstack

/-! ## 3. `optInlinePolicy` Bridges & `KissatCertParamCommon` Drop-In Parity -/

private theorem optInlinePolicy_fn_sigs_eq (P : KissatUnsatPkg) :
    (P.mod.optInlinePolicy P.inlPolicy).fns.map Fn.sig = P.mod.fns.map Fn.sig := by
  have h := Module.optInlinePolicy_sigs P.mod P.inlPolicy
  simp only [Module.sigs, Module.optInlinePolicy_externs] at h
  exact List.append_cancel_right h

private theorem entryFn_spec_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64]) (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0 :=
  entryFn_spec_of_cert_moduleOk A P cert (Module.optInlinePolicy_ok P.inlPolicy P.moduleOk)
    (optInlinePolicy_fn_sigs_eq P) has hrs hh k₀ hc hu

private theorem entryFn_spec_of_compile (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds) (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64]) b 0 :=
  entryFn_spec_of_compile_mod A P (Module.optInlinePolicy_ok P.inlPolicy P.moduleOk)
    (optInlinePolicy_fn_sigs_eq P) has hrs hints code bounds hcm hb hh k₀ hc hu

/-- Whole-module `Defined ∧ FnSpec` over `LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`
(exact `cert.bound`). -/
theorem module_fnspec_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns) (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧
      A.T.FnSpec hh f.name (P.env f.name f.as f.rs) (cert.bound f.name) 0 :=
  cert.fnSpec_noExit_of_legalSigAll_optInlinePolicy hh P.env k₀ hc hu
    P.moduleOk hleg hf (P.noExit f hf)

/-- Whole-module `Defined ∧ FnSpec` over `LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`
(fixed `2048B`). -/
theorem module_fnspec_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧ A.T.FnSpec hh f.name (P.env f.name f.as f.rs) 2048 0 :=
  have ⟨hdef, hfn⟩ := module_fnspec_of_abi A P cert hleg hh k₀ hc hu hf
  ⟨hdef, Target.FnSpec.mono_stack A.T hfn (cert.bound_le_max f.name) hmax⟩

/-- Whole-module `Defined ∧ FnSpec` over raw `compileModuleOptInlinePolicy` (exact bound `b`). -/
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

/-- Whole-module `Defined ∧ FnSpec` over raw `compileModuleOptInlinePolicy` (fixed `maxB`). -/
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

/-! ### `LegalSigAll`-Parameterized `LinkedCert` UNSAT Combinators -/

/-- UNSAT soundness + framing over `LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`
using `LegalSigAll`. -/
theorem solve_bytes_unsat_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns) (hh : A.T.mach.Host) (k₀ : Nat)
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
  have ⟨has, hrs⟩ := hleg P.entryFn_fn P.entry_mem
  solve_bytes_unsat_entry_of_cert A P cert hh
    (entryFn_spec_of_abi A P cert (P.entryFn_sig.2.1 ▸ has) (P.entryFn_sig.2.2 ▸ hrs) hh k₀ hc hu)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Answer-only UNSAT soundness over `LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`
using `LegalSigAll`. -/
theorem unsat_correct_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns) (hh : A.T.mach.Host) (k₀ : Nat)
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

/-- Concrete `Mem 64` UNSAT non-vacuity over `LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`
using `LegalSigAll`. -/
theorem unsat_nonvacuous_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns) (hh : A.T.mach.Host) (k₀ : Nat)
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
  have ⟨has, hrs⟩ := hleg P.entryFn_fn P.entry_mem
  unsat_nonvacuous_entry_of_cert A P cert hh
    (entryFn_spec_of_abi A P cert (P.entryFn_sig.2.1 ▸ has) (P.entryFn_sig.2.2 ▸ hrs) hh k₀ hc hu)
    A.maxStack_ge

/-- Closed concrete-host `A.init` UNSAT execution on `cert.host` using `LegalSigAll`. -/
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
          (cert.bound P.entryFn) (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr cert.host P.entryFn)) :=
  have ⟨has, hrs⟩ := hleg P.entryFn_fn P.entry_mem
  run_unsat_entry_of_cert A P cert
    (entryFn_spec_of_abi A P cert (P.entryFn_sig.2.1 ▸ has) (P.entryFn_sig.2.2 ▸ hrs)
      cert.host 0 cert.code_infix_host cert.labelsUnique)
    A.maxStack_ge

/-! ### Exact-Bound & Fixed-`2048` `LinkedCert` Entry Combinators -/

/-- Exact-bound UNSAT soundness + framing over
`LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`. -/
theorem solve_bytes_unsat_entry_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64]) (hh : A.T.mach.Host) (k₀ : Nat)
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
  solve_bytes_unsat_entry_of_cert A P cert hh (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Exact-bound answer-only UNSAT soundness over
`LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`. -/
theorem unsat_correct_entry_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64]) (hh : A.T.mach.Host) (k₀ : Nat)
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
  unsat_correct_entry_of_cert A P cert hh (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Exact-bound concrete `Mem 64` UNSAT non-vacuity over
`LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`. -/
theorem unsat_nonvacuous_entry_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64]) (hh : A.T.mach.Host) (k₀ : Nat)
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
  unsat_nonvacuous_entry_of_cert A P cert hh (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu)
    A.maxStack_ge

/-- Exact-bound closed-host `A.init` UNSAT execution on `cert.host`. -/
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
          (cert.bound P.entryFn) (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr cert.host P.entryFn)) :=
  run_unsat_entry_of_cert A P cert
    (entryFn_spec_of_abi A P cert has hrs cert.host 0 cert.code_infix_host cert.labelsUnique)
    A.maxStack_ge

/-- Fixed-`2048B` UNSAT soundness + framing over
`LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`. -/
theorem solve_bytes_unsat_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide) (hh : A.T.mach.Host) (k₀ : Nat)
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
  solve_bytes_unsat_maxB_of_cert A P 2048 cert hh
    (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu) (Nat.le_refl _) hmax
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Fixed-`2048B` answer-only UNSAT soundness over
`LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`. -/
theorem unsat_correct_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide) (hh : A.T.mach.Host) (k₀ : Nat)
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
  unsat_correct_maxB_of_cert A P 2048 cert hh
    (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu) (Nat.le_refl _) hmax
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Fixed-`2048B` concrete `Mem 64` UNSAT non-vacuity over
`LinkedCert ... (P.mod.optInlinePolicy P.inlPolicy)`. -/
theorem unsat_nonvacuous_maxB_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hmax : 2048 + A.T.frame.raBytes ≤ 2 ^ 64 := by decide) (hh : A.T.mach.Host) (k₀ : Nat)
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
  unsat_nonvacuous_maxB_of_cert A P 2048 cert hh
    (entryFn_spec_of_abi A P cert has hrs hh k₀ hc hu) (Nat.le_refl _) hmax A.maxStack_ge

/-- Fixed-`2048B` closed-host `A.init` UNSAT execution on `cert.host`. -/
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
  run_unsat_maxB_of_cert A P 2048 cert
    (entryFn_spec_of_abi A P cert has hrs cert.host 0 cert.code_infix_host cert.labelsUnique)
    (Nat.le_refl _) hmax A.maxStack_ge

/-! ### Raw `compileModule` & `compileModuleOptInlinePolicy` Combinators -/

/-- Exact-bound raw `compileModule` UNSAT soundness + framing for ANY `M'` refining `P.mod`. -/
theorem solve_bytes_unsat_of_compile_mod (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds) (hh : A.T.mach.Host) (k₀ : Nat)
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
    (entryFn_spec_of_compile_mod A P hM' hsigs has hrs hints code bounds hcm hb hh k₀ hc hu)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Exact-bound raw `compileModule` answer-only UNSAT soundness for ANY `M'` refining `P.mod`. -/
theorem unsat_correct_of_compile_mod (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds) (hh : A.T.mach.Host) (k₀ : Nat)
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
  unsat_correct_of_fnspec A P hh
    (entryFn_spec_of_compile_mod A P hM' hsigs has hrs hints code bounds hcm hb hh k₀ hc hu)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Exact-bound raw `compileModule` concrete `Mem 64` UNSAT non-vacuity for ANY `M'`. -/
theorem unsat_nonvacuous_of_compile_mod (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
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
    (entryFn_spec_of_compile_mod A P hM' hsigs has hrs hints code bounds hcm hb hh k₀ hc hu)
    hb_stack

/-- Fixed-`maxB` raw `compileModule` UNSAT soundness + framing for ANY `M'` refining `P.mod`. -/
theorem solve_bytes_unsat_of_compile_mod_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
    {b maxB : Nat} (hb : (P.entryFn, b) ∈ bounds) (hble : b ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64) (hh : A.T.mach.Host) (k₀ : Nat)
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
      (entryFn_spec_of_compile_mod A P hM' hsigs has hrs hints code bounds hcm hb hh k₀ hc hu)
      hble hmax)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Fixed-`maxB` raw `compileModule` answer-only UNSAT soundness for ANY `M'`. -/
theorem unsat_correct_of_compile_mod_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
    {b maxB : Nat} (hb : (P.entryFn, b) ∈ bounds) (hble : b ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64) (hh : A.T.mach.Host) (k₀ : Nat)
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
  unsat_correct_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T
      (entryFn_spec_of_compile_mod A P hM' hsigs has hrs hints code bounds hcm hb hh k₀ hc hu)
      hble hmax)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Fixed-`maxB` raw `compileModule` concrete `Mem 64` UNSAT non-vacuity for ANY `M'`. -/
theorem unsat_nonvacuous_of_compile_mod_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
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
      (entryFn_spec_of_compile_mod A P hM' hsigs has hrs hints code bounds hcm hb hh k₀ hc hu)
      hble hmax)
    hmstack

/-- Fixed-`maxB` raw `compileModule` closed `A.init` UNSAT execution for ANY `M'`. -/
theorem run_unsat_of_compile_mod_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    {M' : Module} (hM' : ModuleOk P.env M') (hsigs : M'.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0 M'.fns hints =
      .ok (code, bounds))
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
      (entryFn_spec_of_compile_mod A P hM' hsigs has hrs hints code bounds hcm hb hh k₀ hc hu)
      hble hmax)
    hmstack

/-- Exact-bound raw `compileModuleOptInlinePolicy` UNSAT soundness + framing. -/
theorem solve_bytes_unsat_of_compile (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds) (hh : A.T.mach.Host) (k₀ : Nat)
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

/-- Exact-bound raw `compileModuleOptInlinePolicy` answer-only UNSAT soundness. -/
theorem unsat_correct_of_compile (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b : Nat} (hb : (P.entryFn, b) ∈ bounds) (hh : A.T.mach.Host) (k₀ : Nat)
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
  unsat_correct_of_fnspec A P hh
    (entryFn_spec_of_compile A P has hrs hints code bounds hcm hb hh k₀ hc hu)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Exact-bound raw `compileModuleOptInlinePolicy` concrete `Mem 64` UNSAT non-vacuity. -/
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

/-- Fixed-`maxB` raw `compileModuleOptInlinePolicy` UNSAT soundness + framing. -/
theorem solve_bytes_unsat_of_compile_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b maxB : Nat} (hb : (P.entryFn, b) ∈ bounds) (hble : b ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64) (hh : A.T.mach.Host) (k₀ : Nat)
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

/-- Fixed-`maxB` raw `compileModuleOptInlinePolicy` answer-only UNSAT soundness. -/
theorem unsat_correct_of_compile_maxB (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      P.mod hints P.inlPolicy = .ok (code, bounds))
    {b maxB : Nat} (hb : (P.entryFn, b) ∈ bounds) (hble : b ≤ maxB)
    (hmax : maxB + A.T.frame.raBytes ≤ 2 ^ 64) (hh : A.T.mach.Host) (k₀ : Nat)
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
  unsat_correct_of_fnspec A P hh
    (Target.FnSpec.mono_stack A.T
      (entryFn_spec_of_compile A P has hrs hints code bounds hcm hb hh k₀ hc hu) hble hmax)
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hargs hsp hmem

/-- Fixed-`maxB` raw `compileModuleOptInlinePolicy` concrete `Mem 64` UNSAT non-vacuity. -/
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

/-- Fixed-`maxB` raw `compileModuleOptInlinePolicy` closed `A.init` UNSAT execution. -/
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

end LeanQbe.T.Examples.Kissat.Build.Common.CertParamCommon
