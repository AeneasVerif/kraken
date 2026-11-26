module

public import LeanQbe.T.Amd64.LcnfC0FullCertX64S1
public import LeanQbe.T.Amd64.LcnfC0FullCertX64S2
public import LeanQbe.T.Amd64.LcnfC0FullCertX64S3
public import LeanQbe.T.Amd64.LcnfC0FullCertX64S4
public import LeanQbe.T.Amd64.LcnfC0FullCertX64S5
public import LeanQbe.T.Amd64.LcnfC0FullCertX64S6
public import LeanQbe.T.Amd64.LcnfC0FullCertX64S7
public import LeanQbe.T.LeanLCNF.LcnfC0FullProof
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.AbiLemmas

/-!
# Whole-Module SysV x64 `LinkedCert` & `FnSpec` Bridge for `rtC0CoreMod` (86 Functions)

Combines the seven verified x64 compilation slices (`LcnfC0FullCertX64S1`..`S7`) via balanced
`LinkedCert.append` into `rtC0CoreCert` over the complete 86-function pure-C0 LCNF runtime
(`rtC0CoreMod`, `0` externs, `exits = ["lcnf_panic"]`, `nX = 64`), and bridges
`rtC0CoreMod_moduleOk` (`rtC0CoreEnv`) to whole-module `x64Target.Defined` + `x64Target.FnSpec`
and concrete machine-level runtime `FnSpec` theorems.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-! ## 1. Balanced `LinkedCert.append` Assembly (`rtC0CoreCert`) -/

private theorem drop_take_add {l : List Fn} {a b c : Nat} :
    (l.drop a).take (b + c) = (l.drop a).take b ++ (l.drop (a + b)).take c := by
  have h := List.take_add (l := l.drop a) (i := b) (j := c)
  rwa [List.drop_drop] at h

private theorem drop_take_drop {l : List Fn} {a b : Nat} :
    l.drop a = (l.drop a).take b ++ l.drop (a + b) := by
  have h := (List.take_append_drop b (l.drop a)).symm
  rwa [List.drop_drop] at h

/-- Complete kernel-checked SysV x64 compilation certificate for all `86` functions of
`rtC0CoreMod` (`0` externs, `exits = ["lcnf_panic"]`, `nX = 64`). -/
@[expose] noncomputable def rtC0CoreCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      rtC0CoreMod [] rtExitSyms 64 2048 :=
  let mod12 : Module := { fns := rtC0CoreFlatMod.fns.take 30, exits := rtExitSyms }
  let mod34 : Module := { fns := (rtC0CoreFlatMod.fns.drop 30).take 9, exits := rtExitSyms }
  let mod14 : Module := { fns := rtC0CoreFlatMod.fns.take 39, exits := rtExitSyms }
  let mod56 : Module := { fns := (rtC0CoreFlatMod.fns.drop 39).take 39, exits := rtExitSyms }
  let mod57 : Module := { fns := rtC0CoreFlatMod.fns.drop 39, exits := rtExitSyms }
  let cert12 : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      mod12 [] rtExitSyms 64 2048 :=
    rtC0CertS1.append rtC0CertS2
      (by exact List.take_add (l := rtC0CoreFlatMod.fns) (i := 15) (j := 15))
      (by t_kernel_rfl)
  let cert34 : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      mod34 (rtC0ExtBefore 30) rtExitSyms 64 2048 :=
    rtC0CertS3.append rtC0CertS4
      (by exact drop_take_add (l := rtC0CoreFlatMod.fns) (a := 30) (b := 5) (c := 4))
      (by t_kernel_rfl)
  let cert14 : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      mod14 [] rtExitSyms 64 2048 :=
    cert12.append cert34
      (by exact List.take_add (l := rtC0CoreFlatMod.fns) (i := 30) (j := 9))
      (by t_kernel_rfl)
  let cert56 : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      mod56 (rtC0ExtBefore 39) rtExitSyms 64 2048 :=
    rtC0CertS5.append rtC0CertS6
      (by exact drop_take_add (l := rtC0CoreFlatMod.fns) (a := 39) (b := 22) (c := 17))
      (by t_kernel_rfl)
  let cert57 : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      mod57 (rtC0ExtBefore 39) rtExitSyms 64 2048 :=
    cert56.append rtC0CertS7
      (by exact drop_take_drop (l := rtC0CoreFlatMod.fns) (a := 39) (b := 39))
      (by t_kernel_rfl)
  cert14.append cert57
    (by
      exact rtC0CoreFlatMod_fns_eq.symm.trans
        (List.take_append_drop 39 rtC0CoreFlatMod.fns).symm)
    (by t_kernel_rfl)

/-! ## 2. Legalization, Stack-Bound, and Metadata Checks -/

private theorem rtC0CoreMod_legalSig_check :
    checkLegalSigAll x64LegalTarget rtC0CoreMod.fns = true := by
  t_kernel_rfl

/-- Every function signature in `rtC0CoreMod.fns` (`86` fns) is fixed by `x64LegalTarget.legalSig`.
-/
theorem rtC0CoreMod_legalSig : LegalSigAll x64LegalTarget rtC0CoreMod.fns :=
  legalSigAll_of_check rtC0CoreMod_legalSig_check

/-- Kernel check that `rtC0CoreCert.bounds` covers all `86` runtime functions. -/
theorem rtC0CoreCert_bounds_len : rtC0CoreCert.bounds.length = 86 :=
  rtC0CoreCert.bounds_length.trans rtC0CoreFns_length

/-- Kernel check that every runtime stack bound in `rtC0CoreCert` is at most `272` bytes. -/
theorem rtC0CoreCert_bounds_le :
    rtC0CoreCert.bounds.all (fun p => Nat.ble p.2 272) = true := by
  t_kernel_rfl

/-! ## 3. Whole-Module `x64Target.Defined` & `x64Target.FnSpec` Bridge (`rtC0CoreMod_moduleOk`) -/

private theorem rtC0CoreMod_hwp :
    ∀ fn ∈ rtC0CoreMod.fns, ∀ xs m Q X,
      rtC0CoreEnv fn.name fn.as fn.rs xs m Q X → Func.wp rtC0CoreEnv fn.body xs m Q X := by
  intro fn hfn xs m Q X hc
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
  exact (rtC0CoreMod_moduleOk.fnsOk pre fn post hsp).2.2 xs m Q X hc

/-- Whole-module legalized `x64Target.Defined` + `x64Target.FnSpec` across all `86` runtime
functions on `rtC0CoreCert.host` (`nX = 64`), derived from `rtC0CoreMod_moduleOk`. -/
theorem rtC0Core_all_fnSpec {fn : Fn} (hfn : fn ∈ rtC0CoreMod.fns) :
    x64Target.Defined rtC0CoreCert.host fn.name ∧
    x64Target.FnSpec rtC0CoreCert.host fn.name
      (legalEnv x64LegalTarget (Env.ofModule rtC0CoreMod rtC0CoreEnv)
        fn.name (x64LegalTarget.legalSig fn.as) (x64LegalTarget.legalSig fn.rs))
      (rtC0CoreCert.bound fn.name) 64 :=
  rtC0CoreCert.fnSpec_host rtC0CoreEnv rtC0CoreMod_checkAcyclic rtC0CoreMod_fns_wf
    rtC0CoreMod_hwp hfn

/-- Whole-module source-signature `x64Target.Defined` + `x64Target.FnSpec` across all `86` runtime
functions on `rtC0CoreCert.host` (`nX = 64`), bridging `rtC0CoreMod_moduleOk` and
`rtC0CoreMod_legalSig`. -/
theorem rtC0Core_all_fnSpec_src {fn : Fn} (hfn : fn ∈ rtC0CoreMod.fns) :
    x64Target.Defined rtC0CoreCert.host fn.name ∧
    x64Target.FnSpec rtC0CoreCert.host fn.name
      (fun args m Q X => rtC0CoreEnv fn.name fn.as fn.rs args m Q
        (fun g cs xs m' =>
          X g (x64LegalTarget.legalSig cs) (encodeTup x64LegalTarget cs xs) m'))
      (rtC0CoreCert.bound fn.name) 64 := by
  obtain ⟨hdef, hsp⟩ := rtC0Core_all_fnSpec hfn
  obtain ⟨has, hrs⟩ := rtC0CoreMod_legalSig fn hfn
  have hmem : (fn.name, fn.as, fn.rs) ∈ rtC0CoreMod.sigs :=
    List.mem_append_left _ (List.mem_map.mpr ⟨fn, hfn, rfl⟩)
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq has hrs hmem hsp⟩

/-- Index-accessed whole-module source-signature `Defined` + `FnSpec` for all `i < 86`. -/
theorem rtC0Core_fnSpec_src_at_idx {i : Nat} (hi : i < rtC0CoreMod.fns.length) :
    x64Target.Defined rtC0CoreCert.host (rtC0CoreMod.fns[i]).name ∧
    x64Target.FnSpec rtC0CoreCert.host (rtC0CoreMod.fns[i]).name
      (fun args m Q X =>
        rtC0CoreEnv (rtC0CoreMod.fns[i]).name (rtC0CoreMod.fns[i]).as (rtC0CoreMod.fns[i]).rs
          args m Q
          (fun g cs xs m' =>
            X g (x64LegalTarget.legalSig cs) (encodeTup x64LegalTarget cs xs) m'))
      (rtC0CoreCert.bound (rtC0CoreMod.fns[i]).name) 64 :=
  rtC0Core_all_fnSpec_src (List.getElem_mem hi)

/-! ## 4. Concrete Machine-Level Runtime `FnSpec` Theorems -/

private theorem x64_legal_i64_i64 :
    x64LegalTarget.legalSig [i64, i64] = [i64, i64] := by
  decide

/-- Unwrapped machine-level `FnSpec` for `lcnf_alloc` (`[i64, i64] → [i64]`) against
`lcnfAllocRemSpec`. -/
theorem rtC0Core_alloc_fnSpec :
    x64Target.Defined rtC0CoreCert.host "lcnf_alloc" ∧
    x64Target.FnSpec rtC0CoreCert.host "lcnf_alloc" lcnfAllocRemSpec
      (rtC0CoreCert.bound "lcnf_alloc") 64 :=
  let h := rtC0Core_fnSpec_src_at_idx (i := 0) (by decide)
  ⟨h.1, Target.FnSpec.of_spec x64Target h.2 fun _ _ _ _ hs => rtC0CoreEnv_lcnf_alloc hs⟩

/-- Combined machine-level `FnSpec` bundle for `lcnf_dec_ref_cold`, `lcnf_clo_under`, and
`lcnf_ba_empty` on `rtC0CoreCert.host`. -/
theorem rtC0Core_extra_fnSpecs :
    (x64Target.Defined rtC0CoreCert.host "lcnf_dec_ref_cold" ∧
      x64Target.FnSpec rtC0CoreCert.host "lcnf_dec_ref_cold" lcnfDecRefColdSpec
        (rtC0CoreCert.bound "lcnf_dec_ref_cold") 64) ∧
    (x64Target.Defined rtC0CoreCert.host "lcnf_clo_under" ∧
      x64Target.FnSpec rtC0CoreCert.host "lcnf_clo_under" lcnfCloUnderSpec
        (rtC0CoreCert.bound "lcnf_clo_under") 64) ∧
    (x64Target.Defined rtC0CoreCert.host "lcnf_ba_empty" ∧
      x64Target.FnSpec rtC0CoreCert.host "lcnf_ba_empty"
        (fun args m Q X => rtC0CoreEnv "lcnf_ba_empty" [i64] [i64] args m Q
          (fun g cs xs m' =>
            X g (x64LegalTarget.legalSig cs) (encodeTup x64LegalTarget cs xs) m'))
        (rtC0CoreCert.bound "lcnf_ba_empty") 64) := by
  have hdec := rtC0Core_fnSpec_src_at_idx (i := 2) (by decide)
  have hclo := rtC0Core_fnSpec_src_at_idx (i := 4) (by decide)
  have hba := rtC0Core_fnSpec_src_at_idx (i := 46) (by decide)
  refine ⟨⟨hdec.1, Target.FnSpec.of_spec x64Target hdec.2
      fun _ _ _ _ h => rtC0CoreEnv_lcnf_dec_ref_cold h⟩,
    ⟨hclo.1, Target.FnSpec.of_spec x64Target hclo.2
      fun _ _ _ _ h => rtC0CoreEnv_lcnf_clo_under h⟩,
    hba⟩

/-- Unwrapped machine-level `FnSpec` for `lcnf_nat_slow` (`[i64, i64, i64, i64] → [i64]`)
against `lcnfNatSlowSpec`. -/
theorem rtC0Core_nat_slow_fnSpec :
    x64Target.Defined rtC0CoreCert.host "lcnf_nat_slow" ∧
    x64Target.FnSpec rtC0CoreCert.host "lcnf_nat_slow" lcnfNatSlowSpec
      (rtC0CoreCert.bound "lcnf_nat_slow") 64 :=
  let h := rtC0Core_fnSpec_src_at_idx (i := 34) (by decide)
  ⟨h.1, Target.FnSpec.of_spec x64Target h.2 fun _ _ _ _ hs =>
     rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_nat_slow hs)⟩

/-- Unwrapped machine-level `FnSpec` for `lcnf_nat_to_str` (`[i64, i64] → [i64]`) against
`lcnfNatToStrSpec` (translating `lcnf_panic` exit continuations via `legal_xpost_of_legalSig_eq`).
-/
theorem rtC0Core_nat_to_str_fnSpec :
    x64Target.Defined rtC0CoreCert.host "lcnf_nat_to_str" ∧
    x64Target.FnSpec rtC0CoreCert.host "lcnf_nat_to_str" lcnfNatToStrSpec
      (rtC0CoreCert.bound "lcnf_nat_to_str") 64 := by
  have hsrc := rtC0Core_fnSpec_src_at_idx (i := 85) (by decide)
  refine ⟨hsrc.1, Target.FnSpec.of_spec x64Target hsrc.2 ?_⟩
  rintro ⟨rt, n, ⟨⟩⟩ m Q X ⟨st, val, objs, R, hIn, hwf, hm, hrest⟩
  refine rtR2bEnv_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2bEnv_lcnf_nat_to_str ?_)
  refine ⟨st, val, objs, R, hIn, hwf, hm, ?_⟩
  by_cases hsc : (n &&& 1#64) ≠ 0#64
  · simp only [eq_true hsc, ↓reduceIte] at hrest ⊢
    exact hrest
  · simp only [eq_false hsc, ↓reduceIte] at hrest ⊢
    rcases hrest with ⟨nObj, hmem, haddr, hcanon, hrc, hcn⟩
    refine ⟨nObj, hmem, haddr, hcanon, hrc, ?_⟩
    by_cases hzero : trimZeroLimbsLen nObj.limbs nObj.arrSize = 0
    · simp only [eq_true hzero, ↓reduceIte] at hcn ⊢
      exact hcn
    · simp only [eq_false hzero, ↓reduceIte] at hcn ⊢
      by_cases hoob : mpzMaxLimbsNat < trimZeroLimbsLen nObj.limbs nObj.arrSize
      · simp only [eq_true hoob, ↓reduceIte] at hcn ⊢
        exact legal_xpost_of_legalSig_eq x64_legal_i64_i64 hcn
      · simp only [eq_false hoob, ↓reduceIte] at hcn ⊢
        exact hcn

end LeanQbe.T.Amd64
