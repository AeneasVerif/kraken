module

public import LeanQbe.T.Arm64.LcnfC0FullCertArm64S1
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64S2
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64S3
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64S4
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64S5
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64S6
public import LeanQbe.T.Arm64.LcnfC0FullCertArm64S7
public import LeanQbe.T.LeanLCNF.LcnfC0FullProof
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.AbiLemmas

/-!
# Whole-Module AAPCS64 Arm64 `LinkedCert` & `FnSpec` Bridge for `rtC0CoreMod` (86 Functions)

Combines the seven verified AArch64 compilation slices (`LcnfC0FullCertArm64S1`..`S7`) via
balanced `LinkedCert.append` into `rtC0CoreArm64Cert` over the complete 86-function pure-C0 LCNF
runtime (`rtC0CoreMod`, `0` externs, `exits = ["lcnf_panic"]`, `nX = 64`), and bridges
`rtC0CoreMod_moduleOk` (`rtC0CoreEnv`) to whole-module `armTarget.Defined` + `armTarget.FnSpec`
and concrete machine-level runtime `FnSpec` theorems.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-! ## 1. Balanced `LinkedCert.append` Assembly (`rtC0CoreArm64Cert`) -/

private theorem arm_drop_take_add {l : List Fn} {a b c : Nat} :
    (l.drop a).take (b + c) = (l.drop a).take b ++ (l.drop (a + b)).take c := by
  have h := List.take_add (l := l.drop a) (i := b) (j := c)
  rwa [List.drop_drop] at h

private theorem arm_drop_take_drop {l : List Fn} {a b : Nat} :
    l.drop a = (l.drop a).take b ++ l.drop (a + b) := by
  have h := (List.take_append_drop b (l.drop a)).symm
  rwa [List.drop_drop] at h

/-- Complete kernel-checked AAPCS64 Arm64 compilation certificate for all `86` functions of
`rtC0CoreMod` (`0` externs, `exits = ["lcnf_panic"]`, `nX = 64`). -/
@[expose] noncomputable def rtC0CoreArm64Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      rtC0CoreMod [] rtExitSyms 64 2048 :=
  let mod12 : Module := { fns := rtC0CoreMod.fns.take 30, exits := rtExitSyms }
  let mod34 : Module := { fns := (rtC0CoreMod.fns.drop 30).take 9, exits := rtExitSyms }
  let mod14 : Module := { fns := rtC0CoreMod.fns.take 39, exits := rtExitSyms }
  let mod56 : Module := { fns := (rtC0CoreMod.fns.drop 39).take 39, exits := rtExitSyms }
  let mod57 : Module := { fns := rtC0CoreMod.fns.drop 39, exits := rtExitSyms }
  let cert12 : LinkedCert armTarget armLayout armLegalTarget armLabelClean
      mod12 [] rtExitSyms 64 2048 :=
    rtC0Arm64CertS1.append rtC0Arm64CertS2
      (by exact List.take_add (l := rtC0CoreMod.fns) (i := 15) (j := 15))
      (by t_kernel_rfl)
  let cert34 : LinkedCert armTarget armLayout armLegalTarget armLabelClean
      mod34 (rtC0Arm64ExtBefore 30) rtExitSyms 64 2048 :=
    rtC0Arm64CertS3.append rtC0Arm64CertS4
      (by exact arm_drop_take_add (l := rtC0CoreMod.fns) (a := 30) (b := 5) (c := 4))
      (by t_kernel_rfl)
  let cert14 : LinkedCert armTarget armLayout armLegalTarget armLabelClean
      mod14 [] rtExitSyms 64 2048 :=
    cert12.append cert34
      (by exact List.take_add (l := rtC0CoreMod.fns) (i := 30) (j := 9))
      (by t_kernel_rfl)
  let cert56 : LinkedCert armTarget armLayout armLegalTarget armLabelClean
      mod56 (rtC0Arm64ExtBefore 39) rtExitSyms 64 2048 :=
    rtC0Arm64CertS5.append rtC0Arm64CertS6
      (by exact arm_drop_take_add (l := rtC0CoreMod.fns) (a := 39) (b := 22) (c := 17))
      (by t_kernel_rfl)
  let cert57 : LinkedCert armTarget armLayout armLegalTarget armLabelClean
      mod57 (rtC0Arm64ExtBefore 39) rtExitSyms 64 2048 :=
    cert56.append rtC0Arm64CertS7
      (by exact arm_drop_take_drop (l := rtC0CoreMod.fns) (a := 39) (b := 39))
      (by t_kernel_rfl)
  cert14.append cert57
    (by exact (List.take_append_drop 39 rtC0CoreMod.fns).symm)
    (by t_kernel_rfl)

/-! ## 2. Legalization, Stack-Bound, and Metadata Checks -/

private theorem rtC0CoreMod_arm64_legalSig_check :
    checkLegalSigAll armLegalTarget rtC0CoreMod.fns = true := by
  t_kernel_rfl

/-- Every function signature in `rtC0CoreMod.fns` (`86` fns) is fixed by
`armLegalTarget.legalSig`. -/
theorem rtC0CoreMod_arm64_legalSig : LegalSigAll armLegalTarget rtC0CoreMod.fns :=
  legalSigAll_of_check rtC0CoreMod_arm64_legalSig_check

/-- Kernel check that `rtC0CoreArm64Cert.bounds` covers all `86` runtime functions. -/
theorem rtC0CoreArm64Cert_bounds_len : rtC0CoreArm64Cert.bounds.length = 86 :=
  rtC0CoreArm64Cert.bounds_length.trans rtC0CoreFns_length

/-- Kernel check that every runtime stack bound in `rtC0CoreArm64Cert` is at most `272` bytes. -/
theorem rtC0CoreArm64Cert_bounds_le :
    rtC0CoreArm64Cert.bounds.all (fun p => Nat.ble p.2 272) = true := by
  t_kernel_rfl

/-! ## 3. Whole-Module `armTarget.Defined` & `armTarget.FnSpec` Bridge -/

private theorem rtC0CoreMod_arm64_hwp :
    ∀ fn ∈ rtC0CoreMod.fns, ∀ xs m Q X,
      rtC0CoreEnv fn.name fn.as fn.rs xs m Q X → Func.wp rtC0CoreEnv fn.body xs m Q X := by
  intro fn hfn xs m Q X hc
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
  exact (rtC0CoreMod_moduleOk.fnsOk pre fn post hsp).2.2 xs m Q X hc

/-- Whole-module legalized `armTarget.Defined` + `armTarget.FnSpec` across all `86` runtime
functions on `rtC0CoreArm64Cert.host` (`nX = 64`), derived from `rtC0CoreMod_moduleOk`. -/
theorem rtC0CoreArm64_all_fnSpec {fn : Fn} (hfn : fn ∈ rtC0CoreMod.fns) :
    armTarget.Defined rtC0CoreArm64Cert.host fn.name ∧
    armTarget.FnSpec rtC0CoreArm64Cert.host fn.name
      (legalEnv armLegalTarget (Env.ofModule rtC0CoreMod rtC0CoreEnv)
        fn.name (armLegalTarget.legalSig fn.as) (armLegalTarget.legalSig fn.rs))
      (rtC0CoreArm64Cert.bound fn.name) 64 :=
  rtC0CoreArm64Cert.fnSpec_host rtC0CoreEnv rtC0CoreMod_checkAcyclic rtC0CoreMod_fns_wf
    rtC0CoreMod_arm64_hwp hfn

/-- Whole-module source-signature `armTarget.Defined` + `armTarget.FnSpec` across all `86`
runtime functions on `rtC0CoreArm64Cert.host` (`nX = 64`), bridging `rtC0CoreMod_moduleOk` and
`rtC0CoreMod_arm64_legalSig`. -/
theorem rtC0CoreArm64_all_fnSpec_src {fn : Fn} (hfn : fn ∈ rtC0CoreMod.fns) :
    armTarget.Defined rtC0CoreArm64Cert.host fn.name ∧
    armTarget.FnSpec rtC0CoreArm64Cert.host fn.name
      (fun args m Q X => rtC0CoreEnv fn.name fn.as fn.rs args m Q
        (fun g cs xs m' =>
          X g (armLegalTarget.legalSig cs) (encodeTup armLegalTarget cs xs) m'))
      (rtC0CoreArm64Cert.bound fn.name) 64 := by
  obtain ⟨hdef, hsp⟩ := rtC0CoreArm64_all_fnSpec hfn
  obtain ⟨has, hrs⟩ := rtC0CoreMod_arm64_legalSig fn hfn
  have hmem : (fn.name, fn.as, fn.rs) ∈ rtC0CoreMod.sigs :=
    List.mem_append_left _ (List.mem_map.mpr ⟨fn, hfn, rfl⟩)
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq has hrs hmem hsp⟩

/-- Index-accessed whole-module source-signature `Defined` + `FnSpec` for all `i < 86`. -/
theorem rtC0CoreArm64_fnSpec_src_at_idx {i : Nat} (hi : i < rtC0CoreMod.fns.length) :
    armTarget.Defined rtC0CoreArm64Cert.host (rtC0CoreMod.fns[i]).name ∧
    armTarget.FnSpec rtC0CoreArm64Cert.host (rtC0CoreMod.fns[i]).name
      (fun args m Q X =>
        rtC0CoreEnv (rtC0CoreMod.fns[i]).name (rtC0CoreMod.fns[i]).as (rtC0CoreMod.fns[i]).rs
          args m Q
          (fun g cs xs m' =>
            X g (armLegalTarget.legalSig cs) (encodeTup armLegalTarget cs xs) m'))
      (rtC0CoreArm64Cert.bound (rtC0CoreMod.fns[i]).name) 64 :=
  rtC0CoreArm64_all_fnSpec_src (List.getElem_mem hi)

/-! ## 4. Concrete Machine-Level Runtime `FnSpec` Theorems -/

private theorem arm64_legal_i64_i64 :
    armLegalTarget.legalSig [i64, i64] = [i64, i64] := by
  decide

/-- Unwrapped machine-level `FnSpec` for `lcnf_alloc` (`[i64, i64] → [i64]`) against
`lcnfAllocRemSpec`. -/
theorem rtC0CoreArm64_alloc_fnSpec :
    armTarget.Defined rtC0CoreArm64Cert.host "lcnf_alloc" ∧
    armTarget.FnSpec rtC0CoreArm64Cert.host "lcnf_alloc" lcnfAllocRemSpec
      (rtC0CoreArm64Cert.bound "lcnf_alloc") 64 :=
  let h := rtC0CoreArm64_fnSpec_src_at_idx (i := 0) (by decide)
  ⟨h.1, Target.FnSpec.of_spec armTarget h.2 fun _ _ _ _ hs => rtC0CoreEnv_lcnf_alloc hs⟩

/-- Combined machine-level `FnSpec` bundle for `lcnf_dec_ref_cold`, `lcnf_clo_under`, and
`lcnf_ba_empty` on `rtC0CoreArm64Cert.host`. -/
theorem rtC0CoreArm64_extra_fnSpecs :
    (armTarget.Defined rtC0CoreArm64Cert.host "lcnf_dec_ref_cold" ∧
      armTarget.FnSpec rtC0CoreArm64Cert.host "lcnf_dec_ref_cold" lcnfDecRefColdSpec
        (rtC0CoreArm64Cert.bound "lcnf_dec_ref_cold") 64) ∧
    (armTarget.Defined rtC0CoreArm64Cert.host "lcnf_clo_under" ∧
      armTarget.FnSpec rtC0CoreArm64Cert.host "lcnf_clo_under" lcnfCloUnderSpec
        (rtC0CoreArm64Cert.bound "lcnf_clo_under") 64) ∧
    (armTarget.Defined rtC0CoreArm64Cert.host "lcnf_ba_empty" ∧
      armTarget.FnSpec rtC0CoreArm64Cert.host "lcnf_ba_empty"
        (fun args m Q X => rtC0CoreEnv "lcnf_ba_empty" [i64] [i64] args m Q
          (fun g cs xs m' =>
            X g (armLegalTarget.legalSig cs) (encodeTup armLegalTarget cs xs) m'))
        (rtC0CoreArm64Cert.bound "lcnf_ba_empty") 64) := by
  have hdec := rtC0CoreArm64_fnSpec_src_at_idx (i := 2) (by decide)
  have hclo := rtC0CoreArm64_fnSpec_src_at_idx (i := 4) (by decide)
  have hba := rtC0CoreArm64_fnSpec_src_at_idx (i := 46) (by decide)
  refine ⟨⟨hdec.1, Target.FnSpec.of_spec armTarget hdec.2
      fun _ _ _ _ h => rtC0CoreEnv_lcnf_dec_ref_cold h⟩,
    ⟨hclo.1, Target.FnSpec.of_spec armTarget hclo.2
      fun _ _ _ _ h => rtC0CoreEnv_lcnf_clo_under h⟩,
    hba⟩

/-- Unwrapped machine-level `FnSpec` for `lcnf_nat_slow` (`[i64, i64, i64, i64] → [i64]`)
against `lcnfNatSlowSpec`. -/
theorem rtC0CoreArm64_nat_slow_fnSpec :
    armTarget.Defined rtC0CoreArm64Cert.host "lcnf_nat_slow" ∧
    armTarget.FnSpec rtC0CoreArm64Cert.host "lcnf_nat_slow" lcnfNatSlowSpec
      (rtC0CoreArm64Cert.bound "lcnf_nat_slow") 64 :=
  let h := rtC0CoreArm64_fnSpec_src_at_idx (i := 34) (by decide)
  ⟨h.1, Target.FnSpec.of_spec armTarget h.2 fun _ _ _ _ hs =>
     rtR1Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR1Env_lcnf_nat_slow hs)⟩

/-- Unwrapped machine-level `FnSpec` for `lcnf_nat_to_str` (`[i64, i64] → [i64]`) against
`lcnfNatToStrSpec` (translating `lcnf_panic` exit continuations via `legal_xpost_of_legalSig_eq`).
-/
theorem rtC0CoreArm64_nat_to_str_fnSpec :
    armTarget.Defined rtC0CoreArm64Cert.host "lcnf_nat_to_str" ∧
    armTarget.FnSpec rtC0CoreArm64Cert.host "lcnf_nat_to_str" lcnfNatToStrSpec
      (rtC0CoreArm64Cert.bound "lcnf_nat_to_str") 64 := by
  have hsrc := rtC0CoreArm64_fnSpec_src_at_idx (i := 85) (by decide)
  refine ⟨hsrc.1, Target.FnSpec.of_spec armTarget hsrc.2 ?_⟩
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
        exact legal_xpost_of_legalSig_eq arm64_legal_i64_i64 hcn
      · simp only [eq_false hoob, ↓reduceIte] at hcn ⊢
        exact hcn

end LeanQbe.T.Arm64
