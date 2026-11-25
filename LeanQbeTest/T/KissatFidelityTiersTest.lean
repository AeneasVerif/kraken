/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTiers
public import LeanQbe.T.Examples.Kissat.FullFidelityTiersProof
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullFidelityTiers
meta import LeanQbe.T.Examples.Kissat.FullFidelityTiersProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for `FullFidelityTiers`

1. Executable `#guard` checks on `fidTiersRepls` (`2` fns), `fidTiersStandModule` (`2` fns, `3`
   externs, `0` exits), `fidTiersModule` (`469` fns, `0` externs, `0` exits), `PrintCpp`,
   `PrintQbe`, and 4-ISA `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Restated headline theorems for `fidSyncLegacyTiersFn` (`m6HdrW2aSpec [] []`), `fidAnalyzeRsnFn`
   (`m6AnalyzeRsnHdrSpec`), `EnvSpec` / `TableImpl` / `ModuleOk` against `fidTiersSpecs`,
   closed `469/469` `fidTiers_moduleOk`, UNSAT soundness, and concrete `Mem 64` non-vacuity.
3. Single-line `<= 100`c `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityTiersTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.FullFidelityTiers
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & Legalization Checks -/

#guard fidTiersRepls.length == 2
#guard fidTiersSpecs.length == 2
#guard fidTiersSpecs.all SpecEntry.noExit == true
#guard fidTiersSpecs.map (fun e => (e.name, e.as, e.rs)) == fidTiersRepls.map Fn.sig
#guard fidTiersStandModule.checkAcyclic == true
#guard fidTiersStandModule.fns.length == 2
#guard fidTiersStandModule.externs.length == 3
#guard fidTiersStandModule.exits.isEmpty == true
#guard fidTiersFns.length == 469
#guard (fidTiersFns.map Fn.name).eraseDups.length == 469
#guard fidTiersModule.checkAcyclic == true
#guard fidTiersModule.externs.isEmpty == true
#guard fidTiersModule.exits.isEmpty == true
#guard (ppTModule fidTiersStandModule).isOk
#guard (PrintQbe.module fidTiersStandModule).isOk
#guard (ppTModule fidTiersModule).isOk
#guard (ppModule (fidTiersRepls.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fidTiersRepls.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fidTiersRepls.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (fidTiersRepls.map (Fn.legal .x64AVX512))).isOk
#guard fidTiersRepls.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fidTiersRepls.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fidTiersRepls.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fidTiersRepls.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem ft_repls_wf : ∀ r ∈ fidTiersRepls, r.Wf := fidTiersRepls_wf
theorem ft_stand_acyclic : fidTiersStandModule.checkAcyclic = true := fidTiersStand_acyclic
theorem ft_specs_sigs :
    fidTiersSpecs.map (fun e => (e.name, e.as, e.rs)) = fidTiersRepls.map Fn.sig :=
  fidTiersSpecs_sigs
theorem ft_specs_noExit : fidTiersSpecs.all SpecEntry.noExit = true := fidTiersSpecs_noExit

theorem ft_sync_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ fidSyncLegacyTiersFn.body a m Q X :=
  fid_sync_legacy_tiers_wp Γ hEnsure

theorem ft_arsn_wp (Γ : Env)
    (hLit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hRec : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_record_used" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
      Func.wp Γ fidAnalyzeRsnBody a m Q X :=
  fid_analyze_rsn_wp Γ hLit hRec

theorem ft_stand_tbl : TableImpl fidTiersStandEnv fidTiersRepls fidTiersSpecs :=
  fidTiersStand_tableImpl
theorem ft_stand_mod_ok : ModuleOk fidTiersStandEnv fidTiersStandModule :=
  fidTiersStand_moduleOk

theorem ft_mod_tbl : TableImpl fidTiersEnv fidTiersRepls fidTiersSpecs := fidTiers_tableImpl
theorem ft_env_sync :
    ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      fidTiersEnv "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X :=
  fidTiersEnv_sync_spec
theorem ft_env_arsn :
    ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
      fidTiersEnv "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X :=
  fidTiersEnv_arsn_spec

theorem ft_mod_ok : ModuleOk fidTiersEnv fidTiersModule := fidTiers_moduleOk

theorem ft_sync_nv :
    Func.wp fidTiersStandEnv fidSyncLegacyTiersFn.body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        M6HdrExtOk ext' ∧ nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_tiers_sync

theorem ft_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidTiersEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidTiers_solve_bytes_sound hcfit hwfit hm

theorem ft_unsat_nv :
    Func.wp fidTiersEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidTiers_unsat_nv

end LeanQbeTest.T.KissatFidelityTiersTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev fidt_r_wf := @LeanQbeTest.T.KissatFidelityTiersTest.ft_repls_wf
abbrev fidt_acyc := @LeanQbeTest.T.KissatFidelityTiersTest.ft_stand_acyclic
abbrev fidt_sigs := @LeanQbeTest.T.KissatFidelityTiersTest.ft_specs_sigs
abbrev fidt_noex := @LeanQbeTest.T.KissatFidelityTiersTest.ft_specs_noExit
abbrev fidt_sync := @LeanQbeTest.T.KissatFidelityTiersTest.ft_sync_wp
abbrev fidt_arsn := @LeanQbeTest.T.KissatFidelityTiersTest.ft_arsn_wp
abbrev fidt_stbl := @LeanQbeTest.T.KissatFidelityTiersTest.ft_stand_tbl
abbrev fidt_sok := @LeanQbeTest.T.KissatFidelityTiersTest.ft_stand_mod_ok
abbrev fidt_mtbl := @LeanQbeTest.T.KissatFidelityTiersTest.ft_mod_tbl
abbrev fidt_esync := @LeanQbeTest.T.KissatFidelityTiersTest.ft_env_sync
abbrev fidt_earsn := @LeanQbeTest.T.KissatFidelityTiersTest.ft_env_arsn
abbrev fidt_ok := @LeanQbeTest.T.KissatFidelityTiersTest.ft_mod_ok
abbrev fidt_sb := @LeanQbeTest.T.KissatFidelityTiersTest.ft_solve_sound
abbrev fidt_nv := @LeanQbeTest.T.KissatFidelityTiersTest.ft_unsat_nv
abbrev fidt_snv := @LeanQbeTest.T.KissatFidelityTiersTest.ft_sync_nv

#print axioms fidt_r_wf
#print axioms fidt_acyc
#print axioms fidt_sigs
#print axioms fidt_noex
#print axioms fidt_sync
#print axioms fidt_arsn
#print axioms fidt_stbl
#print axioms fidt_sok
#print axioms fidt_mtbl
#print axioms fidt_esync
#print axioms fidt_earsn
#print axioms fidt_ok
#print axioms fidt_sb
#print axioms fidt_nv
#print axioms fidt_snv
