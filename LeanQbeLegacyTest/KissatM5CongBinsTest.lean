module

public import LeanQbe.T.Examples.Kissat.FullM5CongBinsLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5CongBins
meta import LeanQbe.T.Examples.Kissat.FullM5CongBinsLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification and Axiom Audit for Kissat M5 Dense Binary Extraction (`FullM5CongBins`)

1. Executable `#guard` checks on `m5CongBins_fns` (`3` fns), `m5CongBinsModule.checkAcyclic`,
   `m5CongBinsSpecTable` (`8` rows, `noExit = true`), `PrintCpp`, `PrintQbe`, and `Fn.legal`
   across `.aarch64`, `.scalar64`, `.x64AVX2`.
2. Direct `Func.Wf` + `Func.wp` verification against unchanged `FullM3CongBva.m3CongruenceDenseSpec`
   and `FullDefSweep.fullCongruenceDenseSpec`, plus closed `ModuleOk` and concrete `Mem 64`
   non-vacuity (`XPost := False`, zero SAT/model proofs).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeLegacyTest.KissatM5CongBinsTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5CongBins
open Kraken.Bedrock2.Test

#guard m5CongBins_fns.length == 3
#guard m5CongBins_fns.map Fn.name ==
  ["full_cong_eb_match", "full_cong_extract_binaries", "full_congruence_dense"]
#guard full_congruence_dense.name == "full_congruence_dense"
#guard full_congruence_dense.as == [i64, i64]
#guard full_congruence_dense.rs == [i64]
#guard m5CongBinsModule.checkAcyclic == true
#guard m5CongBinsModule.exits.isEmpty == true
#guard m5CongBinsSpecTable.length == 8
#guard m5CongBinsSpecTable.all (·.noExit) == true
#guard (ppTModule m5CongBinsModule).isOk
#guard (PrintQbe.module m5CongBinsModule).isOk
#guard (ppModule (m5CongBins_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5CongBins_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5CongBins_fns.map (Fn.legal .x64AVX2))).isOk

theorem m5_congruence_dense_spec_ok (Γ : Env)
    (hExtractBins : ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, FullM3CongBva.fullCongExtractTickSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, FullM3CongBva.m3CongWorkStepSpec a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X :=
  m5_congruence_dense_wp Γ hExtractBins hExtract hWork

theorem m5_defsweep_congruence_dense_ok (Γ : Env)
    (hExtractBins : ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, FullM3CongBva.fullCongExtractTickSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, FullM3CongBva.m3CongWorkStepSpec a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullCongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X :=
  m5_defsweep_congruence_dense_wp Γ hExtractBins hExtract hWork

theorem m5_nv_extract_binaries :
    Func.wp m5CongBinsEnv full_cong_extract_binaries_body (nvOneLitCfg.hdr, ()) nvDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_vars = 1 ∧ s'.core.fuel = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  m5_cong_extract_binaries_nv

theorem m5_nv_congruence_dense :
    Func.wp m5CongBinsEnv full_congruence_dense_body (nvOneLitCfg.hdr, 1024#64, ()) nvDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_vars = 1 ∧ s'.core.fuel = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  m5_congruence_dense_nv

end LeanQbeLegacyTest.KissatM5CongBinsTest

abbrev m5cb_eb_wf := @LeanQbe.T.Examples.Kissat.FullM5CongBins.full_cong_eb_match_wf
abbrev m5cb_bin_wf := @LeanQbe.T.Examples.Kissat.FullM5CongBins.full_cong_extract_binaries_wf
abbrev m5cb_cd_wf := @LeanQbe.T.Examples.Kissat.FullM5CongBins.full_congruence_dense_wf
abbrev m5cb_fns_wf := @LeanQbe.T.Examples.Kissat.FullM5CongBins.m5CongBins_fns_wf
abbrev m5cb_acyc := @LeanQbe.T.Examples.Kissat.FullM5CongBins.m5CongBins_acyclic
abbrev m5cb_res := @LeanQbe.T.Examples.Kissat.FullM5CongBins.entails_resolve_ternary_pair
abbrev m5cb_eb_wp := @LeanQbe.T.Examples.Kissat.FullM5CongBins.full_cong_eb_match_wp
abbrev m5cb_bin_wp := @LeanQbe.T.Examples.Kissat.FullM5CongBins.full_cong_extract_binaries_wp
abbrev m5cb_cd_wp := @LeanQbeLegacyTest.KissatM5CongBinsTest.m5_congruence_dense_spec_ok
abbrev m5cb_ds_wp := @LeanQbeLegacyTest.KissatM5CongBinsTest.m5_defsweep_congruence_dense_ok
abbrev m5cb_mod_ok := @LeanQbe.T.Examples.Kissat.FullM5CongBins.m5CongBins_moduleOk
abbrev m5cb_nv_bin := @LeanQbeLegacyTest.KissatM5CongBinsTest.m5_nv_extract_binaries
abbrev m5cb_nv_cd := @LeanQbeLegacyTest.KissatM5CongBinsTest.m5_nv_congruence_dense

#print axioms m5cb_eb_wf
#print axioms m5cb_bin_wf
#print axioms m5cb_cd_wf
#print axioms m5cb_fns_wf
#print axioms m5cb_acyc
#print axioms m5cb_res
#print axioms m5cb_eb_wp
#print axioms m5cb_bin_wp
#print axioms m5cb_cd_wp
#print axioms m5cb_ds_wp
#print axioms m5cb_mod_ok
#print axioms m5cb_nv_bin
#print axioms m5cb_nv_cd
