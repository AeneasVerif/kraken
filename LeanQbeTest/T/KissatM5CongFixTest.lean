module

public import LeanQbe.T.Examples.Kissat.FullM5CongFixProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5CongFix
meta import LeanQbe.T.Examples.Kissat.FullM5CongFixProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification and Axiom Audit for Kissat M5 Congruence Closure Fixes (`FullM5CongFix`)

1. Executable `#guard` checks on `m5CongFix_fns` (`7` fns), `m5CongFixModule.checkAcyclic`,
   `m5CongFixSpecTable` (`15` rows, `noExit = true`), `PrintCpp`, `PrintQbe`, and `Fn.legal`
   across `.aarch64`, `.scalar64`, `.x64AVX2`.
2. Direct `Func.Wf` + `Func.wp` verification of all `7` functions (`full_cong_merge` against exact
   `FullCongSpecs.fullCongMergeSpec`, plus widened `arity ≤ 31` `GateSeqOk32` / `CongHtInv32`
   contracts), closed `ModuleOk`, direct `FullM5CongBins` composition against canonical
   `m3CongruenceDenseSpec` / `fullCongruenceDenseSpec`, and concrete `Mem 64` UNSAT non-vacuity
   (`XPost := False`, zero SAT/model proofs).
3. Single-line `#print axioms` audit (strictly
   `⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatM5CongFixTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5CongBins
open LeanQbe.T.Examples.Kissat.FullM5CongFix
open Kraken.Bedrock2.Test

#guard m5CongFix_fns.length == 7
#guard m5CongFix_fns.map Fn.name ==
  [ "full_cong_merge", "full_cong_extract_ite", "full_cong_emit_xor",
    "full_cong_try_xor_ite", "full_cong_extract", "full_cong_and_match",
    "full_cong_work_step" ]
#guard full_cong_work_step.name == "full_cong_work_step"
#guard full_cong_work_step.as == [i64, i64, i64, i64, i32]
#guard full_cong_work_step.rs == [i64]
#guard m5CongFixModule.checkAcyclic == true
#guard m5CongFixModule.exits.isEmpty == true
#guard m5CongFixSpecTable.length == 15
#guard m5CongFixSpecTable.all (·.noExit) == true
#guard (ppTModule m5CongFixModule).isOk
#guard (PrintQbe.module m5CongFixModule).isOk
#guard (ppModule (m5CongFix_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5CongFix_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5CongFix_fns.map (Fn.legal .x64AVX2))).isOk

theorem m5_cong_merge_canonical_ok (Γ : Env)
    (hFind : ∀ a m Q X, FullCongSpecs.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hAddBin : ∀ a m Q X, FullCongSpecs.fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, FullCongSpecs.fullCongMergeSpec a m Q X →
      Func.wp Γ FullM5CongFix.full_cong_merge_body a m Q X :=
  m5_cong_merge_wp Γ hFind hAddBin

theorem m5_congruence_dense_fix_canonical_ok (Γ : Env)
    (hExtractBins : ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, m5CongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, m5CongWorkStepSpec a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Func.wp Γ FullM5CongBins.full_congruence_dense_body a m Q X :=
  m5_congruence_dense_fix_wp Γ hExtractBins hExtract hWork

theorem m5_nv_cong_extract :
    Func.wp m5CongFixEnv FullM5CongFix.full_cong_extract_body
      (FullDefSweep.nvDefSweepCfg.hdr, 128#64, 1024#64, ()) FullDefSweep.nvDefSweepMem
      (fun (ret, ()) m' => ∃ scr' : List (BitVec 32),
        scr'.length = FullDefSweep.nvDefSweepCfg.scratch_cap ∧ ret.toNat ≤ 128 ∧
        GateSeqOk32 [[0], [1]] 1 scr' ret.toNat 0 ∧
        FullMem FullDefSweep.nvDefSweepCfg { FullDefSweep.nvDefSweepState with scratch :=
          { FullDefSweep.nvDefSweepState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) :=
  m5_cong_extract_nv

theorem m5_nv_cong_work_step :
    Func.wp m5CongFixEnv full_cong_work_step_body
      (FullDefSweep.nvDefSweepCfg.hdr, 0#64, 0#64, 1#64, 1#32, ()) nvCongFixMem
      (fun (r, ()) m' => ∃ s' : FullState,
        FullDenseInv FullDefSweep.nvDefSweepCfg nvOneLitF0 s' ∧
        s'.core.cur_vars = 1 ∧ s'.core.fuel = 1#64 ∧
        ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) ∧
        ((r &&& 3#64) = 2#64 → nvOneLitF0.Unsat) ∧
        FullMem FullDefSweep.nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  m5_cong_work_step_nv

end LeanQbeTest.T.KissatM5CongFixTest

abbrev m5cf_fns_wf := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5CongFix_fns_wf
abbrev m5cf_acyc := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5CongFix_acyclic
abbrev m5cf_merge := @LeanQbeTest.T.KissatM5CongFixTest.m5_cong_merge_canonical_ok
abbrev m5cf_ite := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5_cong_extract_ite_wp
abbrev m5cf_xor := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5_cong_emit_xor_wp
abbrev m5cf_try := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5_cong_try_xor_ite_wp
abbrev m5cf_ext := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5_cong_extract_wp
abbrev m5cf_and := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5_cong_and_match_wp
abbrev m5cf_ws := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5_cong_work_step_wp
abbrev m5cf_mod := @LeanQbe.T.Examples.Kissat.FullM5CongFix.m5CongFix_moduleOk
abbrev m5cf_cd := @LeanQbeTest.T.KissatM5CongFixTest.m5_congruence_dense_fix_canonical_ok
abbrev m5cf_nv_ext := @LeanQbeTest.T.KissatM5CongFixTest.m5_nv_cong_extract
abbrev m5cf_nv_ws := @LeanQbeTest.T.KissatM5CongFixTest.m5_nv_cong_work_step

#print axioms m5cf_fns_wf
#print axioms m5cf_acyc
#print axioms m5cf_merge
#print axioms m5cf_ite
#print axioms m5cf_xor
#print axioms m5cf_try
#print axioms m5cf_ext
#print axioms m5cf_and
#print axioms m5cf_ws
#print axioms m5cf_mod
#print axioms m5cf_cd
#print axioms m5cf_nv_ext
#print axioms m5cf_nv_ws
