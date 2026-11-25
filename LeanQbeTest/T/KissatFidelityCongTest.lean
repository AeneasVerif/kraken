/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCong
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProofSplice
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProofNv
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullFidelityCong
meta import LeanQbe.T.Examples.Kissat.FullFidelityCongProofSplice
meta import LeanQbe.T.Examples.Kissat.FullFidelityCongProofNv
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Guards, and Axiom Audit for Kissat `FullFidelityCong`

1. Executable `#guard` checks on `fidCongModule` (`474` fns, `0` externs, `0` exits, acyclic),
   `fidCongSpecTable` (`474` rows, `noExit = true`), `fidCongRepls` (`19` patched fns),
   `fidCongBefores` (`2` host groups, `3` new helpers), `PrintCpp`, `PrintQbe`, and 4-ISA
   `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX2`, and `.x64AVX512`.
2. Audit-ready restated headline theorems covering `GAP-CONG-01..04` + `BUG-CONG-00` parity
   specs, closed `fidCong_moduleOk` / `TableImpl` / `kissat_solve_bytes` UNSAT soundness, host
   memory lift, and all concrete `Mem 64` UNSAT non-vacuity theorems (`XPost := False`).
3. Single-line `<= 100`c `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatFidelityCongTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM7CongIte
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open Kraken.Bedrock2.Test

/-! ## 1. Executable `#guard` Codegen & 4-ISA Legalization Checks -/

private def fcPatchedFns : List Fn := fidCongRepls ++ (fidCongBefores.flatMap Prod.snd)

#guard fidCongFns.length == 474
#guard (fidCongFns.map Fn.name).eraseDups.length == 474
#guard fidCongRepls.length == 19
#guard fidCongBefores.length == 2
#guard (fidCongBefores.flatMap Prod.snd).length == 3
#guard fidCongModule.checkAcyclic == true
#guard fidCongModule.externs.isEmpty == true
#guard fidCongModule.exits.isEmpty == true
#guard fidCongSpecTable.length == 474
#guard fidCongSpecTable.all SpecEntry.noExit == true
#guard fidCongSpecTable.map (fun e => (e.name, e.as, e.rs)) == fidCongModule.sigs
#guard (ppTModule fidCongModule).isOk
#guard (PrintQbe.module fidCongModule).isOk
#guard (ppModule (fcPatchedFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (fcPatchedFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (fcPatchedFns.map (Fn.legal .x64AVX2))).isOk
#guard (ppModule (fcPatchedFns.map (Fn.legal .x64AVX512))).isOk
#guard fcPatchedFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard fcPatchedFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard fcPatchedFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2
#guard fcPatchedFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512

/-! ## 2. Audit-Ready Restated Headline Theorems -/

theorem fc_repls_wf : ∀ r ∈ fidCongRepls, r.Wf := fidCongRepls_wf
theorem fc_befores_wf : ∀ b ∈ fidCongBefores.flatMap Prod.snd, b.Wf := fidCongBefores_wf
theorem fc_names_nodup : (fidCongFns.map Fn.name).Nodup := fidCongFns_names_nodup
theorem fc_tbl_sigs :
    fidCongSpecTable.map (fun e => (e.name, e.as, e.rs)) = fidCongFns.map Fn.sig :=
  fidCongSpecTable_sigs
theorem fc_tbl_len : fidCongSpecTable.length = 474 := fidCongSpecTable_length
theorem fc_tbl_noExit : fidCongSpecTable.all SpecEntry.noExit = true := fidCongSpecTable_noExit

theorem fc_acyclic :
    fidCongModule.namesNodup ∧
    ∀ pre fn post, fidCongModule.fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ fidCongModule.externs.map Extern.sig)
        fidCongModule.exits :=
  fidCong_acyclic

theorem fc_mod_ok : ModuleOk fidCongEnv fidCongModule := fidCong_moduleOk
theorem fc_tbl_impl : TableImpl fidCongEnv fidCongModule.fns fidCongSpecTable :=
  fidCong_tableImpl

theorem fc_solve_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidCongEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fidCong_solve_bytes_sound hcfit hwfit hm

theorem fc_solve_host
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  fidCong_solve_bytes_host_sound hpost hhost

theorem fc_unsat_nv :
    Func.wp fidCongEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fidCong_unsat_nv

theorem fc_emitXor4_wp :
    ∀ args m Q X, fidCongEmitXor4Spec args m Q X →
      Func.wp fidCongEnv full_cong_emit_xor4_body args m Q X :=
  fidCongEnv_emitXor4_wp

theorem fc_andMatch_wp :
    ∀ a m Q X, fidCongAndMatchSpec a m Q X →
      Func.wp fidCongEnv FullFidelityCong.full_cong_and_match_body a m Q X :=
  fidCongEnv_andMatch_wp

theorem fc_htGrowClear_wp :
    ∀ a m Q X, fidCongHtGrowClearSpec a m Q X →
      Func.wp fidCongEnv full_cong_ht_grow_clear_m7_body a m Q X :=
  fidCongEnv_htGrowClear_wp

theorem fc_sortPairs_wp :
    ∀ a m Q X, fidCongSortPairsSpec a m Q X →
      Func.wp fidCongEnv full_cong_sort_pairs_fid_body a m Q X :=
  fidCongEnv_sortPairs_wp

theorem fc_find_env {a m Q X} (h : Full.fullCongFindSpec a m Q X) :
    fidCongEnv "full_cong_find" [i64, i32] [i32] a m Q X :=
  fidCongEnv_find h

theorem fc_evalGate_wp :
    ∀ a m Q X, fidCongEvalGateSpec a m Q X →
      Func.wp fidCongEnv FullFidelityCong.full_cong_eval_gate_body a m Q X :=
  fidCongEnv_evalGate_wp

theorem fc_congDense_wp :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp fidCongEnv FullFidelityCong.full_congruence_dense_body a m Q X :=
  fidCongEnv_congruenceDense_wp

theorem fc_nv_emit_xor4 :
    Func.wp fidCongEnv full_cong_emit_xor4_body
      (nvFidXor4Cfg.pScratchBuf, 0#64, 4#32, 6#32, 2#32, 0#32, ()) nvFidXor4Mem0
      (fun (r, ()) m' =>
        r = 5#64 ∧
        nvFidXor4StEnd.scratch.scratch_buf =
          [5#32, (1#32 <<< 28#32) ||| 3#32, 0#32, 2#32, 6#32] ∧
        nvFidXor4StEnd.LengthsOk nvFidXor4Cfg ∧
        FullWitnessInv nvFidXor4Cfg nvFidF0 [] nvFidXor4StEnd.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidXor4Cfg nvFidXor4StEnd m')
      (fun _ _ _ _ => False) :=
  nv_fid_cong_emit_xor4

theorem fc_nv_and_match_wide33 :
    Func.wp fidCongEnv FullFidelityCong.full_cong_and_match_body
      (nvFidCfg34.hdr, 0#32, 33#32, ()) nvFid34Mem0
      (fun (r, ()) m' => ∃ repr' : List (BitVec 32),
        r = true ∧ repr'.length = 68 ∧ FullCongReprInv [] 68 repr' ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg34 { nvFid34St0 with core := { nvFid34St0.core with repr := repr' } } m')
      (fun _ _ _ _ => False) :=
  nv_fid_cong_and_match_wide33

theorem fc_nv_ht_grow_clear_256k :
    Func.wp fidCongEnv full_cong_ht_grow_clear_m7_body (nvFidHt256Cfg.hdr, 0#64, ()) nvFidHt256Mem0
      (fun (r, ()) m' => ∃ (scr' : List (BitVec 32)) (rsz' : BitVec 64),
        let s' : FullState :=
          { nvFidHt256St0 with scratch := { nvFidHt256St0.scratch with
            scratch_buf := scr', res_sz := rsz' } }
        r = 262144#64 ∧ rsz' = 0#64 ∧
        FidCongHtCtrlOk nvFidHt256Cfg scr' 0 8 262144 ∧
        (∀ j < 262144, scr'[8 + j]? = some 0xFFFFFFFF#32) ∧
        s'.LengthsOk nvFidHt256Cfg ∧
        FullWitnessInv nvFidHt256Cfg nvFidF0 [] s'.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidHt256Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_cong_ht_grow_clear_256k

theorem fc_nv_sift_pairs :
    Func.wp fidCongEnv full_cong_sift_pairs_fid_body (nvFidPairCfg.pScratchBuf, 0#64, 2#64, ())
      nvFidPairMem0
      (fun () m' =>
        nvFidPairSt1.scratch.scratch_buf = [10#32, 2#32, 10#32, 1#32] ∧
        nvFidPairSt1.LengthsOk nvFidPairCfg ∧
        FullWitnessInv nvFidPairCfg nvFidF0 [] nvFidPairSt1.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidPairCfg nvFidPairSt1 m')
      (fun _ _ _ _ => False) :=
  nv_fid_cong_sift_pairs

theorem fc_nv_sort_pairs :
    Func.wp fidCongEnv full_cong_sort_pairs_fid_body (nvFidPairCfg.pScratchBuf, 2#64, ())
      nvFidPairMem1
      (fun () m' => ∃ scr' : List (BitVec 32),
        let s' : FullState := { nvFidPairSt1 with scratch := { nvFidPairSt1.scratch with
          scratch_buf := scr' } }
        FidPairsOk (fun k r => k = 10#32 ∧ (r = 1#32 ∨ r = 2#32)) scr' 2 ∧
        s'.LengthsOk nvFidPairCfg ∧
        FullWitnessInv nvFidPairCfg nvFidF0 [] s'.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidPairCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_cong_sort_pairs

theorem fc_nv_merge_condeq_ite :
    Func.wp fidCongEnv FullFidelityCong.full_cong_merge_condeq_m7_body
      (nvFidIteCfg.hdr, 2#32, 1#64, 1#64, 0#32, 5#32, ()) nvFidIteMem0
      (fun (r, ()) m' =>
        r = 5#32 ∧
        nvFidIteStEnd.scratch.scratch_buf =
          [0#32, (2#32 <<< 28#32) ||| 3#32, 2#32, 4#32, 4#32] ∧
        FidGateSeqOk 64 nvFidIteFCur 4 nvFidIteStEnd.scratch.scratch_buf 5 0 ∧
        nvFidIteStEnd.LengthsOk nvFidIteCfg ∧
        FullWitnessInv nvFidIteCfg nvFidF0 nvFidIteFCur nvFidIteStEnd.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidIteCfg nvFidIteStEnd m')
      (fun _ _ _ _ => False) :=
  nv_fid_cong_merge_condeq_trivial_ite

theorem fc_nv_eval_gate_selfcancel :
    Func.wp fidCongEnv FullFidelityCong.full_cong_eval_gate_body
      (nvFidEvalCfg.hdr, 0#64, 4#64, 16#64, 0#32, 4#64, ()) nvFidEvalMem0
      (fun (r, ()) m' => ∃ s' : FullState,
        r = 2#64 ∧
        s'.core.inconsistent = 1#64 ∧
        s'.LengthsOk nvFidEvalCfg ∧
        FullCongReprInv nvFidEvalFCur 8 s'.core.repr ∧
        nvFidF0.Unsat ∧ FullMem nvFidEvalCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_cong_eval_gate_xor_selfcancel

end LeanQbeTest.T.KissatFidelityCongTest

/-! ## 3. Single-Line `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

abbrev fidc_r_wf := @LeanQbeTest.T.KissatFidelityCongTest.fc_repls_wf
abbrev fidc_b_wf := @LeanQbeTest.T.KissatFidelityCongTest.fc_befores_wf
abbrev fidc_nd := @LeanQbeTest.T.KissatFidelityCongTest.fc_names_nodup
abbrev fidc_tsig := @LeanQbeTest.T.KissatFidelityCongTest.fc_tbl_sigs
abbrev fidc_tlen := @LeanQbeTest.T.KissatFidelityCongTest.fc_tbl_len
abbrev fidc_tnoex := @LeanQbeTest.T.KissatFidelityCongTest.fc_tbl_noExit
abbrev fidc_acyc := @LeanQbeTest.T.KissatFidelityCongTest.fc_acyclic
abbrev fidc_ok := @LeanQbeTest.T.KissatFidelityCongTest.fc_mod_ok
abbrev fidc_tbl := @LeanQbeTest.T.KissatFidelityCongTest.fc_tbl_impl
abbrev fidc_sb := @LeanQbeTest.T.KissatFidelityCongTest.fc_solve_sound
abbrev fidc_host := @LeanQbeTest.T.KissatFidelityCongTest.fc_solve_host
abbrev fidc_nv := @LeanQbeTest.T.KissatFidelityCongTest.fc_unsat_nv
abbrev fidc_xor4 := @LeanQbeTest.T.KissatFidelityCongTest.fc_emitXor4_wp
abbrev fidc_andm := @LeanQbeTest.T.KissatFidelityCongTest.fc_andMatch_wp
abbrev fidc_htgc := @LeanQbeTest.T.KissatFidelityCongTest.fc_htGrowClear_wp
abbrev fidc_sort := @LeanQbeTest.T.KissatFidelityCongTest.fc_sortPairs_wp
abbrev fidc_find := @LeanQbeTest.T.KissatFidelityCongTest.fc_find_env
abbrev fidc_eval := @LeanQbeTest.T.KissatFidelityCongTest.fc_evalGate_wp
abbrev fidc_cong := @LeanQbeTest.T.KissatFidelityCongTest.fc_congDense_wp
abbrev fidc_nv1 := @LeanQbeTest.T.KissatFidelityCongTest.fc_nv_emit_xor4
abbrev fidc_nv2 := @LeanQbeTest.T.KissatFidelityCongTest.fc_nv_and_match_wide33
abbrev fidc_nv3 := @LeanQbeTest.T.KissatFidelityCongTest.fc_nv_ht_grow_clear_256k
abbrev fidc_nv4 := @LeanQbeTest.T.KissatFidelityCongTest.fc_nv_sift_pairs
abbrev fidc_nv5 := @LeanQbeTest.T.KissatFidelityCongTest.fc_nv_sort_pairs
abbrev fidc_nv6 := @LeanQbeTest.T.KissatFidelityCongTest.fc_nv_merge_condeq_ite
abbrev fidc_nv7 := @LeanQbeTest.T.KissatFidelityCongTest.fc_nv_eval_gate_selfcancel

#print axioms fidc_r_wf
#print axioms fidc_b_wf
#print axioms fidc_nd
#print axioms fidc_tsig
#print axioms fidc_tlen
#print axioms fidc_tnoex
#print axioms fidc_acyc
#print axioms fidc_ok
#print axioms fidc_tbl
#print axioms fidc_sb
#print axioms fidc_host
#print axioms fidc_nv
#print axioms fidc_xor4
#print axioms fidc_andm
#print axioms fidc_htgc
#print axioms fidc_sort
#print axioms fidc_find
#print axioms fidc_eval
#print axioms fidc_cong
#print axioms fidc_nv1
#print axioms fidc_nv2
#print axioms fidc_nv3
#print axioms fidc_nv4
#print axioms fidc_nv5
#print axioms fidc_nv6
#print axioms fidc_nv7
