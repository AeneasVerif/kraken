module

public import LeanQbe.T.Examples.Kissat.FullM7CongIteProof1
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7CongIte
meta import LeanQbe.T.Examples.Kissat.FullM7CongIteProof1
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification & Axiom Audit for Kissat M7 Conditional Equivalence Merge (`FullM7CongIte`)

1. `#guard` checks on `m7CongIteFns` (`7` fns), `m7CongIteModule.checkAcyclic`,
   `m7CongIteSpecTable` (`7` rows, `noExit = true`), `PrintCpp.ppTModule`, `PrintQbe.module`,
   and 4-ISA `Fn.legal` (`aarch64`, `scalar64`, `x64SSE`, `x64AVX2`).
2. Audit restatements of `FullDenseInv`-preserving `full_cong_extract_ite_all_m7_dense_wp`,
   closed `ModuleOk`, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`).
3. Single-line `#print axioms` audit (strictly `⊆ [propext, Classical.choice,
   Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7CongIteTest

open Std.Sat
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5CongFix
open LeanQbe.T.Examples.Kissat.FullM7CongIte
open Kraken.Bedrock2.Test

#guard m7CongIteFns.length == 7
#guard m7CongIteFns.map Fn.name ==
  [ "full_cong_u64_sift_m7", "full_cong_u64_sort_m7",
    "full_cong_bsearch_u64_m7", "full_cong_copy_condbin_m7",
    "full_cong_extract_condeq_m7", "full_cong_merge_condeq_m7",
    "full_cong_extract_ite_all_m7" ]
#guard m7CongIteModule.checkAcyclic == true
#guard m7CongIteModule.externs.isEmpty == true
#guard m7CongIteModule.exits.isEmpty == true
#guard m7CongIteSpecTable.length == 7
#guard m7CongIteSpecTable.all (·.noExit) == true
#guard (ppTModule m7CongIteModule).isOk
#guard (PrintQbe.module m7CongIteModule).isOk
#guard (ppModule (m7CongIteFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7CongIteFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7CongIteFns.map (Fn.legal .x64SSE))).isOk
#guard (ppModule (m7CongIteFns.map (Fn.legal .x64AVX2))).isOk

theorem m7_cong_ite_sigs_audit :
    m7CongIteSpecTable.map (fun e => (e.name, e.as, e.rs)) = m7CongIteModule.sigs :=
  m7CongIteSpecTable_sigs

theorem m7_cong_ite_noExit_audit :
    ∀ e ∈ m7CongIteSpecTable, e.noExit = true :=
  m7CongIteSpecTable_noExit

theorem m7_cong_ite_moduleOk_audit :
    ModuleOk m7CongIteEnv m7CongIteModule :=
  m7CongIte_moduleOk

theorem m7_cong_extract_ite_all_dense_audit (Γ : Env)
    (hCopy : ∀ a m Q X, m7CopyCondbinSpec a m Q X →
      Γ "full_cong_copy_condbin_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, m7ExtractCondeqSpec a m Q X →
      Γ "full_cong_extract_condeq_m7" [i64, i64, i64, i64] [i64] a m Q X)
    (hMerge : ∀ a m Q X, m7MergeCondeqSpec a m Q X →
      Γ "full_cong_merge_condeq_m7" [i64, i32, i64, i64, i32, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {g_len g_cap : BitVec 32} {tick_lim : BitVec 64}
    {Q : Post [i32]} {X : XPost}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hden : FullDenseInv c F0 s) (hgl : g_len.toNat ≤ g_cap.toNat)
    (hcap : g_cap.toNat ≤ c.scratch_cap)
    (hseq : GateSeqOk32 F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0)
    (hm : (FullMem c s ⋆ R) m0)
    (hQ : ∀ (ret : BitVec 32) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → FullWitnessInv c F0 F_cur s'.core → s'.core = s.core →
      g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
      (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
      GateSeqOk32 F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m') :
    Func.wp Γ full_cong_extract_ite_all_m7_body (c.hdr, g_len, g_cap, tick_lim, ()) m0 Q X :=
  full_cong_extract_ite_all_m7_dense_wp Γ hCopy hExt hMerge
    hlen hw hden hgl hcap hseq hm hQ

theorem m7_cong_extract_ite_all_nv_audit :
    Func.wp m7CongIteEnv full_cong_extract_ite_all_m7_body
      (FullDefSweep.nvDefSweepCfg.hdr, 0#32, 128#32, 1024#64, ()) FullDefSweep.nvDefSweepMem
      (fun (ret, ()) m' => ∃ s' : FullState,
        FullDenseInv FullDefSweep.nvDefSweepCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ ret.toNat ≤ 128 ∧
        GateSeqOk32 [[0], [1]] 1 s'.scratch.scratch_buf ret.toNat 0 ∧
        FullMem FullDefSweep.nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  m7_cong_extract_ite_all_nv

end LeanQbeTest.T.KissatM7CongIteTest

abbrev m7ci_fns_wf := @LeanQbe.T.Examples.Kissat.FullM7CongIte.m7CongIteFns_wf
abbrev m7ci_acyc := @LeanQbe.T.Examples.Kissat.FullM7CongIte.m7CongIte_acyclic
abbrev m7ci_sift := @LeanQbe.T.Examples.Kissat.FullM7CongIte.full_cong_u64_sift_m7_wp
abbrev m7ci_sort := @LeanQbe.T.Examples.Kissat.FullM7CongIte.full_cong_u64_sort_m7_wp
abbrev m7ci_bs := @LeanQbe.T.Examples.Kissat.FullM7CongIte.full_cong_bsearch_u64_m7_wp
abbrev m7ci_copy := @LeanQbe.T.Examples.Kissat.FullM7CongIte.full_cong_copy_condbin_m7_wp
abbrev m7ci_ext := @LeanQbe.T.Examples.Kissat.FullM7CongIte.full_cong_extract_condeq_m7_wp
abbrev m7ci_mrg := @LeanQbe.T.Examples.Kissat.FullM7CongIte.full_cong_merge_condeq_m7_wp
abbrev m7ci_all := @LeanQbe.T.Examples.Kissat.FullM7CongIte.full_cong_extract_ite_all_m7_wp
abbrev m7ci_den := @LeanQbeTest.T.KissatM7CongIteTest.m7_cong_extract_ite_all_dense_audit
abbrev m7ci_mod := @LeanQbeTest.T.KissatM7CongIteTest.m7_cong_ite_moduleOk_audit
abbrev m7ci_nv := @LeanQbeTest.T.KissatM7CongIteTest.m7_cong_extract_ite_all_nv_audit

#print axioms m7ci_fns_wf
#print axioms m7ci_acyc
#print axioms m7ci_sift
#print axioms m7ci_sort
#print axioms m7ci_bs
#print axioms m7ci_copy
#print axioms m7ci_ext
#print axioms m7ci_mrg
#print axioms m7ci_all
#print axioms m7ci_den
#print axioms m7ci_mod
#print axioms m7ci_nv
