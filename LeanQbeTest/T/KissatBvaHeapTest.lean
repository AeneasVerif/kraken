module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
meta import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for `FullBvaHeap` (M2 D-Full)

1. Executable `#guard` checks on `bvaHeap_fns` (`13` functions), names & signatures,
   `bvaHeapModule.externs` (`6` canonical `Full` externs), `bvaHeapModule.checkAcyclic`,
   the `19`-row `bvaHeapSpecTable`, and `nvBvaDenseBytes.length == 1756`.
2. Short root-namespace audit theorems + single-line `#print axioms` (`<= 100` cols, every
   `depends on axioms: [...]` output on one complete line `< 115` chars) covering all exported
   `Func.Wf`, acyclicity, generalized BVA soundness (`extUnsatSound_bvaExtendGen`), all `13`
   `Func.wp` proofs (+ canonical `full_init_fresh_var_wp`), `bvaHeapEnv_noExit`,
   `bvaHeap_moduleOk`, and all concrete `Mem 64` UNSAT non-vacuity proofs
   (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatBvaHeapTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullBvaHeap

/-! ## 1. Executable `#guard` sanity checks -/

#guard bvaHeap_fns.length == 13
#guard bvaHeapModule.externs.length == 6
#guard bvaHeapModule.checkAcyclic == true
#guard bvaHeapSpecTable.length == 19
#guard bvaHeap_fns.map Fn.name ==
  [ "full_init_fresh_var", "full_bva_hop1", "full_bva_hop2", "full_bva_hop3",
    "full_bva_match_large", "full_bva_scan_cands", "full_bva_pick_cand",
    "full_bva_filter_row", "full_bva_commit", "full_bva_try_lit",
    "full_fheap_up", "full_fheap_down", "full_factor" ]
#guard (bvaHeap_fns.map fun f => (f.name, f.as.length, f.rs.length)) ==
  [ ("full_init_fresh_var", 2, 0), ("full_bva_hop1", 3, 1), ("full_bva_hop2", 3, 1),
    ("full_bva_hop3", 3, 1), ("full_bva_match_large", 4, 1), ("full_bva_scan_cands", 4, 1),
    ("full_bva_pick_cand", 3, 1), ("full_bva_filter_row", 6, 1), ("full_bva_commit", 2, 1),
    ("full_bva_try_lit", 3, 1), ("full_fheap_up", 4, 0), ("full_fheap_down", 5, 0),
    ("full_factor", 2, 1) ]
#guard (bvaHeapSpecTable.all fun e => e.noExit) == true
#guard nvBvaDenseBytes.length == 1756

end LeanQbeTest.T.KissatBvaHeapTest

/-! ## 2. Short root-namespace audit theorems & single-line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers

theorem bva_fns_wf : ∀ f ∈ bvaHeap_fns, f.Wf := bvaHeap_fns_wf

theorem bva_acyclic : bvaHeapModule.checkAcyclic = true := bvaHeap_acyclic

theorem bva_ext_sound {F0 : CNF Nat} {mv_cur : Nat} {F_cur : List (List Nat)}
    {L : List Nat} {Qs : List (List Nat)} (hs : ExtUnsatSound F0 mv_cur F_cur)
    (hL : ∀ f ∈ L, f < 2 * mv_cur) (hQ : ∀ R ∈ Qs, ∀ q ∈ R, q < 2 * mv_cur)
    (hprod : ∀ f ∈ L, ∀ R ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: R))) :
    ExtUnsatSound F0 (mv_cur + 1) (bvaExtendGen mv_cur L Qs F_cur) :=
  extUnsatSound_bvaExtendGen hs hL hQ hprod

theorem bva_init_heap_wp (Γ : Env) :
    ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Func.wp Γ FullBvaHeap.full_init_fresh_var_body args m Q X :=
  full_init_fresh_var_heap_wp Γ

theorem bva_init_canon_wp (Γ : Env) :
    ∀ args m Q X, Full.fullInitFreshVarSpec args m Q X →
      Func.wp Γ FullBvaHeap.full_init_fresh_var_body args m Q X :=
  FullBvaHeap.full_init_fresh_var_wp Γ

theorem bva_hop1_wp (Γ : Env) :
    ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Func.wp Γ full_bva_hop1_body args m Q X :=
  full_bva_hop1_wp Γ

theorem bva_hop2_wp (Γ : Env)
    (hHop1 : ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Γ "full_bva_hop1" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop2Spec args m Q X →
      Func.wp Γ full_bva_hop2_body args m Q X :=
  full_bva_hop2_wp Γ hHop1

theorem bva_hop3_wp (Γ : Env)
    (hHop2 : ∀ args m Q X, fullBvaHop2Spec args m Q X →
      Γ "full_bva_hop2" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop3Spec args m Q X →
      Func.wp Γ full_bva_hop3_body args m Q X :=
  full_bva_hop3_wp Γ hHop2

theorem bva_match_wp (Γ : Env) :
    ∀ args m Q X, fullBvaMatchLargeSpec args m Q X →
      Func.wp Γ full_bva_match_large_body args m Q X :=
  full_bva_match_large_wp Γ

theorem bva_scan_wp (Γ : Env) :
    ∀ args m Q X, fullBvaScanCandsSpec args m Q X →
      Func.wp Γ full_bva_scan_cands_body args m Q X :=
  full_bva_scan_cands_wp Γ

theorem bva_pick_wp (Γ : Env)
    (hHop3 : ∀ args m Q X, fullBvaHop3Spec args m Q X →
      Γ "full_bva_hop3" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Func.wp Γ full_bva_pick_cand_body args m Q X :=
  full_bva_pick_cand_wp Γ hHop3

theorem bva_filter_wp (Γ : Env)
    (hMatchLarge : ∀ args m Q X, fullBvaMatchLargeSpec args m Q X →
      Γ "full_bva_match_large" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullBvaFilterRowSpec args m Q X →
      Func.wp Γ full_bva_filter_row_body args m Q X :=
  full_bva_filter_row_wp Γ hMatchLarge

theorem bva_commit_wp (Γ : Env)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullBvaCommitSpec args m Q X →
      Func.wp Γ full_bva_commit_body args m Q X :=
  full_bva_commit_wp Γ hDefrag hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch

theorem bva_try_lit_wp (Γ : Env)
    (hScan : ∀ args m Q X, fullBvaScanCandsSpec args m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] args m Q X)
    (hPick : ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] args m Q X)
    (hFilter : ∀ args m Q X, fullBvaFilterRowSpec args m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] args m Q X)
    (hCommit : ∀ args m Q X, fullBvaCommitSpec args m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullBvaTryLitHeapSpec args m Q X →
      Func.wp Γ FullBvaHeap.full_bva_try_lit_body args m Q X :=
  full_bva_try_lit_wp Γ hScan hPick hFilter hCommit

theorem bva_fheap_up_wp (Γ : Env) :
    ∀ args m Q X, fullFheapUpSpec args m Q X →
      Func.wp Γ full_fheap_up_body args m Q X :=
  full_fheap_up_wp Γ

theorem bva_fheap_down_wp (Γ : Env) :
    ∀ args m Q X, fullFheapDownSpec args m Q X →
      Func.wp Γ full_fheap_down_body args m Q X :=
  full_fheap_down_wp Γ

theorem bva_factor_wp (Γ : Env)
    (hUp : ∀ args m Q X, fullFheapUpSpec args m Q X →
      Γ "full_fheap_up" [i64, i64, i64, i32] [] args m Q X)
    (hDown : ∀ args m Q X, fullFheapDownSpec args m Q X →
      Γ "full_fheap_down" [i64, i64, i64, i32, i32] [] args m Q X)
    (hTryLit : ∀ args m Q X, fullBvaTryLitHeapSpec args m Q X →
      Γ "full_bva_try_lit" [i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullFactorHeapSpec args m Q X →
      Func.wp Γ FullBvaHeap.full_factor_body args m Q X :=
  full_factor_wp Γ hUp hDown hTryLit

theorem bva_env_noExit :
    ∀ f as bs xs m Q X X', bvaHeapEnv f as bs xs m Q X → bvaHeapEnv f as bs xs m Q X' :=
  bvaHeapEnv_noExit

theorem bva_moduleOk : ModuleOk bvaHeapEnv bvaHeapModule := bvaHeap_moduleOk

theorem bva_nv_bytes_len : nvBvaDenseBytes.length = 1756 := nvBvaDenseBytes_length

theorem bva_nv_factor :
    Func.wp bvaHeapEnv FullBvaHeap.full_factor_body
      (nvOneLitCfg.hdr, 10#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ r = 1#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_bva_factor

theorem bva_nv_try_lit :
    Func.wp bvaHeapEnv FullBvaHeap.full_bva_try_lit_body
      (nvOneLitCfg.hdr, 0#32, 1#64, ()) nvBvaDenseMem
      (fun (_ok, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_bva_try_lit

theorem bva_nv_init :
    Func.wp bvaHeapEnv FullBvaHeap.full_init_fresh_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvBvaDenseMem
      (fun () m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ s'.core.vals[0]?.getD 1#8 = 0#8 ∧
        s'.core.vals[1]?.getD 1#8 = 0#8 ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_bva_init_fresh_var

theorem bva_nv_hop3 :
    Func.wp bvaHeapEnv full_bva_hop3_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_bva_hop3

theorem bva_nv_scan :
    Func.wp bvaHeapEnv full_bva_scan_cands_body
      (nvOneLitCfg.hdr, 0#32, 0#32, 2#64, ()) nvBvaDenseMem
      (fun (n, ()) m' => ∃ s',
        s'.LengthsOk nvOneLitCfg ∧ n.toNat ≤ 2 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_bva_scan_cands

theorem bva_nv_pick :
    Func.wp bvaHeapEnv full_bva_pick_cand_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_bva_pick_cand

#print axioms bva_fns_wf
#print axioms bva_acyclic
#print axioms bva_ext_sound
#print axioms bva_init_heap_wp
#print axioms bva_init_canon_wp
#print axioms bva_hop1_wp
#print axioms bva_hop2_wp
#print axioms bva_hop3_wp
#print axioms bva_match_wp
#print axioms bva_scan_wp
#print axioms bva_pick_wp
#print axioms bva_filter_wp
#print axioms bva_commit_wp
#print axioms bva_try_lit_wp
#print axioms bva_fheap_up_wp
#print axioms bva_fheap_down_wp
#print axioms bva_factor_wp
#print axioms bva_env_noExit
#print axioms bva_moduleOk
#print axioms bva_nv_bytes_len
#print axioms bva_nv_factor
#print axioms bva_nv_try_lit
#print axioms bva_nv_init
#print axioms bva_nv_hop3
#print axioms bva_nv_scan
#print axioms bva_nv_pick

end AxiomAudit
