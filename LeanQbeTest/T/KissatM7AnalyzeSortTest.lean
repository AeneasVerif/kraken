module

public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Checks, and Axiom Audit for Kissat `M7` (`AnalyzeSort`)

1. Executable `#guard` checks on `m7AnalyzeSortModule` (`6` owned `_m7` functions + `2`
   canonical externs, `0` exits), `checkAcyclic = true`, `PrintCpp`, `PrintQbe`, and
   `Fn.legal` across `aarch64`, `scalar64`, `x64AVX512`, and `x64AVX2`.
2. Short root-namespace audit theorems covering `ModuleOk`, `TableImpl`, `noExit`, drop-in
   `Fn` WP wrappers, and concrete `Mem 64` non-vacuity (`XPost := False`, `0` SAT proofs).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7AnalyzeSortTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort

/-! ## 1. Static Checks & Backend Compilation Guards -/

#guard m7AnalyzeSortModule.checkAcyclic == true
#guard m7AnalyzeSortModule.exits.isEmpty
#guard m7AnalyzeSort_fns.length == 6
#guard m7AnalyzeSortExterns.length == 2
#guard m7AnalyzeSort_fns.map Fn.name ==
  [ "full_sort_tmp_sift_m7", "full_sort_tmp_heap_m7", "full_sort_tmp_m7",
    "full_sort_u32_m7", "full_log10_q16_m7", "full_rephase_m7" ]
#guard (ppTModule m7AnalyzeSortModule).isOk
#guard (PrintQbe.module m7AnalyzeSortModule).isOk
#guard (ppModule (m7AnalyzeSort_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7AnalyzeSort_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7AnalyzeSort_fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7AnalyzeSort_fns.map (Fn.legal .x64AVX2))).isOk

end LeanQbeTest.T.KissatM7AnalyzeSortTest

/-! ## 2. Short Root-Namespace Audit Theorems & Single-Line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort

theorem m7as_wf : ∀ f ∈ m7AnalyzeSort_fns, f.Wf :=
  m7AnalyzeSort_fns_wf

theorem m7as_acyc : m7AnalyzeSortModule.checkAcyclic = true :=
  m7AnalyzeSort_acyclic

theorem m7as_tbl_len : m7AnalyzeSortSpecTable.length = 8 :=
  m7AnalyzeSortSpecTable_length

theorem m7as_noExit_tbl : ∀ e ∈ m7AnalyzeSortSpecTable, e.noExit = true :=
  m7AnalyzeSortSpecTable_noExit

theorem m7as_env_noExit :
    ∀ f as bs xs m Q X X',
      m7AnalyzeSortEnv f as bs xs m Q X → m7AnalyzeSortEnv f as bs xs m Q X' :=
  m7AnalyzeSort_noExit

theorem m7as_tbl_impl :
    TableImpl m7AnalyzeSortEnv m7AnalyzeSort_fns m7AnalyzeSortSpecTable :=
  m7AnalyzeSort_tableImpl

theorem m7as_mod_ok : ModuleOk m7AnalyzeSortEnv m7AnalyzeSortModule :=
  m7AnalyzeSort_moduleOk

theorem m7as_sort_tmp_wp :
    ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      m7SortTmpSpec args m Q X → Func.wp m7AnalyzeSortEnv m7SortTmpFn.body args m Q X :=
  m7SortTmpFn_wp

theorem m7as_sort_tmp_small_wp :
    ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullSortTmpSpec args m Q X →
      (∀ c s R, args.1 = c.hdr → s.LengthsOk c → (FullMem c s ⋆ R) m → s.core.tmp_len ≤ 16) →
      Func.wp m7AnalyzeSortEnv m7SortTmpFn.body args m Q X :=
  m7SortTmpFn_small_canonical_wp

theorem m7as_sort_u32_wp :
    ∀ (args : Tup Val [i64, i32]) (m : Mem 64) (Q : Post []) (X : XPost),
      m7SortU32SortedSpec args m Q X →
        Func.wp m7AnalyzeSortEnv m7SortU32Fn.body args m Q X :=
  m7SortU32Fn_wp

theorem m7as_sort_u32_canon_wp (Γ : Env) :
    ∀ (args : Tup Val [i64, i32]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullSortU32Spec args m Q X → Func.wp Γ m7SortU32Fn.body args m Q X :=
  m7SortU32Fn_canonical_wp Γ

theorem m7as_log10_q16_wp :
    ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      m7Log10Q16Spec a m Q X → Func.wp m7AnalyzeSortEnv m7Log10Q16Fn.body a m Q X :=
  m7Log10Q16Fn_wp

theorem m7as_rephase_wp :
    ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      FullM5Sched.m5RephaseSpec a m Q X →
        Func.wp m7AnalyzeSortEnv m7RephaseFn.body a m Q X :=
  m7RephaseFn_wp

theorem m7as_nv_log10_q16 :
    Func.wp m7AnalyzeSortEnv m7Log10Q16Fn.body (1000#64, ()) (∅ : Mem 64)
      (fun res m' => res.1.toNat < 20 * 65536 ∧ 65536 ≤ res.1.toNat ∧ m' = (∅ : Mem 64))
      (fun _ _ _ _ => False) :=
  nv_m7_log10_q16

theorem m7as_nv_sort_u32 :
    Func.wp m7AnalyzeSortEnv m7SortU32Fn.body (0x1000#64, 17#32, ()) nvM7U32Mem
      (fun () m' => ∃ arr',
        arr'.length = 17 ∧ (arr'.take 17).Perm nvM7U32Arr ∧ M7SortedU32 arr' 17 ∧
        array (t := i32) 0x1000#64 arr' m')
      (fun _ _ _ _ => False) :=
  nv_m7_sort_u32

theorem m7as_nv_sort_tmp :
    Func.wp m7AnalyzeSortEnv m7SortTmpFn.body (nvM7Sort18Cfg.hdr, ()) nvM7Sort18Mem
      (fun () m' => ∃ tmp' wsort',
        let s' : FullState :=
          { core := { nvM7Sort18State.core with tmp := tmp' }
            scratch := { nvM7Sort18State.scratch with wsort := wsort' } }
        s'.LengthsOk nvM7Sort18Cfg ∧
        (tmp'.take 18).Perm (nvM7Sort18State.core.tmp.take 18) ∧
        tmp'[0]? = nvM7Sort18State.core.tmp[0]? ∧
        (∀ i j, 1 ≤ i → i ≤ j → j < 18 →
          Full.fullTmpLe nvM7Sort18State.core.lvl nvM7Sort18State.core.trail_pos
            (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) ∧
        s'.scratch.work_stk2 = nvM7Sort18State.scratch.work_stk2 ∧
        FullExtScratchPres nvM7Sort18State s' ∧
        FullMem nvM7Sort18Cfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_sort_tmp

theorem m7as_nv_rephase :
    Func.wp m7AnalyzeSortEnv m7RephaseFn.body (nvOneLitCfg.hdr, ()) nvM7RephaseMem
      (fun () m' => ∃ s',
        FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧
        s'.core.cur_level ≤ nvM7RephaseState.core.cur_level ∧
        s'.core.fuel.toNat ≤ nvM7RephaseState.core.fuel.toNat ∧
        FullExtScratchPres nvM7RephaseState s' ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m7_rephase

#print axioms m7as_wf
#print axioms m7as_acyc
#print axioms m7as_tbl_len
#print axioms m7as_noExit_tbl
#print axioms m7as_env_noExit
#print axioms m7as_tbl_impl
#print axioms m7as_mod_ok
#print axioms m7as_sort_tmp_wp
#print axioms m7as_sort_u32_wp
#print axioms m7as_sort_u32_canon_wp
#print axioms m7as_log10_q16_wp
#print axioms m7as_rephase_wp
#print axioms m7as_nv_log10_q16
#print axioms m7as_nv_sort_u32
#print axioms m7as_nv_sort_tmp
#print axioms m7as_nv_rephase

end AxiomAudit
