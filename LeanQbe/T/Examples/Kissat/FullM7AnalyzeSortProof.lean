module

public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof0
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof1
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof4
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Rules
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave 4G Top-Level Module Soundness & Concrete NV (`FullM7AnalyzeSortProof`)

Combines all `6` C0 `Func.wp` theorems from `FullM7AnalyzeSortProof{0,1,4}` and the `2`
extern specs (`full_backtrack`, `full_walk`) into a closed `8`-row `SpecTable`:
- `m7AnalyzeSortSpecTable` (`8` rows, all `noExit = true`) and
  `m7AnalyzeSortEnv := Env.ofTable m7AnalyzeSortSpecTable`.
- `m7AnalyzeSort_tableImpl`, `m7AnalyzeSort_moduleOk`, and drop-in `Fn` WP wrappers.
- Concrete `Mem 64` UNSAT-only / safety NV (`nv_m7_log10_q16`, `nv_m7_sort_u32`,
  `nv_m7_sort_tmp`, `nv_m7_rephase`) with `XPost := fun _ _ _ _ => False`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open scoped LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Closed `8`-Row `SpecTable`, `Env`, `TableImpl` & `ModuleOk` -/

/-- Closed `8`-row specification table covering `m7AnalyzeSort_fns` (`6` fns) and
`m7AnalyzeSortExterns` (`full_backtrack`, `full_walk`), all with `noExit = true`. -/
def m7AnalyzeSortSpecTable : List SpecEntry :=
  [ ⟨"full_sort_tmp_sift_m7", [i64, i64, i64, i64, i64], [],
      Full.FullMinSpecs.fullSortTmpSiftSpec, true⟩
  , ⟨"full_sort_tmp_heap_m7", [i64, i64, i64, i64], [], m7SortTmpHeapSpec, true⟩
  , ⟨"full_sort_tmp_m7", [i64], [], m7SortTmpSpec, true⟩
  , ⟨"full_sort_u32_m7", [i64, i32], [], m7SortU32SortedSpec, true⟩
  , ⟨"full_log10_q16_m7", [i64], [i64], m7Log10Q16Spec, true⟩
  , ⟨"full_rephase_m7", [i64], [], FullM5Sched.m5RephaseSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_walk", [i64], [], Full.fullWalkSpec, true⟩
  ]

theorem m7AnalyzeSortSpecTable_length : m7AnalyzeSortSpecTable.length = 8 := by t_kernel_rfl

private theorem m7AnalyzeSortSpecTable_nodup :
    (m7AnalyzeSortSpecTable.map SpecEntry.name).Nodup := by
  show
    ( [ "full_sort_tmp_sift_m7", "full_sort_tmp_heap_m7", "full_sort_tmp_m7",
        "full_sort_u32_m7", "full_log10_q16_m7", "full_rephase_m7",
        "full_backtrack", "full_walk" ] : List String).Nodup
  decide

theorem m7AnalyzeSortSpecTable_allNoExit :
    m7AnalyzeSortSpecTable.all (·.noExit) = true := by t_kernel_rfl

theorem m7AnalyzeSortSpecTable_noExit :
    ∀ e ∈ m7AnalyzeSortSpecTable, e.noExit = true :=
  fun e he => List.all_eq_true.mp m7AnalyzeSortSpecTable_allNoExit e he

/-- Specification environment induced by `m7AnalyzeSortSpecTable`. -/
def m7AnalyzeSortEnv : Env := Env.ofTable m7AnalyzeSortSpecTable

theorem m7AnalyzeSort_noExit :
    ∀ f as bs xs m Q X X',
      m7AnalyzeSortEnv f as bs xs m Q X → m7AnalyzeSortEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7AnalyzeSortSpecTable_noExit

private theorem m7_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (i : Nat) (hi : m7AnalyzeSortSpecTable[i]? = some ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m7AnalyzeSortEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) (List.mem_of_getElem? hi)
      m7AnalyzeSortSpecTable_nodup (by simpa only [SpecEntry.eff, ite_true] using hno xs m Q X hs)

theorem m7AnalyzeSort_allFns_wf : AllFns Fn.Wf m7AnalyzeSort_fns :=
  ⟨full_sort_tmp_sift_m7_wf, full_sort_tmp_heap_m7_wf, full_sort_tmp_m7_wf,
   full_sort_u32_m7_wf, full_log10_q16_m7_wf, full_rephase_m7_wf, trivial⟩

private theorem m7_sort_tmp_heap_impl :
    SpecEntry.Impl m7AnalyzeSortEnv full_sort_tmp_heap_m7
      ⟨"full_sort_tmp_heap_m7", [i64, i64, i64, i64], [], m7SortTmpHeapSpec, true⟩ :=
  .of (full_sort_tmp_heap_m7_wp m7AnalyzeSortEnv (m7_row 0 rfl fun _ _ _ _ h => h))

private theorem m7_sort_tmp_impl :
    SpecEntry.Impl m7AnalyzeSortEnv full_sort_tmp_m7
      ⟨"full_sort_tmp_m7", [i64], [], m7SortTmpSpec, true⟩ :=
  .of (full_sort_tmp_m7_wp m7AnalyzeSortEnv
    (m7_row 1 rfl fun _ _ _ _ => m7SortTmpHeapSpec_monoX))

private theorem m7_rephase_impl :
    SpecEntry.Impl m7AnalyzeSortEnv full_rephase_m7
      ⟨"full_rephase_m7", [i64], [], FullM5Sched.m5RephaseSpec, true⟩ :=
  .of (full_rephase_m7_wp m7AnalyzeSortEnv
    (m7_row 6 rfl fun _ _ _ _ h => h)
    (m7_row 7 rfl fun _ _ _ _ h => h)
    (m7_row 4 rfl fun _ _ _ _ => m7Log10Q16Spec_monoX))

/-- Row-by-row `TableImpl` for `m7AnalyzeSort_fns` (`6` fns) against `m7AnalyzeSortSpecTable`. -/
theorem m7AnalyzeSort_tableImpl :
    TableImpl m7AnalyzeSortEnv m7AnalyzeSort_fns m7AnalyzeSortSpecTable :=
  ⟨.of (full_sort_tmp_sift_m7_wp m7AnalyzeSortEnv),
    ⟨m7_sort_tmp_heap_impl,
    ⟨m7_sort_tmp_impl,
    ⟨.of (full_sort_u32_m7_wp m7AnalyzeSortEnv),
    ⟨.of (full_log10_q16_m7_wp m7AnalyzeSortEnv),
    ⟨m7_rephase_impl, trivial⟩⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` for standalone `m7AnalyzeSortModule` under `m7AnalyzeSortEnv`. -/
theorem m7AnalyzeSort_moduleOk : ModuleOk m7AnalyzeSortEnv m7AnalyzeSortModule :=
  Env.ofTable_moduleOk m7AnalyzeSort_acyclic m7AnalyzeSort_allFns_wf m7AnalyzeSort_tableImpl

/-! ## 2. Drop-In `Fn` WP Wrappers -/

theorem m7SortTmpFn_wp :
    ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      m7SortTmpSpec args m Q X → Func.wp m7AnalyzeSortEnv m7SortTmpFn.body args m Q X :=
  full_sort_tmp_m7_wp m7AnalyzeSortEnv (m7_row 1 rfl fun _ _ _ _ => m7SortTmpHeapSpec_monoX)

theorem m7SortTmpFn_small_canonical_wp :
    ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullSortTmpSpec args m Q X →
      (∀ c s R, args.1 = c.hdr → s.LengthsOk c → (FullMem c s ⋆ R) m → s.core.tmp_len ≤ 16) →
      Func.wp m7AnalyzeSortEnv m7SortTmpFn.body args m Q X :=
  fun args m Q X h h16 => m7SortTmpFn_wp args m Q X (m7SortTmpSpec_of_canonical_small h h16)

theorem m7SortU32Fn_wp :
    ∀ (args : Tup Val [i64, i32]) (m : Mem 64) (Q : Post []) (X : XPost),
      m7SortU32SortedSpec args m Q X → Func.wp m7AnalyzeSortEnv m7SortU32Fn.body args m Q X :=
  full_sort_u32_m7_wp m7AnalyzeSortEnv

theorem m7SortU32Fn_canonical_wp (Γ : Env) :
    ∀ (args : Tup Val [i64, i32]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullSortU32Spec args m Q X → Func.wp Γ m7SortU32Fn.body args m Q X :=
  full_sort_u32_m7_canonical_wp Γ

theorem m7Log10Q16Fn_wp :
    ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      m7Log10Q16Spec a m Q X → Func.wp m7AnalyzeSortEnv m7Log10Q16Fn.body a m Q X :=
  full_log10_q16_m7_wp m7AnalyzeSortEnv

theorem m7RephaseFn_wp :
    ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      FullM5Sched.m5RephaseSpec a m Q X → Func.wp m7AnalyzeSortEnv m7RephaseFn.body a m Q X :=
  full_rephase_m7_wp m7AnalyzeSortEnv
    (m7_row 6 rfl fun _ _ _ _ h => h)
    (m7_row 7 rfl fun _ _ _ _ h => h)
    (m7_row 4 rfl fun _ _ _ _ => m7Log10Q16Spec_monoX)

theorem m7RephaseFn_canonical_wp :
    ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullRephaseSpec a m Q X →
      (∀ c s R, a.1 = c.hdr → s.LengthsOk c → (FullMem c s ⋆ R) m → s.scratch.stable ≠ 0#64) →
      Func.wp m7AnalyzeSortEnv m7RephaseFn.body a m Q X := by
  intro a m Q X ⟨c, F0, s, R, heq, hinv, hm, hQ⟩ hst
  rcases a with ⟨h, ⟨⟩⟩
  dsimp only at heq hst
  subst heq
  exact m7RephaseFn_wp (c.hdr, ()) m Q X (FullM5Sched.m5RephaseSpec_of_stable
    ⟨c, F0, s, R, rfl, hst c s R rfl hinv.lengths hm, hinv, hm, hQ⟩)

/-! ## 3. Concrete `Mem 64` Non-Vacuity (`XPost := False`, `m7AnalyzeSortEnv`) -/

/-- Pure `Mem 64` preservation witness for `full_log10_q16_m7` (`n = 1000`, `X := False`). -/
theorem nv_m7_log10_q16 :
    Func.wp m7AnalyzeSortEnv m7Log10Q16Fn.body (1000#64, ()) (∅ : Mem 64)
      (fun res m' => res.1.toNat < 20 * 65536 ∧ 65536 ≤ res.1.toNat ∧ m' = (∅ : Mem 64))
      (fun _ _ _ _ => False) := by
  apply m7Log10Q16Fn_wp
  rw [m7Log10Q16Spec_eq_m5]
  exact fun _ hr_lt hr_ge => ⟨hr_lt, hr_ge (by decide), rfl⟩

/-- Concrete `17`-element descending `u32` array exercising multi-gap Shellsort (`13 -> 4 -> 1`). -/
def nvM7U32Arr : List (BitVec 32) :=
  [ 17#32, 16#32, 15#32, 14#32, 13#32, 12#32, 11#32, 10#32, 9#32,
    8#32, 7#32, 6#32, 5#32, 4#32, 3#32, 2#32, 1#32 ]

/-- Concrete `68`-byte `Mem 64` image for `nvM7U32Arr` at `0x1000`. -/
def nvM7U32Mem : Mem 64 := (bytesOf (t := i32) nvM7U32Arr).At 0x1000#64

/-- Concrete `Mem 64` non-vacuity (`X := False`) for `full_sort_u32_m7` on `17` descending
items: returns an in-place sorted permutation preserving heap safety. -/
theorem nv_m7_sort_u32 :
    Func.wp m7AnalyzeSortEnv m7SortU32Fn.body (0x1000#64, 17#32, ()) nvM7U32Mem
      (fun () m' => ∃ arr',
        arr'.length = 17 ∧ (arr'.take 17).Perm nvM7U32Arr ∧ M7SortedU32 arr' 17 ∧
        array (t := i32) 0x1000#64 arr' m')
      (fun _ _ _ _ => False) := by
  have hm0 : array (t := i32) 0x1000#64 nvM7U32Arr nvM7U32Mem :=
    array_bytes (t := i32) 0x1000#64 nvM7U32Arr (by decide)
  have hm : (array (t := i32) 0x1000#64 nvM7U32Arr ⋆ emp) nvM7U32Mem := by
    rw [sep_emp]; exact hm0
  have h17 : (17#32).toNat = 17 := rfl
  have hnv : nvM7U32Arr.take 17 = nvM7U32Arr := by t_kernel_rfl
  exact m7SortU32Fn_wp (0x1000#64, 17#32, ()) nvM7U32Mem _ _
    (m7SortU32SortedSpec_of (by decide) hm fun arr' m' hlen hperm _ hsort hm' => by
      rw [sep_emp] at hm'
      rw [h17, hnv] at hperm
      exact ⟨arr', hlen, hperm, hsort, hm'⟩)

private theorem nvM7OneLitMem_sep : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
  rw [sep_emp]; exact nvOneLitMem_ok

private theorem m7_nv_arr_p {t : Ty} (a : BitVec 64) (xs : List (Val t)) (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf (t := t) xs).length = n ∧ array (t := t) a xs ((bytesOf (t := t) xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem m7_nv_arr64_p (a : BitVec 64) (xs : List (BitVec 64)) (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem m7_nv_pad_p (a : BitVec 64) (p : Nat) :
    (List.replicate p (0 : UInt8)).length = p ∧
      region a p ((List.replicate p (0 : UInt8)).At a) :=
  ⟨List.length_replicate .., ⟨List.replicate p 0, List.length_replicate .., rfl⟩⟩

private theorem m7_nv_join_pair {a1 a2 : BitVec 64} {n1 n2 : Nat} {bs1 bs2 : List UInt8}
    {P Q : Mem 64 → Prop} (h1 : bs1.length = n1 ∧ P (bs1.At a1))
    (h2 : bs2.length = n2 ∧ Q (bs2.At a2))
    (hadd : a2 = a1 + BitVec.ofNat 64 n1) (hfit : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a1) := by
  have hl : bs1.length + bs2.length ≤ 2 ^ 64 := by rw [h1.1, h2.1]; exact hfit
  have heq : (Eq (bs1.At a1) ⋆ Eq (bs2.At (a1 + BitVec.ofNat 64 bs1.length)))
      ((bs1 ++ bs2).At a1) :=
    (congrFun (Mem.At_append_sep bs1 bs2 a1 hl) ((bs1 ++ bs2).At a1)).mp rfl
  rw [h1.1, ← hadd] at heq
  exact ⟨by rw [List.length_append, h1.1, h2.1],
    sep_mono2 (fun _ hx => hx ▸ h1.2) (fun _ hy => hy ▸ h2.2) _ heq⟩

private theorem m7_nv_arr_pad_p {t : Ty} (a : BitVec 64) (xs : List (Val t))
    (n p : Nat) (hn : t.bytes * xs.length = n) (hbd : n + p ≤ 2 ^ 64) :
    (bytesOf (t := t) xs ++ List.replicate p (0 : UInt8)).length = n + p ∧
      (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) p)
        ((bytesOf (t := t) xs ++ List.replicate p (0 : UInt8)).At a) :=
  m7_nv_join_pair (m7_nv_arr_p a xs n hn (by omega))
    (m7_nv_pad_p (a + BitVec.ofNat 64 n) p) rfl hbd

private theorem m7_nv_sep_reorg {bs : List UInt8} {a : BitVec 64} {n : Nat}
    {P Q : Mem 64 → Prop} (h : bs.length = n ∧ P (bs.At a)) (hPQ : ∀ f, P f → Q f) :
    bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, hPQ _ h.2⟩

/-- `18`-variable `FullCfg` (`avail = 4508`, `wcap = 1`) for `tmp_len = 18 > 16` O(n) NV. -/
def nvM7Sort18Cfg : FullCfg :=
  { hdr := 0x1000#64
    avail := 4508
    mv := 18
    max_vars := 18
    bva_cap := 0
    nc := 1
    arena_cap := 0
    wcap := 1
    delayed_cap := 0
    red_cap := 0
    extend_cap := 0
    scratch_cap := 0
    hbva := rfl
    hmv := by decide
    hmaxv := by decide
    hnc := by decide
    harena := by decide
    hwcap := by decide
    hdel := by decide
    hred := by decide
    hext := by decide
    hscr := by decide
    havail_fit := by decide
    hsize := by decide }

/-- Mixed-level (`1`, `2`, `3`) & reversed-`trail_pos` `tmp[1..18)` with asserting `tmp[0]`. -/
def nvM7Sort18Tmp : List (BitVec 32) :=
  [ 0#32, 34#32, 32#32, 30#32, 28#32, 26#32, 24#32, 22#32, 20#32,
    18#32, 16#32, 14#32, 12#32, 10#32, 8#32, 6#32, 4#32, 2#32 ]

/-- Variable levels spanning `[1, 3]` across blocks of `6` variables. -/
def nvM7Sort18Lvl : List (BitVec 32) :=
  [ 3#32, 3#32, 3#32, 3#32, 3#32, 3#32,
    1#32, 1#32, 1#32, 1#32, 1#32, 1#32,
    2#32, 2#32, 2#32, 2#32, 2#32, 2#32 ]

/-- Strictly increasing `trail_pos` (`0..17`) forcing run-sorting tie-breaking per bucket. -/
def nvM7Sort18Tpos : List (BitVec 32) :=
  [ 0#32, 1#32, 2#32, 3#32, 4#32, 5#32, 6#32, 7#32, 8#32,
    9#32, 10#32, 11#32, 12#32, 13#32, 14#32, 15#32, 16#32, 17#32 ]

/-- Zero-initialized `FullScratch` of `nvM7Sort18Cfg` (`max_vars = 18`). -/
def nvM7Sort18Scratch : FullScratch :=
  { heap_len := 0, scinc := 0#64, rel_period := 0#64, rel_limit := 0#64, rel_wait := 0#64
    rel_u := 0#64, rel_v := 0#64, rel_trigger := 0#64, conflicts := 0#64
    learned_lits := 0#64, min_removed := 0#64, delayed_len := 0, stable := 0#64
    switched := 0#64, mode_count := 0#64, mode_confl_lim := 0#64, mode_tick_lim := 0#64
    mode_saved_ticks := 0#64, search_ticks := 0#64, q_first := 0#64, q_last := 0#64
    q_search_idx := 0#64, q_search_stamp := 0#64, q_cur_stamp := 0#64
    target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 0#64
    rephased := 0#64, reduce_limit := 0#64, reductions := 0#64, tier1 := 0#64
    tier2 := 0#64, restarts := 0#64, restart_limit := 0#64, ema_fast_biased := 0#64
    ema_fast_exp := 0#64, ema_slow_biased := 0#64, ema_slow_exp := 0#64, extend_len := 0
    rng_state := 0#64, chrono_levels := 0#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64
    probe_limit := 0#64, probings := 0#64, elim_limit := 0#64, eliminations := 0#64
    elim_bound := 0#64, iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64
    viv_cnt := 0#64, subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64
    bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64
    fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64
    walk_vals := List.replicate 36 0#8, phases := List.replicate 18 0#8
    phases_target := List.replicate 18 0#8, phases_best := List.replicate 18 0#8
    walk_best := List.replicate 18 0#8, heap := List.replicate 18 0#32
    pos := List.replicate 18 0#32, shrink_stk := List.replicate 18 0#32
    q_prev := List.replicate 18 0#32, q_next := List.replicate 18 0#32
    q_stamp := List.replicate 18 0#32, wsort := List.replicate 36 0#32
    work_stk1 := List.replicate 36 0#32, work_stk2 := List.replicate 36 0#32
    tarjan_mark := List.replicate 36 0#32, tarjan_reach := List.replicate 36 0#32
    score := List.replicate 18 0#64, sim_sig := List.replicate 18 0#64
    glue_used := List.replicate 64 0#32, last_learned := List.replicate 16 0#32
    delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] }

/-- `18`-variable `FullState` (`tmp_len = 18 > 16`) for `full_sort_tmp_m7` O(n) NV. -/
def nvM7Sort18State : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := 18, unassigned := 0#64
        arena_len := 0, wlen := 0, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64, unflushed := 0#64, probing := 0#64
        trail_end := 0, propagated := 0, cur_level := 0, fuel := 0#64
        confl_ref := 0#64, confl_type := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64
        tmp_cnt := 0, tmp_len := 18, min_clr_len := 0, min_clr_full := 0#64
        oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := List.replicate 36 0#8, lit_mark := List.replicate 36 0#8
        mrk := List.replicate 18 0#8, flags := List.replicate 18 0#32
        lvl := nvM7Sort18Lvl, rsns := List.replicate 18 0#32
        trl := List.replicate 18 0#32, trail_pos := nvM7Sort18Tpos
        tmp := nvM7Sort18Tmp, min_clr := List.replicate 18 0#32
        frame_trail := List.replicate 19 0#32, frame_dec := List.replicate 19 0#32
        wvec := List.replicate 72 0#32, repr := List.replicate 36 0#32
        min_stk := List.replicate 38 0#32, arena := [], wstk := [0#32] }
    scratch := nvM7Sort18Scratch }

private def nv18BlockHdr : List UInt8 :=
  let c := nvM7Sort18Cfg; let s := nvM7Sort18State
  bytes64 [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ++
    bytes64 (Full.hdrTailWords c s)

private def nv18BlockBytes : List UInt8 :=
  let sc := nvM7Sort18State.scratch; let k := nvM7Sort18State.core
  (bytesOf (t := i8) k.vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.walk_vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) k.lit_mark ++ List.replicate 4 0) ++
  (bytesOf (t := i8) k.mrk ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases_target ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases_best ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.walk_best ++ List.replicate 6 0)

private def nv18BlockU32A : List UInt8 :=
  let k := nvM7Sort18State.core
  (bytesOf (t := i32) k.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trail_pos ++ List.replicate 8 0)

private def nv18BlockU32B : List UInt8 :=
  let k := nvM7Sort18State.core; let sc := nvM7Sort18State.scratch
  (bytesOf (t := i32) k.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.shrink_stk ++ List.replicate 8 0)

private def nv18BlockU32C : List UInt8 :=
  let k := nvM7Sort18State.core; let sc := nvM7Sort18State.scratch
  (bytesOf (t := i32) sc.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) k.frame_dec ++ List.replicate 4 0)

private def nv18BlockWvec : List UInt8 :=
  let k := nvM7Sort18State.core; let sc := nvM7Sort18State.scratch
  bytesOf (t := i32) k.wvec ++ bytesOf (t := i32) k.repr ++
  bytesOf (t := i32) sc.wsort ++ bytesOf (t := i32) sc.work_stk1 ++
  bytesOf (t := i32) sc.work_stk2 ++ bytesOf (t := i32) sc.tarjan_mark ++
  bytesOf (t := i32) sc.tarjan_reach ++ bytes64 sc.score ++ bytes64 sc.sim_sig

private def nv18BlockTail : List UInt8 :=
  let k := nvM7Sort18State.core; let sc := nvM7Sort18State.scratch
  bytesOf (t := i32) k.min_stk ++ bytesOf (t := i32) sc.glue_used ++
  bytesOf (t := i32) sc.last_learned ++ bytesOf (t := i32) k.arena ++
  bytesOf (t := i32) k.wstk ++ bytesOf (t := i32) sc.delayed ++
  bytesOf (t := i32) sc.red_refs ++ bytesOf (t := i32) sc.extend_stk ++
  bytesOf (t := i32) sc.scratch_buf ++ List.replicate 0 0

/-- Concrete `4508`-byte `Mem 64` image for `nvM7Sort18State` at `nvM7Sort18Cfg.hdr`. -/
def nvM7Sort18Mem : Mem 64 :=
  (nv18BlockHdr ++ nv18BlockBytes ++ nv18BlockU32A ++ nv18BlockU32B ++
    nv18BlockU32C ++ nv18BlockWvec ++ nv18BlockTail).At nvM7Sort18Cfg.hdr

private theorem nvM7Sort18_lengths : nvM7Sort18State.LengthsOk nvM7Sort18Cfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvM7Sort18Mem_ok :
    (FullMem nvM7Sort18Cfg nvM7Sort18State ⋆ emp) nvM7Sort18Mem := by
  let c := nvM7Sort18Cfg; let s := nvM7Sort18State
  have hv4 : valsBytes c.max_vars - 2 * c.max_vars = 4 := by decide
  have h2m : 2 * c.max_vars = 36 := by decide
  have hm6 : markBytes c.max_vars - c.max_vars = 6 := by decide
  have hm18 : c.max_vars = 18 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by decide
  have h4m : 4 * c.max_vars = 72 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by decide
  have h4p : 4 * (c.max_vars + 1) = 76 := by decide
  have hsl : c.slack = 0 := by decide
  have hHdr : nv18BlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c s)) (nv18BlockHdr.At c.hdr) :=
    m7_nv_join_pair
      ⟨rfl, dimacsState_bytes c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val⟩
      (m7_nv_arr64_p (c.hdr + 32) (Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by decide)
  have hBytes : nv18BlockBytes.length = 240 ∧
      ((array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullScrByteArrs c s.scratch ⋆ c.padBytes) (nv18BlockBytes.At c.pVals) := by
    have h1 := m7_nv_arr_pad_p (t := i8) c.pVals s.core.vals 36 4 rfl (by decide)
    have h2 := m7_nv_arr_pad_p (t := i8) c.pWalkVals s.scratch.walk_vals 36 4 rfl (by decide)
    have h3 := m7_nv_arr_pad_p (t := i8) c.pLitMark s.core.lit_mark 36 4 rfl (by decide)
    have h4 := m7_nv_arr_pad_p (t := i8) c.pMark s.core.mrk 18 6 rfl (by decide)
    have h5 := m7_nv_arr_pad_p (t := i8) c.pPhases s.scratch.phases 18 6 rfl (by decide)
    have h6 := m7_nv_arr_pad_p (t := i8) c.pPhasesTarget s.scratch.phases_target 18 6 rfl
      (by decide)
    have h7 := m7_nv_arr_pad_p (t := i8) c.pPhasesBest s.scratch.phases_best 18 6 rfl (by decide)
    have h8 := m7_nv_arr_pad_p (t := i8) c.pWalkBest s.scratch.walk_best 18 6 rfl (by decide)
    have j12 := m7_nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := m7_nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := m7_nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := m7_nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := m7_nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := m7_nv_join_pair j123456 h7 (by decide) (by decide)
    exact m7_nv_sep_reorg (m7_nv_join_pair j1234567 h8 (by decide) (by decide)) fun _ hm => by
      have pB : ∀ {A1 A2 A3 A4 A5 A6 A7 A8 P1 P2 P3 P4 P5 P6 P7 P8 : Mem 64 → Prop} {k},
          ((((((((A1 ⋆ P1) ⋆ (A2 ⋆ P2)) ⋆ (A3 ⋆ P3)) ⋆ (A4 ⋆ P4)) ⋆
            (A5 ⋆ P5)) ⋆ (A6 ⋆ P6)) ⋆ (A7 ⋆ P7)) ⋆ (A8 ⋆ P8)) k →
          ((A1 ⋆ A3 ⋆ A4) ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆
            (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8)) k := fun x => sep_ac x
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hv4, h2m, hm6, hm18]; exact pB hm
  have hU32A : nv18BlockU32A.length = 400 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nv18BlockU32A.At c.pFlags) := by
    have h1 := m7_nv_arr_pad_p (t := i32) c.pFlags s.core.flags 72 8 rfl (by decide)
    have h2 := m7_nv_arr_pad_p (t := i32) c.pLevel s.core.lvl 72 8 rfl (by decide)
    have h3 := m7_nv_arr_pad_p (t := i32) c.pReason s.core.rsns 72 8 rfl (by decide)
    have h4 := m7_nv_arr_pad_p (t := i32) c.pTrail s.core.trl 72 8 rfl (by decide)
    have h5 := m7_nv_arr_pad_p (t := i32) c.pTrailPos s.core.trail_pos 72 8 rfl (by decide)
    have j12 := m7_nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := m7_nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := m7_nv_join_pair j123 h4 (by decide) (by decide)
    exact m7_nv_sep_reorg (m7_nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu8, h4m]; exact sep_ac hm
  have hU32B : nv18BlockU32B.length = 400 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nv18BlockU32B.At c.pTmp) := by
    have h1 := m7_nv_arr_pad_p (t := i32) c.pTmp s.core.tmp 72 8 rfl (by decide)
    have h2 := m7_nv_arr_pad_p (t := i32) c.pHeap s.scratch.heap 72 8 rfl (by decide)
    have h3 := m7_nv_arr_pad_p (t := i32) c.pPos s.scratch.pos 72 8 rfl (by decide)
    have h4 := m7_nv_arr_pad_p (t := i32) c.pMinClr s.core.min_clr 72 8 rfl (by decide)
    have h5 := m7_nv_arr_pad_p (t := i32) c.pShrinkStk s.scratch.shrink_stk 72 8 rfl (by decide)
    have j12 := m7_nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := m7_nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := m7_nv_join_pair j123 h4 (by decide) (by decide)
    exact m7_nv_sep_reorg (m7_nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu8, h4m]; exact sep_ac hm
  have hU32C : nv18BlockU32C.length = 400 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nv18BlockU32C.At c.pQPrev) := by
    have h1 := m7_nv_arr_pad_p (t := i32) c.pQPrev s.scratch.q_prev 72 8 rfl (by decide)
    have h2 := m7_nv_arr_pad_p (t := i32) c.pQNext s.scratch.q_next 72 8 rfl (by decide)
    have h3 := m7_nv_arr_pad_p (t := i32) c.pQStamp s.scratch.q_stamp 72 8 rfl (by decide)
    have h4 := m7_nv_arr_pad_p (t := i32) c.pFrameTrail s.core.frame_trail 76 4 rfl (by decide)
    have h5 := m7_nv_arr_pad_p (t := i32) c.pFrameDec s.core.frame_dec 76 4 rfl (by decide)
    have j12 := m7_nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := m7_nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := m7_nv_join_pair j123 h4 (by decide) (by decide)
    exact m7_nv_sep_reorg (m7_nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu8, hu4, h4m, h4p]; exact sep_ac hm
  have hWvec : nv18BlockWvec.length = 1440 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nv18BlockWvec.At c.pWvec) := by
    have h1 := m7_nv_arr_p (t := i32) c.pWvec s.core.wvec 288 rfl (by decide)
    have h2 := m7_nv_arr_p (t := i32) c.pRepr s.core.repr 144 rfl (by decide)
    have h3 := m7_nv_arr_p (t := i32) c.pWsort s.scratch.wsort 144 rfl (by decide)
    have h4 := m7_nv_arr_p (t := i32) c.pWorkStk1 s.scratch.work_stk1 144 rfl (by decide)
    have h5 := m7_nv_arr_p (t := i32) c.pWorkStk2 s.scratch.work_stk2 144 rfl (by decide)
    have h6 := m7_nv_arr_p (t := i32) c.pTarjanMark s.scratch.tarjan_mark 144 rfl (by decide)
    have h7 := m7_nv_arr_p (t := i32) c.pTarjanReach s.scratch.tarjan_reach 144 rfl (by decide)
    have h8 := m7_nv_arr64_p c.pScore s.scratch.score 144 rfl (by decide)
    have h9 := m7_nv_arr64_p c.pSimSig s.scratch.sim_sig 144 rfl (by decide)
    have j12 := m7_nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := m7_nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := m7_nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := m7_nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := m7_nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := m7_nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := m7_nv_join_pair j1234567 h8 (by decide) (by decide)
    exact m7_nv_sep_reorg (m7_nv_join_pair j12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nv18BlockTail.length = 476 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nv18BlockTail.At c.pMinStk) := by
    have h1 := m7_nv_arr_p (t := i32) c.pMinStk s.core.min_stk 152 rfl (by decide)
    have h2 := m7_nv_arr_p (t := i32) c.pGlueUsed s.scratch.glue_used 256 rfl (by decide)
    have h3 := m7_nv_arr_p (t := i32) c.pLastLearned s.scratch.last_learned 64 rfl (by decide)
    have h4 := m7_nv_arr_p (t := i32) c.pArena s.core.arena 0 rfl (by decide)
    have h5 := m7_nv_arr_p (t := i32) c.pWstk s.core.wstk 4 rfl (by decide)
    have h6 := m7_nv_arr_p (t := i32) c.pDelayed s.scratch.delayed 0 rfl (by decide)
    have h7 := m7_nv_arr_p (t := i32) c.pRedRefs s.scratch.red_refs 0 rfl (by decide)
    have h8 := m7_nv_arr_p (t := i32) c.pExtendStk s.scratch.extend_stk 0 rfl (by decide)
    have h9 := m7_nv_arr_p (t := i32) c.pScratchBuf s.scratch.scratch_buf 0 rfl (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 (0 : UInt8)).At c.pSlack) := by
      rw [hsl]; exact m7_nv_pad_p c.pSlack 0
    have j12 := m7_nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := m7_nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := m7_nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := m7_nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := m7_nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := m7_nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := m7_nv_join_pair j1234567 h8 (by decide) (by decide)
    have j123456789 := m7_nv_join_pair j12345678 h9 (by decide) (by decide)
    exact m7_nv_sep_reorg (m7_nv_join_pair j123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := m7_nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := m7_nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := m7_nv_sep_reorg (m7_nv_join_pair h02 hU32B (by decide) (by decide)) fun _ hm => by
    have p1 : ∀ {D H CB SB PB UA PA T Hp Ps Mc Sh PB2 : Mem 64 → Prop} {k},
        (((D ⋆ H) ⋆ (CB ⋆ SB ⋆ PB)) ⋆ (UA ⋆ PA) ⋆ ((T ⋆ Hp ⋆ Ps ⋆ Mc ⋆ Sh) ⋆ PB2)) k →
        ((D ⋆ H) ⋆ ((CB ⋆ (UA ⋆ T ⋆ Mc)) ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh)) ⋆ (PB ⋆ PA ⋆ PB2))) k :=
      fun x => sep_ac x
    exact p1 hm
  have h04 := m7_nv_sep_reorg (m7_nv_join_pair h03 hU32C (by decide) (by decide)) fun _ hm => by
    have p2 : ∀ {DH C1 S1 P1 Qp Qn Qs FTr FDec PC : Mem 64 → Prop} {k},
        ((DH ⋆ (C1 ⋆ S1 ⋆ P1)) ⋆
          ((Qp ⋆ Qn ⋆ Qs) ⋆ (FTr ⋆ FDec) ⋆ PC)) k →
        (DH ⋆ ((C1 ⋆ FTr ⋆ FDec) ⋆ (S1 ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ (P1 ⋆ PC))) k :=
      fun x => sep_ac x
    exact p2 hm
  have h05 := m7_nv_join_pair h04 hWvec (by decide) (by decide)
  have h06 : (nv18BlockHdr ++ nv18BlockBytes ++ nv18BlockU32A ++ nv18BlockU32B ++
      nv18BlockU32C ++ nv18BlockWvec ++ nv18BlockTail).length = 4508 ∧
      FullMem c s ((nv18BlockHdr ++ nv18BlockBytes ++ nv18BlockU32A ++ nv18BlockU32B ++
        nv18BlockU32C ++ nv18BlockWvec ++ nv18BlockTail).At c.hdr) := by
    refine m7_nv_sep_reorg (m7_nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => ?_
    have p3 : ∀ {D H CoreB ScrB P2 Wv Re SW Sc Ss MS Gu Ll CD SD SL : Mem 64 → Prop} {k},
        (((D ⋆ H ⋆ (CoreB ⋆ ScrB ⋆ P2)) ⋆ ((Wv ⋆ Re) ⋆ SW ⋆ (Sc ⋆ Ss))) ⋆
          (MS ⋆ (Gu ⋆ Ll) ⋆ CD ⋆ SD ⋆ SL)) k →
        (D ⋆ H ⋆ (CoreB ⋆ Wv ⋆ Re ⋆ MS ⋆ CD) ⋆ (ScrB ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆
          (P2 ⋆ SL)) k :=
      fun x => sep_ac x
    have p4 : ∀ {D H CB UA_T_Mc FTr FDec Wv Re MS CD Scr Pad : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ (((CB ⋆ UA_T_Mc ⋆ FTr ⋆ FDec) ⋆ Wv ⋆ Re ⋆ MS ⋆ CD)) ⋆ Scr ⋆ Pad) k →
        (D ⋆ H ⋆ (CB ⋆ UA_T_Mc ⋆ (FTr ⋆ FDec ⋆ Wv ⋆ Re ⋆ MS) ⋆ CD) ⋆ Scr ⋆ Pad) k :=
      fun x => sep_ac x
    have p5 : ∀ {D H Core SB HpPsSh QpQnQs SW Sc Ss Gu Ll SD Pad : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ Core ⋆ (((SB ⋆ HpPsSh) ⋆ QpQnQs) ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆ Pad) k →
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ (HpPsSh ⋆ QpQnQs) ⋆ SW ⋆ (Sc ⋆ Ss ⋆ Gu ⋆ Ll) ⋆ SD) ⋆ Pad) k :=
      fun x => sep_ac x
    have p6 : ∀ {D H Core Scr PB PA PB2 PC SL : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ Core ⋆ Scr ⋆ (((PB ⋆ PA ⋆ PB2) ⋆ PC) ⋆ SL)) k →
        (D ⋆ H ⋆ Core ⋆ Scr ⋆ (PB ⋆ PA ⋆ PB2 ⋆ PC ⋆ SL)) k :=
      fun x => sep_ac x
    have p7 : ∀ {D H Core SB Hp Ps Sh Qp Qn Qs SW Meta SD Pad : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ ((Hp ⋆ Ps ⋆ Sh) ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k →
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh ⋆ Qp ⋆ Qn ⋆ Qs) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k :=
      fun x => sep_ac x
    unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B
      FullScratchArrays FullScrU32A FullScrMetaArrs FullCfg.pad
    exact p7 (p6 (p5 (p4 (p3 hm))))
  rw [sep_emp]
  exact h06.2

/-- Concrete `Mem 64` non-vacuity (`X := False`) for `full_sort_tmp_m7` on `nvM7Sort18Mem`
(`tmp_len = 18 > 16`, exercising O(n) shadow bucketing, prefix sum, scatter, and `(lvl,
trail_pos)` tie-breaking while leaving `work_stk2` untouched). -/
theorem nv_m7_sort_tmp :
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
      (fun _ _ _ _ => False) := by
  have htl : nvM7Sort18State.core.tmp_len = 18 := rfl
  have hbd : ∀ k, 1 ≤ k → k < 18 →
      (nvM7Sort18State.core.tmp[k]?.getD 0#32).toNat < 2 * nvM7Sort18Cfg.max_vars :=
    fun k _ hk =>
      (by decide : ∀ q < 18,
        (nvM7Sort18State.core.tmp[q]?.getD 0#32).toNat < 2 * nvM7Sort18Cfg.max_vars) k hk
  exact m7SortTmpFn_wp (nvM7Sort18Cfg.hdr, ()) nvM7Sort18Mem _ _
    (m7SortTmpSpec_of nvM7Sort18_lengths (Nat.le_refl 18) hbd nvM7Sort18Mem_ok
      fun tmp' wsort' m' hlen' _ _ hperm' h0' _ _ hsort' _ hpr hm' => by
        rw [sep_emp] at hm'
        exact ⟨tmp', wsort', hlen', hperm', h0' (by decide), hsort', rfl, hpr, hm'⟩)

private theorem nvM7OneLitF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Stable-mode (`stable = 1#64`, `rephased = 1#64` entering `rephase_best`) `FullState`. -/
def nvM7RephaseState : FullState :=
  { nvOneLitState with
    core :=
      { nvOneLitState.core with
        vals := [0#8, 0#8]
        trail_end := 0
        propagated := 0 }
    scratch :=
      { nvOneLitState.scratch with
        stable := 1#64
        rephased := 1#64 } }

/-- Concrete `Mem 64` carrying `FullCoreInv nvOneLitCfg nvOneLitF0 nvM7RephaseState`. -/
def nvM7RephaseMem : Mem 64 :=
  storeMem (storeMem (storeMem (storeMem (storeMem (storeMem nvOneLitMem
    i8 (nvOneLitCfg.pVals + 0#64) 0#8)
    i8 (nvOneLitCfg.pVals + 1#64) 0#8)
    i64 (nvOneLitCfg.hdr + 144) 0#64)
    i64 (nvOneLitCfg.hdr + 152) 0#64)
    i64 (nvOneLitCfg.hdr + 552) 1#64)
    i64 (nvOneLitCfg.hdr + 672) 1#64

private theorem nvM7Rephase_lengths : nvM7RephaseState.LengthsOk nvOneLitCfg :=
  ⟨{ nvOneLit_lengths.core_ok with
     vals_len := rfl
     trail_end_le := Nat.zero_le _
     propagated_le := Nat.zero_le _ },
   { nvOneLit_lengths.scratch_ok with }⟩

private theorem nvM7Rephase_inv : FullCoreInv nvOneLitCfg nvOneLitF0 nvM7RephaseState := by
  refine ⟨nvM7Rephase_lengths, [[0], [1]], fullWitnessInv_empty
    (hext := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩)
    (hinc := rfl) (hal := rfl)
    (hwvec := fun l hl => by
      have hcv : nvM7RephaseState.core.cur_vars = 1 := rfl
      rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact ⟨rfl, rfl⟩)
    (hte := rfl) (hcl := rfl) (hft0 := rfl)
    (hvals := fun l hl => by
      have hcv : nvM7RephaseState.core.cur_vars = 1 := rfl
      rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl)⟩

open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics in
private theorem nvM7RephaseMem_ok :
    (FullMem nvOneLitCfg nvM7RephaseState ⋆ emp) nvM7RephaseMem := by
  have h1 := (FullArenaTactics.store_full_vals (i := 0) (v := 0#8) (by decide)
    nvM7OneLitMem_sep).2
  have h2 := (FullArenaTactics.store_full_vals (i := 1) (v := 0#8) (by decide) h1).2
  have h3 := (FullArenaTactics.store_full_trail_end (v := 0) (by decide) h2).2
  have h4 := (FullArenaTactics.store_full_propagated (v := 0) (by decide) h3).2
  have h5 := (FullArenaTactics.store_full_stable (v := 1#64) h4).2
  have h6 := (FullArenaTactics.store_full_rephased (v := 1#64) h5).2
  simpa only [nvM7RephaseState, nvM7RephaseMem, nvOneLitState,
    show (([1#8, 0xFF#8] : List (BitVec 8)).set 0 0#8).set 1 0#8 = [0#8, 0#8] from rfl] using h6

/-- Concrete `Mem 64` UNSAT non-vacuity (`X := False`) for stable-mode `full_rephase_m7`
(`stable = 1#64`, `rephased = 1#64` entering `rephase_best`). -/
theorem nv_m7_rephase :
    Func.wp m7AnalyzeSortEnv m7RephaseFn.body (nvOneLitCfg.hdr, ()) nvM7RephaseMem
      (fun () m' => ∃ s',
        FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧
        s'.core.cur_level ≤ nvM7RephaseState.core.cur_level ∧
        s'.core.fuel.toNat ≤ nvM7RephaseState.core.fuel.toNat ∧
        FullExtScratchPres nvM7RephaseState s' ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  m7RephaseFn_wp (nvOneLitCfg.hdr, ()) nvM7RephaseMem _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvM7RephaseState, emp, rfl, nvM7Rephase_inv, nvM7RephaseMem_ok,
      fun _ _ _ _ _ _ _ _ _ _ _ _ hinv hcl0 hcl hfl hpr hm' => by
        rw [sep_emp] at hm'
        exact ⟨_, hinv, hcl0 (by decide), hcl, hfl, hpr, nvM7OneLitF0_unsat, hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
