module

public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
public import LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofDriver
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofNv
public import LeanQbe.T.Examples.Kissat.PatchModule
import all LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0a
import all LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
import all LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof1a
import all LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof1b
import all LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof2
import all LeanQbe.T.Examples.Kissat.FullFidelityBase
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBaseProof0
import all LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM6Sweep
import all LeanQbe.T.Examples.Kissat.FullM6SweepProofDriver
import LeanQbe.T.InlineLemmas
import LeanQbe.T.FlatLemmas

/-!
# Closed `PatchBundle` Certification, UNSAT Soundness & Concrete NV for `FullFidelityVivK6`

Zero-edit drop-in certification of `fidVivK6Bundle` (`6` repls + `4` `before`s = `473` fns)
and `fidVivK6NoBvaCommitBundle` (`5` repls + `4` `before`s = `473` fns) on `fidBaseModule`:

1. `fidVivK6Bundle` & `fidVivK6NoBvaCommitBundle` (`PatchModule.PatchBundle`),
   `fidVivK6SplicedModule`, `fidVivK6Env`, `fidVivK6NoBvaCommitEnv`, structural invariants
   (`length = 473`, `namesNodup`, `checkAcyclic = true`, `exits = []`).
2. `fidVivK6Spliced_moduleOk`, `fidVivK6NoBvaCommit_moduleOk`, `TableImpl`,
   `solve_bytes_sound`, `solve_bytes_host_sound`, `unsat_nv`.
3. Four concrete non-bailout `Mem 64` non-vacuity witnesses (`XPost := False`, under
   `fidVivK6Env`):
   - `nv_fid_unwatch_large` (`full_unwatch_large_fid_body`: backward scan + odd peel + u64/u32),
   - `nv_fid_vivify_delayed_irr` (`full_vivify_m6_hdr_fid_body`: `vivifyirr` delayed, `fuel = 100`),
   - `nv_fid_k6_propagate` (`full_k6_propagate_fid_body`: 2-var watched unit propagation),
   - `nv_fid_k6_core_m8` (`full_k6_core_m8_fid_body`: `nv = 4, nc = 2`, cached Kitten ptrs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivK6

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Bva
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBase
open LeanQbe.T.Examples.Kissat.PatchModule

/-! ## 1. `PatchBundle` Definitions & Structural Lemmas -/

/-- `SpecEntry` rows for the `4` inserted helper functions in `fidVivK6Befores`. -/
def fidVivK6BeforeRows : List SpecEntry :=
  [ ⟨"full_viv_collect_fid", [i64, i64], [i64], fullVivCollectFidSpec, true⟩
  , ⟨"full_viv_count_fid", [i64, i64], [], fullVivCountFidSpec, true⟩
  , ⟨"full_viv_sort2_fid", [i64, i64, i64], [], fullVivSort2FidSpec, true⟩
  , ⟨"full_viv_sort_fid", [i64, i64], [], fullVivSortFidSpec, true⟩ ]

/-- Associative `beforeRows` table keyed by `"full_vivify_tier_m6_hdr"`. -/
def fidVivK6BeforeRowAssoc : List (Sym × List SpecEntry) :=
  [("full_vivify_tier_m6_hdr", fidVivK6BeforeRows)]

/-- `SpecEntry` replacement rows for all `6` functions in `fidVivK6Repls`. -/
def fidVivK6ReplRows : List SpecEntry :=
  [ ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩
  , ⟨"full_k6_propagate", [i64], [i32], k6PropagateSpec, true⟩
  , ⟨"full_k6_core_m8", [i64], [], m8K6CoreSpec, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec, true⟩ ]

/-- `SpecEntry` replacement rows for `fidVivK6NoBvaCommitRepls` (`5` fns). -/
def fidVivK6NoBvaCommitReplRows : List SpecEntry := fidVivK6ReplRows.take 5

private def mkFidVivK6Bundle (withBva : Bool) : PatchBundle where
  baseMod := fidBaseModule
  baseTable := fidBaseSpecTable
  baseOk := fidBase_moduleOk
  repls := if withBva then fidVivK6Repls else fidVivK6NoBvaCommitRepls
  replRows := if withBva then fidVivK6ReplRows else fidVivK6NoBvaCommitReplRows
  befores := fidVivK6Befores
  beforeRows := fidVivK6BeforeRows
  rewiredRows := []

/-- Full `6`-repl + `4`-before `PatchBundle` over `fidBaseModule` (`473` fns). -/
def fidVivK6Bundle : PatchBundle := mkFidVivK6Bundle true

/-- `5`-repl + `4`-before `PatchBundle` omitting `full_bva_commit` (`473` fns). -/
def fidVivK6NoBvaCommitBundle : PatchBundle := mkFidVivK6Bundle false

abbrev fidVivK6SplicedFns : List Fn := fidVivK6Bundle.patchedFns
abbrev fidVivK6SplicedModule : LeanQbe.T.Module := fidVivK6Bundle.patchedMod
abbrev fidVivK6Env : Env := patchEnv fidVivK6Bundle

abbrev fidVivK6NoBvaCommitSplicedFns : List Fn := fidVivK6NoBvaCommitBundle.patchedFns
abbrev fidVivK6NoBvaCommitSplicedModule : LeanQbe.T.Module := fidVivK6NoBvaCommitBundle.patchedMod
abbrev fidVivK6NoBvaCommitEnv : Env := patchEnv fidVivK6NoBvaCommitBundle

/-- Full `473`-entry `SpecEntry` table aligned with `fidVivK6SplicedFns`. -/
def fidVivK6SpecTable : List SpecEntry :=
  patchRows fidVivK6ReplRows fidVivK6BeforeRowAssoc fidBaseSpecTable

/-- Full `473`-entry `SpecEntry` table aligned with `fidVivK6NoBvaCommitSplicedFns`. -/
def fidVivK6NoBvaCommitSpecTable : List SpecEntry :=
  patchRows fidVivK6NoBvaCommitReplRows fidVivK6BeforeRowAssoc fidBaseSpecTable

theorem fidVivK6Spliced_noExit : fidVivK6SplicedModule.exits = [] :=
  fidBase_noExit

theorem fidVivK6NoBvaCommitSpliced_noExit : fidVivK6NoBvaCommitSplicedModule.exits = [] :=
  fidBase_noExit

theorem fidVivK6Befores_wf_all :
    ∀ fn ∈ List.flatMap Prod.snd fidVivK6Befores, fn.Wf := by
  intro fn hfn
  simp only [fidVivK6Befores, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hfn
  exact fidVivK6Befores_wf fn hfn

private def takeRowsAt : Nat → List Nat → List SpecEntry → List (Option SpecEntry)
  | _, [], _ => []
  | _, i :: is, [] => (i :: is).map (fun _ => none)
  | cur, i :: is, x :: xs =>
    if cur == i then some x :: takeRowsAt (cur + 1) is xs
    else takeRowsAt (cur + 1) (i :: is) xs

private def fidBaseRowIdxs : List Nat :=
  [11, 12, 17, 18, 39, 59, 66, 67, 68, 70, 80, 86, 181, 182, 212, 213, 218,
   220, 221, 310, 390, 396, 405]

private def fidBaseRowExpected : List (Option SpecEntry) :=
  [ some ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , some ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  , some ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , some ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , some ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , some ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , some ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , some ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , some ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , some ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩
  , some ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  , some ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , some ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinM6Spec, true⟩
  , some ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  , some ⟨"full_viv_clause_m6", [i64, i32], [i64], fun xs m Q X =>
      (⟨"full_viv_clause_m6", [i64, i32], [i64], fullVivClauseM6Spec, true⟩ :
        SpecEntry).eff xs m Q X ∨
      ∃ has' hrs', (⟨"full_viv_clause_m6", [i64, i32], [i64], fullVivClauseM6Spec, true⟩ :
        SpecEntry).cast has' hrs' xs m Q X, true⟩
  , some ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool], fun xs m Q X =>
      (⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool], fullVivTierMatchM6Spec, true⟩ :
        SpecEntry).eff xs m Q X ∨
      ∃ has' hrs', (⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool],
        fullVivTierMatchM6Spec, true⟩ : SpecEntry).cast has' hrs' xs m Q X, true⟩
  , some ⟨"full_viv_clear_tier_m6", [i64, i64], [], fun xs m Q X =>
      (⟨"full_viv_clear_tier_m6", [i64, i64], [], fullVivClearTierM6Spec, true⟩ :
        SpecEntry).eff xs m Q X ∨
      ∃ has' hrs', (⟨"full_viv_clear_tier_m6", [i64, i64], [],
        fullVivClearTierM6Spec, true⟩ : SpecEntry).cast has' hrs' xs m Q X, true⟩
  , some ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
  , some ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩
  , some ⟨"full_k6_propagate", [i64], [i32], k6PropagateSpec, true⟩
  , some ⟨"full_k6_core_m8", [i64], [], m8K6CoreSpec, true⟩
  , some ⟨"full_init_fresh_var", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩
  , some ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec, true⟩ ]

private def fidBaseTableScan (tbl : List SpecEntry) :
    List (Option SpecEntry) × Nat × Bool :=
  (takeRowsAt 0 fidBaseRowIdxs tbl,
   (tbl.map (fun e => if e.name = "full_vivify_tier_m6_hdr" then 5 else 1)).sum,
   tbl.all (fun e =>
     e.name != "full_viv_collect_fid" && e.name != "full_viv_count_fid" &&
     e.name != "full_viv_sort2_fid" && e.name != "full_viv_sort_fid"))

private theorem fidBaseTableScan_ok :
    fidBaseTableScan fidBaseSpecTable = (fidBaseRowExpected, 473, true) := by
  t_kernel_rfl

private theorem fidBaseTableScan_elim {tbl : List SpecEntry} {r1 : List (Option SpecEntry)}
    {r2 : Nat} {r3 : Bool} (h : fidBaseTableScan tbl = (r1, r2, r3)) :
    takeRowsAt 0 fidBaseRowIdxs tbl = r1 ∧
    (tbl.map (fun e => if e.name = "full_vivify_tier_m6_hdr" then 5 else 1)).sum = r2 ∧
    tbl.all (fun e =>
      e.name != "full_viv_collect_fid" && e.name != "full_viv_count_fid" &&
      e.name != "full_viv_sort2_fid" && e.name != "full_viv_sort_fid") = r3 :=
  ⟨congrArg Prod.fst h, congrArg (Prod.fst ∘ Prod.snd) h, congrArg (Prod.snd ∘ Prod.snd) h⟩

private theorem fidBaseTableScan_rows :
    takeRowsAt 0 fidBaseRowIdxs fidBaseSpecTable = fidBaseRowExpected :=
  (fidBaseTableScan_elim fidBaseTableScan_ok).1

private theorem fidBaseTableScan_lenSum :
    (fidBaseSpecTable.map (fun e =>
      if e.name = "full_vivify_tier_m6_hdr" then 5 else 1)).sum = 473 :=
  (fidBaseTableScan_elim fidBaseTableScan_ok).2.1

private theorem fidBaseTableScan_noBef :
    fidBaseSpecTable.all (fun e =>
      e.name != "full_viv_collect_fid" && e.name != "full_viv_count_fid" &&
      e.name != "full_viv_sort2_fid" && e.name != "full_viv_sort_fid") = true :=
  (fidBaseTableScan_elim fidBaseTableScan_ok).2.2

private theorem takeRowsAt_eq (is : List Nat) (cur : Nat) (tbl : List SpecEntry)
    (hsort : is.Pairwise (· < ·)) (hle : ∀ i ∈ is, cur ≤ i) :
    takeRowsAt cur is tbl = is.map (fun i => tbl[i - cur]?) := by
  induction tbl generalizing is cur with
  | nil =>
    cases is with
    | nil => rfl
    | cons i is' => simp [takeRowsAt]
  | cons x xs ih =>
    cases is with
    | nil => rfl
    | cons i is' =>
      dsimp only [takeRowsAt]
      have hicur : cur ≤ i := hle i List.mem_cons_self
      have hpair := List.pairwise_cons.mp hsort
      by_cases heq : cur = i
      · subst heq
        simp only [beq_self_eq_true, ↓reduceIte, List.map_cons, Nat.sub_self,
          List.getElem?_cons_zero]
        have hle' : ∀ j ∈ is', cur + 1 ≤ j := fun j hj => Nat.succ_le_of_lt (hpair.1 j hj)
        rw [ih is' (cur + 1) hpair.2 hle']
        congr 1; apply List.map_congr_left
        intro j hj
        have hgt : cur < j := hpair.1 j hj
        rw [show j - cur = (j - (cur + 1)) + 1 by omega]; rfl
      · have hne : (cur == i) = false := beq_false_of_ne heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        have hle' : ∀ j ∈ i :: is', cur + 1 ≤ j := by
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj'
          · omega
          · exact Nat.le_trans (Nat.succ_le_of_lt (by omega)) (Nat.le_of_lt (hpair.1 j hj'))
        rw [ih (i :: is') (cur + 1) hsort hle', List.map_cons, List.map_cons]
        congr 1
        · rw [show i - cur = (i - (cur + 1)) + 1 by omega]; rfl
        · apply List.map_congr_left
          intro j hj
          have hgt : cur < j := Nat.lt_of_lt_of_le (by omega) (Nat.le_of_lt (hpair.1 j hj))
          rw [show j - cur = (j - (cur + 1)) + 1 by omega]; rfl

private theorem row_at_of_k {k idx : Nat}
    (hk : fidBaseRowIdxs[k]? = some idx) {e : SpecEntry}
    (he : fidBaseRowExpected[k]? = some (some e)) :
    fidBaseSpecTable[idx]? = some e := by
  have hmap : fidBaseRowIdxs.map (fun i => fidBaseSpecTable[i]?) = fidBaseRowExpected := by
    simpa [Nat.sub_zero] using
      (takeRowsAt_eq fidBaseRowIdxs 0 fidBaseSpecTable (by decide)
        fun _ _ => Nat.zero_le _).symm.trans fidBaseTableScan_rows
  have h1 := congrArg (·[k]?) hmap
  simp only [List.getElem?_map, hk, Option.map_some, he, Option.some.injEq] at h1
  exact h1

private theorem fid_repl_step_name (repls : List Fn) (f : Fn) :
    ((repls.find? (·.name == f.name)).getD f).name = f.name := by
  cases hrf : repls.find? (·.name == f.name) with
  | none => rfl
  | some r => exact beq_iff_eq.mp (List.find?_some (a := r) hrf)

private theorem patchFns_len_eq_of_sigs (repls : List Fn) (fs : List Fn) (tbl : List SpecEntry)
    (hsigs : tbl.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig) :
    (patchFns repls fidVivK6Befores fs).length =
      (tbl.map (fun e => if e.name = "full_vivify_tier_m6_hdr" then 5 else 1)).sum := by
  have hsplice : ∀ f : Fn,
      (patchInsAt fidVivK6Befores f ++ [(repls.find? (·.name == f.name)).getD f]).length =
      if f.name = "full_vivify_tier_m6_hdr" then 5 else 1 := by
    intro f
    rw [List.length_append, List.length_singleton]
    dsimp only [patchInsAt]
    rw [fidVivK6Befores, List.find?]
    by_cases heq : f.name = "full_vivify_tier_m6_hdr"
    · have hb : ("full_vivify_tier_m6_hdr" == f.name) = true := beq_iff_eq.mpr heq.symm
      rw [hb]; dsimp only; rw [ite_eq_left heq]; rfl
    · have hb : ("full_vivify_tier_m6_hdr" == f.name) = false :=
        beq_false_of_ne (fun h => heq h.symm)
      rw [hb]; dsimp only [List.find?]; rw [ite_eq_right heq]; rfl
  dsimp only [patchFns]
  rw [List.length_flatMap, List.map_congr_left (fun f _ => hsplice f)]
  induction tbl generalizing fs with
  | nil => cases fs with | nil => rfl | cons _ _ => simp at hsigs
  | cons e es ih =>
    cases fs with
    | nil => simp at hsigs
    | cons f fs' =>
      simp only [List.map_cons, List.cons.injEq] at hsigs
      have hnm : e.name = f.name := congrArg Prod.fst hsigs.1
      simp only [List.map_cons, List.sum_cons, hnm, ih fs' hsigs.2]

private theorem fid_patchFns_length_of (repls : List Fn) :
    (patchFns repls fidVivK6Befores fidBaseFns).length = 473 :=
  (patchFns_len_eq_of_sigs repls fidBaseFns fidBaseSpecTable fidBaseSpecTable_sigs).trans
    fidBaseTableScan_lenSum

theorem fidVivK6Spliced_length : fidVivK6SplicedModule.fns.length = 473 :=
  fid_patchFns_length_of fidVivK6Repls

theorem fidVivK6NoBvaCommitSpliced_length :
    fidVivK6NoBvaCommitSplicedModule.fns.length = 473 :=
  fid_patchFns_length_of fidVivK6NoBvaCommitRepls

private theorem nodup_insBefore {xs extra : List Sym} (anc : Sym)
    (hxs : xs.Nodup) (hex : extra.Nodup) (hdisj : ∀ e ∈ extra, e ∉ xs) :
    (xs.flatMap (fun nm => if nm = anc then extra ++ [nm] else [nm])).Nodup := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    simp only [List.nodup_cons] at hxs
    have ih' := ih hxs.2 (fun e he hm => hdisj e he (List.mem_cons_of_mem a hm))
    simp only [List.flatMap_cons]
    by_cases ha : a = anc
    · rw [ite_eq_left ha, List.append_assoc, List.singleton_append, List.nodup_append]
      refine ⟨hex, List.nodup_cons.mpr ⟨?_, ih'⟩, fun e he y hmem heqy => ?_⟩
      · intro hm
        rw [List.mem_flatMap] at hm
        obtain ⟨y, hy, hyin⟩ := hm
        by_cases hyanc : y = anc
        · simp only [ite_eq_left hyanc, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at hyin
          rcases hyin with hyex | rfl
          · exact hdisj a hyex List.mem_cons_self
          · exact hxs.1 hy
        · simp only [ite_eq_right hyanc, List.mem_cons, List.not_mem_nil, or_false] at hyin
          exact hxs.1 (hyin ▸ hy)
      · subst heqy
        rw [List.mem_cons] at hmem
        rcases hmem with rfl | hm
        · exact hdisj e he List.mem_cons_self
        · rw [List.mem_flatMap] at hm
          obtain ⟨y, hy, hyin⟩ := hm
          by_cases hyanc : y = anc
          · exact absurd (ha ▸ hyanc ▸ hy) hxs.1
          · simp only [ite_eq_right hyanc, List.mem_cons, List.not_mem_nil, or_false] at hyin
            exact hdisj e he (List.mem_cons_of_mem a (hyin ▸ hy))
    · rw [ite_eq_right ha, List.singleton_append]
      refine List.nodup_cons.mpr ⟨?_, ih'⟩
      rw [List.mem_flatMap]; rintro ⟨y, hy, hyin⟩
      by_cases hyanc : y = anc
      · simp only [ite_eq_left hyanc, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hyin
        rcases hyin with hyex | rfl
        · exact hdisj a hyex List.mem_cons_self
        · exact hxs.1 hy
      · simp only [ite_eq_right hyanc, List.mem_cons, List.not_mem_nil, or_false] at hyin
        exact hxs.1 (hyin ▸ hy)

private def fidVivK6BeforeNames : List Sym :=
  ["full_viv_collect_fid", "full_viv_count_fid", "full_viv_sort2_fid", "full_viv_sort_fid"]

private theorem fidVivK6BeforeNames_nodup : fidVivK6BeforeNames.Nodup := by decide

private theorem fidVivK6BeforeNames_not_base :
    ∀ nm ∈ fidVivK6BeforeNames, nm ∉ fidBaseFns.map Fn.name := by
  have hall := List.all_eq_true.mp fidBaseTableScan_noBef
  have hnm_eq : ∀ (tbl : List SpecEntry) (fs : List Fn),
      tbl.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig →
      fs.map Fn.name = tbl.map SpecEntry.name := by
    intro tbl fs hsigs
    induction tbl generalizing fs with
    | nil => cases fs with | nil => rfl | cons _ _ => simp at hsigs
    | cons e es ih =>
      cases fs with
      | nil => simp at hsigs
      | cons f fs' =>
        simp only [List.map_cons, List.cons.injEq] at hsigs
        exact List.cons_eq_cons.mpr ⟨(congrArg Prod.fst hsigs.1).symm, ih fs' hsigs.2⟩
  rw [hnm_eq fidBaseSpecTable fidBaseFns fidBaseSpecTable_sigs]
  intro nm hnm hm
  obtain ⟨e, he, hnm'⟩ := List.mem_map.mp hm
  have hok := hall e he
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
  simp only [fidVivK6BeforeNames, List.mem_cons, List.not_mem_nil, or_false] at hnm
  rcases hnm with rfl | rfl | rfl | rfl
  · exact hok.1.1.1 hnm'
  · exact hok.1.1.2 hnm'
  · exact hok.1.2 hnm'
  · exact hok.2 hnm'

private theorem fid_patchMod_namesNodup (repls : List Fn) :
    ({ fns := patchFns repls fidVivK6Befores fidBaseFns
     , externs := fidBaseModule.externs
     , exits := [] } : LeanQbe.T.Module).namesNodup := by
  unfold LeanQbe.T.Module.namesNodup LeanQbe.T.Module.names
  have hext : fidBaseModule.externs = [] := rfl
  rw [hext, List.map_nil, List.append_nil]
  have hgen : ∀ fs : List Fn, (patchFns repls fidVivK6Befores fs).map Fn.name =
      (fs.map Fn.name).flatMap (fun nm =>
        if nm = "full_vivify_tier_m6_hdr" then fidVivK6BeforeNames ++ [nm] else [nm]) := by
    intro fs
    induction fs with
    | nil => rfl
    | cons f fs' ih =>
      dsimp only [patchFns] at ih ⊢
      simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, fid_repl_step_name, ih]
      dsimp only [patchInsAt]
      rw [fidVivK6Befores, List.find?]
      by_cases heq : f.name = "full_vivify_tier_m6_hdr"
      · have hb : ("full_vivify_tier_m6_hdr" == f.name) = true := beq_iff_eq.mpr heq.symm
        rw [hb]; dsimp only; rw [ite_eq_left heq]; rfl
      · have hb : ("full_vivify_tier_m6_hdr" == f.name) = false :=
          beq_false_of_ne (fun h => heq h.symm)
        rw [hb]; dsimp only [List.find?]; rw [ite_eq_right heq]; rfl
  rw [hgen fidBaseFns]
  exact nodup_insBefore "full_vivify_tier_m6_hdr" fidBaseFns_names_nodup
    fidVivK6BeforeNames_nodup fidVivK6BeforeNames_not_base

/-! ## 2. `fidBaseSpecTable` Index Lookup Bridge & `ModuleOk` -/

private theorem nodup_fn_name_eq {xs : List Fn} (hnd : (xs.map Fn.name).Nodup)
    {x y : Fn} (hx : x ∈ xs) (hy : y ∈ xs) (hnm : x.name = y.name) : x = y := by
  induction xs with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd (hnm ▸ List.mem_map_of_mem hy) hnd.1
    · exact absurd (hnm.symm ▸ List.mem_map_of_mem hx) hnd.1
    · exact ih hnd.2 hx hy

private theorem fid_repl_sig_at {r : Fn} (idx : Nat) (hlt : idx < 469)
    (hsig : (fidBaseFns.get ⟨idx, fidBaseFns_length ▸ hlt⟩).sig = r.sig) :
    ∀ g ∈ fidBaseModule.fns, r.name = g.name → r.sig = g.sig := by
  intro g hg hnm
  change g ∈ fidBaseFns at hg
  have hm := List.get_mem fidBaseFns ⟨idx, fidBaseFns_length ▸ hlt⟩
  have heq := nodup_fn_name_eq fidBaseFns_names_nodup hm hg
    ((congrArg Prod.fst hsig).trans hnm)
  subst heq; exact hsig.symm

private theorem sig_at_tbl (idx : Nat) (hi : idx < 469) {e : SpecEntry}
    (ht : fidBaseSpecTable[idx]? = some e) :
    (fidBaseFns.get ⟨idx, fidBaseFns_length ▸ hi⟩).sig = (e.name, e.as, e.rs) := by
  have hrows := congrArg (·[idx]?) fidBaseSpecTable_sigs
  have h2 : fidBaseFns[idx]? =
      some (fidBaseFns.get ⟨idx, fidBaseFns_length ▸ hi⟩) :=
    List.getElem?_eq_getElem (fidBaseFns_length ▸ hi)
  simp only [List.getElem?_map, ht, h2, Option.map_some, Option.some.injEq] at hrows
  exact hrows.symm

private theorem sig_at_221 :
    (fidBaseFns.get ⟨221, fidBaseFns_length ▸ by decide⟩).sig =
      ("full_vivify_m6_hdr", [i64], [i64]) :=
  sig_at_tbl 221 (by decide) (row_at_of_k (k := 18) rfl rfl)

private theorem sig_at_310 :
    (fidBaseFns.get ⟨310, fidBaseFns_length ▸ by decide⟩).sig =
      ("full_k6_propagate", [i64], [i32]) :=
  sig_at_tbl 310 (by decide) (row_at_of_k (k := 19) rfl rfl)

private theorem sig_at_390 :
    (fidBaseFns.get ⟨390, fidBaseFns_length ▸ by decide⟩).sig =
      ("full_k6_core_m8", [i64], []) :=
  sig_at_tbl 390 (by decide) (row_at_of_k (k := 20) rfl rfl)

private theorem fid_replSigs_of (repls : List Fn) (hsub : ∀ r ∈ repls, r ∈ fidVivK6Repls) :
    ∀ r ∈ repls, ∀ g ∈ fidBaseModule.fns, r.name = g.name → r.sig = g.sig := by
  intro r hr g hg hnm
  have hr' := hsub r hr
  simp only [fidVivK6Repls, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fid_repl_sig_at (r := fidUnwatchLargeFn) 80 (by decide)
      ((sig_at_tbl 80 (by decide) (row_at_of_k (k := 10) rfl rfl)).trans rfl) g hg hnm
  · exact fid_repl_sig_at (r := fidVivifyTierHdrFn) 220 (by decide)
      ((sig_at_tbl 220 (by decide) (row_at_of_k (k := 17) rfl rfl)).trans rfl) g hg hnm
  · exact fid_repl_sig_at (r := fidVivifyHdrFn) 221 (by decide) (sig_at_221.trans rfl) g hg hnm
  · exact fid_repl_sig_at (r := fidK6PropagateFn) 310 (by decide) (sig_at_310.trans rfl) g hg hnm
  · exact fid_repl_sig_at (r := fidK6CoreM8Fn) 390 (by decide) (sig_at_390.trans rfl) g hg hnm
  · exact fid_repl_sig_at (r := fidBvaCommitFn) 405 (by decide)
      ((sig_at_tbl 405 (by decide) (row_at_of_k (k := 22) rfl rfl)).trans rfl) g hg hnm

private theorem env_ofTable_of_find? {tbl : List SpecEntry} {f : Sym} {e : SpecEntry}
    (hf : tbl.find? (·.name == f) = some e) {as bs : List Ty}
    (has : e.as = as) (hrs : e.rs = bs) {xs : Tup Val as} {m : Mem 64}
    {Q : Post bs} {X : XPost} (h : e.cast has hrs xs m Q X) :
    Env.ofTable tbl f as bs xs m Q X := by
  induction tbl with
  | nil => cases hf
  | cons a t ih =>
    rw [List.find?] at hf
    cases hbeq : a.name == f
    · rw [hbeq] at hf; dsimp only at hf
      have hne' : a.name ≠ f := fun h0 => by rw [beq_iff_eq.mpr h0] at hbeq; cases hbeq
      rw [Env.ofTable.eq_2]
      exact Or.inr ⟨fun ⟨h0, _, _⟩ => hne' h0, ih hf⟩
    · rw [hbeq] at hf; dsimp only at hf
      have hae : a = e := Option.some.inj hf
      have hnm : a.name = f := beq_iff_eq.mp hbeq
      subst hae
      rw [Env.ofTable.eq_2]
      exact Or.inl ⟨⟨hnm, has, hrs⟩, h⟩

private theorem patchEnv_front_row (b : PatchBundle) {f : Sym} {as bs : List Ty}
    {sp : Spec as bs} {e : SpecEntry}
    (hfind : b.frontTable.find? (·.name == f) = some e)
    (has : e.as = as) (hrs : e.rs = bs) (hsp : e.cast has hrs = sp)
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost)
    (h : sp xs m Q X) : patchEnv b f as bs xs m Q X := by
  dsimp only [patchEnv]
  exact env_ofTable_of_find? (by rw [List.find?_append, hfind]; rfl) has hrs (hsp ▸ h)

private theorem patchEnv_front_row_bot (b : PatchBundle) {f : Sym} {as bs : List Ty}
    {e : SpecEntry} (hfind : b.frontTable.find? (·.name == f) = some e)
    (has : e.as = as) (hrs : e.rs = bs) (hne : e.noExit = true)
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost)
    (h : (has ▸ hrs ▸ e.spec) xs m Q (fun _ _ _ _ => False)) :
    patchEnv b f as bs xs m Q X := by
  dsimp only [patchEnv]
  have h1 : (b.frontTable ++ b.baseTable).find? (·.name == f) = some e := by
    rw [List.find?_append, hfind]; rfl
  clear hfind
  cases e with
  | mk nm eas ers esp eno =>
    dsimp only at has hrs hne h; subst has hrs
    exact env_ofTable_of_find? h1 rfl rfl
      (by dsimp only [SpecEntry.cast, SpecEntry.eff]; rw [hne, ite_eq_left rfl]; exact h)

private theorem fid_row_at (withBva : Bool) {k idx : Nat}
    (hk : fidBaseRowIdxs[k]? = some idx) {e : SpecEntry}
    (he : fidBaseRowExpected[k]? = some (some e))
    (hnot : (mkFidVivK6Bundle withBva).frontTable.find? (·.name == e.name) = none) :
    ∀ xs m Q X, e.eff xs m Q X →
      patchEnv (mkFidVivK6Bundle withBva) e.name e.as e.rs xs m Q X := by
  intro xs m Q X hs
  rw [patchEnv_base_eq (mkFidVivK6Bundle withBva) hnot]
  change Env.ofTable fidBaseSpecTable e.name e.as e.rs xs m Q X
  exact FullM6ProofUtil.env_ofTable_row_at (row_at_of_k hk he) fidBaseSpecTable_nodup hs

private theorem bcpS15_to_propagate {a m Q X}
    (h : FullM6BcpS15.fullBcpS15Spec a m Q X) : fullPropagateSpec a m Q X := by
  rcases a with ⟨hptr, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, R, rfl, hlen, hwinv, hd0, hm, hQ⟩
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hwinv, hd0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' hte' hap' hfl' hr' hr0
      hr1 hr2 hdone hm' =>
      hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
        fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' s.scratch.delayed m'
        hlen' hw' hte' hap' (fun _ => rfl) hfl' hr' hr0 hr1 hr2 hdone hm'⟩

private theorem mem_fidVivK6Repls_of_noBva {r : Fn}
    (hr : r ∈ fidVivK6NoBvaCommitRepls) : r ∈ fidVivK6Repls := by
  simp only [fidVivK6NoBvaCommitRepls, fidVivK6Repls, List.mem_cons, List.not_mem_nil,
    or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem fid_front_impl_of (withBva : Bool) :
    ∀ (fn : Fn) (e : SpecEntry),
      fn ∈ (mkFidVivK6Bundle withBva).patchedMod.fns →
      (mkFidVivK6Bundle withBva).frontTable.find? (·.name == fn.name) = some e →
      SpecEntry.Impl (patchEnv (mkFidVivK6Bundle withBva)) fn e := by
  let b := mkFidVivK6Bundle withBva
  have h11 := fid_row_at withBva (k := 0) (idx := 11) rfl rfl (by cases withBva <;> rfl)
  have h12 := fid_row_at withBva (k := 1) (idx := 12) rfl rfl (by cases withBva <;> rfl)
  have h17 := fid_row_at withBva (k := 2) (idx := 17) rfl rfl (by cases withBva <;> rfl)
  have h18 := fid_row_at withBva (k := 3) (idx := 18) rfl rfl (by cases withBva <;> rfl)
  have h39 := fid_row_at withBva (k := 4) (idx := 39) rfl rfl (by cases withBva <;> rfl)
  have h59 : ∀ xs m Q X, FullM6Hdr.m6HdrW2aSpec [] [] xs m Q X →
      patchEnv b "m6_hdr_sync_legacy_tiers" [i64] [] xs m Q X := fun xs m Q X h =>
    fid_row_at withBva (k := 5) (idx := 59) rfl rfl (by cases withBva <;> rfl)
      xs m Q X (FullM6Hdr.m6HdrW2aSpec_monoX h)
  have h66 : ∀ xs m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [.bool] xs m Q X →
      patchEnv b "m6_hdr_delaying" [i64, i64] [.bool] xs m Q X := fun xs m Q X h =>
    fid_row_at withBva (k := 6) (idx := 66) rfl rfl (by cases withBva <;> rfl)
      xs m Q X (FullM6Hdr.m6HdrW2aSpec_monoX h)
  have h67 : ∀ xs m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] xs m Q X →
      patchEnv b "m6_hdr_bump_delay" [i64, i64] [] xs m Q X := fun xs m Q X h =>
    fid_row_at withBva (k := 7) (idx := 67) rfl rfl (by cases withBva <;> rfl)
      xs m Q X (FullM6Hdr.m6HdrW2aSpec_monoX h)
  have h68 : ∀ xs m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] xs m Q X →
      patchEnv b "m6_hdr_reduce_delay" [i64, i64] [] xs m Q X := fun xs m Q X h =>
    fid_row_at withBva (k := 8) (idx := 68) rfl rfl (by cases withBva <;> rfl)
      xs m Q X (FullM6Hdr.m6HdrW2aSpec_monoX h)
  have h70 : ∀ xs m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [i64] xs m Q X →
      patchEnv b "m6_hdr_get_watermark" [i64, i64] [i64] xs m Q X := fun xs m Q X h =>
    fid_row_at withBva (k := 9) (idx := 70) rfl rfl (by cases withBva <;> rfl)
      xs m Q X (FullM6Hdr.m6HdrW2aSpec_monoX h)
  have h86 : ∀ xs m Q X, FullM6BcpS15.fullBcpS15Spec xs m Q X →
      patchEnv b "full_propagate" [i64] [i64] xs m Q X := fun xs m Q X hs =>
    fid_row_at withBva (k := 11) (idx := 86) rfl rfl (by cases withBva <;> rfl)
      xs m Q X (bcpS15_to_propagate hs)
  have h181 : ∀ xs m Q X, fullAddBinSpec xs m Q X →
      patchEnv b "full_add_bin" [i64, i32, i32] [i64] xs m Q X := fun xs m Q X hs =>
    fid_row_at withBva (k := 12) (idx := 181) rfl rfl (by cases withBva <;> rfl)
      xs m Q X hs
  have h182 := fid_row_at withBva (k := 13) (idx := 182) rfl rfl (by cases withBva <;> rfl)
  have h212_raw := fid_row_at withBva (k := 14) (idx := 212) rfl rfl (by cases withBva <;> rfl)
  have h212 : ∀ xs m Q X, fullVivClauseM6Spec xs m Q X →
      patchEnv b "full_viv_clause_m6" [i64, i32] [i64] xs m Q X :=
    fun xs m Q X h => h212_raw xs m Q X (Or.inl h)
  have h213_raw := fid_row_at withBva (k := 15) (idx := 213) rfl rfl (by cases withBva <;> rfl)
  have h213 : ∀ xs m Q X, fullVivTierMatchM6Spec xs m Q X →
      patchEnv b "full_viv_tier_match_m6" [i64, i32, i64] [.bool] xs m Q X :=
    fun xs m Q X h => h213_raw xs m Q X (Or.inl h)
  have h218_raw := fid_row_at withBva (k := 16) (idx := 218) rfl rfl (by cases withBva <;> rfl)
  have h218 : ∀ xs m Q X, fullVivClearTierM6Spec xs m Q X →
      patchEnv b "full_viv_clear_tier_m6" [i64, i64] [] xs m Q X :=
    fun xs m Q X h => h218_raw xs m Q X (Or.inl h)
  have h396 := fid_row_at withBva (k := 21) (idx := 396) rfl rfl (by cases withBva <;> rfl)
  have hfUnw : ∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
      patchEnv b "full_unwatch_large" [i64, i32, i32] [] xs m Q X :=
    patchEnv_front_row b (hfind := by cases withBva <;> rfl) rfl rfl rfl
  have hfColl : ∀ xs m Q X, fullVivCollectFidSpec xs m Q X →
      patchEnv b "full_viv_collect_fid" [i64, i64] [i64] xs m Q X :=
    patchEnv_front_row b (hfind := by cases withBva <;> rfl) rfl rfl rfl
  have hfCnt : ∀ xs m Q X, fullVivCountFidSpec xs m Q X →
      patchEnv b "full_viv_count_fid" [i64, i64] [] xs m Q X :=
    patchEnv_front_row b (hfind := by cases withBva <;> rfl) rfl rfl rfl
  have hfS2 : ∀ xs m Q X, fullVivSort2FidSpec xs m Q X →
      patchEnv b "full_viv_sort2_fid" [i64, i64, i64] [] xs m Q X :=
    patchEnv_front_row b (hfind := by cases withBva <;> rfl) rfl rfl rfl
  have hfSort : ∀ xs m Q X, fullVivSortFidSpec xs m Q X →
      patchEnv b "full_viv_sort_fid" [i64, i64] [] xs m Q X :=
    patchEnv_front_row b (hfind := by cases withBva <;> rfl) rfl rfl rfl
  have hfTier : ∀ xs m Q X, m6aVivifyTierSpec xs m Q X →
      patchEnv b "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] xs m Q X :=
    patchEnv_front_row b (hfind := by cases withBva <;> rfl) rfl rfl rfl
  have hfront_repl_names : (b.replRows.map SpecEntry.name) = (b.repls.map Fn.name) := by
    cases withBva <;> rfl
  intro fn e hmem hfind
  have hfnCases : fn ∈ fidVivK6Repls ∨ fn ∈ List.flatMap Prod.snd fidVivK6Befores := by
    change fn ∈ patchFns b.repls b.befores b.baseMod.fns at hmem
    dsimp only [patchFns] at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨g, hg, hgin⟩ := hmem
    have hnotBase : ∀ (g0 : Fn), g0 ∈ b.baseMod.fns →
        b.repls.find? (·.name == g0.name) = none →
        b.frontTable.find? (·.name == g0.name) = none := by
      intro g0 hg0 hr0
      have hrnm : g0.name ∉ b.replRows.map SpecEntry.name := by
        rw [hfront_repl_names, List.mem_map]
        rintro ⟨r, hr, hreq⟩
        have hbad : (fun x : Fn => x.name == g0.name) r = true := beq_iff_eq.mpr hreq
        exact (List.find?_eq_none.mp hr0 r hr) hbad
      have hrr0 : b.replRows.find? (·.name == g0.name) = none := by
        apply List.find?_eq_none.mpr
        intro x hx hbeq
        exact hrnm (List.mem_map.mpr ⟨x, hx, beq_iff_eq.mp hbeq⟩)
      have hbef0 : b.beforeRows.find? (·.name == g0.name) = none := by
        apply List.find?_eq_none.mpr
        intro x hx hbeq
        have hbn : g0.name ∈ b.beforeRows.map SpecEntry.name :=
          List.mem_map.mpr ⟨x, hx, beq_iff_eq.mp hbeq⟩
        have hbeqBef : b.beforeRows.map SpecEntry.name = fidVivK6BeforeNames := rfl
        rw [hbeqBef] at hbn
        exact fidVivK6BeforeNames_not_base g0.name hbn (List.mem_map_of_mem hg0)
      dsimp only [PatchBundle.frontTable]
      have hrew0 : b.rewiredRows = [] := by cases withBva <;> rfl
      rw [hrew0, List.nil_append, List.find?_append, hrr0, Option.none_or, hbef0]
    rw [List.mem_append, List.mem_singleton] at hgin
    rcases hgin with hbef | hfnEq
    · right
      dsimp only [patchInsAt] at hbef
      cases hfp : b.befores.find? (fun x => x.fst == g.name) with
      | none => rw [hfp] at hbef; cases hbef
      | some p =>
        rw [hfp] at hbef
        exact List.mem_flatMap.mpr ⟨p, List.mem_of_find?_eq_some hfp, hbef⟩
    · cases hr : b.repls.find? (·.name == g.name) with
      | none =>
        have hn := hnotBase g hg hr
        simp only [hr, Option.getD_none] at hfnEq; subst hfnEq
        rw [hn] at hfind; cases hfind
      | some r =>
        left
        have hm := List.mem_of_find?_eq_some hr
        simp only [hr, Option.getD_some] at hfnEq; subst hfnEq
        cases withBva
        · exact mem_fidVivK6Repls_of_noBva hm
        · exact hm
  rcases hfnCases with hrepl | hbef
  · simp only [fidVivK6Repls, List.mem_cons, List.not_mem_nil, or_false] at hrepl
    rcases hrepl with rfl | rfl | rfl | rfl | rfl | rfl
    · have he : e = ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he; exact SpecEntry.Impl.of (full_unwatch_large_fid_wp (patchEnv b))
    · have he : e = ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64],
          m6aVivifyTierSpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he
      exact SpecEntry.Impl.of (full_vivify_tier_m6_hdr_fid_wp (patchEnv b)
        h39 hfColl hfCnt hfSort h212 h86 h218)
    · have he : e = ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he
      exact SpecEntry.Impl.of (full_vivify_m6_hdr_fid_wp (patchEnv b)
        h39 h59 h66 h70 hfTier h67 h68)
    · have he : e = ⟨"full_k6_propagate", [i64], [i32], k6PropagateSpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he; exact SpecEntry.Impl.of (full_k6_propagate_fid_wp (patchEnv b))
    · have he : e = ⟨"full_k6_core_m8", [i64], [], m8K6CoreSpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he; exact SpecEntry.Impl.of (full_k6_core_m8_fid_wp (patchEnv b))
    · cases withBva
      · have hnone : (mkFidVivK6Bundle false).frontTable.find?
            (·.name == fidBvaCommitFn.name) = none := rfl
        change (mkFidVivK6Bundle false).frontTable.find?
            (·.name == fidBvaCommitFn.name) = some e at hfind
        rw [hnone] at hfind; cases hfind
      · have he : e = ⟨"full_bva_commit", [i64, i32], [.bool], m4BvaCommitSpec, true⟩ :=
          Option.some.inj (hfind.symm.trans rfl)
        subst he
        exact SpecEntry.Impl.of (full_bva_commit_fid_wp (patchEnv b)
          h17 h396 h181 h12 h18 h182 hfUnw)
  · simp only [fidVivK6Befores, fidVivHelpers, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hbef
    rcases hbef with rfl | rfl | rfl | rfl
    · have he : e = ⟨"full_viv_collect_fid", [i64, i64], [i64],
          fullVivCollectFidSpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he; exact SpecEntry.Impl.of (full_viv_collect_fid_wp (patchEnv b) h11 h213)
    · have he : e = ⟨"full_viv_count_fid", [i64, i64], [], fullVivCountFidSpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he; exact SpecEntry.Impl.of (full_viv_count_fid_wp (patchEnv b))
    · have he : e = ⟨"full_viv_sort2_fid", [i64, i64, i64], [],
          fullVivSort2FidSpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he; exact SpecEntry.Impl.of (full_viv_sort2_fid_wp (patchEnv b))
    · have he : e = ⟨"full_viv_sort_fid", [i64, i64], [], fullVivSortFidSpec, true⟩ := by
        cases withBva <;> exact Option.some.inj (hfind.symm.trans rfl)
      subst he; exact SpecEntry.Impl.of (full_viv_sort_fid_wp (patchEnv b) hfS2)

private theorem fid_callsOk_full :
    checkPatchCallsOk fidBaseModule fidVivK6Repls fidVivK6Befores = true := by t_kernel_rfl

private theorem fid_callsOk_noBva :
    checkPatchCallsOk fidBaseModule fidVivK6NoBvaCommitRepls fidVivK6Befores = true := by
  t_kernel_rfl

private theorem fid_moduleOk_of (withBva : Bool) :
    ModuleOk (patchEnv (mkFidVivK6Bundle withBva)) (mkFidVivK6Bundle withBva).patchedMod := by
  refine patchBundle_moduleOk_sameSpecs (mkFidVivK6Bundle withBva) ?_ ?_ ?_ ?_ ?_
    (fid_front_impl_of withBva) ?_
  · exact fid_patchMod_namesNodup _
  · refine fid_replSigs_of _ ?_
    intro r hr; cases withBva
    · exact mem_fidVivK6Repls_of_noBva hr
    · exact hr
  · intro fn hfn
    rcases hfn with hrepl | hbef
    · cases withBva
      · exact fidVivK6Repls_wf fn (mem_fidVivK6Repls_of_noBva hrepl)
      · exact fidVivK6Repls_wf fn hrepl
    · exact fidVivK6Befores_wf_all fn hbef
  · cases withBva
    · exact fid_callsOk_noBva
    · exact fid_callsOk_full
  · intro fn hfn
    rcases hfn with hrepl | hbef
    · cases withBva
      · change fn ∈ [fidUnwatchLargeFn, fidVivifyTierHdrFn, fidVivifyHdrFn,
          fidK6PropagateFn, fidK6CoreM8Fn] at hrepl
        rcases List.mem_cons.mp hrepl with rfl | hrepl
        · rfl
        · rcases List.mem_cons.mp hrepl with rfl | hrepl
          · rfl
          · rcases List.mem_cons.mp hrepl with rfl | hrepl
            · rfl
            · rcases List.mem_cons.mp hrepl with rfl | hrepl
              · rfl
              · rcases List.mem_singleton.mp hrepl with rfl; rfl
      · change fn ∈ fidVivK6Repls at hrepl
        simp only [fidVivK6Repls, List.mem_cons, List.not_mem_nil, or_false] at hrepl
        rcases hrepl with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · change fn ∈ [fidVivCollectFn, fidVivCountFn, fidVivSort2Fn, fidVivSortFn] at hbef
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbef
      rcases hbef with rfl | rfl | rfl | rfl <;> cases withBva <;> rfl
  · intro s hs xs m P E hbase
    have heq : (mkFidVivK6Bundle withBva).baseTable = fidBaseSpecTable := rfl
    rw [heq] at hbase
    by_cases hf : (mkFidVivK6Bundle withBva).frontTable.find? (·.name == s.1) = none
    · rw [patchEnv_base_eq (mkFidVivK6Bundle withBva) hf, heq]; exact hbase
    · cases hfd : (mkFidVivK6Bundle withBva).frontTable.find? (·.name == s.1) with
      | none => exact absurd hfd hf
      | some e =>
        have hem := List.mem_of_find?_eq_some hfd
        have hnm : e.name = s.1 := beq_iff_eq.mp (List.find?_some (a := e) hfd)
        have hbaseExt : (mkFidVivK6Bundle withBva).baseMod.externs = [] := rfl
        have hbaseFns : (mkFidVivK6Bundle withBva).baseMod.fns = fidBaseFns := rfl
        have hbaseMem : s ∈ fidBaseFns.map Fn.sig := by
          have hs0 := hs
          rw [Module.sigs, hbaseExt, hbaseFns, List.map_nil, List.append_nil] at hs0
          exact hs0
        rcases List.mem_map.mp hbaseMem with ⟨g, hg, hgsig⟩
        have hs1 : s.1 ∈ (mkFidVivK6Bundle withBva).frontNames :=
          List.mem_map.mpr ⟨e, hem, hnm⟩
        have notBef : ∀ {bn : Sym}, bn ∈ fidVivK6BeforeNames → s.1 = bn → False := by
          intro bn hbn hsb
          have hgm : g.name ∈ fidBaseFns.map Fn.name := List.mem_map_of_mem hg
          have hgn : g.name = bn := (congrArg Prod.fst hgsig).trans hsb
          exact fidVivK6BeforeNames_not_base bn hbn (hgn ▸ hgm)
        have hs1_cases : s.1 = "full_unwatch_large" ∨ s.1 = "full_vivify_tier_m6_hdr" ∨
            s.1 = "full_vivify_m6_hdr" ∨ s.1 = "full_k6_propagate" ∨ s.1 = "full_k6_core_m8" ∨
            (withBva = true ∧ s.1 = "full_bva_commit") := by
          cases withBva
          · have hfn5 : (mkFidVivK6Bundle false).frontNames =
                ["full_unwatch_large", "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr",
                 "full_k6_propagate", "full_k6_core_m8"] ++ fidVivK6BeforeNames := rfl
            rw [hfn5, List.mem_append] at hs1
            rcases hs1 with h | h
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
            · exact False.elim (notBef h rfl)
          · have hfn6 : (mkFidVivK6Bundle true).frontNames =
                ["full_unwatch_large", "full_vivify_tier_m6_hdr", "full_vivify_m6_hdr",
                 "full_k6_propagate", "full_k6_core_m8", "full_bva_commit"] ++
                  fidVivK6BeforeNames := rfl
            rw [hfn6, List.mem_append] at hs1
            rcases hs1 with h | h
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))))
            · exact False.elim (notBef h rfl)
        rcases s with ⟨nm, as, bs⟩
        dsimp only at hs1_cases hgsig
        have agree_at : ∀ {idx : Nat} (hi : idx < 469) {ef : SpecEntry},
            fidBaseSpecTable[idx]? = some ef →
            (mkFidVivK6Bundle withBva).frontTable.find? (·.name == nm) = some ef →
            ef.name = nm →
            patchEnv (mkFidVivK6Bundle withBva) nm as bs xs m P E := by
          intro idx hi ef hrow hfind hnm_e
          have hsig0 := sig_at_tbl idx hi hrow
          have hm := List.get_mem fidBaseFns ⟨idx, fidBaseFns_length ▸ hi⟩
          have hnm' : g.name = (fidBaseFns.get ⟨idx, fidBaseFns_length ▸ hi⟩).name :=
            (congrArg Prod.fst hgsig).trans ((congrArg Prod.fst hsig0).trans hnm_e).symm
          have hgeq := nodup_fn_name_eq fidBaseFns_names_nodup hg hm hnm'
          have hsig_eq : (nm, as, bs) = (ef.name, ef.as, ef.rs) :=
            hgsig.symm.trans (hgeq ▸ hsig0)
          have has_e : ef.as = as := (congrArg (Prod.fst ∘ Prod.snd) hsig_eq).symm
          have hrs_e : ef.rs = bs := (congrArg (Prod.snd ∘ Prod.snd) hsig_eq).symm
          have helim := env_ofTable_elim fidBaseSpecTable_nodup hrow has_e hrs_e
            (hnm_e.symm ▸ hbase)
          exact patchEnv_front_row (mkFidVivK6Bundle withBva) hfind has_e hrs_e rfl xs m P E
            helim
        rcases hs1_cases with rfl | rfl | rfl | rfl | rfl | ⟨hbT, rfl⟩
        · exact agree_at (by decide)
            (row_at_of_k (k := 10) (idx := 80) rfl rfl) (by cases withBva <;> rfl) rfl
        · exact agree_at (by decide)
            (row_at_of_k (k := 17) (idx := 220) rfl rfl) (by cases withBva <;> rfl) rfl
        · exact agree_at (by decide)
            (row_at_of_k (k := 18) (idx := 221) rfl rfl) (by cases withBva <;> rfl) rfl
        · exact agree_at (by decide)
            (row_at_of_k (k := 19) (idx := 310) rfl rfl) (by cases withBva <;> rfl) rfl
        · exact agree_at (by decide)
            (row_at_of_k (k := 20) (idx := 390) rfl rfl) (by cases withBva <;> rfl) rfl
        · subst hbT
          exact agree_at (by decide)
            (row_at_of_k (k := 22) (idx := 405) rfl rfl) rfl rfl
where
  env_ofTable_elim {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
      {idx : Nat} {e : SpecEntry} (hget : tbl[idx]? = some e)
      {as bs : List Ty} (has : e.as = as) (hrs : e.rs = bs)
      {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
      (h : Env.ofTable tbl e.name as bs xs m Q X) :
      e.cast has hrs xs m Q X := by
    induction tbl generalizing idx with
    | nil => cases hget
    | cons a t ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [Env.ofTable.eq_2] at h
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero] at hget
        have ha := Option.some.inj hget; subst ha
        rcases h with ⟨_, hcast⟩ | ⟨hneg, _⟩
        · exact hcast
        · exact absurd ⟨rfl, has, hrs⟩ hneg
      | succ i =>
        simp only [List.getElem?_cons_succ] at hget
        rcases h with ⟨⟨heq, _, _⟩, _⟩ | ⟨_, htail⟩
        · exact absurd (heq ▸ List.mem_map_of_mem (List.mem_of_getElem? hget)) hnd.1
        · exact ih hnd.2 hget htail

/-! ## 3. Exported `ModuleOk`, Acyclicity, `TableImpl`, Soundness & End-to-End UNSAT NV -/

theorem fidVivK6Spliced_moduleOk : ModuleOk fidVivK6Env fidVivK6SplicedModule :=
  fid_moduleOk_of true

theorem fidVivK6NoBvaCommit_moduleOk :
    ModuleOk fidVivK6NoBvaCommitEnv fidVivK6NoBvaCommitSplicedModule :=
  fid_moduleOk_of false

private theorem checkAcyclic_of_modOk {Γ : Env} {M : LeanQbe.T.Module} (hM : ModuleOk Γ M) :
    M.checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true]
  refine ⟨listNodup_iff.mpr hM.nodup,
    checkFnsCallsOk_of_forall _ _ [] _ fun pre fn post hsp => ?_⟩
  simpa using (hM.fnsOk pre fn post hsp).2.1

theorem fidVivK6Spliced_acyclic : fidVivK6SplicedModule.checkAcyclic = true :=
  checkAcyclic_of_modOk fidVivK6Spliced_moduleOk

theorem fidVivK6NoBvaCommit_acyclic :
    fidVivK6NoBvaCommitSplicedModule.checkAcyclic = true :=
  checkAcyclic_of_modOk fidVivK6NoBvaCommit_moduleOk

theorem fidVivK6Spliced_wf : ∀ fn ∈ fidVivK6SplicedModule.fns, fn.Wf := by
  intro fn hfn
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
  exact (fidVivK6Spliced_moduleOk.fnsOk pre fn post hsp).1

theorem fidVivK6NoBvaCommit_wf : ∀ fn ∈ fidVivK6NoBvaCommitSplicedModule.fns, fn.Wf := by
  intro fn hfn
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
  exact (fidVivK6NoBvaCommit_moduleOk.fnsOk pre fn post hsp).1

private theorem list_find?_of_mem_nodup {xs : List SpecEntry} (hnd : (xs.map SpecEntry.name).Nodup)
    {e : SpecEntry} (he : e ∈ xs) : xs.find? (·.name == e.name) = some e := by
  induction xs with
  | nil => cases he
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?]
    rcases List.mem_cons.mp he with rfl | ht
    · simp
    · have hne : (a.name == e.name) = false :=
        beq_false_of_ne (fun h => hnd.1 (h ▸ List.mem_map_of_mem ht))
      rw [hne]; exact ih hnd.2 ht

private theorem fid_patchRows_tableImpl_of (withBva : Bool) :
    TableImpl (patchEnv (mkFidVivK6Bundle withBva))
      (mkFidVivK6Bundle withBva).patchedFns
      (patchRows (mkFidVivK6Bundle withBva).replRows fidVivK6BeforeRowAssoc fidBaseSpecTable) := by
  let b := mkFidVivK6Bundle withBva
  have hMod : ModuleOk (patchEnv b) b.patchedMod := fid_moduleOk_of withBva
  have hfnImpl : ∀ (fn : Fn) (e : SpecEntry), fn ∈ b.patchedFns →
      (e.name, e.as, e.rs) = fn.sig →
      (e ∈ b.frontTable ∨ (e ∈ fidBaseSpecTable ∧ b.frontTable.find? (·.name == fn.name) = none)) →
      SpecEntry.Impl (patchEnv b) fn e := by
    intro fn e hfn hsig hloc
    obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
    have hwp := (hMod.fnsOk pre fn post hsp).2.2
    have hnm : e.name = fn.name := congrArg Prod.fst hsig
    have has : e.as = fn.as := congrArg (Prod.fst ∘ Prod.snd) hsig
    have hrs : e.rs = fn.rs := congrArg (Prod.snd ∘ Prod.snd) hsig
    refine ⟨⟨hnm, has, hrs⟩, fun xs m Q X he => hwp xs m Q X ?_⟩
    rcases hloc with hef | ⟨heb, hnotf⟩
    · have hndFront : (b.frontTable.map SpecEntry.name).Nodup := by
        cases withBva <;> simp only [b, mkFidVivK6Bundle, PatchBundle.frontTable,
          fidVivK6NoBvaCommitReplRows, fidVivK6ReplRows, fidVivK6BeforeRows, List.take,
          List.nil_append, List.map_append, List.map_cons, List.map_nil] <;> decide
      have hfind : b.frontTable.find? (·.name == fn.name) = some e := by
        rw [← hnm]; exact list_find?_of_mem_nodup hndFront hef
      exact patchEnv_front_row b hfind has hrs rfl xs m Q X he
    · rw [patchEnv_base_eq b hnotf]
      have hbaseEq : b.baseTable = fidBaseSpecTable := rfl
      rw [hbaseEq]
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp heb
      have hget : fidBaseSpecTable[i]? = some e := by rw [List.getElem?_eq_getElem hi, heq]
      have hcast_row : ∀ {f' : Sym} {as' bs' : List Ty} (xs' : Tup Val as') (Q' : Post bs')
          (h1 : e.name = f') (h2 : e.as = as') (h3 : e.rs = bs'),
          e.cast h2 h3 xs' m Q' X → Env.ofTable fidBaseSpecTable f' as' bs' xs' m Q' X := by
        intro f' as' bs' xs' Q' h1 h2 h3 hx
        subst h1 h2 h3
        exact FullM6ProofUtil.env_ofTable_row_at hget fidBaseSpecTable_nodup hx
      exact hcast_row xs Q hnm has hrs he
  -- Walk `(fidBaseFns, fidBaseSpecTable)` simultaneously via `fidBaseSpecTable_sigs`
  have hloop : ∀ (seenF : List Fn) (fs : List Fn) (tbl : List SpecEntry),
      fidBaseFns = seenF ++ fs →
      tbl.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig →
      (∀ f ∈ fs, f ∈ fidBaseFns) →
      (∀ e ∈ tbl, e ∈ fidBaseSpecTable) →
      TableImpl (patchEnv b) (patchFns b.repls b.befores fs)
        (patchRows b.replRows fidVivK6BeforeRowAssoc tbl) := by
    intro seenF fs tbl _ hms hfsMem htblMem
    induction fs generalizing tbl seenF with
    | nil =>
      cases tbl with
      | nil => change TableImpl (patchEnv b) [] []; rw [TableImpl.eq_1]; trivial
      | cons _ _ => simp at hms
    | cons f fs' ih =>
      cases tbl with
      | nil => simp at hms
      | cons e es' =>
        simp only [List.map_cons, List.cons.injEq] at hms
        have ih' := ih (seenF ++ [f]) es' (by simp [*]) hms.2
          (fun x hx => hfsMem x (List.mem_cons_of_mem f hx))
          (fun x hx => htblMem x (List.mem_cons_of_mem e hx))
        have hfMem : f ∈ fidBaseFns := hfsMem f List.mem_cons_self
        have heMem : e ∈ fidBaseSpecTable := htblMem e List.mem_cons_self
        have henm : e.name = f.name := congrArg Prod.fst hms.1
        have hstep : ∀ (f' : Fn) (e' : SpecEntry),
            f' ∈ b.patchedFns →
            (e'.name, e'.as, e'.rs) = f'.sig →
            (e' ∈ b.frontTable ∨
              (e' ∈ fidBaseSpecTable ∧ b.frontTable.find? (·.name == f'.name) = none)) →
            TableImpl (patchEnv b) [f'] [e'] := by
          intro f' e' hm hs hl
          rw [TableImpl.eq_3]
          exact ⟨hfnImpl f' e' hm hs hl, by rw [TableImpl.eq_1]; trivial⟩
        dsimp only [patchFns, patchRows]
        rw [List.flatMap_cons, List.flatMap_cons]
        have hpair : ∃ (f0 : Fn) (e0 : SpecEntry),
            (b.repls.find? (·.name == f.name)).getD f = f0 ∧
            (b.replRows.find? (·.name == e.name)).getD e = e0 ∧
            f0 ∈ b.patchedFns ∧ (e0.name, e0.as, e0.rs) = f0.sig ∧
            f0.name = f.name ∧
            (e0 ∈ b.frontTable ∨
              (e0 ∈ fidBaseSpecTable ∧ b.frontTable.find? (·.name == f0.name) = none)) := by
          have hinPatch : ∀ (x : Fn),
              (b.repls.find? (·.name == f.name)).getD f = x → x ∈ b.patchedFns := by
            intro x hx
            change x ∈ patchFns b.repls b.befores fidBaseFns
            rw [patchFns, List.mem_flatMap]
            refine ⟨f, hfMem, List.mem_append_right _ (hx ▸ List.mem_singleton_self _)⟩
          have hs_find : ∀ nm : Sym,
              (b.repls.find? (·.name == nm) = none ↔ b.replRows.find? (·.name == nm) = none) := by
            intro nm
            have heqNm : b.repls.map Fn.name = b.replRows.map SpecEntry.name := by
              cases withBva <;> rfl
            rw [List.find?_eq_none, List.find?_eq_none]
            constructor
            · intro h x hx hbeq
              have heq := beq_iff_eq.mp hbeq
              have hxn : x.name ∈ b.repls.map Fn.name := heqNm ▸ List.mem_map_of_mem hx
              obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hxn
              exact h r hr (beq_iff_eq.mpr (hrn.trans heq))
            · intro h r hr hbeq
              have heq := beq_iff_eq.mp hbeq
              have hrn : r.name ∈ b.replRows.map SpecEntry.name := heqNm ▸ List.mem_map_of_mem hr
              obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hrn
              exact h x hx (beq_iff_eq.mpr (hxn.trans heq))
          cases hrf : b.repls.find? (·.name == f.name) with
          | none =>
            have hre : b.replRows.find? (·.name == e.name) = none := by
              rw [henm]; exact (hs_find f.name).mp hrf
            have hnotFront : b.frontTable.find? (·.name == f.name) = none := by
              have hbef : b.beforeRows.find? (·.name == f.name) = none := by
                apply List.find?_eq_none.mpr
                intro x hx hbx
                have hx' : x.name ∈ fidVivK6BeforeNames := by
                  have hm : x.name ∈ b.beforeRows.map SpecEntry.name :=
                    List.mem_map.mpr ⟨x, hx, rfl⟩
                  simpa [b, mkFidVivK6Bundle, fidVivK6BeforeRows, fidVivK6BeforeNames] using hm
                have hfeq : f.name = x.name := (beq_iff_eq.mp hbx).symm
                exact fidVivK6BeforeNames_not_base x.name hx' (hfeq ▸ List.mem_map_of_mem hfMem)
              dsimp only [PatchBundle.frontTable]
              have hrew : b.rewiredRows = [] := by cases withBva <;> rfl
              rw [hrew, List.nil_append, List.find?_append,
                show b.replRows.find? (·.name == f.name) = none from henm ▸ hre, Option.none_or]
              exact hbef
            exact ⟨f, e, rfl, by rw [hre]; rfl,
              hinPatch f (by simp only [hrf, Option.getD_none]), hms.1, rfl,
              Or.inr ⟨heMem, hnotFront⟩⟩
          | some r =>
            have hrb : ∃ er, b.replRows.find? (·.name == e.name) = some er ∧
                (er.name, er.as, er.rs) = r.sig ∧ er ∈ b.frontTable ∧ r.name = f.name := by
              have hnmr : r.name = f.name := beq_iff_eq.mp (List.find?_some (a := r) hrf)
              have hmemr := List.mem_of_find?_eq_some hrf
              cases withBva
              · change r ∈ fidVivK6NoBvaCommitRepls at hmemr
                simp only [fidVivK6NoBvaCommitRepls, List.mem_cons, List.not_mem_nil,
                  or_false] at hmemr
                rcases hmemr with rfl | rfl | rfl | rfl | rfl <;>
                  exact ⟨_, by rw [henm, ← hnmr]; rfl, rfl,
                    by simp [PatchBundle.frontTable, b, mkFidVivK6Bundle,
                      fidVivK6NoBvaCommitReplRows, fidVivK6ReplRows], hnmr⟩
              · change r ∈ fidVivK6Repls at hmemr
                simp only [fidVivK6Repls, List.mem_cons, List.not_mem_nil, or_false] at hmemr
                rcases hmemr with rfl | rfl | rfl | rfl | rfl | rfl <;>
                  exact ⟨_, by rw [henm, ← hnmr]; rfl, rfl,
                    by simp [PatchBundle.frontTable, b, mkFidVivK6Bundle, fidVivK6ReplRows], hnmr⟩
            obtain ⟨er, hfind_er, hsig_er, hem_er, hnm_r⟩ := hrb
            exact ⟨r, er, rfl, by rw [hfind_er]; rfl,
              hinPatch r (by simp only [hrf, Option.getD_some]), hsig_er, hnm_r, Or.inl hem_er⟩
        obtain ⟨f0, e0, hf0, he0, hf0mem, hsig0, hnm0, hloc0⟩ := hpair
        rw [hf0, he0]
        dsimp only [patchInsAt, patchRowInsAt, b, mkFidVivK6Bundle]
        rw [fidVivK6Befores, fidVivK6BeforeRowAssoc, List.find?_cons, List.find?_cons]
        by_cases hanc : f.name = "full_vivify_tier_m6_hdr"
        · have hbeq1 : ("full_vivify_tier_m6_hdr" == f.name) = true :=
            beq_iff_eq.mpr hanc.symm
          have hbeq2 : ("full_vivify_tier_m6_hdr" == e.name) = true :=
            beq_iff_eq.mpr (henm.trans hanc).symm
          simp only [hbeq1, hbeq2, fidVivHelpers, fidVivK6BeforeRows]
          have hmemIns : ∀ bf ∈ [fidVivCollectFn, fidVivCountFn, fidVivSort2Fn,
              fidVivSortFn], bf ∈ b.patchedFns := by
            intro bf hbf
            change bf ∈ patchFns b.repls b.befores fidBaseFns
            rw [patchFns, List.mem_flatMap]
            refine ⟨f, hfMem, List.mem_append_left _ ?_⟩
            dsimp only [patchInsAt, b, mkFidVivK6Bundle, fidVivK6Befores]
            simp only [List.find?, hbeq1, fidVivHelpers]; exact hbf
          have hinFront : ∀ br ∈ fidVivK6BeforeRows, br ∈ b.frontTable := fun br hbr =>
            List.mem_append_right _ hbr
          refine FullM6ProofUtil.tableImpl_append (by rfl) ?_ ih'
          simp only [List.cons_append, List.nil_append]
          refine ⟨hfnImpl _ _ (hmemIns _ (by simp)) rfl
              (Or.inl (hinFront _ (by simp [fidVivK6BeforeRows]))),
            hfnImpl _ _ (hmemIns _ (by simp)) rfl
              (Or.inl (hinFront _ (by simp [fidVivK6BeforeRows]))),
            hfnImpl _ _ (hmemIns _ (by simp)) rfl
              (Or.inl (hinFront _ (by simp [fidVivK6BeforeRows]))),
            hfnImpl _ _ (hmemIns _ (by simp)) rfl
              (Or.inl (hinFront _ (by simp [fidVivK6BeforeRows]))),
            hstep f0 e0 hf0mem hsig0 hloc0⟩
        · have hbne1 : ("full_vivify_tier_m6_hdr" == f.name) = false :=
            beq_false_of_ne (fun h => hanc h.symm)
          have hbne2 : ("full_vivify_tier_m6_hdr" == e.name) = false :=
            beq_false_of_ne (fun h => hanc (henm.symm.trans h.symm))
          rw [hbne1, hbne2]
          dsimp only [List.find?]
          rw [List.nil_append, List.nil_append]
          exact FullM6ProofUtil.tableImpl_append (by rfl) (hstep f0 e0 hf0mem hsig0 hloc0) ih'
  exact hloop [] fidBaseFns fidBaseSpecTable rfl fidBaseSpecTable_sigs
    (fun _ h => h) (fun _ h => h)

theorem fidVivK6Spliced_tableImpl :
    TableImpl fidVivK6Env fidVivK6SplicedFns fidVivK6SpecTable :=
  fid_patchRows_tableImpl_of true

theorem fidVivK6NoBvaCommit_tableImpl :
    TableImpl fidVivK6NoBvaCommitEnv fidVivK6NoBvaCommitSplicedFns fidVivK6NoBvaCommitSpecTable :=
  fid_patchRows_tableImpl_of false

private theorem fid_solveBytes_mem_of (repls : List Fn)
    (hnone : repls.find? (·.name == "kissat_solve_bytes") = none) :
    FullM6Orch.m6oSolveBytesFn ∈ patchFns repls fidVivK6Befores fidBaseFns := by
  rw [patchFns, List.mem_flatMap]
  refine ⟨FullM6Orch.m6oSolveBytesFn, fidBase_solveBytes_mem, ?_⟩
  have hm : FullM6Orch.m6oSolveBytesFn.name = "kissat_solve_bytes" := rfl
  exact List.mem_append_right _ (by simp [hm, hnone])

theorem fidVivK6Spliced_solveBytes_mem :
    FullM6Orch.m6oSolveBytesFn ∈ fidVivK6SplicedModule.fns :=
  fid_solveBytes_mem_of fidVivK6Repls (by rfl)

theorem fidVivK6NoBvaCommit_solveBytes_mem :
    FullM6Orch.m6oSolveBytesFn ∈ fidVivK6NoBvaCommitSplicedModule.fns :=
  fid_solveBytes_mem_of fidVivK6NoBvaCommitRepls (by rfl)

private theorem fid_solve_bytes_iff_of (withBva : Bool) {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    patchEnv (mkFidVivK6Bundle withBva) "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      m7FidSolveBytesSpec xs m Q (fun _ _ _ _ => False) := by
  have hnot : (mkFidVivK6Bundle withBva).frontTable.find? (·.name == "kissat_solve_bytes") =
      none := by cases withBva <;> rfl
  rw [patchEnv_base_eq (mkFidVivK6Bundle withBva) hnot]
  exact fidBaseEnv_solve_bytes_iff

theorem fidVivK6Spliced_solve_bytes_iff {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} :
    fidVivK6Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X ↔
      m7FidSolveBytesSpec xs m Q (fun _ _ _ _ => False) :=
  fid_solve_bytes_iff_of true

private theorem fid_solve_bytes_sound_of (withBva : Bool)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hc : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hw : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (patchEnv (mkFidVivK6Bundle withBva)) FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, Examples.LratBytes.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  have hmem : FullM6Orch.m6oSolveBytesFn ∈ (mkFidVivK6Bundle withBva).patchedMod.fns := by
    cases withBva
    · exact fidVivK6NoBvaCommit_solveBytes_mem
    · exact fidVivK6Spliced_solveBytes_mem
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  exact (fid_moduleOk_of withBva).fnsOk pre FullM6Orch.m6oSolveBytesFn post hsp |>.2.2 _ _ _ _
    ((fid_solve_bytes_iff_of withBva).mpr
      (m7FidSolveBytesSpec_intro hc hw hm fun r m' hr h20 _ hm' => ⟨hr, h20, hm'⟩))

theorem fidVivK6Spliced_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hc : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hw : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidVivK6Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, Examples.LratBytes.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of true hc hw hm

theorem fidVivK6Spliced_solve_bytes_host_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {m_dmem : Mem 64}
    (hc : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hw : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) m_dmem) :
    ∃ m0, (Eq m0 ⋆ F_host) m_dmem ∧
      Func.wp fidVivK6Env FullM6Orch.kissat_solve_bytes_body
        (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m0
        (fun (r, ()) m' =>
          ∀ st_dmem, (Eq m' ⋆ F_host) st_dmem →
            (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
            (r = 20#64 → ∃ cnf, Examples.LratBytes.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem)
        (fun _ _ _ _ => False) := by
  have hm' : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) m_dmem :=
    sep_ac hm
  obtain ⟨m0, m1, h1, h2, hh0, hf0⟩ := hm'
  refine ⟨m0, ⟨m0, m1, h1, h2, rfl, hf0⟩, ?_⟩
  exact wp_mono (fun ⟨r, ()⟩ m' hpost st_dmem hst => by
      dsimp only at hpost; exact fidBase_solve_bytes_host_sound hpost hst)
    (fun _ _ _ _ h => h) _ m0 (fidVivK6Spliced_solve_bytes_sound hc hw hh0)

theorem fidVivK6NoBvaCommit_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hc : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hw : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fidVivK6NoBvaCommitEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, Examples.LratBytes.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of false hc hw hm

theorem fidVivK6NoBvaCommit_solve_bytes_host_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {m_dmem : Mem 64}
    (hc : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hw : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) m_dmem) :
    ∃ m0, (Eq m0 ⋆ F_host) m_dmem ∧
      Func.wp fidVivK6NoBvaCommitEnv FullM6Orch.kissat_solve_bytes_body
        (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m0
        (fun (r, ()) m' =>
          ∀ st_dmem, (Eq m' ⋆ F_host) st_dmem →
            (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
            (r = 20#64 → ∃ cnf, Examples.LratBytes.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem)
        (fun _ _ _ _ => False) := by
  have hm' : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) m_dmem :=
    sep_ac hm
  obtain ⟨m0, m1, h1, h2, hh0, hf0⟩ := hm'
  refine ⟨m0, ⟨m0, m1, h1, h2, rfl, hf0⟩, ?_⟩
  exact wp_mono (fun ⟨r, ()⟩ m' hpost st_dmem hst => by
      dsimp only at hpost; exact fidBase_solve_bytes_host_sound hpost hst)
    (fun _ _ _ _ h => h) _ m0 (fidVivK6NoBvaCommit_solve_bytes_sound hc hw hh0)

private theorem fid_unsat_nv_of (withBva : Bool) :
    Func.wp (patchEnv (mkFidVivK6Bundle withBva)) FullM6Orch.kissat_solve_bytes_body
      (FullM6.nvM6CnfPtr, BitVec.ofNat 64 FullM6.nvM6UnsatBytes.length,
       FullM6.nvM6UnsatWorkPtr, BitVec.ofNat 64 FullM6.nvM6WorkLen, 16#64, ())
      FullM6.nvM6UnsatInitMem
      (fun (r, ()) m' =>
        r = 20#64 ∧ FullM6.nvM6UnsatCnf.Unsat ∧
        (bytes FullM6.nvM6CnfPtr FullM6.nvM6UnsatBytes ⋆
          region FullM6.nvM6UnsatWorkPtr FullM6.nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hmem : FullM6Orch.m6oSolveBytesFn ∈ (mkFidVivK6Bundle withBva).patchedMod.fns := by
    cases withBva
    · exact fidVivK6NoBvaCommit_solveBytes_mem
    · exact fidVivK6Spliced_solveBytes_mem
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  have hm0 : (bytes FullM6.nvM6CnfPtr FullM6.nvM6UnsatBytes ⋆
      region FullM6.nvM6UnsatWorkPtr FullM6.nvM6WorkLen ⋆ emp) FullM6.nvM6UnsatInitMem := by
    rw [sep_emp]; exact FullM6.nvM6UnsatInitMem_sep
  refine (fid_moduleOk_of withBva).fnsOk pre FullM6Orch.m6oSolveBytesFn post hsp |>.2.2 _ _ _ _
    ((fid_solve_bytes_iff_of withBva).mpr
      (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0
        fun r m' _ _ hdet hm' => ?_))
  have hr20 : r = 20#64 := hdet 1 2 9 (by decide) (by decide) (by decide) (by decide)
    (by decide) FullM6.nvM6Unsat_header FullM6.nvM6Unsat_unitTrace
  rw [sep_emp] at hm'
  exact ⟨hr20, FullM6.nvM6UnsatCnf_unsat, hm'⟩

theorem fidVivK6Spliced_unsat_nv :
    Func.wp fidVivK6Env FullM6Orch.kissat_solve_bytes_body
      (FullM6.nvM6CnfPtr, BitVec.ofNat 64 FullM6.nvM6UnsatBytes.length,
       FullM6.nvM6UnsatWorkPtr, BitVec.ofNat 64 FullM6.nvM6WorkLen, 16#64, ())
      FullM6.nvM6UnsatInitMem
      (fun (r, ()) m' =>
        r = 20#64 ∧ FullM6.nvM6UnsatCnf.Unsat ∧
        (bytes FullM6.nvM6CnfPtr FullM6.nvM6UnsatBytes ⋆
          region FullM6.nvM6UnsatWorkPtr FullM6.nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of true

theorem fidVivK6NoBvaCommit_unsat_nv :
    Func.wp fidVivK6NoBvaCommitEnv FullM6Orch.kissat_solve_bytes_body
      (FullM6.nvM6CnfPtr, BitVec.ofNat 64 FullM6.nvM6UnsatBytes.length,
       FullM6.nvM6UnsatWorkPtr, BitVec.ofNat 64 FullM6.nvM6WorkLen, 16#64, ())
      FullM6.nvM6UnsatInitMem
      (fun (r, ()) m' =>
        r = 20#64 ∧ FullM6.nvM6UnsatCnf.Unsat ∧
        (bytes FullM6.nvM6CnfPtr FullM6.nvM6UnsatBytes ⋆
          region FullM6.nvM6UnsatWorkPtr FullM6.nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of false

/-! ## 4. Concrete Non-Bailout `Mem 64` Non-Vacuity (`4` Targeted Components) -/

/-! ### 4a. `nv_fid_unwatch_large`: Backward Scan + Odd Peel + `u64`/`u32` Shift -/

def nvUwCfg : FullCfg :=
  { hdr := 8192#64, avail := 2344, mv := 4, max_vars := 4, bva_cap := 0
    nc := 2, arena_cap := 6, wcap := 16, delayed_cap := 0, red_cap := 0
    extend_cap := 0, scratch_cap := 0
    hbva := by decide, hmv := by decide, hmaxv := by decide, hnc := by decide
    harena := by decide, hwcap := by decide, hdel := by decide, hred := by decide
    hext := by decide, hscr := by decide, havail_fit := by decide, hsize := by decide }

def nvUwWvec : List (BitVec 32) := ((List.replicate 16 0#32).set 0 2#32).set 1 11#32

def nvUwWstk : List (BitVec 32) :=
  [0#32, 0#32, 0x80000003#32, 7#32, 42#32, 0x80000002#32, 5#32, 97#32,
   6#32, 98#32, 8#32, 99#32, 0x80000001#32, 0#32, 0#32, 0#32]

def nvUwCore : FullCoreState :=
  { nvM8MkCore nvUwWvec with wlen := 14, wusable := 0#64, wstk := nvUwWstk }

def nvUwState : FullState :=
  { core := nvUwCore
    scratch := nvM8MkScratch 0#64 0#64 (List.replicate 4 0#32) (List.replicate 4 0#64) }

private def nvUwBytes : List UInt8 :=
  let s := nvUwState; let c := nvUwCfg
  let blkHdr := bytes64 [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ++
    bytes64 (Full.hdrTailWords c s)
  let blkBytes :=
    (bytesOf (t := i8) s.core.vals ++ List.replicate 0 0) ++
    (bytesOf (t := i8) s.scratch.walk_vals ++ List.replicate 0 0) ++
    (bytesOf (t := i8) s.core.lit_mark ++ List.replicate 0 0) ++
    (bytesOf (t := i8) s.core.mrk ++ List.replicate 4 0) ++
    (bytesOf (t := i8) s.scratch.phases ++ List.replicate 4 0) ++
    (bytesOf (t := i8) s.scratch.phases_target ++ List.replicate 4 0) ++
    (bytesOf (t := i8) s.scratch.phases_best ++ List.replicate 4 0) ++
    (bytesOf (t := i8) s.scratch.walk_best ++ List.replicate 4 0)
  let blkU32A :=
    (bytesOf (t := i32) s.core.flags ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.core.lvl ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.core.rsns ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.core.trl ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.core.trail_pos ++ List.replicate 8 0)
  let blkU32B :=
    (bytesOf (t := i32) s.core.tmp ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.scratch.heap ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.scratch.pos ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.core.min_clr ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.scratch.shrink_stk ++ List.replicate 8 0)
  let blkU32C :=
    (bytesOf (t := i32) s.scratch.q_prev ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.scratch.q_next ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.scratch.q_stamp ++ List.replicate 8 0) ++
    (bytesOf (t := i32) s.core.frame_trail ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.frame_dec ++ List.replicate 4 0)
  let blkWvec :=
    bytesOf (t := i32) s.core.wvec ++ bytesOf (t := i32) s.core.repr ++
    bytesOf (t := i32) s.scratch.wsort ++ bytesOf (t := i32) s.scratch.work_stk1 ++
    bytesOf (t := i32) s.scratch.work_stk2 ++ bytesOf (t := i32) s.scratch.tarjan_mark ++
    bytesOf (t := i32) s.scratch.tarjan_reach ++ bytes64 s.scratch.score ++
    bytes64 s.scratch.sim_sig
  let blkTail :=
    bytesOf (t := i32) s.core.min_stk ++ bytesOf (t := i32) s.scratch.glue_used ++
    bytesOf (t := i32) s.scratch.last_learned ++ bytesOf (t := i32) s.core.arena ++
    bytesOf (t := i32) s.core.wstk ++ bytesOf (t := i32) s.scratch.delayed ++
    bytesOf (t := i32) s.scratch.red_refs ++ bytesOf (t := i32) s.scratch.extend_stk ++
    bytesOf (t := i32) s.scratch.scratch_buf ++ List.replicate 0 0
  blkHdr ++ blkBytes ++ blkU32A ++ blkU32B ++ blkU32C ++ blkWvec ++ blkTail

def nvUwMem : Mem 64 := nvUwBytes.At nvUwCfg.hdr

private theorem nvUwState_lengths : nvUwState.LengthsOk nvUwCfg := by
  dsimp only [nvUwState, nvUwCore, nvM8MkCore, nvM8MkScratch, nvUwWvec, nvUwWstk, nvUwCfg]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvUw_watchStack : WatchStackLayout nvUwState.core := by
  have hcv : nvUwState.core.cur_vars = 4 := rfl
  refine ⟨fun l hl => ?_, fun l hl hpos => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
    fun l hl idx hi => ?_⟩
  · have hl8 : l < 8 := by omega
    rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases (show l = 0 ∨ (1 ≤ l ∧ l < 8) by omega) with rfl | ⟨_, _⟩
    · decide
    · have h0 : fullWatchSizeCore nvUwState.core l = 0 := by
        dsimp only [fullWatchSizeCore, nvUwState, nvUwCore, nvM8MkCore, nvUwWvec]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_replicate]
        split <;> rfl
      omega
  · by_cases hl1 : l1 = 0
    · subst hl1
      have h0 : fullWatchSizeCore nvUwState.core l2 = 0 := by
        dsimp only [fullWatchSizeCore, nvUwState, nvUwCore, nvM8MkCore, nvUwWvec]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_replicate]
        split <;> rfl
      omega
    · have h0 : fullWatchSizeCore nvUwState.core l1 = 0 := by
        dsimp only [fullWatchSizeCore, nvUwState, nvUwCore, nvM8MkCore, nvUwWvec]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_replicate]
        split <;> rfl
      omega
  · by_cases hl0 : l = 0
    · subst hl0
      have hsz : fullWatchSizeCore nvUwState.core 0 = 11 := rfl
      rw [hsz] at hi
      rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨
        idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 by omega) with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> decide
    · have h0 : fullWatchSizeCore nvUwState.core l = 0 := by
        dsimp only [fullWatchSizeCore, nvUwState, nvUwCore, nvM8MkCore, nvUwWvec]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_replicate]
        split <;> rfl
      omega

private theorem nvUwMem_ok : FullMem nvUwCfg nvUwState nvUwMem := by
  let c := nvUwCfg; let s := nvUwState
  have hv0 : valsBytes c.max_vars - 2 * c.max_vars = 0 := by decide
  have hm4 : markBytes c.max_vars - c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by decide
  have h2m : BitVec.ofNat 64 (2 * c.max_vars) = 8#64 := rfl
  have hm4v : BitVec.ofNat 64 c.max_vars = 4#64 := rfl
  have h4m : BitVec.ofNat 64 (4 * c.max_vars) = 16#64 := rfl
  have h4p : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 20#64 := rfl
  have htw : (Full.hdrTailWords c s).length = 140 := Full.hdrTailWords_length c s
  have hHdr := Full.nv_join_pair
    (Full.nv_arr64_p (a := c.hdr) (xs := [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc,
      s.core.d_cur, s.core.d_val]) 32 rfl (by decide))
    (Full.nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120 (by rw [htw])
      (by decide))
    (by decide) (by decide)
  have hBytes := by
    have h1 := Full.nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 8 0 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 8 0
      rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark)
      8 0 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 4 4 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases)
      4 4 rfl (by decide)
    have h6 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesTarget)
      (xs := s.scratch.phases_target) 4 4 rfl (by decide)
    have h7 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 4 4
      rfl (by decide)
    have h8 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 4 4
      rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := Full.nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := Full.nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := Full.nv_join_pair j123456 h7 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullCfg.padBytes c)
      (Full.nv_join_pair j1234567 h8 (by decide) (by decide)) fun _ hm => by
      have pB : ∀ {A1 A2 A3 A4 A5 A6 A7 A8 P1 P2 P3 P4 P5 P6 P7 P8 : Mem 64 → Prop} {k},
          ((((((((A1 ⋆ P1) ⋆ (A2 ⋆ P2)) ⋆ (A3 ⋆ P3)) ⋆ (A4 ⋆ P4)) ⋆
            (A5 ⋆ P5)) ⋆ (A6 ⋆ P6)) ⋆ (A7 ⋆ P7)) ⋆ (A8 ⋆ P8)) k →
          ((A1 ⋆ A3 ⋆ A4) ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆
            (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8)) k := fun x => sep_ac x
      unfold FullCoreByteArrs FullScrByteArrs FullCfg.padBytes
      rw [hv0, h2m, hm4, hm4v]; exact pB hm
  have hU32A := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags)
      16 8 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 16 8 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns)
      16 8 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 16 8 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 16 8
      rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ FullCfg.padU32A c)
      (Full.nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu8, h4m]; exact sep_ac hm
  have hU32B := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 16 8 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap)
      16 8 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 16 8 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr)
      16 8 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 16 8
      rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
          array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
          array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ FullCfg.padU32B c)
      (Full.nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu8, h4m]; exact sep_ac hm
  have hU32C := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev)
      16 8 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next)
      16 8 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 16 8
      rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 20 4
      rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 20 4
      rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := (array (t := i32) c.pQPrev s.scratch.q_prev ⋆
          array (t := i32) c.pQNext s.scratch.q_next ⋆
          array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
          (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
          array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ FullCfg.padU32C c)
      (Full.nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu8, hu4, h4m, h4p]; exact sep_ac hm
  have hWvec := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 64 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 32 rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 32 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1)
      32 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2)
      32 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 32
      rfl (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 32
      rfl (by decide)
    have h8 := Full.nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 32 rfl (by decide)
    have h9 := Full.nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 32 rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := Full.nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := Full.nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := Full.nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := Full.nv_join_pair j1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
          FullScrWksArrs c s.scratch ⋆
          (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
      (Full.nv_join_pair j12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 40 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256
      rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64
      rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 24 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 64 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed)
      0 rfl (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs)
      0 rfl (by decide)
    have h8 := Full.nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0
      rfl (by decide)
    have h9 := Full.nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0
      rfl (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 (0 : UInt8)).At c.pSlack) := by
      have hsl : c.slack = 0 := by decide
      rw [hsl]; exact ⟨rfl, ⟨[], rfl, rfl⟩⟩
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := Full.nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := Full.nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := Full.nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := Full.nv_join_pair j1234567 h8 (by decide) (by decide)
    have j123456789 := Full.nv_join_pair j12345678 h9 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := array (t := i32) c.pMinStk s.core.min_stk ⋆
          (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
          array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
          FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
      (Full.nv_join_pair j123456789 h10 (by decide) (by decide))
      fun _ hm => by unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := Full.nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := Full.nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := Full.nv_sep_reorg (Full.nv_join_pair h02 hU32B (by decide) (by decide)) fun _ hm => by
    have p1 : ∀ {D H CB SB PB UA PA T Hp Ps Mc Sh PB2 : Mem 64 → Prop} {k},
        (((D ⋆ H) ⋆ (CB ⋆ SB ⋆ PB)) ⋆ (UA ⋆ PA) ⋆ ((T ⋆ Hp ⋆ Ps ⋆ Mc ⋆ Sh) ⋆ PB2)) k →
        ((D ⋆ H) ⋆ ((CB ⋆ (UA ⋆ T ⋆ Mc)) ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh)) ⋆ (PB ⋆ PA ⋆ PB2))) k :=
      fun x => sep_ac x
    exact p1 hm
  have h04 := Full.nv_sep_reorg (Full.nv_join_pair h03 hU32C (by decide) (by decide)) fun _ hm => by
    have p2 : ∀ {DH C1 S1 P1 Qp Qn Qs FTr FDec PC : Mem 64 → Prop} {k},
        ((DH ⋆ (C1 ⋆ S1 ⋆ P1)) ⋆ ((Qp ⋆ Qn ⋆ Qs) ⋆ (FTr ⋆ FDec) ⋆ PC)) k →
        (DH ⋆ ((C1 ⋆ FTr ⋆ FDec) ⋆ (S1 ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ (P1 ⋆ PC))) k := fun x => sep_ac x
    exact p2 hm
  have h05 := Full.nv_join_pair h04 hWvec (by decide) (by decide)
  have h06 := Full.nv_sep_reorg (Q := FullMem c s)
    (Full.nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    have p3 : ∀ {D H CoreB ScrB P2 Wv Re SW Sc Ss MS Gu Ll CD SD SL : Mem 64 → Prop} {k},
        (((D ⋆ H ⋆ (CoreB ⋆ ScrB ⋆ P2)) ⋆ ((Wv ⋆ Re) ⋆ SW ⋆ (Sc ⋆ Ss))) ⋆
          (MS ⋆ (Gu ⋆ Ll) ⋆ CD ⋆ SD ⋆ SL)) k →
        (D ⋆ H ⋆ (CoreB ⋆ Wv ⋆ Re ⋆ MS ⋆ CD) ⋆ (ScrB ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆
          (P2 ⋆ SL)) k := fun x => sep_ac x
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
        (D ⋆ H ⋆ Core ⋆ Scr ⋆ (PB ⋆ PA ⋆ PB2 ⋆ PC ⋆ SL)) k := fun x => sep_ac x
    have p7 : ∀ {D H Core SB Hp Ps Sh Qp Qn Qs SW Meta SD Pad : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ ((Hp ⋆ Ps ⋆ Sh) ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k →
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh ⋆ Qp ⋆ Qn ⋆ Qs) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k :=
      fun x => sep_ac x
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B
      FullScratchArrays FullScrU32A FullScrMetaArrs FullCfg.pad dimacsState
    exact p7 (p6 (p5 (p4 (p3 hm))))
  exact h06.2

theorem nv_fid_unwatch_large :
    Func.wp fidVivK6Env full_unwatch_large_fid_body (nvUwCfg.hdr, 0#32, 42#32, ()) nvUwMem
      (fun _ m' => ∃ s',
        FullState.LengthsOk nvUwCfg s' ∧ WatchStackLayout s'.core ∧
        s'.core.cur_vars = 4 ∧ FullMem nvUwCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvUwCfg nvUwState ⋆ emp) nvUwMem := by
    rw [sep_emp]; exact nvUwMem_ok
  exact full_unwatch_large_fid_wp fidVivK6Env (nvUwCfg.hdr, 0#32, 42#32, ()) nvUwMem
    _ (fun _ _ _ _ => False)
    ⟨nvUwCfg, nvUwState, emp, rfl, nvUwState_lengths, nvUw_watchStack, hm,
      fun _ _ _ _ hlen hw _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hlen, hw, rfl, hm'⟩⟩

/-! ### 4b. `nv_fid_vivify_delayed_irr`: Delayed `vivifyirr` (`w_delay[3] = 1`, `fuel = 100`) -/

def nvFidVivExt : List (BitVec 64) :=
  ((List.replicate 288 0#64).set 0 fullM6HdrMagic).set 23 1#64

private def nvFidVivCoreBytes : List UInt8 :=
  let c := nvM6Cfg; let s := nvM6SparseState
  let blkHdr := bytes64 [3#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords c s)
  let blkBytes :=
    (bytesOf (t := i8) s.core.vals ++ List.replicate 2 0) ++
    (bytesOf (t := i8) s.scratch.walk_vals ++ List.replicate 2 0) ++
    (bytesOf (t := i8) s.core.lit_mark ++ List.replicate 2 0) ++
    (bytesOf (t := i8) s.core.mrk ++ List.replicate 5 0) ++
    (bytesOf (t := i8) s.scratch.phases ++ List.replicate 5 0) ++
    (bytesOf (t := i8) s.scratch.phases_target ++ List.replicate 5 0) ++
    (bytesOf (t := i8) s.scratch.phases_best ++ List.replicate 5 0) ++
    (bytesOf (t := i8) s.scratch.walk_best ++ List.replicate 5 0)
  let blkU32A :=
    (bytesOf (t := i32) s.core.flags ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.lvl ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.rsns ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.trl ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.trail_pos ++ List.replicate 4 0)
  let blkU32B :=
    (bytesOf (t := i32) s.core.tmp ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.heap ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.pos ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.min_clr ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.shrink_stk ++ List.replicate 4 0)
  let blkU32C :=
    (bytesOf (t := i32) s.scratch.q_prev ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.q_next ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.q_stamp ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.frame_trail ++ List.replicate 0 0) ++
    (bytesOf (t := i32) s.core.frame_dec ++ List.replicate 0 0)
  let blkWvec :=
    bytesOf (t := i32) s.core.wvec ++ bytesOf (t := i32) s.core.repr ++
    bytesOf (t := i32) s.scratch.wsort ++ bytesOf (t := i32) s.scratch.work_stk1 ++
    bytesOf (t := i32) s.scratch.work_stk2 ++ bytesOf (t := i32) s.scratch.tarjan_mark ++
    bytesOf (t := i32) s.scratch.tarjan_reach ++ bytes64 s.scratch.score ++
    bytes64 s.scratch.sim_sig
  let blkTail :=
    bytesOf (t := i32) s.core.min_stk ++ bytesOf (t := i32) s.scratch.glue_used ++
    bytesOf (t := i32) s.scratch.last_learned ++ bytesOf (t := i32) s.core.arena ++
    bytesOf (t := i32) s.core.wstk ++ bytesOf (t := i32) s.scratch.delayed ++
    bytesOf (t := i32) s.scratch.red_refs ++ bytesOf (t := i32) s.scratch.extend_stk ++
    bytesOf (t := i32) s.scratch.scratch_buf ++ List.replicate 0 0
  blkHdr ++ blkBytes ++ blkU32A ++ blkU32B ++ blkU32C ++ blkWvec ++ blkTail

def nvFidVivMem : Mem 64 := (bytes64 nvFidVivExt ++ nvFidVivCoreBytes).At (nvM6Cfg.hdr - 2304)

private theorem nvFidVivExt_len : nvFidVivExt.length = 288 := by
  rw [nvFidVivExt, List.length_set, List.length_set, List.length_replicate]

private theorem nvFidVivExt_magic : nvFidVivExt[0]? = some fullM6HdrMagic := by
  rw [nvFidVivExt, List.getElem?_set_ne (by decide : 23 ≠ 0)]
  exact List.getElem?_set_self (by rw [List.length_replicate]; decide)

private theorem nvFidVivMem_ok :
    FullM6HdrMem nvM6Cfg nvFidVivExt nvM6SparseState nvFidVivMem := by
  let c := nvM6Cfg; let s := nvM6SparseState
  have hv2 : valsBytes c.max_vars - 2 * c.max_vars = 2 := by decide
  have hm5 : markBytes c.max_vars - c.max_vars = 5 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu0 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have h2m : BitVec.ofNat 64 (2 * c.max_vars) = 6#64 := rfl
  have hmv : BitVec.ofNat 64 c.max_vars = 3#64 := rfl
  have h4m : BitVec.ofNat 64 (4 * c.max_vars) = 12#64 := rfl
  have h4p : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 16#64 := rfl
  have htw : (Full.hdrTailWords c s).length = 140 := Full.hdrTailWords_length c s
  have hHdr := Full.nv_join_pair
    (Full.nv_arr64_p (a := c.hdr) (xs := [3#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
    (Full.nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120 (by rw [htw])
      (by decide))
    (by decide) (by decide)
  have hBytes := by
    have h1 := Full.nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 6 2 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 6 2
      rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark)
      6 2 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 3 5 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases)
      3 5 rfl (by decide)
    have h6 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesTarget)
      (xs := s.scratch.phases_target) 3 5 rfl (by decide)
    have h7 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 3 5
      rfl (by decide)
    have h8 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 3 5
      rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := Full.nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := Full.nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := Full.nv_join_pair j123456 h7 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullCfg.padBytes c)
      (Full.nv_join_pair j1234567 h8 (by decide) (by decide)) fun _ hm => by
      have pB : ∀ {A1 A2 A3 A4 A5 A6 A7 A8 P1 P2 P3 P4 P5 P6 P7 P8 : Mem 64 → Prop} {k},
          ((((((((A1 ⋆ P1) ⋆ (A2 ⋆ P2)) ⋆ (A3 ⋆ P3)) ⋆ (A4 ⋆ P4)) ⋆
            (A5 ⋆ P5)) ⋆ (A6 ⋆ P6)) ⋆ (A7 ⋆ P7)) ⋆ (A8 ⋆ P8)) k →
          ((A1 ⋆ A3 ⋆ A4) ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆
            (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8)) k := fun x => sep_ac x
      unfold FullCoreByteArrs FullScrByteArrs FullCfg.padBytes
      rw [hv2, h2m, hm5, hmv]; exact pB hm
  have hU32A := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags)
      12 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 12 4 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns)
      12 4 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 12 4 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 12 4
      rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ FullCfg.padU32A c)
      (Full.nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, h4m]; exact sep_ac hm
  have hU32B := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 12 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap)
      12 4 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 12 4 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr)
      12 4 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 12 4
      rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
          array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
          array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ FullCfg.padU32B c)
      (Full.nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, h4m]; exact sep_ac hm
  have hU32C := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev)
      12 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next)
      12 4 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 12 4
      rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 16 0
      rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 16 0
      rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := (array (t := i32) c.pQPrev s.scratch.q_prev ⋆
          array (t := i32) c.pQNext s.scratch.q_next ⋆
          array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
          (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
          array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ FullCfg.padU32C c)
      (Full.nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu0, h4m, h4p]; exact sep_ac hm
  have hWvec := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 48 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 24 rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 24 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1)
      24 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2)
      24 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 24
      rfl (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 24
      rfl (by decide)
    have h8 := Full.nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 24 rfl (by decide)
    have h9 := Full.nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 24 rfl (by decide)
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := Full.nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := Full.nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := Full.nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := Full.nv_join_pair j1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
          FullScrWksArrs c s.scratch ⋆
          (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
      (Full.nv_join_pair j12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 32 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256
      rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64
      rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 24 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed)
      0 rfl (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs)
      0 rfl (by decide)
    have h8 := Full.nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0
      rfl (by decide)
    have h9 := Full.nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 512
      rfl (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 (0 : UInt8)).At c.pSlack) := by
      have hsl : c.slack = 0 := by decide
      rw [hsl]; exact ⟨rfl, ⟨[], rfl, rfl⟩⟩
    have j12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := Full.nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := Full.nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := Full.nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := Full.nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := Full.nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := Full.nv_join_pair j1234567 h8 (by decide) (by decide)
    have j123456789 := Full.nv_join_pair j12345678 h9 (by decide) (by decide)
    exact Full.nv_sep_reorg
      (Q := array (t := i32) c.pMinStk s.core.min_stk ⋆
          (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
          array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
          FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
      (Full.nv_join_pair j123456789 h10 (by decide) (by decide))
      fun _ hm => by unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := Full.nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := Full.nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := Full.nv_sep_reorg (Full.nv_join_pair h02 hU32B (by decide) (by decide)) fun _ hm => by
    have p1 : ∀ {D H CB SB PB UA PA T Hp Ps Mc Sh PB2 : Mem 64 → Prop} {k},
        (((D ⋆ H) ⋆ (CB ⋆ SB ⋆ PB)) ⋆ (UA ⋆ PA) ⋆ ((T ⋆ Hp ⋆ Ps ⋆ Mc ⋆ Sh) ⋆ PB2)) k →
        ((D ⋆ H) ⋆ ((CB ⋆ (UA ⋆ T ⋆ Mc)) ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh)) ⋆ (PB ⋆ PA ⋆ PB2))) k :=
      fun x => sep_ac x
    exact p1 hm
  have h04 := Full.nv_sep_reorg (Full.nv_join_pair h03 hU32C (by decide) (by decide)) fun _ hm => by
    have p2 : ∀ {DH C1 S1 P1 Qp Qn Qs FTr FDec PC : Mem 64 → Prop} {k},
        ((DH ⋆ (C1 ⋆ S1 ⋆ P1)) ⋆ ((Qp ⋆ Qn ⋆ Qs) ⋆ (FTr ⋆ FDec) ⋆ PC)) k →
        (DH ⋆ ((C1 ⋆ FTr ⋆ FDec) ⋆ (S1 ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ (P1 ⋆ PC))) k := fun x => sep_ac x
    exact p2 hm
  have h05 := Full.nv_join_pair h04 hWvec (by decide) (by decide)
  have hCore := Full.nv_sep_reorg (Q := FullMem c s)
    (Full.nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    have p3 : ∀ {D H CoreB ScrB P2 Wv Re SW Sc Ss MS Gu Ll CD SD SL : Mem 64 → Prop} {k},
        (((D ⋆ H ⋆ (CoreB ⋆ ScrB ⋆ P2)) ⋆ ((Wv ⋆ Re) ⋆ SW ⋆ (Sc ⋆ Ss))) ⋆
          (MS ⋆ (Gu ⋆ Ll) ⋆ CD ⋆ SD ⋆ SL)) k →
        (D ⋆ H ⋆ (CoreB ⋆ Wv ⋆ Re ⋆ MS ⋆ CD) ⋆ (ScrB ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆
          (P2 ⋆ SL)) k := fun x => sep_ac x
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
        (D ⋆ H ⋆ Core ⋆ Scr ⋆ (PB ⋆ PA ⋆ PB2 ⋆ PC ⋆ SL)) k := fun x => sep_ac x
    have p7 : ∀ {D H Core SB Hp Ps Sh Qp Qn Qs SW Meta SD Pad : Mem 64 → Prop} {k},
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ ((Hp ⋆ Ps ⋆ Sh) ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k →
        (D ⋆ H ⋆ Core ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh ⋆ Qp ⋆ Qn ⋆ Qs) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k :=
      fun x => sep_ac x
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B
      FullScratchArrays FullScrU32A FullScrMetaArrs FullCfg.pad dimacsState
    exact p7 (p6 (p5 (p4 (p3 hm))))
  have hb64 : (bytes64 nvFidVivExt).length = 2304 := by rw [bytes64_length, nvFidVivExt_len]
  refine fullM6HdrMem_mk (Full.nv_sep_append ?_ ?_ (array64_bytes _ _
      (by rw [nvFidVivExt_len]; omega)) hCore.2)
  · rw [hb64]; decide
  · dsimp only [nvFidVivCoreBytes]; rw [hb64, hCore.1]; omega

private theorem fid_repl_mem_spliced {idx : Nat} (hi : idx < 469) (r : Fn)
    (hnm : (fidBaseFns.get ⟨idx, fidBaseFns_length ▸ hi⟩).sig.1 = r.name)
    (hfind : fidVivK6Repls.find? (·.name == r.name) = some r) :
    r ∈ fidVivK6SplicedModule.fns := by
  change r ∈ patchFns fidVivK6Repls fidVivK6Befores fidBaseFns
  rw [patchFns, List.mem_flatMap]
  refine ⟨fidBaseFns.get ⟨idx, fidBaseFns_length ▸ hi⟩, List.get_mem _ _,
    List.mem_append_right _ ?_⟩
  change (fidBaseFns.get ⟨idx, fidBaseFns_length ▸ hi⟩).name = r.name at hnm
  rw [hnm, hfind]; exact List.mem_singleton_self _

theorem nv_fid_vivify_delayed_irr :
    Func.wp fidVivK6Env full_vivify_m6_hdr_fid_body (nvM6Cfg.hdr, ()) nvFidVivMem
      (fun (r, ()) m' => ∃ ext' s',
        M6HdrExtOk ext' ∧ (r = 1#64 ∨ r = 20#64) ∧
        FullSparseInv nvM6Cfg nvM6F0 s' ∧ nvM6F0.Unsat ∧
        FullM6HdrMem nvM6Cfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullM6HdrMem nvM6Cfg nvFidVivExt nvM6SparseState ⋆ emp) nvFidVivMem := by
    rw [sep_emp]; exact nvFidVivMem_ok
  have hmem : fidVivifyHdrFn ∈ fidVivK6SplicedModule.fns :=
    fid_repl_mem_spliced (idx := 221) (by decide) fidVivifyHdrFn
      (congrArg Prod.fst sig_at_221) rfl
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  have hwp := (fidVivK6Spliced_moduleOk.fnsOk pre _ post hsp).2.2
  have hcfg : FullM6HdrCfgOk nvM6Cfg := M6HdrCfgOk_of_le (by decide)
  have hext : M6HdrExtOk nvFidVivExt := M6HdrExtOk.of_len nvFidVivExt_len
  refine hwp (nvM6Cfg.hdr, ()) nvFidVivMem _ (fun _ _ _ _ => False)
    (patchEnv_front_row fidVivK6Bundle (sp := m6aVivifySpec) (hfind := rfl)
      rfl rfl rfl _ _ _ _
      ⟨nvM6Cfg, nvM6F0, nvFidVivExt, nvM6SparseState, emp, rfl, hcfg, hext,
        nvM6Sparse_invW.toSparse, hm, fun r ext' s' m' ⟨hext', _⟩ hsp' _ _ hr _ hm' => by
          rw [sep_emp] at hm'; exact ⟨ext', s', hext', hr, hsp', nvM6F0_unsat, hm'⟩⟩)

/-! ### 4c. `nv_fid_k6_propagate`: 2-Variable Watched Unit Propagation (`prop = 0 < trl_end = 1`) -/

def nvK6PropP : (Nat → Bool) → Prop := fun β => β 0 = true ∧ β 1 = true

def nvK6PropState : K6State :=
  { nvM6K6State with
    nv := 2#32, nc := 1#32, lvl := 0#32, prop := 0#32, trl_end := 1#32
    unass := 1#32, incons := 0#32, alen := 2#32
    trl := (List.replicate 512 0#32).set 0 0#32
    vals := ((List.replicate 1024 0#32).set 0 1#32).set 1 2#32
    whead := ((List.replicate 1024 0xFFFFFFFF#32).set 1 0#32).set 2 1#32
    wblit := ((List.replicate 4096 0#32).set 0 0x80000002#32).set 1 0x80000001#32
    clOff := (List.replicate 2048 0#32).set 0 0#32
    clSz := (List.replicate 2048 0#32).set 0 2#32
    arena := ((List.replicate 2784 0#32).set 0 1#32).set 1 2#32 }

def nvK6PropMem : Mem 64 := (bytesOf (t := i32) nvK6PropState.toSlab).At 0x2000#64

private theorem kmax24576_val : k6MaxV 24576 = 512 := rfl

private theorem nvK6PropState_shapes : nvK6PropState.ShapesOk nvM6K6Layout := by
  have hmV : nvM6K6Layout.maxV = 512 := by unfold nvM6K6Layout k6LayoutOfCap; exact kmax24576_val
  have hmC : nvM6K6Layout.maxCl = 2048 := by unfold K6Layout.maxCl; rw [hmV]
  have hac : nvM6K6Layout.acap = 2784 := by
    unfold nvM6K6Layout k6LayoutOfCap; dsimp only; rw [kmax24576_val]
  refine ⟨List.length_replicate, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
    (dsimp only [nvK6PropState, nvM6K6State];
     simp only [List.length_set, List.length_replicate, hmV, hmC, hac] <;> decide)

private theorem arena_take2_nat :
    List.take 2 (List.drop 0 (List.map BitVec.toNat
      (((List.replicate 2784 0#32).set 0 1#32).set 1 2#32))) = [1, 2] := rfl

private theorem nvK6PropState_inv : K6Inv nvM6K6Layout nvK6PropP nvK6PropState := by
  have hmV : nvM6K6Layout.maxV = 512 := by unfold nvM6K6Layout k6LayoutOfCap; exact kmax24576_val
  have hmO : nvM6K6Layout.maxOrig = 1536 := by unfold K6Layout.maxOrig; rw [hmV]
  have hmC : nvM6K6Layout.maxCl = 2048 := by unfold K6Layout.maxCl; rw [hmV]
  have hac : nvM6K6Layout.acap = 2784 := by
    unfold nvM6K6Layout k6LayoutOfCap; dsimp only; rw [kmax24576_val]
  have hsh := nvK6PropState_shapes
  have hoff0 : k6ClauseOff nvK6PropState 0 = 0 := by
    dsimp only [k6ClauseOff, nvK6PropState]
    rw [List.getElem?_set_self (by rw [List.length_replicate]; decide)]; rfl
  have hsz0 : k6ClauseSize nvK6PropState 0 = 2 := by
    dsimp only [k6ClauseSize, nvK6PropState]
    rw [List.getElem?_set_self (by rw [List.length_replicate]; decide)]; rfl
  have hlits0 : k6ClauseLits nvK6PropState 0 = [1, 2] := by
    unfold k6ClauseLits; rw [hoff0, hsz0]; exact arena_take2_nat
  have hcl : K6ClausesOk nvM6K6Layout nvK6PropP nvK6PropState :=
    { acap_eq := by rw [hac]; rfl
      max_v_eq := by rw [hmV]; rfl
      max_orig_eq := by rw [hmO]; rfl
      max_cl_eq := by rw [hmC]; rfl
      nv_le := by rw [hmV]; decide
      nc_le := by rw [hmC]; decide
      alen_le := by rw [hac]; decide
      nassump_le := by rw [hmV]; decide
      nkl_le := by rw [hmV]; decide
      nana_le := by rw [hmV]; decide
      cl_wf := fun cid hcid => by
        have hnc : nvK6PropState.nc.toNat = 1 := rfl
        have hc0 : cid = 0 := by omega
        subst hc0
        refine ⟨by rw [hsz0]; decide, by rw [hoff0, hsz0]; decide, ?_, ?_⟩
        · intro l hl; rw [hlits0] at hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> decide
        · intro β ⟨_, hb1⟩
          rw [hlits0, CNF.Clause.sat_iff_exists_mem_eq]
          exact ⟨(1, true), mem_cnfClause_iff.mpr (by decide), by simp [hb1]⟩
      cl_mono := fun c1 c2 hc1 hc2 => by
        have hnc : nvK6PropState.nc.toNat = 1 := rfl; omega
      incons_ok := fun h => by cases h rfl
      assump_ok := fun i hi => by
        have hna : nvK6PropState.nassump.toNat = 0 := rfl; omega
      flags_clean := fun v hv => by
        have hnv : nvK6PropState.nv.toNat = 2 := rfl
        have hf : nvK6PropState.flags[v]?.getD 0#32 = 0#32 := by
          dsimp only [nvK6PropState, nvM6K6State]
          rw [List.getElem?_replicate, ite_eq_left (by omega), Option.getD_some]
        rw [hf]; decide }
  have k5w_repl_nil : ∀ {n w : Nat}, w < n →
      K5WChain (List.replicate n (4294967295#32 : BitVec 32)) (BitVec.ofNat 32 w) [w] := by
    intro n w hi
    refine K5WChain.cons (by rw [List.length_replicate]; exact hi) (by
      have h : (List.replicate n (4294967295#32 : BitVec 32))[w]'(by
          rw [List.length_replicate]; exact hi) = 4294967295#32 := by
        have hg : (List.replicate n (4294967295#32 : BitVec 32))[w]? = some 4294967295#32 := by
          rw [List.getElem?_replicate, ite_eq_left hi]
        have he := List.getElem?_eq_getElem (by rw [List.length_replicate]; exact hi :
          w < (List.replicate n (4294967295#32 : BitVec 32)).length)
        rw [he] at hg; exact Option.some.inj hg
      rw [h]; exact K5WChain.nil)
  have hwat : K6WatchesOk nvK6PropState := by
    refine ⟨[[], [0], [1], []], by decide, by decide, fun l hl => ?_, fun l hl w hw => ?_⟩
    · have hnv2 : 2 * nvK6PropState.nv.toNat = 4 := rfl
      rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl | rfl
      · have hwh0 : nvK6PropState.whead[0]?.getD 4294967295#32 = 4294967295#32 := rfl
        rw [hwh0]; exact K5WChain.nil
      · have hwh1 : nvK6PropState.whead[1]?.getD 4294967295#32 = 0#32 := rfl
        rw [hwh1]; dsimp only [nvK6PropState, nvM6K6State]; exact k5w_repl_nil (by decide)
      · have hwh2 : nvK6PropState.whead[2]?.getD 4294967295#32 = 1#32 := rfl
        rw [hwh2]; dsimp only [nvK6PropState, nvM6K6State]; exact k5w_repl_nil (by decide)
      · have hwh3 : nvK6PropState.whead[3]?.getD 4294967295#32 = 4294967295#32 := rfl
        rw [hwh3]; exact K5WChain.nil
    · have hnv2 : 2 * nvK6PropState.nv.toNat = 4 := rfl
      rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl | rfl
      · simp at hw
      · have hw0 : w = 0 := by simpa using hw
        subst hw0
        have ha0 : (nvK6PropState.arena[k6ClauseOff nvK6PropState 0 + 0]?.getD 0#32).toNat = 1 :=
          by rw [hoff0]; rfl
        have hwb0 : nvK6PropState.wblit[0]?.getD 0#32 = 0x80000002#32 := rfl
        have hb0 : 2 ∈ k6ClauseLits nvK6PropState 0 := by rw [hlits0]; simp
        exact ⟨by decide, by rw [hsz0]; decide, ha0, by rw [hwb0]; decide,
          by rw [hwb0]; exact hb0, by rw [hwb0, hsz0]; decide,
          fun _ => by rw [hwb0, hoff0]; rfl⟩
      · have hw1 : w = 1 := by simpa using hw
        subst hw1
        have ha1 : (nvK6PropState.arena[k6ClauseOff nvK6PropState 0 + 1]?.getD 0#32).toNat = 2 :=
          by rw [hoff0]; rfl
        have hwb1 : nvK6PropState.wblit[1]?.getD 0#32 = 0x80000001#32 := rfl
        have hb1 : 1 ∈ k6ClauseLits nvK6PropState 0 := by rw [hlits0]; simp
        exact ⟨by decide, by rw [hsz0]; decide, ha1, by rw [hwb1]; decide,
          by rw [hwb1]; exact hb1, by rw [hwb1, hsz0]; decide,
          fun _ => by rw [hwb1, hoff0]; rfl⟩
      · simp at hw
  have hasg : K6BaseAssignOk nvK6PropP nvK6PropState :=
    { trl_end_le := by decide
      prop_le := by decide
      unass_eq := by decide
      vals_dom := fun l hl => by
        have hnv2 : 2 * nvK6PropState.nv.toNat = 4 := rfl
        rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl | rfl <;>
          (dsimp only [nvK6PropState, nvM6K6State]; simp [-List.reduceReplicate])
      vals_neg_iff := fun l hl => by
        have hnv2 : 2 * nvK6PropState.nv.toNat = 4 := rfl
        rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl | rfl <;>
          (dsimp only [nvK6PropState, nvM6K6State]; simp [-List.reduceReplicate])
      vals_nz_iff_trl := fun l hl => by
        have hnv2 : 2 * nvK6PropState.nv.toNat = 4 := rfl
        have hte : nvK6PropState.trl_end.toNat = 1 := rfl
        rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl | rfl
        · exact ⟨fun _ => ⟨0, by omega, by rfl⟩, fun _ => by decide⟩
        · exact ⟨fun _ => ⟨0, by omega, by rfl⟩, fun _ => by decide⟩
        · exact ⟨(fun h => by dsimp only [nvK6PropState, nvM6K6State] at h
                              simp [-List.reduceReplicate] at h),
            fun ⟨i, hi, heq⟩ => by
              rw [hte] at hi; have hi0 : i = 0 := by omega
              subst hi0; have ht0 : nvK6PropState.trl[0]?.getD 0#32 = 0#32 := rfl
              rw [ht0] at heq; cases heq⟩
        · exact ⟨(fun h => by dsimp only [nvK6PropState, nvM6K6State] at h
                              simp [-List.reduceReplicate] at h),
            fun ⟨i, hi, heq⟩ => by
              rw [hte] at hi; have hi0 : i = 0 := by omega
              subst hi0; have ht0 : nvK6PropState.trl[0]?.getD 0#32 = 0#32 := rfl
              rw [ht0] at heq; cases heq⟩
      trl_nodup := by
        dsimp only [k6TrailLits, nvK6PropState, nvM6K6State]
        simp [-List.reduceReplicate]
      trl_lt := fun l hl => by
        dsimp only [k6TrailLits, nvK6PropState, nvM6K6State] at hl
        simp [-List.reduceReplicate] at hl
        subst hl; decide
      trl_lvl_le := fun v hv => by
        have hnv : nvK6PropState.nv.toNat = 2 := rfl
        have hll : nvK6PropState.lvlArr[v]?.getD 0#32 = 0#32 := by
          dsimp only [nvK6PropState, nvM6K6State]
          rw [List.getElem?_replicate, ite_eq_left (by omega), Option.getD_some]
        rw [hll]; decide
      unass_lvl_zero := fun v hv h0 => by
        have hnv : nvK6PropState.nv.toNat = 2 := rfl
        have hll : nvK6PropState.lvlArr[v]?.getD 0#32 = 0#32 := by
          dsimp only [nvK6PropState, nvM6K6State]
          rw [List.getElem?_replicate, ite_eq_left (by omega), Option.getD_some]
        have hrs : nvK6PropState.rsn[v]?.getD 0#32 = 4294967295#32 := by
          dsimp only [nvK6PropState, nvM6K6State]
          rw [List.getElem?_replicate, ite_eq_left (by omega), Option.getD_some]
        exact ⟨hll, hrs⟩
      trl_lvl_mono := fun i j hij hj => by
        have hte : nvK6PropState.trl_end.toNat = 1 := rfl
        have hj0 : j = 0 := by omega
        have hi0 : i = 0 := by omega
        subst hi0 hj0; exact Nat.le_refl _
      dec_earliest := fun i j hj hi hpos => by
        have hte : nvK6PropState.trl_end.toNat = 1 := rfl
        omega
      lvl0_ok := fun i hi hl0 => by
        have hte : nvK6PropState.trl_end.toNat = 1 := rfl
        have hi0 : i = 0 := by omega
        subst hi0
        refine ⟨rfl, rfl, fun β ⟨hb0, _⟩ => ?_⟩
        rw [CNF.Clause.sat_iff_exists_mem_eq]
        exact ⟨(0, true), mem_cnfClause_iff.mpr (by decide), by simp [hb0]⟩ }
  exact ⟨hsh, hcl, hwat, hasg, fun i hi => by
    have hte : nvK6PropState.trl_end.toNat = 1 := rfl
    have hi0 : i = 0 := by omega
    subst hi0
    have hrs0 : nvK6PropState.rsn[(nvK6PropState.trl[0]?.getD 0#32).toNat / 2]?.getD
        4294967295#32 = 4294967295#32 := by
      have : nvK6PropState.trl[0]?.getD 0#32 = 0#32 := rfl
      rw [this]; dsimp only [nvK6PropState, nvM6K6State]
      rw [List.getElem?_replicate, ite_eq_left (by decide), Option.getD_some]
    exact Or.inl hrs0⟩

private theorem nvK6PropState_synced : K6TrailSynced nvK6PropState := fun i hi => by
  have hte : nvK6PropState.trl_end.toNat = 1 := rfl
  have hi0 : i = 0 := by omega
  subst hi0; exact ⟨rfl, rfl⟩

private theorem nat_xor1_eq (k : Nat) :
    k ^^^ 1 = if k % 2 = 0 then k + 1 else k - 1 := by
  apply Nat.eq_of_testBit_eq
  intro b
  cases b with
  | zero =>
    rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one k with hm | hm
    · have h1 : (k + 1) % 2 = 1 := by omega
      simp [hm, h1]
    · have h1 : (k - 1) % 2 = 0 := by omega
      simp [hm, h1]
  | succ b =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
    simp only [show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit, Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one k with hm | hm
    · have h1 : (k + 1) / 2 = k / 2 := by omega
      simp [hm, Nat.testBit_succ, h1]
    · have h1 : (k - 1) / 2 = k / 2 := by omega
      simp [hm, Nat.testBit_succ, h1]

theorem nv_fid_k6_propagate :
    Func.wp fidVivK6Env full_k6_propagate_fid_body (0x2000#64, ()) nvK6PropMem
      (fun (confl, ()) m' => ∃ ks',
        confl = 4294967295#32 ∧
        K6Inv nvM6K6Layout nvK6PropP ks' ∧ K6TrailSynced ks' ∧
        ks'.prop = ks'.trl_end ∧ 1 ≤ ks'.trl_end.toNat ∧
        K6Mem nvM6K6Layout 0x2000#64 ks' m')
      (fun _ _ _ _ => False) := by
  have hm : (K6Mem nvM6K6Layout 0x2000#64 nvK6PropState ⋆ emp) nvK6PropMem := by
    rw [sep_emp, k6Mem_eq_array 0x2000#64 nvK6PropState_shapes]
    refine array_bytes (t := i32) 0x2000#64 nvK6PropState.toSlab ?_
    have hl := K6State.toSlab_length nvK6PropState_shapes
    have hkl : nvM6K6Layout.k6Fixed + nvM6K6Layout.acap = 22272 := by
      unfold K6Layout.k6Fixed; rw [nvM6K6Layout_maxV, nvM6K6Layout_acap]
    rw [hl, hkl]; decide
  have hmem : fidK6PropagateFn ∈ fidVivK6SplicedModule.fns :=
    fid_repl_mem_spliced (idx := 310) (by decide) fidK6PropagateFn
      (congrArg Prod.fst sig_at_310) rfl
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  have hwp := (fidVivK6Spliced_moduleOk.fnsOk pre _ post hsp).2.2
  refine hwp (0x2000#64, ()) nvK6PropMem _ (fun _ _ _ _ => False)
    (patchEnv_front_row fidVivK6Bundle (sp := k6PropagateSpec) (hfind := rfl)
      rfl rfl rfl _ _ _ _
      ⟨nvM6K6Layout, nvK6PropP, nvK6PropState, emp, nvK6PropState_inv, nvK6PropState_synced, hm,
        fun confl ks' m' hinv' hsync' hpres hge _ _ hnone hsome hm' => ?_⟩)
  rw [sep_emp] at hm'
  by_cases hconfl : confl = 4294967295#32
  · subst hconfl
    exact ⟨ks', rfl, hinv', hsync', hnone rfl, by
      have : nvK6PropState.trl_end.toNat = 1 := rfl; omega, hm'⟩
  · exfalso
    obtain ⟨hlt, hall⟩ := hsome hconfl
    have hwf := hinv'.clauses.cl_wf confl.toNat hlt
    have hsat := hwf.2.2.2 (fun _ => true) ⟨rfl, rfl⟩
    rw [CNF.Clause.sat_iff_exists_mem_eq] at hsat
    obtain ⟨lit, hlitm, hlitb⟩ := hsat
    let l := litOfLiteral lit
    have hlcl : l ∈ k6ClauseLits ks' confl.toNat := mem_cnfClause_iff.mp hlitm
    have hl_lt : l < 2 * ks'.nv.toNat := hwf.2.2.1 l hlcl
    have hval2 := hall l hlcl
    have hx_lt : l ^^^ 1 < 2 * ks'.nv.toNat := by rw [nat_xor1_eq]; split <;> omega
    have hval1 : ks'.vals[l ^^^ 1]? = some 1#32 := by
      have hneg := (hinv'.assign.vals_neg_iff (l ^^^ 1) hx_lt).mpr
      have hx : (l ^^^ 1) ^^^ 1 = l := by rw [nat_xor1_eq, nat_xor1_eq]; split <;> split <;> omega
      rw [hx] at hneg
      have h1 := hneg (by rw [hval2]; rfl)
      rcases Option.isSome_iff_exists.mp (Classical.byContradiction fun hnone' => by
        have : ks'.vals[l ^^^ 1]? = none := Option.not_isSome_iff_eq_none.mp hnone'
        rw [this] at h1; cases h1) with ⟨v, hv⟩
      rw [hv, Option.getD_some] at h1; rw [hv, h1]
    have hnz : ks'.vals[l ^^^ 1]?.getD 0#32 ≠ 0#32 := by rw [hval1]; decide
    obtain ⟨i, hi, heq⟩ := (hinv'.assign.vals_nz_iff_trl (l ^^^ 1) hx_lt).mp hnz
    let l' := (ks'.trl[i]?.getD 0#32).toNat
    have hl'_div : l' / 2 = l / 2 := by
      have hd : (l ^^^ 1) / 2 = l / 2 := by rw [nat_xor1_eq]; split <;> omega
      exact heq.trans hd
    have hkl_lt : ks'.nv.toNat ≤ 512 := hinv'.clauses.nv_le
    have hl'_trl_len : i < ks'.trl.length := by
      have hte := hinv'.assign.trl_end_le
      have htl := hinv'.shapes.trl_len
      have hmV : nvM6K6Layout.maxV = 512 := by
        unfold nvM6K6Layout k6LayoutOfCap; exact kmax24576_val
      omega
    have hl'_mem : l' ∈ k6TrailLits ks' := by
      unfold k6TrailLits
      have hget : (ks'.trl.take ks'.trl_end.toNat)[i]? = some (ks'.trl[i]'hl'_trl_len) := by
        rw [List.getElem?_take, ite_eq_left hi, List.getElem?_eq_getElem hl'_trl_len]
      exact List.mem_map.mpr ⟨ks'.trl[i]'hl'_trl_len, List.mem_of_getElem? hget,
        by simp [l', List.getElem?_eq_getElem hl'_trl_len]⟩
    have hl'_lt := hinv'.assign.trl_lt l' hl'_mem
    have hlvl_le := hinv'.assign.trl_lvl_le (l' / 2) (by omega)
    have hklvl : ks'.lvl = 0#32 := by rw [hpres.lvl]; rfl
    have hlvl0 : ks'.lvlArr[l' / 2]?.getD 0#32 = 0#32 := by
      rw [hklvl] at hlvl_le
      apply BitVec.eq_of_toNat_eq; exact Nat.le_zero.mp hlvl_le
    obtain ⟨hv1', _, hent'⟩ := hinv'.assign.lvl0_ok i hi hlvl0
    have hsat' := hent' (fun _ => true) ⟨rfl, rfl⟩
    rw [CNF.Clause.sat_iff_exists_mem_eq] at hsat'
    obtain ⟨lit', hlit'm, hlit'b⟩ := hsat'
    have hl'eq : litOfLiteral lit' = l' := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using mem_cnfClause_iff.mp hlit'm
    have hne : l' ≠ l := fun h => by
      have h' : (ks'.trl[i]?.getD 0#32).toNat = l := h
      rw [h', hval2] at hv1'; cases hv1'
    have hle : l % 2 = 0 := by dsimp only [l, litOfLiteral, mkLit]; rw [← hlitb]; simp
    have hl'e : l' % 2 = 0 := by rw [← hl'eq]; dsimp only [litOfLiteral, mkLit]; rw [← hlit'b]; simp
    omega

/-! ### 4d. `nv_fid_k6_core_m8`: Non-Trivial `nv = 4, nc = 2` Core Setup -/

def nvFidK6CoreBuf : List (BitVec 32) :=
  (((((((((nvM6SweepScratchBuf.set 4192 4#32 |>.set 4193 2#32)
    |>.set 4206 5#32)
    |>.set 4207 100#32)
    |>.set 11648 0#32)
    |>.set 12672 2#32)
    |>.set 13696 0#32)
    |>.set 11649 2#32)
    |>.set 12673 (0x40000000#32 ||| 2#32))
    |>.set 13697 1#32)

private def setScrAt (m : Mem 64) (i : Nat) (v : BitVec 32) : Mem 64 :=
  storeMem m i32 (nvM4SweepCfg.pScratchBuf + BitVec.ofNat 64 (4 * i)) v

def nvFidK6CoreMem : Mem 64 :=
  let m1 := setScrAt nvM6SweepMem 4192 4#32
  let m2 := setScrAt m1 4193 2#32
  let m3 := setScrAt m2 4206 5#32
  let m4 := setScrAt m3 4207 100#32
  let m5 := setScrAt m4 11648 0#32
  let m6 := setScrAt m5 12672 2#32
  let m7 := setScrAt m6 13696 0#32
  let m8 := setScrAt m7 11649 2#32
  let m9 := setScrAt m8 12673 (0x40000000#32 ||| 2#32)
  setScrAt m9 13697 1#32

private def scrRest (s : FullState) : Mem 64 → Prop :=
  FullCoreArrays nvM4SweepCfg s.core ⋆ FullScrByteArrs nvM4SweepCfg s.scratch ⋆
  FullScrU32A nvM4SweepCfg s.scratch ⋆ FullScrWksArrs nvM4SweepCfg s.scratch ⋆
  FullScrMetaArrs nvM4SweepCfg s.scratch ⋆
  array (t := i32) nvM4SweepCfg.pDelayed s.scratch.delayed ⋆
  array (t := i32) nvM4SweepCfg.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) nvM4SweepCfg.pExtendStk s.scratch.extend_stk ⋆
  nvM4SweepCfg.pad ⋆
  dimacsState nvM4SweepCfg.hdr (BitVec.ofNat 64 nvM4SweepCfg.mv)
    (BitVec.ofNat 64 nvM4SweepCfg.nc) s.core.d_cur s.core.d_val ⋆
  array64 (nvM4SweepCfg.hdr + 32) (Full.hdrTailWords nvM4SweepCfg s)

private theorem fullMem_eq_scr (s : FullState) (scr : List (BitVec 32)) :
    FullMem nvM4SweepCfg { s with scratch := { s.scratch with scratch_buf := scr } } =
      (array (t := i32) nvM4SweepCfg.pScratchBuf scr ⋆ scrRest s) := by
  have hH : Full.hdrTailWords nvM4SweepCfg
      { s with scratch := { s.scratch with scratch_buf := scr } } =
      Full.hdrTailWords nvM4SweepCfg s := rfl
  have hB : FullScrByteArrs nvM4SweepCfg { s.scratch with scratch_buf := scr } =
      FullScrByteArrs nvM4SweepCfg s.scratch := rfl
  have hU : FullScrU32A nvM4SweepCfg { s.scratch with scratch_buf := scr } =
      FullScrU32A nvM4SweepCfg s.scratch := rfl
  have hW : FullScrWksArrs nvM4SweepCfg { s.scratch with scratch_buf := scr } =
      FullScrWksArrs nvM4SweepCfg s.scratch := rfl
  have hM : FullScrMetaArrs nvM4SweepCfg { s.scratch with scratch_buf := scr } =
      FullScrMetaArrs nvM4SweepCfg s.scratch := rfl
  unfold FullMem FullScratchArrays FullScrDynArrs scrRest
  dsimp only
  rw [hH, hB, hU, hW, hM]; ac_rfl

private theorem scr_off_step {xs : List (BitVec 32)} {m : Mem 64} {R : Mem 64 → Prop}
    (i : Nat) (v : BitVec 32) (hi : i < xs.length) (hi64 : i < 2 ^ 64)
    (hm : (array (t := i32) nvM4SweepCfg.pScratchBuf xs ⋆ R) m) :
    (array (t := i32) nvM4SweepCfg.pScratchBuf (xs.set i v) ⋆ R) (setScrAt m i v) := by
  unfold setScrAt
  have htn : (BitVec.ofNat 64 i).toNat = i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
  have hs := (store_array (t := i32) (i := i) v (by decide) hi hm).2
  have hb4 : i32.bytes = 4 := rfl
  rw [hb4] at hs; exact hs

private theorem nvFidK6CoreBuf_ok : M8K6BufOk nvFidK6CoreBuf := by
  have hlen : nvFidK6CoreBuf.length = 24576 := by
    simp [nvFidK6CoreBuf, nvM6SweepScratchBuf_length]
  have hnc : nvFidK6CoreBuf[4193]? = some 2#32 := by
    dsimp only [nvFidK6CoreBuf]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
  have hal : nvFidK6CoreBuf[4206]? = some 5#32 := by
    dsimp only [nvFidK6CoreBuf]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide),
        List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
  have hac : nvFidK6CoreBuf[4207]? = some 100#32 := by
    dsimp only [nvFidK6CoreBuf]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
        List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
  refine M8K6BufOk.mk_of (by rw [hlen, hac]; decide) (by rw [hlen]; decide)
    (by rw [hnc]; decide) (by rw [hal, hac]; decide) fun cid hcid => ?_
  rw [hnc] at hcid
  have hcid' : cid < 2 := by simpa using hcid
  rcases (show cid = 0 ∨ cid = 1 by omega) with rfl | rfl
  · have ho0 : nvFidK6CoreBuf[11648]? = some 0#32 := by
      dsimp only [nvFidK6CoreBuf]
      rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
          List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
          List.getElem?_set_ne (by decide),
          List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
    have hm0 : nvFidK6CoreBuf[12672]? = some 2#32 := by
      dsimp only [nvFidK6CoreBuf]
      rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
          List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
          List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
    have ha0 : nvFidK6CoreBuf[13696]? = some 0#32 := by
      dsimp only [nvFidK6CoreBuf]
      rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
          List.getElem?_set_ne (by decide),
          List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
    dsimp only; rw [ho0, hm0, ha0, hac]; decide
  · have ho1 : nvFidK6CoreBuf[11649]? = some 2#32 := by
      dsimp only [nvFidK6CoreBuf]
      rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
          List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
    have hm1 : nvFidK6CoreBuf[12673]? = some (0x40000000#32 ||| 2#32) := by
      dsimp only [nvFidK6CoreBuf]
      rw [List.getElem?_set_ne (by decide),
          List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
    have ha1 : nvFidK6CoreBuf[13697]? = some 1#32 := by
      dsimp only [nvFidK6CoreBuf]
      rw [List.getElem?_set_self (by simp [nvM6SweepScratchBuf_length])]
    dsimp only; rw [ho1, hm1, ha1, hac]; decide

private theorem nvFidK6CoreMem_ok :
    FullMem nvM4SweepCfg
      { nvM6SweepState with
        scratch := { nvM6SweepState.scratch with scratch_buf := nvFidK6CoreBuf } }
      nvFidK6CoreMem := by
  rw [fullMem_eq_scr]
  have h0 : (array (t := i32) nvM4SweepCfg.pScratchBuf nvM6SweepScratchBuf ⋆
      scrRest nvM6SweepState) nvM6SweepMem := by
    have heq : nvM6SweepState =
        { nvM6SweepState with
          scratch := { nvM6SweepState.scratch with scratch_buf := nvM6SweepScratchBuf } } := rfl
    have h := nvM6SweepMem_ok
    rw [heq] at h
    rwa [fullMem_eq_scr] at h
  have h1 := scr_off_step 4192 4#32 (by rw [nvM6SweepScratchBuf_length]; decide) (by decide) h0
  have h2 := scr_off_step 4193 2#32 (by simp [nvM6SweepScratchBuf_length]) (by decide) h1
  have h3 := scr_off_step 4206 5#32 (by simp [nvM6SweepScratchBuf_length]) (by decide) h2
  have h4 := scr_off_step 4207 100#32 (by simp [nvM6SweepScratchBuf_length]) (by decide) h3
  have h5 := scr_off_step 11648 0#32 (by simp [nvM6SweepScratchBuf_length]) (by decide) h4
  have h6 := scr_off_step 12672 2#32 (by simp [nvM6SweepScratchBuf_length]) (by decide) h5
  have h7 := scr_off_step 13696 0#32 (by simp [nvM6SweepScratchBuf_length]) (by decide) h6
  have h8 := scr_off_step 11649 2#32 (by simp [nvM6SweepScratchBuf_length]) (by decide) h7
  have h9 := scr_off_step 12673 (0x40000000#32 ||| 2#32)
    (by simp [nvM6SweepScratchBuf_length]) (by decide) h8
  exact scr_off_step 13697 1#32 (by simp [nvM6SweepScratchBuf_length]) (by decide) h9

private theorem fid_lengths_with_scrBuf {c : FullCfg} {s : FullState} {buf : List (BitVec 32)}
    (h : s.LengthsOk c) (hlen : buf.length = c.scratch_cap) :
    ({ s with scratch := { s.scratch with scratch_buf := buf } } : FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with scratch_buf_len := hlen }⟩

theorem nv_fid_k6_core_m8 :
    Func.wp fidVivK6Env full_k6_core_m8_fid_body (nvM4SweepCfg.hdr, ()) nvFidK6CoreMem
      (fun _ m' => ∃ scr',
        scr'.length = nvM4SweepCfg.scratch_cap ∧
        M8K6BufOk scr' ∧
        FullMem nvM4SweepCfg
          { nvM6SweepState with scratch := { nvM6SweepState.scratch with scratch_buf := scr' } }
          m')
      (fun _ _ _ _ => False) := by
  let s0 : FullState :=
    { nvM6SweepState with
      scratch := { nvM6SweepState.scratch with scratch_buf := nvFidK6CoreBuf } }
  have hlen : s0.LengthsOk nvM4SweepCfg :=
    fid_lengths_with_scrBuf nvM6SweepState_lengths (by
      dsimp only [nvFidK6CoreBuf]; simp only [List.length_set, nvM6SweepScratchBuf_length]; rfl)
  have hm : (FullMem nvM4SweepCfg s0 ⋆ emp) nvFidK6CoreMem := by
    rw [sep_emp]; exact nvFidK6CoreMem_ok
  have hmem : fidK6CoreM8Fn ∈ fidVivK6SplicedModule.fns :=
    fid_repl_mem_spliced (idx := 390) (by decide) fidK6CoreM8Fn (congrArg Prod.fst sig_at_390) rfl
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hmem
  have hwp := (fidVivK6Spliced_moduleOk.fnsOk pre _ post hsp).2.2
  exact hwp (nvM4SweepCfg.hdr, ()) nvFidK6CoreMem _ (fun _ _ _ _ => False)
    (patchEnv_front_row_bot fidVivK6Bundle
      (e := ⟨"full_k6_core_m8", [i64], [], m8K6CoreSpec, true⟩) rfl rfl rfl rfl _ _ _ _
      (m8K6CoreSpec_intro rfl hlen (by decide) nvFidK6CoreBuf_ok hm
        (fun scr' m' hlen' _ hok' hm' => by
          rw [sep_emp] at hm'; exact ⟨scr', hlen', hok', hm'⟩)))

end LeanQbe.T.Examples.Kissat.FullFidelityVivK6
