/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullProof
public import LeanQbe.T.Examples.Kissat.FullM4BumpProof
public import LeanQbe.T.Examples.Kissat.FullM3VivChronoLemmas
public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof0
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM5OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM5OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM5
public import LeanQbe.T.Examples.Kissat.FullM5Proof1
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof1
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof2
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushLemmas
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProofWatch
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof1
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof1b
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2a
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2b
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2c
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof

/-!
# Kissat M6.0 Parametric Segment Transports — Part 0 (`FullM6Transport0`)

Spec-table rows, zero-`whnf` transport combinators, and parametric `TableImpl (Env.ofTable tbl)`
transport theorems (`0` `@[expose]`, plain `public section`, `0` M1 `.olean` leaks) covering
`105` non-Orch functions in the first half of `FullM6`:
1. Shared combinators (`fullSliceTransport`, `modSubTransport`, `envRow_mem`,
   `allFns_drop_take_wf`).
2. `Dimacs` (`8`) and `Full1..5/M4` kept prefix (`42`: core `6`, heap `4`, rescale `1`, bump/sched
   `8`, init/assign `17`, parse `2`, prop helpers `3`, `recompute_tiers` `1`, reds `3`, `sweep_copy`
   `1`, renamed `"full_reduce"` `1`).
3. `FullM6Hdr` (`[0..23]` + `[24] = m6_hdr_decide`, `25` fns).
4. `FullM6BcpS15` (`4` fns).
5. `FullM6CompactFlush` (`8` fns: `full_flush_trail`, `full_sweep_bins_m6cf`, `full_enter_dense`,
   `full_compact_{needed,flush,mark_live}`, `Tmk` `full_extend_push{2,_cl}`).
6. `FullM6WatchGc` (`12` used fns, dropping `[5, 13..16]`).
7. Cross-module spec bridges (`extend_push{2,_cl}` `Tmk` ↔ canonical `Full` specs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Transport

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-! ## 1. Shared Parametric Segment-Transport Combinators (Zero-`whnf`) -/

/-- Closed `Full` table at canonical `Full.fullSolveBytesSpec` (`166` rows). -/
abbrev fullBaseTable : List SpecEntry := Full.fullSpecTable Full.fullSolveBytesSpec

theorem fullSpecTable_sigs :
    fullBaseTable.map (fun e => (e.name, e.as, e.rs)) =
      Full.fullFns.map (fun f => (f.name, f.as, f.rs)) :=
  Full.fullSpecTable_sigs Full.fullSolveBytesSpec

theorem fullFns_length_eq : Full.fullFns.length = fullBaseTable.length := by
  have h1 := congrArg List.length fullSpecTable_sigs
  simpa only [List.length_map] using h1.symm

theorem fullBaseTable_nodup : (fullBaseTable.map SpecEntry.name).Nodup := by
  have hnames : fullBaseTable.map SpecEntry.name = Full.fullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) fullSpecTable_sigs
    simpa only [List.map_map, Function.comp_def] using hm
  exact tbl_nodup_of_sigs (M := Full.fullModule)
    (by t_kernel_rfl : Full.fullModule.checkAcyclic = true) hnames

/-- `O(idx)` membership witness in `fullBaseTable` avoiding `simp` over `166` rows. -/
theorem fullRow_at (idx : Nat) (e : SpecEntry)
    (h : fullBaseTable[idx]? = some e := by rfl) : e ∈ fullBaseTable :=
  List.mem_of_getElem? h

/-- Direct `Env.ofTable tbl` lookup from an explicit membership witness `e ∈ tbl`. -/
theorem envRow_mem {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (nm : String) (as bs : List Ty) (sp : Spec as bs)
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ tbl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → Env.ofTable tbl nm as bs xs m Q X :=
  fun xs m Q X hs => Env.ofTable_of_mem hmem hnd (by
    dsimp only [SpecEntry.eff]
    simp only [ite_true]
    exact hno xs m Q X hs)

/-- Convert `(xs.all p = true)` to `∀ x ∈ xs, p x = true` without unfolding. -/
theorem all_mem_of_bool {α : Type _} {xs : List α} {p : α → Bool}
    (h : xs.all p = true) : ∀ x ∈ xs, p x = true :=
  List.all_eq_true.mp h

/-- Convert `(∀ f ∈ fs, f.Wf)` to `AllFns Fn.Wf fs`. -/
theorem allFns_of_mem {fs : List Fn} (h : ∀ f ∈ fs, f.Wf) : AllFns Fn.Wf fs := by
  induction fs with
  | nil => exact trivial
  | cons a t ih =>
      exact ⟨h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

/-- Lift `(∀ f ∈ allFns, f.Wf)` to `AllFns Fn.Wf ((allFns.drop off).take n)`. -/
theorem allFns_drop_take_wf {allFns : List Fn}
    (hwf : ∀ f ∈ allFns, f.Wf) (off n : Nat) :
    AllFns Fn.Wf ((allFns.drop off).take n) :=
  allFns_of_mem fun _ hf => hwf _ (List.mem_of_mem_drop (List.mem_of_mem_take hf))

/-- Prove `hm1_sub` cleanly when `fs = (M1.fns.drop off).take n` and
`sub_tbl = (t1.drop off).take n`. -/
theorem modSub_drop_take {M1 : Module} {t1 : List SpecEntry}
    (hsig : t1.map (fun e => (e.name, e.as, e.rs)) =
      M1.fns.map (fun f => (f.name, f.as, f.rs)))
    {off n : Nat} :
    ((M1.fns.drop off).take n).length = ((t1.drop off).take n).length ∧
    ∀ p ∈ List.zip ((M1.fns.drop off).take n) ((t1.drop off).take n),
      p.1 ∈ M1.fns ∧ p.2 ∈ t1 ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
  have hlen1 : M1.fns.length = t1.length := by
    have := congrArg List.length hsig
    simpa only [List.length_map] using this.symm
  have hlen_dt :
      ((M1.fns.drop off).take n).length = ((t1.drop off).take n).length := by
    simp only [List.length_take, List.length_drop, hlen1]
  refine ⟨hlen_dt, fun p hp => ?_⟩
  rw [List.mem_iff_getElem] at hp
  obtain ⟨k, hk_lt, hk_eq⟩ := hp
  have hk_zip_len : k < min ((M1.fns.drop off).take n).length ((t1.drop off).take n).length := by
    simpa [List.length_zip] using hk_lt
  have hk1 : k < ((M1.fns.drop off).take n).length :=
    Nat.lt_of_lt_of_le hk_zip_len (Nat.min_le_left _ _)
  have hk2 : k < ((t1.drop off).take n).length :=
    Nat.lt_of_lt_of_le hk_zip_len (Nat.min_le_right _ _)
  have hk_zip : p =
      (((M1.fns.drop off).take n)[k]'hk1, ((t1.drop off).take n)[k]'hk2) := by
    rw [← hk_eq, List.getElem_zip]
  have hp1_dt : p.1 ∈ (M1.fns.drop off).take n := by rw [hk_zip]; exact List.getElem_mem hk1
  have hp2_dt : p.2 ∈ (t1.drop off).take n := by rw [hk_zip]; exact List.getElem_mem hk2
  have hoff_k1 : off + k < M1.fns.length := by
    simp only [List.length_take, List.length_drop] at hk1; omega
  have hoff_k2 : off + k < t1.length := hlen1 ▸ hoff_k1
  have hp1_eq : M1.fns[off + k]'hoff_k1 = p.1 := by
    rw [hk_zip]; dsimp only; rw [List.getElem_take, List.getElem_drop]
  have hp2_eq : t1[off + k]'hoff_k2 = p.2 := by
    rw [hk_zip]; dsimp only; rw [List.getElem_take, List.getElem_drop]
  have hopt :
      (t1.map (fun e => (e.name, e.as, e.rs)))[off + k]? =
      (M1.fns.map (fun f => (f.name, f.as, f.rs)))[off + k]? :=
    congrArg (fun l => l[off + k]?) hsig
  simp only [List.getElem?_map, List.getElem?_eq_getElem hoff_k2,
    List.getElem?_eq_getElem hoff_k1, Option.map_some] at hopt
  have hsig_k := Option.some.inj hopt
  rw [hp1_eq, hp2_eq] at hsig_k
  exact ⟨List.mem_of_mem_drop (List.mem_of_mem_take hp1_dt),
    List.mem_of_mem_drop (List.mem_of_mem_take hp2_dt),
    congrArg Prod.fst hsig_k, congrArg (fun x => x.2.1) hsig_k,
    congrArg (fun x => x.2.2) hsig_k⟩

/-- Transport an arbitrary sub-segment `(fs, sub_tbl)` from a closed standalone `ModuleOk`
into an arbitrary specification table `tbl` via `FullM6ProofUtil.tableImpl_transport_of_callsOk`. -/
theorem modSubTransport {M1 : Module} {t1 : List SpecEntry}
    (hM1 : ModuleOk (Env.ofTable t1) M1) (hnd1 : (t1.map SpecEntry.name).Nodup)
    {fs : List Fn} {sub_tbl extRows : List SpecEntry}
    (hlen : fs.length = sub_tbl.length)
    (hm1_sub : ∀ p ∈ List.zip fs sub_tbl,
      p.1 ∈ M1.fns ∧ p.2 ∈ t1 ∧ p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs)
    (hcalls : ∀ fn ∈ fs,
      fn.checkCallsOk ((sub_tbl ++ extRows).map fun e => (e.name, e.as, e.rs)) [] = true)
    (hext_m1 : ∀ e ∈ extRows, e ∈ t1)
    {tbl : List SpecEntry}
    (hnd2 : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ sub_tbl, e ∈ tbl)
    (hext : ∀ e ∈ extRows, e ∈ tbl) :
    AllFns Fn.Wf fs ∧ TableImpl (Env.ofTable tbl) fs sub_tbl := by
  refine tableImpl_transport_of_callsOk hM1 hnd1 hnd2 hlen ?_ hcalls ?_
  · intro p hp
    obtain ⟨h1, h2, hnm, has, hrs⟩ := hm1_sub p hp
    exact ⟨h1, h2, hown p.2 (List.of_mem_zip hp).2, hnm, has, hrs⟩
  · intro s hs
    rcases List.mem_map.mp hs with ⟨e, he, rfl⟩
    rcases List.mem_append.mp he with h | h
    · have hex : ∃ p ∈ List.zip fs sub_tbl, p.2 = e := by
        rw [List.mem_iff_getElem] at h
        obtain ⟨k, hk, hkeq⟩ := h
        have hkz : k < (List.zip fs sub_tbl).length := by rw [List.length_zip, hlen]; omega
        exact ⟨(List.zip fs sub_tbl)[k], List.getElem_mem hkz, by simp [List.getElem_zip, hkeq]⟩
      obtain ⟨p, hpz, rfl⟩ := hex
      exact ⟨p.2, (hm1_sub p hpz).2.1, hown p.2 h, rfl⟩
    · exact ⟨e, hext_m1 e h, hext e h, rfl⟩

/-- Transport a contiguous `(drop off).take n` slice from a standalone `ModuleOk`. -/
theorem modDropTakeTransport {M1 : Module} {t1 : List SpecEntry}
    (hM1 : ModuleOk (Env.ofTable t1) M1) (hnd1 : (t1.map SpecEntry.name).Nodup)
    (hsig : t1.map (fun e => (e.name, e.as, e.rs)) =
      M1.fns.map (fun f => (f.name, f.as, f.rs)))
    (off n : Nat) (extRows : List SpecEntry)
    (hcalls : ((M1.fns.drop off).take n).all
      (fun fn => fn.checkCallsOk
        (((t1.drop off).take n ++ extRows).map fun e => (e.name, e.as, e.rs)) []) = true)
    (hext_m1 : ∀ e ∈ extRows, e ∈ t1)
    {tbl : List SpecEntry}
    (hnd2 : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ (t1.drop off).take n, e ∈ tbl)
    (hext : ∀ e ∈ extRows, e ∈ tbl) :
    AllFns Fn.Wf ((M1.fns.drop off).take n) ∧
    TableImpl (Env.ofTable tbl) ((M1.fns.drop off).take n) ((t1.drop off).take n) :=
  let hz := modSub_drop_take hsig (off := off) (n := n)
  modSubTransport hM1 hnd1 hz.1 hz.2 (all_mem_of_bool hcalls) hext_m1 hnd2 hown hext

/-- Transport a contiguous `(drop off).take n` slice from `Full.fullEnv_moduleOk`. -/
theorem fullSliceTransport
    (off n : Nat) (extRows : List SpecEntry)
    (hcalls : ((Full.fullFns.drop off).take n).all
      (fun fn => fn.checkCallsOk
        (((fullBaseTable.drop off).take n ++ extRows).map
          fun e => (e.name, e.as, e.rs)) []) = true)
    (hext_full : ∀ e ∈ extRows, e ∈ fullBaseTable)
    {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ (fullBaseTable.drop off).take n, e ∈ tbl)
    (hext : ∀ e ∈ extRows, e ∈ tbl) :
    AllFns Fn.Wf ((Full.fullFns.drop off).take n) ∧
    TableImpl (Env.ofTable tbl) ((Full.fullFns.drop off).take n)
      ((fullBaseTable.drop off).take n) :=
  modDropTakeTransport Full.fullEnv_moduleOk fullBaseTable_nodup fullSpecTable_sigs
    off n extRows hcalls hext_full hnd hown hext

/-! ## 2. Segment Definitions (`Dimacs`, `Full1..5/M4` Kept Prefix, `Hdr`, `BcpS15`, `CF`, `WG`) -/

/-- `8` fns: `Dimacs` parser and model checker (`Full[0..7]`). -/
def m6DimacsFns : List Fn := Full.fullFns.take 8
def m6DimacsRows : List SpecEntry := fullBaseTable.take 8

/-- `6` fns: `Full1` core utilities (`full_isqrt .. full_wsort_sift`, `Full[8..13]`). -/
def m6Full1CoreFns : List Fn := (Full.fullFns.drop 8).take 6
def m6Full1CoreRows : List SpecEntry := (fullBaseTable.drop 8).take 6

/-- `3` fns: `FullM6WatchGc[0..2]` (`wstack_{radix_sort,defrag}_m6`, `watch_push_m6`). -/
def m6WatchGc0Fns : List Fn := FullM6WatchGc.m6WatchGc_fns.take 3
def m6WatchGc0Rows : List SpecEntry :=
  [ ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [],
      FullM6WatchGc.fullWstackRadixSortSpec, true⟩
  , ⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ]

/-- `4` fns: `Full1` VSIDS binary heap (`full_heap_{up,down,push,pop}`, `Full[16..19]`). -/
def m6HeapFns : List Fn := (Full.fullFns.drop 16).take 4
def m6HeapRows : List SpecEntry := (fullBaseTable.drop 16).take 4

/-- `1` fn: `full_rescale` (`Full[20]`). -/
def m6RescaleFns : List Fn := (Full.fullFns.drop 20).take 1
def m6RescaleRows : List SpecEntry := (fullBaseTable.drop 20).take 1

/-- `8` fns: `M4Bump`, `Full[22..24]`, `VivChrono` `full_tick_rel`, `M5Sched[0..2]`. -/
def m6BumpSchedFns : List Fn :=
  [FullM4Bump.m4BumpVarFn] ++ ((Full.fullFns.drop 22).take 3 ++
  ([FullM3VivChrono.m3TickRelFn] ++ FullM5Sched.m5Sched_fns.take 3))

def m6BumpSchedRows : List SpecEntry :=
  [⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩] ++
  ((fullBaseTable.drop 22).take 3 ++
  ([⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩] ++
  FullM5Sched.m5SchedSpecTable.take 3))

/-- `17` fns: assign/backtrack/init kept prefix (`Full[27..28,31..35,37,40]` + `M5`). -/
def m6InitAssignFns : List Fn :=
  (Full.fullFns.drop 27).take 2 ++
  ([ FullM5HeurCore.m5SaveTargetBestFn
   , FullM5HeurCore.m5BacktrackRawFn
   , FullM5HeurCore.m5BacktrackFn ] ++
  ((Full.fullFns.drop 31).take 5 ++
  (FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  ((Full.fullFns.drop 37).take 1 ++
  (FullM5Orch.m5Orch_fns.take 2 ++
  ((Full.fullFns.drop 40).take 1 ++
  ((FullM5Orch.m5Orch_fns.drop 2).take 1 ++
   [FullM5.m5InitStateFwdFn])))))))

def m6InitAssignRows : List SpecEntry :=
  (fullBaseTable.drop 27).take 2 ++
  ([ ⟨"full_save_target_best", [i64], [], Full.fullSaveTargetBestSpec, true⟩
   , ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩
   , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ] ++
  ((fullBaseTable.drop 31).take 5 ++
  ([⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩] ++
  ((fullBaseTable.drop 37).take 1 ++
  ([ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
   , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩ ] ++
  ((fullBaseTable.drop 40).take 1 ++
   [ ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩
   , ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
       Full.fullInitStateSpec, true⟩ ]))))))

/-- `24` fns: `FullM6Hdr[0..23]` (`full_m6_hdr_sizeof .. m6_hdr_dr_allow`). -/
def m6Hdr0Fns : List Fn := FullM6Hdr.m6HdrModule.fns.take 24
def m6Hdr0Rows : List SpecEntry :=
  [ ⟨"full_m6_hdr_sizeof", [], [i64], FullM6Hdr.m6HdrSizeofSpec, true⟩
  , ⟨"full_m6_ext_sizeof", [], [i64], FullM6Hdr.m6ExtSizeofSpec, true⟩
  , ⟨"m6_hdr_init", [i64], [], FullM6Hdr.m6HdrInitSpec, true⟩
  , ⟨"m6_hdr_reset", [i64], [], FullM6Hdr.m6HdrResetSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], FullM6Hdr.m6ExtEnsureInitSpec, true⟩
  , ⟨"m6_hdr_ext_ready", [i64], [.bool], FullM6Hdr.m6HdrExtReadySpec, true⟩
  , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], FullM6Hdr.fullM6MemInitSpec, true⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], FullM6Hdr.m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_recompute_tiers", [i64], [], FullM6Hdr.m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_update_tier_limits", [i64], [], FullM6Hdr.m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_record_used", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], FullM6Hdr.m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], FullM6Hdr.m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], FullM6Hdr.m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reset_delay", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], FullM6Hdr.m6HdrW2aSpec [i64] [i64], true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"m6_hdr_add_ticks", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_dr_init", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_update", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩
  , ⟨"m6_hdr_dr_allow", [i64], [.bool], FullM6Hdr.m6HdrDrAllowSpec, true⟩ ]

/-- `2` fns: `full_skip_cl`, `full_ingest_cl` (`Full[42..43]`). -/
def m6ParseHelpersFns : List Fn := (Full.fullFns.drop 42).take 2
def m6ParseHelpersRows : List SpecEntry := (fullBaseTable.drop 42).take 2

/-- `3` fns: `full_find_repl`, `full_assign_level`, `full_unwatch_large`. -/
def m6PropHelpersFns : List Fn :=
  (Full.fullFns.drop 45).take 2 ++ FullM5Otfs.m5Otfs_fns.take 1
def m6PropHelpersRows : List SpecEntry :=
  (fullBaseTable.drop 45).take 2 ++
  [⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩]

/-- `4` fns: `FullM6BcpS15` (`full_prop_lit_ovf_s15 .. full_bcp_s15`). -/
def m6BcpS15Fns : List Fn := FullM6BcpS15.m6BcpS15_fns
def m6BcpS15Rows : List SpecEntry := FullM6BcpS15.m6BcpS15SpecTable.take 4

/-- `1` fn: `full_recompute_tiers` (`Full[50]`). -/
def m6RecomputeTiersFns : List Fn := (Full.fullFns.drop 50).take 1
def m6RecomputeTiersRows : List SpecEntry := (fullBaseTable.drop 50).take 1

/-- `2` fns: `FullM6WatchGc[3..4]` (`full_lit_rank_m6`, `full_sweep_bins_range_m6`). -/
def m6WatchGc1Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 3).take 2
def m6WatchGc1Rows : List SpecEntry :=
  [ ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins_range_m6", [i64, i64], [], FullM6WatchGc.fullSweepBinsRangeSpec, true⟩ ]

/-- `2` fns: `FullM6WatchGc[6..7]` (`full_rewatch_range_m6`, `full_rewatch_arena_m6`). -/
def m6WatchGc2Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 6).take 2
def m6WatchGc2Rows : List SpecEntry :=
  [ ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool], FullM6WatchGc.fullRewatchRangeSpec, true⟩
  , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩ ]

/-- `1` fn: `FullM6CompactFlush.m6CompactFlush_fns[1]` (`full_sweep_bins_m6cf`). -/
def m6SweepBinsM6cfFns : List Fn := (FullM6CompactFlush.m6CompactFlush_fns.drop 1).take 1
def m6SweepBinsM6cfRows : List SpecEntry :=
  [⟨"full_sweep_bins_m6cf", [i64], [], Full.fullSweepBinsSpec, true⟩]

/-- `1` fn: `full_sweep_copy` (`Full[58]`). -/
def m6SweepCopyFns : List Fn := (Full.fullFns.drop 58).take 1
def m6SweepCopyRows : List SpecEntry := (fullBaseTable.drop 58).take 1

/-- `5` fns: `FullM6WatchGc[8..12]` (`move_red_pass2_m6 .. mark_reasons_m6`). -/
def m6WatchGc3Fns : List Fn := (FullM6WatchGc.m6WatchGc_fns.drop 8).take 5
def m6WatchGc3Rows : List SpecEntry :=
  [ ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [],
      FullM6WatchGc.fullMoveRedPass2Spec, true⟩
  , ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [],
      FullM6WatchGc.fullMoveRedEndBufSpec, true⟩
  , ⟨"full_move_red_end_m6", [i64, i64, i64], [], FullM6WatchGc.fullMoveRedEndSpec, true⟩
  , ⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons_m6", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩ ]

/-- `1` fn: `FullM6CompactFlush.m6cfFlushTrailFn` (`full_flush_trail`). -/
def m6FlushTrailFns : List Fn := [FullM6CompactFlush.m6cfFlushTrailFn]
def m6FlushTrailRows : List SpecEntry :=
  [⟨"full_flush_trail", [i64], [i64], FullM6CompactFlush.fullFlushTrailSpec, true⟩]

/-- `3` fns: `full_red_less`, `full_red_sift`, `full_sort_reds` (`Full[52..54]`). -/
def m6RedsFns : List Fn := (Full.fullFns.drop 52).take 3
def m6RedsRows : List SpecEntry := (fullBaseTable.drop 52).take 3

/-- Canonical `"full_reduce"` handle backed by `FullM5Orch.full_reduce_m5_body`. -/
def m6ReduceFn : Fn :=
  ⟨"full_reduce", [i64, .bool], [i64], FullM5Orch.full_reduce_m5_body⟩

/-- `1` fn: `"full_reduce"` (`Full.fullReduceSpec`). -/
def m6ReduceFns : List Fn := [m6ReduceFn]
def m6ReduceRows : List SpecEntry :=
  [⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩]

/-- `1` fn: `FullM6Hdr[24]` (`m6_hdr_decide`). -/
def m6HdrDecideFns : List Fn := (FullM6Hdr.m6HdrModule.fns.drop 24).take 1
def m6HdrDecideRows : List SpecEntry :=
  [⟨"m6_hdr_decide", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩]

/-- `1` fn: `m6cfExtendPush2Fn` (`full_extend_push2`, `fullExtendPush2TmkSpec`). -/
def m6CfExtendPush2Fns : List Fn := [FullM6CompactFlush.m6cfExtendPush2Fn]
def m6CfExtendPush2Rows : List SpecEntry :=
  [⟨"full_extend_push2", [i64, i32, i32], [.bool],
    FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩]

/-- `1` fn: `m6cfExtendPushClFn` (`full_extend_push_cl`, `fullExtendPushClTmkSpec`). -/
def m6CfExtendPushClFns : List Fn := [FullM6CompactFlush.m6cfExtendPushClFn]
def m6CfExtendPushClRows : List SpecEntry :=
  [⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
    FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩]

/-- `1` fn: `m6cfEnterDenseFn` (`full_enter_dense`, `schedEnterDenseSpec`). -/
def m6CfEnterDenseFns : List Fn := [FullM6CompactFlush.m6cfEnterDenseFn]
def m6CfEnterDenseRows : List SpecEntry :=
  [⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩]

/-- `3` fns: `full_compact_{needed,flush,mark_live}` from `FullM6CompactFlush`. -/
def m6CfCompact3Fns : List Fn :=
  [ FullM6CompactFlush.m6cfCompactNeededFn
  , FullM6CompactFlush.m6cfCompactFlushFn
  , FullM6CompactFlush.m6cfCompactMarkLiveFn ]

def m6CfCompact3Rows : List SpecEntry :=
  [ ⟨"full_compact_needed", [i64], [.bool], FullM6CompactFlush.fullCompactNeededM6Spec, true⟩
  , ⟨"full_compact_flush", [i64], [i64], FullM4Compact.fullCompactFlushSpec, true⟩
  , ⟨"full_compact_mark_live", [i64], [], FullM4Compact.fullCompactMarkLiveSpec, true⟩ ]

/-! ## 3. Metadata, `noExit`, and Row-Membership Exports (Zero-`@[expose]`) -/

private theorem m6Dimacs_len_p : m6DimacsFns.length = m6DimacsRows.length := rfl
theorem m6Dimacs_len : m6DimacsFns.length = m6DimacsRows.length := m6Dimacs_len_p
private theorem m6Full1Core_len_p : m6Full1CoreFns.length = m6Full1CoreRows.length := rfl
theorem m6Full1Core_len : m6Full1CoreFns.length = m6Full1CoreRows.length := m6Full1Core_len_p
private theorem m6WatchGc0_len_p : m6WatchGc0Fns.length = m6WatchGc0Rows.length := rfl
theorem m6WatchGc0_len : m6WatchGc0Fns.length = m6WatchGc0Rows.length := m6WatchGc0_len_p
private theorem m6Heap_len_p : m6HeapFns.length = m6HeapRows.length := rfl
theorem m6Heap_len : m6HeapFns.length = m6HeapRows.length := m6Heap_len_p
private theorem m6Rescale_len_p : m6RescaleFns.length = m6RescaleRows.length := rfl
theorem m6Rescale_len : m6RescaleFns.length = m6RescaleRows.length := m6Rescale_len_p
private theorem m6BumpSched_len_p : m6BumpSchedFns.length = m6BumpSchedRows.length := rfl
theorem m6BumpSched_len : m6BumpSchedFns.length = m6BumpSchedRows.length := m6BumpSched_len_p
private theorem m6InitAssign_len_p : m6InitAssignFns.length = m6InitAssignRows.length := rfl
theorem m6InitAssign_len : m6InitAssignFns.length = m6InitAssignRows.length := m6InitAssign_len_p
private theorem m6Hdr0_len_p : m6Hdr0Fns.length = m6Hdr0Rows.length := rfl
theorem m6Hdr0_len : m6Hdr0Fns.length = m6Hdr0Rows.length := m6Hdr0_len_p
private theorem m6ParseHelpers_len_p :
    m6ParseHelpersFns.length = m6ParseHelpersRows.length := rfl
theorem m6ParseHelpers_len :
    m6ParseHelpersFns.length = m6ParseHelpersRows.length := m6ParseHelpers_len_p
private theorem m6PropHelpers_len_p :
    m6PropHelpersFns.length = m6PropHelpersRows.length := rfl
theorem m6PropHelpers_len :
    m6PropHelpersFns.length = m6PropHelpersRows.length := m6PropHelpers_len_p
private theorem m6BcpS15_len_p : m6BcpS15Fns.length = m6BcpS15Rows.length := rfl
theorem m6BcpS15_len : m6BcpS15Fns.length = m6BcpS15Rows.length := m6BcpS15_len_p
private theorem m6RecomputeTiers_len_p :
    m6RecomputeTiersFns.length = m6RecomputeTiersRows.length := rfl
theorem m6RecomputeTiers_len :
    m6RecomputeTiersFns.length = m6RecomputeTiersRows.length := m6RecomputeTiers_len_p
private theorem m6WatchGc1_len_p : m6WatchGc1Fns.length = m6WatchGc1Rows.length := rfl
theorem m6WatchGc1_len : m6WatchGc1Fns.length = m6WatchGc1Rows.length := m6WatchGc1_len_p
private theorem m6WatchGc2_len_p : m6WatchGc2Fns.length = m6WatchGc2Rows.length := rfl
theorem m6WatchGc2_len : m6WatchGc2Fns.length = m6WatchGc2Rows.length := m6WatchGc2_len_p
private theorem m6SweepBinsM6cf_len_p :
    m6SweepBinsM6cfFns.length = m6SweepBinsM6cfRows.length := rfl
theorem m6SweepBinsM6cf_len :
    m6SweepBinsM6cfFns.length = m6SweepBinsM6cfRows.length := m6SweepBinsM6cf_len_p
private theorem m6SweepCopy_len_p : m6SweepCopyFns.length = m6SweepCopyRows.length := rfl
theorem m6SweepCopy_len : m6SweepCopyFns.length = m6SweepCopyRows.length := m6SweepCopy_len_p
private theorem m6WatchGc3_len_p : m6WatchGc3Fns.length = m6WatchGc3Rows.length := rfl
theorem m6WatchGc3_len : m6WatchGc3Fns.length = m6WatchGc3Rows.length := m6WatchGc3_len_p
private theorem m6FlushTrail_len_p : m6FlushTrailFns.length = m6FlushTrailRows.length := rfl
theorem m6FlushTrail_len : m6FlushTrailFns.length = m6FlushTrailRows.length := m6FlushTrail_len_p
private theorem m6Reds_len_p : m6RedsFns.length = m6RedsRows.length := rfl
theorem m6Reds_len : m6RedsFns.length = m6RedsRows.length := m6Reds_len_p
private theorem m6Reduce_len_p : m6ReduceFns.length = m6ReduceRows.length := rfl
theorem m6Reduce_len : m6ReduceFns.length = m6ReduceRows.length := m6Reduce_len_p
private theorem m6HdrDecide_len_p : m6HdrDecideFns.length = m6HdrDecideRows.length := rfl
theorem m6HdrDecide_len : m6HdrDecideFns.length = m6HdrDecideRows.length := m6HdrDecide_len_p
private theorem m6CfExtendPush2_len_p :
    m6CfExtendPush2Fns.length = m6CfExtendPush2Rows.length := rfl
theorem m6CfExtendPush2_len :
    m6CfExtendPush2Fns.length = m6CfExtendPush2Rows.length := m6CfExtendPush2_len_p
private theorem m6CfExtendPushCl_len_p :
    m6CfExtendPushClFns.length = m6CfExtendPushClRows.length := rfl
theorem m6CfExtendPushCl_len :
    m6CfExtendPushClFns.length = m6CfExtendPushClRows.length := m6CfExtendPushCl_len_p
private theorem m6CfEnterDense_len_p :
    m6CfEnterDenseFns.length = m6CfEnterDenseRows.length := rfl
theorem m6CfEnterDense_len :
    m6CfEnterDenseFns.length = m6CfEnterDenseRows.length := m6CfEnterDense_len_p
private theorem m6CfCompact3_len_p : m6CfCompact3Fns.length = m6CfCompact3Rows.length := rfl
theorem m6CfCompact3_len : m6CfCompact3Fns.length = m6CfCompact3Rows.length := m6CfCompact3_len_p

private theorem m6Dimacs_sigs_p :
    m6DimacsRows.map (fun e => (e.name, e.as, e.rs)) =
      m6DimacsFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6Dimacs_sigs :
    m6DimacsRows.map (fun e => (e.name, e.as, e.rs)) =
      m6DimacsFns.map (fun f => (f.name, f.as, f.rs)) := m6Dimacs_sigs_p
private theorem m6Full1Core_sigs_p :
    m6Full1CoreRows.map (fun e => (e.name, e.as, e.rs)) =
      m6Full1CoreFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6Full1Core_sigs :
    m6Full1CoreRows.map (fun e => (e.name, e.as, e.rs)) =
      m6Full1CoreFns.map (fun f => (f.name, f.as, f.rs)) := m6Full1Core_sigs_p
private theorem m6WatchGc0_sigs_p :
    m6WatchGc0Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6WatchGc0Fns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6WatchGc0_sigs :
    m6WatchGc0Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6WatchGc0Fns.map (fun f => (f.name, f.as, f.rs)) := m6WatchGc0_sigs_p
private theorem m6Heap_sigs_p :
    m6HeapRows.map (fun e => (e.name, e.as, e.rs)) =
      m6HeapFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6Heap_sigs :
    m6HeapRows.map (fun e => (e.name, e.as, e.rs)) =
      m6HeapFns.map (fun f => (f.name, f.as, f.rs)) := m6Heap_sigs_p
private theorem m6Rescale_sigs_p :
    m6RescaleRows.map (fun e => (e.name, e.as, e.rs)) =
      m6RescaleFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6Rescale_sigs :
    m6RescaleRows.map (fun e => (e.name, e.as, e.rs)) =
      m6RescaleFns.map (fun f => (f.name, f.as, f.rs)) := m6Rescale_sigs_p
private theorem m6BumpSched_sigs_p :
    m6BumpSchedRows.map (fun e => (e.name, e.as, e.rs)) =
      m6BumpSchedFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6BumpSched_sigs :
    m6BumpSchedRows.map (fun e => (e.name, e.as, e.rs)) =
      m6BumpSchedFns.map (fun f => (f.name, f.as, f.rs)) := m6BumpSched_sigs_p
private theorem m6InitAssign_sigs_p :
    m6InitAssignRows.map (fun e => (e.name, e.as, e.rs)) =
      m6InitAssignFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6InitAssign_sigs :
    m6InitAssignRows.map (fun e => (e.name, e.as, e.rs)) =
      m6InitAssignFns.map (fun f => (f.name, f.as, f.rs)) := m6InitAssign_sigs_p
private theorem m6Hdr0_sigs_p :
    m6Hdr0Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6Hdr0Fns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6Hdr0_sigs :
    m6Hdr0Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6Hdr0Fns.map (fun f => (f.name, f.as, f.rs)) := m6Hdr0_sigs_p
private theorem m6ParseHelpers_sigs_p :
    m6ParseHelpersRows.map (fun e => (e.name, e.as, e.rs)) =
      m6ParseHelpersFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6ParseHelpers_sigs :
    m6ParseHelpersRows.map (fun e => (e.name, e.as, e.rs)) =
      m6ParseHelpersFns.map (fun f => (f.name, f.as, f.rs)) := m6ParseHelpers_sigs_p
private theorem m6PropHelpers_sigs_p :
    m6PropHelpersRows.map (fun e => (e.name, e.as, e.rs)) =
      m6PropHelpersFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6PropHelpers_sigs :
    m6PropHelpersRows.map (fun e => (e.name, e.as, e.rs)) =
      m6PropHelpersFns.map (fun f => (f.name, f.as, f.rs)) := m6PropHelpers_sigs_p
private theorem m6BcpS15_sigs_p :
    m6BcpS15Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6BcpS15Fns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6BcpS15_sigs :
    m6BcpS15Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6BcpS15Fns.map (fun f => (f.name, f.as, f.rs)) := m6BcpS15_sigs_p
private theorem m6RecomputeTiers_sigs_p :
    m6RecomputeTiersRows.map (fun e => (e.name, e.as, e.rs)) =
      m6RecomputeTiersFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6RecomputeTiers_sigs :
    m6RecomputeTiersRows.map (fun e => (e.name, e.as, e.rs)) =
      m6RecomputeTiersFns.map (fun f => (f.name, f.as, f.rs)) := m6RecomputeTiers_sigs_p
private theorem m6WatchGc1_sigs_p :
    m6WatchGc1Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6WatchGc1Fns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6WatchGc1_sigs :
    m6WatchGc1Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6WatchGc1Fns.map (fun f => (f.name, f.as, f.rs)) := m6WatchGc1_sigs_p
private theorem m6WatchGc2_sigs_p :
    m6WatchGc2Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6WatchGc2Fns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6WatchGc2_sigs :
    m6WatchGc2Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6WatchGc2Fns.map (fun f => (f.name, f.as, f.rs)) := m6WatchGc2_sigs_p
private theorem m6SweepBinsM6cf_sigs_p :
    m6SweepBinsM6cfRows.map (fun e => (e.name, e.as, e.rs)) =
      m6SweepBinsM6cfFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6SweepBinsM6cf_sigs :
    m6SweepBinsM6cfRows.map (fun e => (e.name, e.as, e.rs)) =
      m6SweepBinsM6cfFns.map (fun f => (f.name, f.as, f.rs)) := m6SweepBinsM6cf_sigs_p
private theorem m6SweepCopy_sigs_p :
    m6SweepCopyRows.map (fun e => (e.name, e.as, e.rs)) =
      m6SweepCopyFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6SweepCopy_sigs :
    m6SweepCopyRows.map (fun e => (e.name, e.as, e.rs)) =
      m6SweepCopyFns.map (fun f => (f.name, f.as, f.rs)) := m6SweepCopy_sigs_p
private theorem m6WatchGc3_sigs_p :
    m6WatchGc3Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6WatchGc3Fns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6WatchGc3_sigs :
    m6WatchGc3Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6WatchGc3Fns.map (fun f => (f.name, f.as, f.rs)) := m6WatchGc3_sigs_p
private theorem m6FlushTrail_sigs_p :
    m6FlushTrailRows.map (fun e => (e.name, e.as, e.rs)) =
      m6FlushTrailFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6FlushTrail_sigs :
    m6FlushTrailRows.map (fun e => (e.name, e.as, e.rs)) =
      m6FlushTrailFns.map (fun f => (f.name, f.as, f.rs)) := m6FlushTrail_sigs_p
private theorem m6Reds_sigs_p :
    m6RedsRows.map (fun e => (e.name, e.as, e.rs)) =
      m6RedsFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6Reds_sigs :
    m6RedsRows.map (fun e => (e.name, e.as, e.rs)) =
      m6RedsFns.map (fun f => (f.name, f.as, f.rs)) := m6Reds_sigs_p
private theorem m6Reduce_sigs_p :
    m6ReduceRows.map (fun e => (e.name, e.as, e.rs)) =
      m6ReduceFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6Reduce_sigs :
    m6ReduceRows.map (fun e => (e.name, e.as, e.rs)) =
      m6ReduceFns.map (fun f => (f.name, f.as, f.rs)) := m6Reduce_sigs_p
private theorem m6HdrDecide_sigs_p :
    m6HdrDecideRows.map (fun e => (e.name, e.as, e.rs)) =
      m6HdrDecideFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6HdrDecide_sigs :
    m6HdrDecideRows.map (fun e => (e.name, e.as, e.rs)) =
      m6HdrDecideFns.map (fun f => (f.name, f.as, f.rs)) := m6HdrDecide_sigs_p
private theorem m6CfExtendPush2_sigs_p :
    m6CfExtendPush2Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6CfExtendPush2Fns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6CfExtendPush2_sigs :
    m6CfExtendPush2Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6CfExtendPush2Fns.map (fun f => (f.name, f.as, f.rs)) := m6CfExtendPush2_sigs_p
private theorem m6CfExtendPushCl_sigs_p :
    m6CfExtendPushClRows.map (fun e => (e.name, e.as, e.rs)) =
      m6CfExtendPushClFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6CfExtendPushCl_sigs :
    m6CfExtendPushClRows.map (fun e => (e.name, e.as, e.rs)) =
      m6CfExtendPushClFns.map (fun f => (f.name, f.as, f.rs)) := m6CfExtendPushCl_sigs_p
private theorem m6CfEnterDense_sigs_p :
    m6CfEnterDenseRows.map (fun e => (e.name, e.as, e.rs)) =
      m6CfEnterDenseFns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6CfEnterDense_sigs :
    m6CfEnterDenseRows.map (fun e => (e.name, e.as, e.rs)) =
      m6CfEnterDenseFns.map (fun f => (f.name, f.as, f.rs)) := m6CfEnterDense_sigs_p
private theorem m6CfCompact3_sigs_p :
    m6CfCompact3Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6CfCompact3Fns.map (fun f => (f.name, f.as, f.rs)) := rfl
theorem m6CfCompact3_sigs :
    m6CfCompact3Rows.map (fun e => (e.name, e.as, e.rs)) =
      m6CfCompact3Fns.map (fun f => (f.name, f.as, f.rs)) := m6CfCompact3_sigs_p

private theorem m6DimacsRows_noExit_p : m6DimacsRows.all SpecEntry.noExit = true := rfl
theorem m6DimacsRows_noExit : m6DimacsRows.all SpecEntry.noExit = true := m6DimacsRows_noExit_p
private theorem m6Full1CoreRows_noExit_p : m6Full1CoreRows.all SpecEntry.noExit = true := rfl
theorem m6Full1CoreRows_noExit :
    m6Full1CoreRows.all SpecEntry.noExit = true := m6Full1CoreRows_noExit_p
private theorem m6WatchGc0Rows_noExit_p : m6WatchGc0Rows.all SpecEntry.noExit = true := rfl
theorem m6WatchGc0Rows_noExit :
    m6WatchGc0Rows.all SpecEntry.noExit = true := m6WatchGc0Rows_noExit_p
private theorem m6HeapRows_noExit_p : m6HeapRows.all SpecEntry.noExit = true := rfl
theorem m6HeapRows_noExit : m6HeapRows.all SpecEntry.noExit = true := m6HeapRows_noExit_p
private theorem m6RescaleRows_noExit_p : m6RescaleRows.all SpecEntry.noExit = true := rfl
theorem m6RescaleRows_noExit :
    m6RescaleRows.all SpecEntry.noExit = true := m6RescaleRows_noExit_p
private theorem m6BumpSchedRows_noExit_p : m6BumpSchedRows.all SpecEntry.noExit = true := rfl
theorem m6BumpSchedRows_noExit :
    m6BumpSchedRows.all SpecEntry.noExit = true := m6BumpSchedRows_noExit_p
private theorem m6InitAssignRows_noExit_p : m6InitAssignRows.all SpecEntry.noExit = true := rfl
theorem m6InitAssignRows_noExit :
    m6InitAssignRows.all SpecEntry.noExit = true := m6InitAssignRows_noExit_p
private theorem m6Hdr0Rows_noExit_p : m6Hdr0Rows.all SpecEntry.noExit = true := rfl
theorem m6Hdr0Rows_noExit : m6Hdr0Rows.all SpecEntry.noExit = true := m6Hdr0Rows_noExit_p
private theorem m6ParseHelpersRows_noExit_p : m6ParseHelpersRows.all SpecEntry.noExit = true := rfl
theorem m6ParseHelpersRows_noExit :
    m6ParseHelpersRows.all SpecEntry.noExit = true := m6ParseHelpersRows_noExit_p
private theorem m6PropHelpersRows_noExit_p : m6PropHelpersRows.all SpecEntry.noExit = true := rfl
theorem m6PropHelpersRows_noExit :
    m6PropHelpersRows.all SpecEntry.noExit = true := m6PropHelpersRows_noExit_p
private theorem m6BcpS15Rows_noExit_p : m6BcpS15Rows.all SpecEntry.noExit = true := rfl
theorem m6BcpS15Rows_noExit :
    m6BcpS15Rows.all SpecEntry.noExit = true := m6BcpS15Rows_noExit_p
private theorem m6RecomputeTiersRows_noExit_p :
    m6RecomputeTiersRows.all SpecEntry.noExit = true := rfl
theorem m6RecomputeTiersRows_noExit :
    m6RecomputeTiersRows.all SpecEntry.noExit = true := m6RecomputeTiersRows_noExit_p
private theorem m6WatchGc1Rows_noExit_p : m6WatchGc1Rows.all SpecEntry.noExit = true := rfl
theorem m6WatchGc1Rows_noExit :
    m6WatchGc1Rows.all SpecEntry.noExit = true := m6WatchGc1Rows_noExit_p
private theorem m6WatchGc2Rows_noExit_p : m6WatchGc2Rows.all SpecEntry.noExit = true := rfl
theorem m6WatchGc2Rows_noExit :
    m6WatchGc2Rows.all SpecEntry.noExit = true := m6WatchGc2Rows_noExit_p
private theorem m6SweepBinsM6cfRows_noExit_p :
    m6SweepBinsM6cfRows.all SpecEntry.noExit = true := rfl
theorem m6SweepBinsM6cfRows_noExit :
    m6SweepBinsM6cfRows.all SpecEntry.noExit = true := m6SweepBinsM6cfRows_noExit_p
private theorem m6SweepCopyRows_noExit_p : m6SweepCopyRows.all SpecEntry.noExit = true := rfl
theorem m6SweepCopyRows_noExit :
    m6SweepCopyRows.all SpecEntry.noExit = true := m6SweepCopyRows_noExit_p
private theorem m6WatchGc3Rows_noExit_p : m6WatchGc3Rows.all SpecEntry.noExit = true := rfl
theorem m6WatchGc3Rows_noExit :
    m6WatchGc3Rows.all SpecEntry.noExit = true := m6WatchGc3Rows_noExit_p
private theorem m6FlushTrailRows_noExit_p : m6FlushTrailRows.all SpecEntry.noExit = true := rfl
theorem m6FlushTrailRows_noExit :
    m6FlushTrailRows.all SpecEntry.noExit = true := m6FlushTrailRows_noExit_p
private theorem m6RedsRows_noExit_p : m6RedsRows.all SpecEntry.noExit = true := rfl
theorem m6RedsRows_noExit : m6RedsRows.all SpecEntry.noExit = true := m6RedsRows_noExit_p
private theorem m6ReduceRows_noExit_p : m6ReduceRows.all SpecEntry.noExit = true := rfl
theorem m6ReduceRows_noExit : m6ReduceRows.all SpecEntry.noExit = true := m6ReduceRows_noExit_p
private theorem m6HdrDecideRows_noExit_p : m6HdrDecideRows.all SpecEntry.noExit = true := rfl
theorem m6HdrDecideRows_noExit :
    m6HdrDecideRows.all SpecEntry.noExit = true := m6HdrDecideRows_noExit_p
private theorem m6CfExtendPush2Rows_noExit_p :
    m6CfExtendPush2Rows.all SpecEntry.noExit = true := rfl
theorem m6CfExtendPush2Rows_noExit :
    m6CfExtendPush2Rows.all SpecEntry.noExit = true := m6CfExtendPush2Rows_noExit_p
private theorem m6CfExtendPushClRows_noExit_p :
    m6CfExtendPushClRows.all SpecEntry.noExit = true := rfl
theorem m6CfExtendPushClRows_noExit :
    m6CfExtendPushClRows.all SpecEntry.noExit = true := m6CfExtendPushClRows_noExit_p
private theorem m6CfEnterDenseRows_noExit_p : m6CfEnterDenseRows.all SpecEntry.noExit = true := rfl
theorem m6CfEnterDenseRows_noExit :
    m6CfEnterDenseRows.all SpecEntry.noExit = true := m6CfEnterDenseRows_noExit_p
private theorem m6CfCompact3Rows_noExit_p : m6CfCompact3Rows.all SpecEntry.noExit = true := rfl
theorem m6CfCompact3Rows_noExit :
    m6CfCompact3Rows.all SpecEntry.noExit = true := m6CfCompact3Rows_noExit_p

/-- Public row-membership witnesses for callers outside `FullM6Transport0` (`0` `@[expose]`). -/
private theorem row_kissat_skip_ws_comments_p :
    (⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩ : SpecEntry) ∈
      m6DimacsRows := List.mem_of_getElem? (i := 2) rfl
theorem row_kissat_skip_ws_comments :
    (⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩ : SpecEntry) ∈
      m6DimacsRows := row_kissat_skip_ws_comments_p
private theorem row_kissat_parse_header_p :
    (⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ : SpecEntry) ∈
      m6DimacsRows := List.mem_of_getElem? (i := 5) rfl
theorem row_kissat_parse_header :
    (⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ : SpecEntry) ∈
      m6DimacsRows := row_kissat_parse_header_p
private theorem row_kissat_next_lit_p :
    (⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩ : SpecEntry) ∈
      m6DimacsRows := List.mem_of_getElem? (i := 6) rfl
theorem row_kissat_next_lit :
    (⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩ : SpecEntry) ∈
      m6DimacsRows := row_kissat_next_lit_p
private theorem row_full_isqrt_p :
    (⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_isqrt :
    (⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := row_full_isqrt_p
private theorem row_full_ilog10_p :
    (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := List.mem_of_getElem? (i := 1) rfl
theorem row_full_ilog10 :
    (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := row_full_ilog10_p
private theorem row_full_arena_next_p :
    (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := List.mem_of_getElem? (i := 3) rfl
theorem row_full_arena_next :
    (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := row_full_arena_next_p
private theorem row_full_alloc_cl_p :
    (⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := List.mem_of_getElem? (i := 4) rfl
theorem row_full_alloc_cl :
    (⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := row_full_alloc_cl_p
private theorem row_full_wsort_sift_p :
    (⟨"full_wsort_sift", [i64, i64, i64, i64], [], Full.fullWsortSiftSpec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := List.mem_of_getElem? (i := 5) rfl
theorem row_full_wsort_sift :
    (⟨"full_wsort_sift", [i64, i64, i64, i64], [], Full.fullWsortSiftSpec, true⟩ : SpecEntry) ∈
      m6Full1CoreRows := row_full_wsort_sift_p
private theorem row_full_wstack_defrag_m6_p :
    (⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈
      m6WatchGc0Rows := List.mem_of_getElem? (i := 1) rfl
theorem row_full_wstack_defrag_m6 :
    (⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈
      m6WatchGc0Rows := row_full_wstack_defrag_m6_p
private theorem row_full_watch_push_m6_p :
    (⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈
      m6WatchGc0Rows := List.mem_of_getElem? (i := 2) rfl
theorem row_full_watch_push_m6 :
    (⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈
      m6WatchGc0Rows := row_full_watch_push_m6_p
private theorem row_full_heap_up_p :
    (⟨"full_heap_up", [i64, i32], [], Full.fullHeapUpSpec, true⟩ : SpecEntry) ∈
      m6HeapRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_heap_up :
    (⟨"full_heap_up", [i64, i32], [], Full.fullHeapUpSpec, true⟩ : SpecEntry) ∈
      m6HeapRows := row_full_heap_up_p
private theorem row_full_heap_down_p :
    (⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩ : SpecEntry) ∈
      m6HeapRows := List.mem_of_getElem? (i := 1) rfl
theorem row_full_heap_down :
    (⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩ : SpecEntry) ∈
      m6HeapRows := row_full_heap_down_p
private theorem row_full_heap_push_p :
    (⟨"full_heap_push", [i64, i32], [], Full.fullHeapPushSpec, true⟩ : SpecEntry) ∈
      m6HeapRows := List.mem_of_getElem? (i := 2) rfl
theorem row_full_heap_push :
    (⟨"full_heap_push", [i64, i32], [], Full.fullHeapPushSpec, true⟩ : SpecEntry) ∈
      m6HeapRows := row_full_heap_push_p
private theorem row_full_rescale_p :
    (⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩ : SpecEntry) ∈
      m6RescaleRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_rescale :
    (⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩ : SpecEntry) ∈
      m6RescaleRows := row_full_rescale_p
private theorem row_full_bump_var_p :
    (⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_bump_var :
    (⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := row_full_bump_var_p
private theorem row_full_bump_decay_p :
    (⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := List.mem_of_getElem? (i := 1) rfl
theorem row_full_bump_decay :
    (⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := row_full_bump_decay_p
private theorem row_full_queue_mtf_p :
    (⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := List.mem_of_getElem? (i := 3) rfl
theorem row_full_queue_mtf :
    (⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := row_full_queue_mtf_p
private theorem row_full_log10_q16_p :
    (⟨"full_log10_q16", [i64], [i64], FullM5Sched.m5Log10Q16Spec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := List.mem_of_getElem? (i := 5) rfl
theorem row_full_log10_q16 :
    (⟨"full_log10_q16", [i64], [i64], FullM5Sched.m5Log10Q16Spec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := row_full_log10_q16_p
private theorem row_full_scale_delta_m5_p :
    (⟨"full_scale_delta_m5", [i64, i64], [i64], FullM5Sched.m5ScaleDeltaSpec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := List.mem_of_getElem? (i := 6) rfl
theorem row_full_scale_delta_m5 :
    (⟨"full_scale_delta_m5", [i64, i64], [i64], FullM5Sched.m5ScaleDeltaSpec, true⟩ : SpecEntry) ∈
      m6BumpSchedRows := row_full_scale_delta_m5_p
private theorem row_full_assign_lvl_p :
    (⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_assign_lvl :
    (⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := row_full_assign_lvl_p
private theorem row_full_assign_p :
    (⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := List.mem_of_getElem? (i := 1) rfl
theorem row_full_assign :
    (⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := row_full_assign_p
private theorem row_full_backtrack_p :
    (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := List.mem_of_getElem? (i := 4) rfl
theorem row_full_backtrack :
    (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := row_full_backtrack_p
private theorem row_full_add_clause_p :
    (⟨"full_add_clause", [i64, i32, i32, .bool], [i64], Full.fullAddClauseSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := List.mem_of_getElem? (i := 5) rfl
theorem row_full_add_clause :
    (⟨"full_add_clause", [i64, i32, i32, .bool], [i64], Full.fullAddClauseSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := row_full_add_clause_p
private theorem row_full_init_state_p :
    (⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
      Full.fullInitStateSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := List.mem_of_getElem? (i := 16) rfl
theorem row_full_init_state :
    (⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
      Full.fullInitStateSpec, true⟩ : SpecEntry) ∈
      m6InitAssignRows := row_full_init_state_p
private theorem row_m6_hdr_record_used_p :
    (⟨"m6_hdr_record_used", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩ : SpecEntry) ∈
      m6Hdr0Rows := List.mem_of_getElem? (i := 11) rfl
theorem row_m6_hdr_record_used :
    (⟨"m6_hdr_record_used", [i64, i64], [], FullM6Hdr.m6HdrW2aSpec [i64] [], true⟩ : SpecEntry) ∈
      m6Hdr0Rows := row_m6_hdr_record_used_p
private theorem row_m6_hdr_update_tier_limits_p :
    (⟨"m6_hdr_update_tier_limits", [i64], [], FullM6Hdr.m6HdrW2aSpec [] [], true⟩ : SpecEntry) ∈
      m6Hdr0Rows := List.mem_of_getElem? (i := 10) rfl
theorem row_m6_hdr_update_tier_limits :
    (⟨"m6_hdr_update_tier_limits", [i64], [], FullM6Hdr.m6HdrW2aSpec [] [], true⟩ : SpecEntry) ∈
      m6Hdr0Rows := row_m6_hdr_update_tier_limits_p
private theorem row_m6_hdr_dr_init_p :
    (⟨"m6_hdr_dr_init", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩ : SpecEntry) ∈
      m6Hdr0Rows := List.mem_of_getElem? (i := 21) rfl
theorem row_m6_hdr_dr_init :
    (⟨"m6_hdr_dr_init", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩ : SpecEntry) ∈
      m6Hdr0Rows := row_m6_hdr_dr_init_p
private theorem row_m6_hdr_dr_update_p :
    (⟨"m6_hdr_dr_update", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩ : SpecEntry) ∈
      m6Hdr0Rows := List.mem_of_getElem? (i := 22) rfl
theorem row_m6_hdr_dr_update :
    (⟨"m6_hdr_dr_update", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩ : SpecEntry) ∈
      m6Hdr0Rows := row_m6_hdr_dr_update_p
private theorem row_full_skip_cl_p :
    (⟨"full_skip_cl", [i64, i64], [.bool], Full.fullSkipClSpec, true⟩ : SpecEntry) ∈
      m6ParseHelpersRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_skip_cl :
    (⟨"full_skip_cl", [i64, i64], [.bool], Full.fullSkipClSpec, true⟩ : SpecEntry) ∈
      m6ParseHelpersRows := row_full_skip_cl_p
private theorem row_full_ingest_cl_p :
    (⟨"full_ingest_cl", [i64, i64], [i64], Full.fullIngestClSpec, true⟩ : SpecEntry) ∈
      m6ParseHelpersRows := List.mem_of_getElem? (i := 1) rfl
theorem row_full_ingest_cl :
    (⟨"full_ingest_cl", [i64, i64], [i64], Full.fullIngestClSpec, true⟩ : SpecEntry) ∈
      m6ParseHelpersRows := row_full_ingest_cl_p
private theorem row_full_find_repl_p :
    (⟨"full_find_repl", [i64, i64], [i64], Full.fullFindReplSpec, true⟩ : SpecEntry) ∈
      m6PropHelpersRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_find_repl :
    (⟨"full_find_repl", [i64, i64], [i64], Full.fullFindReplSpec, true⟩ : SpecEntry) ∈
      m6PropHelpersRows := row_full_find_repl_p
private theorem row_full_assign_level_p :
    (⟨"full_assign_level", [i64, i32, i32], [i32], Full.fullAssignLevelSpec, true⟩ : SpecEntry) ∈
      m6PropHelpersRows := List.mem_of_getElem? (i := 1) rfl
theorem row_full_assign_level :
    (⟨"full_assign_level", [i64, i32, i32], [i32], Full.fullAssignLevelSpec, true⟩ : SpecEntry) ∈
      m6PropHelpersRows := row_full_assign_level_p
private theorem row_full_unwatch_large_p :
    (⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ : SpecEntry) ∈
      m6PropHelpersRows := List.mem_of_getElem? (i := 2) rfl
theorem row_full_unwatch_large :
    (⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ : SpecEntry) ∈
      m6PropHelpersRows := row_full_unwatch_large_p
private theorem row_full_recompute_tiers_p :
    (⟨"full_recompute_tiers", [i64], [], Full.fullRecomputeTiersSpec, true⟩ : SpecEntry) ∈
      m6RecomputeTiersRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_recompute_tiers :
    (⟨"full_recompute_tiers", [i64], [], Full.fullRecomputeTiersSpec, true⟩ : SpecEntry) ∈
      m6RecomputeTiersRows := row_full_recompute_tiers_p
private theorem row_full_lit_rank_m6_p :
    (⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩ : SpecEntry) ∈
      m6WatchGc1Rows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_lit_rank_m6 :
    (⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩ : SpecEntry) ∈
      m6WatchGc1Rows := row_full_lit_rank_m6_p
private theorem row_full_sweep_bins_range_m6_p :
    (⟨"full_sweep_bins_range_m6", [i64, i64], [],
      FullM6WatchGc.fullSweepBinsRangeSpec, true⟩ : SpecEntry) ∈
      m6WatchGc1Rows := List.mem_of_getElem? (i := 1) rfl
theorem row_full_sweep_bins_range_m6 :
    (⟨"full_sweep_bins_range_m6", [i64, i64], [],
      FullM6WatchGc.fullSweepBinsRangeSpec, true⟩ : SpecEntry) ∈
      m6WatchGc1Rows := row_full_sweep_bins_range_m6_p
private theorem row_full_rewatch_range_m6_p :
    (⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool],
      FullM6WatchGc.fullRewatchRangeSpec, true⟩ : SpecEntry) ∈
      m6WatchGc2Rows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_rewatch_range_m6 :
    (⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool],
      FullM6WatchGc.fullRewatchRangeSpec, true⟩ : SpecEntry) ∈
      m6WatchGc2Rows := row_full_rewatch_range_m6_p
private theorem row_full_sweep_copy_p :
    (⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64],
      Full.fullSweepCopySpec, true⟩ : SpecEntry) ∈
      m6SweepCopyRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_sweep_copy :
    (⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64],
      Full.fullSweepCopySpec, true⟩ : SpecEntry) ∈
      m6SweepCopyRows := row_full_sweep_copy_p
private theorem row_full_move_red_end_m6_p :
    (⟨"full_move_red_end_m6", [i64, i64, i64], [],
      FullM6WatchGc.fullMoveRedEndSpec, true⟩ : SpecEntry) ∈
      m6WatchGc3Rows := List.mem_of_getElem? (i := 2) rfl
theorem row_full_move_red_end_m6 :
    (⟨"full_move_red_end_m6", [i64, i64, i64], [],
      FullM6WatchGc.fullMoveRedEndSpec, true⟩ : SpecEntry) ∈
      m6WatchGc3Rows := row_full_move_red_end_m6_p
private theorem row_full_arena_sweep_m6_p :
    (⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈
      m6WatchGc3Rows := List.mem_of_getElem? (i := 3) rfl
theorem row_full_arena_sweep_m6 :
    (⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈
      m6WatchGc3Rows := row_full_arena_sweep_m6_p
private theorem row_full_flush_trail_p :
    (⟨"full_flush_trail", [i64], [i64], FullM6CompactFlush.fullFlushTrailSpec, true⟩ : SpecEntry) ∈
      m6FlushTrailRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_flush_trail :
    (⟨"full_flush_trail", [i64], [i64], FullM6CompactFlush.fullFlushTrailSpec, true⟩ : SpecEntry) ∈
      m6FlushTrailRows := row_full_flush_trail_p
private theorem row_full_sort_reds_p :
    (⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩ : SpecEntry) ∈
      m6RedsRows := List.mem_of_getElem? (i := 2) rfl
theorem row_full_sort_reds :
    (⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩ : SpecEntry) ∈
      m6RedsRows := row_full_sort_reds_p
private theorem row_full_extend_push2_p :
    (⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ : SpecEntry) ∈
      m6CfExtendPush2Rows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_extend_push2 :
    (⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ : SpecEntry) ∈
      m6CfExtendPush2Rows := row_full_extend_push2_p
private theorem row_full_extend_push_cl_p :
    (⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ : SpecEntry) ∈
      m6CfExtendPushClRows := List.mem_of_getElem? (i := 0) rfl
theorem row_full_extend_push_cl :
    (⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ : SpecEntry) ∈
      m6CfExtendPushClRows := row_full_extend_push_cl_p

/-! ## 4. Kept `Dimacs` & `Full1..5/M4` Prefix Segment Transports -/

/-- `Dimacs` (`8` fns): zero external callees. -/
theorem m6Dimacs_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6DimacsRows, e ∈ tbl) :
    AllFns Fn.Wf m6DimacsFns ∧ TableImpl (Env.ofTable tbl) m6DimacsFns m6DimacsRows :=
  fullSliceTransport 0 8 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd hown
    (fun _ h => nomatch h)

/-- `Full1` core utilities (`6` fns): zero external callees. -/
theorem m6Full1Core_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6Full1CoreRows, e ∈ tbl) :
    AllFns Fn.Wf m6Full1CoreFns ∧
    TableImpl (Env.ofTable tbl) m6Full1CoreFns m6Full1CoreRows :=
  fullSliceTransport 8 6 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd hown
    (fun _ h => nomatch h)

/-- `Full1` VSIDS heap ops (`4` fns): zero external callees. -/
theorem m6Heap_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6HeapRows, e ∈ tbl) :
    AllFns Fn.Wf m6HeapFns ∧ TableImpl (Env.ofTable tbl) m6HeapFns m6HeapRows :=
  fullSliceTransport 16 4 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd hown
    (fun _ h => nomatch h)

/-- `Full1` `full_rescale` (`1` fn): zero external callees. -/
theorem m6Rescale_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6RescaleRows, e ∈ tbl) :
    AllFns Fn.Wf m6RescaleFns ∧ TableImpl (Env.ofTable tbl) m6RescaleFns m6RescaleRows :=
  fullSliceTransport 20 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd hown
    (fun _ h => nomatch h)

private theorem m3_tick_zip_p :
    ∀ p ∈ List.zip [FullM3VivChrono.m3TickRelFn]
        [⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩],
      p.1 ∈ FullM3VivChrono.m3Module.fns ∧
      p.2 ∈ FullM3VivChrono.m3SpecTable ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
  intro p hp
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
  subst hp
  exact ⟨List.mem_of_getElem? (i := 0) (by rfl),
    List.mem_of_getElem? (i := 0) (by rfl), rfl, rfl, rfl⟩

private theorem m5Sched3_len_p :
    (FullM5Sched.m5Sched_fns.take 3).length = (FullM5Sched.m5SchedSpecTable.take 3).length := rfl

private theorem m5Sched3_zip_p :
    ∀ p ∈ List.zip (FullM5Sched.m5Sched_fns.take 3) (FullM5Sched.m5SchedSpecTable.take 3),
      p.1 ∈ FullM5Sched.m5SchedModule.fns ∧ p.2 ∈ FullM5Sched.m5SchedSpecTable ∧
      p.2.name = p.1.name ∧ p.2.as = p.1.as ∧ p.2.rs = p.1.rs := by
  have hz := modSub_drop_take (M1 := FullM5Sched.m5SchedModule)
    (t1 := FullM5Sched.m5SchedSpecTable.take 6) rfl (off := 0) (n := 3)
  have hdt : (FullM5Sched.m5SchedModule.fns.drop 0).take 3 =
      FullM5Sched.m5Sched_fns.take 3 := rfl
  have hst : ((FullM5Sched.m5SchedSpecTable.take 6).drop 0).take 3 =
      FullM5Sched.m5SchedSpecTable.take 3 := by
    rw [List.drop_zero, List.take_take]; rfl
  intro p hp
  rw [← hdt, ← hst] at hp
  obtain ⟨h1, h2, hn, ha, hrs⟩ := hz.2 p hp
  exact ⟨h1, List.mem_of_mem_take h2, hn, ha, hrs⟩

private theorem m5SchedSpecTable_nodup :
    (FullM5Sched.m5SchedSpecTable.map SpecEntry.name).Nodup := by
  decide

/-- `M4Bump`, `Full[22..24]`, `FullM3VivChrono.full_tick_rel`, `M5Sched[0..2]` (`8` fns). -/
theorem m6BumpSched_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BumpSchedRows, e ∈ tbl)
    (hUp : (⟨"full_heap_up", [i64, i32], [], Full.fullHeapUpSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRes : (⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6BumpSchedFns ∧
    TableImpl (Env.ofTable tbl) m6BumpSchedFns m6BumpSchedRows := by
  have h1 : SpecEntry.Impl (Env.ofTable tbl) FullM4Bump.m4BumpVarFn
      ⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ :=
    SpecEntry.Impl.of (FullM4Bump.full_bump_var_m4_wp (Env.ofTable tbl)
      (envRow_mem hnd "full_heap_up" [i64, i32] [] Full.fullHeapUpSpec hUp)
      (envRow_mem hnd "full_rescale" [i64] [] Full.fullRescaleSpec hRes))
  have h2 := fullSliceTransport 22 3 [⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩]
    (by t_kernel_rfl) (fun e he => by
      simp only [List.mem_singleton] at he; subst he; exact fullRow_at 20 _)
    hnd (fun _ h => hown _ (List.mem_append_right _ (List.mem_append_left _ h)))
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact hRes)
  have h3 := modSubTransport FullM3VivChrono.m3_moduleOk FullM3VivChrono.m3SpecTable_nodup
    (fs := [FullM3VivChrono.m3TickRelFn])
    (sub_tbl := [⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩])
    (extRows := [])
    rfl m3_tick_zip_p
    (all_mem_of_bool (by t_kernel_rfl)) (fun _ h => nomatch h) hnd
    (fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact hown _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ List.mem_cons_self))))
    (fun _ h => nomatch h)
  have h4 := modSubTransport FullM5Sched.m5Sched_moduleOk m5SchedSpecTable_nodup
    (extRows := []) m5Sched3_len_p m5Sched3_zip_p
    (all_mem_of_bool (by t_kernel_rfl)) (fun _ h => nomatch h) hnd
    (fun _ h => hown _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ h)))) (fun _ h => nomatch h)
  have hwf : AllFns Fn.Wf m6BumpSchedFns :=
    allFns_append ⟨FullM4Bump.full_bump_var_m4_wf, trivial⟩
      (allFns_append h2.1 (allFns_append h3.1 h4.1))
  have htbl : TableImpl (Env.ofTable tbl) m6BumpSchedFns m6BumpSchedRows :=
    tableImpl_append rfl ⟨h1, trivial⟩
      (tableImpl_append rfl h2.2 (tableImpl_append rfl h3.2 h4.2))
  exact ⟨hwf, htbl⟩

private theorem m6InitAssignRows_mem_p (i : Nat) (e : SpecEntry) :
    m6InitAssignRows[i]? = some e → e ∈ m6InitAssignRows :=
  fun h => List.mem_of_getElem? h

/-- `17` fns: `Full[27..28]`, `M5HeurCore` save/bt, `Full[31..35]`, `fast_init_hdr`,
`Full[37,40]`, `M5Orch` caps + `init_state_m5`, `M5.full_init_state`. -/
theorem m6InitAssign_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6InitAssignRows, e ∈ tbl)
    (hHdr : (⟨"kissat_parse_header", [i64, i64, i64], [.bool],
      kissatParseHeaderSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAlloc : (⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64],
      Full.fullAllocClSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPush : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl)
    (hHeapPush : (⟨"full_heap_push", [i64, i32], [],
      Full.fullHeapPushSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6InitAssignFns ∧
    TableImpl (Env.ofTable tbl) m6InitAssignFns m6InitAssignRows := by
  have hm : ∀ (i : Nat) (e : SpecEntry), m6InitAssignRows[i]? = some e → e ∈ tbl :=
    fun i e h => hown e (m6InitAssignRows_mem_p i e h)
  have hs0 := fullSliceTransport 27 2 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd
    (fun _ h => hown _ (List.mem_append_left _ h)) (fun _ h => nomatch h)
  have hSave : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5SaveTargetBestFn
      ⟨"full_save_target_best", [i64], [], Full.fullSaveTargetBestSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_save_target_best_m5_wp (Env.ofTable tbl))
  have hBtRaw : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5BacktrackRawFn
      ⟨"full_backtrack_raw_m5", [i64, i64], [], FullM5HeurCore.fullBacktrackRawSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_backtrack_raw_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 2 _ (by rfl)))
      (envRow_mem hnd _ _ _ _ hHeapPush))
  have hBt : SpecEntry.Impl (Env.ofTable tbl) FullM5HeurCore.m5BacktrackFn
      ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5HeurCore.full_backtrack_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 3 _ (by rfl)))
      (envRow_mem hnd _ _ _ _ (hm 2 _ (by rfl))))
  have hs1 := fullSliceTransport 31 5
    [ ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩
    , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩ ]
    (by t_kernel_rfl)
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact fullRow_at 12 _
      · exact fullRow_at 15 _)
    hnd (fun _ h => hown _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ h))))
    (fun _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> assumption)
  have hInitHdr : TableImpl (Env.ofTable tbl)
      (FullFastBveBudgets.fastBveBudgets_fns.take 1)
      [⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩] := by
    have heq : FullFastBveBudgets.fastBveBudgets_fns.take 1 =
        [⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.full_init_hdr_body⟩] := rfl
    rw [heq]
    exact ⟨SpecEntry.Impl.of (FullFastBveBudgets.fast_init_hdr_canon_wp (Env.ofTable tbl)),
      trivial⟩
  have hs2 := fullSliceTransport 37 1
    [⟨"full_fixed_bytes", [i64], [i64], Full.fullFixedBytesSpec, true⟩]
    (by t_kernel_rfl)
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact fullRow_at 34 _)
    hnd (fun _ h => hown _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))))))
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact hm 8 _ (by rfl))
  have hCaps : TableImpl (Env.ofTable tbl) (FullM5Orch.m5Orch_fns.take 2)
      [ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.fullCalcExtCapM5Spec, true⟩
      , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.fullCalcScrCapM5Spec, true⟩ ] := by
    have heq : FullM5Orch.m5Orch_fns.take 2 =
        [ ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.full_calc_ext_cap_m5_body⟩
        , ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.full_calc_scr_cap_m5_body⟩ ] := rfl
    rw [heq]
    exact ⟨SpecEntry.Impl.of (FullM5Orch.full_calc_ext_cap_m5_wp (Env.ofTable tbl)),
      SpecEntry.Impl.of (FullM5Orch.full_calc_scr_cap_m5_wp (Env.ofTable tbl)), trivial⟩
  have hs3 := fullSliceTransport 40 1
    [⟨"full_init_ptrs", [i64, i64, i64], [], Full.fullInitPtrsSpec, true⟩]
    (by t_kernel_rfl)
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact fullRow_at 35 _)
    hnd (fun _ h => hown _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ h))))))))
    (fun _ h => by simp only [List.mem_singleton] at h; subst h; exact hm 9 _ (by rfl))
  have hInitStM5 : TableImpl (Env.ofTable tbl) ((FullM5Orch.m5Orch_fns.drop 2).take 1)
      [⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
        Full.fullInitStateSpec, true⟩] := by
    have heq : (FullM5Orch.m5Orch_fns.drop 2).take 1 =
        [⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
          FullM5Orch.full_init_state_m5_body⟩] := rfl
    rw [heq]
    refine ⟨SpecEntry.Impl.of (FullM5Orch.full_init_state_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hHdr) (envRow_mem hnd _ _ _ _ (hm 8 _ (by rfl)))
      (envRow_mem hnd _ _ _ _ (hm 11 _ (by rfl)))
      (envRow_mem hnd _ _ _ _ (hm 12 _ (by rfl)) FullM5Orch.fullCalcExtCapM5Spec_noExit)
      (envRow_mem hnd _ _ _ _ (hm 13 _ (by rfl)) FullM5Orch.fullCalcScrCapM5Spec_noExit)
      (envRow_mem hnd _ _ _ _ (hm 14 _ (by rfl)))
      (envRow_mem hnd _ _ _ _ (hm 10 _ (by rfl))) (envRow_mem hnd _ _ _ _ (hm 6 _ (by rfl)))
      (envRow_mem hnd _ _ _ _ (hm 7 _ (by rfl)))), trivial⟩
  have hInitSt : SpecEntry.Impl (Env.ofTable tbl) FullM5.m5InitStateFwdFn
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], Full.fullInitStateSpec, true⟩ :=
    SpecEntry.Impl.of (FullM5.m5_init_state_fwd_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ (hm 15 _ (by rfl))))
  have hwf_heur : AllFns Fn.Wf
      [ FullM5HeurCore.m5SaveTargetBestFn
      , FullM5HeurCore.m5BacktrackRawFn
      , FullM5HeurCore.m5BacktrackFn ] :=
    ⟨FullM5HeurCore.full_save_target_best_m5_wf,
      FullM5HeurCore.full_backtrack_raw_m5_wf,
      FullM5HeurCore.full_backtrack_m5_wf, trivial⟩
  have hwf_hdr : AllFns Fn.Wf (FullFastBveBudgets.fastBveBudgets_fns.take 1) := by
    change AllFns Fn.Wf [⟨"full_init_hdr", _, _, FullFastBveBudgets.full_init_hdr_body⟩]
    exact ⟨FullFastBveBudgets.full_init_hdr_wf, trivial⟩
  have hwf_caps : AllFns Fn.Wf (FullM5Orch.m5Orch_fns.take 2) := by
    change AllFns Fn.Wf
      [ ⟨"full_calc_ext_cap_m5", _, _, FullM5Orch.full_calc_ext_cap_m5_body⟩
      , ⟨"full_calc_scr_cap_m5", _, _, FullM5Orch.full_calc_scr_cap_m5_body⟩ ]
    exact ⟨FullM5Orch.full_calc_ext_cap_m5_wf, FullM5Orch.full_calc_scr_cap_m5_wf, trivial⟩
  have hwf_st5 : AllFns Fn.Wf ((FullM5Orch.m5Orch_fns.drop 2).take 1) := by
    change AllFns Fn.Wf [⟨"full_init_state_m5", _, _, FullM5Orch.full_init_state_m5_body⟩]
    exact ⟨FullM5Orch.full_init_state_m5_wf, trivial⟩
  have hwf : AllFns Fn.Wf m6InitAssignFns :=
    allFns_append hs0.1 (allFns_append hwf_heur (allFns_append hs1.1 (allFns_append hwf_hdr
      (allFns_append hs2.1 (allFns_append hwf_caps (allFns_append hs3.1
        (allFns_append hwf_st5 ⟨FullM5.full_init_state_wf, trivial⟩)))))))
  have htbl : TableImpl (Env.ofTable tbl) m6InitAssignFns m6InitAssignRows :=
    tableImpl_append rfl hs0.2 (tableImpl_append rfl ⟨hSave, hBtRaw, hBt, trivial⟩
      (tableImpl_append rfl hs1.2 (tableImpl_append rfl hInitHdr
        (tableImpl_append rfl hs2.2 (tableImpl_append rfl hCaps
          (tableImpl_append rfl hs3.2 (tableImpl_append rfl hInitStM5 ⟨hInitSt, trivial⟩)))))))
  exact ⟨hwf, htbl⟩

/-- `2` fns: `full_skip_cl`, `full_ingest_cl` (`Full[42..43]`). -/
theorem m6ParseHelpers_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6ParseHelpersRows, e ∈ tbl)
    (hNext : (⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAsgn : (⟨"full_assign_lvl", [i64, i32, i32, i32], [],
      Full.fullAssignLvlSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAddCl : (⟨"full_add_clause", [i64, i32, i32, .bool], [i64],
      Full.fullAddClauseSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6ParseHelpersFns ∧
    TableImpl (Env.ofTable tbl) m6ParseHelpersFns m6ParseHelpersRows := by
  refine fullSliceTransport 42 2
    [ ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
    , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
    , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], Full.fullAddClauseSpec, true⟩ ]
    (by t_kernel_rfl) ?_ hnd hown ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact fullRow_at 6 _
    · exact fullRow_at 27 _
    · exact fullRow_at 31 _
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> assumption

/-- `3` fns: `full_find_repl`, `full_assign_level`, `full_unwatch_large`. -/
theorem m6PropHelpers_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6PropHelpersRows, e ∈ tbl) :
    AllFns Fn.Wf m6PropHelpersFns ∧
    TableImpl (Env.ofTable tbl) m6PropHelpersFns m6PropHelpersRows := by
  have hs := fullSliceTransport 45 2 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd
    (fun _ h => hown _ (List.mem_append_left _ h)) (fun _ h => nomatch h)
  have hu : AllFns Fn.Wf (FullM5Otfs.m5Otfs_fns.take 1) ∧
      TableImpl (Env.ofTable tbl) (FullM5Otfs.m5Otfs_fns.take 1)
        [⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩] := by
    have heq : FullM5Otfs.m5Otfs_fns.take 1 =
        [⟨"full_unwatch_large", [i64, i32, i32], [], FullM5Otfs.full_unwatch_large_body⟩] := rfl
    rw [heq]
    exact ⟨⟨FullM5Otfs.full_unwatch_large_wf, trivial⟩,
      ⟨SpecEntry.Impl.of (FullM5Otfs.full_unwatch_large_wp (Env.ofTable tbl)), trivial⟩⟩
  exact ⟨allFns_append hs.1 hu.1, tableImpl_append rfl hs.2 hu.2⟩

/-- `1` fn: `full_recompute_tiers` (`Full[50]`): zero external callees. -/
theorem m6RecomputeTiers_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6RecomputeTiersRows, e ∈ tbl) :
    AllFns Fn.Wf m6RecomputeTiersFns ∧
    TableImpl (Env.ofTable tbl) m6RecomputeTiersFns m6RecomputeTiersRows :=
  fullSliceTransport 50 1 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd hown
    (fun _ h => nomatch h)

/-- `1` fn: `full_sweep_copy` (`Full[58]`): calls `full_watch_push`, `full_assign_lvl`. -/
theorem m6SweepCopy_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6SweepCopyRows, e ∈ tbl)
    (hPush : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAsgn : (⟨"full_assign_lvl", [i64, i32, i32, i32], [],
      Full.fullAssignLvlSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6SweepCopyFns ∧
    TableImpl (Env.ofTable tbl) m6SweepCopyFns m6SweepCopyRows := by
  refine fullSliceTransport 58 1
    [ ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
    , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ ]
    (by t_kernel_rfl) ?_ hnd hown ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact fullRow_at 15 _
    · exact fullRow_at 27 _
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> assumption

/-- `3` fns: `full_red_less`, `full_red_sift`, `full_sort_reds` (`Full[52..54]`). -/
theorem m6Reds_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6RedsRows, e ∈ tbl) :
    AllFns Fn.Wf m6RedsFns ∧ TableImpl (Env.ofTable tbl) m6RedsFns m6RedsRows :=
  fullSliceTransport 52 3 [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd hown
    (fun _ h => nomatch h)

/-- `1` fn: canonical `"full_reduce"` backed by `FullM5Orch.full_reduce_m5_body`. -/
theorem m6Reduce_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hIsqrt : (⟨"full_isqrt", [i64], [i64], Full.fullIsqrtSpec, true⟩ : SpecEntry) ∈ tbl)
    (hIlog : (⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ : SpecEntry) ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32],
      Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRec : (⟨"full_recompute_tiers", [i64], [],
      Full.fullRecomputeTiersSpec, true⟩ : SpecEntry) ∈ tbl)
    (hMrk : (⟨"full_mark_reasons", [i64, .bool], [],
      Full.fullMarkReasonsSpec, true⟩ : SpecEntry) ∈ tbl)
    (hSort : (⟨"full_sort_reds", [i64, i64], [], Full.fullSortRedsSpec, true⟩ : SpecEntry) ∈ tbl)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl)
    (hSweep : (⟨"full_arena_sweep", [i64], [i64],
      Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6ReduceFns ∧ TableImpl (Env.ofTable tbl) m6ReduceFns m6ReduceRows :=
  ⟨⟨FullM5Orch.full_reduce_m5_wf, trivial⟩,
    ⟨SpecEntry.Impl.of (FullM5Orch.full_reduce_m5_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hIsqrt) (envRow_mem hnd _ _ _ _ hIlog)
      (envRow_mem hnd _ _ _ _ hNext) (envRow_mem hnd _ _ _ _ hRec)
      (envRow_mem hnd _ _ _ _ hMrk) (envRow_mem hnd _ _ _ _ hSort)
      (envRow_mem hnd _ _ _ _ hBt) (envRow_mem hnd _ _ _ _ hProp)
      (envRow_mem hnd _ _ _ _ hSweep)), trivial⟩⟩

/-! ## 5. `FullM6Hdr[0..23]` & `[24]` (`m6_hdr_decide`) Transports -/

private theorem m6Hdr0Fns_eq :
    m6Hdr0Fns =
      [ ⟨"full_m6_hdr_sizeof", [], [i64], FullM6Hdr.full_m6_hdr_sizeof_body⟩
      , ⟨"full_m6_ext_sizeof", [], [i64], FullM6Hdr.full_m6_ext_sizeof_body⟩
      , ⟨"m6_hdr_init", [i64], [], FullM6Hdr.m6_hdr_init_body⟩
      , ⟨"m6_hdr_reset", [i64], [], FullM6Hdr.m6_hdr_reset_body⟩
      , ⟨"m6_ext_ensure_init", [i64], [], FullM6Hdr.m6_ext_ensure_init_body⟩
      , ⟨"m6_hdr_ext_ready", [i64], [.bool], FullM6Hdr.m6_hdr_ext_ready_body⟩
      , ⟨"full_m6_mem_init", [i64, i64, i64, i64, i64], [i64], FullM6Hdr.full_m6_mem_init_body⟩
      , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], FullM6Hdr.m6_hdr_sync_legacy_tiers_body⟩
      , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], FullM6Hdr.m6_hdr_recompute_tiers_mode_body⟩
      , ⟨"m6_hdr_recompute_tiers", [i64], [], FullM6Hdr.m6_hdr_recompute_tiers_body⟩
      , ⟨"m6_hdr_update_tier_limits", [i64], [], FullM6Hdr.m6_hdr_update_tier_limits_body⟩
      , ⟨"m6_hdr_record_used", [i64, i64], [], FullM6Hdr.m6_hdr_record_used_body⟩
      , ⟨"m6_hdr_get_tier1", [i64, .bool], [i64], FullM6Hdr.m6_hdr_get_tier1_body⟩
      , ⟨"m6_hdr_get_tier2", [i64, .bool], [i64], FullM6Hdr.m6_hdr_get_tier2_body⟩
      , ⟨"m6_hdr_delaying", [i64, i64], [.bool], FullM6Hdr.m6_hdr_delaying_body⟩
      , ⟨"m6_hdr_bump_delay", [i64, i64], [], FullM6Hdr.m6_hdr_bump_delay_body⟩
      , ⟨"m6_hdr_reduce_delay", [i64, i64], [], FullM6Hdr.m6_hdr_reduce_delay_body⟩
      , ⟨"m6_hdr_reset_delay", [i64, i64], [], FullM6Hdr.m6_hdr_reset_delay_body⟩
      , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], FullM6Hdr.m6_hdr_get_watermark_body⟩
      , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], FullM6Hdr.m6_hdr_set_watermark_body⟩
      , ⟨"m6_hdr_add_ticks", [i64, i64], [], FullM6Hdr.m6_hdr_add_ticks_body⟩
      , ⟨"m6_hdr_dr_init", [i64], [], FullM6Hdr.m6_hdr_dr_init_body⟩
      , ⟨"m6_hdr_dr_update", [i64], [], FullM6Hdr.m6_hdr_dr_update_body⟩
      , ⟨"m6_hdr_dr_allow", [i64], [.bool], FullM6Hdr.m6_hdr_dr_allow_body⟩ ] := rfl

private theorem m6Hdr0Rows_mem_p (i : Nat) (e : SpecEntry) :
    m6Hdr0Rows[i]? = some e → e ∈ m6Hdr0Rows :=
  fun h => List.mem_of_getElem? h

/-- `FullM6Hdr[0..23]` (`24` fns): only external callee is `full_init_state`. -/
theorem m6Hdr0_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6Hdr0Rows, e ∈ tbl)
    (hInitSt : (⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
      Full.fullInitStateSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6Hdr0Fns ∧ TableImpl (Env.ofTable tbl) m6Hdr0Fns m6Hdr0Rows := by
  have hwf : AllFns Fn.Wf m6Hdr0Fns := by
    have h0 : AllFns Fn.Wf ((FullM6Hdr.m6Hdr_fns.drop 0).take 24) :=
      allFns_drop_take_wf FullM6Hdr.m6Hdr_fns_wf 0 24
    simpa [m6Hdr0Fns, FullM6Hdr.m6HdrModule] using h0
  have hm : ∀ (i : Nat) (e : SpecEntry), m6Hdr0Rows[i]? = some e → e ∈ tbl :=
    fun i e h => hown e (m6Hdr0Rows_mem_p i e h)
  have h_init := envRow_mem hnd _ _ _ _ (hm 2 _ (by rfl))
    (fun _ _ _ _ h => FullM6Hdr.m6HdrInitSpec_monoX h)
  have h_ens := envRow_mem hnd _ _ _ _ (hm 4 _ (by rfl))
    (fun _ _ _ _ h => FullM6Hdr.m6ExtEnsureInitSpec_monoX h)
  have h_sync := envRow_mem hnd _ _ _ _ (hm 7 _ (by rfl))
    (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  have h_mode := envRow_mem hnd _ _ _ _ (hm 8 _ (by rfl))
    (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  have h_rec := envRow_mem hnd _ _ _ _ (hm 9 _ (by rfl))
    (fun _ _ _ _ h => FullM6Hdr.m6HdrW2aSpec_monoX h)
  have h_dr := envRow_mem hnd _ _ _ _ (hm 21 _ (by rfl))
    (fun _ _ _ _ h => FullM6Hdr.m6HdrDrMutSpec_monoX h)
  have h_ist := envRow_mem hnd _ _ _ _ hInitSt
  refine ⟨hwf, ?_⟩
  rw [m6Hdr0Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6Hdr.full_m6_hdr_sizeof_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6Hdr.full_m6_ext_sizeof_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_init_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_reset_wp (Env.ofTable tbl) h_init)
    , SpecEntry.Impl.of (FullM6Hdr.m6_ext_ensure_init_wp (Env.ofTable tbl) h_init)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_ext_ready_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.full_m6_mem_init_wp (Env.ofTable tbl) h_ist h_init)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_sync_legacy_tiers_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_recompute_tiers_mode_wp (Env.ofTable tbl) h_ens h_sync)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_recompute_tiers_wp (Env.ofTable tbl) h_mode)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_update_tier_limits_wp (Env.ofTable tbl) h_ens h_rec)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_record_used_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_get_tier1_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_get_tier2_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_delaying_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_bump_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_reduce_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_reset_delay_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_get_watermark_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_set_watermark_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_add_ticks_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_dr_init_wp (Env.ofTable tbl) h_ens)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_dr_update_wp (Env.ofTable tbl) h_dr)
    , SpecEntry.Impl.of (FullM6Hdr.m6_hdr_dr_allow_wp (Env.ofTable tbl) h_ens)
    , trivial ⟩

private theorem m6HdrDecideFns_eq :
    m6HdrDecideFns = [⟨"m6_hdr_decide", [i64], [i64], FullM6Hdr.m6_hdr_decide_body⟩] := rfl

/-- `FullM6Hdr[24]` (`m6_hdr_decide`, `1` fn): calls `m6_hdr_dr_init`, `full_next_dec_var`,
and `full_assign`. -/
theorem m6HdrDecide_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hDrInit : (⟨"m6_hdr_dr_init", [i64], [], FullM6Hdr.m6HdrDrMutSpec, true⟩ : SpecEntry) ∈ tbl)
    (hNextDec : (⟨"full_next_dec_var", [i64], [i64],
      Full.fullNextDecVarSpec, true⟩ : SpecEntry) ∈ tbl)
    (hAssign : (⟨"full_assign", [i64, i32, i32], [],
      Full.fullAssignSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6HdrDecideFns ∧
    TableImpl (Env.ofTable tbl) m6HdrDecideFns m6HdrDecideRows := by
  rw [m6HdrDecideFns_eq]
  exact ⟨⟨FullM6Hdr.m6_hdr_decide_wf, trivial⟩,
    ⟨SpecEntry.Impl.of (FullM6Hdr.m6_hdr_decide_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hNextDec) (envRow_mem hnd _ _ _ _ hAssign)
      (envRow_mem hnd _ _ _ _ hDrInit
        (fun _ _ _ _ h => FullM6Hdr.m6HdrDrMutSpec_monoX h))), trivial⟩⟩

/-! ## 6. `FullM6BcpS15` (`4` fns) Transport -/

private theorem m6BcpS15SpecTable_nodup :
    (FullM6BcpS15.m6BcpS15SpecTable.map SpecEntry.name).Nodup := by
  decide

private theorem m6BcpS15Rows_len_p : m6BcpS15Fns.length = m6BcpS15Rows.length := rfl

/-- `FullM6BcpS15` (`4` fns): only external callee is `full_watch_push`. -/
theorem m6BcpS15_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BcpS15Rows, e ∈ tbl)
    (hPush : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6BcpS15Fns ∧ TableImpl (Env.ofTable tbl) m6BcpS15Fns m6BcpS15Rows := by
  refine tableImpl_transport_of_callsOk
    FullM6BcpS15.m6BcpS15_moduleOk m6BcpS15SpecTable_nodup hnd
    (allowed := (m6BcpS15Rows ++
      [(⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
        Full.fullWatchPushSpec, true⟩ : SpecEntry)]).map
      fun (e : SpecEntry) => (e.name, e.as, e.rs))
    (exits := [])
    m6BcpS15Rows_len_p ?_ (all_mem_of_bool (by t_kernel_rfl)) ?_
  · intro p hp
    simp only [m6BcpS15Fns, m6BcpS15Rows, FullM6BcpS15.m6BcpS15_fns,
      FullM6BcpS15.m6BcpS15SpecTable, List.take_succ_cons, List.take_zero,
      List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, hown _ ?_, rfl, rfl, rfl⟩ <;>
      first
      | exact List.mem_of_getElem? (i := 0) rfl
      | exact List.mem_of_getElem? (i := 1) rfl
      | exact List.mem_of_getElem? (i := 2) rfl
      | exact List.mem_of_getElem? (i := 3) rfl
  · intro s hs
    rcases List.mem_map.mp hs with ⟨e, he, rfl⟩
    rcases List.mem_append.mp he with h | h
    · refine ⟨e, ?_, hown e h, rfl⟩
      have hsub : ∀ x ∈ FullM6BcpS15.m6BcpS15SpecTable.take 4,
          x ∈ FullM6BcpS15.m6BcpS15SpecTable := fun _ hx => List.mem_of_mem_take hx
      exact hsub e h
    · have he_eq : e = ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
          Full.fullWatchPushSpec, true⟩ := by simpa using h
      rw [he_eq]
      exact ⟨_, List.mem_of_getElem? (i := 4) rfl, hPush, rfl⟩

/-! ## 7. `FullM6CompactFlush` (`8` fns, `Tmk` `extend_push*` + `flush_trail` +
  `sweep_bins_m6cf` + `enter_dense` + `compact_*`) Transports -/

private theorem m6SweepBinsM6cfFns_eq :
    m6SweepBinsM6cfFns =
      [⟨"full_sweep_bins_m6cf", [i64], [], FullM6CompactFlush.full_sweep_bins_m6cf_body⟩] := rfl

/-- `full_sweep_bins_m6cf` (`1` fn): calls `full_wstack_defrag`. -/
theorem m6SweepBinsM6cf_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hDefrag : (⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈
      tbl) :
    AllFns Fn.Wf m6SweepBinsM6cfFns ∧
    TableImpl (Env.ofTable tbl) m6SweepBinsM6cfFns m6SweepBinsM6cfRows := by
  rw [m6SweepBinsM6cfFns_eq]
  exact ⟨⟨FullM6CompactFlush.full_sweep_bins_m6cf_wf, trivial⟩,
    ⟨SpecEntry.Impl.of (FullM6CompactFlush.full_sweep_bins_m6cf_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hDefrag)), trivial⟩⟩

/-- `full_flush_trail` (`1` fn): calls `full_backtrack`, `full_propagate`. -/
theorem m6FlushTrail_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hProp : (⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6FlushTrailFns ∧
    TableImpl (Env.ofTable tbl) m6FlushTrailFns m6FlushTrailRows :=
  ⟨⟨FullM6CompactFlush.full_flush_trail_wf, trivial⟩,
    ⟨SpecEntry.Impl.of (FullM6CompactFlush.full_flush_trail_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hBt) (envRow_mem hnd _ _ _ _ hProp)), trivial⟩⟩

/-- `full_extend_push2` (`1` fn, `TmkZero`-preserving): zero external callees. -/
theorem m6CfExtendPush2_transport (tbl : List SpecEntry) :
    AllFns Fn.Wf m6CfExtendPush2Fns ∧
    TableImpl (Env.ofTable tbl) m6CfExtendPush2Fns m6CfExtendPush2Rows :=
  ⟨⟨FullM6CompactFlush.full_extend_push2_m6cf_wf, trivial⟩,
   ⟨SpecEntry.Impl.of (FullM6CompactFlush.full_extend_push2_m6cf_tmk_wp (Env.ofTable tbl)),
    trivial⟩⟩

/-- `full_extend_push_cl` (`1` fn, `TmkZero`-preserving): zero external callees. -/
theorem m6CfExtendPushCl_transport (tbl : List SpecEntry) :
    AllFns Fn.Wf m6CfExtendPushClFns ∧
    TableImpl (Env.ofTable tbl) m6CfExtendPushClFns m6CfExtendPushClRows :=
  ⟨⟨FullM6CompactFlush.full_extend_push_cl_m6cf_wf, trivial⟩,
   ⟨SpecEntry.Impl.of (FullM6CompactFlush.full_extend_push_cl_m6cf_tmk_wp (Env.ofTable tbl)),
    trivial⟩⟩

/-- `full_enter_dense` (`1` fn): calls `backtrack`, `flush_trail`, `sweep_bins`,
`watch_push`, `arena_sweep`, `arena_next`. -/
theorem m6CfEnterDense_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hBt : (⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ : SpecEntry) ∈ tbl)
    (hFlush : (⟨"full_flush_trail", [i64], [i64],
      FullM6CompactFlush.fullFlushTrailSpec, true⟩ : SpecEntry) ∈ tbl)
    (hSweep : (⟨"full_sweep_bins", [i64], [], Full.fullSweepBinsSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPush : (⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl)
    (hArenaSw : (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl) :
    AllFns Fn.Wf m6CfEnterDenseFns ∧
    TableImpl (Env.ofTable tbl) m6CfEnterDenseFns m6CfEnterDenseRows :=
  ⟨⟨FullM6CompactFlush.full_enter_dense_m6cf_wf, trivial⟩,
    ⟨SpecEntry.Impl.of (FullM6CompactFlush.full_enter_dense_m6cf_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hBt) (envRow_mem hnd _ _ _ _ hFlush)
      (envRow_mem hnd _ _ _ _ hSweep) (envRow_mem hnd _ _ _ _ hPush)
      (envRow_mem hnd _ _ _ _ hArenaSw) (envRow_mem hnd _ _ _ _ hNext)), trivial⟩⟩

/-- `full_compact_{needed,flush,mark_live}` (`3` fns). -/
theorem m6CfCompact3_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hFlush : (⟨"full_flush_trail", [i64], [i64],
      FullM6CompactFlush.fullFlushTrailSpec, true⟩ : SpecEntry) ∈ tbl)
    (hArenaSw : (⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl) :
    AllFns Fn.Wf m6CfCompact3Fns ∧
    TableImpl (Env.ofTable tbl) m6CfCompact3Fns m6CfCompact3Rows :=
  ⟨⟨FullM6CompactFlush.full_compact_needed_m6cf_wf,
      FullM6CompactFlush.full_compact_flush_m6cf_wf,
      FullM6CompactFlush.full_compact_mark_live_m6cf_wf, trivial⟩,
    ⟨SpecEntry.Impl.of (FullM6CompactFlush.full_compact_needed_m6cf_wp (Env.ofTable tbl)),
      SpecEntry.Impl.of (FullM6CompactFlush.full_compact_flush_m6cf_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hFlush) (envRow_mem hnd _ _ _ _ hArenaSw)),
      SpecEntry.Impl.of (FullM6CompactFlush.full_compact_mark_live_m6cf_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNext)),
      trivial⟩⟩

/-! ## 8. `FullM6WatchGc` (`12` Used Fns, Dropping `[5, 13..16]`) Transports -/

private theorem m6WatchGc0Fns_eq :
    m6WatchGc0Fns =
      [ ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [],
          FullM6WatchGc.full_wstack_radix_sort_m6_body⟩
      , ⟨"full_wstack_defrag_m6", [i64], [], FullM6WatchGc.full_wstack_defrag_m6_body⟩
      , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
          FullM6WatchGc.full_watch_push_m6_body⟩ ] := rfl

private theorem m6WatchGc0Rows_mem_p (i : Nat) (e : SpecEntry) :
    m6WatchGc0Rows[i]? = some e → e ∈ m6WatchGc0Rows :=
  fun h => List.mem_of_getElem? h

/-- `FullM6WatchGc[0..2]` (`3` fns): only external callee is `full_wsort_sift`. -/
theorem m6WatchGc0_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6WatchGc0Rows, e ∈ tbl)
    (hSift : (⟨"full_wsort_sift", [i64, i64, i64, i64], [],
      Full.fullWsortSiftSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6WatchGc0Fns ∧
    TableImpl (Env.ofTable tbl) m6WatchGc0Fns m6WatchGc0Rows := by
  have hm : ∀ (i : Nat) (e : SpecEntry), m6WatchGc0Rows[i]? = some e → e ∈ tbl :=
    fun i e h => hown e (m6WatchGc0Rows_mem_p i e h)
  have hRad := envRow_mem hnd _ _ _ _ (hm 0 _ (by rfl))
    (fun _ _ _ _ h => FullM6WatchGc.fullWstackRadixSortSpec_xirrel h)
  have hDef := envRow_mem hnd _ _ _ _ (hm 1 _ (by rfl))
  have hSf := envRow_mem hnd _ _ _ _ hSift
  refine ⟨allFns_drop_take_wf FullM6WatchGc.m6WatchGc_fns_wf 0 3, ?_⟩
  rw [m6WatchGc0Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_wstack_radix_sort_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_wstack_defrag_m6_wp (Env.ofTable tbl) hSf hRad)
    , SpecEntry.Impl.of (FullM6WatchGc.full_watch_push_m6_wp (Env.ofTable tbl) hDef)
    , trivial ⟩

private theorem m6WatchGc1Fns_eq :
    m6WatchGc1Fns =
      [ ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], FullM6WatchGc.full_lit_rank_m6_body⟩
      , ⟨"full_sweep_bins_range_m6", [i64, i64], [],
          FullM6WatchGc.full_sweep_bins_range_m6_body⟩ ] := rfl

/-- `FullM6WatchGc[3..4]` (`2` fns): only external callee is `full_wstack_defrag_m6`. -/
theorem m6WatchGc1_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hDefrag : (⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩ : SpecEntry) ∈
      tbl) :
    AllFns Fn.Wf m6WatchGc1Fns ∧
    TableImpl (Env.ofTable tbl) m6WatchGc1Fns m6WatchGc1Rows := by
  refine ⟨allFns_drop_take_wf FullM6WatchGc.m6WatchGc_fns_wf 3 2, ?_⟩
  rw [m6WatchGc1Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_lit_rank_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_sweep_bins_range_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDefrag))
    , trivial ⟩

private theorem m6WatchGc2Fns_eq :
    m6WatchGc2Fns =
      [ ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool],
          FullM6WatchGc.full_rewatch_range_m6_body⟩
      , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool],
          FullM6WatchGc.full_rewatch_arena_m6_body⟩ ] := rfl

private theorem m6WatchGc2Rows_mem_p (i : Nat) (e : SpecEntry) :
    m6WatchGc2Rows[i]? = some e → e ∈ m6WatchGc2Rows :=
  fun h => List.mem_of_getElem? h

/-- `FullM6WatchGc[6..7]` (`2` fns): calls `full_lit_rank_m6`, `full_watch_push_m6`. -/
theorem m6WatchGc2_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6WatchGc2Rows, e ∈ tbl)
    (hRank : (⟨"full_lit_rank_m6", [i64, i64, i32], [i64],
      Full.fullLitRankSpec, true⟩ : SpecEntry) ∈ tbl)
    (hPush : (⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6WatchGc2Fns ∧
    TableImpl (Env.ofTable tbl) m6WatchGc2Fns m6WatchGc2Rows := by
  have hm : ∀ (i : Nat) (e : SpecEntry), m6WatchGc2Rows[i]? = some e → e ∈ tbl :=
    fun i e h => hown e (m6WatchGc2Rows_mem_p i e h)
  have hRng := envRow_mem hnd _ _ _ _ (hm 0 _ (by rfl))
    (fun _ _ _ _ h => FullM6WatchGc.fullRewatchRangeSpec_xirrel h)
  refine ⟨allFns_drop_take_wf FullM6WatchGc.m6WatchGc_fns_wf 6 2, ?_⟩
  rw [m6WatchGc2Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_rewatch_range_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hRank) (envRow_mem hnd _ _ _ _ hPush))
    , SpecEntry.Impl.of (FullM6WatchGc.full_rewatch_arena_m6_wp (Env.ofTable tbl) hRng)
    , trivial ⟩

private theorem m6WatchGc3Fns_eq :
    m6WatchGc3Fns =
      [ ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [],
          FullM6WatchGc.full_move_red_pass2_m6_body⟩
      , ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [],
          FullM6WatchGc.full_move_red_end_buf_m6_body⟩
      , ⟨"full_move_red_end_m6", [i64, i64, i64], [], FullM6WatchGc.full_move_red_end_m6_body⟩
      , ⟨"full_arena_sweep_m6", [i64], [i64], FullM6WatchGc.full_arena_sweep_m6_body⟩
      , ⟨"full_mark_reasons_m6", [i64, .bool], [], FullM6WatchGc.full_mark_reasons_m6_body⟩ ] :=
  rfl

private theorem m6WatchGc3Rows_mem_p (i : Nat) (e : SpecEntry) :
    m6WatchGc3Rows[i]? = some e → e ∈ m6WatchGc3Rows :=
  fun h => List.mem_of_getElem? h

/-- `FullM6WatchGc[8..12]` (`5` fns): calls `sweep_bins_range_m6`, `rewatch_range_m6`,
`arena_next`, `sweep_copy`. -/
theorem m6WatchGc3_transport {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6WatchGc3Rows, e ∈ tbl)
    (hSwR : (⟨"full_sweep_bins_range_m6", [i64, i64], [],
      FullM6WatchGc.fullSweepBinsRangeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hRewR : (⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool],
      FullM6WatchGc.fullRewatchRangeSpec, true⟩ : SpecEntry) ∈ tbl)
    (hNext : (⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ : SpecEntry) ∈
      tbl)
    (hCopy : (⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64],
      Full.fullSweepCopySpec, true⟩ : SpecEntry) ∈ tbl) :
    AllFns Fn.Wf m6WatchGc3Fns ∧
    TableImpl (Env.ofTable tbl) m6WatchGc3Fns m6WatchGc3Rows := by
  have hm : ∀ (i : Nat) (e : SpecEntry), m6WatchGc3Rows[i]? = some e → e ∈ tbl :=
    fun i e h => hown e (m6WatchGc3Rows_mem_p i e h)
  have hP2 := envRow_mem hnd _ _ _ _ (hm 0 _ (by rfl))
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedPass2Spec_xirrel h)
  have hBuf := envRow_mem hnd _ _ _ _ (hm 1 _ (by rfl))
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedEndBufSpec_xirrel h)
  have hMre := envRow_mem hnd _ _ _ _ (hm 2 _ (by rfl))
    (fun _ _ _ _ h => FullM6WatchGc.fullMoveRedEndSpec_xirrel h)
  refine ⟨allFns_drop_take_wf FullM6WatchGc.m6WatchGc_fns_wf 8 5, ?_⟩
  rw [m6WatchGc3Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6WatchGc.full_move_red_pass2_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WatchGc.full_move_red_end_buf_m6_wp (Env.ofTable tbl) hP2)
    , SpecEntry.Impl.of (FullM6WatchGc.full_move_red_end_m6_wp (Env.ofTable tbl) hBuf)
    , SpecEntry.Impl.of (FullM6WatchGc.full_arena_sweep_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hSwR
          (fun _ _ _ _ h => FullM6WatchGc.fullSweepBinsRangeSpec_xirrel h))
        (envRow_mem hnd _ _ _ _ hNext) (envRow_mem hnd _ _ _ _ hCopy) hMre
        (envRow_mem hnd _ _ _ _ hRewR
          (fun _ _ _ _ h => FullM6WatchGc.fullRewatchRangeSpec_xirrel h)))
    , SpecEntry.Impl.of (FullM6WatchGc.full_mark_reasons_m6_wp (Env.ofTable tbl))
    , trivial ⟩

/-! ## 9. Exact Cross-Module Spec Bridges -/

/-- Strengthen `Full.fullExtendPush2Spec` from `FullFastBveBudgets.fullExtendPush2TmkSpec`. -/
theorem m6_extend_push2_tmk_to_canon {Γ : Env} {nm : Sym}
    (hTmk : ∀ a m Q X, FullFastBveBudgets.fullExtendPush2TmkSpec a m Q X →
      Γ nm [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullExtendPush2Spec a m Q X →
      Γ nm [i64, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, blk, ot, ⟨⟩⟩ m Q X ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact hTmk _ m Q X
    ⟨c, s, R, hpre, hlen, hm, fun r s' m' hc hlen' ⟨h1, h2, h3, _⟩ hm' =>
      hQ r s' m' hc hlen' ⟨h1, h2, h3⟩ hm'⟩

/-- Strengthen `Full.fullExtendPushClSpec` from `FullFastBveBudgets.fullExtendPushClTmkSpec`. -/
theorem m6_extend_push_cl_tmk_to_canon {Γ : Env} {nm : Sym}
    (hTmk : ∀ a m Q X, FullFastBveBudgets.fullExtendPushClTmkSpec a m Q X →
      Γ nm [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullExtendPushClSpec a m Q X →
      Γ nm [i64, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, blk, cr, ⟨⟩⟩ m Q X ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact hTmk _ m Q X
    ⟨c, s, R, hpre, hlen, hm, fun r s' m' hc hlen' ⟨h1, h2, h3, _⟩ hm' =>
      hQ r s' m' hc hlen' ⟨h1, h2, h3⟩ hm'⟩

/-- `FullM6CompactFlush.m6cfExtendPush2Fn` also implements canonical `Full.fullExtendPush2Spec`. -/
theorem m6CfExtendPush2_canon_impl (tbl : List SpecEntry) :
    SpecEntry.Impl (Env.ofTable tbl) FullM6CompactFlush.m6cfExtendPush2Fn
      ⟨"full_extend_push2", [i64, i32, i32], [.bool], Full.fullExtendPush2Spec, true⟩ :=
  SpecEntry.Impl.of (FullM6CompactFlush.full_extend_push2_m6cf_wp (Env.ofTable tbl))

/-- `FullM6CompactFlush.m6cfExtendPushClFn` also implements canonical
`Full.fullExtendPushClSpec`. -/
theorem m6CfExtendPushCl_canon_impl (tbl : List SpecEntry) :
    SpecEntry.Impl (Env.ofTable tbl) FullM6CompactFlush.m6cfExtendPushClFn
      ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], Full.fullExtendPushClSpec, true⟩ :=
  SpecEntry.Impl.of (FullM6CompactFlush.full_extend_push_cl_m6cf_wp (Env.ofTable tbl))

/-- `fastBveBudgets_fns[0]` (`full_init_hdr`) also implements `fullFastInitHdrSpec`. -/
theorem m6InitHdrFast_impl (tbl : List SpecEntry) :
    SpecEntry.Impl (Env.ofTable tbl)
      ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.full_init_hdr_body⟩
      ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.fullFastInitHdrSpec, true⟩ :=
  SpecEntry.Impl.of (FullFastBveBudgets.fast_init_hdr_wp (Env.ofTable tbl))

end LeanQbe.T.Examples.Kissat.FullM6Transport
