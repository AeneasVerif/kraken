/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6Transport0
public import LeanQbe.T.Examples.Kissat.FullM5
public import LeanQbe.T.Examples.Kissat.FullM5Proof
public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof
public import LeanQbe.T.Examples.Kissat.FullM6WalkParseProof3
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof0b
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2e
public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof
public import LeanQbe.T.Examples.Kissat.FullM6BvaNoHopsProof
public import LeanQbe.T.Examples.Kissat.FullM7ReorderProof
public import LeanQbe.T.Examples.Kissat.FullM4CompactProof
public import LeanQbe.T.Examples.Kissat.FullM4VivBceProof
public import LeanQbe.T.Examples.Kissat.FullM4BvaProof
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas
public import LeanQbe.T.Examples.Kissat.FullM5ProbePropProof
public import LeanQbe.T.Examples.Kissat.FullM5HbrProof
public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFixProof
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof
public import LeanQbe.T.Examples.Kissat.FullM5OrchProof
public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM4InprocHotProof
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas
public import LeanQbe.T.Examples.Kissat.FullM4Proof
public import LeanQbe.T.Examples.Kissat.FullFastAdapters
public import LeanQbe.T.Examples.Kissat.FullFastTmkLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas

/-!
# Kissat M6.0 Parametric Segment Transports — Part 1 (`FullM6Transport1`)

Spec-table rows and parametric `TableImpl (Env.ofTable tbl)` transports (zero expose tags,
plain `public section`, `0` M1 `.olean` leaks) covering all `234` remaining non-Orch functions in
`FullM6`: `FullM6MinShrink`, `FullM6WalkParse`, `FullM6VivBackbone` (`40`), `FullM6CongSubst`
(`23` + `FullM3CongBva` `[0..2]`), `FullM4Sweep` (`22` + `full_sweep_dense_m5`), `FullM6BveFwd`
(`[0..15]` + `[16..23]`), `FullM6BvaNoHops`, `FullM7Reorder` (`3`), `FullM4Compact` (`10`),
`FullM4VivBce` (`4`), `FullFastSched`/`M5Orch`, `FullKitten` + `FullM5KittenDefFix`, and kept
`Full1..5/M4` segments.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Transport

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-! ## 1. Additional Zero-`whnf` Transport Combinators & Cross-Module Bridges -/

/-- Extract `(∀ fn ∈ M.fns, fn.Wf)` from any `ModuleOk Γ M`. -/
theorem allFns_wf_of_moduleOk {Γ : Env} {M : LeanQbe.T.Module} (hM : ModuleOk Γ M) :
    ∀ fn ∈ M.fns, fn.Wf := by
  intro fn hmem
  rcases List.append_of_mem hmem with ⟨pre, post, hsplit⟩
  exact (hM.fnsOk pre fn post hsplit).1

/-- Transport `(M1.fns.drop off).take n` when `t1` appends extern rows after `M1.fns.length`. -/
theorem modTakeSliceTransport {M1 : LeanQbe.T.Module} {t1 : List SpecEntry}
    (hM1 : ModuleOk (Env.ofTable t1) M1) (hnd1 : (t1.map SpecEntry.name).Nodup)
    (hsig : (t1.take M1.fns.length).map (fun e => (e.name, e.as, e.rs)) =
      M1.fns.map (fun f => (f.name, f.as, f.rs)))
    (off n : Nat) (hle : off + n ≤ M1.fns.length) (extRows : List SpecEntry)
    (hcalls : ((M1.fns.drop off).take n).all
      (fun fn => fn.checkCallsOk
        (((t1.drop off).take n ++ extRows).map fun e => (e.name, e.as, e.rs)) []) = true)
    (hext_m1 : ∀ e ∈ extRows, e ∈ t1)
    {tbl : List SpecEntry} (hnd2 : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ (t1.drop off).take n, e ∈ tbl) (hext : ∀ e ∈ extRows, e ∈ tbl) :
    AllFns Fn.Wf ((M1.fns.drop off).take n) ∧
    TableImpl (Env.ofTable tbl) ((M1.fns.drop off).take n) ((t1.drop off).take n) := by
  have htake : ((t1.take M1.fns.length).drop off).take n = (t1.drop off).take n := by
    rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
  have hsub := modSub_drop_take (M1 := M1) (t1 := t1.take M1.fns.length) hsig
    (off := off) (n := n)
  rw [htake] at hsub
  exact modSubTransport hM1 hnd1 hsub.1
    (fun p hp =>
      have hp' := hsub.2 p hp
      ⟨hp'.1, List.mem_of_mem_take hp'.2.1, hp'.2.2⟩)
    (all_mem_of_bool hcalls) hext_m1 hnd2 hown hext

private theorem fullSlice0_transport (off n : Nat)
    (hcalls : ((Full.fullFns.drop off).take n).all
      (fun fn => fn.checkCallsOk
        (((fullBaseTable.drop off).take n ++ []).map fun (e : SpecEntry) => (e.name, e.as, e.rs))
        []) = true)
    {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ (fullBaseTable.drop off).take n, e ∈ tbl) :
    AllFns Fn.Wf ((Full.fullFns.drop off).take n) ∧
    TableImpl (Env.ofTable tbl) ((Full.fullFns.drop off).take n)
      ((fullBaseTable.drop off).take n) :=
  fullSliceTransport off n [] hcalls (fun _ h => nomatch h) hnd hown (fun _ h => nomatch h)

/-- `AllFns Fn.Wf` for any `(drop off).take n` slice of `FullM5.m5Fns`. -/
theorem m5SliceWf (off n : Nat) :
    AllFns Fn.Wf ((FullM5.m5Fns.drop off).take n) :=
  allFns_drop_take_wf (allFns_wf_of_moduleOk FullM5.m5Env_moduleOk) off n

/-- Direct `Env.ofTable tbl` row lookup from `(rows[i]? = some e)`. -/
theorem envRowAt {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    {rows : List SpecEntry} (hown : ∀ e ∈ rows, e ∈ tbl)
    (i : Nat) {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (h : rows[i]? = some ⟨nm, as, bs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → Env.ofTable tbl nm as bs xs m Q X :=
  envRow_mem hnd nm as bs sp (hown _ (List.mem_of_getElem? h)) hno

/-- `Nodup` witness for `FullM4Bva.m4BvaSpecTable`. -/
theorem m4BvaSpecTable_nodup : (FullM4Bva.m4BvaSpecTable.map SpecEntry.name).Nodup := by
  decide

private theorem oneImpl {tbl : List SpecEntry} {fs : List Fn} {rs : List SpecEntry}
    {nm : Sym} {as bs : List Ty} {body : Func as bs} {sp : Spec as bs}
    (hfn : fs = [⟨nm, as, bs, body⟩]) (hrs : rs = [⟨nm, as, bs, sp, true⟩])
    (hwf : AllFns Fn.Wf fs)
    (hwp : ∀ xs m Q X, sp xs m Q X → Func.wp (Env.ofTable tbl) body xs m Q X) :
    AllFns Fn.Wf fs ∧ TableImpl (Env.ofTable tbl) fs rs := by
  subst hfn hrs; exact ⟨hwf, ⟨SpecEntry.Impl.of hwp, trivial⟩⟩

private theorem mem1 {α : Type _} {a : α} {l : List α} (h : a ∈ l) : ∀ e ∈ [a], e ∈ l :=
  fun _ he => by cases List.mem_singleton.mp he; exact h

private theorem memC {α : Type _} {a : α} {xs l : List α} (h : a ∈ l)
    (hs : ∀ e ∈ xs, e ∈ l) : ∀ e ∈ a :: xs, e ∈ l :=
  fun _ he => by rcases List.mem_cons.mp he with rfl | hx; exact h; exact hs _ hx

/-- Strengthen `Full.FullProbeTransSpecs.fullAnalyze20Spec` from canonical
`Full.fullAnalyzeSpec`. -/
theorem m6_analyze_to_20 {Γ : Env}
    (hAna : ∀ a m Q X, Full.fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.FullProbeTransSpecs.fullAnalyze20Spec a m Q X →
      Γ "full_analyze" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcf, hm, hQ⟩
  refine hAna _ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcf, hm,
    fun r s' m' hlen' hr hcv hfu ⟨hws2, h20o⟩ h20u h0 h1 hm' => ?_⟩
  let toPt (ho : Full.FullOtfsWitnessInv c F0 F_cur s'.core) :
      Full.FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur s'.core :=
    ⟨ho.ext_sound, ho.inconsistent_sound, ho.arena, ho.watches, ho.cur_level_le,
      ho.trail_lits_lt, ho.trail_vars_nodup, ho.vals_domain, ho.vals_true_iff, ho.vals_false_iff,
      ho.lvl_le, ho.dec_earliest, ho.levels_inhabited, ho.level0_sound, ho.trail_pos_inv,
      ho.level0_rsn_none, ho.frame_trail_lt, ho.frame_trail_mono, ho.frame_trail_before_lt,
      ho.frame_dec_lt, ho.reason_inv_below, ho.reason_lit_mem_below⟩
  let toPtW (hw : Full.FullOtfsInvW c F0 F_cur s') :
      Full.FullProbeTransSpecs.FullOtfsInvW c F0 F_cur s' :=
    ⟨hw.1, toPt hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2⟩
  exact hQ r s' m' hlen' hr hcv hfu hws2
    (fun h20 => ⟨h20u h20, toPtW (h20o h20).1⟩) (fun h0' => toPtW (h0 h0')) h1 hm'

/-- Bridge canonical `Full.fullAddBinSpec` callers onto `FullM6VivBackbone.fullAddBinM6Spec`. -/
theorem m6_add_bin_m6_to_canon {Γ : Env} {nm : Sym}
    (hBin : ∀ a m Q X, FullM6VivBackbone.fullAddBinM6Spec a m Q X →
      Γ nm [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, Full.fullAddBinSpec a m Q X → Γ nm [i64, i32, i32] [i64] a m Q X :=
  fun a m Q X h => hBin a m Q X h

/-- Bridge canonical `Full.fullAddBinSpec` onto `Full.FullCongSpecs.fullAddBinSpec`. -/
theorem m6_add_bin_to_cong {Γ : Env}
    (hBin : ∀ a m Q X, Full.fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, Full.FullCongSpecs.fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hl, hw, h0, ha, hb, hent, hm, hQ⟩
  refine hBin _ m Q X ⟨c, F0, F_cur, s, R, rfl, hl, hw, h0, (fun _ _ => hent), hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
    phases' wsort' m' s' hl' hw' hr h20 _ hm'
  exact hQ r s' m' hl' hw' h0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun h20r => (h20 h20r).2) hm'

/-! ## 2. Segment Definitions (`234` Non-Orch Functions, Part 1) -/

def m6RescaleM6Fns : List Fn := FullM6WalkParse.m6WalkParse_fns.take 1
def m6RescaleM6Rows : List SpecEntry :=
  [⟨"full_rescale_m6", [i64], [], Full.fullRescaleSpec, true⟩]
def m6ParseBodyM6Fns : List Fn := (FullM6WalkParse.m6WalkParse_fns.drop 1).take 1
def m6ParseBodyM6Rows : List SpecEntry :=
  [⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩]
def m6AnalyzeLitFns : List Fn := (Full.fullFns.drop 62).take 1
def m6AnalyzeLitRows : List SpecEntry := (fullBaseTable.drop 62).take 1
def m6AnalyzeRsnFns : List Fn := (FullM5.m5Fns.drop 70).take 1
def m6AnalyzeRsnRows : List SpecEntry :=
  [⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩]
def m6ClearAnaFns : List Fn := (Full.fullFns.drop 64).take 1
def m6ClearAnaRows : List SpecEntry := (fullBaseTable.drop 64).take 1
def m6MinShrink0Fns : List Fn := (FullM6MinShrink.m6MinShrink_fns.drop 4).take 2
def m6MinShrink0Rows : List SpecEntry :=
  [ ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], FullM6MinShrink.m6AnaSiftSpec, true⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], [], FullM6MinShrink.m6SortAnaQsSpec, true⟩ ]
def m6OtfsFns : List Fn :=
  (FullM5.m5Fns.drop 74).take 1 ++
  [⟨"full_otfs_bin", [i64, i32, i32], [.bool], FullM5Otfs.full_otfs_bin_m5_body⟩] ++
  (FullM5.m5Fns.drop 76).take 1
def m6OtfsRows : List SpecEntry :=
  [ ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], Full.fullOtfsSubsumeSpec, true⟩ ]
def m6MinMarkFns : List Fn := (Full.fullFns.drop 69).take 1
def m6MinMarkRows : List SpecEntry := (fullBaseTable.drop 69).take 1
def m6SortTmpFns : List Fn := (Full.fullFns.drop 71).take 3
def m6SortTmpRows : List SpecEntry := (fullBaseTable.drop 71).take 3
def m6MinShrink1Fns : List Fn := (FullM6MinShrink.m6MinShrink_fns.drop 8).take 7
def m6MinShrink1Rows : List SpecEntry :=
  [ ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
      FullM6MinShrink.m6MinLitDfsSpec, true⟩
  , ⟨"full_min_lit_m6", [i64, i32], [.bool], Full.fullMinLitSpec, true⟩
  , ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool], Full.fullShrinkLowerSpec, true⟩
  , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
      FullM6MinShrink.m6ShrinkBlkBoolSpec, true⟩
  , ⟨"full_shrink_blk_m6", [i64, i64, i64, i32, i64], [], Full.fullShrinkBlkSpec, true⟩
  , ⟨"full_min_shrink_m6", [i64], [], Full.fullMinShrinkSpec, true⟩
  , ⟨"full_deduce_1uip_m6", [i64], [i64], Full.fullDeduce1uipSpec, true⟩ ]
def m6DetNewLevelFns : List Fn := (Full.fullFns.drop 77).take 1
def m6DetNewLevelRows : List SpecEntry := (fullBaseTable.drop 77).take 1
def m6OneLitConflFns : List Fn := (FullM5.m5Fns.drop 86).take 1
def m6OneLitConflRows : List SpecEntry :=
  [⟨"full_one_lit_confl", [i64], [i64], Full.fullOneLitConflSpec, true⟩]
def m6Learn2Fns : List Fn := (FullM5.m5Fns.drop 88).take 2
def m6Learn2Rows : List SpecEntry :=
  [ ⟨"full_eager_subsume", [i64, i64], [], Full.fullEagerSubsumeSpec, true⟩
  , ⟨"full_learn_clause", [i64, i64], [i64], Full.fullLearnClauseSpec, true⟩ ]
def m6BumpAnaM5Fns : List Fn := (FullM5.m5Fns.drop 72).take 2
def m6BumpAnaM5Rows : List SpecEntry :=
  [ ⟨"full_bump_analyzed", [i64], [], Full.fullBumpAnalyzedSpec, true⟩
  , ⟨"full_restore_bump_ana_m5", [i64], [], FullM5HeurCore.fullRestoreBumpAnaSpec, true⟩ ]
def m6AnalyzeM5Fns : List Fn := (FullM5.m5Fns.drop 90).take 1
def m6AnalyzeM5Rows : List SpecEntry :=
  [⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩]
def m6NextDecVarFns : List Fn := (Full.fullFns.drop 83).take 1
def m6NextDecVarRows : List SpecEntry := (fullBaseTable.drop 83).take 1
def m6WarmupFns : List Fn := (FullM5.m5Fns.drop 93).take 1
def m6WarmupRows : List SpecEntry :=
  [⟨"full_warmup", [i64], [], Full.fullWarmupSpec, true⟩]
def m6WalkCoreFns : List Fn := (FullM6WalkParse.m6WalkParse_fns.drop 2).take 9
def m6WalkCoreRows : List SpecEntry :=
  [ ⟨"full_walk_cb_inv_m6", [i64, i64, i64], [i64], FullM6WalkParse.m6WalkCbInvSpec, true⟩
  , ⟨"full_walk_score_m6", [i64, i64], [i32], FullM6WalkParse.m6WalkScoreSpec, true⟩
  , ⟨"full_walk_collect_m6", [i64, i64, i64], [i64], FullM6WalkParse.m6WalkCollectSpec, true⟩
  , ⟨"full_walk_build_csr_m6", [i64, i64, i64, i64], [i64],
      FullM6WalkParse.m6WalkBuildCsrSpec, true⟩
  , ⟨"full_walk_break_m6", [i64, i32, i64, i64, i64], [i64],
      FullM6WalkParse.m6WalkBreakSpec, true⟩
  , ⟨"full_walk_pick_m6", [i64, i64, i64, i64, i64, i64], [i32],
      FullM6WalkParse.m6WalkPickSpec, true⟩
  , ⟨"full_walk_flip_m6", [i64, i32, i64, i64, i64, i64], [i64],
      FullM6WalkParse.m6WalkFlipSpec, true⟩
  , ⟨"full_walk_core_m6", [i64], [], Full.fullWalkSpec, true⟩
  , ⟨"full_walk_m6", [i64], [], FullM6WalkParse.m6WalkSpec, true⟩ ]
def m6RestartDueFns : List Fn := (FullM5.m5Fns.drop 100).take 1
def m6RestartDueRows : List SpecEntry :=
  [⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩]
def m6RestartFns : List Fn := (Full.fullFns.drop 93).take 1
def m6RestartRows : List SpecEntry := (fullBaseTable.drop 93).take 1
def m6ExtendFns : List Fn := (FullM5.m5Fns.drop 104).take 1
def m6ExtendRows : List SpecEntry :=
  [⟨"full_extend", [i64], [], Full.fullExtendSpec, true⟩]
def m6HasBinFns : List Fn := (Full.fullFns.drop 97).take 1
def m6HasBinRows : List SpecEntry := (fullBaseTable.drop 97).take 1
def m6DelBinSideFns : List Fn := (Full.fullFns.drop 99).take 1
def m6DelBinSideRows : List SpecEntry := (fullBaseTable.drop 99).take 1
def m6AddBinM6Fns : List Fn := FullM6VivBackbone.m6VivBackbone_fns.take 1
def m6AddBinM6Rows : List SpecEntry := FullM6VivBackbone.m6VivBackboneSpecTable.take 1
def m6DelBinToLuckyFns : List Fn := (Full.fullFns.drop 100).take 6
def m6DelBinToLuckyRows : List SpecEntry := (fullBaseTable.drop 100).take 6
def m6HbrDomFns : List Fn := (FullM5.m5Fns.drop 114).take 1
def m6HbrDomRows : List SpecEntry :=
  [⟨"full_hbr_dom", [i64, i32, i32], [i32], Full.fullHbrDomSpec, true⟩]
def m6ProbePropLitFns : List Fn := (FullM5.m5Fns.drop 115).take 1
def m6ProbePropLitRows : List SpecEntry :=
  [⟨"full_probe_prop_lit", [i64, i32], [.bool], Full.fullProbePropLitSpec, true⟩]
def m6ProbePair2Fns : List Fn := (Full.fullFns.drop 108).take 2
def m6ProbePair2Rows : List SpecEntry := (fullBaseTable.drop 108).take 2
def m6ProbeAssumePairFns : List Fn :=
  [⟨"full_probe_assume_pair", [i64, i32], [i64],
    FullM6VivBackbone.full_probe_assume_pair_m6_body⟩]
def m6ProbeAssumePairRows : List SpecEntry :=
  [⟨"full_probe_assume_pair", [i64, i32], [i64], Full.fullProbeAssumePairSpec, true⟩]
def m6ProbeRunFns : List Fn := (FullM5.m5Fns.drop 119).take 1
def m6ProbeRunRows : List SpecEntry :=
  [⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩]
def m6VivBb1Fns : List Fn := (FullM6VivBackbone.m6VivBackbone_fns.drop 3).take 26
def m6VivBb1Rows : List SpecEntry := (FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 26
def m6VivBb2Fns : List Fn := (FullM6VivBackbone.m6VivBackbone_fns.drop 29).take 11
def m6VivBb2Rows : List SpecEntry := (FullM6VivBackbone.m6VivBackboneSpecTable.drop 29).take 11
def m6TarjanPopSccFns : List Fn := (Full.fullFns.drop 120).take 1
def m6TarjanPopSccRows : List SpecEntry := (fullBaseTable.drop 120).take 1
def m6TarjanSccFns : List Fn := FullM6CongSubst.m6CongSubst_fns.take 1
def m6TarjanSccRows : List SpecEntry :=
  [⟨"full_tarjan_scc", [i64], [i64], Full.fullTarjanSccSpec, true⟩]
def m6SubstElimVarsFns : List Fn := (Full.fullFns.drop 122).take 1
def m6SubstElimVarsRows : List SpecEntry := (fullBaseTable.drop 122).take 1
def m6SubstRewriteFns : List Fn := (FullM6CongSubst.m6CongSubst_fns.drop 1).take 3
def m6SubstRewriteRows : List SpecEntry :=
  [ ⟨"full_subst_rewrite_bins", [i64], [.bool], Full.fullSubstRewriteBinsSpec, true⟩
  , ⟨"full_subst_rewrite_ar", [i64], [.bool], Full.fullSubstRewriteArSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩ ]
def m6RebuildWatchesFns : List Fn := (Full.fullFns.drop 127).take 1
def m6RebuildWatchesRows : List SpecEntry := (fullBaseTable.drop 127).take 1
def m6CongFindFns : List Fn := (Full.fullFns.drop 128).take 1
def m6CongFindRows : List SpecEntry := (fullBaseTable.drop 128).take 1
def m6CongMergeFns : List Fn := (FullM6CongSubst.m6CongSubst_fns.drop 4).take 1
def m6CongMergeRows : List SpecEntry :=
  [⟨"full_cong_merge", [i64, i32, i32], [.bool], Full.fullCongMergeSpec, true⟩]
def m6CongBva3Fns : List Fn := FullM3CongBva.m3CongBva_fns.take 3
def m6CongBva3Rows : List SpecEntry := FullM3CongBva.m3SpecTable.take 3
def m6HasTernaryFns : List Fn := (FullM5.m5Fns.drop 164).take 1
def m6HasTernaryRows : List SpecEntry :=
  [⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], Full.fullHasTernarySpec, true⟩]
def m6SortU32Fns : List Fn := (Full.fullFns.drop 131).take 1
def m6SortU32Rows : List SpecEntry := (fullBaseTable.drop 131).take 1
def m6CongDenseFns : List Fn := (FullM6CongSubst.m6CongSubst_fns.drop 5).take 18
def m6CongDenseRows : List SpecEntry :=
  [ ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64],
      FullM6CongSubst.m6CongExtractIteSpec, true⟩
  , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64],
      FullM6CongSubst.m6CongEmitXorSpec, true⟩
  , ⟨"full_cong_has_clause_k", [i64, i32], [.bool], FullM6CongSubst.m6CongHasClauseKSpec, true⟩
  , ⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64],
      FullM6CongSubst.m6CongExtractXorKSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
      FullM6CongSubst.m6CongTryXorIteSpec, true⟩
  , ⟨"full_cong_count_bins", [i64], [], FullM6CongSubst.m6CongCountBinsSpec, true⟩
  , ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool], FullM6CongSubst.m6CongEbMatchSpec, true⟩
  , ⟨"full_cong_extract_binaries", [i64, i64], [i64],
      FullM6CongSubst.m6CongExtractBinariesSpec, true⟩
  , ⟨"full_cong_find_units_equivs", [i64], [i64],
      FullM6CongSubst.m6CongFindUnitsEquivsSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM6CongSubst.m6CongExtractSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM6CongSubst.m6CongAndMatchSpec, true⟩
  , ⟨"full_cong_xor_match", [i64, i32, i32], [i32], FullM6CongSubst.m6CongXorMatchSpec, true⟩
  , ⟨"full_cong_enq_var", [i64, i64, i32], [], FullM6CongSubst.m6CongEnqVarSpec, true⟩
  , ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64],
      FullM6CongSubst.m6CongEvalGateSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
      FullM6CongSubst.m6CongWorkStepSpec, true⟩
  , ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64],
      FullM6CongSubst.m6CongWorklistSpec, true⟩
  , ⟨"full_cong_fwd_subsume", [i64, i64], [i64], FullM6CongSubst.m6CongFwdSubsumeSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩ ]
def m6Sweep22Fns : List Fn := FullM4Sweep.fullM4Sweep_fns.take 22
def m6Sweep22Rows : List SpecEntry := FullM4Sweep.fullM4SweepSpecTable.take 22
def m6SweepDenseM5Fns : List Fn := (FullM5.m5Fns.drop 200).take 1
def m6SweepDenseM5Rows : List SpecEntry :=
  [⟨"full_sweep_dense_m5", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩]
def m6FwdDedupBinsFns : List Fn := (Full.fullFns.drop 145).take 1
def m6FwdDedupBinsRows : List SpecEntry := (fullBaseTable.drop 145).take 1
def m6BveFwd0Fns : List Fn := FullM6BveFwd.m6BveFwd_fns.take 10
def m6BveFwd0Rows : List SpecEntry :=
  [ ⟨"full_dense_prop_unit_m6", [i64, i32], [.bool], FullM6BveFwd.fullDensePropUnitM6Spec, true⟩
  , ⟨"full_dense_flush_units_m6", [i64], [.bool], FullM6BveFwd.fullDenseFlushUnitsM6Spec, true⟩
  , ⟨"full_fwd_flush_large_m6", [i64], [], FullM6BveFwd.fullFwdFlushLargeM6Spec, true⟩
  , ⟨"full_fwd_reconnect_irred_m6", [i64], [], FullM6BveFwd.fullFwdReconnectIrredM6Spec, true⟩
  , ⟨"full_fwd_scan_lit_m6", [i64, i32, i32, i32, .bool], [i32],
      FullM6BveFwd.fullFwdScanLitM6Spec, true⟩
  , ⟨"full_fwd_check_cl_m6", [i64, i32], [.bool], FullM6BveFwd.fullFwdCheckClM6Spec, true⟩
  , ⟨"full_fwd_connect_subsumer_m6", [i64, i32], [],
      FullM6BveFwd.fullFwdConnectSubsumerM6Spec, true⟩
  , ⟨"full_fwd_collect_sort_m6", [i64], [i64], FullM6BveFwd.fullFwdCollectSortM6Spec, true⟩
  , ⟨"full_forward_sub_m6", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_collect_m6", [i64, i32, i64, i32], [i32], Full.fullBveCollectSpec, true⟩ ]
def m6KittenInitFns : List Fn := (FullM5.m5Fns.drop 147).take 1
def m6KittenInitRows : List SpecEntry :=
  [⟨"full_kitten_init", [i64, i32, i32], [], Full.fullKittenInitSpec, true⟩]
def m6Kitten14Fns : List Fn := (Full.fullKittenModule.fns.drop 1).take 14
def m6Kitten14Rows : List SpecEntry := (Full.fullKittenSpecTable.drop 1).take 14
def m6KittenDefFix5Fns : List Fn := FullM5KittenDefFix.m5KittenDefFix_fns.take 5
def m6KittenDefFix5Rows : List SpecEntry := FullM5KittenDefFix.m5KittenDefFixSpecTable.take 5
def m6FindDefinitionFns : List Fn := (FullM5.m5Fns.drop 211).take 1
def m6FindDefinitionRows : List SpecEntry :=
  [⟨"full_find_definition", [i64, i32, i32, i32], [], FullDefSweep.fullFindDefinitionSpec, true⟩]
def m6BveFwd1Fns : List Fn := (FullM6BveFwd.m6BveFwd_fns.drop 10).take 6
def m6BveFwd1Rows : List SpecEntry :=
  [ ⟨"full_bve_mark_and_m6", [i64, i32, i32, i32, i32, i32], [.bool],
      FullM6BveFwd.fullBveMarkAndM6Spec, true⟩
  , ⟨"full_bve_get_tern_m6", [i64, i32, i32, i32], [.bool],
      FullM6BveFwd.fullBveGetTernM6Spec, true⟩
  , ⟨"full_bve_match_tern_m6", [i64, i32, i32, i32, i32, i32], [i32],
      FullM6BveFwd.fullBveMatchTernM6Spec, true⟩
  , ⟨"full_bve_find_ite_m6", [i64, i32, i32, i32], [.bool],
      FullM6BveFwd.fullBveFindIteM6Spec, true⟩
  , ⟨"full_bve_gates_m6", [i64, i32, i32, i32], [], FullM6BveFwd.fullBveGatesM6Spec, true⟩
  , ⟨"full_bve_var_m6", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩ ]
def m6BveCollectFns : List Fn := (Full.fullFns.drop 148).take 1
def m6BveCollectRows : List SpecEntry := (fullBaseTable.drop 148).take 1
def m6BveResPairFns : List Fn := (Full.fullFns.drop 151).take 1
def m6BveResPairRows : List SpecEntry := (fullBaseTable.drop 151).take 1
def m6BveWeakenFns : List Fn := (Full.fullFns.drop 152).take 1
def m6BveWeakenRows : List SpecEntry :=
  [⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
    FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩]
def m6BveTryBceFns : List Fn := (Full.fullFns.drop 153).take 1
def m6BveTryBceRows : List SpecEntry := (fullBaseTable.drop 153).take 1
def m6BveCommitResFns : List Fn := (Full.fullFns.drop 154).take 1
def m6BveCommitResRows : List SpecEntry :=
  [⟨"full_bve_commit_res", [i64, i64, i64], [i64],
    FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩]
def m6BveExtNeedFns : List Fn := (Full.fullFns.drop 155).take 1
def m6BveExtNeedRows : List SpecEntry := (fullBaseTable.drop 155).take 1
def m6InitFreshVarM6Fns : List Fn := (FullM6VivBackbone.m6VivBackbone_fns.drop 1).take 1
def m6InitFreshVarM6Rows : List SpecEntry :=
  (FullM6VivBackbone.m6VivBackboneSpecTable.drop 1).take 1
def m6BvaHopFns : List Fn := FullM4Bva.m4Bva_fns.take 3
def m6BvaHopRows : List SpecEntry := FullM4Bva.m4BvaSpecTable.take 3
def m6BvaMatchLargeFns : List Fn := (FullM5.m5Fns.drop 223).take 1
def m6BvaMatchLargeRows : List SpecEntry :=
  [⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], FullBvaHeap.fullBvaMatchLargeSpec, true⟩]
def m6BvaScanCandsFns : List Fn := (FullM5.m5Fns.drop 224).take 1
def m6BvaScanCandsRows : List SpecEntry :=
  [⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], FullM4Bva.m4BvaScanCandsSpec, true⟩]
def m6BvaPickCandFns : List Fn :=
  [⟨"full_bva_pick_cand", [i64, i32, i32], [i32],
    FullM6BvaNoHops.full_bva_pick_cand_no_hops_body⟩]
def m6BvaPickCandRows : List SpecEntry :=
  [⟨"full_bva_pick_cand", [i64, i32, i32], [i32], FullBvaHeap.fullBvaPickCandSpec, true⟩]
def m6BvaFilterRowFns : List Fn := (FullM4Bva.m4Bva_fns.drop 4).take 1
def m6BvaFilterRowRows : List SpecEntry := (FullM4Bva.m4BvaSpecTable.drop 4).take 1
def m6BvaCommitFns : List Fn := (FullM5.m5Fns.drop 227).take 1
def m6BvaCommitRows : List SpecEntry :=
  [⟨"full_bva_commit", [i64, i32], [.bool], FullM4Bva.m4BvaCommitSpec, true⟩]
def m6BvaTryLitFns : List Fn := (FullM4Bva.m4Bva_fns.drop 6).take 1
def m6BvaTryLitRows : List SpecEntry := (FullM4Bva.m4BvaSpecTable.drop 6).take 1
def m6FheapPairFns : List Fn := (FullM5.m5Fns.drop 229).take 2
def m6FheapPairRows : List SpecEntry :=
  [ ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.fullFheapDownSpec, true⟩ ]
def m6FactorFns : List Fn := (FullM4Bva.m4Bva_fns.drop 7).take 1
def m6FactorRows : List SpecEntry := (FullM4Bva.m4BvaSpecTable.drop 7).take 1
def m6Compact10Fns : List Fn := (FullM4Compact.compact_fns.drop 3).take 10
def m6Compact10Rows : List SpecEntry := (FullM4Compact.compactSpecTable.drop 3).take 10
def m6ReorderFns : List Fn := FullM7Reorder.m7ReorderModule.fns
def m6ReorderRows : List SpecEntry :=
  [ ⟨"full_reorder_weight_m7", [i64], [i64], FullM7Reorder.m7ReorderWeightSpec, true⟩
  , ⟨"full_reorder_sift_m7", [i64, i64, i64], [], FullM7Reorder.m7ReorderSiftSpec, true⟩
  , ⟨"full_reorder_queue_m7", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩ ]
def m6VivBce4Fns : List Fn := (FullM4VivBce.m4VivBce_fns.drop 12).take 4
def m6VivBce4Rows : List SpecEntry :=
  [ ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4VivBce.fullBceSideM4Spec, true⟩
  , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.fullBcePairM4Spec, true⟩
  , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.fullBceVarM4Spec, true⟩
  , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.fullBceM4Spec, true⟩ ]
def m6SchedMinMaxFns : List Fn := (FullM5.m5Fns.drop 252).take 2
def m6SchedMinMaxRows : List SpecEntry :=
  [ ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩ ]
def m6ElimDticksFns : List Fn :=
  [⟨"full_elim_dticks", [i64, .bool], [i64], FullM5Orch.full_elim_dticks_m5_body⟩]
def m6ElimDticksRows : List SpecEntry :=
  [⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩]
def m6BveFwd2Fns : List Fn := (FullM6BveFwd.m6BveFwd_fns.drop 16).take 8
def m6BveFwd2Rows : List SpecEntry :=
  [ ⟨"full_bve_var_key_m6", [i64, i32], [i64], FullM6BveFwd.fullBveVarKeyM6Spec, true⟩
  , ⟨"full_bve_heap_up_m6", [i64, i64, i32], [], FullM6BveFwd.fullBveHeapUpM6Spec, true⟩
  , ⟨"full_bve_heap_down_m6", [i64, i64, i32], [], FullM6BveFwd.fullBveHeapDownM6Spec, true⟩
  , ⟨"full_bve_heap_push_m6", [i64, i64, i32], [i64], FullM6BveFwd.fullBveHeapPushM6Spec, true⟩
  , ⟨"full_bve_heap_pop_m6", [i64, i64], [i32], FullM6BveFwd.fullBveHeapPopM6Spec, true⟩
  , ⟨"full_bve_collect_nbrs_m6", [i64, i32], [i64], FullM3CongBva.m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve_m6", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩ ]

/-! ## 3. Segment Metadata, Count Check (`234`), and `sigs` Exports -/

def m6Transport1Fns : List Fn :=
  m6RescaleM6Fns ++ m6ParseBodyM6Fns ++ m6AnalyzeLitFns ++ m6AnalyzeRsnFns ++ m6ClearAnaFns
  ++ m6MinShrink0Fns ++ m6OtfsFns ++ m6MinMarkFns ++ m6SortTmpFns ++ m6MinShrink1Fns
  ++ m6DetNewLevelFns ++ m6OneLitConflFns ++ m6Learn2Fns ++ m6BumpAnaM5Fns ++ m6AnalyzeM5Fns
  ++ m6NextDecVarFns ++ m6WarmupFns ++ m6WalkCoreFns ++ m6RestartDueFns ++ m6RestartFns
  ++ m6ExtendFns ++ m6HasBinFns ++ m6DelBinSideFns ++ m6AddBinM6Fns ++ m6DelBinToLuckyFns
  ++ m6HbrDomFns ++ m6ProbePropLitFns ++ m6ProbePair2Fns ++ m6ProbeAssumePairFns ++ m6ProbeRunFns
  ++ m6VivBb1Fns ++ m6VivBb2Fns ++ m6TarjanPopSccFns ++ m6TarjanSccFns ++ m6SubstElimVarsFns
  ++ m6SubstRewriteFns ++ m6RebuildWatchesFns ++ m6CongFindFns ++ m6CongMergeFns ++ m6CongBva3Fns
  ++ m6HasTernaryFns ++ m6SortU32Fns ++ m6CongDenseFns ++ m6Sweep22Fns ++ m6SweepDenseM5Fns
  ++ m6FwdDedupBinsFns ++ m6BveFwd0Fns ++ m6KittenInitFns ++ m6Kitten14Fns ++ m6KittenDefFix5Fns
  ++ m6FindDefinitionFns ++ m6BveFwd1Fns ++ m6BveCollectFns ++ m6BveResPairFns ++ m6BveWeakenFns
  ++ m6BveTryBceFns ++ m6BveCommitResFns ++ m6BveExtNeedFns ++ m6InitFreshVarM6Fns ++ m6BvaHopFns
  ++ m6BvaMatchLargeFns ++ m6BvaScanCandsFns ++ m6BvaPickCandFns ++ m6BvaFilterRowFns
  ++ m6BvaCommitFns ++ m6BvaTryLitFns ++ m6FheapPairFns ++ m6FactorFns ++ m6Compact10Fns
  ++ m6ReorderFns ++ m6VivBce4Fns ++ m6SchedMinMaxFns ++ m6ElimDticksFns ++ m6BveFwd2Fns
def m6Transport1Rows : List SpecEntry :=
  m6RescaleM6Rows ++ m6ParseBodyM6Rows ++ m6AnalyzeLitRows ++ m6AnalyzeRsnRows ++ m6ClearAnaRows
  ++ m6MinShrink0Rows ++ m6OtfsRows ++ m6MinMarkRows ++ m6SortTmpRows ++ m6MinShrink1Rows
  ++ m6DetNewLevelRows ++ m6OneLitConflRows ++ m6Learn2Rows ++ m6BumpAnaM5Rows ++ m6AnalyzeM5Rows
  ++ m6NextDecVarRows ++ m6WarmupRows ++ m6WalkCoreRows ++ m6RestartDueRows ++ m6RestartRows
  ++ m6ExtendRows ++ m6HasBinRows ++ m6DelBinSideRows ++ m6AddBinM6Rows ++ m6DelBinToLuckyRows
  ++ m6HbrDomRows ++ m6ProbePropLitRows ++ m6ProbePair2Rows ++ m6ProbeAssumePairRows
  ++ m6ProbeRunRows ++ m6VivBb1Rows ++ m6VivBb2Rows ++ m6TarjanPopSccRows ++ m6TarjanSccRows
  ++ m6SubstElimVarsRows ++ m6SubstRewriteRows ++ m6RebuildWatchesRows ++ m6CongFindRows
  ++ m6CongMergeRows ++ m6CongBva3Rows ++ m6HasTernaryRows ++ m6SortU32Rows ++ m6CongDenseRows
  ++ m6Sweep22Rows ++ m6SweepDenseM5Rows ++ m6FwdDedupBinsRows ++ m6BveFwd0Rows
  ++ m6KittenInitRows ++ m6Kitten14Rows ++ m6KittenDefFix5Rows ++ m6FindDefinitionRows
  ++ m6BveFwd1Rows ++ m6BveCollectRows ++ m6BveResPairRows ++ m6BveWeakenRows ++ m6BveTryBceRows
  ++ m6BveCommitResRows ++ m6BveExtNeedRows ++ m6InitFreshVarM6Rows ++ m6BvaHopRows
  ++ m6BvaMatchLargeRows ++ m6BvaScanCandsRows ++ m6BvaPickCandRows ++ m6BvaFilterRowRows
  ++ m6BvaCommitRows ++ m6BvaTryLitRows ++ m6FheapPairRows ++ m6FactorRows ++ m6Compact10Rows
  ++ m6ReorderRows ++ m6VivBce4Rows ++ m6SchedMinMaxRows ++ m6ElimDticksRows ++ m6BveFwd2Rows

theorem m6Transport1_count_check : m6Transport1Fns.length = 234 := by t_kernel_rfl
theorem m6Transport1Rows_count_check : m6Transport1Rows.length = 234 := by t_kernel_rfl
theorem m6Transport1Rows_noExit : ∀ e ∈ m6Transport1Rows, e.noExit = true := by
  exact fun e he => all_mem_of_bool
    (by t_kernel_rfl : m6Transport1Rows.all SpecEntry.noExit = true) e he

theorem m6RescaleM6_sigs : m6RescaleM6Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6RescaleM6Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6ParseBodyM6_sigs : m6ParseBodyM6Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6ParseBodyM6Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6AnalyzeLit_sigs : m6AnalyzeLitRows.map (fun e => (e.name, e.as, e.rs)) =
    m6AnalyzeLitFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6AnalyzeRsn_sigs : m6AnalyzeRsnRows.map (fun e => (e.name, e.as, e.rs)) =
    m6AnalyzeRsnFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6ClearAna_sigs : m6ClearAnaRows.map (fun e => (e.name, e.as, e.rs)) =
    m6ClearAnaFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6MinShrink0_sigs : m6MinShrink0Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6MinShrink0Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Otfs_sigs : m6OtfsRows.map (fun e => (e.name, e.as, e.rs)) =
    m6OtfsFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6MinMark_sigs : m6MinMarkRows.map (fun e => (e.name, e.as, e.rs)) =
    m6MinMarkFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6SortTmp_sigs : m6SortTmpRows.map (fun e => (e.name, e.as, e.rs)) =
    m6SortTmpFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6MinShrink1_sigs : m6MinShrink1Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6MinShrink1Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6DetNewLevel_sigs : m6DetNewLevelRows.map (fun e => (e.name, e.as, e.rs)) =
    m6DetNewLevelFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6OneLitConfl_sigs : m6OneLitConflRows.map (fun e => (e.name, e.as, e.rs)) =
    m6OneLitConflFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Learn2_sigs : m6Learn2Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6Learn2Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BumpAnaM5_sigs : m6BumpAnaM5Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6BumpAnaM5Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6AnalyzeM5_sigs : m6AnalyzeM5Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6AnalyzeM5Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6NextDecVar_sigs : m6NextDecVarRows.map (fun e => (e.name, e.as, e.rs)) =
    m6NextDecVarFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Warmup_sigs : m6WarmupRows.map (fun e => (e.name, e.as, e.rs)) =
    m6WarmupFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6WalkCore_sigs : m6WalkCoreRows.map (fun e => (e.name, e.as, e.rs)) =
    m6WalkCoreFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6RestartDue_sigs : m6RestartDueRows.map (fun e => (e.name, e.as, e.rs)) =
    m6RestartDueFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Restart_sigs : m6RestartRows.map (fun e => (e.name, e.as, e.rs)) =
    m6RestartFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Extend_sigs : m6ExtendRows.map (fun e => (e.name, e.as, e.rs)) =
    m6ExtendFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6HasBin_sigs : m6HasBinRows.map (fun e => (e.name, e.as, e.rs)) =
    m6HasBinFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6DelBinSide_sigs : m6DelBinSideRows.map (fun e => (e.name, e.as, e.rs)) =
    m6DelBinSideFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6AddBinM6_sigs : m6AddBinM6Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6AddBinM6Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6DelBinToLucky_sigs : m6DelBinToLuckyRows.map (fun e => (e.name, e.as, e.rs)) =
    m6DelBinToLuckyFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6HbrDom_sigs : m6HbrDomRows.map (fun e => (e.name, e.as, e.rs)) =
    m6HbrDomFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6ProbePropLit_sigs : m6ProbePropLitRows.map (fun e => (e.name, e.as, e.rs)) =
    m6ProbePropLitFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6ProbePair2_sigs : m6ProbePair2Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6ProbePair2Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6ProbeAssumePair_sigs : m6ProbeAssumePairRows.map (fun e => (e.name, e.as, e.rs)) =
    m6ProbeAssumePairFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6ProbeRun_sigs : m6ProbeRunRows.map (fun e => (e.name, e.as, e.rs)) =
    m6ProbeRunFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6VivBb1_sigs : m6VivBb1Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6VivBb1Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6VivBb2_sigs : m6VivBb2Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6VivBb2Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6TarjanPopScc_sigs : m6TarjanPopSccRows.map (fun e => (e.name, e.as, e.rs)) =
    m6TarjanPopSccFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6TarjanScc_sigs : m6TarjanSccRows.map (fun e => (e.name, e.as, e.rs)) =
    m6TarjanSccFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6SubstElimVars_sigs : m6SubstElimVarsRows.map (fun e => (e.name, e.as, e.rs)) =
    m6SubstElimVarsFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6SubstRewrite_sigs : m6SubstRewriteRows.map (fun e => (e.name, e.as, e.rs)) =
    m6SubstRewriteFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6RebuildWatches_sigs : m6RebuildWatchesRows.map (fun e => (e.name, e.as, e.rs)) =
    m6RebuildWatchesFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6CongFind_sigs : m6CongFindRows.map (fun e => (e.name, e.as, e.rs)) =
    m6CongFindFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6CongMerge_sigs : m6CongMergeRows.map (fun e => (e.name, e.as, e.rs)) =
    m6CongMergeFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6CongBva3_sigs : m6CongBva3Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6CongBva3Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6HasTernary_sigs : m6HasTernaryRows.map (fun e => (e.name, e.as, e.rs)) =
    m6HasTernaryFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6SortU32_sigs : m6SortU32Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6SortU32Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6CongDense_sigs : m6CongDenseRows.map (fun e => (e.name, e.as, e.rs)) =
    m6CongDenseFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Sweep22_sigs : m6Sweep22Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6Sweep22Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6SweepDenseM5_sigs : m6SweepDenseM5Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6SweepDenseM5Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6FwdDedupBins_sigs : m6FwdDedupBinsRows.map (fun e => (e.name, e.as, e.rs)) =
    m6FwdDedupBinsFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveFwd0_sigs : m6BveFwd0Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveFwd0Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6KittenInit_sigs : m6KittenInitRows.map (fun e => (e.name, e.as, e.rs)) =
    m6KittenInitFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Kitten14_sigs : m6Kitten14Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6Kitten14Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6KittenDefFix5_sigs : m6KittenDefFix5Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6KittenDefFix5Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6FindDefinition_sigs : m6FindDefinitionRows.map (fun e => (e.name, e.as, e.rs)) =
    m6FindDefinitionFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveFwd1_sigs : m6BveFwd1Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveFwd1Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveCollect_sigs : m6BveCollectRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveCollectFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveResPair_sigs : m6BveResPairRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveResPairFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveWeaken_sigs : m6BveWeakenRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveWeakenFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveTryBce_sigs : m6BveTryBceRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveTryBceFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveCommitRes_sigs : m6BveCommitResRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveCommitResFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveExtNeed_sigs : m6BveExtNeedRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveExtNeedFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6InitFreshVarM6_sigs : m6InitFreshVarM6Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6InitFreshVarM6Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BvaHop_sigs : m6BvaHopRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BvaHopFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BvaMatchLarge_sigs : m6BvaMatchLargeRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BvaMatchLargeFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BvaScanCands_sigs : m6BvaScanCandsRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BvaScanCandsFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BvaPickCand_sigs : m6BvaPickCandRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BvaPickCandFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BvaFilterRow_sigs : m6BvaFilterRowRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BvaFilterRowFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BvaCommit_sigs : m6BvaCommitRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BvaCommitFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BvaTryLit_sigs : m6BvaTryLitRows.map (fun e => (e.name, e.as, e.rs)) =
    m6BvaTryLitFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6FheapPair_sigs : m6FheapPairRows.map (fun e => (e.name, e.as, e.rs)) =
    m6FheapPairFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Factor_sigs : m6FactorRows.map (fun e => (e.name, e.as, e.rs)) =
    m6FactorFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Compact10_sigs : m6Compact10Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6Compact10Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6Reorder_sigs : m6ReorderRows.map (fun e => (e.name, e.as, e.rs)) =
    m6ReorderFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6VivBce4_sigs : m6VivBce4Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6VivBce4Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6SchedMinMax_sigs : m6SchedMinMaxRows.map (fun e => (e.name, e.as, e.rs)) =
    m6SchedMinMaxFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6ElimDticks_sigs : m6ElimDticksRows.map (fun e => (e.name, e.as, e.rs)) =
    m6ElimDticksFns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
theorem m6BveFwd2_sigs : m6BveFwd2Rows.map (fun e => (e.name, e.as, e.rs)) =
    m6BveFwd2Fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl
/-! ## 4. Parametric `TableImpl` Transports — Kept `Full`, `WalkParse`, & `MinShrink` -/

theorem m6RescaleM6_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6RescaleM6Fns ∧ TableImpl (Env.ofTable tbl) m6RescaleM6Fns m6RescaleM6Rows :=
  oneImpl rfl rfl ⟨FullM6WalkParse.full_rescale_m6_wf, trivial⟩
    (FullM6WalkParse.full_rescale_m6_wp (Env.ofTable tbl))

theorem m6ParseBodyM6_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hSkip : ⟨"full_skip_cl", [i64, i64], [.bool], Full.fullSkipClSpec, true⟩ ∈ tbl)
    (hIng : ⟨"full_ingest_cl", [i64, i64], [i64], Full.fullIngestClSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl)
    (hWs : ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6ParseBodyM6Fns ∧
    TableImpl (Env.ofTable tbl) m6ParseBodyM6Fns m6ParseBodyM6Rows :=
  oneImpl rfl rfl ⟨FullM6WalkParse.full_parse_body_m6_wf, trivial⟩
    (FullM6WalkParse.full_parse_body_m6_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hSkip)
      (envRow_mem hnd _ _ _ _ hIng) (envRow_mem hnd _ _ _ _ hProp) (envRow_mem hnd _ _ _ _ hWs))

theorem m6AnalyzeLit_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6AnalyzeLitRows, e ∈ tbl) :
    AllFns Fn.Wf m6AnalyzeLitFns ∧
    TableImpl (Env.ofTable tbl) m6AnalyzeLitFns m6AnalyzeLitRows :=
  fullSlice0_transport 62 1 (by t_kernel_rfl) hnd hown

theorem m6AnalyzeRsn_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hLit : ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6AnalyzeRsnFns ∧
    TableImpl (Env.ofTable tbl) m6AnalyzeRsnFns m6AnalyzeRsnRows :=
  oneImpl rfl rfl (m5SliceWf 70 1)
    (FullM5HeurCore.full_analyze_rsn_m5_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hLit))

theorem m6ClearAna_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6ClearAnaRows, e ∈ tbl) :
    AllFns Fn.Wf m6ClearAnaFns ∧ TableImpl (Env.ofTable tbl) m6ClearAnaFns m6ClearAnaRows :=
  fullSlice0_transport 64 1 (by t_kernel_rfl) hnd hown

private theorem m6MinShrink0Fns_eq :
    m6MinShrink0Fns =
      [ ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], FullM6MinShrink.full_ana_sift_m6_body⟩
      , ⟨"full_sort_ana_qs_m6", [i64, i64], [], FullM6MinShrink.full_sort_ana_qs_m6_body⟩ ] :=
  rfl
theorem m6MinShrink0_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6MinShrink0Rows, e ∈ tbl) :
    AllFns Fn.Wf m6MinShrink0Fns ∧
    TableImpl (Env.ofTable tbl) m6MinShrink0Fns m6MinShrink0Rows := by
  have r0 := envRowAt hnd hown 0 rfl (fun _ _ _ _ h => FullM6MinShrink.m6AnaSiftSpec_monoX h)
  refine ⟨allFns_drop_take_wf FullM6MinShrink.m6MinShrink_fns_wf 4 2, ?_⟩
  rw [m6MinShrink0Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6MinShrink.full_ana_sift_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6MinShrink.full_sort_ana_qs_m6_wp (Env.ofTable tbl) r0), trivial ⟩

private theorem m6OtfsFns_eq :
    m6OtfsFns =
      [ ⟨"full_otfs_large", [i64, i32, i32], [.bool], FullM5Otfs.full_otfs_large_body⟩
      , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], FullM5Otfs.full_otfs_bin_m5_body⟩
      , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [],
          FullM5HeurCore.full_otfs_subsume_m5_body⟩ ] := rfl
theorem m6Otfs_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl)
    (hUnw : ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6OtfsFns ∧ TableImpl (Env.ofTable tbl) m6OtfsFns m6OtfsRows := by
  refine ⟨⟨(m5SliceWf 74 1).1, FullM5Otfs.full_otfs_bin_m5_wf,
    FullM5HeurCore.full_otfs_subsume_m5_wf, trivial⟩, ?_⟩
  rw [m6OtfsFns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM5Otfs.full_otfs_large_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDef) (envRow_mem hnd _ _ _ _ hUnw) (envRow_mem hnd _ _ _ _ hWp))
    , SpecEntry.Impl.of (FullM5Otfs.full_otfs_bin_m5_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNext) (envRow_mem hnd _ _ _ _ hDef)
        (envRow_mem hnd _ _ _ _ hUnw) (envRow_mem hnd _ _ _ _ hWp))
    , SpecEntry.Impl.of (FullM5HeurCore.full_otfs_subsume_m5_wp (Env.ofTable tbl)), trivial ⟩

theorem m6MinMark_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6MinMarkRows, e ∈ tbl) :
    AllFns Fn.Wf m6MinMarkFns ∧ TableImpl (Env.ofTable tbl) m6MinMarkFns m6MinMarkRows :=
  fullSlice0_transport 69 1 (by t_kernel_rfl) hnd hown

theorem m6SortTmp_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6SortTmpRows, e ∈ tbl) :
    AllFns Fn.Wf m6SortTmpFns ∧ TableImpl (Env.ofTable tbl) m6SortTmpFns m6SortTmpRows :=
  fullSlice0_transport 71 3 (by t_kernel_rfl) hnd hown

private theorem m6MinShrink1Fns_eq :
    m6MinShrink1Fns =
      [ ⟨"full_min_lit_dfs_m6", [i64, i32, .bool, .bool], [.bool],
          FullM6MinShrink.full_min_lit_dfs_m6_body⟩
      , ⟨"full_min_lit_m6", [i64, i32], [.bool], FullM6MinShrink.full_min_lit_m6_body⟩
      , ⟨"full_shrink_lower_m6", [i64, i32, i32], [.bool],
          FullM6MinShrink.full_shrink_lower_m6_body⟩
      , ⟨"full_shrink_blk_bool_m6", [i64, i64, i64, i32, i64], [.bool],
          FullM6MinShrink.full_shrink_blk_bool_m6_body⟩
      , ⟨"full_shrink_blk_m6", [i64, i64, i64, i32, i64], [],
          FullM6MinShrink.full_shrink_blk_m6_body⟩
      , ⟨"full_min_shrink_m6", [i64], [], FullM6MinShrink.full_min_shrink_m6_body⟩
      , ⟨"full_deduce_1uip_m6", [i64], [i64], FullM6MinShrink.full_deduce_1uip_m6_body⟩ ] := rfl
theorem m6MinShrink1_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6MinShrink1Rows, e ∈ tbl)
    (hMark : ⟨"full_min_mark", [i64, i32, i8], [], Full.fullMinMarkSpec, true⟩ ∈ tbl)
    (hSortTmp : ⟨"full_sort_tmp", [i64], [], Full.fullSortTmpSpec, true⟩ ∈ tbl)
    (hAnaLit : ⟨"full_analyze_lit", [i64, i32, i32], [.bool], Full.fullAnalyzeLitSpec, true⟩ ∈ tbl)
    (hAnaRsn : ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], Full.fullAnalyzeRsnSpec, true⟩ ∈ tbl)
    (hClear : ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩ ∈ tbl)
    (hOtfsL : ⟨"full_otfs_large", [i64, i32, i32], [.bool], Full.fullOtfsLargeSpec, true⟩ ∈ tbl)
    (hOtfsB : ⟨"full_otfs_bin", [i64, i32, i32], [.bool], Full.fullOtfsBinSpec, true⟩ ∈ tbl)
    (hOtfsS : ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [],
      Full.fullOtfsSubsumeSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6MinShrink1Fns ∧
    TableImpl (Env.ofTable tbl) m6MinShrink1Fns m6MinShrink1Rows := by
  have rDfs := envRowAt hnd hown 0 rfl (fun _ _ _ _ h => FullM6MinShrink.m6MinLitDfsSpec_monoX h)
  have rLow := envRowAt hnd hown 2 rfl (fun _ _ _ _ h => h)
  have rBlkB := envRowAt hnd hown 3 rfl
    (fun _ _ _ _ h => FullM6MinShrink.m6ShrinkBlkBoolSpec_monoX h)
  have rMrk := envRow_mem hnd _ _ _ _ hMark
  refine ⟨allFns_drop_take_wf FullM6MinShrink.m6MinShrink_fns_wf 8 7, ?_⟩
  rw [m6MinShrink1Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6MinShrink.full_min_lit_dfs_m6_wp (Env.ofTable tbl) rMrk)
    , SpecEntry.Impl.of (FullM6MinShrink.full_min_lit_m6_wp (Env.ofTable tbl) rDfs)
    , SpecEntry.Impl.of (FullM6MinShrink.full_shrink_lower_m6_wp (Env.ofTable tbl) rMrk rDfs)
    , SpecEntry.Impl.of (FullM6MinShrink.full_shrink_blk_bool_m6_wp (Env.ofTable tbl) rLow rMrk)
    , SpecEntry.Impl.of (FullM6MinShrink.full_shrink_blk_m6_wp (Env.ofTable tbl) rBlkB)
    , SpecEntry.Impl.of (FullM6MinShrink.full_min_shrink_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hSortTmp) rMrk rDfs rBlkB)
    , SpecEntry.Impl.of (FullM6MinShrink.full_deduce_1uip_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hAnaLit) (envRow_mem hnd _ _ _ _ hAnaRsn)
        (envRow_mem hnd _ _ _ _ hClear) (envRow_mem hnd _ _ _ _ hOtfsL)
        (envRow_mem hnd _ _ _ _ hOtfsB) (envRow_mem hnd _ _ _ _ hOtfsS)), trivial ⟩

theorem m6DetNewLevel_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6DetNewLevelRows, e ∈ tbl) :
    AllFns Fn.Wf m6DetNewLevelFns ∧
    TableImpl (Env.ofTable tbl) m6DetNewLevelFns m6DetNewLevelRows :=
  fullSlice0_transport 77 1 (by t_kernel_rfl) hnd hown

theorem m6OneLitConfl_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl)
    (hDet : ⟨"full_det_new_level", [i64, i64], [i64], Full.fullDetNewLevelSpec, true⟩ ∈ tbl)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hALvl : ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ ∈ tbl)
    (hUnw : ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6OneLitConflFns ∧
    TableImpl (Env.ofTable tbl) m6OneLitConflFns m6OneLitConflRows :=
  oneImpl rfl rfl (m5SliceWf 86 1)
    (FullM5Otfs.full_one_lit_confl_m5_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hDef)
      (envRow_mem hnd _ _ _ _ hDet) (envRow_mem hnd _ _ _ _ hBt)
      (envRow_mem hnd _ _ _ _ hALvl) (envRow_mem hnd _ _ _ _ hUnw) (envRow_mem hnd _ _ _ _ hWp))

private theorem m6Learn2Fns_eq :
    m6Learn2Fns =
      [ ⟨"full_eager_subsume", [i64, i64], [], FullM5HeurCore.full_eager_subsume_m5_body⟩
      , ⟨"full_learn_clause", [i64, i64], [i64], FullM5HeurCore.full_learn_clause_m5_body⟩ ] :=
  rfl
theorem m6Learn2_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6Learn2Rows, e ∈ tbl)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hALvl : ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ ∈ tbl)
    (hDet : ⟨"full_det_new_level", [i64, i64], [i64], Full.fullDetNewLevelSpec, true⟩ ∈ tbl)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl)
    (hRed : ⟨"full_reduce", [i64, .bool], [i64], Full.fullReduceSpec, true⟩ ∈ tbl)
    (hACl : ⟨"full_add_clause", [i64, i32, i32, .bool], [i64],
      Full.fullAddClauseSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6Learn2Fns ∧ TableImpl (Env.ofTable tbl) m6Learn2Fns m6Learn2Rows := by
  refine ⟨m5SliceWf 88 2, ?_⟩
  rw [m6Learn2Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM5HeurCore.full_eager_subsume_m5_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM5HeurCore.full_learn_clause_m5_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hBt) (envRow_mem hnd _ _ _ _ hALvl)
        (envRow_mem hnd _ _ _ _ hDet) (envRow_mem hnd _ _ _ _ hDef)
        (envRow_mem hnd _ _ _ _ hRed) (envRow_mem hnd _ _ _ _ hACl)
        (envRowAt hnd hown 0 rfl (fun _ _ _ _ h => h))), trivial ⟩

private theorem m6BumpAnaM5Fns_eq :
    m6BumpAnaM5Fns =
      [ ⟨"full_bump_analyzed", [i64], [], FullM5HeurCore.full_bump_analyzed_m5_body⟩
      , ⟨"full_restore_bump_ana_m5", [i64], [],
          FullM5HeurCore.full_restore_bump_ana_m5_body⟩ ] := rfl
theorem m6BumpAnaM5_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BumpAnaM5Rows, e ∈ tbl)
    (hBV : ⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩ ∈ tbl)
    (hQM : ⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩ ∈ tbl)
    (hBD : ⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩ ∈ tbl)
    (hCA : ⟨"full_clear_ana", [i64], [], Full.fullClearAnaSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BumpAnaM5Fns ∧ TableImpl (Env.ofTable tbl) m6BumpAnaM5Fns m6BumpAnaM5Rows := by
  refine ⟨m5SliceWf 72 2, ?_⟩
  rw [m6BumpAnaM5Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM5HeurCore.full_bump_analyzed_m5_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hBV) (envRow_mem hnd _ _ _ _ hQM) (envRow_mem hnd _ _ _ _ hBD))
    , SpecEntry.Impl.of (FullM5HeurCore.full_restore_bump_ana_m5_wp (Env.ofTable tbl)
        (envRowAt hnd hown 0 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hCA)), trivial ⟩

theorem m6AnalyzeM5_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hOne : ⟨"full_one_lit_confl", [i64], [i64], Full.fullOneLitConflSpec, true⟩ ∈ tbl)
    (hDed : ⟨"full_deduce_1uip", [i64], [i64], Full.fullDeduce1uipSpec, true⟩ ∈ tbl)
    (hRst : ⟨"full_restore_bump_ana_m5", [i64], [],
      FullM5HeurCore.fullRestoreBumpAnaSpec, true⟩ ∈ tbl)
    (hMin : ⟨"full_min_shrink", [i64], [], Full.fullMinShrinkSpec, true⟩ ∈ tbl)
    (hTick : ⟨"full_tick_rel", [i64], [], Full.fullTickRelSpec, true⟩ ∈ tbl)
    (hEma : ⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩ ∈ tbl)
    (hLrn : ⟨"full_learn_clause", [i64, i64], [i64], Full.fullLearnClauseSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6AnalyzeM5Fns ∧
    TableImpl (Env.ofTable tbl) m6AnalyzeM5Fns m6AnalyzeM5Rows :=
  oneImpl rfl rfl (m5SliceWf 90 1)
    (FullM5HeurCore.full_analyze_m5_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hOne)
      (envRow_mem hnd _ _ _ _ hDed) (envRow_mem hnd _ _ _ _ hRst)
      (envRow_mem hnd _ _ _ _ hMin) (envRow_mem hnd _ _ _ _ hTick)
      (envRow_mem hnd _ _ _ _ hEma) (envRow_mem hnd _ _ _ _ hLrn))

theorem m6NextDecVar_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6NextDecVarRows, e ∈ tbl)
    (hHeapPop : ⟨"full_heap_pop", [i64], [i64], Full.fullHeapPopSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6NextDecVarFns ∧
    TableImpl (Env.ofTable tbl) m6NextDecVarFns m6NextDecVarRows :=
  fullSliceTransport 83 1 [⟨"full_heap_pop", [i64], [i64], Full.fullHeapPopSpec, true⟩]
    (by t_kernel_rfl) (mem1 (fullRow_at 19 _)) hnd hown (mem1 hHeapPop)

theorem m6Warmup_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hNext : ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩ ∈ tbl)
    (hAsg : ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl)
    (hBtRaw : ⟨"full_backtrack_raw_m5", [i64, i64], [],
      FullM5HeurCore.fullBacktrackRawSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6WarmupFns ∧ TableImpl (Env.ofTable tbl) m6WarmupFns m6WarmupRows :=
  oneImpl rfl rfl (m5SliceWf 93 1)
    (FullM5HeurCore.full_warmup_m5_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hNext)
      (envRow_mem hnd _ _ _ _ hAsg) (envRow_mem hnd _ _ _ _ hProp)
      (envRow_mem hnd _ _ _ _ hBtRaw))

private theorem m6WalkCoreFns_eq :
    m6WalkCoreFns =
      [ ⟨"full_walk_cb_inv_m6", [i64, i64, i64], [i64], FullM6WalkParse.full_walk_cb_inv_m6_body⟩
      , ⟨"full_walk_score_m6", [i64, i64], [i32], FullM6WalkParse.full_walk_score_m6_body⟩
      , ⟨"full_walk_collect_m6", [i64, i64, i64], [i64],
          FullM6WalkParse.full_walk_collect_m6_body⟩
      , ⟨"full_walk_build_csr_m6", [i64, i64, i64, i64], [i64],
          FullM6WalkParse.full_walk_build_csr_m6_body⟩
      , ⟨"full_walk_break_m6", [i64, i32, i64, i64, i64], [i64],
          FullM6WalkParse.full_walk_break_m6_body⟩
      , ⟨"full_walk_pick_m6", [i64, i64, i64, i64, i64, i64], [i32],
          FullM6WalkParse.full_walk_pick_m6_body⟩
      , ⟨"full_walk_flip_m6", [i64, i32, i64, i64, i64, i64], [i64],
          FullM6WalkParse.full_walk_flip_m6_body⟩
      , ⟨"full_walk_core_m6", [i64], [], FullM6WalkParse.full_walk_core_m6_body⟩
      , ⟨"full_walk_m6", [i64], [], FullM6WalkParse.full_walk_m6_body⟩ ] := rfl
theorem m6WalkCore_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6WalkCoreRows, e ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hRng : ⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩ ∈ tbl)
    (hWarm : ⟨"full_warmup", [i64], [], Full.fullWarmupSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6WalkCoreFns ∧ TableImpl (Env.ofTable tbl) m6WalkCoreFns m6WalkCoreRows := by
  have er := envRowAt hnd hown
  have hRngR := envRow_mem hnd _ _ _ _ hRng
  refine ⟨allFns_drop_take_wf FullM6WalkParse.m6WalkParse_fns_wf 2 9, ?_⟩
  rw [m6WalkCoreFns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6WalkParse.full_walk_cb_inv_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WalkParse.full_walk_score_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WalkParse.full_walk_collect_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNext))
    , SpecEntry.Impl.of (FullM6WalkParse.full_walk_build_csr_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WalkParse.full_walk_break_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WalkParse.full_walk_pick_m6_wp (Env.ofTable tbl)
        (er 4 rfl (fun _ _ _ _ h => h)) (er 1 rfl (fun _ _ _ _ h => h)) hRngR)
    , SpecEntry.Impl.of (FullM6WalkParse.full_walk_flip_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6WalkParse.full_walk_core_m6_wp (Env.ofTable tbl)
        (er 2 rfl (fun _ _ _ _ h => h)) (er 3 rfl (fun _ _ _ _ h => h))
        (er 0 rfl (fun _ _ _ _ h => h)) hRngR (er 5 rfl (fun _ _ _ _ h => h))
        (er 6 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6WalkParse.full_walk_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hWarm) (er 7 rfl (fun _ _ _ _ h => h))), trivial ⟩

/-! ## 5. Parametric `TableImpl` Transports — Restart, Extend, & Probe -/

theorem m6RestartDue_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hIlog : ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6RestartDueFns ∧ TableImpl (Env.ofTable tbl) m6RestartDueFns m6RestartDueRows :=
  oneImpl rfl rfl (m5SliceWf 100 1)
    (FullM5Sched.full_restart_due_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hIlog))

theorem m6Restart_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6RestartRows, e ∈ tbl)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hNext : ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6RestartFns ∧ TableImpl (Env.ofTable tbl) m6RestartFns m6RestartRows :=
  fullSliceTransport 93 1
    [ ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
    , ⟨"full_next_dec_var", [i64], [i64], Full.fullNextDecVarSpec, true⟩ ]
    (by t_kernel_rfl)
    (memC (fullRow_at 30 _) (mem1 (fullRow_at 83 _))) hnd hown (memC hBt (mem1 hNext))

theorem m6Extend_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6ExtendFns ∧ TableImpl (Env.ofTable tbl) m6ExtendFns m6ExtendRows :=
  oneImpl rfl rfl (m5SliceWf 104 1) (FullM4.m4_extend_wp (Env.ofTable tbl))

theorem m6HasBin_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6HasBinRows, e ∈ tbl) :
    AllFns Fn.Wf m6HasBinFns ∧ TableImpl (Env.ofTable tbl) m6HasBinFns m6HasBinRows :=
  fullSlice0_transport 97 1 (by t_kernel_rfl) hnd hown

theorem m6DelBinSide_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6DelBinSideRows, e ∈ tbl) :
    AllFns Fn.Wf m6DelBinSideFns ∧ TableImpl (Env.ofTable tbl) m6DelBinSideFns m6DelBinSideRows :=
  fullSlice0_transport 99 1 (by t_kernel_rfl) hnd hown

theorem m6AddBinM6_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hHb : ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ ∈ tbl)
    (hALvl : ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6AddBinM6Fns ∧ TableImpl (Env.ofTable tbl) m6AddBinM6Fns m6AddBinM6Rows :=
  oneImpl rfl rfl (allFns_drop_take_wf FullM6VivBackbone.m6VivBackbone_fns_wf 0 1)
    (FullM6VivBackbone.full_add_bin_m6_ext_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hHb) (envRow_mem hnd _ _ _ _ hALvl) (envRow_mem hnd _ _ _ _ hWp))

theorem m6DelBinToLucky_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6DelBinToLuckyRows, e ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hALvl : ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ ∈ tbl)
    (hAsg : ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ ∈ tbl)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl)
    (hAna : ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩ ∈ tbl)
    (hDelSide : ⟨"full_delete_bin_side", [i64, i32, i32], [],
      Full.fullDeleteBinSideSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6DelBinToLuckyFns ∧
    TableImpl (Env.ofTable tbl) m6DelBinToLuckyFns m6DelBinToLuckyRows :=
  fullSliceTransport 100 6
    [ ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
    , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
    , ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩
    , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
    , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
    , ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩
    , ⟨"full_delete_bin_side", [i64, i32, i32], [], Full.fullDeleteBinSideSpec, true⟩ ]
    (by t_kernel_rfl)
    (memC (fullRow_at 11 _) <| memC (fullRow_at 27 _) <| memC (fullRow_at 28 _) <|
      memC (fullRow_at 30 _) <| memC (fullRow_at 49 _) <| memC (fullRow_at 82 _) <|
      mem1 (fullRow_at 99 _))
    hnd hown
    (memC hNext <| memC hALvl <| memC hAsg <| memC hBt <| memC hProp <| memC hAna <| mem1 hDelSide)

theorem m6HbrDom_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6HbrDomFns ∧ TableImpl (Env.ofTable tbl) m6HbrDomFns m6HbrDomRows :=
  oneImpl rfl rfl (m5SliceWf 114 1) (FullM5Hbr.full_hbr_dom_m5_wp (Env.ofTable tbl))

theorem m6ProbePropLit_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hRepl : ⟨"full_find_repl", [i64, i64], [i64], Full.fullFindReplSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl)
    (hHbr : ⟨"full_hbr_dom", [i64, i32, i32], [i32], Full.fullHbrDomSpec, true⟩ ∈ tbl)
    (hALvl : ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6ProbePropLitFns ∧
    TableImpl (Env.ofTable tbl) m6ProbePropLitFns m6ProbePropLitRows :=
  oneImpl rfl rfl (m5SliceWf 115 1)
    (FullM5ProbeProp.full_probe_prop_lit_m5_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hRepl)
      (envRow_mem hnd _ _ _ _ hWp) (envRow_mem hnd _ _ _ _ hHbr) (envRow_mem hnd _ _ _ _ hALvl))

theorem m6ProbePair2_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6ProbePair2Rows, e ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl)
    (hAddBin : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl)
    (hPpl : ⟨"full_probe_prop_lit", [i64, i32], [.bool], Full.fullProbePropLitSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6ProbePair2Fns ∧ TableImpl (Env.ofTable tbl) m6ProbePair2Fns m6ProbePair2Rows :=
  fullSliceTransport 108 2
    [ ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
    , ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩
    , ⟨"full_probe_prop_lit", [i64, i32], [.bool], Full.fullProbePropLitSpec, true⟩ ]
    (by t_kernel_rfl)
    (memC (fullRow_at 49 _) <| memC (fullRow_at 98 _) <| mem1 (fullRow_at 107 _))
    hnd hown (memC hProp <| memC hAddBin <| mem1 hPpl)

theorem m6ProbeAssumePair_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hAsg : ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ ∈ tbl)
    (hPp : ⟨"full_probe_prop", [i64], [i64], Full.fullProbePropSpec, true⟩ ∈ tbl)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hAna : ⟨"full_analyze", [i64], [i64], Full.fullAnalyzeSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl)
    (hFh : ⟨"full_probe_flush_hbr", [i64, i64], [i64], Full.fullProbeFlushHbrSpec, true⟩ ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6ProbeAssumePairFns ∧
    TableImpl (Env.ofTable tbl) m6ProbeAssumePairFns m6ProbeAssumePairRows :=
  oneImpl rfl rfl ⟨(allFns_drop_take_wf FullM6VivBackbone.m6VivBackbone_fns_wf 2 1).1, trivial⟩
    (FullM6VivBackbone.full_probe_assume_pair_m6_canon_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hAsg) (envRow_mem hnd _ _ _ _ hPp) (envRow_mem hnd _ _ _ _ hBt)
      (m6_analyze_to_20 (envRow_mem hnd _ _ _ _ hAna)) (envRow_mem hnd _ _ _ _ hProp)
      (envRow_mem hnd _ _ _ _ hFh) (envRow_mem hnd _ _ _ _ hAu))

theorem m6ProbeRun_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hAp : ⟨"full_probe_assume_pair", [i64, i32], [i64],
      Full.fullProbeAssumePairSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6ProbeRunFns ∧ TableImpl (Env.ofTable tbl) m6ProbeRunFns m6ProbeRunRows :=
  oneImpl rfl rfl (m5SliceWf 119 1)
    (FullM3Backbone.m3_probe_run_cursor_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hBt) (envRow_mem hnd _ _ _ _ hAp))

/-! ## 6. Parametric `TableImpl` Transports — `FullM6VivBackbone` (`37` Remaining Fns) -/

private theorem m6VivBb1Fns_eq :
    m6VivBb1Fns =
      [ ⟨"full_viv_unreason_m6", [i64, i32], [], FullM6VivBackbone.full_viv_unreason_m6_body⟩
      , ⟨"full_viv_watch_rank_m6", [i64, i32], [i64],
          FullM6VivBackbone.full_viv_watch_rank_m6_body⟩
      , ⟨"full_viv_best_watch_m6", [i64, i32], [], FullM6VivBackbone.full_viv_best_watch_m6_body⟩
      , ⟨"full_viv_simplify_m6", [i64, i32], [i64], FullM6VivBackbone.full_viv_simplify_m6_body⟩
      , ⟨"full_viv_commit_m6", [i64, i32, i32, i32], [i64],
          FullM6VivBackbone.full_viv_commit_m6_body⟩
      , ⟨"full_viv_mark_garb_m6", [i64, i32], [], FullM6VivBackbone.full_viv_mark_garb_m6_body⟩
      , ⟨"full_viv_subsumes_bin_m6", [i64, i32, i32], [.bool],
          FullM6VivBackbone.full_viv_subsumes_bin_m6_body⟩
      , ⟨"full_viv_subsumes_cl_m6", [i64, i32, i32], [.bool],
          FullM6VivBackbone.full_viv_subsumes_cl_m6_body⟩
      , ⟨"full_viv_deduce_m6", [i64, i32, i32, i32], [i32],
          FullM6VivBackbone.full_viv_deduce_m6_body⟩
      , ⟨"full_viv_best_implied_m6", [i64, i32], [i32],
          FullM6VivBackbone.full_viv_best_implied_m6_body⟩
      , ⟨"full_viv_reestablish_m6", [i64, i32], [],
          FullM6VivBackbone.full_viv_reestablish_m6_body⟩
      , ⟨"full_viv_inst_check_m6", [i64, i32, i32, i32], [.bool],
          FullM6VivBackbone.full_viv_inst_check_m6_body⟩
      , ⟨"full_viv_inst_m6", [i64, i32, i32], [i64], FullM6VivBackbone.full_viv_inst_m6_body⟩
      , ⟨"full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64],
          FullM6VivBackbone.full_viv_finish_m6_body⟩
      , ⟨"full_viv_sort_counts_m6", [i64, i32], [],
          FullM6VivBackbone.full_viv_sort_counts_m6_body⟩
      , ⟨"full_viv_has_l0_m6", [i64, i32, i32], [.bool], FullM6VivBackbone.full_viv_has_l0_m6_body⟩
      , ⟨"full_viv_l0_simp_m6", [i64, i32, i32], [i64], FullM6VivBackbone.full_viv_l0_simp_m6_body⟩
      , ⟨"full_viv_reuse_prefix_m6", [i64, i32, i32], [],
          FullM6VivBackbone.full_viv_reuse_prefix_m6_body⟩
      , ⟨"full_viv_clause_m6", [i64, i32], [i64], FullM6VivBackbone.full_viv_clause_m6_body⟩
      , ⟨"full_viv_tier_match_m6", [i64, i32, i64], [.bool],
          FullM6VivBackbone.full_viv_tier_match_m6_body⟩
      , ⟨"full_viv_collect_m6", [i64, i64], [i64], FullM6VivBackbone.full_viv_collect_m6_body⟩
      , ⟨"full_viv_count_m6", [i64, i64], [], FullM6VivBackbone.full_viv_count_m6_body⟩
      , ⟨"full_viv_keys_m6", [i64, i64], [], FullM6VivBackbone.full_viv_keys_m6_body⟩
      , ⟨"full_viv_sort_sched_m6", [i64, i64], [], FullM6VivBackbone.full_viv_sort_sched_m6_body⟩
      , ⟨"full_viv_clear_tier_m6", [i64, i64], [], FullM6VivBackbone.full_viv_clear_tier_m6_body⟩
      , ⟨"full_vivify_m6", [i64, i64, i64], [i64], FullM6VivBackbone.full_vivify_m6_body⟩ ] := rfl
theorem m6VivBb1_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6VivBb1Rows, e ∈ tbl)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hUnw : ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl)
    (hAb6 : ⟨"full_add_bin_m6", [i64, i32, i32], [i64],
      FullM6VivBackbone.fullAddBinM6Spec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl)
    (hAsg : ⟨"full_assign", [i64, i32, i32], [], Full.fullAssignSpec, true⟩ ∈ tbl)
    (hPIgn : ⟨"full_propagate_ignore", [i64, i64], [i64],
      Full.fullPropagateIgnoreSpec, true⟩ ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6VivBb1Fns ∧ TableImpl (Env.ofTable tbl) m6VivBb1Fns m6VivBb1Rows := by
  have er := envRowAt hnd hown
  have rBt := envRow_mem hnd _ _ _ _ hBt; have rUnw := envRow_mem hnd _ _ _ _ hUnw
  have rAu := envRow_mem hnd _ _ _ _ hAu; have rAb6 := envRow_mem hnd _ _ _ _ hAb6
  have rWp := envRow_mem hnd _ _ _ _ hWp; have rAsg := envRow_mem hnd _ _ _ _ hAsg
  have rPI := envRow_mem hnd _ _ _ _ hPIgn; have rNext := envRow_mem hnd _ _ _ _ hNext
  have r0 := er 0 rfl (fun _ _ _ _ h => h); have r2 := er 2 rfl (fun _ _ _ _ h => h)
  have r4 := er 4 rfl (fun _ _ _ _ h => h); have r8 := er 8 rfl (fun _ _ _ _ h => h)
  have r19 := er 19 rfl (fun _ _ _ _ h => h)
  refine ⟨allFns_drop_take_wf FullM6VivBackbone.m6VivBackbone_fns_wf 3 26, ?_⟩
  rw [m6VivBb1Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6VivBackbone.full_viv_unreason_m6_wp (Env.ofTable tbl) rBt)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_watch_rank_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_watch_m6_wp (Env.ofTable tbl)
        (er 1 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_simplify_m6_wp (Env.ofTable tbl)
        rUnw rAu rAb6 rWp)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_commit_m6_wp (Env.ofTable tbl)
        rBt rUnw rAu rAb6 rWp r0 r2)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_mark_garb_m6_wp (Env.ofTable tbl) r0 rUnw)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_bin_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_subsumes_cl_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_deduce_m6_wp (Env.ofTable tbl)
        (er 6 rfl (fun _ _ _ _ h => h)) (er 7 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_best_implied_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reestablish_m6_wp (Env.ofTable tbl) rBt)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_check_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_inst_m6_wp (Env.ofTable tbl)
        rBt rAsg rPI r8 (er 11 rfl (fun _ _ _ _ h => h)) r4)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_finish_m6_wp (Env.ofTable tbl)
        r8 (er 5 rfl (fun _ _ _ _ h => h)) rBt r4 (er 10 rfl (fun _ _ _ _ h => h))
        (er 12 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_counts_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_has_l0_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_l0_simp_m6_wp (Env.ofTable tbl)
        (er 15 rfl (fun _ _ _ _ h => h)) rBt (er 3 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_reuse_prefix_m6_wp (Env.ofTable tbl) rBt)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clause_m6_wp (Env.ofTable tbl)
        (er 16 rfl (fun _ _ _ _ h => h)) (er 14 rfl (fun _ _ _ _ h => h))
        (er 17 rfl (fun _ _ _ _ h => h)) (er 9 rfl (fun _ _ _ _ h => h)) rAsg rPI rBt
        (er 13 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_tier_match_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_collect_m6_wp (Env.ofTable tbl) rNext r19)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_count_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_keys_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_sort_sched_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_viv_clear_tier_m6_wp (Env.ofTable tbl) rNext r19)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_vivify_m6_wp (Env.ofTable tbl)
        rBt (er 20 rfl (fun _ _ _ _ h => h)) (er 21 rfl (fun _ _ _ _ h => h))
        (er 22 rfl (fun _ _ _ _ h => h)) (er 23 rfl (fun _ _ _ _ h => h))
        (er 18 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hProp)
        (er 24 rfl (fun _ _ _ _ h => h))), trivial ⟩

private theorem m6VivBb2Fns_eq :
    m6VivBb2Fns =
      [ ⟨"full_prioritize_binaries_m6", [i64], [.bool],
          FullM6VivBackbone.full_prioritize_binaries_m6_body⟩
      , ⟨"full_backbone_sched_m6", [i64], [i64], FullM6VivBackbone.full_backbone_sched_m6_body⟩
      , ⟨"full_backbone_keep_m6", [i64, i64], [], FullM6VivBackbone.full_backbone_keep_m6_body⟩
      , ⟨"full_backbone_unwind_m6", [i64, i64, i64], [],
          FullM6VivBackbone.full_backbone_unwind_m6_body⟩
      , ⟨"full_backbone_prop_m6", [i64, i64, .bool], [.bool],
          FullM6VivBackbone.full_backbone_prop_m6_body⟩
      , ⟨"full_backbone_analyze_m6", [i64, i32, i32, i64], [i32],
          FullM6VivBackbone.full_backbone_analyze_m6_body⟩
      , ⟨"full_backbone_round_m6", [i64, i64, .bool], [i64],
          FullM6VivBackbone.full_backbone_round_m6_body⟩
      , ⟨"full_backbone_m6", [i64, i64], [i64], FullM6VivBackbone.full_backbone_m6_body⟩
      , ⟨"full_trans_lit_m6", [i64, i32, .bool], [.bool], FullM6VivBackbone.full_trans_lit_m6_body⟩
      , ⟨"full_trans_sort_m6", [i64, i64], [], FullM6VivBackbone.full_trans_sort_m6_body⟩
      , ⟨"full_transitive_m6", [i64, i64], [i64], FullM6VivBackbone.full_transitive_m6_body⟩ ] :=
  rfl
theorem m6VivBb2_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6VivBb2Rows, e ∈ tbl)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl)
    (hDbs : ⟨"full_delete_bin_side", [i64, i32, i32], [], Full.fullDeleteBinSideSpec, true⟩ ∈ tbl)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6VivBb2Fns ∧ TableImpl (Env.ofTable tbl) m6VivBb2Fns m6VivBb2Rows := by
  have er := envRowAt hnd hown
  have rBt := envRow_mem hnd _ _ _ _ hBt; have rProp := envRow_mem hnd _ _ _ _ hProp
  have rAu := envRow_mem hnd _ _ _ _ hAu; have r0 := er 0 rfl (fun _ _ _ _ h => h)
  refine ⟨allFns_drop_take_wf FullM6VivBackbone.m6VivBackbone_fns_wf 29 11, ?_⟩
  rw [m6VivBb2Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6VivBackbone.full_prioritize_binaries_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_sched_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_keep_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_unwind_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_prop_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_analyze_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_round_m6_wp (Env.ofTable tbl)
        (er 4 rfl (fun _ _ _ _ h => h)) (er 5 rfl (fun _ _ _ _ h => h))
        (er 3 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_backbone_m6_wp (Env.ofTable tbl)
        rBt rProp rAu r0 (er 1 rfl (fun _ _ _ _ h => h)) (er 6 rfl (fun _ _ _ _ h => h))
        (er 2 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_trans_lit_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDbs) rAu)
    , SpecEntry.Impl.of (FullM6VivBackbone.full_trans_sort_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6VivBackbone.full_transitive_m6_wp (Env.ofTable tbl)
        rBt r0 (er 9 rfl (fun _ _ _ _ h => h)) (er 8 rfl (fun _ _ _ _ h => h)) rProp
        (envRow_mem hnd _ _ _ _ hDef)), trivial ⟩

/-! ## 7. Parametric `TableImpl` Transports — `FullM6CongSubst` (`23`) + `M3CongBva` (`3`) -/

theorem m6TarjanPopScc_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6TarjanPopSccRows, e ∈ tbl) :
    AllFns Fn.Wf m6TarjanPopSccFns ∧
    TableImpl (Env.ofTable tbl) m6TarjanPopSccFns m6TarjanPopSccRows :=
  fullSlice0_transport 120 1 (by t_kernel_rfl) hnd hown

theorem m6TarjanScc_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hPop : ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool],
      Full.fullTarjanPopSccSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6TarjanSccFns ∧ TableImpl (Env.ofTable tbl) m6TarjanSccFns m6TarjanSccRows :=
  oneImpl rfl rfl (allFns_drop_take_wf FullM6CongSubst.m6CongSubst_fns_wf 0 1)
    (FullM6CongSubst.full_tarjan_scc_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hPop))

theorem m6SubstElimVars_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl)
    (hEp2 : ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ ∈ tbl)
    (hSetIn : ⟨"full_set_inactive", [i64, i32, i32], [], Full.fullSetInactiveSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6SubstElimVarsFns ∧
    TableImpl (Env.ofTable tbl) m6SubstElimVarsFns m6SubstElimVarsRows :=
  oneImpl rfl rfl ⟨Full.full_subst_elim_vars_wf, trivial⟩
    (Full.full_subst_elim_vars_bridge_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hAu)
      (envRow_mem hnd _ _ _ _ hProp) (m6_extend_push2_tmk_to_canon (envRow_mem hnd _ _ _ _ hEp2))
      (envRow_mem hnd _ _ _ _ hSetIn))

private theorem m6SubstRewriteFns_eq :
    m6SubstRewriteFns =
      [ ⟨"full_subst_rewrite_bins", [i64], [.bool], FullM6CongSubst.full_subst_rewrite_bins_body⟩
      , ⟨"full_subst_rewrite_ar", [i64], [.bool], FullM6CongSubst.full_subst_rewrite_ar_body⟩
      , ⟨"full_substitute", [i64], [i64], FullM6CongSubst.full_substitute_body⟩ ] := rfl
theorem m6SubstRewrite_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6SubstRewriteRows, e ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl)
    (hAb : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl)
    (hBt : ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩ ∈ tbl)
    (hTar : ⟨"full_tarjan_scc", [i64], [i64], Full.fullTarjanSccSpec, true⟩ ∈ tbl)
    (hElim : ⟨"full_subst_elim_vars", [i64, i64], [.bool],
      Full.fullSubstElimVarsSpec, true⟩ ∈ tbl)
    (hSwp : ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6SubstRewriteFns ∧
    TableImpl (Env.ofTable tbl) m6SubstRewriteFns m6SubstRewriteRows := by
  have er := envRowAt hnd hown
  have rAu := envRow_mem hnd _ _ _ _ hAu
  have rAb := envRow_mem hnd _ _ _ _ hAb
  refine ⟨allFns_drop_take_wf FullM6CongSubst.m6CongSubst_fns_wf 1 3, ?_⟩
  rw [m6SubstRewriteFns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6CongSubst.full_subst_rewrite_bins_wp (Env.ofTable tbl) rAu rAb)
    , SpecEntry.Impl.of (FullM6CongSubst.full_subst_rewrite_ar_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hNext) rAu rAb)
    , SpecEntry.Impl.of (FullM6CongSubst.full_substitute_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hBt) (envRow_mem hnd _ _ _ _ hTar)
        (envRow_mem hnd _ _ _ _ hElim) (er 0 rfl (fun _ _ _ _ h => h))
        (er 1 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hSwp)
        (envRow_mem hnd _ _ _ _ hProp)), trivial ⟩

theorem m6RebuildWatches_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6RebuildWatchesRows, e ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl)
    (hSwp : ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6RebuildWatchesFns ∧
    TableImpl (Env.ofTable tbl) m6RebuildWatchesFns m6RebuildWatchesRows :=
  fullSliceTransport 127 1
    [ ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
    , ⟨"full_arena_sweep", [i64], [i64], Full.fullArenaSweepSpec, true⟩ ]
    (by t_kernel_rfl)
    (memC (fullRow_at 49 _) (mem1 (fullRow_at 60 _))) hnd hown (memC hProp (mem1 hSwp))

theorem m6CongFind_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6CongFindRows, e ∈ tbl) :
    AllFns Fn.Wf m6CongFindFns ∧ TableImpl (Env.ofTable tbl) m6CongFindFns m6CongFindRows :=
  fullSlice0_transport 128 1 (by t_kernel_rfl) hnd hown

theorem m6CongMerge_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hCf : ⟨"full_cong_find", [i64, i32], [i32], Full.fullCongFindSpec, true⟩ ∈ tbl)
    (hAb : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6CongMergeFns ∧ TableImpl (Env.ofTable tbl) m6CongMergeFns m6CongMergeRows :=
  oneImpl rfl rfl (allFns_drop_take_wf FullM6CongSubst.m6CongSubst_fns_wf 4 1)
    (FullM6CongSubst.full_cong_merge_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hCf) (m6_add_bin_to_cong (envRow_mem hnd _ _ _ _ hAb)))

theorem m6CongBva3_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6CongBva3Rows, e ∈ tbl)
    (hCf : ⟨"full_cong_find", [i64, i32], [i32], Full.fullCongFindSpec, true⟩ ∈ tbl)
    (hCm : ⟨"full_cong_merge", [i64, i32, i32], [.bool], Full.fullCongMergeSpec, true⟩ ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6CongBva3Fns ∧ TableImpl (Env.ofTable tbl) m6CongBva3Fns m6CongBva3Rows :=
  modTakeSliceTransport FullM3CongBva.m3_moduleOk FullM3CongBva.m3SpecTable_nodup (by t_kernel_rfl)
    0 3 (by decide)
    [ FullM3CongBva.m3SpecTable[11]'(by decide)
    , FullM3CongBva.m3SpecTable[12]'(by decide)
    , FullM3CongBva.m3SpecTable[14]'(by decide) ]
    (by t_kernel_rfl)
    (memC (List.getElem_mem _) <| memC (List.getElem_mem _) <| mem1 (List.getElem_mem _))
    hnd hown (memC hCf <| memC hCm <| mem1 hAu)

theorem m6HasTernary_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6HasTernaryFns ∧ TableImpl (Env.ofTable tbl) m6HasTernaryFns m6HasTernaryRows :=
  oneImpl rfl rfl (m5SliceWf 164 1) (FullM4InprocHot.full_has_ternary_m4_wp (Env.ofTable tbl))

theorem m6SortU32_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6SortU32Rows, e ∈ tbl) :
    AllFns Fn.Wf m6SortU32Fns ∧ TableImpl (Env.ofTable tbl) m6SortU32Fns m6SortU32Rows :=
  fullSlice0_transport 131 1 (by t_kernel_rfl) hnd hown

private theorem m6CongDenseFns_eq :
    m6CongDenseFns =
      [ ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64],
          FullM6CongSubst.full_cong_extract_ite_body⟩
      , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64],
          FullM6CongSubst.full_cong_emit_xor_body⟩
      , ⟨"full_cong_has_clause_k", [i64, i32], [.bool],
          FullM6CongSubst.full_cong_has_clause_k_body⟩
      , ⟨"full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64],
          FullM6CongSubst.full_cong_extract_xor_k_body⟩
      , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
          FullM6CongSubst.full_cong_try_xor_ite_body⟩
      , ⟨"full_cong_count_bins", [i64], [], FullM6CongSubst.full_cong_count_bins_body⟩
      , ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool],
          FullM6CongSubst.full_cong_eb_match_body⟩
      , ⟨"full_cong_extract_binaries", [i64, i64], [i64],
          FullM6CongSubst.full_cong_extract_binaries_body⟩
      , ⟨"full_cong_find_units_equivs", [i64], [i64],
          FullM6CongSubst.full_cong_find_units_equivs_body⟩
      , ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM6CongSubst.full_cong_extract_body⟩
      , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM6CongSubst.full_cong_and_match_body⟩
      , ⟨"full_cong_xor_match", [i64, i32, i32], [i32], FullM6CongSubst.full_cong_xor_match_body⟩
      , ⟨"full_cong_enq_var", [i64, i64, i32], [], FullM6CongSubst.full_cong_enq_var_body⟩
      , ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64],
          FullM6CongSubst.full_cong_eval_gate_body⟩
      , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
          FullM6CongSubst.full_cong_work_step_body⟩
      , ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64],
          FullM6CongSubst.full_cong_worklist_body⟩
      , ⟨"full_cong_fwd_subsume", [i64, i64], [i64], FullM6CongSubst.full_cong_fwd_subsume_body⟩
      , ⟨"full_congruence_dense", [i64, i64], [i64],
          FullM6CongSubst.full_congruence_dense_body⟩ ] := rfl
theorem m6CongDense_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6CongDenseRows, e ∈ tbl)
    (hTern : ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool],
      Full.fullHasTernarySpec, true⟩ ∈ tbl)
    (hSortU : ⟨"full_sort_u32", [i64, i32], [], Full.fullSortU32Spec, true⟩ ∈ tbl)
    (hHb : ⟨"full_has_bin", [i64, i32, i32], [.bool], Full.fullHasBinSpec, true⟩ ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hAb : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl)
    (hUf : ⟨"full_cong_unit_fold", [i64, i32, i32], [i64],
      FullM3CongBva.m3CongUnitFoldSpec, true⟩ ∈ tbl)
    (hEf : ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
      FullM3CongBva.m3CongEquivFoldSpec, true⟩ ∈ tbl)
    (hCf : ⟨"full_cong_find", [i64, i32], [i32], Full.fullCongFindSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6CongDenseFns ∧ TableImpl (Env.ofTable tbl) m6CongDenseFns m6CongDenseRows := by
  have er := envRowAt hnd hown
  have rTern := envRow_mem hnd _ _ _ _ hTern; have rSortU := envRow_mem hnd _ _ _ _ hSortU
  have rHb := envRow_mem hnd _ _ _ _ hHb; have rNext := envRow_mem hnd _ _ _ _ hNext
  have rCf := envRow_mem hnd _ _ _ _ hCf; have r0 := er 0 rfl (fun _ _ _ _ h => h)
  have r5 := er 5 rfl (fun _ _ _ _ h => h); have r13 := er 13 rfl (fun _ _ _ _ h => h)
  refine ⟨allFns_drop_take_wf FullM6CongSubst.m6CongSubst_fns_wf 5 18, ?_⟩
  rw [m6CongDenseFns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6CongSubst.full_cong_extract_ite_wp (Env.ofTable tbl) rTern)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_emit_xor_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_has_clause_k_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_extract_xor_k_wp (Env.ofTable tbl)
        rSortU (er 2 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_try_xor_ite_wp (Env.ofTable tbl)
        rTern (er 1 rfl (fun _ _ _ _ h => h)) r0)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_count_bins_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_eb_match_wp (Env.ofTable tbl) rHb)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_extract_binaries_wp (Env.ofTable tbl)
        rNext rHb (m6_add_bin_to_cong (envRow_mem hnd _ _ _ _ hAb)) r5
        (er 6 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_find_units_equivs_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hAu) (envRow_mem hnd _ _ _ _ hEf))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_extract_wp (Env.ofTable tbl)
        rNext rHb r5 (er 4 rfl (fun _ _ _ _ h => h)) (er 3 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_and_match_wp (Env.ofTable tbl) rCf)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_xor_match_wp (Env.ofTable tbl) rCf rSortU)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_enq_var_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_eval_gate_wp (Env.ofTable tbl)
        rCf rSortU (envRow_mem hnd _ _ _ _ hUf) (envRow_mem hnd _ _ _ _ hEf)
        (er 10 rfl (fun _ _ _ _ h => h)) (er 11 rfl (fun _ _ _ _ h => h))
        (er 12 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_work_step_wp (Env.ofTable tbl) rCf r13)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_worklist_wp (Env.ofTable tbl) rCf r13)
    , SpecEntry.Impl.of (FullM6CongSubst.full_cong_fwd_subsume_wp (Env.ofTable tbl)
        rNext rCf (envRow_mem hnd _ _ _ _ hAu))
    , SpecEntry.Impl.of (FullM6CongSubst.full_congruence_dense_wp (Env.ofTable tbl)
        (er 7 rfl (fun _ _ _ _ h => h)) (er 8 rfl (fun _ _ _ _ h => h))
        (er 9 rfl (fun _ _ _ _ h => h)) (er 15 rfl (fun _ _ _ _ h => h))
        (er 16 rfl (fun _ _ _ _ h => h))), trivial ⟩

/-! ## 8. Parametric `TableImpl` Transports — `Sweep`, `Kitten`, & `BveFwd` Split -/

theorem m6Sweep22_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6Sweep22Rows, e ∈ tbl)
    (hRng : ⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩ ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl)
    (hAb : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6Sweep22Fns ∧ TableImpl (Env.ofTable tbl) m6Sweep22Fns m6Sweep22Rows :=
  modTakeSliceTransport FullM4Sweep.fullM4SweepEnv_moduleOk FullM4Sweep.fullM4SweepSpecTable_nodup
    (by t_kernel_rfl) 0 22 (by decide)
    [ FullM4Sweep.fullM4SweepSpecTable[24]'(by decide)
    , FullM4Sweep.fullM4SweepSpecTable[27]'(by decide)
    , FullM4Sweep.fullM4SweepSpecTable[28]'(by decide) ]
    (by t_kernel_rfl)
    (memC (List.getElem_mem _) <| memC (List.getElem_mem _) <| mem1 (List.getElem_mem _))
    hnd hown (memC hRng <| memC hAu <| mem1 hAb)

theorem m6SweepDenseM5_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hVar : ⟨"full_m4_sweep_var", [i64, i32, i64], [i64],
      FullM4Sweep.m4SweepVarSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6SweepDenseM5Fns ∧
    TableImpl (Env.ofTable tbl) m6SweepDenseM5Fns m6SweepDenseM5Rows :=
  oneImpl rfl rfl ⟨FullM5Orch.full_sweep_dense_m5_wf, trivial⟩
    (FullM5Orch.full_sweep_dense_m5_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hVar))

theorem m6FwdDedupBins_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6FwdDedupBinsRows, e ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6FwdDedupBinsFns ∧
    TableImpl (Env.ofTable tbl) m6FwdDedupBinsFns m6FwdDedupBinsRows :=
  fullSliceTransport 145 1 [⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩]
    (by t_kernel_rfl) (mem1 (fullRow_at 102 _)) hnd hown (mem1 hAu)

private theorem m6BveFwd0Fns_eq :
    m6BveFwd0Fns =
      [ ⟨"full_dense_prop_unit_m6", [i64, i32], [.bool], FullM6BveFwd.full_dense_prop_unit_m6_body⟩
      , ⟨"full_dense_flush_units_m6", [i64], [.bool], FullM6BveFwd.full_dense_flush_units_m6_body⟩
      , ⟨"full_fwd_flush_large_m6", [i64], [], FullM6BveFwd.full_fwd_flush_large_m6_body⟩
      , ⟨"full_fwd_reconnect_irred_m6", [i64], [],
          FullM6BveFwd.full_fwd_reconnect_irred_m6_body⟩
      , ⟨"full_fwd_scan_lit_m6", [i64, i32, i32, i32, .bool], [i32],
          FullM6BveFwd.full_fwd_scan_lit_m6_body⟩
      , ⟨"full_fwd_check_cl_m6", [i64, i32], [.bool], FullM6BveFwd.full_fwd_check_cl_m6_body⟩
      , ⟨"full_fwd_connect_subsumer_m6", [i64, i32], [],
          FullM6BveFwd.full_fwd_connect_subsumer_m6_body⟩
      , ⟨"full_fwd_collect_sort_m6", [i64], [i64], FullM6BveFwd.full_fwd_collect_sort_m6_body⟩
      , ⟨"full_forward_sub_m6", [i64, i64], [i64], FullM6BveFwd.full_forward_sub_m6_body⟩
      , ⟨"full_bve_collect_m6", [i64, i32, i64, i32], [i32],
          FullM6BveFwd.full_bve_collect_m6_body⟩ ] := rfl
theorem m6BveFwd0_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BveFwd0Rows, e ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl)
    (hUnw : ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ ∈ tbl)
    (hAb : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl)
    (hDed : ⟨"full_fwd_dedup_bins", [i64], [.bool], Full.fullFwdDedupBinsSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BveFwd0Fns ∧ TableImpl (Env.ofTable tbl) m6BveFwd0Fns m6BveFwd0Rows := by
  have er := envRowAt hnd hown
  have rWp := envRow_mem hnd _ _ _ _ hWp; have rNext := envRow_mem hnd _ _ _ _ hNext
  have r1 := er 1 rfl FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit
  have r2 := er 2 rfl FullM6BveFwd.fullFwdFlushLargeM6Spec_noExit
  refine ⟨allFns_drop_take_wf FullM6BveFwd.m6BveFwd_fns_wf 0 10, ?_⟩
  rw [m6BveFwd0Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6BveFwd.full_dense_prop_unit_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hAu))
    , SpecEntry.Impl.of (FullM6BveFwd.full_dense_flush_units_m6_wp (Env.ofTable tbl)
        (er 0 rfl FullM6BveFwd.fullDensePropUnitM6Spec_noExit))
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_flush_large_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDef))
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_reconnect_irred_m6_wp (Env.ofTable tbl)
        r2 rNext rWp)
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_scan_lit_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_check_cl_m6_wp (Env.ofTable tbl)
        (er 4 rfl FullM6BveFwd.fullFwdScanLitM6Spec_noExit) (envRow_mem hnd _ _ _ _ hUnw)
        (envRow_mem hnd _ _ _ _ hAu) (envRow_mem hnd _ _ _ _ hAb) r1)
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_connect_subsumer_m6_wp (Env.ofTable tbl) rWp)
    , SpecEntry.Impl.of (FullM6BveFwd.full_fwd_collect_sort_m6_wp (Env.ofTable tbl) rNext)
    , SpecEntry.Impl.of (FullM6BveFwd.full_forward_sub_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hDed) r1 (er 7 rfl FullM6BveFwd.fullFwdCollectSortM6Spec_noExit)
        r2 (er 5 rfl FullM6BveFwd.fullFwdCheckClM6Spec_noExit)
        (er 6 rfl FullM6BveFwd.fullFwdConnectSubsumerM6Spec_noExit) rNext
        (er 3 rfl FullM6BveFwd.fullFwdReconnectIrredM6Spec_noExit))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_collect_m6_wp (Env.ofTable tbl)), trivial ⟩

theorem m6KittenInit_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6KittenInitFns ∧ TableImpl (Env.ofTable tbl) m6KittenInitFns m6KittenInitRows :=
  oneImpl rfl rfl (m5SliceWf 147 1) (FullM4InprocHot.full_kitten_init_m4_wp (Env.ofTable tbl))

theorem m6Kitten14_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6Kitten14Rows, e ∈ tbl) :
    AllFns Fn.Wf m6Kitten14Fns ∧ TableImpl (Env.ofTable tbl) m6Kitten14Fns m6Kitten14Rows :=
  modTakeSliceTransport Full.fullKittenEnv_moduleOk Full.fullKittenSpecTable_nodup
    (by t_kernel_rfl) 1 14 (by decide) [] (by t_kernel_rfl) (fun _ h => nomatch h)
    hnd hown (fun _ h => nomatch h)

theorem m6KittenDefFix5_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6KittenDefFix5Rows, e ∈ tbl)
    (hKw : ⟨"full_kitten_watch", [i64, i32, i32, i32], [], Full.fullKittenWatchSpec, true⟩ ∈ tbl)
    (hKa : ⟨"full_kitten_assign", [i64, i32, i32], [], Full.fullKittenAssignSpec, true⟩ ∈ tbl)
    (hKb : ⟨"full_kitten_backtrack", [i64, i32], [], Full.fullKittenBacktrackSpec, true⟩ ∈ tbl)
    (hKp : ⟨"full_kitten_propagate", [i64], [i32], Full.fullKittenPropagateSpec, true⟩ ∈ tbl)
    (hKan : ⟨"full_kitten_analyze", [i64, i32], [.bool], Full.fullKittenAnalyzeSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6KittenDefFix5Fns ∧
    TableImpl (Env.ofTable tbl) m6KittenDefFix5Fns m6KittenDefFix5Rows :=
  modTakeSliceTransport FullM5KittenDefFix.m5KittenDefFix_moduleOk
    FullM5KittenDefFix.m5KittenDefFixSpecTable_nodup (by t_kernel_rfl) 0 5 (by decide)
    [ FullM5KittenDefFix.m5KittenDefFixSpecTable[7]'(by decide)
    , FullM5KittenDefFix.m5KittenDefFixSpecTable[8]'(by decide)
    , FullM5KittenDefFix.m5KittenDefFixSpecTable[9]'(by decide)
    , FullM5KittenDefFix.m5KittenDefFixSpecTable[10]'(by decide)
    , FullM5KittenDefFix.m5KittenDefFixSpecTable[11]'(by decide) ]
    (by t_kernel_rfl)
    (memC (List.getElem_mem _) <| memC (List.getElem_mem _) <| memC (List.getElem_mem _) <|
      memC (List.getElem_mem _) <| mem1 (List.getElem_mem _))
    hnd hown (memC hKw <| memC hKa <| memC hKb <| memC hKp <| mem1 hKan)

theorem m6FindDefinition_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hInit : ⟨"full_kitten_init", [i64, i32, i32], [], Full.fullKittenInitSpec, true⟩ ∈ tbl)
    (hAddCl : ⟨"full_kitten_add_clause_m5", [i64, i32, i64, i32], [.bool],
      Full.fullKittenAddClauseSpec, true⟩ ∈ tbl)
    (hSolve : ⟨"full_kitten_solve_m5", [i64, i64], [i64], Full.fullKittenSolveSpec, true⟩ ∈ tbl)
    (hCore : ⟨"full_kitten_core_m5", [i64], [i32], Full.fullKittenCoreSpec, true⟩ ∈ tbl)
    (hShrink : ⟨"full_kitten_shrink", [i64], [], Full.fullKittenShrinkSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6FindDefinitionFns ∧
    TableImpl (Env.ofTable tbl) m6FindDefinitionFns m6FindDefinitionRows := by
  let Γ := Env.ofTable tbl
  let Γ' : Env := fun f as rs =>
    if f = "full_kitten_add_clause" then Γ "full_kitten_add_clause_m5" as rs
    else if f = "full_kitten_solve" then Γ "full_kitten_solve_m5" as rs
    else if f = "full_kitten_core" then Γ "full_kitten_core_m5" as rs
    else Γ f as rs
  exact oneImpl rfl rfl (m5SliceWf 211 1)
    (FullM5KittenDefFix.full_find_definition_m5_wp Γ FullM5KittenDefFix.fastKInv_laws_m5
      (FullFast.fast_kitten_init_adapter (envRow_mem hnd _ _ _ _ hInit))
      (FullFast.fast_kitten_add_clause_adapter (Γ := Γ') (envRow_mem hnd _ _ _ _ hAddCl))
      (FullFast.fast_kitten_solve_adapter (Γ := Γ') (envRow_mem hnd _ _ _ _ hSolve))
      (FullFast.fast_kitten_core_adapter (Γ := Γ') (envRow_mem hnd _ _ _ _ hCore))
      (FullFast.fast_kitten_shrink_adapter (envRow_mem hnd _ _ _ _ hShrink)))

private theorem m6BveFwd1Fns_eq :
    m6BveFwd1Fns =
      [ ⟨"full_bve_mark_and_m6", [i64, i32, i32, i32, i32, i32], [.bool],
          FullM6BveFwd.full_bve_mark_and_m6_body⟩
      , ⟨"full_bve_get_tern_m6", [i64, i32, i32, i32], [.bool],
          FullM6BveFwd.full_bve_get_tern_m6_body⟩
      , ⟨"full_bve_match_tern_m6", [i64, i32, i32, i32, i32, i32], [i32],
          FullM6BveFwd.full_bve_match_tern_m6_body⟩
      , ⟨"full_bve_find_ite_m6", [i64, i32, i32, i32], [.bool],
          FullM6BveFwd.full_bve_find_ite_m6_body⟩
      , ⟨"full_bve_gates_m6", [i64, i32, i32, i32], [], FullM6BveFwd.full_bve_gates_m6_body⟩
      , ⟨"full_bve_var_m6", [i64, i32], [i64], FullM6BveFwd.full_bve_var_m6_body⟩ ] := rfl
theorem m6BveFwd1_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BveFwd1Rows, e ∈ tbl)
    (hFindDef : ⟨"full_find_definition", [i64, i32, i32, i32], [],
      FullDefSweep.fullFindDefinitionSpec, true⟩ ∈ tbl)
    (hBveColM6 : ⟨"full_bve_collect_m6", [i64, i32, i64, i32], [i32],
      Full.fullBveCollectSpec, true⟩ ∈ tbl)
    (hExtNeed : ⟨"full_bve_ext_need", [i64, i32, i32], [i64], Full.fullBveExtNeedSpec, true⟩ ∈ tbl)
    (hWeaken : ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
      FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩ ∈ tbl)
    (hSetIn : ⟨"full_set_inactive", [i64, i32, i32], [], Full.fullSetInactiveSpec, true⟩ ∈ tbl)
    (hResPair : ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool],
      Full.fullBveResolvePairSpec, true⟩ ∈ tbl)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl)
    (hCommit : ⟨"full_bve_commit_res", [i64, i64, i64], [i64],
      FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩ ∈ tbl)
    (hFlushU : ⟨"full_dense_flush_units_m6", [i64], [.bool],
      FullM6BveFwd.fullDenseFlushUnitsM6Spec, true⟩ ∈ tbl)
    (hTryBce : ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool],
      Full.fullBveTryBceSpec, true⟩ ∈ tbl)
    (hEp2 : ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ ∈ tbl)
    (hDelBin : ⟨"full_delete_binary", [i64, i32, i32], [], Full.fullDeleteBinarySpec, true⟩ ∈ tbl)
    (hEpCl : ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BveFwd1Fns ∧ TableImpl (Env.ofTable tbl) m6BveFwd1Fns m6BveFwd1Rows := by
  have er := envRowAt hnd hown
  have rGt := er 1 rfl FullM6BveFwd.fullBveGetTernM6Spec_noExit
  refine ⟨allFns_drop_take_wf FullM6BveFwd.m6BveFwd_fns_wf 10 6, ?_⟩
  rw [m6BveFwd1Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6BveFwd.full_bve_mark_and_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_get_tern_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_match_tern_m6_wp (Env.ofTable tbl) rGt)
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_find_ite_m6_wp (Env.ofTable tbl) rGt
        (er 2 rfl FullM6BveFwd.fullBveMatchTernM6Spec_noExit))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_gates_m6_wp (Env.ofTable tbl)
        (er 0 rfl FullM6BveFwd.fullBveMarkAndM6Spec_noExit)
        (er 3 rfl FullM6BveFwd.fullBveFindIteM6Spec_noExit) (envRow_mem hnd _ _ _ _ hFindDef))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_var_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hBveColM6) (envRow_mem hnd _ _ _ _ hExtNeed)
        (envRow_mem hnd _ _ _ _ hWeaken) (envRow_mem hnd _ _ _ _ hSetIn)
        (er 4 rfl FullM6BveFwd.fullBveGatesM6Spec_noExit)
        (envRow_mem hnd _ _ _ _ hResPair) (envRow_mem hnd _ _ _ _ hDef)
        (envRow_mem hnd _ _ _ _ hCommit)
        (envRow_mem hnd _ _ _ _ hFlushU FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit)
        (envRow_mem hnd _ _ _ _ hTryBce) (envRow_mem hnd _ _ _ _ hEp2)
        (envRow_mem hnd _ _ _ _ hDelBin) (envRow_mem hnd _ _ _ _ hEpCl)), trivial ⟩

theorem m6BveCollect_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BveCollectRows, e ∈ tbl) :
    AllFns Fn.Wf m6BveCollectFns ∧ TableImpl (Env.ofTable tbl) m6BveCollectFns m6BveCollectRows :=
  fullSlice0_transport 148 1 (by t_kernel_rfl) hnd hown

theorem m6BveResPair_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BveResPairRows, e ∈ tbl) :
    AllFns Fn.Wf m6BveResPairFns ∧ TableImpl (Env.ofTable tbl) m6BveResPairFns m6BveResPairRows :=
  fullSlice0_transport 151 1 (by t_kernel_rfl) hnd hown

theorem m6BveWeaken_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hEp2 : ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ ∈ tbl)
    (hDelBin : ⟨"full_delete_binary", [i64, i32, i32], [], Full.fullDeleteBinarySpec, true⟩ ∈ tbl)
    (hEpCl : ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BveWeakenFns ∧ TableImpl (Env.ofTable tbl) m6BveWeakenFns m6BveWeakenRows :=
  oneImpl rfl rfl ⟨Full.full_bve_weaken_wf, trivial⟩
    (FullFast.fast_bve_weaken_tmk_wp (Env.ofTable tbl)
      (envRow_mem hnd _ _ _ _ hEp2) (envRow_mem hnd _ _ _ _ hDelBin) (envRow_mem hnd _ _ _ _ hEpCl))

theorem m6BveTryBce_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BveTryBceRows, e ∈ tbl) :
    AllFns Fn.Wf m6BveTryBceFns ∧ TableImpl (Env.ofTable tbl) m6BveTryBceFns m6BveTryBceRows :=
  fullSlice0_transport 153 1 (by t_kernel_rfl) hnd hown

theorem m6BveCommitRes_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hAlloc : ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl)
    (hAb : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl)
    (hAu : ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BveCommitResFns ∧
    TableImpl (Env.ofTable tbl) m6BveCommitResFns m6BveCommitResRows :=
  oneImpl rfl rfl ⟨Full.full_bve_commit_res_wf, trivial⟩
    (FullFast.fast_bve_commit_res_tmk_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hAlloc)
      (envRow_mem hnd _ _ _ _ hWp) (envRow_mem hnd _ _ _ _ hAb) (envRow_mem hnd _ _ _ _ hAu))

theorem m6BveExtNeed_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BveExtNeedRows, e ∈ tbl) :
    AllFns Fn.Wf m6BveExtNeedFns ∧ TableImpl (Env.ofTable tbl) m6BveExtNeedFns m6BveExtNeedRows :=
  fullSlice0_transport 155 1 (by t_kernel_rfl) hnd hown

/-! ## 9. `TableImpl` Transports — `BVA`, `Compact`, `Reorder`, `Bce`, `BveFwd[16..23]` -/

theorem m6InitFreshVarM6_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6InitFreshVarM6Fns ∧
    TableImpl (Env.ofTable tbl) m6InitFreshVarM6Fns m6InitFreshVarM6Rows :=
  oneImpl rfl rfl (allFns_drop_take_wf FullM6VivBackbone.m6VivBackbone_fns_wf 1 1)
    (FullM6VivBackbone.full_init_fresh_var_m6_wp (Env.ofTable tbl))

theorem m6BvaHop_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BvaHopRows, e ∈ tbl) :
    AllFns Fn.Wf m6BvaHopFns ∧ TableImpl (Env.ofTable tbl) m6BvaHopFns m6BvaHopRows :=
  modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
    0 3 (by decide) [] (by t_kernel_rfl) (fun _ h => nomatch h) hnd hown (fun _ h => nomatch h)

theorem m6BvaMatchLarge_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6BvaMatchLargeFns ∧
    TableImpl (Env.ofTable tbl) m6BvaMatchLargeFns m6BvaMatchLargeRows :=
  oneImpl rfl rfl (m5SliceWf 223 1) (FullBvaHeap.full_bva_match_large_wp (Env.ofTable tbl))

theorem m6BvaScanCands_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6BvaScanCandsFns ∧
    TableImpl (Env.ofTable tbl) m6BvaScanCandsFns m6BvaScanCandsRows :=
  oneImpl rfl rfl (m5SliceWf 224 1) (FullM4Bva.m4_bva_scan_cands_wp (Env.ofTable tbl))

theorem m6BvaPickCand_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6BvaPickCandFns ∧
    TableImpl (Env.ofTable tbl) m6BvaPickCandFns m6BvaPickCandRows :=
  oneImpl rfl rfl ⟨FullM6BvaNoHops.full_bva_pick_cand_no_hops_wf, trivial⟩
    (FullM6BvaNoHops.m6_bva_pick_cand_no_hops_wp (Env.ofTable tbl))

theorem m6BvaFilterRow_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BvaFilterRowRows, e ∈ tbl)
    (hMatch : ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool],
      FullBvaHeap.fullBvaMatchLargeSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BvaFilterRowFns ∧
    TableImpl (Env.ofTable tbl) m6BvaFilterRowFns m6BvaFilterRowRows :=
  modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
    4 1 (by decide) [FullM4Bva.m4BvaSpecTable[19]'(by decide)] (by t_kernel_rfl)
    (mem1 (List.getElem_mem _)) hnd hown (mem1 hMatch)

theorem m6BvaCommit_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl)
    (hIfv : ⟨"full_init_fresh_var", [i64, i32], [],
      FullBvaHeap.fullInitFreshVarHeapSpec, true⟩ ∈ tbl)
    (hAb : ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ∈ tbl)
    (hAl : ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], Full.fullAllocClSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl)
    (hDel : ⟨"full_delete_binary", [i64, i32, i32], [], Full.fullDeleteBinarySpec, true⟩ ∈ tbl)
    (hUnw : ⟨"full_unwatch_large", [i64, i32, i32], [], Full.fullUnwatchLargeSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BvaCommitFns ∧ TableImpl (Env.ofTable tbl) m6BvaCommitFns m6BvaCommitRows :=
  oneImpl rfl rfl (m5SliceWf 227 1)
    (FullM5DenseSafe.full_bva_commit_m5_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hDef)
      (envRow_mem hnd _ _ _ _ hIfv) (envRow_mem hnd _ _ _ _ hAb) (envRow_mem hnd _ _ _ _ hAl)
      (envRow_mem hnd _ _ _ _ hWp) (envRow_mem hnd _ _ _ _ hDel) (envRow_mem hnd _ _ _ _ hUnw))

theorem m6BvaTryLit_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BvaTryLitRows, e ∈ tbl)
    (hPick : ⟨"full_bva_pick_cand", [i64, i32, i32], [i32],
      FullBvaHeap.fullBvaPickCandSpec, true⟩ ∈ tbl)
    (hFilt : ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullM4Bva.m4BvaFilterRowSpec, true⟩ ∈ tbl)
    (hCom : ⟨"full_bva_commit", [i64, i32], [.bool], FullM4Bva.m4BvaCommitSpec, true⟩ ∈ tbl)
    (hScan : ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      FullM4Bva.m4BvaScanCandsSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BvaTryLitFns ∧ TableImpl (Env.ofTable tbl) m6BvaTryLitFns m6BvaTryLitRows :=
  modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
    6 1 (by decide)
    [ FullM4Bva.m4BvaSpecTable[3]'(by decide), FullM4Bva.m4BvaSpecTable[4]'(by decide)
    , FullM4Bva.m4BvaSpecTable[5]'(by decide), FullM4Bva.m4BvaSpecTable[20]'(by decide) ]
    (by t_kernel_rfl)
    (memC (List.getElem_mem _) <| memC (List.getElem_mem _) <| memC (List.getElem_mem _) <|
      mem1 (List.getElem_mem _))
    hnd hown (memC hPick <| memC hFilt <| memC hCom <| mem1 hScan)

private theorem m6FheapPairFns_eq :
    m6FheapPairFns =
      [ ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.full_fheap_up_body⟩
      , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.full_fheap_down_body⟩ ] :=
  rfl
theorem m6FheapPair_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6FheapPairFns ∧ TableImpl (Env.ofTable tbl) m6FheapPairFns m6FheapPairRows := by
  refine ⟨m5SliceWf 229 2, ?_⟩
  rw [m6FheapPairFns_eq]
  exact ⟨ SpecEntry.Impl.of (FullBvaHeap.full_fheap_up_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullBvaHeap.full_fheap_down_wp (Env.ofTable tbl)), trivial ⟩

theorem m6Factor_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6FactorRows, e ∈ tbl)
    (hTry : ⟨"full_bva_try_lit", [i64, i32, i64], [.bool],
      FullBvaHeap.fullBvaTryLitHeapSpec, true⟩ ∈ tbl)
    (hUp : ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩ ∈ tbl)
    (hDn : ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [],
      FullBvaHeap.fullFheapDownSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6FactorFns ∧ TableImpl (Env.ofTable tbl) m6FactorFns m6FactorRows :=
  modTakeSliceTransport FullM4Bva.m4Bva_moduleOk m4BvaSpecTable_nodup (by t_kernel_rfl)
    7 1 (by decide)
    [ FullM4Bva.m4BvaSpecTable[6]'(by decide)
    , FullM4Bva.m4BvaSpecTable[21]'(by decide)
    , FullM4Bva.m4BvaSpecTable[22]'(by decide) ]
    (by t_kernel_rfl)
    (memC (List.getElem_mem _) <| memC (List.getElem_mem _) <| mem1 (List.getElem_mem _))
    hnd hown (memC hTry <| memC hUp <| mem1 hDn)

theorem m6Compact10_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6Compact10Rows, e ∈ tbl)
    (hFl : ⟨"full_compact_flush", [i64], [i64], FullM4Compact.fullCompactFlushSpec, true⟩ ∈ tbl)
    (hMl : ⟨"full_compact_mark_live", [i64], [], FullM4Compact.fullCompactMarkLiveSpec, true⟩ ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl)
    (hDef : ⟨"full_wstack_defrag", [i64], [], Full.fullWstackDefragSpec, true⟩ ∈ tbl)
    (hWp : ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool],
      Full.fullWatchPushSpec, true⟩ ∈ tbl)
    (hRew : ⟨"full_rewatch_arena", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6Compact10Fns ∧ TableImpl (Env.ofTable tbl) m6Compact10Fns m6Compact10Rows :=
  modTakeSliceTransport FullM4Compact.compact_moduleOk FullM4Compact.compactSpecTable_nodup
    (by t_kernel_rfl) 3 10 (by decide)
    [ FullM4Compact.compactSpecTable[1]'(by decide), FullM4Compact.compactSpecTable[2]'(by decide)
    , FullM4Compact.compactSpecTable[13]'(by decide), FullM4Compact.compactSpecTable[14]'(by decide)
    , FullM4Compact.compactSpecTable[15]'(by decide)
    , FullM4Compact.compactSpecTable[18]'(by decide) ]
    (by t_kernel_rfl)
    (memC (List.getElem_mem _) <| memC (List.getElem_mem _) <| memC (List.getElem_mem _) <|
      memC (List.getElem_mem _) <| memC (List.getElem_mem _) <| mem1 (List.getElem_mem _))
    hnd hown (memC hFl <| memC hMl <| memC hNext <| memC hDef <| memC hWp <| mem1 hRew)

private theorem m6ReorderFns_eq :
    m6ReorderFns =
      [ ⟨"full_reorder_weight_m7", [i64], [i64], FullM7Reorder.full_reorder_weight_m7_body⟩
      , ⟨"full_reorder_sift_m7", [i64, i64, i64], [], FullM7Reorder.full_reorder_sift_m7_body⟩
      , ⟨"full_reorder_queue_m7", [i64], [i64], FullM7Reorder.full_reorder_queue_m7_body⟩ ] := rfl
theorem m6Reorder_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6ReorderRows, e ∈ tbl)
    (hNext : ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6ReorderFns ∧ TableImpl (Env.ofTable tbl) m6ReorderFns m6ReorderRows := by
  have er := envRowAt hnd hown
  refine ⟨allFns_of_mem (allFns_wf_of_moduleOk FullM7Reorder.m7Reorder_moduleOk), ?_⟩
  rw [m6ReorderFns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM7Reorder.full_reorder_weight_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Reorder.full_reorder_sift_m7_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM7Reorder.full_reorder_queue_m7_wp (Env.ofTable tbl)
        (er 0 rfl (fun _ _ _ _ h => FullM7Reorder.m7ReorderWeightSpec_noExit h))
        (envRow_mem hnd _ _ _ _ hNext)
        (er 1 rfl (fun _ _ _ _ h => FullM7Reorder.m7ReorderSiftSpec_noExit h))), trivial ⟩

private theorem m6VivBce4Fns_eq :
    m6VivBce4Fns =
      [ ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32],
          FullM4VivBce.full_bce_side_m4_body⟩
      , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], FullM4VivBce.full_bce_pair_m4_body⟩
      , ⟨"full_bce_var_m4", [i64, i32], [], FullM4VivBce.full_bce_var_m4_body⟩
      , ⟨"full_bce_m4", [i64, i64], [i64], FullM4VivBce.full_bce_m4_body⟩ ] := rfl
theorem m6VivBce4_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6VivBce4Rows, e ∈ tbl)
    (hBce : ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool],
      Full.fullBveTryBceSpec, true⟩ ∈ tbl)
    (hEp2 : ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ ∈ tbl)
    (hEpCl : ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩ ∈ tbl)
    (hDelBin : ⟨"full_delete_binary", [i64, i32, i32], [], Full.fullDeleteBinarySpec, true⟩ ∈ tbl)
    (hCol : ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], Full.fullBveCollectSpec, true⟩ ∈ tbl)
    (hEd : ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩ ∈ tbl)
    (hReb : ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩ ∈ tbl)
    (hProp : ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6VivBce4Fns ∧ TableImpl (Env.ofTable tbl) m6VivBce4Fns m6VivBce4Rows := by
  have er := envRowAt hnd hown
  refine ⟨allFns_drop_take_wf (allFns_wf_of_moduleOk FullM4VivBce.m4VivBce_moduleOk) 12 4, ?_⟩
  rw [m6VivBce4Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM4VivBce.full_bce_side_m4_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hBce)
        (m6_extend_push2_tmk_to_canon (envRow_mem hnd _ _ _ _ hEp2))
        (m6_extend_push_cl_tmk_to_canon (envRow_mem hnd _ _ _ _ hEpCl))
        (envRow_mem hnd _ _ _ _ hDelBin))
    , SpecEntry.Impl.of (FullM4VivBce.full_bce_pair_m4_wp (Env.ofTable tbl)
        (er 0 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM4VivBce.full_bce_var_m4_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hCol) (er 1 rfl (fun _ _ _ _ h => h)))
    , SpecEntry.Impl.of (FullM5.m5_bce_m4_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hEd)
        (er 2 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hReb)
        (envRow_mem hnd _ _ _ _ hProp)), trivial ⟩

private theorem m6SchedMinMaxFns_eq :
    m6SchedMinMaxFns =
      [ ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.full_min_u64_body⟩
      , ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.full_max_u64_body⟩ ] := rfl
theorem m6SchedMinMax_transport {tbl : List SpecEntry} (_ : (tbl.map SpecEntry.name).Nodup) :
    AllFns Fn.Wf m6SchedMinMaxFns ∧
    TableImpl (Env.ofTable tbl) m6SchedMinMaxFns m6SchedMinMaxRows := by
  refine ⟨m5SliceWf 252 2, ?_⟩
  rw [m6SchedMinMaxFns_eq]
  exact ⟨ SpecEntry.Impl.of (FullFastSched.sched_min_u64_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullFastSched.sched_max_u64_wp (Env.ofTable tbl)), trivial ⟩

theorem m6ElimDticks_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hMax : ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6ElimDticksFns ∧ TableImpl (Env.ofTable tbl) m6ElimDticksFns m6ElimDticksRows :=
  oneImpl rfl rfl ⟨FullM5Orch.full_elim_dticks_m5_wf, trivial⟩
    (FullM5Orch.full_elim_dticks_m5_wp (Env.ofTable tbl) (envRow_mem hnd _ _ _ _ hMax))

private theorem m6BveFwd2Fns_eq :
    m6BveFwd2Fns =
      [ ⟨"full_bve_var_key_m6", [i64, i32], [i64], FullM6BveFwd.full_bve_var_key_m6_body⟩
      , ⟨"full_bve_heap_up_m6", [i64, i64, i32], [], FullM6BveFwd.full_bve_heap_up_m6_body⟩
      , ⟨"full_bve_heap_down_m6", [i64, i64, i32], [], FullM6BveFwd.full_bve_heap_down_m6_body⟩
      , ⟨"full_bve_heap_push_m6", [i64, i64, i32], [i64], FullM6BveFwd.full_bve_heap_push_m6_body⟩
      , ⟨"full_bve_heap_pop_m6", [i64, i64], [i32], FullM6BveFwd.full_bve_heap_pop_m6_body⟩
      , ⟨"full_bve_collect_nbrs_m6", [i64, i32], [i64],
          FullM6BveFwd.full_bve_collect_nbrs_m6_body⟩
      , ⟨"full_elim_bve_m6", [i64, i64], [i64], FullM6BveFwd.full_elim_bve_m6_body⟩
      , ⟨"full_eliminate_m6", [i64, .bool], [i64], FullM6BveFwd.full_eliminate_m6_body⟩ ] := rfl
theorem m6BveFwd2_transport {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hown : ∀ e ∈ m6BveFwd2Rows, e ∈ tbl)
    (hFlushU : ⟨"full_dense_flush_units_m6", [i64], [.bool],
      FullM6BveFwd.fullDenseFlushUnitsM6Spec, true⟩ ∈ tbl)
    (hBveVar : ⟨"full_bve_var_m6", [i64, i32], [i64],
      FullFastBveBudgets.fullBveVarDefSpec, true⟩ ∈ tbl)
    (hElimDt : ⟨"full_elim_dticks", [i64, .bool], [i64],
      FullFastSched.schedElimDticksSpec, true⟩ ∈ tbl)
    (hIlog : ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩ ∈ tbl)
    (hScale : ⟨"full_scale_delta", [i64, i64], [i64],
      FullFastSched.schedScaleDeltaSpec, true⟩ ∈ tbl)
    (hEd : ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩ ∈ tbl)
    (hMinU : ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩ ∈ tbl)
    (hFwdSub : ⟨"full_forward_sub_m6", [i64, i64], [i64],
      FullFastBveBudgets.fullForwardSubFastSpec, true⟩ ∈ tbl)
    (hFactor : ⟨"full_factor", [i64, i64], [i64], FullM3CongBva.fullFactorHeapSpec, true⟩ ∈ tbl)
    (hReb : ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩ ∈ tbl) :
    AllFns Fn.Wf m6BveFwd2Fns ∧ TableImpl (Env.ofTable tbl) m6BveFwd2Fns m6BveFwd2Rows := by
  have er := envRowAt hnd hown
  have rDown := er 2 rfl FullM6BveFwd.fullBveHeapDownM6Spec_noExit
  refine ⟨allFns_drop_take_wf FullM6BveFwd.m6BveFwd_fns_wf 16 8, ?_⟩
  rw [m6BveFwd2Fns_eq]
  exact ⟨ SpecEntry.Impl.of (FullM6BveFwd.full_bve_var_key_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_heap_up_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_heap_down_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_heap_push_m6_wp (Env.ofTable tbl)
        (er 0 rfl FullM6BveFwd.fullBveVarKeyM6Spec_noExit)
        (er 1 rfl FullM6BveFwd.fullBveHeapUpM6Spec_noExit) rDown)
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_heap_pop_m6_wp (Env.ofTable tbl) rDown)
    , SpecEntry.Impl.of (FullM6BveFwd.full_bve_collect_nbrs_m6_wp (Env.ofTable tbl))
    , SpecEntry.Impl.of (FullM6BveFwd.full_elim_bve_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hFlushU FullM6BveFwd.fullDenseFlushUnitsM6Spec_noExit)
        (er 3 rfl FullM6BveFwd.fullBveHeapPushM6Spec_noExit)
        (er 4 rfl FullM6BveFwd.fullBveHeapPopM6Spec_noExit)
        (er 5 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hBveVar))
    , SpecEntry.Impl.of (FullM6BveFwd.full_eliminate_m6_wp (Env.ofTable tbl)
        (envRow_mem hnd _ _ _ _ hElimDt) (envRow_mem hnd _ _ _ _ hIlog)
        (envRow_mem hnd _ _ _ _ hScale) (envRow_mem hnd _ _ _ _ hEd)
        (envRow_mem hnd _ _ _ _ hMinU) (envRow_mem hnd _ _ _ _ hFwdSub)
        (er 6 rfl (fun _ _ _ _ h => h)) (envRow_mem hnd _ _ _ _ hFactor)
        (envRow_mem hnd _ _ _ _ hReb)), trivial ⟩

end LeanQbe.T.Examples.Kissat.FullM6Transport

