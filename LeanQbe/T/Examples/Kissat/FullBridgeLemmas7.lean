module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.DimacsLemmas
import LeanQbe.T.Examples.Kissat.FullTransLemmas
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas7a
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Part A (`22` fns, `Stage 4`)

Bridges `22` functions across four landed Stage-4 families onto canonical `FullSpec` table rows
(`fullSpecTable fullSolveBytesSpec` / `fullEnv`):
- Part 1 (`DimacsLemmas{1,}`, `8` fns, indices `0..7`): `kissat_is_ws`, `kissat_is_digit`,
  `kissat_skip_ws_comments`, `kissat_skip_ws1`, `kissat_read_nat`, `kissat_parse_header`,
  `kissat_next_lit`, `kissat_check_model`.
- Part 2 (`FullTransLemmas`, `2` fns, indices `112..113`): `full_trans_lit`, `full_transitive`.
- Part 3 (`FullVivifyLemmas{1,2,3,}` + `FullVivTopLemmas`, `6` fns, indices `114..119`):
  `full_viv_simplify`, `full_viv_sort_lits`, `full_viv_deduce`, `full_viv_commit`,
  `full_viv_clause`, `full_vivify`.
- Part 4 (`FullBvaFwdLemmas{2,3,}`, `6` fns, indices `145..147, 157..159`): `full_fwd_dedup_bins`,
  `full_fwd_check_cl`, `full_forward_sub`, `full_init_fresh_var`, `full_bva_try_lit`,
  `full_factor`.
- Part 5: index-verified `SpecEntry.Impl fullEnv` summary theorem `full_bridge_7_ok` (and
  `mainSpec`-parametric `full_bridge_7_mk_ok`) covering all `22` functions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## Part 1: `DimacsLemmas` (`8` fns) -/

section Part1

theorem kissat_is_ws_bridge_wp (Γ : Env) :
    ∀ a m Q X, kissatIsWsSpec a m Q X → Func.wp Γ kissat_is_ws_body a m Q X :=
  kissat_is_ws_wp Γ

theorem kissat_is_digit_bridge_wp (Γ : Env) :
    ∀ a m Q X, kissatIsDigitSpec a m Q X → Func.wp Γ kissat_is_digit_body a m Q X :=
  kissat_is_digit_wp Γ

theorem kissat_skip_ws_comments_bridge_wp (Γ : Env)
    (hWs : ∀ a m Q X, kissatIsWsSpec a m Q X → Γ "kissat_is_ws" [i64] [.bool] a m Q X) :
    ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Func.wp Γ kissat_skip_ws_comments_body a m Q X :=
  kissat_skip_ws_comments_wp Γ hWs

theorem kissat_skip_ws1_bridge_wp (Γ : Env)
    (hWs : ∀ a m Q X, kissatIsWsSpec a m Q X → Γ "kissat_is_ws" [i64] [.bool] a m Q X) :
    ∀ a m Q X, kissatSkipWs1Spec a m Q X → Func.wp Γ kissat_skip_ws1_body a m Q X :=
  kissat_skip_ws1_wp Γ hWs

theorem kissat_read_nat_bridge_wp (Γ : Env)
    (hDig : ∀ a m Q X, kissatIsDigitSpec a m Q X → Γ "kissat_is_digit" [i64] [.bool] a m Q X)
    (hWs : ∀ a m Q X, kissatIsWsSpec a m Q X → Γ "kissat_is_ws" [i64] [.bool] a m Q X) :
    ∀ a m Q X, kissatReadNatSpec a m Q X → Func.wp Γ kissat_read_nat_body a m Q X :=
  kissat_read_nat_wp Γ hDig hWs

theorem kissat_parse_header_bridge_wp (Γ : Env)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X)
    (hWs1 : ∀ a m Q X, kissatSkipWs1Spec a m Q X →
      Γ "kissat_skip_ws1" [i64, i64] [.bool] a m Q X)
    (hNat : ∀ a m Q X, kissatReadNatSpec a m Q X →
      Γ "kissat_read_nat" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, kissatParseHeaderSpec a m Q X → Func.wp Γ kissat_parse_header_body a m Q X :=
  kissat_parse_header_wp Γ hSwc hWs1 hNat

theorem kissat_next_lit_bridge_wp (Γ : Env)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X)
    (hNat : ∀ a m Q X, kissatReadNatSpec a m Q X →
      Γ "kissat_read_nat" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, kissatNextLitSpec a m Q X → Func.wp Γ kissat_next_lit_body a m Q X :=
  kissat_next_lit_wp Γ hSwc hNat

theorem kissat_check_model_bridge_wp (Γ : Env)
    (hHdr : ∀ a m Q X, kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hLit : ∀ a m Q X, kissatNextLitSpec a m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, kissatCheckModelExactSpec a m Q X → Func.wp Γ kissat_check_model_body a m Q X :=
  kissat_check_model_exact_wp Γ hHdr hLit hSwc

end Part1

/-! ## Part 2: `FullTransLemmas` (`2` fns) -/

section Part2

theorem full_trans_lit_bridge_wp (Γ : Env)
    (hDelBin : ∀ a m Q X, fullDeleteBinSideSpec a m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullTransLitSpec a m Q X → Func.wp Γ full_trans_lit_body a m Q X :=
  full_trans_lit_wp Γ hDelBin hAddUnit

theorem full_transitive_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hTransLit : ∀ a m Q X, fullTransLitSpec a m Q X →
      Γ "full_trans_lit" [i64, i32] [.bool] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullTransitiveSpec a m Q X → Func.wp Γ full_transitive_body a m Q X :=
  full_transitive_wp Γ hBt hTransLit hProp hDefrag

end Part2

/-! ## Part 3: `FullVivifyLemmas` & `FullVivTopLemmas` (`6` fns) -/

section Part3

private theorem fullConflictOkW_to_viv {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflictOkW F_cur s) : FullVivifySpecs.FullVivConflictOk F_cur s :=
  h.elim (fun ⟨ht, h0, h1, hf0, hf1, hent⟩ => Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩) Or.inr

private theorem vivUnwatchLarge_adapter {Γ : Env}
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, FullVivifySpecs.fullVivUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X := by
  rintro ⟨h, lit, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hw, hm, hQ⟩
  have hlay : WatchStackLayout s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw
    have hdm : s.core.dense_mode = 0#64 := hsp.2.2.2.2
    simp only [hdm, ↓reduceIte] at hmw
    exact hmw.layout
  refine hUnwatch _ m Q X ⟨c, s, R, rfl, hsp.1.lengths, hlay, hm, ?_⟩
  dsimp only
  intro wvec' wstk' wu' m' hlen' _ hmode' hm'
  have hw' : FullWitnessInv c F0 F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu' } :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hmode' F_cur hw.watches }
  have hsp' : FullVivifySpecs.FullSparseInv c F0
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
    ⟨⟨hlen', F_cur, hw'⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩
  exact hQ wvec' wstk' wu' m' hsp' hw' hm'

private theorem vivAddUnit_adapter {Γ : Env}
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullVivifySpecs.fullVivAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hlit, hent, hm, hQ⟩
  refine hAddUnit _ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp.1, hsp.2.1, fun _ => hent, hm, ?_⟩
  dsimp only
  intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl0 hltf _ hm'
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', cur_level := cl', unassigned := unass',
                            unflushed := unfl', inconsistent := inc' }
      scratch := { s.scratch with phases := ph', target_assigned := ta', best_assigned := ba',
                                  phases_target := pt', phases_best := pb', heap := hp',
                                  pos := ps', heap_len := hl', q_search_idx := qsi',
                                  q_search_stamp := qss' } }
  have hsp' : FullVivifySpecs.FullSparseInvW c F0 F_cur s' :=
    ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
  exact hQ ok s' m' hsp' hcl0 rfl rfl rfl rfl rfl rfl (fun hf => (hltf hlit hf).1) hm'

private theorem vivAddBin_adapter {Γ : Env}
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, FullVivifySpecs.fullVivAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hext, hdm, hcl0, _ha, _hb, hent, hm, hQ⟩
  refine hAddBin _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, fun _ _ => hent, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
    ph' wso' m' hlen' hw' hr h20 _ hm'
  exact hQ r _ m' hlen' hr hw' hlm hext hdm rfl rfl rfl hcl0 rfl rfl (fun h => (h20 h).1) hm'

private theorem vivWatchPush_adapter {Γ : Env}
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullVivifySpecs.fullVivWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm, hQ⟩
  exact hWatchPush _ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm,
    fun ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' hoth hT hF hm' =>
      hQ ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' hoth hT (fun hf => (hF hf).1) hm'⟩

theorem full_viv_sort_lits_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullVivSortLitsSpec a m Q X → Func.wp Γ full_viv_sort_lits_body a m Q X :=
  full_viv_sort_lits_wp Γ

theorem full_viv_simplify_bridge_wp (Γ : Env)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullVivSimplifySpec a m Q X → Func.wp Γ full_viv_simplify_body a m Q X :=
  full_viv_simplify_wp Γ (vivUnwatchLarge_adapter hUnwatch) (vivAddUnit_adapter hAddUnit)
    (vivAddBin_adapter hAddBin) (vivWatchPush_adapter hWatchPush)

theorem full_viv_deduce_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullVivDeduceSpec a m Q X → Func.wp Γ full_viv_deduce_body a m Q X := by
  rintro ⟨h, cref, implied, out_ptr, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, rfl, hsp, href, hng, hconfl, himp, hm, hQ⟩
  exact full_viv_deduce_wp Γ _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, rfl, hsp, href, hng,
      fun hi => (hconfl hi).elim (Or.inl ∘ fullConflictOkW_to_viv) Or.inr, himp, hm, hQ⟩

theorem full_viv_commit_bridge_wp (Γ : Env)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullVivCommitSpec a m Q X → Func.wp Γ full_viv_commit_body a m Q X :=
  full_viv_commit_wp Γ (vivUnwatchLarge_adapter hUnwatch) (vivAddUnit_adapter hAddUnit)
    (vivAddBin_adapter hAddBin) (vivWatchPush_adapter hWatchPush)

end Part3

/-! ## Part 4: `FullBvaFwdLemmas` (`6` fns) -/

section Part4

theorem full_fwd_dedup_bins_bridge_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullFwdDedupBinsSpec a m Q X → Func.wp Γ full_fwd_dedup_bins_body a m Q X :=
  full_fwd_dedup_bins_wp Γ hAddUnit

theorem full_fwd_check_cl_bridge_wp (Γ : Env)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullFwdCheckClSpec a m Q X → Func.wp Γ full_fwd_check_cl_body a m Q X :=
  full_fwd_check_cl_wp Γ hUnwatch hAddUnit hAddBin

theorem full_forward_sub_bridge_wp (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hCheckCl : ∀ a m Q X, fullFwdCheckClSpec a m Q X →
      Γ "full_fwd_check_cl" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullForwardSubSpec a m Q X → Func.wp Γ full_forward_sub_body a m Q X :=
  full_forward_sub_wp Γ hDedup hNext hCheckCl

theorem full_init_fresh_var_bridge_wp (Γ : Env)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullInitFreshVarSpec a m Q X → Func.wp Γ full_init_fresh_var_body a m Q X :=
  full_init_fresh_var_wp Γ hHeapPush

theorem full_bva_try_lit_bridge_wp (Γ : Env)
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hInitFresh : ∀ a m Q X, fullInitFreshVarSpec a m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBvaTryLitSpec a m Q X → Func.wp Γ full_bva_try_lit_body a m Q X :=
  full_bva_try_lit_wp Γ hHasBin hInitFresh hAddBin hDelBin

theorem full_factor_bridge_wp (Γ : Env)
    (hTryLit : ∀ a m Q X, fullBvaTryLitSpec a m Q X →
      Γ "full_bva_try_lit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullFactorSpec a m Q X → Func.wp Γ full_factor_body a m Q X :=
  full_factor_wp Γ hTryLit

end Part4

/-! ## Part 5: Index-verified `SpecEntry.Impl fullEnv` summary (`22` fns) -/

section Part5

private theorem fullFns_nodup : (fullFns.map Fn.name).Nodup := by
  have hchk := full_acyclic
  simp only [fullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem fullSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((fullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (fullSpecTable mainSpec).map SpecEntry.name = fullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (fullSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]
  exact fullFns_nodup

private theorem mkFullEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (fullSpecTable_nodup mainSpec) (hno xs m Q X h)

/-- Canonical `fullFns` / `fullSpecTable` indices of the `22` functions bridged in Part A. -/
@[expose] def fullBridge7Indices : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 112, 113, 114, 115, 116, 117, 118, 119, 145, 146, 147, 157, 158, 159]

/-- Index-verified `SpecEntry.Impl (mkFullEnv mainSpec)` summary covering all `22` Part-A
functions (`Dimacs` `8`, `Transitive` `2`, `Vivification` `6`, `Fwd/BVA/Factor` `6`). -/
theorem full_bridge_7_mk_ok (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ n ∈ fullBridge7Indices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row := by
  let Γ := mkFullEnv mainSpec
  let hWs := mkFullEnv_row_at (mainSpec := mainSpec) 0
    ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  let hDig := mkFullEnv_row_at (mainSpec := mainSpec) 1
    ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  let hSwc := mkFullEnv_row_at (mainSpec := mainSpec) 2
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  let hWs1 := mkFullEnv_row_at (mainSpec := mainSpec) 3
    ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  let hNat := mkFullEnv_row_at (mainSpec := mainSpec) 4
    ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  let hHdr := mkFullEnv_row_at (mainSpec := mainSpec) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let hLit := mkFullEnv_row_at (mainSpec := mainSpec) 6
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  let hNext := mkFullEnv_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let hDefrag := mkFullEnv_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let hWPush := mkFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let hHeapPush := mkFullEnv_row_at (mainSpec := mainSpec) 18
    ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  let hAssign := mkFullEnv_row_at (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let hBt := mkFullEnv_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let hPropIgn := mkFullEnv_row_at (mainSpec := mainSpec) 48
    ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  let hProp := mkFullEnv_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let hUnwatch := mkFullEnv_row_at (mainSpec := mainSpec) 56
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let hHasBin := mkFullEnv_row_at (mainSpec := mainSpec) 97
    ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  let hAddBin := mkFullEnv_row_at (mainSpec := mainSpec) 98
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let hDelBinSide := mkFullEnv_row_at (mainSpec := mainSpec) 99
    ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  let hDelBin := mkFullEnv_row_at (mainSpec := mainSpec) 100
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  let hAddUnit := mkFullEnv_row_at (mainSpec := mainSpec) 102
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let hTransLit := mkFullEnv_row_at (mainSpec := mainSpec) 112
    ⟨"full_trans_lit", [i64, i32], [.bool], fullTransLitSpec, true⟩
  let hVivSimp := mkFullEnv_row_at (mainSpec := mainSpec) 114
    ⟨"full_viv_simplify", [i64, i32], [i64], fullVivSimplifySpec, true⟩
  let hVivSort := mkFullEnv_row_at (mainSpec := mainSpec) 115
    ⟨"full_viv_sort_lits", [i64, i64, i32], [], fullVivSortLitsSpec, true⟩
  let hVivDed := mkFullEnv_row_at (mainSpec := mainSpec) 116
    ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
  let hVivCom := mkFullEnv_row_at (mainSpec := mainSpec) 117
    ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64], fullVivCommitSpec, true⟩
  let hVivCl := mkFullEnv_row_at (mainSpec := mainSpec) 118
    ⟨"full_viv_clause", [i64, i32], [i64], fullVivClauseSpec, true⟩
  let hDedup := mkFullEnv_row_at (mainSpec := mainSpec) 145
    ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  let hCheckCl := mkFullEnv_row_at (mainSpec := mainSpec) 146
    ⟨"full_fwd_check_cl", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
  let hInitFresh := mkFullEnv_row_at (mainSpec := mainSpec) 157
    ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarSpec, true⟩
  let hTryLit := mkFullEnv_row_at (mainSpec := mainSpec) 158
    ⟨"full_bva_try_lit", [i64, i32], [.bool], fullBvaTryLitSpec, true⟩
  intro n hn
  simp only [fullBridge7Indices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨kissat_is_ws, _, rfl, rfl, .of (kissat_is_ws_bridge_wp Γ)⟩
  · exact ⟨kissat_is_digit, _, rfl, rfl, .of (kissat_is_digit_bridge_wp Γ)⟩
  · exact ⟨kissat_skip_ws_comments, _, rfl, rfl, .of (kissat_skip_ws_comments_bridge_wp Γ hWs)⟩
  · exact ⟨kissat_skip_ws1, _, rfl, rfl, .of (kissat_skip_ws1_bridge_wp Γ hWs)⟩
  · exact ⟨kissat_read_nat, _, rfl, rfl, .of (kissat_read_nat_bridge_wp Γ hDig hWs)⟩
  · exact ⟨kissat_parse_header, _, rfl, rfl, .of (kissat_parse_header_bridge_wp Γ hSwc hWs1 hNat)⟩
  · exact ⟨kissat_next_lit, _, rfl, rfl, .of (kissat_next_lit_bridge_wp Γ hSwc hNat)⟩
  · exact ⟨kissat_check_model, _, rfl, rfl, .of (kissat_check_model_bridge_wp Γ hHdr hLit hSwc)⟩
  · exact ⟨full_trans_lit, _, rfl, rfl, .of (full_trans_lit_bridge_wp Γ hDelBinSide hAddUnit)⟩
  · exact ⟨full_transitive, _, rfl, rfl,
      .of (full_transitive_bridge_wp Γ hBt hTransLit hProp hDefrag)⟩
  · exact ⟨full_viv_simplify, _, rfl, rfl,
      .of (full_viv_simplify_bridge_wp Γ hUnwatch hAddUnit hAddBin hWPush)⟩
  · exact ⟨full_viv_sort_lits, _, rfl, rfl, .of (full_viv_sort_lits_bridge_wp Γ)⟩
  · exact ⟨full_viv_deduce, _, rfl, rfl, .of (full_viv_deduce_bridge_wp Γ)⟩
  · exact ⟨full_viv_commit, _, rfl, rfl,
      .of (full_viv_commit_bridge_wp Γ hUnwatch hAddUnit hAddBin hWPush)⟩
  · exact ⟨full_viv_clause, _, rfl, rfl,
      .of (full_viv_clause_bridge_wp Γ hVivSimp hVivSort hAssign hPropIgn hBt hVivDed hVivCom)⟩
  · exact ⟨full_vivify, _, rfl, rfl, .of (full_vivify_bridge_wp Γ hBt hNext hVivCl hProp)⟩
  · exact ⟨full_fwd_dedup_bins, _, rfl, rfl, .of (full_fwd_dedup_bins_bridge_wp Γ hAddUnit)⟩
  · exact ⟨full_fwd_check_cl, _, rfl, rfl,
      .of (full_fwd_check_cl_bridge_wp Γ hUnwatch hAddUnit hAddBin)⟩
  · exact ⟨full_forward_sub, _, rfl, rfl, .of (full_forward_sub_bridge_wp Γ hDedup hNext hCheckCl)⟩
  · exact ⟨full_init_fresh_var, _, rfl, rfl, .of (full_init_fresh_var_bridge_wp Γ hHeapPush)⟩
  · exact ⟨full_bva_try_lit, _, rfl, rfl,
      .of (full_bva_try_lit_bridge_wp Γ hHasBin hInitFresh hAddBin hDelBin)⟩
  · exact ⟨full_factor, _, rfl, rfl, .of (full_factor_bridge_wp Γ hTryLit)⟩

/-- Index-verified `SpecEntry.Impl fullEnv` summary covering all `22` Part-A functions against
`fullSpecTable fullSolveBytesSpec`. -/
theorem full_bridge_7_ok :
    ∀ n ∈ fullBridge7Indices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl fullEnv fn row :=
  full_bridge_7_mk_ok fullSolveBytesSpec

end Part5

end LeanQbe.T.Examples.Kissat.Full
