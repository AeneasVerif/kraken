module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas
public import LeanQbe.T.Examples.Kissat.FullCongLemmas
public import LeanQbe.T.Examples.Kissat.FullReduceLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Lemmas — Parts 13–15 (`Stage 4`)

Parametric `(Γ : Env)` table-entry bridge lemmas `full_<fn>_bridge_wp` adapting landed shards
13–15 to canonical `FullSpec2`/`FullSpec3` contracts (`26` functions):
- Part 13 (`FullBveBvaLemmas`, `6` fns): `full_bve_collect`, `full_bve_mark_and`,
  `full_bve_gates`, `full_bve_resolve_pair`, `full_bve_weaken`, `full_bve_try_bce`.
- Part 14 (`FullCongLemmas`, `10` fns): `full_cong_find`, `full_cong_merge`, `full_has_ternary`,
  `full_sort_u32`, `full_cong_extract_ite`, `full_cong_emit_xor`, `full_cong_try_xor_ite`,
  `full_cong_extract`, `full_cong_hash_step`, `full_congruence`.
- Part 15 (`FullReduceLemmas`, `10` fns): `full_mark_reasons`, `full_red_less`, `full_red_sift`,
  `full_sort_reds`, `full_lit_rank`, `full_unwatch_large`, `full_sweep_bins`, `full_sweep_copy`,
  `full_rewatch_arena`, `full_arena_sweep`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## Part 13: `FullBveBvaLemmas` (`6` fns) -/

section Part13

theorem full_bve_collect_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullBveCollectSpec a m Q X → Func.wp Γ full_bve_collect_body a m Q X :=
  full_bve_collect_wp Γ

theorem full_bve_mark_and_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullBveMarkAndSpec a m Q X → Func.wp Γ full_bve_mark_and_body a m Q X :=
  full_bve_mark_and_wp Γ

theorem full_bve_gates_bridge_wp (Γ : Env)
    (hMark : ∀ a m Q X, fullBveMarkAndSpec a m Q X →
      Γ "full_bve_mark_and" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveGatesSpec a m Q X → Func.wp Γ full_bve_gates_body a m Q X :=
  full_bve_gates_wp Γ hMark

theorem full_bve_resolve_pair_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullBveResolvePairSpec a m Q X → Func.wp Γ full_bve_resolve_pair_body a m Q X :=
  full_bve_resolve_pair_wp Γ

theorem full_bve_weaken_bridge_wp (Γ : Env)
    (hExtPush2 : ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hExtPushCl : ∀ a m Q X, fullExtendPushClSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveWeakenSpec a m Q X → Func.wp Γ full_bve_weaken_body a m Q X :=
  full_bve_weaken_wp Γ hExtPush2 hDelBin hExtPushCl

theorem full_bve_try_bce_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullBveTryBceSpec a m Q X → Func.wp Γ full_bve_try_bce_body a m Q X :=
  full_bve_try_bce_wp Γ

end Part13

/-! ## Part 14: `FullCongLemmas` (`10` fns) -/

section Part14

private theorem congGateSeq_to_canon {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (h : FullCongSpecs.GateSeqOk F_cur cv scr g_len g) :
    FullCongGateSeqOk F_cur cv scr g_len g := by
  induction h with
  | done => exact .done
  | step hg _ ih => exact .step hg ih

private theorem canon_to_congGateSeq {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (h : FullCongGateSeqOk F_cur cv scr g_len g) :
    FullCongSpecs.GateSeqOk F_cur cv scr g_len g := by
  induction h with
  | done => exact .done
  | step hg _ ih => exact .step hg ih

theorem full_cong_find_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullCongFindSpec a m Q X → Func.wp Γ full_cong_find_body a m Q X :=
  full_cong_find_wp Γ

theorem full_cong_merge_bridge_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullCongMergeSpec a m Q X → Func.wp Γ full_cong_merge_body a m Q X := by
  refine full_cong_merge_wp Γ hFind ?_
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, _ha, _hb, hent, hm, hQ⟩
  refine hAddBin _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, fun _ _ => hent, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' un' uf' wv' ws' wl' wu' nb' om' inc' ph' wso' m'
      hlen' hw' _ h20 _ hm' =>
      hQ r _ m' hlen' hw' hcl0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun h => (h20 h).2) hm'⟩

theorem full_has_ternary_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullHasTernarySpec a m Q X → Func.wp Γ full_has_ternary_body a m Q X :=
  full_has_ternary_wp Γ

theorem full_sort_u32_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullSortU32Spec a m Q X → Func.wp Γ full_sort_u32_body a m Q X :=
  full_sort_u32_wp Γ

theorem full_cong_extract_ite_bridge_wp (Γ : Env)
    (hHasTern : ∀ a m Q X, fullHasTernarySpec a m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullCongExtractIteSpec a m Q X →
      Func.wp Γ full_cong_extract_ite_body a m Q X := by
  rintro ⟨h, cl, y, t, gl, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hc, hy, ht, hcy, hct, hyt, he1, he2, hcap,
      hg, hm, hQ⟩
  refine full_cong_extract_ite_wp Γ hHasTern _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hc, hy, ht, hcy, hct, hyt, he1, he2, hcap,
      canon_to_congGateSeq hg, hm,
      fun ret scr' m' hlen' hret hpre hg' hm' =>
        hQ ret scr' m' hlen' hret hpre (congGateSeq_to_canon hg') hm'⟩

theorem full_cong_emit_xor_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullCongEmitXorSpec a m Q X → Func.wp Γ full_cong_emit_xor_body a m Q X := by
  rintro ⟨sp, gl, x0, x1, x2, ⟨⟩⟩ m Q X
    ⟨F_cur, cv, scr, R, h0, h1, h2, hcv, hcap, hsl, hxor, hg, hm, hQ⟩
  refine full_cong_emit_xor_wp Γ _ m Q X
    ⟨F_cur, cv, scr, R, h0, h1, h2, hcv, hcap, hsl, hxor, canon_to_congGateSeq hg, hm,
      fun scr' m' hlen' hpre hg' hm' =>
        hQ scr' m' hlen' hpre (congGateSeq_to_canon hg') hm'⟩

theorem full_cong_try_xor_ite_bridge_wp (Γ : Env)
    (hHasTern : ∀ a m Q X, fullHasTernarySpec a m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] a m Q X)
    (hEmitXor : ∀ a m Q X, fullCongEmitXorSpec a m Q X →
      Γ "full_cong_emit_xor" [i64, i64, i32, i32, i32] [i64] a m Q X)
    (hExtIte : ∀ a m Q X, fullCongExtractIteSpec a m Q X →
      Γ "full_cong_extract_ite" [i64, i32, i32, i32, i64] [i64] a m Q X) :
    ∀ a m Q X, fullCongTryXorIteSpec a m Q X → Func.wp Γ full_cong_try_xor_ite_body a m Q X := by
  rintro ⟨h, a, b, cl, gl, gc, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha, hb, hcl, hab, hac, hbc, hent, h5, hcap,
      hg, hm, hQ⟩
  refine full_cong_try_xor_ite_wp Γ hHasTern ?_ ?_ _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha, hb, hcl, hab, hac, hbc, hent, h5, hcap,
      canon_to_congGateSeq hg, hm,
      fun ret scr' m' hlen' hlo hhi hpre hg' hm' =>
        hQ ret scr' m' hlen' hlo hhi hpre (congGateSeq_to_canon hg') hm'⟩
  · rintro ⟨sp, gl', x0, x1, x2, ⟨⟩⟩ m' Q' X'
      ⟨Fc', cv, scr, R', h0, h1, h2, hcv, hcp, hsl, hxor, hg', hm', hQ'⟩
    exact hEmitXor _ m' Q' X' ⟨Fc', cv, scr, R', h0, h1, h2, hcv, hcp, hsl, hxor,
      congGateSeq_to_canon hg', hm', fun scr' m'' hl' hp' hg'' hm'' =>
        hQ' scr' m'' hl' hp' (canon_to_congGateSeq hg'') hm''⟩
  · rintro ⟨h', cl', y, t, gl', ⟨⟩⟩ m' Q' X'
      ⟨c', F0', Fc', s', R', rfl, hl', hw', hnd', hcl0', hc', hy, ht, hcy, hct, hyt, he1, he2,
        hcp, hg', hm', hQ'⟩
    exact hExtIte _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hnd', hcl0', hc', hy, ht,
      hcy, hct, hyt, he1, he2, hcp, congGateSeq_to_canon hg', hm',
      fun ret scr' m'' hl'' hr hp' hg'' hm'' =>
        hQ' ret scr' m'' hl'' hr hp' (canon_to_congGateSeq hg'') hm''⟩

theorem full_cong_extract_bridge_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hTryXorIte : ∀ a m Q X, fullCongTryXorIteSpec a m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullCongExtractSpec a m Q X → Func.wp Γ full_cong_extract_body a m Q X := by
  rintro ⟨h, gc, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hcap, hm, hQ⟩
  refine full_cong_extract_wp Γ hNext hHasBin ?_ _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hcap, hm,
      fun ret scr' m' hlen' hle hg' hm' => hQ ret scr' m' hlen' hle (congGateSeq_to_canon hg') hm'⟩
  rintro ⟨h', a, b, cl, gl, gc', ⟨⟩⟩ m' Q' X'
    ⟨c', F0', Fc', s', R', rfl, hl', hw', hnd', hcl0', ha, hb, hcl, hab, hac, hbc, hent, h5,
      hcp, hg', hm', hQ'⟩
  exact hTryXorIte _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hnd', hcl0', ha, hb, hcl,
    hab, hac, hbc, hent, h5, hcp, congGateSeq_to_canon hg', hm',
    fun ret scr' m'' hl'' hlo hhi hp' hg'' hm'' =>
      hQ' ret scr' m'' hl'' hlo hhi hp' (canon_to_congGateSeq hg'') hm''⟩

theorem full_cong_hash_step_bridge_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullSortU32Spec a m Q X → Γ "full_sort_u32" [i64, i32] [] a m Q X)
    (hMerge : ∀ a m Q X, fullCongMergeSpec a m Q X →
      Γ "full_cong_merge" [i64, i32, i32] [.bool] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullCongHashStepSpec a m Q X → Func.wp Γ full_cong_hash_step_body a m Q X := by
  rintro ⟨h, gl, ho, hs, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hcl0, hdm, hrep, hsz, hle, hcap, hg, hm, hQ⟩
  refine full_cong_hash_step_wp Γ hFind hSort hMerge ?_ _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hcl0, hdm, hrep, hsz, hle, hcap,
      canon_to_congGateSeq hg, hm, hQ⟩
  rintro ⟨h', lit, ⟨⟩⟩ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', _hcl0, hlit, hent, hm', hQ'⟩
  refine hAddUnit _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', fun _ => hent, hm',
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' un' uf' inc'
      ph' ta' ba' pt' pb' hp' ps' hl'' qsi' qss' m'' hlen'' hw'' hcl0' hltf _ hm'' =>
      hQ' ok _ m'' hlen'' hw'' hcl0' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun hf => (hltf hlit hf).2) hm''⟩

theorem full_congruence_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hEnter : ∀ a m Q X, fullEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hExtract : ∀ a m Q X, fullCongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64] [i64] a m Q X)
    (hHashStep : ∀ a m Q X, fullCongHashStepSpec a m Q X →
      Γ "full_cong_hash_step" [i64, i64, i64, i64] [.bool] a m Q X)
    (hRebuild : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCongruenceSpec a m Q X → Func.wp Γ full_congruence_body a m Q X := by
  refine full_congruence_wp Γ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hle, hm, hQ⟩
    obtain ⟨F_cur, hw⟩ := hsp.1.witness
    have hcl := hsp.1.lengths.core_ok
    have hmx := c.hmaxv; unfold dimacsBound at hmx
    have hcl64 : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
    have htgt : tgt.toNat < s.core.cur_level → tgt.toNat < c.max_vars := by
      intro _; have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
    refine hBt _ m Q X ⟨c, s, R, rfl, hsp.1.lengths, hcl64, htgt, hw.trail_lits_lt, hm,
      fun vals' lvl' rsns' trl' tp' te' prop' cl' un' sc' m'
        hlen' _ _ hcl' hps _ _ _ hw' _ hm' => ?_⟩
    have hext' : FullExtScratchOk c { s with
        core := { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
          unassigned := un' }
        scratch := sc' } :=
      ⟨fun i hi => by dsimp only; rw [hps.1.1]; exact hsp.2.2.2.1.1 i hi,
        by dsimp only; rw [hps.1.2]; exact hsp.2.2.2.1.2⟩
    exact hQ _ m' ⟨⟨hlen', F_cur, hw' F0 F_cur hw hle⟩, hsp.2.1, hsp.2.2.1, hext', hsp.2.2.2.2⟩
      (hcl'.trans (Nat.min_eq_right hle)) (Nat.le_refl _) hm'
  · rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
    refine hEnter _ m Q X ⟨c, F0, s, R, rfl, hsp, hm, fun ok s' m' _ hfu ht hf hm' =>
      hQ ok s' m' (by rw [hfu]; exact Nat.le_refl _) ht hf hm'⟩
  · rintro ⟨h, gc, ⟨⟩⟩ m Q X ⟨c, F0, Fc, s, R, rfl, hl, hw, hnd, hcl0, hcap, hm, hQ⟩
    exact hExtract _ m Q X ⟨c, F0, Fc, s, R, rfl, hl, hw, hnd, hcl0, hcap, hm,
      fun ret scr' m' hl' hle hg' hm' => hQ ret scr' m' hl' hle (canon_to_congGateSeq hg') hm'⟩
  · rintro ⟨h, gl, ho, hs, ⟨⟩⟩ m Q X
      ⟨c, F0, Fc, s, R, rfl, hl, hw, hlm, hnd, hext, hcl0, hdm, hrep, hsz, hle, hcap, hg, hm, hQ⟩
    exact hHashStep _ m Q X ⟨c, F0, Fc, s, R, rfl, hl, hw, hlm, hnd, hext, hcl0, hdm, hrep, hsz,
      hle, hcap, congGateSeq_to_canon hg, hm, hQ⟩
  · rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdn, hm, hQ⟩
    refine hRebuild _ m Q X ⟨c, F0, s, R, rfl, hdn, hm, fun r s' m' hsp' hcl0 hfu _ h20 hm' =>
      hQ r s' m' hsp'.1.lengths hfu h20 (fun _ => ⟨hsp', hcl0⟩) hm'⟩
  · rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hm, hQ⟩
    obtain ⟨Fc, hw⟩ := hsp.1.witness
    refine hProp _ m Q X ⟨c, F0, Fc, s, R, rfl, hsp.1.lengths, hw, hsp.2.2.2.2, hm, ?_⟩
    dsimp only
    intro r vals' flags' lvl' rsns' trl' tp' te' prop' un' uf' wv' ar' ws' wl' wu' fu'
      ct' cr' c0' c1' om' tk' wso' ph' m' hl' hw' _ hpm hfu _ _ hr1 _ _ hm'
    let s' : FullState :=
      { s with
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := un',
          unflushed := uf', wvec := wv', arena := ar', wstk := ws', wlen := wl', wusable := wu',
          fuel := fu', confl_type := ct', confl_ref := cr', confl_lit0 := c0', confl_lit1 := c1',
          oom := om' }
        scratch := { s.scratch with search_ticks := tk', wsort := wso', phases := ph' } }
    have hnd' : FullArenaVarsNodup s' := by
      intro ref href hng
      have href0 : ref ∈ fullArenaClauseRefsCore s.core := hpm.2.1 ▸ href
      obtain ⟨_, hgb, hp⟩ := hpm.2.2 ref href0
      exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.1 ref href0 (hgb.symm.trans hng))
    have hll' : FullLastLearnedWf s' := fun i hi => by
      dsimp only [s', fullArenaClauseRefs]; rw [hpm.2.1]; exact hsp.2.2.2.1.1 i hi
    have hsp' : FullSparseInv c F0 s' :=
      ⟨⟨hl', Fc, hw'⟩, hsp.2.1, hnd', ⟨hll', hsp.2.2.2.1.2⟩, hsp.2.2.2.2⟩
    exact hQ r s' m' hsp' hcl0 hfu
      (fun h1 => level0_unsat_of_conflict_okW (s := s') hw' hcl0 (hr1 h1).2.2) hm'

end Part14

/-! ## Part 15: `FullReduceLemmas` (`10` fns) -/

section Part15

private theorem redBinOnlySlice_get {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : FullReduceSpecs.BinOnlyWatchSliceOk F_cur k lit p rem) :
    ∀ i < rem, let w := k.wstk[p + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat]) := by
  induction h with
  | empty => intro i hi; omega
  | bin hw hmsb _ hlt hent _ ih =>
    intro i hi
    cases i with
    | zero => simpa [hw] using ⟨hmsb, hlt, hent⟩
    | succ j =>
      have := ih j (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

private theorem redBinOnlySlice_of_all {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (hlen : k.LengthsOk c) {lit p rem : Nat} (hbd : p + rem ≤ k.wstk.length)
    (hall : ∀ i < rem, let w := k.wstk[p + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat])) :
    FullReduceSpecs.BinOnlyWatchSliceOk F_cur k lit p rem := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hcv := hlen.cur_vars_le
  induction rem generalizing p with
  | zero => exact .empty
  | succ r ih =>
    have hp_lt : p < k.wstk.length := by omega
    have h0 := hall 0 (Nat.zero_lt_succ r)
    rw [Nat.add_zero, List.getElem?_eq_getElem hp_lt, Option.getD_some] at h0
    have hne : k.wstk[p]'hp_lt ≠ 0xFFFFFFFF#32 := by
      intro heq; have h2 := h0.2.1; rw [heq] at h2
      have hm : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := by decide
      rw [hm] at h2; omega
    refine .bin (List.getElem?_eq_getElem hp_lt) h0.1 hne h0.2.1 h0.2.2
      (ih (by omega) fun j hj => ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using hall (j + 1) (by omega)

private theorem redBinOnly_to_full {F_cur : List (List Nat)} {k : FullCoreState}
    (h : FullReduceSpecs.BinOnlyWatchesInv F_cur k) : FullBinOnlyWatchesInv F_cur k :=
  ⟨h.layout, fun l hl => redBinOnlySlice_get (h.slices l hl)⟩

private theorem fullBinOnly_to_red {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (hlen : k.LengthsOk c) (h : FullBinOnlyWatchesInv F_cur k) :
    FullReduceSpecs.BinOnlyWatchesInv F_cur k :=
  ⟨h.1, fun l hl =>
    redBinOnlySlice_of_all hlen
      (by have := h.1.bounds l hl; have := hlen.wlen_le; have := hlen.wstk_len_arr; omega)
      (h.2 l hl)⟩

theorem full_mark_reasons_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullMarkReasonsSpec a m Q X → Func.wp Γ full_mark_reasons_body a m Q X :=
  full_mark_reasons_wp Γ

theorem full_red_less_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullRedLessSpec a m Q X → Func.wp Γ full_red_less_body a m Q X :=
  full_red_less_wp Γ

theorem full_red_sift_bridge_wp (Γ : Env)
    (hLess : ∀ a m Q X, fullRedLessSpec a m Q X →
      Γ "full_red_less" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullRedSiftSpec a m Q X → Func.wp Γ full_red_sift_body a m Q X :=
  full_red_sift_wp Γ hLess

theorem full_sort_reds_bridge_wp (Γ : Env)
    (hSift : ∀ a m Q X, fullRedSiftSpec a m Q X →
      Γ "full_red_sift" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullSortRedsSpec a m Q X → Func.wp Γ full_sort_reds_body a m Q X :=
  full_sort_reds_wp Γ hSift

theorem full_lit_rank_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullLitRankSpec a m Q X → Func.wp Γ full_lit_rank_body a m Q X :=
  full_lit_rank_wp Γ

theorem full_unwatch_large_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullUnwatchLargeSpec a m Q X → Func.wp Γ full_unwatch_large_body a m Q X :=
  full_unwatch_large_wp Γ

theorem full_sweep_bins_bridge_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X → Func.wp Γ full_sweep_bins_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  refine full_sweep_bins_wp Γ hDefrag _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, ?_⟩
  dsimp only
  intro wvec' wstk' wlen' nb' wsort' m' hlen' _ hfb hdw hw' hm'
  exact hQ wvec' wstk' wlen' nb' wsort' m' hlen' hfb hdw hw' hm'

private theorem redWatchPush_adapter {Γ : Env}
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullReduceSpecs.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm, hQ⟩
  exact hPush _ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm,
    fun ok wv ws wl wu wso m' hl' hly' hoth hT hF hm' =>
      hQ ok wv ws wl wu wso m' hl' hly' hoth hT (fun hf => (hF hf).1) hm'⟩

theorem full_sweep_copy_bridge_wp (Γ : Env)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullSweepCopySpec a m Q X → Func.wp Γ full_sweep_copy_body a m Q X := by
  rintro ⟨h, src, dst, osz, ar, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hds, h3, hfit, har, hlts, hrt, hm, hQ⟩
  refine full_sweep_copy_wp Γ hAssign (redWatchPush_adapter hPush) _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hds, h3, hfit, har, hlts,
      fun ht => let ⟨hw, hfb, hent⟩ := hrt ht; ⟨hw, fullBinOnly_to_red hlen.core_ok hfb, hent⟩,
      hm, ?_⟩
  dsimp only [FullReduceSpecs.fullSweepCopyPost, FullReduceSpecs.fullSweepCopyOutcome]
  intro r arena' vals' flags' lvl' rsns' trl' tp' te' un' uf' wv' ws' wl' wu' nb' om' ph' wso' m'
    hlen' hout ⟨hf_out, ht_out⟩ hm'
  exact hQ r arena' vals' flags' lvl' rsns' trl' tp' te' un' uf' wv' ws' wl' wu' nb' om' ph' wso' m'
    hlen' (fun i hi => hout i hi) hf_out
    (fun ht => let ⟨hw', hbo', rest⟩ := ht_out ht; ⟨hw', redBinOnly_to_full hbo', rest⟩) hm'

theorem full_rewatch_arena_bridge_wp (Γ : Env)
    (hRank : ∀ a m Q X, fullLitRankSpec a m Q X →
      Γ "full_lit_rank" [i64, i64, i32] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullRewatchArenaSpec a m Q X → Func.wp Γ full_rewatch_arena_body a m Q X := by
  rintro ⟨h, dst, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hdst, hcl, hm, hQ⟩
  refine full_rewatch_arena_wp Γ hRank (redWatchPush_adapter hPush) _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hdst, hw, hdm,
      fun r hr => let ⟨hg, hm0⟩ := hcl r hr; ⟨hm0, hg⟩, hm, ?_⟩
  dsimp only [FullReduceSpecs.fullRewatchArenaPost]
  intro ok ar' wv' ws' wl' wu' om' wso' m' hlen' hw' hrefs hnd hT hF hm'
  exact hQ ok ar' wv' ws' wl' wu' om' wso' m' hlen' hw' hnd hrefs hF hT hm'

theorem full_arena_sweep_bridge_wp (Γ : Env)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X → Γ "full_sweep_bins" [i64] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hCopy : ∀ a m Q X, fullSweepCopySpec a m Q X →
      Γ "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] a m Q X)
    (hRewatch : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Γ "full_rewatch_arena" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullArenaSweepSpec a m Q X → Func.wp Γ full_arena_sweep_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hrm, hm, hQ⟩
  refine full_arena_sweep_wp Γ ?_ hNext ?_ ?_ _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hrm, hm, ?_⟩
  · rintro ⟨h', ⟨⟩⟩ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hm', hQ'⟩
    refine hSweepBins _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hm', ?_⟩
    dsimp only
    intro wv' ws' wl' nb' wso' m'' hl'' hfb hdw hw'' hm''
    exact hQ' wv' ws' wl' nb' wso' m'' hl'' (fullBinOnly_to_red hl''.core_ok hfb) hfb hdw hw'' hm''
  · rintro ⟨h', src, dst, osz, ar, ⟨⟩⟩ m' Q' X'
      ⟨c', F0', Fc', s', R', rfl, hl', hds, h3, hfit, har, hlts, hrt, hm', hQ'⟩
    refine hCopy _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hds, h3, hfit, har, hlts,
      fun ht => let ⟨hw', hbo', hent⟩ := hrt ht; ⟨hw', redBinOnly_to_full hbo', hent⟩, hm', ?_⟩
    dsimp only
    intro r ar' va' fl' lv' rs' tr' tp' te' un' uf' wv' ws' wl' wu' nb' om' ph' wso' m''
      hl'' hout hf_o ht_o hm''
    exact hQ' r ar' va' fl' lv' rs' tr' tp' te' un' uf' wv' ws' wl' wu' nb' om' ph' wso' m''
      hl'' hout ⟨hf_o, fun ht =>
        let ⟨hw'', hfb'', rest⟩ := ht_o ht
        ⟨hw'', fullBinOnly_to_red hl''.core_ok hfb'', rest⟩⟩ hm''
  · rintro ⟨h', dst, ⟨⟩⟩ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hdst, hw', hdm', hcl, hm', hQ'⟩
    refine hRewatch _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hdm', hdst,
      fun r hr => let ⟨hm0, hg⟩ := hcl r hr; ⟨hg, hm0⟩, hm', ?_⟩
    dsimp only
    intro ok ar' wv' ws' wl' wu' om' wso' m'' hl'' hw'' hnd' hrefs hF hT hm''
    exact hQ' ok ar' wv' ws' wl' wu' om' wso' m'' hl'' hw'' hrefs hnd' hT hF hm''
  · dsimp only [FullReduceSpecs.fullArenaSweepPost]
    intro r va' fl' lv' rs' tr' tp' te' un' uf' wv' ws' ar' al' wl' wu' fr' ni' nr' nb' om' sc' m'
      hl' hw' hnd' hll' hext' hws2' hr hr01 hpos hr1 hr2 hr3 hm'
    exact hQ r va' fl' lv' rs' tr' tp' te' un' uf' wv' ws' ar' al' wl' wu' fr' ni' nr' nb' om' sc'
      m' hl' hr hext' hws2' hll' hw' hnd' hr01 hpos hr1 hr2 hr3 hm'

end Part15

end LeanQbe.T.Examples.Kissat.Full
