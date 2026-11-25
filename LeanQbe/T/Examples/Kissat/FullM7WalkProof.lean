/-
  FullM7WalkProof.lean — Verified soundness & memory-safety proofs for
  Kissat 4.0.4 ProbSAT local search (`full_walk_m7`) and full warmup
  (`full_warmup_m7`, `full_walk_warmup_m7`), module certification
  (`m7Walk_moduleOk`), and concrete non-vacuity (`nv_m7_walk`, `nv_m7_warmup`).
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7Walk
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0b
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM7Walk

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Full

public section

/-! ### Bit-level & core-invariant helpers -/

private theorem m7p_bv64_add1_lt {x : BitVec 64} {n : Nat}
    (h1 : x.toNat < n) (h2 : n + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem m7p_bv64_sub1 {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]
  have hx := x.isLt
  omega

private theorem m7p_bv64_shr2_add1_le {v mv : Nat}
    (hv_le : v ≤ mv) (hmv_pos : 0 < mv) (hmv : mv < 2 ^ 30) :
    ((BitVec.ofNat 64 v >>> BitVec.signExtend 64 2#32) + 1#64).toNat = v / 4 + 1 ∧
      v / 4 + 1 ≤ 2 * mv := by
  have hsh : (BitVec.ofNat 64 v >>> BitVec.signExtend 64 2#32).toNat = v / 4 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hadd :
      ((BitVec.ofNat 64 v >>> BitVec.signExtend 64 2#32) + 1#64).toNat = v / 4 + 1 := by
    rw [BitVec.toNat_add, hsh, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨hadd, by omega⟩

private theorem m7ArenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem m7ArenaPermEq_trans {k0 k1 k2 : FullCoreState}
    (h01 : FullArenaPermEq k0 k1) (h12 : FullArenaPermEq k1 k2) :
    FullArenaPermEq k0 k2 := by
  refine ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, ?_⟩
  intro r hr
  have hr1 : r ∈ fullArenaClauseRefsCore k1 := by rw [h01.2.1]; exact hr
  obtain ⟨hs01, hg01, hp01⟩ := h01.2.2 r hr
  obtain ⟨hs12, hg12, hp12⟩ := h12.2.2 r hr1
  exact ⟨hs12.trans hs01, hg12.trans hg01, hp12.trans hp01⟩

private theorem m7CoreLengths_with_fuel {c : FullCfg} {k : FullCoreState} {f' : BitVec 64}
    (h : k.LengthsOk c) : ({ k with fuel := f' } : FullCoreState).LengthsOk c :=
  ⟨h.vals_len, h.lit_mark_len, h.mrk_len, h.flags_len, h.lvl_len, h.rsns_len, h.trl_len,
    h.trail_pos_len, h.tmp_len_arr, h.min_clr_len_arr, h.frame_trail_len, h.frame_dec_len,
    h.wvec_len, h.repr_len, h.min_stk_len, h.arena_len_arr, h.wstk_len_arr, h.cur_vars_ge,
    h.cur_vars_le, h.arena_len_le, h.wlen_le, h.trail_end_le, h.propagated_le, h.tmp_len_le,
    h.min_clr_len_le⟩

private theorem m7CoreLengths_with_probing {c : FullCfg} {k : FullCoreState} {p' : BitVec 64}
    (h : k.LengthsOk c) : ({ k with probing := p' } : FullCoreState).LengthsOk c :=
  ⟨h.vals_len, h.lit_mark_len, h.mrk_len, h.flags_len, h.lvl_len, h.rsns_len, h.trl_len,
    h.trail_pos_len, h.tmp_len_arr, h.min_clr_len_arr, h.frame_trail_len, h.frame_dec_len,
    h.wvec_len, h.repr_len, h.min_stk_len, h.arena_len_arr, h.wstk_len_arr, h.cur_vars_ge,
    h.cur_vars_le, h.arena_len_le, h.wlen_le, h.trail_end_le, h.propagated_le, h.tmp_len_le,
    h.min_clr_len_le⟩

private theorem m7ScratchLengths_with_wv {c : FullCfg} {sc : FullScratch}
    {wv' : List (BitVec 8)} (h : sc.LengthsOk c) (hl : wv'.length = c.max_vars) :
    ({ sc with walk_best := wv' } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, h.phases_len, h.phases_target_len, h.phases_best_len, hl, h.heap_len_arr,
    h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len, h.wsort_len,
    h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len, h.score_len,
    h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr, h.red_refs_len,
    h.extend_stk_len, h.scratch_buf_len⟩

private theorem m7ScratchLengths_with_wsort {c : FullCfg} {sc : FullScratch}
    {ws' : List (BitVec 32)} (h : sc.LengthsOk c) (hl : ws'.length = 2 * c.max_vars) :
    ({ sc with wsort := ws' } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, h.phases_len, h.phases_target_len, h.phases_best_len, h.walk_best_len,
    h.heap_len_arr, h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len, hl,
    h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len, h.score_len,
    h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr, h.red_refs_len,
    h.extend_stk_len, h.scratch_buf_len⟩

private theorem m7ScratchLengths_with_phases {c : FullCfg} {sc : FullScratch}
    {ph' : List (BitVec 8)} (h : sc.LengthsOk c) (hl : ph'.length = c.max_vars) :
    ({ sc with phases := ph' } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, hl, h.phases_target_len, h.phases_best_len, h.walk_best_len,
    h.heap_len_arr, h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len,
    h.wsort_len, h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len,
    h.score_len, h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr,
    h.red_refs_len, h.extend_stk_len, h.scratch_buf_len⟩

private theorem m7ScratchLengths_with_st {c : FullCfg} {sc : FullScratch}
    {st' : BitVec 64} (h : sc.LengthsOk c) :
    ({ sc with search_ticks := st' } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, h.phases_len, h.phases_target_len, h.phases_best_len, h.walk_best_len,
    h.heap_len_arr, h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len,
    h.wsort_len, h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len,
    h.score_len, h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr,
    h.red_refs_len, h.extend_stk_len, h.scratch_buf_len⟩

private theorem m7ArenaHdr_eq {k1 k2 : FullCoreState} (har : k2.arena = k1.arena) (r : Nat) :
    fullArenaHdrCore k2 r = fullArenaHdrCore k1 r := by
  simp [fullArenaHdrCore, har]

private theorem m7ArenaClauseSize_eq {k1 k2 : FullCoreState}
    (har : k2.arena = k1.arena) (r : Nat) :
    fullArenaClauseSizeCore k2 r = fullArenaClauseSizeCore k1 r := by
  simp [fullArenaClauseSizeCore, har]

private theorem m7ArenaClauseGarb_eq {k1 k2 : FullCoreState}
    (har : k2.arena = k1.arena) (r : Nat) :
    fullArenaClauseGarbCore k2 r = fullArenaClauseGarbCore k1 r := by
  simp [fullArenaClauseGarbCore, m7ArenaHdr_eq har]

private theorem m7ArenaClauseLits_eq {k1 k2 : FullCoreState}
    (har : k2.arena = k1.arena) (r : Nat) :
    fullArenaClauseLitsCore k2 r = fullArenaClauseLitsCore k1 r := by
  simp [fullArenaClauseLitsCore, m7ArenaClauseSize_eq har, har]

private theorem m7ArenaClauses_congr {c : FullCfg} {F_cur : List (List Nat)}
    {k1 k2 : FullCoreState} (hal : k2.arena_len = k1.arena_len) (har : k2.arena = k1.arena)
    (hcv : k2.cur_vars = k1.cur_vars) (h : FullArenaClausesInv c F_cur k1) :
    FullArenaClausesInv c F_cur k2 := by
  have hrefs : fullArenaClauseRefsCore k2 = fullArenaClauseRefsCore k1 := by
    simp [fullArenaClauseRefsCore, hal, har]
  refine ⟨by rw [hal]; exact h.len_ok, ?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hrefs] at hr
    simpa [hal, har, m7ArenaClauseSize_eq har] using h.refs_wf r hr
  · intro r hr hh; rw [hrefs] at hr
    rw [m7ArenaHdr_eq har] at hh
    simpa [hal, har, m7ArenaClauseSize_eq har] using h.shrk_term r hr hh
  · intro r hr hg l hl; rw [hrefs] at hr
    rw [m7ArenaClauseGarb_eq har] at hg; rw [m7ArenaClauseLits_eq har] at hl
    rw [hcv]; exact h.lits_lt r hr hg l hl
  · intro r hr hg; rw [hrefs] at hr
    rw [m7ArenaClauseGarb_eq har] at hg; rw [m7ArenaClauseLits_eq har]
    exact h.entails r hr hg

private theorem m7WatchSlice_congr {F_cur : List (List Nat)} {k1 k2 : FullCoreState}
    {lit p rem : Nat} (hws : k2.wstk = k1.wstk) (hcv : k2.cur_vars = k1.cur_vars)
    (hal : k2.arena_len = k1.arena_len) (har : k2.arena = k1.arena)
    (h : WatchSliceOk F_cur k1 lit p rem) : WatchSliceOk F_cur k2 lit p rem := by
  induction h with
  | empty => exact WatchSliceOk.empty
  | bin h1 h2 h3 h4 h5 _ ih =>
    exact WatchSliceOk.bin (by simpa [hws] using h1) h2 h3 (by simpa [hcv] using h4) h5 ih
  | large h1 h2 h3 h4 h5 _ ih =>
    exact WatchSliceOk.large (by simpa [hws] using h1) (by simpa [hws] using h2) h3 h4
      (by simpa [fullArenaClauseRefsCore, har, hal] using h5) ih

private theorem m7DenseWatchSlice_congr {F_cur : List (List Nat)} {k1 k2 : FullCoreState}
    {lit p rem : Nat} (hws : k2.wstk = k1.wstk) (hcv : k2.cur_vars = k1.cur_vars)
    (hal : k2.arena_len = k1.arena_len) (har : k2.arena = k1.arena)
    (h : DenseWatchSliceOk F_cur k1 lit p rem) : DenseWatchSliceOk F_cur k2 lit p rem := by
  induction h with
  | empty => exact DenseWatchSliceOk.empty
  | bin h1 h2 h3 h4 h5 _ ih =>
    exact DenseWatchSliceOk.bin (by simpa [hws] using h1) h2 h3 (by simpa [hcv] using h4) h5 ih
  | occ h1 h2 h3 h4 h5 h6 _ ih =>
    exact DenseWatchSliceOk.occ (by simpa [hws] using h1) (by simpa [hws] using h2) h3 h4 h5
      (by simpa [fullArenaClauseRefsCore, har, hal] using h6) ih

private theorem m7ModeWatches_congr {F_cur : List (List Nat)} {k1 k2 : FullCoreState}
    (hdm : k2.dense_mode = k1.dense_mode) (hcv : k2.cur_vars = k1.cur_vars)
    (hal : k2.arena_len = k1.arena_len) (har : k2.arena = k1.arena)
    (hwl : k2.wlen = k1.wlen) (hwv : k2.wvec = k1.wvec) (hws : k2.wstk = k1.wstk)
    (h : ModeWatchesInv F_cur k1) : ModeWatchesInv F_cur k2 := by
  have hoff : ∀ x, fullWatchOffCore k2 x = fullWatchOffCore k1 x := fun x => by
    simp [fullWatchOffCore, hwv]
  have hsz : ∀ x, fullWatchSizeCore k2 x = fullWatchSizeCore k1 x := fun x => by
    simp [fullWatchSizeCore, hwv]
  have hlay : ∀ hk : WatchStackLayout k1, WatchStackLayout k2 := fun hk =>
    ⟨fun x hx => by
       rw [hoff, hsz, hwl]; exact hk.bounds x (by simpa [hcv] using hx),
     fun x hx hp => by
       rw [hoff]; rw [hsz] at hp; exact hk.pos_off x (by simpa [hcv] using hx) hp,
     fun l1 l2 h1 h2 hne hp1 hp2 => by
       rw [hoff, hoff, hsz, hsz]; rw [hsz] at hp1 hp2
       exact hk.disjoint l1 l2 (by simpa [hcv] using h1) (by simpa [hcv] using h2) hne hp1 hp2,
     fun x hx idx hidx => by
       rw [hoff, hws]; rw [hsz] at hidx
       exact hk.no_sentinel x (by simpa [hcv] using hx) idx hidx⟩
  by_cases hz : k1.dense_mode = 0#64
  · have hz2 : k2.dense_mode = 0#64 := hdm ▸ hz
    simp only [ModeWatchesInv, hz, hz2, ↓reduceIte] at h ⊢
    exact ⟨hlay h.layout, fun x hx => by
      rw [hoff, hsz]
      exact m7WatchSlice_congr hws hcv hal har (h.slices x (by simpa [hcv] using hx))⟩
  · have hz2 : k2.dense_mode ≠ 0#64 := hdm ▸ hz
    simp only [ModeWatchesInv, hz, hz2, ↓reduceIte] at h ⊢
    exact ⟨hlay h.layout, fun x hx => by
      rw [hoff, hsz]
      exact m7DenseWatchSlice_congr hws hcv hal har (h.slices x (by simpa [hcv] using hx))⟩

private theorem m7Witness_congr {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {k1 k2 : FullCoreState} (hw : FullWitnessInv c F0 F_cur k1)
    (hcv : k2.cur_vars = k1.cur_vars)
    (hinc : k2.inconsistent = k1.inconsistent) (hal : k2.arena_len = k1.arena_len)
    (har : k2.arena = k1.arena) (hdm : k2.dense_mode = k1.dense_mode)
    (hwl : k2.wlen = k1.wlen) (hwv : k2.wvec = k1.wvec) (hws : k2.wstk = k1.wstk)
    (hcl : k2.cur_level = k1.cur_level) (hte : k2.trail_end = k1.trail_end)
    (htr : k2.trl = k1.trl) (hv : k2.vals = k1.vals) (hl : k2.lvl = k1.lvl)
    (hr : k2.rsns = k1.rsns) (htp : k2.trail_pos = k1.trail_pos)
    (hft : k2.frame_trail = k1.frame_trail) (hfd : k2.frame_dec = k1.frame_dec) :
    FullWitnessInv c F0 F_cur k2 := by
  refine ⟨by simpa [hcv] using hw.ext_sound, by simpa [hinc] using hw.inconsistent_sound,
    m7ArenaClauses_congr hal har hcv hw.arena,
    m7ModeWatches_congr hdm hcv hal har hwl hwv hws hw.watches, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hcl, hte] using hw.cur_level_le
  · intro i hi; simpa [hcv, htr] using hw.trail_lits_lt i (by simpa [hte] using hi)
  · intro i j hi hj; simpa [htr] using
      hw.trail_vars_nodup i j (by simpa [hte] using hi) (by simpa [hte] using hj)
  · intro l hl; simpa [hv] using hw.vals_domain l (by simpa [hcv] using hl)
  · intro l hl; simpa [hv, hte, htr] using hw.vals_true_iff l (by simpa [hcv] using hl)
  · intro l hl; simpa [hv, hte, htr] using hw.vals_false_iff l (by simpa [hcv] using hl)
  · intro i hi; simpa [hl, htr, hcl] using hw.lvl_le i (by simpa [hte] using hi)
  · intro i j hi hj; simpa [hl, htr, hr] using
      hw.dec_earliest i j (by simpa [hte] using hi) (by simpa [hte] using hj)
  · intro L h1 hL; simpa [hte, hl, htr] using hw.levels_inhabited L h1 (by simpa [hcl] using hL)
  · intro i hi h0; simpa [htr] using
      hw.level0_sound i (by simpa [hte] using hi) (by simpa [hl, htr] using h0)
  · intro i hi; simpa [htp, htr] using hw.trail_pos_inv i (by simpa [hte] using hi)
  · intro idx hi h0; simpa [hr, htr] using
      hw.level0_rsn_none idx (by simpa [hte] using hi) (by simpa [hl, htr] using h0)
  · intro L hL; simpa [hft, hte] using hw.frame_trail_lt L (by simpa [hcl] using hL)
  · intro L1 L2 h12 h2; simpa [hft] using hw.frame_trail_mono L1 L2 h12 (by simpa [hcl] using h2)
  · intro L h1 hL i hi; simpa [hl, htr] using
      hw.frame_trail_before_lt L h1 (by simpa [hcl] using hL) i (by simpa [hft] using hi)
  · intro L h1 hL; simpa [hfd, hcv] using hw.frame_dec_lt L h1 (by simpa [hcl] using hL)
  · intro idx hi
    have hri := hw.reason_inv idx (by simpa [hte] using hi)
    dsimp only at hri ⊢
    rw [htr, hr]
    intro hne
    have hri' := hri hne
    by_cases hbin : k1.rsns[(k1.trl[idx]?.getD 0#32).toNat / 2]?.getD 4294967295#32 &&&
        2147483648#32 = 0#32
    · simp only [hbin, ne_eq, not_true_eq_false, ↓reduceIte] at hri' ⊢
      refine ⟨by simpa [fullArenaClauseRefsCore, hal, har] using hri'.1,
        by simpa [m7ArenaClauseGarb_eq har] using hri'.2.1, fun q hq => ?_⟩
      have hq1 := hri'.2.2 q (by simpa [m7ArenaClauseLits_eq har] using hq)
      rcases hq1 with rfl | ⟨m, hm1, hm2, hm3⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨m, hm1, by simpa [htr] using hm2, by simpa [hl, htr] using hm3⟩
    · simp only [hbin, ne_eq, not_false_eq_true, ↓reduceIte] at hri' ⊢
      rcases hri' with ⟨hot1, hot2, m, hm1, hm2, hm3⟩
      exact ⟨by simpa [hcv] using hot1, hot2, m, hm1, by simpa [htr] using hm2,
        by simpa [hl, htr] using hm3⟩
  · intro idx hi
    have hrl := hw.reason_lit_mem idx (by simpa [hte] using hi)
    dsimp only at hrl ⊢
    rw [htr, hr]
    intro h1 h2
    simpa [m7ArenaClauseLits_eq har] using hrl h1 h2

private theorem m7Witness_with_fuel {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {f' : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with fuel := f' } :=
  m7Witness_congr hw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

private theorem m7Witness_with_probing {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {p' : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with probing := p' } :=
  m7Witness_congr hw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

private theorem m7CoreInv_with_fuel {c : FullCfg} {F0 : Std.Sat.CNF Nat} {s : FullState}
    {f' : BitVec 64} (hinv : FullCoreInv c F0 s) :
    FullCoreInv c F0 { s with core := { s.core with fuel := f' } } :=
  ⟨⟨m7CoreLengths_with_fuel hinv.lengths.core_ok, hinv.lengths.scratch_ok⟩,
    let ⟨F_cur, hw⟩ := hinv.witness; ⟨F_cur, m7Witness_with_fuel hw⟩⟩

private theorem m7CoreInv_with_probing {c : FullCfg} {F0 : Std.Sat.CNF Nat} {s : FullState}
    {p' : BitVec 64} (hinv : FullCoreInv c F0 s) :
    FullCoreInv c F0 { s with core := { s.core with probing := p' } } :=
  ⟨⟨m7CoreLengths_with_probing hinv.lengths.core_ok, hinv.lengths.scratch_ok⟩,
    let ⟨F_cur, hw⟩ := hinv.witness; ⟨F_cur, m7Witness_with_probing hw⟩⟩

private theorem m7CoreInv_with_st {c : FullCfg} {F0 : Std.Sat.CNF Nat} {s : FullState}
    {st' : BitVec 64} (hinv : FullCoreInv c F0 s) :
    FullCoreInv c F0 { s with scratch := { s.scratch with search_ticks := st' } } :=
  ⟨⟨hinv.lengths.core_ok, m7ScratchLengths_with_st hinv.lengths.scratch_ok⟩, hinv.witness⟩

private theorem m7CoreLengths_decide {c : FullCfg} {k : FullCoreState}
    {ft' fd' : List (BitVec 32)} {cl' : Nat} (h : k.LengthsOk c)
    (hft : ft'.length = c.max_vars + 1) (hfd : fd'.length = c.max_vars + 1) :
    ({ k with frame_trail := ft', frame_dec := fd', cur_level := cl' } :
      FullCoreState).LengthsOk c :=
  ⟨h.vals_len, h.lit_mark_len, h.mrk_len, h.flags_len, h.lvl_len, h.rsns_len, h.trl_len,
    h.trail_pos_len, h.tmp_len_arr, h.min_clr_len_arr, hft, hfd, h.wvec_len, h.repr_len,
    h.min_stk_len, h.arena_len_arr, h.wstk_len_arr, h.cur_vars_ge, h.cur_vars_le, h.arena_len_le,
    h.wlen_le, h.trail_end_le, h.propagated_le, h.tmp_len_le, h.min_clr_len_le⟩

private theorem m7ArenaPermEq_with_fuel {k k' : FullCoreState} {f' : BitVec 64}
    (h : FullArenaPermEq k k') : FullArenaPermEq k { k' with fuel := f' } :=
  h

private theorem m7ArenaPermEq_with_probing {k k' : FullCoreState} {p' : BitVec 64}
    (h : FullArenaPermEq k k') : FullArenaPermEq k { k' with probing := p' } :=
  h

private theorem m7p_bv64_shl1 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< BitVec.signExtend 64 1#32).toNat = 2 * x.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem m7p_lit_pos_shl64 {v : BitVec 64} (hv : v.toNat < 2 ^ 29) :
    ((v <<< BitVec.signExtend 64 1#32).truncate 32).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_setWidth, m7p_bv64_shl1 (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem m7p_lit_neg_shl64 {v : BitVec 64} (hv : v.toNat < 2 ^ 29) :
    (((v <<< BitVec.signExtend 64 1#32).truncate 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hpos := m7p_lit_pos_shl64 hv
  rw [BitVec.toNat_or, hpos, show (1#32 : BitVec 32).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp
  | succ k =>
    have hdiv1 : (2 * v.toNat + 1) / 2 = v.toNat := by omega
    have hdiv2 : (2 * v.toNat) / 2 = v.toNat := by omega
    rw [Nat.testBit_or]
    simp [Nat.testBit_succ, hdiv1, hdiv2]

private theorem m7p_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem m7p_rshift32_lt {x : BitVec 64} :
    (x >>> 32#64).toNat < 2 ^ 32 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt; omega

private theorem m7p_and_mask32_toNat (x : BitVec 64) :
    ((x &&& 0xffffffff#64).truncate 32).toNat < 2 ^ 32 :=
  ((x &&& 0xffffffff#64).truncate 32).isLt

/-! ### Extern call bridges -/

private theorem m7NextDecVar_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hNDV : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hhdr : args.fst.val = c.hdr) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (r = 0xffffffffffffffff#64 ∨
        r.toNat < s.core.cur_vars ∧ s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_next_dec_var" args k) m := by
  refine wp_call_of_spec args k ?_
  refine hNDV _ _ _ _ ⟨c, s, R, hhdr, hlen, hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hs' ⟨hpres, hres⟩ hm'
  dsimp only [PreservesCoreSlice, fullSafetySlice] at hcore
  exact hk r s' m' hcore hs' hpres hres hm'

private theorem m7Backtrack_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    (hhdr : args.fst.val = c.hdr) (hinv : FullCoreInv c F0 s)
    (htarget : args.snd.fst.val.toNat ≤ s.core.cur_level) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', FullCoreInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_level = min s.core.cur_level args.snd.fst.val.toNat →
      s'.core.fuel = s.core.fuel → s'.core.probing = s.core.probing →
      s'.core.dense_mode = s.core.dense_mode → s'.core.inconsistent = s.core.inconsistent →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.arena_garbage = s.core.arena_garbage →
      s'.core.first_reducible = s.core.first_reducible → s'.core.num_irred = s.core.num_irred →
      s'.core.num_redundant = s.core.num_redundant → s'.core.num_binary = s.core.num_binary →
      s'.core.tmp_cnt = s.core.tmp_cnt → s'.core.tmp_len = s.core.tmp_len →
      s'.core.min_clr_len = s.core.min_clr_len → s'.core.min_clr_full = s.core.min_clr_full →
      s'.core.lit_mark = s.core.lit_mark → s'.core.mrk = s.core.mrk →
      s'.core.tmp = s.core.tmp → s'.core.min_clr = s.core.min_clr →
      s'.core.repr = s.core.repr → s'.core.min_stk = s.core.min_stk →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_backtrack" args k) m := by
  obtain ⟨hlen, F_cur, hw⟩ := hinv
  have hdb : Examples.LratBytes.dimacsBound = 2 ^ 28 := rfl
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have h1 := hw.cur_level_le; have h2 := hlen.core_ok.trail_end_le
    have h3 := hlen.core_ok.cur_vars_le; have h4 := c.hmaxv; omega
  have htgt : args.snd.fst.val.toNat < s.core.cur_level →
      args.snd.fst.val.toNat < c.max_vars := by
    intro hlt; have h1 := hw.cur_level_le; have h2 := hlen.core_ok.trail_end_le
    have h3 := hlen.core_ok.cur_vars_le; omega
  refine wp_call_of_spec args k ?_
  refine hBT _ _ _ _ ⟨c, s, R, hhdr, hlen, hcl_lt, htgt, hw.trail_lits_lt, hm, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hs' _ _ hcl hpres _ _ _ hw1 _ hm'
  have hperm : FullArenaPermEq s.core { s.core with
      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' } :=
    ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩
  have hw' := hw1 F0 F_cur hw htarget
  exact hk s' m' ⟨hs', F_cur, hw'⟩ hperm hcl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl hpres.1 hm'

private theorem m7Propagate_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    (hhdr : args.fst.val = c.hdr) (hinv : FullCoreInv c F0 s) (hd0 : s.core.dense_mode = 0#64)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) s' m', FullCoreInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat) →
      FullExtScratchPres s s' →
      s'.core.probing = s.core.probing → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode → s'.core.inconsistent = s.core.inconsistent →
      s'.core.cur_vars = s.core.cur_vars → s'.core.d_cur = s.core.d_cur →
      s'.core.d_val = s.core.d_val → s'.core.arena_garbage = s.core.arena_garbage →
      s'.core.first_reducible = s.core.first_reducible → s'.core.num_irred = s.core.num_irred →
      s'.core.num_redundant = s.core.num_redundant → s'.core.num_binary = s.core.num_binary →
      s'.core.tmp_cnt = s.core.tmp_cnt → s'.core.tmp_len = s.core.tmp_len →
      s'.core.min_clr_len = s.core.min_clr_len → s'.core.min_clr_full = s.core.min_clr_full →
      s'.core.lit_mark = s.core.lit_mark → s'.core.mrk = s.core.mrk →
      s'.core.tmp = s.core.tmp → s'.core.min_clr = s.core.min_clr →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.repr = s.core.repr → s'.core.min_stk = s.core.min_stk →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_propagate" args k) m := by
  obtain ⟨hlen, F_cur, hw⟩ := hinv
  refine wp_call_of_spec args k ?_
  refine hProp _ _ _ _ ⟨c, F0, F_cur, s, R, hhdr, hlen, hw, hd0, hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' _ hs' hw' _ hperm hfuel hr_dom hr0
    hr1 _ _ hm'
  exact hk r _ m' ⟨hs', F_cur, hw'⟩ hperm hfuel hr_dom
    (fun h0 hlt => (hr0 h0).2.2 hlt) (fun h1 => (hr1 h1).1) ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm'

/-! ### `M7WarmupCoreEq`: fixed-core-field tracking across warmup steps -/

private structure M7WarmupCoreEq (k0 k : FullCoreState) : Prop where
  d_cur_eq : k.d_cur = k0.d_cur
  d_val_eq : k.d_val = k0.d_val
  cur_vars_eq : k.cur_vars = k0.cur_vars
  arena_len_eq : k.arena_len = k0.arena_len
  arena_garbage_eq : k.arena_garbage = k0.arena_garbage
  first_reducible_eq : k.first_reducible = k0.first_reducible
  num_irred_eq : k.num_irred = k0.num_irred
  num_redundant_eq : k.num_redundant = k0.num_redundant
  num_binary_eq : k.num_binary = k0.num_binary
  tmp_cnt_eq : k.tmp_cnt = k0.tmp_cnt
  tmp_len_eq : k.tmp_len = k0.tmp_len
  min_clr_len_eq : k.min_clr_len = k0.min_clr_len
  min_clr_full_eq : k.min_clr_full = k0.min_clr_full
  dense_mode_eq : k.dense_mode = k0.dense_mode
  inconsistent_eq : k.inconsistent = k0.inconsistent
  lit_mark_eq : k.lit_mark = k0.lit_mark
  mrk_eq : k.mrk = k0.mrk
  tmp_eq : k.tmp = k0.tmp
  min_clr_eq : k.min_clr = k0.min_clr
  repr_eq : k.repr = k0.repr
  min_stk_eq : k.min_stk = k0.min_stk

private theorem m7WarmupCoreEq_refl (k : FullCoreState) : M7WarmupCoreEq k k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

private theorem m7WarmupCoreEq_trans {k0 k1 k2 : FullCoreState}
    (h01 : M7WarmupCoreEq k0 k1) (h12 : M7WarmupCoreEq k1 k2) : M7WarmupCoreEq k0 k2 :=
  ⟨h12.d_cur_eq.trans h01.d_cur_eq, h12.d_val_eq.trans h01.d_val_eq,
    h12.cur_vars_eq.trans h01.cur_vars_eq, h12.arena_len_eq.trans h01.arena_len_eq,
    h12.arena_garbage_eq.trans h01.arena_garbage_eq,
    h12.first_reducible_eq.trans h01.first_reducible_eq,
    h12.num_irred_eq.trans h01.num_irred_eq, h12.num_redundant_eq.trans h01.num_redundant_eq,
    h12.num_binary_eq.trans h01.num_binary_eq, h12.tmp_cnt_eq.trans h01.tmp_cnt_eq,
    h12.tmp_len_eq.trans h01.tmp_len_eq, h12.min_clr_len_eq.trans h01.min_clr_len_eq,
    h12.min_clr_full_eq.trans h01.min_clr_full_eq, h12.dense_mode_eq.trans h01.dense_mode_eq,
    h12.inconsistent_eq.trans h01.inconsistent_eq, h12.lit_mark_eq.trans h01.lit_mark_eq,
    h12.mrk_eq.trans h01.mrk_eq, h12.tmp_eq.trans h01.tmp_eq, h12.min_clr_eq.trans h01.min_clr_eq,
    h12.repr_eq.trans h01.repr_eq, h12.min_stk_eq.trans h01.min_stk_eq⟩

private theorem m7Walk_close_Q {c : FullCfg} {s s' : FullState} {fuel' : BitVec 64}
    {m' : Mem 64} {R : Mem 64 → Prop} {Q : Post []}
    (hQ : ∀ (fuel' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      let s'' : FullState := { core := { s.core with fuel := fuel' }, scratch := sc' }
      FullState.LengthsOk c s'' → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s'' → (FullMem c s'' ⋆ R) m' → Q () m')
    (hcore : s'.core = { s.core with fuel := fuel' })
    (hlen : s'.LengthsOk c) (hfuel : fuel'.toNat ≤ s.core.fuel.toNat)
    (hpres : FullExtScratchPres s s') (hm' : (FullMem c s' ⋆ R) m') : Q () m' := by
  have hst : s' = { core := { s.core with fuel := fuel' }, scratch := s'.scratch } := by
    rcases s' with ⟨c', sc'⟩; dsimp only at hcore; subst hcore; rfl
  have hfin := hQ fuel' s'.scratch m'
  rw [← hst] at hfin
  exact hfin hlen hfuel hpres hm'

private theorem m7Warmup_close_Q {c : FullCfg} {F0 : Std.Sat.CNF Nat} {s s' : FullState}
    {m' : Mem 64} {R : Mem 64 → Prop} {Q : Post []}
    (hQ : ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' unass' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
      let s'' : FullState := FullState.mk { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        frame_trail := ftrl', frame_dec := fdec', trail_end := te', propagated := prop',
        probing := prob', unassigned := unass', unflushed := unfl', wvec := wvec',
        arena := arena', wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
        confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
        oom := oom' } sc';
      FullCoreInv c F0 s'' → FullArenaPermEq s.core s''.core →
      fuel'.toNat ≤ s.core.fuel.toNat → FullExtScratchPres s s'' →
      (s.core.probing = 0#64 → prob' = 0#64) → (FullMem c s'' ⋆ R) m' → Q () m')
    (hinv : FullCoreInv c F0 s') (hperm : FullArenaPermEq s.core s'.core)
    (hfuel : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hpres : FullExtScratchPres s s')
    (hprob : s.core.probing = 0#64 → s'.core.probing = 0#64) (heq : M7WarmupCoreEq s.core s'.core)
    (hcl : s'.core.cur_level = s.core.cur_level) (hm' : (FullMem c s' ⋆ R) m') : Q () m' := by
  have hst : s' = FullState.mk { s.core with
      vals := s'.core.vals, flags := s'.core.flags, lvl := s'.core.lvl, rsns := s'.core.rsns,
      trl := s'.core.trl, trail_pos := s'.core.trail_pos, frame_trail := s'.core.frame_trail,
      frame_dec := s'.core.frame_dec, trail_end := s'.core.trail_end,
      propagated := s'.core.propagated, probing := s'.core.probing,
      unassigned := s'.core.unassigned, unflushed := s'.core.unflushed, wvec := s'.core.wvec,
      arena := s'.core.arena, wstk := s'.core.wstk, wlen := s'.core.wlen,
      wusable := s'.core.wusable, fuel := s'.core.fuel, confl_type := s'.core.confl_type,
      confl_ref := s'.core.confl_ref, confl_lit0 := s'.core.confl_lit0,
      confl_lit1 := s'.core.confl_lit1, oom := s'.core.oom } s'.scratch := by
    rcases s with ⟨k0, sc0⟩
    rcases s' with ⟨c', sc'⟩
    rcases heq with ⟨hd1, hd2, hcv, hal, hag, hfr, hni, hnr, hnb, htc, htl, hmcl, hmcf, hdm, hinc,
      hlm, hmrk, htmp, hmc, hrep, hms⟩
    dsimp only at *
    cases c'; cases k0; simp only at *
    subst hd1 hd2 hcv hal hag hfr hni hnr hnb htc htl hmcl hmcf hdm hinc hlm hmrk htmp hmc hrep hms
    subst hcl; rfl
  have hfin := hQ s'.core.vals s'.core.flags s'.core.lvl s'.core.rsns s'.core.trl s'.core.trail_pos
    s'.core.frame_trail s'.core.frame_dec s'.core.trail_end s'.core.propagated s'.core.probing
    s'.core.unassigned s'.core.unflushed s'.core.wvec s'.core.arena s'.core.wstk s'.core.wlen
    s'.core.wusable s'.core.fuel s'.core.confl_type s'.core.confl_ref s'.core.confl_lit0
    s'.core.confl_lit1 s'.core.oom s'.scratch m'
  rw [← hst] at hfin
  exact hfin hinv hperm hfuel hpres hprob hm'

attribute [local c0_load] FullArenaTactics.load_full_cur_level
attribute [local c0_load] FullArenaTactics.load_full_unflushed
attribute [local c0_load] FullArenaTactics.load_full_dense_mode
attribute [local c0_load] FullArenaTactics.load_full_unassigned
attribute [local c0_load] FullArenaTactics.load_full_inconsistent
attribute [local c0_load] FullArenaTactics.load_full_oom
attribute [local c0_load] FullArenaTactics.load_full_fuel
attribute [local c0_load] FullArenaTactics.load_full_cur_vars
attribute [local c0_load] FullArenaTactics.load_full_max_vars
attribute [local c0_load] FullArenaTactics.load_full_search_ticks
attribute [local c0_load] FullArenaTactics.load_full_probing
attribute [local c0_load] FullArenaTactics.load_full_stable
attribute [local c0_load] FullArenaTactics.load_full_trail_end
attribute [local c0_load] FullArenaTactics.load_full_propagated
attribute [local c0_load] FullArenaTactics.load_full_phases_ptr
attribute [local c0_load] FullArenaTactics.load_full_phases_best_ptr
attribute [local c0_load] FullArenaTactics.load_full_phases_target_ptr
attribute [local c0_load] FullArenaTactics.load_full_frame_trail_ptr
attribute [local c0_load] FullArenaTactics.load_full_frame_dec_ptr
attribute [local c0_load] FullArenaTactics.c0_load_full_phases
attribute [local c0_load] FullArenaTactics.c0_load_full_phases_best
attribute [local c0_load] FullArenaTactics.c0_load_full_phases_target
attribute [local c0_store] FullArenaTactics.c0_store_full_cur_level
attribute [local c0_store] FullArenaTactics.store_full_probing
attribute [local c0_store] FullArenaTactics.store_full_search_ticks
attribute [local c0_store] FullArenaTactics.c0_store_full_frame_trail
attribute [local c0_store] FullArenaTactics.c0_store_full_frame_dec
attribute [local c0_load] FullArenaTactics.load_full_scratch_cap
attribute [local c0_load] FullArenaTactics.load_full_scratch_buf_ptr
attribute [local c0_load] FullArenaTactics.load_full_walk_best_ptr
attribute [local c0_load] FullArenaTactics.load_full_walk_vals_ptr
attribute [local c0_load] FullArenaTactics.load_full_wsort_ptr
attribute [local c0_load] FullArenaTactics.load_full_arena_len
attribute [local c0_load] FullArenaTactics.load_full_walk_cnt_stat
attribute [local c0_load] FullArenaTactics.c0_load_full_wsort
attribute [local c0_load] FullArenaTactics.c0_load_full_walk_vals
attribute [local c0_load] FullArenaTactics.c0_load_full_walk_best
attribute [local c0_store] FullArenaTactics.store_full_walk_cnt_stat
attribute [local c0_store] FullArenaTactics.store_full_fuel
attribute [local c0_store] FullArenaTactics.c0_store_full_wsort
attribute [local c0_store] FullArenaTactics.c0_store_full_walk_best
attribute [local c0_store] FullArenaTactics.c0_store_full_scratch_buf
attribute [local c0_store] FullArenaTactics.c0_store_full_phases

/-! ### `full_walk_m7_wp` — ProbSAT local search WP -/

/-- `full_walk_m7` preserves `FullCoreInv` core fields (except `fuel`), `LengthsOk`, and
`FullExtScratchPres`, matching `Full.fullWalkSpec` under generalized `step7CbInvSpec`. -/
theorem full_walk_m7_wp_gen (Γ : Env)
    (hInitVals : ∀ a m Q X, m7InitValsSpec a m Q X →
      Γ "full_walk_init_vals_m7" [i64] [] a m Q X)
    (hCollect : ∀ a m Q X, m7CollectSpec a m Q X →
      Γ "full_walk_collect_m7" [i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X, step7CbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    (hInitTable : ∀ a m Q X, m7InitTableSpec a m Q X →
      Γ "full_walk_init_table_m7" [i64, i64] [] a m Q X)
    (hBuildOcc : ∀ a m Q X, m7BuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    (hEffort : ∀ a m Q X, m7EffortSpec a m Q X →
      Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, m7PickSpec a m Q X →
      Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    (hFlip : ∀ a m Q X, m7FlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hSaveMin : ∀ a m Q X, m7SaveMinSpec a m Q X →
      Γ "full_walk_save_min_m7" [i64, i64, Ty.bool] [] a m Q X)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (hS : fullWalkSpec a m Q X) :
    Func.wp Γ full_walk_m7_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hS with ⟨c, F0, s, R, hhdr, hinv, hm, hQ⟩
  subst hhdr
  have hlen := hinv.lengths
  have hmax := c.hmaxv
  have hscr := c.hscr
  have hdb : Examples.LratBytes.dimacsBound = 2 ^ 28 := rfl
  have hcv_le := hlen.core_ok.cur_vars_le
  have hale := hlen.core_ok.arena_len_le
  have hwb := hlen.scratch_ok.walk_best_len
  have hwv := hlen.scratch_ok.walk_vals_len
  have hph := hlen.scratch_ok.phases_len
  have hws := hlen.scratch_ok.wsort_len
  have hsbl := hlen.scratch_ok.scratch_buf_len
  dsimp only [Func.wp, full_walk_m7_body]
  c0_hsteps_nogrp
  · exact m7Walk_close_Q hQ rfl hlen (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  · exact m7Walk_close_Q hQ rfl hlen (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  · exact m7Walk_close_Q hQ rfl hlen (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  have hcv_ne0 : ¬BitVec.ofNat 64 s.core.cur_vars = 0 := by assumption
  have hcv_pos : 0 < s.core.cur_vars :=
    Nat.pos_of_ne_zero (fun h0 => hcv_ne0 (by rw [h0]; rfl))
  have hscr_64 : 64 ≤ c.scratch_cap := by
    rw [show c.scratch_cap % 2 ^ 64 = c.scratch_cap from Nat.mod_eq_of_lt (by omega),
      show BitVec.toNat 64 = 64 from rfl] at hc
    omega
  c0_hsteps_nogrp
  -- 5. call full_walk_init_vals_m7
  refine m7InitVals_call hInitVals rfl hlen hm fun s1 m1 hcore1 hlen1 hpres1 hm1 => ?_
  c0_hsteps_nogrp
  -- 6. call full_walk_collect_m7
  refine m7Collect_call hCollect rfl hlen1 hm1 fun rcol s2 m2 hcore2 hlen2 hpres2 hm2 => ?_
  have hcore20 : s2.core = s.core := hcore2.trans hcore1
  have hpres20 : FullExtScratchPres s s2 :=
    ⟨hpres2.1.trans hpres1.1, hpres2.2.trans hpres1.2⟩
  c0_hsteps_nogrp
  -- 7. Join block J26: increment walk_cnt_stat and return
  refine wp_join_group (ts := [])
    (fun _ mE => ∃ sE : FullState, sE.core = s.core ∧ sE.LengthsOk c ∧
      FullExtScratchPres s sE ∧ (FullMem c sE ⋆ R) mE)
    (fun _ ⟨⟩ mE ⟨sE, hcoreE, hlenE, hpresE, _hmE⟩ => by
      c0_hsteps
      let sE' : FullState := { sE with scratch :=
        { sE.scratch with walk_cnt_stat := sE.scratch.walk_cnt_stat + 1#64 } }
      have hlenE' : sE'.LengthsOk c := ⟨hlenE.core_ok, { hlenE.scratch_ok with }⟩
      exact m7Walk_close_Q hQ (by simp [sE', hcoreE]) hlenE' (Nat.le_refl _) hpresE
        (by assumption))
    (fun J26 hJ26 => by
      c0_hsplit
      · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      have hncl_ne := hc; clear hc
      c0_hsplit
      · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      clear hc
      c0_hsplit
      · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      have hcap_le := hc; clear hc
      let ncl := rcol >>> 32#64
      let nlit := rcol &&& 0xffffffff#64
      have hncl_lt : ncl.toNat < 2 ^ 32 := m7p_rshift32_lt
      have hncl_pos : 0 < ncl.toNat :=
        Nat.pos_of_ne_zero (fun h0 => hncl_ne (BitVec.eq_of_toNat_eq h0))
      have hcap5 : 32 + 5 * ncl.toNat ≤ c.scratch_cap := by
        have hsc_mod : c.scratch_cap % 2 ^ 64 = c.scratch_cap := by
          have := c.hscr
          unfold Examples.LratBytes.dimacsBound at this
          omega
        have hmod : (32 + 5 * ncl.toNat) % 2 ^ 64 = 32 + 5 * ncl.toNat :=
          Nat.mod_eq_of_lt (by have := hncl_lt; omega)
        change ¬ c.scratch_cap % 2 ^ 64 < (32 + 5 * ncl.toNat) % 2 ^ 64 at hcap_le
        rw [hsc_mod, hmod] at hcap_le
        omega
      have hncl_le : ncl.toNat ≤ c.scratch_cap := by omega
      c0_hsteps_nogrp
      refine step7CbInv_call hCbInv rfl hlen2 hm2 fun cb_inv m3 hcb1 hcb2 hm3 => ?_
      c0_hsteps_nogrp
      refine m7InitTable_call hInitTable rfl hlen2 hm3 fun s3 m4 hcore3 hlen3 hpres3 hm4 => ?_
      have hcore30 : s3.core = s.core := hcore3.trans hcore20
      have hpres30 : FullExtScratchPres s s3 :=
        ⟨hpres3.1.trans hpres20.1, hpres3.2.trans hpres20.2⟩
      c0_hsteps_nogrp
      refine m7BuildOcc_call hBuildOcc rfl hlen3 hm4 fun ru s4 m5 hcore4 hlen4 hpres4 hru hm5 => ?_
      have hcore40 : s4.core = s.core := hcore4.trans hcore30
      have hpres40 : FullExtScratchPres s s4 :=
        ⟨hpres4.1.trans hpres30.1, hpres4.2.trans hpres30.2⟩
      c0_hsteps_nogrp
      -- step_lim := max(256, ncl <<< 1), eff_lim := min(4096, step_lim)
      refine wp_join_group (ts := [i64]) (fun _ mS => (FullMem c s4 ⋆ R) mS)
        (fun _ ⟨step_lim, ⟨⟩⟩ mS hmS => by
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ mE => (FullMem c s4 ⋆ R) mE)
            (fun _ ⟨eff_lim, ⟨⟩⟩ mE hmE => by
              c0_hsteps_nogrp
              refine m7Effort_call hEffort rfl hlen4 hmE fun eff_ticks m6 _ _ hm6 => ?_
              c0_hsteps_nogrp
              have hwcap := m7p_bv64_shr2_add1_le hcv_le (by omega)
                (by have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at this; omega)
              have h2cv : (BitVec.ofNat 64 s.core.cur_vars <<<
                  BitVec.signExtend 64 1#32).toNat = 2 * s.core.cur_vars := by
                rw [m7p_bv64_shl1 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hbase : (32#64 + 4#64 * ncl).toNat = 32 + 4 * ncl.toNat := by
                rw [BitVec.toNat_add, BitVec.toNat_mul,
                  show (32#64 : BitVec 64).toNat = 32 from rfl,
                  show (4#64 : BitVec 64).toNat = 4 from rfl,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              -- J53_exit
              refine wp_join_group (ts := [i64, i64, i64, i64, Ty.bool, i64, i64])
                (fun _ mX => ∃ sX fuelX, sX.core = { s.core with fuel := fuelX } ∧
                  fuelX.toNat ≤ s.core.fuel.toNat ∧ sX.LengthsOk c ∧
                  FullExtScratchPres s sX ∧ (FullMem c sX ⋆ R) mX)
                (fun _ ⟨_, _, buX, _, flX, _, _, ⟨⟩⟩ mX
                    ⟨sX, fuelX, hcoreX, hfuelX, hlenX, hpresX, hmX⟩ => by
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun _ mZ => ∃ sZ, sZ.core = { s.core with fuel := fuelX } ∧
                      sZ.LengthsOk c ∧ FullExtScratchPres s sZ ∧ (FullMem c sZ ⋆ R) mZ)
                    (fun _ ⟨⟩ mZ ⟨sZ, hcoreZ, hlenZ, hpresZ, hmZ⟩ => by
                      c0_hsteps
                      let sZ' : FullState := { sZ with scratch :=
                        { sZ.scratch with walk_cnt_stat := sZ.scratch.walk_cnt_stat + 1#64 } }
                      have hlenZ' : sZ'.LengthsOk c := ⟨hlenZ.core_ok, { hlenZ.scratch_ok with }⟩
                      exact m7Walk_close_Q hQ (by simp [sZ', hcoreZ]) hlenZ' hfuelX
                        hpresZ (by assumption))
                    (fun _ hJsave => by
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine m7SaveMin_call hSaveMin rfl hlenX hmX
                          fun sY mY hcoreY hlenY hpresY hmY => ?_
                        c0_hsteps
                        exact hJsave () mY ⟨sY, hcoreY.trans hcoreX, hlenY,
                          ⟨hpresY.1.trans hpresX.1, hpresY.2.trans hpresX.2⟩, hmY⟩
                      · c0_hsteps
                        exact hJsave () mX ⟨sX, hcoreX, hlenX, hpresX, hmX⟩))
                (fun J53X hJ53X => by
                  refine wp_loop_group (ts := [i64, i64, i64, i64, Ty.bool, i64, i64])
                    (fun fn _ mL => ∃ sL fuelL, sL.core = { s.core with fuel := fuelL } ∧
                      fuelL.toNat = fn ∧ fuelL.toNat ≤ s.core.fuel.toNat ∧ sL.LengthsOk c ∧
                      FullExtScratchPres s sL ∧ (FullMem c sL ⋆ R) mL) ?_ ?_
                  · intro J53 fn ⟨uc, ml, bc, bu, fl, flp, tks, ⟨⟩⟩ mL hJ53
                      ⟨sL, fuelL, hcoreL, hfnL, hfuelL, hlenL, hpresL, hmL⟩
                    have hcoreL_cv : sL.core.cur_vars = s.core.cur_vars := by rw [hcoreL]
                    have hcoreL_fl : sL.core.fuel = fuelL := by rw [hcoreL]
                    c0_hsplit
                    · -- uc > 0
                      have huc_pos : 0 < uc.toNat := by simpa using hc
                      c0_hsplit
                      · -- uc ≤ ncl
                        have huc_le : uc.toNat ≤ ncl.toNat := hc
                        c0_hsplit
                        · -- flp < step_lim
                          c0_hsplit
                          · -- tks < eff_ticks
                            c0_hsplit
                            · -- fuelL > 0
                              have hf_pos : 0 < fuelL.toNat := by simpa [hcoreL_fl] using hc
                              have hfn_sub : (fuelL - 1#64).toNat = fn - 1 := by
                                rw [m7p_bv64_sub1 hf_pos, hfnL]
                              have hlt_n : fn - 1 < fn := by omega
                              have hurem_lt : (flp % uc).toNat < uc.toNat := by
                                rw [BitVec.toNat_umod]; exact Nat.mod_lt _ huc_pos
                              have hslot_sb : (32#64 + 4#64 * (rcol >>> 32#64) + flp % uc).toNat <
                                  sL.scratch.scratch_buf.length := by
                                rw [hlenL.scratch_ok.scratch_buf_len, BitVec.toNat_add,
                                  show (32#64 + 4#64 * (rcol >>> 32#64)).toNat =
                                    32 + 4 * ncl.toNat from hbase,
                                  Nat.mod_eq_of_lt (by omega)]
                                omega
                              have huc_ne : uc ≠ 0#64 := fun h0 => by
                                rw [h0] at huc_pos; simp at huc_pos
                              c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                              c0_hstep; c0_hstep; c0_hstep; c0_hstep
                              let sL1 : FullState := { sL with core := { sL.core with
                                fuel := fuelL - 1#64 } }
                              have hcoreL1 : sL1.core = { s.core with fuel := fuelL - 1#64 } := by
                                simp only [sL1, hcoreL]
                              have hfuelL1 : (fuelL - 1#64).toNat ≤ s.core.fuel.toNat := by omega
                              have hlenL1 : sL1.LengthsOk c :=
                                ⟨m7CoreLengths_with_fuel hlenL.core_ok, hlenL.scratch_ok⟩
                              have hpresL1 : FullExtScratchPres s sL1 := hpresL
                              have hslot_sb1 : (32#64 + 4#64 * (rcol >>> 32#64) + flp % uc).toNat <
                                  sL1.scratch.scratch_buf.length := hslot_sb
                              have hmL1 : (FullMem c sL1 ⋆ R) m := by
                                rw [hcoreL_fl] at hm
                                exact hm
                              refine C0HeadStep.head_wp_load ?_
                                (FullArenaTactics.c0_load_full_scratch_buf hslot_sb1 hmL1) ?_
                              · rfl
                              c0_hsplit
                              · -- (v75.setWidth 64) ≥ ncl -> break -> J53X
                                c0_hsteps
                                exact hJ53X _ m
                                  ⟨sL1, fuelL - 1#64, hcoreL1, hfuelL1, hlenL1, hpresL1, ‹_›⟩
                              · -- pick + flip + wsort + best
                                c0_hsteps_nogrp
                                refine m7Pick_call hPick rfl hlenL1 ‹_›
                                  fun rpick sL2 mL2 hcoreL2 hlenL2 hpresL2 hmL2 => ?_
                                have hcoreL2' : sL2.core = { s.core with fuel := fuelL - 1#64 } :=
                                  hcoreL2.trans hcoreL1
                                have hpresL20 : FullExtScratchPres s sL2 :=
                                  ⟨hpresL2.1.trans hpresL1.1, hpresL2.2.trans hpresL1.2⟩
                                c0_hsteps_nogrp
                                c0_hsplit
                                · -- v80 ≥ 2 * cur_vars -> continue
                                  c0_hsteps
                                  exact hJ53 (fn - 1) _ _ hlt_n
                                    ⟨sL2, fuelL - 1#64, hcoreL2', hfn_sub, hfuelL1, hlenL2,
                                      hpresL20, hmL2⟩
                                · -- call full_walk_flip_m7
                                  c0_hsteps_nogrp
                                  refine m7Flip_call hFlip rfl hlenL2 hmL2
                                    fun rflip sL3 mL3 hcoreL3 hlenL3 hpresL3 _ hmL3 => ?_
                                  have hcoreL3' :
                                      sL3.core = { s.core with fuel := fuelL - 1#64 } :=
                                    hcoreL3.trans hcoreL2'
                                  have hpresL30 : FullExtScratchPres s sL3 :=
                                    ⟨hpresL3.1.trans hpresL20.1, hpresL3.2.trans hpresL20.2⟩
                                  c0_hsteps_nogrp
                                  -- J_fin (@L5: ml', bc', fl')
                                  refine wp_join_group (ts := [i64, i64, Ty.bool])
                                    (fun _ mFin => ∃ sFin,
                                      sFin.core = { s.core with fuel := fuelL - 1#64 } ∧
                                      sFin.LengthsOk c ∧ FullExtScratchPres s sFin ∧
                                      (FullMem c sFin ⋆ R) mFin)
                                    (fun _ ⟨mhF, bcF, flF, ⟨⟩⟩ mFin
                                        ⟨sFin, hcoreFin, hlenFin, hpresFin, hmFin⟩ => by
                                      c0_hsteps_nogrp
                                      -- J_done (@L13)
                                      refine wp_join_group
                                        (ts := [i64, i64, i64, Ty.bool])
                                        (fun _ mD => ∃ sD,
                                          sD.core = { s.core with fuel := fuelL - 1#64 } ∧
                                          sD.LengthsOk c ∧ FullExtScratchPres s sD ∧
                                          (FullMem c sD ⋆ R) mD)
                                        (fun _ ⟨buD, mhD, bcD, flD, ⟨⟩⟩ mD
                                            ⟨sD, hcoreD, hlenD, hpresD, hmD⟩ => by
                                          c0_hsteps
                                          exact hJ53 (fn - 1) _ _ hlt_n
                                            ⟨sD, fuelL - 1#64, hcoreD, hfn_sub, hfuelL1, hlenD,
                                              hpresD, hmD⟩)
                                        (fun J_done hJ_done => by
                                          c0_hsplit
                                          · -- v91 < bu -> @L14 join -> check flF -> maybe copy
                                            refine wp_join_group (ts := [i64, i64, Ty.bool])
                                              (fun _ m14 => ∃ s14,
                                                s14.core = { s.core with fuel := fuelL - 1#64 } ∧
                                                s14.LengthsOk c ∧ FullExtScratchPres s s14 ∧
                                                (FullMem c s14 ⋆ R) m14)
                                              (fun _ _ m14 ⟨s14, hcore14, hlen14, hpres14, hm14⟩ =>
                                                by
                                                c0_hsteps
                                                exact hJ_done _ m14 ⟨s14, hcore14, hlen14,
                                                  hpres14, hm14⟩)
                                              (fun J14 hJ14 => by
                                                c0_hsplit
                                                · c0_hsteps
                                                  exact hJ14 _ mFin ⟨sFin, hcoreFin, hlenFin,
                                                    hpresFin, hmFin⟩
                                                · refine wp_loop_group (ts := [i64])
                                                    (fun nb ⟨idx, ⟨⟩⟩ mB => ∃ sB,
                                                      idx.toNat ≤ s.core.cur_vars ∧
                                                      nb = s.core.cur_vars - idx.toNat ∧
                                                      sB.core =
                                                        { s.core with fuel := fuelL - 1#64 } ∧
                                                      sB.LengthsOk c ∧ FullExtScratchPres s sB ∧
                                                      (FullMem c sB ⋆ R) mB)
                                                    ?_ ?_
                                                  · intro J97 nb ⟨idx, ⟨⟩⟩ mB hJ97
                                                      ⟨sB, hidx, hnb, hcoreB, hlenB, hpresB, hmB⟩
                                                    have hcvB : sB.core.cur_vars = s.core.cur_vars
                                                      := by rw [hcoreB]
                                                    c0_hsplit
                                                    · have hidx_lt : idx.toNat < s.core.cur_vars :=
                                                        by
                                                        rw [Nat.mod_eq_of_lt (by omega)] at hc
                                                        exact hc
                                                      have h2idx :
                                                          (idx <<< (1 : BitVec 64)).toNat <
                                                          sB.scratch.walk_vals.length := by
                                                        change (idx <<< BitVec.signExtend 64 1#32
                                                          ).toNat < sB.scratch.walk_vals.length
                                                        rw [m7p_bv64_shl1 (by omega),
                                                          hlenB.scratch_ok.walk_vals_len]
                                                        omega
                                                      have hidx_wb :
                                                          idx.toNat < sB.scratch.walk_best.length :=
                                                        by
                                                        rw [hlenB.scratch_ok.walk_best_len]
                                                        omega
                                                      have hidx1 : (idx + (1 : BitVec 64)).toNat =
                                                          idx.toNat + 1 := by
                                                        simpa using
                                                          m7p_bv64_add1_lt hidx_lt (by omega)
                                                      c0_hsteps
                                                      let wb' := sB.scratch.walk_best.set idx.toNat
                                                        sB.scratch.walk_vals[
                                                          (idx <<< (1 : BitVec 64)).toNat]
                                                      let sB' : FullState := FullState.mk sB.core
                                                        { sB.scratch with walk_best := wb' }
                                                      have hlenB' : sB'.LengthsOk c :=
                                                        ⟨hlenB.core_ok, m7ScratchLengths_with_wv
                                                          hlenB.scratch_ok
                                                          (by
                                                            simp [wb',
                                                              hlenB.scratch_ok.walk_best_len])⟩
                                                      exact hJ97 (s.core.cur_vars - (idx.toNat + 1))
                                                        _ _ (by omega)
                                                        ⟨sB', by rw [hidx1]; omega, by rw [hidx1],
                                                          hcoreB, hlenB', hpresB, ‹_›⟩
                                                    · c0_hsteps
                                                      exact hJ14 _ mB
                                                        ⟨sB, hcoreB, hlenB, hpresB, hmB⟩
                                                  · intro J97 hJ97
                                                    c0_hsteps
                                                    exact hJ97 s.core.cur_vars _ mFin
                                                      ⟨sFin, Nat.zero_le _, by rfl, hcoreFin,
                                                        hlenFin, hpresFin, hmFin⟩)
                                          · c0_hsteps
                                            exact hJ_done _ mFin ⟨sFin, hcoreFin, hlenFin, hpresFin,
                                              hmFin⟩))
                                    (fun J_fin hJ_fin => by
                                      c0_hsplit
                                      · -- fl = true: @L6 (J93) -> @L12 (J96) -> @L5 (J_fin)
                                        clear hc
                                        refine wp_join_group (ts := [i64, i64, Ty.bool])
                                          (fun _ m93 => ∃ s93,
                                            s93.core = { s.core with fuel := fuelL - 1#64 } ∧
                                            s93.LengthsOk c ∧ FullExtScratchPres s s93 ∧
                                            (FullMem c s93 ⋆ R) m93)
                                          (fun _ ⟨ml0, bc0, fl0, ⟨⟩⟩ m93
                                              ⟨s93, hcore93, hlen93, hpres93, hm93⟩ => by
                                            refine wp_join_group (ts := [i64])
                                              (fun _ m96 => ∃ s96,
                                                s96.core = { s.core with fuel := fuelL - 1#64 } ∧
                                                s96.LengthsOk c ∧ FullExtScratchPres s s96 ∧
                                                (FullMem c s96 ⋆ R) m96)
                                              (fun _ ⟨ml1, ⟨⟩⟩ m96
                                                  ⟨s96, hcore96, hlen96, hpres96, hm96⟩ => by
                                                c0_hsteps
                                                exact hJ_fin _ m96 ⟨s96, hcore96, hlen96, hpres96,
                                                  hm96⟩)
                                              (fun J96 hJ96 => by
                                                c0_hsplit
                                                · clear hc
                                                  c0_hsplit
                                                  · have hml_ws :
                                                        ml0.toNat < s93.scratch.wsort.length := by
                                                      rw [hlen93.scratch_ok.wsort_len]
                                                      have hlt : ml0.toNat < (BitVec.ofNat 64
                                                          s.core.cur_vars >>>
                                                          BitVec.signExtend 64 2#32 + 1#64).toNat
                                                        := hc
                                                      omega
                                                    c0_hsteps
                                                    let ws96 := s93.scratch.wsort.set ml0.toNat
                                                      ((BitVec.setWidth 32
                                                        (rpick &&& 4294967295#64)) >>> 1#32)
                                                    let s96 := FullState.mk s93.core
                                                      { s93.scratch with wsort := ws96 }
                                                    have hws96 := hlen93.scratch_ok.wsort_len
                                                    have hlen96 : s96.LengthsOk c :=
                                                      ⟨hlen93.core_ok, m7ScratchLengths_with_wsort
                                                        hlen93.scratch_ok
                                                        (by simp [ws96, hws96])⟩
                                                    exact hJ96 _ _ ⟨s96, hcore93, hlen96,
                                                      hpres93, ‹_›⟩
                                                  · c0_hsteps; exact hJ96 _ m93
                                                      ⟨s93, hcore93, hlen93, hpres93, hm93⟩
                                                · c0_hsteps; exact hJ96 _ m93
                                                    ⟨s93, hcore93, hlen93, hpres93, hm93⟩))
                                          (fun J93 hJ93 => by
                                            c0_hsplit
                                            · -- ml ≥ limit -> @L7 (J93b) -> @L6 (J93)
                                              refine wp_join_group (ts := [i64, i64, Ty.bool])
                                                (fun _ mB => ∃ sB,
                                                  sB.core = { s.core with fuel := fuelL - 1#64 } ∧
                                                  sB.LengthsOk c ∧ FullExtScratchPres s sB ∧
                                                  (FullMem c sB ⋆ R) mB)
                                                (fun _ _ mB ⟨sB, hcoreB, hlenB, hpresB, hmB⟩ => by
                                                  c0_hsteps
                                                  exact hJ93 _ mB ⟨sB, hcoreB, hlenB, hpresB, hmB⟩)
                                                (fun J93b hJ93b => by
                                                  c0_hsplit
                                                  · have hbc_pos : 0 < bc.toNat := by
                                                      simpa using hc
                                                    clear hc
                                                    c0_hsplit
                                                    · have hbc_le : bc.toNat ≤ ml.toNat := hc
                                                      clear hc
                                                      c0_hsplit
                                                      · have hml_le :
                                                            ml.toNat ≤ (BitVec.ofNat 64
                                                              s.core.cur_vars >>>
                                                              BitVec.signExtend 64 2#32 +
                                                              1#64).toNat := hc
                                                        have hml_wsort :
                                                            ml.toNat ≤ 2 * c.max_vars := by
                                                          omega
                                                        refine wp_loop_group (ts := [i64])
                                                          (fun nk ⟨k, ⟨⟩⟩ mK => ∃ sK,
                                                            k.toNat ≤ bc.toNat ∧
                                                            nk = bc.toNat - k.toNat ∧
                                                            sK.core =
                                                              { s.core with fuel := fuelL - 1#64 } ∧
                                                            sK.LengthsOk c ∧
                                                            FullExtScratchPres s sK ∧
                                                            (FullMem c sK ⋆ R) mK)
                                                          ?_ ?_
                                                        · intro J97 nk ⟨k, ⟨⟩⟩ mK hJ97
                                                            ⟨sK, hk_le, hnk, hcoreK, hlenK, hpresK,
                                                              hmK⟩
                                                          have hcvK :
                                                              sK.core.cur_vars = s.core.cur_vars :=
                                                            by rw [hcoreK]
                                                          c0_hsplit
                                                          · have hk_lt : k.toNat < bc.toNat := hc
                                                            clear hc
                                                            have hk_ws :
                                                                k.toNat < sK.scratch.wsort.length :=
                                                              by
                                                              rw [hlenK.scratch_ok.wsort_len]
                                                              omega
                                                            have hk1 :
                                                                (k + (1 : BitVec 64)).toNat =
                                                                k.toNat + 1 := by
                                                              simpa using
                                                                m7p_bv64_add1_lt hk_lt (by omega)
                                                            c0_hsteps_nogrp
                                                            -- @L9 join after if ((u64)w < cv)
                                                            refine wp_join_group (ts := [])
                                                              (fun _ m99 => ∃ s99,
                                                                s99.core = { s.core with
                                                                  fuel := fuelL - 1#64 } ∧
                                                                s99.LengthsOk c ∧
                                                                FullExtScratchPres s s99 ∧
                                                                (FullMem c s99 ⋆ R) m99)
                                                              (fun _ ⟨⟩ m99
                                                                  ⟨s99, hcore99, hlen99, hpres99,
                                                                    hm99⟩ => by
                                                                c0_hsteps
                                                                exact hJ97
                                                                  (bc.toNat - (k.toNat + 1))
                                                                  _ _ (by omega)
                                                                  ⟨s99, by rw [hk1]; omega,
                                                                    by rw [hk1], hcore99, hlen99,
                                                                    hpres99, hm99⟩)
                                                              (fun J99 hJ99 => by
                                                                c0_hsplit
                                                                · -- w < cur_vars
                                                                  have hw_lt_cond := hc; clear hc
                                                                  let w32 :=
                                                                    sK.scratch.wsort[k.toNat]
                                                                  have hw_lt : w32.toNat <
                                                                      sK.scratch.walk_best.length :=
                                                                    by
                                                                    rw [
                                                                      hlenK.scratch_ok.walk_best_len
                                                                      ]
                                                                    have hwv :
                                                                        (w32.setWidth 64).toNat <
                                                                        (BitVec.ofNat 64
                                                                          s.core.cur_vars).toNat :=
                                                                      by simpa [hcvK] using
                                                                        hw_lt_cond
                                                                    rw [m7p_zext32,
                                                                      BitVec.toNat_ofNat,
                                                                      Nat.mod_eq_of_lt (by omega)]
                                                                      at hwv
                                                                    omega
                                                                  have hw64_lt :
                                                                      (w32.setWidth 64).toNat <
                                                                      sK.scratch.walk_best.length :=
                                                                    by
                                                                    rw [BitVec.toNat_setWidth,
                                                                      Nat.mod_eq_of_lt (by
                                                                        have := w32.isLt; omega)]
                                                                    exact hw_lt
                                                                  c0_hsteps_nogrp
                                                                  refine wp_join_group (ts := [i32])
                                                                    (fun _ mP => mP = mK) ?_ ?_
                                                                  · intro _ ⟨phP, ⟨⟩⟩ mP hmEq
                                                                    subst hmEq
                                                                    c0_hsteps!
                                                                    let wb1 :=
                                                                      sK.scratch.walk_best.set
                                                                        (w32.setWidth 64).toNat
                                                                        (phP.setWidth 8)
                                                                    let sP := FullState.mk
                                                                      sK.core { sK.scratch with
                                                                        walk_best := wb1 }
                                                                    have hwbP :=
                                                                      hlenK.scratch_ok.walk_best_len
                                                                    have hlenP : sP.LengthsOk c :=
                                                                      ⟨hlenK.core_ok,
                                                                        m7ScratchLengths_with_wv
                                                                          hlenK.scratch_ok (by
                                                                            simp [wb1, hwbP])⟩
                                                                    exact hJ99 () _
                                                                      ⟨sP, hcoreK, hlenP, hpresK,
                                                                        ‹_›⟩
                                                                  · intro J106 hJ106
                                                                    c0_hsteps <;>
                                                                      exact hJ106 _ _ rfl
                                                                · c0_hsteps
                                                                  exact hJ99 () mK
                                                                    ⟨sK, hcoreK, hlenK, hpresK,
                                                                      hmK⟩)
                                                          · -- k ≥ bc -> compact J100
                                                            c0_hsteps_nogrp
                                                            refine wp_loop_group (ts := [i64])
                                                              (fun nj ⟨j, ⟨⟩⟩ mJ => ∃ sJ,
                                                                j.toNat ≤ (ml - bc).toNat ∧
                                                                nj = (ml - bc).toNat - j.toNat ∧
                                                                sJ.core =
                                                                  { s.core with
                                                                    fuel := fuelL - 1#64 } ∧
                                                                sJ.LengthsOk c ∧
                                                                FullExtScratchPres s sJ ∧
                                                                (FullMem c sJ ⋆ R) mJ)
                                                              ?_ ?_
                                                            · intro J100 nj ⟨j, ⟨⟩⟩ mJ hJ100
                                                                ⟨sJ, hj_le, hnj, hcoreJ, hlenJ,
                                                                  hpresJ, hmJ⟩
                                                              c0_hsplit
                                                              · have hj_lt :
                                                                    j.toNat < (ml - bc).toNat :=
                                                                  hc
                                                                have hsub_eq : (ml - bc).toNat =
                                                                    ml.toNat - bc.toNat := by
                                                                  rw [BitVec.toNat_sub]
                                                                  have := bc.isLt
                                                                  have := ml.isLt
                                                                  omega
                                                                have hsrc : (bc + j).toNat <
                                                                    sJ.scratch.wsort.length := by
                                                                  rw [hlenJ.scratch_ok.wsort_len,
                                                                    BitVec.toNat_add,
                                                                    Nat.mod_eq_of_lt (by omega)]
                                                                  omega
                                                                have hdst : j.toNat <
                                                                    sJ.scratch.wsort.length := by
                                                                  rw [hlenJ.scratch_ok.wsort_len]
                                                                  omega
                                                                have hj1 :
                                                                    (j + (1 : BitVec 64)).toNat =
                                                                    j.toNat + 1 := by
                                                                  simpa using m7p_bv64_add1_lt
                                                                    hj_lt (by omega)
                                                                c0_hsteps
                                                                let wsJ :=
                                                                  sJ.scratch.wsort.set j.toNat
                                                                    sJ.scratch.wsort[(bc + j).toNat]
                                                                let sJ' := FullState.mk sJ.core
                                                                  { sJ.scratch with wsort := wsJ }
                                                                have hwsJ :=
                                                                  hlenJ.scratch_ok.wsort_len
                                                                have hlenJ' : sJ'.LengthsOk c :=
                                                                  ⟨hlenJ.core_ok,
                                                                    m7ScratchLengths_with_wsort
                                                                      hlenJ.scratch_ok
                                                                      (by simp [wsJ, hwsJ])⟩
                                                                exact hJ100
                                                                  ((ml - bc).toNat - (j.toNat + 1))
                                                                  _ _ (by omega)
                                                                  ⟨sJ', by rw [hj1]; omega,
                                                                    by rw [hj1], hcoreJ, hlenJ',
                                                                    hpresJ, ‹_›⟩
                                                              · c0_hsteps
                                                                exact hJ93b _ mJ ⟨sJ, hcoreJ, hlenJ,
                                                                  hpresJ, hmJ⟩
                                                            · intro J100 hJ100
                                                              c0_hsteps
                                                              exact hJ100 (ml - bc).toNat _ mK
                                                                ⟨sK, Nat.zero_le _, by rfl, hcoreK,
                                                                  hlenK, hpresK, hmK⟩
                                                        · intro J97 hJ97
                                                          c0_hsteps
                                                          exact hJ97 bc.toNat _ mL3
                                                            ⟨sL3, Nat.zero_le _, by rfl, hcoreL3',
                                                              hlenL3, hpresL30, hmL3⟩
                                                      · c0_hsteps; exact hJ93b _ mL3
                                                          ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩
                                                    · c0_hsteps; exact hJ93b _ mL3
                                                        ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩
                                                  · c0_hsteps; exact hJ93b _ mL3
                                                      ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩)
                                            · c0_hsteps
                                              exact hJ93 _ mL3 ⟨sL3, hcoreL3', hlenL3, hpresL30,
                                                hmL3⟩)
                                      · c0_hsteps
                                        exact hJ_fin _ mL3 ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩)
                            · c0_hsteps; exact hJ53X _ mL
                                ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                          · c0_hsteps; exact hJ53X _ mL
                              ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                        · c0_hsteps; exact hJ53X _ mL
                            ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                      · c0_hsteps; exact hJ53X _ mL
                          ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                    · c0_hsteps; exact hJ53X _ mL
                        ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                  · intro J53 hJ53
                    c0_hsteps
                    exact hJ53 s.core.fuel.toNat _ m6
                      ⟨s4, s.core.fuel, hcore40, rfl, Nat.le_refl _, hlen4, hpres40, hm6⟩))
            (fun J36 hJ36 => by
              c0_hsplit
              · c0_hsteps; exact hJ36 _ _ hmS
              · c0_hsteps; exact hJ36 _ _ hmS))
        (fun J35 hJ35 => by
          c0_hsplit
          · c0_hsteps; exact hJ35 _ _ hm5
          · c0_hsteps; exact hJ35 _ _ hm5))

/-- `full_walk_m7` preserves `FullCoreInv` core fields (except `fuel`), `LengthsOk`, and
`FullExtScratchPres`, matching `Full.fullWalkSpec`. -/
theorem full_walk_m7_wp (Γ : Env)
    (hInitVals : ∀ a m Q X, m7InitValsSpec a m Q X →
      Γ "full_walk_init_vals_m7" [i64] [] a m Q X)
    (hCollect : ∀ a m Q X, m7CollectSpec a m Q X →
      Γ "full_walk_collect_m7" [i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X, m7CbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    (hInitTable : ∀ a m Q X, m7InitTableSpec a m Q X →
      Γ "full_walk_init_table_m7" [i64, i64] [] a m Q X)
    (hBuildOcc : ∀ a m Q X, m7BuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    (hEffort : ∀ a m Q X, m7EffortSpec a m Q X →
      Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, m7PickSpec a m Q X →
      Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    (hFlip : ∀ a m Q X, m7FlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hSaveMin : ∀ a m Q X, m7SaveMinSpec a m Q X →
      Γ "full_walk_save_min_m7" [i64, i64, Ty.bool] [] a m Q X)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (hS : fullWalkSpec a m Q X) :
    Func.wp Γ full_walk_m7_body a m Q X :=
  full_walk_m7_wp_gen Γ hInitVals hCollect
    (fun a m Q X h => hCbInv a m Q X (step7CbInvSpec_to_m7 h))
    hInitTable hBuildOcc hEffort hPick hFlip hSaveMin a m Q X hS

/-! ### `full_warmup_m7_wp` & `full_walk_warmup_m7_wp` — full warmup WP -/

/-- `full_warmup_m7` preserves `FullCoreInv`, `FullArenaPermEq`, `FullExtScratchPres`,
`probing = 0`, and `cur_level = 0`, matching `Full.fullWarmupSpec`. -/
theorem full_warmup_m7_wp (Γ : Env)
    (hNDV : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (hS : fullWarmupSpec a m Q X) :
    Func.wp Γ full_warmup_m7_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hS with ⟨c, F0, s, R, hhdr, hinv, hd0, hm, hQ⟩
  subst hhdr
  have hlen := hinv.lengths
  have hmax := c.hmaxv
  have hdb : Examples.LratBytes.dimacsBound = 2 ^ 28 := rfl
  have hcl0_lt : s.core.cur_level ≤ s.core.cur_vars := by
    obtain ⟨_, hw0⟩ := hinv.witness
    exact Nat.le_trans hw0.cur_level_le hlen.core_ok.trail_end_le
  dsimp only [Func.wp, full_warmup_m7_body]
  c0_hsteps_nogrp
  -- 7 remaining entry guards (dense_mode == 0 simplifies automatically via hd0)
  c0_hsteps_nogrp
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  have hcv_le_entry : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hcl_eq0 : BitVec.ofNat 64 s.core.cur_level = 0 := by assumption
  have hcl_entry : s.core.cur_level = 0 := by
    have h := congrArg BitVec.toNat hcl_eq0
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s.core.cur_level < 2 ^ 64 by omega)] using h
  c0_hsteps_nogrp
  -- J46_exit (unused i64)
  refine wp_join_group (ts := [i64])
    (fun _ mE => ∃ sE, FullCoreInv c F0 sE ∧ FullArenaPermEq s.core sE.core ∧
      sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sE ∧
      M7WarmupCoreEq s.core sE.core ∧ sE.core.dense_mode = 0#64 ∧ (FullMem c sE ⋆ R) mE)
    (fun _ _ mE ⟨sE, hinvE, hpermE, hfuelE, hpresE, heqE, _, _hmE⟩ => by
      c0_hsteps_nogrp
      let sE1 : FullState := { sE with core := { sE.core with probing := 1#64 } }
      have hinvE1 : FullCoreInv c F0 sE1 := m7CoreInv_with_probing hinvE
      have hpermE1 : FullArenaPermEq s.core sE1.core := m7ArenaPermEq_with_probing hpermE
      refine m7Backtrack_call hBT rfl hinvE1 (Nat.zero_le _) ‹_› fun sB mB hinvB hpermB hclB
          hfuelB _ hdB _ hcvB halB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpresB hmB => ?_
      c0_hsteps
      let sF : FullState := FullState.mk
        { sB.core with probing := s.core.probing }
        { sB.scratch with search_ticks := s.scratch.search_ticks }
      have hinvF : FullCoreInv c F0 sF := m7CoreInv_with_st (m7CoreInv_with_probing hinvB)
      have hpermF : FullArenaPermEq s.core sF.core :=
        m7ArenaPermEq_with_probing (m7ArenaPermEq_trans hpermE1 hpermB)
      have hclF : sF.core.cur_level = s.core.cur_level := by
        show sB.core.cur_level = s.core.cur_level
        rw [hclB, hcl_entry]; simp
      have hfuelF : sF.core.fuel.toNat ≤ s.core.fuel.toNat := by
        change sB.core.fuel.toNat ≤ s.core.fuel.toNat
        rw [hfuelB]; exact hfuelE
      have heqF : M7WarmupCoreEq s.core sF.core := by
        refine m7WarmupCoreEq_trans heqE ?_
        constructor <;> assumption
      exact m7Warmup_close_Q hQ hinvF hpermF hfuelF
        ⟨hpresB.1.trans hpresE.1, hpresB.2.trans hpresE.2⟩ (fun h => h) heqF hclF ‹_›)
    (fun J46E hJ46E => by
      refine wp_loop_group (ts := [i64])
        (fun fn ⟨k, ⟨⟩⟩ mL => ∃ sL, k.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - k.toNat ∧
          FullCoreInv c F0 sL ∧ FullArenaPermEq s.core sL.core ∧
          sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sL ∧
          M7WarmupCoreEq s.core sL.core ∧ sL.core.dense_mode = 0#64 ∧ (FullMem c sL ⋆ R) mL)
        ?_ ?_
      · intro J46 fn ⟨k, ⟨⟩⟩ mL hJ46
          ⟨sL, hk_le, hfn, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
        have hcvL : sL.core.cur_vars = s.core.cur_vars := heqL.cur_vars_eq
        have hincL : sL.core.inconsistent = s.core.inconsistent := heqL.inconsistent_eq
        have hlenL := hinvL.lengths
        c0_hsplit
        · -- steps < cv
          have hk_lt_bv : k.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
          have hk_lt : k.toNat < s.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega)] at hk_lt_bv
            exact hk_lt_bv
          have hk1 : (k + 1#64).toNat = k.toNat + 1 :=
            m7p_bv64_add1_lt hk_lt (by omega)
          have hlt_n : s.core.cur_vars - (k.toNat + 1) < fn := by omega
          c0_hsplit
          · -- unassigned > 0
            c0_hsplit
            · -- oom == 0
              c0_hsplit
              · -- fuel > 0
                c0_hsteps_nogrp
                refine m7NextDecVar_call hNDV rfl hlenL hmL
                  fun r sL2 mL2 hcoreL2 hlenL2 hpresL2 hresL2 hmL2 => ?_
                have hinvL2 : FullCoreInv c F0 sL2 :=
                  ⟨hlenL2, by rw [hcoreL2]; exact hinvL.witness⟩
                have hpermL2 : FullArenaPermEq s.core sL2.core := by
                  rw [hcoreL2]; exact hpermL
                have hfuelL2 : sL2.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hcoreL2]; exact hfuelL
                have hpresL20 : FullExtScratchPres s sL2 :=
                  ⟨hpresL2.1.trans hpresL.1, hpresL2.2.trans hpresL.2⟩
                have heqL2 : M7WarmupCoreEq s.core sL2.core := by
                  rw [hcoreL2]; exact heqL
                have hdL2 : sL2.core.dense_mode = 0#64 := by
                  rw [hcoreL2]; exact hdL
                c0_hsteps_nogrp
                c0_hsplit
                · -- r == -1 -> exit
                  c0_hsteps
                  exact hJ46E (k, ()) mL2
                    ⟨sL2, hinvL2, hpermL2, hfuelL2, hpresL20, heqL2, hdL2, hmL2⟩
                · -- pick phase and decide lit
                  have hr_spec : r.toNat < sL2.core.cur_vars ∧
                      sL2.core.vals[2 * r.toNat]?.getD 0#8 = 0#8 := by
                    rcases hresL2 with rfl | hok
                    · exact absurd rfl hc
                    · simpa [hcoreL2] using hok
                  have hr_lt : r.toNat < c.max_vars := by
                    have := hlenL2.core_ok.cur_vars_le; omega
                  have hr_ph : r.toNat < sL2.scratch.phases.length := by
                    rw [hlenL2.scratch_ok.phases_len]; exact hr_lt
                  have hr_pb : r.toNat < sL2.scratch.phases_best.length := by
                    rw [hlenL2.scratch_ok.phases_best_len]; exact hr_lt
                  have hr_pt : r.toNat < sL2.scratch.phases_target.length := by
                    rw [hlenL2.scratch_ok.phases_target_len]; exact hr_lt
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i8])
                    (fun _ m61 => (FullMem c sL2 ⋆ R) m61)
                    (fun _ ⟨ph, ⟨⟩⟩ m61 hm61 => by
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i32])
                        (fun ⟨lit, ⟨⟩⟩ m62 =>
                          (lit.toNat = 2 * r.toNat ∨ lit.toNat = 2 * r.toNat + 1) ∧
                          (FullMem c sL2 ⋆ R) m62)
                        (fun _ ⟨lit, ⟨⟩⟩ m62 ⟨hlit_eq, hm62⟩ => by
                          have hcl_L2 : sL2.core.cur_level ≤ sL2.core.cur_vars := by
                            obtain ⟨_, hwL2⟩ := hinvL2.witness
                            exact Nat.le_trans hwL2.cur_level_le hlenL2.core_ok.trail_end_le
                          c0_hsplit
                          · -- nlvl > max_vars -> exit
                            c0_hsteps
                            exact hJ46E (k, ()) m62
                              ⟨sL2, hinvL2, hpermL2, hfuelL2, hpresL20, heqL2, hdL2, hm62⟩
                          · have hmv := c.hmaxv
                            have hcv := hlenL2.core_ok.cur_vars_le
                            have hnlvl_le : sL2.core.cur_level + 1 ≤ c.max_vars := by
                              unfold Examples.LratBytes.dimacsBound at hmv
                              change ¬ c.max_vars % 2 ^ 64 <
                                  (sL2.core.cur_level + 1) % 2 ^ 64 at hc
                              have h1 : c.max_vars % 2 ^ 64 = c.max_vars :=
                                Nat.mod_eq_of_lt (by omega)
                              have h2 : (sL2.core.cur_level + 1) % 2 ^ 64 =
                                  sL2.core.cur_level + 1 :=
                                Nat.mod_eq_of_lt (by omega)
                              rw [h1, h2] at hc
                              omega
                            have hnlvl_ft : sL2.core.cur_level + 1 <
                                sL2.core.frame_trail.length := by
                              rw [hlenL2.core_ok.frame_trail_len]; omega
                            have hnlvl_fd : sL2.core.cur_level + 1 <
                                sL2.core.frame_dec.length := by
                              rw [hlenL2.core_ok.frame_dec_len]; omega
                            c0_hsteps_nogrp
                            let nlvl := sL2.core.cur_level + 1
                            let ft' := sL2.core.frame_trail.set nlvl
                              (BitVec.ofNat 32 sL2.core.trail_end)
                            let fd' := sL2.core.frame_dec.set nlvl lit
                            let sDec : FullState := { sL2 with core := { sL2.core with
                              frame_trail := ft', frame_dec := fd', cur_level := nlvl } }
                            have hlenDec : sDec.LengthsOk c :=
                              ⟨m7CoreLengths_decide hlenL2.core_ok
                                (by simp [ft', hlenL2.core_ok.frame_trail_len])
                                (by simp [fd', hlenL2.core_ok.frame_dec_len]),
                                hlenL2.scratch_ok⟩
                            have hdec_probe := full_decide_preserves_fullCore
                              (unas' := sL2.core.unassigned) (unfl' := sL2.core.unflushed)
                              hinvL2 hlenL2.scratch_ok hlenL2.core_ok.flags_len
                              hr_spec.1 hr_spec.2 hlit_eq
                            have hval0_lit : sL2.core.vals[lit.toNat]?.getD 0#8 = 0#8 :=
                              hdec_probe.2.1
                            have hte_lt : sL2.core.trail_end < sL2.core.cur_vars :=
                              hdec_probe.2.2.1
                            have hguard_false :
                                ¬(sDec.core.cur_vars ≤ lit.toNat / 2 ∨
                                  c.max_vars ≤ sDec.core.trail_end ∨
                                  sDec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                              have hv_eq : lit.toNat / 2 = r.toNat := by omega
                              have hcv_le2 := hlenL2.core_ok.cur_vars_le
                              intro hor
                              rcases hor with h1 | h2 | h3
                              · exact absurd (hv_eq ▸ h1) (Nat.not_le.mpr hr_spec.1)
                              · exact absurd h2
                                  (Nat.not_le.mpr (Nat.lt_of_lt_of_le hte_lt hcv_le2))
                              · exact h3 hval0_lit
                            have hte_bv : (BitVec.ofNat 64 sL2.core.trail_end).truncate 32 =
                                BitVec.ofNat 32 sL2.core.trail_end := by
                              apply BitVec.eq_of_toNat_eq; simp
                            have hcl_lt64 : sL2.core.cur_level < 2 ^ 64 := by
                              have := hcl_L2; have := hlenL2.core_ok.cur_vars_le
                              have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at this; omega
                            have hnlvl_lt64 : sL2.core.cur_level + 1 < 2 ^ 64 := by
                              have := hcl_L2; have := hlenL2.core_ok.cur_vars_le
                              have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at this; omega
                            have hnlvl_nat :
                                (BitVec.ofNat 64 sL2.core.cur_level + 1#64).toNat = nlvl := by
                              dsimp [nlvl]
                              rw [BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt hcl_lt64,
                                Nat.mod_eq_of_lt hnlvl_lt64]
                            refine wp_call_of_spec _ _ (hAssign _ _ _ _ ?_)
                            refine ⟨c, sDec, R, rfl, hlenDec,
                              (by dsimp [sDec, nlvl]; have := hnlvl_le; have := c.hmaxv;
                                  unfold Examples.LratBytes.dimacsBound at this; omega),
                              (by simp only [sDec, nlvl, ft', fd', ← hnlvl_nat, ← hte_bv]
                                  exact hm), ?_⟩
                            split
                            · rename_i h; exact False.elim (hguard_false h)
                            · intro v rsn' unfl' flagsA unassA phasesA mA hflA hphA sA' hmA
                              have hdec_ok := full_decide_preserves_fullCore
                                (unas' := unassA) (unfl' := sL2.core.unflushed) hinvL2
                                (m7ScratchLengths_with_phases hlenL2.scratch_ok hphA) hflA
                                hr_spec.1 hr_spec.2 hlit_eq
                              let sA : FullState :=
                                { core := { sL2.core with
                                    unassigned := unassA,
                                    trail_end := sL2.core.trail_end + 1,
                                    vals := (sL2.core.vals.set lit.toNat 1#8).set
                                      (lit.toNat ^^^ 1) 255#8,
                                    flags := flagsA,
                                    lvl := sL2.core.lvl.set (lit.toNat / 2)
                                      (BitVec.ofNat 32 nlvl),
                                    rsns := sL2.core.rsns.set (lit.toNat / 2) 4294967295#32,
                                    trl := sL2.core.trl.set sL2.core.trail_end lit,
                                    trail_pos := sL2.core.trail_pos.set (lit.toNat / 2)
                                      (BitVec.ofNat 32 sL2.core.trail_end),
                                    frame_trail := ft', frame_dec := fd', cur_level := nlvl },
                                  scratch := { sL2.scratch with phases := phasesA } }
                              have hsA_eq : sA = sA' := by
                                dsimp [sA, sA', sDec, v, rsn', unfl']
                              rw [← hsA_eq] at hmA
                              have hinvA : FullCoreInv c F0 sA := hdec_ok.1
                              have hpermA : FullArenaPermEq s.core sA.core := hpermL2
                              have hfuelA : sA.core.fuel.toNat ≤ s.core.fuel.toNat := hfuelL2
                              have hpresA : FullExtScratchPres s sA := hpresL20
                              have heqA : M7WarmupCoreEq s.core sA.core :=
                                ⟨heqL2.1, heqL2.2, heqL2.3, heqL2.4, heqL2.5, heqL2.6, heqL2.7,
                                  heqL2.8, heqL2.9, heqL2.10, heqL2.11, heqL2.12, heqL2.13,
                                  heqL2.14, heqL2.15, heqL2.16, heqL2.17, heqL2.18, heqL2.19,
                                  heqL2.20, heqL2.21⟩
                              have hdA : sA.core.dense_mode = 0#64 := hdL2
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun _ mJ => ∃ sJ, FullCoreInv c F0 sJ ∧
                                  FullArenaPermEq s.core sJ.core ∧
                                  sJ.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  FullExtScratchPres s sJ ∧ M7WarmupCoreEq s.core sJ.core ∧
                                  sJ.core.dense_mode = 0#64 ∧ (FullMem c sJ ⋆ R) mJ)
                                (fun _ ⟨⟩ mJ
                                    ⟨sJ, hinvJ, hpermJ, hfuelJ, hpresJ, heqJ, hdJ, hmJ⟩ => by
                                  c0_hsteps
                                  exact hJ46 (s.core.cur_vars - (k.toNat + 1)) (k + 1#64, ())
                                    mJ hlt_n
                                    ⟨sJ, by rw [hk1]; omega, by rw [hk1], hinvJ, hpermJ,
                                      hfuelJ, hpresJ, heqJ, hdJ, hmJ⟩)
                                (fun J75 hJ75 => by
                                  refine wp_loop_group (ts := [])
                                    (fun fn _ mP => ∃ sP, fn = sP.core.fuel.toNat ∧
                                      FullCoreInv c F0 sP ∧ FullArenaPermEq s.core sP.core ∧
                                      sP.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                      FullExtScratchPres s sP ∧ M7WarmupCoreEq s.core sP.core ∧
                                      sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ R) mP) ?_ ?_
                                  · intro J_prop fn ⟨⟩ mP hJ_prop
                                      ⟨sP, hfnP, hinvP, hpermP, hfuelP, hpresP, heqP, hdP, hmP⟩
                                    have hlenP := hinvP.lengths
                                    c0_hsplit
                                    · have hprop_lt : sP.core.propagated < sP.core.trail_end := by
                                        have := hlenP.core_ok.trail_end_le
                                        have := hlenP.core_ok.propagated_le
                                        have := hlenP.core_ok.cur_vars_le
                                        have := c.hmaxv
                                        unfold Examples.LratBytes.dimacsBound at this
                                        change (BitVec.ofNat 64 sP.core.propagated).toNat <
                                            (BitVec.ofNat 64 sP.core.trail_end).toNat at hc
                                        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                          Nat.mod_eq_of_lt (by omega),
                                          Nat.mod_eq_of_lt (by omega)] at hc
                                        exact hc
                                      c0_hsplit
                                      · c0_hsplit
                                        · c0_hsteps_nogrp
                                          refine m7Propagate_call hProp rfl hinvP hdP hmP
                                            fun r sP2 mP2 hinvP2 hpermP2 hfuelP2 hr_dom hr0_fuel
                                              hr1_fuel hpresP2 hprobP2 hclP2 hdP2 hincP2 hcvP2
                                              hd1P2 hd2P2 hgarbP2 hagP2 hfrP2 hniP2 hnrP2 hnbP2
                                              htcP2 htlP2 hmclP2 hmcfP2 hlmP2 hmrkP2 htmpP2 hmcP2
                                              hfdP2 hrepP2 hmstkP2 hmP2 => ?_
                                          have hpermP0 := m7ArenaPermEq_trans hpermP hpermP2
                                          have hfuelP0 : sP2.core.fuel.toNat ≤ s.core.fuel.toNat :=
                                            Nat.le_trans hfuelP2 hfuelP
                                          have hpresP0 : FullExtScratchPres s sP2 :=
                                            ⟨hpresP2.1.trans hpresP.1, hpresP2.2.trans hpresP.2⟩
                                          have heqP0 : M7WarmupCoreEq s.core sP2.core := by
                                            refine m7WarmupCoreEq_trans heqP ?_
                                            exact ⟨hd1P2, hd2P2, hcvP2, hpermP2.1,
                                              hgarbP2, hagP2, hfrP2, hniP2, hnrP2, hnbP2, htcP2,
                                              htlP2, hmclP2, hdP2, hincP2, hmcfP2, hlmP2, hmrkP2,
                                              htmpP2, hrepP2, hmstkP2⟩
                                          have hdP0 : sP2.core.dense_mode = 0#64 := by
                                            rw [hdP2, hdP]
                                          c0_hsplit
                                          · c0_hsteps; exact hJ75 () mP2
                                              ⟨sP2, hinvP2, hpermP0, hfuelP0, hpresP0, heqP0,
                                                hdP0, hmP2⟩
                                          · have hlt_fuel : sP2.core.fuel.toNat < fn := by
                                              rw [hfnP]
                                              rcases hr_dom with rfl | rfl | rfl
                                              · exact hr0_fuel rfl hprop_lt
                                              · exact hr1_fuel rfl
                                              · exact absurd rfl hc
                                            c0_hsteps
                                            exact hJ_prop sP2.core.fuel.toNat () mP2 hlt_fuel
                                              ⟨sP2, rfl, hinvP2, hpermP0, hfuelP0, hpresP0, heqP0,
                                                hdP0, hmP2⟩
                                        · c0_hsteps; exact hJ75 () mP
                                            ⟨sP, hinvP, hpermP, hfuelP, hpresP, heqP, hdP, hmP⟩
                                      · c0_hsteps; exact hJ75 () mP
                                          ⟨sP, hinvP, hpermP, hfuelP, hpresP, heqP, hdP, hmP⟩
                                    · c0_hsteps; exact hJ75 () mP
                                        ⟨sP, hinvP, hpermP, hfuelP, hpresP, heqP, hdP, hmP⟩
                                  · intro J_prop hJ_prop
                                    c0_hsteps
                                    exact hJ_prop sA.core.fuel.toNat () mA
                                      ⟨sA, rfl, hinvA, hpermA, hfuelA, hpresA, heqA, hdA, hmA⟩))
                        (fun J62 hJ62 => by
                          have hr29 : r.toNat < 2 ^ 29 := by
                            have := hr_lt
                            have := c.hmaxv
                            unfold Examples.LratBytes.dimacsBound at this
                            omega
                          c0_hsplit
                          · c0_hsteps
                            exact hJ62
                              (((r <<< BitVec.signExtend 64 1#32).truncate 32 ||| 1#32), ()) _
                              ⟨Or.inr (m7p_lit_neg_shl64 hr29), hm61⟩
                          · c0_hsteps
                            exact hJ62 (((r <<< BitVec.signExtend 64 1#32).truncate 32), ()) _
                              ⟨Or.inl (m7p_lit_pos_shl64 hr29), hm61⟩))
                    (fun J61 hJ61 => by
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps; exact hJ61 _ _ hmL2
                        · c0_hsteps; exact hJ61 _ _ hmL2
                      · c0_hsteps; exact hJ61 _ _ hmL2)
              · c0_hsteps
                exact hJ46E (k, ()) mL ⟨sL, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
            · c0_hsteps
              exact hJ46E (k, ()) mL ⟨sL, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
          · c0_hsteps
            exact hJ46E (k, ()) mL ⟨sL, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
        · c0_hsteps
          exact hJ46E (k, ()) mL ⟨sL, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
      · intro J46 hJ46
        c0_hsteps
        exact hJ46 s.core.cur_vars (0#64, ()) m
          ⟨s, Nat.zero_le _, by simp, hinv, m7ArenaPermEq_refl _, Nat.le_refl _, ⟨rfl, rfl⟩,
            m7WarmupCoreEq_refl _, hd0, hm⟩)

/-- `full_walk_warmup_m7` sequences `full_warmup_m7` then `full_walk_m7`, matching
`Full.fullWarmupSpec`. -/
theorem full_walk_warmup_m7_wp (Γ : Env)
    (hWarmup : ∀ a m Q X, fullWarmupSpec a m Q X →
      Γ "full_warmup_m7" [i64] [] a m Q X)
    (hWalk : ∀ a m Q X, fullWalkSpec a m Q X →
      Γ "full_walk_m7" [i64] [] a m Q X)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (hS : fullWarmupSpec a m Q X) :
    Func.wp Γ full_walk_warmup_m7_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hS with ⟨c, F0, s, R, hhdr, hinv, hd0, hm, hQ⟩
  subst hhdr
  dsimp only [Func.wp, full_walk_warmup_m7_body]
  refine wp_call_of_spec _ _ ?_
  refine hWarmup _ _ _ _ ⟨c, F0, s, R, rfl, hinv, hd0, hm, ?_⟩
  intro vals1 flags1 lvl1 rsns1 trl1 tp1 ftrl1 fdec1 te1 prop1 prob1 unass1 unfl1 wvec1 arena1
    wstk1 wlen1 wu1 fuel1 ctype1 cref1 c01 c11 oom1 sc1 m1 s1' hinv1 hperm1 hfuel1 hpres1 hprob1 hm1
  refine wp_call_of_spec _ _ ?_
  refine hWalk _ _ _ _ ⟨c, F0, s1', R, rfl, hinv1, hm1, ?_⟩
  intro fuel2 sc2 m2 s2' hlen2 hfuel2 hpres2 hm2
  have hinv2 : FullCoreInv c F0 s2' := ⟨hlen2,
    let ⟨Fc, hw1⟩ := hinv1.witness; ⟨Fc, m7Witness_with_fuel hw1⟩⟩
  have hfuel12 : fuel2.toNat ≤ s.core.fuel.toNat := by
    have hs1f : s1'.core.fuel = fuel1 := rfl
    rw [hs1f] at hfuel2; omega
  exact hQ vals1 flags1 lvl1 rsns1 trl1 tp1 ftrl1 fdec1 te1 prop1 prob1 unass1 unfl1 wvec1 arena1
    wstk1 wlen1 wu1 fuel2 ctype1 cref1 c01 c11 oom1 sc2 m2 hinv2 hperm1 hfuel12
    ⟨hpres2.1.trans hpres1.1, hpres2.2.trans hpres1.2⟩ hprob1 hm2

/-! ### Module spec table, environment, certification & concrete non-vacuity -/

/-- Closed 19-row spec table for `m7WalkModule` (`13` defined functions + `6` externs), all with
`noExit = true`. -/
def m7WalkSpecTable : List SpecEntry :=
  [ SpecEntry.ofFn full_walk_cb_inv_m7 m7CbInvSpec true
  , SpecEntry.ofFn full_walk_init_table_m7 m7InitTableSpec true
  , SpecEntry.ofFn full_walk_effort_m7 m7EffortSpec true
  , SpecEntry.ofFn full_walk_init_vals_m7 m7InitValsSpec true
  , SpecEntry.ofFn full_walk_collect_m7 m7CollectSpec true
  , SpecEntry.ofFn full_walk_build_occ_m7 m7BuildOccSpec true
  , SpecEntry.ofFn full_walk_break_m7 m7BreakSpec true
  , SpecEntry.ofFn full_walk_pick_m7 m7PickSpec true
  , SpecEntry.ofFn full_walk_flip_m7 m7FlipSpec true
  , SpecEntry.ofFn full_walk_save_min_m7 m7SaveMinSpec true
  , SpecEntry.ofFn full_walk_m7 fullWalkSpec true
  , SpecEntry.ofFn full_warmup_m7 fullWarmupSpec true
  , SpecEntry.ofFn full_walk_warmup_m7 fullWarmupSpec true
  , SpecEntry.mk "full_rng_next" [i64] [i64] fullRngNextSpec true
  , SpecEntry.mk "full_arena_next" [i64, i32] [i32] fullArenaNextSpec true
  , SpecEntry.mk "full_next_dec_var" [i64] [i64] fullNextDecVarSpec true
  , SpecEntry.mk "full_assign" [i64, i32, i32] [] fullAssignSpec true
  , SpecEntry.mk "full_propagate" [i64] [i64] fullPropagateSpec true
  , SpecEntry.mk "full_backtrack" [i64, i64] [] fullBacktrackSpec true ]

/-- Relational environment induced by `m7WalkSpecTable`. -/
def m7WalkEnv : Env := Env.ofTable m7WalkSpecTable

private theorem m7WalkSpecTable_nodup : (m7WalkSpecTable.map SpecEntry.name).Nodup := by
  decide

private theorem m7WalkSpecTable_noExit_all :
    ∀ e ∈ m7WalkSpecTable, e.noExit = true := by
  intro e he
  simp only [m7WalkSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- All entries in `m7WalkEnv` satisfy `XPost`-weakening (`noExit = true`). -/
theorem m7WalkEnv_noExit (f : Sym) (as bs : List Ty) (xs : Tup Val as) (m : Mem 64)
    (Q : Post bs) (X X' : XPost) :
    m7WalkEnv f as bs xs m Q X → m7WalkEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7WalkSpecTable_noExit_all f as bs xs m Q X X'

private theorem m7WalkEnv_lookup (e : SpecEntry) (he : e ∈ m7WalkSpecTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (hs : e.spec xs m Q (fun _ _ _ _ => False)) (hne : e.noExit = true) :
    m7WalkEnv e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem he m7WalkSpecTable_nodup (by simpa [SpecEntry.eff, hne] using hs)

private theorem m7WalkEnv_ofFn (fn : Fn) (spec : Spec fn.as fn.rs)
    (he : SpecEntry.ofFn fn spec true ∈ m7WalkSpecTable)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hs : spec xs m Q (fun _ _ _ _ => False)) :
    m7WalkEnv fn.name fn.as fn.rs xs m Q X :=
  m7WalkEnv_lookup (SpecEntry.ofFn fn spec true) he hs rfl

private theorem m7WalkEnv_ext (nm : Sym) (as bs : List Ty) (spec : Spec as bs)
    (he : SpecEntry.mk nm as bs spec true ∈ m7WalkSpecTable)
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hs : spec xs m Q (fun _ _ _ _ => False)) :
    m7WalkEnv nm as bs xs m Q X :=
  m7WalkEnv_lookup (SpecEntry.mk nm as bs spec true) he hs rfl

/-- `m7WalkEnv` satisfies every row of `m7WalkSpecTable`. -/
theorem m7Walk_tableImpl :
    TableImpl m7WalkEnv m7WalkModule.fns m7WalkSpecTable := by
  have hCbInv : ∀ a m Q X, m7CbInvSpec a m Q X →
      m7WalkEnv "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_cb_inv_m7 m7CbInvSpec
      (by simp [m7WalkSpecTable]) (m7CbInvSpec_noExit h)
  have hInitTable : ∀ a m Q X, m7InitTableSpec a m Q X →
      m7WalkEnv "full_walk_init_table_m7" [i64, i64] [] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_init_table_m7 m7InitTableSpec
      (by simp [m7WalkSpecTable]) (m7InitTableSpec_noExit h)
  have hEffort : ∀ a m Q X, m7EffortSpec a m Q X →
      m7WalkEnv "full_walk_effort_m7" [i64, i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_effort_m7 m7EffortSpec
      (by simp [m7WalkSpecTable]) (m7EffortSpec_noExit h)
  have hInitVals : ∀ a m Q X, m7InitValsSpec a m Q X →
      m7WalkEnv "full_walk_init_vals_m7" [i64] [] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_init_vals_m7 m7InitValsSpec
      (by simp [m7WalkSpecTable]) (m7InitValsSpec_noExit h)
  have hCollect : ∀ a m Q X, m7CollectSpec a m Q X →
      m7WalkEnv "full_walk_collect_m7" [i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_collect_m7 m7CollectSpec
      (by simp [m7WalkSpecTable]) (m7CollectSpec_noExit h)
  have hBuildOcc : ∀ a m Q X, m7BuildOccSpec a m Q X →
      m7WalkEnv "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_build_occ_m7 m7BuildOccSpec
      (by simp [m7WalkSpecTable]) (m7BuildOccSpec_noExit h)
  have hBreak : ∀ a m Q X, m7BreakSpec a m Q X →
      m7WalkEnv "full_walk_break_m7" [i64, i32, i64] [i32] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_break_m7 m7BreakSpec
      (by simp [m7WalkSpecTable]) (m7BreakSpec_noExit h)
  have hPick : ∀ a m Q X, m7PickSpec a m Q X →
      m7WalkEnv "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_pick_m7 m7PickSpec
      (by simp [m7WalkSpecTable]) (m7PickSpec_noExit h)
  have hFlip : ∀ a m Q X, m7FlipSpec a m Q X →
      m7WalkEnv "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_flip_m7 m7FlipSpec
      (by simp [m7WalkSpecTable]) (m7FlipSpec_noExit h)
  have hSaveMin : ∀ a m Q X, m7SaveMinSpec a m Q X →
      m7WalkEnv "full_walk_save_min_m7" [i64, i64, Ty.bool] [] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_save_min_m7 m7SaveMinSpec
      (by simp [m7WalkSpecTable]) (m7SaveMinSpec_noExit h)
  have hWalk : ∀ a m Q X, fullWalkSpec a m Q X →
      m7WalkEnv "full_walk_m7" [i64] [] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_walk_m7 fullWalkSpec
      (by simp [m7WalkSpecTable]) (by dsimp only [fullWalkSpec] at h ⊢; exact h)
  have hWarmup : ∀ a m Q X, fullWarmupSpec a m Q X →
      m7WalkEnv "full_warmup_m7" [i64] [] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ofFn full_warmup_m7 fullWarmupSpec
      (by simp [m7WalkSpecTable]) (by dsimp only [fullWarmupSpec] at h ⊢; exact h)
  have hRng : ∀ a m Q X, fullRngNextSpec a m Q X →
      m7WalkEnv "full_rng_next" [i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ext "full_rng_next" [i64] [i64] fullRngNextSpec
      (by simp [m7WalkSpecTable]) (by dsimp only [fullRngNextSpec] at h ⊢; exact h)
  have hArena : ∀ a m Q X, fullArenaNextSpec a m Q X →
      m7WalkEnv "full_arena_next" [i64, i32] [i32] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ext "full_arena_next" [i64, i32] [i32] fullArenaNextSpec
      (by simp [m7WalkSpecTable]) (by dsimp only [fullArenaNextSpec] at h ⊢; exact h)
  have hNDV : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      m7WalkEnv "full_next_dec_var" [i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ext "full_next_dec_var" [i64] [i64] fullNextDecVarSpec
      (by simp [m7WalkSpecTable])
      (by dsimp only [fullNextDecVarSpec, SafetySlice.spec] at h ⊢; exact h)
  have hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      m7WalkEnv "full_assign" [i64, i32, i32] [] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ext "full_assign" [i64, i32, i32] [] fullAssignSpec
      (by simp [m7WalkSpecTable]) (by dsimp only [fullAssignSpec] at h ⊢; exact h)
  have hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      m7WalkEnv "full_propagate" [i64] [i64] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ext "full_propagate" [i64] [i64] fullPropagateSpec
      (by simp [m7WalkSpecTable]) (by dsimp only [fullPropagateSpec] at h ⊢; exact h)
  have hBT : ∀ a m Q X, fullBacktrackSpec a m Q X →
      m7WalkEnv "full_backtrack" [i64, i64] [] a m Q X :=
    fun _ _ _ _ h => m7WalkEnv_ext "full_backtrack" [i64, i64] [] fullBacktrackSpec
      (by simp [m7WalkSpecTable]) (by dsimp only [fullBacktrackSpec] at h ⊢; exact h)
  dsimp only [m7WalkModule, m7WalkFns, m7Walk_fns, m7WalkSpecTable, TableImpl]
  refine ⟨SpecEntry.Impl.of (full_walk_cb_inv_m7_wp m7WalkEnv), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_init_table_m7_wp m7WalkEnv), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_effort_m7_wp m7WalkEnv), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_init_vals_m7_wp m7WalkEnv), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_collect_m7_wp m7WalkEnv hArena), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_build_occ_m7_wp m7WalkEnv), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_break_m7_wp m7WalkEnv), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_pick_m7_wp m7WalkEnv hBreak hRng), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_flip_m7_wp m7WalkEnv), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_save_min_m7_wp m7WalkEnv), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_walk_m7_wp m7WalkEnv hInitVals hCollect hCbInv hInitTable
    hBuildOcc hEffort hPick hFlip hSaveMin), ?_⟩
  refine ⟨SpecEntry.Impl.of (full_warmup_m7_wp m7WalkEnv hNDV hAssign hProp hBT), ?_⟩
  exact ⟨SpecEntry.Impl.of (full_walk_warmup_m7_wp m7WalkEnv hWarmup hWalk), trivial⟩

private theorem m7Walk_allFns_wf : AllFns Fn.Wf m7WalkModule.fns := by
  have helper : ∀ fs : List Fn, (∀ f ∈ fs, f.Wf) → AllFns Fn.Wf fs := by
    intro fs h
    induction fs with
    | nil => exact trivial
    | cons f rest ih => exact ⟨h f (by simp), ih (fun x hx => h x (by simp [hx]))⟩
  exact helper m7WalkModule.fns m7WalkFns_wf

/-- Complete closed `ModuleOk` theorem for `m7WalkModule` under `m7WalkEnv`. -/
theorem m7Walk_moduleOk : ModuleOk m7WalkEnv m7WalkModule :=
  Env.ofTable_moduleOk m7Walk_acyclic m7Walk_allFns_wf m7Walk_tableImpl

/-! ### Concrete non-vacuity on `nvOneLitCfg` (`XPost := False`) -/

private theorem nvM7_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core := by
  have hvb : Examples.Kissat.VarsBounded 1 [[0], [1]] := by
    intro cl hcl l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl <;>
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl; decide
  have harena : FullArenaClausesInv nvOneLitCfg [[0], [1]] nvOneLitState.core :=
    ⟨Or.inl rfl,
     fun _ hr => False.elim (List.not_mem_nil hr),
     fun _ hr => False.elim (List.not_mem_nil hr),
     fun _ hr => False.elim (List.not_mem_nil hr),
     fun _ hr => False.elim (List.not_mem_nil hr)⟩
  have hlayout : WatchStackLayout nvOneLitState.core :=
    ⟨fun l hl => by
       have hl2 : l = 0 ∨ l = 1 := by simp [nvOneLitState] at hl; omega
       rcases hl2 with rfl | rfl <;>
         simp [fullWatchOffCore, fullWatchSizeCore, nvOneLitState],
     fun l hl hpos => by
       have hl2 : l = 0 ∨ l = 1 := by simp [nvOneLitState] at hl; omega
       rcases hl2 with rfl | rfl <;>
         simp [fullWatchSizeCore, nvOneLitState] at hpos,
     fun l1 _ h1 _ _ hpos _ => by
       have hl2 : l1 = 0 ∨ l1 = 1 := by simp [nvOneLitState] at h1; omega
       rcases hl2 with rfl | rfl <;>
         simp [fullWatchSizeCore, nvOneLitState] at hpos,
     fun l hl idx hidx => by
       have hl2 : l = 0 ∨ l = 1 := by simp [nvOneLitState] at hl; omega
       rcases hl2 with rfl | rfl <;>
         simp [fullWatchSizeCore, nvOneLitState] at hidx⟩
  have hwatches : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    change WatchesInv [[0], [1]] nvOneLitState.core
    refine ⟨hlayout, fun l hl => ?_⟩
    have hl2 : l = 0 ∨ l = 1 := by simp [nvOneLitState] at hl; omega
    rcases hl2 with rfl | rfl <;>
      simpa [fullWatchOffCore, fullWatchSizeCore, nvOneLitState] using WatchSliceOk.empty
  refine ⟨⟨hvb, id⟩, fun h => absurd rfl h, harena, hwatches, by decide, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; simp [nvOneLitState] at hi; subst hi; decide
  · intro i j hi hj _; simp [nvOneLitState] at hi hj; omega
  · intro l hl
    have hl2 : l = 0 ∨ l = 1 := by simp [nvOneLitState] at hl; omega
    rcases hl2 with rfl | rfl
    · right; left; rfl
    · right; right; rfl
  · intro l hl
    have hl2 : l = 0 ∨ l = 1 := by simp [nvOneLitState] at hl; omega
    rcases hl2 with rfl | rfl
    · constructor
      · intro _; exact ⟨0, by decide, rfl⟩
      · intro _; rfl
    · constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨i, hi, heq⟩; simp [nvOneLitState] at hi heq; subst hi; contradiction
  · intro l hl
    have hl2 : l = 0 ∨ l = 1 := by simp [nvOneLitState] at hl; omega
    rcases hl2 with rfl | rfl
    · constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨i, hi, heq⟩; simp [nvOneLitState] at hi heq; subst hi; contradiction
    · constructor
      · intro _; exact ⟨0, by decide, rfl⟩
      · intro _; rfl
  · intro i hi; simp [nvOneLitState] at hi; subst hi; decide
  · intro i j hi hj _ _; simp [nvOneLitState] at hi hj; omega
  · intro L h1 h0; simp [nvOneLitState] at h0; omega
  · intro i hi _; simp [nvOneLitState] at hi; subst hi
    exact Examples.Kissat.entails_mem_cnfOfClauses (by simp [nvOneLitState])
  · intro i hi; simp [nvOneLitState] at hi; subst hi; rfl
  · intro i hi _; simp [nvOneLitState] at hi; subst hi; rfl
  · intro L hL; simp [nvOneLitState] at hL; subst hL; decide
  · intro L1 L2 _ hL2
    have h1 : L1 = 0 := by simp [nvOneLitState] at hL2; omega
    have h2 : L2 = 0 := by simp [nvOneLitState] at hL2; omega
    subst h1; subst h2; exact Nat.le_refl _
  · intro L h1 h0; simp [nvOneLitState] at h0; omega
  · intro L h1 h0; simp [nvOneLitState] at h0; omega
  · intro idx hi; simp [nvOneLitState] at hi; subst hi; exact fun h => absurd rfl h
  · intro idx hi; simp [nvOneLitState] at hi; subst hi; exact fun h => absurd rfl h

private theorem m7Walk_fns_nodup : (m7WalkModule.fns.map Fn.name).Nodup := by
  decide

/-- Concrete non-vacuity of `full_walk_m7` on `nvOneLitCfg` (`XPost := False`). -/
theorem nv_m7_walk :
    Func.wp m7WalkEnv full_walk_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun _ m' => ∃ s' : FullState, s'.LengthsOk nvOneLitCfg ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hinv : FullCoreInv nvOneLitCfg nvOneLitF0 nvOneLitState :=
    ⟨nvOneLit_lengths, ⟨[[0], [1]], nvM7_witness⟩⟩
  refine Env.ofTable_sound m7Walk_fns_nodup m7Walk_tableImpl full_walk_m7
    (by simp [m7WalkModule, m7WalkFns, m7Walk_fns]) (nvOneLitCfg.hdr, ()) nvOneLitMem _ _ ?_
  refine m7WalkEnv_ofFn full_walk_m7 fullWalkSpec (by simp [m7WalkSpecTable]) ?_
  refine ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, Std.ExtHashMap.emp, rfl, hinv,
    by rw [Std.ExtHashMap.sep_emp]; exact nvOneLitMem_ok, ?_⟩
  intro _ _ _ _ hlen' _ _ hm'
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨_, hlen', hm'⟩

/-- Concrete non-vacuity of `full_warmup_m7` on `nvOneLitCfg` (`XPost := False`). -/
theorem nv_m7_warmup :
    Func.wp m7WalkEnv full_warmup_m7_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun _ m' => ∃ s' : FullState, FullCoreInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.probing = 0#64 ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hinv : FullCoreInv nvOneLitCfg nvOneLitF0 nvOneLitState :=
    ⟨nvOneLit_lengths, ⟨[[0], [1]], nvM7_witness⟩⟩
  refine Env.ofTable_sound m7Walk_fns_nodup m7Walk_tableImpl full_warmup_m7
    (by simp [m7WalkModule, m7WalkFns, m7Walk_fns]) (nvOneLitCfg.hdr, ()) nvOneLitMem _ _ ?_
  refine m7WalkEnv_ofFn full_warmup_m7 fullWarmupSpec (by simp [m7WalkSpecTable]) ?_
  refine ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, Std.ExtHashMap.emp, rfl, hinv, rfl,
    by rw [Std.ExtHashMap.sep_emp]; exact nvOneLitMem_ok, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ prob' _ _ _ _ _ _ _ _ _ _ _ _ sc' m' _ hinv' _ _ _ hprob' hm'
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨_, hinv', hprob' rfl, hm'⟩

end

end LeanQbe.T.Examples.Kissat.FullM7Walk
