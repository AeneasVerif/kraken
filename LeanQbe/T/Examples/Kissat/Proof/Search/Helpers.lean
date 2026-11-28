/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Search.Spec
public import LeanQbe.T.Examples.Kissat.Src.Search
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Search Segment Call Wrappers & Header/Region Helpers (`Proof.Search.Helpers`)

Shared parametric `(Γ : Env)` call wrappers, header load/store lemmas over `FullM6HdrMem`,
and post-compaction workspace restoration bridges for `Proof.Search.Wp0`, `Wp1`, and `Wp2`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Search

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Pure & Invariant Preservation Helpers -/

theorem fullM6HdrCfgOk_compat {c c' : FullCfg}
    (hcfg : FullM6HdrCfgOk c) (hc : FullCfgCompat c c') : FullM6HdrCfgOk c' := by
  unfold FullM6HdrCfgOk at hcfg ⊢
  rw [hc.hdr]
  exact hcfg

theorem fullCfgCompat_refl (c : FullCfg) : FullCfgCompat c c :=
  ⟨rfl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fullCfgCompat_trans {c0 c1 c2 : FullCfg}
    (h01 : FullCfgCompat c0 c1) (h12 : FullCfgCompat c1 c2) : FullCfgCompat c0 c2 :=
  ⟨h12.hdr.trans h01.hdr, h12.avail.trans h01.avail, Nat.le_trans h12.mv_le h01.mv_le,
   h12.max_vars.trans h01.max_vars, h12.nc.trans h01.nc,
   h12.arena_cap.trans h01.arena_cap, h12.wcap.trans h01.wcap,
   h12.delayed_cap.trans h01.delayed_cap, h12.red_cap.trans h01.red_cap,
   h12.extend_cap.trans h01.extend_cap, h12.scratch_cap.trans h01.scratch_cap⟩

theorem m6Hdr_store_search_ticks_len {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hl : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    let s' := HdrWordField.search_ticks.set s v
    storeOk m i64 (c.hdr + 0x258#64) ∧
      s'.LengthsOk c ∧
      s'.core = s.core ∧
      s'.scratch.extend_len = s.scratch.extend_len ∧
      (FullM6HdrMem c ext s' ⋆ R) (storeMem m i64 (c.hdr + 0x258#64) v) := by
  have hst := fullHdr_store_ofOff (off := 600) (f := .search_ticks) rfl rfl v
    (fullM6HdrMem_focus hm)
  let s' := HdrWordField.search_ticks.set s v
  have hsc : s'.scratch.LengthsOk c := by
    have hs0 := hl.scratch_ok
    exact ⟨hs0.walk_vals_len, hs0.phases_len, hs0.phases_target_len, hs0.phases_best_len,
      hs0.walk_best_len, hs0.heap_len_arr, hs0.pos_len, hs0.shrink_stk_len, hs0.q_prev_len,
      hs0.q_next_len, hs0.q_stamp_len, hs0.wsort_len, hs0.work_stk1_len, hs0.work_stk2_len,
      hs0.tarjan_mark_len, hs0.tarjan_reach_len, hs0.score_len, hs0.sim_sig_len,
      hs0.glue_used_len, hs0.last_learned_len, hs0.delayed_len_arr, hs0.red_refs_len,
      hs0.extend_stk_len, hs0.scratch_buf_len⟩
  exact ⟨hst.1, ⟨hl.core_ok, hsc⟩, rfl, rfl, fullM6HdrMem_unfocus hst.2⟩

theorem fullArenaVarsNodup_of_permEq {s s' : FullState}
    (hn : FullArenaVarsNodup s) (hp : FullArenaPermEq s.core s'.core) :
    FullArenaVarsNodup s' := by
  intro r hr hng
  have hr0 : r ∈ fullArenaClauseRefs s := by
    dsimp [fullArenaClauseRefs] at hr ⊢
    exact hp.2.1 ▸ hr
  have hinfo := hp.2.2 r hr0
  have hng0 : fullArenaClauseGarb s r = false := by
    dsimp [fullArenaClauseGarb] at hng ⊢
    exact hinfo.2.1 ▸ hng
  have hnd : (List.map (fun x => x / 2) (fullArenaClauseLitsCore s.core r)).Nodup :=
    hn r hr0 hng0
  exact (List.Perm.nodup_iff (List.Perm.map (fun x => x / 2) hinfo.2.2)).mpr hnd

theorem fullLastLearnedWf_of_permEq {s s' : FullState}
    (hlw : FullLastLearnedWf s) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hp : FullArenaPermEq s.core s'.core) : FullLastLearnedWf s' := by
  intro i hi
  have h0 := hlw i hi
  dsimp only [fullArenaClauseRefs] at h0 ⊢
  rw [hll]
  rcases h0 with h | h
  · exact Or.inl h
  · exact Or.inr (hp.2.1 ▸ h)

theorem fullCoreLengthsOk_with_fuel {c : FullCfg} {k : FullCoreState} (fuel' : BitVec 64)
    (hl : FullCoreState.LengthsOk c k) :
    FullCoreState.LengthsOk c { k with fuel := fuel' } :=
  ⟨hl.vals_len, hl.lit_mark_len, hl.mrk_len, hl.flags_len, hl.lvl_len, hl.rsns_len,
   hl.trl_len, hl.trail_pos_len, hl.tmp_len_arr, hl.min_clr_len_arr, hl.frame_trail_len,
   hl.frame_dec_len, hl.wvec_len, hl.repr_len, hl.min_stk_len, hl.arena_len_arr,
   hl.wstk_len_arr, hl.cur_vars_ge, hl.cur_vars_le, hl.arena_len_le, hl.wlen_le,
   hl.trail_end_le, hl.propagated_le, hl.tmp_len_le, hl.min_clr_len_le⟩

theorem fullM6HdrInv_with_fuel {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (fuel' : BitVec 64) (hinv : FullM6HdrInv c F0 ext s) :
    FullM6HdrInv c F0 ext { core := { s.core with fuel := fuel' }, scratch := s.scratch } :=
  let s' : FullState := { core := { s.core with fuel := fuel' }, scratch := s.scratch }
  have hlen' : s'.LengthsOk c :=
    ⟨fullCoreLengthsOk_with_fuel fuel' hinv.sparse.lengths.core_ok, hinv.sparse.lengths.scratch_ok⟩
  ⟨hinv.cfgOk, hinv.extOk,
    FullSparseInv.with_fuel_scratch hinv.sparse hlen' rfl (fullExtScratchPres_refl s)⟩

private theorem watchSliceOk_with_unflushed {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : WatchSliceOk F_cur k lit p rem) :
    WatchSliceOk F_cur { k with unflushed := 0#64 } lit p rem := by
  induction h with
  | empty => exact WatchSliceOk.empty
  | bin hw h1 h2 h3 h4 _ ih => exact WatchSliceOk.bin hw h1 h2 h3 h4 ih
  | large hw0 hwc h1 h2 h3 _ ih => exact WatchSliceOk.large hw0 hwc h1 h2 h3 ih

private theorem denseWatchSliceOk_with_unflushed {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) :
    DenseWatchSliceOk F_cur { k with unflushed := 0#64 } lit p rem := by
  induction h with
  | empty => exact DenseWatchSliceOk.empty
  | bin hw h1 h2 h3 h4 _ ih => exact DenseWatchSliceOk.bin hw h1 h2 h3 h4 ih
  | occ hw0 hwc h1 h2 h3 h4 _ ih => exact DenseWatchSliceOk.occ hw0 hwc h1 h2 h3 h4 ih

theorem fullM6HdrInv_clear_unflushed {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (hinv : FullM6HdrInv c F0 ext s) :
    FullM6HdrInv c F0 ext (HdrWordField.unflushed.set s 0#64) := by
  have hsp := hinv.sparse
  refine ⟨hinv.cfgOk, hinv.extOk, ?_⟩
  have hl : (HdrWordField.unflushed.set s 0#64).LengthsOk c := by
    refine ⟨?_, hsp.lengths.scratch_ok⟩
    have hl0 := hsp.lengths.core_ok
    exact ⟨hl0.vals_len, hl0.lit_mark_len, hl0.mrk_len, hl0.flags_len, hl0.lvl_len,
      hl0.rsns_len, hl0.trl_len, hl0.trail_pos_len, hl0.tmp_len_arr, hl0.min_clr_len_arr,
      hl0.frame_trail_len, hl0.frame_dec_len, hl0.wvec_len, hl0.repr_len, hl0.min_stk_len,
      hl0.arena_len_arr, hl0.wstk_len_arr, hl0.cur_vars_ge, hl0.cur_vars_le,
      hl0.arena_len_le, hl0.wlen_le, hl0.trail_end_le, hl0.propagated_le,
      hl0.tmp_len_le, hl0.min_clr_len_le⟩
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  have hwt : ModeWatchesInv F_cur (HdrWordField.unflushed.set s 0#64).core := by
    have hm := hw.watches
    dsimp only [ModeWatchesInv] at hm ⊢
    change (if s.core.dense_mode = 0#64 then
        WatchesInv F_cur s.core
      else DenseWatchesInv F_cur s.core) at hm
    change (if s.core.dense_mode = 0#64 then
        WatchesInv F_cur { s.core with unflushed := 0#64 }
      else DenseWatchesInv F_cur { s.core with unflushed := 0#64 })
    split at hm <;> split
    · exact ⟨⟨hm.layout.bounds, hm.layout.pos_off, hm.layout.disjoint, hm.layout.no_sentinel⟩,
        fun l hl => watchSliceOk_with_unflushed (hm.slices l hl)⟩
    · contradiction
    · contradiction
    · exact ⟨⟨hm.layout.bounds, hm.layout.pos_off, hm.layout.disjoint, hm.layout.no_sentinel⟩,
        fun l hl => denseWatchSliceOk_with_unflushed (hm.slices l hl)⟩
  have hw' : FullWitnessInv c F0 F_cur (HdrWordField.unflushed.set s 0#64).core :=
    ⟨hw.ext_sound, hw.inconsistent_sound,
      ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt, hw.arena.entails⟩,
      hwt, hw.cur_level_le, hw.trail_lits_lt, hw.trail_vars_nodup, hw.vals_domain,
      hw.vals_true_iff, hw.vals_false_iff, hw.lvl_le, hw.dec_earliest, hw.levels_inhabited,
      hw.level0_sound, hw.trail_pos_inv, hw.level0_rsn_none, hw.frame_trail_lt,
      hw.frame_trail_mono, hw.frame_trail_before_lt, hw.frame_dec_lt, hw.reason_inv,
      hw.reason_lit_mem⟩
  exact ⟨⟨hl, ⟨F_cur, hw'⟩⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

/-! ## 2. Header Load / Store Stepping Helpers over `FullM6HdrMem` -/

theorem m6Hdr_load_off {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (f : HdrWordField) (off : Nat)
    (hoff : HdrWordField.ofOff? off = some f) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 off) = some (f.get c s) :=
  fullHdr_load_ofOff hoff (fullM6HdrMem_focus hm)

theorem m6Hdr_store_scr {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} (f : HdrWordField) (off : Nat)
    (hoff : HdrWordField.ofOff? off = some f) (hmut : f.isMutable = true)
    (hscr : f.isScrPres = true) (v : BitVec 64) (hinv : FullM6HdrInv c F0 ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    storeOk m i64 (c.hdr + BitVec.ofNat 64 off) ∧
      FullM6HdrInv c F0 ext (f.set s v) ∧
      (FullM6HdrMem c ext (f.set s v) ⋆ R)
        (storeMem m i64 (c.hdr + BitVec.ofNat 64 off) v) := by
  have hst := fullHdr_store_ofOff hoff hmut v (fullM6HdrMem_focus hm)
  exact ⟨hst.1, fullM6HdrInv_upd_scrHdr f hscr hinv v, fullM6HdrMem_unfocus hst.2⟩

theorem m6Hdr_store_fuel_sub1 {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    let s' := HdrWordField.fuel.set s (s.core.fuel - 1#64)
    storeOk m i64 (c.hdr + 0xa8#64) ∧
      FullM6HdrInv c F0 ext s' ∧
      (FullM6HdrMem c ext s' ⋆ R) (storeMem m i64 (c.hdr + 0xa8#64) (s.core.fuel - 1#64)) := by
  have hst := fullHdr_store_ofOff (off := 168) (f := .fuel) rfl rfl (s.core.fuel - 1#64)
    (fullM6HdrMem_focus hm)
  exact ⟨hst.1, fullM6HdrInv_with_fuel (s.core.fuel - 1#64) hinv, fullM6HdrMem_unfocus hst.2⟩

theorem m6Hdr_store_unflushed0 {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    let s' := HdrWordField.unflushed.set s 0#64
    storeOk m i64 (c.hdr + 0x200#64) ∧
      FullM6HdrInv c F0 ext s' ∧
      (FullM6HdrMem c ext s' ⋆ R) (storeMem m i64 (c.hdr + 0x200#64) 0#64) := by
  have hst := fullHdr_store_ofOff (off := 512) (f := .unflushed) rfl rfl 0#64
    (fullM6HdrMem_focus hm)
  exact ⟨hst.1, fullM6HdrInv_clear_unflushed hinv, fullM6HdrMem_unfocus hst.2⟩

theorem bv64_sub1_lt {f : BitVec 64} (hne : f ≠ 0#64) : (f - 1#64).toNat < f.toNat := by
  have hpos : 0 < f.toNat := by
    rcases Nat.eq_zero_or_pos f.toNat with hz | hp
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [hz])) hne
    · exact hp
  have hlt : f.toNat < 2 ^ 64 := f.isLt
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_sub]
  simp
  omega

/-! ## 3. Parametric Call Wrappers (`FullM6HdrMem`-threaded) -/

theorem search_call_lucky_late {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, Lucky.Spec.fullLuckyLateM7Spec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_lucky_late_m7" args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  exact ⟨c, F0, ext, s, R, rfl, hinv, hm,
    fun r ext' s' m' hs' hext' hr hfuel _ h20 h02 h10 hm' =>
      hk r ext' s' m' hs' hext' hr hfuel h20 h02 h10 hm'⟩

theorem search_call_propagate {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, PropSearch.Spec.propagateM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      s.core.trail_end ≤ s'.core.trail_end →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → ∃ F_cur, s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullM6HdrInvW c F0 F_cur ext' s' ∧ FullWitnessInv c F0 F_cur s'.core ∧
        FullConflictOkW F_cur s') →
      (r = 2#64 → s'.core.oom ≠ 0#64 ∨ s'.core.fuel = 0#64) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_propagate" args k) m := by
  obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine ⟨c, F0, F_cur, ext, s, R, rfl, hinv.cfgOk, hinv.extOk, hinv.sparse.lengths,
    hw, hinv.sparse.2.2.2.2, hm, ?_⟩
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m' s'
    hext' _ hlen' hw' hte_ext _ hperm hprobe_pr _ _ _ _ hfuel hr h0 h1 h2 _ hm'
  have hll_wf : FullLastLearnedWf s' :=
    fullLastLearnedWf_of_permEq hinv.sparse.2.2.2.1.1 hprobe_pr.1.1 hperm
  have hext_ok : FullExtScratchOk c s' :=
    ⟨hll_wf, hprobe_pr.1.2 ▸ hinv.sparse.2.2.2.1.2⟩
  have hnodup : FullArenaVarsNodup s' :=
    fullArenaVarsNodup_of_permEq hinv.sparse.2.2.1 hperm
  have hinvW' : FullM6HdrInvW c F0 F_cur ext' s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hext'
      ⟨hlen', hw', hinv.sparse.2.1, hnodup, hext_ok, hinv.sparse.2.2.2.2⟩
  exact hk r ext' s' m' hinvW'.toInv rfl rfl hfuel hr hte_ext.1 h0
    (fun h1eq => let ⟨hf, ho, hc⟩ := h1 h1eq; ⟨F_cur, hf, ho, hinvW', hw', hc⟩)
    h2 hm'

theorem search_call_arena_sweep {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m',
      FullM6HdrInv c F0 ext s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = 0 →
      s'.core.fuel = s.core.fuel →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      (r = 0#64 ∨ r = 1#64 → s'.core.oom = 0#64) →
      (r = 1#64 → s.core.trail_end < s'.core.trail_end) →
      (r = 2#64 → F0.Unsat) →
      (r = 3#64 → s'.core.oom ≠ 0#64) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_arena_sweep" args k) m := by
  obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine ⟨c, F0, F_cur, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
    hinv.sparse.lengths, hw, hinv.sparse.2.2.1, hinv.sparse.2.2.2.2,
    (fun hlt => absurd hlt (by omega)), hmf, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena'
    alen' wlen' wu' fred' ni' nr' nb' oom' sc' m' s'
    hlen' hr hex_len hws2 hll' hw' hnodup' h01 _ h1 h2 h3 hm'
  have hext' : FullExtScratchOk c s' :=
    ⟨hll', hex_len ▸ hinv.sparse.2.2.2.1.2⟩
  have hinv' : FullM6HdrInv c F0 ext s' :=
    ⟨hinv.cfgOk, hinv.extOk,
      ⟨⟨hlen', ⟨F_cur, hw'⟩⟩, hinv.sparse.2.1, hnodup', hext', hinv.sparse.2.2.2.2⟩⟩
  exact hk r s' m' hinv' rfl hl0 rfl hr h01 (fun he1 => (h1 he1).2) (fun he2 => (h2 he2).2)
    h3 (fullM6HdrMem_unfocus hm')

theorem search_call_compact_needed {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [.bool] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, Compact.Spec.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ res : Bool, wp Γ Q X (k (res, ())) m) :
    wp Γ Q X (Expr.call "full_compact_needed" args k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have h1 := hinv.sparse.1.witness
    have := hinv.sparse.lengths.core_ok.cur_vars_le
    have := c.hmaxv
    have : 2 * Ref.dimacsBound ≤ 2 ^ 64 := by unfold Ref.dimacsBound; decide
    rcases h1 with ⟨_, hw⟩
    have := hw.cur_level_le
    have := hinv.sparse.lengths.core_ok.trail_end_le
    omega
  exact ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.lengths, hcl_lt, hmf,
    fun res _ => hk res⟩

theorem search_call_compact {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, Compact.Spec.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_compact" args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  exact ⟨c, F0, ext, s, R, rfl, hinv, hm, hk⟩

theorem search_call_scale_delta {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost} (base : BitVec 64)
    (hargs : vals args = (c.hdr, base, ()))
    (hfn : ∀ a m Q X, Limits.Spec.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ delta : BitVec 64, wp Γ Q X (k (delta, ())) m) :
    wp Γ Q X (Expr.call "full_scale_delta_m5" args k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  exact ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.lengths, hmf, hk⟩

theorem search_call_probe {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost} (initial : Bool)
    (hargs : vals args = (c.hdr, initial, ()))
    (hfn : ∀ a m Q X, Probe.Spec.fullProbeM6Spec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_probe_m6" args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  exact ⟨c, F0, ext, s, R, rfl, hinv, hl0, hm, hk⟩

theorem search_call_eliminate {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost} (initial : Bool)
    (hargs : vals args = (c.hdr, initial, ()))
    (hfn : ∀ a m Q X, Eliminate.Spec.fullEliminateM6Spec a m Q X →
      Γ "full_eliminate_m6" [i64, .bool] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_eliminate_m6" args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  exact ⟨c, F0, ext, s, R, rfl, hinv, hl0, hm, hk⟩

theorem search_call_backtrack0 {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, 0#64, ()))
    (hfn : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m',
      FullM6HdrInv c F0 ext s' → s'.core.cur_level = 0 →
      s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
      s'.core.inconsistent = s.core.inconsistent →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_backtrack" args k) m := by
  obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
  have hlen := hinv.sparse.lengths
  have hcv := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv
  have hte := hlen.core_ok.trail_end_le
  have hcl : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le
    have : 2 * Ref.dimacsBound ≤ 2 ^ 64 := by unfold Ref.dimacsBound; decide
    omega
  have hmv0 : (0 : Nat) < s.core.cur_level → 0 < c.max_vars := by
    intro hlt; have := hw.cur_level_le; omega
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hcl,
    (by simpa using hmv0), hw.trail_lits_lt, hmf, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s'
    hlen' _ _ hcl_eq hprobe_pr hsc_eq _ _ hbt_ok _ hm'
  have hcl0 : cl' = 0 := by simpa [Nat.min_zero] using hcl_eq
  have hw' : FullWitnessInv c F0 F_cur s'.core := hbt_ok F0 F_cur hw (Nat.zero_le _)
  have hll' : FullLastLearnedWf s' := by
    intro i hi
    have := hinv.sparse.2.2.2.1.1 i hi
    dsimp only [fullArenaClauseRefs] at this ⊢
    rw [hprobe_pr.1.1]; exact this
  have hext' : FullExtScratchOk c s' := ⟨hll', hprobe_pr.1.2 ▸ hinv.sparse.2.2.2.1.2⟩
  have hinv' : FullM6HdrInv c F0 ext s' :=
    ⟨hinv.cfgOk, hinv.extOk,
      ⟨⟨hlen', ⟨F_cur, hw'⟩⟩, hinv.sparse.2.1, hinv.sparse.2.2.1, hext', hinv.sparse.2.2.2.2⟩⟩
  exact hk s' m' hinv' hcl0 rfl rfl rfl (fullM6HdrMem_unfocus hm')

theorem search_call_update_classify {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core = s.core →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_update_classify_fid" args k) m := by
  refine m6Hdr_call_m6HdrW2a hargs (fun Q' X' => hfn _ m Q' X') hinv.cfgOk hinv.extOk
    hinv.sparse.lengths hm ?_
  rintro ⟨⟨⟩⟩ ext' s' m' hcore hlen' hpr' hext' _ hm'
  exact hk ext' s' m' (fullM6HdrInv_of_m6Pres (fullM6HdrInv_with_ext hinv hext') hlen' hcore hpr')
    hcore hm'

theorem search_call_set_watermark {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost} (w0 w1 : BitVec 64)
    (hargs : vals args = (c.hdr, w0, w1, ()))
    (hfn : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core = s.core →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "m6_hdr_set_watermark" args k) m := by
  refine m6Hdr_call_m6HdrW2a hargs (fun Q' X' => hfn _ m Q' X') hinv.cfgOk hinv.extOk
    hinv.sparse.lengths hm ?_
  rintro ⟨⟨⟩⟩ ext' s' m' hcore hlen' hpr' hext' _ hm'
  exact hk ext' s' m' (fullM6HdrInv_of_m6Pres (fullM6HdrInv_with_ext hinv hext') hlen' hcore hpr')
    hcore hm'

theorem search_call_analyze {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hconfl : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m',
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_vars = s.core.cur_vars ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_analyze_m6_hdr" args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine m6HdrAnalyzeSpec_of hinv hconfl hm ?_
  intro r ext' s' m' _ _ hr hcv hfl _ h20 _ h1 hm'
  exact hk r ext' s' m' hr h20 (fun eq1 =>
    let ⟨hW', hlt⟩ := h1 eq1
    ⟨hW'.toInv, hcv, hfl, hlt⟩) hm'

theorem search_call_reduce {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, false, ()))
    (hfn : ∀ a m Q X, Reduce.Spec.fullReduceM6Spec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s'.core.cur_level ≤ s.core.cur_level) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_reduce_m6" args k) m := by
  obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
  have hinvW : FullM6HdrInvW c F0 F_cur ext s :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hinv.sparse.lengths, hw, hinv.sparse.2.1, hinv.sparse.2.2.1,
       hinv.sparse.2.2.2.1, hinv.sparse.2.2.2.2⟩
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  exact ⟨c, F0, F_cur, ext, s, R, rfl, hinvW, hm,
    fun r c' ext' s' m' hc hinv' hr hcv hfl h20 h1 _ hm' =>
      hk r c' ext' s' m' hc hinv' hr hcv hfl h20 h1 hm'⟩

theorem search_call_switch_mode {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, Restart.Spec.fullSwitchModeM7Spec a m Q X →
      Γ "full_switch_mode_m7" [i64] [] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core = s.core →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_switch_mode_m7" args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine ⟨c, ext, s, R, rfl, hinv.cfgOk, hinv.extOk, hinv.sparse.lengths, hm, ?_⟩
  intro ext' s' m' hcore hlen' hpr hext' hm'
  exact hk ext' s' m' (⟨hinv.cfgOk, hext', FullSparseInv.with_fuel_scratch hinv.sparse hlen'
    (by rw [hcore]) hpr⟩) hcore hm'

theorem search_call_restart_due {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m',
      FullM6HdrInv c F0 ext s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = s.core.cur_level →
      s'.core.trail_end = s.core.trail_end →
      s'.core.fuel = s.core.fuel →
      s'.core.oom = s.core.oom →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_restart_due" args k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.lengths, hmf, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcpres hlen' ⟨_, hextpr⟩ hm'
  have hinv' : FullM6HdrInv c F0 ext s' :=
    ⟨hinv.cfgOk, hinv.extOk, FullSparseInv.of_safetySlice hinv.sparse hlen' hcpres hextpr⟩
  have hco := fullCoreState_agrees_with_scratch hcpres
  exact hk r s' m' hinv' (congrArg FullCoreState.cur_vars hco)
    (congrArg FullCoreState.cur_level hco) (congrArg FullCoreState.trail_end hco)
    (congrArg FullCoreState.fuel hco) (congrArg FullCoreState.oom hco)
    (fullM6HdrMem_unfocus hm')

theorem search_call_restart {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m',
      FullM6HdrInv c F0 ext s' → s'.core.fuel = s.core.fuel →
      s'.core.cur_level ≤ s.core.cur_level →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_restart" args k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine ⟨c, F0, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.1, hmf, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hcore' hle hexpr hm'
  have hll' : FullLastLearnedWf s' := by
    intro i hi
    have := hinv.sparse.2.2.2.1.1 i hi
    dsimp only [fullArenaClauseRefs] at this ⊢
    rw [hexpr.1]; exact this
  have hinv' : FullM6HdrInv c F0 ext s' :=
    ⟨hinv.cfgOk, hinv.extOk,
      ⟨hcore', hinv.sparse.2.1, hinv.sparse.2.2.1,
       ⟨hll', hexpr.2 ▸ hinv.sparse.2.2.2.1.2⟩, hinv.sparse.2.2.2.2⟩⟩
  exact hk s' m' hinv' rfl hle (fullM6HdrMem_unfocus hm')

theorem search_call_reorder {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost} (budget : BitVec 64)
    (hargs : vals args = (c.hdr, budget, ()))
    (hfn : ∀ a m Q X, Reorder.Spec.fullReorderM6Spec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m',
      FullM6HdrInv c F0 ext s' → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel = s.core.fuel →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_reorder_m6" args k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine ⟨c, F0, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse, hmf, ?_⟩
  intro r s' m' hsp' _ hcl' hfu' hm'
  exact hk r s' m' ⟨hinv.cfgOk, hinv.extOk, hsp'⟩ hcl' hfu' (fullM6HdrMem_unfocus hm')

theorem search_call_rephase {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, Walk.Spec.fullRephaseM6Spec a m Q X →
      Γ "full_rephase" [i64] [] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_rephase" args k) m := by
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  exact ⟨c, F0, ext, s, R, rfl, hinv, hm,
    fun ext' s' m' hinv' _ _ hcl' hfl' _ hm' => hk ext' s' m' hinv' hcl' hfl' hm'⟩

theorem search_call_decide {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, m6HdrDecideSpec a m Q X →
      Γ "m6_hdr_decide_fid" [i64] [i64] a m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.fuel = s.core.fuel →
      (r = 0#64 ∨ r = 1#64) →
      (r = 1#64 → s'.core.cur_level = s.core.cur_level + 1 ∧
        s'.core.trail_end = s.core.trail_end + 1) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "m6_hdr_decide_fid" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hfn (c.hdr, ()) m (fun rs m' => wp Γ Q X (k rs) m') X ?_
  refine m6HdrDecideSpec_of (fullM6HdrInv_to_coreInv hinv) hm ?_
  intro r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext' m' s'
    hcoreInv' hexpr hr _ h1 hm'
  have hll' : FullLastLearnedWf s' := by
    intro i hi
    have := hinv.sparse.2.2.2.1.1 i hi
    dsimp only [fullArenaClauseRefs] at this ⊢
    rw [hexpr.1]; exact this
  have hinv' : FullM6HdrInv c F0 ext' s' :=
    ⟨hcoreInv'.cfgOk, hcoreInv'.extOk,
      ⟨hcoreInv'.coreInv, hinv.sparse.2.1, hinv.sparse.2.2.1,
       ⟨hll', hexpr.2 ▸ hinv.sparse.2.2.2.1.2⟩, hinv.sparse.2.2.2.2⟩⟩
  exact hk r ext' s' m' hinv' rfl hr (fun eq1 => let ⟨hc, ht, _⟩ := h1 eq1; ⟨hc, ht⟩) hm'

theorem search_call_extend {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hfn : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hlen : s.LengthsOk c) (hext_le : s.scratch.extend_len ≤ c.extend_cap)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m', s'.LengthsOk c →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_extend" args k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec args k (hargs ▸ hfn _ m (fun rs m' => wp Γ Q X (k rs) m') X ?_)
  refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, ⟨rfl, hext_le⟩, hlen, hmf, ?_⟩
  rintro ⟨⟨⟩⟩ s' m' _ hlen' _ hm'
  exact hk s' m' hlen' (fullM6HdrMem_unfocus hm')

/-! ## 4. Post-Compaction SAT Restoration Helpers (`kissat_solve_bytes_seeded`) -/

private theorem hdrTailWords_set_bva (c0 c1 : FullCfg) (s : FullState)
    (hc : FullCfgCompat c0 c1) :
    (hdrTailWords c1 s).set 94 (BitVec.ofNat 64 c0.bva_cap) = hdrTailWords c0 s := by
  rcases hc with ⟨hhdr, havail, _, hmax, hnc, harena, hwcap, hdel, hred, hext, hscr⟩
  cases c0; cases c1
  simp only at hhdr havail hmax hnc harena hwcap hdel hred hext hscr
  subst hhdr havail hmax hnc harena hwcap hdel hred hext hscr
  simp [hdrTailWords, HdrWordField.tailChunk0, HdrWordField.tailChunk1,
    HdrWordField.tailChunk2, HdrWordField.tailChunk3, FullCfg.pFlags, FullCfg.pLitMark,
    FullCfg.pRepr, FullCfg.pSimSig, FullCfg.pFrameTrail, FullCfg.pFrameDec,
    FullCfg.pWorkStk1, FullCfg.pWorkStk2, FullCfg.pTarjanMark, FullCfg.pTarjanReach,
    FullCfg.pWalkVals, FullCfg.pWalkBest, FullCfg.pExtendStk, FullCfg.pScratchBuf,
    FullCfg.pLastLearned, FullCfg.pWsort, FullCfg.pShrinkStk, FullCfg.pRedRefs,
    FullCfg.pGlueUsed, FullCfg.pQNext, FullCfg.pQStamp, FullCfg.pPhasesTarget,
    FullCfg.pPhasesBest, FullCfg.pTrailPos, FullCfg.pQPrev, FullCfg.pVals,
    FullCfg.pMark, FullCfg.pLevel, FullCfg.pReason, FullCfg.pTrail, FullCfg.pWvec,
    FullCfg.pArena, FullCfg.pWstk, FullCfg.pDelayed, FullCfg.pTmp, FullCfg.pHeap,
    FullCfg.pPos, FullCfg.pScore, FullCfg.pPhases, FullCfg.pMinStk, FullCfg.pMinClr,
    FullCfg.minDepth]

theorem search_r10_store_bva {c0 c1 : FullCfg} (s : FullState) (R : Mem 64 → Prop)
    (m : Mem 64) (hc : FullCfgCompat c0 c1)
    (hm : (FullMemShrinkMid c1 (BitVec.ofNat 64 c0.mv) s ⋆ R) m) :
    storeOk m i64 (c1.hdr + 0x310#64) ∧
      (dimacsState c0.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c0.nc)
          s.core.d_cur s.core.d_val ⋆
        array64 (c0.hdr + 32#64) (hdrTailWords c0 s) ⋆
        FullCoreArrays c1 s.core ⋆ FullScratchArrays c1 s.scratch ⋆ c1.pad ⋆ R)
        (storeMem m i64 (c1.hdr + 0x310#64) (BitVec.ofNat 64 c0.bva_cap)) := by
  have hi : 94 < (hdrTailWords c1 s).length := by rw [hdrTailWords_length]; decide
  have hptr : c1.hdr + 32#64 + BitVec.ofNat 64 (8 * 94) = c1.hdr + 0x310#64 := by
    rw [BitVec.add_assoc]; congr 1
  dsimp only [FullMemShrinkMid] at hm
  have hm_arr : (array64 (c1.hdr + 32#64) (hdrTailWords c1 s) ⋆
      (dimacsState c1.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c1.nc)
          s.core.d_cur s.core.d_val ⋆
        FullCoreArrays c1 s.core ⋆ FullScratchArrays c1 s.scratch ⋆ c1.pad ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  have hst := store_array64 (BitVec.ofNat 64 c0.bva_cap) hi hm_arr
  rw [hptr] at hst
  refine ⟨hst.1, ?_⟩
  have h2 := hst.2
  rw [hdrTailWords_set_bva c0 c1 s hc, hc.nc] at h2
  rw [hc.hdr] at h2 ⊢
  exact sep_cast h2 (by ac_rfl)

theorem search_r10_load_max_vars {c : FullCfg} (mv' : BitVec 64) (s : FullState)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (FullMemShrinkMid c mv' s ⋆ R) m) :
    loadVal m i64 (c.hdr + 0x300#64) = some (BitVec.ofNat 64 c.max_vars) := by
  have hi : 92 < (hdrTailWords c s).length := by rw [hdrTailWords_length]; decide
  have hptr : c.hdr + 32#64 + BitVec.ofNat 64 (8 * 92) = c.hdr + 0x300#64 := by
    rw [BitVec.add_assoc]; congr 1
  dsimp only [FullMemShrinkMid] at hm
  have hm_arr : (array64 (c.hdr + 32#64) (hdrTailWords c s) ⋆
      (dimacsState c.hdr mv' (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  have hl := loadVal_array64 hi hm_arr
  rw [hptr] at hl
  have hval : (hdrTailWords c s)[92] = BitVec.ofNat 64 c.max_vars := by
    simp [hdrTailWords, HdrWordField.tailChunk0, HdrWordField.tailChunk1,
      HdrWordField.tailChunk2, HdrWordField.tailChunk3]
  simpa [hval] using hl

theorem search_r10_load_pVals {c0 : FullCfg} (s : FullState) (R : Mem 64 → Prop)
    (m : Mem 64) (hm : (array64 (c0.hdr + 32#64) (hdrTailWords c0 s) ⋆ R) m) :
    loadVal m i64 (c0.hdr + 0x40#64) = some c0.pVals := by
  have hi : 4 < (hdrTailWords c0 s).length := by rw [hdrTailWords_length]; decide
  have hptr : c0.hdr + 32#64 + BitVec.ofNat 64 (8 * 4) = c0.hdr + 0x40#64 := by
    rw [BitVec.add_assoc]; congr 1
  have hl := loadVal_array64 hi hm
  rw [hptr] at hl
  have hval : (hdrTailWords c0 s)[4] = c0.pVals := by
    simp [hdrTailWords, HdrWordField.tailChunk0]
  simpa [hval] using hl

private theorem cfg_compat_pVals {c0 c1 : FullCfg} (hc : FullCfgCompat c0 c1) :
    c0.pVals = c1.pVals := by
  have hh := hc.hdr; simp [FullCfg.pVals, hh]

private theorem sep_apply {P P' Q Q' : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ Q) m) (hp : ∀ x, P x → P' x) (hq : ∀ x, Q x → Q' x) :
    (P' ⋆ Q') m :=
  sep_mono hp (sep_mono_r hq h)

private theorem array_i8_reg {a : BitVec 64} {xs : List (BitVec 8)} {n : Nat}
    (hlen : xs.length = n) (hfit : n ≤ 2 ^ 64) {f : Mem 64} (h : array (t := i8) a xs f) :
    region a n f := by
  have hby : (i8 : Ty).bytes = 1 := rfl
  have hr := array_to_region (t := i8) (by rw [hby, hlen, Nat.one_mul]; exact hfit) h
  rwa [hby, hlen, Nat.one_mul] at hr

private theorem array_i32_reg {a : BitVec 64} {xs : List (BitVec 32)} {n : Nat}
    (hlen : xs.length = n) (hfit : 4 * n ≤ 2 ^ 64) {f : Mem 64} (h : array (t := i32) a xs f) :
    region a (4 * n) f := by
  have hby : (i32 : Ty).bytes = 4 := rfl
  have hr := array_to_region (t := i32) (by rw [hby, hlen]; exact hfit) h
  rwa [hby, hlen] at hr

private theorem array_i64_reg {a : BitVec 64} {xs : List (BitVec 64)} {n : Nat}
    (hlen : xs.length = n) (hfit : 8 * n ≤ 2 ^ 64) {f : Mem 64} (h : array (t := i64) a xs f) :
    region a (8 * n) f := by
  have hby : (i64 : Ty).bytes = 8 := rfl
  have hr := array_to_region (t := i64) (by rw [hby, hlen]; exact hfit) h
  rwa [hby, hlen] at hr

private theorem array64_i64_reg {a : BitVec 64} {xs : List (BitVec 64)} {n : Nat}
    (hlen : xs.length = n) (hfit : 8 * n ≤ 2 ^ 64) {f : Mem 64} (h : array64 a xs f) :
    region a (8 * n) f := by
  rw [array64_eq_array] at h
  exact array_i64_reg hlen hfit h

private theorem sat_core_to_regions {c1 : FullCfg} {k : FullCoreState}
    (hb : Ref.dimacsBound ≤ 10 ^ 9) (hl : FullCoreState.LengthsOk c1 k) {f : Mem 64}
    (h : (array (t := i8) c1.pLitMark k.lit_mark ⋆
      array (t := i8) c1.pMark k.mrk ⋆
      FullCoreU32A c1 k ⋆ FullCoreU32B c1 k ⋆ FullCoreDynArrs c1 k) f) :
    (region c1.pLitMark (2 * c1.max_vars) ⋆ region c1.pMark c1.max_vars ⋆
     region c1.pFlags (4 * c1.max_vars) ⋆ region c1.pLevel (4 * c1.max_vars) ⋆
     region c1.pReason (4 * c1.max_vars) ⋆ region c1.pTrail (4 * c1.max_vars) ⋆
     region c1.pTrailPos (4 * c1.max_vars) ⋆ region c1.pTmp (4 * c1.max_vars) ⋆
     region c1.pMinClr (4 * c1.max_vars) ⋆ region c1.pFrameTrail (4 * (c1.max_vars + 1)) ⋆
     region c1.pFrameDec (4 * (c1.max_vars + 1)) ⋆ region c1.pWvec (16 * c1.max_vars) ⋆
     region c1.pRepr (8 * c1.max_vars) ⋆ region c1.pMinStk (8 * c1.minDepth) ⋆
     region c1.pArena (4 * c1.arena_cap) ⋆ region c1.pWstk (4 * c1.wcap)) f := by
  have hmx := c1.hmaxv
  have har := c1.harena
  have hwc := c1.hwcap
  have hfit_min : 4 * (2 * c1.minDepth) ≤ 2 ^ 64 := by
    unfold FullCfg.minDepth fullMinDepthOf; split <;> omega
  dsimp only [FullCoreU32A, FullCoreU32B, FullCoreDynArrs] at h
  have h1 : (region c1.pLitMark (2 * c1.max_vars) ⋆ region c1.pMark c1.max_vars ⋆
      (region c1.pFlags (4 * c1.max_vars) ⋆ region c1.pLevel (4 * c1.max_vars) ⋆
       region c1.pReason (4 * c1.max_vars) ⋆ region c1.pTrail (4 * c1.max_vars) ⋆
       region c1.pTrailPos (4 * c1.max_vars) ⋆ region c1.pTmp (4 * c1.max_vars) ⋆
       region c1.pMinClr (4 * c1.max_vars)) ⋆
      (region c1.pFrameTrail (4 * (c1.max_vars + 1)) ⋆
       region c1.pFrameDec (4 * (c1.max_vars + 1)) ⋆
       region c1.pWvec (4 * (4 * c1.max_vars)) ⋆ region c1.pRepr (4 * (2 * c1.max_vars)) ⋆
       region c1.pMinStk (4 * (2 * c1.minDepth))) ⋆
      (region c1.pArena (4 * c1.arena_cap) ⋆ region c1.pWstk (4 * c1.wcap))) f := by
    refine sep_apply h (fun _ ab => ?_) (fun _ dyn => ?_)
    · refine sep_apply ab (fun _ au => ?_) (fun _ u32b => ?_)
      · refine sep_apply au (fun _ lm => ?_) (fun _ u32a => ?_)
        · exact sep_apply lm (fun _ u => array_i8_reg hl.lit_mark_len (by omega) u)
            (fun _ u => array_i8_reg hl.mrk_len (by omega) u)
        · refine sep_apply u32a (fun _ a1 => ?_)
            (fun _ u => array_i32_reg hl.min_clr_len_arr (by omega) u)
          refine sep_apply a1 (fun _ a2 => ?_)
            (fun _ u => array_i32_reg hl.tmp_len_arr (by omega) u)
          refine sep_apply a2 (fun _ a3 => ?_)
            (fun _ u => array_i32_reg hl.trail_pos_len (by omega) u)
          refine sep_apply a3 (fun _ a4 => ?_)
            (fun _ u => array_i32_reg hl.trl_len (by omega) u)
          refine sep_apply a4 (fun _ a5 => ?_)
            (fun _ u => array_i32_reg hl.rsns_len (by omega) u)
          exact sep_apply a5 (fun _ u => array_i32_reg hl.flags_len (by omega) u)
            (fun _ u => array_i32_reg hl.lvl_len (by omega) u)
      · refine sep_apply u32b (fun _ b1 => ?_)
          (fun _ u => array_i32_reg hl.min_stk_len hfit_min u)
        refine sep_apply b1 (fun _ b2 => ?_)
          (fun _ u => array_i32_reg hl.repr_len (by omega) u)
        refine sep_apply b2 (fun _ b3 => ?_)
          (fun _ u => array_i32_reg hl.wvec_len (by omega) u)
        exact sep_apply b3 (fun _ u => array_i32_reg hl.frame_trail_len (by omega) u)
          (fun _ u => array_i32_reg hl.frame_dec_len (by omega) u)
    · exact sep_apply dyn (fun _ u => array_i32_reg hl.arena_len_arr (by omega) u)
        (fun _ u => array_i32_reg hl.wstk_len_arr (by omega) u)
  have h16 : 4 * (4 * c1.max_vars) = 16 * c1.max_vars := by omega
  have h8r : 4 * (2 * c1.max_vars) = 8 * c1.max_vars := by omega
  have h8m : 4 * (2 * c1.minDepth) = 8 * c1.minDepth := by omega
  rw [h16, h8r, h8m] at h1
  exact sep_cast h1 (by ac_rfl)

private theorem sat_scr_to_regions {c1 : FullCfg} {sc : FullScratch}
    (hb : Ref.dimacsBound ≤ 10 ^ 9) (hs : FullScratch.LengthsOk c1 sc) {f : Mem 64}
    (h : FullScratchArrays c1 sc f) :
    (region c1.pWalkVals (2 * c1.max_vars) ⋆ region c1.pPhases c1.max_vars ⋆
     region c1.pPhasesTarget c1.max_vars ⋆ region c1.pPhasesBest c1.max_vars ⋆
     region c1.pWalkBest c1.max_vars ⋆ region c1.pHeap (4 * c1.max_vars) ⋆
     region c1.pPos (4 * c1.max_vars) ⋆ region c1.pShrinkStk (4 * c1.max_vars) ⋆
     region c1.pQPrev (4 * c1.max_vars) ⋆ region c1.pQNext (4 * c1.max_vars) ⋆
     region c1.pQStamp (4 * c1.max_vars) ⋆ region c1.pWsort (8 * c1.max_vars) ⋆
     region c1.pWorkStk1 (8 * c1.max_vars) ⋆ region c1.pWorkStk2 (8 * c1.max_vars) ⋆
     region c1.pTarjanMark (8 * c1.max_vars) ⋆ region c1.pTarjanReach (8 * c1.max_vars) ⋆
     region c1.pScore (8 * c1.max_vars) ⋆ region c1.pSimSig (8 * c1.max_vars) ⋆
     region c1.pGlueUsed 256 ⋆ region c1.pLastLearned 64 ⋆
     region c1.pDelayed (12 * c1.delayed_cap) ⋆ region c1.pRedRefs (4 * c1.red_cap) ⋆
     region c1.pExtendStk (4 * c1.extend_cap) ⋆ region c1.pScratchBuf (4 * c1.scratch_cap)) f := by
  have hmx := c1.hmaxv
  have hdl := c1.hdel
  have hrd := c1.hred
  have hex := c1.hext
  have hsc := c1.hscr
  dsimp only [FullScratchArrays, FullScrByteArrs, FullScrU32A, FullScrWksArrs,
    FullScrMetaArrs, FullScrDynArrs] at h
  have h1 : (
      (region c1.pWalkVals (2 * c1.max_vars) ⋆ region c1.pPhases c1.max_vars ⋆
       region c1.pPhasesTarget c1.max_vars ⋆ region c1.pPhasesBest c1.max_vars ⋆
       region c1.pWalkBest c1.max_vars) ⋆
      (region c1.pHeap (4 * c1.max_vars) ⋆ region c1.pPos (4 * c1.max_vars) ⋆
       region c1.pShrinkStk (4 * c1.max_vars) ⋆ region c1.pQPrev (4 * c1.max_vars) ⋆
       region c1.pQNext (4 * c1.max_vars) ⋆ region c1.pQStamp (4 * c1.max_vars)) ⋆
      (region c1.pWsort (4 * (2 * c1.max_vars)) ⋆ region c1.pWorkStk1 (4 * (2 * c1.max_vars)) ⋆
       region c1.pWorkStk2 (4 * (2 * c1.max_vars)) ⋆ region c1.pTarjanMark (4 * (2 * c1.max_vars)) ⋆
       region c1.pTarjanReach (4 * (2 * c1.max_vars))) ⋆
      (region c1.pScore (8 * c1.max_vars) ⋆ region c1.pSimSig (8 * c1.max_vars) ⋆
       region c1.pGlueUsed (4 * 64) ⋆ region c1.pLastLearned (4 * 16)) ⋆
      (region c1.pDelayed (4 * (3 * c1.delayed_cap)) ⋆ region c1.pRedRefs (4 * c1.red_cap) ⋆
       region c1.pExtendStk (4 * c1.extend_cap) ⋆
       region c1.pScratchBuf (4 * c1.scratch_cap))) f := by
    refine sep_apply h (fun _ s1 => ?_) (fun _ dyn => ?_)
    · refine sep_apply s1 (fun _ s2 => ?_) (fun _ meta_a => ?_)
      · refine sep_apply s2 (fun _ s3 => ?_) (fun _ wks => ?_)
        · refine sep_apply s3 (fun _ ba => ?_) (fun _ u32a => ?_)
          · refine sep_apply ba (fun _ b1 => ?_)
              (fun _ u => array_i8_reg hs.walk_best_len (by omega) u)
            refine sep_apply b1 (fun _ b2 => ?_)
              (fun _ u => array_i8_reg hs.phases_best_len (by omega) u)
            refine sep_apply b2 (fun _ b3 => ?_)
              (fun _ u => array_i8_reg hs.phases_target_len (by omega) u)
            exact sep_apply b3 (fun _ u => array_i8_reg hs.walk_vals_len (by omega) u)
              (fun _ u => array_i8_reg hs.phases_len (by omega) u)
          · refine sep_apply u32a (fun _ a1 => ?_)
              (fun _ u => array_i32_reg hs.q_stamp_len (by omega) u)
            refine sep_apply a1 (fun _ a2 => ?_)
              (fun _ u => array_i32_reg hs.q_next_len (by omega) u)
            refine sep_apply a2 (fun _ a3 => ?_)
              (fun _ u => array_i32_reg hs.q_prev_len (by omega) u)
            refine sep_apply a3 (fun _ a4 => ?_)
              (fun _ u => array_i32_reg hs.shrink_stk_len (by omega) u)
            exact sep_apply a4 (fun _ u => array_i32_reg hs.heap_len_arr (by omega) u)
              (fun _ u => array_i32_reg hs.pos_len (by omega) u)
        · refine sep_apply wks (fun _ w1 => ?_)
            (fun _ u => array_i32_reg hs.tarjan_reach_len (by omega) u)
          refine sep_apply w1 (fun _ w2 => ?_)
            (fun _ u => array_i32_reg hs.tarjan_mark_len (by omega) u)
          refine sep_apply w2 (fun _ w3 => ?_)
            (fun _ u => array_i32_reg hs.work_stk2_len (by omega) u)
          exact sep_apply w3 (fun _ u => array_i32_reg hs.wsort_len (by omega) u)
            (fun _ u => array_i32_reg hs.work_stk1_len (by omega) u)
      · refine sep_apply meta_a (fun _ m1 => ?_)
          (fun _ u => array_i32_reg hs.last_learned_len (by omega) u)
        refine sep_apply m1 (fun _ m2 => ?_)
          (fun _ u => array_i32_reg hs.glue_used_len (by omega) u)
        exact sep_apply m2 (fun _ u => array64_i64_reg hs.score_len (by omega) u)
          (fun _ u => array64_i64_reg hs.sim_sig_len (by omega) u)
    · refine sep_apply dyn (fun _ d1 => ?_)
        (fun _ u => array_i32_reg hs.scratch_buf_len (by omega) u)
      refine sep_apply d1 (fun _ d2 => ?_)
        (fun _ u => array_i32_reg hs.extend_stk_len (by omega) u)
      exact sep_apply d2 (fun _ u => array_i32_reg hs.delayed_len_arr (by omega) u)
        (fun _ u => array_i32_reg hs.red_refs_len (by omega) u)
  have h8w : 4 * (2 * c1.max_vars) = 8 * c1.max_vars := by omega
  have h12d : 4 * (3 * c1.delayed_cap) = 12 * c1.delayed_cap := by omega
  have h256 : 4 * 64 = 256 := rfl
  have h64 : 4 * 16 = 64 := rfl
  rw [h8w, h12d, h256, h64] at h1
  exact sep_cast h1 (by ac_rfl)

theorem search_r10_post_to_region {c0 c1 : FullCfg} {s : FullState}
    {mv' nc' cur' val' cnf_ptr work_ptr : BitVec 64} {wlen : Nat}
    {cnfBytes : List UInt8} {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hle : fullAlignPad work_ptr + Src.fullM6HdrTotalBytes ≤ wlen)
    (hfit : wlen ≤ 2 ^ 64)
    (hhdr : c0.hdr = fullM6WorkHdr work_ptr)
    (hav : c0.avail = wlen - fullAlignPad work_ptr - Src.fullM6ExtBytes)
    (hext : M6HdrExtOk ext) (hc : FullCfgCompat c0 c1) (hlen : s.LengthsOk c1)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c0.hdr mv' nc' cur' val' ⋆
        array64 (c0.hdr + 32#64) (hdrTailWords c0 s) ⋆
        bytes c0.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
        array (t := i8) c1.pLitMark s.core.lit_mark ⋆
        array (t := i8) c1.pMark s.core.mrk ⋆
        FullCoreU32A c1 s.core ⋆ FullCoreU32B c1 s.core ⋆ FullCoreDynArrs c1 s.core ⋆
        FullScratchArrays c1 s.scratch ⋆ c1.pad ⋆
        array64 (c1.hdr - 2304#64) ext ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m := by
  have hb : Ref.dimacsBound ≤ 10 ^ 9 := by unfold Ref.dimacsBound; decide
  have hm_avail : (region c1.hdr c1.avail ⋆
      (bytes cnf_ptr cnfBytes ⋆ array64 (c1.hdr - 2304#64) ext ⋆
        region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := by
    have hm0 : (dimacsState c1.hdr mv' nc' cur' val' ⋆
        array64 (c1.hdr + 32#64) (hdrTailWords c0 s) ⋆
        bytes c1.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
        (array (t := i8) c1.pLitMark s.core.lit_mark ⋆
          array (t := i8) c1.pMark s.core.mrk ⋆
          FullCoreU32A c1 s.core ⋆ FullCoreU32B c1 s.core ⋆ FullCoreDynArrs c1 s.core) ⋆
        FullScratchArrays c1 s.scratch ⋆ c1.pad ⋆
        (bytes cnf_ptr cnfBytes ⋆ array64 (c1.hdr - 2304#64) ext ⋆
          region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := by
      have hm_tmp := hm
      rw [← hc.hdr, cfg_compat_pVals hc] at hm_tmp
      exact sep_cast hm_tmp (by ac_rfl)
    refine sep_mono (fun x hbody => FullCfg.regions_to_avail c1 ?_) hm0
    have htw : ∀ {f}, array64 (c1.hdr + 32#64) (hdrTailWords c0 s) f →
        region (c1.hdr + 32#64) 1120 f := fun hf => by
      have hlen_tw : (hdrTailWords c0 s).length = 140 := hdrTailWords_length c0 s
      have hr := array64_i64_reg hlen_tw (by decide) hf
      have hmul : 8 * 140 = 1120 := rfl
      rwa [hmul] at hr
    have hvl : ∀ {f}, bytes c1.pVals (s.core.vals.map UInt8.ofBitVec) f →
        region c1.pVals (2 * c1.max_vars) f := fun hf => by
      have hlen_v : (s.core.vals.map UInt8.ofBitVec).length = 2 * c1.max_vars := by
        simp [hlen.core_ok.vals_len]
      simpa [hlen_v] using bytes_to_region hf
    have hraw : (region c1.hdr 32 ⋆ region (c1.hdr + 32#64) 1120 ⋆
        region c1.pVals (2 * c1.max_vars) ⋆
        (region c1.pLitMark (2 * c1.max_vars) ⋆ region c1.pMark c1.max_vars ⋆
         region c1.pFlags (4 * c1.max_vars) ⋆ region c1.pLevel (4 * c1.max_vars) ⋆
         region c1.pReason (4 * c1.max_vars) ⋆ region c1.pTrail (4 * c1.max_vars) ⋆
         region c1.pTrailPos (4 * c1.max_vars) ⋆ region c1.pTmp (4 * c1.max_vars) ⋆
         region c1.pMinClr (4 * c1.max_vars) ⋆ region c1.pFrameTrail (4 * (c1.max_vars + 1)) ⋆
         region c1.pFrameDec (4 * (c1.max_vars + 1)) ⋆ region c1.pWvec (16 * c1.max_vars) ⋆
         region c1.pRepr (8 * c1.max_vars) ⋆ region c1.pMinStk (8 * c1.minDepth) ⋆
         region c1.pArena (4 * c1.arena_cap) ⋆ region c1.pWstk (4 * c1.wcap)) ⋆
        (region c1.pWalkVals (2 * c1.max_vars) ⋆ region c1.pPhases c1.max_vars ⋆
         region c1.pPhasesTarget c1.max_vars ⋆ region c1.pPhasesBest c1.max_vars ⋆
         region c1.pWalkBest c1.max_vars ⋆ region c1.pHeap (4 * c1.max_vars) ⋆
         region c1.pPos (4 * c1.max_vars) ⋆ region c1.pShrinkStk (4 * c1.max_vars) ⋆
         region c1.pQPrev (4 * c1.max_vars) ⋆ region c1.pQNext (4 * c1.max_vars) ⋆
         region c1.pQStamp (4 * c1.max_vars) ⋆ region c1.pWsort (8 * c1.max_vars) ⋆
         region c1.pWorkStk1 (8 * c1.max_vars) ⋆ region c1.pWorkStk2 (8 * c1.max_vars) ⋆
         region c1.pTarjanMark (8 * c1.max_vars) ⋆ region c1.pTarjanReach (8 * c1.max_vars) ⋆
         region c1.pScore (8 * c1.max_vars) ⋆ region c1.pSimSig (8 * c1.max_vars) ⋆
         region c1.pGlueUsed 256 ⋆ region c1.pLastLearned 64 ⋆
         region c1.pDelayed (12 * c1.delayed_cap) ⋆ region c1.pRedRefs (4 * c1.red_cap) ⋆
         region c1.pExtendStk (4 * c1.extend_cap) ⋆ region c1.pScratchBuf (4 * c1.scratch_cap)) ⋆
        c1.pad) x := by
      refine sep_apply hbody (fun _ r1 => ?_) (fun _ p => p)
      refine sep_apply r1 (fun _ r2 => ?_) (fun _ sc => sat_scr_to_regions hb hlen.scratch_ok sc)
      refine sep_apply r2 (fun _ r3 => ?_) (fun _ cr => sat_core_to_regions hb hlen.core_ok cr)
      refine sep_apply r3 (fun _ r4 => ?_) (fun _ vl => hvl vl)
      exact sep_apply r4 (fun _ dm => dimacsState_to_region dm) (fun _ tw => htw tw)
    exact sep_cast hraw (by ac_rfl)
  have hm_ext : (region work_ptr (fullAlignPad work_ptr) ⋆
      region (fullM6WorkBase work_ptr) Src.fullM6ExtBytes ⋆
      region (fullM6WorkHdr work_ptr) c0.avail ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m := by
    have hext_reg : ∀ {f}, array64 (c1.hdr - 2304#64) ext f →
        region (fullM6WorkBase work_ptr) Src.fullM6ExtBytes f := fun hf => by
      have hlen_e : ext.length = Src.fullM6ExtWords := hext.len
      have hr := array64_i64_reg hlen_e (by decide) hf
      have ha_eq : c1.hdr - 2304#64 = fullM6WorkBase work_ptr := by
        rw [hc.hdr, hhdr, ← m6ExtAddr_fullM6WorkHdr work_ptr, m6ExtAddr_eq]; rfl
      rw [ha_eq] at hr
      have hmul : 8 * Src.fullM6ExtWords = Src.fullM6ExtBytes := rfl
      rwa [hmul] at hr
    have h1 : (region (fullM6WorkHdr work_ptr) c0.avail ⋆
        (bytes cnf_ptr cnfBytes ⋆ region (fullM6WorkBase work_ptr) Src.fullM6ExtBytes ⋆
          region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := by
      refine sep_apply hm_avail (fun _ ha => by rw [hc.hdr, hc.avail, hhdr] at ha; exact ha)
        (fun _ hb => ?_)
      refine sep_apply hb (fun _ hc => ?_) (fun _ hr => hr)
      refine sep_apply hc (fun _ hd => ?_) (fun _ hw => hw)
      exact sep_apply hd (fun _ x => x) (fun _ he => hext_reg he)
    exact sep_cast h1 (by ac_rfl)
  have hsum1 : Src.fullM6ExtBytes + c0.avail = wlen - fullAlignPad work_ptr := by
    have hb2 : Src.fullM6ExtBytes = 2304 := rfl
    have hb3 : Src.fullM6HdrTotalBytes = 3456 := rfl
    omega
  have hhdr_eq : fullM6WorkBase work_ptr + BitVec.ofNat 64 Src.fullM6ExtBytes =
      fullM6WorkHdr work_ptr := rfl
  have hm_r1 : ((region (fullM6WorkBase work_ptr) Src.fullM6ExtBytes ⋆
      region (fullM6WorkHdr work_ptr) c0.avail) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_cast hm_ext (by ac_rfl)
  rw [← hhdr_eq, region_merge_eq hsum1 (by omega)] at hm_r1
  have hsum2 : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by omega
  have hm_r2 : ((region work_ptr (fullAlignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr)) (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m := by
    have hb_eq : fullM6WorkBase work_ptr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) := rfl
    rw [hb_eq] at hm_r1
    exact sep_cast hm_r1 (by ac_rfl)
  rw [region_merge_eq hsum2 hfit] at hm_r2
  exact sep_cast hm_r2 (by ac_rfl)

/-! ## 5. Dependency Table & Projections (`searchDeps`) -/

/-- Combined upstream specification table across the `19` `Proof.*.Spec` callees of
`Src.Search.fns` (`165` distinct symbols). -/
@[expose] def searchDeps : List SpecEntry :=
  Internal.Spec.specs ++ Limits.Spec.specs ++ Extend.Spec.specs ++
  Collect.Spec.specs ++ Tiers.Spec.specs ++ Decide.Spec.specs ++
  Restart.Spec.specs ++ Reorder.Spec.specs ++ Walk.Spec.specs ++
  Compact.Spec.specs ++ Backtrack.Spec.specs ++ Reduce.Spec.specs ++
  Analyze.Spec.specs ++ Parse.Spec.specs ++ Dimacs.Spec.specs ++
  Probe.Spec.specs ++ Lucky.Spec.specs ++ Eliminate.Spec.specs ++
  PropSearch.Spec.specs

private theorem sat_l {Γ : Env} {a b : List SpecEntry} (h : Γ.Sat (a ++ b)) : Γ.Sat a :=
  fun _ he => h _ (List.mem_append.mpr (Or.inl he))

private theorem sat_r {Γ : Env} {a b : List SpecEntry} (h : Γ.Sat (a ++ b)) : Γ.Sat b :=
  fun _ he => h _ (List.mem_append.mpr (Or.inr he))

private theorem sat_deps_prop_search {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat PropSearch.Spec.specs := sat_r h
private theorem sat_deps_eliminate {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Eliminate.Spec.specs := sat_r (sat_l h)
private theorem sat_deps_lucky {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Lucky.Spec.specs := sat_r (sat_l (sat_l h))
private theorem sat_deps_probe {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Probe.Spec.specs := sat_r (sat_l (sat_l (sat_l h)))
private theorem sat_deps_dimacs {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Dimacs.Spec.specs := sat_r (sat_l (sat_l (sat_l (sat_l h))))
private theorem sat_deps_parse {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Parse.Spec.specs := sat_r (sat_l (sat_l (sat_l (sat_l (sat_l h)))))
private theorem sat_deps_analyze {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Analyze.Spec.specs := sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l h))))))
private theorem sat_deps_reduce {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Reduce.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l h)))))))
private theorem sat_deps_backtrack {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Backtrack.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l h))))))))
private theorem sat_deps_compact {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Compact.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l h)))))))))
private theorem sat_deps_walk {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Walk.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l h))))))))))
private theorem sat_deps_reorder {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Reorder.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l h)))))))))))
private theorem sat_deps_restart {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Restart.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l
    (sat_l (sat_l h))))))))))))
private theorem sat_deps_decide {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Decide.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l
    (sat_l h)))))))))))))
private theorem sat_deps_tiers {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Tiers.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l
    (sat_l (sat_l h))))))))))))))
private theorem sat_deps_collect {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Collect.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l
    (sat_l (sat_l (sat_l h)))))))))))))))
private theorem sat_deps_extend {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Extend.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l
    (sat_l (sat_l (sat_l (sat_l h))))))))))))))))
private theorem sat_deps_limits {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Limits.Spec.specs :=
  sat_r (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l
    (sat_l (sat_l (sat_l (sat_l (sat_l h)))))))))))))))))
private theorem sat_deps_internal {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Sat Internal.Spec.specs :=
  sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l (sat_l
    (sat_l (sat_l (sat_l (sat_l (sat_l h)))))))))))))))))

theorem deps_has_mem_init {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_m6_mem_init" Internal.Spec.fullM6MemInitExactSpec :=
  Internal.Spec.has_full_m6_mem_init_exact (sat_deps_internal h)

theorem deps_has_update_classify {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_update_classify_fid" (m6HdrW2aSpec [] []) :=
  Internal.Spec.has_full_update_classify_fid (sat_deps_internal h)

theorem deps_has_scale_delta {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_scale_delta_m5" Limits.Spec.schedScaleDeltaSpec :=
  Lib.SpecTable.has_at (sat_deps_limits h) 3 rfl
    (Limits.Spec.specs_xfree _ (List.getElem_mem (l := Limits.Spec.specs) (n := 3) (by decide)))

theorem deps_has_extend {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_extend" fullExtendSpec :=
  Lib.SpecTable.has_at (sat_deps_extend h) 4 rfl
    (Extend.Spec.specs_xfree _ (List.getElem_mem (l := Extend.Spec.specs) (n := 4) (by decide)))

theorem deps_has_arena_sweep {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_arena_sweep" fullArenaSweepSpec :=
  Collect.Spec.has_full_arena_sweep (sat_deps_collect h)

theorem deps_has_set_watermark {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []) :=
  Tiers.Spec.has_m6_hdr_set_watermark (sat_deps_tiers h)

theorem deps_has_decide {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "m6_hdr_decide_fid" m6HdrDecideSpec :=
  Decide.Spec.has_m6_hdr_decide_fid (sat_deps_decide h)

theorem deps_has_switch_mode {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_switch_mode_m7" Restart.Spec.fullSwitchModeM7Spec :=
  Restart.Spec.has_full_switch_mode_m7 (sat_deps_restart h)

theorem deps_has_restart_due {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_restart_due" fullRestartDueSpec :=
  Restart.Spec.has_full_restart_due (sat_deps_restart h)

theorem deps_has_restart {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_restart" fullRestartSpec :=
  Restart.Spec.has_full_restart (sat_deps_restart h)

theorem deps_has_reorder {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_reorder_m6" Reorder.Spec.fullReorderM6Spec :=
  Reorder.Spec.has_full_reorder_m6 (sat_deps_reorder h)

theorem deps_has_rephase {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_rephase" Walk.Spec.fullRephaseM6Spec :=
  Walk.Spec.has_full_rephase (sat_deps_walk h)

theorem deps_has_compact_needed {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_compact_needed" Compact.Spec.fullCompactNeededSpec :=
  Compact.Spec.has_full_compact_needed (sat_deps_compact h)

theorem deps_has_compact {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_compact" Compact.Spec.fullCompactSpec :=
  Compact.Spec.has_full_compact (sat_deps_compact h)

theorem deps_has_backtrack {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_backtrack" fullBacktrackSpec :=
  Backtrack.Spec.has_full_backtrack (sat_deps_backtrack h)

theorem deps_has_reduce {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_reduce_m6" Reduce.Spec.fullReduceM6Spec :=
  Reduce.Spec.has_full_reduce_m6 (sat_deps_reduce h)

theorem deps_has_analyze {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_analyze_m6_hdr" m6HdrAnalyzeSpec :=
  Analyze.Spec.has_full_analyze_m6_hdr (sat_deps_analyze h)

theorem deps_has_parse_body {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_parse_body" Parse.Spec.fullParseBodyM6Spec :=
  Parse.Spec.has_full_parse_body (sat_deps_parse h)

theorem deps_has_check_model {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "kissat_check_model" kissatCheckModelExactSpec :=
  Dimacs.Spec.has_kissat_check_model (sat_deps_dimacs h)

theorem deps_has_probe {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_probe_m6" Probe.Spec.fullProbeM6Spec :=
  Probe.Spec.has_full_probe_m6 (sat_deps_probe h)

theorem deps_has_lucky_late {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_lucky_late_m7" Lucky.Spec.fullLuckyLateM7Spec :=
  Lucky.Spec.has_full_lucky_late_m7 (sat_deps_lucky h)

theorem deps_has_eliminate {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_eliminate_m6" Eliminate.Spec.fullEliminateM6Spec :=
  Eliminate.Spec.has_full_eliminate_m6 (sat_deps_eliminate h)

theorem deps_has_propagate {Γ : Env} (h : Γ.Sat searchDeps) :
    Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec :=
  PropSearch.Spec.has_full_propagate (sat_deps_prop_search h)

/-! ## 6. BitVec Branch & Bounds Utilities -/

theorem fullM6HdrInv_nat_lt {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (hinv : FullM6HdrInv c F0 ext s) :
    s.core.cur_vars < 2 ^ 64 ∧ s.core.cur_level < 2 ^ 64 ∧
      s.core.trail_end < 2 ^ 64 ∧ s.core.propagated < 2 ^ 64 := by
  obtain ⟨_, hw⟩ := hinv.sparse.1.witness
  have h1 := hinv.sparse.lengths.core_ok.cur_vars_le
  have h2 := c.hmaxv
  have hb : Ref.dimacsBound ≤ 10 ^ 9 := by unfold Ref.dimacsBound; decide
  have h3 := hw.cur_level_le
  have h4 := hinv.sparse.lengths.core_ok.trail_end_le
  have h5 := hinv.sparse.lengths.core_ok.propagated_le
  omega

theorem jnz_bv_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : BitVec 64} {k : Arg Val .bool} {e1 e2 : Expr Val Cont rs}
    (hk : k.val = (a == b)) (ht : a = b → wp Γ Q X e1 m) (hf : a ≠ b → wp Γ Q X e2 m) :
    wp Γ Q X (.jnz k e1 e2) m :=
  wp_jnz_iff (a = b) (by rw [hk, beq_iff_eq]) ht hf

theorem jnz_bv_ne {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : BitVec 64} {k : Arg Val .bool} {e1 e2 : Expr Val Cont rs}
    (hk : k.val = (a != b)) (ht : a ≠ b → wp Γ Q X e1 m) (hf : a = b → wp Γ Q X e2 m) :
    wp Γ Q X (.jnz k e1 e2) m :=
  wp_jnz_iff (a ≠ b) (by rw [hk, bne_iff_ne]) ht (fun h => hf (Classical.byContradiction h))

theorem jnz_bv_ult0 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a : Nat} (ha : a < 2 ^ 64) {k : Arg Val .bool} {e1 e2 : Expr Val Cont rs}
    (hk : k.val = BitVec.ult 0#64 (BitVec.ofNat 64 a))
    (ht : 0 < a → wp Γ Q X e1 m) (hf : a = 0 → wp Γ Q X e2 m) :
    wp Γ Q X (.jnz k e1 e2) m := by
  refine wp_jnz_decide (0 < a) ?_ ht (fun h => hf (by omega))
  rw [hk]; simp [BitVec.ult, Nat.mod_eq_of_lt ha]

theorem jnz_bv_ule_nat {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) {k : Arg Val .bool} {e1 e2 : Expr Val Cont rs}
    (hk : k.val = BitVec.ule (BitVec.ofNat 64 b) (BitVec.ofNat 64 a))
    (ht : b ≤ a → wp Γ Q X e1 m) (hf : a < b → wp Γ Q X e2 m) :
    wp Γ Q X (.jnz k e1 e2) m := by
  refine wp_jnz_decide (b ≤ a) ?_ ht (fun h => hf (by omega))
  rw [hk]; simp [BitVec.ule, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem jnz_bv_ult {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : BitVec 64} {k : Arg Val .bool} {e1 e2 : Expr Val Cont rs}
    (hk : k.val = BitVec.ult a b)
    (ht : a < b → wp Γ Q X e1 m) (hf : b ≤ a → wp Γ Q X e2 m) :
    wp Γ Q X (.jnz k e1 e2) m := by
  refine wp_jnz_decide (a.toNat < b.toNat) hk (fun h => ht (BitVec.lt_def.mpr h))
    (fun h => hf (BitVec.le_def.mpr (by omega)))

theorem jnz_bv_ule {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : BitVec 64} {k : Arg Val .bool} {e1 e2 : Expr Val Cont rs}
    (hk : k.val = BitVec.ule a b)
    (ht : a ≤ b → wp Γ Q X e1 m) (hf : b < a → wp Γ Q X e2 m) :
    wp Γ Q X (.jnz k e1 e2) m := by
  refine wp_jnz_decide (a.toNat ≤ b.toNat) hk (fun h => ht (BitVec.le_def.mpr h))
    (fun h => hf (BitVec.lt_def.mpr (by omega)))

end LeanQbe.T.Examples.Kissat.Proof.Search
