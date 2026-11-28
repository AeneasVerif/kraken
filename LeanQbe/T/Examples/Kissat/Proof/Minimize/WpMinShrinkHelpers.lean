/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpSortPerm
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0Grind

/-!
# Structural & Invariant Helpers for `full_min_shrink_m6`

Pure invariants, `List.Perm` / `EntailsClause` / `Nodup` preservation lemmas, initial marking,
block-shrink / DFS transitions, compaction, mark-clearing, and swap/reversal preservation lemmas
for `WpMinShrink`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Grind LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open FullMinTactics
open scoped FullArenaTactics FullMinTactics

public section

/-! ## 1. Pure Permutation, Literal Bound, & State Projection Helpers -/

/-- Bundled mutable scratch arrays and scalar cursors threaded through `full_min_shrink_m6`. -/
structure ShrinkScratch where
  tmp : List (BitVec 32)
  mrk : List (BitVec 8)
  mclr : List (BitVec 32)
  sstk : List (BitVec 32)
  wsort : List (BitVec 32)
  ws1 : List (BitVec 32)
  mcl : Nat
  mcf : BitVec 64
  ticks : BitVec 64
  resSz : BitVec 64

abbrev ShrinkScratch.st (b : ShrinkScratch) (s : FullState) : FullState :=
  s13BlkState s b.tmp b.mrk b.mclr b.sstk b.wsort b.ws1 b.mcl b.mcf b.ticks b.resSz

abbrev ShrinkScratch.ofState (s : FullState) : ShrinkScratch :=
  ⟨s.core.tmp, s.core.mrk, s.core.min_clr, s.scratch.shrink_stk, s.scratch.wsort,
   s.scratch.work_stk1, s.core.min_clr_len, s.core.min_clr_full, s.scratch.search_ticks,
   s.scratch.res_sz⟩

structure ShrinkScratch.LengthsOk (b : ShrinkScratch) (c : FullCfg) : Prop where
  tmp_len : b.tmp.length = c.max_vars
  mrk_len : b.mrk.length = c.max_vars
  mclr_len : b.mclr.length = c.max_vars
  mcl_le : b.mcl ≤ c.max_vars
  sstk_len : b.sstk.length = c.max_vars
  wsort_len : b.wsort.length = 2 * c.max_vars
  ws1_len : b.ws1.length = 2 * c.max_vars

theorem m6_entails_of_perm {F : List (List Nat)} {xs ys : List (BitVec 32)}
    (hp : xs.Perm ys) (h : (cnfOfClauses F).EntailsClause (cnfClause (xs.map BitVec.toNat))) :
    (cnfOfClauses F).EntailsClause (cnfClause (ys.map BitVec.toNat)) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, ((hp.map BitVec.toNat).mem_iff).mp hl, hsat⟩

theorem m6_nodup_of_perm {xs ys : List (BitVec 32)} (hp : xs.Perm ys)
    (hnd : (xs.map fun x => x.toNat / 2).Nodup) :
    (ys.map fun x => x.toNat / 2).Nodup :=
  (hp.map fun x => x.toNat / 2).nodup_iff.mp hnd

theorem m6_bv32_ne_ff_of_lt {l : BitVec 32} {n : Nat} (hn : 2 * n < 2 ^ 32 - 1)
    (hl : l.toNat < 2 * n) : l ≠ 0xFFFFFFFF#32 := by
  intro h; c0_grind

theorem m6CoreInv_blk {c : FullCfg} {F0 : CNF Nat} {s : FullState} {b : ShrinkScratch}
    (hcore : FullOtfsCoreInv c F0 s) (hb : b.LengthsOk c) :
    FullOtfsCoreInv c F0 (b.st s) := by
  have hcore' := fullOtfsCoreInv_with_min_tmp (mcf1 := b.mcf) hcore hb.tmp_len
    hcore.1.core_ok.tmp_len_le hb.mrk_len hcore.1.core_ok.min_stk_len hb.mclr_len hb.mcl_le
    hcore.1.scratch_ok
  exact ⟨⟨hcore'.1.core_ok,
    { hcore'.1.scratch_ok with
      shrink_stk_len := hb.sstk_len, wsort_len := hb.wsort_len, work_stk1_len := hb.ws1_len }⟩,
    hcore'.2⟩

theorem m6Witness_blk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {b : ShrinkScratch} (hw : FullOtfsWitnessInv c F0 F_cur s.core) :
    FullOtfsWitnessInv c F0 F_cur (b.st s).core :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem m6Witness_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {tmp1 : List (BitVec 32)} {tl1 : Nat} {mrk1 : List (BitVec 8)}
    {mclr1 sstk1 wsort1 ws1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 conf1 llits1 mrem1 ticks1 resSz1 : BitVec 64}
    (hw : FullOtfsWitnessInv c F0 F_cur s.core) :
    FullOtfsWitnessInv c F0 F_cur
      (fullMinShrinkState s tmp1 tl1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 conf1 llits1
        mrem1 ticks1 resSz1).core :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem m6Blk_mark_step (s : FullState) (b : ShrinkScratch) (v : Nat) (tag : BitVec 8) :
    let st' := fullMinMarkStepState (b.st s) v tag
    st' = ({ b with
      mrk := st'.core.mrk, mclr := st'.core.min_clr,
      mcl := st'.core.min_clr_len, mcf := st'.core.min_clr_full }).st s := by
  intro st'
  dsimp only [st', fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, ShrinkScratch.st,
    s13BlkState]
  split <;> rfl

theorem m6LitMarksClear_of {c : FullCfg} {s s' : FullState}
    (hclear : FullLitMarksClear c s)
    (hmrk0 : ∀ v < c.max_vars, s'.core.mrk[v]?.getD 0#8 = 0#8)
    (hlm : s'.core.lit_mark = s.core.lit_mark) : FullLitMarksClear c s' :=
  ⟨hmrk0, by rw [hlm]; exact hclear.2⟩

theorem m6_take_map_filter_no_sent :
    ∀ {xs : List (BitVec 32)} {n : Nat}, n ≤ xs.length →
      (∀ k < n, xs[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      (xs.take n).filter (· ≠ 0xFFFFFFFF#32) = xs.take n
  | _, 0, _, _ => by simp
  | x :: xs, n + 1, hn, hne => by
    have h0 := hne 0 (Nat.zero_lt_succ n)
    simp only [List.getElem?_cons_zero, Option.getD_some] at h0
    rw [List.take_succ_cons, List.filter_cons]
    simp only [decide_eq_true h0, ite_true]
    exact congrArg (x :: ·) (m6_take_map_filter_no_sent (by simp at hn; exact hn)
      (fun k hk => hne (k + 1) (by omega)))

theorem m6_sort_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {tmp' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (_hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (ht_pos : 1 ≤ s.core.tmp_len) (_ht_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hnd : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup)
    (hEnt : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)))
    (hlits : ∀ k < s.core.tmp_len,
      (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(s.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hlvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      0 < (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (h0lvl : (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      s.core.cur_level)
    (htmp' : tmp'.length = c.max_vars)
    (hperm : (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len))
    (h0eq : 0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?)
    (hmap_r : ∀ j, 1 ≤ j → j < s.core.tmp_len →
      ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) :
    let orig_tlen := s.core.tmp_len
    ((tmp'.take orig_tlen).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp'.take orig_tlen).map BitVec.toNat)) ∧
    tmp'[0]? = s.core.tmp[0]? ∧
    (s.core.lvl[(tmp'[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (∀ k < orig_tlen,
      (tmp'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp'[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 ∧
      tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
    (∀ k, 1 ≤ k → k < orig_tlen →
      0 < (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s.core.cur_level) := by
  intro orig_tlen
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hlen.core_ok.cur_vars_le
  have h0eq' : tmp'[0]? = s.core.tmp[0]? := h0eq ht_pos
  have hlits' : ∀ k < orig_tlen,
      (tmp'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp'[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 ∧
      tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      have h0s := hlits 0 ht_pos
      have hk_len : 0 < tmp'.length := by rw [htmp']; omega
      have hne : tmp'[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        have hlt : (tmp'[0]'hk_len).toNat < 2 * s.core.cur_vars := by
          have h0 := h0s.1
          rwa [← h0eq', List.getElem?_eq_getElem hk_len, Option.getD_some] at h0
        rw [List.getElem?_eq_getElem hk_len, Option.getD_some]
        exact m6_bv32_ne_ff_of_lt (by omega) hlt
      exact ⟨by simp only [h0eq']; exact h0s.1, by simp only [h0eq']; exact h0s.2, hne⟩
    · obtain ⟨i, hi1, hi2, hieq⟩ := hmap_r k (by omega) hk
      have his := hlits i hi2
      have hk_len : k < tmp'.length := by rw [htmp']; omega
      have hne : tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        have hlt : (tmp'[k]'hk_len).toNat < 2 * s.core.cur_vars := by
          have hi := his.1
          rwa [← hieq, List.getElem?_eq_getElem hk_len, Option.getD_some] at hi
        rw [List.getElem?_eq_getElem hk_len, Option.getD_some]
        exact m6_bv32_ne_ff_of_lt (by omega) hlt
      exact ⟨by simp only [hieq]; exact his.1, by simp only [hieq]; exact his.2, hne⟩
  refine ⟨m6_nodup_of_perm hperm.symm hnd, m6_entails_of_perm hperm.symm hEnt, h0eq',
    by simp only [h0eq']; exact h0lvl, hlits', fun k hk1 hk2 => ?_⟩
  obtain ⟨i, hi1, hi2, hieq⟩ := hmap_r k hk1 hk2
  simp only [hieq]; exact hlvls i hi1 hi2

/-! ## 2. Initial Mark Loop (`for i < orig_tlen: full_min_mark`) -/

theorem fullMinMarkInv_weaken {k : FullCoreState} {keep1 keep2 : List Nat}
    (h : FullMinMarkInv k keep1) (hsub : ∀ l ∈ keep1, l ∈ keep2) : FullMinMarkInv k keep2 :=
  ⟨h.mrk_dom, h.clr_cov, fun idx hi h2 => (h.rem_sound idx hi h2).elim
    (fun hm => Or.inl (hsub _ hm)) Or.inr⟩

theorem m6_mark_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {b : ShrinkScratch} {mrk0 : List (BitVec 8)} {orig_tlen i : Nat}
    (hcore : FullOtfsCoreInv c F0 s) (hb_len : b.LengthsOk c)
    (hot_le : orig_tlen ≤ s.core.cur_vars) (hi_lt : i < orig_tlen)
    (hlits : ∀ k < orig_tlen,
      (b.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(b.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hmin_i : FullMinMarkInv (b.st s).core ((b.tmp.take i).map BitVec.toNat))
    (hno8_i : ∀ w < s.core.cur_vars, (b.mrk[w]?.getD 0#8 &&& 8#8) = 0#8)
    (hab_i : ∀ w, s.core.cur_vars ≤ w → b.mrk[w]? = mrk0[w]?)
    (hdone_i : ∀ k < i, (b.mrk[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) :
    let st := b.st s
    let v := (b.tmp[i]'(by have := hcore.1.core_ok.cur_vars_le; have := hb_len.tmp_len; omega) >>>
      1).toNat
    let st' := fullMinMarkStepState st v 2#8
    st'.LengthsOk c ∧
    FullMinMarkInv st'.core ((b.tmp.take (i + 1)).map BitVec.toNat) ∧
    (∀ w < s.core.cur_vars, (st'.core.mrk[w]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (∀ w, s.core.cur_vars ≤ w → st'.core.mrk[w]? = mrk0[w]?) ∧
    (∀ k < i + 1, (st'.core.mrk[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  intro st v st'
  have hcv := hcore.1.core_ok.cur_vars_le
  have hsc := m6CoreInv_blk hcore hb_len
  have hi_arr : i < b.tmp.length := by rw [hb_len.tmp_len]; omega
  have hv_nat : v = (b.tmp[i]?.getD 0#32).toNat / 2 := by
    dsimp only [v]; rw [bv32_lshr_1, List.getElem?_eq_getElem hi_arr, Option.getD_some]
  have hl_spec := hlits i hi_lt
  have hv_lt : v < s.core.cur_vars := by rw [hv_nat]; omega
  have hlen' : st'.LengthsOk c := fullMinMarkStepState_lengths hsc.1 v 2#8
  have hmin_w : FullMinMarkInv st.core ((b.tmp.take (i + 1)).map BitVec.toNat) :=
    fullMinMarkInv_weaken hmin_i fun l hl => by
      rw [List.mem_map] at hl ⊢; obtain ⟨x, hx, rfl⟩ := hl
      rw [List.take_succ_eq_append_getElem hi_arr]
      exact ⟨x, List.mem_append_left _ hx, rfl⟩
  have hl_mem : (b.tmp[i]?.getD 0#32).toNat ∈ (b.tmp.take (i + 1)).map BitVec.toNat := by
    rw [List.mem_map, List.take_succ_eq_append_getElem hi_arr]
    exact ⟨b.tmp[i]'hi_arr, List.mem_append_right _ (List.mem_singleton.mpr rfl), by
      rw [List.getElem?_eq_getElem hi_arr, Option.getD_some]⟩
  have hstep_b := fullMinMarkStepState_bit8_mono2 hsc.1 hv_lt (Or.inl rfl) (hno8_i v hv_lt)
  have hmin' : FullMinMarkInv st'.core ((b.tmp.take (i + 1)).map BitVec.toNat) := by
    dsimp only [st', fullMinMarkStepState, fullMinMarkStepCore]
    split
    · exact hmin_w
    · rw [hv_nat]
      exact fullMinMarkInv_mark_keep hsc hmin_w hl_spec.1 hl_mem hl_spec.2 (hno8_i _ (by omega))
  have hno8' : ∀ w < s.core.cur_vars, (st'.core.mrk[w]?.getD 0#8 &&& 8#8) = 0#8 := fun w hw => by
    have he := hstep_b.1 w hw; dsimp only [st] at he; rw [he]; exact hno8_i w hw
  have hab' : ∀ w, s.core.cur_vars ≤ w → st'.core.mrk[w]? = mrk0[w]? := fun w hw =>
    (fullMinMarkStepState_mrk_above (s := st) hv_lt 2#8 w hw).trans (hab_i w hw)
  have hdone' : ∀ k < i + 1,
      (st'.core.mrk[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro k hk
    by_cases hki : k = i
    · subst k; rw [← hv_nat]
      dsimp only [st', fullMinMarkStepState, fullMinMarkStepCore]
      split
      · rename_i hc; exact hc.resolve_left (Nat.not_le.mpr hv_lt)
      · dsimp only [fullMinMarkCore]
        rw [List.getElem?_set_self (by rw [hb_len.mrk_len]; omega), Option.getD_some]
        exact bv8_and2_of_or2 _
    · have hklt : (b.tmp[k]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
        have := (hlits k (by omega)).1; omega
      exact hstep_b.2 _ hklt (hdone_i k (by omega))
  exact ⟨hlen', hmin', hno8', hab', hdone'⟩

/-! ## 3. Grouping, Block-Shrink, & DFS Step Helpers -/

structure M6ShrinkLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (orig_tlen : Nat) (tmp_s : List (BitVec 32)) (mrk0 : List (BitVec 8)) (beg : Nat)
    (b : ShrinkScratch) : Prop where
  beg_ge1 : 1 ≤ beg
  beg_le : beg ≤ orig_tlen
  len : b.LengthsOk c
  tmp0_eq : b.tmp[0]? = tmp_s[0]?
  tail_eq : ∀ j, beg ≤ j → j < orig_tlen → b.tmp[j]? = tmp_s[j]?
  kept_lits : ∀ k < orig_tlen, b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (b.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    (b.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8
  kept_lvls : ∀ k, 1 ≤ k → k < orig_tlen → b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let lv := (s.core.lvl[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s.core.cur_level
  kept_sorted : ∀ i j, 1 ≤ i → i ≤ j → j < orig_tlen →
    b.tmp[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    b.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(b.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (s.core.lvl[(b.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  beg_bd : beg < orig_tlen → ∀ k, 1 ≤ k → k < beg →
    b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
    (s.core.lvl[(tmp_s[beg]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  nodup : (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup
  min_inv : FullMinMarkInv (b.st s).core
    (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)
  ent : (cnfOfClauses F_cur).EntailsClause
    (cnfClause (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
  no8 : ∀ w < s.core.cur_vars, (b.mrk[w]?.getD 0#8 &&& 8#8) = 0#8
  mrk_above : ∀ w, s.core.cur_vars ≤ w → b.mrk[w]? = mrk0[w]?

theorem m6Shrink_block_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen beg end_b : Nat} {blvl : BitVec 32} {tmp_s : List (BitVec 32)}
    {mrk0 : List (BitVec 8)} {b b' : ShrinkScratch}
    (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hinv : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 beg b)
    (hbeg_end : beg < end_b) (hend_le : end_b ≤ orig_tlen)
    (hs0_lvl : (s.core.lvl[(tmp_s[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (_hs_nosent : ∀ k < orig_tlen, tmp_s[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hs_lvls : ∀ k, 1 ≤ k → k < orig_tlen →
      0 < (s.core.lvl[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hs_sorted : ∀ i j, 1 ≤ i → i ≤ j → j < orig_tlen →
      (s.core.lvl[(tmp_s[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hblk_lvl : ∀ j, beg ≤ j → j < end_b →
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hend_strict : end_b < orig_tlen →
      blvl.toNat < (s.core.lvl[(tmp_s[end_b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hlen' : b'.LengthsOk c)
    (hmin' : FullMinMarkInv (b'.st s).core
      (((b'.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hab' : ∀ w, s.core.cur_vars ≤ w → b'.mrk[w]? = b.mrk[w]?)
    (hno8' : ∀ w < s.core.cur_vars, (b'.mrk[w]?.getD 0#8 &&& 8#8) = 0#8)
    (hout : ∀ k < orig_tlen, (k < beg ∨ end_b ≤ k) → b'.tmp[k]? = b.tmp[k]?)
    (hin_lvl : ∀ k, beg ≤ k → k < end_b → b'.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(b'.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hin_nodup : (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map
        fun x => x.toNat / 2).Nodup →
      (∀ k < orig_tlen, (k < beg ∨ end_b ≤ k) → b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.core.lvl[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
      (((b'.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup)
    (hEnt_impl : FullOtfsWitnessInv c F0 F_cur (b.st s).core →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
      FullOtfsWitnessInv c F0 F_cur (b'.st s).core ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (((b'.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)))
    (hkept' : ∀ k < orig_tlen, b'.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (b'.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (b'.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) :
    M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 end_b b' := by
  have hbeg_ge1 := hinv.beg_ge1
  have hbeg_lv := hblk_lvl beg (le_refl _) hbeg_end
  have hbeg_rng := hs_lvls beg hbeg_ge1 (by omega)
  have hother_ne : ∀ k < orig_tlen, (k < beg ∨ end_b ≤ k) →
      b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat := by
    intro k hk hkb hne
    by_cases hk0 : k = 0
    · subst k
      have hlv0 : (s.core.lvl[(b.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s.core.cur_level := by simp only [hinv.tmp0_eq]; exact hs0_lvl
      omega
    · rcases hkb with hlt_b | hge_e
      · have := hinv.beg_bd (by omega) k (by omega) hlt_b hne; omega
      · have hk_eq := hinv.tail_eq k (by omega) hk
        have hs := hend_strict (by omega)
        have hle := hs_sorted end_b k (by omega) hge_e hk
        simp only [hk_eq]; omega
  have h0_eq' : b'.tmp[0]? = tmp_s[0]? :=
    (hout 0 (by omega) (Or.inl (by omega))).trans hinv.tmp0_eq
  have htail' : ∀ j, end_b ≤ j → j < orig_tlen → b'.tmp[j]? = tmp_s[j]? := fun j hj1 hj2 =>
    (hout j hj2 (Or.inr hj1)).trans (hinv.tail_eq j (by omega) hj2)
  have hlvl_fn' : ∀ k, 1 ≤ k → k < orig_tlen → b'.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let lv := (s.core.lvl[(b'.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level := by
    intro k hk1 hk2 hne
    by_cases hkb : beg ≤ k ∧ k < end_b
    · rw [hin_lvl k hkb.1 hkb.2 hne]; rw [← hbeg_lv]; exact hbeg_rng
    · have hk_eq := hout k hk2 (by omega)
      simp only [hk_eq] at hne ⊢
      exact hinv.kept_lvls k hk1 hk2 hne
  have hsort' : ∀ i j, 1 ≤ i → i ≤ j → j < orig_tlen →
      b'.tmp[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      b'.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(b'.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(b'.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
    intro i j hi1 hij hj hni hnj
    by_cases hi_b : i < beg
    · have hi_eq := hout i (by omega) (Or.inl hi_b)
      have hli := hinv.beg_bd (by omega) i hi1 hi_b (by rwa [← hi_eq])
      by_cases hj_b : j < beg
      · have hj_eq := hout j hj (Or.inl hj_b)
        simp only [hi_eq, hj_eq]
        exact hinv.kept_sorted i j hi1 hij hj (by rwa [← hi_eq]) (by rwa [← hj_eq])
      · by_cases hj_e : j < end_b
        · rw [hin_lvl j (by omega) hj_e hnj]; simp only [hi_eq]; omega
        · have hj_eq := htail' j (by omega) hj
          have hs := hend_strict (by omega)
          have hle := hs_sorted end_b j (by omega) (by omega) hj
          simp only [hi_eq, hj_eq]; omega
    · by_cases hi_e : i < end_b
      · rw [hin_lvl i (by omega) hi_e hni]
        by_cases hj_e : j < end_b
        · rw [hin_lvl j (by omega) hj_e hnj]; exact le_refl _
        · have hj_eq := htail' j (by omega) hj
          have hs := hend_strict (by omega)
          have hle := hs_sorted end_b j (by omega) (by omega) hj
          simp only [hj_eq]; omega
      · have hi_eq := htail' i (by omega) (by omega)
        have hj_eq := htail' j (by omega) hj
        simp only [hi_eq, hj_eq]; exact hs_sorted i j hi1 hij hj
  have hbd' : end_b < orig_tlen → ∀ k, 1 ≤ k → k < end_b →
      b'.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(b'.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      (s.core.lvl[(tmp_s[end_b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
    intro he k hk1 hk2 hnk
    have hs := hend_strict he
    by_cases hk_b : k < beg
    · have hk_eq := hout k (by omega) (Or.inl hk_b)
      have hli := hinv.beg_bd (by omega) k hk1 hk_b (by rwa [← hk_eq])
      simp only [hk_eq]; omega
    · rw [hin_lvl k (by omega) hk2 hnk]; exact hs
  exact ⟨by omega, hend_le, hlen', h0_eq', htail', hkept', hlvl_fn', hsort', hbd',
    hin_nodup hinv.nodup hother_ne, hmin', (hEnt_impl (m6Witness_blk hw) hinv.ent).2, hno8',
    fun w hw' => (hab' w hw').trans (hinv.mrk_above w hw')⟩

theorem m6Shrink_block_no_shrink {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {orig_tlen beg end_b : Nat} {blvl : BitVec 32} {tmp_s : List (BitVec 32)}
    {mrk0 : List (BitVec 8)} {b : ShrinkScratch}
    (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hinv : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 beg b)
    (hbeg_end : beg < end_b) (hend_le : end_b ≤ orig_tlen)
    (hs0_lvl : (s.core.lvl[(tmp_s[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hs_nosent : ∀ k < orig_tlen, tmp_s[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hs_lvls : ∀ k, 1 ≤ k → k < orig_tlen →
      0 < (s.core.lvl[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(tmp_s[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hs_sorted : ∀ i j, 1 ≤ i → i ≤ j → j < orig_tlen →
      (s.core.lvl[(tmp_s[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hblk_lvl : ∀ j, beg ≤ j → j < end_b →
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hend_strict : end_b < orig_tlen →
      blvl.toNat < (s.core.lvl[(tmp_s[end_b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) :
    M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 end_b b :=
  m6Shrink_block_step hw hinv hbeg_end hend_le hs0_lvl hs_nosent hs_lvls hs_sorted hblk_lvl
    hend_strict hinv.len hinv.min_inv (fun _ _ => rfl) hinv.no8 (fun _ _ _ => rfl)
    (fun k hk1 hk2 _ => by rw [hinv.tail_eq k hk1 (by omega)]; exact hblk_lvl k hk1 hk2)
    (fun h _ => h) (fun hw' hent' => ⟨hw', hent'⟩) hinv.kept_lits

structure M6DfsLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (orig_tlen : Nat) (blvl : BitVec 32) (tmp_s : List (BitVec 32)) (mrk0 : List (BitVec 8))
    (beg end_b mk2 : Nat) (b : ShrinkScratch) : Prop where
  beg_ge1 : 1 ≤ beg
  beg_mk : beg ≤ mk2
  mk_end : mk2 ≤ end_b
  end_le : end_b ≤ orig_tlen
  len : b.LengthsOk c
  tmp0_eq : b.tmp[0]? = tmp_s[0]?
  tail_eq : ∀ j, mk2 ≤ j → j < orig_tlen → b.tmp[j]? = tmp_s[j]?
  kept_lits : ∀ k < orig_tlen, b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (b.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    (b.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8
  kept_lvls : ∀ k, 1 ≤ k → k < orig_tlen → b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let lv := (s.core.lvl[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s.core.cur_level
  kept_sorted : ∀ i j, 1 ≤ i → i ≤ j → j < orig_tlen →
    b.tmp[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    b.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(b.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (s.core.lvl[(b.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  beg_bd : ∀ k, 1 ≤ k → k < beg → b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < blvl.toNat
  blk_lvl : ∀ k, beg ≤ k → k < mk2 → b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(b.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat
  nodup : (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup
  min_inv : FullMinMarkInv (b.st s).core
    (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)
  ent : (cnfOfClauses F_cur).EntailsClause
    (cnfClause (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
  no8 : ∀ w < s.core.cur_vars, (b.mrk[w]?.getD 0#8 &&& 8#8) = 0#8
  mrk_above : ∀ w, s.core.cur_vars ≤ w → b.mrk[w]? = mrk0[w]?

theorem m6Dfs_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen beg end_b : Nat} {blvl : BitVec 32} {tmp_s : List (BitVec 32)}
    {mrk0 : List (BitVec 8)} {b : ShrinkScratch}
    (hinv : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 beg b)
    (hbeg_end : beg < end_b) (hend_le : end_b ≤ orig_tlen)
    (hblk_lvl : ∀ j, beg ≤ j → j < end_b →
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) :
    M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg end_b beg b := by
  have hbeg_l := hblk_lvl beg (le_refl _) hbeg_end
  refine ⟨hinv.beg_ge1, le_refl _, Nat.le_of_lt hbeg_end, hend_le, hinv.len, hinv.tmp0_eq,
    hinv.tail_eq, hinv.kept_lits, hinv.kept_lvls, hinv.kept_sorted, ?_, fun _ h1 h2 => absurd h1
      (by omega), hinv.nodup, hinv.min_inv, hinv.ent, hinv.no8, hinv.mrk_above⟩
  intro k hk1 hk2 hne
  rw [← hbeg_l]
  exact hinv.beg_bd (by omega) k hk1 hk2 hne

theorem m6Dfs_step_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen beg end_b mk2 : Nat} {blvl : BitVec 32} {tmp_s : List (BitVec 32)}
    {mrk0 : List (BitVec 8)} {b : ShrinkScratch} {mrk' : List (BitVec 8)}
    {mclr' wsort' : List (BitVec 32)} {mcl' : Nat} {mcf' ticks' : BitVec 64}
    (hinv : M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg end_b mk2 b)
    (hmk_end : mk2 < end_b)
    (hblk_lvl : ∀ j, beg ≤ j → j < end_b →
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hmrk_len' : mrk'.length = c.max_vars) (hmclr_len' : mclr'.length = c.max_vars)
    (hmcl_le' : mcl' ≤ c.max_vars) (hw_len' : wsort'.length = 2 * c.max_vars)
    (hm2' : ∀ w < s.core.cur_vars,
      (b.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8' : ∀ w < s.core.cur_vars,
      (mrk'[w]?.getD 0#8 &&& 8#8) = (b.mrk[w]?.getD 0#8 &&& 8#8))
    (hab' : ∀ w, s.core.cur_vars ≤ w → mrk'[w]? = b.mrk[w]?)
    (hmin' : FullMinMarkInv ({ b with
        mrk := mrk', mclr := mclr', wsort := wsort', mcl := mcl', mcf := mcf',
        ticks := ticks' }.st s).core
      (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) :
    M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg end_b (mk2 + 1)
      { b with
        mrk := mrk', mclr := mclr', wsort := wsort', mcl := mcl', mcf := mcf',
        ticks := ticks' } := by
  have hbm := hinv.beg_mk
  have hel := hinv.end_le
  have hlen' : ShrinkScratch.LengthsOk
      { b with
        mrk := mrk', mclr := mclr', wsort := wsort', mcl := mcl', mcf := mcf',
        ticks := ticks' } c :=
    { hinv.len with
      mrk_len := hmrk_len', mclr_len := hmclr_len', mcl_le := hmcl_le', wsort_len := hw_len' }
  refine ⟨hinv.beg_ge1, by omega, by omega, hel, hlen', hinv.tmp0_eq,
    fun j hj1 hj2 => hinv.tail_eq j (by omega) hj2, ?_, hinv.kept_lvls, hinv.kept_sorted,
    hinv.beg_bd, ?_, hinv.nodup, hmin', hinv.ent,
    fun w hw' => by rw [hbit8' w hw', hinv.no8 w hw'],
    fun w hw' => (hab' w hw').trans (hinv.mrk_above w hw')⟩
  · intro k hk hne
    dsimp only at hne ⊢
    obtain ⟨h1, h2, h3⟩ := hinv.kept_lits k hk hne
    exact ⟨h1, h2, hm2' _ (by omega) h3⟩
  · intro k hk1 hk2 hne
    by_cases hkm : k = mk2
    · subst k
      rw [hinv.tail_eq mk2 (le_refl _) (by omega)]
      exact hblk_lvl mk2 hk1 hmk_end
    · exact hinv.blk_lvl k hk1 (by omega) hne

theorem m6Dfs_step_true {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen beg end_b mk2 : Nat} {blvl : BitVec 32} {tmp_s : List (BitVec 32)}
    {mrk0 : List (BitVec 8)} {b : ShrinkScratch} {mrk' : List (BitVec 8)}
    {mclr' wsort' : List (BitVec 32)} {mcl' : Nat} {mcf' ticks' : BitVec 64}
    (hcv : s.core.cur_vars ≤ c.max_vars) (hot_le : orig_tlen ≤ s.core.cur_vars)
    (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hinv : M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg end_b mk2 b)
    (hmk_end : mk2 < end_b)
    (hmrk_len' : mrk'.length = c.max_vars) (hmclr_len' : mclr'.length = c.max_vars)
    (hmcl_le' : mcl' ≤ c.max_vars) (hw_len' : wsort'.length = 2 * c.max_vars)
    (hm2' : ∀ w < s.core.cur_vars,
      (b.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8' : ∀ w < s.core.cur_vars,
      (mrk'[w]?.getD 0#8 &&& 8#8) = (b.mrk[w]?.getD 0#8 &&& 8#8))
    (hab' : ∀ w, s.core.cur_vars ≤ w → mrk'[w]? = b.mrk[w]?)
    (hroot_min : ∀ keep',
      (∀ l ∈ (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat),
        l = (b.tmp[mk2]?.getD 0#32).toNat ∨ l ∈ keep') →
      FullMinMarkInv ({ b with
        mrk := mrk', mclr := mclr', wsort := wsort', mcl := mcl', mcf := mcf',
        ticks := ticks' }.st s).core keep') :
    let tmp' := b.tmp.set mk2 0xFFFFFFFF#32
    M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg end_b (mk2 + 1)
      { b with
        tmp := tmp', mrk := mrk', mclr := mclr', wsort := wsort', mcl := mcl', mcf := mcf',
        ticks := ticks' } := by
  intro tmp'
  let b' : ShrinkScratch := { b with
    tmp := tmp', mrk := mrk', mclr := mclr', wsort := wsort', mcl := mcl', mcf := mcf',
    ticks := ticks' }
  have hb1 := hinv.beg_ge1
  have hbm := hinv.beg_mk
  have hel := hinv.end_le
  have htl := hinv.len.tmp_len
  have hmk2_len : mk2 < b.tmp.length := by rw [htl]; omega
  have ht' : tmp'.length = c.max_vars := by simp [tmp', htl]
  have hlen' : b'.LengthsOk c :=
    { tmp_len := ht', mrk_len := hmrk_len', mclr_len := hmclr_len', mcl_le := hmcl_le',
      sstk_len := hinv.len.sstk_len, wsort_len := hw_len', ws1_len := hinv.len.ws1_len }
  have hkeep_sub : ∀ l ∈ (((b.tmp.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat),
      l = (b.tmp[mk2]?.getD 0#32).toNat ∨
      l ∈ (((tmp'.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
    intro l hl
    rw [mem_filter_map_toNat_take] at hl ⊢
    obtain ⟨k, hk, bv, hkb, hne, rfl⟩ := hl
    by_cases hkm : k = mk2
    · left; subst k; rw [hkb, Option.getD_some]
    · right; refine ⟨k, by rw [ht']; rw [htl] at hk; exact hk, bv, ?_, hne, rfl⟩
      dsimp only [tmp']; rw [List.getElem?_set_ne (Ne.symm hkm)]; exact hkb
  have hmin' : FullMinMarkInv (b'.st s).core
      (((tmp'.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
    have hr := hroot_min _ hkeep_sub
    exact ⟨hr.mrk_dom, hr.clr_cov, hr.rem_sound⟩
  have hkept' : ∀ k < orig_tlen, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (tmp'[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro k hk hne
    have hkm : k ≠ mk2 := fun h => by
      subst k; dsimp only [tmp'] at hne
      rw [List.getElem?_set_self (by rw [htl]; omega), Option.getD_some] at hne
      exact hne rfl
    have hkeq : tmp'[k]? = b.tmp[k]? := List.getElem?_set_ne (Ne.symm hkm)
    simp only [hkeq] at hne ⊢
    obtain ⟨h1, h2, h3⟩ := hinv.kept_lits k hk hne
    exact ⟨h1, h2, hm2' _ (by omega) h3⟩
  have hEnt' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((tmp'.take orig_tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) := by
    have hwf := m6Witness_blk (b := b') hw
    refine fullMinMark_entails hwf hmin' hinv.ent fun l hl => ?_
    rw [mem_filter_map_toNat_take] at hl
    obtain ⟨k, hk, bv, hkb, hne, rfl⟩ := hl
    have hk_o : k < orig_tlen := by omega
    obtain ⟨h1, h2, h3⟩ := hinv.kept_lits k hk_o (by rw [hkb, Option.getD_some]; exact hne)
    have hb_eq : (b.tmp[k]?.getD 0#32).toNat = bv.toNat := by rw [hkb, Option.getD_some]
    rw [hb_eq] at h1 h2 h3
    exact ⟨h1, h2, Or.inr (hm2' _ (by omega) h3)⟩
  refine ⟨hb1, by omega, by omega, hel, hlen', ?_, fun j hj1 hj2 => ?_, hkept',
    fun k hk1 hk2 hne => ?_, fun i j hi1 hij hj hni hnj => ?_, fun k hk1 hk2 hne => ?_,
    fun k hk1 hk2 hne => ?_,
    nodup_filter_set_sent (by rw [htl]; omega) (by omega) hinv.nodup, hmin', hEnt',
    fun w hw' => by rw [hbit8' w hw', hinv.no8 w hw'],
    fun w hw' => (hab' w hw').trans (hinv.mrk_above w hw')⟩
  · dsimp only [b', tmp']
    rw [List.getElem?_set_ne (by omega)]
    exact hinv.tmp0_eq
  · dsimp only [b', tmp']; rw [List.getElem?_set_ne (by omega)]
    exact hinv.tail_eq j (by omega) hj2
  · have hkm : k ≠ mk2 := fun h => by
      subst k; dsimp only [b'] at hne; simp [tmp', List.getElem?_set_self hmk2_len] at hne
    have hkeq : tmp'[k]? = b.tmp[k]? := List.getElem?_set_ne (Ne.symm hkm)
    dsimp only [b'] at hne ⊢; simp only [hkeq] at hne ⊢; exact hinv.kept_lvls k hk1 hk2 hne
  · have him : i ≠ mk2 := fun h => by
      subst i; dsimp only [b'] at hni; simp [tmp', List.getElem?_set_self hmk2_len] at hni
    have hjm : j ≠ mk2 := fun h => by
      subst j; dsimp only [b'] at hnj; simp [tmp', List.getElem?_set_self hmk2_len] at hnj
    have hieq : tmp'[i]? = b.tmp[i]? := List.getElem?_set_ne (Ne.symm him)
    have hjeq : tmp'[j]? = b.tmp[j]? := List.getElem?_set_ne (Ne.symm hjm)
    dsimp only [b'] at hni hnj ⊢; simp only [hieq, hjeq] at hni hnj ⊢
    exact hinv.kept_sorted i j hi1 hij hj hni hnj
  · have hkm : k ≠ mk2 := by omega
    have hkeq : tmp'[k]? = b.tmp[k]? := List.getElem?_set_ne (Ne.symm hkm)
    dsimp only [b'] at hne ⊢; simp only [hkeq] at hne ⊢; exact hinv.beg_bd k hk1 hk2 hne
  · have hkm : k ≠ mk2 := fun h => by
      subst k; dsimp only [b'] at hne; simp [tmp', List.getElem?_set_self hmk2_len] at hne
    have hkeq : tmp'[k]? = b.tmp[k]? := List.getElem?_set_ne (Ne.symm hkm)
    dsimp only [b'] at hne ⊢; simp only [hkeq] at hne ⊢; exact hinv.blk_lvl k hk1 (by omega) hne

theorem m6Dfs_to_loop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen beg end_b : Nat} {blvl : BitVec 32} {tmp_s : List (BitVec 32)}
    {mrk0 : List (BitVec 8)} {b : ShrinkScratch}
    (hinv : M6DfsLoopInv c F0 F_cur s orig_tlen blvl tmp_s mrk0 beg end_b end_b b)
    (hend_strict : end_b < orig_tlen →
      blvl.toNat < (s.core.lvl[(tmp_s[end_b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) :
    M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 end_b b := by
  have hb1 := hinv.beg_ge1
  have hbm := hinv.beg_mk
  refine ⟨by omega, hinv.end_le, hinv.len, hinv.tmp0_eq, hinv.tail_eq, hinv.kept_lits,
    hinv.kept_lvls, hinv.kept_sorted, ?_, hinv.nodup, hinv.min_inv, hinv.ent, hinv.no8,
    hinv.mrk_above⟩
  intro he k hk1 hk2 hne
  have hs := hend_strict he
  by_cases hkb : k < beg
  · have := hinv.beg_bd k hk1 hkb hne; omega
  · have := hinv.blk_lvl k (by omega) hk2 hne; omega

/-! ## 4. Compaction, Mark Clearing, Reversal, & Final Spec Discharge -/

structure M6CompactInv (c : FullCfg) (s : FullState) (orig_tlen : Nat)
    (tmp_s tmp_f tmp_c : List (BitVec 32)) (keep k : Nat) : Prop where
  keep_ge1 : 1 ≤ keep
  keep_le : keep ≤ k
  k_le : k ≤ orig_tlen
  tmp_len : tmp_c.length = c.max_vars
  tmp0_eq : tmp_c[0]? = tmp_s[0]?
  prefix_eq : tmp_c.take keep = (tmp_f.take k).filter (· ≠ 0xFFFFFFFF#32)
  tail_eq : ∀ j, k ≤ j → j < orig_tlen → tmp_c[j]? = tmp_f[j]?
  elem_ok : ∀ j, 1 ≤ j → j < keep →
    let l := (tmp_c[j]?.getD 0#32).toNat
    let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    0 < lv ∧ lv < s.core.cur_level

theorem m6Compact_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen : Nat} {tmp_s : List (BitVec 32)} {mrk0 : List (BitVec 8)} {b : ShrinkScratch}
    (hot_pos : 1 ≤ orig_tlen) (_hot_le : orig_tlen ≤ s.core.cur_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hs_nosent0 : tmp_s[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hshrink : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 orig_tlen b) :
    M6CompactInv c s orig_tlen tmp_s b.tmp b.tmp 1 1 := by
  refine ⟨le_refl _, le_refl _, hot_pos, hshrink.len.tmp_len, hshrink.tmp0_eq, ?_,
    fun _ _ _ => rfl, fun _ h1 h2 => absurd h1 (by omega)⟩
  symm
  refine m6_take_map_filter_no_sent (by rw [hshrink.len.tmp_len]; omega) fun j hj => ?_
  have hj0 : j = 0 := by omega
  subst j; rw [hshrink.tmp0_eq]; exact hs_nosent0

theorem m6Compact_step_skip {c : FullCfg} {s : FullState} {orig_tlen : Nat}
    {tmp_s tmp_f tmp_c : List (BitVec 32)} {keep k : Nat}
    (hcv : s.core.cur_vars ≤ c.max_vars) (hot_le : orig_tlen ≤ s.core.cur_vars)
    (hcinv : M6CompactInv c s orig_tlen tmp_s tmp_f tmp_c keep k) (hk_lt : k < orig_tlen)
    (htf_len : tmp_f.length = c.max_vars)
    (hskip : tmp_c[k]?.getD 0#32 = 0xFFFFFFFF#32) :
    M6CompactInv c s orig_tlen tmp_s tmp_f tmp_c keep (k + 1) := by
  have hk_ge := hcinv.keep_ge1
  have hkl := hcinv.keep_le
  have hk_f : k < tmp_f.length := by rw [htf_len]; omega
  have hce : tmp_c[k]? = tmp_f[k]? := hcinv.tail_eq k (le_refl _) hk_lt
  have hfe : tmp_f[k] = 0xFFFFFFFF#32 := by
    have := hce ▸ hskip
    rwa [List.getElem?_eq_getElem hk_f, Option.getD_some] at this
  refine ⟨hk_ge, by omega, by omega, hcinv.tmp_len, hcinv.tmp0_eq, ?_,
    fun j hj1 hj2 => hcinv.tail_eq j (by omega) hj2, hcinv.elem_ok⟩
  rw [hcinv.prefix_eq, List.take_succ_eq_append_getElem hk_f, List.filter_append, hfe]
  simp

theorem m6Compact_step_keep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen : Nat} {tmp_s tmp_c : List (BitVec 32)} {mrk0 : List (BitVec 8)}
    {b : ShrinkScratch} {keep k : Nat}
    (hcv : s.core.cur_vars ≤ c.max_vars) (hot_le : orig_tlen ≤ s.core.cur_vars)
    (hshrink : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 orig_tlen b)
    (hcinv : M6CompactInv c s orig_tlen tmp_s b.tmp tmp_c keep k) (hk_lt : k < orig_tlen)
    (hkeep_ne : tmp_c[k]?.getD 0#32 ≠ 0xFFFFFFFF#32) :
    let v := tmp_c[k]?.getD 0#32
    let tmp' := tmp_c.set keep v
    M6CompactInv c s orig_tlen tmp_s b.tmp tmp' (keep + 1) (k + 1) := by
  intro v tmp'
  have hk_ge := hcinv.keep_ge1
  have hkl := hcinv.keep_le
  have htf := hshrink.len.tmp_len
  have htc := hcinv.tmp_len
  have hk_f : k < b.tmp.length := by rw [htf]; omega
  have hkeep_c : keep < tmp_c.length := by rw [htc]; omega
  have htc' : tmp'.length = c.max_vars := by simp [tmp', htc]
  have hce : tmp_c[k]? = b.tmp[k]? := hcinv.tail_eq k (le_refl _) hk_lt
  have hvf : v = b.tmp[k]'hk_f := by
    dsimp only [v]; rw [hce, List.getElem?_eq_getElem hk_f, Option.getD_some]
  have hv_ne : b.tmp[k]'hk_f ≠ 0xFFFFFFFF#32 := by rwa [← hvf]
  have hpref : tmp'.take (keep + 1) = (b.tmp.take (k + 1)).filter (· ≠ 0xFFFFFFFF#32) := by
    rw [List.take_succ_eq_append_getElem (by rw [htc']; omega)]
    rw [List.take_succ_eq_append_getElem hk_f, List.filter_append]
    have hfilt1 : [b.tmp[k]'hk_f].filter (· ≠ 0xFFFFFFFF#32) = [v] := by
      simp [hv_ne, hvf]
    have htake_k : tmp'.take keep = tmp_c.take keep := by
      apply List.ext_getElem
      · simp [htc', htc]
      · intro j hj1 _
        have hjk : j < keep := Nat.lt_of_lt_of_le hj1 (List.length_take_le _ _)
        dsimp only [tmp']
        rw [List.getElem_take, List.getElem_take, List.getElem_set_ne (by omega)]
    have hget_k : tmp'[keep]'(by rw [htc']; omega) = v := by
      dsimp only [tmp']; exact List.getElem_set_self (by rw [List.length_set]; exact hkeep_c)
    rw [htake_k, hget_k, hcinv.prefix_eq, hfilt1]
  refine ⟨by omega, by omega, by omega, htc', ?_, hpref, fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_⟩
  · dsimp only [tmp']
    rw [List.getElem?_set_ne (by omega)]
    exact hcinv.tmp0_eq
  · dsimp only [tmp']; rw [List.getElem?_set_ne (by omega)]
    exact hcinv.tail_eq j (by omega) hj2
  · by_cases hjk : j = keep
    · subst j
      have hj_eq : tmp'[keep]? = b.tmp[k]? := by
        dsimp only [tmp']
        rw [List.getElem?_set_self hkeep_c, List.getElem?_eq_getElem hk_f, hvf]
      have hf_ne : b.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [List.getElem?_eq_getElem hk_f, Option.getD_some]; exact hv_ne
      obtain ⟨h1, h2, _⟩ := hshrink.kept_lits k hk_lt hf_ne
      obtain ⟨h3, h4⟩ := hshrink.kept_lvls k (by omega) hk_lt hf_ne
      simp only [hj_eq]; exact ⟨h1, h2, h3, h4⟩
    · have hj_eq : tmp'[j]? = tmp_c[j]? := List.getElem?_set_ne (Ne.symm hjk)
      simp only [hj_eq]; exact hcinv.elem_ok j hj1 (by omega)

structure M6TmpOutInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (orig_tlen keep : Nat) (tmp1 : List (BitVec 32)) : Prop where
  keep_ge1 : 1 ≤ keep
  keep_le : keep ≤ orig_tlen
  tmp_len : tmp1.length = c.max_vars
  tmp0_eq : tmp1[0]? = s.core.tmp[0]?
  nodup : ((tmp1.take keep).map fun x => x.toNat / 2).Nodup
  ent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp1.take keep).map BitVec.toNat))
  elem_ok : ∀ j, 1 ≤ j → j < keep →
    let l := (tmp1[j]?.getD 0#32).toNat
    let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    0 < lv ∧ lv < s.core.cur_level

theorem m6_compact_to_out {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen : Nat} {tmp_s tmp_c : List (BitVec 32)} {mrk0 : List (BitVec 8)}
    {b : ShrinkScratch} {keep : Nat}
    (hs_0eq : tmp_s[0]? = s.core.tmp[0]?)
    (hshrink : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 orig_tlen b)
    (hcinv : M6CompactInv c s orig_tlen tmp_s b.tmp tmp_c keep orig_tlen) :
    M6TmpOutInv c F0 F_cur s orig_tlen keep tmp_c := by
  have hnd := hshrink.nodup
  have hent := hshrink.ent
  rw [← hcinv.prefix_eq] at hnd hent
  exact ⟨hcinv.keep_ge1, Nat.le_trans hcinv.keep_le hcinv.k_le, hcinv.tmp_len,
    hcinv.tmp0_eq.trans hs_0eq, hnd, hent, hcinv.elem_ok⟩

theorem m6TmpOutInv_swap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen keep lo hi : Nat} {tmp1 : List (BitVec 32)}
    (hot_le : orig_tlen ≤ s.core.cur_vars) (hcv : s.core.cur_vars ≤ c.max_vars)
    (hout : M6TmpOutInv c F0 F_cur s orig_tlen keep tmp1)
    (hlo : 1 ≤ lo) (hlohi : lo < hi) (hhi : hi < keep) :
    let tmp' := (tmp1.set lo (tmp1[hi]?.getD 0#32)).set hi (tmp1[lo]?.getD 0#32)
    M6TmpOutInv c F0 F_cur s orig_tlen keep tmp' := by
  intro tmp'
  have hkeep_len : keep ≤ tmp1.length := by rw [hout.tmp_len]; have := hout.keep_le; omega
  have hhi_len : hi < tmp1.length := by omega
  have hlo_len : lo < tmp1.length := by omega
  have ht' : tmp'.length = c.max_vars := by simp [tmp', hout.tmp_len]
  have htake_eq : tmp'.take keep =
      (((tmp1.take keep).set lo ((tmp1.take keep)[hi]'(by rw [List.length_take]; omega))).set
        hi ((tmp1.take keep)[lo]'(by rw [List.length_take]; omega))) := by
    apply List.ext_getElem
    · simp [tmp', ht', hout.tmp_len]
    · intro j hj1 _
      simp only [List.length_take] at hj1
      have hj_k : j < keep := by omega
      simp only [tmp', List.getElem_take]
      by_cases hj_hi : j = hi
      · subst j
        rw [List.getElem_set_self (by simp [hout.tmp_len]; omega)]
        rw [List.getElem_set_self (by simp [hout.tmp_len]; omega)]
        rw [List.getElem?_eq_getElem hlo_len, Option.getD_some]
      · rw [List.getElem_set_ne (Ne.symm hj_hi), List.getElem_set_ne (Ne.symm hj_hi)]
        by_cases hj_lo : j = lo
        · subst j
          rw [List.getElem_set_self (by rw [List.length_set]; omega)]
          rw [List.getElem_set_self (by rw [List.length_set, List.length_take]; omega)]
          rw [List.getElem?_eq_getElem hhi_len, Option.getD_some]
        · rw [List.getElem_set_ne (Ne.symm hj_lo), List.getElem_set_ne (Ne.symm hj_lo)]
          simp only [List.getElem_take]
  have hperm : (tmp'.take keep).Perm (tmp1.take keep) := by
    rw [htake_eq]
    exact m7_list_swap_perm (tmp1.take keep) hlohi (by rw [List.length_take]; omega)
  refine ⟨hout.keep_ge1, hout.keep_le, ht', ?_, m6_nodup_of_perm hperm.symm hout.nodup,
    m6_entails_of_perm hperm.symm hout.ent, fun j hj1 hj2 => ?_⟩
  · dsimp only [tmp']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hout.tmp0_eq
  · dsimp only [tmp']
    by_cases hj_hi : j = hi
    · subst j
      rw [List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
      rw [List.getElem?_eq_getElem hlo_len, Option.getD_some]
      have he := hout.elem_ok lo hlo (by omega)
      rwa [List.getElem?_eq_getElem hlo_len, Option.getD_some] at he
    · rw [List.getElem?_set_ne (Ne.symm hj_hi)]
      by_cases hj_lo : j = lo
      · subst j
        rw [List.getElem?_set_self hlo_len, Option.getD_some]
        rw [List.getElem?_eq_getElem hhi_len, Option.getD_some]
        have he := hout.elem_ok hi (by omega) hhi
        rwa [List.getElem?_eq_getElem hhi_len, Option.getD_some] at he
      · rw [List.getElem?_set_ne (Ne.symm hj_lo)]
        exact hout.elem_ok j hj1 hj2

theorem m6_clear_full_done {c : FullCfg} {s : FullState} {mrk0 mrk' : List (BitVec 8)}
    (hclear : FullLitMarksClear c s)
    (hmrk0_above : ∀ w, s.core.cur_vars ≤ w → mrk0[w]? = s.core.mrk[w]?)
    (hzero : ∀ w < s.core.cur_vars, mrk'[w]? = some 0#8)
    (hab : ∀ w, s.core.cur_vars ≤ w → mrk'[w]? = mrk0[w]?) :
    ∀ w < c.max_vars, mrk'[w]?.getD 0#8 = 0#8 := by
  intro w hw
  by_cases hlt : w < s.core.cur_vars
  · rw [hzero w hlt, Option.getD_some]
  · have hge : s.core.cur_vars ≤ w := by omega
    rw [hab w hge, hmrk0_above w hge]; exact hclear.1 w hw

structure M6ClearListInv (c : FullCfg) (s : FullState) (mclr1 : List (BitVec 32))
    (mcl1 z : Nat) (mrk_z : List (BitVec 8)) : Prop where
  z_le : z ≤ mcl1
  mrk_len : mrk_z.length = c.max_vars
  mrk_above : ∀ w, s.core.cur_vars ≤ w → mrk_z[w]? = s.core.mrk[w]?
  cov : ∀ w < s.core.cur_vars, mrk_z[w]?.getD 0#8 ≠ 0#8 →
    ∃ j, z ≤ j ∧ j < mcl1 ∧ (mclr1[j]?.getD 0#32).toNat = w

theorem m6_clear_list_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen : Nat} {tmp_s : List (BitVec 32)} {mrk0 : List (BitVec 8)} {b : ShrinkScratch}
    (hmcf : b.mcf = 0#64)
    (hshrink : M6ShrinkLoopInv c F0 F_cur s orig_tlen tmp_s mrk0 orig_tlen b)
    (hmrk0_above : ∀ w, s.core.cur_vars ≤ w → mrk0[w]? = s.core.mrk[w]?) :
    M6ClearListInv c s b.mclr b.mcl 0 b.mrk := by
  refine ⟨Nat.zero_le _, hshrink.len.mrk_len,
    fun w hw => (hshrink.mrk_above w hw).trans (hmrk0_above w hw), fun w hw hnz => ?_⟩
  have h6 : (b.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 := fun h =>
    hnz (bv8_eq_zero_of_masks _ (hshrink.min_inv.mrk_dom w hw) (hshrink.no8 w hw) h)
  obtain ⟨j, hj, hjeq⟩ := hshrink.min_inv.clr_cov hmcf w hw h6
  exact ⟨j, Nat.zero_le _, hj, hjeq⟩

theorem m6_clear_list_step_lt {c : FullCfg} {s : FullState} {mclr1 : List (BitVec 32)}
    {mcl1 z : Nat} {mrk_z : List (BitVec 8)}
    (hinv : M6ClearListInv c s mclr1 mcl1 z mrk_z) (hz : z < mcl1)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hz_lt : (mclr1[z]?.getD 0#32).toNat < s.core.cur_vars) :
    M6ClearListInv c s mclr1 mcl1 (z + 1) (mrk_z.set (mclr1[z]?.getD 0#32).toNat 0#8) := by
  have hlen : (mclr1[z]?.getD 0#32).toNat < mrk_z.length := by rw [hinv.mrk_len]; omega
  refine ⟨hz, by simp [hinv.mrk_len], fun w hw => by
    rw [List.getElem?_set_ne (by omega)]; exact hinv.mrk_above w hw, fun w hw hnz => ?_⟩
  by_cases hwz : w = (mclr1[z]?.getD 0#32).toNat
  · subst w
    rw [List.getElem?_set_self hlen, Option.getD_some] at hnz
    exact absurd rfl hnz
  · rw [List.getElem?_set_ne (Ne.symm hwz)] at hnz
    obtain ⟨j, hj1, hj2, hjeq⟩ := hinv.cov w hw hnz
    have hjz : j ≠ z := fun h => by subst j; exact hwz hjeq.symm
    exact ⟨j, by omega, hj2, hjeq⟩

theorem m6_clear_list_step_ge {c : FullCfg} {s : FullState} {mclr1 : List (BitVec 32)}
    {mcl1 z : Nat} {mrk_z : List (BitVec 8)}
    (hinv : M6ClearListInv c s mclr1 mcl1 z mrk_z) (hz : z < mcl1)
    (hz_ge : s.core.cur_vars ≤ (mclr1[z]?.getD 0#32).toNat) :
    M6ClearListInv c s mclr1 mcl1 (z + 1) mrk_z := by
  refine ⟨hz, hinv.mrk_len, hinv.mrk_above, fun w hw hnz => ?_⟩
  obtain ⟨j, hj1, hj2, hjeq⟩ := hinv.cov w hw hnz
  have hjz : j ≠ z := fun h => by subst j; omega
  exact ⟨j, by omega, hj2, hjeq⟩

theorem m6_clear_list_done {c : FullCfg} {s : FullState} {mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mrk_z : List (BitVec 8)}
    (hclear : FullLitMarksClear c s)
    (hinv : M6ClearListInv c s mclr1 mcl1 mcl1 mrk_z) :
    ∀ w < c.max_vars, mrk_z[w]?.getD 0#8 = 0#8 := by
  intro w hw
  by_cases hlt : w < s.core.cur_vars
  · by_cases hnz : mrk_z[w]?.getD 0#8 = 0#8
    · exact hnz
    · obtain ⟨j, hj1, hj2, _⟩ := hinv.cov w hlt hnz
      omega
  · rw [hinv.mrk_above w (by omega)]; exact hclear.1 w hw

theorem m6_finish_spec {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {orig_tlen keep : Nat} {tmp' : List (BitVec 32)} {mrk' : List (BitVec 8)}
    {mclr' sstk' wsort' ws1' : List (BitVec 32)}
    {conf' llits' mrem' ticks' resSz' : BitVec 64}
    (hlen : s.LengthsOk c) (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hclear : FullLitMarksClear c s) (hot_le : orig_tlen ≤ s.core.cur_vars)
    (hot_eq : orig_tlen = s.core.tmp_len)
    (hout : M6TmpOutInv c F0 F_cur s orig_tlen keep tmp')
    (hmrk_len' : mrk'.length = c.max_vars) (hmclr_len' : mclr'.length = c.max_vars)
    (hsstk_len' : sstk'.length = c.max_vars) (hw_len' : wsort'.length = 2 * c.max_vars)
    (hws1_len' : ws1'.length = 2 * c.max_vars)
    (hmrk0' : ∀ w < c.max_vars, mrk'[w]?.getD 0#8 = 0#8) :
    let s' := fullMinShrinkState s tmp' keep mrk' mclr' sstk' wsort' ws1' 0 0#64 conf'
      llits' mrem' ticks' resSz'
    s'.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s'.core ∧ FullLitMarksClear c s' ∧
    1 ≤ keep ∧ keep ≤ s.core.tmp_len ∧ tmp'[0]? = s.core.tmp[0]? ∧
    ((tmp'.take keep).map fun x => x.toNat / 2).Nodup ∧
    (∀ j, 1 ≤ j → j < keep →
      let l := (tmp'[j]?.getD 0#32).toNat
      let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      0 < lv ∧ lv < s.core.cur_level) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take keep).map BitVec.toNat)) := by
  intro s'
  have hcv := hlen.core_ok.cur_vars_le
  refine ⟨?_, m6Witness_fin hw, m6LitMarksClear_of hclear (fun v hv => hmrk0' v hv) rfl,
    hout.keep_ge1, hot_eq ▸ hout.keep_le, hout.tmp0_eq, hout.nodup, hout.elem_ok, hout.ent⟩
  dsimp only [s', fullMinShrinkState]
  exact ⟨{ hlen.core_ok with
    tmp_len_arr := hout.tmp_len
    tmp_len_le := by
      dsimp only; have := hout.keep_le; have := hot_le; have := hot_eq; have := hcv; omega
    mrk_len := hmrk_len'
    min_clr_len_arr := hmclr_len'
    min_clr_len_le := Nat.zero_le _ },
    { hlen.scratch_ok with
      shrink_stk_len := hsstk_len'
      wsort_len := hw_len'
      work_stk1_len := hws1_len' }⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
